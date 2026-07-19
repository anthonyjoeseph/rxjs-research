-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation, in three layers.
--   1. Inv (CONCRETE below) relates evaluator state to automaton
--      state between cascades.
--   2. Two frame relations — BurstInv (mid-subscribe-frame) and Mid
--      (mid-cascade, indexed by the chains still to fold) — with
--      their entry/step/exit lemmas.  These are the postulated
--      waypoints; the step lemmas (subscribeE-wf, mid-step) mirror
--      the evaluator's own recursion and carry the same TERMINATING
--      debt as the functions they follow.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _≤_; _≡ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; any; length)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_;
                                sched-init; st-init; sched-next;
                                arrTy; arrSource; chainsOf; chainStep;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; protocol-init;
                                stepProtocol; runProtocol; paidUp;
                                checkFinal; Accepted; accepted; WellFormed)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

_>>=ᴹ_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=ᴹ f = f a
nothing >>=ᴹ f = nothing

runProtocol-++ : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A)) →
  runProtocol S (xs ++ ys)
    ≡ (runProtocol S xs >>=ᴹ λ S′ → runProtocol S′ ys)
runProtocol-++ S []       ys = refl
runProtocol-++ S (x ∷ xs) ys with stepProtocol x S
... | just S′ = runProtocol-++ S′ xs ys
... | nothing = refl

run-++-just : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A))
              {S₁ S₂ : ProtocolSt} →
  runProtocol S xs ≡ just S₁ → runProtocol S₁ ys ≡ just S₂ →
  runProtocol S (xs ++ ys) ≡ just S₂
run-++-just S xs ys {S₁} e₁ e₂ =
  trans (runProtocol-++ S xs ys)
        (trans (cong (λ m → m >>=ᴹ (λ S′ → runProtocol S′ ys)) e₁) e₂)

acceptPaid : (S : ProtocolSt) → paidUp S ≡ true → Accepted (checkFinal (just S))
acceptPaid S eq rewrite eq = accepted

------------------------------------------------------------------
-- Inv, CONCRETE: the between-cascades simulation relation
------------------------------------------------------------------

-- registrations of s, counted off the registry (the writer's ledger
-- the automaton's live multiset must shadow)
countRegs : ∀ {n} {Γ : Ctx n} {t}
          → Source → List (RegId × Source × Chain Γ t) → ℕ
countRegs s [] = zero
countRegs s ((_ , x , _) ∷ r) =
  if s ≡ᵇ x then suc (countRegs s r) else countRegs s r

-- a path that never reaches the root delivers no values there
sinksToShare : ∀ {n} {Γ : Ctx n} {u t} → Path Γ u t → Bool
sinksToShare root           = false
sinksToShare (share-sink i) = true
sinksToShare (f ↠ p)        = sinksToShare p

allShareSunk : ∀ {n} {Γ : Ctx n} {t}
             → List (RegId × Source × Chain Γ t) → Bool
allShareSunk []                      = true
allShareSunk ((_ , _ , (u , p)) ∷ r) = sinksToShare p ∧ allShareSunk r

-- the open (or last) instant is strictly in the past
CurrentPast : Maybe (Id × Owed) → Id → Set
CurrentPast nothing        nextId = ⊤
CurrentPast (just (j , _)) nextId = suc j ≤ nextId

record Inv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    -- the automaton's live multiset shadows the registry: per source,
    -- one for one
    live-matches : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    -- for any arrival the SCHEDULER can actually produce, the
    -- snapshot is the full registration count — registry entries are
    -- well-typed for their scheduled source, so chainsOf's type
    -- check drops nothing.  (Conditioning on sched-next matters: an
    -- ill-typed phantom arrival would break the equation vacuously.)
    chains-count : ∀ (a : Arrival Γ) (sched″ : Sched Γ) →
      sched-next sched ≡ inj₂ (a , sched″) →
      countRegs (arrSource a) (EvalSt.registry st) ≡ length (chainsOf a st)
    -- freshness is one comparison: ids mint from arrival position
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    current-past : CurrentPast (ProtocolSt.current S) nextId
    -- after the root completes, only share plumbing survives — no
    -- registration can ever carry a value to the root again
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true

------------------------------------------------------------------
-- the subscribe frame: BurstInv and its entry/step/exit lemmas
------------------------------------------------------------------

postulate
  -- mid-subscribe-frame: instant `id` open with EMPTY owed (subscribe
  -- and plumbing emits never seed or pay), live shadowing the
  -- registry, horizon ≤ id, every init fresh, every close matched
  BurstInv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → Id → Sched Γ → EvalSt e → ProtocolSt → Set

  -- the empty states are related
  burst-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    BurstInv {e = e} 0 (sched-init e ins) (st-init e) protocol-init

  -- ONE subscription's burst preserves the frame relation.  The
  -- per-primitive preservation induction: one obligation per
  -- subscribeE clause, mirrored on its recursion (same TERMINATING
  -- debt as the function; discharged together, later)
  subscribeE-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    Σ ProtocolSt λ S′ →
      let r = subscribeE b κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

  -- leaving the frame: the open instant settles (owed never seeded ⇒
  -- paid), landing Inv-related for the first arrival
  burst-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv 0 sched st S →
    Inv 1 sched st S × (paidUp S ≡ true)

-- the root subscription, composed
subscribe-wf :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Σ ProtocolSt λ S →
    let r = subscribeE e root 0 0 (sched-init e ins) (st-init e)
    in (runProtocol protocol-init (proj₁ r) ≡ just S)
       × Inv 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
       × (paidUp S ≡ true)
subscribe-wf e ins
  with subscribeE-wf e root 0 0 (sched-init e ins) (st-init e)
                     protocol-init (burst-init e ins)
... | S , run , binv
  with burst-final _ _ S binv
... | inv , paid = S , run , inv , paid

------------------------------------------------------------------
-- one cascade: Mid and its entry/step/exit lemmas, the chain fold
-- composed
------------------------------------------------------------------

postulate
  -- mid-cascade, indexed by the chains still to fold: instant nextId
  -- open; owed[arrSource] = the remaining chains not yet cancelled
  -- (a cutPending already forgave each cancelled one); every share
  -- handoff so far bumped exactly its dispatch fan-out; live shadows
  -- the registry; the ledger fields (delivered/cancelled/dying/
  -- watermark) agree with the automaton's arithmetic
  Mid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      → (a : Arrival Γ) → Id
      → List (RegId × Path Γ (arrTy a) t)
      → Sched Γ → EvalSt e → ProtocolSt → Set

  -- entering: the latch opens the ledger; the automaton, Inv-related
  -- and paid, stands ready to open instant nextId
  mid-init : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
    sched-next sched ≡ inj₂ (a , sched′) →
    Inv nextId sched st S → paidUp S ≡ true →
    Mid a nextId (chainsOf a st) sched′ (cascadeLatch a st) S

  -- a cancelled chain folds to nothing (its close already rode the
  -- cutting emit; its owed was forgiven right there)
  mid-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    {a : Arrival Γ} {nextId : Id} {rid : RegId}
    {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
    {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
    Mid a nextId ps sched st S

  -- one surviving chain's emits — the chain emit, any share
  -- fan-outs, any cut closes — are accepted, paying/bumping/
  -- cancelling exactly per the ledger.  THE deep lemma: mirrors
  -- foldPath/dispatchShare/stepFrame (same TERMINATING debt)
  mid-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    {a : Arrival Γ} {nextId : Id} {rid : RegId}
    {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
    {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = chainStep nextId a p sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      in (runProtocol S (proj₁ r) ≡ just S′)
         × Mid a nextId ps (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

  -- leaving: all chains folded ⇒ fully paid; finish (drop the spent
  -- source, sweep) lands Inv-related at suc nextId
  mid-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    {a : Arrival Γ} {nextId : Id}
    {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
    Mid a nextId [] sched st S →
    Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                     (proj₂ (cascadeFinish a sched st)) S
    × (paidUp S ≡ true)

-- the chain fold, composed (mirrors cascadeGo's own recursion —
-- structural on the snapshot, no termination debt at this level)
cascadeGo-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  Mid a nextId chains sched st S →
  Σ ProtocolSt λ S′ →
    let r = cascadeGo {e = e} a nextId chains sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Mid a nextId [] (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
cascadeGo-wf a nextId [] sched st S mid = S , refl , mid
cascadeGo-wf a nextId ((rid , p) ∷ ps) sched st S mid
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in ceq
... | true  = cascadeGo-wf a nextId ps sched st S (mid-skip mid ceq)
... | false
  with mid-step {ps = ps} mid ceq
... | S₁ , run₁ , mid₁
  with cascadeGo-wf a nextId ps
         (proj₁ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         (proj₂ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         S₁ mid₁
... | S₂ , run₂ , mid₂ =
  S₂
  , run-++-just S
      (proj₁ (chainStep nextId a p sched
               (record st { delivered = rid ∷ EvalSt.delivered st })))
      _ run₁ run₂
  , mid₂

-- one arrival's cascade, composed
cascade-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  Σ ProtocolSt λ S′ →
    let r = cascade a nextId sched′ st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Inv (suc nextId) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (paidUp S′ ≡ true)
cascade-wf nextId sched a sched′ st S eq inv paid
  with cascadeGo-wf a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
         (mid-init nextId sched a sched′ st S eq inv paid)
... | S′ , run , mid
  with mid-final mid
... | inv′ , paid′ = S′ , run , inv′ , paid′

------------------------------------------------------------------
-- the composition: fuel induction over drain, then the theorem
------------------------------------------------------------------

drain-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
    (S : ProtocolSt) →
  Inv nextId sched st S → paidUp S ≡ true →
  Σ ProtocolSt λ S′ →
    (runProtocol S (drain {e = e} fuel nextId sched st) ≡ just S′)
    × (paidUp S′ ≡ true)
drain-wf zero    nextId sched st S inv paid = S , refl , paid
drain-wf (suc k) nextId sched st S inv paid with sched-next sched in eq
... | inj₁ _            = S , refl , paid
... | inj₂ (a , sched′)
  with cascade-wf nextId sched a sched′ st S eq inv paid
... | S₁ , run₁ , inv₁ , paid₁
  with drain-wf k (suc nextId)
         (proj₁ (proj₂ (cascade a nextId sched′ st)))
         (proj₂ (proj₂ (cascade a nextId sched′ st)))
         S₁ inv₁ paid₁
... | S₂ , run₂ , paid₂ =
  S₂
  , run-++-just S (proj₁ (cascade a nextId sched′ st)) _ run₁ run₂
  , paid₂

-- the primitives' half of the sandwich: remaining debt is the frame
-- relations and their step lemmas above
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins
  with subscribe-wf e ins
... | S₀ , run₀ , inv₀ , paid₀
  with drain-wf fuel 1
         (proj₁ (proj₂ (subscribeE e root 0 0 (sched-init e ins) (st-init e))))
         (proj₂ (proj₂ (subscribeE e root 0 0 (sched-init e ins) (st-init e))))
         S₀ inv₀ paid₀
... | S₁ , run₁ , paid₁
  rewrite run-++-just protocol-init
            (proj₁ (subscribeE e root 0 0 (sched-init e ins) (st-init e)))
            (drain fuel 1
              (proj₁ (proj₂ (subscribeE e root 0 0 (sched-init e ins) (st-init e))))
              (proj₂ (proj₂ (subscribeE e root 0 0 (sched-init e ins) (st-init e)))))
            run₀ run₁
  = acceptPaid S₁ paid₁
