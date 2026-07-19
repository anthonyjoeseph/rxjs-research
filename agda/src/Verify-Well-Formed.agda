-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation, in three layers.
--   1. Inv (CONCRETE below) relates evaluator state to automaton
--      state between cascades.
--   2. Two frame relations — BurstInv (mid-subscribe-frame) and Mid
--      (mid-cascade, indexed by the chains still to fold) — both
--      CONCRETE records now, with entry/step/exit lemmas.  Proven:
--      burst-init, burst-final.  Postulated: the step lemmas
--      (subscribeE-wf, mid-step — the per-clause preservation
--      grind), mid-init, mid-skip, mid-final, and the single
--      budget-sufficient totality conjecture at the bottom.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; any; length)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_;
                                sched-init; st-init; sched-next;
                                arrTy; arrSource; chainsOf; chainStep;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate;
                                sameSource; drySource; dryEvent; hasDry;
                                budgetAt)
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

-- dry-freeness splits over ++ (the step lemmas are conditioned on it;
-- budget-sufficient below asserts it for the whole seeded run)
true≢false : {A : Set} → true ≡ false → A
true≢false ()

hasDry-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry (xs ++ ys) ≡ false →
  (hasDry xs ≡ false) × (hasDry ys ≡ false)
hasDry-++ []        ys h = refl , h
hasDry-++ (em ∷ xs) ys h
  with sameSource (InstEmit.source em) drySource
     | any dryEvent (InstEmit.events em)
... | true  | _     = true≢false h
... | false | true  = true≢false h
... | false | false = hasDry-++ xs ys h

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

-- snapshot entries still obliged to fire: not yet forgiven by a
-- cutPending (the automaton's remaining owed for the arrival source)
countRemaining : ∀ {X : Set} → List (RegId × X) → List RegId → ℕ
countRemaining []               c = zero
countRemaining ((rid , _) ∷ ps) c =
  if any (_≡ᵇ rid) c then countRemaining ps c else suc (countRemaining ps c)

-- association-list reads on the automaton's owed table
lookupOwed : Source → Owed → ℕ
lookupOwed s []            = zero
lookupOwed s ((x , n) ∷ o) = if s ≡ᵇ x then n else lookupOwed s o

-- every source but s is paid to zero (bumped shares get paid back
-- down within the very chainStep that announced them)
zeroExcept : Source → Owed → Bool
zeroExcept s []            = true
zeroExcept s ((x , n) ∷ o) =
  (if s ≡ᵇ x then true else n ≡ᵇ 0) ∧ zeroExcept s o

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

-- mid-subscribe-frame, CONCRETE: live shadows the registry exactly
-- (burst closes and registry cuts move in lockstep), and the open
-- instant — if any emit has landed — is `id` with a LITERALLY EMPTY
-- owed table: subscribe/plumbing settle to net zero, handoffs are
-- minted only by foldPath (never in a burst), and cancelOwed on []
-- is a no-op, so nothing ever writes an entry
record BurstInv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                (id : Id) (sched : Sched Γ) (st : EvalSt e)
                (S : ProtocolSt) : Set where
  field
    live-matches  : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    chains-count  : ∀ (a : Arrival Γ) (sched″ : Sched Γ) →
      sched-next sched ≡ inj₂ (a , sched″) →
      countRegs (arrSource a) (EvalSt.registry st) ≡ length (chainsOf a st)
    horizon-low   : ProtocolSt.horizon S ≤ id
    current-frame : (ProtocolSt.current S ≡ nothing)
                  ⊎ (ProtocolSt.current S ≡ just (id , []))
    done-plumbed  : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true

-- the empty states are related
burst-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  BurstInv {e = e} 0 (sched-init e ins) (st-init e) protocol-init
burst-init e ins = record
  { live-matches  = λ s → refl
  ; chains-count  = λ a sched″ _ → refl
  ; horizon-low   = z≤n
  ; current-frame = inj₁ refl
  ; done-plumbed  = λ ()
  }

postulate
  -- ONE subscription's burst preserves the frame relation.  The
  -- per-primitive preservation induction: one obligation per
  -- subscribeE clause, mirrored on its (now fuel-structural)
  -- recursion.  Conditioned on the run not going dry: a fuel-starved
  -- burst carries the dry sentinel, which the protocol rejects by
  -- design — the unconditioned statement would be false at fuel 0
  subscribeE-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : ℕ) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel b κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel b κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

-- an instant standing on an empty (or absent) owed table settles
≤-up : ∀ {a b : ℕ} → a ≤ b → a ≤ suc b
≤-up z≤n     = z≤n
≤-up (s≤s p) = s≤s (≤-up p)

paid-nothing : (S : ProtocolSt) → ProtocolSt.current S ≡ nothing →
               paidUp S ≡ true
paid-nothing S ceq with ProtocolSt.current S | ceq
... | nothing | refl = refl

paid-empty : (S : ProtocolSt) {j : Id} →
             ProtocolSt.current S ≡ just (j , []) → paidUp S ≡ true
paid-empty S ceq with ProtocolSt.current S | ceq
... | just (j , []) | refl = refl

-- leaving the frame: the open instant settles (owed never seeded ⇒
-- paid), landing Inv-related for the first arrival
burst-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv 0 sched st S →
  Inv 1 sched st S × (paidUp S ≡ true)
burst-final sched st S binv = inv , paid (BurstInv.current-frame binv)
  where
  past : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       CurrentPast (ProtocolSt.current S) 1
  past (inj₁ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) tt
  past (inj₂ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) (s≤s z≤n)

  paid : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       paidUp S ≡ true
  paid (inj₁ ceq) = paid-nothing S ceq
  paid (inj₂ ceq) = paid-empty S ceq

  inv : Inv 1 sched st S
  inv = record
    { live-matches = BurstInv.live-matches binv
    ; chains-count = BurstInv.chains-count binv
    ; horizon-low  = ≤-up (BurstInv.horizon-low binv)
    ; current-past = past (BurstInv.current-frame binv)
    ; done-plumbed = BurstInv.done-plumbed binv
    }

-- the root subscription, composed (at the budget evaluate seeds)
subscribe-wf :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false →
  Σ ProtocolSt λ S →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in (runProtocol protocol-init (proj₁ r) ≡ just S)
       × Inv 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
       × (paidUp S ≡ true)
subscribe-wf e ins nodry
  with subscribeE-wf (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
                     protocol-init (burst-init e ins) nodry
... | S , run , binv
  with burst-final _ _ S binv
... | inv , paid = S , run , inv , paid

------------------------------------------------------------------
-- one cascade: Mid and its entry/step/exit lemmas, the chain fold
-- composed
------------------------------------------------------------------

-- mid-cascade, CONCRETE, indexed by the chains still to fold.  Two
-- asymmetries a naive "live shadows registry" misses:
--   · for a spent (isLast) arrival the automaton runs AHEAD of the
--     registry — each delivered chain's exhausted close retires its
--     live entry on the spot, but the registry entries drop only at
--     cascadeFinish — so the arrival source's live count equals the
--     obliged remainder of the snapshot, not the registry count;
--   · the owed table exists only once the first chain emit has
--     opened the instant (seeding happens at first delivery), so the
--     ledger is a sum: not-yet-opened (the automaton still stands on
--     the previous, settled instant) or opened with owed[arrSource]
--     = the not-yet-cancelled remainder and every share paid back to
--     zero (a handoff's bump is repaid within its own chainStep).
-- fold-live carries dry-freeness for the remaining fold: Mid's
-- arguments determine every future chainStep, so the premise lives
-- here instead of infecting every step statement
record Mid {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (nextId : Id)
           (ps : List (RegId × Path Γ (arrTy a) t))
           (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    live-others  : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    live-source  : countIn (arrSource a) (ProtocolSt.live S)
      ≡ (if Arrival.isLast a
         then countRemaining ps (EvalSt.cancelled st)
         else countRegs (arrSource a) (EvalSt.registry st))
    chains-count : ∀ (a′ : Arrival Γ) (sched″ : Sched Γ) →
      sched-next sched ≡ inj₂ (a′ , sched″) →
      countRegs (arrSource a′) (EvalSt.registry st) ≡ length (chainsOf a′ st)
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    ledger       :
        (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
      ⊎ (Σ Owed λ ow →
           (ProtocolSt.current S ≡ just (nextId , ow))
         × (lookupOwed (arrSource a) ow
              ≡ countRemaining ps (EvalSt.cancelled st))
         × (zeroExcept (arrSource a) ow ≡ true))
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true
    fold-live    : hasDry (proj₁ (cascadeGo a nextId ps sched st)) ≡ false

postulate
  -- entering: the latch opens the ledger; the automaton, Inv-related
  -- and paid, stands ready to open instant nextId.  The dry-freeness
  -- of the whole cascade fold arrives as a premise (split off
  -- budget-sufficient by the drain composition below)
  mid-init : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
    sched-next sched ≡ inj₂ (a , sched′) →
    Inv nextId sched st S → paidUp S ≡ true →
    hasDry (proj₁ (cascadeGo a nextId (chainsOf a st) sched′
                             (cascadeLatch a st))) ≡ false →
    Mid a nextId (chainsOf a st) sched′ (cascadeLatch a st) S

  -- one surviving chain's emits — the chain emit, any share
  -- fan-outs, any cut closes — are accepted, paying/bumping/
  -- cancelling exactly per the ledger.  THE deep lemma: mirrors
  -- foldPath/dispatchShare/stepFrame (all gas/fuel-structural now).
  -- Mid's eventual definition carries the dry-freeness of the
  -- remaining fold — its arguments determine every future chainStep
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

-- a cancelled head contributes nothing to countRemaining (the `if`
-- takes the then-branch)
cr-skip : ∀ {X : Set} (rid : RegId) (x : X)
          (ps : List (RegId × X)) (c : List RegId) →
          any (_≡ᵇ rid) c ≡ true →
          countRemaining ((rid , x) ∷ ps) c ≡ countRemaining ps c
cr-skip rid x ps c h rewrite h = refl

-- and nothing to cascadeGo: its first clause skips a cancelled head
-- outright, folding the tail with the SAME state (two-column trick —
-- cascadeGo's `with` won't unfold under rewrite)
cascadeGo-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id) (rid : RegId)
  (p : Path Γ (arrTy a) t) (ps : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  cascadeGo {e = e} a nextId ((rid , p) ∷ ps) sched st
    ≡ cascadeGo {e = e} a nextId ps sched st
cascadeGo-skip a nextId rid p ps sched st ceq
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | ceq
... | true | refl = refl

-- a cancelled chain folds to nothing (its close already rode the
-- cutting emit; its owed was forgiven right there): every Mid field is
-- stable when the snapshot head drops, given the head is cancelled
mid-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id} {rid : RegId}
  {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  Mid a nextId ps sched st S
mid-skip {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq = record
  { live-others  = Mid.live-others mid
  ; live-source  = trans (Mid.live-source mid)
      (cong (λ z → if Arrival.isLast a then z
                   else countRegs (arrSource a) (EvalSt.registry st))
            (cr-skip rid p ps (EvalSt.cancelled st) ceq))
  ; chains-count = Mid.chains-count mid
  ; horizon-low  = Mid.horizon-low mid
  ; ledger       = ledger′
  ; done-plumbed = Mid.done-plumbed mid
  ; fold-live    = subst (λ z → hasDry (proj₁ z) ≡ false)
      (cascadeGo-skip a nextId rid p ps sched st ceq)
      (Mid.fold-live mid)
  }
  where
  ledger′ :
      (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
    ⊎ (Σ Owed λ ow →
         (ProtocolSt.current S ≡ just (nextId , ow))
       × (lookupOwed (arrSource a) ow
            ≡ countRemaining ps (EvalSt.cancelled st))
       × (zeroExcept (arrSource a) ow ≡ true))
  ledger′ with Mid.ledger mid
  ... | inj₁ x                    = inj₁ x
  ... | inj₂ (ow , cur , lk , zx) =
        inj₂ (ow , cur
             , trans lk (cr-skip rid p ps (EvalSt.cancelled st) ceq)
             , zx)

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

-- one arrival's cascade, composed.  The dry-freeness premise is
-- stated on the cascade's own emits — definitionally the cascadeGo
-- fold's emits, which is the shape mid-init wants
cascade-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascade a nextId sched′ st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = cascade a nextId sched′ st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Inv (suc nextId) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (paidUp S′ ≡ true)
cascade-wf nextId sched a sched′ st S eq inv paid nodry
  with cascadeGo-wf a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
         (mid-init nextId sched a sched′ st S eq inv paid nodry)
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
  hasDry (drain {e = e} fuel nextId sched st) ≡ false →
  Σ ProtocolSt λ S′ →
    (runProtocol S (drain {e = e} fuel nextId sched st) ≡ just S′)
    × (paidUp S′ ≡ true)
drain-wf zero    nextId sched st S inv paid _  = S , refl , paid
drain-wf (suc k) nextId sched st S inv paid hd with sched-next sched in eq
... | inj₁ _            = S , refl , paid
... | inj₂ (a , sched′)
  -- the with-abstraction has already rewritten hd's type to the
  -- unfolded `cascade emits ++ drain k …` shape — split it there
  with hasDry-++ (proj₁ (cascade a nextId sched′ st))
         (drain k (suc nextId)
           (proj₁ (proj₂ (cascade a nextId sched′ st)))
           (proj₂ (proj₂ (cascade a nextId sched′ st))))
         hd
... | nodry₁ , nodry₂
  with cascade-wf nextId sched a sched′ st S eq inv paid nodry₁
... | S₁ , run₁ , inv₁ , paid₁
  with drain-wf k (suc nextId)
         (proj₁ (proj₂ (cascade a nextId sched′ st)))
         (proj₂ (proj₂ (cascade a nextId sched′ st)))
         S₁ inv₁ paid₁ nodry₂
... | S₂ , run₂ , paid₂ =
  S₂
  , run-++-just S (proj₁ (cascade a nextId sched′ st)) _ run₁ run₂
  , paid₂

-- the reified termination debt: the seeded sync budget never runs
-- dry on a canonical run.  This is the old TERMINATING pragma's
-- claim, now a provable statement — the evaluator is total either
-- way, and QuickCheck's WellFormed check falsifies this postulate at
-- runtime the moment any program exhausts its budget
postulate
  budget-sufficient :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (evaluate fuel e ins) ≡ false

-- the primitives' half of the sandwich: remaining debt is the frame
-- relations, their step lemmas, and budget sufficiency above
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins
  with hasDry-++
         (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e)))
         (drain fuel 1
           (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e))))
           (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e)))))
         (budget-sufficient fuel e ins)
... | nodry₀ , nodry₁
  with subscribe-wf e ins nodry₀
... | S₀ , run₀ , inv₀ , paid₀
  with drain-wf fuel 1
         (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         S₀ inv₀ paid₀ nodry₁
... | S₁ , run₁ , paid₁
  rewrite run-++-just protocol-init
            (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                               (sched-init e ins) (st-init e)))
            (drain fuel 1
              (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e))))
              (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e)))))
            run₀ run₁
  = acceptPaid S₁ paid₁
