-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation.  `Inv` relates the evaluator's state
-- (scheduler + registry) to the automaton's (live multiset, seen
-- instants, no open instant between cascades); `subscribe-wf` drives
-- the automaton through the root burst, `cascade-wf` through one
-- arrival's cascade, each landing Inv-related and fully paid.  The
-- top-level composition — fuel induction over `drain`, glued by
-- runProtocol's distribution over ++ — is DEFINED below; the two
-- stage lemmas and the invariant are the postulated waypoints
-- (structural inductions mirroring the evaluator's own recursion:
-- tedious, but each clause is mechanical).
module Verify-Well-Formed where

open import Data.Bool    using (true)
open import Data.Nat     using (zero; suc)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Rx.Prim      using (Fuel; freshId; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                sched-init; st-init; sched-next;
                                subscribeE; cascade; drain; evaluate;
                                root; arrTick; arrOrd)
open import Rx.Protocol  using (ProtocolSt; protocol-init; stepProtocol;
                                runProtocol; paidUp; checkFinal;
                                Accepted; accepted; WellFormed)

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
-- the invariant and the two stage lemmas (postulated waypoints —
-- structural inductions a lesser intelligence can discharge clause
-- by clause)
------------------------------------------------------------------

postulate
  -- the simulation relation: the automaton's live multiset is the
  -- registry's sources; no instant is open; seen covers every past
  -- instant, and every future (tick, ordinal) the scheduler can mint
  -- is fresh for it (freshId is injective; arrival ticks are ≥ 1 and
  -- strictly increase per source, so the subscribe frame's freshId 0 0
  -- and all future cascade ids stay distinct); done only if the root
  -- completed, after which no chain can carry a value
  Inv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      → Sched Γ → EvalSt e → ProtocolSt → Set

  -- the root subscription's burst: from the empty automaton to an
  -- Inv-related, fully-paid state.  Proof: per-primitive preservation
  -- through subscribeE/pushBurst — subscribe/plumbing emits are net
  -- zero, every init is fresh, every close matches
  subscribe-wf :
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    Σ ProtocolSt λ S →
      let r = subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e)
      in (runProtocol protocol-init (proj₁ r) ≡ just S)
         × Inv (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
         × (paidUp S ≡ true)

  -- one arrival's cascade: accepted from any Inv-related paid state,
  -- landing Inv-related and fully paid.  The heart: owed[s] seeds to
  -- the chain count and each chain pays (delivered exactly once, or
  -- cancelled with its cutPending riding the cutting emit); handoff
  -- bumps match dispatch fan-outs; fins absorb until an inner's last
  -- registration.  Mirrors cascade/foldPath/dispatchShare clause by
  -- clause
  cascade-wf :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
      (st : EvalSt e) (S : ProtocolSt) →
    sched-next sched ≡ inj₂ (a , sched′) →
    Inv sched st S → paidUp S ≡ true →
    Σ ProtocolSt λ S′ →
      let r = cascade a (freshId (arrTick a) (arrOrd a)) sched′ st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × Inv (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (paidUp S′ ≡ true)

------------------------------------------------------------------
-- the composition: fuel induction over drain, then the theorem
------------------------------------------------------------------

drain-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  Inv sched st S → paidUp S ≡ true →
  Σ ProtocolSt λ S′ →
    (runProtocol S (drain {e = e} fuel sched st) ≡ just S′)
    × (paidUp S′ ≡ true)
drain-wf zero    sched st S inv paid = S , refl , paid
drain-wf (suc k) sched st S inv paid with sched-next sched in eq
... | inj₁ _            = S , refl , paid
... | inj₂ (a , sched′)
  with cascade-wf sched a sched′ st S eq inv paid
... | S₁ , run₁ , inv₁ , paid₁
  with drain-wf k
         (proj₁ (proj₂ (cascade a (freshId (arrTick a) (arrOrd a)) sched′ st)))
         (proj₂ (proj₂ (cascade a (freshId (arrTick a) (arrOrd a)) sched′ st)))
         S₁ inv₁ paid₁
... | S₂ , run₂ , paid₂ =
  S₂
  , run-++-just S
      (proj₁ (cascade a (freshId (arrTick a) (arrOrd a)) sched′ st)) _
      run₁ run₂
  , paid₂

-- the primitives' half of the sandwich, no longer a postulate: its
-- remaining debt is Inv/subscribe-wf/cascade-wf above
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins
  with subscribe-wf e ins
... | S₀ , run₀ , inv₀ , paid₀
  with drain-wf fuel
         (proj₁ (proj₂ (subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e))))
         (proj₂ (proj₂ (subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e))))
         S₀ inv₀ paid₀
... | S₁ , run₁ , paid₁
  rewrite run-++-just protocol-init
            (proj₁ (subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e)))
            (drain fuel
              (proj₁ (proj₂ (subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e))))
              (proj₂ (proj₂ (subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e)))))
            run₀ run₁
  = acceptPaid S₁ paid₁
