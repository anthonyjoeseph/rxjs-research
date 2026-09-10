-- THE DELIVERY MIRROR IS A JOIN OVER TWO LISTS, AND THAT IS THE WHOLE
-- OF WHAT ITS SHAPE HANDS OVER.  A chain's descent folds `⊔` down the
-- PATH, and at a share sink it folds `⊔` across the REGISTRATIONS the
-- share admits; nothing else in the family branches.  So a ceiling on
-- the descent is never established by computing it -- the measure is
-- closed to instantiation, for reasons recorded at the clause that
-- closes it -- but always by an induction whose only content is that
-- some invariant survives one step of the fold.
--
-- SO THE INVARIANT IS A PARAMETER AND NOT A CHOICE MADE HERE.  Both
-- lemmas take the predicate, the per-element bound and the preservation
-- step, exactly as the subscribe side's burst fold does; what they
-- supply is the `⊔`-lub plumbing and the threading, which is the part
-- that is the same whatever the ceiling turns out to be.  Choosing the
-- predicate is the consumer's design decision, and stating these apart
-- from it is what lets that decision move without the induction moving.
--
-- AND THE REGISTRATION FOLD PRESERVES ITS TAIL AT TWO STATES, WHICH IS
-- THE ONE PLACE THIS DIFFERS FROM AN ORDINARY FOLD.  The mirror reports
-- a share's tail at BOTH the entry state and the state the head's own
-- delivery leaves, because a cancelled chain delivers nothing while the
-- survivor delivers at a state the cancelled branch never builds.  A
-- caller therefore owes preservation twice, and the two obligations are
-- genuinely different: one is a weakening down the list, the other is a
-- step across a fold that has run.
module Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Join where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Nat     using (ℕ; zero; suc; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (⊔-lub; ≤-refl)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp   using (Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; RegId; Path; Frame; root; share-sink; _↠_;
         stepFrame; foldPath; shareAdmit; shareLatch)
open import Verify-Budget-Sufficient.Nest-Store using (storeSyncMax)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFold; depthDisp; depthShareGo; depthFrame)

------------------------------------------------------------------
-- THE REGISTRATION FOLD
------------------------------------------------------------------

-- The values and the finish flag are FIXED across the fold, since one
-- share hands the same payload to every chain registered on it; what
-- varies is the path, the state and the schedule.  Fixing them is what
-- keeps the element bound stateable at all -- a chain's own path comes
-- out of the registry, so nothing outside the list names it.
shareGo-le : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (C : ℕ)
  (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (Q : List (RegId × Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e → Set) →
  (∀ (rid : RegId) (p : Path Γ (lookup Γ i) t)
     (ps : List (RegId × Path Γ (lookup Γ i) t))
     (sch : Sched Γ) (sto : EvalSt e) → Q ((rid , p) ∷ ps) sch sto →
     depthFold sf gas bid now (toℕ i) p vals
       (if fin then close (toℕ i) exhausted ∷ [] else []) fin sch
       (record sto { delivered = rid ∷ EvalSt.delivered sto }) ≤ C) →
  (∀ (rid : RegId) (p : Path Γ (lookup Γ i) t)
     (ps : List (RegId × Path Γ (lookup Γ i) t))
     (sch : Sched Γ) (sto : EvalSt e) → Q ((rid , p) ∷ ps) sch sto →
     Q ps sch sto) →
  (∀ (rid : RegId) (p : Path Γ (lookup Γ i) t)
     (ps : List (RegId × Path Γ (lookup Γ i) t))
     (sch : Sched Γ) (sto : EvalSt e) → Q ((rid , p) ∷ ps) sch sto →
     Q ps (proj₁ (proj₂ (foldPath sf gas bid now (toℕ i) p vals
                          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sch
                          (record sto { delivered = rid ∷ EvalSt.delivered sto }))))
          (proj₂ (proj₂ (foldPath sf gas bid now (toℕ i) p vals
                          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sch
                          (record sto { delivered = rid ∷ EvalSt.delivered sto }))))) →
  ∀ (ps : List (RegId × Path Γ (lookup Γ i) t)) (sch : Sched Γ) (sto : EvalSt e) →
  Q ps sch sto →
  depthShareGo sf gas bid now i vals fin ps sch sto ≤ C
shareGo-le C sf gas bid now i vals fin Q hb h0 h1 []              sch sto q = z≤n
shareGo-le C sf gas bid now i vals fin Q hb h0 h1 ((rid , p) ∷ ps) sch sto q =
  ⊔-lub (shareGo-le C sf gas bid now i vals fin Q hb h0 h1 ps sch sto
           (h0 rid p ps sch sto q))
        (⊔-lub (hb rid p ps sch sto q)
               (shareGo-le C sf gas bid now i vals fin Q hb h0 h1 ps _ _
                  (h1 rid p ps sch sto q)))

------------------------------------------------------------------
-- THE DISPATCH
------------------------------------------------------------------

-- THE PREMISES ARE ASKED AT A STRICTLY SMALLER GAS, AND THE BOUND IS
-- WHAT MAKES THE PAIR WALKABLE.  The dispatch peels one unit before
-- entering the fold, so the only gas it ever reads a fold at is below
-- the one it was entered at; a premise quantified over EVERY gas says
-- the same thing about this lemma and hides that peel from every
-- caller, which is fatal for the one caller that matters.  The fold's
-- own sink arm is a dispatch at the gas the fold holds, so fold and
-- dispatch recur through each other, and the cycle terminates only
-- because the dispatch descends.  With the descent absent from the
-- type there is no measure the pair can share and the arm cannot be
-- written at all; with it present the caller has an ordering in scope
-- and the recursion is an ordinary walk down the gas.  Costing the
-- caller nothing is what makes it free to state: a consumer proving
-- the element bound at every gas proves it at a smaller one.
disp-le : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (C : ℕ)
  (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (Q : List (RegId × Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e → Set) →
  (∀ (g : ℕ) → g < gas → ∀ (rid : RegId) (p : Path Γ (lookup Γ i) t)
     (ps : List (RegId × Path Γ (lookup Γ i) t))
     (sch : Sched Γ) (sto : EvalSt e) → Q ((rid , p) ∷ ps) sch sto →
     depthFold sf g bid now (toℕ i) p vals
       (if fin then close (toℕ i) exhausted ∷ [] else []) fin sch
       (record sto { delivered = rid ∷ EvalSt.delivered sto }) ≤ C) →
  (∀ (rid : RegId) (p : Path Γ (lookup Γ i) t)
     (ps : List (RegId × Path Γ (lookup Γ i) t))
     (sch : Sched Γ) (sto : EvalSt e) → Q ((rid , p) ∷ ps) sch sto →
     Q ps sch sto) →
  (∀ (g : ℕ) → g < gas → ∀ (rid : RegId) (p : Path Γ (lookup Γ i) t)
     (ps : List (RegId × Path Γ (lookup Γ i) t))
     (sch : Sched Γ) (sto : EvalSt e) → Q ((rid , p) ∷ ps) sch sto →
     Q ps (proj₁ (proj₂ (foldPath sf g bid now (toℕ i) p vals
                          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sch
                          (record sto { delivered = rid ∷ EvalSt.delivered sto }))))
          (proj₂ (proj₂ (foldPath sf g bid now (toℕ i) p vals
                          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sch
                          (record sto { delivered = rid ∷ EvalSt.delivered sto }))))) →
  ∀ (sch : Sched Γ) (sto : EvalSt e) →
  Q (shareAdmit i (EvalSt.registry sto)) sch (shareLatch i fin sto) →
  depthDisp sf gas bid now i vals fin sch sto ≤ C
disp-le C sf zero      bid now i vals fin Q hb h0 h1 sch sto q = z≤n
disp-le C sf (suc gas) bid now i vals fin Q hb h0 h1 sch sto q =
  shareGo-le C sf gas bid now i vals fin Q (hb gas ≤-refl) h0 (h1 gas ≤-refl)
    _ sch _ q

-- AND THE LATCH IS INVISIBLE TO THE STORE, which is what lets a
-- consumer state the dispatch's ceiling at the state it was ENTERED
-- at rather than at the one the fold runs on.  The latch writes the
-- completion and dying lists; the synchronous store reads slots, nodes
-- and registry, and none of those three is a place the latch touches.
latch-sync : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  storeSyncMax sched (shareLatch i fin st) ≡ storeSyncMax sched st
latch-sync i false sched st = refl
latch-sync i true  sched st = refl

------------------------------------------------------------------
-- THE PATH FOLD
------------------------------------------------------------------

-- THE PREDICATE READS THE PATH AS WELL AS THE STATE, and it has to:
-- the values a frame hands on are the ones IT built, so nothing outside
-- the descent bounds them, and a bound asked for at an arbitrary value
-- list is a bound nobody can supply.  The path index is what lets the
-- two leaf obligations be stated at the two heads that have them --
-- a frame's own spend, and a share sink's dispatch -- rather than
-- uniformly at every position.
fold-le : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (C : ℕ)
  (sf : Gas) (gas : ℕ) (bid : Id) (now : Tick) (envSrc : Source)
  (P : ∀ {v} → Path Γ v t → List (Val Γ v) → Bool → Sched Γ → EvalSt e → Set) →
  (∀ {s v} (f : Frame Γ s v) (p′ : Path Γ v t) (vals : List (Val Γ s))
     (fin : Bool) (sch : Sched Γ) (sto : EvalSt e) → P (f ↠ p′) vals fin sch sto →
     depthFrame sf bid now f p′ vals fin sch sto ≤ C) →
  (∀ (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
     (sch : Sched Γ) (sto : EvalSt e) → P (share-sink i) vals fin sch sto →
     depthDisp sf gas bid now i vals fin sch sto ≤ C) →
  (∀ {s v} (f : Frame Γ s v) (p′ : Path Γ v t) (vals : List (Val Γ s))
     (fin : Bool) (sch : Sched Γ) (sto : EvalSt e) → P (f ↠ p′) vals fin sch sto →
     P p′ (proj₁ (stepFrame sf bid now f p′ vals fin sch sto))
          (proj₁ (proj₂ (proj₂ (stepFrame sf bid now f p′ vals fin sch sto))))
          (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf bid now f p′ vals fin sch sto)))))
          (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf bid now f p′ vals fin sch sto)))))) →
  ∀ {v} (p : Path Γ v t) (vals : List (Val Γ v))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sch : Sched Γ) (sto : EvalSt e) → P p vals fin sch sto →
  depthFold sf gas bid now envSrc p vals evs fin sch sto ≤ C
fold-le C sf gas bid now envSrc P hf hd hp root           vals evs fin sch sto h = z≤n
fold-le C sf gas bid now envSrc P hf hd hp (share-sink i) vals evs fin sch sto h =
  hd i vals fin sch sto h
fold-le C sf gas bid now envSrc P hf hd hp (f ↠ p′)       vals evs fin sch sto h =
  ⊔-lub (hf f p′ vals fin sch sto h)
        (fold-le C sf gas bid now envSrc P hf hd hp p′
           (proj₁ r) (evs ++ proj₁ (proj₂ r))
           (proj₁ (proj₂ (proj₂ r)))
           (proj₁ (proj₂ (proj₂ (proj₂ r))))
           (proj₂ (proj₂ (proj₂ (proj₂ r))))
           (hp f p′ vals fin sch sto h))
  where r = stepFrame sf bid now f p′ vals fin sch sto
