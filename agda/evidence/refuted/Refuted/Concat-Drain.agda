-- ══════════════════════════════════════════════════════════════════
-- CONCAT'S DRAIN: the shared-bud receipt, as stated, is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT IS WRONG, AND IT IS NOT THE WITNESS.  The row's pin is sound: the
-- second conjunct really does stop the Σ being upward-closed in `bud`, so
-- the free large witness is gone.  The defect is one level out.  The
-- ceiling conjunct compares a cap derived from `c` against
-- `sizeCapAt e sl (suc id)`, and NOTHING in the hypotheses relates the
-- two: `OKB` unfolds to a slots equation and `capsOK? (frameStep J c)`,
-- both of which get EASIER as `c` grows, while `sizeCapAt` reads only
-- `e` and `sl`.  So take `c` with `cSize c = suc (sizeCapAt e sl 1)` and
-- the conjunct is unsatisfiable at EVERY bud — the witness never gets a
-- chance to matter, and the queue's contents never do either.
--
-- CLAUDE.md's first almost-always-wrong shape: a conclusion needing
-- information that appears in NO hypothesis.  So the repair is a
-- RESTATEMENT, and this refutation is what licenses it — the fact that
-- today's only caller happens to have the tie in scope would not be.
--
-- WHICH HYPOTHESIS.  `concatDrain-nodry`, the sole consumer, carries
-- exactly the missing tie one argument along from the call it does not
-- pass it to:
--
--   Caps.cSize (frameStep (fLvlD (cSize c) (cWid c) dep J) c)
--     ≤ sizeCapAt e sl (suc id)
--
-- and beside it `VbB c sl Ψ J q ≡ true`, which the same consumer already
-- argues (in its own header) is a genuine precondition rather than a
-- convenience.  Both are needed and for different conjuncts: the tie for
-- the ceiling, the queue receipt to bound `nest` per element — a free
-- `Closed Γ s` list has no nest bound at all, which is the retired
-- `concatDrain-nodry-vb`'s defect arriving at the second conjunct.
--
-- NOTE WHAT THIS DOES NOT SHOW.  Nothing here says the CONDITIONED form
-- is true.  With the tie in hand the ceiling conjunct still needs
-- `opIterD S W dep bud (suc (sizeᵉ o)) (suc J) ≤ fLvlD S W dep J` — the
-- arithmetic the postulate's own header defers to a separate leaf — and
-- that is a bound on the WITNESS, so the two conjuncts are then in real
-- tension.  That tension is the row's remaining content.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Concat-Drain where

open import Data.Bool using (true)
open import Data.Nat  using (ℕ; suc; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-trans; ≤ᵇ⇒≤; 1+n≰n; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; _,_; _×_; Σ)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id)
open import Rx.Exp  using (Ctx; Closed; Val; obs; natᵗ; ofᵉ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; sched-init; st-init;
                               opIterD)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Nest using (nest)
open import Verify-Budget-Sufficient.Measures using (∧-true)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using (cSize≤frameStep)
open import Verify-Budget-Sufficient.Wet.Part6 using (sizeCapAt; 2≤sizeCapAt)
open import Verify-Budget-Sufficient.Burst-Walk using (OKB)
open import Decide using (T-to)

----------------------------------------------------------------------
-- THE WITNESS.  The empty context, so every list in the state and the
-- schedule is empty and OKB holds by computation at ANY caps; and a
-- caps triple whose size is one past the cap the conclusion measures
-- against.  Nothing about the queue is load-bearing — one element is
-- needed only because `all p [] = true`.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

sl₀ : Slots Γ₀
sl₀ = λ ()

e₀ : Closed Γ₀ natᵗ
e₀ = ofᵉ (nat̂ 1 ∷ [])

N : ℕ
N = sizeCapAt e₀ sl₀ 1

c₀ : Caps
c₀ = caps (suc N) 1 1

2≤c₀ : 2 ≤ Caps.cSize c₀
2≤c₀ = ≤-trans (2≤sizeCapAt e₀ sl₀ 1) (n≤1+n N)

----------------------------------------------------------------------
-- THE DEFECT, in one chain: `cSize` never shrinks along `frameStep`
-- (`cSize≤frameStep`), so whatever level the witness picks, the ceiling
-- conjunct is at least `cSize c₀ = suc N` against `N`.
----------------------------------------------------------------------

concatDrain-nodry-nestBud-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
     (c : Caps) (sl : Slots Γ) (Ψ dep J : ℕ) (id : Id) (allNid : NodeId)
     (q : List (Closed Γ s))
     (sched : Sched Γ) (st : EvalSt e) →
     OKB {e = e} c sl Ψ J sched st →
     Σ ℕ (λ bud →
            all (λ o → nest o sl (EvalSt.connectedShares st) ≤ᵇ bud) q ≡ true
          × all (λ o → Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c)
                                                      dep bud (suc (sizeᵉ o)) (suc J)) c)
                          ≤ᵇ sizeCapAt e sl (suc id)) q ≡ true))
  → ⊥
concatDrain-nodry-nestBud-absurd nb
  with nb {e = e₀} c₀ sl₀ 0 0 0 0 0 (e₀ ∷ []) (sched-init e₀ sl₀) (st-init e₀)
          ((refl , refl) , refl)
... | bud , _ , clQ = 1+n≰n (≤-trans (cSize≤frameStep c₀ K 2≤c₀) fits)
  where
  K : ℕ
  K = opIterD (Caps.cSize c₀) (Caps.cWid c₀) 0 bud (suc (sizeᵉ e₀)) 1

  fits : Caps.cSize (frameStep K c₀) ≤ N
  fits = ≤ᵇ⇒≤ (Caps.cSize (frameStep K c₀)) N
           (T-to (proj₁ (∧-true (Caps.cSize (frameStep K c₀) ≤ᵇ N) true clQ)))

----------------------------------------------------------------------
-- THE MIRROR HAS THE SAME DEFECT, AND IT WAS THE PRECEDENT.  The concat
-- row was pinned by copying `thruConsume-nodry-nestBud`'s two-conjunct Σ
-- — which is the right shape — but the thru side takes OKB alone too, so
-- what got copied was the defect along with the pin.  Same witness, and
-- one step shorter: the conjunct is a bare `≤`, so nothing has to be
-- projected out of an `all`.
--
-- IT WAS CLASSED GRINDABLE, which is the part worth recording: the class
-- means "the shape is already known, only the typing is left", and a
-- worked precedent was named — the precedent being this row's own twin,
-- with the identical hole.  A precedent audit that compares Σ shapes and
-- not TELESCOPES certifies both halves of a false pair.
----------------------------------------------------------------------

thruConsume-nodry-nestBud-absurd :
  (∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
     (c : Caps) (sl : Slots Γ) (Ψ dep J : ℕ) (id : Id)
     (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
     (sched : Sched Γ) (st : EvalSt e) →
     OKB {e = e} c sl Ψ J sched st →
     Σ ℕ (λ bud → nest o sl (EvalSt.connectedShares st) ≤ bud
                  × Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c)
                                                   dep bud (suc (sizeᵉ o)) (suc J)) c)
                      ≤ sizeCapAt e sl (suc id)))
  → ⊥
thruConsume-nodry-nestBud-absurd nb
  with nb {u = natᵗ} {e = e₀} c₀ sl₀ 0 0 0 0 e₀ [] (sched-init e₀ sl₀) (st-init e₀)
          ((refl , refl) , refl)
... | bud , _ , fits =
  1+n≰n (≤-trans (cSize≤frameStep c₀
                    (opIterD (Caps.cSize c₀) (Caps.cWid c₀) 0 bud (suc (sizeᵉ e₀)) 1)
                    2≤c₀)
                 fits)

----------------------------------------------------------------------
-- CHECKED THE DECISIVE WAY, then reverted: with both
-- postulates imported from `src` and APPLIED to the two witnesses above,
-- `_ : ⊥` typechecked.  So this is not a mismatch between a transcribed
-- type and the real one — `src` proved falsity, and the restatement that
-- followed is what stopped it.  The application is not kept: an
-- inhabitant of ⊥ in a checked tree makes every later refutation here
-- worthless, which is the one thing this tree cannot afford.
----------------------------------------------------------------------
