-- ══════════════════════════════════════════════════════════════════
-- THE SQUARING REACHES THE VALUE SIDE TOO, so the descent's whole
-- denomination is refuted and not merely its store half.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT CLAIMS.  What ONE subscription DELIVERS -- the
-- sync half of the burst it hands back -- carries values no larger
-- than `iterSize S (layᵉ o + slotsSize sl) B`, where `B` bounds the
-- program's own syntax.  It reads no table and it is a function of the
-- program alone, which is exactly why it was the last reading that
-- could have survived: nothing here is about what a fold left behind.
--
-- WHERE IT BREAKS, AND IT IS THE SAME MECHANISM ONE READING OVER.  A
-- `μ` is subscribed by unfolding it, and unfolding plants a copy of
-- the whole program at every mention of the recursive occurrence.
-- `layᵉ` charges nothing for the `μ` and nothing under the `defer`
-- those mentions must stand under, so the rung count is FIXED before
-- the number of mentions is chosen -- and a rung is affine in the
-- bound, so a fixed count buys a fixed factor.  The copies are a
-- multiplicity, and a factor does not cover one.
--
-- WHAT MAKES IT A VALUE READING RATHER THAN A STORE ONE.  The copies
-- are not parked here: the unfolded program is a one-shot source whose
-- single emission IS the deferred subtree the copies sit in, so the
-- squared syntax is handed back in the burst.  That is why no cell has
-- to be hand-built and why nothing about a door, a limit or a queue
-- can be carrying the failure -- there is no door and no queue, only
-- `subscribeE` at `root` entered on an empty table.
--
-- WHAT IT LEAVES.  The two halves of this descent share one charge and
-- both are now refuted at the same edge, so the repair is one repair:
-- the level cannot be handed to the statement by the syntax, and has
-- to be quantified over the way the caps face already quantifies its
-- frame steps when it prices an unfold.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Sz-Mu where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; hot; Tick; Id)
open import Rx.Exp using (Ctx; Exp; Tm; Closed; Val; natᵗ; obs;
  emptyᵉ; ofᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ; strmᵗ; sizeᵉ; sizeᵛ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; st-init;
  sched-init; subscribeE; splitBurst; iterSize)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.  The reading it is denominated in is the real one.
----------------------------------------------------------------------
SubscribeESz : Set
SubscribeESz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (o : Closed Γ u) (κ : Path Γ u t) (id : Id)
  (now : Tick) (sched : Sched Γ) (st : EvalSt e)
  (S B : ℕ) → 2 ≤ S → (sizeᵉ o ≤ᵇ B) ≡ true →
  valsSz? (iterSize S (layᵉ o + slotsSize (Sched.slots sched)) B)
    (proj₁ (splitBurst {A = Val Γ t}
      (proj₁ (subscribeE g o κ id now sched st))))
    ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `bodyAt k` emits ONE value, and that value is a
-- deferred subtree mentioning the μ-var `k` times -- the defer being
-- both what the guard demands and what keeps the emission a single
-- value rather than `k` of them, so the reading cannot join them away.
----------------------------------------------------------------------
Γ : Ctx 1
Γ = natᵗ ∷ⱽ []ⱽ

sl : Slots Γ
sl fzero = scripted (hot [])

musO : (j : ℕ) → List (Tm Γ [] (obs natᵗ ∷ []) [] (obs natᵗ))
musO zero    = []
musO (suc j) = strmᵗ (mergeAllᵉ nothing (varᵉ (here refl))) ∷ musO j

bigAt : (k : ℕ) → Exp Γ [] (obs natᵗ ∷ []) [] natᵗ
bigAt k = mergeAllᵉ nothing (ofᵉ (musO k))

bodyAt : (k : ℕ) → Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
bodyAt k = ofᵉ (strmᵗ (deferᵉ (bigAt k)) ∷ [])

oAt : (k : ℕ) → Closed Γ (obs natᵗ)
oAt k = μᵉ (bodyAt k)

e₀ : Closed Γ (obs natᵗ)
e₀ = emptyᵉ

outAt : (k : ℕ) → List (Val Γ (obs natᵗ))
outAt k = proj₁ (splitBurst {A = Val Γ (obs natᵗ)}
            (proj₁ (subscribeE (gasPad 64 g0) (oAt k) root 0 0
                      (sched-init e₀ sl) (st-init e₀))))

Mval : ℕ → ℕ
Mval k = iterSize 2 (layᵉ (oAt k) + slotsSize sl) (sizeᵉ (oAt k))

----------------------------------------------------------------------
-- THE FIGURES, READ ON BOTH SIDES OF THE CROSSING.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the whole mechanism in six numbers.  The layer
-- count is ZERO at both lengths -- a defer cuts it and a `μ` adds
-- nothing -- so the charge is the empty telescope's single rung and it
-- does not move when the copies do, while the program's own syntax
-- grows by three per mention.  A count that saw the copies would not
-- report the same zero twice.
figures : List ℕ
figures = layᵉ (oAt 3) ∷ sizeᵉ (oAt 3) ∷ Mval 3
        ∷ layᵉ (oAt 4) ∷ sizeᵉ (oAt 4) ∷ Mval 4 ∷ slotsSize sl ∷ []

figures≡ : figures ≡ 0 ∷ 17 ∷ 70 ∷ 0 ∷ 20 ∷ 82 ∷ 1 ∷ []
figures≡ = refl

-- LOAD-BEARING: the run DELIVERS, and it delivers ONE value.  An empty
-- burst would make the conclusion hold on nothing, and `k` separate
-- emissions would be joined rather than summed -- what is measured
-- here is a single value carrying every copy.
delivered : List ℕ
delivered = length (outAt 3) ∷ length (outAt 4) ∷ []

delivered≡ : delivered ≡ 1 ∷ 1 ∷ []
delivered≡ = refl

-- LOAD-BEARING: the sizes against the charges above.  Sixty-one under
-- seventy, then ninety-two over eighty-two -- the delivered syntax is
-- QUADRATIC in the mentions where the charge is linear in them, so the
-- gap opens rather than being a constant that a bigger count absorbs.
sizes : List ℕ
sizes = map (sizeᵛ {Γ = Γ} (obs natᵗ)) (outAt 3)
     ++ map (sizeᵛ {Γ = Γ} (obs natᵗ)) (outAt 4)

sizes≡ : sizes ≡ 61 ∷ 92 ∷ []
sizes≡ = refl

----------------------------------------------------------------------
-- THE WITNESS.  Entered at `root` on the initial table, so nothing is
-- hand-built and no frame stands between the subscription and what it
-- hands back.
----------------------------------------------------------------------
valRow : ℕ → Bool
valRow k = valsSz? {Γ = Γ} {s = obs natᵗ} (Mval k) (outAt k)

-- LOAD-BEARING, and it brackets the crossing rather than exhibiting
-- one side of it.  One mention fewer and the claim HOLDS at the very
-- same rungs, so what fails is the multiplicity and not the gas, the
-- telescope, or the arithmetic of `iterSize`.
valRows : List Bool
valRows = valRow 3 ∷ valRow 4 ∷ []

valRows≡ : valRows ≡ true ∷ false ∷ []
valRows≡ = refl

subscribeE-sz-absurd : SubscribeESz → ⊥
subscribeE-sz-absurd pr =
  f≡t (trans (sym valRow4≡false)
             (pr {e = e₀} (gasPad 64 g0) (oAt 4) root 0 0
                 (sched-init e₀ sl) (st-init e₀) 2 (sizeᵉ (oAt 4))
                 (s≤s (s≤s z≤n)) refl))
  where
    valRow4≡false : valRow 4 ≡ false
    valRow4≡false = refl
