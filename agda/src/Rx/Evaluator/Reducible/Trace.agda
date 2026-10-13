------------------------------------------------------------------
-- THE TRACE A SUBSCRIBE ANSWERS WITH, AND WHERE IT ENDS.  A module of
-- its own because it is the one family the oracle must build LAZY:
-- each call it records carries the answer the fold gave, and a strict
-- trace builds every call and answer it records where a run reads
-- only the ones it needs.  The strictness pragma is per module, so the
-- strict families on either side of it -- the continuation's records
-- beneath, the stage records above -- sit in
-- `Rx.Evaluator.Reducible.Support` and
-- `Rx.Evaluator.Reducible.Candidate`.
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Trace where

open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ)
open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Data.Unit using () renaming (tt to tt₀)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Evaluator using (Path)
open import Rx.Evaluator.Reducible.Support using (Pre; standing; fallen; Call; RP; Ans; Answered; joinPre; next)

-- THE TRACE: THE CALLS A SUBSCRIBE MADE TO ITS CONTINUATION, IN ORDER,
-- EACH TYPED AGAINST THE SUCCESSOR THE ONE BEFORE IT ANSWERED WITH.
-- Each call carries its answer, which IS the fold applied to it, by the
-- equation it carries, so a subscribe answers with the trace and
-- nothing else about its continuation, and reading where it ended
-- re-runs nothing.  A frame arm
-- translates its source's trace through the frame it pushed, call by
-- call, and the translation's end is the successor of the continuation
-- it was handed -- which is what the exit frame's peel used to do.
--
-- AND THE TRACE STOPS WHERE THE PATH FELL.  A connect never calls the
-- continuation it was handed -- the trigger receives the definition's
-- values through the row it registered, folded raw -- and every fold
-- above a fall reads the store and calls nothing it closed over, so
-- there is no successor to compute past that point.  `fellᵗ` records
-- the fallen continuation the fall left and the state it was threaded,
-- so a frame that goes on calling after its source fell has a fold to
-- call and a trace to append; the arm above still owes the fall
-- itself, as the ground its answer ends on.
data Trace {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
           (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t)
         : (pre : Pre κ) → RP {e = e} m P S κ pre → S → Set₁ where
  []ᵗ   : ∀ {pre rp s} → Trace m P S κ pre rp s
  fellᵗ : ∀ {pre rp s} → RP {e = e} m P S κ fallen → S → Trace m P S κ pre rp s
  _∷ᵗ_  : ∀ {pre rp s} {c : Call {e = e} m P κ pre} (a : Answered rp s c)
        → Trace m P S κ (Ans.pre′ (Answered.an a)) (next (Answered.an a)) (Ans.s′ (Answered.an a))
        → Trace m P S κ pre rp s

-- where a trace ends: the ground it left the path on
endPre : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
         {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
       → Trace {e = e} m P S κ pre rp s → Pre κ
endPre {pre = pre} []ᵗ = pre
endPre (fellᵗ _ _)     = fallen
endPre (c ∷ᵗ tr)       = endPre tr

-- the continuation it left standing there, and the state
endRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
        {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
      → (tr : Trace {e = e} m P S κ pre rp s) → RP {e = e} m P S κ (endPre tr)
endRP {rp = rp} []ᵗ = rp
endRP (fellᵗ rp′ _) = rp′
endRP (c ∷ᵗ tr)     = endRP tr

endS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
       {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
     → Trace {e = e} m P S κ pre rp s → S
endS {s = s} []ᵗ  = s
endS (fellᵗ _ s′) = s′
endS (c ∷ᵗ tr)    = endS tr

-- ONE TRACE AFTER ANOTHER: the second picks up where the first ended,
-- and nothing is recorded past a fall -- whether the first fell, or
-- began on fallen ground and made no call.  A call made to a fallen
-- continuation is a fold of the store and computes no successor, so
-- the record has nothing to say about it.
_++ᵗ_ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
        {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
      → (tr : Trace {e = e} m P S κ pre rp s)
      → Trace {e = e} m P S κ (endPre tr) (endRP tr) (endS tr)
      → Trace {e = e} m P S κ pre rp s
fellᵗ rp′ s′ ++ᵗ _   = fellᵗ rp′ s′
(c ∷ᵗ tr)    ++ᵗ tr′ = c ∷ᵗ (tr ++ᵗ tr′)
_++ᵗ_ {pre = standing _} []ᵗ tr′ = tr′
_++ᵗ_ {pre = fallen}     []ᵗ tr′ = []ᵗ

end-++ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
         {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
       → (tr : Trace {e = e} m P S κ pre rp s)
       → (tr′ : Trace {e = e} m P S κ (endPre tr) (endRP tr) (endS tr))
       → endPre (tr ++ᵗ tr′) ≡ joinPre (endPre tr) (endPre tr′)
end-++ (fellᵗ _ _)  tr′ = refl
end-++ (c ∷ᵗ tr)    tr′ = end-++ tr tr′
end-++ {pre = standing _} []ᵗ tr′ = refl
end-++ {pre = fallen}     []ᵗ tr′ = refl
