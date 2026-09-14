-- THE TOP-LINE DRY CLAIM IS FALSE, AND IT IS FALSE AT FOUR LINES OF
-- ORDINARY RXJS.
--
-- `evaluate` concatenates a root burst with a drain, and the root burst
-- is the subscription walk entered at the triple the program itself
-- reads.  The rank component of that triple is the observable NESTING, a
-- count of written `strmᵗ` heads, and the hop guard spends it against
-- the nesting of whatever inner is handed to a flattener.  The two are
-- not comparable, and the gap is not a slack a larger seed closes:
-- substituting a value of observable type into a template goes through
-- `reify`, which AT THAT TYPE IS `strmᵗ`, so the instance is written one
-- deeper than the template it came from, while every clause of the
-- nesting measure JOINS its children.  A template that wraps its
-- argument therefore hands out an inner the entry has already been shown
-- not to dominate, the guard refuses to descend, and the run reports the
-- dry close.
--
-- THE SECOND WITNESS IS WHAT SAYS NO CLAUSE REPAIRS IT.  Summing the map
-- clause rather than joining it closes the first program strictly, since
-- a `mapᵉ` applies its template once per value and the instance is one
-- deeper than the template exactly once.  A fold re-applies its step to
-- its OWN accumulator, so a step that re-wraps deepens once per
-- DELIVERY, and the gap is then the delivery count — which no reading of
-- the syntax carries, and which lengthening the source moves while
-- leaving the program's own reading fixed.
--
-- WHAT THIS KILLS IS THE SEED DOING TWO JOBS, NOT THE DESCENT.  The
-- nesting orders the recursion correctly: it is a fact about the term,
-- every subterm reads under it by one projection of a join, and that is
-- what made the entry side definitional at every constructor.  It is
-- only the second job — bounding what the walk may READ — that no
-- syntactic figure can do, because a reading prices what a subtree will
-- EMIT.  So the repair the two witnesses force is a reading quantified
-- BESIDE the rank rather than read off it, and neither witness touches
-- the descent that the rank was introduced for.
module Refuted.Dry-Wrap where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; varᵗ; fstᵗ)
open import Rx.Slots using (Slots)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Evaluator using (evaluate; hasDry)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT HERE RATHER THAN IMPORTED.  `src` declares
-- a definition of exactly this type, so what the witnesses below report
-- is that one of the leaves that body stands on is false — but a
-- refutation that APPLIED that definition would be evidence about
-- whatever it says today, and this one is evidence about the form it was
-- taken against.  A repair that moves the entry seeding makes the rows
-- below fail to typecheck rather than quietly agreeing with it.
----------------------------------------------------------------------

RankSufficient : Set
RankSufficient =
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE FIRST WITNESS — `of(EMPTY).pipe(map(x => of(x)), mergeAll())`.
-- The template's argument is of observable type and the template WRAPS
-- it, so the value the flattener is handed is written one `strmᵗ` deeper
-- than anything the program's own text shows.
----------------------------------------------------------------------

wrap : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
wrap = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

src : Closed Γ₀ (obs natᵗ)
src = ofᵉ (strmᵗ emptyᵉ ∷ [])

p : Closed Γ₀ (obs natᵗ)
p = mergeAllᵉ nothing (mapᵉ wrap src)

----------------------------------------------------------------------
-- THE SECOND — `of(EMPTY,EMPTY,EMPTY).pipe(scan((a,_) => of(a), EMPTY),
-- mergeAll())`.  The step re-wraps its own accumulator, so the values
-- this hands out nest once, twice and three times against a reading
-- taken of the program as written.  It is claimed beside the first
-- because the two die to DIFFERENT repairs: a summing map clause closes
-- the first and leaves this one exactly where it was.
----------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ obs natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ emptyᵉ

q : Closed Γ₀ natᵗ
q = mergeAllᵉ nothing
      (scanᵉ step seed (ofᵉ (strmᵗ emptyᵉ ∷ strmᵗ emptyᵉ ∷ strmᵗ emptyᵉ ∷ [])))

----------------------------------------------------------------------
-- THE CROSSINGS, PINNED BY `refl` RATHER THAN COMPUTED INSIDE THE ⊥.
-- The two readings are claimed beside the two dry rows because the
-- finding is their ORDER: a program reading ONE whose run goes dry is
-- the whole of it, so a repair that moved either end would leave a
-- witness reporting two numbers that no longer meet.
----------------------------------------------------------------------

nest-p : obsDepthᵉ p ≡ 1
nest-p = refl

dry-p : hasDry (evaluate 1 p ins₀) ≡ true
dry-p = refl

nest-q : obsDepthᵉ q ≡ 1
nest-q = refl

dry-q : hasDry (evaluate 1 q ins₀) ≡ true
dry-q = refl

rank-sufficient-false : RankSufficient → ⊥
rank-sufficient-false h with trans (sym (h 1 p ins₀)) dry-p
... | ()

-- and the same claim killed a second time, at the program no clause of
-- the measure reaches
rank-sufficient-false-fold : RankSufficient → ⊥
rank-sufficient-false-fold h with trans (sym (h 1 q ins₀)) dry-q
... | ()
