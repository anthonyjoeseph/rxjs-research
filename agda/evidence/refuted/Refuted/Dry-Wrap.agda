-- THE TOP-LINE DRY CLAIM IS FALSE, AND THE CLAUSE THAT KILLS IT IS THE
-- ONE THE DESCENT CANNOT GIVE UP.
--
-- `evaluate` concatenates a root burst with a drain, and the burst is
-- the subscription walk entered at the triple the program itself reads.
-- The rank component of that triple is the observable NESTING, and the
-- hop guard spends it against the nesting of whatever inner is handed to
-- a flattener.  The measure cuts a `deferᵉ` to ZERO without reading its
-- body — which is precisely the clause that makes the measure survive
-- μ-unfolding, and so the clause the recursion edge is bought with.  A
-- program written behind a gate therefore reads zero, the guard enters
-- at zero, and the first hop under that gate refuses to descend.
--
-- SO THE SEED STARVES EXACTLY WHERE THE DESCENT IS PAID FOR.  A gate's
-- body is not subscribed in the frame that wrote it: the defer registers
-- its frame and leaves the body PENDING, so the subscribe happens at an
-- ARRIVAL, which re-seeds the rank from the value it carries joined with
-- the store's reading — and neither mentions a body still waiting in the
-- schedule.  Nothing anywhere in the run holds the pending body's
-- nesting, which is what makes this a design tension rather than a
-- missing clause: reading the body would close it and would cost the
-- measure the unfolding equation.
--
-- AND TWO FURTHER WITNESSES SAY THE GATE IS NOT THE WHOLE OF IT.
-- Substituting a value of observable type into a template goes through
-- `reify`, which AT THAT TYPE IS `strmᵗ`, so an instance is written one
-- deeper than its template while every clause of the measure JOINS.  A
-- template that wraps its argument therefore hands out an inner the
-- entry was never shown to dominate — with no gate in the program at
-- all.  Summing the map clause closes that one strictly, since a
-- template is applied once per value; it leaves the fold exactly where
-- it was, because a step re-applied to its OWN accumulator deepens once
-- per DELIVERY and the gap is then a delivery count no reading of the
-- syntax carries.
--
-- WHAT ALL THREE KILL IS THE SEED DOING TWO JOBS, NOT THE DESCENT.  The
-- nesting orders the recursion correctly — it is a fact about the term,
-- every subterm reads under it by one projection of a join, and that is
-- what made the entry side definitional at every constructor.  It is the
-- second job, pricing what a subtree will EMIT, that no syntactic figure
-- can do.  So the repair is a bound the machine CARRIES, quantified
-- beside the rank rather than read off it, and none of the three touches
-- the descent the rank was introduced for.
module Refuted.Dry-Wrap where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Fuel; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Exp; Fn; Tm; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; deferᵉ; input; strmᵗ; varᵗ; fstᵗ)
open import Rx.Slots using (Slots; scripted)
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

----------------------------------------------------------------------
-- AND THE THIRD, WHICH NEEDS NO TEMPLATE AT ALL.  A `deferᵉ` registers
-- its frame and leaves its body PENDING, so the body is subscribed at an
-- ARRIVAL rather than inside the subscribe frame that wrote it — and an
-- arrival re-seeds the rank from the value it carries joined with the
-- store's own reading, neither of which mentions a body still waiting in
-- the schedule.  So a gate over a flattener over a gate goes dry on a
-- scripted slot, with nothing substituted anywhere.  It is the widest of
-- the three: the first two need a template that deepens its argument,
-- and this one needs only that a subscribe happen LATE.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 3 , 5 ∷ after 4 , 6 ∷ after 5 , 7 ∷ []))

obsSlot : ∀ {Δᵍ Δ} → Exp Γ₁ Δᵍ Δ [] (obs natᵗ)
obsSlot = ofᵉ (strmᵗ (input zero) ∷ [])

g : Closed Γ₁ natᵗ
g = deferᵉ (mergeAllᵉ nothing (deferᵉ obsSlot))

nest-g : obsDepthᵉ g ≡ 0
nest-g = refl

dry-g : hasDry (evaluate 50 g insLate) ≡ true
dry-g = refl

rank-sufficient-false : RankSufficient → ⊥
rank-sufficient-false h with trans (sym (h 1 p ins₀)) dry-p
... | ()

-- and the same claim killed a second time, at the program no clause of
-- the measure reaches
rank-sufficient-false-fold : RankSufficient → ⊥
rank-sufficient-false-fold h with trans (sym (h 1 q ins₀)) dry-q
... | ()

-- and a third time behind a gate, where nothing is substituted and the
-- program's whole reading is zero
rank-sufficient-false-gate : RankSufficient → ⊥
rank-sufficient-false-gate h with trans (sym (h 50 g insLate)) dry-g
... | ()
