-- `emit-map` IS FALSE, and the witness is a step function that embeds its
-- own payload on BOTH sides of the `mapᵉ` clause's `+`.
--
-- THE MEASURE SUMS AT A MAP: `nestDᵉ sl (mapᵉ f e) = nestDᵗ sl f + nestDᵉ sl e`.
-- A `strmᵗ` template is SUBSTITUTED, not consumed, so a template that is
-- itself a `mapᵉ` with the payload variable in both positions delivers the
-- payload's nesting twice while charging its own syntax nothing — both
-- occurrences are `varᵗ`, and `nestDᵗ sl (varᵗ _) = 0`.
--
-- WHY THE ⊔ REPAIR DOES NOT COVER IT.  `nestDᵗ` joins duplicated subterms
-- with `⊔` at `pairᵗ`, at a term list and at `ifᵗ`, which is what made the
-- earlier duplication witness (`Probed.Nest-Depth` §3) measure 2 rather
-- than 3.  The `mapᵉ` clause is not one of those: a map's own layers and
-- its source's layers genuinely stack, so the `+` is right for the SYNTAX
-- and wrong for a SUBSTITUTED variable appearing under both operands.
--
-- A `caseᵗ` cannot do this even though its clause also sums, and the
-- difference is worth recording: `nestDᵗ sl (caseᵗ s l r)` charges the
-- scrutinee, but `evalWith` CONSUMES the scrutinee rather than embedding
-- it, so that sum over-approximates.  Only a template whose operands both
-- survive into the result can double-count.
--
-- ⚠ AND THE PARENT SURVIVES THIS WITNESS, which is the half of the
-- finding that says where the defect is.  Put one `*All` layer over the
-- doubling map — the shape the arm consuming this leaf actually sees —
-- and `depthE` reads 1 against a `depthCap` of 2.  So the arm's
-- conclusion is not refuted here; only the intermediate predicate is.
--
-- WHAT THAT MEANS, and it is a route rather than an arithmetic slip.
-- `burstND?` bounds an emitted payload's CAP by the emitter's cap, and a
-- cap is syntactic: `nestDᵉ` charges a `mapᵉ`'s template whether or not
-- the depth family ever enters it.  `depthBurst`'s walk enters a payload
-- only through a `thru-outer` frame, and a `map-f` is not one — so a map
-- can hand on a payload whose CAP exceeds its own while the DEPTH of
-- that payload stays far below.  Bounding caps by caps is therefore
-- STRUCTURALLY the wrong currency at this clause, and no tightening of
-- the predicate repairs it.
--
-- THE OCCURRENCE REPAIR IS ALSO REFUTED, and §2 below is the witness.
-- Charging the measure for template occurrences —
-- `nestDᵗ sl f + occᵗ f * nestDᵉ sl e` for a new syntactic `occᵗ` — was
-- the obvious first repair and it reads as sufficient, because the
-- witness above delivers the payload's NESTING twice.  It is not, and
-- the reason is a second axis: the substituted value's WIDTH.  A
-- template holding its payload variable under an inner `*All` that
-- feeds a `scanᵉ` puts the payload's `outWᵉ` into the measure's
-- per-payload FACTOR, so at a payload of nesting ZERO the emitted
-- expression's nesting is the payload's WIDTH — 4 at a three-payload
-- source, 8 at a seven-payload one, against a bound of 1 in both.  No
-- multiple of `nestDᵉ sl e` reaches a quantity that is 0 there.
--
-- SO THE CURRENCY IS THE FINDING, THREE WITNESSES DEEP, and the shape
-- the repair has to take is already in the tree twice.  `innWⱽ` carries
-- exactly this problem on the WIDTH face and solves it in two moves: a
-- `mapᵉ` charges its source's width a multiplier read off the template's
-- own payload multiplicity (`pmIᵗⱽ … ⊔ 1`), and a `scanᵉ` EXPONENTIATES
-- that multiplicity over the source's payload count.  Transporting both
-- onto `nestDᵉ` covers the two witnesses above — but not the third, and
-- that is the part that settles it: the exponent is `outWᵉ` of the
-- source, and `outWᵉ` is NOT stable under substitution, since
-- `innWᵗⱽ (varᵗ _)` is 0 while `innWᵗⱽ (strmᵗ v)` is `outWᵉ v`.  A
-- syntactic measure cannot be closed under a substitution that moves its
-- own count factor.
--
-- WHICH IS WHY BOTH SIBLING FACES STATE THEIR SUBSTITUTION BOUND
-- CAPS-CONDITIONED AND AT AN ITERATED COUNT — `applyFn-iterSize` and
-- `applyFn-iterFold`, each reading a cap for the env and a fold count
-- for the term — and the depth face is the one that tried to read a
-- syntactic bound instead.  So `EmitCap` is not a statement about
-- program text: it is the depth face's missing third member of that
-- family, and its unconditional form is what these rows refute.  A
-- hypothesis is licensed here for the one reason that licenses one at
-- all.
module Refuted.Emit-Map where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ; ofᵉ;
  emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; applyFn)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init;
  subscribeE)
open import Verify-Budget-Sufficient.Depth-Compositional
  using (innerNest; burstND?; EmitCap; depthCap)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Rx.Frame-Width using (outWᵉ)
open import Data.Product using (proj₁)

g20 : Gas
g20 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

-- ONE `*All` layer, so the payload carries nesting 1
deep : Closed Γ₀ natᵗ
deep = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- the source: one payload, and that payload IS `deep`
bD : Closed Γ₀ (obs natᵗ)
bD = ofᵉ (strmᵗ deep ∷ [])

-- THE WITNESS.  Both operands of the inner `mapᵉ` are the payload
-- variable: the function position at index 1 (past the inner map's own
-- binder) and the source position at index 0.
fD : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fD = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

progM : Closed Γ₀ (obs (obs natᵗ))
progM = mapᵉ fD bD

schedM : Sched Γ₀
schedM = sched-init progM slots₀

stM : EvalSt progM
stM = st-init progM

------------------------------------------------------------------
-- THE ARITHMETIC, as numerals Agda computes.
------------------------------------------------------------------

-- the emitter charges its template NOTHING: both occurrences are `varᵗ`
fnNest : nestDᵗ slots₀ fD ≡ 0
fnNest = refl

srcNest : nestDᵉ slots₀ bD ≡ 1
srcNest = refl

-- so the bound the clause has to live within is 1
bound : innerNest slots₀ progM ≡ 1
bound = refl

-- and what the map EMITS measures 2: one copy of the payload's layer per
-- operand of the substituted template
emitted : nestDᵉ slots₀ (applyFn fD deep) ≡ 2
emitted = refl

------------------------------------------------------------------
-- THE REFUTATION
------------------------------------------------------------------

row : burstND? slots₀ (innerNest slots₀ progM) (obs (obs natᵗ))
        (proj₁ (subscribeE g20 progM root 0 0 schedM stM)) ≡ false
row = refl

emit-map-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {s}
     (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
     (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     EmitCap g (mapᵉ f b) κ bid now sched st) → ⊥
emit-map-absurd h with h g20 fD bD root 0 0 schedM stM
... | ()


progTop : Closed Γ₀ (obs natᵗ)
progTop = mergeAllᵉ progM

schedT : Sched Γ₀
schedT = sched-init progTop slots₀

stT : EvalSt progTop
stT = st-init progTop

-- ONE `*All` layer over the doubling map, so the burst walk of the arm
-- that consumes the refuted leaf actually enters the emitted payload.
progTopDepth : depthE g20 progTop root 0 0 schedT stT ≡ 1
progTopDepth = refl

progTopCap : depthCap progTop (root {Γ = Γ₀} {t = obs natᵗ}) schedT ≡ 2
progTopCap = refl


------------------------------------------------------------------
-- § 2 — THE SAME LEAF, THE OTHER AXIS: the emitted nesting is the
-- payload's WIDTH, at a payload whose nesting is 0.
--
-- This is what kills charging occurrences.  The template's payload
-- variable sits under a `*All` that feeds a `scanᵉ`, so after
-- substitution the payload's `outWᵉ` becomes the scan clause's
-- per-payload factor — and before substitution that factor is 0,
-- because a `varᵗ` has no width.
------------------------------------------------------------------

-- FLAT AND WIDE: three data payloads, no `*All` anywhere
wide3 : Closed Γ₀ natᵗ
wide3 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

wide7 : Closed Γ₀ natᵗ
wide7 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])

-- the scan's step: one `*All` layer, and it does NOT mention the payload
gW : Fn Γ₀ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gW = strmᵗ (mergeAllᵉ (ofᵉ (strmᵗ emptyᵉ ∷ [])))

-- THE WITNESS: the payload variable feeds a `*All` whose consumer is a
-- `scanᵉ`, so the payload's width lands in the count factor
fW : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fW = strmᵗ (scanᵉ gW (strmᵗ emptyᵉ)
             (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

bW3 : Closed Γ₀ (obs natᵗ)
bW3 = ofᵉ (strmᵗ wide3 ∷ [])

progW : Closed Γ₀ (obs (obs natᵗ))
progW = mapᵉ fW bW3

schedW : Sched Γ₀
schedW = sched-init progW slots₀

stW : EvalSt progW
stW = st-init progW

-- THE PAYLOAD HAS NO NESTING AT ALL, so every multiple of its nesting is
-- 0 and no occurrence charge can reach the gap below
wideNest : nestDᵉ slots₀ wide3 ≡ 0
wideNest = refl

-- what it has instead, and the quantity the gap turns out to be
wideOutW : outWᵉ 0 slots₀ wide3 ≡ 3
wideOutW = refl

-- the template charges 1 — its own `*All` — and the count factor 0,
-- because `varᵗ` has no width
fnNestW : nestDᵗ slots₀ fW ≡ 1
fnNestW = refl

boundW : innerNest slots₀ progW ≡ 1
boundW = refl

-- AND THE GAP IS THE WIDTH, pinned twice so the growing quantity is
-- named rather than inferred: 3 payloads ↦ 4, 7 payloads ↦ 8
emittedW3 : nestDᵉ slots₀ (applyFn fW wide3) ≡ 4
emittedW3 = refl

emittedW7 : nestDᵉ slots₀ (applyFn fW wide7) ≡ 8
emittedW7 = refl

rowW : burstND? slots₀ (innerNest slots₀ progW) (obs (obs natᵗ))
         (proj₁ (subscribeE g20 progW root 0 0 schedW stW)) ≡ false
rowW = refl
