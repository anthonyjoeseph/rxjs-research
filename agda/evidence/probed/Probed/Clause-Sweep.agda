-- THE CLAUSES THE FOLD FAMILIES NEVER EXERCISED, AND WHAT AN EXACT
-- READING COSTS TO EVALUATE.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THE COVERAGE IS THE RISK HERE AND NOT A CAVEAT.  The plug-priced
-- reading is exact at three fold families, and both readings it replaced
-- were exact at the families THEY were tried on — each died at the first
-- shape nobody had instantiated.  So a reading whose whole receipt is
-- one operator is in the position those two were in before their
-- refutations, and the rows below are the shapes that position is made
-- of: a template read against its argument, a template that DROPS it, a
-- binder that is not a fold's, the two flatteners that are not a merge,
-- and a recursion.
--
-- AND THE COST IS A SEPARATE QUESTION FROM THE ARITHMETIC.  An exact
-- clause iterates over its refold count, which is a delivery count, and
-- a delivery count is a PRODUCT at every flattener — so the quantity the
-- clause recurses on is the one quantity in this development known to
-- grow multiplicatively.  Whether the reading can be evaluated at all
-- past single digits is therefore not a performance footnote: a measure
-- a typechecker cannot reduce cannot discharge a guard, however true it
-- is.
--
-- THE BOUNDARY.  Every program here is CLOSED — no `input`, so the slot
-- clause is read at the empty environment and nothing exercises it.
-- That clause needs a staged reading of its own, built the way
-- `Probed.Slot-Defer` builds the delivery one, and it is the one part of
-- the sweep nothing below reaches.
--
-- FORK: dry-operator
module Probed.Clause-Sweep where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Tm; Fn; obs; natᵗ;
                         ofᵉ; mapᵉ; scanᵉ; mergeAllᵉ;
                         switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                         varᵗ; nat̂; fstᵗ; inlᵗ; inrᵗ; caseᵗ; strmᵗ)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Plug-Priced using (depthᴾ; carriedᴾ; ψ₀; rdᵉ; topOf; ε)
open import Probed.Swapped-Exponent using (hopD′ᵉ; ν₀; η₀)
open import Refuted.Sync-Count using (Γ₀; ins₀)
open import Refuted.Root-Refold using (burstAt)

----------------------------------------------------------------------
-- THE TWO CARRIERS every program below is built out of.  `seed`
-- delivers one value and carries no hop; `deep` is the same thing behind
-- a flattener, so it delivers one and carries one.  Keeping the depth at
-- one is deliberate — a row that separates two readings at a depth of
-- one separates them, and a larger carrier only makes a wrong reading
-- harder to tell from a right one.  Both are stated over an arbitrary
-- local telescope, since every template below plants one under a binder.
----------------------------------------------------------------------

seed : ∀ {Δᵍ Δ Θ} → Tm Γ₀ Δᵍ Δ Θ (obs natᵗ)
seed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

deep : ∀ {Δᵍ Δ Θ} → Tm Γ₀ Δᵍ Δ Θ (obs natᵗ)
deep = strmᵗ (mergeAllᵉ nothing (ofᵉ (seed ∷ [])))

----------------------------------------------------------------------
-- THE TEMPLATE CLAUSE, three ways round.  `mapLive`'s template WRAPS its
-- argument, so the reading has to reach the plug; `mapDrop`'s ignores it
-- and emits the shallower carrier, so what the reading reports there is
-- whatever the clause keeps of a source it no longer passes on; and
-- `mapDeep`'s ignores it and emits a carrier as deep as the one it
-- dropped, which is where the two mechanisms come apart — a reading that
-- ADDS the template's hop to the source's reports one more than a
-- reading that substitutes and takes the deeper of the two.
----------------------------------------------------------------------

wrapT : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
wrapT = strmᵗ (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))

dropT : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
dropT = seed

mapLive : Closed Γ₀ (obs natᵗ)
mapLive = mapᵉ wrapT (ofᵉ (seed ∷ []))

mapDrop : Closed Γ₀ (obs natᵗ)
mapDrop = mapᵉ dropT (ofᵉ (deep ∷ []))

_ : depthᴾ ψ₀ mapLive ≡ 1                              -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 mapLive ins₀) ≡ 1           -- LOAD-BEARING
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 mapLive ins₀) ≤ᵇ depthᴾ ψ₀ mapLive) ≡ true
_ = refl

-- LOAD-BEARING: the template emits a carrier of depth zero, so a clause
-- that dropped the source's own reading along with the argument would
-- report zero here and a clause that keeps it reports one.
_ : depthᴾ ψ₀ mapDrop ≡ 1                              -- LOAD-BEARING
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 mapDrop ins₀) ≤ᵇ depthᴾ ψ₀ mapDrop) ≡ true
_ = refl

deepT : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
deepT = deep

mapDeep : Closed Γ₀ (obs natᵗ)
mapDeep = mapᵉ deepT (ofᵉ (deep ∷ []))

-- LOAD-BEARING: source and template each carry one hop and the template
-- passes neither on, so the emitted value carries exactly one.  A clause
-- summing the two reports two.
_ : depthᴾ ψ₀ mapDeep ≡ 1                              -- LOAD-BEARING
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 mapDeep ins₀) ≤ᵇ depthᴾ ψ₀ mapDeep) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE BINDER THAT IS NOT A FOLD'S.  A `caseᵗ` pushes the scrutinee onto
-- the environment for BOTH arms, so the reading is a join over two
-- readings taken at the same plug — the one shape where reading a single
-- arm would pass every fold row and still be wrong.  The left arm hands
-- the plug straight back and the right ignores it, so the two arms
-- disagree and the join is what decides.
----------------------------------------------------------------------

caseT : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
caseT = caseᵗ {t = natᵗ} (inlᵗ (varᵗ (here refl))) (varᵗ (here refl)) seed

caseRight : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
caseRight = caseᵗ (inrᵗ (nat̂ 0)) (varᵗ (here refl)) seed

caseProg : Closed Γ₀ (obs natᵗ)
caseProg = mapᵉ caseT (ofᵉ (deep ∷ []))

caseProgR : Closed Γ₀ (obs natᵗ)
caseProgR = mapᵉ caseRight (ofᵉ (deep ∷ []))

-- LOAD-BEARING: the deciding arm is the left one here and the right one
-- below, and the reading joins rather than selecting — so both report
-- the deeper arm, and a reading that followed the scrutinee's tag would
-- separate them.
_ : depthᴾ ψ₀ caseProg ≡ 1                             -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ caseProgR ≡ 1                            -- LOAD-BEARING
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 caseProg ins₀) ≤ᵇ depthᴾ ψ₀ caseProg) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 caseProgR ins₀) ≤ᵇ depthᴾ ψ₀ caseProgR) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE TWO FLATTENERS THAT ARE NOT A MERGE.  A switch and an exhaust
-- enter an inner exactly as a merge does and differ only in which inners
-- they keep — so the reading charges all three the same hop, and the
-- rows say whether the runs agree with that.  A switch DROPS the earlier
-- inner and an exhaust drops the later one, so each hands out strictly
-- less than the merge over the same list, which is why a shared clause
-- is sound and a row at each is what says so.
----------------------------------------------------------------------

twoDeep : Closed Γ₀ (obs (obs natᵗ))
twoDeep = ofᵉ (strmᵗ (ofᵉ (deep ∷ [])) ∷ strmᵗ (ofᵉ (deep ∷ [])) ∷ [])

switchProg : Closed Γ₀ (obs natᵗ)
switchProg = switchAllᵉ twoDeep

exhaustProg : Closed Γ₀ (obs natᵗ)
exhaustProg = exhaustAllᵉ twoDeep

mergeProg : Closed Γ₀ (obs natᵗ)
mergeProg = mergeAllᵉ nothing twoDeep

_ : depthᴾ ψ₀ switchProg ≡ 2                           -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ exhaustProg ≡ 2                          -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ mergeProg ≡ 2                            -- LOAD-BEARING
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 switchProg ins₀) ≤ᵇ depthᴾ ψ₀ switchProg) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 exhaustProg ins₀) ≤ᵇ depthᴾ ψ₀ exhaustProg) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 mergeProg ins₀) ≤ᵇ depthᴾ ψ₀ mergeProg) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE RECURSION.  `varᵉ` and the gate below it read zero, which is the
-- only thing that lets a reading survive an unfolding — so the whole
-- content of those clauses is an ABSENCE, and the row that instantiates
-- one has to be at a program where an absence is wrong if anything
-- leaks.  The recursive reference sits beside a live carrier under one
-- flattener, so the frame hands out the carrier and the reading must
-- cover it without the recursion contributing.
----------------------------------------------------------------------

recProg : Closed Γ₀ (obs natᵗ)
recProg = μᵉ (mergeAllᵉ nothing
               (ofᵉ (strmᵗ (ofᵉ (deep ∷ [])) ∷
                     strmᵗ (deferᵉ (varᵉ (here refl))) ∷ [])))

_ : depthᴾ ψ₀ recProg ≡ 2                              -- LOAD-BEARING
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 recProg ins₀) ≤ᵇ depthᴾ ψ₀ recProg) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE COST, which is the row this file exists for as much as any
-- clause.  Every family above keeps its delivery count at one or two;
-- these raise it by widening the lists a flattener multiplies, and the
-- fold clause below iterates once per delivery.  Each row is
-- LOAD-BEARING in a sense none of the others are — it could fail by not
-- finishing, and a reading a typechecker cannot reduce cannot discharge
-- a guard however true it is.
----------------------------------------------------------------------

wide : ∀ {Δᵍ Δ Θ} → Tm Γ₀ Δᵍ Δ Θ (obs natᵗ)
wide = strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ []))

-- five inners of five deliveries each: the flattener's product
count₂₅ : Closed Γ₀ natᵗ
count₂₅ = mergeAllᵉ nothing (ofᵉ (wide ∷ wide ∷ wide ∷ wide ∷ wide ∷ []))

_ : proj₁ (topOf (rdᵉ ψ₀ ε count₂₅)) ≡ 25              -- LOAD-BEARING
_ = refl

-- the fold clause iterating twenty-five times, each refold reading its
-- step against the previous accumulator
foldWide : Closed Γ₀ (obs natᵗ)
foldWide = scanᵉ (strmᵗ (mergeAllᵉ nothing
                          (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))))
                 seed count₂₅

_ : depthᴾ ψ₀ foldWide ≡ 26                            -- LOAD-BEARING
_ = refl

-- LOAD-BEARING, and it is the whole cost argument in one row: the
-- reading iterates twenty-five times and lands on the number a run
-- reaches, because a step that re-wraps its accumulator genuinely
-- deepens it once per refold.  The closed form exponentiates over the
-- same count instead, and what it reports at this program is twelve
-- orders of magnitude out — a bound that large is true and unusable,
-- since nothing descends against it.
_ : hopD′ᵉ ν₀ η₀ foldWide ≡ 1694577218886              -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE FORK.  The same choice the sibling files take apart at the fold,
-- retaken at a clause no fold family reaches.  The two readings agree at
-- every flattener here and at the recursion — a switch, an exhaust and a
-- merge all cost one hop under either — so the separation is not a
-- re-measurement of the fold and not an artefact of the root.  It is the
-- TEMPLATE clause: the closed form adds the template's own hop to the
-- source's, the iterated reading substitutes the source into the
-- template's environment and takes the deeper.  They part at the one
-- program where a template is as deep as the argument it discards.
----------------------------------------------------------------------

Point : Set
Point = Closed Γ₀ (obs natᵗ)

closedForm iterated : Point → ℕ
closedForm e = hopD′ᵉ ν₀ η₀ e
iterated   e = depthᴾ ψ₀ e

clause-sweep-fork : Separates closedForm iterated
clause-sweep-fork = separates-at mapDeep (λ ())
