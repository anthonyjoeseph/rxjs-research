------------------------------------------------------------------
-- THE HOP DOES NOT DESCEND IN measureE.  Refuted 2026-07-27, at all
-- three of the sites the hop-descent interface claimed, by Agda.
--
-- The claim was: an observable value `o` carried by a carrier `b`'s
-- subscription burst satisfies measureE B o ≺ᵛ measureE B b, so the
-- *All clause can peel one gs against dBound-hop's r′ < r.
--
-- It is false, and for one reason at all three sites: a hop value is
-- a TEMPLATE INSTANTIATED WITH A VALUE, and a template may use its
-- bound variable more than once.  subΘ then copies that value's
-- shells once PER OCCURRENCE (exactly the plugs summand of
-- subΘ-countsᵗ), while the carrier holds them ONCE.  Duplication
-- makes the hop's multiset strictly BIGGER, so ≺ᵛ points the wrong
-- way — the carrier's shells do not dominate the hop's.
--
-- Each refutation below is a closed absurd-pattern proof, not a
-- computed disagreement: Agda checks that `≺ᵛ` has no inhabitant.
--
--   hop-of-false       SITE 1, of-literals    — via caseᵗ
--   hop-fn-obs-false   SITE 2b, obs source    — via a plain mapᵉ,
--                      WITH its guarding premise satisfied
--   hop-fn-data-false  SITE 2a, data source   — via caseᵗ, so the
--                      2026-07-27 isData restriction does not save it
--
-- Site 3 (μ-unfold, unfoldμ-≺) is unaffected: unfolding substitutes
-- SYNTAX for a Δᵍ variable under a guard, never a shell-carrying
-- value, so nothing is copied.
--
-- What survives: `hop-anchored` (the share boundary, paid with
-- unconn — see sharedConnect-unconn) and unfoldμ-≺.  What does not:
-- rank ∘ measureE as dBound's `r`.  See the memo at the hop-descent
-- block in Verify-Budget-Sufficient.
------------------------------------------------------------------
module Hop-Descent-Probe where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Fin  using (Fin) renaming (zero to fz)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat  using (_<_; _≤_; s≤s; z≤n)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
open import Data.Bool using (true)
open import Verify-Budget-Sufficient using (measureE; counts; _≺ᵛ_; ≺-here; ≺-there)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ)
open import Data.Product using (_,_)

Γ : Ctx 1
Γ = natᵗ ∷ᵛ []ᵛ

-- a fat leaf: shellSizeᵉ big ≡ 4, innerᵉ big ≡ []
idFn : Fn Γ [] [] [] natᵗ natᵗ
idFn = varᵗ (here refl)

big : Closed Γ natᵗ
big = mapᵉ idFn (mapᵉ idFn (mapᵉ idFn (input fz)))

_ : shellSizeᵉ big ≡ 4
_ = refl

_ : shellsᵉ big ≡ 4 ∷ []
_ = refl

-- the duplicating branch: uses its obs-typed Θ var TWICE
dup : Tm Γ [] [] (obs natᵗ ∷ []) (obs natᵗ)
dup = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

_ : innerᵗ dup ≡ 2 ∷ []
_ = refl

other : Tm Γ [] [] (unitᵗ ∷ []) (obs natᵗ)
other = strmᵗ emptyᵉ

-- caseᵗ, the one binder: scrutinee delivers `big`, branch duplicates it
tm : Tm Γ [] [] [] (obs natᵗ)
tm = caseᵗ (inlᵗ (strmᵗ big)) dup other

ts : List (Tm Γ [] [] [] (obs natᵗ))
ts = tm ∷ []

carrier : Closed Γ (obs natᵗ)
carrier = ofᵉ ts

o : Val Γ (obs natᵗ)
o = evalTm tm

-- the value handed to the burst carries big's shell TWICE …
_ : shellsᵉ o ≡ 2 ∷ 4 ∷ 4 ∷ []
_ = refl

-- … while the carrier that is supposed to dominate it carries it ONCE
_ : shellsᵉ carrier ≡ 1 ∷ 4 ∷ 2 ∷ 1 ∷ []
_ = refl

-- so at class 4 the hop GROWS: 2 against 1, and lex reads top-down.
-- The demand was measureE B o ≺ᵛ measureE B carrier; these are the
-- two vectors it compares, at B ≡ 5
_ : measureE 5 o        ≡ 0 ∷ᵛ 2 ∷ᵛ 0 ∷ᵛ 1 ∷ᵛ 0 ∷ᵛ 0 ∷ᵛ []ᵛ
_ = refl

_ : measureE 5 carrier  ≡ 0 ∷ᵛ 1 ∷ᵛ 0 ∷ᵛ 1 ∷ᵛ 2 ∷ᵛ 0 ∷ᵛ []ᵛ
_ = refl

-- THE REFUTATION, machine-checked rather than read off the vectors:
-- lex reads top-down, the top class ties at 0, and at class 4 the hop
-- has 2 where the carrier has 1 — so `≺ᵛ` has no inhabitant here.
-- Both constructors are refuted by absurd patterns: ≺-here needs
-- 2 < 1, ≺-there needs the heads equal and then 0 < 0 / 1 < 1 / 2 < 0.
hop-of-false : measureE 5 o ≺ᵛ measureE 5 carrier → ⊥
hop-of-false (≺-here ())
hop-of-false (≺-there (≺-here (s≤s ())))

------------------------------------------------------------------
-- AND THE SAME HOLE WITHOUT `caseᵗ`.  A plain `mapᵉ` whose Fn uses
-- its obs-typed argument twice duplicates just as well, so this is
-- not a quirk of the one binder in Tm — it is what substituting a
-- shell-carrying value into a multi-occurrence template does.
-- Site 2b guarded exactly this with a premise on the plug's own
-- measure.  The premise HOLDS here (fn-premise, below, is a proof)
-- and the conclusion still fails, so the guard was not the fix.
------------------------------------------------------------------

dupF : Fn Γ [] [] [] (obs natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

src : Closed Γ (obs natᵗ)
src = ofᵉ (strmᵗ big ∷ [])

carrier₂ : Closed Γ (obs natᵗ)
carrier₂ = mapᵉ dupF src

o₂ : Val Γ (obs natᵗ)
o₂ = applyFn dupF big

_ : shellsᵉ carrier₂ ≡ 2 ∷ 2 ∷ 4 ∷ []
_ = refl

_ : shellsᵉ o₂ ≡ 2 ∷ 4 ∷ 4 ∷ []
_ = refl

-- hop-fn-obs's premise: the plug's own measure is under the carrier's
fn-premise : counts 5 (shellsᵛ (obs natᵗ) big) ≺ᵛ measureE 5 carrier₂
fn-premise = ≺-there (≺-there (≺-there (≺-here (s≤s z≤n))))

-- and its conclusion is still false
hop-fn-obs-false : measureE 5 o₂ ≺ᵛ measureE 5 carrier₂ → ⊥
hop-fn-obs-false (≺-here ())
hop-fn-obs-false (≺-there (≺-here (s≤s ())))

------------------------------------------------------------------
-- AND SITE 2a FALLS TOO, so the isData restriction does not save it.
-- The restriction empties the PLUG (a data value carries no shells),
-- but `caseᵗ` can mint an obs-carrying value from nothing — `inlᵗ
-- (strmᵗ big)` is a closed term — and bind it to a Θ var the branch
-- then uses twice.  The duplication needs no obs-typed input at all.
------------------------------------------------------------------

-- same shape as `big`, one Θ deeper: shellsᵉ is Θ-blind
bigΘ : Exp Γ [] [] (natᵗ ∷ []) natᵗ
bigΘ = mapᵉ (varᵗ (here refl)) (mapᵉ (varᵗ (here refl))
         (mapᵉ (varᵗ (here refl)) (input fz)))

dup₃ : Tm Γ [] [] (obs natᵗ ∷ natᵗ ∷ []) (obs natᵗ)
dup₃ = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

-- a fn whose SOURCE is natᵗ — isData natᵗ ≡ true, so hop-fn-data applies
dataF : Fn Γ [] [] [] natᵗ (obs natᵗ)
dataF = caseᵗ (inlᵗ {t = unitᵗ} (strmᵗ bigΘ)) dup₃ (strmᵗ emptyᵉ)

carrier₃ : Closed Γ (obs natᵗ)
carrier₃ = mapᵉ dataF (ofᵉ (nat̂ 0 ∷ []))

o₃ : Val Γ (obs natᵗ)
o₃ = applyFn dataF 0

_ : isData natᵗ ≡ true
_ = refl

_ : shellsᵉ carrier₃ ≡ 2 ∷ 4 ∷ 2 ∷ 1 ∷ []
_ = refl

_ : shellsᵉ o₃ ≡ 2 ∷ 4 ∷ 4 ∷ []
_ = refl

hop-fn-data-false : measureE 5 o₃ ≺ᵛ measureE 5 carrier₃ → ⊥
hop-fn-data-false (≺-here ())
hop-fn-data-false (≺-there (≺-here (s≤s ())))

------------------------------------------------------------------
-- THE CANDIDATE, MEASURED.  hopD (Rx.Hop-Depth) is the proposed
-- replacement for dBound's `r`: an upper bound on the *All frames a
-- subscription can still enter.  Below, every witness above descends
-- STRICTLY under it — the check the refuted measure fails.
--
-- The hop edge to satisfy is  hopDᵉ V o < hopDᵉ V (mergeAllᵉ carrier),
-- the *All frame being what owns the demand.  V is irrelevant here
-- (no scanᵉ in any witness), so these hold at every V; 0 is shown.
------------------------------------------------------------------

-- witness 1, the caseᵗ of-literals hop:  2 ↦ 1
_ : hopDᵉ 0 (mergeAllᵉ carrier) ≡ 2
_ = refl

_ : hopDᵉ 0 o ≡ 1
_ = refl

-- witness 2, the two-use mapᵉ hop:  2 ↦ 1
_ : hopDᵉ 0 (mergeAllᵉ carrier₂) ≡ 2
_ = refl

_ : hopDᵉ 0 o₂ ≡ 1
_ = refl

-- witness 3, the data-source caseᵗ hop:  2 ↦ 1
_ : hopDᵉ 0 (mergeAllᵉ carrier₃) ≡ 2
_ = refl

_ : hopDᵉ 0 o₃ ≡ 1
_ = refl

------------------------------------------------------------------
-- THE LIFTED-LEAF VARIANT, which is why mapᵉ composes by `+` and not
-- by `⊔`.  Same shape as witness 2 with the leaf `big` replaced by
-- mergeAll (of (strm big)) — one hop deeper.  Under the real
-- definition the hop reads 4 ↦ 2, strict.  Under a `⊔`-at-mapᵉ
-- variant it would read 2 ↦ 2 and fail, so this pins the choice.
------------------------------------------------------------------

bigL : Closed Γ natᵗ
bigL = mergeAllᵉ (ofᵉ (strmᵗ big ∷ []))

srcL : Closed Γ (obs natᵗ)
srcL = ofᵉ (strmᵗ bigL ∷ [])

carrierL : Closed Γ (obs natᵗ)
carrierL = mapᵉ dupF srcL

oL : Val Γ (obs natᵗ)
oL = applyFn dupF bigL

_ : hopDᵉ 0 bigL ≡ 1
_ = refl

-- the leaf now contributes 1, and mapᵉ ADDS it to dupF's own 1,
-- doubled by dupF's two occurrences: 1 + 2*1 ≡ 3, plus the frame
_ : hopDᵉ 0 (mergeAllᵉ carrierL) ≡ 4
_ = refl

_ : hopDᵉ 0 oL ≡ 2
_ = refl

-- and the `⊔`-at-mapᵉ reading of the same carrier, spelled out: it
-- would be 1 ⊔ 1 ≡ 1 for carrierL, so 2 for the frame, against oL's
-- 2 — a tie, hence not a descent.  (hopDᵗ dupF and hopDᵉ srcL are the
-- two operands `⊔` would have combined.)
_ : hopDᵗ 0 dupF ≡ 1
_ = refl

_ : hopDᵉ 0 srcL ≡ 1
_ = refl

------------------------------------------------------------------
-- THE SCAN REFOLD, which is the clause that forced hopD to take V.
-- This is syncBudget's own 2026-07-19 program: an obs-typed
-- accumulator whose template embeds the accumulator TWICE,
--   acc ↦ mergeAll (of [acc , acc])
-- so each folded value nests the accumulator one deeper.  Built here
-- by hand, fold by fold, against hopD's scan clause.
------------------------------------------------------------------

-- the acc-doubling step function, acc : obs natᵗ, source : natᵗ
scanF : Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
scanF = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
                            ∷ fstᵗ (varᵗ (here refl)) ∷ [])))

scanSrc : Closed Γ natᵗ
scanSrc = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

theScan : Closed Γ (obs natᵗ)
theScan = scanᵉ scanF (strmᵗ big) scanSrc

-- the accumulator after k folds, applied literally
acc₀ acc₁ acc₂ acc₃ : Val Γ (obs natᵗ)
acc₀ = evalTm (strmᵗ big)
acc₁ = applyFn scanF (acc₀ , 1)
acc₂ = applyFn scanF (acc₁ , 2)
acc₃ = applyFn scanF (acc₂ , 3)

-- it nests exactly one per fold — the memo's "after k folded values
-- the acc nests k deep", now a refl-check rather than a measurement
_ : hopDᵉ 4 acc₀ ≡ 0
_ = refl

_ : hopDᵉ 4 acc₁ ≡ 1
_ = refl

_ : hopDᵉ 4 acc₂ ≡ 2
_ = refl

_ : hopDᵉ 4 acc₃ ≡ 3
_ = refl

-- and hopD's scan clause dominates every one of them: with occsᵗ
-- scanF ≡ 2 the clause pays (2+2)^V, which at V ≡ 4 is 256 against a
-- depth of 4.  The margin is the point — the clause has to hold for
-- EVERY k ≤ V, and it is exponential where the refold is linear
_ : occsᵗ scanF ≡ 2
_ = refl

_ : hopDᵉ 4 theScan ≡ 256
_ = refl

------------------------------------------------------------------
-- THE μ EDGE.  The directive's caution was not to assume unfoldμ-≺
-- transfers — it is a fact about the shell multiset, and hopD of an
-- unfolding is a different question.  It is: an unfold substitutes the
-- original closed μ for a Δᵍ variable, and Δᵍ variables are reachable
-- only under deferᵉ, which hopD cuts to 0.  So hopD is EQUAL across an
-- unfold, not merely ≤ — the μ edge stays weakly monotone in r and
-- keeps paying with dBound-μ's s, exactly as it already did.
------------------------------------------------------------------

μbody : Exp Γ (natᵗ ∷ []) [] [] natᵗ
μbody = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ (varᵉ (here refl))) ∷ []))

_ : hopDᵉ 4 (μᵉ μbody) ≡ 1
_ = refl

_ : hopDᵉ 4 (unfoldμ μbody) ≡ 1
_ = refl

-- stated as the edge the walk will consume
μ-hopD-stable : hopDᵉ 4 (unfoldμ μbody) ≡ hopDᵉ 4 (μᵉ μbody)
μ-hopD-stable = refl
