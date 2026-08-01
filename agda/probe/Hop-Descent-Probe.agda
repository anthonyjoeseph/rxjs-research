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
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
open import Data.Bool using (true)
open import Verify-Budget-Sufficient using (measureE; counts; _≺ᵛ_; ≺-here; ≺-there)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵉ; pmᵗ)
open import Rx.Frame-Width using (outWᵉ; dWᵉ)
open import Rx.Evaluator using (Slots; shared)
open import Data.Product using (_,_)

Γ : Ctx 1
Γ = natᵗ ∷ᵛ []ᵛ

-- a slot telescope for the width measures, which read one (the μ
-- refutation below uses no input, so any shared def will do)
ins1 : Slots Γ
ins1 i = shared emptyᵉ

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

-- the leaf now contributes 1, and mapᵉ ADDS it to dupF's own 1:
-- 1 + 1*1 ≡ 2, plus the frame.  dupF's two mentions sit under an
-- `ofᵉ`, where hopD combines by `⊔`, so the multiplier there is 1 —
-- this is the `⊔` half of why a coefficient is not a count
_ : hopDᵉ 0 (mergeAllᵉ carrierL) ≡ 3
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

-- and hopD's scan clause dominates every one of them: with the
-- multiplier pmᵗ scanF ≡ 1 the clause pays (2+1)^V, which at V ≡ 4 is
-- 81 against a depth of 4.  The margin is the point — the clause has
-- to hold for EVERY k ≤ V, and it is exponential where the refold is
-- linear.  (scanF mentions its accumulator twice, but both mentions
-- sit under an `ofᵉ`'s `⊔`, so the multiplier is 1 where a count
-- would have said 2 and paid (2+2)^V ≡ 256 for nothing.)
_ : pmᵗ 4 0 scanF ≡ 1
_ = refl

_ : occsᵗ scanF ≡ 2
_ = refl

_ : hopDᵉ 4 theScan ≡ 81
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

------------------------------------------------------------------
-- AND THE SAME QUESTION FOR THE PARKED WIDTH, ANSWERED THE OTHER WAY.
-- REFUTED 2026-08-01, before the postulate that assumed it was built on.
--
-- hopD survives an unfold because Δᵍ variables are reachable only under
-- deferᵉ and hopD CUTS a defer to 0.  dW does the opposite: its whole
-- reason to exist is that it does NOT cut there —
-- `dWᵉ (deferᵉ e) = outWᵉ e ⊔ dWᵉ e`.  So the unfolding's plug lands at
-- exactly the positions dW is looking at, and what it exposes is the
-- μ's own outW, which dW does not bound.
--
-- The shape below.  `body` merges two literals: a defer whose body is
-- `mergeAllᵉ (ofᵉ [strmᵗ (varᵉ …)])` — a template that reads the μ-var
-- as an INNER observable — and a three-element literal that gives the μ
-- an outW of 6 while parking nothing.  Before the unfold the defer's
-- body has outW 0 (the var is a 0-width leaf) so dW is 0; after it, the
-- var has become the whole μ and the defer's body has outW 6.
--
-- 0 ↦ 6.  `dWᵉ (unfoldμ body) ≤ dWᵉ (μᵉ body)` is FALSE, and it is not
-- false by a constant: put k copies in the `ofᵉ` and the template's
-- innW slope multiplies, so any bound must be affine in the plug's
-- width with the pmO/pmI slopes — the hopD-subΘ machinery, not a
-- ⊔-monotonicity.  Hence Caps-Face states the μ edge's two axes
-- TOGETHER, existentially in j′, off the SIZE hypothesis it already has
------------------------------------------------------------------

μdefer : Exp Γ [] (natᵗ ∷ []) [] natᵗ
μdefer = mergeAllᵉ (ofᵉ (strmᵗ (varᵉ (here refl)) ∷ []))

μwide : Exp Γ (natᵗ ∷ []) [] [] natᵗ
μwide = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ μdefer)
                     ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ []))

_ : outWᵉ 1 ins1 (μᵉ μwide) ≡ 6
_ = refl

_ : dWᵉ 1 ins1 (μᵉ μwide) ≡ 0
_ = refl

_ : dWᵉ 1 ins1 (unfoldμ μwide) ≡ 6
_ = refl

-- the standing guard: if anyone re-states the μ edge as ⊔-monotone in
-- dW, this stops typechecking
μ-dW-not-stable : dWᵉ 1 ins1 (unfoldμ μwide) ≡ 6
μ-dW-not-stable = refl

------------------------------------------------------------------
-- REFUTATION 1 OF A COUNT: IT OVER-PRICES A PHANTOM.
--
-- Built 2026-07-28 while starting phase 3, by trying to construct the
-- worst case for hopD-subΘᵉ before proving it.  Against the `occsᵗ`
-- draft of hopD this program REFUTED the walk conjunct
--
--     every value a subscription emits has hopD ≤ hopD of what was
--     subscribed
--
-- reading 3 against an allowance of 2, and it refuted it with a
-- plugged value of hop depth ZERO.
--
-- THE MECHANISM.  hopD's mapᵉ coefficient prices how much of the
-- SOURCE's depth reaches the result.  occsᵗ counts EVERY varᵗ in the
-- template, whatever binder it belongs to.  Substitution replaces an
-- OUTER Θ variable by a reified observable, and that observable
-- carries its own map/scan templates — whose bound variables occsᵗ
-- then counts too.  So the coefficient INFLATED under a substitution
-- that duplicated nothing: the new occurrences belong to a different
-- binder.
--
-- Below, `plugged` is Θ-BUSHY but hop-SHALLOW — two map templates over
-- emptyᵉ, occsᵉ 2 and hopDᵉ 0.  Plugging it raised the occsᵗ
-- coefficient 2 ↦ 3, and that lone extra unit multiplied an inner
-- source's hop depth of 1.
--
-- Any per-BINDER quantity fixes this one, because a plug is Θ-closed:
-- every variable it brings is compared against an index already bumped
-- past it and contributes nothing.  The multiplier hopD now uses reads
-- 1 before and 1 after, so `emitted-fits` below is the standing guard —
-- if a coefficient ever drifts back to an index-blind count, it stops
-- typechecking.  (It is not the whole story: the NEXT section refutes
-- the per-binder count too.)
------------------------------------------------------------------

-- a Θ-BUSHY but hop-SHALLOW value: occsᵉ 2, hopDᵉ 0.  Both of its
-- varᵗ live under its own map binders, so its multiplier at index 0
-- reads 0 — the Θ-closedness that makes a coefficient
-- substitution-stable
plugged : Closed Γ natᵗ
plugged = mapᵉ idFn (mapᵉ idFn emptyᵉ)

_ : occsᵉ plugged ≡ 2
_ = refl

_ : pmᵉ 4 0 plugged ≡ 0
_ = refl

_ : hopDᵉ 4 plugged ≡ 0
_ = refl

-- the inner source: one hop, no occurrences
innerSrc : Exp Γ [] [] (obs natᵗ ∷ []) natᵗ
innerSrc = mergeAllᵉ (ofᵉ (strmᵗ emptyᵉ ∷ []))

-- the inner template.  `sndᵗ` DISCARDS the outer observable — it is
-- mentioned and thrown away, which is the point: it contributes
-- nothing semantically and still moves occsᵗ
innerFn : Tm Γ [] [] (natᵗ ∷ obs natᵗ ∷ []) natᵗ
innerFn = sndᵗ (pairᵗ (varᵗ (there (here refl))) (varᵗ (here refl)))

-- SIDE BY SIDE.  occsᵗ sees the discarded outer mention; the
-- multiplier sees only the binder whose argument is plugged here
_ : occsᵗ innerFn ≡ 2
_ = refl

_ : pmᵗ 4 0 innerFn ≡ 1
_ = refl

innerBody : Exp Γ [] [] (obs natᵗ ∷ []) natᵗ
innerBody = mapᵉ innerFn innerSrc

-- the outer program: map an observable-valued template over a source
-- that emits `plugged`
outerFn : Fn Γ [] [] [] (obs natᵗ) (obs natᵗ)
outerFn = strmᵗ innerBody

outerSrc : Closed Γ (obs natᵗ)
outerSrc = ofᵉ (strmᵗ plugged ∷ [])

prog : Closed Γ (obs natᵗ)
prog = mapᵉ outerFn outerSrc

-- the source emits exactly `plugged`
_ : evalTm (strmᵗ plugged) ≡ plugged
_ = refl

-- the program's allowance (it was 2 under occsᵗ: the inner
-- coefficient counted the discarded mention)
_ : hopDᵉ 4 prog ≡ 1
_ = refl

-- what the map frame emits for it: stepFrame (map-f fn) is
-- `map (applyFn fn)`, so this IS the burst's value
emitted : Val Γ (obs natᵗ)
emitted = applyFn outerFn plugged

-- 3 under occsᵗ — the substitution had raised the coefficient from 2
-- to 3 and that unit multiplied the inner source's one hop
_ : hopDᵛ 4 (obs natᵗ) emitted ≡ 1
_ = refl

-- the coefficient did not move under the substitution — 1 before and
-- 1 after, where occsᵗ went 2 ↦ 3 — and so the emission fits.  The
-- walk conjunct burstHopD? holds of this program, where
-- under the index-blind count it demanded 3 ≤ 2
emitted-fits : hopDᵛ 4 (obs natᵗ) emitted ≤ hopDᵉ 4 prog
emitted-fits = s≤s z≤n

------------------------------------------------------------------
-- REFUTATION 2 OF A COUNT: IT UNDER-PRICES A MULTIPLIER.
--
-- Built 2026-07-28 while setting up phase 3's induction.  Working out
-- what the mapᵉ clause needs from its recursive calls, the coefficient
-- that makes the induction close is not an occurrence count at all —
-- and this program shows the per-binder count `occs0ᵗ`, which fixes
-- refutation 1, failing anyway.
--
-- THE MECHANISM.  hopD's mapᵉ clause MULTIPLIES its source's depth by
-- the template's coefficient.  A substitution plugs its value into the
-- source position of an INNER map, where that inner template's
-- coefficient multiplies it — and the OUTER coefficient, being a count
-- of occurrences, prices the plug at 1 no matter how large the inner
-- factor is.  So depth reaches the emission scaled by something the
-- allowance never saw.
--
-- Under `occs0ᵗ`, the numbers below read: g3's coefficient 3 (three
-- uses of its own variable), fMul's own depth 3·1 ≡ 3, the outer
-- coefficient 1 (one mention, nothing duplicated), an allowance of
-- 3 + 1·1 ≡ 4 — and an emission of 3·(1+1) ≡ 6.
--
-- The outer template mentions its argument exactly once and duplicates
-- nothing, so this is not refutation 1 wearing a different hat.  No
-- occurrence count of any kind can fix it: the quantity these clauses
-- need is the MULTIPLIER hopD itself applies along the path to the
-- plug, and multipliers are composed, not counted.  That is `pmᵗ`,
-- which hopD now uses, and under which the same program reads 2 ≤ 2 —
-- because pmᵗ also sees that g3's three uses sit at primᵗ positions
-- hopD reads as 0, so their multiplier is 0 and the count of 3 was
-- fiction in the other direction too.
------------------------------------------------------------------

-- three uses of its own variable, all at primᵗ positions — hopD reads
-- those as 0, so the depth that can flow through them is 0 and the
-- multiplier is 0, where a count says 3
g3 : Tm Γ [] [] (natᵗ ∷ obs natᵗ ∷ []) natᵗ
g3 = primᵗ add (pairᵗ (varᵗ (here refl))
       (primᵗ add (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))))

_ : occsᵗ g3 ≡ 3
_ = refl

_ : pmᵗ 4 0 g3 ≡ 0
_ = refl

_ : hopDᵗ 4 g3 ≡ 0
_ = refl

-- the outer observable, mentioned ONCE, in a position that carries a hop
bMention : Exp Γ [] [] (obs natᵗ ∷ []) natᵗ
bMention = mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))

_ : hopDᵉ 4 bMention ≡ 1
_ = refl

-- the template's own depth: 3 under the count, 1 under the multiplier
fMul : Fn Γ [] [] [] (obs natᵗ) (obs natᵗ)
fMul = strmᵗ (mapᵉ g3 bMention)

_ : hopDᵗ 4 fMul ≡ 1
_ = refl

-- and the OUTER coefficient is 1 either way: one mention, no duplication
_ : pmᵗ 4 0 fMul ≡ 1
_ = refl

vDeep : Closed Γ natᵗ
vDeep = mergeAllᵉ (ofᵉ (strmᵗ emptyᵉ ∷ []))

_ : hopDᵉ 4 vDeep ≡ 1
_ = refl

progMul : Closed Γ (obs natᵗ)
progMul = mapᵉ fMul (ofᵉ (strmᵗ vDeep ∷ []))

-- the allowance: 1 + 1·1  (it was 3 + 1·1 ≡ 4 under the count)
_ : hopDᵉ 4 progMul ≡ 2
_ = refl

emittedMul : Val Γ (obs natᵗ)
emittedMul = applyFn fMul vDeep

-- the emission: the plug landed in bMention, inside g3.  Under the
-- count that was 3·(1+1) ≡ 6 against an allowance of 4; under the
-- multiplier it is 1·(1+1) ≡ 2 against an allowance of 2
_ : hopDᵛ 4 (obs natᵗ) emittedMul ≡ 2
_ = refl

-- the standing guard for refutation 2.  Under any coefficient that
-- counts occurrences rather than composing multipliers, this is 6 ≤ 4
-- and stops typechecking
mul-fits : hopDᵛ 4 (obs natᵗ) emittedMul ≤ hopDᵉ 4 progMul
mul-fits = s≤s (s≤s z≤n)
