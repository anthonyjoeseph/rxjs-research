------------------------------------------------------------------
-- WHAT ONE APPLICATION COSTS.  The gate on the AFFINE-FIRST reading
-- of the five evaluation obligations (evalTms-caps, evalSeed-caps,
-- unfoldμ-caps, mapFrame-caps, scanFrame-caps).
--
-- THE CANDIDATE BEING GATED.  Each of the five bounds the output of
-- ONE evaluation by entry quantities, and the affine reading is that
-- one `j` pays for it:
--
--     size    sizeᵛ (evalTm z) ≤ sizeStep S S,  S ≥ sizeᵗ z
--     size    sizeᵛ (applyFn f v) ≤ sizeStep S s,  S ≥ sizeᵗ f, s ≥ sizeᵛ v
--     width   dWᵉ (unfoldμ body) ≤ (affine in outWᵉ (μᵉ body))
--
-- with `sizeStep S s = S * suc (2 * s)` and `foldStep S w = S ^ suc w`
-- the per-j increments of the Caps recurrence.
--
-- ALL THREE ARE REFUTED HERE, and each refutation is a family rather
-- than an accident — the growth is EXPONENTIAL in the entry syntax on
-- every one of them, so no constant slackening of an affine form
-- survives.  What the numbers also say, and this is the usable half:
-- the exponent is small enough that a FEW j cover it, and one j per
-- syntax node covers it with room.  See the reading at the foot.
--
--   §1  seedDbl     evalSeed-caps / evalTms-caps.  A closed term of
--                   size 6k+1 whose VALUE has size 2^(k+1)−1: k nested
--                   `caseᵗ`, each branch pairing its own binding with
--                   itself.  The doubling is proven for all k
--                   (seed-val-rec / seed-size-rec), so the table is a
--                   reading of a closed form, not a sample.
--   §2  fnDbl       mapFrame-caps / scanFrame-caps.  The same ladder
--                   as a step function, so the input value is what
--                   gets copied.  Beaten at k = 6, on a value of size
--                   127.
--   §3  the j LADDER.  How many `j` the same rows actually need —
--                   `iterSize` against the measured output.  Two on
--                   the worst §1 and §2 rows, three on a value of 33
--                   million, against a sizeᵗ of 85 to 145.
--   §4  μscan       unfoldμ-caps, the width half.  The μ-var under a
--                   defer, inside the SOURCE of a scan: innWᵉ's scan
--                   clause puts the source's width in an EXPONENT, so
--                   plugging the μ back in exponentiates.  outWᵉ
--                   (μᵉ body) = m ↦ dWᵉ (unfoldμ body) = m * 2 ^ m.
--                   Hop-Descent-Probe's μwide is the m = 1 shadow of
--                   this (0 ↦ 6); the ladder is the shape.
--   §5  the WIDTH j LADDER.  `foldStep S w = S ^ suc w` swallows §4
--                   whole at j′ = 2 — which is the finding that
--                   matters, because it says the width half of
--                   unfoldμ-caps does not WANT an affine form.
--   §6  THE RECEIPT THAT LANDED.  `j′ = sizeᵗ` — one iterSize fold per
--                   syntax node — against every §1 and §2 row, read at
--                   the WORST admissible base S = 1.  These are the
--                   regression set for evalWith-iterSize /
--                   applyFn-iterSize / evalTm-iterSize (Caps-Face).
--   §7  THE WIDTH HALF'S OWN GATE.  Where one foldStep per node does
--                   and does not dominate, read off the width
--                   recurrence's CLAUSES rather than off a program.
--                   mapᵉ and the *All family fit in one fold; `scanᵉ`
--                   does NOT — its innW clause is M ^ M against a
--                   budget of S ^ (1 + M) — and the repair costs no
--                   receipt, because a scanᵉ node carries three
--                   children and therefore three spare folds.
--   §8  iwDef       the SECOND thing the width half needs, which the
--                   cap does not carry: `innWᵉ` of a slot def.
--                   slotCaps? bounds `sizeᵉ d` and `pWᵉ d` and nothing
--                   else, and pW cannot be made to bound innW — here is
--                   a def with pW 0 and innW 3.  REPAIRED: the shared
--                   clause now carries the innW conjunct too.
--   §9  THE FIVE MEMBERS, LANDED.  All five are ground in Caps-Face,
--                   and these are the receipts they carry — the lift
--                   that IS the width half, the μ edge's two halves on
--                   §4's ladder, and the scan rung's composition.
--
-- Standalone (hand-built syntax only, no evaluator state), so
-- src/Main.agda never reaches it: it needs its own make target.
------------------------------------------------------------------
module Eval-Growth-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_; _<ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Fin  using (Fin) renaming (zero to fz)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)
open import Data.Nat.Properties using (+-assoc; +-comm)

open import Rx.Exp
open import Rx.Frame-Width using (outWᵉ; innWᵉ; dWᵉ; pWᵉ; pmIᵗ; pmOᵉ)
open import Rx.Evaluator using (Slots; shared)
open import Verify-Budget-Sufficient using (sizeStep; iterSize; foldStep; iterFold)

Γ : Ctx 1
Γ = natᵗ ∷ᵛ []ᵛ

-- one slot, a share of `emptyᵉ`: the width measures read a telescope and
-- nothing in this file uses the slot, so the smallest inert one will do
ins1 : Slots Γ
ins1 i = shared emptyᵉ

------------------------------------------------------------------
-- §1  THE SEED THAT DOUBLES.  evalSeed-caps / evalTms-caps.
--
-- `Tw k` is the k-fold self-product of natᵗ, and `seedDbl k` is the
-- CLOSED term that builds its inhabitant by k nested `caseᵗ`: each
-- level scrutinises the level below (wrapped in inlᵗ, so the left
-- branch always fires), binds it, and returns the PAIR of that binding
-- with itself.  Six syntax nodes buy one doubling of the value.
--
-- This is the shape the Caps-Face memo predicted and never gated —
-- "a step function with d nested cases, each pairing the binding above
-- it with itself, turns an input of size 1 into a value of size
-- Θ(2 ^ d) out of syntax of size Θ(d)".  Here it is, machine-checked
------------------------------------------------------------------

Tw : ℕ → Ty
Tw zero    = natᵗ
Tw (suc k) = Tw k ×ᵗ Tw k

seedDbl : (k : ℕ) → Tm Γ [] [] [] (Tw k)
seedDbl zero    = nat̂ 0
seedDbl (suc k) =
  caseᵗ (inlᵗ (seedDbl k))
        (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))
        (varᵗ (here refl))

-- the two closed forms, PROVEN for all k rather than sampled: the
-- syntax grows by six per level and the value doubles and adds one
dblV : ℕ → ℕ
dblV zero    = 1
dblV (suc k) = suc (dblV k + dblV k)

seed-val-rec : ∀ k → sizeᵛ (Tw k) (evalTm (seedDbl k)) ≡ dblV k
seed-val-rec zero    = refl
seed-val-rec (suc k) = cong (λ z → suc (z + z)) (seed-val-rec k)

seed-size-rec : ∀ k → sizeᵗ (seedDbl (suc k)) ≡ 6 + sizeᵗ (seedDbl k)
seed-size-rec k =
  cong (λ z → suc (suc z))
       (trans (+-assoc (sizeᵗ (seedDbl k)) 3 1)
              (+-comm (sizeᵗ (seedDbl k)) 4))

-- the table.  `sizeStep S S` is the whole of what one j buys when the
-- entry cap S is read at the term's own size — the tightest honest S,
-- since the cap is at least the enclosing program's size
_ : sizeᵗ (seedDbl 4)  ≡ 25
_ = refl
_ : dblV 4             ≡ 31
_ = refl
_ : sizeStep 25 25     ≡ 1275
_ = refl                        -- one j is ample here

_ : sizeᵗ (seedDbl 8)  ≡ 49
_ = refl
_ : dblV 8             ≡ 511
_ = refl
_ : sizeStep 49 49     ≡ 4851
_ = refl                        -- still ample

_ : sizeᵗ (seedDbl 12) ≡ 73
_ = refl
_ : dblV 12            ≡ 8191
_ = refl
_ : sizeStep 73 73     ≡ 10731
_ = refl                        -- the last row one j survives

-- THE REFUTATION.  k = 13: a closed term of size 79 whose value has
-- size 16383, against a one-j budget of 12561
_ : sizeᵗ (seedDbl 13) ≡ 79
_ = refl
_ : dblV 13            ≡ 16383
_ = refl
_ : sizeStep 79 79     ≡ 12561
_ = refl

seed-one-j-refuted : (sizeStep 79 79 <ᵇ dblV 13) ≡ true
seed-one-j-refuted = refl

-- AND IT IS NOT A CONSTANT SLACKENING.  At k = 20 the same one j is
-- given a cap FOUR TIMES the term's size and still loses
_ : sizeᵗ (seedDbl 20) ≡ 121
_ = refl
_ : dblV 20            ≡ 2097151
_ = refl
_ : sizeStep 484 484   ≡ 468996
_ = refl

seed-one-j-refuted-4x : (sizeStep 484 484 <ᵇ dblV 20) ≡ true
seed-one-j-refuted-4x = refl

------------------------------------------------------------------
-- §2  THE STEP FUNCTION THAT DOUBLES.  mapFrame-caps / scanFrame-caps.
--
-- The same ladder with the input variable at the bottom, so what gets
-- copied 2^k times is the ARRIVING PAYLOAD rather than a literal.
-- `applyFn (fnDbl k) v` is the 2^k-fold self-pairing of v.
--
-- It falls much earlier than §1 because the affine form here is
-- `sizeStep S s` with s the INPUT's size — one, for a nat — so the
-- budget is 3S rather than ~2S²
------------------------------------------------------------------

fnDbl : (k : ℕ) → Fn Γ [] [] [] natᵗ (Tw k)
fnDbl zero    = varᵗ (here refl)
fnDbl (suc k) =
  caseᵗ (inlᵗ (fnDbl k))
        (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))
        (varᵗ (here refl))

fn-val-rec : ∀ k (v : ℕ) → sizeᵛ (Tw k) (applyFn (fnDbl k) v) ≡ dblV k
fn-val-rec zero    v = refl
fn-val-rec (suc k) v = cong (λ z → suc (z + z)) (fn-val-rec k v)

_ : sizeᵗ (fnDbl 5)  ≡ 31
_ = refl
_ : dblV 5           ≡ 63
_ = refl
_ : sizeStep 31 1    ≡ 93
_ = refl                        -- one j still holds, barely

-- THE REFUTATION, on a value of size 127
_ : sizeᵗ (fnDbl 6)  ≡ 37
_ = refl
_ : dblV 6           ≡ 127
_ = refl
_ : sizeStep 37 1    ≡ 111
_ = refl

fn-one-j-refuted : (sizeStep 37 1 <ᵇ dblV 6) ≡ true
fn-one-j-refuted = refl

-- with the cap read at TEN TIMES the step function's size, and the
-- payload ten times a nat, the same family beats it at k = 14
_ : sizeᵗ (fnDbl 14)  ≡ 85
_ = refl
_ : dblV 14           ≡ 32767
_ = refl
_ : sizeStep 850 10   ≡ 17850
_ = refl

fn-one-j-refuted-10x : (sizeStep 850 10 <ᵇ dblV 14) ≡ true
fn-one-j-refuted-10x = refl

------------------------------------------------------------------
-- §3  HOW MANY j IT ACTUALLY WANTS.  The replacement candidate.
--
-- `iterSize S j s` is the cap after j folds.  Each j multiplies by
-- at least 2S, so the j the doubling ladder needs is
-- log_{2S} (2 ^ k) — LOGARITHMIC in the value's size and therefore
-- LINEAR-with-a-tiny-constant in the syntax.  Every row below closes
-- at j′ ≤ 3, against a sizeᵗ of 85, 121 and 145 — so `j′ = sizeᵗ` is
-- nowhere near tight on any of them.
--
-- That is the shape the caps face could carry: `j′ = sizeᵗ f` is one
-- fold per syntax node, it is ≤ cSize by the clause's own hypothesis,
-- and it is exactly the per-frame charge cascadeGo-charge already
-- budgets (`j ≤ D * cSize`).  MEASURED HERE: that it is not tight on
-- these rows.  NOT measured here: that it is an upper bound in
-- general — see the flag at the foot
------------------------------------------------------------------

-- §1's worst row, k = 20: value 2097151 against the cap after j folds
_ : iterSize 121 1 121 ≡ 29403
_ = refl
_ : iterSize 121 2 121 ≡ 7115647
_ = refl

seed-two-j-suffices : (dblV 20 ≤ᵇ iterSize 121 2 121) ≡ true
seed-two-j-suffices = refl

-- §2's worst row, k = 14: value 32767 from a step function of size 85
_ : iterSize 85 1 1 ≡ 255
_ = refl
_ : iterSize 85 2 1 ≡ 43435
_ = refl

fn-two-j-suffices : (dblV 14 ≤ᵇ iterSize 85 2 1) ≡ true
fn-two-j-suffices = refl

-- and the ladder pushed past where the value is computable: k = 24 is a
-- value of size 33554431 out of a term of size 145, closed by THREE j
_ : dblV 24          ≡ 33554431
_ = refl
_ : iterSize 145 3 145 ≡ 3548641695
_ = refl

seed-three-j-suffices : (dblV 24 ≤ᵇ iterSize 145 3 145) ≡ true
seed-three-j-suffices = refl

------------------------------------------------------------------
-- §4  THE μ EDGE'S WIDTH.  unfoldμ-caps, the half the ruling calls
-- riskiest — and the affine form is refuted, EXPONENTIALLY.
--
-- Hop-Descent-Probe's μwide already showed dWᵉ is not ⊔-stable across
-- an unfold (0 ↦ 6).  Its reading was that the true bound is "affine
-- in the plug's width with the pmO/pmI slopes".  It is not, and the
-- reason is structural rather than a missing coefficient:
--
--     innWᵉ (scanᵉ f z e) = (pmIᵗ 0 f ⊔ 1) ^ (outWᵉ e) * (…)
--
-- The source's width sits in an EXPONENT.  Put the μ-var in that
-- source — under the defer that makes it legal — and the unfolding
-- raises the exponent from 0 to the μ's own outW.
--
-- THE SHAPE.  `μbody m` emits observables: an `ofᵉ` of m+1 elements,
-- the first a deferred `mergeAllᵉ (scanᵉ f z (varᵉ …))` and the rest
-- inert.  So outWᵉ (μᵉ (μbody m)) = suc m, dWᵉ (μᵉ (μbody m)) = 0
-- (the var is a zero-width leaf under the defer), and after the
-- unfold the defer's body is a scan whose source has width suc m.
--
-- `dupFn` is the step function that makes the exponent's base 2: it
-- reads its accumulator through `fstᵗ` in TWO branches of an ofᵉ, so
-- pmOᵉ of its body — and hence pmIᵗ 0 of the function — is 2
------------------------------------------------------------------

-- the accumulator-duplicating scan step: (obs natᵗ ×ᵗ obs natᵗ) ↦ obs natᵗ
dupFn : Fn Γ [] (obs natᵗ ∷ []) [] (obs natᵗ ×ᵗ obs natᵗ) (obs natᵗ)
dupFn = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
                            ∷ fstᵗ (varᵗ (here refl)) ∷ [])))

-- base 2, machine-checked: this is the exponent's base in innWᵉ's
-- scan clause, and the whole §4 finding rests on it being ≥ 2
_ : pmIᵗ 1 ins1 0 dupFn ≡ 2
_ = refl

dupSeed : Tm Γ [] (obs natᵗ ∷ []) [] (obs natᵗ)
dupSeed = strmᵗ emptyᵉ

-- THE DEFERRED BODY: a scan over the μ-var, merged.  Legal because
-- deferᵉ is what moves Δᵍ into Δ
μscan : Exp Γ [] (obs natᵗ ∷ []) [] natᵗ
μscan = mergeAllᵉ (scanᵉ dupFn dupSeed (varᵉ (here refl)))

-- an inert element, so the μ's own outW can be dialled with m
inert : Tm Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
inert = strmᵗ emptyᵉ

μbody0 : Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
μbody0 = ofᵉ (strmᵗ (deferᵉ μscan) ∷ [])

μbody1 : Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
μbody1 = ofᵉ (strmᵗ (deferᵉ μscan) ∷ inert ∷ [])

μbody2 : Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
μbody2 = ofᵉ (strmᵗ (deferᵉ μscan) ∷ inert ∷ inert ∷ [])

μbody3 : Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
μbody3 = ofᵉ (strmᵗ (deferᵉ μscan) ∷ inert ∷ inert ∷ inert ∷ [])

μbody4 : Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
μbody4 = ofᵉ (strmᵗ (deferᵉ μscan) ∷ inert ∷ inert ∷ inert ∷ inert ∷ [])

-- THE ENTRY QUANTITIES.  Before the unfold, dW is 0 on every rung —
-- exactly as μwide reported — while outW is the dial
_ : outWᵉ 1 ins1 (μᵉ μbody0) ≡ 1
_ = refl
_ : dWᵉ 1 ins1 (μᵉ μbody0)   ≡ 0
_ = refl
_ : outWᵉ 1 ins1 (μᵉ μbody4) ≡ 5
_ = refl
_ : dWᵉ 1 ins1 (μᵉ μbody4)   ≡ 0
_ = refl

-- AND AFTER.  0 ↦ (suc m) * 2 ^ (suc m), doubling per rung while the
-- entry width and the entry SIZE both move by one
_ : dWᵉ 1 ins1 (unfoldμ μbody0) ≡ 2
_ = refl
_ : dWᵉ 1 ins1 (unfoldμ μbody1) ≡ 8
_ = refl
_ : dWᵉ 1 ins1 (unfoldμ μbody2) ≡ 24
_ = refl
_ : dWᵉ 1 ins1 (unfoldμ μbody3) ≡ 64
_ = refl
_ : dWᵉ 1 ins1 (unfoldμ μbody4) ≡ 160
_ = refl

-- the sizes, so the growth can be read against the SIZE hypothesis
-- unfoldμ-caps actually carries
_ : sizeᵉ (μᵉ μbody0) ≡ 18
_ = refl
_ : sizeᵉ (μᵉ μbody4) ≡ 26
_ = refl

-- THE REFUTATION.  Every entry quantity on this ladder moves by a
-- CONSTANT per rung — one inert literal, so sizeᵉ (μᵉ body) goes
-- 18, 20, 22, 24, 26 and outWᵉ (μᵉ body) goes 1, 2, 3, 4, 5 — while
-- dWᵉ of the unfolding MORE THAN DOUBLES: 2, 8, 24, 64, 160.  So no
-- affine function of any of them bounds the family, whatever the
-- coefficients.  Stated as the ratio, on the two steepest rungs
μ-doubles-3 : (2 * dWᵉ 1 ins1 (unfoldμ μbody2)
                 <ᵇ dWᵉ 1 ins1 (unfoldμ μbody3)) ≡ true
μ-doubles-3 = refl

μ-doubles-4 : (2 * dWᵉ 1 ins1 (unfoldμ μbody3)
                 <ᵇ dWᵉ 1 ins1 (unfoldμ μbody4)) ≡ true
μ-doubles-4 = refl

-- and the affine candidate the μwide memo actually proposed, read at
-- the most generous syntactic coefficient available (the μ's own size
-- as the multiplier, its own outW as the variable): beaten at m = 4
μ-affine-refuted : (dWᵉ 1 ins1 (unfoldμ μbody4)
                      ≤ᵇ sizeᵉ (μᵉ μbody4) * outWᵉ 1 ins1 (μᵉ μbody4)) ≡ false
μ-affine-refuted = refl

-- 160 against 130, and the gap only widens: two rungs further on it is
-- 896 against 210.  The entry quantities are LINEAR in the rung and the
-- unfolding's width is EXPONENTIAL in it, so the crossing is permanent
μbody6 : Exp Γ (obs natᵗ ∷ []) [] [] (obs natᵗ)
μbody6 = ofᵉ (strmᵗ (deferᵉ μscan) ∷ inert ∷ inert ∷ inert
            ∷ inert ∷ inert ∷ inert ∷ [])

_ : outWᵉ 1 ins1 (μᵉ μbody6)   ≡ 7
_ = refl
_ : sizeᵉ (μᵉ μbody6)          ≡ 30
_ = refl
_ : dWᵉ 1 ins1 (unfoldμ μbody6) ≡ 896
_ = refl

μ-affine-refuted-6 : (dWᵉ 1 ins1 (unfoldμ μbody6)
                        ≤ᵇ sizeᵉ (μᵉ μbody6) * outWᵉ 1 ins1 (μᵉ μbody6)) ≡ false
μ-affine-refuted-6 = refl

------------------------------------------------------------------
-- §5  AND WHY THAT IS FINE.  `foldStep S w = S ^ suc w`.
--
-- The width recurrence's per-j increment is already an exponential
-- with the SIZE cap as its base, so §4's 2 ^ (suc m) is swallowed by
-- ONE j on every rung, with the entire base to spare.  The width half
-- of unfoldμ-caps does not want an affine form; it wants foldStep,
-- which is what the recurrence gives it.
--
-- Read at the tightest honest caps: S = sizeᵉ (μᵉ body) = 26, W = its
-- own dW = 0
------------------------------------------------------------------

_ : foldStep 26 0 ≡ 26
_ = refl

μ-one-j-misses-width : (dWᵉ 1 ins1 (unfoldμ μbody4) ≤ᵇ foldStep 26 0) ≡ false
μ-one-j-misses-width = refl

-- 160 against 26: ONE j read at W = 0 is NOT enough either, and for a
-- reason that is bookkeeping rather than growth — the entry dW is
-- genuinely ZERO on this family, so the first foldStep has nothing in
-- its exponent.  The second has the whole base, and closes it by 38
-- orders of magnitude
_ : foldStep 26 (foldStep 26 0) ≡ 26 ^ 27
_ = refl
_ : iterFold 26 2 0 ≡ 26 ^ 27
_ = refl

μ-two-j-covers-width : (dWᵉ 1 ins1 (unfoldμ μbody4) ≤ᵇ iterFold 26 2 0) ≡ true
μ-two-j-covers-width = refl

-- and the SIZE half of the same edge, which nobody has gated either:
-- unfolding replaces each var occurrence by the whole μ, so the growth
-- is the occurrence count times the μ's size — quadratic in the entry
-- size, hence inside ONE sizeStep
_ : sizeᵉ (unfoldμ μbody4) ≡ 50
_ = refl

μ-one-j-covers-size : (sizeᵉ (unfoldμ μbody4) ≤ᵇ sizeStep 26 26) ≡ true
μ-one-j-covers-size = refl

------------------------------------------------------------------
-- §6  THE RECEIPT THAT LANDED, GATED.  `j′ = sizeᵗ` — one iterSize
-- fold per syntax node — against every row §1 and §2 measure.
--
-- These are the regression set for `evalWith-iterSize` /
-- `applyFn-iterSize` / `evalTm-iterSize` (Caps-Face): the proven bound
-- is `sizeᵛ (evalWith tm env) ≤ iterSize S (sizeᵗ tm) V` for ANY S ≥ 1
-- and any V bounding the environment, so the gates below are read at
-- the WORST admissible base, S = 1, where one fold is only
-- `s ↦ suc (2 s)`.  Every real instantiation has S = Caps.cSize c ≥ 2
-- and is therefore slacker still.
--
-- Two shapes of row: the first pair EVALUATES, so it gates the lemma's
-- own left-hand side; the rest read `dblV`, which seed-val-rec and
-- fn-val-rec prove IS that left-hand side for all k
------------------------------------------------------------------

-- evaluated, both sides: a closed term of size 49 whose value has size
-- 511, against 49 folds from an empty environment
_ : (sizeᵛ {Γ = Γ} (Tw 8) (evalTm (seedDbl 8))
       ≤ᵇ iterSize 1 (sizeᵗ (seedDbl 8)) 0)
      ≡ true
_ = refl

-- and the step-function face at the same rung, seeded at the payload's
-- own size (a nat, so 1)
_ : (sizeᵛ {Γ = Γ} (Tw 6) (applyFn (fnDbl 6) 0)
       ≤ᵇ iterSize 1 (sizeᵗ (fnDbl 6)) 1)
      ≡ true
_ = refl

-- §1's REFUTING row, k = 13 — the one that beat a single j — closed by
-- the syntax-linear receipt with 79 folds
seed-syntax-receipt-13 : (dblV 13 ≤ᵇ iterSize 1 (sizeᵗ (seedDbl 13)) 0) ≡ true
seed-syntax-receipt-13 = refl

-- §1's worst row, k = 20: 2097151 against 121 folds
seed-syntax-receipt-20 : (dblV 20 ≤ᵇ iterSize 1 (sizeᵗ (seedDbl 20)) 0) ≡ true
seed-syntax-receipt-20 = refl

-- and the row past where the value is computable, k = 24: 33554431
-- against 145 folds
seed-syntax-receipt-24 : (dblV 24 ≤ᵇ iterSize 1 (sizeᵗ (seedDbl 24)) 0) ≡ true
seed-syntax-receipt-24 = refl

-- §2's REFUTING row, k = 6, on a value of size 127 out of 37 nodes
fn-syntax-receipt-6 : (dblV 6 ≤ᵇ iterSize 1 (sizeᵗ (fnDbl 6)) 1) ≡ true
fn-syntax-receipt-6 = refl

-- §2's worst row, k = 14, at the slackened payload the §2 table uses
fn-syntax-receipt-14 : (dblV 14 ≤ᵇ iterSize 1 (sizeᵗ (fnDbl 14)) 10) ≡ true
fn-syntax-receipt-14 = refl

------------------------------------------------------------------
-- §7  THE WIDTH HALF'S OWN GATE — where ONE foldStep per syntax node
-- does and does not dominate, read off the width recurrence's clauses
-- rather than off a program.
--
-- The size half (§6) is settled: `sizeStep` dominates EVERY term
-- constructor with one fold each, so `evalWith-iterSize` needs no
-- side conditions.  The width half is not uniform, and this section
-- pins down exactly which clause breaks it.
--
-- READ THE CLAUSE, NOT THE PROGRAM.  A structural induction over an
-- expression arrives at each node with all its children's out/inn/dW
-- already bounded by ONE accumulated number, M — and M is the ITERATE,
-- unrelated to the step base S.  So each clause of `innWᵉ` / `outWᵉ`
-- becomes an arithmetic obligation "clause read at M ≤ foldStep S M",
-- at the worst honest base S = 2.  The three that matter:
--
--   mapᵉ f e     innWᵗ f + (pmIᵗ 0 f ⊔ 1) * innWᵉ e   ↦   M * M + M
--   mergeAllᵉ e  outWᵉ e * innWᵉ e                     ↦   M * M
--   scanᵉ f z e  (pmIᵗ 0 f ⊔ 1) ^ outWᵉ e
--                  * (innWᵗ f + innWᵗ z + innWᵉ e + 1) ↦   M ^ M * (3 M + 1)
--
-- The first two FIT in one fold and the third does not, by orders of
-- magnitude — the source's width sits in an EXPONENT whose base is
-- also at M, so the clause is M ^ M against a budget of S ^ (1 + M).
------------------------------------------------------------------

-- mapᵉ, one fold, at the two tightest rungs and beyond
map-one-fold-2 : (2 * 2 + 2 ≤ᵇ foldStep 2 2) ≡ true      -- 6 against 8
map-one-fold-2 = refl
map-one-fold-3 : (3 * 3 + 3 ≤ᵇ foldStep 2 3) ≡ true      -- 12 against 16
map-one-fold-3 = refl
map-one-fold-6 : (6 * 6 + 6 ≤ᵇ foldStep 2 6) ≡ true      -- 42 against 128
map-one-fold-6 = refl

-- mergeAllᵉ (and its three *All siblings, same clause), one fold
merge-one-fold-3 : (3 * 3 ≤ᵇ foldStep 2 3) ≡ true        -- 9 against 16
merge-one-fold-3 = refl
merge-one-fold-6 : (6 * 6 ≤ᵇ foldStep 2 6) ≡ true        -- 36 against 128
merge-one-fold-6 = refl

-- scanᵉ, ONE FOLD, REFUTED — and not by a factor
scan-one-fold-refuted-4 : (foldStep 2 4 <ᵇ 4 ^ 4 * (3 * 4 + 1)) ≡ true
scan-one-fold-refuted-4 = refl                           -- 32 against 3328

scan-one-fold-refuted-6 : (foldStep 2 6 <ᵇ 6 ^ 6 * (3 * 6 + 1)) ≡ true
scan-one-fold-refuted-6 = refl                           -- 128 against 887 328

-- AND THE REPAIR COSTS NO RECEIPT.  Two folds swallow the same rows,
-- and a `scanᵉ` node HAS the folds to spend: it carries THREE children,
-- each at least one syntax node, so a budget of `sizeᵉ (scanᵉ f z e)`
-- = suc (sizeᵗ f + sizeᵗ z + sizeᵉ e) leaves three folds over the
-- LARGEST child.  The induction has to be organised at the MAX of the
-- children rather than at their running sum — which is the whole of
-- what this section says has to change
scan-two-folds-4 : (4 ^ 4 * (3 * 4 + 1) ≤ᵇ iterFold 2 2 4) ≡ true
scan-two-folds-4 = refl

scan-two-folds-6 : (6 ^ 6 * (3 * 6 + 1) ≤ᵇ iterFold 2 2 6) ≡ true
scan-two-folds-6 = refl

------------------------------------------------------------------
-- §8  THE SECOND THING THE WIDTH HALF NEEDS, AND THE CAP DOES NOT
-- CARRY IT: `innWᵉ` OF A SLOT DEF.
--
-- Every eval-cluster member concludes `valCaps?`, whose second conjunct
-- is `pWᵛ ≤ cWid`, so the width of an EVALUATED value has to come out
-- of the size hypothesis (there is no innW/outW hypothesis on the way
-- in).  Going through size means bounding `outWᵉ` and `innWᵉ` by the
-- syntax — and that stops dead at `input i`, whose measures descend
-- into the slot's def on slot fuel while `sizeᵉ (input i)` is 1.
--
-- The cap's slot side condition is `slotCaps?`, and its shared clause
-- bounds exactly two things: `sizeᵉ d ≤ B` and `pWᵉ n sl d ≤ W`.  It
-- does NOT bound `innWᵉ n sl d`, and pW cannot be made to — the two are
-- independent, because innW reads the STEP FUNCTION's embedded
-- observables while outW/dW read the source's.
--
-- Here is a def where they separate: an ofᵉ of three literals inside a
-- map's step function, over an empty source.  pW is zero on both halves
-- and innW is three, and the gap widens with the of-list
------------------------------------------------------------------

iwDef : Exp Γ [] [] [] (obs natᵗ)
iwDef = mapᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])))
             (emptyᵉ {t = natᵗ})

_ : outWᵉ 1 ins1 iwDef ≡ 0
_ = refl
_ : dWᵉ 1 ins1 iwDef   ≡ 0
_ = refl
_ : pWᵉ 1 ins1 iwDef   ≡ 0
_ = refl
_ : innWᵉ 1 ins1 iwDef ≡ 3
_ = refl

-- so the slot side condition is satisfied at W = 0 while the quantity
-- the width induction needs at `input i` is 3.  No W read off pW alone
-- bounds it
iw-escapes-pW : (pWᵉ 1 ins1 iwDef <ᵇ innWᵉ 1 ins1 iwDef) ≡ true
iw-escapes-pW = refl

------------------------------------------------------------------
-- §9  THE FIVE MEMBERS, LANDED — the receipts they actually carry,
-- gated.  All five are now GROUND in Caps-Face over three pieces:
-- `wid-iterFold` (one foldStep per syntax node, §7's shape),
-- `slotsCaps?-slotWid` (§8's leaf), and the size receipts §6 already
-- gates.  What is new here is the ARITHMETIC each member's j′ is:
--
--     evalTms / evalSeed   j′ = sizeᵗ + suc K
--     mapFrame             j′ = sizeᵗ fn + suc K
--     scanFrame            j′ = length vals * suc (sizeᵗ fn) + suc K
--     unfoldμ              j′ = suc B + suc K
--
-- with B the entry size cap and K the size cap at `j + a` — the width
-- half is ALWAYS `suc K` more folds than the size half, because the
-- width is read off the RESULT's size and iterFold outruns iterSize.
------------------------------------------------------------------

-- THE LIFT, which is the whole of the width half: a width read at the
-- seed `suc W` — the leaf bound the slot telescope supplies — is a
-- width read at the cap ONE fold on, so the bound slides up by the
-- folds the size receipt already bought
lift-gate-1 : (iterFold 2 1 1 ≤ᵇ iterFold 2 2 0) ≡ true   -- 4 against 8
lift-gate-1 = refl
lift-gate-2 : (iterFold 2 1 2 ≤ᵇ iterFold 2 2 1) ≡ true   -- 8 against 32
lift-gate-2 = refl
lift-gate-3 : (iterFold 2 2 1 ≤ᵇ iterFold 2 3 0) ≡ true   -- 32 against 512
lift-gate-3 = refl

-- unfoldμ-caps, THE SIZE HALF.  size-unfoldμ (now a shared prerequisite
-- in .Keeps-Ring rather than a wet-side lemma) bounds the unfolding by
-- the μ's size SQUARED, and `suc B` folds of iterSize cover a factor of
-- B because each fold at least doubles (iterSize-2^)
μ-size-receipt-4 : (sizeᵉ (unfoldμ μbody4)
                      ≤ᵇ sizeᵉ (μᵉ μbody4) * sizeᵉ (μᵉ μbody4)) ≡ true
μ-size-receipt-4 = refl                        -- 50 against 676

μ-size-fits-4 : (sizeᵉ (μᵉ μbody4) * sizeᵉ (μᵉ μbody4)
                   ≤ᵇ 2 ^ suc (sizeᵉ (μᵉ μbody4)) * sizeᵉ (μᵉ μbody4)) ≡ true
μ-size-fits-4 = refl                           -- 676 against 26 * 2 ^ 27

-- unfoldμ-caps, THE WIDTH HALF, on §4's ladder — the family that
-- refuted every affine reading.  The landed bound is
-- `dWᵉ (unfoldμ body) ≤ iterFold S (sizeᵉ (unfoldμ body)) (suc W)` read
-- at the worst admissible S = 2 and W = 0, so the receipt buys FIFTY
-- folds on μbody4.  Three already cover the ladder's whole measured
-- range, (m+1) * 2 ^ (m+1) — which is what "the width half does not
-- want an affine form" means once it is a theorem rather than a table
μ-width-receipt-4 : (dWᵉ 1 ins1 (unfoldμ μbody4) ≤ᵇ iterFold 2 3 1) ≡ true
μ-width-receipt-4 = refl                       -- 160 against 2 ^ 33

μ-width-receipt-6 : (dWᵉ 1 ins1 (unfoldμ μbody6) ≤ᵇ iterFold 2 3 1) ≡ true
μ-width-receipt-6 = refl                       -- 896 against 2 ^ 33

-- scanFrame-caps, THE RUNG.  scanVals threads the accumulator, and each
-- rung costs one PAIRING (the arriving payload is paired with the
-- stored accumulator, exactly one sizeStep) plus one fold per node of
-- the step function — so `suc (sizeᵗ fn)` per payload, `length vals` of
-- them.  Gated as the composition it is: one rung off §2's k = 6 step
-- function beats the value that refuted a single j
scan-one-rung-6 : (dblV 6 ≤ᵇ iterSize 1 (1 * suc (sizeᵗ (fnDbl 6))) 1) ≡ true
scan-one-rung-6 = refl

scan-three-rungs-6 : (dblV 6 ≤ᵇ iterSize 1 (3 * suc (sizeᵗ (fnDbl 6))) 1) ≡ true
scan-three-rungs-6 = refl

------------------------------------------------------------------
-- THE READING (2026-08-01).
--
-- AFFINE IS REFUTED ON ALL THREE AXES the ruling named, and none of
-- the three refutations is by a constant:
--
--   evalSeed / evalTms   one j (sizeStep S S at S = the term's size)
--     is beaten at k = 13, and at a 4× slackened cap by k = 16.  The
--     growth is 2 ^ (sizeᵗ / 6), proven for all k.
--   mapFrame / scanFrame  one j (sizeStep S s) is beaten at k = 6, on
--     a value of size 127; a 10× slackened cap survives only to k = 14.
--   unfoldμ, width       the ratio DOUBLES per rung while the entry
--     syntax grows by one node, so no affine form in any entry
--     quantity survives.
--
-- WHAT SURVIVES, and it is the whole content of the probe: the
-- recurrence's own per-j increments are multiplicative (sizeStep) and
-- exponential (foldStep), so a HANDFUL of j covers every row —
-- j′ ≤ 3 on the size ladder up to a value of 33 million, j′ = 2 on the
-- μ width.  The receipt the cluster should carry is therefore
--
--     j′ = sizeᵗ f   (resp. sizeᵗ z, sizeᵉ body)
--
-- one fold per syntax node, which each clause's own hypothesis already
-- bounds by cSize, and which is exactly what cascadeGo-charge budgets
-- per frame.  That is a LINEAR receipt in the syntax, not an affine
-- bound on the value — a different shape from the one the ruling
-- proposed, and strictly cheaper than the tower fallback.
--
-- THE SIZE HALF IS NOW PROVEN rather than measured — see §6 and
-- Caps-Face's evalWith-iterSize — and it needed NO hypothesis relating
-- the term's size to S, which is what lets it instantiate at
-- S = Caps.cSize c.  THE WIDTH HALF IS NOT THE SAME SHAPE: §7 reads the
-- width recurrence clause by clause and finds exactly one constructor,
-- `scanᵉ`, that one fold cannot dominate.
--
-- AND THE CLUSTER IS NOW LANDED (2026-08-01).  mapFrame-caps,
-- scanFrame-caps, evalTms-caps, evalSeed-caps and unfoldμ-caps are all
-- GROUND, and so is the width lemma `wid-iterFold` they rest on: one
-- foldStep per syntax node in exactly §7's shape — the induction
-- organised at the MAX of a node's children, one fold per non-scanᵉ
-- node and two per scanᵉ, funded by its three children.  §9 has the
-- rows.  What is left under them is §8's leaf, `slotsCaps?-slotWid`.
--
-- NOT MEASURED HERE, and flagged: whether a family exists whose
-- required j′ exceeds sizeᵗ.  The scan clause's exponent base is
-- `pmIᵗ 0 f ⊔ 1`, which is itself syntax-bounded, and scanVals
-- ITERATES applyFn once per payload — so a scan frame's receipt is
-- the payload count times the per-application j′, which is the
-- iteration side cascadeGo-charge owns rather than this cluster
------------------------------------------------------------------
