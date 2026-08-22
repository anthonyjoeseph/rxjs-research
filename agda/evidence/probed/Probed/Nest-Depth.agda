------------------------------------------------------------------
-- TARGET: depth-all-bound
--
-- THE CANDIDATE MEASURE FOR THE RESTATEMENT, instantiated before any of
-- it is written into `src`.  `depth-all-bound` is refuted
-- (Refuted.Depth-Nest) because its cap is linear in the syntax while
-- `depthE` grows in `wraps × ticks`, and the width family cannot supply
-- the product either — `width-route-absurd` refutes all four measures at
-- once, because a wrap layer multiplies width by one.  So the
-- restatement needs a NEW measure, and this file is the cheap test of
-- one before a mutual block is touched on the strength of a guess.
--
-- THE MEASURE, read off the mechanism rather than fitted: a `*All` layer
-- is worth one `suc`, because that is what `depthFrame` at `thru-outer`
-- charges; a `scanᵉ` is worth its SOURCE'S PAYLOAD COUNT times its step
-- function's layers, because the accumulator is re-wrapped once per
-- delivered payload and `depthFrame … (scan-f …)` charges the emissions
-- nothing (`burst-scf-zero`).  That is the `length vals * suc (sizeᵗ fn)`
-- shape `scanFrame-caps` already pays, arriving at the depth face.
--
-- LOAD-BEARING, and in the strongest form available: the rows do not ask
-- the measure to DOMINATE the depth, they ask it to EQUAL it, at both
-- crossings the refutation walks — 49 at four wraps over twelve ticks
-- and 204 at seven over twenty-nine.  A measure off by anything at all,
-- in either direction, fails these rows, and the two rows are 4·12+1 and
-- 7·29+1 so no single constant can satisfy both.  `flatRow` is the
-- non-degeneracy row: at zero wraps the product collapses and the
-- measure must fall back to 1, which is what says the other two rows are
-- reading the product and not the program's size.
--
-- SHAPES NOT COVERED, and they are the reason this stays evidence: only
-- `mergeAllᵉ` (no concat/switch/exhaust layer, whose queueing
-- `nodesNestMax` charges separately); only one scan, so a scan nested
-- inside another scan's step function is untested and is exactly where a
-- product of THREE factors would show up; no `input`/slot descent, so
-- the connect arc is unmeasured here and `slotsNestBelow` is the term
-- that would carry it; and no post-cascade state.
------------------------------------------------------------------
module Probed.Nest-Depth where

open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp  using (Ctx; Closed; Exp; Tm; Fn; natᵗ; obs; _×ᵗ_; nat̂;
  strmᵗ; fstᵗ; sndᵗ; pairᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; unit̂; bool̂; varᵗ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Frame-Width using (outWᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Path; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

------------------------------------------------------------------
-- the candidate measure
------------------------------------------------------------------

mutual
  nestDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  nestDᵉ sl (input i)              = 0
  nestDᵉ sl (ofᵉ ts)               = nestDᵗˢ sl ts
  nestDᵉ sl emptyᵉ                 = 0
  nestDᵉ sl (mapᵉ f e)             = nestDᵗ sl f + nestDᵉ sl e
  nestDᵉ sl (takeᵉ c e)            = nestDᵉ sl e
  -- THE PRODUCT: one re-wrap per delivered payload
  nestDᵉ {n = n} sl (scanᵉ f z e)  =
    nestDᵗ sl z + outWᵉ n sl e * nestDᵗ sl f + nestDᵉ sl e
  -- THE SPENDING ARC: one suc per *All layer
  nestDᵉ sl (mergeAllᵉ e)          = suc (nestDᵉ sl e)
  nestDᵉ sl (concatAllᵉ e)         = suc (nestDᵉ sl e)
  nestDᵉ sl (switchAllᵉ e)         = suc (nestDᵉ sl e)
  nestDᵉ sl (exhaustAllᵉ e)        = suc (nestDᵉ sl e)
  nestDᵉ sl (μᵉ e)                 = nestDᵉ sl e
  nestDᵉ sl (varᵉ x)               = 0
  nestDᵉ sl (deferᵉ e)             = nestDᵉ sl e

  nestDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
  nestDᵗ sl (varᵗ x)      = 0
  nestDᵗ sl unit̂          = 0
  nestDᵗ sl (bool̂ _)      = 0
  nestDᵗ sl (nat̂ _)       = 0
  nestDᵗ sl (pairᵗ a b)   = nestDᵗ sl a + nestDᵗ sl b
  nestDᵗ sl (fstᵗ p)      = nestDᵗ sl p
  nestDᵗ sl (sndᵗ p)      = nestDᵗ sl p
  nestDᵗ sl (inlᵗ a)      = nestDᵗ sl a
  nestDᵗ sl (inrᵗ a)      = nestDᵗ sl a
  nestDᵗ sl (caseᵗ s l r) = nestDᵗ sl s + nestDᵗ sl l + nestDᵗ sl r
  nestDᵗ sl (ifᵗ c a b)   = nestDᵗ sl c + nestDᵗ sl a + nestDᵗ sl b
  nestDᵗ sl (primᵗ _ a)   = nestDᵗ sl a
  nestDᵗ sl (strmᵗ e)     = nestDᵉ sl e

  nestDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestDᵗˢ sl []       = 0
  nestDᵗˢ sl (y ∷ ys) = nestDᵗ sl y + nestDᵗˢ sl ys

------------------------------------------------------------------
-- the harness: Refuted.Depth-Nest's family, which is where the
-- crossings were measured
------------------------------------------------------------------

gasN : ℕ → Gas
gasN zero    = g0
gasN (suc m) = gs (gasN m)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

Step : Set
Step = Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)

accᵗ : Step
accᵗ = fstᵗ (varᵗ (here refl))

wraps : ℕ → Step → Step
wraps zero    t = t
wraps (suc m) t = strmᵗ (mergeAllᵉ (ofᵉ (wraps m t ∷ [])))

nats : ℕ → List (Tm Γ₀ [] [] [] natᵗ)
nats zero    = []
nats (suc m) = nat̂ m ∷ nats m

seedᵗ : Tm Γ₀ [] [] [] (obs natᵗ)
seedᵗ = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

prog : ℕ → ℕ → Closed Γ₀ (obs natᵗ)
prog w k = scanᵉ (wraps w accᵗ) seedᵗ (ofᵉ (nats k))

rootProg : ℕ → ℕ → Closed Γ₀ natᵗ
rootProg w k = mergeAllᵉ (prog w k)

rootPath : Path Γ₀ natᵗ natᵗ
rootPath = root {Γ = Γ₀} {t = natᵗ}

------------------------------------------------------------------
-- §1  THE MEASURE PREDICTS THE DEPTH EXACTLY, at both crossings
------------------------------------------------------------------

-- LOAD-BEARING: 4·12+1, and the depth side is the 49 that refutes
-- `depth-all-bound`.
lowRow : depthE (gasN 70) (rootProg 4 12) rootPath 0 0
           (sched-init (rootProg 4 12) slots₀) (st-init (rootProg 4 12))
         ≡ nestDᵉ slots₀ (rootProg 4 12)
lowRow = refl

-- LOAD-BEARING: 7·29+1, and the depth side is the 204 that refutes
-- `depth-capped`'s three-cSize interface at 201.  No constant satisfies
-- this row and the one above at once.
highRow : depthE (gasN 215) (rootProg 7 29) rootPath 0 0
            (sched-init (rootProg 7 29) slots₀) (st-init (rootProg 7 29))
          ≡ nestDᵉ slots₀ (rootProg 7 29)
highRow = refl

-- LOAD-BEARING, as the non-degeneracy row: zero wraps collapses the
-- product, so a measure reading the program's SIZE rather than its
-- layer product cannot also pass this.
flatRow : nestDᵉ slots₀ (rootProg 0 5) ≡ 1
flatRow = refl

-- and the two products in closed form, so the rows above are legible as
-- arithmetic and not only as agreement
lowVal : nestDᵉ slots₀ (rootProg 4 12) ≡ 49
lowVal = refl

highVal : nestDᵉ slots₀ (rootProg 7 29) ≡ 204
highVal = refl
