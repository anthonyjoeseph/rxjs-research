------------------------------------------------------------------
-- THE NESTING MEASURE: how many `*All` layers a run can descend
-- through, as opposed to how many payloads travel abreast.
--
-- WHY IT IS NOT `Rx.Frame-Width`, and the distinction cost a refutation
-- to learn.  The width family measures payloads abreast, and a wrap
-- layer — `strmᵗ (mergeAllᵉ (ofᵉ (t ∷ [])))` — has `outWⱽ` equal to
-- `1 * innWⱽ (ofᵉ (t ∷ []))`: it multiplies by one and adds nothing, so
-- every measure over there is blind to how deeply a step function wraps
-- its own accumulator.  `Refuted.Depth-Nest.width-route-absurd` pins
-- that against the max of all four at once, 24 against a depth of 49.
--
-- THE TWO CLAUSES THAT CARRY IT, both read off the evaluator rather
-- than fitted to a number:
--
--   · a `*All` layer is worth ONE `suc`, because that is what
--     `depthFrame` at a `thru-outer` frame charges;
--   · a `scanᵉ` is worth its SOURCE'S PAYLOAD COUNT times its step
--     function's layers, because the accumulator is re-wrapped once per
--     delivered payload while the scan's own frame charges its
--     emissions nothing (`burst-scf-zero`).
--
-- which is the `length vals * suc (sizeᵗ fn)` shape `scanFrame-caps`
-- already pays on the size and width faces, arriving at the depth face.
--
-- The rows behind this shape live in `Probed.Nest-Depth`, and the
-- receipt they earned sits in the header of the statement they are
-- evidence about (`depth-all-burst`, the one arm of that face still
-- open): this measure equals `depthE` ON
-- THE NOSE — not merely dominates it — at three programs, the third of
-- which is a scan nested inside another scan's step function, and says
-- the product COMPOUNDS: one factor per nested scan, so the measure is
-- exponential in the program and no fixed-degree product of caps fields
-- could have replaced it.  A slot's own nesting is the part those rows
-- do not reach; it is charged in `slotNest`, not here.
--
-- AND THE DEPTH FACE'S CAP IS NOW READ OFF THIS MEASURE AND NOTHING
-- ELSE, its size term dropped, so at a root path over a slotless
-- context those rows pin the CAP as an equality rather than the measure
-- as an approximation.  That is what makes the equality load-bearing
-- rather than pleasing: a measure that merely dominated would leave the
-- face free to carry slack, and the face now has none to carry.
--
-- THE `input` CLAUSE CONTRIBUTES NOTHING, and a descending one was
-- TRIED AND IS STRUCTURALLY DEAD.  `outWⱽ`'s shape — descend into the
-- slot definition on slot fuel with a visited set — does not work here,
-- because the consumer fixes the fuel at the slot count `n`, which is a
-- VARIABLE: `nestDⱽ n [] sl (input i)` never reduces, and the parent
-- has no more fuel than the child it would recurse into, so there is no
-- inequality to prove even in principle.  The width family gets away
-- with it by threading `j` through its consumers; a measure read off a
-- `Sched` cannot.
--
-- So the slot's nesting is charged in `slotNest`, whose
-- `slotsNestBelow-step` is an equality at exactly the index the `input`
-- clause needs.  It charged the def's SIZE beside its nesting for as
-- long as the depth cap read both currencies; with the cap read off
-- nesting alone that summand was pure over-payment, and dropping it puts
-- the connect's charge and its payment back on the same number.  What
-- either version costs is any bound of a slot's nesting BY its size,
-- since an exponential quantity has none; those were feeding a
-- caps-conditioned interface that the depth refutations retire anyway.
------------------------------------------------------------------
module Rx.Nest-Depth where

open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; suc; _+_; _*_)

open import Rx.Exp using (Ctx; Exp; Tm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
  strmᵗ)
open import Rx.Frame-Width using (outWᵉ)
open import Rx.Slots using (Slots)

mutual
  nestDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  nestDᵉ sl (input i)             = 0
  nestDᵉ sl (ofᵉ ts)              = nestDᵗˢ sl ts
  nestDᵉ sl emptyᵉ                = 0
  nestDᵉ sl (mapᵉ f e)            = nestDᵗ sl f + nestDᵉ sl e
  nestDᵉ sl (takeᵉ c e)           = nestDᵉ sl e
  -- THE PRODUCT: one re-wrap per delivered payload
  nestDᵉ {n = n} sl (scanᵉ f z e) =
    nestDᵗ sl z + outWᵉ n sl e * nestDᵗ sl f + nestDᵉ sl e
  -- THE SPENDING ARC: one suc per *All layer
  nestDᵉ sl (mergeAllᵉ e)         = suc (nestDᵉ sl e)
  nestDᵉ sl (concatAllᵉ e)        = suc (nestDᵉ sl e)
  nestDᵉ sl (switchAllᵉ e)        = suc (nestDᵉ sl e)
  nestDᵉ sl (exhaustAllᵉ e)       = suc (nestDᵉ sl e)
  nestDᵉ sl (μᵉ e)                = nestDᵉ sl e
  nestDᵉ sl (varᵉ x)              = 0
  nestDᵉ sl (deferᵉ e)            = nestDᵉ sl e

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

  nestDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) →
    List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestDᵗˢ sl []       = 0
  nestDᵗˢ sl (y ∷ ys) = nestDᵗ sl y + nestDᵗˢ sl ys
