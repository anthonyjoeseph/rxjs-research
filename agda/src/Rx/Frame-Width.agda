------------------------------------------------------------------
-- THE FRAME WIDTH: how much work one subscribe frame can be made to
-- do, measured from the PROGRAM rather than from the size ledger.
--
-- This is round 3's escape.  hopD's scan clause charges (2 + pm)^V with
-- V the STORE anchor, and round3-anchor-indexed-absurd shows that any
-- work index reading such a charge re-anchors at capᴱ and closes the
-- three-edge loop that killed rounds 1 and 2.  The way out is to charge
-- the fold count instead — and a scan's fold count is its SOURCE's
-- per-frame payload count, which bottoms out in `ofᵉ` list lengths.
-- That is what these measures compute.
--
-- TWO MEASURES, because a *All multiplies them:
--
--   outWᵉ e   how many payloads e's subscribe frame can deliver
--   innWᵉ e   the widest observable that frame can EMIT
--
--     outWᵉ (mergeAllᵉ e) = outWᵉ e * innWᵉ e
--
-- entering every inner that every payload carries.  Neither bounds the
-- other, so both are needed, and each needs its own plug slope — hence
-- four functions rather than two.
--
-- AND TWO SLOPES, for the reason hopD needed pm and for the reason
-- three drafts of hopD's coefficient were refuted: a template may use
-- its bound variable more than once, so a coefficient here is the
-- FACTOR a plugged value's width is scaled by along paths to the
-- variable, never an occurrence count.  pmO is outW's slope, pmI is
-- innW's, and the *All clause needs BOTH by the product rule:
--
--   pmOᵉ k (mergeAllᵉ e) = outWᵉ e * pmIᵉ k e + pmOᵉ k e * innWᵉ e
--
-- A draft with one slope cannot state that clause at all.
--
-- WHERE THE TOWER IS: the scanᵉ clause, and only there.
--
--   innWᵉ (scanᵉ f z e) = (pmIᵗ 0 f ⊔ 1) ^ (outWᵉ e) * (…)
--
-- The accumulator is refolded once per arriving payload, and each fold
-- scales its width by the template's slope — so the exponent is the
-- SOURCE's payload count.  Syntax in, syntax out: no store quantity
-- appears anywhere in these definitions.  That is the whole point.
--
-- SLOT FUEL.  A share is reached by a connect, not by descending into
-- syntax, and a slot def may reference other slots — so `input` is not
-- structural and the recursion carries an explicit budget `j`, spent
-- one per connect.  The lexicographic order is (j, the expression), and
-- j is instantiated at the slot count because the connect descent
-- strictly drops `unconn`.
--
-- GATED, NOT GUESSED.  agda/probe/Frame-Work-Probe.agda measures nine
-- runs of the real evaluator, and the gate there checks these measures
-- against every one of them — the literal corpus, the duplication case,
-- the two-level amplification, and all three share routings.  A draft
-- that under-counts any of them is refuted on the spot, which is how
-- the plug slopes got their shape.
------------------------------------------------------------------
module Rx.Frame-Width where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≡ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; length)

open import Rx.Exp
open import Rx.Evaluator using (Slots; Slot; scripted; shared)

mutual
  -- slope of outW in the width of the value plugged at index k
  pmOᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmOᵉ j sl k (input i)       = 0
  pmOᵉ j sl k (ofᵉ ts)        = 0          -- outW of an ofᵉ is its LENGTH
  pmOᵉ j sl k emptyᵉ          = 0
  pmOᵉ j sl k (mapᵉ f e)      = pmOᵉ j sl k e
  pmOᵉ j sl k (takeᵉ c e)     = pmOᵉ j sl k e
  pmOᵉ j sl k (scanᵉ f z e)   = pmOᵉ j sl k e
  -- product rule: outW (mergeAll e) = outW e * innW e
  pmOᵉ j sl k (mergeAllᵉ e)   = outWᵉ j sl e * pmIᵉ j sl k e + pmOᵉ j sl k e * innWᵉ j sl e
  pmOᵉ j sl k (concatAllᵉ e)  = outWᵉ j sl e * pmIᵉ j sl k e + pmOᵉ j sl k e * innWᵉ j sl e
  pmOᵉ j sl k (switchAllᵉ e)  = outWᵉ j sl e * pmIᵉ j sl k e + pmOᵉ j sl k e * innWᵉ j sl e
  pmOᵉ j sl k (exhaustAllᵉ e) = outWᵉ j sl e * pmIᵉ j sl k e + pmOᵉ j sl k e * innWᵉ j sl e
  pmOᵉ j sl k (μᵉ e)          = pmOᵉ j sl k e
  pmOᵉ j sl k (varᵉ x)        = 0
  pmOᵉ j sl k (deferᵉ e)      = 0

  pmOᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  pmOᵗ j sl k (varᵗ x)      = 0
  pmOᵗ j sl k unit̂          = 0
  pmOᵗ j sl k (bool̂ _)      = 0
  pmOᵗ j sl k (nat̂ _)       = 0
  pmOᵗ j sl k (pairᵗ a b)   = pmOᵗ j sl k a ⊔ pmOᵗ j sl k b
  pmOᵗ j sl k (fstᵗ p)      = pmOᵗ j sl k p
  pmOᵗ j sl k (sndᵗ p)      = pmOᵗ j sl k p
  pmOᵗ j sl k (inlᵗ a)      = pmOᵗ j sl k a
  pmOᵗ j sl k (inrᵗ a)      = pmOᵗ j sl k a
  pmOᵗ j sl k (caseᵗ s l r) = pmOᵗ j sl (suc k) l ⊔ pmOᵗ j sl (suc k) r
                       ⊔ (pmIᵗ j sl 0 l ⊔ pmIᵗ j sl 0 r ⊔ 1) * pmOᵗ j sl k s
  pmOᵗ j sl k (ifᵗ c a b)   = pmOᵗ j sl k a ⊔ pmOᵗ j sl k b
  pmOᵗ j sl k (primᵗ _ a)   = 0
  pmOᵗ j sl k (strmᵗ e)     = pmOᵉ j sl k e

  -- slope of innW in the same
  pmIᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmIᵉ j sl k (input i)       = 0
  pmIᵉ j sl k (ofᵉ ts)        = pmIᵗˢ j sl k ts
  pmIᵉ j sl k emptyᵉ          = 0
  pmIᵉ j sl k (mapᵉ f e)      = pmIᵗ j sl (suc k) f + (pmIᵗ j sl 0 f ⊔ 1) * pmIᵉ j sl k e
  pmIᵉ j sl k (takeᵉ c e)     = pmIᵉ j sl k e
  -- the refold: the slope compounds once per fold
  pmIᵉ j sl k (scanᵉ f z e)   = (pmIᵗ j sl 0 f ⊔ 1) ^ (outWᵉ j sl e)
                         * (pmIᵗ j sl (suc k) f + pmIᵗ j sl k z + pmIᵉ j sl k e)
  pmIᵉ j sl k (mergeAllᵉ e)   = pmIᵉ j sl k e
  pmIᵉ j sl k (concatAllᵉ e)  = pmIᵉ j sl k e
  pmIᵉ j sl k (switchAllᵉ e)  = pmIᵉ j sl k e
  pmIᵉ j sl k (exhaustAllᵉ e) = pmIᵉ j sl k e
  pmIᵉ j sl k (μᵉ e)          = pmIᵉ j sl k e
  pmIᵉ j sl k (varᵉ x)        = 0
  pmIᵉ j sl k (deferᵉ e)      = 0

  pmIᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  pmIᵗ j sl k (varᵗ x)      = if varIx x ≡ᵇ k then 1 else 0
  pmIᵗ j sl k unit̂          = 0
  pmIᵗ j sl k (bool̂ _)      = 0
  pmIᵗ j sl k (nat̂ _)       = 0
  pmIᵗ j sl k (pairᵗ a b)   = pmIᵗ j sl k a ⊔ pmIᵗ j sl k b
  pmIᵗ j sl k (fstᵗ p)      = pmIᵗ j sl k p
  pmIᵗ j sl k (sndᵗ p)      = pmIᵗ j sl k p
  pmIᵗ j sl k (inlᵗ a)      = pmIᵗ j sl k a
  pmIᵗ j sl k (inrᵗ a)      = pmIᵗ j sl k a
  pmIᵗ j sl k (caseᵗ s l r) = (pmIᵗ j sl (suc k) l ⊔ pmIᵗ j sl (suc k) r)
                       + (pmIᵗ j sl 0 l ⊔ pmIᵗ j sl 0 r ⊔ 1) * pmIᵗ j sl k s
  pmIᵗ j sl k (ifᵗ c a b)   = pmIᵗ j sl k a ⊔ pmIᵗ j sl k b
  pmIᵗ j sl k (primᵗ _ a)   = 0
  pmIᵗ j sl k (strmᵗ e)     = pmOᵉ j sl k e

  pmIᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pmIᵗˢ j sl k []       = 0
  pmIᵗˢ j sl k (y ∷ ys) = pmIᵗ j sl k y ⊔ pmIᵗˢ j sl k ys

  outWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  -- a slot is reached by a CONNECT; the connect edge pays, not this
  -- A SHARE IS A CONNECT: descend into the slot's def, on slot fuel.
  -- Slot defs may reference slots, so this is not structural — j is the
  -- lexicographic outer measure and every connect spends one
  outWᵉ zero    sl (input i) = 0
  outWᵉ (suc j) sl (input i) with sl i
  ... | scripted _ = 0
  ... | shared d   = outWᵉ j sl d
  outWᵉ j sl (ofᵉ ts)        = length ts
  outWᵉ j sl emptyᵉ          = 0
  outWᵉ j sl (mapᵉ f e)      = outWᵉ j sl e
  outWᵉ j sl (takeᵉ c e)     = outWᵉ j sl e
  outWᵉ j sl (scanᵉ f z e)   = outWᵉ j sl e
  -- THE *All EDGE: every payload's inner is entered
  outWᵉ j sl (mergeAllᵉ e)   = outWᵉ j sl e * innWᵉ j sl e
  outWᵉ j sl (concatAllᵉ e)  = outWᵉ j sl e * innWᵉ j sl e
  outWᵉ j sl (switchAllᵉ e)  = outWᵉ j sl e * innWᵉ j sl e
  outWᵉ j sl (exhaustAllᵉ e) = outWᵉ j sl e * innWᵉ j sl e
  outWᵉ j sl (μᵉ e)          = outWᵉ j sl e
  outWᵉ j sl (varᵉ x)        = 0
  outWᵉ j sl (deferᵉ e)      = 0          -- crosses a tick

  innWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  innWᵉ zero    sl (input i) = 0
  innWᵉ (suc j) sl (input i) with sl i
  ... | scripted _ = 0
  ... | shared d   = innWᵉ j sl d
  innWᵉ j sl (ofᵉ ts)        = innWᵗˢ j sl ts
  innWᵉ j sl emptyᵉ          = 0
  innWᵉ j sl (mapᵉ f e)      = innWᵗ j sl f + (pmIᵗ j sl 0 f ⊔ 1) * innWᵉ j sl e
  innWᵉ j sl (takeᵉ c e)     = innWᵉ j sl e
  -- THE REFOLD, and the tower: the accumulator's width compounds once
  -- per fold, and the fold count is the SOURCE's payload count
  innWᵉ j sl (scanᵉ f z e)   = (pmIᵗ j sl 0 f ⊔ 1) ^ (outWᵉ j sl e)
                        * (innWᵗ j sl f + innWᵗ j sl z + innWᵉ j sl e + 1)
  innWᵉ j sl (mergeAllᵉ e)   = innWᵉ j sl e
  innWᵉ j sl (concatAllᵉ e)  = innWᵉ j sl e
  innWᵉ j sl (switchAllᵉ e)  = innWᵉ j sl e
  innWᵉ j sl (exhaustAllᵉ e) = innWᵉ j sl e
  innWᵉ j sl (μᵉ e)          = innWᵉ j sl e
  innWᵉ j sl (varᵉ x)        = 0
  innWᵉ j sl (deferᵉ e)      = 0

  innWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
  innWᵗ j sl (varᵗ x)      = 0
  innWᵗ j sl unit̂          = 0
  innWᵗ j sl (bool̂ _)      = 0
  innWᵗ j sl (nat̂ _)       = 0
  innWᵗ j sl (pairᵗ a b)   = innWᵗ j sl a ⊔ innWᵗ j sl b
  innWᵗ j sl (fstᵗ p)      = innWᵗ j sl p
  innWᵗ j sl (sndᵗ p)      = innWᵗ j sl p
  innWᵗ j sl (inlᵗ a)      = innWᵗ j sl a
  innWᵗ j sl (inrᵗ a)      = innWᵗ j sl a
  innWᵗ j sl (caseᵗ s l r) = (innWᵗ j sl l ⊔ innWᵗ j sl r) + (pmIᵗ j sl 0 l ⊔ pmIᵗ j sl 0 r ⊔ 1) * innWᵗ j sl s
  innWᵗ j sl (ifᵗ c a b)   = innWᵗ j sl a ⊔ innWᵗ j sl b
  innWᵗ j sl (primᵗ _ a)   = 0
  -- an obs-typed term denotes an observable; its width is that
  -- observable's frame width
  innWᵗ j sl (strmᵗ e)     = outWᵉ j sl e

  innWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  innWᵗˢ j sl []       = 0
  innWᵗˢ j sl (y ∷ ys) = innWᵗ j sl y ⊔ innWᵗˢ j sl ys
