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
open import Data.Fin  using (Fin)
open import Data.List using (List; []; _∷_; length; tabulate)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

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
  -- ONE PAYLOAD PER ARRIVAL.  A scripted source delivers a single data
  -- value per instant; 0 here made every clause above it — all of which
  -- are multiplicative — collapse the whole program to 0, which
  -- State-Blowup-Probe refutes as a width cap
  ... | scripted _ = 1
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
  -- a scripted payload is DATA, so it carries no inner observable — but
  -- 1 rather than 0 keeps innW usable as a multiplier and an exponent
  -- base, which is how the scanᵉ clause below consumes it
  ... | scripted _ = 1
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

-- the frame width of a runtime VALUE: an embedded observable carries its
-- expression's, a ground payload carries none.  Mirrors ofWᵛ/hopDᵛ
outWᵛ : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) (t : Ty) → Val Γ t → ℕ
outWᵛ j sl unitᵗ    _        = 0
outWᵛ j sl boolᵗ    _        = 0
outWᵛ j sl natᵗ     _        = 0
outWᵛ j sl (s ×ᵗ t) (a , b)  = outWᵛ j sl s a ⊔ outWᵛ j sl t b
outWᵛ j sl (s +ᵗ t) (inj₁ a) = outWᵛ j sl s a
outWᵛ j sl (s +ᵗ t) (inj₂ b) = outWᵛ j sl t b
outWᵛ j sl (obs t)  e        = outWᵉ j sl e

------------------------------------------------------------------
-- THE PARKED WIDTH — the supply side of the deferᵉ gap.
--
-- `outWᵉ (deferᵉ e) = 0` is correct and load-bearing: a defer delivers
-- NOTHING this instant, and every wet-side width bound depends on it.
-- But the evaluator PARKS that body — subscribeE's deferᵉ clause adds a
-- LiveSource whose pending is `(suc now , body)` at `elemTy = obs u` —
-- and the caps predicate's widLive conjunct then demands the BODY's
-- width.  Under outW alone no entry measure supplies it: the body's
-- width has vanished from the program's outWᵉ and from every value
-- measure derived from it.
--
-- dW is the missing quantity, and it is SUPPLY-SIDE ONLY: nothing wet
-- reads it.  It ⊔-collects, over every deferᵉ subterm, that body's own
-- outW together with the body's own parked widths:
--
--     dWᵉ (deferᵉ e) = outWᵉ e ⊔ dWᵉ e
--
-- It COLLECTS rather than multiplies.  A parked body is not entered at
-- park time — the *All above it sees a pending, not a payload — so a
-- `mergeAllᵉ` over a defer does not compound the parked width the way it
-- compounds a delivered one.  Every other constructor is therefore a
-- plain ⊔ over its subterms, uniformly, including the ones outW/innW
-- may drop (a prim's argument, an `ifᵗ` scrutinee): dW is an upper
-- bound with no multiplicative structure, so collecting more is free and
-- makes the descent lemmas hold clause for clause.
--
-- Same fuel discipline as outW: `j` is spent one per connect, on the
-- shared-slot descent, and is 0 elsewhere.
--
-- AND THE JOIN IS WHAT THE CAPS SIDE READS.  `pW = outW ⊔ dW` is the
-- width a value or an expression can be made to demand, delivered now or
-- parked for later; capsOK?'s widLive/widNode and valCaps?'s width half
-- are stated at pW, and capsAt's base pays for it.
------------------------------------------------------------------

mutual
  dWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  -- a share is a connect: descend into the def, on slot fuel
  dWᵉ zero    sl (input i) = 0
  dWᵉ (suc j) sl (input i) with sl i
  -- a scripted slot's payloads are DATA, so nothing is parked there
  ... | scripted _ = 0
  ... | shared d   = dWᵉ j sl d
  dWᵉ j sl (ofᵉ ts)        = dWᵗˢ j sl ts
  dWᵉ j sl emptyᵉ          = 0
  dWᵉ j sl (mapᵉ f e)      = dWᵗ j sl f ⊔ dWᵉ j sl e
  dWᵉ j sl (takeᵉ c e)     = dWᵗ j sl c ⊔ dWᵉ j sl e
  dWᵉ j sl (scanᵉ f z e)   = dWᵗ j sl f ⊔ dWᵗ j sl z ⊔ dWᵉ j sl e
  dWᵉ j sl (mergeAllᵉ e)   = dWᵉ j sl e
  dWᵉ j sl (concatAllᵉ e)  = dWᵉ j sl e
  dWᵉ j sl (switchAllᵉ e)  = dWᵉ j sl e
  dWᵉ j sl (exhaustAllᵉ e) = dWᵉ j sl e
  dWᵉ j sl (μᵉ e)          = dWᵉ j sl e
  dWᵉ j sl (varᵉ x)        = 0
  -- THE CLAUSE THE WHOLE FAMILY EXISTS FOR
  dWᵉ j sl (deferᵉ e)      = outWᵉ j sl e ⊔ dWᵉ j sl e

  dWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
  dWᵗ j sl (varᵗ x)      = 0
  dWᵗ j sl unit̂          = 0
  dWᵗ j sl (bool̂ _)      = 0
  dWᵗ j sl (nat̂ _)       = 0
  dWᵗ j sl (pairᵗ a b)   = dWᵗ j sl a ⊔ dWᵗ j sl b
  dWᵗ j sl (fstᵗ p)      = dWᵗ j sl p
  dWᵗ j sl (sndᵗ p)      = dWᵗ j sl p
  dWᵗ j sl (inlᵗ a)      = dWᵗ j sl a
  dWᵗ j sl (inrᵗ a)      = dWᵗ j sl a
  dWᵗ j sl (caseᵗ s l r) = dWᵗ j sl s ⊔ dWᵗ j sl l ⊔ dWᵗ j sl r
  dWᵗ j sl (ifᵗ c a b)   = dWᵗ j sl c ⊔ dWᵗ j sl a ⊔ dWᵗ j sl b
  dWᵗ j sl (primᵗ _ a)   = dWᵗ j sl a
  dWᵗ j sl (strmᵗ e)     = dWᵉ j sl e

  dWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  dWᵗˢ j sl []       = 0
  dWᵗˢ j sl (y ∷ ys) = dWᵗ j sl y ⊔ dWᵗˢ j sl ys

-- the parked width of a runtime VALUE, mirroring outWᵛ clause for clause
dWᵛ : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) (t : Ty) → Val Γ t → ℕ
dWᵛ j sl unitᵗ    _        = 0
dWᵛ j sl boolᵗ    _        = 0
dWᵛ j sl natᵗ     _        = 0
dWᵛ j sl (s ×ᵗ t) (a , b)  = dWᵛ j sl s a ⊔ dWᵛ j sl t b
dWᵛ j sl (s +ᵗ t) (inj₁ a) = dWᵛ j sl s a
dWᵛ j sl (s +ᵗ t) (inj₂ b) = dWᵛ j sl t b
dWᵛ j sl (obs t)  e        = dWᵉ j sl e

-- THE JOIN.  Delivered now, or parked for later — the caps side bounds
-- both with one number
pWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
pWᵉ j sl e = outWᵉ j sl e ⊔ dWᵉ j sl e

pWᵛ : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) (t : Ty) → Val Γ t → ℕ
pWᵛ j sl t v = outWᵛ j sl t v ⊔ dWᵛ j sl t v

------------------------------------------------------------------
-- AND THE SLOT TELESCOPE'S OWN PARKED WIDTH.  A shared slot's def is
-- subscribed WHOLE at a connect, so its parked bodies are entry data
-- exactly as its size is — and slotsSize's counterpart on the width axis
-- is what capsAt's base has to pay.  Scripted slots contribute nothing:
-- their element type is data, so both halves of pW are zero there.
--
-- Written as a recursive walk over the index list (as slotsGo? is, and
-- for the same reason): a non-matching definition unfolds on a NEUTRAL
-- telescope and grows every type that mentions it.
------------------------------------------------------------------

slotPW : ∀ {n} {Γ : Ctx n} {u} (j : ℕ) (sl : Slots Γ) → Slot Γ u → ℕ
slotPW j sl (scripted _) = 0
slotPW j sl (shared d)   = pWᵉ j sl d

slotsPWgo : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) → List (Fin n) → ℕ
slotsPWgo j sl []       = 0
slotsPWgo j sl (i ∷ is) = slotPW j sl (sl i) ⊔ slotsPWgo j sl is

slotsPW : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) → ℕ
slotsPW {n = n} j sl = slotsPWgo j sl (tabulate {n = n} (λ i → i))
