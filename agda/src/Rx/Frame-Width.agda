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
-- THE SLOT DESCENT DROPS VISITED SLOTS.  A share is reached by a
-- connect, not by descending into syntax, and a slot def may reference
-- other slots — so `input` is not structural.  The descent carries the
-- set `vs` of shared slots already entered on this path: entering
-- `input i` at an unvisited `shared d` descends into `d` with `i`
-- marked, and A REVISIT CONTRIBUTES ZERO.
--
-- WHY ZERO IS THE FAITHFUL NUMBER.  A share is reached by a CONNECT,
-- and share-connect-no-replay says the second arrival at slot i inside
-- one cascade gets no replay of the burst — it hands back the existing
-- subject.  What that slot emits LATER flows through registrations,
-- which the cascade side counts; the static measure must not count it
-- twice.  Scripted slots are not marked (they cannot cycle, and the `1`
-- for a data payload is load-bearing — State-Blowup-Probe refutes 0).
--
-- THE FUEL `j` STAYS, FOR TERMINATION ONLY: the visited check fires
-- first, so `j` no longer carries any semantics.  The lexicographic
-- order is still (j, the expression), and j is instantiated at the slot
-- count because the connect descent strictly drops `unconn`.
--
-- AND THE COLLECTORS STAY AT `[]`.  `capsOK?` bounds a STORED value,
-- and a stored value carries no record of which connect put it there —
-- its width is read at the ENTRY form — so `subscribeE`'s shared branch
-- needs the def at `[]`.  Reading a def unmarked lets the descent come
-- back round to that def's own slot ONCE (it marks the slot on the way
-- in), so the base height is `Σkᵢ + max kᵢ` rather than `Σkᵢ`: still
-- linear, which is what `visited-height-fits-unmarked` gates.  Against
-- the fuel form's `(Σkᵢ)·n` that is the whole point.
--
-- The exported names are the measures AT `[]`; `outWⱽ` and friends are
-- the descent itself, and only lemmas that reduce through the `input`
-- clause ever mention them.
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
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; []; _∷_; length; tabulate)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Rx.Exp
open import Rx.Evaluator using (Slots; Slot; scripted; shared)

-- membership on the visited set, decidable by the index's ℕ view
_∈ᵇ_ : ∀ {n} → Fin n → List (Fin n) → Bool
i ∈ᵇ []       = false
i ∈ᵇ (k ∷ ks) = if toℕ i ≡ᵇ toℕ k then true else i ∈ᵇ ks

mutual
  -- slope of outW in the width of the value plugged at index k
  pmOⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmOⱽ j vs sl k (input i)       = 0
  pmOⱽ j vs sl k (ofᵉ ts)        = 0          -- outW of an ofᵉ is its LENGTH
  pmOⱽ j vs sl k emptyᵉ          = 0
  pmOⱽ j vs sl k (mapᵉ f e)      = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (takeᵉ c e)     = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (scanᵉ f z e)   = pmOⱽ j vs sl k e
  -- product rule: outW (mergeAll e) = outW e * innW e
  pmOⱽ j vs sl k (mergeAllᵉ e)   = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (concatAllᵉ e)  = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (switchAllᵉ e)  = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (exhaustAllᵉ e) = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (μᵉ e)          = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (varᵉ x)        = 0
  pmOⱽ j vs sl k (deferᵉ e)      = 0

  pmOᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  pmOᵗⱽ j vs sl k (varᵗ x)      = 0
  pmOᵗⱽ j vs sl k unit̂          = 0
  pmOᵗⱽ j vs sl k (bool̂ _)      = 0
  pmOᵗⱽ j vs sl k (nat̂ _)       = 0
  pmOᵗⱽ j vs sl k (pairᵗ a b)   = pmOᵗⱽ j vs sl k a ⊔ pmOᵗⱽ j vs sl k b
  pmOᵗⱽ j vs sl k (fstᵗ p)      = pmOᵗⱽ j vs sl k p
  pmOᵗⱽ j vs sl k (sndᵗ p)      = pmOᵗⱽ j vs sl k p
  pmOᵗⱽ j vs sl k (inlᵗ a)      = pmOᵗⱽ j vs sl k a
  pmOᵗⱽ j vs sl k (inrᵗ a)      = pmOᵗⱽ j vs sl k a
  pmOᵗⱽ j vs sl k (caseᵗ s l r) = pmOᵗⱽ j vs sl (suc k) l ⊔ pmOᵗⱽ j vs sl (suc k) r
                       ⊔ (pmIᵗⱽ j vs sl 0 l ⊔ pmIᵗⱽ j vs sl 0 r ⊔ 1) * pmOᵗⱽ j vs sl k s
  pmOᵗⱽ j vs sl k (ifᵗ c a b)   = pmOᵗⱽ j vs sl k a ⊔ pmOᵗⱽ j vs sl k b
  pmOᵗⱽ j vs sl k (primᵗ _ a)   = 0
  pmOᵗⱽ j vs sl k (strmᵗ e)     = pmOⱽ j vs sl k e

  -- slope of innW in the same
  pmIⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmIⱽ j vs sl k (input i)       = 0
  pmIⱽ j vs sl k (ofᵉ ts)        = pmIᵗˢⱽ j vs sl k ts
  pmIⱽ j vs sl k emptyᵉ          = 0
  pmIⱽ j vs sl k (mapᵉ f e)      = pmIᵗⱽ j vs sl (suc k) f + (pmIᵗⱽ j vs sl 0 f ⊔ 1) * pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (takeᵉ c e)     = pmIⱽ j vs sl k e
  -- the refold: the slope compounds once per fold
  pmIⱽ j vs sl k (scanᵉ f z e)   = (pmIᵗⱽ j vs sl 0 f ⊔ 1) ^ (outWⱽ j vs sl e)
                         * (pmIᵗⱽ j vs sl (suc k) f + pmIᵗⱽ j vs sl k z + pmIⱽ j vs sl k e)
  pmIⱽ j vs sl k (mergeAllᵉ e)   = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (concatAllᵉ e)  = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (switchAllᵉ e)  = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (exhaustAllᵉ e) = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (μᵉ e)          = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (varᵉ x)        = 0
  pmIⱽ j vs sl k (deferᵉ e)      = 0

  pmIᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  pmIᵗⱽ j vs sl k (varᵗ x)      = if varIx x ≡ᵇ k then 1 else 0
  pmIᵗⱽ j vs sl k unit̂          = 0
  pmIᵗⱽ j vs sl k (bool̂ _)      = 0
  pmIᵗⱽ j vs sl k (nat̂ _)       = 0
  pmIᵗⱽ j vs sl k (pairᵗ a b)   = pmIᵗⱽ j vs sl k a ⊔ pmIᵗⱽ j vs sl k b
  pmIᵗⱽ j vs sl k (fstᵗ p)      = pmIᵗⱽ j vs sl k p
  pmIᵗⱽ j vs sl k (sndᵗ p)      = pmIᵗⱽ j vs sl k p
  pmIᵗⱽ j vs sl k (inlᵗ a)      = pmIᵗⱽ j vs sl k a
  pmIᵗⱽ j vs sl k (inrᵗ a)      = pmIᵗⱽ j vs sl k a
  pmIᵗⱽ j vs sl k (caseᵗ s l r) = (pmIᵗⱽ j vs sl (suc k) l ⊔ pmIᵗⱽ j vs sl (suc k) r)
                       + (pmIᵗⱽ j vs sl 0 l ⊔ pmIᵗⱽ j vs sl 0 r ⊔ 1) * pmIᵗⱽ j vs sl k s
  pmIᵗⱽ j vs sl k (ifᵗ c a b)   = pmIᵗⱽ j vs sl k a ⊔ pmIᵗⱽ j vs sl k b
  pmIᵗⱽ j vs sl k (primᵗ _ a)   = 0
  pmIᵗⱽ j vs sl k (strmᵗ e)     = pmOⱽ j vs sl k e

  pmIᵗˢⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) (k : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pmIᵗˢⱽ j vs sl k []       = 0
  pmIᵗˢⱽ j vs sl k (y ∷ ys) = pmIᵗⱽ j vs sl k y ⊔ pmIᵗˢⱽ j vs sl k ys

  outWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  -- a slot is reached by a CONNECT; the connect edge pays, not this
  -- A SHARE IS A CONNECT: descend into the slot's def, on slot fuel.
  -- Slot defs may reference slots, so this is not structural — j is the
  -- lexicographic outer measure and every connect spends one
  outWⱽ zero    vs sl (input i) = 0
  outWⱽ (suc j) vs sl (input i) with i ∈ᵇ vs
  -- A REVISIT DELIVERS NOTHING: the connect hands back the existing
  -- subject, and what the slot emits later the cascade side counts
  ... | true  = 0
  ... | false with sl i
  -- ONE PAYLOAD PER ARRIVAL.  A scripted source delivers a single data
  -- value per instant; 0 here made every clause above it — all of which
  -- are multiplicative — collapse the whole program to 0, which
  -- State-Blowup-Probe refutes as a width cap
  ...   | scripted _ = 1
  ...   | shared d   = outWⱽ j (i ∷ vs) sl d
  outWⱽ j vs sl (ofᵉ ts)        = length ts
  outWⱽ j vs sl emptyᵉ          = 0
  outWⱽ j vs sl (mapᵉ f e)      = outWⱽ j vs sl e
  outWⱽ j vs sl (takeᵉ c e)     = outWⱽ j vs sl e
  outWⱽ j vs sl (scanᵉ f z e)   = outWⱽ j vs sl e
  -- THE *All EDGE: every payload's inner is entered
  outWⱽ j vs sl (mergeAllᵉ e)   = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (concatAllᵉ e)  = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (switchAllᵉ e)  = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (exhaustAllᵉ e) = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (μᵉ e)          = outWⱽ j vs sl e
  outWⱽ j vs sl (varᵉ x)        = 0
  outWⱽ j vs sl (deferᵉ e)      = 0          -- crosses a tick

  innWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  innWⱽ zero    vs sl (input i) = 0
  innWⱽ (suc j) vs sl (input i) with i ∈ᵇ vs
  ... | true  = 0                       -- likewise: no inner is entered
  ... | false with sl i
  -- a scripted payload is DATA, so it carries no inner observable — but
  -- 1 rather than 0 keeps innW usable as a multiplier and an exponent
  -- base, which is how the scanᵉ clause below consumes it
  ...   | scripted _ = 1
  ...   | shared d   = innWⱽ j (i ∷ vs) sl d
  innWⱽ j vs sl (ofᵉ ts)        = innWᵗˢⱽ j vs sl ts
  innWⱽ j vs sl emptyᵉ          = 0
  innWⱽ j vs sl (mapᵉ f e)      = innWᵗⱽ j vs sl f + (pmIᵗⱽ j vs sl 0 f ⊔ 1) * innWⱽ j vs sl e
  innWⱽ j vs sl (takeᵉ c e)     = innWⱽ j vs sl e
  -- THE REFOLD, and the tower: the accumulator's width compounds once
  -- per fold, and the fold count is the SOURCE's payload count
  innWⱽ j vs sl (scanᵉ f z e)   = (pmIᵗⱽ j vs sl 0 f ⊔ 1) ^ (outWⱽ j vs sl e)
                        * (innWᵗⱽ j vs sl f + innWᵗⱽ j vs sl z + innWⱽ j vs sl e + 1)
  innWⱽ j vs sl (mergeAllᵉ e)   = innWⱽ j vs sl e
  innWⱽ j vs sl (concatAllᵉ e)  = innWⱽ j vs sl e
  innWⱽ j vs sl (switchAllᵉ e)  = innWⱽ j vs sl e
  innWⱽ j vs sl (exhaustAllᵉ e) = innWⱽ j vs sl e
  innWⱽ j vs sl (μᵉ e)          = innWⱽ j vs sl e
  innWⱽ j vs sl (varᵉ x)        = 0
  innWⱽ j vs sl (deferᵉ e)      = 0

  innWᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
  innWᵗⱽ j vs sl (varᵗ x)      = 0
  innWᵗⱽ j vs sl unit̂          = 0
  innWᵗⱽ j vs sl (bool̂ _)      = 0
  innWᵗⱽ j vs sl (nat̂ _)       = 0
  innWᵗⱽ j vs sl (pairᵗ a b)   = innWᵗⱽ j vs sl a ⊔ innWᵗⱽ j vs sl b
  innWᵗⱽ j vs sl (fstᵗ p)      = innWᵗⱽ j vs sl p
  innWᵗⱽ j vs sl (sndᵗ p)      = innWᵗⱽ j vs sl p
  innWᵗⱽ j vs sl (inlᵗ a)      = innWᵗⱽ j vs sl a
  innWᵗⱽ j vs sl (inrᵗ a)      = innWᵗⱽ j vs sl a
  innWᵗⱽ j vs sl (caseᵗ s l r) = (innWᵗⱽ j vs sl l ⊔ innWᵗⱽ j vs sl r) + (pmIᵗⱽ j vs sl 0 l ⊔ pmIᵗⱽ j vs sl 0 r ⊔ 1) * innWᵗⱽ j vs sl s
  innWᵗⱽ j vs sl (ifᵗ c a b)   = innWᵗⱽ j vs sl a ⊔ innWᵗⱽ j vs sl b
  innWᵗⱽ j vs sl (primᵗ _ a)   = 0
  -- an obs-typed term denotes an observable; its width is that
  -- observable's frame width
  innWᵗⱽ j vs sl (strmᵗ e)     = outWⱽ j vs sl e

  innWᵗˢⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  innWᵗˢⱽ j vs sl []       = 0
  innWᵗˢⱽ j vs sl (y ∷ ys) = innWᵗⱽ j vs sl y ⊔ innWᵗˢⱽ j vs sl ys

------------------------------------------------------------------
-- THE EXPORTED MEASURES: the descent AT THE ENTRY FORM, `vs = []`.
--
-- Every reading site outside this module is a wrapper application and
-- unfolds definitionally, so only lemmas that reduce THROUGH the
-- `input` clause ever see the visited set — and those are the ones the
-- collectors' `[]` costs one turn.
------------------------------------------------------------------

pmOᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
pmOᵉ j sl k e = pmOⱽ j [] sl k e

pmOᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
pmOᵗ j sl k tm = pmOᵗⱽ j [] sl k tm

pmIᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
pmIᵉ j sl k e = pmIⱽ j [] sl k e

pmIᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
pmIᵗ j sl k tm = pmIᵗⱽ j [] sl k tm

pmIᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
pmIᵗˢ j sl k ts = pmIᵗˢⱽ j [] sl k ts

outWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
outWᵉ j sl e = outWⱽ j [] sl e

innWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
innWᵉ j sl e = innWⱽ j [] sl e

innWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
innWᵗ j sl tm = innWᵗⱽ j [] sl tm

innWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
innWᵗˢ j sl ts = innWᵗˢⱽ j [] sl ts


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
  -- CLAUSE ORDER IS LOAD-BEARING: the `input` pair splits on the FUEL,
  -- and if it came first Agda would build a case tree that splits on
  -- `j` at the root — leaving `dWⱽ j vs sl (ofᵉ ts)` STUCK for a variable
  -- j, which is exactly the shape every caller has (the fuel is the
  -- slot count `n`, never a literal).  With `input` last, the tree
  -- splits on the expression first and every other clause reduces
  dWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  dWⱽ j vs sl (ofᵉ ts)        = dWᵗˢⱽ j vs sl ts
  dWⱽ j vs sl emptyᵉ          = 0
  dWⱽ j vs sl (mapᵉ f e)      = dWᵗⱽ j vs sl f ⊔ dWⱽ j vs sl e
  dWⱽ j vs sl (takeᵉ c e)     = dWᵗⱽ j vs sl c ⊔ dWⱽ j vs sl e
  dWⱽ j vs sl (scanᵉ f z e)   = dWᵗⱽ j vs sl f ⊔ dWᵗⱽ j vs sl z ⊔ dWⱽ j vs sl e
  dWⱽ j vs sl (mergeAllᵉ e)   = dWⱽ j vs sl e
  dWⱽ j vs sl (concatAllᵉ e)  = dWⱽ j vs sl e
  dWⱽ j vs sl (switchAllᵉ e)  = dWⱽ j vs sl e
  dWⱽ j vs sl (exhaustAllᵉ e) = dWⱽ j vs sl e
  dWⱽ j vs sl (μᵉ e)          = dWⱽ j vs sl e
  dWⱽ j vs sl (varᵉ x)        = 0
  -- THE CLAUSE THE WHOLE FAMILY EXISTS FOR
  dWⱽ j vs sl (deferᵉ e)      = outWⱽ j vs sl e ⊔ dWⱽ j vs sl e
  -- a share is a connect: descend into the def, on slot fuel
  dWⱽ zero    vs sl (input i) = 0
  dWⱽ (suc j) vs sl (input i) with i ∈ᵇ vs
  ... | true  = 0
  ... | false with sl i
  -- a scripted slot's payloads are DATA, so nothing is parked there
  ...   | scripted _ = 0
  ...   | shared d   = dWⱽ j (i ∷ vs) sl d

  dWᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
  dWᵗⱽ j vs sl (varᵗ x)      = 0
  dWᵗⱽ j vs sl unit̂          = 0
  dWᵗⱽ j vs sl (bool̂ _)      = 0
  dWᵗⱽ j vs sl (nat̂ _)       = 0
  dWᵗⱽ j vs sl (pairᵗ a b)   = dWᵗⱽ j vs sl a ⊔ dWᵗⱽ j vs sl b
  dWᵗⱽ j vs sl (fstᵗ p)      = dWᵗⱽ j vs sl p
  dWᵗⱽ j vs sl (sndᵗ p)      = dWᵗⱽ j vs sl p
  dWᵗⱽ j vs sl (inlᵗ a)      = dWᵗⱽ j vs sl a
  dWᵗⱽ j vs sl (inrᵗ a)      = dWᵗⱽ j vs sl a
  dWᵗⱽ j vs sl (caseᵗ s l r) = dWᵗⱽ j vs sl s ⊔ dWᵗⱽ j vs sl l ⊔ dWᵗⱽ j vs sl r
  dWᵗⱽ j vs sl (ifᵗ c a b)   = dWᵗⱽ j vs sl c ⊔ dWᵗⱽ j vs sl a ⊔ dWᵗⱽ j vs sl b
  dWᵗⱽ j vs sl (primᵗ _ a)   = dWᵗⱽ j vs sl a
  dWᵗⱽ j vs sl (strmᵗ e)     = dWⱽ j vs sl e

  dWᵗˢⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n)) (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  dWᵗˢⱽ j vs sl []       = 0
  dWᵗˢⱽ j vs sl (y ∷ ys) = dWᵗⱽ j vs sl y ⊔ dWᵗˢⱽ j vs sl ys


-- the parked half's exported names, likewise at the entry form
dWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
dWᵉ j sl e = dWⱽ j [] sl e

dWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
dWᵗ j sl tm = dWᵗⱽ j [] sl tm

dWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
dWᵗˢ j sl ts = dWᵗˢⱽ j [] sl ts

-- and the join, on the descent itself: the caps side reads it at `[]`
pWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
pWⱽ j vs sl e = outWⱽ j vs sl e ⊔ dWⱽ j vs sl e

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

------------------------------------------------------------------
-- AND THE TELESCOPE'S INNER WIDTH, which pW does NOT see.
--
-- pW is `outW ⊔ dW`: what a def DELIVERS now and what it PARKS.  A
-- width induction that meets `input i` reads a third quantity off the
-- same def — `innWᵉ`, the widest observable that frame can EMIT — and
-- the two are independent, because innW reads the STEP FUNCTION's
-- embedded observables while outW/dW read the source's.
-- Eval-Growth-Probe's §8 `iwDef` separates them: pW 0 against innW 3.
--
-- Scripted slots contribute nothing here for the same reason they
-- contribute nothing to slotsPW — the side condition that consumes
-- this collector (slotCaps?) is size-only on its scripted clauses —
-- and the `innWᵉ (input i) = 1` a scripted slot presents to the
-- induction is paid for by the `suc` on capsAt's base instead
slotIW : ∀ {n} {Γ : Ctx n} {u} (j : ℕ) (sl : Slots Γ) → Slot Γ u → ℕ
slotIW j sl (scripted _) = 0
slotIW j sl (shared d)   = innWᵉ j sl d

slotsIWgo : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) → List (Fin n) → ℕ
slotsIWgo j sl []       = 0
slotsIWgo j sl (i ∷ is) = slotIW j sl (sl i) ⊔ slotsIWgo j sl is

slotsIW : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) → ℕ
slotsIW {n = n} j sl = slotsIWgo j sl (tabulate {n = n} (λ i → i))
