------------------------------------------------------------------
-- THE VISITED-SET SLOT DESCENT: the entry width ceiling IS linear in
-- the program, once the width measures stop re-entering a shared slot.
--
-- WHAT THIS IS AGAINST.  Slot-Fuel-Probe prices the fuel descent and
-- refutes the `3 + 2 * sz` base height: `outWᵉ (suc j) sl (input i) |
-- shared d = outWᵉ j sl d` spends GENERIC fuel, every consumer
-- instantiates that fuel at `n` (the slot count), so a def in a slot
-- CYCLE is re-entered once per level and exponentiates again each time.
-- A def of k wraps in a 2-cycle padded with n−2 one-node dummy slots
-- demands k·(n−1) stories off sz = 19 + 28k + n — a PRODUCT, and the
-- slope in sz is k, unbounded.  At k = 8, n = 100: 792 demanded against
-- the 689 that 3 + 2·sz allows.
--
-- THE RULING it prices out is the second of its own two exits: the slot
-- descent stops spending fuel and starts DROPPING VISITED SLOTS, the
-- way the evaluator's own connect does.  Entering `input i` with
-- `sl i = shared d` and `i` unvisited descends into `d` with `i`
-- marked; A REVISIT CONTRIBUTES ZERO.
--
-- WHY ZERO IS THE FAITHFUL NUMBER, and not a convenient one.  A share
-- is reached by a CONNECT, and the README's share-connect-no-replay
-- theorem says a late join gets no replay of the connect burst.  So the
-- second arrival at slot i inside one connect cascade delivers NOTHING
-- in that frame: it hands back the existing subject.  What the slot
-- does emit LATER flows through registrations, and the cascade side —
-- cReg, the delivery bound — is what counts those.  The static measure
-- must not count them twice.
--
-- WHAT IS MEASURED HERE, all refl or structural:
--
--   §1  the measures, visited-set form (the nine-function mutual block
--       of Rx.Frame-Width with the descent changed, and dW beside it)
--
--   §2  THE COLLAPSE.  Slot-Fuel-Probe's own 4-slot cycle `insC`, whose
--       fuel measure is above 2 ^ (2 ^ (2 ^ (2 ^ 256))) at fuel 4, sits
--       at a FIXED POINT of 258 · 2 ^ 521 from fuel 2 up — two stories,
--       one per shared slot, and more fuel buys nothing.  The fuel axis
--       is gone as a source of growth.
--
--       AND WHAT THE COLLECTORS COST.  A def read with an EMPTY visited
--       set goes round the cycle ONE MORE TIME than any connect does,
--       because its own slot is not yet marked.  Marking removes the
--       turn — but `capsOK?` reads a STORED value at the entry form and
--       cannot supply a marked one, so the collectors STAY at `[]` and
--       the base pays that one turn.  One, not `n`: still linear.
--
--   §3  AGREEMENT OFF THE CYCLE.  On an ACYCLIC telescope the two
--       descents are equal, refl, at every fuel level from n up: the
--       visited set only ever fires on a repeated slot, and a repeat on
--       a descent path IS a cycle in the slot graph.  So nothing that
--       does not cycle re-pins, which is why the soundness gate is
--       confined to cyclic telescopes.
--
--   §4  THE BASE HEIGHT, gated.  The (k, n) row that refuted the linear
--       price is re-run: the demand is now 2k (one entry per SHARED
--       slot on a path, and a 2-cycle has two), not k·(n−1), and 2k
--       sits under 3 + 2·sz with the whole telescope to spare.  Stated
--       generally as `visited-height-fits`: a descent path of shared
--       defs of k₁ … k_m wraps demands Σkᵢ stories and costs
--       Σ(10 + 14kᵢ) nodes, so the demand is under 2·sz for every
--       shape — the inequality Leg A exists to make real.
--
--   §5  THE SOUNDNESS DIRECTION: the visited-set measure is BELOW the
--       fuel measure everywhere (dropping a subtree of the descent can
--       only shrink a measure built from ⊔, +, * and ^), so every cap
--       computed from it is tighter — which is why §3's agreement is
--       the whole soundness story off the cycle, and why only cyclic
--       telescopes could make the State-Blowup wall move.  No row of
--       that wall has one.
--
-- A NOTE ON WHAT IS NOT WRITTEN HERE, paid for twice by an OOM: `_≤ᵇ_`
-- and `_≤_` on ℕ recurse UNARILY, so neither a `≤ᵇ` bracket nor a
-- `≤-refl` may be pointed at these numbers — 258 · 2 ^ 521 is 10 ^ 159
-- constructors.  Magnitudes are pinned as CLOSED-FORM EQUALITIES, which
-- the builtin nat compares in binary, and the two-sided facts are `≡`
-- rather than `≤`.
--
-- Standalone, so src/Main.agda never reaches it.  Fast.
------------------------------------------------------------------
module Visited-Width-Probe where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_;
                             z≤n; s≤s)
open import Data.Nat.Properties
  using (≤ᵇ⇒≤; ≤-trans; ≤-refl; ≤-reflexive; *-identityˡ; *-identityʳ;
         *-monoˡ-≤; *-monoʳ-≤; *-mono-≤; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤;
         ^-monoʳ-≤; m≤m⊔n; m≤n⊔m; m≤m*n; m≤n+m; m≤m+n; ⊔-lub)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin; toℕ) renaming (zero to fz; suc to fs)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim using (hot)
open import Rx.Exp
open import Rx.Evaluator using (Slots; Slot; scripted; shared; slotsSize)
open import Rx.Frame-Width using (outWᵉ)

------------------------------------------------------------------
-- §1  THE MEASURES, VISITED-SET FORM.
--
-- The nine-function mutual block of Rx.Frame-Width, verbatim except in
-- the two `input` clauses, plus dW's three beside it.  `vs` is the set
-- of shared slots already entered on this descent path; the fuel `j`
-- stays for TERMINATION ONLY (each descent still spends one, and the
-- consumer still instantiates it at the slot count) — it no longer
-- carries any semantics, because the visited check fires first.
--
-- Scripted slots are NOT marked: they do not recurse, so they cannot
-- cycle, and `outWᵉ … (input i) = 1` for a data payload is load-bearing
-- (zero there collapses every multiplicative clause above it, which
-- State-Blowup-Probe refutes as a width cap).
------------------------------------------------------------------

_∈ᵇ_ : ∀ {n} → Fin n → List (Fin n) → Bool
i ∈ᵇ []       = false
i ∈ᵇ (k ∷ ks) = if toℕ i ≡ᵇ toℕ k then true else i ∈ᵇ ks

mutual
  pmOⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
       (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmOⱽ j vs sl k (input i)       = 0
  pmOⱽ j vs sl k (ofᵉ ts)        = 0
  pmOⱽ j vs sl k emptyᵉ          = 0
  pmOⱽ j vs sl k (mapᵉ f e)      = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (takeᵉ c e)     = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (scanᵉ f z e)   = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (mergeAllᵉ e)   = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (concatAllᵉ e)  = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (switchAllᵉ e)  = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (exhaustAllᵉ e) = outWⱽ j vs sl e * pmIⱽ j vs sl k e + pmOⱽ j vs sl k e * innWⱽ j vs sl e
  pmOⱽ j vs sl k (μᵉ e)          = pmOⱽ j vs sl k e
  pmOⱽ j vs sl k (varᵉ x)        = 0
  pmOⱽ j vs sl k (deferᵉ e)      = 0

  pmOᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
        (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
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

  pmIⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
       (sl : Slots Γ) (k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmIⱽ j vs sl k (input i)       = 0
  pmIⱽ j vs sl k (ofᵉ ts)        = pmIᵗˢⱽ j vs sl k ts
  pmIⱽ j vs sl k emptyᵉ          = 0
  pmIⱽ j vs sl k (mapᵉ f e)      = pmIᵗⱽ j vs sl (suc k) f + (pmIᵗⱽ j vs sl 0 f ⊔ 1) * pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (takeᵉ c e)     = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (scanᵉ f z e)   = (pmIᵗⱽ j vs sl 0 f ⊔ 1) ^ (outWⱽ j vs sl e)
                         * (pmIᵗⱽ j vs sl (suc k) f + pmIᵗⱽ j vs sl k z + pmIⱽ j vs sl k e)
  pmIⱽ j vs sl k (mergeAllᵉ e)   = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (concatAllᵉ e)  = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (switchAllᵉ e)  = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (exhaustAllᵉ e) = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (μᵉ e)          = pmIⱽ j vs sl k e
  pmIⱽ j vs sl k (varᵉ x)        = 0
  pmIⱽ j vs sl k (deferᵉ e)      = 0

  pmIᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
        (sl : Slots Γ) (k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
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

  pmIᵗˢⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
         (sl : Slots Γ) (k : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pmIᵗˢⱽ j vs sl k []       = 0
  pmIᵗˢⱽ j vs sl k (y ∷ ys) = pmIᵗⱽ j vs sl k y ⊔ pmIᵗˢⱽ j vs sl k ys

  -- THE CLAUSE THE WHOLE PROBE IS ABOUT
  outWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
        (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  outWⱽ zero    vs sl (input i) = 0
  outWⱽ (suc j) vs sl (input i) with i ∈ᵇ vs
  ... | true  = 0                       -- A REVISIT DELIVERS NOTHING
  ... | false with sl i
  ...   | scripted _ = 1
  ...   | shared d   = outWⱽ j (i ∷ vs) sl d
  outWⱽ j vs sl (ofᵉ ts)        = length ts
  outWⱽ j vs sl emptyᵉ          = 0
  outWⱽ j vs sl (mapᵉ f e)      = outWⱽ j vs sl e
  outWⱽ j vs sl (takeᵉ c e)     = outWⱽ j vs sl e
  outWⱽ j vs sl (scanᵉ f z e)   = outWⱽ j vs sl e
  outWⱽ j vs sl (mergeAllᵉ e)   = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (concatAllᵉ e)  = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (switchAllᵉ e)  = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (exhaustAllᵉ e) = outWⱽ j vs sl e * innWⱽ j vs sl e
  outWⱽ j vs sl (μᵉ e)          = outWⱽ j vs sl e
  outWⱽ j vs sl (varᵉ x)        = 0
  outWⱽ j vs sl (deferᵉ e)      = 0

  innWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
        (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
  innWⱽ zero    vs sl (input i) = 0
  innWⱽ (suc j) vs sl (input i) with i ∈ᵇ vs
  ... | true  = 0                       -- likewise: no inner is entered
  ... | false with sl i
  ...   | scripted _ = 1
  ...   | shared d   = innWⱽ j (i ∷ vs) sl d
  innWⱽ j vs sl (ofᵉ ts)        = innWᵗˢⱽ j vs sl ts
  innWⱽ j vs sl emptyᵉ          = 0
  innWⱽ j vs sl (mapᵉ f e)      = innWᵗⱽ j vs sl f + (pmIᵗⱽ j vs sl 0 f ⊔ 1) * innWⱽ j vs sl e
  innWⱽ j vs sl (takeᵉ c e)     = innWⱽ j vs sl e
  innWⱽ j vs sl (scanᵉ f z e)   = (pmIᵗⱽ j vs sl 0 f ⊔ 1) ^ (outWⱽ j vs sl e)
                        * (innWᵗⱽ j vs sl f + innWᵗⱽ j vs sl z + innWⱽ j vs sl e + 1)
  innWⱽ j vs sl (mergeAllᵉ e)   = innWⱽ j vs sl e
  innWⱽ j vs sl (concatAllᵉ e)  = innWⱽ j vs sl e
  innWⱽ j vs sl (switchAllᵉ e)  = innWⱽ j vs sl e
  innWⱽ j vs sl (exhaustAllᵉ e) = innWⱽ j vs sl e
  innWⱽ j vs sl (μᵉ e)          = innWⱽ j vs sl e
  innWⱽ j vs sl (varᵉ x)        = 0
  innWⱽ j vs sl (deferᵉ e)      = 0

  innWᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
         (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
  innWᵗⱽ j vs sl (varᵗ x)      = 0
  innWᵗⱽ j vs sl unit̂          = 0
  innWᵗⱽ j vs sl (bool̂ _)      = 0
  innWᵗⱽ j vs sl (nat̂ _)       = 0
  innWᵗⱽ j vs sl (pairᵗ a b)   = innWᵗⱽ j vs sl a ⊔ innWᵗⱽ j vs sl b
  innWᵗⱽ j vs sl (fstᵗ p)      = innWᵗⱽ j vs sl p
  innWᵗⱽ j vs sl (sndᵗ p)      = innWᵗⱽ j vs sl p
  innWᵗⱽ j vs sl (inlᵗ a)      = innWᵗⱽ j vs sl a
  innWᵗⱽ j vs sl (inrᵗ a)      = innWᵗⱽ j vs sl a
  innWᵗⱽ j vs sl (caseᵗ s l r) = (innWᵗⱽ j vs sl l ⊔ innWᵗⱽ j vs sl r)
                       + (pmIᵗⱽ j vs sl 0 l ⊔ pmIᵗⱽ j vs sl 0 r ⊔ 1) * innWᵗⱽ j vs sl s
  innWᵗⱽ j vs sl (ifᵗ c a b)   = innWᵗⱽ j vs sl a ⊔ innWᵗⱽ j vs sl b
  innWᵗⱽ j vs sl (primᵗ _ a)   = 0
  innWᵗⱽ j vs sl (strmᵗ e)     = outWⱽ j vs sl e

  innWᵗˢⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
          (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  innWᵗˢⱽ j vs sl []       = 0
  innWᵗˢⱽ j vs sl (y ∷ ys) = innWᵗⱽ j vs sl y ⊔ innWᵗˢⱽ j vs sl ys

-- and the parked half, same descent
mutual
  dWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
      (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
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
  dWⱽ j vs sl (deferᵉ e)      = outWⱽ j vs sl e ⊔ dWⱽ j vs sl e
  dWⱽ zero    vs sl (input i) = 0
  dWⱽ (suc j) vs sl (input i) with i ∈ᵇ vs
  ... | true  = 0
  ... | false with sl i
  ...   | scripted _ = 0
  ...   | shared d   = dWⱽ j (i ∷ vs) sl d

  dWᵗⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
       (sl : Slots Γ) → Tm Γ Δᵍ Δ Θ t → ℕ
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

  dWᵗˢⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
        (sl : Slots Γ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  dWᵗˢⱽ j vs sl []       = 0
  dWᵗˢⱽ j vs sl (y ∷ ys) = dWᵗⱽ j vs sl y ⊔ dWᵗˢⱽ j vs sl ys

pWⱽ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) → Exp Γ Δᵍ Δ Θ t → ℕ
pWⱽ j vs sl e = outWⱽ j vs sl e ⊔ dWⱽ j vs sl e

------------------------------------------------------------------
-- §2  THE COLLAPSE, on Slot-Fuel-Probe's own cycle.
--
-- `insC` is the 4-slot telescope of that probe: two SHARED slots whose
-- defs reference each other, plus two one-node scripted dummies whose
-- only job is to raise the slot count (and hence the fuel).  Under the
-- fuel descent its outW at fuel 4 is above 2 ^ (2 ^ (2 ^ (2 ^ 256))).
------------------------------------------------------------------

Γ₄ : Ctx 4
Γ₄ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

accV : ∀ {Θ} → Tm Γ₄ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seedO : ∀ {Θ} → Tm Γ₄ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

W2 : Fn Γ₄ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
W2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

base0 : Closed Γ₄ natᵗ
base0 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

mix : Closed Γ₄ natᵗ → Closed Γ₄ natᵗ
mix e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ strmᵗ base0 ∷ []))

wrap : Closed Γ₄ natᵗ → Closed Γ₄ natᵗ
wrap e = mergeAllᵉ (scanᵉ W2 seedO e)

d0 d1 : Closed Γ₄ natᵗ
d0 = wrap (mix (input (fs fz)))
d1 = wrap (mix (input fz))

insC : Slots Γ₄
insC fz                = shared d0
insC (fs fz)           = shared d1
insC (fs (fs fz))      = scripted (hot [])
insC (fs (fs (fs fz))) = scripted (hot [])

in0 in1 : Closed Γ₄ natᵗ
in0 = input fz
in1 = input (fs fz)

_ : slotsSize insC ≡ 50
_ = refl

-- THE FUEL DESCENT, one level, for the comparison (this is the number
-- Slot-Fuel-Probe pins, and the one the tower is built on)
_ : outWᵉ 1 insC in0 ≡ 256
_ = refl

-- THE VISITED DESCENT.  Entering slot 0 marks it; its def reaches slot
-- 1, which marks slot 1; slot 1's def reaches slot 0 again — VISITED,
-- hence 0 — so the descent stops after TWO shared entries instead of
-- continuing for `n` levels.  At fuel 1 nothing has cycled yet and the
-- two descents agree exactly
_ : outWⱽ 1 [] insC in0 ≡ 256
_ = refl

-- THE FIXED POINT, refl and with no numeral spelled: more fuel buys
-- NOTHING once the cycle closes.  Under the fuel descent each of these
-- steps was one more tower story (Slot-Fuel-Probe's t3 / t4 / t5)
_ : outWⱽ 3 [] insC in0 ≡ outWⱽ 2 [] insC in0
_ = refl

_ : outWⱽ 4 [] insC in0 ≡ outWⱽ 2 [] insC in0
_ = refl

_ : outWⱽ 20 [] insC in0 ≡ outWⱽ 2 [] insC in0
_ = refl

_ : outWⱽ 20 [] insC in1 ≡ outWⱽ 2 [] insC in1
_ = refl

-- AND WHAT `slotPW` / `slotIW` COST — measured, because it decides the
-- collectors' form and the port turns on it.  Those collectors read the
-- DEF: `slotPW j sl (shared d) = pWᵉ j sl d`, i.e. at an EMPTY visited
-- set.  The def's own slot is then not yet marked, so the descent comes
-- back round to it ONE MORE TIME than a connect does — on `insC` a third
-- `wrap` layer, i.e. a THIRD tower story, `2 ^ (258 · 2 ^ 521)`, which
-- is why it is not computed here.
--
-- MARKING FIRST REMOVES THAT TURN, and the def then agrees with the
-- reference on the nose:
_ : outWⱽ 3 (fz ∷ []) insC d0 ≡ outWⱽ 20 (fz ∷ []) insC d0
_ = refl

_ : outWⱽ 20 (fz ∷ []) insC d0 ≡ outWⱽ 4 [] insC in0
_ = refl

-- BUT THE COLLECTORS MUST STAY UNMARKED ANYWAY, and this is the ruling
-- the port ran into rather than a preference.  `capsOK?` bounds a STORED
-- value, and a stored value carries no record of which connect put it
-- there — its width is read at the ENTRY form.  So `subscribeE`'s shared
-- branch needs the def at `[]`, and a slot side condition stated at
-- `i ∷ []` cannot supply it: the two differ by exactly the turn above,
-- and no monotonicity closes a gap in that direction.
--
-- The cost of staying at `[]` is ONE turn, not `n`: the descent marks
-- slot i on the way back in, so a path meets at most one shared def
-- twice and none three times.  The base height is therefore
-- `Σkᵢ + max kᵢ` rather than `Σkᵢ` — still LINEAR, which is all Leg A
-- needs (§4's `visited-height-fits-unmarked`).
--
-- WHAT THE PORT OWES, then, is visited-set ANTITONICITY beside the fuel
-- monotonicity Caps-Face already has: `[] ⊆ i ∷ []`, so the measure at
-- the bigger set is smaller, and the leaf lemma closes.  That is a
-- second `monoᵉ`-shaped mutual block, and it is the one piece of Leg A
-- that is not mechanical.

-- THE MAGNITUDE, in CLOSED FORM rather than as a wall of digits — and
-- as an EQUALITY rather than a `≤ᵇ` bracket, because `_≤ᵇ_` and `_≤_`
-- on ℕ recurse unarily and a 159-digit numeral is not something to
-- count down from (the container dies; measured).  Two shared slots of
-- one wrap apiece buy TWO stories and stop:
--
--     outW(mix (input 1)) = 512    innW(scanᵉ …) = 2 ^ 512 * 258
--
-- so the whole static width is 258 · 2 ^ 521, which sits under
-- towerℕ 4 = 2 ^ 65536 — against a fuel measure that was above
-- 2 ^ (2 ^ (2 ^ (2 ^ 256))) at the same fuel
_ : outWⱽ 4 [] insC in0 ≡ 258 * 2 ^ 521
_ = refl

_ : outWⱽ 4 [] insC in1 ≡ 258 * 2 ^ 521
_ = refl

-- THE REVISIT CLAUSE ITSELF, isolated: slot 0 met with slot 0 already
-- on the path contributes nothing, at any fuel
_ : outWⱽ 9 (fz ∷ []) insC in0 ≡ 0
_ = refl

_ : innWⱽ 9 (fz ∷ []) insC in0 ≡ 0
_ = refl

_ : dWⱽ 9 (fz ∷ []) insC in0 ≡ 0
_ = refl

------------------------------------------------------------------
-- §3  AGREEMENT OFF THE CYCLE.
--
-- The visited set can only fire on a slot that appears TWICE on one
-- descent path, and two occurrences of a slot on a path is exactly a
-- cycle in the slot graph.  So on an acyclic telescope the two
-- descents compute the same number, at every fuel from the slot count
-- up — which is why nothing acyclic re-pins, and why the State-Blowup
-- wall's rows (all acyclic) are the ones that carry over unchanged.
--
-- Gated on an acyclic 4-slot telescope of the same shape and size as
-- the cycle: slot 0's def reaches slot 1, slot 1's def reaches a
-- SCRIPTED slot instead of reaching back.
------------------------------------------------------------------

a0 a1 : Closed Γ₄ natᵗ
a0 = wrap (mix (input (fs fz)))
a1 = wrap (mix (input (fs (fs fz))))

insA : Slots Γ₄
insA fz                = shared a0
insA (fs fz)           = shared a1
insA (fs (fs fz))      = scripted (hot [])
insA (fs (fs (fs fz))) = scripted (hot [])

_ : slotsSize insA ≡ 50
_ = refl

-- the two descents agree, refl, at the fuel every consumer uses (n = 4)
-- and above
_ : outWⱽ 4 [] insA in0 ≡ outWᵉ 4 insA in0
_ = refl

_ : outWⱽ 4 [] insA in1 ≡ outWᵉ 4 insA in1
_ = refl

_ : outWⱽ 4 [] insA a0 ≡ outWᵉ 4 insA a0
_ = refl

_ : dWⱽ 4 [] insA a0 ≡ 0
_ = refl

-- and on a telescope with NO shared slots at all they agree trivially,
-- which is the State-Blowup / Frame-Work case
insS : Slots Γ₄
insS fz                = scripted (hot [])
insS (fs fz)           = scripted (hot [])
insS (fs (fs fz))      = scripted (hot [])
insS (fs (fs (fs fz))) = scripted (hot [])

_ : outWⱽ 4 [] insS (mix (input fz)) ≡ outWᵉ 4 insS (mix (input fz))
_ = refl

------------------------------------------------------------------
-- §4  THE BASE HEIGHT, AND THE INEQUALITY LEG A EXISTS TO MAKE REAL.
--
-- Slot-Fuel-Probe's refuting row is a def of k wraps in a 2-cycle
-- padded with n − 2 one-node dummy slots:
--
--     sz      = 19 + 28k + n          stories ≥ k * (n − 1)     (fuel)
--
-- and at k = 8, n = 100 that is 792 against the 689 that 3 + 2·sz
-- allows.  Under the visited descent the SAME program demands 2k: a
-- descent path enters each SHARED slot at most once, there are two of
-- them, and each contributes its own k wraps.  The dummies contribute
-- nothing at all — they are scripted, and they were only ever raising
-- the FUEL.
------------------------------------------------------------------

-- the row that refuted the linear price, re-run: 16 against 689
_ : 2 * 8 ≡ 16
_ = refl

_ : (2 * 8 ≤ᵇ 3 + 2 * (19 + 28 * 8 + 100)) ≡ true
_ = refl

-- and the fuel form's own demand, for the comparison
_ : (8 * 99 ≤ᵇ 3 + 2 * (19 + 28 * 8 + 100)) ≡ false
_ = refl

-- THE GENERAL SHAPE, and it is not the 2-cycle that matters — it is
-- that a shared slot pays for its own stories in its own syntax.  A
-- descent path visits distinct shared slots d₁ … d_m; slot i of kᵢ
-- wraps demands kᵢ stories (Slot-Fuel-Probe's `wrapStep`, one story per
-- wrap) and costs 10 + 14·kᵢ nodes of `slotsSize`.  So the demand along
-- the whole path is Σkᵢ against a size of Σ(10 + 14kᵢ), and
--
--     Σkᵢ ≤ 2 * Σ(10 + 14kᵢ)
--
-- with a factor of 28 to spare.  Under the FUEL descent the same path
-- was re-entered once per fuel level and the demand was (Σkᵢ)·n, with
-- n bought at ONE node apiece — which is the product the ruling is
-- retiring.  Stated per slot and summed by monotonicity:
visited-slot-fits : ∀ (k : ℕ) → k ≤ 2 * (10 + 14 * k)
visited-slot-fits k =
  ≤-trans (≤-trans (m≤n+m k 20) (+-monoʳ-≤ 20 (m≤m+n k (27 * k))))
          (≤-reflexive (shape k))
  where
  shape : ∀ (x : ℕ) → 20 + (x + 27 * x) ≡ 2 * (10 + 14 * x)
  shape = solve 1 (λ x → con 20 :+ (x :+ con 27 :* x)
                           := con 2 :* (con 10 :+ con 14 :* x)) refl

visited-height-fits : ∀ (a b : ℕ) →
  a + b ≤ 3 + 2 * ((10 + 14 * a) + (10 + 14 * b))
visited-height-fits a b =
  ≤-trans (+-mono-≤ (visited-slot-fits a) (visited-slot-fits b))
          (≤-trans (≤-reflexive (sym (split a b)))
                   (m≤n+m (2 * ((10 + 14 * a) + (10 + 14 * b))) 3))
  where
  split : ∀ (x y : ℕ) → 2 * ((10 + 14 * x) + (10 + 14 * y))
                          ≡ 2 * (10 + 14 * x) + 2 * (10 + 14 * y)
  split = solve 2 (λ x y → con 2 :* ((con 10 :+ con 14 :* x)
                                       :+ (con 10 :+ con 14 :* y))
                             := con 2 :* (con 10 :+ con 14 :* x)
                                :+ con 2 :* (con 10 :+ con 14 :* y)) refl

------------------------------------------------------------------
-- §5  THE SOUNDNESS DIRECTION.
--
-- Every clause of the family is built from ⊔, +, * and ^ with the
-- measured children in POSITIVE position, so replacing a descent by 0
-- can only lower the result: the visited-set measure is everywhere at
-- or below the fuel measure at the same fuel.  Gated on the cycle,
-- where the gap is the whole tower, and on the acyclic telescope, where
-- §3 says the gap is zero.
--
-- That is the shape of the soundness argument, and it is also its
-- LIMIT: `≤ the old cap` is not the gate.  The gate is that every REAL
-- RUN's measured width still sits under the new (smaller) cap, which
-- only the State-Blowup wall can say — and §3 confines that question to
-- telescopes with a slot CYCLE, since every acyclic one computes the
-- IDENTICAL number, refl, in §3.  No State-Blowup or Frame-Work row
-- has a cyclic telescope, so no measured row moves.
--
-- NOT STATED AS `outWⱽ ≤ outWᵉ` ON THESE PROGRAMS, deliberately: `_≤_`
-- on ℕ is the unary z≤n / s≤s chain and `≤-refl` at 258 · 2 ^ 521 is
-- 10 ^ 159 constructors.  §3's equalities are the checkable form of the
-- same fact, and the general inequality is a clause-by-clause induction
-- that belongs in Caps-Face beside `monoᵉ`, not in a probe.
------------------------------------------------------------------

-- AND THE SAME WITH THE UNMARKED TURN PAID FOR.  Reading defs at `[]`
-- lets ONE of them be met twice, so the demand is `Σkᵢ + max kᵢ` rather
-- than `Σkᵢ`.  Still linear, and still with room: the max is under the
-- sum, and the sum is under the syntax twice over
visited-height-fits-unmarked : ∀ (a b : ℕ) →
  (a + b) + (a ⊔ b) ≤ 3 + 2 * ((10 + 14 * a) + (10 + 14 * b))
visited-height-fits-unmarked a b =
  ≤-trans (≤-trans (+-monoʳ-≤ (a + b) (⊔-lub (m≤m+n a b) (m≤n+m b a)))
                   (≤-reflexive (dbl (a + b))))
          (≤-trans (*-monoʳ-≤ 2 sum≤) (m≤n+m (2 * ((10 + 14 * a) + (10 + 14 * b))) 3))
  where
  dbl : ∀ (x : ℕ) → x + x ≡ 2 * x
  dbl = solve 1 (λ x → x :+ x := con 2 :* x) refl
  m14 : ∀ (x : ℕ) → x + 13 * x ≡ 14 * x
  m14 = solve 1 (λ x → x :+ con 13 :* x := con 14 :* x) refl
  sum≤ : a + b ≤ (10 + 14 * a) + (10 + 14 * b)
  sum≤ = +-mono-≤ (≤-trans (m≤m+n a (13 * a))
                           (≤-trans (≤-reflexive (m14 a)) (m≤n+m (14 * a) 10)))
                  (≤-trans (m≤m+n b (13 * b))
                           (≤-trans (≤-reflexive (m14 b)) (m≤n+m (14 * b) 10)))
