------------------------------------------------------------------
-- THE NESTING MEASURE `M`, and the frame row that supplies it.
--
-- The budget `k` the subscribe clique descends on counts nesting, and
-- Mu-Nest-Probe pinned which nesting: `syncSizeᵉ`, the measure that
-- stops at `deferᵉ` — the sole gate moving Δᵍ into Δ — and therefore
-- drops by exactly one across the μ edge, matching k's single descent
-- at `sLvlD S W d (suc k) J ↦ opIterD S W d k …`.
--
-- The term's own syncSize is NOT enough, and the reason is the share
-- edge.  `sharedConnect` subscribes the slot's STORED def, which is
-- structurally unrelated to the `input i` the caller was looking at —
-- a term-only hypothesis has one unit to offer a callee that needs the
-- def's whole nesting (Mu-Nest-Probe's `plain-share-absurd`).  So the
-- measure carries a RESIDUE: the nesting still owed by every share that
-- has not been connected yet.
--
--     M e sl cs = syncSizeᵉ e + resid sl cs
--
-- `resid` is .Measures' `unconn` reweighted — the same
-- `memberSource … connectedShares` mask the evaluator already keeps,
-- summed by the same `sum-tab-mono`, with an unconnected shared slot
-- contributing its def's syncSize instead of 1.  That is what makes it
-- sound: a share connects at most once ever (`sharedConnect` writes
-- `toℕ i` into `connectedShares` BEFORE walking the def, and
-- `subscribeSharedSlot` short-circuits on an already-connected one), so
-- the residue only ever falls, and the edge that spends it pays for
-- itself.
--
-- Note the residue does NOT reset per instant — `connectedShares` is
-- initialised `[]` once and is append-only — and does not need to:
-- `resid≤slots` holds for EVERY cs, so the frame row below is uniform
-- in whatever the connected set happens to be at frame entry.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Nest where

open import Data.Bool using (true; false; if_then_else_; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Nat  using (ℕ; suc; _+_; _*_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-monoʳ-≤; *-mono-≤;
         *-identityˡ; *-identityʳ; +-identityʳ; *-distribˡ-+;
         +-comm; m≤m+n; n≤1+n; ≡⇒≡ᵇ)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; _∷_; sum; tabulate)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Prim  using (Source)
open import Rx.Exp   using (Ctx; Exp; Closed; syncSizeᵉ; sizeᵉ)
open import Rx.Slots using (Slots; scripted; shared; slotSize; slotsSize)
open import Rx.Evaluator using (sizeAt; memberSource; sameSource)
open import Verify-Budget-Sufficient.Caps
  using (iterSize-suc; sizeAt-mono; syncSize≤sizeᵉ; sum-tab-mono; T⇒≡true)

------------------------------------------------------------------
-- § 1.  THE RESIDUE — `unconn`, reweighted.
------------------------------------------------------------------

residAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
residAt sl cs i with sl i
... | shared d   = if memberSource (toℕ i) cs then 0 else syncSizeᵉ d
... | scripted _ = 0

resid : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
resid sl cs = sum (tabulate (residAt sl cs))

-- the residue is syntactically owned, uniformly in cs: every entry is
-- either masked out or a def's syncSize, and syncSize sits under size
residAt≤slot : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n) →
  residAt sl cs i ≤ slotSize (sl i)
residAt≤slot sl cs i with sl i
... | scripted s = z≤n
... | shared d with memberSource (toℕ i) cs
...   | true  = z≤n
...   | false = syncSize≤sizeᵉ d

resid≤slots : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) →
  resid sl cs ≤ slotsSize sl
resid≤slots sl cs = sum-tab-mono _ _ (residAt≤slot sl cs)

-- connecting anything never raises the residue …
residAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → residAt sl (s ∷ cs) i ≤ residAt sl cs i
residAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared d with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

resid-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (s : Source) →
  resid sl (s ∷ cs) ≤ resid sl cs
resid-cons-≤ sl cs s = sum-tab-mono _ _ (residAt-cons-≤ sl cs s)

-- … and connecting slot i zeroes i's own contribution outright, which
-- is the unit the share edge hands its callee
residAt-connected : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n) →
  residAt sl (toℕ i ∷ cs) i ≡ 0
residAt-connected sl cs i with sl i
... | scripted _ = refl
... | shared d
  rewrite T⇒≡true (toℕ i ≡ᵇ toℕ i) (≡⇒≡ᵇ (toℕ i) (toℕ i) refl) = refl

------------------------------------------------------------------
-- § 2.  M, and the ONE inequality the frame refresh spends.
------------------------------------------------------------------

M : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Slots Γ → List Source → ℕ
M e sl cs = syncSizeᵉ e + resid sl cs

M≤ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t)
  (sl : Slots Γ) (cs : List Source) → M e sl cs ≤ sizeᵉ e + slotsSize sl
M≤ e sl cs = +-mono-≤ (syncSize≤sizeᵉ e) (resid≤slots sl cs)

------------------------------------------------------------------
-- § 3.  THE FRAME ROW.  A frame holds `sizeᵉ o ≤ sizeAt S j` for its
-- payload and `slotsSize sl ≤ S` for the telescope, so M is bounded by
-- `sizeAt S j + S` — one summand MORE than the entry level.  The entry
-- level cannot pay for it: `sizeAt S j + S ≤ suc (sizeAt S j)` wants
-- `S ≤ 1`, against the clique's own `2 ≤ S` (Share-Residue-Probe § 1
-- refutes it at S = 2, j = 0).  ONE MORE SIZE LEVEL pays for it with
-- room to spare, because `sizeAt S (suc j)` unfolds to
-- `S * suc (2 * sizeAt S j)` — the `+ S` is already there and the rest
-- needs only `1 ≤ 2 * S`.  Levels are the cheap currency, and reading k
-- one level up is a RAISE, so every consumer already landed moves with
-- it under `sizeAt-mono` and nothing is re-derived.
------------------------------------------------------------------

sizeAt-suc : ∀ (S J : ℕ) → sizeAt S (suc J) ≡ S * suc (2 * sizeAt S J)
sizeAt-suc S J = iterSize-suc S J S

-- the arithmetic core, with no measure in it
core : ∀ (S x : ℕ) → 1 ≤ S → x + S ≤ S * suc (2 * x)
core S x 1≤S =
  ≤-trans (≤-trans (≤-reflexive (+-comm x S)) (+-monoʳ-≤ S x≤S2x))
          (≤-reflexive step)
  where
  x≤2x : x ≤ 2 * x
  x≤2x = ≤-trans (m≤m+n x x) (≤-reflexive (sym (cong (x +_) (+-identityʳ x))))

  x≤S2x : x ≤ S * (2 * x)
  x≤S2x = ≤-trans (≤-reflexive (sym (*-identityˡ x))) (*-mono-≤ 1≤S x≤2x)

  step : S + S * (2 * x) ≡ S * suc (2 * x)
  step = trans (cong (_+ S * (2 * x)) (sym (*-identityʳ S)))
               (sym (*-distribˡ-+ S 1 (2 * x)))

one-level-supply : ∀ (S j x y : ℕ) →
  1 ≤ S → x ≤ sizeAt S j → y ≤ S → x + y ≤ suc (sizeAt S (suc j))
one-level-supply S j x y 1≤S hx hy =
  ≤-trans (≤-trans (+-mono-≤ hx hy) (core S (sizeAt S j) 1≤S))
          (≤-trans (≤-reflexive (sym (sizeAt-suc S j))) (n≤1+n (sizeAt S (suc j))))

-- the row in the shape the frame clause states it
refresh-supplies-M : ∀ {n} {Γ : Ctx n} (S j : ℕ) {Δᵍ Δ Θ t}
  (o : Exp Γ Δᵍ Δ Θ t) (sl : Slots Γ) (cs : List Source) →
  1 ≤ S → sizeᵉ o ≤ sizeAt S j → slotsSize sl ≤ S →
  M o sl cs ≤ suc (sizeAt S (suc j))
refresh-supplies-M S j o sl cs 1≤S hsz hsl =
  one-level-supply S j (syncSizeᵉ o) (resid sl cs) 1≤S
    (≤-trans (syncSize≤sizeᵉ o) hsz)
    (≤-trans (resid≤slots sl cs) hsl)

-- the raise IS a raise: whatever the old k bought, the new one buys
k-raise : ∀ (S J : ℕ) → 1 ≤ S → suc (sizeAt S J) ≤ suc (sizeAt S (suc J))
k-raise S J 1≤S = s≤s (sizeAt-mono 1≤S ≤-refl (n≤1+n J))
