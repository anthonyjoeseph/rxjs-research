------------------------------------------------------------------
-- THE SHARE-RESIDUE PROBE: can the frame refresh SUPPLY the nesting
-- measure, once the measure carries the unconnected slots?
--
-- Mu-Nest-Probe fixed the measure: a subscribe is bounded by
--
--     M b U = syncSizeᵉ b + Σ_{i ∈ U} syncSizeᵉ (def i)
--
-- with U the slots not yet in `connectedShares`.  What that probe did
-- NOT check — and what this one does, first, because it is the most
-- uncertain piece and the one that decides the whole approach — is
-- whether a frame's refreshed `k` dominates M for the payloads that
-- frame subscribes.  The receipts a frame has are
--
--     sizeᵉ o    ≤ Caps.cSize (frameStep j c)  ≡  sizeAt S j   (valsCaps?)
--     slotsSize sl ≤ Caps.cSize c              ≡  S            (the clique's slSz)
--
-- so M is bounded by `sizeAt S j + S` and NOT by `sizeAt S j` alone.
--
-- § 1  DISCHARGE (i) — k at the entry level, `suc (sizeAt S J)`, as
--   `fLvlD` instantiates it today — FAILS, and not marginally: it needs
--   `S ≤ 1` against the clique's own `2 ≤ S`.  `entry-level-absurd`
--   refutes the general row, at the smallest witness there is
--   (S = 2, j = 0: the row demands 4 ≤ 3).
--
-- § 2  DISCHARGE (ii) — k at ONE MORE size level, `suc (sizeAt S (suc J))`
--   — HOLDS, with room to spare.  `sizeAt S (suc J)` is
--   `S * suc (2 * sizeAt S J)`, which already contains `2 * S * sizeAt S J`;
--   the row needs only `1 ≤ 2 * S`.  It does not even need `S ≤ sizeAt S J`.
--   This is the approved discharge, so § 2 also carries the rows the
--   FAMILY EDIT will need: the clause `fLvlD S W (suc d) J` reads its k
--   at `suc (sizeAt S (suc J))` instead of `suc (sizeAt S J)`, which is a
--   RAISE, so every existing consumer moves up by the k-monotonicity
--   already proven (`sIterD-mono`) and nothing is re-derived.
--
-- § 3  THE RESIDUE ITSELF is bounded by `slotsSize sl` with no
--   distinctness side condition, because it is a MASKED sum over the
--   whole telescope rather than a sum over a list of indices: every
--   entry is either dropped (0) or `syncSizeᵉ d ≤ sizeᵉ d`.  It is
--   .Measures' `unconn` REWEIGHTED — same `memberSource … connectedShares`
--   mask, same `sum-tab-mono` — so `unconn`'s lifecycle lemmas each have
--   a residue twin proven the same way, and § 3 lands as `resid≤slots`
--   beside the existing `unconn≤slots`.
--
-- § 4  AND THE RESET PREMISE IS NOT NEEDED.  `connectedShares` starts
--   `[]` at `st-init` (Rx.Evaluator:934) and is only ever CONSED to, at
--   the single write in `sharedConnect` (:1338); the only other mentions
--   in the evaluator are the field declaration (:286, "connect happens
--   once, ever") and the `memberSource` read in `subscribeSharedSlot`
--   (:1363).  There is no per-instant reset, so the residue does NOT
--   return to full between instants.  It does not have to: § 3's bound
--   holds for EVERY cs, so the refresh row is uniform in whatever
--   `connectedShares` happens to be at frame entry, and the measure is
--   monotonically spent over the whole run rather than per instant.
--   That is strictly stronger than the reset premise and removes the
--   question.
--
-- § 5  M assembled, plus `M≤` — the one inequality the frame refresh
--   spends, `M e sl cs ≤ sizeᵉ e + slotsSize sl`, which is exactly the
--   `x + y` § 2 supplies.
------------------------------------------------------------------
module Share-Residue-Probe where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-monoʳ-≤; *-mono-≤;
         *-identityˡ; *-identityʳ; +-identityʳ; *-distribˡ-+;
         +-comm; m≤m+n; n≤1+n; ≡⇒≡ᵇ)
open import Data.Empty using (⊥)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; _∷_; sum; tabulate)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim  using (Source)
open import Rx.Exp   using (Ctx; Exp; Closed; syncSizeᵉ; sizeᵉ)
open import Rx.Slots using (Slot; Slots; scripted; shared; slotSize; slotsSize)
open import Rx.Evaluator using (sizeAt; sizeStep; memberSource; sameSource)
open import Verify-Budget-Sufficient.Caps using (iterSize-suc; sizeAt-mono)
open import Verify-Budget-Sufficient.Measures
  using (syncSize≤sizeᵉ; sum-tab-mono; T⇒≡true)

------------------------------------------------------------------
-- § 1.  THE ROW AT THE ENTRY LEVEL, WHICH IS WHAT fLvlD READS TODAY
------------------------------------------------------------------

Entry-Level-Supply : Set
Entry-Level-Supply = ∀ (S j x y : ℕ) →
  2 ≤ S → x ≤ sizeAt S j → y ≤ S → x + y ≤ suc (sizeAt S j)

-- sizeAt 2 0 is 2, so the row demands 2 + 2 ≤ 3
entry-level-absurd : Entry-Level-Supply → ⊥
entry-level-absurd H with H 2 0 2 2 (s≤s (s≤s z≤n)) ≤-refl ≤-refl
... | s≤s (s≤s (s≤s ()))

------------------------------------------------------------------
-- § 2.  THE ROW AT ONE MORE SIZE LEVEL.  `sizeAt S (suc J)` unfolds to
-- `S * suc (2 * sizeAt S J)` (iterSize-suc), which is `S + 2 * S * x`
-- with x the entry level's cap — the `+ S` the residue costs is already
-- there, and the `x` is covered because `1 ≤ 2 * S`
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

-- and the same row in the shape the frame clause will state it: the
-- payload's own measure against the raised k
refresh-supplies-M : ∀ {n} {Γ : Ctx n} (S j resid : ℕ) {t} (o : Closed Γ t) →
  1 ≤ S → sizeᵉ o ≤ sizeAt S j → resid ≤ S →
  syncSizeᵉ o + resid ≤ suc (sizeAt S (suc j))
refresh-supplies-M S j resid o 1≤S hsz hr =
  one-level-supply S j (syncSizeᵉ o) resid 1≤S
    (≤-trans (syncSize≤sizeᵉ o) hsz) hr

-- THE RAISE IS A RAISE: whatever the old k bought, the new one buys
-- too, so every landed consumer moves up by k-monotonicity alone
k-raise : ∀ (S J : ℕ) → 1 ≤ S → suc (sizeAt S J) ≤ suc (sizeAt S (suc J))
k-raise S J 1≤S = s≤s (sizeAt-mono 1≤S ≤-refl (n≤1+n J))

------------------------------------------------------------------
-- § 3.  THE RESIDUE.  A masked sum over the whole telescope: a slot
-- already in `connectedShares` contributes nothing, a scripted slot
-- contributes nothing (only a `shared` def is ever subscribed by a
-- connect), and a live shared slot contributes its def's syncSize
------------------------------------------------------------------

-- the mask is the one the evaluator already keeps: `connectedShares`,
-- read through `memberSource`, exactly as .Measures' `unconnAt` reads
-- it.  The residue is that same count REWEIGHTED — an unconnected
-- shared slot contributes its def's syncSize instead of 1 — so every
-- structural lemma about `unconn` (antitone in cs, never rises on a
-- cons, ≤ slotsSize) has a residue twin proven the same way, off the
-- same `sum-tab-mono`
residAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
residAt sl cs i with sl i
... | shared d   = if memberSource (toℕ i) cs then 0 else syncSizeᵉ d
... | scripted _ = 0

resid : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
resid sl cs = sum (tabulate (residAt sl cs))

-- the § 3 bound, uniform in cs — which is what makes § 4's missing
-- reset a non-issue
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

-- and the two lifecycle rows the connect edge will spend: a cons never
-- raises the residue, and connecting slot i drops i's own contribution
-- to 0 outright
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

residAt-connected : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n) →
  residAt sl (toℕ i ∷ cs) i ≡ 0
residAt-connected sl cs i with sl i
... | scripted _ = refl
... | shared d
  rewrite T⇒≡true (toℕ i ≡ᵇ toℕ i) (≡⇒≡ᵇ (toℕ i) (toℕ i) refl) = refl

------------------------------------------------------------------
-- § 5.  M ITSELF — the nesting measure the 13 signatures will carry:
-- the term's own syncSize plus the residue of everything the connect
-- edge can still hand it.  The share edge's step is § 3 + the
-- residAt-connected row; the μ and chain edges are Mu-Nest-Probe's
-- `mu-residue-step` / `chain-residue-step` with `resid sl cs` as the
-- residue, and the frame refresh is § 2's `refresh-supplies-M`
------------------------------------------------------------------

M : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Slots Γ → List Source → ℕ
M e sl cs = syncSizeᵉ e + resid sl cs

M≤ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (cs : List Source) →
  M e sl cs ≤ sizeᵉ e + slotsSize sl
M≤ e sl cs = +-mono-≤ (syncSize≤sizeᵉ e) (resid≤slots sl cs)
