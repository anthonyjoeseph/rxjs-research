-- ══════════════════════════════════════════════════════════════════
-- THE STORE'S CEILING ENTRY IS UNSATISFIABLE, AT EVERY TERM AND EVERY
-- CAP.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE ROUTE SAID.  The store carries, for every term sitting in a
-- `mergeAll` queue, a ceiling AT EVERY LEVEL UNDER THE COUNT.  The
-- quantifier is what made the entry look supplyable at a distance: a
-- queue is written by one arm and read by another with an arbitrary
-- amount of walking in between, so the reader's level is unknown at
-- the write, and asking for all of them at once is the only entry a
-- writer could meet without knowing who reads it.
--
-- WHY IT CANNOT WORK, AND IT IS THE TOP OF THE RANGE.  A ceiling is
-- the REMAINING budget -- it says a descent starting here still fits
-- under the count -- so at the count itself there is nothing left,
-- while one operator of the level ladder steps strictly past whatever
-- level it is read at.  Read at its own upper endpoint the entry
-- therefore asks for one more than the roof, and that is a
-- contradiction in the naturals rather than a demand on the term: the
-- refutation below quantifies over every cap, every depth, every
-- telescope and every parked term, and spends none of them.
--
-- SO THIS IS NOT A MISSING PRODUCER BUT A FALSE CONJUNCT, and any
-- invariant carrying it discharges its consumers vacuously rather than
-- at all.  The endpoint being INCLUDED is the whole defect, so nothing
-- here is evidence about a range that stops short of the roof.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Park-Free where

open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; +-comm; n≮n; m+[n∸m]≡n)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (opIterD; opIterD-suc; sizeAt; sLvlD; widAt)
open import Verify-Budget-Sufficient.Caps using (Caps; sizeCount;
  sLvlD-infl; opIterD-infl; fIterD-infl)
open import Verify-Budget-Sufficient.Caps-Nest using (nest)
open import Verify-Budget-Sufficient.Nest-Ceiling using (CeilD)

-- ONE OPERATOR ALREADY STEPS, which is the whole engine.  The proven
-- inflation chain for this family starts by weakening `suc J` to `J`;
-- keeping that first step is a strict bound, and it holds at every
-- fuel, every payload count and every level.
opIterD-strict : ∀ (S W d k m J : ℕ) → suc J ≤ opIterD S W d k (suc m) J
opIterD-strict S W d k m J =
  ≤-trans (≤-trans (≤-trans (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J))))
                            (≤-trans (sLvlD-infl S W d k J₀)
                                     (opIterD-infl S W d k m (sLvlD S W d k J₀))))
                   (fIterD-infl S W d k (suc (widAt S W J₂)) J₂))
          (≤-reflexive (sym (opIterD-suc S W d k m J)))
  where
  J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
  J₂ = opIterD S W d k m (sLvlD S W d k J₀)

-- THE ENTRY AT ONE PARKED TERM, restated here rather than imported --
-- the store's own per-term conjunct, which is what the arm that parks
-- a term would have had to establish for the term it appends.
ParkOne : ∀ {n} {Γ : Ctx n} {u} → Caps → ℕ → Slots Γ → List Source → Closed Γ u → Set
ParkOne c d sl sh o =
  ∀ (Lv : ℕ) → Lv ≤ sizeCount c d ⊔ Caps.cSize c →
    CeilD c d Lv (nest o sl sh) (suc (suc (sizeᵉ o)))

park-absurd : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (d : ℕ) (sl : Slots Γ)
  (sh : List Source) (o : Closed Γ u) → ParkOne c d sl sh o → ⊥
park-absurd c d sl sh o H = n≮n TOP (subst (_≤ TOP) (+-comm TOP 1) over)
  where
  TOP = sizeCount c d ⊔ Caps.cSize c
  over : TOP + 1 ≤ TOP
  over = H TOP ≤-refl 1
           (subst (_≤ opIterD (Caps.cSize c) (Caps.cWid c) d
                       (nest o sl sh) (suc (suc (sizeᵉ o))) TOP)
                  (sym (+-comm TOP 1))
                  (opIterD-strict (Caps.cSize c) (Caps.cWid c) d
                     (nest o sl sh) (suc (sizeᵉ o)) TOP))

-- AND IT IS NOT THE ENDPOINT, WHICH IS WHAT STOPS THE RANGE BEING
-- TIGHTENED INSTEAD.  A ceiling fails at EVERY level whose own ladder
-- outgrows the roof, and the ladder is a tower while the roof is one
-- delivery count -- so the levels where the relation holds are the
-- levels a term's descent genuinely fits at, which is a fact about the
-- TERM.  No range of levels can be quantified over for all terms, and
-- the row above is one instance of this rather than a boundary case.
ceil-absurd-at : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (d : ℕ) (sl : Slots Γ)
  (sh : List Source) (o : Closed Γ u) (Lv : ℕ) →
  let TOP = sizeCount c d ⊔ Caps.cSize c in
  Lv ≤ suc TOP →
  suc TOP ≤ opIterD (Caps.cSize c) (Caps.cWid c) d (nest o sl sh)
             (suc (suc (sizeᵉ o))) Lv →
  CeilD c d Lv (nest o sl sh) (suc (suc (sizeᵉ o))) → ⊥
ceil-absurd-at c d sl sh o Lv hLv hlad H =
  n≮n TOP (subst (_≤ TOP) (m+[n∸m]≡n hLv) (H (suc TOP ∸ Lv)
    (subst (_≤ opIterD (Caps.cSize c) (Caps.cWid c) d (nest o sl sh)
                (suc (suc (sizeᵉ o))) Lv)
           (sym (m+[n∸m]≡n hLv)) hlad)))
  where
  TOP = sizeCount c d ⊔ Caps.cSize c
