{-# OPTIONS --guardedness #-}

-- A HOT'S ROWS ARE BOUNDED WHERE ITS SOURCE IS (`hot-rows-bounded`).  A
-- hot lists its source's proper rows (`quickcheck.Tabled.hotOf`), and
-- cutting a bounded source at its end keeps its gaps, its held
-- boundaries and its settling (`ProperCuts`): an end past the settled
-- prefix lies past every row of it.
--
-- A pin is settled on less than its row's prefix, so whether an end
-- before it moves is a fact about the source (`hot-pin-ends`).
--
-- DEAD ROUTE: deriving `hot-pin-ends` from `Cuts.Bounded` alone.  Two
-- cuts, the shallower holding a pin of `q` at `y` and a boundary `b`
-- with `q ≺ b`, the deeper the same pin and an end at `c₀` with
-- `b ≼ c₀ ≺ y`, are bounded by `b`: `Clear N q` holds, and no row before
-- `b` moves.  The end moved, so the hot of the shallower cut keeps the
-- pin and the deeper drops it.
module simultaneous.HotRows where

open import Data.List using ([_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Tree using (Obs)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet; pin; end; Proper; _≺_; _≼_)
open import denotation.Laws.Modulus using (⟨_⟩; upto; ≺→≼; ≼-≺-≺; ≼-or-≻)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import quickcheck.Tabled.Exact using (proper-exact)
open import quickcheck.Tabled.Exact.Base using (Exact; sound; complete)
open import simultaneous.Listing using (listC-ok; UncutEnv)
open import simultaneous.TableKit using (Rows)
open import simultaneous.ListTR using (self-exact)
open import simultaneous.Horizon using (Tag; module Cuts; bounded-≃)
open import simultaneous.HorizonTree using (Cut; srcL)

------------------------------------------------------------------------
-- Cuts cut at their ends

module ProperCuts {A : Set} (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set) (B : Cuts.Bounded c Bd)
  -- an end before a settled pin is settled
  (ends : ∀ {N q k N′ y c₀} → Cuts.Clear c Bd N q → Cuts.HeldClear c Bd N q k → N ≤ N′ → y ≼ k
        → c N y (pin q) → c₀ ≺ y → (c N c₀ end → c N′ c₀ end) × (c N′ c₀ end → c N c₀ end))
  where

  open Cuts c Bd
  module B = Bounded B
  module P = Cuts (λ N → Proper (c N)) Bd

  -- An end in the other cut lies past `k`, or is one here.
  move : ∀ {k} {t t′ : EmissionSet A} → (∀ {z e′} → z ≼ k → t z e′ → t′ z e′) → (∀ {z e′} → z ≼ k → t′ z e′ → t z e′)
       → ∀ {y e} → y ≼ k → Proper t y e → Proper t′ y e
  move {k} {t} {t′} to from {y} {e} yk (x , pe) = to {y} {e} yk x , λ {c₀} x′ → help c₀ x′
    where
      help : ∀ c₀ → t′ c₀ end → y ≼ c₀
      help c₀ x′ with ≼-or-≻ c₀ k
      ... | inj₁ ck = pe (from {c₀} {end} ck x′)
      ... | inj₂ kc = ≺→≼ {y} {c₀} (≼-≺-≺ {y} {k} {c₀} yk kc)

  fwd : ∀ {N k} → Clear N k → P.Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} {e} yk → move {k} {c N} {c N′} (λ {z} {e′} zk → proj₁ (upto ag {z} {e′} zk)) (λ {z} {e′} zk → proj₂ (upto ag {z} {e′} zk)) {y} {e} yk
                                         , move {k} {c N′} {c N} (λ {z} {e′} zk → proj₂ (upto ag {z} {e′} zk)) (λ {z} {e′} zk → proj₁ (upto ag {z} {e′} zk)) {y} {e} yk) ⟩
    where
      ag = B.fwd {N} {k} cl le

  fwd-pin : ∀ {N q k} → Clear N q → HeldClear N q k → P.PinSettled N q k
  fwd-pin {N} {q} {k} cl hc {N′} le {y} yk = to , from
    where
      pa = B.fwd-pin {N} {q} {k} cl hc le yk

      to : Proper (c N) y (pin q) → Proper (c N′) y (pin q)
      to (x , pe) = proj₁ pa x , λ {c₀} x′ → help c₀ x′
        where
          help : ∀ c₀ → c N′ c₀ end → y ≼ c₀
          help c₀ x′ with ≼-or-≻ y c₀
          ... | inj₁ yc = yc
          ... | inj₂ cy = pe (proj₂ (ends {N} {q} {k} {N′} {y} {c₀} cl hc le yk x cy) x′)

      from : Proper (c N′) y (pin q) → Proper (c N) y (pin q)
      from (x′ , pe) = proj₂ pa x′ , λ {c₀} x → help c₀ x
        where
          help : ∀ c₀ → c N c₀ end → y ≼ c₀
          help c₀ xe with ≼-or-≻ y c₀
          ... | inj₁ yc = yc
          ... | inj₂ cy = pe (proj₁ (ends {N} {q} {k} {N′} {y} {c₀} cl hc le yk (proj₂ pa x′) cy) xe)

  bounded : P.Bounded
  bounded = record
    { gap = λ bd x → B.gap bd (proj₁ x) ; held-in = B.held-in ; held-under = B.held-under
    ; fwd = λ {N} {k} → fwd {N} {k} ; fwd-pin = λ {N} {q} {k} → fwd-pin {N} {q} {k} }

------------------------------------------------------------------------
-- A hot

postulate
  -- AN END BEFORE A SETTLED PIN OF A SOURCE IS SETTLED.
  hot-pin-ends : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {Bd : ℕ → Pos → Tag → Set}
               → Cuts.Bounded (Cut n s ρ (p ⊕ [ ix 1 ])) Bd
               → ∀ {N q k N′ y c₀} → Cuts.Clear (Cut n s ρ (p ⊕ [ ix 1 ])) Bd N q → Cuts.HeldClear (Cut n s ρ (p ⊕ [ ix 1 ])) Bd N q k
               → N ≤ N′ → y ≼ k → Cut n s ρ (p ⊕ [ ix 1 ]) N y (pin q) → c₀ ≺ y
               → (Cut n s ρ (p ⊕ [ ix 1 ]) N c₀ end → Cut n s ρ (p ⊕ [ ix 1 ]) N′ c₀ end)
               × (Cut n s ρ (p ⊕ [ ix 1 ]) N′ c₀ end → Cut n s ρ (p ⊕ [ ix 1 ]) N c₀ end)

-- A HOT'S ROWS are its source's proper rows, cut where the source is.
hot-rows-bounded : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {Bd : ℕ → Pos → Tag → Set}
                 → Cuts.Bounded (Cut n s ρ (p ⊕ [ ix 1 ])) Bd → Cuts.Bounded (λ N → Rows (hotOf (srcL n s uρ p N))) Bd
hot-rows-bounded n s {ρ} uρ p {Bd} B =
  bounded-≃ (λ {N} → complete (ex N)) (λ {N} → sound (ex N))
    (ProperCuts.bounded (Cut n s ρ (p ⊕ [ ix 1 ])) Bd B
      (λ {N} {q} {k} {N′} {y} {c₀} → hot-pin-ends n s uρ p B {N} {q} {k} {N′} {y} {c₀}))
  where
    ex : ∀ N → Exact (hotOf (srcL n s uρ p N)) (Proper (Cut n s ρ (p ⊕ [ ix 1 ]) N))
    ex N = proper-exact (self-exact (proj₁ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ])))))
                        (proj₂ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))))
