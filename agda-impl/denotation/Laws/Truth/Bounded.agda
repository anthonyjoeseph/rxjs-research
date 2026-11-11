{-# OPTIONS --guardedness #-}

-- A BOUNDED MERGE KEEPS THE TRUTH: a joining
-- (`denotation.Laws.Truth.Joining`) whose lane `i` sits where the
-- schedule subscribes it, at its value's second child or at the second
-- child of the end that frees it.  Of two lanes, the earlier is apart
-- from the later or ends where the later is queued
-- (`denotation.Laws.BoundedInv`), so no other lane reaches under a
-- lane's cut.  A lane of the next pinning past a lane's cut is that
-- lane: a later one lies past the cut's spin, and an earlier one's end,
-- before the cut's lane is subscribed, is the next's too.
module denotation.Laws.Truth.Bounded where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_])
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _<_; _≤_; _≟_)
open import Data.Nat.Properties using (<-cmp; ≤-refl; m≤n⇒m<n∨m≡n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; _⊕_; inside)
open import denotation.EmissionSet using (out; end; pin; Silent; EmissionSet; Den; enter; After; _≺_; _≼_; module Values; module Bounded; module Op)
open import denotation.Read using (loud)
open import denotation.Laws.Modulus using (AgreeTo; AgreeTo-sym; ≺-trans; ≺→≼; ≼-refl; ≺-ext; ≺-irrefl)
open import denotation.Laws.Count using (pinned-after)
open import denotation.Laws.Shows using (ShowsK; k-shows)
open import denotation.Laws.Worlds using (W; W⁼; here; inW; Real; Ok; InvAt; InvD; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc; ⊑-snoc⁺; leads; plain-ix;
  world-after; inside-⊑; nest; nest⁼; nest-in; flat-under)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI)
import denotation.Laws.Join as LJ
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.Truth using (Truth; Rel; Spun; Lies; below-next)
open import denotation.Laws.Truth.Joining using (Slots; module Core; under-c; lies-⊑)

-- A second child's world lies past its parent.
end-before : ∀ {H c s} → Real s → W⁼ H (c ⊕ [ ix 1 ]) s → c ≺ s
end-before {c = c} _ here = ≺-ext c {ix 1} []
end-before {c = c} {s} rs (inW w) = ≺-trans {c} {c ⊕ [ ix 1 ]} {s} (≺-ext c {ix 1} []) (world-after w rs)

-- A bounded merge's lanes, each where the schedule subscribes it.
module BoundedSide {A B : Set} {H : Pos → Set} {p : Pos} (ok : Ok H p) (n : ℕ) (g : A → Den B) (Ig : ∀ a → InvD H (g a))
                   {u : EmissionSet A} (Iu : InvAt H p u) where
  open Bounded n g u using (Sub; Lane)
  open Values u using (Nth)
  open Nths u using (nth-val; nth-fun; nth-lt)
  module BI = BoundedI ok n g Ig Iu
  open BI using (Lr; lr-row; apart; queued-in)

  Sl : Pos → A → Pos → Set
  Sl q a s = Σ ℕ λ i → Sub i q s a

  -- A lane's pin row is its own.
  lr-pin : ∀ {i q s a y r} → Sub i q s a → After (g a) s y (pin r) → Lr a s y
  lr-pin sb ly = lr-row ly λ ae _ → pin≢end (InvAt.func (BI.LI sb) (proj₁ ly) (proj₁ ae))
    where
      pin≢end : ∀ {r} → pin {B} r ≡ end → ⊥
      pin≢end ()

  -- Two lanes, each holding a connect, one with a row under it.
  two-r : ∀ {i i′ q q′ s s′ a a′ r y} → i < i′ → Sub i q s a → Sub i′ q′ s′ a′ → W⁼ H s r → W⁼ H s′ r → Lr a s y → r ⊑ y → ⊥
  two-r lt sb sb′ r⁼ r⁼′ ly ry with BI.rel lt sb sb′
  ... | apart xr xr′ ne rw rw′ = BI.apart-ww xr xr′ ne (nest⁼ rw r⁼) (nest⁼ rw′ r⁼′)
  ... | queued-in ac _ v      = BI.nest-back sb ac (nest⁼ v r⁼′) ly ry

  meet : ∀ {q₀ a₀ s₀ z q a k r} → u q₀ (out a₀) → Sl q₀ a₀ s₀ → enter (g a₀) s₀ z (pin r) → u q (out a) → Lane q a k (pin r)
       → enter (g a₀) s₀ k (pin r)
  meet {z = z} {k = k} {r} _ (i₀ , sb₀) lz _ (i , _ , sb , lk) with <-cmp i i₀
  ... | tri< lt _ _ = ⊥-elim (two-r lt sb sb₀ (proj₁ (InvAt.pinned (BI.LI sb) (proj₁ lk))) (proj₁ (InvAt.pinned (BI.LI sb₀) lz))
                                    (lr-pin sb lk) (inside-⊑ r k (proj₂ (InvAt.pinned (BI.LI sb) (proj₁ lk)))))
  ... | tri> _ _ gt = ⊥-elim (two-r gt sb₀ sb (proj₁ (InvAt.pinned (BI.LI sb₀) lz)) (proj₁ (InvAt.pinned (BI.LI sb) (proj₁ lk)))
                                    (lr-pin sb₀ (lz , world-after (InvAt.world (BI.LI sb₀) lz) (InvAt.real (BI.LI sb₀) lz)))
                                    (inside-⊑ r z (proj₂ (InvAt.pinned (BI.LI sb₀) lz))))
  ... | tri≈ _ refl _ with BI.sub-fun sb sb₀
  ...   | refl , refl , refl = proj₁ lk

  -- A value no later than a lane's own.
  le-nth : ∀ {k i ρ q b a} → k ≤ i → Nth k ρ b → Nth i q a → ρ ≼ q
  le-nth {ρ = ρ} {q} k≤i nr nq with m≤n⇒m<n∨m≡n k≤i
  ... | inj₁ lt = ≺→≼ {ρ} {q} (nth-lt lt nr nq)
  ... | inj₂ refl with nth-fun nr nq
  ...   | refl = ≼-refl {ρ}

  seat : ∀ {q a s} → u q (out a) → Sl q a s → Σ Pos λ ρ → Σ A λ b → u ρ (out b) × ρ ≼ q × W⁼ H (ρ ⊕ [ ix 1 ]) s
  seat _ (_ , sb) with BI.seat* sb
  ... | BI.seat′ {r = ρ} {b} _ _ k≤i nr rw = ρ , b , nth-val nr , le-nth k≤i nr (proj₁ sb) , rw

  slots : Slots H g u Lane
  slots = record
    { Sl   = Sl
    ; slot = λ { (i , s , sb , l) → s , (i , sb) , l }
    ; mk   = λ { (i , sb) l → i , _ , sb , l }
    ; okS  = λ _ sl → BI.okS (proj₂ sl)
    ; past = λ { (_ , sb) → LJ.Join.BoundedJ.starts-past {A} {B} p n (proj₂ sb) }
    ; seat = seat
    ; meet = meet
    }

-- The bounded merge: lanes where the schedule subscribes them, a queued
-- lane handed its place at an end.
module Bnds {A B : Set} {H : Pos → Set} (n : ℕ) {f f′ : A → Den B} {s s′ : Den A}
            (Is : InvD H s) (Is′ : InvD H s′) (If : ∀ a → InvD H (f a)) (If′ : ∀ a → InvD H (f′ a))
            (R : Rel H s s′) (Rf : ∀ a → Rel H (f a) (f′ a)) (p : Pos) (ok : Ok H p) where
  o o′ : EmissionSet A
  o  = enter s p
  o′ = enter s′ p

  open Bounded n f o using (Sub; Lane; Indexed; Queued)
  open Nths o using (nth-val)
  module J  = BoundedSide ok n f If (Is p ok)
  module J′ = BoundedSide ok n f′ If′ (Is′ p ok)
  module BI = J.BI
  open BI using (Lr; lr-row; lr-hand; apart; queued-in)
  module C  = Core {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ g u → Bounded.Lane n g u) (λ g u → Bounded.Indexed n g u)
                   (λ _ _ _ _ → ⊥) (λ g u → Bounded.Queued n g u) J.slots J′.slots

  Lanes : Pos → Set
  Lanes Q = LJ.Join.BoundedJ.Lanes {A} {B} Q n o f f′

  -- A lane of the next, read on this side.
  I′ : ∀ {i q s₁ a} → Sub i q s₁ a → InvAt H s₁ (enter (f′ a) s₁)
  I′ {s₁ = s₁} {a} sb = If′ a s₁ (BI.okS sb)

  -- A lane's row, or the first child of its queued end.
  lr-any : ∀ {a s₁ y e} → After (f a) s₁ y e → (Lr a s₁ y → ⊥) → (Lr a s₁ (y ⊕ [ ix 0 ]) → ⊥) → ⊥
  lr-any ly k₁ k₂ = k₁ (lr-row ly (λ ae Q → k₂ (lr-hand ae Q refl)))

  -- Another lane than a cut's, against the cut.
  module Off {X : EmissionSet B} {i₀ q₀ a₀ s₀ c} (sb₀ : Sub i₀ q₀ s₀ a₀) (tr : Truth (enter (f a₀) s₀) X) (c⁼ : W⁼ H s₀ c)
             (ct : Truth.Cut tr c) where
    I₀ : InvAt H s₀ (enter (f a₀) s₀)
    I₀ = BI.LI sb₀

    z₀ : Pos
    z₀ = proj₁ (Truth.shows tr ct 0)

    cz₀ : (c ⊕ [ ix 0 ]) ⊑ z₀
    cz₀ = proj₁ (proj₂ (proj₂ (Truth.shows tr ct 0)))

    lz₀ : enter (f a₀) s₀ z₀ (proj₁ (proj₂ (Truth.shows tr ct 0)))
    lz₀ = proj₂ (proj₂ (proj₂ (Truth.shows tr ct 0)))

    -- The cut's first spin row: silent, so no queued end.
    lr₀ : Lr a₀ s₀ z₀
    lr₀ = lr-row (lz₀ , world-after (InvAt.world I₀ lz₀) (InvAt.real I₀ lz₀))
                 (λ ae _ → loud tt (subst Silent (InvAt.func I₀ lz₀ (proj₁ ae)) (Truth.silent tr ct (0 , cz₀) lz₀)))

    -- A later lane: apart, or under the cut's lane's end, which lies past the spin.
    off-a : ∀ {i q s₁ a y k} → i₀ < i → Sub i q s₁ a → W H s₁ y → Real y → c ⊑ y → y ≺ (c ⊕ [ ix k ]) → ⊥
    off-a {y = y} {k} lt sb yW yR cy yk with BI.rel lt sb₀ sb
    ... | apart xr₀ xr ne rw₀ rw = BI.apart-lead xr₀ xr ne (nest⁼ rw₀ c⁼) (nest rw yW) cy
    ... | queued-in {c₀} ac₀ _ v = leads (proj₂ ok) (nest-in (BI.s-w sb₀) c⁼) nW nS (inW (nest v yW)) cy
      where
        nW : W⁼ H (c₀ ⊕ [ ix 1 ]) c → ⊥
        nW w = BI.nest-back sb₀ ac₀ w lr₀ (⊑-trans (⊑-snoc⁺ c) cz₀)

        nS : c ⊑ (c₀ ⊕ [ ix 1 ]) → ⊥
        nS l with ⊑-snoc c₀ l
        ... | inj₂ eq = flat-under I₀ (proj₁ ac₀) lz₀ (subst (_⊑ z₀) eq (⊑-trans (⊑-snoc⁺ c) cz₀))
        ... | inj₁ cc₀ with under-c c cc₀
        ...   | inj₁ refl       = flat-under I₀ (proj₁ ac₀) lz₀ cz₀
        ...   | inj₂ (inj₁ sp)  = loud tt (Truth.silent tr ct sp (proj₁ ac₀))
        ...   | inj₂ (inj₂ far) =
          ≺-irrefl {y} (≺-trans {y} {c ⊕ [ ix k ]} {y} yk (≺-trans {c ⊕ [ ix k ]} {c₀} {y} (far k)
            (≺-trans {c₀} {c₀ ⊕ [ ix 1 ]} {y} (≺-ext c₀ {ix 1} []) (world-after (nest v yW) yR))))

    -- An earlier lane: apart, or ending where the cut's lane is queued.
    off-b : ∀ {i q s₁ a y} → i < i₀ → Sub i q s₁ a → Lr a s₁ y → c ⊑ y → ⊥
    off-b lt sb ly cy with BI.rel lt sb sb₀
    ... | apart xr xr₀ ne rw rw₀ = BI.apart-lead xr₀ xr (λ eq → ne (sym eq)) (nest⁼ rw₀ c⁼) (nest rw (BI.lr-w sb ly)) cy
    ... | queued-in ac _ v      = BI.nest-back sb ac (nest⁼ v c⁼) ly cy

    off : ∀ {i q s₁ a y k} → Sub i q s₁ a → (i ≡ i₀ → ⊥) → Lr a s₁ y → c ⊑ y → y ≺ (c ⊕ [ ix k ]) → ⊥
    off {i} sb ne ly cy yk with <-cmp i i₀
    ... | tri< lt _ _ = off-b lt sb ly cy
    ... | tri≈ _ eq _ = ne eq
    ... | tri> _ _ gt = off-a gt sb (BI.lr-w sb ly) (BI.lr-real sb ly) cy yk

  mk-lanes : ∀ {b} → (∀ {q a s₁ k} → o q (out a) → J.Sl q a s₁ → Indexed q → k ≼ b → ¬ ⊥ → AgreeTo k (enter (f a) s₁) (enter (f′ a) s₁))
           → (∀ {q a s₁ k r} → o q (out a) → J.Sl q a s₁ → Indexed q → k ≼ b → ¬ ⊥ → T (inside r k)
              → (enter (f a) s₁ k (pin r) → enter (f′ a) s₁ k (pin r)) × (enter (f′ a) s₁ k (pin r) → enter (f a) s₁ k (pin r)))
           → Lanes b
  mk-lanes {b} la _ = LJ.Join.BoundedJ.lanes (λ {i} {_} {_} {a} sb _ → la (nth-val (proj₁ sb)) (i , sb) (i , a , proj₁ sb) (≼-refl {b}) (λ ()))

  sl-to : ∀ Q → AgreeTo Q o o′ → Lanes Q → ∀ {q a s₁} → s₁ ≼ Q → J.Sl q a s₁ → J′.Sl q a s₁
  sl-to Q ag L {s₁ = s₁} s₁Q (i , sb) = i , LJ.Join.BoundedJ.sub-to {A} {B} Q n ag L (LJ.Join.BoundedJ.stem-≼ {A} {B} Q n s₁ s₁Q) sb

  sl-from : ∀ Q → AgreeTo Q o o′ → Lanes Q → ∀ {q a s₁} → s₁ ≼ Q → J′.Sl q a s₁ → J.Sl q a s₁
  sl-from Q ag L {s₁ = s₁} s₁Q (i , sb) = i , LJ.Join.BoundedJ.sub-from {A} {B} Q n ag L (LJ.Join.BoundedJ.stem-≼ {A} {B} Q n s₁ s₁Q) sb

  -- Under a lane's cut's spin, a lane row is that lane's.
  in-lane : ∀ {q₀ a₀ s₀ c y e q a} {X : EmissionSet B} → o q₀ (out a₀) → J.Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
          → W⁼ H s₀ c → Truth.Cut tr c → Spun c y → o q (out a) → Lane q a y e → enter (f a₀) s₀ y e
  in-lane {c = c} {y} _ (i₀ , sb₀) tr c⁼ ct (_ , cy) _ (i , _ , sb , ly) with i ≟ i₀
  ... | yes refl with BI.sub-fun sb sb₀
  ...   | refl , refl , refl = proj₁ ly
  in-lane {c = c} {y} _ (i₀ , sb₀) tr c⁼ ct (_ , cy) _ (i , _ , sb , ly) | no ne =
    ⊥-elim (lr-any ly (λ l → Off.off sb₀ tr c⁼ ct sb ne l (⊑-trans (⊑-snoc⁺ c) cy) (below-next c cy ≤-refl))
                      (λ l → Off.off sb₀ tr c⁼ ct sb ne l (⊑-trans (⊑-snoc⁺ c) (⊑-trans cy (⊑-snoc⁺ y)))
                                     (below-next c (⊑-trans cy (⊑-snoc⁺ y)) ≤-refl)))

  -- No lane row at a lane's cut.
  at-lane : ∀ {q₀ a₀ s₀ c e q a} {X : EmissionSet B} → o q₀ (out a₀) → J.Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
          → W⁼ H s₀ c → Truth.Cut tr c → o q (out a) → Lane q a c e → ⊥
  at-lane {c = c} _ (i₀ , sb₀) tr c⁼ ct _ (i , _ , sb , ly) with i ≟ i₀
  ... | yes refl with BI.sub-fun sb sb₀ | Truth.shows tr ct 0
  ...   | refl , refl , refl | _ , _ , cz , lz = flat-under (BI.LI sb₀) (proj₁ ly) lz cz
  at-lane {c = c} _ (i₀ , sb₀) tr c⁼ ct _ (i , _ , sb , ly) | no ne =
    lr-any ly (λ l → Off.off sb₀ tr c⁼ ct sb ne l (⊑-refl c) (≺-ext c {ix 0} []))
              (λ l → Off.off sb₀ tr c⁼ ct sb ne l (⊑-snoc⁺ c) (below-next c (⊑-refl (c ⊕ [ ix 0 ])) ≤-refl))

  -- No hand-off at a lane's cut.
  at-hand : ∀ {q₀ a₀ s₀ c q a} {X : EmissionSet B} → o q₀ (out a₀) → J.Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
          → W⁼ H s₀ (c ⊕ [ ix 0 ]) → Truth.Cut tr (c ⊕ [ ix 0 ]) → o q (out a) → Lane q a c end → Queued c → ⊥
  at-hand {c = c} _ (i₀ , sb₀) tr c⁼ ct _ (i , _ , sb , ly) h with i ≟ i₀
  ... | yes refl with BI.sub-fun sb sb₀ | Truth.shows tr ct 0
  ...   | refl , refl , refl | _ , _ , cz , lz = flat-under (BI.LI sb₀) (proj₁ ly) lz (⊑-trans (⊑-snoc⁺ (c ⊕ [ ix 0 ])) cz)
  at-hand {c = c} _ (i₀ , sb₀) tr c⁼ ct _ (i , _ , sb , ly) h | no ne =
    Off.off sb₀ tr c⁼ ct sb ne (lr-hand ly h refl) (⊑-refl (c ⊕ [ ix 0 ])) (≺-ext (c ⊕ [ ix 0 ]) {ix 0} [])

  -- The next's lane pinning past a lane's cut, its subscription read on this side.
  one-at : ∀ {i₀ q₀ a₀ s₀ c w i q s₁ a r} {X : EmissionSet B} → Sub i₀ q₀ s₀ a₀ → (tr : Truth (enter (f a₀) s₀) X)
         → W⁼ H s₀ c → Truth.Cut tr c → Lies c w
         → (∀ {q₂ a₂ s₂ c₂} → o q₂ (out a₂) → J.Sl q₂ a₂ s₂ → Indexed q₂ → After (f a₂) s₂ c₂ end → c₂ ≺ s₀ → ¬ ⊥ → enter (f′ a₂) s₂ c₂ end)
         → Sub i q s₁ a → enter (f′ a) s₁ w (pin r) → enter (f′ a₀) s₀ w (pin r)
  one-at {i₀ = i₀} {c = c} {i = i} {a = a} sb₀ tr c⁼ ct li ends sb lw with <-cmp i i₀
  ... | tri≈ _ refl _ with BI.sub-fun sb sb₀
  ...   | refl , refl , refl = lw
  one-at {i₀ = i₀} {c = c} {i = i} {a = a} sb₀ tr c⁼ ct li ends sb lw | tri> _ _ gt =
    ⊥-elim (Off.off-a sb₀ tr c⁼ ct gt sb (InvAt.world (I′ sb) lw) (InvAt.real (I′ sb) lw) (lies-⊑ li) (below-next c (proj₂ li) ≤-refl))
  one-at {i₀ = i₀} {c = c} {i = i} {a = a} sb₀ tr c⁼ ct li ends sb lw | tri< lt _ _ with BI.rel lt sb sb₀
  ... | apart xr xr₀ ne rw rw₀ =
    ⊥-elim (BI.apart-lead xr₀ xr (λ eq → ne (sym eq)) (nest⁼ rw₀ c⁼) (nest rw (InvAt.world (I′ sb) lw)) (lies-⊑ li))
  ... | queued-in ac _ v =
    ⊥-elim (InvAt.under (I′ sb) (ends (nth-val (proj₁ sb)) (i , sb) (i , a , proj₁ sb) ac (end-before (proj₁ (BI.okS sb₀)) v) (λ ()))
                        lw plain-ix (nest⁼ v c⁼) (lies-⊑ li))

  one-lane : ∀ {q₀ a₀ s₀ c w r q a} {X : EmissionSet B} → o q₀ (out a₀) → J.Sl q₀ a₀ s₀ → (tr : Truth (enter (f a₀) s₀) X)
           → W⁼ H s₀ c → Truth.Cut tr c → Lies c w → r ⊑ c → AgreeTo q₀ o o′ → AgreeTo r o o′ → Lanes r
           → (∀ {q₂ a₂ s₂ c₂} → o q₂ (out a₂) → J.Sl q₂ a₂ s₂ → Indexed q₂ → After (f a₂) s₂ c₂ end → c₂ ≺ s₀ → ¬ ⊥ → enter (f′ a₂) s₂ c₂ end)
           → o′ q (out a) → Bounded.Lane n f′ o′ q a w (pin r) → enter (f′ a₀) s₀ w (pin r)
  one-lane {r = r} _ (_ , sb₀) tr c⁼ ct li _ _ agr L ends _ (_ , s₁ , sb′ , lw′) =
    one-at sb₀ tr c⁼ ct li ends
      (LJ.Join.BoundedJ.sub-from {A} {B} r n agr L (LJ.Join.BoundedJ.stem-≼ {A} {B} r n s₁ (pinned-after (J′.BI.LI sb′) (proj₁ lw′))) sb′) (proj₁ lw′)

  module P = C.Policy Lanes mk-lanes sl-to sl-from in-lane at-lane at-hand one-lane

bounded-truth : ∀ {A B H} n {f f′ : A → Den B} {s s′ : Den A}
              → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
              → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
              → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap (mergeᶠ (just n)) f s) (Op.flatMap (mergeᶠ (just n)) f′ s′)
bounded-truth {A} {B} {H} n {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Bnds.P.placed {A} {B} {H} n {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok
    (k-shows (λ m → SJ.Flat.Bnd.sk-bounded {A} {B} {H} {m} s f Is If p ok (sk-o m p ok) (λ a q okq → sk-f m a q okq) n))
    (λ ()) (λ ()) (λ ())
    (λ Q → LJ.Join.BoundedJ.BP.agree {A} {B} Q n)
    (λ Q ao _ q qQ (i , a , N) → i , a , LJ.Join.BoundedJ.nth-to {A} {B} Q n ao qQ N)
    (λ Q ao _ q qQ (i , a , N) → i , a , LJ.Join.BoundedJ.nth-to {A} {B} Q n (AgreeTo-sym ao) qQ N)
    (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())
