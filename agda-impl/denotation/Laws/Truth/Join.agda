{-# OPTIONS --guardedness #-}

-- THE JOINERS KEEP THE TRUTH: merge, switch and exhaust are joinings
-- (`denotation.Laws.Truth.Joining`) whose lanes sit at their values'
-- second children.  A lane row under a lane's world is that lane's
-- (`same`), so no other lane reaches under a lane's cut, a lane of the
-- next that pins past it is the same lane, and no lane hands off.
module denotation.Laws.Truth.Join where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_])
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; _⊕_; inside; _≟ᵖ_)
open import denotation.EmissionSet using (out; end; pin; EmissionSet; Den; enter; After; LaneOf; _≺_; _≼_; module Switch; module Exhaust;
  module Op)
open import denotation.Laws.Modulus using (AgreeTo; upto; AgreeTo-sym; ≼-refl; ≼-or-≻; ≺-ext)
open import denotation.Laws.Shows using (ShowsK; k-shows)
open import denotation.Laws.Worlds using (W⁼; here; Ok; InvAt; InvD; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc⁺; conv; plain-ix; ok-step; ok-in;
  inside-⊑; ⊕-injˡ; flat-under)
open import denotation.Laws.Worlds.Leaves using (out-inj)
import denotation.Laws.JoinInv as JI
open import denotation.Laws.JoinInv using (switch-cut-up)
import denotation.Laws.Join as LJ
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.Truth using (Truth; Rel; Spun; Lies)
open import denotation.Laws.Truth.Joining using (Slots; module Core; lies-⊑)

-- A switch's cut, past a subtree no value lies under, falls before it.
switch-cut-in : ∀ {A B : Set} (f : A → Den B) (o : EmissionSet A) {q z w} → Switch.Cut f o q z → w ⊑ z
              → (∀ {y e} → o y e → w ⊑ y → ⊥) → Switch.Cut f o q w
switch-cut-in f o {w = w} (q′ , a′ , x , qq′ , q′z) wz nv with ≼-or-≻ w q′
... | inj₂ q′w = q′ , a′ , x , qq′ , q′w
... | inj₁ wq′ = ⊥-elim (nv x (conv {w} {w} {q′} (⊑-refl w) wq′ q′z wz))

-- A joiner's lanes, each at its value's second child.
module JoinerSide {A B : Set} {H : Pos → Set} {p : Pos} (ok : Ok H p) (g : A → Den B) (Ig : ∀ a → InvD H (g a))
                  {u : EmissionSet A} (Iu : InvAt H p u) where
  module JU = JI.Join ok g Ig Iu

  -- A lane row under a lane's world is that lane's.
  same : ∀ {q₀ a₀ q a w y e} → u q₀ (out a₀) → W⁼ H (q₀ ⊕ [ ix 1 ]) w → u q (out a) → LaneOf g q a y e → w ⊑ y
       → enter (g a₀) (q₀ ⊕ [ ix 1 ]) y e
  same {q₀} {q = q} x₀ w⁼ x l le with q ≟ᵖ q₀
  ... | no ne = ⊥-elim (JU.kid-lane x₀ plain-ix w⁼ x (JU.lw x l) (λ eq → ne (sym (⊕-injˡ q₀ q eq))) le)
  ... | yes refl with out-inj (InvAt.func Iu x x₀)
  ...   | refl = proj₁ l

  Sl : Pos → A → Pos → Set
  Sl q _ s = s ≡ q ⊕ [ ix 1 ]

  mk : ∀ {q a s k e} → Sl q a s → After (g a) s k e → LaneOf g q a k e
  mk refl l = l

  okS : ∀ {q a s} → u q (out a) → Sl q a s → Ok H s
  okS {q} x refl = ok-step q (ok-in ok (InvAt.world Iu x) (InvAt.real Iu x))

  past : ∀ {q a s} → Sl q a s → q ≺ s
  past {q} refl = ≺-ext q {ix 1} []

  meet : ∀ {q₀ a₀ s₀ z q a k r} → u q₀ (out a₀) → Sl q₀ a₀ s₀ → enter (g a₀) s₀ z (pin r) → u q (out a) → LaneOf g q a k (pin r)
       → enter (g a₀) s₀ k (pin r)
  meet {k = k} {r} x₀ refl lz x l = same x₀ (proj₁ (InvAt.pinned (JU.LI x₀) lz)) x l (inside-⊑ r k (proj₂ (InvAt.pinned (JU.LI x) (proj₁ l))))

  slots : Slots H g u (LaneOf g)
  slots = record
    { Sl   = Sl
    ; slot = λ l → _ , refl , l
    ; mk   = mk
    ; okS  = okS
    ; past = λ {q} {a} {s} → past {q} {a} {s}
    ; seat = λ { {q} {a} x refl → q , a , x , ≼-refl {q} , here }
    ; meet = meet
    }

-- The joiners: lanes at their values, none handing off.
module Joiners {A B : Set} {H : Pos → Set} {f f′ : A → Den B} {s s′ : Den A}
               (Is : InvD H s) (Is′ : InvD H s′) (If : ∀ a → InvD H (f a)) (If′ : ∀ a → InvD H (f′ a))
               (R : Rel H s s′) (Rf : ∀ a → Rel H (f a) (f′ a)) (p : Pos) (ok : Ok H p)
               (Runs : (A → Den B) → EmissionSet A → Pos → Set) (Cut : (A → Den B) → EmissionSet A → Pos → Pos → Set) where
  o o′ : EmissionSet A
  o  = enter s p
  o′ = enter s′ p

  module J  = JoinerSide ok f If (Is p ok)
  module J′ = JoinerSide ok f′ If′ (Is′ p ok)
  module C  = Core {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ g _ → LaneOf g) Runs Cut (λ _ _ _ → ⊥) J.slots J′.slots

  Lanes : Pos → Set
  Lanes Q = LJ.Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′

  mk-lanes : ∀ {b} → (∀ {q a s₁ k} → o q (out a) → s₁ ≡ q ⊕ [ ix 1 ] → Runs f o q → k ≼ b → ¬ Cut f o q k
                       → AgreeTo k (enter (f a) s₁) (enter (f′ a) s₁))
           → (∀ {q a s₁ k r} → o q (out a) → s₁ ≡ q ⊕ [ ix 1 ] → Runs f o q → k ≼ b → ¬ Cut f o q r → T (inside r k)
              → (enter (f a) s₁ k (pin r) → enter (f′ a) s₁ k (pin r)) × (enter (f′ a) s₁ k (pin r) → enter (f a) s₁ k (pin r)))
           → Lanes b
  mk-lanes la lf = LJ.Join.JoinerJ.lanes (λ x rn _ kQ nc → la x refl rn kQ nc) (λ x rn _ kQ nr i → lf x refl rn kQ nr i)

  -- Under a lane's cut's spin, a lane row is that lane's.
  in-lane : ∀ {q₀ a₀ s₀ c y e q a} {X : EmissionSet B} → o q₀ (out a₀) → s₀ ≡ q₀ ⊕ [ ix 1 ] → (tr : Truth (enter (f a₀) s₀) X)
          → W⁼ H s₀ c → Truth.Cut tr c → Spun c y → o q (out a) → LaneOf f q a y e → enter (f a₀) s₀ y e
  in-lane {c = c} x₀ refl _ c⁼ _ (_ , cy) x l = J.same x₀ c⁼ x l (⊑-trans (⊑-snoc⁺ c) cy)

  -- No lane row at a lane's cut: it would be that lane's, under its spin.
  at-lane : ∀ {q₀ a₀ s₀ c e q a} {X : EmissionSet B} → o q₀ (out a₀) → s₀ ≡ q₀ ⊕ [ ix 1 ] → (tr : Truth (enter (f a₀) s₀) X)
          → W⁼ H s₀ c → Truth.Cut tr c → o q (out a) → LaneOf f q a c e → ⊥
  at-lane {c = c} x₀ refl tr c⁼ ct x l with Truth.shows tr ct 0
  ... | _ , _ , cz , lz = flat-under (J.JU.LI x₀) (J.same x₀ c⁼ x l (⊑-refl c)) lz cz

  at-hand : ∀ {q₀ a₀ s₀ c q a} {X : EmissionSet B} → o q₀ (out a₀) → s₀ ≡ q₀ ⊕ [ ix 1 ] → (tr : Truth (enter (f a₀) s₀) X)
          → W⁼ H s₀ (c ⊕ [ ix 0 ]) → Truth.Cut tr (c ⊕ [ ix 0 ]) → o q (out a) → LaneOf f q a c end → ⊥ → ⊥
  at-hand _ _ _ _ _ _ _ ()

  -- The next's lane pinning past a lane's cut is that lane.
  one-lane : ∀ {q₀ a₀ s₀ c w r q a} {X : EmissionSet B} → o q₀ (out a₀) → s₀ ≡ q₀ ⊕ [ ix 1 ] → (tr : Truth (enter (f a₀) s₀) X)
           → W⁼ H s₀ c → Truth.Cut tr c → Lies c w → r ⊑ c → AgreeTo q₀ o o′ → AgreeTo r o o′ → Lanes r
           → (∀ {q₂ a₂ s₂ c₂} → o q₂ (out a₂) → s₂ ≡ q₂ ⊕ [ ix 1 ] → Runs f o q₂ → After (f a₂) s₂ c₂ end → c₂ ≺ s₀ → ¬ Cut f o q₂ c₂
              → enter (f′ a₂) s₂ c₂ end)
           → o′ q (out a) → LaneOf f′ q a w (pin r) → enter (f′ a₀) s₀ w (pin r)
  one-lane {q₀} x₀ refl _ c⁼ _ li _ ag₀ _ _ _ x′ l′ = J′.same (proj₁ (upto ag₀ {q₀} (≼-refl {q₀})) x₀) c⁼ x′ l′ (lies-⊑ li)

  module P = C.Policy Lanes mk-lanes (λ _ _ _ _ sl → sl) (λ _ _ _ _ sl → sl) in-lane at-lane at-hand one-lane

------------------------------------------------------------------------
-- The joiners

merge-truth : ∀ {A B H} {f f′ : A → Den B} {s s′ : Den A}
            → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
            → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
            → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap (mergeᶠ nothing) f s) (Op.flatMap (mergeᶠ nothing) f′ s′)
merge-truth {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Joiners.P.placed {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ _ _ _ → ⊤) (λ _ _ _ _ → ⊥)
    (k-shows (λ n → SJ.Flat.sk-merge {A} {B} {H} {n} s f Is If p ok (sk-o n p ok) (λ a q okq → sk-f n a q okq)))
    (λ ()) (λ ()) (λ ())
    (λ Q → LJ.Join.MergeJ.agree {A} {B} Q) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())

switch-truth : ∀ {A B H} {f f′ : A → Den B} {s s′ : Den A}
             → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
             → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
             → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap switchᶠ f s) (Op.flatMap switchᶠ f′ s′)
switch-truth {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Joiners.P.placed {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ _ _ _ → ⊤) (λ g u → Switch.Cut g u)
    (k-shows (λ n → SJ.Flat.sk-switch {A} {B} {H} {n} s f Is If p ok (sk-o n p ok) (λ a q okq → sk-f n a q okq)))
    (λ {q} {k} {y} → switch-cut-up f (enter s p) {q} {k} {y}) (λ {q} {k} {y} → switch-cut-up f′ (enter s′ p) {q} {k} {y})
    (λ {q} {z} {w} → switch-cut-in f (enter s p) {q} {z} {w})
    (λ Q → LJ.Join.SwitchJ.agree {A} {B} Q) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt)
    (λ Q ao → LJ.Join.SwitchJ.cut-to {A} {B} Q {f} {f′} {enter s p} {enter s′ p} ao)
    (λ Q ao → LJ.Join.SwitchJ.cut-to {A} {B} Q {f′} {f} {enter s′ p} {enter s p} (AgreeTo-sym ao))

exhaust-truth : ∀ {A B H} {f f′ : A → Den B} {s s′ : Den A}
              → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
              → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
              → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap exhaustᶠ f s) (Op.flatMap exhaustᶠ f′ s′)
exhaust-truth {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ sk-o sk-f R Rf p ok =
  Joiners.P.placed {A} {B} {H} {f} {f′} {s} {s′} Is Is′ If If′ R Rf p ok (λ g u → Exhaust.Run g u) (λ _ _ _ _ → ⊥)
    (k-shows (λ n → SJ.Flat.sk-exhaust {A} {B} {H} {n} s f Is If p ok (sk-o n p ok) (λ a q okq → sk-f n a q okq)))
    (λ ()) (λ ()) (λ ())
    (λ Q → LJ.Join.ExhaustJ.agree {A} {B} Q) (λ Q → LJ.Join.ExhaustJ.runs-to {A} {B} Q)
    (λ Q ao L q qQ → LJ.Join.ExhaustJ.cur-from {A} {B} Q ao L q q qQ)
    (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())
