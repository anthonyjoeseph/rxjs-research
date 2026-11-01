-- TWO LANES' REGIONS MEET ONLY AT ONE VALUE'S.  A plain lane subscribes
-- at its value's second child, and two values' children's worlds are
-- apart (`Kids.kids`).  A bounded merge's lanes, taken in schedule order,
-- lie under distinct roots, or the later under the second child of an end
-- of the earlier (`BoundedI.rel`): past that end, so past the earlier's
-- cap.
module adequacy.Regions where

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; [_]; _++_)
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-cmp)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; out; Den)
open import denotation.Laws.Modulus using (≺-ext; ≺-≼-≺)
open import denotation.Laws.Worlds using (W⁼; here; inW; nest-in; plain-ix; world-after⁼; Ok; InvAt; InvD)
open import denotation.Laws.JoinInv using (module Kids)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import adequacy.Cursor using (LaneRg; polF)

-- Worlds nest.
w-trans : ∀ {H a b c} → W⁼ H a b → W⁼ H b c → W⁼ H a c
w-trans here    w = w
w-trans (inW v) w = inW (nest-in v w)

module _ {A B : Set} {H : Pos → Set} {at : Pos} (ok : Ok H at) (F : A → Den B) (fi : ∀ a → InvD H (F a))
         {O : EmissionSet A} (io : InvAt H at O) where

  plain : ∀ {q q′ a a′ y} → O q (out a) → O q′ (out a′) → W⁼ H (q ++ [ ix 1 ]) y → W⁼ H (q′ ++ [ ix 1 ]) y → q ≡ q′
  plain {q} {q′} x x′ w w′ with q ≟ᵖ q′
  ... | yes eq = eq
  ... | no ne  = ⊥-elim (Kids.kids ok io x x′ plain-ix plain-ix (λ eq → ne (∷ʳ-injectiveˡ q q′ eq)) w w′)

  module _ (m : ℕ) where
    open BoundedI ok m F fi io

    bounded : ∀ {q q′ y} → LaneRg H (polF (mergeᶠ (just m)) F O) O q y → LaneRg H (polF (mergeᶠ (just m)) F O) O q′ y → q ≡ q′
    bounded (ry , a , s , x , (i , sb) , w , cap) (_ , a′ , s′ , x′ , (i′ , sb′) , w′ , cap′) with <-cmp i i′
    ... | tri≈ _ refl _ = proj₁ (sub-fun sb sb′)
    ... | tri< lt _ _ with rel lt sb sb′
    ...   | apart xr xr′ ne wr wr′ = ⊥-elim (apart-ww xr xr′ ne (w-trans wr w) (w-trans wr′ w′))
    ...   | queued-in {c} ac _ wc  = ⊥-elim (cap (i , s , sb , ac) (≺-≼-≺ {c} (≺-ext c []) (world-after⁼ (w-trans wc w′) ry)))
    bounded (ry , a , s , x , (i , sb) , w , cap) (_ , a′ , s′ , x′ , (i′ , sb′) , w′ , cap′) | tri> _ _ gt with rel gt sb′ sb
    ...   | apart xr xr′ ne wr wr′ = ⊥-elim (apart-ww xr xr′ ne (w-trans wr w′) (w-trans wr′ w))
    ...   | queued-in {c} ac _ wc  = ⊥-elim (cap′ (i′ , s′ , sb′ , ac) (≺-≼-≺ {c} (≺-ext c []) (world-after⁼ (w-trans wc w) ry)))

  -- One lane to a position of a joiner's lane regions.
  lane-sole : ∀ op {q q′ y} → LaneRg H (polF op F O) O q y → LaneRg H (polF op F O) O q′ y → q ≡ q′
  lane-sole (mergeᶠ nothing)  (_ , _ , _ , x , refl , w , _) (_ , _ , _ , x′ , refl , w′ , _) = plain x x′ w w′
  lane-sole (mergeᶠ (just m)) r r′ = bounded m r r′
  lane-sole switchᶠ           (_ , _ , _ , x , refl , w , _) (_ , _ , _ , x′ , refl , w′ , _) = plain x x′ w w′
  lane-sole exhaustᶠ          (_ , _ , _ , x , refl , w , _) (_ , _ , _ , x′ , refl , w′ , _) = plain x x′ w w′
