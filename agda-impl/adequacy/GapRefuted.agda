{-# OPTIONS --guardedness #-}

-- `gapped-past` REFUTED: a connect over `of [ tt ]` whose body is a burst
-- at `[ ix 1 ]` of a joiner at `[ ix 1 ]`, the stepped side's joiner
-- holding one more skip, at `[ ix 0 ]`, outside the burst.  That skip
-- ends the burst before it starts; the part's burst pins the source's
-- value, rejoined just past `[ ix 1 ]`.  The stepped side reads two skips
-- to its silence, the part three: Placed and Sane, and not Fewer.
module adequacy.GapRefuted where

open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList using (Pos; ix)
import denotation.Unfold as U
open import operation.Placed using (skipᵃ; hushᵃ)
open import adequacy.Sane using (Sane)
open import adequacy.Placed using (Placed; ordered)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Gapped using (module Gapping)

open Ghosting ⊤ using (Past; residual)
open Gapping ⊤ using (Gapped; gap-connect; gap-bursting; gap-join; gap-live; alike; dropᵗ; []ᵗ)

src : U.Node [] ⊤
src = U.ofᶜ (ix 0 ∷ []) 0 (tt ∷ [])

body : List (Pos × Maybe ⊤) → U.Node (⊤ ∷ []) ⊤
body xs = U.burstingᶜ (ix 1 ∷ []) (U.joinᶜ (here refl) (ix 1 ∷ []) xs nothing)

stepped part : U.Node [] ⊤
stepped = U.connectᶜ (ix 2 ∷ []) (body ((ix 0 ∷ [] , nothing) ∷ [])) (U.live src)
part    = U.connectᶜ (ix 2 ∷ []) (body []) (U.live src)

gapped : Gapped [] stepped part
gapped = gap-connect (gap-bursting (gap-join (dropᵗ []ᵗ))) (gap-live alike)

sane : Sane []ᴬ stepped
sane = tt , tt

placed : Placed stepped []ᴬ
placed = record { ordered = refl , record { ordered = tt , record { ordered = tt } } }
       , (record { ordered = tt } , tt)
       , (record { ordered = refl , record { ordered = tt } } , tt)

refuted : ¬ (∀ {κ} {g′ g″ : U.Node [] ⊤} → Gapped κ g′ g″ → Sane []ᴬ g′ → Placed g′ []ᴬ → Past (residual g′) (residual g″))
refuted gp-past with Past.fewer (gp-past gapped sane placed) (skipᵃ (skipᵃ hushᵃ))
... | skipᵃ (skipᵃ (skipᵃ hushᵃ)) , s≤s (s≤s ())
