{-# OPTIONS --guardedness #-}

-- THE READER'S SENDING: the fold of `joinStep` over its reading, each
-- fold's emits sent on a lane under the row folded in.  A fold's emits
-- are the emit it folds in, past the routes a reader joining late sends
-- first, so the sending carries what the reading carries.
module simultaneous.CarryRead where

open import Data.Bool using (true)
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; proj₂)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; enter; module Op)
open import denotation.Laws.Worlds using (InvAt)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Carry using (PMap; CarryAt; annValues)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; joinStep)

-- The elaborated reader's run over a handle: the fold of `joinStep`,
-- each fold's emits sent.
Reading : ∀ {X} → Den (AIE X) → Den (IE X)
Reading d = Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan joinStep (true , []) d)

postulate
  read-post : ∀ {X : Set} {M : PMap} {HP HE LP H : Pos → Set} {t : EmissionSet X} {d′ : Den (AIE X)} {s s′}
            → InvAt H s′ (enter d′ s′) → CarryAt annValues M HP HE LP t (enter d′ s′) s s′
            → CarryAt valuesOf M HP HE LP t (enter (Reading d′) s′) s s′

