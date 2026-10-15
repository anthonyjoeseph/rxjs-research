{-# OPTIONS --guardedness --large-indices #-}

-- `walk-tree` refuted.  A `rest` frame is well only from a last delivery
-- no later than its position, while a callback run before it may leave
-- the last anywhere under that position, and `retʷ` says nothing of
-- where it is.  Returning into a frame whose first act delivers is then
-- not well.
module adequacy.RefuteWalk where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList using (ix; root; Timeline)
open import operation.AbstractObservable using (module Run; module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; fin)
open import operation.Machine using (module Machine)
open import adequacy.Sorted using (module Sorting)
open Heap using (same)

open Run (Pureᴾ ⊤) using (Act; done; eff)
open Shared Timeline (Out ⊤) using (⟨_,_,_⟩; ret; push; rest; bottom)
open Machine ⊤ using (Mach; mach)
open Sorting ⊤ using (WellMach; StepBy; WellRun; silentʷ; finʷ; runʷ; retʷ; restʷ; bottomʷ; walk-tree)

-- Deliver the root's completion.
ending : Act [] ⊤
ending = eff fin λ _ → done tt

-- Returned at the root, the last delivery left under it, `ending` next.
stuck : Mach
stuck = mach ⟨ [] , root , ret tt same (push (rest ending) same bottom) ⟩ 0 [] [] [] [] false []

stuck-well : WellMach (ix 0 ∷ ix 0 ∷ []) stuck
stuck-well = record
  { going = record { ctl = retʷ (restʷ (λ lo le → finʷ le) bottomʷ) ; heap = (λ ()) , (λ ()) ; bursts = [] }
  ; queue = record { timers = [] ; queued = [] } }

refuted : ⊥
refuted with walk-tree stuck-well refl
... | silentʷ r with WellRun.ctl r
...   | runʷ (finʷ (inj₁ ())) _
...   | runʷ (finʷ (inj₂ ())) _
