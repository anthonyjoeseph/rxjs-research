{-# OPTIONS --guardedness #-}

-- `re-leftover` refuted: the body a connect whose source is a joiner of
-- the fed connect.  The retag feeds the joiner; the nested connect's
-- leftover bursts its source's part, so the two leftovers differ.
module adequacy.RefuteReLeftover where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴸ)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList.Events using (Timeline)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run; base; gate; joins; maybe; quiet) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Climbs.Connect using (module ClimbConnect)

open Shared Timeline (Out ⊤) using (Heapᴹ; stored)
open Heap using (World; slot; cell) renaming (same to same⊑)
open Run (Pureᴾ ⊤) using (done)
open Strongly ⊤ using (Sub; joinˢ; doneˢ; connectˢ; idle; feeding)

-- The joiner's gate, a subject's closed flag and subscribers, the
-- joiner's sink, a cut.
w : World
w = cell gate ∷ cell (base Bool) ∷ cell (joins ⊤) ∷ slot ⊤ ∷ cell (base Bool) ∷ cell (maybe quiet) ∷ []

H : Heapᴹ w
H = stored (lift true) same⊑ ∷ᴬ stored (lift false) same⊑ ∷ᴬ stored (lift []) same⊑
  ∷ᴬ stored (record { onNext = λ _ → done tt ; onComplete = done tt ; isClosed = done false }) same⊑
  ∷ᴬ stored (lift true) same⊑ ∷ᴬ stored (lift nothing) same⊑ ∷ᴬ []ᴬ

-- The nested connect's source: a live joiner of the fed connect.
bd : Sub w (⊤ ∷ []) ⊤
bd = connectˢ (record { subscribers = Heap.there (Heap.there Heap.here) ; closed = Heap.there Heap.here })
       (Heap.there (Heap.there (Heap.there (Heap.there Heap.here))) , Heap.there (Heap.there (Heap.there (Heap.there (Heap.there Heap.here)))))
       (Heap.there (Heap.there (Heap.there (Heap.there (Heap.there Heap.here))))) nothing nothing idle [] nothing U.idleᶜ
       (joinˢ [] (Heap.there (Heap.there (Heap.there Heap.here))) Heap.here (hereᴸ refl) (just ([] , nothing)))
       doneˢ

module R = ClimbConnect.Refed ⊤ H
  {Sj = record { subscribers = Heap.there (Heap.there Heap.here) ; closed = Heap.there Heap.here }}
  {c = Heap.there (Heap.there (Heap.there (Heap.there Heap.here))) , Heap.there (Heap.there (Heap.there (Heap.there (Heap.there Heap.here))))}
  {b = Heap.there (Heap.there (Heap.there (Heap.there (Heap.there Heap.here))))} {kb = nothing} {k = nothing}
  {rp = []} {e = nothing} {rt = U.idleᶜ} {u = doneˢ} {bd = bd} (feeding tt [] []) []

refuted : ⊥
refuted with R.re-leftover
... | ()
