{-# OPTIONS --guardedness #-}

-- `fin-shut` refuted: a live joiner joined at the finish's own position.
-- The shut tells it at once, past its subscription; the retag tells it
-- under the finish.  A gap keeps every joiner's end, so no gap relates
-- the two.
module adequacy.RefuteFinShut where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴸ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import denotation.MonotonicList.Events using (Pos; Timeline; last) renaming (sub to subᴾ)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run; base; gate; joins; maybe; quiet) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Gapped using (module Gapping)
open import adequacy.Climbs.Connect using (module ClimbConnect)

open Shared Timeline (Out ⊤) using (Heapᴹ; stored)
open Heap using (World; slot; cell) renaming (same to same⊑)
open Run (Pureᴾ ⊤) using (done)
open Strongly ⊤ using (Sub; joinˢ; doneˢ; connectˢ; here; idle)
open Gapping ⊤ using (Gapped; alike; gap-map; gap-scan; gap-take; gap-flat; gap-late; gap-join; gap-connect; gap-shut; gap-defer; gap-ending; gap-rest; gap-union; gap-bursting; gap-under)

-- A top-level joiner's variable, position and end.
endOf : ∀ {Γ A} → U.Node Γ A → Maybe (A ∈ Γ × Pos × Maybe Pos)
endOf (U.joinᶜ j p xs e) = just (j , p , e)
endOf _                  = nothing

shut-end : ∀ {Γ C A} (i : C ∈ Γ) c (b : U.Node Γ A)
         → endOf (U.shut i c b) ≡ mapᴹ (λ { (j , p , e) → j , p , U.told i c j p e (U.same? i j) }) (endOf b)
shut-end i c (U.framesᶜ _ _ _)         = refl
shut-end i c (U.burstᶜ _ _ _ _)        = refl
shut-end i c (U.ofᶜ _ _ _)             = refl
shut-end i c (U.mapᶜ _ _)              = refl
shut-end i c (U.scanᶜ _ _ _)           = refl
shut-end i c (U.takeWhileᶜ _ _ _)      = refl
shut-end i c (U.flatMapᶜ _ _ _ _ _ _)  = refl
shut-end i c (U.joinᶜ _ _ _ _)         = refl
shut-end i c (U.connectᶜ _ _ _)        = refl
shut-end i c (U.deferᶜ _ _ _)          = refl
shut-end i c (U.endingᶜ _ _)           = refl
shut-end i c (U.restᶜ _)               = refl
shut-end i c U.idleᶜ                   = refl
shut-end i c (U.unionᶜ _ _)            = refl
shut-end i c (U.burstingᶜ _ _)         = refl
shut-end i c (U.underᶜ _ _)            = refl

-- A gap keeps a top-level joiner's end.
gapped-end : ∀ {κ Γ A} {x y : U.Node Γ A} → Gapped κ x y → endOf x ≡ endOf y
gapped-end alike                    = refl
gapped-end (gap-map _)              = refl
gapped-end (gap-scan _)             = refl
gapped-end (gap-take _)             = refl
gapped-end (gap-flat _ _ _ _)       = refl
gapped-end (gap-late _ _ _ _ _ _)   = refl
gapped-end (gap-join _)             = refl
gapped-end (gap-connect _ _)        = refl
gapped-end (gap-shut {i = i} {c} {b} {b′} g) =
  trans (shut-end i c b) (trans (cong (mapᴹ _) (gapped-end g)) (sym (shut-end i c b′)))
gapped-end (gap-defer _)            = refl
gapped-end (gap-ending _)           = refl
gapped-end (gap-rest _)             = refl
gapped-end (gap-union _ _)          = refl
gapped-end (gap-bursting _)         = refl
gapped-end (gap-under _ _)          = refl

-- The joiner's gate, the subject's closed flag and subscribers, the
-- joiner's sink, a cut.
w : World
w = cell gate ∷ cell (base Bool) ∷ cell (joins ⊤) ∷ slot ⊤ ∷ cell (base Bool) ∷ cell (maybe quiet) ∷ []

H : Heapᴹ w
H = stored (lift true) same⊑ ∷ᴬ stored (lift false) same⊑ ∷ᴬ stored (lift []) same⊑
  ∷ᴬ stored (record { onNext = λ _ → done tt ; onComplete = done tt ; isClosed = done false }) same⊑
  ∷ᴬ stored (lift true) same⊑ ∷ᴬ stored (lift nothing) same⊑ ∷ᴬ []ᴬ

q : Pos
q = []

bd : Sub w (⊤ ∷ []) ⊤
bd = joinˢ q (Heap.there (Heap.there (Heap.there Heap.here))) Heap.here (hereᴸ refl) (just ([] , nothing))

module F = ClimbConnect.Fins ⊤ H
  {Sj = record { subscribers = Heap.there (Heap.there Heap.here) ; closed = Heap.there Heap.here }}
  {c = Heap.there (Heap.there (Heap.there (Heap.there Heap.here))) , Heap.there (Heap.there (Heap.there (Heap.there (Heap.there Heap.here))))}
  {b = Heap.there (Heap.there (Heap.there (Heap.there (Heap.there Heap.here))))} {kb = nothing} {k = nothing}
  {rp = q} {e = nothing} {rt = U.idleᶜ} {u = doneˢ} {bd = bd} here q

refuted : ⊥
refuted with F.fin-shut refl
... | _ , refl , gp with gapped-end gp
... | ()
