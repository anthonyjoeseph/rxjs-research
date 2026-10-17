{-# OPTIONS --guardedness --large-indices #-}

-- A TREE IN A GROWN WORLD.  An allocation moves no name the run already
-- holds, so the tree it leaves is the old one with every name weakened
-- along the growth; what the meaning keeps, the programs, positions and
-- ghosts, is world-free and stays as it was.
module adequacy.Grow where

open import Data.List using (List; []; _∷_) renaming (map to mapList)
open import Data.Maybe using () renaming (map to mapMaybe)
open import Data.Product using (_,_)
open import operation.AbstractObservable using (module Heap; module Run)
open import operation.PureObservable using (Pureᴾ)
open import adequacy.Strong using (module Strongly)

module Growing (R : Set) where
  open Heap using (_⊑_; wk∋)
  open Run (Pureᴾ R) using (wkR; wkSubject; module Kit; module FlatKit)
  open Kit using (wkCut)
  open FlatKit using (wkFlat)
  open Strongly R using (Sub; Lane; lane; Feed; idle; feeding; finishing; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ
                        ; connectˢ; joinˢ; deferˢ; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer
                        ; this-lane; next-lane)

  wkFeed : ∀ {A h v} → h ⊑ v → Feed A h → Feed A v
  wkFeed τ idle             = idle
  wkFeed τ (feeding a q ss) = feeding a q (mapList (λ { (s , j) → wk∋ τ s , j }) ss)
  wkFeed τ (finishing q ss) = finishing q (mapList (λ { (s , j) → wk∋ τ s , j }) ss)

  mutual
    wkTree : ∀ {h v Δ A} → h ⊑ v → Sub h Δ A → Sub v Δ A
    wkTree τ (pendingˢ s q)                      = pendingˢ s q
    wkTree τ (coldˢ s hd ph)                     = coldˢ (wk∋ τ s) (wk∋ τ hd) ph
    wkTree τ (ofˢ p i xs)                        = ofˢ p i xs
    wkTree τ doneˢ                               = doneˢ
    wkTree τ (mapˢ f t)                          = mapˢ f (wkTree τ t)
    wkTree τ (scanˢ f r t)                       = scanˢ f (wkR τ r) (wkTree τ t)
    wkTree τ (takeWhileˢ i p c k tk t)           = takeWhileˢ i p (wkCut τ c) (mapMaybe (wk∋ τ) k) tk (wkTree τ t)
    wkTree τ (flatMapˢ op f fl oc k r pl t ls)   = flatMapˢ op f (wkFlat τ fl) (wkCut τ oc) (mapMaybe (wk∋ τ) k) (wk∋ τ r) pl (wkTree τ t) (wkLanes τ ls)
    wkTree τ (connectˢ S c b kb k fd q e rt s bd) = connectˢ (wkSubject τ S) (wkCut τ c) (wkR τ b) (mapMaybe (wk∋ τ) kb) (mapMaybe (wk∋ τ) k)
                                                     (wkFeed τ fd) q e rt (wkTree τ s) (wkTree τ bd)
    wkTree τ (joinˢ j s fl x m)                  = joinˢ j (wk∋ τ s) (wkR τ fl) x m
    wkTree τ (deferˢ k t)                        = deferˢ (mapMaybe (wk∋ τ) k) (wkTree τ t)

    wkLanes : ∀ {h v Δ B} → h ⊑ v → List (Lane h Δ B) → List (Lane v Δ B)
    wkLanes τ []                 = []
    wkLanes τ (lane c k t ∷ ls) = lane (wkCut τ c) (mapMaybe (wk∋ τ) k) (wkTree τ t) ∷ wkLanes τ ls

  -- A path, carried along.
  mutual
    wkPath : ∀ {h v Δ A Δ′ A′} (τ : h ⊑ v) {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Path (wkTree τ t) (wkTree τ u)
    wkPath τ here          = here
    wkPath τ (in-map p)    = in-map (wkPath τ p)
    wkPath τ (in-scan p)   = in-scan (wkPath τ p)
    wkPath τ (in-take p)   = in-take (wkPath τ p)
    wkPath τ (in-outer p)  = in-outer (wkPath τ p)
    wkPath τ (in-lanes p)  = in-lanes (wkPathᴸ τ p)
    wkPath τ (in-source p) = in-source (wkPath τ p)
    wkPath τ (in-body p)   = in-body (wkPath τ p)
    wkPath τ (in-defer p)  = in-defer (wkPath τ p)

    wkPathᴸ : ∀ {h v Δ B Δ′ A′} (τ : h ⊑ v) {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → PathLanes (wkLanes τ ls) (wkTree τ u)
    wkPathᴸ τ (this-lane p) = this-lane (wkPath τ p)
    wkPathᴸ τ (next-lane p) = next-lane (wkPathᴸ τ p)
