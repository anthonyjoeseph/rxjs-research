{-# OPTIONS --guardedness #-}

-- THE CONNECT FEED'S EDGES, BY HAND.  Drawn programs rarely subscribe a
-- joiner while a connect's source is being fed, so these do it on
-- purpose: a joiner subscribing mid-feed, the body or a joiner
-- completing mid-feed, a connect inside a joiner's lane, a joiner
-- bursting inline.  `Oracle-CLI hand` holds each to `quickcheck.Quickcheck.prop` and
-- `quickcheck.Placing.placing`.
module quickcheck.Adversary where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Tm using (var; nat; bool)
open import quickcheck.Code using (Code; Prog; Script; script; cold; of; takeWhile; flatMap; connect; connected; defer)

private
  -- Two values in one frame, then a third, then done.
  two-then-one : Script natᵗ
  two-then-one = script ((1 , 10 ∷ 11 ∷ []) ∷ (1 , 12 ∷ []) ∷ []) true false

  src : ∀ {Γ Δᵍ Δ Θ} → Code Γ Δᵍ Δ Θ natᵗ
  src = cold two-then-one

cases : List (String × Prog natᵗ)
cases =
    ("a joiner per value, subscribed mid-feed"
    , connect src (flatMap (mergeᶠ nothing) (connected (here refl)) (connected (here refl))))
  ∷ ("a switch onto a fresh joiner per value"
    , connect src (flatMap switchᶠ (connected (here refl)) (connected (here refl))))
  ∷ ("an exhaust onto joiners"
    , connect src (flatMap exhaustᶠ (connected (here refl)) (connected (here refl))))
  ∷ ("a concat of two joiners"
    , connect src (flatMap (mergeᶠ (just 1)) (connected (here refl)) (of (nat 0 ∷ nat 1 ∷ []))))
  ∷ ("the body completing mid-feed, a joiner still owed"
    , connect src (takeWhile true (bool false) (flatMap (mergeᶠ nothing) (connected (here refl)) (of (nat 0 ∷ nat 1 ∷ [])))))
  ∷ ("joiners completing mid-feed"
    , connect src (flatMap (mergeᶠ nothing) (takeWhile true (bool false) (connected (here refl))) (of (nat 0 ∷ nat 1 ∷ []))))
  ∷ ("a joiner bursting inline"
    , connect src (flatMap (mergeᶠ nothing) (flatMap (mergeᶠ nothing) (of (var (here refl) ∷ var (here refl) ∷ [])) (connected (here refl))) (of (nat 0 ∷ nat 1 ∷ []))))
  ∷ ("a connect inside a joiner's lane, joining the outer source per value"
    , connect src (flatMap (mergeᶠ nothing) (connect (connected (here refl)) (flatMap (mergeᶠ nothing) (connected (there (here refl))) (connected (here refl)))) (of (nat 0 ∷ nat 1 ∷ []))))
  ∷ ("a connect over an inline source, joining the outer source per value"
    , connect src (flatMap (mergeᶠ nothing) (connect (of (var (here refl) ∷ var (here refl) ∷ [])) (flatMap (mergeᶠ nothing) (connected (there (here refl))) (connected (here refl)))) (connected (here refl))))
  ∷ ("a nested connect over a joiner, switching onto the outer source"
    , connect src (connect (connected (here refl)) (flatMap switchᶠ (connected (there (here refl))) (connected (here refl)))))
  ∷ ("a deferred joiner per value"
    , connect src (flatMap (mergeᶠ nothing) (defer (connected (here refl))) (connected (here refl))))
  ∷ []
