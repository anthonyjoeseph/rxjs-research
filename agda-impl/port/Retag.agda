{-# OPTIONS --guardedness #-}

-- RETAG: what each joiner holds of its feed, rewritten through a
-- subtree.  Only a joiner's part and its `Fed` clause read what it
-- holds, so every other part of the relation is kept as it stands; a
-- feed restaged at a connect is a retag of that connect's body.
--
-- Heap removal: the old `Sub h Δ A` (indexed by world `h`) becomes
-- `Sub Γ A`.  `Env Δ h`, `names`, `subjects`, `joiners`, `pendings`,
-- `unsub`, `Owes`, `Begun`, `fed-retag`, `fed-owed`, `envP`,
-- `joiners-path`, and the `Body` module are all heap-only concepts
-- with no tree counterpart and are NOT ported.
module port.Retag where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe)

open import denotation.MonotonicList.Events using (Pos)
open import port.Strong using (module Strongly)

-- What a joiner at `x`, joined at `j`, holds, rewritten.
Retag : List Set → Set₁
Retag Δ = ∀ {B} → B ∈ Δ → Pos → Maybe (List (Pos × Maybe B) × Maybe Pos) → Maybe (List (Pos × Maybe B) × Maybe Pos)

-- Under a connect: its own joiners kept.
keep : ∀ {A Δ} → Retag Δ → Retag (A ∷ Δ)
keep g (here _)  j st = st
keep g (there x) j st = g x j st

module Retagging (R : Set) where
  open Strongly R

  mutual
    retag : ∀ {Γ A} → Retag Γ → Sub Γ A → Sub Γ A
    retag g (pendingˢ s q)                  = pendingˢ s q
    retag g (coldˢ b ph)                    = coldˢ b ph
    retag g (ofˢ p i xs)                    = ofˢ p i xs
    retag g doneˢ                           = doneˢ
    retag g (mapˢ f s)                      = mapˢ f (retag g s)
    retag g (scanˢ f z s)                   = scanˢ f z (retag g s)
    retag g (cutˢ l a s)                    = cutˢ l a (retag g s)
    retag g (laneˢ r s)                     = laneˢ r (retag g s)
    retag g (takeWhileˢ i q tk s)           = takeWhileˢ i q tk (retag g s)
    retag g (flatMapˢ op f d n qs pl o ls)  = flatMapˢ op f d n qs pl (retag g o) (retagᴸ g ls)
    retag g (connectˢ k r e rt s b)         = connectˢ k r e rt (retag g s) (retag (keep g) b)
    retag g (joinˢ j gate x st)             = joinˢ j gate x (g x j st)

    retagᴸ : ∀ {Γ B} → Retag Γ → List (Sub Γ B) → List (Sub Γ B)
    retagᴸ g []       = []
    retagᴸ g (s ∷ ls) = retag g s ∷ retagᴸ g ls
