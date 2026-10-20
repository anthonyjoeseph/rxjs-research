{-# OPTIONS --guardedness #-}

-- THE AUTHOR'S PROGRAM AND ITS ELABORATION.  An `SObs` is what a user
-- writes against srxjs: the same primitives as plain rxjs, so the same
-- tree, and its plain reading is the tree itself.  `batchSimultaneous`
-- stands only on top, applied to the elaboration, so it is not a former.
--
-- `elaborate` is srxjs written in rxjs, one former at a time: each
-- primitive rebuilt over InstEmits, so that every emit carries its
-- instant and the counting protocol.  It is generic in the leaves and in
-- the names, so every runtime runs the same elaboration, and nothing in
-- it can do more with a name than compare it.  A `cold` is elaborated
-- around the author's leaf and `fresh`; `connected` and `defer` carry no
-- emits of their own, so they are elaborated to themselves.
open import Relation.Binary.Definitions using (DecidableEquality)

module simultaneous.SObs where

open import Data.Bool using (Bool)
open import Data.List using (List; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline)
open import simultaneous.InstEmit using (InstEmit)
open import simultaneous.Leaf using (WithFresh)

SObs : List Set → Set → Set₁
SObs = Obs Timeline

module Elaborate {C : Set → Set₁} {N : Set} (_≟_ : DecidableEquality N) where

  -- What the engine runs: the author's leaves and `fresh`.
  E : List Set → Set → Set₁
  E = Obs (WithFresh C N)

  IE : Set → Set
  IE = InstEmit N

  -- Each primitive over InstEmits, and the batcher.
  postulate
    coldˢ      : ∀ {Γ A} → C A → E Γ (IE A)
    emptyˢ     : ∀ {Γ A} → E Γ (IE A)
    ofˢ        : ∀ {Γ A} → List A → E Γ (IE A)
    mapˢ       : ∀ {Γ A B} → (A → B) → E Γ (IE A) → E Γ (IE B)
    scanˢ      : ∀ {Γ A B} → (B → A → B) → B → E Γ (IE A) → E Γ (IE B)
    takeWhileˢ : ∀ {Γ A} → Bool → (A → Bool) → E Γ (IE A) → E Γ (IE A)
    flatMapˢ   : ∀ {Γ A B} → FlatOp → (A → E Γ (IE B)) → E Γ (IE A) → E Γ (IE B)
    connectˢ   : ∀ {Γ A B} → E Γ (IE A) → E (IE A ∷ Γ) (IE B) → E Γ (IE B)

    batchSimultaneous : ∀ {Γ A} → E Γ (IE A) → E Γ (IE (List A))

  mutual
    elaborate : ∀ {Γ A} → Obs C Γ A → E (L.map IE Γ) (IE A)
    elaborate (cold c)          = coldˢ c
    elaborate empty             = emptyˢ
    elaborate (of xs)           = ofˢ xs
    elaborate (map f s)         = mapˢ f (elaborate s)
    elaborate (scan f z s)      = scanˢ f z (elaborate s)
    elaborate (takeWhile i p s) = takeWhileˢ i p (elaborate s)
    elaborate (flatMap op f s)  = flatMapˢ op (λ a → elaborate (f a)) (elaborate s)
    elaborate (connect s b)     = connectˢ (elaborate s) (elaborate b)
    elaborate (connected i)     = connected (∈-map⁺ IE i)
    elaborate (defer l)         = defer (elaborateLater l)

    elaborateLater : ∀ {Γ A} → Later C Γ A → Later (WithFresh C N) (L.map IE Γ) (IE A)
    elaborateLater l .Later.force = elaborate (Later.force l)
