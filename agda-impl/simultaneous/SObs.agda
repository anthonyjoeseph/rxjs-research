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
-- it can do more with a name than compare it.  `connected` and `defer`
-- carry no emits of their own, so they are elaborated to themselves.
open import Relation.Binary.Definitions using (DecidableEquality)

module simultaneous.SObs where

open import Data.Bool using (Bool; true; _∧_)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₂)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Timeline)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; delivery; valuesOf)

SObs : List Set → Set → Set₁
SObs = Obs Timeline

module Elaborate {C : Set → Set₁} {N : Set} (_≟_ : DecidableEquality N) (name : N) where

  -- What the engine runs: the author's leaves.
  E : List Set → Set → Set₁
  E = Obs C

  IE : Set → Set
  IE = InstEmit N

  -- PLACEHOLDER: every emit is one delivery under the one `name`, with
  -- no counting protocol; the spec fails.  It fixes the shape the real
  -- operators take: each `INLINE`, built from constructors and plain
  -- lambdas around its child, opaque only in data.
  delivered : ∀ {A} → List A → IE A
  delivered as = instEmit (L.map value as) name name delivery

  stepped : ∀ {A B} → (B → A → B) → B × IE B → IE A → B × IE B
  stepped f (b , _) e = L.foldl f b (valuesOf e) , delivered (L.drop 1 (L.scanl f b (valuesOf e)))

  coldˢ : ∀ {Γ A} → C A → E Γ (IE A)
  coldˢ c = map (λ a → delivered (a ∷ [])) (cold c)
  {-# INLINE coldˢ #-}

  emptyˢ : ∀ {Γ A} → E Γ (IE A)
  emptyˢ = empty
  {-# INLINE emptyˢ #-}

  ofˢ : ∀ {Γ A} → List A → E Γ (IE A)
  ofˢ xs = of (delivered xs ∷ [])
  {-# INLINE ofˢ #-}

  mapˢ : ∀ {Γ A B} → (A → B) → E Γ (IE A) → E Γ (IE B)
  mapˢ f s = map (λ e → delivered (L.map f (valuesOf e))) s
  {-# INLINE mapˢ #-}

  scanˢ : ∀ {Γ A B} → (B → A → B) → B → E Γ (IE A) → E Γ (IE B)
  scanˢ f z s = map proj₂ (scan (stepped f) (z , delivered []) s)
  {-# INLINE scanˢ #-}

  takeWhileˢ : ∀ {Γ A} → Bool → (A → Bool) → E Γ (IE A) → E Γ (IE A)
  takeWhileˢ i p s = takeWhile i (λ e → L.foldr (λ a r → p a ∧ r) true (valuesOf e)) s
  {-# INLINE takeWhileˢ #-}

  flatMapˢ : ∀ {Γ A B} → FlatOp → (A → E Γ (IE B)) → E Γ (IE A) → E Γ (IE B)
  flatMapˢ op g s = flatMap op (λ e → flatMap (mergeᶠ nothing) (λ a → g a) (of (valuesOf e))) s
  {-# INLINE flatMapˢ #-}

  connectˢ : ∀ {Γ A B} → E Γ (IE A) → E (IE A ∷ Γ) (IE B) → E Γ (IE B)
  connectˢ s b = connect s b
  {-# INLINE connectˢ #-}

  batchSimultaneous : ∀ {Γ A} → E Γ (IE A) → E Γ (IE (List A))
  batchSimultaneous s = map (λ e → delivered (valuesOf e ∷ [])) s

  -- `elaborate`, one clause per former, each operator inlined around the
  -- elaborated child: Agda's productivity check accepts recursion through
  -- `defer` only under constructors, and sees through `INLINE`, nested
  -- too.  An opaque definition around any recursive call sinks the whole
  -- mutual block, and so does a pattern-matching lambda whose arm holds
  -- the child: Agda lifts it out as a definition of its own.
  --
  -- The rule binds only the path down to a child.  Data may pass through
  -- anything, so an operator's logic can stay opaque once it reads its
  -- child as a `connect`'s source through `connected`, and a choice
  -- between programs can gate each with a `takeWhile` on a one-value
  -- `of`.  A child moved under a new binder needs `rename`, which is
  -- opaque; elaborating under a renaming, as `rename` does, avoids it.
  --
  -- DEAD ROUTE: postulated operators around the calls.  Measured: a
  --   postulate, or a definition without `INLINE`, in place of any
  --   constructor fails termination at every clause, `connect`'s included.
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
    elaborate (defer l)         = defer (elaborateˡ l)

    elaborateˡ : ∀ {Γ A} → Later C Γ A → Later C (L.map IE Γ) (IE A)
    elaborateˡ l .Later.force = elaborate (Later.force l)
