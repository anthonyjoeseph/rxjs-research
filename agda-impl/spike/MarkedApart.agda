{-# OPTIONS --guardedness #-}

-- SPIKE: THE ORDER IS NOT INDUCTIVE, WITH OR WITHOUT `apart`.  Both
-- statements are refuted by evaluation, at configurations the fold part
-- (`spike.MarkedInv.Base`) admits.
--
-- The shape of both: a flatMap with two lanes, an `of` subscribed at `q`
-- in the first and an `of` subscribed at `q ⊕ ix 1` in the second.  The
-- first of's next key is a sibling of its last (`ix i` to `ix (suc i)`),
-- not a child, so running it lands on territory the second already
-- holds.  Nothing in `Ord` or `apart` says no other node holds a key
-- under where an of will emit NEXT: that is a fact about what each node
-- will key in future, held pairwise across nodes, and neither a fold over
-- nodes nor a comparison of keys against the position.
--
-- What excludes these configurations in a real run is provenance: a key
-- under `q ⊕ ix 1` can only be made by an event there, and only the
-- first of emits there.  Stated as an invariant that is a zone per node,
-- covering every key it will ever make (an of at `q` at index `i` owns
-- `[at (q ⊕ ix i) , after q)`; a cold owns its frame and the cascade
-- column of its frame's end; a joiner its inbox), with zones pairwise
-- disjoint and none under the position.  Its preservation is linear,
-- each step's new zones inside the old zones of the nodes it rewrote
-- plus the position's subtree, but it is a new kind of field, and the
-- feed's joiners need their join positions distinct, which no zone
-- covers.
module spike.MarkedApart where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_; [_]; length; filterᵇ)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (empty; mergeᶠ)
open import Data.Maybe using (nothing)
open import denotation.MonotonicList.Events using (Pos; ix; root)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.MarkedPure using (module Machine; module Driver)
open Machine using (St; ofS; doneS; lnS; flatS; top; plug; Conf; ⟨_,_,_,_⟩; absorbed; _⊕_)
open import spike.MarkedFirst using (keys; Ord; past; fresh)
open import spike.MarkedInv using (Base; inv)
open Driver ℕ using (Step; silent; value; complete; drained; step)

------------------------------------------------------------------------
-- `apart`, as `quickcheck.MarkedOrder` probes it

private
  underᵇ : Pos → Key → Bool
  underᵇ q k = not (k <ᴷ at q) ∧ (k <ᴷ after q)

  alone : List Key → Key → Bool
  alone ks (at q)    = length (filterᵇ (underᵇ q) ks) ≤ᵇ 1
  alone ks (after q) = true

  allᵇ : List Key → List Key → Bool
  allᵇ ks []       = true
  allᵇ ks (k ∷ js) = alone ks k ∧ allᵇ ks js

Apart : Conf ℕ → Set
Apart ⟨ c , s , m , p ⟩ = allᵇ (keys (plug c s)) (keys (plug c s)) ≡ true

NextOrd NextApart : Step → Set
NextOrd (silent t k)    = Ord k
NextOrd (value t p a k) = Ord k
NextOrd (complete p)    = Data.Unit.⊤
NextOrd drained         = Data.Unit.⊤
NextApart (silent t k)    = Apart k
NextApart (value t p a k) = Apart k
NextApart (complete p)    = Data.Unit.⊤
NextApart drained         = Data.Unit.⊤

------------------------------------------------------------------------
-- Two lanes: an of at `q`, and one already under its next value

private
  q : Pos
  q = root

  lanes : List ℕ → St [] ℕ
  lanes xs = flatS (mergeᶠ nothing) (λ (_ : ℕ) → empty) false 2 [] doneS
    (lnS true (ofS 0 q xs) ∷ lnS true (ofS 0 (q ⊕ [ ix 1 ]) (0 ∷ [])) ∷ [])

  later : St [] ℕ
  later = flatS (mergeᶠ nothing) (λ (_ : ℕ) → empty) false 2 [] doneS
    (lnS true (ofS 1 q (0 ∷ [])) ∷ lnS true (ofS 0 (q ⊕ [ ix 1 ]) (0 ∷ [])) ∷ [])

  wf : ∀ {s : St [] ℕ} {p} → s ≡ lanes (0 ∷ 0 ∷ []) → Base ⟨ top , s , absorbed , p ⟩
  wf refl = inv tt tt (tt , tt , tt , tt)

-- The order is not kept by every step.  Absorbed just after the first
-- of's value 0, it runs value 1 at `q ⊕ ix 1`, with the second lane's key
-- under it.
ord-next-false : ¬ (∀ k → Base k → Ord k → NextOrd (step k))
ord-next-false h with h ⟨ top , later , absorbed , q ⊕ [ ix 0 ] ⟩ (inv tt tt (tt , tt , tt , tt)) (past (refl ∷ refl ∷ []) (tt , tt , tt , tt))
... | fresh (_ ∷ () ∷ _) _

-- Nor with `apart` added.  One step earlier: `apart` holds, and the run
-- of value 0 makes the first of's next key the second lane's ancestor.
apart-next-false : ¬ (∀ k → Base k → Ord k → Apart k → NextOrd (step k) Data.Product.× NextApart (step k))
apart-next-false h with h ⟨ top , lanes (0 ∷ 0 ∷ []) , absorbed , q ⟩ (wf refl) (past (refl ∷ refl ∷ []) (tt , tt , tt , tt)) refl
... | _ , ()
