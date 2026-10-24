{-# OPTIONS --guardedness #-}

-- SPIKE: BIRTHS NO LATER THAN THE CURSOR DO NOT MAKE THE ORDER INDUCTIVE.
-- Every node that records where it was subscribed (an of, a joiner) was
-- subscribed at or before the position (`Born`).  That excludes both
-- configurations `spike.MarkedApart` refutes the order at, each holding a
-- node born after the position.  The cursor is taken AT the position, so
-- any cursor at or past it admits the same configuration.
--
-- Two nodes born at the same position still are admitted: their keys tie
-- once one of them runs (`born-next-false`).  Excluding them is
-- distinctness of births, a fact about pairs of nodes; held per frame it
-- relates every birth under one child to every birth under another,
-- which is the pairwise field again, indexed by the pair's least common
-- frame.
--
-- Nor is the per-node half of the route there: a key under its node's
-- own birth is false of reachable configurations.  A joiner shows its
-- feed under its source's emission (`operation.Marked.queued` queues it
-- at the source's position, tagged with the joiner's), and a cold's later
-- frames sit in a cascade keyed by tick at the root
-- (`operation.MarkedPure.rest`).  Both zones are made by something other
-- than the node.
module spike.MarkedBorn where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (empty; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; ix; root; _<ᵖ_)
open import operation.MarkedPure using (module Machine; module Driver)
open Machine using (St; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; top; plug; Conf; ⟨_,_,_,_⟩; absorbed; _⊕_)
open import spike.MarkedFirst using (Ord; past; fresh)
open import spike.MarkedInv using (Base; inv)
open import spike.MarkedApart using (NextOrd)
open Driver ℕ using (step)

------------------------------------------------------------------------
-- Where each node that records it was subscribed

mutual
  births : ∀ {Γ A} → St Γ A → List Pos
  births (ofS i p xs)            = [ p ]
  births (joinS j g x ib)        = [ j ]
  births (mapS f s)              = births s
  births (scanS f z s)           = births s
  births (cutS l a s)            = births s
  births (lnS b s)               = births s
  births (takeS i q w s)         = births s
  births (flatS op f d n q o ls) = births o Data.List.++ birthsL ls
  births (connS k o b)           = births o Data.List.++ births b
  births _                       = []

  birthsL : ∀ {Γ A} → List (St Γ A) → List Pos
  birthsL []       = []
  birthsL (s ∷ ls) = births s Data.List.++ birthsL ls

-- Every birth at or before the cursor.
Born : ∀ {R} → Conf R → Set
Born ⟨ c , s , m , p ⟩ = All (λ b → (p <ᵖ b) ≡ false) (births (plug c s))

------------------------------------------------------------------------
-- Two ofs subscribed at one position

private
  q : Pos
  q = root

  twins : St [] ℕ
  twins = flatS (mergeᶠ nothing) (λ (_ : ℕ) → empty) false 2 [] doneS
    (lnS true (ofS 1 q (0 ∷ [])) ∷ lnS true (ofS 1 q (0 ∷ [])) ∷ [])

-- Absorbed after both ofs' value 0, born before it: the first runs value
-- 1 at `q ⊕ ix 1`, where the second is keyed.
born-next-false : ¬ (∀ k → Base k → Ord k → Born k → NextOrd (step k))
born-next-false h with h ⟨ top , twins , absorbed , q ⊕ [ ix 0 ] ⟩ (inv tt tt (tt , tt , tt , tt)) (past (refl ∷ refl ∷ []) (tt , tt , tt , tt)) (refl ∷ refl ∷ [])
... | fresh (_ ∷ () ∷ _) _
