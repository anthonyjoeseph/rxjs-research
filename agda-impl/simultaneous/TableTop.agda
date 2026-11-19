{-# OPTIONS --guardedness #-}

-- THE TOP'S CASE (`top-rel`): the program's record, carried through the
-- batcher's plumbing one layer at a time.  The plain run stays the
-- program's own; only the elaborated table and its subscription change.
-- The program is subscribed as the told run's source, two labels under
-- the merge's first lane.
--
-- The plain completion is imaged on an elaborated end at every layer:
-- the told run's end past its mark (`told-rel`), then the end the take
-- leaves under the completion mark (`closed-rel`).  The merge alone has
-- no end, since the subscribe mark's lane never ends, so the merge and
-- the take are one layer.  Each layer's marks are unshown, and lie in
-- the subscription's instant or in the plain completion's, which leads
-- its instant or follows a value of it imaged before them.
module simultaneous.TableTop where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
import quickcheck.Tabled as Tb
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC)
open import simultaneous.TableCorr using (Rel)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; elaborate; completing; wrapped)

------------------------------------------------------------------------
-- The tables of one closed program and its plumbing

Plain : ∀ {A} → ℕ → Obs Timeline [] A → ℕ → Maybe (Tb.Listed A)
Plain n o N = listC (3 + N) n o [] root

At : ∀ {A} → ℕ → Obs Timeline [] (IE A) → Pos → ℕ → Maybe (Tb.Listed (IE A))
At n e p N = listC (3 + N) n e [] p

-- The merge's first lane, and the told run's source under it.
lane₀ core₀ : Pos
lane₀ = root ⊕ (ix 0 ∷ ix 1 ∷ [])
core₀ = root ⊕ (ix 0 ∷ ix 1 ∷ ix 1 ∷ [])

------------------------------------------------------------------------
-- The layers

postulate
  -- THE TOLD RUN: the program read through its own subject by a concat
  -- queueing the completion mark.  The connect's hot rows are the
  -- source's, rekeyed under its subscription; the concat's first part
  -- reads them back, and its second leaves the mark and the end past the
  -- source's end.
  -- RECOVERY: git show a0945587 restores the told run carried over approx (simultaneous/CarryTold.agda over the inventory and inversion of simultaneous/ToldRows.agda), each to be restated over the tables.
  told-rel : ∀ {A} {S : Scope} n (o : Obs Timeline [] A)
           → Rel (Plain n o) (At n (elab (λ i → i) o) core₀) root core₀ S
           → Rel (Plain n o) (At n (completing (elab (λ i → i) o)) lane₀) root lane₀ S

  -- THE CLOSED RUN: the told run merged with the subscribe mark's lane,
  -- taken through the completion mark.  Owes that the program never
  -- emits a completion mark, so the take's first failure is the told
  -- run's; the subscribe mark lies in the subscription's instant.
  -- RECOVERY: git show a0945587 restores the merge and take carried over approx (simultaneous/WrapTake.agda, simultaneous/CarryWrap.agda) and the core's emits (simultaneous/CoreOuts.agda), each to be restated over the tables.
  closed-rel : ∀ {A} {S : Scope} n (o : Obs Timeline [] A)
             → Rel (Plain n o) (At n (completing (elab (λ i → i) o)) lane₀) root lane₀ S
             → Rel (Plain n o) (At n (wrapped (elab (λ i → i) o)) root) root root S

  -- THE RESTAMP: every emit renamed for the last `begin` before it, a
  -- scan read through `proj₂`.  Positions, constructors and values stay;
  -- as `scan-tab`'s elaborated half, agreement back is by coherence.
  stamped-rel : ∀ {A} {S : Scope} n (o : Obs Timeline [] A)
              → Rel (Plain n o) (At n (wrapped (elab (λ i → i) o)) root) root root S
              → Rel (Plain n o) (At n (elaborate o) root) root root S

------------------------------------------------------------------------
-- The top

top-rel : ∀ {A} {S : Scope} n (o : Obs Timeline [] A)
        → Rel (Plain n o) (At n (elab (λ i → i) o) core₀) root core₀ S
        → Rel (Plain n o) (At n (elaborate o) root) root root S
top-rel n o R = stamped-rel n o (closed-rel n o (told-rel n o R))
