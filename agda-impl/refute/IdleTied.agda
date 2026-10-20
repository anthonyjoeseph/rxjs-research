-- A pool not `Restful` breaks `idle-tied`: a defer steps to a skip but
-- rests hushed, so joined with an idle pool it hushes where it skipped.
module refute.IdleTied where

open import Data.List using ([])
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (¬_)
open import Tree using (Later; empty)
open import denotation.MonotonicList.Events using (Timeline)
import denotation.Unfold as U
open import adequacy.Strong.Against using (module StrongAgainst)
open StrongAgainst ⊤ using (Tied; Pinned; pinned)

l : Later Timeline [] ⊤
Later.force l = empty

p : U.Node [] ⊤
p = U.deferᶜ l [] []

x : U.Node [] ⊤
x = U.burstingᶜ [] p

tied : Tied p x
tied = pinned

refuted : ¬ (∀ {A B} {p : U.Node [] A} {x : U.Node [] B} → Tied p x → Tied (U.unionᶜ p U.idleᶜ) x)
refuted it with it {p = p} {x = x} tied
... | ()

o : U.Node [] ⊤
o = U.idleᶜ

-- The same pool joined with an ended outer's rest, as `close-tied` joins it.
refuted-close : ¬ (∀ {A B} {p : U.Node [] A} {x : U.Node [] B} → Tied p x → Tied (U.unionᶜ p (U.restᶜ o)) x)
refuted-close it with it {p = p} {x = x} tied
... | ()
