{-# OPTIONS --guardedness #-}

-- THE BUG CACHE: every program that ever made the semantics disagree,
-- as one list the compiled runner walks.
--
-- APPEND-ONLY.  A counterexample becomes a row; once its bug is fixed it
-- stays as a regression guard.  Nothing is deleted or rewritten, so
-- `make bug-cache` is green exactly when no known counterexample remains.
--
-- A ROW IS A PROGRAM, NOT A SEED.  A seed names a program only until the
-- generator changes, so a row holds the `Prog` itself; the label says
-- where it came from and means nothing more.
module quickcheck.Bug-Cache where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (mergeᶠ; exhaustᶠ)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Code using (Prog; script; cold; of; map; flatMap; connect; connected; μ; defer)
open import quickcheck.Tm using (var; nat; plus)

cases : List (String × Prog natᵗ)
cases =
  -- a looping source its body never joins: the meaning was silent
  ("connect, unjoined looping source" , connect (cold (script ((1 , 1 ∷ []) ∷ []) false true)) (cold (script [] false false)))
  ∷ -- a body done later beside a looping source, in a lane of an outer gone quiet
  ("connect, body done beside its looping source" , flatMap (mergeᶠ nothing) (connect (cold (script ((1 , 1 ∷ []) ∷ []) false true)) (cold (script ((2 , []) ∷ []) true false))) (cold (script ((0 , 0 ∷ []) ∷ []) false false)))
  ∷ -- three lanes joined to a source whose burst follows a timer: the meaning showed them lane by lane
  ("connect, lanes joined across a timer's burst" ,
    defer (connect
      (connect (μ (cold (script ((1 , 1 ∷ []) ∷ (2 , 3 ∷ 3 ∷ []) ∷ []) false false)))
               (map (plus (plus (var (here refl)) (var (here refl))) (plus (var (here refl)) (nat 5)))
                    (cold (script ((1 , []) ∷ (0 , 0 ∷ 4 ∷ 3 ∷ []) ∷ (1 , 2 ∷ 3 ∷ 4 ∷ []) ∷ []) false false))))
      (flatMap (mergeᶠ (just 3)) (defer (connected (here refl)))
               (flatMap exhaustᶠ (of (plus (nat 3) (nat 4) ∷ plus (nat 3) (nat 4) ∷ [])) (of (nat 2 ∷ nat 1 ∷ []))))))
  ∷ []
