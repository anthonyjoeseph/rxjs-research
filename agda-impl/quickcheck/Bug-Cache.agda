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
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

open import quickcheck.Ty using (natᵗ)
open import quickcheck.Code using (Prog; script; cold; connect)

cases : List (String × Prog natᵗ)
cases =
  -- a looping source its body never joins: the meaning was silent
  ("connect, unjoined looping source" , connect (cold (script ((1 , 1 ∷ []) ∷ []) false true)) (cold (script [] false false)))
  ∷ []
