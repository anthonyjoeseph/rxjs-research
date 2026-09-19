module Heavy where

-- A FIXTURE, AND WHAT IT IS A FIXTURE FOR.  `dev-changed` escalates to the
-- full gate when a changed module carries a MULTI-MEMBER mutual block, and
-- reports rather than silently drops such a module when it is only a CONE
-- member -- because agda-dev stubs a block's siblings, so a dev pass there
-- is not a check.  Nothing in `agda/src` has one any more: every mutual
-- block in the tree is written with the keyword, which agda-dev treats as
-- opaque and emits verbatim, so both rules fire on nothing and would rot
-- untested.  This declares a block the way Agda itself groups them -- a
-- forward signature whose definition arrives only after a second
-- declaration has come and gone -- which needs no keyword at all.
open import Leaf using (A)

even : A → Set
odd  : A → Set

even x = odd x
odd  x = even x
