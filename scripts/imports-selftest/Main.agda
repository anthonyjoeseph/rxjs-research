-- FIXTURE: the CLAIM ROOT of this fixture tree, and the reason the tree has
-- one at all.  A claim root NAMES definitions instead of applying them, so
-- every import here is locally unused and the checker must report NOTHING for
-- this file.  The real claim roots (src/Main.agda, refuted/Refuted/Main.agda)
-- cannot serve as the test: the checker is meant to leave them alone, so
-- pointing it at them proves only that it is silent, never that it is silent
-- FOR THE RIGHT REASON.  This file is never typechecked by anything.
module Main where

-- AND THE BLANKET RULE BINDS THE CLAIM ROOT TOO (Anthony), which is the one
-- place the two rules collide: this file is skipped wholesale by the USE check,
-- and must STILL be reported for the line below.  src/Main.agda's own header has
-- demanded `using` lists in prose since long before anything checked it.
open import Fixture.Root-Blanket

open import Guard-Root using (root-anchor)
open import Guard-Two-A using (two-a-anchor)
open import Guard-Two-B using (two-b-anchor)
