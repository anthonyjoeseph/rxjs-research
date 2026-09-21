-- THE PALETTE A THEOREM RUNS AT: a shared definition is a plain tree
-- that carries its own authorship.
--
-- WHY IT IS A SEPARATE MODULE FROM `Rx.Palette`.  `Rx.Slots` is
-- parameterized by `Palette`, and everything in the evaluator reads
-- `Slots`, so `Rx.Palette` is imported by nearly the whole tree.
-- Deciding authorship needs `Rx.Elaborate`, and putting that dependency
-- in `Rx.Palette` would put the elaboration underneath the evaluator --
-- which happens to be acyclic today and is the wrong shape to rely on.
-- Here the two meet only where a theorem asks them to.
--
-- WHAT RUNS AT WHICH.  The CLI, the QuickCheck corpus and the unit
-- tests run at `plainPalette`, where every plain tree is a legal
-- definition and the evaluator is at full scope; a THEOREM about
-- elaborated programs runs here, where a definition provably cannot
-- hand the machine an envelope no elaboration produced.  Both
-- instantiations coexist in one build, which is the whole point of the
-- parameter.
module Rx.Palette.SExp where

open import Rx.Palette  using (Palette)
open import Rx.Authored using (Authored; authoredTree)

sexpPalette : Palette
sexpPalette = record { Tree = Authored ; embed = authoredTree }
