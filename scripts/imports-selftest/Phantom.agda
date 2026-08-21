-- FIXTURE for `make imports-selftest`: the shape that a many-minute build is
-- the only other way to find.  Agda calls an import of a name the module does
-- not export a ModuleDoesntExport WARNING, and `-W error` turns that into exit
-- 42 deep in the tower, in a module that is itself correct -- so the report
-- names the importer and says nothing about where the name went.  It arrives
-- when a definition MOVES: the old module stops exporting the name, and one
-- consumer's `using` clause still asks for it while its sibling has already
-- been repaired.  The `public` ban is what makes the check sound, since
-- without re-exports a module can only export what its own text mentions.
module Phantom where

open import Phantom-Src using (real-thing; module Sub-Mod; gone; hidden)

-- THE SOURCE SIDE IS WHAT IS ASKED ABOUT, and this row is what pins it: `x to
-- y` binds `y` but the module must export `x`, so a check reading the BOUND
-- name asks Phantom-Src for `r2` -- absent -- and reports a false phantom on
-- the one item here that is correct.
open import Phantom-Src using () renaming (real-thing to r2; absent to a2)

-- THERE IS NO MIXFIX ROW HERE, deliberately.  An import spells an operator
-- in full -- `using (_⊗_)`, never a section -- so the token the check looks
-- for is the token the defining module writes, and no mutation of the
-- name-splitting the USE check depends on can make such a row fail.  A row
-- that cannot fail is not a row; the section rows in Quiet.agda are where
-- that splitting is pinned, and they fire on exactly the mutation that
-- deleted 507 live names.
--
-- Every imported name is spent right here, phantoms included, so nothing in
-- this file can be reported dead: a phantom is a name that does not EXIST, not
-- a name that goes unused, and a row that could also fire as a dead name would
-- not tell the two apart.
alive : Set
alive = real-thing Sub-Mod.inner gone hidden r2 a2
