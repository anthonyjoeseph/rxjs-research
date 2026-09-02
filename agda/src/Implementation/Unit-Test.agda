-- Type-level unit tests: a performance cache of discovered counterexamples.
-- Each entry is a `refl`-checked pin — it fixes the exact batching the impl
-- must produce for a specific generated program (spec-derived). A regression
-- fails the typechecker instantly instead of surfacing only in a random
-- QuickCheck seed.
--
-- APPEND-ONLY, via scripts/gen-unit-tests.sh: a new QuickCheck failure
-- becomes a new module under `Unit-Test/` and a claim below; a fixed bug just
-- becomes a passing guard that stays.  Invariant: this module fully
-- typechecks ⟺ no known counterexample remains — green here is the impl≡spec
-- finish line for the cached cases.  Delete this module once
-- Formal-Verification is discharged.
--
-- THE CASES THEMSELVES LIVE ONE PER MODULE, and this file is the ledger that
-- claims them: each is pinned anonymously below, which is what a MODULE_ROOTS
-- file's reachability is seeded from.  Why they are not rows in this file is
-- in `Unit-Test/Prelude.agda`.
module Implementation.Unit-Test where


open import Implementation.Unit-Test.Case-315 using (wf-315)
_ : _
_ = wf-315

open import Implementation.Unit-Test.Case-378 using (wf-378)
_ : _
_ = wf-378
