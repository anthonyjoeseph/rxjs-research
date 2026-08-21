-- E1 must stay QUIET here: a src file importing only src.  The namespace
-- test is on the module's ROOT component, so a src module whose own name
-- merely CONTAINS the word must not trip it.
module Good where

open import Rx.Prim using (Gas)
open import Verify-Budget-Sufficient.Refuted-Notes using (note)
