-- A PARAMETERIZED MODULE, for the module-ARGUMENT arm of the scan.  The
-- fixture is read textually and never typechecked; what it has to exhibit is
-- the SHAPE `open import Param <arg>`, where `<arg>` has no other consumer.
module Param {A : Set} (f : A → A) where

apply : A → A
apply x = f x
