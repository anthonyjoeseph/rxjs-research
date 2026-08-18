module Thy where

postulate Nat : Set

-- WIRED: applied by a real body that Main reaches.
good-lemma : Nat → Nat
good-lemma x = x

-- PASSED-ONLY: its ONLY use is as a bare argument to a postulate.
bad-lemma : Nat → Nat
bad-lemma x = x

-- NESTED VALUE COMPUTATION: `nested` is applied inside parens to build a
-- value, NOT handed over as a proof.  Must keep its reachability.
nested : Nat → Nat
nested x = x

postulate parent-core : (Nat → Nat) → Nat → Nat

other : Nat → Nat
other y = good-lemma y

top-line : Nat → Nat
top-line z = other (parent-core bad-lemma (nested z))
