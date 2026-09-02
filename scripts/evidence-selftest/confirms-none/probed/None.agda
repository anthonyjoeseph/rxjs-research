-- E7's first counterexample: a receipt whose rows restate the target's
-- predicate by hand, so nothing holds them to the statement.
-- TARGET: live-one @b6f6f3
module None where
held : Bool
held = pred 3
row : held ≡ true
row = refl
