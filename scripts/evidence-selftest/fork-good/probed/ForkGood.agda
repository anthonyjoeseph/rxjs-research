-- The legal shape of the second kind: a probe standing at a design choice,
-- naming the statement whose shape is in question, and PROVING that its two
-- candidates disagree rather than saying so.
-- FORK: live-one
module ForkGood where
nest-fork : Separates sum-d join-d
nest-fork = record { at = prog ; apart = λ () }
