-- E7's third: the type is tied, and the body hands the postulate back as
-- its own proof -- which typechecks, and instantiates nothing.
-- TARGET: live-one @b6f6f3
module Lemma where
row : Confirms (live-one 3)
row = live-one 3
