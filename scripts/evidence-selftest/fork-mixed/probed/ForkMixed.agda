-- Both kinds in one file, so the receipt written from it would report
-- coverage the separating row never bought.
-- TARGET: live-one @b6f6f3
-- FORK: live-one
module ForkMixed where
nest-fork : Separates sum-d join-d
nest-fork = record { at = prog ; apart = λ () }
row : Confirms (live-one 3)
row = refl
