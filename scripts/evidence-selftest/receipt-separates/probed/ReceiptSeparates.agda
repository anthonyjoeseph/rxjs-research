-- A fork wearing a receipt's marker: it chooses between mechanisms whatever
-- the header says, so `-- PROBED:` written from it is a coverage claim about
-- a statement the separating rows were never about.
-- TARGET: live-one @b6f6f3
module ReceiptSeparates where
nest-fork : Separates sum-d join-d
nest-fork = record { at = prog ; apart = λ () }
