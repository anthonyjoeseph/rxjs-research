-- fixture: a sibling module the elaboration takes a helper from BY NAME.
-- `liftᵖ` is imported, so what it writes counts; `plainExp` is not, and it
-- names `notᵖ`, which the map declares unreachable -- so a check crediting
-- the whole module, or slicing `liftᵖ` down to the next signature and so
-- through the `mutual` block below it, is not quiet.
module SExp.Plain where

liftᵖ : Tm Γ t → Exp Γ t
liftᵖ f = liftᵉ (primᵗ add f)

mutual
  plainExp : SExp Γ t → Exp Γ t
  plainExp (notˢ b) = liftᵉ (primᵗ notᵖ (plainTm b))

  plainTm : STm Γ t → Tm Γ t
  plainTm (natˢ k) = nat̂ k
