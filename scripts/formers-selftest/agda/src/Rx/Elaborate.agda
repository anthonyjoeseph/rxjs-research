-- fixture: the elaboration the sixth surface composes the generator with.
-- The sweep draws the AUTHOR's palette, so no plain former is named by a
-- generator arm at all and the surface has to follow the arms.
--
-- Three of the four properties that composition has are pinned right here,
-- by the base fixture being QUIET: `liftˢ` is drawn and its arm reaches a
-- HELPER, so what the helper writes counts; `notˢ` is NOT drawn, so what
-- its arm writes does not, which a union over the file would get wrong;
-- and `deferˢ` IS drawn but its arm is a POSTULATE, which has no body and
-- so reaches nothing.
module Rx.Elaborate where

postulate
  -- a drawn arm with no body: the shape that makes an author former's
  -- reachability say nothing about its plain counterpart's
  deferᵖ : SExp Γ t → Exp Γ t

mutual
  toPlain : SExp Γ t → Exp Γ t
  toPlain (liftˢ f)  = liftᵖ (toPlainTm f)
  toPlain (deferˢ e) = deferᵖ (toPlain e)
  toPlain (notˢ b)   = liftᵉ (primᵗ notᵖ (toPlainTm b))

  toPlainTm : STm Γ t → Tm Γ t
  toPlainTm (natˢ k) = nat̂ k

liftᵖ : Tm Γ t → Exp Γ t
liftᵖ f = liftᵉ (primᵗ add f)
