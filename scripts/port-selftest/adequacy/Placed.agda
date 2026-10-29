-- THE PORT CHECK'S IN-PLACE FIXTURE.  Never typechecked.  A module of the
-- old tower, ported where it stands: every declaration answers to the old
-- tower, those it already had included.
module adequacy.Placed where

-- MUST NOT: an old body, kept.
weigh-++ : Set
weigh-++ = Set

-- MUST FIRE (FILLED GAP): the old `under-shown-connect`, a postulate of
-- this very module, filled in place.
under-shown-connect : Set
under-shown-connect = Set

-- MUST NOT: the emission-set reading of an old body.
sibling-spreadᵀ : Set
sibling-spreadᵀ = Set

-- MUST FIRE (FILLED GAP): the emission-set reading of an old postulate.
placingᵀ : Set
placingᵀ = Set

-- MUST FIRE (NEW NAME): a emission-set reading of no old name.
inventedᵀ : Set
inventedᵀ = Set
