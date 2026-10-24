-- THE PORT CHECK'S FIXTURE.  Never typechecked: `make port-selftest` runs
-- `check-port.py` over it against the real old tower, and names every row
-- that must fire and every row that must not.
module port.Fixture where

open import Engine

-- MUST NOT: an old name, ported with a body.
run : Set
run = Set

-- MUST FIRE (NEW NAME): a body under a name the old tower never had.
invented : Set
invented = Set

-- MUST FIRE (FILLED GAP): the old `placing` is a postulate.
placing : Set
placing = Set

postulate
  -- MUST NOT: a new postulate states a gap and proves nothing.
  fresh-gap : Set

  -- MUST NOT: an old postulate stays one.
  ticks-up : Set

  -- MUST NOT: an old body, postulated, pointed at.
  --
  -- OLD BODY: 85c14392490061b71342d104b2d16a16cb4ec724 agda-impl/adequacy/Content.agda
  content : Set

  -- MUST FIRE (NO OLD BODY): an old body, postulated, unpointed.
  complete : Set

  -- MUST FIRE (BAD OLD BODY): the path does not exist there.
  --
  -- OLD BODY: 85c14392490061b71342d104b2d16a16cb4ec724 agda-impl/adequacy/Nowhere.agda
  reaches : Set

  -- MUST FIRE (BAD OLD BODY): the file exists, but declares no such name.
  --
  -- OLD BODY: 85c14392490061b71342d104b2d16a16cb4ec724 agda-impl/adequacy/Content.agda
  prefix-chain : Set

  -- MUST FIRE (BAD OLD BODY): no such commit.
  --
  -- OLD BODY: 0000000000000000000000000000000000000000 agda-impl/adequacy/Progress.agda
  reached : Set

-- MUST NOT: a private helper is part of the body it serves.
private
  helper : Set
  helper = Set

-- MUST NOT: a where-local is too.
read-of : Set
read-of = local
  where
  local : Set
  local = Set
