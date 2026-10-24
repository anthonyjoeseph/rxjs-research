-- In the port's import cone, and new since the frozen commit: checked as
-- the port is.
module Engine where

-- MUST FIRE (NEW NAME): a new body moved out of `port/` is still in scope.
smuggled : Set
smuggled = Set

postulate
  -- MUST NOT: a new postulate in the cone is free too.
  engine-gap : Set
