-- the selftest's fifth surface: the sweep's per-former census.  Three
-- formers, matching `scripts/formers.tsv`'s `exp` rows, and the fixture
-- is QUIET -- every tag is in a row and every constructor is on the roll.
module QuickCheck where

data Former : Set where
  fLift fDefer fSharedSig : Former

formerTag : Former → String
formerTag fLift      = "lift"
formerTag fDefer     = "defer"
formerTag fSharedSig = "sharedSig"

allFormers : List Former
allFormers = fLift ∷ fDefer ∷ fSharedSig ∷ []
