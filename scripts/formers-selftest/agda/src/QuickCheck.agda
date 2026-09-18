-- the selftest's fifth and sixth surfaces: the sweep's per-former census
-- and the Agda generator.  Three formers, matching `scripts/formers.tsv`'s
-- `exp` rows, and the fixture is QUIET -- every tag is in a row, every
-- constructor is on the roll, and the generator writes exactly the two
-- the map declares it reaches.
module QuickCheck where

genB : ℕ → Gen ℕ
genB bound rs = bound , rs

-- the generator region, which the sixth surface reads between `genB` and
-- the census below.  It writes every name the map declares it reaches and
-- no other.  `notᵖCount` is here to pin the token boundary: a substring
-- scan would read `notᵖ` out of it and report the agen=no row's hole
-- closed when the generator has no such lane.
genExp : ℕ → Gen Exp
genExp d = genB 2 >>=G λ c → pureG
  (      if c ≡ᵇ 0 then liftᵉ (nat̂ notᵖCount)
    else if c ≡ᵇ 1 then sharedSigᵉ (add d)
    else deferᵉ d)

marksᵉ : Exp → Marks
marksᵉ (liftᵉ t)      = one fLift
marksᵉ (deferᵉ e)     = one fDefer
marksᵉ (sharedSigᵉ e) = one fSharedSig

data Former : Set where
  fLift fDefer fSharedSig : Former

formerTag : Former → String
formerTag fLift      = "lift"
formerTag fDefer     = "defer"
formerTag fSharedSig = "sharedSig"

allFormers : List Former
allFormers = fLift ∷ fDefer ∷ fSharedSig ∷ []
