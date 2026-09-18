-- the selftest's fifth and sixth surfaces: the sweep's per-former census
-- and the Agda sweep's reach.  Three formers, matching
-- `scripts/formers.tsv`'s `exp` rows, and the fixture is QUIET.
--
-- The generator writes the AUTHOR's palette and nothing plain, which is
-- the whole reason the sixth surface is a composition: read alone this
-- region reaches no former in the map at all.
module QuickCheck where

genB : ℕ → Gen ℕ
genB bound rs = bound , rs

-- the generator region, which the sixth surface reads between `genB` and
-- the census below.  It draws every author former whose elaboration the
-- map declares reached and no other -- in particular no `notˢ`, which is
-- what leaves that prim row's hole open.  `notᵖCount` is here to pin the
-- token boundary: a substring scan would read `notᵖ` out of it and report
-- the agen=no row's hole closed when nothing writes one.
genExp : ℕ → Gen SExp
genExp d = genB 2 >>=G λ c → pureG
  (      if c ≡ᵇ 0 then liftˢ (natˢ notᵖCount)
    else if c ≡ᵇ 1 then deferˢ d
    else liftˢ (natˢ d))

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
