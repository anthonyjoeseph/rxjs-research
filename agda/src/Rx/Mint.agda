module Rx.Mint where

open import Data.Nat  using (ℕ; suc)

------------------------------------------------------------------
-- One ledger for every identifier the run mints.
------------------------------------------------------------------

-- THE COUNTERS ARE SILOED BY A KEY RATHER THAN BY A FIELD, AND THAT IS
-- WHAT TURNS A FAMILY OF FACTS INTO ONE FACT.  The scheduler minted
-- ordinals, sources and node instances out of three separate fields, so
-- everything anyone wanted to know about allocation had to be said once
-- per field: the freshness induction over the run is stated about node
-- instances and about nothing else, and the other two carry no
-- monotonicity at all — not because they do not need it but because
-- proving it a second time costs a second induction over the same
-- relations.  Keyed, the induction is stated at an ARBITRARY key and
-- every counter inherits it.
--
-- WHAT KEEPS THE KEYS APART IS THE BUMP AND NOT THE READER.  `next`
-- advances the key it was asked for and leaves every other key
-- pointwise alone — which is what the off-diagonal rows of the
-- monotonicity lemma say, each of them reflexivity rather than a step.
-- So a value minted at one key says nothing about any other, and the
-- siloing is a theorem rather than a convention about who writes which
-- field.  The stronger EQUALITY that pairs with it, and the strict
-- bound saying a minted identifier can never be handed out twice, are
-- not stated here: nothing consumes them until distinctness itself is,
-- and a fact proven ahead of its assembly is inventory.  Nor is
-- distinctness stated: one table is what makes it SAYABLE, and its only
-- consumer is a well-formedness claim read off a run, which is a tier of
-- its own.  So the route from here is to that tier and not to a
-- statement minted early -- which would reach Main through nothing and
-- be inventory one level up.
--
-- THE CARRIER IS A FUNCTION FROM KEYS AND NOT A RECORD OF FIELDS,
-- WHICH IS WHAT A GENERIC STATEMENT NEEDS.  Three fields would put the
-- key back in the syntax, leaving a statement about an arbitrary
-- counter unable to name the field it is about.  Nothing here needs
-- extensionality: every fact below is pointwise at a key the caller
-- supplies, so each reduces on the two keys' constructors.

data MintKey : Set where
  ordinalᵏ : MintKey                  -- arbitration order among scheduled sources
  sourceᵏ  : MintKey                  -- dynamic sources: colds, deferᵉ bodies
  nodeᵏ    : MintKey                  -- operator node instances
  regᵏ     : MintKey                  -- registration chains, one per subscribing path

record Mint : Set where
  constructor mint
  field counter : MintKey → ℕ

open Mint public using (counter)

-- the seeds the run starts from: ordinals and sources both begin above
-- the scripted slots, which own the identifiers below that bound, while
-- node instances begin at zero and are the run's own.
--
-- AND SOURCES BEGIN ONE HIGHER STILL, LEAVING `n` OWNED BY NOTHING: no
-- slot holds it (they hold `0 ... n-1`) and no mint hands it out (this
-- counter starts above it).  Nothing in the term language can denote a
-- token now, so the gap buys no property; closing it would renumber
-- every source a run produces, which is the only reason it stands.
-- Ordinals are a separate namespace, so that seed is unmoved.
mint-init : ℕ → Mint
mint-init n = mint λ where
  ordinalᵏ → n
  sourceᵏ  → suc n
  nodeᵏ    → 0
  regᵏ     → 0

-- the identifier a mint hands out at a key.  Reading and advancing are
-- separate because a call site names the value it just minted and then
-- says where the counter now stands in terms of THAT.
freshId : MintKey → Mint → ℕ
freshId k m = counter m k

-- WRITE AT A KEY, AND `next` IS THE ONE WRITE THE RUN EVER MAKES.  The
-- setter is the primitive rather than the derived form because an
-- update site spells its new counter with the bound variable it just
-- minted, and a derived-only `next` would force a second reading of the
-- same mint in every such statement.
-- RECOVERY: git show 309d7206^:agda/src/Rx/Mint.agda restores the
--   setter's hit/miss characterisation, the off-key equality and the
--   strict bound saying a minted identifier is never handed out twice
--   -- the four facts a distinctness statement spends, deleted because
--   none of them had a consumer and the statement that would give them
--   one is not written.

setAt : MintKey → ℕ → Mint → Mint
setAt ordinalᵏ v m = mint λ where
  ordinalᵏ → v
  sourceᵏ  → counter m sourceᵏ
  nodeᵏ    → counter m nodeᵏ
  regᵏ     → counter m regᵏ
setAt sourceᵏ  v m = mint λ where
  ordinalᵏ → counter m ordinalᵏ
  sourceᵏ  → v
  nodeᵏ    → counter m nodeᵏ
  regᵏ     → counter m regᵏ
setAt nodeᵏ    v m = mint λ where
  ordinalᵏ → counter m ordinalᵏ
  sourceᵏ  → counter m sourceᵏ
  nodeᵏ    → v
  regᵏ     → counter m regᵏ
setAt regᵏ     v m = mint λ where
  ordinalᵏ → counter m ordinalᵏ
  sourceᵏ  → counter m sourceᵏ
  nodeᵏ    → counter m nodeᵏ
  regᵏ     → v

