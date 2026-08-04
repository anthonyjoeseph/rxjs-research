------------------------------------------------------------------
-- HOW THE INDEX DESCENDS, and what it costs in clauses.
--
-- Chain-Supply-Probe § 2 proved the index CAN descend across a chain
-- edge.  It did not settle how a clause GETS the predecessor to descend
-- to: `chain-index-desc` concludes at `m′` where the clause holds
-- `… ≤ suc m′`, so the clause needs a NAME for `m′`, and an abstract
-- `ops` has none.  Threading `ops` unchanged does NOT work — the source
-- would report at the clause's own index while `op-step` demands the
-- predecessor, and that gap runs the wrong way for `opIterD-mono`.
--
-- So the index must be SPLIT at every clause that recurses.  This probe
-- prices the split.  The rows are arithmetic because that is all they
-- are: `sizeᵉ b` is stuck on a variable at every clause, so a ℕ
-- variable in its place is the same unification problem the real clause
-- presents.  The SHAPES the rows are instantiated at are read off
-- `sizeᵉ`'s own equations (Rx.Exp:463-475):
--
--     mapᵉ f e      suc (sizeᵗ f + sizeᵉ e)          head + source
--     takeᵉ c e     suc (sizeᵗ c + sizeᵉ e)          head + source
--     scanᵉ f z e   suc (sizeᵗ f + sizeᵗ z + sizeᵉ e)  head is itself a sum
--     mergeAllᵉ e   suc (sizeᵉ e)                    headless
--     concatAllᵉ e  suc (sizeᵉ e)                    headless
--     switchAllᵉ e  suc (sizeᵉ e)                    headless
--     exhaustAllᵉ e suc (sizeᵉ e)                    headless
--     μᵉ e          suc (sizeᵉ e)                    headless
--     deferᵉ e      suc (sizeᵉ e)                    headless
------------------------------------------------------------------
module Chain-Descent-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤n+m)
open import Data.Empty using (⊥)

------------------------------------------------------------------
-- § 1.  THE ZERO CLAUSE IS FREE, and it does not need `sizeᵉ` to
-- reduce.  `suc x ≤ zero` is uninhabited by CONSTRUCTOR — neither `z≤n`
-- (wrong first index) nor `s≤s` (wrong second) can build it — so the
-- absurd pattern closes whatever the head term is, stuck or not.  This
-- is what makes the split cost one LINE per chain clause, not a proof.
------------------------------------------------------------------

zero-clause-free : ∀ (x : ℕ) → suc x ≤ zero → ⊥
zero-clause-free x ()

-- and it stays free under the doubled successor an operator clause
-- actually presents (`suc (sizeᵉ (mapᵉ f b))` unfolds to `suc (suc …)`)
zero-clause-doubled : ∀ (hd src : ℕ) → suc (suc (hd + src)) ≤ zero → ⊥
zero-clause-doubled hd src ()

------------------------------------------------------------------
-- § 2.  THE DESCENT ITSELF, one lemma for the whole family.
------------------------------------------------------------------

desc : ∀ (hd src m′ : ℕ) → suc (suc (hd + src)) ≤ suc m′ → suc src ≤ m′
desc hd src m′ (s≤s h) = ≤-trans (s≤s (m≤n+m src hd)) h

-- map / take: the head is a single `sizeᵗ`, spent as `hd` directly
headed-desc : ∀ (szf szb ops′ : ℕ) →
  suc (suc (szf + szb)) ≤ suc ops′ → suc szb ≤ ops′
headed-desc szf szb ops′ h = desc szf szb ops′ h

-- scan: the head is itself a sum, and `+` associating LEFT means
-- `suc (szf + szz + szb)` already IS `suc ((szf + szz) + szb)`, so the
-- same lemma covers it with `hd := szf + szz`.  No second lemma, and
-- no `+-assoc` rewrite at the call site
scan-desc : ∀ (szf szz szb ops′ : ℕ) →
  suc (suc (szf + szz + szb)) ≤ suc ops′ → suc szb ≤ ops′
scan-desc szf szz szb ops′ h = desc (szf + szz) szb ops′ h

-- the HEADLESS constructors present `suc (suc szb)` with no sum at all.
-- `hd := 0` makes `0 + szb` reduce to `szb` definitionally, so the one
-- lemma still applies and the family needs no special case
headless-desc : ∀ (szb ops′ : ℕ) →
  suc (suc szb) ≤ suc ops′ → suc szb ≤ ops′
headless-desc szb ops′ h = desc 0 szb ops′ h

------------------------------------------------------------------
-- § 3.  WHICH CLAUSES ACTUALLY SPLIT, counted off the clause BODIES
-- rather than off the constructor list — the two disagree, and reading
-- the constructor list is how this probe first got it wrong.
--
-- FOUR split, one each:
--   mapᵉ, takeᵉ, scanᵉ   — chain edges, `hd` as in § 2
--   subscribeAll-caps    — the four *All clauses delegate their WHOLE
--                          body to it, so they share its conclusion and
--                          therefore its index; the `op-step` that
--                          consumes the source and the pushed frames sits
--                          inside IT, and so does the split.  Its
--                          hypothesis is about the *All TERM
--                          (`suc (suc (sizeᵉ b)) ≤ ops`), inherited from
--                          its callers verbatim.
--
-- The rest do NOT split, and owe nothing:
--   mergeAll/concatAll/switchAll/exhaustAll — pass index and hypothesis
--                          straight through to the delegate above
--   μᵉ with gas           — a FRESH ENTRY, not a chain edge: it
--                          subscribes `unfoldμ body`, which is LARGER
--                          than `body`, so no descent exists.  That is
--                          exactly why `op-step-mu` consumes it at
--                          `sLvlD` and charges it as one nesting level.
--                          It mints the index at the level's size cap
--                          and pays one `s≤s`.
--   μᵉ out of gas, deferᵉ, input, ofᵉ, emptyᵉ, varᵉ — no recursion at
--                          all (defer PARKS its body as a pending live
--                          source), so `ops` stays abstract and unused
--
-- So the descent is NOT deferrable the way the plumbing memo assumed: a
-- clause that does not split has no predecessor to hand its source, and
-- a weak `∀ {x y} → x ≤ y` hole hides that by accepting any two numbers.
-- The split belongs in the SAME pass that threads the parameter — and
-- once it is there, every index obligation is discharged outright and
-- the hole is not needed at all.
------------------------------------------------------------------
