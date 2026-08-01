-- THE PROOF (in progress) of budget sufficiency: the seeded sync
-- budget never runs dry on a canonical run — the old TERMINATING
-- pragma's claim, decomposed.
--
-- Architecture: an instant-indexed size invariant.  The only things
-- that grow across a run are the runtime values stored in the
-- machine (schedule pendings, scan accumulators, concat queues);
-- everything else is fixed program syntax.  Both fuel demand and
-- stored-value sizes TOWER (chained obs-typed scans exponentiate at
-- each story — the 2026-07-19 attack, see syncBudget's comment in
-- Rx.Evaluator), so the Gas budget is a tower and sizeBudgetAt is
-- its ℕ shadow for the ≤ᵇ-decidable store invariant.
--
--   stBounded? B          — every stored value's size ≤ B (decidable)
--   INV at instant id     — stBounded? (sizeBudgetAt … id)
--   subscribeE-wet        — THE WET CONTRACT (stated; the induction)
--   cascadeGo-wet         — the chain fold stays wet, lands bounded
--   burst-wet (PROVEN)    — the contract at the root + seed-covers
--   cascade-dry (PROVEN)  — latch + fold core + finish, composed
--   drain-dry (PROVEN)    — the fuel loop composes cascades
--   budget-sufficient     — (PROVEN from the above) the whole run
--
-- PROVEN: pop-slots/pop-bounded (inverting schedGo, hoisted for
-- exactly this), the cascade's structural ring (latch/sweep/finish/
-- mono), sync-linearity (plugs-len/occs/inner-len-subΘ), the seed
-- inequality (prod≤3pow/seed-covers — the tower dominance
-- arithmetic at instant 0, discharging the burst cores from the
-- contract), cascade-dry, drain-dry, and the theorem.
--
-- AND THE HOP MEASURE, in full (2026-07-27..29).  dBound's `r` is
-- hopD, a remaining-hop count; the emitted-value invariant the *All
-- clause consumes — every value a burst carries is no deeper than what
-- was subscribed — is proven end to end, with no postulate in its
-- chain: pm-subΘ, hopD-subΘᵉ/ᵗ/ᵗˢ (hopD is AFFINE in a substituted
-- value's depth), hopD-evalWith, hopD-applyFn, hopD-map-emit.  Getting
-- the measure's coefficient right took three machine-checked
-- refutations; see the hop-descent memo below and
-- agda/probe/Hop-Descent-Probe.agda.
--
-- READ THIS FIRST (2026-07-29).  subscribeE-walk has been refuted
-- TWICE in one day, and the second refutation is the live one.
--
--   walk-hyps-absurd    the 2026-07-24 face was VACUOUS: one V served
--                       as both the demand anchor and the store
--                       ceiling, and those two roles contradict.
--   hop-anchor-absurd   the anchor split (demand at the call's own
--                       entry bound capᴱ W E) removes the vacuity but
--                       does NOT close the hop edge: a call and its
--                       hop child then sit at DIFFERENT anchors, the
--                       child's anchor exceeds the parent's d, and the
--                       child's demand exceeds it in turn.
--
-- ROUND 3 IS NOW THE FACE (walk-hyps-round3b + the restated
-- subscribeE-walk), and it COLLAPSED to a single measure on the way in.
-- Anthony's DAG carried a work index G and a separate fuel demand d;
-- both turned out to need the same reset caps at a hop edge, so they
-- stand or fall together and are now one number.  G is the fuel budget,
-- the descent order, and walkCap's index at once, with every cap in it
-- — the s′ reset Ŝ, the r reset R̂, the hop index F — fixed at ENTRY
-- rather than at the ledger.  F is threaded UNCHANGED into the hop
-- child, so parent and child finally read the same index, and the hop
-- edge that killed round 2 is dBound-hop verbatim.
--
-- Two further hypotheses had to move, each forced by its own
-- machine-checked absurdity rather than by taste:
--   · round3-old-ell-absurd — `pathLen κ + d ≤ ℓ` carried the SAME loop
--     routed through ℓ (walkCap's base is (3+Ω)·suc ℓ).  Now
--     `pathLen κ + G ≤ ℓ`.
--   · round3-anchor-indexed-absurd — the work index may not be measured
--     at the anchor, which is what forces `r` off hopDᵉ's V-index.
--
-- NO NEW POSTULATE.  The work index is not a new measure at all — it
-- is dBound at entry caps, so Ŝ, R̂ and F are ordinary ℕ parameters
-- carried like Ψ, Ω and ℓ.  What they cost instead is ONE semantic
-- debt, named by round3b-ledger-reset-absurd: the caps may not be the
-- ledger.  There has to be an entry-determined bound on the size of an
-- observable a run can REACH, or the measure re-anchors at capᴱ and
-- dies as rounds 1 and 2 did.  agda/probe/Frame-Work-Probe.agda is the
-- evidence such a bound exists — the fold count is the source's
-- per-frame payload count, which bottoms out in ofᵉ list lengths — and
-- also the warning about its size: it is an iterated exponential in the
-- nesting depth, so it is a tower and must not be written as anything
-- shaped like `3 + Ω`.
--
-- FIVE POSTULATES REMAIN, and the assembly knot is not among them.
-- They are: the three walk faces (subscribeE-wet, cascadeGo-wet,
-- subscribeE-walk) and the two pieces the BUDGET CLAIM is assembled
-- from (cascadeGo-charge and cascadeGo-deliveries).  3 + 2 = 5, and
-- that is the whole ledger — THE CAPS FACE IS DOWN TO THE TWO
-- DESIGN-OWNED COUNTS and nothing else.
-- frameBlowup is fully defined, and cascadeGo-caps, the cascade
-- bookends and the chain snapshot are all ground.
--
-- THE FIVE EVALUATION OBLIGATIONS ARE GROUND (2026-08-01), which is
-- what the count 10 → 5 is.  mapFrame-caps, scanFrame-caps,
-- evalTms-caps, evalSeed-caps and unfoldμ-caps all had the same
-- difficulty and it had the same answer: an evaluated value is FRESH
-- SYNTAX, so its WIDTH has to come out of its SIZE, and that is
-- affordable exactly because the two per-j increments are different
-- heights — `sizeStep S s = S * suc (2 s)` is multiplicative and
-- `foldStep S w = S ^ suc w` is exponential.  So each member spends its
-- size receipt (evalWith-iterSize / applyFn-iterSize / size-unfoldμ,
-- one fold per syntax node) and then `suc K` MORE folds, K the size cap
-- it just reached, and the width falls out of `wid-iterFold` — the
-- width lemma, one foldStep per node of the RESULT.
--
-- THE WIDTH LEMMA ITSELF IS PROVEN TOO.  `wid-iterFold` bounds every
-- width measure of an expression by `iterFold S (sizeᵉ e) M` off a leaf
-- bound M, by structural induction organised at the MAX of a node's
-- children rather than at their running sum: every non-scanᵉ node
-- spends ONE foldStep and `scanᵉ` spends TWO, funded by the three
-- children it carries.  Eval-Growth-Probe §7 is the clause-by-clause
-- reading that forced that shape — mapᵉ and the *All family fit in one
-- fold, `scanᵉ` does not, its innW clause being M ^ M against a budget
-- of S ^ (1 + M).
--
-- FIVE MEASURES HAD TO GO AT ONCE, because the clauses cross-reference:
-- innW's mapᵉ clause reads pmI, its scanᵉ clause reads outW in an
-- EXPONENT, and pmO's *All clause reads both.  And the arithmetic is
-- two obligations at the children's bound Tb — `2 Tb² ≤ S ^ suc Tb` for
-- one fold and `Tb ^ Tb (3Tb+1) ≤ S ^ suc (S ^ suc Tb)` for two — which
-- both reduce to one engine, a square under an exponential from 4 on.
-- Tb is ≥ 4 at every internal node because one fold off a leaf bound of
-- at least 1 is already S ^ 2.
--
-- AND SO IS THE LEAF.  `input i` has `sizeᵉ = 1` and width measures
-- that descend into the slot telescope, so the side condition has to
-- supply them — which is why slotCaps? gained an innW conjunct
-- (Eval-Growth-Probe §8: a def with pW 0 and innW 3, so pW cannot be
-- made to bound it).  The step that was owed is FUEL: `innWᵉ n sl
-- (input i)` is `innWᵉ (n-1) sl d`, one CONNECT below what the conjunct
-- states, so the leaf wants the measures' monotonicity in the slot
-- fuel — which is `monoᵉ` / `monoᴰᵉ`, proven by the same lexicographic
-- (fuel, syntax) recursion the measures are defined by: only the
-- `input` clauses read the fuel, and there more fuel means a deeper
-- descent, while every other clause is a ⊔, a sum, a product or an
-- exponential of the children, all monotone.
--
-- THE FUEL COLUMN ALSO COST A REDUCTION MODULE.  outWᵉ and innWᵉ take
-- their `input` clauses FIRST, so their case trees split on the fuel at
-- the root and every other clause is STUCK at the variable fuel a
-- structural induction has (dWᵉ takes `input` last for exactly this
-- reason and says so).  Rather than reorder a measure the whole design
-- reads, `Red` unsticks each constructor once — twenty-four two-line
-- equations — and both inductions read them off.
--
-- THE CHAIN-HALF LEMMA IS GONE, REFUTED (2026-08-01).
-- regsSz?-subscribeE asked a FIXED cap C to survive a subscribe, and
-- subscribeE pushes one frame per shell of what it walks, so
-- `suc (pathLen κ) ≤ C` buys room for exactly one of them.
-- Chain-Half-Probe computes a chain of length six out of a tight
-- C = 5.  The ground subscribeE-caps has the same two hypotheses and
-- survives only because it reports at `frameStep (j + j′) c`: each
-- pushed frame is paid for by the j that pushes it.  And capsOK?'s
-- second conjunct IS regsSz?, so the face already hands the chain half
-- back — the postulate had no consumer.
--
-- THE COUNT WENT UP AND THE TREE GOT SMALLER, which is the trade worth
-- making: one opaque face of the whole subscribe machine became three
-- statements about `evalTm` and `unfoldμ` alone — no state, no
-- recursion, no chain — each of which is the SAME tower difficulty the
-- two frame postulates already stand on.
--
-- EVERY COMPANION OF THE CAPS TREE IS GROUND, AND SO IS THE FACE.
-- That is what the repairs of 2026-07-31/08-01 bought:
-- thruConsume-caps, thruWalk-caps, concatDrain-caps, innerFinish-caps
-- and subscribeE-input-caps join subscribeInner-caps, and five
-- postulates leave the tree in one leg.  thruConsume was always
-- provable and its CALLER was not, because thruWalk owed it a joint
-- bound nobody could supply; under the separate pair thruWalk hands
-- down, per payload, the very conjunct it already carries.  The per-op
-- node bookkeeping stores nothing new — merge's counter, switch's
-- current-inner and exhaust's flag carry no payload, and concatAll's
-- queue stores the payload VERBATIM, so `obsCaps?` IS
-- `valCaps? … (obs s)` definitionally and the drained residue goes back
-- into the node with the bound it came out with.  switchAll's cut is
-- the only clause that moves the registry, and it is cutSweep-caps
-- without the node.
--
-- AND THE SLOT EDGE WITH THEM.  subscribeE-input-caps reads its four
-- branches straight off the new side condition: the shared def's size
-- is what sharedSlot-caps asks for, the hot script either answers with a
-- one-shot close or registers (one j), and the cold slot's sync values
-- and resolved async pendings are the two conjuncts slotCaps? carries.
-- THE WIDTH HALF IS FREE ON THE SCRIPTED BRANCHES, and only there: a
-- scripted slot's element type is DATA — the `ok` proof the `scripted`
-- constructor carries IS `T (isData t)` — and both halves of pWᵛ are
-- identically zero on a data type, since only their `obs` clauses read
-- a width at all.  The SHARED branch is not free, since the parked-width
-- repair: a slot def is subscribed whole at a connect and may bury a
-- defer, so slotCaps? carries `pWᵉ n sl d ≤ cWid` there, and capsAt's
-- base pays for it with `slotsPW`.
--
-- subscribeInner-caps is PROVEN — the caps grind's first clause, taken
-- first because it was the most uncertain: the *All edge
-- where the inner observable comes off a burst payload rather than the
-- syntax, so every hypothesis it feeds back into subscribeE-caps has to
-- come from valCaps? and from κ extended by one frame.  It closes.
--
-- stepFrame-caps is PROVEN TOO, and it is the hub: foldPath-caps's
-- `↠` clause is the only place the whole delivery clique spends a j,
-- and this is what it spends it on.  Three of its five clauses are
-- STRUCTURAL and are now ground with their leaves (takeDispatch-caps,
-- innerReact-caps, thruWrap-caps, plus the node ring lookupNode-caps /
-- capsOK?-setNode / cutSweep-caps).  The other two, map-f and scan-f,
-- are where `applyFn` builds a value, and they are the two new
-- postulates.
--
-- THE SHARED-SLOT PAIR IS PROVEN TOO — sharedSlot-caps and
-- sharedConnect-caps, the share's join and its connect.  The def is
-- subscribed under `share-sink i`, a chain of LENGTH ZERO, so
-- subscribeE-caps's chain hypothesis degenerates to `1 ≤ cSize` and
-- costs the clause nothing at all.  The clause that pays for
-- them is register-caps: registering costs exactly one j, the first
-- place in the tree a fold is spent on the cReg dimension, and it needs
-- `1 ≤ Caps.cReg c` — FALSE at cReg c = 0, where cReg (frameStep j c) is
-- 0 at every j and a registry of length one cannot fit.  That condition
-- is threaded unchanged exactly as `2 ≤ Caps.cSize c` is, and supplied
-- at the top by 1≤capsAt-reg, which the recurrence proves.  The delivery
-- clique never registers and does not carry it.
--
-- THE CAPS TREE WAS BLOCKED ON TWO THINGS, BOTH TREE-WIDE.  ONE OF THEM
-- IS RESOLVED (2026-07-31); the other is next.
--
--   (1) THE JOINT BOUND — RESOLVED, BY DELETING IT.  subscribeE-caps
--       demanded `pathLen κ + sizeᵉ b ≤ cSize` while the delivery side
--       carries `pathLen ≤ cSize` and `size ≤ cSize` SEPARATELY, and a
--       chain of length cSize-1 under a payload of size cSize-1 sums to
--       twice the cap.  The obvious repair — thread round 3's ℓ ledger
--       through the delivery clique too, since the WALK face carries
--       `pathLen κ + G ≤ ℓ` end to end — was GATED FIRST, and the gate
--       came back negative.  Joint-Probe measures the joint sum against
--       the TIGHT admissible cSize (the largest quantity capsOK?
--       actually forces cSize to dominate on the state reached) over
--       seventeen families, and it is violated on every one of them —
--       at adm + 1 EXACTLY on every family carrying a scan, because the
--       payload being subscribed IS the stored accumulator, so its size
--       alone already attains the cap and any chain on top overshoots.
--       No constant slackening of a ledger survives that.
--
--       So the JOINT FORM went rather than the delivery side.
--       subscribeE-caps and every subscribe-side companion now ask for
--       `suc (pathLen κ) ≤ cSize` and `sizeᵉ b ≤ cSize` separately —
--       exactly the pair foldPath-caps already splits out of pathSz?.
--       THE INDUCTION STILL CLOSES BY ABSORPTION: each *All hop extends
--       the chain by one from-inner frame and PAYS ONE j for it, and one
--       j at least doubles cSize (frameStep-size-suc: the next level is
--       `S * suc (2 B)`), so the +1 fits under the stepped cap with room
--       — frameStep-chain-suc, three lines.  subscribeInner-caps is the
--       model clause: it now recurses at `suc j` and reports `suc j₂`,
--       and `+-suc` is the entire cost of the change.
--
--   (2) `c` NOT TIED TO `sl` — REPAIRED AT THE TELESCOPE.  capsAt's base
--       is `2 + sizeᵉ e + slotsSize sl`, and the connection used to be
--       gone by the time a companion was stated at an abstract `c`, so
--       nothing let subscribeE-input-caps bound a SLOT DEF or a scripted
--       value.  `slotsCaps? (Caps.cSize c) sl` is that connection as a
--       decidable side condition — every shared def's sizeᵉ and every
--       scripted slot's payload sizes under cSize, as a RECURSIVE walk
--       over the index list for pathSz?'s reason (a non-matching form
--       unfolds on a neutral telescope and OOMs).  It threads unchanged
--       through the whole tree, exactly as `2 ≤ cSize c` and
--       `1 ≤ cReg c` do, because slots never change during a run; and it
--       is supplied by slotsCaps?-capsAt, which the recurrence proves:
--       every payload is a summand of its slot's slotSize, every
--       slotSize a summand of slotsSize, and slotsSize a summand of the
--       base, which iterSize only grows.  What is left is the CLAUSE.
--
-- WHAT THE stepFrame GRIND FOUND, and it is a live problem rather than
-- a gap: `sizeStep S s = S * suc (2 * s)` is size-subΘᵉ's bound, the cost
-- of PLUGGING an env into a template — but applyFn EVALUATES, and
-- evalWith's `caseᵗ` clause extends the environment with the computed
-- scrutinee.  A step function with d nested cases, each pairing the
-- binding above it with itself, turns an input of size 1 into a value
-- of size Θ(2 ^ d) out of syntax of size Θ(d).  The wet family already
-- pays for this in its own currency — stepFrame-scan-wet's receipt is
-- `E * 3 ^ (suc (caseWᵗ fn) * length vals)` — and the caps face has to
-- pay it in j.  The two statements stay TRUE because j′ is existential
-- and iterSize outruns the clause, but the receipt is NOT one fold per
-- frame, and that lands on cascadeGo-charge's `j ≤ D * cSize`.  Flagged,
-- not patched: that is the other half of the budget claim.
--
-- The whole tree is STATED BEFORE ANY CLAUSE IS GROUND, which is the
-- outside-in rule applied at this joint: a change to the shape then
-- changes it here, cheaply, instead of invalidating a pile of finished
-- clause proofs.  Two things follow immediately, and both are the point.
--
-- caps-tick is NOT among the fifteen — it is derived, four lines of
-- assembly over the cascade companions.  And the joint the round was
-- about (does one cascade's fold count FIT the recurrence's iteration
-- budget?) is now a named conjunct of cascadeGo-caps rather than
-- something hidden inside a face — with the probes saying which count it
-- has to fit.  THREE have been refuted there: `cWid * cReg` (J-Budget-
-- Probe), `cWid * cReg * cSize` (Fold-Count-Probe, where nested shares
-- beat it exponentially), and `2 ^ cReg * cSize`, whose middle step
-- Mint-Loop-Probe measured false — a mid-cascade mint puts the path
-- count's R above cReg, and 176 deliveries came out of a 7-registration
-- entry state.  The count is now `2 ^ cReg * 2 ^ cReg * cSize`, and the
-- delivery bound behind it is stated WHOLE — the two-coordinate split
-- was tried and died twice the same session, once at `≤ cSize` (fibre 4
-- against a cSize of 3) and once at `≤ 2 ^ cReg` (fibre 576 against a cap
-- of 512, on a four-level ladder built to test exactly that).  The first
-- coordinate measured fine throughout, which is what makes the split
-- pointless rather than unlucky: D is (something small) times (something
-- the size of D).  cascadeGo-caps itself is no longer postulated — it is
-- the product of the per-delivery charge and the delivery bound — and
-- all three refutations landed on a stated assembly with no clause proof
-- underneath it to lose.  That is what the outside-in rule bought.
--
-- caps-frame, likewise, was refuted as uninstantiable (same-level
-- preservation is false: the subscribe frame itself folds) and split
-- into subscribeE-caps, which reports its growth as a fold count, plus
-- the chain-half lemma any repaired face consumes.  Trading false
-- postulates for true ones is progress; the number is not the metric.
--
-- ROUND 4 (2026-07-29): the caps are defined BY RECURRENCE on the
-- instant, Caps (suc id) = frameBlowup (Caps id), after deepScan refuted
-- every fixed-height shape.  All three components of frameBlowup are
-- defined and gated in State-Blowup-Probe, which measures capsOK?'s own
-- conjuncts off a real run — and in doing so refuted three parts of the
-- first round-4 draft: foldStep (gated against payload counts, too small
-- for the outWᵛ it actually bounds, so it now reads cSize), outWᵉ's
-- scripted clause (0, collapsing every scripted program's width cap),
-- and the base case (which now pays for its own root frame).  Its
-- ITERATION COUNT then took a fourth refutation, from Fold-Count-Probe:
-- nested shares make one cascade's deliveries exponential in the shared-
-- slot count while every Caps component stays linear.  And a fifth, from
-- Mint-Loop-Probe, which measured `j` rather than the deliveries the
-- earlier probes stood in for and found the path count's `2 ^ cReg`
-- middle step false: the count is `2 ^ cReg * 2 ^ cReg * cSize`,
-- delivery paths against subsets of the entry registry squared, times
-- frames per path.  The second exponent is not a second coordinate with
-- a story any more; it is the slack the measurements demand.
-- frameStep and its whole monotonicity toolkit are parametric in the
-- count, so both landed in frameBlowup alone.  Round 3's face is
-- untouched — it was only ever missing something to instantiate Ŝ, R̂, F
-- at.  The two real cores are subscribeE-wet and
-- cascadeGo-wet — the termination content proper: fuel-accounting
-- induction over the subscription machine's clauses (the three
-- decrement edges each consume one hasAtLeast-peel against
-- dBound-μ/-hop/-connect; everything between is structural), and the
-- fold's threading invariant (see cascadeGo-wet's memo).  The third is
-- subscribeE-walk, the joint wet/dry/length face they are stated
-- against.  The reachability cluster is what supplies its three entry
-- caps Ŝ, R̂, F — one measure in three roles, so F cannot drift to an
-- unaudited source (reach-resets, PROVEN, is that wiring).
-- PROVEN 2026-07-29: hopD-size (the hop measure is now
-- derived end to end), and the walk's two bookkeeping companions
-- subscribeE-slots and subscribeE-connected-mono — one joint `Keeps`
-- induction over subscribeE's whole clique.  SPLICED: Verify-Well-Formed imports
-- budget-sufficient from here instead of postulating it.

-- ─── MODULE MAP (2026-07-30) ──────────────────────────────────────
-- This file was one 12,687-line module; a full re-check cost ~22
-- minutes, and that is the dev loop's dominant cost now that the caps
-- face is being ground clause by clause.  It is split along the strata
-- that were already stable.  Agda caches each module's interface, so a
-- clause committed here re-checks only this file.
--
--   .Measures    the measures — gas, dBound, hopD, seed arithmetic,
--                size/fnCap/ofW, INV?/widthOK?, the walk face and its
--                four absurdity records
--   .Keeps-Ring  the shared structural prerequisite: stepping the
--                evaluator keeps the slot telescope and the connected
--                shares (KeepsC), plus the share-boundary facts
--   .Caps-Face   round 4's per-instant cap recurrence, the caps face
--                and its companion tree, caps-tick, reach-resets
--   .Wet         the wet family, the width family, and the theorem
--                (burst-wet, cascade-dry, drain-dry, budget-sufficient)
--
-- .Caps-Face and .Wet are SIBLINGS over .Keeps-Ring, not a stack: the wet
-- family never mentions Caps, so grinding the caps face leaves it (and
-- Verify-Well-Formed, which imports budget-sufficient from .Wet) alone.
--
-- This file is the ACTIVE GRIND, and re-exports all three so every
-- existing importer and probe sees the same names it always did.
-- ──────────────────────────────────────────────────────────────────
module Verify-Budget-Sufficient where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _<_;
                                _⊔_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ⊔-mono-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤; *-assoc;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ;
                                       *-distribʳ-+; *-distribˡ-+; *-identityʳ; <⇒≤;
                                       ^-monoˡ-≤; ^-*-assoc;
                                       ^-distribˡ-+-*; *-mono-≤;
                                       +-monoʳ-≤; *-comm;
                                       m≤m⊔n; m≤n⊔m; ⊔-lub; *-zeroʳ; *-identityˡ;
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; all; any; length;
                                sum; tabulate; concat; map)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                _at_from_as_; EmitKind; subscribe;
                                InstEvent; init; value; close; handoff;
                                complete; exhausted;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                shellsᵉ; shellsᵛ;
                                subΘExp; subΘTm; subΘTms;
                                plugsᵉ; plugsᵗ; plugsᵗˢ;
                                occsᵉ; occsᵗ; occsᵗˢ; varIx;
                                renExp; renTm; renTms; Ren∈; ext∈; ++Ren;
                                wkExp; wkTm; reify;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms;
                                elimDExp; elimDTm; elimDTms;
                                compare∈; _⊟_; ⊟-++ˡ; ⊟-++ʳ; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                oneShotBurst; installNode; setNode; lookupNode;
                                NodeId;
                                root; share-sink; _↠_; Frame; AllOp;
                                map-f; scan-f; take-f; from-inner;
                                thru-outer; Stream;
                                sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                takeVals; takeDispatch; cutThrough; pathHasNode;
                                dropSource; arrSource; chainsOf; cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; mintSource; mintOrdinal; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; splitBurst; retagEvents;
                                mergeBump; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                concatDrain; innerFinish; innerReact;
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize)

open import Verify-Budget-Sufficient.Measures   public
open import Verify-Budget-Sufficient.Keeps-Ring public
open import Verify-Budget-Sufficient.Caps-Face  public
open import Verify-Budget-Sufficient.Wet        public

------------------------------------------------------------------
-- THE ACTIVE GRIND.  Clause work happens here — this module re-checks
-- in seconds where .Caps-Face re-checks in one minute and .Wet in
-- twenty — and MIGRATES into .Caps-Face the moment a cluster closes,
-- because the delivery clique lives there and consumes it.
--
-- Nothing is parked here at the moment: subscribeInner-caps and the
-- whole stepFrame cluster have moved across.
------------------------------------------------------------------
