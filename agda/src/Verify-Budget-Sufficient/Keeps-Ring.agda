-- STRATUM 1b of Verify-Budget-Sufficient: THE KEEPS RING.
--
-- The one structural fact both faces need and neither owns: stepping
-- the evaluator never changes the SLOT TELESCOPE, and never
-- disconnects a share that was already connected.  KeepsC packages the
-- pair, and the ring proves it for every entry point of the walk.
--
-- The wet face uses it for the ledger (sharedConnect-drop /
-- sharedConnect-unconn, the connect measure's strict descent).  The caps
-- face needs it for a different reason: valCaps? and its relatives read
-- widths off Sched.slots, so a bound established before a sub-call has
-- to be transported to that call's POST sched, and slotsEq is the
-- transport.
--
-- It sits in its own module for exactly that reason — a sibling of
-- .Caps-Face and a dependency of .Wet, so that neither face's grind
-- re-checks the other's.  Also here: obs-slot-shared and the two
-- valueless-share lemmas, the walk's share-boundary facts, which are
-- structural and measure-free in the same way.
module Verify-Budget-Sufficient.Keeps-Ring where

open import Data.Bool    using (Bool; true; false; T)
open import Data.Nat     using (zero; suc; _+_; _*_; _≤_; _<_; _≡ᵇ_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; +-identityʳ; *-monoˡ-≤; n≤1+n)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Rx.Prim      using (Tick; Id; Source; InstEmit; _at_from_as_; subscribe; InstEvent; init; close; complete;
  exhausted; Gas; g0; gs; after_,_; hot; cold)
open import Rx.Exp       using (obs; _≟ᵗ_; inputsBelowᵉ; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; Exp; Tm; varᵗ; unit̂; bool̂;
  nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; input; ofᵉ; emptyᵉ; mapᵉ;
  takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; elimGExp;
  elimGTm; elimGTms; elimDExp; elimDTm; elimDTms; compare∈; ⊟-++ˡ; ⊟-++ʳ; unfoldμ; evalTm)
open import Rx.Evaluator using (Sched; EvalSt; memberSource; NodeState; scan-st; take-st; merge-st; concat-st; switch-st;
  exhaust-st; installNode; lookupNode; NodeId; share-sink; _↠_; Frame; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; Stream; takeVals; takeDispatch; Path; subscribeE; stepFrame;
  pushBurst; subscribeInner; subscribeAll; register; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
  splitEvents; splitBurst; switchKill; thruConsume; thruWalk; thruWrap; concatDrain;
  innerFinish; innerReact; sharedConnect; subscribeSharedSlot; burstCompleted; aliveThroughᶠ;
  sameSource)
open import Rx.Slots using (scripted; shared; Slot; Slots)
open import Verify-Budget-Sufficient.Measures using
  (size-renᵉ; sizeᵉ-pos; sucmul; sum2; sum3; unconn; unconn-antitone;
   unconn-insert)

-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.
-- subscribeInner re-enters subscribeE on an observable VALUE o
-- carried by the carrier's burst, so the clause owes a strictly
-- smaller dBound demand for o.  Two routes were stated for it.  One
-- survives; the other was REFUTED and is gone.
--
--   hop-anchored (SURVIVES)  o crossed a SHARE boundary — it came out
--             of slot i's def, whose shells are unrelated to b's.
--             This exits the per-value order entirely and pays with U:
--             the connect edge strictly drops unconn
--             (sharedConnect-unconn, proven below), and o is
--             store-sized, so connect-anchor re-anchors rank ≤ R.
--             Fed to dBound-connect.
--
--   hop-descends (FALSE)  measureE B o ≺ᵛ measureE B b — "o's shells
--             sit inside b's", fed to dBound-hop through rank-mono-≺.
--             This does not hold, at ANY of its three claimed sites; all
--             three die by absurd pattern.

-- WHY IT IS FALSE, in one line: a hop value is a TEMPLATE
-- INSTANTIATED WITH A VALUE, and a template may use its bound
-- variable more than once.  subΘ then copies that value's shells
-- once per occurrence — precisely the plugs summand that
-- subΘ-countsᵗ makes exact — while the carrier holds them once.  So
-- duplication makes the hop's multiset strictly BIGGER and ≺ᵛ points
-- the wrong way.  The probe's witness is
--   mergeAll (map (x ↦ merge (of (x , x))) (of (strm big)))
-- whose hop grows class-4 from 1 to 2.  Note it needs no `caseᵗ` and
-- no exotic typing — an ordinary two-use lambda over an obs-typed
-- source does it.

-- Three things this KILLS, and it is worth being exact about each:
--
--   · the isData restriction does NOT rescue site 2a.
--     It empties the plug when the SOURCE is data, but `caseᵗ` mints
--     an obs-carrying value from a closed term — `inlᵗ (strmᵗ big)` —
--     and binds it to a Θ var the branch then uses twice.  The
--     restriction is still right for its own reason (it removes the
--     scripted-slot regress, see obs-slot-shared) but it does not
--     touch this.
--   · site 2b's guarding premise does not rescue it either.  The
--     probe DISCHARGES that premise and the conclusion still fails.
--   · subscribeE-walk's `r` had to be REPLACED, not merely proven.
--     While it was rank V (measureE V b) the walk handed the *All
--     clause a demand `d` that the clause was to peel with dBound-hop,
--     and with the hop's measure able to exceed the carrier's that
--     peel was unavailable — `d` could simply under-count the walk.
--     SETTLED: `r` is now hopDᵉ V b (phase 2 below).

-- Site 3, μ-unfold, was unaffected and had been proven as unfoldμ-≺;
-- under hopD it is not even an inequality (hopD is EQUAL across an
-- unfold), so the shell version is retired with the rest.

-- WHAT `r` MUST BE INSTEAD is open.  Note first that this is the
-- SAME pattern syncBudget's memo already records as the reason the
-- budget must be a tower at all — "a scanᵉ with an obs-typed
-- accumulator whose template embeds the accumulator twice
-- (acc ↦ mergeAll(of[acc,acc]))", measured.  That memo
-- read the pattern as a demand SIZE problem and towered the budget
-- for it; what went unnoticed is that the same two-use template also
-- destroys the per-hop ORDER the demand was to descend in.  The size
-- half is fine and stays.

-- Ruled out as `r` so far, each against the probe's witness:
--   · the shell multiset — the refutation above
--   · syncSizeᵉ — 16 ↦ 17 across the witness's first hop
--   · sizeᵉ — same, and for the same reason
--   · obs-depth of the subscribed type — CONSTANT along the
--     witness's hop chain (natᵗ, natᵗ, natᵗ), so never strict
--   · strmᵗ-nesting depth — 1, 1, 0: non-strict at the first hop

-- THE CANDIDATE, now stated as Rx.Hop-Depth.hopD: a REMAINING-HOP
-- count — how many *All frames a subscription can still enter.  Two
-- of its clauses were forced by witnesses rather than chosen:
--
--   · mapᵉ composes by `+`, not `⊔`.  A fn's template is applied to
--     the source's values, so the chains CONCATENATE.  Lifting the
--     probe's leaf from `big` to mergeAll (of (strm big)) reads 4 ↦ 2
--     under `+` and 2 ↦ 2 — a tie — under `⊔`.
--   · the source's depth enters scaled by occsᵗ.  A bare `+` did not
--     survive a nested map: subΘ plugs the value at EVERY Θ-var
--     occurrence, so two occurrences either side of a `+` count the
--     plugged depth twice.  Same multiplicity the proven
--     sync-linearity ledger already uses.
--
-- V enters at scanᵉ, where the accumulator is REFOLDED: hopD(accₖ)
-- grows once per folded value — the acc nests k deep after k folded
-- values — so the clause pays (2 + occs)^V,
-- from solving aₖ ≤ F + c·(aₖ₋₁ ⊔ m) at k ≤ V.  hopD is therefore a
-- function of the expression AND the store bound, which is what
-- dBound already anticipates in allowing r ≤ R = suc V ^ suc V.

-- THE DESCENT IS MEASURED, statically and corpus-wide, and it was measured
-- before anything below took a dependency on it.  Statically, all four
-- refutation witnesses descend strictly (2↦1, 2↦1, 2↦1, 4↦2); the scan
-- accumulator's depth is 0,1,2,3 after 0..3 folds, against a clause
-- paying 256 at V ≡ 4; and hopD is EQUAL across a μ unfold, since an
-- unfold substitutes for a Δᵍ variable and those sit only under
-- deferᵉ, which hopD cuts.  So the μ edge is weakly monotone in r and
-- keeps paying with dBound-μ's s — unfoldμ-≺ was NOT assumed to
-- transfer, it is a fact about the shell multiset and says nothing
-- about hopD.

-- Corpus-wide, via the burst probe's numeric hopLog (make
-- the burst harness), testing the emitted-value invariant hopD v ≤ hopD b
-- that the hop edge consumes — with hopD (mergeAllᵉ c) ≡ suc (hopD c),
-- that inequality is exactly what makes a hop strict:
--
--   A  generated, scripted slots     1000 progs   11010 obs   0 viol
--   B  generated, shared slots       1000 progs   17739 obs   0 viol
--   C  directed, 2 slots               19 progs     199 obs   0 viol
--   C₃ directed, 3 slots, 2 shares     36 progs     681 obs   0 viol
--   D  directed, obs into templates    14 progs     172 obs   0 viol
--   D  generated, obs into templates  700 progs   17804 obs   0 viol

-- Re-measured in full after the coefficient became a multiplier: the
-- coefficient sits on both sides of every one of these inequalities,
-- so none of the earlier greens carried over.
--
-- B IS BREADTH-WEIGHTED — 40 seeds × 25 programs at depth 3 — because
-- random SHARE shapes are where a surprise would hide, and a deeper,
-- narrower run buys depth at coverage's expense.
--
-- D CLOSES A STRUCTURAL BLIND SPOT, and it is
-- the only one of the six with a demonstrated ability to see the bug
-- this measure was calibrated against.  A, B, C and C₃ keep every
-- observable inside `ofᵉ (strmᵗ e ∷ …)` with e Θ-CLOSED — the
-- QuickCheck generator's only Fns are natᵗ → natᵗ — so across ~25k hop
-- observations NO program ever substituted an observable into a
-- template.  That is the single mechanism both refutations live in
-- (measureE's duplicated shells; hopD-with-occsᵗ's phantom
-- coefficient), and both were found by adversarial construction rather
-- than by the corpus.  D generates obs-typed templates: an obs-typed
-- source may be wrapped in a mapᵉ whose bound variable is an
-- observable, or a scanᵉ whose accumulator is one.
--
-- D has a DIRECTED half as well, because the generated half could not
-- be trusted alone: reaching the mechanism needs several draws to line
-- up, and 500 generated programs run against the KNOWN-BUGGY occsᵗ
-- coefficient found zero violations.  The directed half forces the
-- conjunction, and measured both ways on identical programs it reads
--
--   occsᵗ (the index-blind count)   130 obs   9 VIOLATIONS
--   the multiplier                  130 obs   0 violations

-- Eight of those eleven programs fire under occsᵗ; the other three are
-- controls whose shapes are correct by construction.  That 9 ↦ 0 is
-- the evidence that the corpus can see the mechanism at all — a corpus
-- that cannot fail on the bug it guards is decoration.

-- Three further directed programs (mulG/mulG₂) carry the SECOND
-- refutation, the one the per-binder count `occs0ᵗ` also failed: an
-- outer template that mentions its observable once and duplicates
-- nothing, over an inner map whose coefficient multiplies whatever
-- lands in its source.  Their machine-checked static counterpart is
-- mul-exceeds (6 against an allowance of 4 under occs0ᵗ) and mul-fits
-- (2 ≤ 2 under the multiplier); the corpus
-- carries the runtime guard.
--
-- (Two of thirty D seeds time out on pathological programs and are
-- excluded from the count above; the self-doubling scan step is not
-- generated at all, since its syntax doubles per folded value.  Its
-- hop behaviour is refl-checked statically instead.)
--
-- selfcheck and wellFormed clean throughout, so the log does not move
-- the evaluator.  The probe's V is capped at 8 (the real V makes
-- (2+occs)^V a bignum per subscribe and OOMs a depth-4 corpus); a
-- smaller V shrinks the PARENT's allowance, so the cap can only make
-- the test harder, never hide a violation.  Sweeping it over 4/8/16
-- gives identical counts and no violations, so the cap is not deciding
-- the answer.

-- AND k ≤ V, the piece whose failure would have reshaped the assembly,
-- turns out to need no measurement at all — it is a CONSEQUENCE of the
-- store invariant this proof already carries, not a new premise:
--
--   · a scan accumulator is a STORED value, and boundedNode above reads
--     exactly `boundedNode B (scan-st v) = sizeᵛ v ≤ᵇ B`, so INV? at
--     instant id already gives sizeᵛ accₖ ≤ sizeBudgetAt e sl id ≡ V;
--   · a fold that DEEPENS the accumulator adds at least one syntax
--     constructor, so k ≤ sizeᵛ accₖ; a fold that does not deepen it
--     does not raise hopD either, so it costs nothing;
--   · hence k ≤ sizeᵛ accₖ ≤ V, which is the scan clause's side
--     condition, discharged from INV? rather than assumed.

-- The margin is not close, and that is why no corpus counter was
-- written for it: V is towerℕ ((4 + size) · suc id), so V ≥ towerℕ 5 ≡
-- 2^65536.  A counter comparing a run's fold count against a number
-- that cannot be computed would be vacuous, not evidence.  (k≤towerℕ,
-- already proven above, is the arithmetic half.)

-- PHASE 2 (the assembly) IS DONE — everything below is stated in terms
-- of hopD and typechecks.  What moved, and what it cost:
--
--   · `r` is hopDᵉ V b, a plain ℕ.  rank ∘ measureE is gone and
--     NOTHING replaces the rank wrapper — hopD is already the number.
--   · `R` is hopR V = (2+V)^((1+V)^(1+V)), replacing (1+V)^(1+V).
--     (Stated as (2+V)^((1+V)²) on the day, when the coefficient was
--     still a count; the exponent became exponential when it became a
--     multiplier.  See the hop-rank-cap memo above.)  hopD's
--     scan clause pays (2+occs)^V per node, so a store-sized def costs
--     one polynomial degree more in the exponent.  prod≤3pow absorbs
--     it inside the SAME three exponential stories — its slack
--     identity closes on (V+2)³ where it used to close on (V+2)², and
--     it now wants 3V ≤ 2^V (V ≥ 4) where it wanted 2V ≤ 2^V (V ≥ 2).
--     Both are free at V = towerℕ (4+sz) ≥ 2^65536.  THE BUDGET TOWER
--     DOES NOT MOVE: a tower of 2s cannot notice a polynomial in an
--     exponent.
--   · the structural edge stopped being a sub-multiset argument.
--     hopD-map/-take/-scan/-all above are one line each.
--   · the μ edge is not even an inequality — see the hopD structural
--     block's header.

-- AND THEN THE HOP EDGE ITSELF WAS REFUTED, same day, before anything
-- was proven — which is what phase 2 existed to find out.

-- The plan was that the hop edge needs no postulate: hopD's *All
-- clauses are literally suc (hopD carrier), so a walk conjunct
--
--     every value a subscription emits has hopD ≤ hopD of what was
--     subscribed                                        (burstHopD?)
--
-- would make the strictness definitional.  That conjunct is FALSE for
-- hopD as written: a program whose allowance is 2 and whose very first
-- emission is 3.
--
-- RECOVERY: `git show 94a5a3c^:agda/probe/Hop-Descent-Probe.agda` restores
--   the witness above as refl-checked numbers plus an absurd pattern,
--   together with mul-exceeds / mul-fits and the four static descent rows
--   this header cites — the apparatus, which is the half worth recovering.

-- WHY, and it is a CALIBRATION bug in one coefficient rather than a
-- failure of the remaining-hop idea.  hopD's mapᵉ clause scales by a
-- coefficient, and the question is what that coefficient counts.
-- Three answers were tried in one day; the first two are refuted by
-- machine-checked witnesses.
--
-- (1) occsᵗ, the index-blind count the sync-linearity ledger uses.
-- It counts EVERY varᵗ in the template.  The coefficient exists to
-- price the SOURCE's value, which is the occurrences of the map's OWN
-- bound variable — those agree on a template and come apart under
-- substitution, since subΘ replaces an OUTER Θ variable by a reified
-- observable carrying its own templates, whose own bound variables
-- occsᵗ then counts as well.  So it inflates although nothing was
-- duplicated.  `plugged` makes that stark with a value of hop depth
-- ZERO: occsᵉ 2, hopD 0, lifting an inner coefficient 2 ↦ 3, and the
-- extra unit multiplies an inner source's hop depth of 1.  The
-- template even DISCARDS the plugged observable (sndᵗ) — the mention
-- alone is enough.
--
-- (2) occs0ᵗ, the same count restricted to the binder's own index.
-- It fixes (1) and stays put under substitution — a plug is Θ-closed,
-- so every variable it brings is compared against an already-bumped
-- index.  It was gated the full way (corpora re-run, static witnesses
-- re-checked) and taken.  It is still wrong, and for a reason that
-- has nothing to do with which variables get counted: it is a COUNT.
-- hopD combines by `⊔` at ofᵉ and pairᵗ, where two mentions cost what
-- one costs; and it MULTIPLIES at mapᵉ, where a plug landing in an
-- inner map's SOURCE is scaled by that inner template's coefficient —
-- a factor no count of outer mentions can see.  `mul-exceeds` is that
-- witness: an outer template that mentions its argument exactly once
-- and duplicates nothing, emitting at hop depth 6 against an
-- allowance of 4.

-- Note (1) and (2) point in OPPOSITE directions: (1) over-prices
-- phantom duplication, (2) under-prices real multiplication.  That is
-- what makes the third answer determined rather than guessed — it is
-- pinned from both sides.

-- Neither is the two-use duplication that killed measureE.  That was
-- real duplication the measure failed to price at all.
--
-- (3) THE ANSWER, and it is what these coefficients always meant: the
-- plug MULTIPLIER, Rx.Hop-Depth.pmᵗ.  Read hopD as a function of one
-- substituted value's depth; it is affine in that depth,
--
--     hopD (e[v]) ≤ hopD e + pm k e · hopD v
--
-- and pm is the slope — the factor hopD's own arithmetic applies along
-- every path from the root to an occurrence of the variable at index
-- k.  pm is hopD's own recursion with two changes: a variable at index
-- k contributes 1 where hopD contributes 0, and the *All frames drop
-- their `suc`, an operator's hop being added to the plug's depth
-- rather than multiplied by it.  Same tree, a different semiring at
-- the leaves — which is exactly the shape phase 3 was told to look
-- for, arrived at from the induction rather than from the analogy.
--
-- pm inherits the substitution-invariance that made occs0 usable, for
-- the same reason and at the same index.  It also reads the witnesses
-- of (1) and (2) correctly in BOTH directions: 1 where occsᵗ said 3,
-- and 1 where occs0ᵗ's ×3 came from primᵗ positions hopD scores as 0.

-- WHAT IT COST, all inside the same three exponential stories: hopR's
-- exponent went from polynomial to exponential (see the hop-rank-cap
-- memo), hopD-size was restated at (2+s)^(V′^s) — the old (2+s)^(V′·s)
-- is FALSE for a multiplier and was retracted rather than left
-- standing — and prod≤3pow's side condition moved from 3V ≤ 2^V (V ≥ 4)
-- to (V+2)² ≤ 2^V (V ≥ 6).  The budget tower did not move.

-- WHAT STOOD THROUGHOUT: the structural facts, the μ edge, `r`'s slot
-- being a plain ℕ, and R being a cap on hopD over store-sized syntax
-- whatever the coefficient.  What is RESTATED: the emitted-value
-- conjunct, burstHopD? above, carried by subscribeE-walk.

-- PHASE 3 IS DISCHARGED.  The conjunct's engine is built
-- and contains no postulate:
--
--   pm-subΘ          a coefficient does not move under substitution
--   hopD-subΘᵉ/ᵗ/ᵗˢ  hopD is AFFINE in the substituted depths, with pm
--                    as the slope — subΘ-countsᵉ/ᵗ's induction clause
--                    for clause, no clause failing to transfer
--   hopD-evalWith    the same at evalWith, which is what frames call
--   hopD-applyFn     the one-value instance
--   hopD-map-emit    the shape the walk's mapᵉ clause applies
--
-- pm is what makes the induction close, and finding it was the point:
-- the mapᵉ clause needs exactly `pm 0 f` from its recursive calls, and
-- no occurrence count is that quantity.  The one statement that had to
-- change along the way was the environment bound — evalWith's caseᵗ
-- pushes the scrutinee's value onto the environment, so the bound is
-- per-position and the slope weighted to match; see hopD-evalWith.
------------------------------------------------------------------

-- THE SHARE BOUNDARY IS THE ONLY input SITE AT AN OBSERVABLE TYPE.
-- `scripted` demands T (isData (obs u)), and isData (obs u) is false, so
-- the constructor is uninhabited here and Agda discharges it with (). This
-- is the whole content of the restriction, in one absurd pattern:
-- before it, this lemma was false and the *All input clause had a case that
-- could not be paid for.  Every hop that reaches a slot is now a connect.
obs-slot-shared : ∀ {n} {Γ : Ctx n} {k u} (s : Slot Γ k (obs u)) →
  Σ (Closed Γ (obs u)) λ d → Σ (T (inputsBelowᵉ k d)) λ ok →
    s ≡ shared d {ok = ok}
obs-slot-shared (shared d {ok = ok}) = d , ok , refl
obs-slot-shared (scripted {ok = ()} _)

-- and the two NON-connecting share paths carry no values: a spent share
-- emits init/close/complete, a live one emits a bare init, both pure
-- bookkeeping.  So no hop originates there, and the input site reduces to
-- sharedConnect alone — the one path that pays with unconn
share-live-novals : ∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
  proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
          (((init s ∷ []) at id from s as subscribe) ∷ [])) ≡ []
share-live-novals s id = refl

share-spent-novals : ∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
  proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
          (((init s ∷ close s exhausted ∷ complete ∷ []) at id from s as subscribe) ∷ []))
    ≡ []
share-spent-novals s id = refl

------------------------------------------------------------------
-- PHASE B — the two structural bookkeeping facts, PROVEN, together.
--
-- The slot telescope is read-only and connectedShares is append-only.
-- Both are one induction over subscribeE's whole clique, so they are
-- proven jointly: `Keeps` bundles them and the clique is walked once.
--
-- What makes the grind mechanical rather than exploratory: across all
-- of Rx/Evaluator.agda, `slots =` appears exactly ONCE (sched-init) and
-- `connectedShares =` exactly TWICE (st-init, and sharedConnect, which
-- PREPENDS toℕ i and touches nothing else).  So every clause is refl,
-- the IH, or the one cons — and the one cons is `member-cons`.
--
-- The clique is subscribeE's own cone: subscribeE, subscribeInner,
-- thruConsume/-Walk/-Wrap, concatDrain, innerFinish, innerReact,
-- stepFrame, pushBurst, subscribeAll, sharedConnect,
-- subscribeSharedSlot, takeDispatch, switchKill.  (foldPath and the
-- delivery clique are NOT in it — the burst leaves subscribeE and is
-- pushed through a FRAME, never re-entered through a path.)
------------------------------------------------------------------

-- a RECORD, not a Σ: `keeps-trans` must solve its middle point by
-- unification, and `EvalSt.connectedShares` is not injective — as a Σ
-- the whole grind below blocked on metas.  And it is
-- indexed by the two FIELDS, not by the two states.  The machine
-- rebuilds a schedule as `record sched { nextNode = suc … }`, which is
-- not definitionally the schedule it came from — so a state-indexed
-- record would not accept the recursive call.  Its slots ARE
-- definitionally the same, and that is all this carries.
record KeepsC {n} {Γ : Ctx n} (sl sl′ : Slots Γ) (cs cs′ : List Source) : Set where
  constructor keeps
  field
    slotsEq  : sl′ ≡ sl
    connMono : ∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true
open KeepsC

Keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
        Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Keeps sched st sched′ st′ =
  KeepsC (Sched.slots sched) (Sched.slots sched′)
         (EvalSt.connectedShares st) (EvalSt.connectedShares st′)

keeps-refl : ∀ {n} {Γ : Ctx n} {sl : Slots Γ} {cs : List Source} → KeepsC sl sl cs cs
keeps-refl = keeps refl (λ s p → p)

keeps-trans : ∀ {n} {Γ : Ctx n} {a b c : Slots Γ} {x y z : List Source} →
  KeepsC a b x y → KeepsC b c y z → KeepsC a c x z
keeps-trans (keeps e₁ m₁) (keeps e₂ m₂) =
  keeps (trans e₂ e₁) (λ s p → m₂ s (m₁ s p))

-- the ONE fact about connectedShares the connect edge needs
member-cons : ∀ (s x : Source) (xs : List Source) →
  memberSource s xs ≡ true → memberSource s (x ∷ xs) ≡ true
member-cons s x xs p with sameSource s x
... | true  = refl
... | false = p

------------------------------------------------------------------
-- the clique, declared first (mirrors the evaluator's own block)
------------------------------------------------------------------

subscribeE-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeE g b κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeInner-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeInner g op allNid κ id now o sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                    (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

thruConsume-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruConsume g op nid κ id now o sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWalk-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruWalk g op nid κ id now os sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWrap-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

concatDrain-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  let r = concatDrain g allNid κ id now q sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                    (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

innerFinish-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  let r = innerFinish g op allNid inst κ id now vals sched st mns
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

innerReact-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

takeDispatch-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  let r = takeDispatch {t = t} {e = e} nid vals fin sched st mns
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

switchKill-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (mv : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  let r = switchKill {t = t} {e = e} mv sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

stepFrame-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = stepFrame g id now f κ vals fin sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

pushBurst-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  let r = pushBurst g id now f κ ems sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeAll-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (ns : NodeState Γ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeAll g op ns b κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = sharedConnect g i d κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-core : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let st₁ = register (toℕ i) κ
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      r   = subscribeE g d (share-sink i) id now sched st₁
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedSlot-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

------------------------------------------------------------------
-- the pure leaves: cut/sweep rewrite live, registry, cancelled and
-- nodes — none of them slots, none of them connectedShares
------------------------------------------------------------------

takeDispatch-keeps nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = keeps refl (λ s p → p)
... | false = keeps refl (λ s p → p)
takeDispatch-keeps nid vals fin sched st nothing                  = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (scan-st _))       = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (merge-st _ _))    = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (concat-st _ _ _)) = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (switch-st _ _))   = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (exhaust-st _ _))  = keeps-refl

switchKill-keeps nothing  sched st = keeps-refl
switchKill-keeps (just v) sched st = keeps refl (λ s p → p)

thruWrap-keeps op nid false vs bs sched st = keeps-refl
thruWrap-keeps mergeᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)      = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (concat-st _ _ _)   = keeps-refl
... | just (switch-st _ _)     = keeps-refl
... | just (exhaust-st _ _)    = keeps-refl
... | nothing                  = keeps-refl
thruWrap-keeps concatᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (concat-st q act _) = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (merge-st _ _)      = keeps-refl
... | just (switch-st _ _)     = keeps-refl
... | just (exhaust-st _ _)    = keeps-refl
... | nothing                  = keeps-refl
thruWrap-keeps switchᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _)   = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (merge-st _ _)      = keeps-refl
... | just (concat-st _ _ _)   = keeps-refl
... | just (exhaust-st _ _)    = keeps-refl
... | nothing                  = keeps-refl
thruWrap-keeps exhaustᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _)  = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (merge-st _ _)      = keeps-refl
... | just (concat-st _ _ _)   = keeps-refl
... | just (switch-st _ _)     = keeps-refl
... | nothing                  = keeps-refl

------------------------------------------------------------------
-- the recursive members
------------------------------------------------------------------

subscribeInner-keeps g0 op allNid κ id now o sched st = keeps-refl
subscribeInner-keeps (gs fuel) op allNid κ id now o sched st =
  subscribeE-keeps fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st

thruConsume-keeps g mergeᵒ nid κ id now o sched st =
  subscribeInner-keeps g mergeᵒ nid κ id now o sched st
thruConsume-keeps {u = u} g concatᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (concat-st {w} q true od) with w ≟ᵗ u
...   | yes refl = keeps-refl
...   | no _     = keeps-refl
thruConsume-keeps {u = u} g concatᵒ nid κ id now o sched st
    | just (concat-st q false od) =
      subscribeInner-keeps g concatᵒ nid κ id now o sched st
thruConsume-keeps g concatᵒ nid κ id now o sched st | nothing = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (scan-st _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (take-st _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (merge-st _ _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (switch-st _ _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (exhaust-st _ _) = keeps-refl
thruConsume-keeps g switchᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
      keeps-trans (switchKill-keeps cur sched st)
                  (subscribeInner-keeps g switchᵒ nid κ id now o
                     (proj₁ (proj₂ (switchKill cur sched st)))
                     (proj₂ (proj₂ (switchKill cur sched st))))
... | just (scan-st _)       = keeps-refl
... | just (take-st _)       = keeps-refl
... | just (merge-st _ _)    = keeps-refl
... | just (concat-st _ _ _) = keeps-refl
... | just (exhaust-st _ _)  = keeps-refl
... | nothing                = keeps-refl
thruConsume-keeps g exhaustᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = keeps-refl
... | just (exhaust-st false od) =
      subscribeInner-keeps g exhaustᵒ nid κ id now o sched st
... | just (scan-st _)       = keeps-refl
... | just (take-st _)       = keeps-refl
... | just (merge-st _ _)    = keeps-refl
... | just (concat-st _ _ _) = keeps-refl
... | just (switch-st _ _)   = keeps-refl
... | nothing                = keeps-refl

thruWalk-keeps g op nid κ id now [] sched st = keeps-refl
thruWalk-keeps g op nid κ id now (o ∷ os) sched st =
  keeps-trans (thruConsume-keeps g op nid κ id now o sched st)
    (thruWalk-keeps g op nid κ id now os
      (proj₁ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st))))
      (proj₂ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st)))))

concatDrain-keeps g allNid κ id now [] sched st = keeps-refl
concatDrain-keeps g allNid κ id now (o ∷ q) sched st
  with proj₁ (proj₂ (proj₂ (proj₂
        (subscribeInner g concatᵒ allNid κ id now o sched st))))
... | true =
      keeps-trans (subscribeInner-keeps g concatᵒ allNid κ id now o sched st)
        (concatDrain-keeps g allNid κ id now q
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g concatᵒ allNid κ id now o sched st))))))
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g concatᵒ allNid κ id now o sched st)))))))
... | false = subscribeInner-keeps g concatᵒ allNid κ id now o sched st

innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (merge-st k od))   = keeps refl (λ s p → p)
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st nothing                  = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (scan-st _))       = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (take-st _))       = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (concat-st _ _ _)) = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (switch-st _ _))   = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (exhaust-st _ _))  = keeps-refl
innerFinish-keeps {s = s} g concatᵒ allNid inst κ id now vals sched st
                  (just (concat-st {w} q act od)) with w ≟ᵗ s
... | yes refl = concatDrain-keeps g allNid κ id now q sched st
... | no _     = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st nothing                = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (scan-st _))     = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (take-st _))     = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (merge-st _ _))  = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _))= keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (switch-st (just c) od))
  with c ≡ᵇ inst
... | true  = keeps refl (λ s p → p)
... | false = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (switch-st nothing od)) = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st nothing                 = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (scan-st _))      = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (take-st _))      = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (merge-st _ _))   = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (concat-st _ _ _))= keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (exhaust-st act od)) = keeps refl (λ s p → p)
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st nothing                 = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (scan-st _))      = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (take-st _))      = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (merge-st _ _))   = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (concat-st _ _ _))= keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (switch-st _ _))  = keeps-refl

innerReact-keeps g op allNid inst κ id now vals sched st false = keeps-refl
innerReact-keeps g op allNid inst κ id now vals sched st true
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = keeps-refl
... | false = innerFinish-keeps g op allNid inst κ id now vals sched st
                (lookupNode allNid (EvalSt.nodes st))

stepFrame-keeps g id now (map-f fn) κ vals fin sched st = keeps-refl
stepFrame-keeps {u = u} g id now (scan-f fn nid) κ vals fin sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (scan-st {w} sacc) with w ≟ᵗ u
...   | yes refl = keeps refl (λ s p → p)
...   | no _     = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | nothing = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (take-st _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (merge-st _ _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (concat-st _ _ _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (switch-st _ _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (exhaust-st _ _) = keeps-refl
stepFrame-keeps g id now (take-f nid) κ vals fin sched st =
  takeDispatch-keeps nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-keeps g id now (from-inner op allNid inst) κ vals fin sched st =
  innerReact-keeps g op allNid inst κ id now vals sched st fin
stepFrame-keeps g id now (thru-outer op nid) κ vals fin sched st =
  keeps-trans (thruWalk-keeps g op nid κ id now vals sched st)
    (thruWrap-keeps op nid fin
      (proj₁ (thruWalk g op nid κ id now vals sched st))
      (proj₁ (proj₂ (thruWalk g op nid κ id now vals sched st)))
      (proj₁ (proj₂ (proj₂ (thruWalk g op nid κ id now vals sched st))))
      (proj₂ (proj₂ (proj₂ (thruWalk g op nid κ id now vals sched st)))))

pushBurst-keeps g id now f κ [] sched st = keeps-refl
pushBurst-keeps g id now f κ (em ∷ ems) sched st =
  keeps-trans
    (stepFrame-keeps g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st)
    (pushBurst-keeps g id now f κ ems
       (proj₁ (proj₂ (proj₂ (proj₂ SF))))
       (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  where
  sp = splitEvents (InstEmit.events em)
  SF = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st

subscribeAll-keeps g op ns b κ id now sched st =
  keeps-trans
    (subscribeE-keeps g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
       (record sched { nextNode = suc (Sched.nextNode sched) })
       (installNode (Sched.nextNode sched) ns st))
    (pushBurst-keeps g id now (thru-outer op (Sched.nextNode sched)) κ
       (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
  where
  SE = subscribeE g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
         (record sched { nextNode = suc (Sched.nextNode sched) })
         (installNode (Sched.nextNode sched) ns st)

-- the connect's payment, hoisted out of the burstCompleted split: both
-- exits return sched₁ and a state whose connectedShares is st₂'s, so the
-- branch is cosmetic and the proof is shared
sharedConnect-core fuel i d κ id now sched st =
  keeps (slotsEq K0)
        (λ s p → connMono K0 s
                   (member-cons s (toℕ i) (EvalSt.connectedShares st) p))
  where
  K0 = subscribeE-keeps fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))

sharedConnect-keeps g0 i d κ id now sched st = keeps-refl
sharedConnect-keeps (gs fuel) i d κ id now sched st
  with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))
... | true  = sharedConnect-core fuel i d κ id now sched st
... | false = sharedConnect-core fuel i d κ id now sched st

sharedSlot-keeps g i d κ id now sched st
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = keeps-refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  = keeps-refl
...   | false = sharedConnect-keeps g i d κ id now sched st

subscribeE-keeps {Γ = Γ} g (input i) κ id now sched st with Sched.slots sched i
... | shared d = sharedSlot-keeps g i d κ id now sched st
... | scripted (hot _) with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = keeps-refl
...   | false = keeps-refl
subscribeE-keeps g (input i) κ id now sched st | scripted (cold sync [])       = keeps-refl
subscribeE-keeps g (input i) κ id now sched st | scripted (cold sync (x ∷ xs)) = keeps-refl
subscribeE-keeps g (ofᵉ ts)  κ id now sched st = keeps-refl
subscribeE-keeps g emptyᵉ    κ id now sched st = keeps-refl
subscribeE-keeps g (mapᵉ f b) κ id now sched st =
  keeps-trans (subscribeE-keeps g b (map-f f ↠ κ) id now sched st)
    (pushBurst-keeps g id now (map-f f) κ
      (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
  where SE = subscribeE g b (map-f f ↠ κ) id now sched st
subscribeE-keeps g (takeᵉ count b) κ id now sched st with evalTm count
... | zero  = keeps-refl
... | suc k =
      keeps-trans (subscribeE-keeps g b (take-f (Sched.nextNode sched) ↠ κ) id now
                    (record sched { nextNode = suc (Sched.nextNode sched) })
                    (installNode (Sched.nextNode sched) (take-st (suc k)) st))
        (pushBurst-keeps g id now (take-f (Sched.nextNode sched)) κ
          (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
      where SE = subscribeE g b (take-f (Sched.nextNode sched) ↠ κ) id now
                   (record sched { nextNode = suc (Sched.nextNode sched) })
                   (installNode (Sched.nextNode sched) (take-st (suc k)) st)
subscribeE-keeps g (scanᵉ f z b) κ id now sched st =
  keeps-trans (subscribeE-keeps g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
                (record sched { nextNode = suc (Sched.nextNode sched) })
                (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st))
    (pushBurst-keeps g id now (scan-f f (Sched.nextNode sched)) κ
      (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
  where SE = subscribeE g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
               (record sched { nextNode = suc (Sched.nextNode sched) })
               (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st)
subscribeE-keeps g (mergeAllᵉ b) κ id now sched st =
  subscribeAll-keeps g mergeᵒ (merge-st 0 false) b κ id now sched st
subscribeE-keeps {u = u} g (concatAllᵉ b) κ id now sched st =
  subscribeAll-keeps g concatᵒ (concat-st {t = u} [] false false) b κ id now sched st
subscribeE-keeps g (switchAllᵉ b) κ id now sched st =
  subscribeAll-keeps g switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE-keeps g (exhaustAllᵉ b) κ id now sched st =
  subscribeAll-keeps g exhaustᵒ (exhaust-st false false) b κ id now sched st
subscribeE-keeps g0 (μᵉ body) κ id now sched st = keeps-refl
subscribeE-keeps (gs fuel) (μᵉ body) κ id now sched st =
  subscribeE-keeps fuel (unfoldμ body) κ id now sched st
subscribeE-keeps g (varᵉ ()) κ id now sched st
subscribeE-keeps g (deferᵉ body) κ id now sched st = keeps-refl

------------------------------------------------------------------
-- the two faces

subscribeE-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (subscribeE g b κ id now sched st)))
    ≡ Sched.slots sched
subscribeE-slots g b κ id now sched st =
  slotsEq (subscribeE-keeps g b κ id now sched st)

subscribeE-connected-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (s : Source) →
  memberSource s (EvalSt.connectedShares st) ≡ true →
  memberSource s
    (EvalSt.connectedShares (proj₂ (proj₂ (subscribeE g b κ id now sched st))))
    ≡ true
subscribeE-connected-mono g b κ id now sched st s =
  connMono (subscribeE-keeps g b κ id now sched st) s

-- THE SHARE BOUNDARY'S PAYMENT, assembled.  sharedConnect adds i to
-- connectedShares before walking the def, so unconn-insert's strict drop is
-- taken at the connect itself; subscribeE-slots keeps the telescope fixed and
-- subscribeE-connected-mono keeps i connected, so unconn-antitone carries the
-- drop across everything the def does on its way up.  Both exit branches
-- return sched₁ and a state whose connectedShares is st₂'s (the completed
-- branch rewrites registry and completedSources only), so the split is
-- cosmetic.  This is the `hop-anchored` disjunct's payment obligation.
-- the drop, on the pieces sharedConnect threads (one clause, so the where
-- block is visible; the burstCompleted split above it is cosmetic)
sharedConnect-drop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)}
  {okd : T (inputsBelowᵉ (toℕ i) dd)} →
  Sched.slots sched i ≡ shared dd {ok = okd} →
  memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
  unconn (Sched.slots (proj₁ (proj₂ (subscribeE fuel d (share-sink i) id now sched
            (register (toℕ i) κ (record st
              { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))))
         (EvalSt.connectedShares (proj₂ (proj₂ (subscribeE fuel d (share-sink i) id now sched
            (register (toℕ i) κ (record st
              { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))))
  < unconn (Sched.slots sched) (EvalSt.connectedShares st)
sharedConnect-drop fuel i d κ id now sched st eqi fresh
  rewrite subscribeE-slots fuel d (share-sink i) id now sched
            (register (toℕ i) κ (record st
              { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
  = ≤-trans (s≤s step≤) step<
  where
  st₁ = register (toℕ i) κ
          (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
  st₂ = proj₂ (proj₂ (subscribeE fuel d (share-sink i) id now sched st₁))
  -- i stays connected through the def's walk
  kept : ∀ s → memberSource s (toℕ i ∷ EvalSt.connectedShares st) ≡ true →
               memberSource s (EvalSt.connectedShares st₂) ≡ true
  kept s h = subscribeE-connected-mono fuel d (share-sink i) id now sched st₁ s h
  step≤ : unconn (Sched.slots sched) (EvalSt.connectedShares st₂)
        ≤ unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st)
  step≤ = unconn-antitone (Sched.slots sched)
            (toℕ i ∷ EvalSt.connectedShares st) (EvalSt.connectedShares st₂) kept
  step< : unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st)
        < unconn (Sched.slots sched) (EvalSt.connectedShares st)
  step< = unconn-insert (Sched.slots sched) (EvalSt.connectedShares st) i eqi fresh

-- and the same drop read off sharedConnect's own result: both exit branches
-- return sched₁ and a state whose connectedShares is st₂'s (the completed
-- branch rewrites registry and completedSources only)
sharedConnect-unconn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)}
  {okd : T (inputsBelowᵉ (toℕ i) dd)} →
  Sched.slots sched i ≡ shared dd {ok = okd} →
  memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
  unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
         (EvalSt.connectedShares
           (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
  < unconn (Sched.slots sched) (EvalSt.connectedShares st)
sharedConnect-unconn fuel i d κ id now sched st eqi fresh
  with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))
... | true  = sharedConnect-drop fuel i d κ id now sched st eqi fresh
... | false = sharedConnect-drop fuel i d κ id now sched st eqi fresh

------------------------------------------------------------------
-- THE SIZE-ELIM LAWS — the third shared prerequisite, moved here for
-- the same reason slotsEq is here: BOTH faces need them and neither
-- owns them.  The wet family reads size-unfoldμ for its μ clause's
-- ledger; the caps face reads it for unfoldμ-caps's size half, which is
-- what the eval cluster's width half is then paid out of.
--
-- Elimination copies the closure at ≤ one var position per node, so
-- size grows by at most the closure's own size.  Same sucmul/sum
-- skeleton as size-subΘᵉ; only elimD's hit clause plants the copy.
------------------------------------------------------------------

lift1 : ∀ {M} → 1 ≤ M → 1 ≤ 1 * M
lift1 {M} h = ≤-trans h (≤-reflexive (sym (+-identityʳ M)))

-- subst on the Δ-index of Exp is transparent to sizeᵉ
size-substᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Δ′ Θ t} (p : Δ ≡ Δ′) (e : Exp Γ Δᵍ Δ Θ t) →
  sizeᵉ (subst (λ ζ → Exp Γ Δᵍ ζ Θ t) p e) ≡ sizeᵉ e
size-substᴱ refl e = refl

-- elimination copies the closure at ≤ one var position per node, so
-- size grows by at most the closure's own size.  Same sucmul/sum
-- skeleton as size-subΘᵉ; only elimD's hit clause plants the copy.
mutual
  size-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    sizeᵉ (elimGExp x cl e) ≤ sizeᵉ e * sizeᵉ cl
  size-elimGᵉ x cl (input i)       = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (ofᵉ ts)        =
    sucmul (sizeᵗˢ ts) (sizeᵉ cl) (size-elimGᵗˢ x cl ts) (sizeᵉ-pos cl)
  size-elimGᵉ x cl emptyᵉ          = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (mapᵉ f e)      =
    sucmul (sizeᵗ f + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ f) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl f) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (takeᵉ c e)     =
    sucmul (sizeᵗ c + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ c) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl c) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (scanᵉ f z e)   =
    sucmul ((sizeᵗ f + sizeᵗ z) + sizeᵉ e) (sizeᵉ cl)
      (sum3 (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl f) (size-elimGᵗ x cl z) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (mergeAllᵉ e)   =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (concatAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (switchAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (exhaustAllᵉ e) =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (μᵉ e)          =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ (there x) cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (varᵉ y)        = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (deferᵉ e)      =
    sucmul (sizeᵉ e) (sizeᵉ cl)
      (≤-trans (≤-reflexive (size-substᴱ (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e)))
               (size-elimDᵉ (∈-++⁺ˡ x) cl e))
      (sizeᵉ-pos cl)

  size-elimDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    sizeᵉ (elimDExp x cl e) ≤ sizeᵉ e * sizeᵉ cl
  size-elimDᵉ x cl (input i)       = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (ofᵉ ts)        =
    sucmul (sizeᵗˢ ts) (sizeᵉ cl) (size-elimDᵗˢ x cl ts) (sizeᵉ-pos cl)
  size-elimDᵉ x cl emptyᵉ          = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (mapᵉ f e)      =
    sucmul (sizeᵗ f + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ f) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl f) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (takeᵉ c e)     =
    sucmul (sizeᵗ c + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ c) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl c) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (scanᵉ f z e)   =
    sucmul ((sizeᵗ f + sizeᵗ z) + sizeᵉ e) (sizeᵉ cl)
      (sum3 (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl f) (size-elimDᵗ x cl z) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (mergeAllᵉ e)   =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (concatAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (switchAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (exhaustAllᵉ e) =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (μᵉ e)          =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (varᵉ y)        with compare∈ x y
  ... | inj₁ refl =
    ≤-trans (≤-reflexive (size-renᵉ (λ ()) (λ ()) (λ ()) cl))
            (≤-reflexive (sym (+-identityʳ (sizeᵉ cl))))
  ... | inj₂ y′   = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (deferᵉ e)      =
    sucmul (sizeᵉ e) (sizeᵉ cl)
      (≤-trans (≤-reflexive (size-substᴱ (⊟-++ʳ x) (elimDExp (∈-++⁺ʳ _ x) cl e)))
               (size-elimDᵉ (∈-++⁺ʳ _ x) cl e))
      (sizeᵉ-pos cl)

  size-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    sizeᵗ (elimGTm x cl tm) ≤ sizeᵗ tm * sizeᵉ cl
  size-elimGᵗ x cl (varᵗ y)      = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl unit̂          = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (bool̂ _)      = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (nat̂ _)       = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (pairᵗ a b)   =
    sucmul (sizeᵗ a + sizeᵗ b) (sizeᵉ cl)
      (sum2 (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimGᵗ x cl a) (size-elimGᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (fstᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimGᵗ x cl p) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (sndᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimGᵗ x cl p) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (inlᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (inrᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (caseᵗ s l r) =
    sucmul ((sizeᵗ s + sizeᵗ l) + sizeᵗ r) (sizeᵉ cl)
      (sum3 (sizeᵗ s) (sizeᵗ l) (sizeᵗ r) (sizeᵉ cl)
            (size-elimGᵗ x cl s) (size-elimGᵗ x cl l) (size-elimGᵗ x cl r))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (ifᵗ c a b)   =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (sizeᵉ cl)
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimGᵗ x cl c) (size-elimGᵗ x cl a) (size-elimGᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (primᵗ _ a)   =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (strmᵗ e)     =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)

  size-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    sizeᵗ (elimDTm x cl tm) ≤ sizeᵗ tm * sizeᵉ cl
  size-elimDᵗ x cl (varᵗ y)      = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl unit̂          = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (bool̂ _)      = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (nat̂ _)       = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (pairᵗ a b)   =
    sucmul (sizeᵗ a + sizeᵗ b) (sizeᵉ cl)
      (sum2 (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimDᵗ x cl a) (size-elimDᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (fstᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimDᵗ x cl p) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (sndᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimDᵗ x cl p) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (inlᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (inrᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (caseᵗ s l r) =
    sucmul ((sizeᵗ s + sizeᵗ l) + sizeᵗ r) (sizeᵉ cl)
      (sum3 (sizeᵗ s) (sizeᵗ l) (sizeᵗ r) (sizeᵉ cl)
            (size-elimDᵗ x cl s) (size-elimDᵗ x cl l) (size-elimDᵗ x cl r))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (ifᵗ c a b)   =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (sizeᵉ cl)
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimDᵗ x cl c) (size-elimDᵗ x cl a) (size-elimDᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (primᵗ _ a)   =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (strmᵗ e)     =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)

  size-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    sizeᵗˢ (elimGTms x cl ts) ≤ sizeᵗˢ ts * sizeᵉ cl
  size-elimGᵗˢ x cl []       = lift1 (sizeᵉ-pos cl)
  size-elimGᵗˢ x cl (y ∷ ys) =
    sum2 (sizeᵗ y) (sizeᵗˢ ys) (sizeᵉ cl)
         (size-elimGᵗ x cl y) (size-elimGᵗˢ x cl ys)

  size-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    sizeᵗˢ (elimDTms x cl ts) ≤ sizeᵗˢ ts * sizeᵉ cl
  size-elimDᵗˢ x cl []       = lift1 (sizeᵉ-pos cl)
  size-elimDᵗˢ x cl (y ∷ ys) =
    sum2 (sizeᵗ y) (sizeᵗˢ ys) (sizeᵉ cl)
         (size-elimDᵗ x cl y) (size-elimDᵗˢ x cl ys)

-- the μ-copy size bound: unfolding plants (μᵉ body) at the body's
-- global-var positions, so the copy is at most sizeᵉ (μᵉ body) squared
size-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  sizeᵉ (unfoldμ body) ≤ sizeᵉ (μᵉ body) * sizeᵉ (μᵉ body)
size-unfoldμ body =
  ≤-trans (size-elimGᵉ (here refl) (μᵉ body) body)
          (*-monoˡ-≤ (sizeᵉ (μᵉ body)) (n≤1+n (sizeᵉ body)))
