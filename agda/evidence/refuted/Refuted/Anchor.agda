-- ══════════════════════════════════════════════════════════════════
-- THE ROUND-3 ANCHOR: retired vocabulary, and why
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks — unlike a
-- prose note, which decays silently.
--
-- THIS TREE IS OUTSIDE `agda/src` ON PURPOSE (Anthony, 2026-08-18).
-- Keeping a dead route in `src` forces `src` to keep whatever machinery
-- makes the route STATE-able, and that machinery is otherwise deletable:
-- these two files held seven definitions alive in Measures for no other
-- reason.  So refutations live here, are checked by `make refuted`, and
-- are NOT subject to the wiring law — nothing in `src` may import them.
-- They do not change, so `src` refers to them in COMMENTS (`-- REFUTED:`).
-- ══════════════════════════════════════════════════════════════════
module Refuted.Anchor where

open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; <-≤-trans; *-monoˡ-≤; *-monoʳ-≤; m≤m+n; m≤n+m; n≤1+n;
  ^-monoʳ-≤; *-identityʳ; <⇒≤; ^-monoˡ-≤; *-identityˡ; <-irrefl)
open import Data.Empty   using (⊥)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Relation.Binary.PropositionalEquality
  using (refl; sym)
open import Rx.Prim      using (_at_from_as_; g0)
open import Rx.Prim using (_at_from_as_; g0)

open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; capᴱ; dBound; hopR; k≤3^k; n<2^n)

-- THE RECURRENCE-CLOSED CAP.  Per-clause obligations (c ≤ 4 own
-- mints; oneShotBurst events ≤ 3+Ω; hops ≤ the child's burstLen,
-- each a fresh subtree at a strictly smaller descent; per-value
-- fold/hop sites ≤ frame crossings ≤ ℓ) all close under
--   walkCap(d)² · base + walkCap(d-1) + c ≤ walkCap(suc d)
-- because the exponent triples per descent step: β^(2·3^d + 2) ≤
-- β^(3^(suc d)) once 3^d ≥ 2, and the d ∈ {0,1} cases are
-- degenerate (a demand that small admits no child subtree).
walkCap : (Ω ℓ d : ℕ) → ℕ
walkCap Ω ℓ d = ((3 + Ω) * suc ℓ) ^ (3 ^ d)

------------------------------------------------------------------
-- ROUND 3's VOCABULARY (2026-07-29): one shared anchor, one d-free
-- work index.  RETIRED WITH THE LEDGER WALK (2026-08-13, module
-- header); what is left is what the four absurds below consume.
------------------------------------------------------------------

-- THE ANCHOR — ONE object in all three roles the face needs: the
-- demand's anchor, the s′ reset bound at hop edges, and the receipt's
-- ceiling.  Rounds 1 and 2 needed two objects for those roles and died
-- of the gap between them.  This one can serve all three because
-- walkCap's index here is G, which is d-free, so nothing about the
-- anchor depends on the demand it anchors.
anchorᴬ : (Ψ W Ω ℓ G E : ℕ) → ℕ
anchorᴬ Ψ W Ω ℓ G E = capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G))

------------------------------------------------------------------
-- THE JOINT WALK FACE (2026-07-24): wet half, dry half, and the
-- length ledger in ONE contract — memo (5)(b)'s "state them
-- together".  Settled design points:
--   · d is an UPPER bound on the call's dBound demand (≤, not ≡):
--     every conjunct is monotone in d, so callers weaken freely
--     and clause proofs descend by exactly one per edge.
--   · THE CEILING capᴱ W (E·3^(suc Ψ·walkCap)) ≤ V ties the
--     halves together: the receipt conjunct E′ ≤ E·3^(…) keeps
--     every mid-walk ledger position under it, so every mid-walk
--     store and emission is sized ≤ V — exactly what dBound-hop's
--     s′ ≤ V reset and the rank machinery's class caps need at
--     hop edges.  V is the caller's DESCENT ANCHOR — at the root
--     instantiation, the landing budget sizeBudgetAt (suc id),
--     where the ceiling becomes memo (5)'s story-count
--     arithmetic.  No fixed V survives as a store INVARIANT
--     (folds outgrow it) — it survives as a CEILING on the
--     receipt, which is why the receipt conjunct is load-bearing
--     and not instrumentation.
--   · the dry half consumes hasAtLeast (suc d) peels against
--     dBound-μ/-hop/-connect; hop targets get their rank drop
--     from the shell hop machinery and their width bound from W11
--     applied to the child call (W11 deleted 2026-08-21 with the
--     retired walk; this records the contract, not live machinery).
--   · subsumption: subscribeE-walkS below is this contract's
--     store-half projection — its ground clauses lift conjunct by
--     conjunct in the grind.  The two cores at the bottom stay
--     until the landing composes (𝔉 into the boundary).
------------------------------------------------------------------

-- the empty gas cannot fund a peel — the walk's base-case
-- refutation, and the only piece of the retired walk apparatus
-- that says something about the machine rather than about the
-- ledger it was stated over.
g0-hasAtLeast-absurd : ∀ {G} → g0 hasAtLeast suc G → ⊥
g0-hasAtLeast-absurd ()

------------------------------------------------------------------
-- REFUTATION 1 (the statement): the 2026-07-24 face was vacuous.
--
--   (demand)  dBound V (hopR V) U (hopDᵉ V b) (syncSizeᵉ b) ≤ d
--   (ceiling) capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d))       ≤ V
--
-- (demand) puts d ≥ suc V as soon as the call has ONE unconnected
-- share or ONE remaining hop, since dBound V R U r s expands to
-- s + suc V * (r + suc R * U).  (ceiling) puts V above a tower in d:
-- walkCap Ω ℓ d ≥ 3^(3^d) ≥ d, and capᴱ W X ≥ 2^X > X.  d ≥ suc V and
-- V > d.  walk-hyps-absurd is the proof.  The contrast that showed the
-- SPLIT anchor makes the same constraints satisfiable
-- (`walk-hyps-splitAnchor`) is deleted — REFUTATION 2 below then killed
-- the split too, so the satisfiability receipt pointed at a route that
-- is itself dead.  RECOVERY: git show c87c91a.
------------------------------------------------------------------

-- (demand) alone already puts d past V, given one share or one hop
sucV≤d : ∀ (V R U r s d : ℕ) → 1 ≤ r + suc R * U →
  dBound V R U r s ≤ d → suc V ≤ d
sucV≤d V R U r s d 1≤ h =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (suc V))))
                   (*-monoʳ-≤ (suc V) 1≤))
          (≤-trans (m≤n+m (suc V * (r + suc R * U)) s) h)

-- walkCap's base is ≥ 3 and its exponent is 3^d, so it dominates d
d≤walkCap : ∀ (Ω ℓ d : ℕ) → d ≤ walkCap Ω ℓ d
d≤walkCap Ω ℓ d =
  ≤-trans (k≤3^k d)
    (≤-trans (^-monoʳ-≤ 3 (k≤3^k d))
             (^-monoˡ-≤ (3 ^ d) 3≤β))
  where
  3≤β : 3 ≤ (3 + Ω) * suc ℓ
  3≤β = ≤-trans (m≤m+n 3 Ω)
          (≤-trans (≤-reflexive (sym (*-identityʳ (3 + Ω))))
                   (*-monoʳ-≤ (3 + Ω) (s≤s z≤n)))

-- the cap ITSELF sits under the ceiling's exponent argument.  Stated
-- separately from d≤walkArg because round 3 needs it at an index that
-- is NOT the cap's own — the growth index and the demand come apart
walkCap≤walkArg : ∀ (Ψ Ω ℓ G E : ℕ) → 3 ≤ E →
  walkCap Ω ℓ G ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G)
walkCap≤walkArg Ψ Ω ℓ G E 3≤E =
  ≤-trans (k≤3^k w) (≤-trans (^-monoʳ-≤ 3 w≤Ψw) E-mul)
  where
  w : ℕ
  w = walkCap Ω ℓ G
  w≤Ψw : w ≤ suc Ψ * w
  w≤Ψw = ≤-trans (≤-reflexive (sym (*-identityˡ w)))
                 (*-monoˡ-≤ w {1} {suc Ψ} (s≤s z≤n))
  E-mul : 3 ^ (suc Ψ * w) ≤ E * 3 ^ (suc Ψ * w)
  E-mul = ≤-trans (≤-reflexive (sym (*-identityˡ (3 ^ (suc Ψ * w)))))
                  (*-monoˡ-≤ (3 ^ (suc Ψ * w)) {1} {E}
                             (≤-trans (s≤s z≤n) 3≤E))

-- so does the ceiling's whole exponent argument
d≤walkArg : ∀ (Ψ Ω ℓ d E : ℕ) → 3 ≤ E →
  d ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ d)
d≤walkArg Ψ Ω ℓ d E 3≤E =
  ≤-trans (d≤walkCap Ω ℓ d) (walkCap≤walkArg Ψ Ω ℓ d E 3≤E)

-- and so does the cap's own BASE — the length ledger's ℓ.  This is
-- what makes the d-indexed length hypothesis refutable under a shared
-- anchor (round3-old-ell-absurd below)
ℓ≤walkCap : ∀ (Ω ℓ G : ℕ) → ℓ ≤ walkCap Ω ℓ G
ℓ≤walkCap Ω ℓ G = ≤-trans (n≤1+n ℓ) (≤-trans sucℓ≤β β≤β^)
  where
  β : ℕ
  β = (3 + Ω) * suc ℓ
  sucℓ≤β : suc ℓ ≤ β
  sucℓ≤β = ≤-trans (≤-reflexive (sym (*-identityˡ (suc ℓ))))
                   (*-monoˡ-≤ (suc ℓ) {1} {3 + Ω} (s≤s z≤n))
  1≤3^G : 1 ≤ 3 ^ G
  1≤3^G = ^-monoʳ-≤ 3 {0} {G} z≤n
  β≤β^ : β ≤ β ^ (3 ^ G)
  β≤β^ = ≤-trans (≤-reflexive (sym (*-identityʳ β)))
                 (^-monoʳ-≤ β {1} {3 ^ G} 1≤3^G)

-- THE REFUTATION.  Instantiate at any real call: U = unconn of a
-- program with a shared slot (≥ 1 at the root, where connectedShares
-- is []), or r = hopDᵉ V b of any *All (≥ 1 by hopD's own suc).
walk-hyps-absurd : ∀ (Ψ W Ω V ℓ R U r s d E : ℕ) →
  3 ≤ E →
  1 ≤ r + suc R * U →
  dBound V R U r s ≤ d →
  capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)) ≤ V →
  ⊥
walk-hyps-absurd Ψ W Ω V ℓ R U r s d E 3≤E 1≤ dem ceil =
  <-irrefl refl
    (≤-trans (≤-trans (sucV≤d V R U r s d 1≤ dem)
                      (d≤walkArg Ψ Ω ℓ d E 3≤E))
             (≤-trans (<⇒≤ (n<2^n X))
                      (≤-trans (^-monoˡ-≤ X (s≤s (s≤s z≤n))) ceil)))
  where
  X : ℕ
  X = E * 3 ^ (suc Ψ * walkCap Ω ℓ d)

------------------------------------------------------------------
-- REFUTATION 2 (the hop edge): THE SPLIT ANCHOR DOES NOT CLOSE
-- EITHER.  Probed 2026-07-29 BEFORE grinding any clause, per the
-- outside-in rule — the vacuity had already shown once that this face
-- can look grind-ready and be uninstantiable, so the most uncertain
-- piece goes first.  IT REFUTES.
--
-- With per-call anchoring, each call measures its demand at its OWN
-- entry bound.  The outer call sits at A = capᴱ W E with demand ≤ d.
-- It re-enters (subscribeInner) on an inner observable o drawn from
-- the carrier's burst.  By then the ledger has moved to E″, and the
-- face's own receipt conjunct permits E″ anywhere up to
-- E * 3 ^ (suc Ψ * walkCap Ω ℓ d).  So the inner call's anchor is
-- A″ = capᴱ W E″, its demand is dBound A″ (hopR A″) U″ r″ s″, and the
-- hop edge owes  suc (inner demand) ≤ d.
--
-- That is impossible at the ledger the face itself permits:
--
--   · d  ≤ E″                    (d≤walkArg — the work bound dominates d)
--   · E″ <  capᴱ W E″ ≡ A″       (n<2^n, then base 2 ≤ 2 + 2W)
--   · suc A″ ≤ inner demand      (sucV≤d — ONE inner share or ONE
--                                 remaining hop is enough)
--
-- so A″ < d ≤ E″ < A″.  Absurd.
--
-- WHAT THIS MEANS.  The split did not remove the circle; it MOVED it,
-- from between the face's two hypotheses to between a call and its own
-- hop child.  Both times the mechanism is identical: an anchor that
-- tracks the store, a demand monotone in that anchor, and a store that
-- grows super-exponentially in the demand.  Renaming the anchor cannot
-- fix a loop whose three edges are all still present.
--
-- Note the refutation needs NO facts about hopD at all — not its scan
-- clause, not its monotonicity in the anchor.  It is pure dBound /
-- capᴱ / walkCap arithmetic, so no recalibration of the hop measure
-- can escape it.  (Anchor-monotonicity of hopD would make it worse,
-- not better: hopDᵉ A″ o ≥ hopDᵉ A o, so the inner r″ is inflated too.)
--
-- WHAT WOULD ESCAPE IT, stated so the next session does not re-derive
-- it: the anchor must be SHARED across the whole walk (so the hop edge
-- never transports between two different anchors) AND
-- ENTRY-DETERMINED (so it does not depend on d).  That is exactly what
-- the ceiling was trying and failing to be — it was shared, but it was
-- indexed by walkCap Ω ℓ d, which is d-dependent, and that is the
-- edge that closed the loop.  So the change is not to the anchor at
-- all: it is to the GROWTH CAP.  walkCap's index must become a
-- d-free measure of the walk's work — the hop depth and the syntax
-- both bound it, and both are fixed at entry — after which one shared
-- anchor capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)) with G entry-
-- determined serves as the demand anchor, the s′ reset bound, and the
-- store ceiling at once, with no circularity.
--
-- That is a contract change beyond the anchor split, so it is NOT
-- taken here.
------------------------------------------------------------------

hop-anchor-absurd : ∀ (Ψ W Ω ℓ E d U″ r″ s″ : ℕ) →
  3 ≤ E →
  -- the inner call is nontrivial: one unconnected share or one hop
  1 ≤ r″ + suc (hopR (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)))) * U″ →
  -- what the hop edge owes, at the largest ledger the receipt permits
  suc (dBound (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)))
              (hopR (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d))))
              U″ r″ s″) ≤ d →
  ⊥
hop-anchor-absurd Ψ W Ω ℓ E d U″ r″ s″ 3≤E 1≤ owed =
  <-irrefl refl
    (≤-trans A″<d (≤-trans (d≤walkArg Ψ Ω ℓ d E 3≤E) (<⇒≤ E″<A″)))
  where
  E″ : ℕ
  E″ = E * 3 ^ (suc Ψ * walkCap Ω ℓ d)
  A″ : ℕ
  A″ = capᴱ W E″

  -- the inner demand already exceeds its own anchor, and d exceeds it
  A″<d : suc A″ ≤ d
  A″<d = ≤-trans (n≤1+n (suc A″))
           (≤-trans (s≤s (sucV≤d A″ (hopR A″) U″ r″ s″
                            (dBound A″ (hopR A″) U″ r″ s″) 1≤ ≤-refl))
                    owed)

  -- but the anchor is exponential in the ledger, which already
  -- dominates d
  E″<A″ : suc E″ ≤ A″
  E″<A″ = ≤-trans (n<2^n E″) (^-monoˡ-≤ E″ (s≤s (s≤s z≤n)))

------------------------------------------------------------------
-- ROUND 3 (the candidate), PROBED BEFORE RESTATING ANYTHING.  Two
-- refutations in two days, both statement-level, both found by writing
-- the witness down rather than by grinding a clause.  The third shape
-- gets the same treatment first.
--
-- THE WITNESS DAG.  Every parameter must be definable in ONE acyclic
-- order, each from entry data and previously-defined parameters only:
--
--   G := an entry measure (root syntax + slot telescope + Ω)
--   ℓ := f G                                    -- entry path budget
--   A := capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
--   d := dBound A (hopR A) U r s                -- huge; fuel is free
--
-- A is ONE object in all three roles round 2 needed two for: the
-- demand anchor, the s′ reset bound at hop edges, and the receipt's
-- ceiling.  It can be, precisely because walkCap's index is now G and
-- not d, so nothing to the right of the arrow feeds anything left of
-- it.  The DAG receipt that carried that order in its type
-- (`walk-hyps-round3b`, deleted with the walk — git show c87c91a)
-- quantified them exactly so: Ŝ, R̂, U, r, s are
-- universally quantified — fixed before anything store-shaped exists —
-- and G is existentially produced from them, ℓ from G.  A statement of
-- that shape cannot hide a cycle.
--
-- WHY IT IS NOT TRIVIALLY TRUE, since "pick d enormous" is exactly
-- what round 2 could not do: there the hop child re-anchored at
-- capᴱ W E″ for the GROWN ledger, and E″'s permitted range was itself
-- indexed by d — so enlarging d enlarged the child's anchor faster,
-- and suc (child demand) ≤ d was unreachable at EVERY d.  Here the
-- child measures at the same A, so the hop edge is dBound-hop
-- verbatim.  Conjunct (4) is the one that died in round 2.
--
-- AND TWO CONDITIONAL REFUTATIONS, which is the probe's real yield:
-- the DAG is satisfiable but only after two further contract edits,
-- and each is forced by a machine-checked absurdity, not by taste.
--
--   (a) round3-old-ell-absurd — THE LENGTH HYPOTHESIS MUST BE
--       RESTATED d-FREE.  `pathLen κ + d ≤ ℓ` forces ℓ ≥ d, the
--       demand forces d ≥ suc A, and A is a tower in ℓ (ℓ≤walkCap:
--       walkCap's own base is (3 + Ω) * suc ℓ).  So ℓ ≥ tower ℓ —
--       the identical three-edge loop, routed through ℓ instead of
--       through the anchor.  Sharing the anchor does NOT fix this;
--       only restating the hypothesis does.  It becomes
--       `pathLen κ + G ≤ ℓ`: path growth paid for by G-derived work,
--       not by remaining fuel.  Conjunct (7) is its preservation
--       across a frame crossing, and it mentions no d at all.
--
--   (b) round3-anchor-indexed-absurd — G MUST BE MEASURED WITH AN
--       ANCHOR-FREE HOP DEPTH.  If the work index has to dominate any
--       quantity that is itself ≥ the anchor, then G ≥ capᴱ W X while
--       X ≥ walkCap Ω ℓ G ≥ G, and the loop is back.  This is not
--       hypothetical: hopDᵉ's scan clause is (2 + pmᵗ V 0 f) ^ V * …,
--       whose EXPONENT is the store anchor, so a single scanᵉ puts the
--       hop depth above the anchor.  Keep hopD's V-index and round 3
--       dies exactly where rounds 1 and 2 did.
--
-- So the load-bearing edit is NOT walkCap's index — that is a
-- consequence.  It is hopD's scan-clause allowance, which must move
-- off the store bound and onto an entry-determined frame-emission
-- bound.  The premises for that are in the machine already: per-node
-- sync emissions are ≤ 3 + Ω (widthOK? / ofWᵉ / pathΩ? carried it,
-- and only ofWᵉ is still in the tree);
-- widths are syntax-fixed (strmᵗ is Tm's only obs introduction and
-- substitution plugs into list elements, never appends); and a sync
-- frame has no μ feedback (a μ-bound variable lives in Δᵍ and is
-- reachable only under deferᵉ, Rx/Exp.agda:76-79, which crosses a
-- tick).  A scan therefore folds at most as many times per frame as
-- emissions arrive, and that count is entry data.
--
-- WHAT WAS STILL UNCHECKED HERE — that an entry-determined G really
-- does bound the frame work — is semantic, not arithmetic, and it has
-- since been measured: Frame-Work-Probe (DELETED; git history).  It reports
-- YES, with one correction to the expected shape.  The fold count is
-- the source's per-frame PAYLOAD count (for a literal source, the ofᵉ
-- list's length), so it is entry-determined; but each *All nesting
-- level exponentiates it, so G is an iterated exponential in the
-- nesting depth rather than a polynomial in the syntax.  That does not
-- threaten anything above — anchorᴬ is DEFINED from G and dwarfs it at
-- any size — but it is what the entry caps have to be written as.
------------------------------------------------------------------



-- (c) AND THE PRICE OF THE COLLAPSE, which is the round's whole
-- remaining debt: the reset caps may not be the LEDGER.  If the only
-- available bound on a hop child's syncSize is the store ceiling — that
-- is, if there is no entry-determined cap on the size of an observable a
-- run can reach — then the one measure is anchored at capᴱ again and
-- dies exactly as rounds 1 and 2 did.  So Ŝ and R̂ have to come from
-- reachability, not from the ledger, and that is a semantic fact about
-- the machine rather than an arithmetic one
round3b-ledger-reset-absurd : ∀ (Ψ W Ω E p U r s G : ℕ) → 3 ≤ E →
  1 ≤ r + suc (hopR (anchorᴬ Ψ W Ω (p + G) G E)) * U →
  dBound (anchorᴬ Ψ W Ω (p + G) G E)
         (hopR (anchorᴬ Ψ W Ω (p + G) G E)) U r s ≤ G →
  ⊥
round3b-ledger-reset-absurd Ψ W Ω E p U r s G 3≤E 1≤ dem =
  <-irrefl refl (<-≤-trans X<A (≤-trans (≤-trans (n≤1+n A) A<G) G≤X))
  where
  X : ℕ
  X = E * 3 ^ (suc Ψ * walkCap Ω (p + G) G)
  A : ℕ
  A = capᴱ W X
  X<A : X < A
  X<A = ≤-trans (n<2^n X) (^-monoˡ-≤ X (s≤s (s≤s z≤n)))
  A<G : A < G
  A<G = sucV≤d A (hopR A) U r s G 1≤ dem
  G≤X : G ≤ X
  G≤X = d≤walkArg Ψ Ω (p + G) G E 3≤E

-- (a) the OLD length hypothesis, under the shared anchor: still absurd
round3-old-ell-absurd : ∀ (Ψ W Ω ℓ E G p U r s d : ℕ) → 3 ≤ E →
  1 ≤ r + suc (hopR (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)))) * U →
  dBound (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)))
         (hopR (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)))) U r s ≤ d →
  p + d ≤ ℓ →
  ⊥
round3-old-ell-absurd Ψ W Ω ℓ E G p U r s d 3≤E 1≤ dem len =
  <-irrefl refl (<-≤-trans A<ℓ ℓ≤A)
  where
  X : ℕ
  X = E * 3 ^ (suc Ψ * walkCap Ω ℓ G)
  A : ℕ
  A = anchorᴬ Ψ W Ω ℓ G E
  -- the demand outruns its own anchor, and ℓ has to cover the demand
  A<ℓ : A < ℓ
  A<ℓ = ≤-trans (sucV≤d A (hopR A) U r s d 1≤ dem)
                (≤-trans (m≤n+m d p) len)
  -- but the anchor is a tower in ℓ, because ℓ is walkCap's own base
  ℓ≤A : ℓ ≤ A
  ℓ≤A = ≤-trans (ℓ≤walkCap Ω ℓ G)
          (≤-trans (walkCap≤walkArg Ψ Ω ℓ G E 3≤E)
                   (<⇒≤ (≤-trans (n<2^n X) (^-monoˡ-≤ X (s≤s (s≤s z≤n))))))

-- (b) a work index that must dominate the anchor: still absurd.  One
-- scanᵉ suffices to put hopDᵉ V b above V, since its clause's exponent
-- IS V — which is why hopD's re-index is the load-bearing edit
round3-anchor-indexed-absurd : ∀ (Ψ W Ω ℓ E G : ℕ) → 3 ≤ E →
  capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)) ≤ G →
  ⊥
round3-anchor-indexed-absurd Ψ W Ω ℓ E G 3≤E h =
  <-irrefl refl (<-≤-trans X<A (≤-trans h (d≤walkArg Ψ Ω ℓ G E 3≤E)))
  where
  X : ℕ
  X = E * 3 ^ (suc Ψ * walkCap Ω ℓ G)
  X<A : X < capᴱ W X
  X<A = ≤-trans (n<2^n X) (^-monoˡ-≤ X (s≤s (s≤s z≤n)))
