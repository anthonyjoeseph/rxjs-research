------------------------------------------------------------------
-- THE BURST'S PAYLOAD CONDITIONS, AT THE SUBSCRIBE AND AT EVERY ELEMENT
-- TYPE.  A `*All`'s walk re-enters `depthE` at each emitted inner, so it
-- needs two facts about that inner which the outer's own conditions do
-- not mention: its hop is at most its emitter's, and its synchronous
-- size still fits `V`.  Both are properties of `subscribeE`'s FIRST
-- projection — the values the source itself emits, before any frame runs
-- — so neither is about the `*All` at all, and this is where they live.
--
-- THE ELEMENT TYPE IS ARBITRARY, and that is forced rather than tidy:
-- the arm that consumes this is at `obs u`, but the induction leaves the
-- observable world at its first step, since a `mapᵉ` recurses into a
-- source whose elements are the function's DOMAIN.  A statement pinned
-- to `obs u` could not make that call.  At a data type both conjuncts
-- are trivially true — `hopDᵛ` is 0 and there is no expression to size —
-- which is what makes the generality free.
--
-- AND THE DISPATCH IS THE CHECKED PART.  Each remaining clause hands its
-- whole obligation to one leaf stated at that constructor, so `hopDᵉ`'s
-- and `syncSizeᵉ`'s clause equations have to REDUCE this statement's
-- hypothesis and conclusion into the leaf's — a leaf stated at the wrong
-- index is a type error here rather than a surprise when it is finally
-- proven.  The four `*All`s share ONE leaf, at `subscribeAll`, because
-- they are one fact: the constructor chooses an operator and a node
-- state and nothing else.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Burst-Face where

open import Data.Nat using (ℕ; suc; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-trans; n≤1+n; ≤-reflexive)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (lookup)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (T)
open import Decide using (∧-intro)

open import Rx.Prim using (Gas; g0; gs; Id; Tick; InstEmit; InstEvent; hot; cold;
  _at_from_as_; subscribe; exhausted;
  value; init; close; handoff; complete)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; Tm; isData; inputsBelowᵉ; syncSizeᵉ; unfoldμ; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; input;
  ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ;
  deferᵉ)
open import Rx.Slots using (Slots; scripted; shared; slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; NodeState; AllOp; Path; Stream; sharedPlumb;
  subscribeSharedSlot; memberSource; burstCompleted; share-sink; register; dropSource;
  subscribeE; subscribeAll; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
  merge-st; concat-st; switch-st; exhaust-st)
open import Rx.Hop-Depth using (hopDᵉ; hopD-unfoldμ)
open import Rx.Slot-Hop using (slotHop; slotHop-fix)
open import Verify-Budget-Sufficient.Measures using (burstHopD?; hopDev?; syncSize-unfoldμ;
  hopDᵛ-data;
  syncSize≤sizeᵉ; slotDef-size; ∧-true; all-++-intro)
open import Verify-Budget-Sufficient.Wet.Part2 using (sharedPlumb-hopD)

-- the sync-size side of `hopDᵛ`: read off the VALUE's type, since only
-- an observable payload carries an expression to size
syncOK? : ∀ {n} {Γ : Ctx n} → ℕ → (u : Ty) → Val Γ u → Bool
syncOK? V unitᵗ    _        = true
syncOK? V boolᵗ    _        = true
syncOK? V natᵗ     _        = true
syncOK? V (s ×ᵗ t) (a , b)  = syncOK? V s a ∧ syncOK? V t b
syncOK? V (s +ᵗ t) (inj₁ a) = syncOK? V s a
syncOK? V (s +ᵗ t) (inj₂ b) = syncOK? V t b
syncOK? V (obs t)  ex       = syncSizeᵉ ex ≤ᵇ V

syncEv? : ∀ {n} {Γ : Ctx n} {u} → ℕ → InstEvent (Val Γ u) → Bool
syncEv? {u = u} V (value v) = syncOK? V u v
syncEv? V (init _)    = true
syncEv? V (close _ _) = true
syncEv? V (handoff _) = true
syncEv? V complete    = true

burstSync? : ∀ {n} {Γ : Ctx n} {u} → ℕ → Stream Γ u → Bool
burstSync? V = all (λ em → all (syncEv? V) (InstEmit.events em))

-- the pair every arm lands, at the currency's own slot vector.
--
-- ⚠ THE SECOND CONJUNCT IS FALSE AS STATED, AND THE FACE IS UNDER
-- RESTATEMENT BECAUSE OF IT.  `syncOK?` at an observable payload asks
-- `syncSizeᵉ ≤ V` for a `V` the arms receive ADDITIVELY — a map's
-- condition is `suc (syncSizeᵗ f + syncSizeᵉ e)` and `syncSizeᵗˢ` is a
-- sum — while substitution MULTIPLIES by the number of times the
-- function names its argument.  A function naming it twice therefore
-- emits a payload about twice its source's size out of a budget that
-- paid for the source once, and a scan step naming its accumulator
-- twice doubles per emission.  Three of the five arms emit substituted
-- payloads and all three fall to that one witness family; the two that
-- do not are the one-shot, whose payloads are `evalTm` of terms the
-- source was written with, and the take, whose frame does not touch a
-- value.
--
-- WHAT SURVIVES IS THE HOP CONJUNCT, and that is the useful half.
-- `hopDᵉ` carries an occurrence COEFFICIENT (`pmᵗ`) for exactly this
-- reason, and the consuming depth bound comes out EQUAL to the measured
-- depth at the same programs, duplication and an extra level of nesting
-- included.  So the repair is a size currency of `hopDᵉ`'s shape, or the
-- caps ledger that already has one — `valCaps?` bounds a payload by
-- `Caps.cSize (frameStep J c)` and the wet push faces establish it at
-- every frame — and it is NOT a larger `V`: each witness scales with its
-- own source, so no numeral survives.
-- REFUTED: `Refuted.Hop-Burst-Sync`, four witnesses — the map arm, the
--   scan arm, the `*All` arm, and the dispatch they sit under.  The same
--   module pins the CONSUMING bound as tight rather than false at the
--   same programs, which is what confines the repair to this conjunct.
HopsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  ℕ → Slots Γ → ℕ → Stream Γ u × Sched Γ × EvalSt e → Set
HopsOK V sl d r = (burstHopD? V (slotHop V sl) d (proj₁ r) ≡ true)
                × (burstSync? V (proj₁ r) ≡ true)

-- the slot subject at the CLOSED stage, so the leaf's `syncSizeᵉ` and
-- `hopDᵉ` are not read at three unsolved binder lists
inp : ∀ {n} (Γ : Ctx n) (i : Fin n) → Closed Γ (lookup Γ i)
inp Γ i = input i


------------------------------------------------------------------
-- A SCRIPTED SLOT'S SCRIPT IS DATA, WHICH IS WHAT MAKES THREE OF THE
-- FOUR `input` BRANCHES CLOSE WITHOUT ARITHMETIC.  `Slot`'s scripted
-- constructor carries `T (isData t)` as a side condition, and both
-- conjuncts read a value by its TYPE — so at a data type there is no
-- expression to size and no hop to charge, at any budget whatever.
-- Only the sync half is new: `hopDᵛ-data` (.Measures) already says the
-- same of the hop side and is shared with the walk face's push arms.
-- Each measure needs its own `with` on the pair's left half, which is
-- where `isData`'s hereditary reading has to be taken apart.
------------------------------------------------------------------

syncOK?-data : ∀ {n} {Γ : Ctx n} (V : ℕ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → syncOK? {Γ = Γ} V u v ≡ true
syncOK?-data V unitᵗ ok v = refl
syncOK?-data V boolᵗ ok v = refl
syncOK?-data V natᵗ  ok v = refl
syncOK?-data V (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = ∧-intro (syncOK?-data V s (subst T (sym eqs) tt) a)
                      (syncOK?-data V u ok b)
... | false = ⊥-elim ok
syncOK?-data V (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = syncOK?-data V s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
syncOK?-data V (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = syncOK?-data V u ok b
... | false = ⊥-elim ok
syncOK?-data V (obs u) ok v = ⊥-elim ok

-- a scripted slot's script is data, so its values pass both conjuncts at
-- every budget -- which is what makes the scripted arms close with no
-- arithmetic at all
mapValue-hopD : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (r : ℕ) (u : Ty) →
  T (isData u) → (vs : List (Val Γ u)) →
  all (hopDev? V η r) (map value vs) ≡ true
mapValue-hopD V η r u ok []       = refl
mapValue-hopD V η r u ok (v ∷ vs) =
  ∧-intro (subst (λ x → (x ≤ᵇ r) ≡ true) (sym (hopDᵛ-data V η u ok v)) refl)
          (mapValue-hopD V η r u ok vs)

mapValue-sync : ∀ {n} {Γ : Ctx n} (V : ℕ) (u : Ty) → T (isData u) →
  (vs : List (Val Γ u)) → all (syncEv? {Γ = Γ} {u = u} V) (map value vs) ≡ true
mapValue-sync V u ok []       = refl
mapValue-sync V u ok (v ∷ vs) =
  ∧-intro (syncOK?-data V u ok v) (mapValue-sync V u ok vs)

-- retagging an emit's kind leaves its EVENTS alone, so the share's
-- plumbing relabel is invisible to the sync side too
sharedPlumb-sync : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (str : Stream Γ u) →
  burstSync? V str ≡ true → burstSync? V (sharedPlumb str) ≡ true
sharedPlumb-sync V []         h = refl
sharedPlumb-sync V (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-sync V ems (proj₂ (∧-true _ _ h)))

------------------------------------------------------------------
-- THE ARMS.  One leaf per constructor whose burst is not already free
-- of value events, and ONE for all four `*All`s.  Each is a bare
-- statement about the evaluator at that constructor: no induction
-- hypothesis is passed in, so the leaf carries the whole arm and the
-- dispatch below carries none of it.
--
-- THE HOP CONJUNCT IS THE SHARP ONE: at no slack it makes the outer
-- frame's own `suc` and the measure's hop edge the SAME unit, which is
-- why the `*All` bound that consumes these comes out tight rather than
-- generous.  Nothing in the three conditions below mentions a payload,
-- and the consuming fold spends one payload condition per emitted
-- inner, so this is where the depth face's remaining risk went.
------------------------------------------------------------------

-- ⚠ THE SIZE CONDITION IS NOT INHERITED AT THE `input` CLAUSE, WHICH IS
-- WHY THERE IS A THIRD CONDITION.  A slot read is not a structural
-- descent: `depthE` recurses into the shared DEF, and the subject's own
-- `sizeᵉ (input i) ≡ 1` bounds nothing whatever about that def.  So `V`
-- sits at its floor of 2 while the def is as large as you like, and the
-- def outruns the bound its own slot reports — 21 against 20, at a source
-- of twenty literals, which `hopDᵉ` charges nothing for at any `V` and
-- `depthE` charges one nesting level each.  `slotsSize (Sched.slots
-- sched) ≤ V` is the repair, and it costs no leaf at either end:
-- `slotDef-size` (.Measures) turns it into the def's own size at the
-- clause, and `slotsSize≤sizeCapAt` discharges it at the root out of
-- `capsBase`'s slot summand.  The mirror had it all along —
-- `subscribeE-caps` takes exactly this hypothesis beside its own size
-- condition, which is the diff worth doing before believing any of these
-- signatures.
-- REFUTED: `depth-hop-slot-absurd` (`Refuted.Depth-Hop`), whose figures
--   are pinned by `refl`, so a repair that closes the gap has to move one
--   of them by name

-- ⚠ AND THE CONDITION IS OVER `syncSizeᵉ` BECAUSE THE `μᵉ` RE-ENTRY
-- DESTROYS `sizeᵉ`.  `depthE` at `gs` recurses on `unfoldμ body`, and
-- `size-unfoldμ` (.Keeps-Ring) bounds that only by `sizeᵉ (μᵉ body) *
-- sizeᵉ (μᵉ body)` — a square per unfold, so a FIXED `V` cannot survive
-- repeated unfolding, while the bound does not move at all:
-- `hopD-unfoldμ` is an EQUALITY, so the clause's obligation is this
-- statement at a bigger subject and nothing else.  `syncSizeᵉ` is the
-- measure the two sides already agree on — it and `hopDᵉ` and `depthE`
-- all charge a `deferᵉ` body ZERO, `elimG` substitutes only under
-- defers, and so `unfoldμ-shrinks` (.Measures) makes the condition
-- STRICTLY DECREASE across the very step that squares the size.  It is a
-- STRENGTHENING the root consumer pays nothing for: `syncSize≤sizeᵉ`
-- composes with `size≤sizeCapAt` in one `≤-trans`, and both witnesses in
-- `Refuted.Depth-Hop` stay excluded by the arithmetic that excluded them
-- before.
-- DEAD ROUTE: closing that clause through the induction hypothesis with a
--   condition over `sizeᵉ`.  The hypothesis the clause needs is exactly
--   the one unfolding destroys, so no measure and no clause order
--   recovers it — what had to change was the condition itself.
-- PROBED: THE REGION THE TWO MEASURES PART COMPANY IN, which is the whole
--   region this strengthening opens: a large `deferᵉ` body, admitted here
--   and excluded by `sizeᵉ` at any `V` below its size.  Twenty literals
--   under a bare `deferᵉ` hold at `V = 2` against a bound of 0, with the
--   body's own depth at 4.  The same body under `mergeAllᵉ`, where the
--   burst arm subscribes the emitted inner at full size, holds TIGHT at 1
--   against 1.  And a `μᵉ` whose body emits both that source and its own
--   recursive variable holds tight at 1 against 1 while
--   `sizeᵉ (unfoldμ body) ≤ V` computes to `false` — the step the
--   condition turns on, pinned by `refl` in `Probed.Depth-Hop`.  Not
--   reached: nested `μᵉ`, and a `deferᵉ` body large against a `V` the
--   slot telescope must also fit.

------------------------------------------------------------------
-- THE ARMS ARE A MIRROR, NOT NEW MATHEMATICS, and that is the one thing
-- that sizes the work.  Every frame's own arithmetic is discharged — a
-- payload built at SUBSTITUTION rather than written in the source is
-- exactly what the substitution kit covers — and so is every frame's
-- FOLD over a burst: the wet push faces land this exact conjunct at
-- their own frame, one face per frame, with the clause structure a
-- mirror would have.
--
-- WHAT THOSE FACES BUNDLE IT WITH is why they cannot simply be spent:
-- the invariant, the fnCap burst predicate, dryness and the registry
-- ledger all arrive as hypotheses beside the hop receipt, and carrying
-- four more currencies is how a hop statement acquires a caps context by
-- the back door.  So each arm is one of those faces with its other
-- conjuncts dropped — a mirror whose every piece has a discharged
-- original, which is what makes the arms separable and the remaining
-- risk labour rather than design.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE OTHER PRODUCER IS THE WALK FACE'S OWN LANDING, and it is NOT
-- circular: `WalkStmt` (.Walk-Level/Statement) takes `depthE g b κ … ≤
-- dep` as a PARAMETER and lands this exact hop conjunct at this exact
-- instantiation — `subscribeAll-walk`'s body spends it as its own
-- seventh receipt — so the depth face's first disjunct is what would pay
-- for it.  The cost is the context: `F ≡ sizeCapAt e sl (suc id)` PINS
-- `V` to a size cap, and `capsOK?`, `INV?`, the path predicates, the
-- registry ledger and the ceiling all arrive as hypotheses.  Per-inner
-- termination is the GAS: the depth measure peels one before entering
-- the payload.
--
-- ⚠ THAT IS A ROUTE AND NOT EVIDENCE, so it ranks the hop half at
-- nothing.  It does now license the size half's restatement: trading a
-- leaf for those hypotheses would launder tracked debt into untracked,
-- and only a refutation of the unconditional form buys it — which is
-- what `Refuted.Hop-Burst-Sync` supplies, and it supplies it against
-- the size conjunct alone.
-- DEAD ROUTE: spending an existing depth-free producer, so that no caps
--   context is needed at all.  `subscribeE-wet`'s landing carries
--   `hasDry` and `INV?` and no burst-hop conjunct, and the hop-spine
--   face reaches only the `scan-f` frame at push level — so there is
--   nothing already landed to spend, and a depth-free supplier is these
--   statements rather than a lemma reaching them.
-- TWIN: `subscribeE-caps` for the dispatch these leaves hang under, at
--   this same generality; `pushMap-wet`, `pushTake-wet`, `pushScan-wet`
--   and `pushThru-walk` for the burst FOLD each of the four frame arms
--   owes, each already landing this exact hop conjunct at its own frame;
--   `hopD-map-emit` and `hopD-unfoldμ` for the per-frame arithmetic
--   under them, and `hopD-evalWith` for a one-shot's own payloads, which
--   are `evalTm` of the terms the source was written with.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE SIZE CONJUNCT'S TRUE FORM IS ALREADY PROVEN, AND THE CITATION IS
-- STRATIFIED RATHER THAN CIRCULAR.  `subscribeE-caps` (.Subscribe-Face)
-- lands `burstCaps? (frameStep j c) sl` over this very burst, and that
-- bounds every payload in it by `Caps.cSize` — `valCaps?-size` reads the
-- bound off — so no payload arithmetic has to be re-derived here at all.
-- What it costs is the caps context, and the one hypothesis worth naming
-- before reaching for it is `depthE g b κ … ≤ dep`: the depth bound this
-- module exists to supply.
--
-- SO THE CITATION IS AVAILABLE ONLY WHERE THE DEPTH INDUCTION HAS
-- ALREADY FIRED — at a STRUCTURAL descent, where the subject shrinks and
-- the face's own hypothesis at the subterm is in hand.  The `*All` clause
-- is exactly that shape: the outer IS a subterm, so its depth bound comes
-- from the induction, that bound buys the caps receipt over the outer's
-- burst, and the receipt bounds the payloads the inner descent then
-- re-enters at one gas less.  Read as a cycle it is caps ← depth ← caps;
-- read at the indices it is two subjects and two measures.
------------------------------------------------------------------

-- AND THE CONSUMER ALREADY ASKS IN THIS CURRENCY, which is the part
-- that says the swap is a reinvention undone and not a coincidence.
-- `subscribeE-wet-via-caps` (Caps-Bridge) carries, in ONE signature, a
-- gas hypothesis stated over `hopDᵉ Ŝ (slotHop Ŝ sl) b` and the
-- `depOK` hypothesis `depthE g b κ id now sched st ≤ capsH e sl id`
-- that this module exists to discharge — same `sl`, same
-- `Ŝ = sizeCapAt e sl (suc id)`, adjacent lines.  So `V` and `η` do
-- not have to be invented: `V`'s two nameable instantiations coincide,
-- the consumer's `sizeCapAt e sl (suc id)` and `suc (entryCeil n ins
-- e)`, which is the `M` the tower arithmetic is stated at.
-- `make dup-check` could not see that: the two statements are not the
-- same fact, only the same job.
--
-- PROBED: DOMINATION AT THE FOUR REFUTATION WITNESSES (`Probed.Depth-Hop`).
--   `hopDᵉ` dominates `depthE` at every program that killed the
--   predecessor — the two small programs at a refold bound of one (depth
--   4 and 8), and both rows of the quadratic gadget at four (35 and 70).
--   That is evidence reaching the RISKY region rather than a degenerate
--   row, because those four programs ARE the region.

postulate
  -- PROBED: `Probed.Depth-Hop` §§ 13 and 15, over a syntactic outer —
  --   `ofᵉ` of one `*All` inner — at the smallest `V` the conditions
  --   admit.  § 13 measures the CONSUMING assembly's arithmetic and § 15
  --   computes the two Bools this leaf asserts, so a payload deeper than
  --   its emitter fails a row the consuming fold's `⊔` could have
  --   hidden.  Four paths, one per `*All` operator, each on its own
  --   program's initial state: 2 against 2 in § 13 and green in § 15,
  --   with a budget one unit lower FALSE — which is what makes the
  --   series LOAD-BEARING at zero margin rather than merely green.
  --   Conjuncts covered: the hop conjunct against the measure's hop
  --   edge, and the sync conjunct at the same `V` — the latter only over
  --   payloads no substitution enlarged, which is the region where it is
  --   true.  Not reached: a path that is not `thru-outer … ↠ root`, and
  --   the slot telescope, since every program runs over an empty slot
  --   vector.
  --   AND THE ONE DIRECTION THAT COULD FAIL IS NOT REACHABLE AT ALL,
  --   which is that section's § 14 and carries no row deliberately: only
  --   the exponential `scanᵉ` clause lets an emitted inner's hop outrun
  --   its emitter's, and reaching it needs many refolds, which need a
  --   long source, which raises `syncSizeᵉ b` — so the condition forces
  --   a `V` whose `3 ^ V` outruns whatever nesting those refolds built.
  --   The risky region is excluded by the hypothesis rather than by
  --   luck, and what would reach it is an emission that is not syntax: a
  --   scripted slot, which the slots width bounds the same way, or a
  --   `μᵉ` re-entry, which `hopD-unfoldμ` holds fixed.
  hops-of : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (V : ℕ) (g : Gas) (ts : List (Tm Γ [] [] [] u)) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → syncSizeᵉ (ofᵉ ts) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (hopDᵉ V (slotHop V sl) (ofᵉ ts))
      (subscribeE g (ofᵉ ts) κ bid now sched st)

  -- PROBED: `Probed.Depth-Hop` § 15, at the region no syntactic outer
  --   reaches — a `mapᵉ` whose function puts its ARGUMENT under a
  --   `*All`, so every payload is a hop deeper than the inner the source
  --   carried and the depth appears at substitution rather than in the
  --   source.  What pays for it is `pmᵗ`'s occurrence coefficient, and
  --   it pays exactly, 1 against 1, with a budget of 0 FALSE on the same
  --   burst.  This is the clause whose predecessor was refuted for
  --   reading that coefficient at the unsubstituted source.  Not
  --   reached: a function wrapping its argument more than once, and a
  --   source whose own hop is positive.
  hops-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (V : ℕ) (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → syncSizeᵉ (mapᵉ f b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (hopDᵉ V (slotHop V sl) (mapᵉ f b))
      (subscribeE g (mapᵉ f b) κ bid now sched st)

  hops-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (V : ℕ) (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → syncSizeᵉ (takeᵉ cnt b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (hopDᵉ V (slotHop V sl) (takeᵉ cnt b))
      (subscribeE g (takeᵉ cnt b) κ bid now sched st)

  hops-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (V : ℕ) (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → syncSizeᵉ (scanᵉ f z b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (hopDᵉ V (slotHop V sl) (scanᵉ f z b))
      (subscribeE g (scanᵉ f z b) κ bid now sched st)

  -- ONE LEAF FOR FOUR CLAUSES: the constructor picks an operator and an
  -- initial node state, and `subscribeAll` is the rest of every one of
  -- them.  Stated at `suc` on both sides because that is what the four
  -- `hopDᵉ` and `syncSizeᵉ` clauses reduce to.
  -- ⚠ AND THE SIZE CONDITION IS THE ONE THE BURST ARM WILL TEST, which is
  -- worth writing down before it is ground: `b` shrinks at every
  -- structural descent, so the condition is inherited for free THERE — the
  -- two clauses that are not structural descents have their own blocks
  -- above — but
  -- at the burst arm `b` becomes an emitted PAYLOAD whose size may EXCEED
  -- its emitter's — that is the difficulty the whole face is about.  The
  -- caps machinery is what re-establishes it (`applyFn-iterSize` bounds an
  -- emitted payload's size by the cap), which is why `V` is a size CAP and
  -- not `sizeᵉ e`; and it re-establishes MORE than the arm needs, since
  -- `syncSize≤sizeᵉ` turns a `sizeᵉ` bound on the payload into this
  -- condition in one step.  IT CANNOT BE RE-ESTABLISHED FROM WHAT THIS
  -- STATEMENT CARRIES, and `Refuted.Hop-Burst-Sync` says so at an inner
  -- that is itself a duplicating map — so none of the four operators'
  -- arithmetic enters, and the finding is the caps hypothesis, the shape
  -- `cascade-depth-capsH` already has, rather than a smaller `V`.
  --
  -- PROBED: EVERY CLAUSE OF `hopDᵉ`, AND ALL OF IT TIGHT (`Probed.Depth-Hop`).
  --   The three regions this receipt used to name as unreached — off the
  --   root path, the slot telescope, the `input` clause — are reached, and
  --   the rows are tight rather than slack, which is the part worth
  --   trusting.  A two-slot STRATIFIED telescope whose slot 1 reads slot 0
  --   gives 3 against 3, with two of the three units coming out of the η
  --   chain instead of the program's syntax, and it exercises `ηAt`'s
  --   `suc k` branch — the one `Rx.Slot-Hop` records series W as having
  --   missed entirely.  A scripted slot charged 0 gives 1 against 1, with
  --   the subscription moved into the map's function so the row can fail.
  --   `deferᵉ`, the other constant-0 clause and the same shape that killed
  --   the predecessor's `input`, gives 0 against 0 wrapping the deepest
  --   program in the file, and 1 against 1 nested under a `*All`.  `μᵉ`
  --   unfolding for twenty units of gas gives 1 against 1.  `takeᵉ` over
  --   that deepest program gives 4 against 4.  And all four `*All`
  --   operators give 4 against 4 at one nesting — the uniform `suc` clause
  --   was the widest untested coverage claim in the measure, since
  --   cancelling and dropping change which inners are LIVE and not how
  --   deep a live one sits.
  hops-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (V : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
    (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → suc (syncSizeᵉ b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (suc (hopDᵉ V (slotHop V sl) b))
      (subscribeAll g op ns b κ bid now sched st)

------------------------------------------------------------------
-- THE CONNECT WRAPPER, over the latch as a BOOLEAN rather than a
-- scrutinee.  `sharedConnect` decides in one `if` whether the def died
-- inside its own connect burst, and both arms wrap the SAME plumbing
-- relabel behind an emit carrying no value event — so taking the latch
-- as an argument turns a `with` inside a recursive clause into two lines
-- that say the same thing, and keeps the recursion's `where` block free.
------------------------------------------------------------------
connect-hops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (V : ℕ) (η : Fin n → ℕ)
  (r : ℕ) (i : Fin n) (bid : Id) (c : Bool)
  (burst : Stream Γ (lookup Γ i)) (sched : Sched Γ) (st : EvalSt e) →
  burstHopD? V η r burst ≡ true → burstSync? V burst ≡ true →
  let res : Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
      res = if c
        then (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                 at bid from toℕ i as subscribe) ∷ sharedPlumb burst)
             , sched
             , record st { registry = dropSource (toℕ i) (EvalSt.registry st)
                         ; completedSources = toℕ i ∷ EvalSt.completedSources st }
        else ((init (toℕ i) ∷ []) at bid from toℕ i as subscribe) ∷ sharedPlumb burst
             , sched , st
  in (burstHopD? V η r (proj₁ res) ≡ true) × (burstSync? V (proj₁ res) ≡ true)
connect-hops V η r i bid true burst sched st h sy =
  ∧-intro refl (sharedPlumb-hopD V η r burst h)
  , ∧-intro refl (sharedPlumb-sync V burst sy)
connect-hops V η r i bid false burst sched st h sy =
  ∧-intro refl (sharedPlumb-hopD V η r burst h)
  , ∧-intro refl (sharedPlumb-sync V burst sy)

------------------------------------------------------------------
-- THE DISPATCH.  Three constructors need no arm at all — their burst
-- carries no `value` event, so both predicates hold by computation —
-- and `μᵉ` needs none either: unfolding leaves the hop EQUAL and
-- strictly shrinks the synchronous size, so the recursive call is the
-- whole proof and the gas peel is what terminates it.
------------------------------------------------------------------
mutual
  subscribeE-hops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → syncSizeᵉ b ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (hopDᵉ V (slotHop V sl) b) (subscribeE g b κ bid now sched st)

  -- THE SLOT ARM.  Three of the four branches carry no value event of
  -- their own: a spent script and a live re-registration emit only
  -- protocol, and a script's own values are DATA by the constructor's
  -- side condition.  The fourth is the connect, and it is the only
  -- recursive edge in the face that is not a structural descent.
  hops-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (V : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → syncSizeᵉ (inp Γ i) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    HopsOK V sl (hopDᵉ V (slotHop V sl) (inp Γ i))
      (subscribeE g (inp Γ i) κ bid now sched st)

  -- THE SLOT IS A PARAMETER, WITH ITS EQUATION BESIDE IT: `slotHop V sl
  -- i` unfolds through `sl i`, so an arm that matched the slot would
  -- rewrite its own budget and the fixpoint would no longer apply to
  -- what was left.  The def's connect spends a gas unit, and
  -- `slotHop-fix` says the staged number IS that def's hop — so the arm
  -- is the dispatch again at the def, transported along an equality,
  -- with `slotDef-size` paying the def's size condition out of the
  -- slots telescope.
  hops-slot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (V : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
    {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
    HopsOK V sl (slotHop V sl i)
      (subscribeSharedSlot g i d κ bid now sched st)

  subscribeE-hops V g (input i) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-input V g i κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g (ofᵉ ts) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-of V g ts κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g emptyᵉ κ bid now sl sched st 2≤V szb slSz slEq = refl , refl
  subscribeE-hops V g (mapᵉ f b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-map V g f b κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g (takeᵉ cnt b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-take V g cnt b κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g (scanᵉ f z b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-scan V g f z b κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g (mergeAllᵉ b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-all V g mergeᵒ (merge-st 0 false) b κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops {u = u} V g (concatAllᵉ b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-all V g concatᵒ (concat-st {t = u} [] false false) b κ bid now sl sched st
      2≤V szb slSz slEq
  subscribeE-hops V g (switchAllᵉ b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-all V g switchᵒ (switch-st nothing false) b κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g (exhaustAllᵉ b) κ bid now sl sched st 2≤V szb slSz slEq =
    hops-all V g exhaustᵒ (exhaust-st false false) b κ bid now sl sched st 2≤V szb slSz slEq
  subscribeE-hops V g0 (μᵉ body) κ bid now sl sched st 2≤V szb slSz slEq = refl , refl
  subscribeE-hops V (gs fuel) (μᵉ body) κ bid now sl sched st 2≤V szb slSz slEq =
    subst (λ d → HopsOK V sl d (subscribeE fuel (unfoldμ body) κ bid now sched st))
      (hopD-unfoldμ V (slotHop V sl) body)
      (subscribeE-hops V fuel (unfoldμ body) κ bid now sl sched st 2≤V
        (≤-trans (≤-reflexive (syncSize-unfoldμ body))
                 (≤-trans (n≤1+n (syncSizeᵉ body)) szb))
        slSz slEq)
  subscribeE-hops V g (varᵉ ()) κ bid now sl sched st
  subscribeE-hops V g (deferᵉ body) κ bid now sl sched st 2≤V szb slSz slEq = refl , refl


  hops-input V g i κ bid now sl sched st 2≤V szb slSz slEq
    with Sched.slots sched i in slotEq
  ... | shared d =
    hops-slot V g i d κ bid now sl sched st 2≤V slSz slEq
      (trans (sym (cong (λ y → y i) slEq)) slotEq)
  ... | scripted (hot _)
    with memberSource (toℕ i) (EvalSt.completedSources st)
  ...   | true  = refl , refl
  ...   | false = refl , refl
  hops-input {Γ = Γ} V g i κ bid now sl sched st 2≤V szb slSz slEq
    | scripted {ok} (cold sync []) =
    ∧-intro (∧-intro refl
               (all-++-intro (hopDev? V (slotHop V sl) (slotHop V sl i))
                  (map value sync) _
                  (mapValue-hopD V (slotHop V sl) (slotHop V sl i)
                     (lookup Γ i) ok sync) refl)) refl
    , ∧-intro (∧-intro refl
                 (all-++-intro (syncEv? V) (map value sync) _
                    (mapValue-sync V (lookup Γ i) ok sync) refl)) refl
  hops-input {Γ = Γ} V g i κ bid now sl sched st 2≤V szb slSz slEq
    | scripted {ok} (cold sync (dl ∷ ds)) =
    ∧-intro (∧-intro refl
               (mapValue-hopD V (slotHop V sl) (slotHop V sl i)
                  (lookup Γ i) ok sync)) refl
    , ∧-intro (∧-intro refl (mapValue-sync V (lookup Γ i) ok sync)) refl

  hops-slot V g i d κ bid now sl sched st 2≤V slSz slEq eq
    with memberSource (toℕ i) (EvalSt.completedSources st)
       | memberSource (toℕ i) (EvalSt.connectedShares st)
  ... | true  | _    = refl , refl
  ... | false | true = refl , refl
  hops-slot V g0 i d κ bid now sl sched st 2≤V slSz slEq eq
    | false | false = refl , refl
  hops-slot V (gs fuel) i d κ bid now sl sched st 2≤V slSz slEq eq
    | false | false =
    connect-hops V (slotHop V sl) (slotHop V sl i) i bid
      (burstCompleted (proj₁ r)) (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (subst (λ x → burstHopD? V (slotHop V sl) x (proj₁ r) ≡ true)
             (sym (slotHop-fix V sl i eq)) (proj₁ ih))
      (proj₂ ih)
    where
    st₁ = register (toℕ i) κ
            (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
    r   = subscribeE fuel d (share-sink i) bid now sched st₁
    ih  = subscribeE-hops V fuel d (share-sink i) bid now sl sched st₁ 2≤V
            (≤-trans (syncSize≤sizeᵉ d) (≤-trans (slotDef-size sl i eq) slSz))
            slSz slEq
