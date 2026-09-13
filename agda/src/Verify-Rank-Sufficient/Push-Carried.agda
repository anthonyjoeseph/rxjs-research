------------------------------------------------------------------
-- THE BURST PIPELINE CARRIES WHAT IT WAS HANDED, and the reassembly
-- adds nothing of its own.
--
-- `pushBurst` rebuilds each emit out of four parts and only ONE of
-- them can hold a payload: the split's bookkeeping has had its values
-- taken out, the retag DROPS values by construction, and the appended
-- completion carries none — so a re-emitted burst reads exactly what
-- the FRAME produced, whatever the child delivered.  That is what
-- makes this a list induction with no arithmetic in it: the child's
-- reading enters only as the frame's own hypothesis.
--
-- TWO BOUNDS AND NOT ONE, WHICH IS WHERE THE STORE ENTERS.  A scan's
-- emission IS its stored accumulator, so a claim about what a burst
-- carries cannot be made about the burst alone; and the two quantities
-- cannot share a bound, because the payload half is compared against
-- the TERM being walked while the store holds nodes an ANCESTOR
-- installed, whose readings the current term does not dominate.  So
-- the payload rides `Rv` and the store rides `Rst`, and a frame that
-- writes what it emits is handed the ordering between them rather than
-- assuming it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Push-Carried where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ⊔-lub; m≤m⊔n;
  m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong₂)

open import Rx.Prim using (Tick; Id; value; complete; InstEmit)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Val; Fn; _×ᵗ_; mapᵉ; scanᵉ;
  evalTm)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Evaluator using (Stream; Frame; Path; Sched; EvalSt; NodeId;
  AllOp; map-f; scan-f; take-f; thru-outer; _↠_; scan-st; installNode;
  subscribeE; stepFrame; splitEvents; retagEvents; pushBurst; stHop)
open import Verify-Rank-Sufficient.Carried using (valsHop; emitHop; burstHop;
  emitHop-++; emitHop-values; emitHop-bk; emitHop-retag; splitEvents-vals)

----------------------------------------------------------------------
-- A FRAME THAT DEEPENS NOTHING: its outputs read under the payload
-- bound it was handed, and whatever it writes leaves the store under
-- the store bound.  This is the hypothesis the walk's four
-- non-flattening operators run on.
----------------------------------------------------------------------

-- TWO PAYLOAD BOUNDS AND NOT ONE, WHICH IS THE WHOLE OF WHAT A
-- FLATTENER NEEDS.  Four of the walk's operators hand their frame the
-- bound they hand back, and for those the two are the same number.  A
-- flattener cannot: what it receives is an emitted OBSERVABLE read under
-- its source's own reading, and what it hands back is that observable's
-- deliveries read under the flattener's — which is one `suc` higher.
-- Collapsing the two costs exactly that `suc`, and the `suc` is the
-- rank the inner subscription descends by, so a single-bound frame
-- predicate is weaker than the truth by precisely the amount the descent
-- has to spend.
FrameCarries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t →
  (Fin n → Rd₃) → ℕ → ℕ → ℕ → Set
FrameCarries {Γ = Γ} {e = e} {s = s} {u = u} ac id now f κ ψ Rin Rv Rst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    valsHop ψ s vals ≤ Rin → stHop ψ st ≤ Rst →
    valsHop ψ u (proj₁ (stepFrame ac id now f κ vals fin sd st)) ≤ Rv
    × stHop ψ (proj₂ (proj₂ (proj₂ (proj₂
        (stepFrame ac id now f κ vals fin sd st))))) ≤ Rst

----------------------------------------------------------------------
-- THE TWO NON-FLATTENING FRAMES, WHICH ARE NOT ONE SHELF.  Both are
-- leaves rather than bodies, and the reason differs: a take's outputs
-- are a prefix of what it was handed under a node whose reading is zero
-- by construction, while a map's are a TEMPLATE evaluated at the
-- payload, which is a second source of depth neither bound reads.  The
-- fold is not among them and cannot be — see below.
----------------------------------------------------------------------

-- A TEMPLATE IS READ AGAINST ITS ARGUMENT AND MAY IGNORE IT, SO THE
-- EQUAL-BOUNDS FORM IS WRONG HERE AND ONLY HERE.  The map step of the
-- term reading exists for exactly this: it reads the template under an
-- environment binding the payload's reading, so what a `map-f` frame
-- hands back is that step APPLIED to the bound it was handed, never the
-- bound itself.
--
-- SO THE TWO ENDS ARE READINGS OF DIFFERENT EXPRESSIONS, AND THAT IS
-- THE WHOLE OF THE REPAIR.  The frame is handed what the SOURCE emits
-- and gives back what the TEMPLATE makes of it, so the incoming bound
-- is the source's reading and the outgoing one the map expression's.
-- Those differ by exactly the layer the reading's map clause charges,
-- which is exactly the layer one application of the template can add —
-- so the statement is pinned at both ends and neither end is the other.
-- Collapsing them to the larger is available at the call site and is
-- what the witnesses below kill: it hands the frame a payload the
-- source could never emit, and the template then adds its layer to
-- that.  The source expression is a parameter because the incoming
-- bound names it; nothing else in the statement reads `b`.
--
-- REFUTED: `Refuted.Map-Template` — the freely-quantified form, at a
--   template that drops a numeral and returns a flattener over a
--   literal.  The payload reads ZERO, so the frame is held to the
--   strongest bound the predicate can impose, and the output reads ONE;
--   the store is untouched, so the second conjunct is satisfied and the
--   crossing is the payload one alone.  The same module pins the walk's
--   own bound at this template at ONE and the output fitting under it,
--   which is what keeps the witness from being read as reaching the
--   call site.
-- REFUTED: `Refuted.Map-Pinned` — and the symmetric PIN that finding was
--   read as licensing, at a template that WRAPS its argument instead of
--   dropping it.  Both ends pinned at the map expression's reading, the
--   payload reached by RUNNING that expression: it reads exactly the
--   pinned bound, so the hypothesis is met with no margin, and one more
--   application puts the output a layer past it.  The same module pins
--   the source's reading at ZERO and the template applied to what the
--   source ACTUALLY emits fitting under the map's reading — which is
--   the form below, standing at the very program that kills the
--   symmetric one.
-- PROBED: `Probed.Map-Frame` — the statement itself, applied, at six
--   points: three templates that ADD a layer, DROP their argument and
--   PRESERVE it, each at a source reading zero and at one reading one.
--   Every payload is reached by SUBSCRIBING the source under this very
--   frame, so the incoming hypothesis is decided rather than granted —
--   and it is decided at EQUALITY, since what the frame is handed equals
--   the source's reading at both sources.  The growing rows are tight,
--   returning exactly the map expression's reading; the dropping row has
--   a layer of slack at the deeper source, which is the reading tracking
--   the source rather than the template body.  NOT covered: no row
--   reaches an arrival, a drain step, or a store an earlier frame wrote,
--   so the store conjunct is tight at zero throughout and says only that
--   a map leaves the store alone; and no template's own body maps again.
postulate
  map-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (b : Exp Γ [] [] [] s) (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rst : ℕ) →
    FrameCarries {e = e} ac id now (map-f fn) κ ψ
      (depthᵉ ψ b) (depthᵉ ψ (mapᵉ fn b)) Rst

-- THE PREFIX FRAME, WHICH THE WITNESS ABOVE DOES NOT REACH.  A take
-- hands back `takeVals`' prefix of the list it was given and writes a
-- node the reading prices at zero; the cutting arm additionally DROPS
-- registry entries, which can only lower the store's reading.  So
-- nothing here evaluates anything, and the equal-bounds form is the
-- right one for this frame even though it is the wrong one for its
-- neighbour.
--
-- PROBED: `Probed.Take-Frame` — four frames reached by RUNNING the
--   take arm's own subscription, each held to the TIGHTEST bounds the
--   predicate admits: the reading the frame was handed and the reading
--   the store carried in.  Both conjuncts compare something, which the
--   source is built for — a fold whose accumulator is an observable, so
--   the payload reads positive where a stream of nats would read zero,
--   and whose node the store can read where the take's own is priced at
--   zero.  The store half comes back TIGHT at every point, which is the
--   cutting arm dropping entries and installing nothing.  Counts below,
--   at and above what the burst supplies, at two fold rates; the two
--   below hand back strictly less.  No row reaches an arrival, a drain
--   step, or a take whose node an earlier burst already spent — every
--   point sits at a burst that finishes, and the finish flag is pinned
--   rather than assumed.
postulate
  take-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (nid : NodeId)
    (κ : Path Γ s t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) →
    FrameCarries {e = e} ac id now (take-f {s = s} nid) κ ψ Rv Rv Rst

----------------------------------------------------------------------
-- THE HOP EDGE, AND IT IS ONE LEAF.  A flattener's frame is the only
-- one that re-enters the evaluator: `thruConsume` hands each emitted
-- observable to `subscribeInner`, which is where the RANK descends and
-- where a run that has exhausted it returns the dry marker instead of a
-- burst.  Every other clause of that frame parks, drops or forwards.
--
-- WHAT THE PREMISE BUYS, and why it is `suc Rin` rather than `Rin`.
-- The values arriving here are observables read under the SOURCE's
-- reading; `subscribeInner` subscribes one of them at the rank one
-- below the caller's, so what it needs is a rank strictly above what an
-- arriving observable reads.  The flattener arm supplies exactly that
-- from the entry invariant, because the reading's own clause for a
-- flattener is `suc` of its source's and the invariant already puts the
-- flattener's reading under the rank.  So the descent is paid for by
-- the one clause of the reading that takes `suc`, which is what the
-- edge was always supposed to buy.
--
-- WHY IT IS NOT A `-core` OVER THE WALK.  The inner is a runtime VALUE,
-- structurally unrelated to the term the walk is inducting on, so no
-- arm of the walk reaches it and the report about it cannot be an
-- induction hypothesis.  It is a genuine leaf and not a missing wire.
--
-- AND THE ROOM IN IT IS MEASURED RATHER THAN GUESSED.  Every point
-- instantiated so far hands back EXACTLY what it was handed, so the
-- `suc` is afforded and never spent, and the form holding the frame to
-- `Rin` would have done at all of them.  It is stated at `suc Rin`
-- because that is what the flattening arms consume and the weaker
-- statement is the easier one to prove; if that proof stalls, the
-- stronger form is the thing to reach for rather than a new hypothesis.
--
-- DEAD ROUTE: refuting the store conjunct at a PARKED inner deeper
--   than the source that emitted it.  There is no such queue to build.
--   A value of observable type IS a closed expression, and the value
--   reading at that type is the same projection of the same triple the
--   expression reading is, so a parked inner reads exactly what the
--   frame was handed; the park clause appends it to a queue the store
--   reading takes a `⊔` over, and the premise already affords a whole
--   successor above that.  The axis is bound-side twice over — the
--   queue's depth enters the bound and the outgoing reading through the
--   same `⊔` — so no instantiation of it can fail, however deep.  What
--   is left falsifiable at this frame is the WRITE, not the queue.
--
-- PROBED: `Probed.Hop-Edge` — six frames reached by RUNNING the
--   subscription the flattener arm builds, over all three operators, at
--   a fold that deepens its accumulator once and twice per delivery, at
--   two source lengths, and at one whose limit forces the PARK branch.
--   Every conjunct is positive at every row (the pins carry both sides)
--   and the margin is a constant one.  NOT reached: a frame whose rank
--   is spent, which no root can exhibit since a flattener's own reading
--   is a successor.
--
-- PROBED: `Probed.Hop-Store` — the same frame at a store that is
--   already deep, which is the configuration no other row on this shelf
--   reaches: the flattener's own node is installed holding parked
--   inners reading nought, one and two before the frame runs, and the
--   store bound is taken at the LEAST value the premise and the
--   incoming hypothesis admit, so nothing absorbs an over-deep write.
--   The payload hypothesis is decided at EQUALITY at every row.  What
--   the three buy is the outgoing store: the frame installs the
--   arriving inner and leaves a store reading one below its bound, the
--   first nonzero store reading anywhere on the shelf.  NOT covered: no
--   row runs a frame over a store a DIFFERENT frame wrote, and here the
--   write and the payload coincide, so nothing separates them.
--
-- PROBED: `Probed.Defer-Blind` — the same frame at the one source whose
--   emitted inner is GATED, against a control emitting the same body
--   openly.  Both rows are DEGENERATE in their conjuncts and that is
--   stated at the probe: a source emitting one inner returns nothing and
--   installs nothing either reading reaches, so the payload out and both
--   store figures are nought at both points and neither conjunct could
--   have failed.  What the two buy is the pair of pinned readings — the
--   body reads four, the open frame is held to four and the gated frame
--   to one — which is a finding about where an arrival's bound comes
--   from and is owed at the store reading's own definition.  NOT
--   covered: the arrival frame itself, which is the frame the finding
--   points at and which no row here runs.
postulate
  thru-outer-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) → suc Rin ≤ Rst →
    FrameCarries {e = e} ac id now (thru-outer op nid) κ ψ Rin (suc Rin) Rst

----------------------------------------------------------------------
-- THE WALK, on the burst's spine.  Every emit contributes the frame's
-- outputs and nothing else, and the store is threaded emit by emit.
----------------------------------------------------------------------

pushBurst-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (burst : Stream Γ s) (sd : Sched Γ) (st : EvalSt e)
  (ψ : Fin n → Rd₃) (Rin Rv Rst : ℕ) →
  FrameCarries {e = e} ac id now f κ ψ Rin Rv Rst →
  burstHop ψ s burst ≤ Rin → stHop ψ st ≤ Rst →
  burstHop ψ u (proj₁ (pushBurst ac id now f κ burst sd st)) ≤ Rv
  × stHop ψ (proj₂ (proj₂ (pushBurst ac id now f κ burst sd st))) ≤ Rst
pushBurst-carried ac id now f κ []  sd st ψ Rin Rv Rst fc hb hs = z≤n , hs
pushBurst-carried {Γ = Γ} {t = t} {e = e} {s = s} {u = u}
                  ac id now f κ (em ∷ ems) sd st ψ Rin Rv Rst fc hb hs =
  ⊔-lub (≤-trans (≤-reflexive eq) (proj₁ step)) (proj₁ ih) , proj₂ ih
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)

  sf = stepFrame ac id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sd st

  vals′ = proj₁ sf
  evs   = proj₁ (proj₂ sf)
  fin′  = proj₁ (proj₂ (proj₂ sf))
  sd₁   = proj₁ (proj₂ (proj₂ (proj₂ sf)))
  st₁   = proj₂ (proj₂ (proj₂ (proj₂ sf)))

  -- what this emit was handed, off the burst bound it entered with
  hvals : valsHop ψ s (proj₁ sp) ≤ Rin
  hvals = ≤-trans (≤-reflexive (splitEvents-vals ψ s (InstEmit.events em)))
                  (≤-trans (m≤m⊔n _ _) hb)

  step : valsHop ψ u vals′ ≤ Rv × stHop ψ st₁ ≤ Rst
  step = fc (proj₁ sp) (proj₂ (proj₂ sp)) sd st hvals hs

  -- three of the four parts hold no payload at all
  eq : emitHop ψ u (proj₁ (proj₂ sp) ++ retagEvents evs ++ map value vals′
         ++ (if fin′ then complete ∷ [] else []))
       ≡ valsHop ψ u vals′
  eq = trans (emitHop-++ ψ u (proj₁ (proj₂ sp)) _)
             (cong₂ _⊔_ (emitHop-bk ψ s u (InstEmit.events em))
               (trans (emitHop-++ ψ u (retagEvents evs) _)
                      (cong₂ _⊔_ (emitHop-retag ψ t u evs)
                                  (emitHop-values ψ u vals′ fin′))))

  ih : burstHop ψ u (proj₁ (pushBurst ac id now f κ ems sd₁ st₁)) ≤ Rv
     × stHop ψ (proj₂ (proj₂ (pushBurst ac id now f κ ems sd₁ st₁))) ≤ Rst
  ih = pushBurst-carried ac id now f κ ems sd₁ st₁ ψ Rin Rv Rst fc
         (≤-trans (m≤n⊔m _ _) hb) (proj₂ step)

----------------------------------------------------------------------
-- THE FOLD, AND IT IS NOT A FRAME LEAF AT ALL.
--
-- A scan's outputs are the successive ACCUMULATORS, so what the frame
-- hands back is a function of the STORE and the step and the payload
-- enters only as the step's second argument.  A step that discards that
-- argument cuts the payload out of the answer entirely, and then no
-- bound on what the frame was handed can bound what it returns.  The
-- frame predicate above compares the two against one number and the
-- number is the payload's, which is why the fold cannot sit beside its
-- two siblings however the bound is chosen.
--
-- AND THE STORE BOUND CANNOT ABSORB IT EITHER.  The state a fold writes
-- is the state it was handed with one node replaced by the LAST of its
-- outputs, so a frame predicate holding the store bound FIXED across the
-- step asserts the accumulator does not deepen — which is the one thing
-- a fold does.  Widening it to a separate bound out is no repair: a
-- burst refolds once per value, so the bound would have to move once per
-- emit and the predicate would be a recurrence rather than a bound.
--
-- SO THE STATEMENT IS TAKEN AT THE BURST AND AT THE MACHINE'S OWN SEED.
-- The reading's scan clause ITERATES the step over the source's top
-- count from the seed's own reading, so the term reading already prices
-- every refold this burst can perform — but only for the accumulator
-- THIS term installed, and a node handed over abstractly carries no tie
-- to any term.  Naming the seed is what supplies the tie: the store the
-- burst is pushed into is the one `subscribeE` returns off
-- `installNode nid (scan-st (evalTm z))`, which is exactly what the
-- walk's own scan arm builds.  That makes this coarser than a frame
-- leaf, and the coarseness is the finding rather than a shortcut —
-- nothing weaker has a true form.
--
-- REFUTED: `Refuted.Scan-Store` — the frame-local statement, at the
--   smallest step that deepens: a numeral arrives reading zero against
--   a payload bound of zero, the step discards it, and one accumulator
--   comes back reading one.  The store bound is left slack there so the
--   row cannot be read as a store bound that was merely too tight.
-- PROBED: `Probed.Fold-Burst` — the fold's only measure-side quantity
--   is the accumulator it writes, and the rows move everything feeding
--   its refold count: one, two and three layers per refold; source
--   length to four; a source whose every delivery is a flattened pair,
--   where the reading spends a product rather than a count; a limited
--   flattener, which queues inners into a node the run mints; a fold
--   under a fold; a seed above the floor.  The margin is constant along
--   every family.  Two axes are shown INERT rather than left unswept:
--   the continuation, since the fold's step names neither it nor the
--   clock, so every row is evidence at every continuation; and the
--   store's other nodes, since a fold carries them through untouched
--   and a deeper one raises the premise's reading by what it raises the
--   conclusion's.  No row reaches an arrival or a drain step.
postulate
  scan-burst-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u) (b : Closed Γ s)
    (nid : NodeId) (κ : Path Γ u t) (sd : Sched Γ) (st : EvalSt e)
    (ψ : Fin n → Rd₃) (Rst : ℕ) →
    depthᵉ ψ (scanᵉ f z b) ≤ Rst →
    let r  = subscribeE ac b (scan-f f nid ↠ κ) id now sd
               (installNode nid (scan-st {t = u} (evalTm z)) st)
        pb = pushBurst ac id now (scan-f f nid) κ
               (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
    in burstHop ψ s (proj₁ r) ≤ depthᵉ ψ (scanᵉ f z b) →
       stHop ψ (proj₂ (proj₂ r)) ≤ Rst →
       burstHop ψ u (proj₁ pb) ≤ depthᵉ ψ (scanᵉ f z b)
       × stHop ψ (proj₂ (proj₂ pb)) ≤ Rst
