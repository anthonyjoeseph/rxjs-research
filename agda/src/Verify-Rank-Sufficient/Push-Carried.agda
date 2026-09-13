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

open import Data.Bool using (Bool; if_then_else_; T)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; suc; _⊔_; _⊔′_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ⊔-lub; m≤m⊔n;
  m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong₂)

open import Rx.Prim using (Tick; Id; value; complete; InstEmit)
open import Rx.Exp using (Ctx; Closed; Tm; Val; Fn; _×ᵗ_; scanᵉ; evalTm; inputsBelowᵉ)
open import Rx.Inputs-Below using (below-scan)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; depthᵉ; rdᵉ; rdᵗ; ε; _▸_)
open import Rx.Evaluator using (Stream; Frame; Path; Sched; EvalSt; NodeId;
  AllOp; map-f; scan-f; take-f; thru-outer; _↠_; scan-st; installNode;
  subscribeE; stepFrame; splitEvents; retagEvents; pushBurst; stHop)
open import Verify-Rank-Sufficient.Carried using (valsAt; emitAt; valsRd; burstRd; _⊑_; emitAt-++; emitAt-values; emitAt-bk; emitAt-retag;
  splitEvents-valsAt)

----------------------------------------------------------------------
-- A FRAME THAT DEEPENS NOTHING: its outputs read under the payload
-- bound it was handed, and whatever it writes leaves the store under
-- the store bound.  This is the hypothesis the walk's four
-- non-flattening operators run on.
----------------------------------------------------------------------

-- TWO PAYLOAD BOUNDS AND NOT ONE, WHICH IS THE WHOLE OF WHAT A
-- FLATTENER NEEDS.  Four of the walk's operators hand their frame the
-- bound they hand back, and for those the two are the same reading.  A
-- flattener cannot: what it receives is an emitted OBSERVABLE read under
-- its source's own reading, and what it hands back is that observable's
-- deliveries read under the flattener's — which is one `suc` higher.
-- Collapsing the two costs exactly that `suc`, and the `suc` is the
-- rank the inner subscription descends by, so a single-bound frame
-- predicate is weaker than the truth by precisely the amount the descent
-- has to spend.
--
-- AND BOTH BOUNDS ARE WHOLE READINGS RATHER THAN DEPTHS, WHICH IS WHAT
-- LETS THE SHELF SPEAK ABOUT A TEMPLATE AT ALL.  A payload admitted by
-- its depth alone is a payload whose DELIVERY COUNT is unconstrained,
-- and a template that folds over its argument deepens once per
-- delivery — so a frame's output is a function of a quantity the
-- depth-only predicate could not see, and no figure computed from the
-- frame and the incoming depth bounds it.  The reading carries the
-- count beside the depth and the template step consumes exactly that
-- pair, so the residue below is the frame's own function read against
-- the bound it was entered under.
--
-- DEAD ROUTE: admitting the payload by its HOP ALONE and pinning the
--   outgoing bound at any ℕ read off the frame, the path or the source
--   expression.  Three such pins were separated by one program: a
--   template whose body folds returns three, five and seven layers at
--   three payloads that read nought apart, so a single admitted bound
--   answers all three and no choice of the outgoing figure holds.  The
--   currency is the defect and not the pin, which is why the repair is
--   here rather than at any of them.
-- RECOVERY: git show 19ce2c6:agda/evidence/refuted/Refuted/Path-Heads.agda
--   restores the machine form of that separation — the folding template
--   and the three payloads, plus the two head statements it killed.  It
--   was deleted because `src` can no longer state it: the pins it
--   refutes were spelled in the depth-only currency the paragraph above
--   is the repair for.
FrameCarries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ lo u t →
  (Fin n → Rd₃) → Rd → Rd → ℕ → Set
FrameCarries {Γ = Γ} {e = e} {s = s} {u = u} ac id now f κ ψ Rin Rv Rst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    valsRd ψ s vals ⊑ Rin → stHop ψ st ≤ Rst →
    valsRd ψ u (proj₁ (stepFrame ac id now f κ vals fin sd st)) ⊑ Rv
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

-- THE RESIDUE ITSELF, SPELLED ONCE BECAUSE THREE FACES READ IT.  It is
-- the per-value half of the reading's own map clause, character for
-- character: the template read under an environment binding the
-- incoming pair, joined at the hop with the incoming hop because the
-- source stays subscribed under a template that drops its argument.
-- Both walks and the shelf spend the same expression, so a change to
-- the reading's map clause is a type error at all three rather than a
-- silent disagreement between them.
mapRd : ∀ {n} {Γ : Ctx n} {s u} (ψ : Fin n → Rd₃) →
  Rd → Fn Γ [] [] [] s u → Rd
mapRd ψ Rin fn = proj₁ r , proj₂ r ⊔′ proj₂ Rin
  where r = rdᵗ ψ (ε ▸ Rin) fn

-- A TEMPLATE IS READ AGAINST ITS ARGUMENT AND MAY IGNORE IT, SO THE
-- EQUAL-BOUNDS FORM IS WRONG HERE AND ONLY HERE.  The map step of the
-- term reading exists for exactly this: it reads the template under an
-- environment binding the payload's reading, so what a `map-f` frame
-- hands back is that step APPLIED to the bound it was handed, never the
-- bound itself.
--
-- AND THE RESIDUE IS FRAME-LOCAL, WHICH IS WHAT THE WIDER CURRENCY
-- BOUGHT.  The bound the frame is entered under IS an environment
-- entry, so the template can be read against it directly and no source
-- expression appears in the statement at all.  That matters beyond
-- tidiness: a chain step records the frame and not the expression the
-- frame was built from, so the earlier form — pinned at the readings of
-- a source and of its wrapping — was unavailable to the chain walk and
-- forced a separate leaf there.  This form is the leaf, and the walk
-- spends it directly.
--
-- DEAD ROUTE: pinning the two ends at a SOURCE expression and its
--   wrapping, with the payload admitted by depth.  It relates two
--   quantities in different currencies — the outgoing one sees the
--   source's delivery count, the incoming one drops the payload's — so
--   a source delivering once fixes a finite bound while payloads
--   delivering three and five times are admitted beside it at nought,
--   and a folding template hands back a layer per delivery.
-- REFUTED: `Refuted.Map-Template` — the freely-quantified equal-bounds
--   form, at a template that drops a numeral and returns a flattener
--   over a literal.  The payload reads ZERO, so the frame is held to the
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
--   source ACTUALLY emits fitting under the map's reading, which is the
--   comparison this form makes pointwise.
-- PROBED: `Probed.Map-Frame` — twelve frames reached by RUNNING: each row
--   subscribes the source under a `map-f` frame, splits the burst the
--   subscription produced and hands the frame that, so the incoming
--   values are ones the source can emit rather than the strongest the
--   bound admits.  Both halves of the payload hypothesis are DECIDED, so
--   a source overrunning its own reading on either component leaves the
--   row unsolvable.  Four templates — wrapping, dropping for a literal,
--   the identity, and one that FOLDS over its argument's deliveries — at
--   three source depths, plus three sources differing only in how many
--   values the delivered observable carries.  The wrapping rows are tight
--   at every source, so one extra layer in a template's body would take
--   the conclusion out; the dropping rows are load-bearing at the two
--   deeper sources, where the payload falls to zero under a bound that
--   stays where the source left it.  The delivery triple is the one that
--   reaches what killed the predecessor currency: counts one, three, five
--   in and one, nine, twenty-five out, hops three, five, seven, tight at
--   each — the residue tracks the deliveries rather than saturating.
--   Not covered: every row is a SUBSCRIBE at the root, so nothing here
--   says what the frame does to a store a LATER frame wrote; one template
--   application per row, so no template whose own body maps again; the
--   finish flag is whatever the source's burst carried and is not varied;
--   and the context is closed, so no row reaches the slot telescope.
postulate
  map-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (κ : Path Γ lo u t) (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) →
    FrameCarries {e = e} ac id now (map-f fn) κ ψ
      Rin (mapRd ψ Rin fn) Rst

-- THE FOLD'S FRAME AT THE SAME RESIDUE, AND IT IS WRONG AS WRITTEN —
-- WHICH IS THE POINT OF WRITING IT.  A scan's per-value output is the
-- reading's own fold ITERATED once per delivery of the source, from the
-- accumulator the seed installed; the expression below is that
-- iteration run ONCE.  So the statement is exactly right on a burst of
-- one delivery and falls a layer short per delivery after that, and the
-- quantity it is missing is the REFOLD COUNT — neither the payload's
-- reading nor the store's hop, but the LENGTH of the list the frame is
-- handed, a third axis this predicate quantifies over unboundedly.
--
-- THE NARROWING IS WHAT THIS BUYS, and it is why the wrong statement is
-- worth standing here rather than a weaker true one.  The region that
-- can refute it was the whole of the payload currency; it is now bursts
-- of length above one at a template that folds, which is small enough to
-- instantiate and small enough to say what the repair has to carry.
--
-- AND THE MISSING AXIS IS NOT ONE QUANTITY BUT TWO, WHICH IS WHY NO
-- CHOICE OF THE OUTPUT BOUND REPAIRS THIS IN PLACE.  `FrameCarries`
-- hands a frame exactly two scalars: the payload bound, which is a
-- POINTWISE join over the list and so carries no cardinality at all,
-- and the store bound, which reads a scan node through the hop half of
-- that node's value alone.  A fold needs both halves back — how many
-- refolds, and what the accumulator it is refolding DELIVERS — and the
-- term reading already computes each: the refold count is the source's
-- own top component, and the accumulator is read as a full pair before
-- the store projects it away.  So the gap is in the walk's currency and
-- not in this statement's right-hand side, and that is what says the
-- repair is a restatement of the PREDICATE rather than of the leaf.
--
-- AND THE FRAME CANNOT BE RETIRED INSTEAD, which is the cheaper repair
-- one would reach for first: the fold is already stated at the burst
-- and at the seed where both quantities are in scope, so the walk's arm
-- looks redundant.  It is not.  A subscription over a slot REGISTERS
-- its whole path, this frame included, so a later arrival walks the
-- fold with no term anywhere in reach — the burst-and-seed form is
-- unavailable at exactly the point this arm is entered.
--
-- REFUTED: `Refuted.Scan-Store` — the symmetric form, pinning the fold's
--   residue at its own incoming bound.  It dies on the other side of the
--   same axis: a step that WRAPS its accumulator outruns any bound fixed
--   before the first refold, so neither the incoming pair nor one
--   application of the template is what a fold hands back.
postulate
  scan-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (κ : Path Γ lo u t) (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) →
    FrameCarries {e = e} ac id now (scan-f fn nid) κ ψ
      Rin (mapRd ψ Rin fn) Rst

-- THE PREFIX FRAME, WHICH THE WITNESS ABOVE DOES NOT REACH.  A take
-- hands back `takeVals`' prefix of the list it was given and writes a
-- node the reading prices at zero; the cutting arm additionally DROPS
-- registry entries, which can only lower the store's reading.  So
-- nothing here evaluates anything, and the equal-bounds form is the
-- right one for this frame even though it is the wrong one for its
-- neighbour.
--
-- PROBED: `Probed.Take-Frame` — seven frames reached by RUNNING, each
--   held to the TIGHTEST bounds the predicate admits: the payload PAIR
--   the frame was handed and the reading the store carried in.  Both
--   conjuncts compare something, which the source is built for — a fold
--   whose accumulator is an observable, so the payload reads positive
--   where a stream of nats would read zero, and whose node the store can
--   read where the take's own is priced at zero.  Five points are the
--   take arm's own subscription, at counts below, at and above what the
--   burst supplies and at two fold rates; the two below hand back
--   strictly less.  The fifth varies the accumulator's DELIVERY count
--   rather than its depth, which is the half of the pair the others
--   leave at one: what it is handed reads nine deliveries and the prefix
--   it returns reads three, so the count side is a cut rather than a
--   comparison of one against one.
--   Two more stand at a DRAIN STEP, after whole cascades have run, so
--   the node is one an earlier instant already charged and the store is
--   one an earlier instant's frames wrote — it reads three after one
--   instant and four after two, deeper than any subscription reaches,
--   and comes back tight at both.  The payload is tight there too and
--   climbs with the run, and the finish flag separates the arm's two
--   branches where no hop figure can.  A take is reached at an arrival
--   only BELOW a frame that adds depth, since every arrival's payload
--   is a slot's and a scripted slot is data-typed; and a node at ZERO
--   is not reachable at an arrival at all, because the cut that empties
--   the count severs the registry and the sweep drops the source.  NOT
--   covered: no row runs the frame over a store written by a chain it is
--   not part of.
postulate
  take-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (nid : NodeId)
    (κ : Path Γ lo s t) (ψ : Fin n → Rd₃) (Rv : Rd) (Rst : ℕ) →
    FrameCarries {e = e} ac id now (take-f {s = s} nid) κ ψ Rv Rv Rst

----------------------------------------------------------------------
-- THE SHELF HAS NO ENTRY FOR THE EXIT FRAME, AND THAT IS THE ARM EVERY
-- REGISTERED CHAIN IS MADE OF.  A flattener's own frame is CONSUMED the
-- moment its value is subscribed — the inner goes on under an exit
-- frame carrying the flattener's node, and the continuation below is
-- the one the outer already had.  So the arm priced directly below
-- appears on no registered chain at all: instantiated over flattener
-- stacks one to three deep, the same stacks behind a gate, and a capped
-- flattener across the steps of its own queue drain, the count of it on
-- the chains an arrival reaches is nought at every point, while the
-- exit frame's is the chain's whole length (`Probed.Chain-Compose`).
--
-- WHICH MAKES THE ABSENCE A CHOICE RATHER THAN AN OVERSIGHT, and the
-- two candidates are separated rather than argued.  `innerReact` hands
-- its payload back untouched on every branch but the completion one,
-- where the node's queue is drained and freshly subscribed inners'
-- bursts are appended — so an exit frame either threads what it was
-- handed or costs one as the frame above it does, and the two rules
-- disagree on a run this evaluator performs.  They agree wherever the
-- reading tracks the chain, and come apart behind a gate, whose figure
-- is a constant while the chain its body registers is as deep as the
-- body.  A rule chosen here therefore decides whether the tier's
-- premise holds at all, and the arm the rule would be chosen for is
-- stated somewhere else, which is the finding directly below.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- AND THE EXIT ARM IS STATED AT THE WALK RATHER THAN HERE, WHICH IS A
-- PLACEMENT FINDING AND NOT A GAP.  The chain walk
-- (`Verify-Rank-Sufficient.Path-Fits`) is the producer of a chain's
-- certificate and the only thing that ever stands at an exit frame, so
-- its carrying leaf sits beside it; this shelf's own consumer is the
-- subscribe walk, which descends a TERM and reaches no exit frame at
-- all.  An entry added here would be a second statement of the same
-- fact one module deeper than its consumer.
--
-- WHAT THIS SHELF CANNOT SUPPLY THE WALK, and it is why two of the
-- walk's arms are leaves at the PATH rather than steps assembled out
-- of these.  The burst arm of a fold is not a frame-carrying statement,
-- so a chain's steps cannot be composed out of the shelf as it stands.
-- And the map arm is pinned at the readings of a SOURCE EXPRESSION and
-- of its wrapping, which a chain step does not carry: a chain records
-- the frame, not the expression the frame was built from.  So a rule
-- for the map or scan head is owed at the path, where the whole tail is
-- in hand, and reaching for a third arm here would state something
-- nothing could consume.
----------------------------------------------------------------------

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
-- AND THE COUNT HALF IS A CLAIM THE WIDER CURRENCY NEWLY MAKES, WHICH
-- NOTHING HAS INSTANTIATED.  The outgoing reading is the incoming one
-- with its DEPTH raised and its DELIVERY COUNT left where it was, which
-- is what the reading's own flattening clause says: that clause carries
-- the source's middle component through untouched and takes `suc` of
-- the depth alone.  So the count half is not a weakening chosen here —
-- it is the machinery's answer read off — but the machinery's answer is
-- APPROXIMATE at this clause by construction, pricing what an arriving
-- inner delivers as what one of ITS deliveries delivers, and no row
-- anywhere stands at a payload whose two components differ.  Until one
-- does, this half of the statement is asserted and not evidenced.
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
--   and the margin is a constant one.  The DELIVERY half of the pair is
--   decided too: the hypothesis saturates at every row, so a source
--   delivering one more than its reading admits leaves the row
--   unsolvable, and the conclusion keeps a delivery of margin wherever
--   the outer carries two.  NOT reached: a frame whose rank is spent,
--   which no root can exhibit since a flattener's own reading is a
--   successor.
--
-- PROBED: `Probed.Hop-Store` — the same frame at a store that is
--   already deep, which is the configuration no other row on this shelf
--   reaches: the flattener's own node is installed holding parked
--   inners reading nought, one and two before the frame runs, and the
--   store bound is taken at the LEAST value the premise and the
--   incoming hypothesis admit, so nothing absorbs an over-deep write.
--   The payload hypothesis is decided at EQUALITY on BOTH components at
--   every row, and the count side does not move with the queue, which is
--   what says this family varies the store and nothing else.  What
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
--   have failed — the delivery half reads nought throughout at the gated
--   point and returns nothing under a bound of one at the open one.  What the two buy is the pair of pinned readings — the
--   body reads four, the open frame is held to four and the gated frame
--   to one — which is a finding about where an arrival's bound comes
--   from and is owed at the store reading's own definition.  NOT
--   covered: the arrival frame itself, which is the frame the finding
--   points at and which no row here runs.
postulate
  thru-outer-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (κ : Path Γ lo u t) (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) →
    suc (proj₂ Rin) ≤ Rst →
    FrameCarries {e = e} ac id now (thru-outer op nid) κ ψ
      Rin (proj₁ Rin , suc (proj₂ Rin)) Rst

----------------------------------------------------------------------
-- THE WALK, on the burst's spine.  Every emit contributes the frame's
-- outputs and nothing else, and the store is threaded emit by emit.
----------------------------------------------------------------------

pushBurst-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ lo u t)
  (burst : Stream Γ s) (sd : Sched Γ) (st : EvalSt e)
  (ψ : Fin n → Rd₃) (Rin Rv : Rd) (Rst : ℕ) →
  FrameCarries {e = e} ac id now f κ ψ Rin Rv Rst →
  burstRd ψ s burst ⊑ Rin → stHop ψ st ≤ Rst →
  burstRd ψ u (proj₁ (pushBurst ac id now f κ burst sd st)) ⊑ Rv
  × stHop ψ (proj₂ (proj₂ (pushBurst ac id now f κ burst sd st))) ≤ Rst
pushBurst-carried ac id now f κ []  sd st ψ Rin Rv Rst fc hb hs =
  (z≤n , z≤n) , hs
pushBurst-carried {Γ = Γ} {t = t} {e = e} {s = s} {u = u}
                  ac id now f κ (em ∷ ems) sd st ψ Rin Rv Rst fc hb hs =
  ( ⊔-lub (≤-trans (≤-reflexive (eq proj₁)) (proj₁ (proj₁ step)))
          (proj₁ (proj₁ ih))
  , ⊔-lub (≤-trans (≤-reflexive (eq proj₂)) (proj₂ (proj₁ step)))
          (proj₂ (proj₁ ih)) ) , proj₂ ih
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)

  sf = stepFrame ac id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sd st

  vals′ = proj₁ sf
  evs   = proj₁ (proj₂ sf)
  fin′  = proj₁ (proj₂ (proj₂ sf))
  sd₁   = proj₁ (proj₂ (proj₂ (proj₂ sf)))
  st₁   = proj₂ (proj₂ (proj₂ (proj₂ sf)))

  -- what this emit was handed, off the burst bound it entered with, at
  -- either component: the split is a partition and the join is
  -- pointwise, so one argument serves both
  hvals : valsRd ψ s (proj₁ sp) ⊑ Rin
  hvals =
    ≤-trans (≤-reflexive (splitEvents-valsAt proj₁ ψ s (InstEmit.events em)))
            (≤-trans (m≤m⊔n _ _) (proj₁ hb))
    , ≤-trans (≤-reflexive (splitEvents-valsAt proj₂ ψ s (InstEmit.events em)))
              (≤-trans (m≤m⊔n _ _) (proj₂ hb))

  step : valsRd ψ u vals′ ⊑ Rv × stHop ψ st₁ ≤ Rst
  step = fc (proj₁ sp) (proj₂ (proj₂ sp)) sd st hvals hs

  -- three of the four parts hold no payload at all
  eq : (p : Rd → ℕ) →
       emitAt p ψ u (proj₁ (proj₂ sp) ++ retagEvents evs ++ map value vals′
         ++ (if fin′ then complete ∷ [] else []))
       ≡ valsAt p ψ u vals′
  eq p = trans (emitAt-++ p ψ u (proj₁ (proj₂ sp)) _)
               (cong₂ _⊔_ (emitAt-bk p ψ s u (InstEmit.events em))
                 (trans (emitAt-++ p ψ u (retagEvents evs) _)
                        (cong₂ _⊔_ (emitAt-retag p ψ t u evs)
                                    (emitAt-values p ψ u vals′ fin′))))

  ih : burstRd ψ u (proj₁ (pushBurst ac id now f κ ems sd₁ st₁)) ⊑ Rv
     × stHop ψ (proj₂ (proj₂ (pushBurst ac id now f κ ems sd₁ st₁))) ≤ Rst
  ih = pushBurst-carried ac id now f κ ems sd₁ st₁ ψ Rin Rv Rst fc
         (≤-trans (m≤n⊔m _ _) (proj₁ hb) , ≤-trans (m≤n⊔m _ _) (proj₂ hb))
         (proj₂ step)

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
--   every family.  The DELIVERY half of the payload is its own axis and
--   six of the eight rows are degenerate there — a step re-wrapping one
--   copy leaves the count where the seed put it — so two rows re-wrap
--   two copies and three, where the count compounds once per refold to
--   sixty-four and to seven hundred and twenty-nine against six
--   refolds, and a reading flat in that rate crosses at the first.
--   Two axes are shown INERT rather than left unswept:
--   the continuation, since the fold's step names neither it nor the
--   clock, so every row is evidence at every continuation; and the
--   store's other nodes, since a fold carries them through untouched
--   and a deeper one raises the premise's reading by what it raises the
--   conclusion's.  No row reaches an arrival or a drain step, and no
--   row both deepens and multiplies at once.
postulate
  scan-burst-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u) (b : Closed Γ s)
    (ok : T (inputsBelowᵉ lo (scanᵉ f z b)))
    (nid : NodeId) (κ : Path Γ lo u t) (sd : Sched Γ) (st : EvalSt e)
    (ψ : Fin n → Rd₃) (Rst : ℕ) →
    depthᵉ ψ (scanᵉ f z b) ≤ Rst →
    let r  = subscribeE ac b (scan-f f nid ↠ κ) id now sd
               (installNode nid (scan-st {t = u} (evalTm z)) st)
        pb = pushBurst ac id now (scan-f f nid) κ
               (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
    in burstRd ψ s (proj₁ r) ⊑ proj₂ (rdᵉ ψ ε b) →
       stHop ψ (proj₂ (proj₂ r)) ≤ Rst →
       burstRd ψ u (proj₁ pb) ⊑ proj₂ (rdᵉ ψ ε (scanᵉ f z b))
       × stHop ψ (proj₂ (proj₂ pb)) ≤ Rst
