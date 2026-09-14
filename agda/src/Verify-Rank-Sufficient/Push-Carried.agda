------------------------------------------------------------------
-- THE CARRIED FAMILY, ALL FIVE FRAMES, AT THE FULL AXIS SET, IN ONE
-- PASS.  A sketch: nothing here typechecks and nothing imports it yet.

-- WHAT THE SHELF IS.  `stepFrame⇓-total` is handed `HandedOK vals τ`
-- and nothing anywhere says what the frame HANDS BACK is bounded.  That
-- missing statement is the whole of what `subscribe-carried` is waiting
-- on, and it is per-frame: a burst pushed through a frame is bounded
-- iff each frame bounds its own output in terms of its input.

-- AND THE LESSON THAT DECIDES ITS SHAPE IS A MEASURED ONE.  The
-- predecessor of this family was discovered ONE FRAME AT A TIME, by
-- refutation, over weeks: the free equal-bounds form died to a template
-- that DROPS its argument, the symmetric pinned form died to a template
-- that WRAPS, and the fold's arm then sat at SHAPE for a third missing
-- axis — the length of the list the frame iterates.  Each refutation
-- killed a currency and each successor added a genuinely missing axis,
-- so the sequence was converging and not spiralling.  But the axis set
-- is KNOWN now, and going on discovering it a frame at a time is the
-- campaign re-learning one lesson five times.  So every frame below is
-- stated at the full set from the first line, including the frames
-- whose own arm does not obviously need it: an axis a frame ignores
-- costs that frame a `_` and costs the family nothing, and an axis a
-- frame turns out to need costs a restatement of all five.

-- THE AXIS SET, WHICH IS THREE AND NOT ONE.
--
--   · the PAYLOAD PAIR.  `ValOK` today reads an observable value's
--     DEPTH alone.  The hop re-seeds at BOTH lower components of the
--     triple — `(U , obsDepthᵉ o , syncSizeᵉ o)` — so a bound on one of
--     them cannot re-establish the entry invariant at the re-entry, and
--     a template that wraps its argument moves the size while leaving
--     the depth alone.  The pair is the same two numbers the triple's
--     lower half already is, which is what keeps it one currency.
--   · the STORE reading, unchanged: a frame may read and write a node,
--     and a fold's accumulator deepens in the store rather than in any
--     value.
--   · the ITERATION LENGTH.  A fold refolds once per delivery and a
--     walk subscribes once per delivery, so the output of both is the
--     transformer ITERATED `length vals` times.  This is the axis the
--     fold's arm was refuted for, and it is stated here for all five.

-- DEAD ROUTE: bounding a frame's output by its input alone, at ANY
--   choice of the output bound.  `FrameCarries` hands a frame two
--   scalars and a fold needs both halves of the pair back — how many
--   refolds, and what the accumulator it is refolding DELIVERS — so the
--   defect is in the predicate's currency and not in any leaf's
--   right-hand side.  That is what makes the repair a restatement of
--   the FAMILY rather than of whichever arm went red.

-- AND THE SUBSTITUTION LEMMA THEN COLLAPSES FOUR OF THE FIVE, WHICH IS
-- A CHANGE OF CURRENCY AND NOT A FIFTH RESTATEMENT.  Every refutation
-- this family has taken killed a price stated in terms of what the
-- frame was HANDED — a template that drops its argument, a template
-- that wraps it.  `Rx.Obs-Depth.Substitution` prices the same output in
-- terms of the TEMPLATE instead: what `map-f fn` emits is a
-- substitution instance of a subterm of `fn`, so its depth is
-- `obsDepthᵗ fn` less one, a reading of the PROGRAM that no value
-- handed in can move.  Neither refutation is a refutation of that, and
-- the input bound `Pin` drops out of four of the five leaves entirely.
-- What remains input-dependent is the fold, whose accumulator is fed
-- back, and that is the iteration axis this family already names.
module Verify-Rank-Sufficient.Push-Carried where

open import Data.Bool using (Bool; true)
open import Data.Bool.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Induction.WellFounded using (Acc)

open import Rx.Prim using (Id; Tick; InstEmit)
open import Rx.Exp using (Ctx; Closed; Ty; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
  Fn; isData; applyFn; syncSizeᵉ; syncSizeᵗ)
open import Rx.Obs-Depth using (obsDepthᵉ; obsDepthᵗ)
open import Rx.Obs-Depth.Substitution using (obsDepth-applyFn; syncSize-applyFn;
  dataSize)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; Frame; AllOp; NodeId;
  map-f; scan-f; take-f; from-inner; thru-outer; obsSt)
open import Rx.Evaluator.Run using (stepFrame; pushBurst)

------------------------------------------------------------------
-- 1.  THE PAYLOAD PAIR, WHICH REPLACES THE SCALAR `ValOK` READS.
------------------------------------------------------------------

-- the two numbers the triple's lower half is, read off a value.  Named
-- rather than inlined because every one of the five leaves below reads
-- it and a change here has to be a type error at all five.
Pay : Set
Pay = ℕ × ℕ            -- (syncSize , obsDepth)

_⊑_ : Pay → Pay → Set
(s₁ , d₁) ⊑ (s₂ , d₂) = s₁ ≤ s₂ × d₁ ≤ d₂

_⊔ᵖ_ : Pay → Pay → Pay
(s₁ , d₁) ⊔ᵖ (s₂ , d₂) = s₁ ⊔ s₂ , d₁ ⊔ d₂

valPay : ∀ {n} {Γ : Ctx n} {u} → Val Γ (obs u) → Pay
valPay o = syncSizeᵉ o , obsDepthᵉ o

-- THE TYPE SPLIT IS KEPT AND THE SCALAR IS WIDENED, which is the
-- smallest change that carries the finding.  `Refuted.Carried-Unranked`
-- killed the FLAT reading — asked of every value at every type — and the
-- split is what answered it; nothing about that answer is disturbed by
-- the leaf being a pair rather than a number.
ValOK : ∀ {n} {Γ : Ctx n} (u : Ty) → Pay → Val Γ u → Set
ValOK unitᵗ _ _ = ⊤
ValOK boolᵗ _ _ = ⊤
ValOK natᵗ  _ _ = ⊤
ValOK (s ×ᵗ t) P (a , b) = ValOK s P a × ValOK t P b
ValOK (s +ᵗ t) P (inj₁ a) = ValOK s P a
ValOK (s +ᵗ t) P (inj₂ b) = ValOK t P b
ValOK (obs t)  P o = proj₁ (valPay o) ≤ proj₁ P × proj₂ (valPay o) < proj₂ P
  -- STRICT in the depth and NON-strict in the size, and the asymmetry
  -- is the two guards: the hop compares depths strictly (an emitted
  -- observable is written strictly below the term that emitted it,
  -- since `obsDepthᵗ (strmᵗ e)` is a successor), while the μ peel
  -- compares sizes of the same term against itself.

HandedOK : ∀ {n} {Γ : Ctx n} {u} → List (Val Γ u) → Pay → Set
HandedOK {u = u} vs P = All (ValOK u P) vs

BurstOK : ∀ {n} {Γ : Ctx n} {s} → Stream Γ s → Pay → Set
BurstOK bs P = All (λ em → All (EventOK P) (InstEmit.events em)) bs

------------------------------------------------------------------
-- 2.  THE PREDICATE, AT ALL THREE AXES.
------------------------------------------------------------------

-- WHAT A FRAME IS ASKED.  Given a payload bound it is handed, a store
-- bound it is entered under, and the LENGTH of the list it is handed,
-- its outputs sit under the bound the leaf names and the store it
-- leaves sits under the same store bound.  The length is a parameter of
-- the OUTPUT bound rather than a hypothesis, which is the whole
-- difference from the predecessor: a leaf may ignore it (`take-f`
-- does), and a leaf that needs it can say so without any other leaf
-- being restated.
FrameCarries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ lo u t →
  Pay → (ℕ → Pay) → ℕ → Set
FrameCarries {Γ = Γ} {e = e} {s = s} {u = u} ac id now f κ Pin Pout Sst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    HandedOK vals Pin → obsSt st ≤ Sst →
    HandedOK (proj₁ (stepFrame ac id now f κ vals fin sd st))
             (Pout (length vals))
    × obsSt (proj₂ (proj₂ (proj₂ (proj₂
        (stepFrame ac id now f κ vals fin sd st))))) ≤ Sst

-- THE TEMPLATE'S OWN READING, AND IT TAKES NO INPUT BOUND.  This is
-- the whole of the currency change: the predecessor's `fnPay` was a
-- TRANSFORMER, `Pay → Pay`, priced at whatever the frame was handed,
-- and every refutation this family took was a refutation of some choice
-- of that transformer.  A template is a closed term, so what it emits
-- is a substitution instance of a subterm of it and its reading is a
-- constant — one the `+ dataSize s` on the size half is the only
-- concession to, since a substituted literal is larger than the `varᵗ`
-- it replaces while carrying no observable at all.
tmPay : ∀ {n} {Γ : Ctx n} {s u} → Fn Γ [] [] [] s u → Ty → Pay
tmPay fn s = syncSizeᵗ fn + dataSize s , obsDepthᵗ fn

-- and its iteration, which is the axis the fold was refuted for.  `n`
-- is the length of the list the frame is handed; a frame that does not
-- iterate takes the transformer at zero and gets its input back.
iter : (Pay → Pay) → ℕ → Pay → Pay
iter g zero    P = P
iter g (suc k) P = g (iter g k P)

------------------------------------------------------------------
-- 3.  THE FIVE LEAVES, STATED TOGETHER.
------------------------------------------------------------------

-- All five in one block, deliberately: the block is the claim that the
-- axis set is settled, and a sixth frame or a sixth axis is a restatement
-- of the block rather than an addition to a shelf.  What varies between
-- them is now only WHETHER THE INPUT BOUND APPEARS AT ALL, and it does
-- so in exactly one.
--
-- What each leaf says, in one line apiece:
--
--   map-f      the TEMPLATE's own reading, and `Pin` does not occur.
--              Every value out of a map is `applyFn fn v`, a
--              substitution instance of a subterm of `fn`, so the
--              output's depth is a reading of the program and the two
--              template refutations cannot touch it.  Applied ONCE
--              however long the list is — a map distributes, it does
--              not iterate.
--   scan-f     the ONE leaf that still takes its input bound, because
--              it is the one frame whose own output is fed back into
--              the environment it evaluates under.  `iter` is that
--              feedback, and the substitution lemma says exactly why it
--              cannot be avoided: an accumulator at observable type
--              makes the environment non-data, which is the single
--              condition under which a template's reading is not
--              static.
--   take-f     identity.  A take hands back a PREFIX of what it was
--              given under a node the reading prices at zero, and its
--              cutting arm only drops registry entries.
--   thru-outer the hop, and it now hands back what the INNER's own
--              subscription produced.  Its premise used to have to be
--              carried in; with the substitution lemma the inner was
--              already written strictly below the template that emitted
--              it, one frame down.
--   from-inner the exit frame, and it is NOT the identity even though
--              nothing is evaluated: a `mergeAll` drain grafts a QUEUED
--              inner's flush into the same step, so what comes back can
--              be a value the frame was never handed.  Bounded by the
--              node's own queue, which the store bound covers — hence
--              iterated at the store's transformer rather than at the
--              payload's.

-- THE MAP LEAF, AS A REAL BODY.  It is a list induction and one
-- application of the substitution corollary per element; nothing about
-- the machine is consulted, which is what makes it writable at all.
map-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) → isData s ≡ true →
  FrameCarries {e = e} ac id now (map-f fn) κ
    Pin (λ _ → tmPay fn s) Sst
map-frame-carried ac id now fn κ Pin Sst ds vals fin sd st hk sk =
  map-handed fn ds vals , sk
  where
  map-handed : ∀ {n} {Γ : Ctx n} {s u} (fn : Fn Γ [] [] [] s u) →
    isData s ≡ true → (vs : List (Val Γ s)) →
    HandedOK (map (applyFn fn) vs) (tmPay fn s)
  map-handed fn ds []       = []ᵃ
  map-handed fn ds (v ∷ vs) = applyFn-ok fn ds v ∷ᵃ map-handed fn ds vs

-- one value's worth, at the result type.  Only the observable arm has
-- content; at every data type `ValOK` is `⊤` or a pair of them.
applyFn-ok : ∀ {n} {Γ : Ctx n} {s u} (fn : Fn Γ [] [] [] s u) →
  isData s ≡ true → (v : Val Γ s) → ValOK u (tmPay fn s) (applyFn fn v)
applyFn-ok {u = unitᵗ}   fn ds v = tt
applyFn-ok {u = boolᵗ}   fn ds v = tt
applyFn-ok {u = natᵗ}    fn ds v = tt
applyFn-ok {u = a ×ᵗ b}  fn ds v = applyFn-ok-× fn ds v
applyFn-ok {u = a +ᵗ b}  fn ds v = applyFn-ok-+ fn ds v
applyFn-ok {u = obs w}   fn ds v =
  syncSize-applyFn ds fn v , obsDepth-applyFn ds fn v
  -- the second component IS the door's guard, discharged from the
  -- program with no bound carried in

postulate
  -- the two structural arms, which push the corollary under a pair or
  -- an injection.  Mechanical, and separated only because `ValOK`
  -- recurses on the type while `applyFn` does not.
  applyFn-ok-× : ∀ {n} {Γ : Ctx n} {s a b} (fn : Fn Γ [] [] [] s (a ×ᵗ b)) →
    isData s ≡ true → (v : Val Γ s) → ValOK (a ×ᵗ b) (tmPay fn s) (applyFn fn v)
  applyFn-ok-+ : ∀ {n} {Γ : Ctx n} {s a b} (fn : Fn Γ [] [] [] s (a +ᵗ b)) →
    isData s ≡ true → (v : Val Γ s) → ValOK (a +ᵗ b) (tmPay fn s) (applyFn fn v)

  -- MAP OVER OBSERVABLES, which is the same open form the fold has.
  -- When the element type is itself an observable the environment the
  -- template evaluates under is not data, so the output's reading is
  -- the template's PLUS the incoming one.  Not a different mechanism —
  -- `Rx.Obs-Depth.Substitution.obsDepth-eval-open` is the statement.
  map-frame-carried-obs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (map-f fn) κ
      Pin (λ _ → tmPay fn s ⊔ᵖ Pin) Sst

  -- THE ONE LEAF THAT IS STILL A FUNCTION OF ITS INPUT, and after the
  -- substitution lemma it is the only genuinely dynamic quantity on
  -- this face.  The accumulator is a `Val` the store holds and the
  -- template is re-applied to it once per delivery, so at an
  -- accumulator type carrying an observable the environment is non-data
  -- at every refold and the reading grows by the template's own per
  -- step.  Bounded by the delivery count, which is what `iter` at
  -- `length vals` is.
  scan-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (scan-f fn nid) κ
      Pin (λ k → iter (λ P → tmPay fn (u ×ᵗ s) ⊔ᵖ P) k Pin) Sst

  take-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (nid : NodeId)
    (κ : Path Γ lo s t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (take-f {s = s} nid) κ
      Pin (λ _ → Pin) Sst

  thru-outer-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (thru-outer op nid) κ
      Pin (λ k → iter (λ P → P) k (proj₁ Pin , inner-depth Pin)) Sst

  from-inner-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp)
    (allNid inst : NodeId)
    (κ : Path Γ lo s t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (from-inner op allNid inst) κ
      Pin (λ k → iter (λ P → P ⊔ᵖ (Sst , Sst)) k Pin) Sst

-- the strict drop the hop's own guard is, read off the pair.  It is
-- `pred` on the depth and the identity on the size — an inner is
-- written strictly shallower than the term that emitted it, and nothing
-- says it is SMALLER, which is exactly why the triple's two lower
-- components are separate axes and not one.
inner-depth : Pay → ℕ
inner-depth (_ , zero)  = zero
inner-depth (_ , suc d) = d

------------------------------------------------------------------
-- 4.  THE ASSEMBLY, WHICH IS WHAT MAKES THE FIVE LEAVES LEAVES.
------------------------------------------------------------------

-- one real body dispatching on the frame, so each leaf's FIT is tested
-- the moment it is proven rather than asserted by a `-core`'s
-- hypothesis list.  The `Pout` a caller gets back is the frame's own
-- transformer, which is why this returns a Σ rather than taking the
-- bound as an argument: the caller does not get to choose it.
stepFrame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) →
  Σ (ℕ → Pay) (λ Pout → FrameCarries {e = e} ac id now fr κ Pin Pout Sst)
stepFrame-carried ac id now (map-f {s = s} fn) κ Pin Sst with isData s ≟ true
... | yes ds = _ , map-frame-carried ac id now fn κ Pin Sst ds
... | no  _  = _ , map-frame-carried-obs ac id now fn κ Pin Sst
  -- THE SPLIT IS THE FINDING, AND IT IS DECIDABLE ON THE TYPE.  A map
  -- whose element type is data prices its output at the template alone;
  -- a map over observables is the open form.  Nothing about the run
  -- distinguishes them, which is why the test sits here and not inside
  -- a leaf.
stepFrame-carried ac id now (scan-f fn nid) κ Pin Sst =
  _ , scan-frame-carried ac id now fn nid κ Pin Sst
stepFrame-carried ac id now (take-f nid) κ Pin Sst =
  _ , take-frame-carried ac id now nid κ Pin Sst
stepFrame-carried ac id now (thru-outer op nid) κ Pin Sst =
  _ , thru-outer-frame-carried ac id now op nid κ Pin Sst
stepFrame-carried ac id now (from-inner op allNid inst) κ Pin Sst =
  _ , from-inner-carried ac id now op allNid inst κ Pin Sst

-- and the burst walk, which is the list induction over emits.  Each
-- emit is split, stepped at the frame's own transformer, and reassembled
-- — so the bound the whole burst comes back at is the transformer taken
-- at the LONGEST emit, which is the join the `⊔ᵖ` above is for.
pushBurst-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u)
  (κ : Path Γ lo u t) (burst : Stream Γ s) (Pin : Pay) (Sst : ℕ) →
  BurstOK burst Pin → obsSt st ≤ Sst →
  BurstOK (proj₁ (pushBurst ac id now f κ burst sd st))
          (proj₁ (stepFrame-carried ac id now f κ Pin Sst) (burstWidth burst))
pushBurst-carried ac id now f κ [] Pin Sst bk sk = []ᵃ
pushBurst-carried ac id now f κ (em ∷ ems) Pin Sst (b ∷ᵃ bs) sk =
  emit-ok (proj₂ (stepFrame-carried ac id now f κ Pin Sst)
             (proj₁ (splitEvents (InstEmit.events em))) _ _ _
             (split-handed (InstEmit.events em) b) sk)
    ∷ᵃ pushBurst-carried ac id now f κ ems Pin Sst bs _

-- the bound a burst comes back at, as the consumer sees it: the frame's
-- own transformer taken at the burst's width.  Named because
-- `subscribe-carried`'s clauses all widen from it back to the triple,
-- and a clause spelling it out is a clause that drifts when a leaf's
-- transformer moves.
Pout-of : Tri → ℕ → Pay
Pout-of τ k = iter (λ P → P) k (payOf τ)

-- the longest emit in a burst: the iteration count the transformer is
-- taken at, since every emit is stepped separately and the bound has to
-- cover all of them
burstWidth : ∀ {n} {Γ : Ctx n} {s} → Stream Γ s → ℕ
burstWidth [] = zero
burstWidth (em ∷ ems) =
  length (proj₁ (splitEvents (InstEmit.events em))) ⊔ burstWidth ems

------------------------------------------------------------------
-- 5.  WHAT THIS PAYS, WHICH IS THE DOOR.
------------------------------------------------------------------

-- `subscribe-carried` becomes a real body over this: a subscribe's
-- burst is its source's burst pushed through the frames its own term
-- installs, so every structural clause of `subscribeE` spends
-- `pushBurst-carried` at its own frame and the flattener clauses spend
-- it at `thru-outer`.  The leaves that remain are the ones no frame
-- answers — the source's own burst, which is `Refuted.Carried-Shared`'s
-- slot conjunct and belongs to the schedule rather than to any frame.
--
-- AND THE DOOR IS PAID ONE FRAME LOWER THAN ANYONE WAS LOOKING.  The
-- hop's guard asks `obsDepthᵉ o <? r` of a value a `thru-outer` frame
-- was handed — and where that value came from a template, the strict
-- comparison was already true of the TEMPLATE, before any frame saw it.
-- `applyFn-ok` at the observable arm IS the guard, and it is discharged
-- from `obsDepthᵗ fn` with nothing carried in.  So the leaf the door
-- needs is `map-frame-carried`, which is written, and not
-- `thru-outer-frame-carried`, which is not: the hop only has to pass
-- the reading ALONG.
--
-- What is left for the hop to answer is the one shape a template does
-- not produce: an observable delivered by a SOURCE rather than written
-- by a term.  That is a claim about the registry, which is where
-- `Refuted.Carried-Shared` already sends it.
postulate
  subscribe-carried-schedule : ∀ {n} {Γ : Ctx n} {u} (o : Val Γ (obs u))
    (P : Pay) → ValOK (obs u) P o → obsDepthᵉ o < proj₂ P
