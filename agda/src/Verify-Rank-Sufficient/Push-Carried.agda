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
module Verify-Rank-Sufficient.Push-Carried where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc)

open import Rx.Prim using (Id; Tick; InstEvent; InstEmit)
open import Rx.Exp using (Ctx; Closed; Ty; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
  Fn; syncSizeᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; Frame; AllOp; NodeId;
  map-f; scan-f; take-f; from-inner; thru-outer; stepFrame; pushBurst; obsSt)

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

-- the template's reading, applied to the bound the frame was entered
-- under.  Spelled once because three of the five leaves spend it, so a
-- change to it is a type error at all three rather than a silent
-- disagreement between them.
postulate
  fnPay : ∀ {n} {Γ : Ctx n} {s u} → Fn Γ [] [] [] s u → Pay → Pay

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
-- of the block rather than an addition to a shelf.  The transformer is
-- the only thing that varies between them.
--
-- What each transformer says, in one line apiece:
--
--   map-f      the template read at the incoming pair, joined with the
--              incoming pair because a template may DROP its argument
--              and leave the source's own reading standing.  Applied
--              ONCE however long the list is — a map does not iterate,
--              it distributes.
--   scan-f     the same template ITERATED once per delivery, from the
--              accumulator the seed installed.  This is the arm the
--              predecessor stated at one application and was refuted
--              for; the fix is `iter`, not a different right-hand side.
--   take-f     identity.  A take hands back a PREFIX of what it was
--              given under a node the reading prices at zero, and its
--              cutting arm only drops registry entries.  The
--              equal-bounds form is right here and only here, and the
--              length is ignored — which is what the family's shape is
--              for.
--   thru-outer the hop, and the one leaf whose output is STRICTLY
--              shallower: each value is an inner observable, subscribed,
--              and its burst is what comes back.  So the output is read
--              at the INNER's pair, which `ValOK (obs u)` already says
--              is below the incoming one.  Iterated, because the walk
--              consumes every value in the list and each consume can
--              write the store the next reads.
--   from-inner the exit frame, and it is NOT the identity even though
--              nothing is evaluated: a `mergeAll` drain grafts a QUEUED
--              inner's flush into the same step, so what comes back can
--              be a value the frame was never handed.  Bounded by the
--              node's own queue, which the store bound covers — hence
--              iterated at the store's transformer rather than at the
--              payload's.
postulate
  map-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (map-f fn) κ
      Pin (λ _ → fnPay fn Pin ⊔ᵖ Pin) Sst

  scan-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (κ : Path Γ lo u t) (Pin : Pay) (Sst : ℕ) →
    FrameCarries {e = e} ac id now (scan-f fn nid) κ
      Pin (λ k → iter (λ P → fnPay fn P ⊔ᵖ P) k Pin) Sst

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
stepFrame-carried ac id now (map-f fn) κ Pin Sst =
  _ , map-frame-carried ac id now fn κ Pin Sst
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
-- AND THE DOOR IS DOWNSTREAM OF IT RATHER THAN BESIDE IT.  The hop's
-- guard asks `obsDepthᵉ o <? r` of a value a frame handed on; what
-- `thru-outer-frame-carried` says is that such a value's depth is
-- strictly below the bound the frame was entered under.  So the `no`
-- arm is unreachable the moment this family holds, and the clause can
-- then be DELETED from `Rx.Evaluator` — which is what takes
-- `Refuted.Dry-Wrap` red and `rank-sufficient` true.  Killing the door
-- is not a separate mechanism to invent; it is this shelf, spent.
postulate
  subscribe-carried-schedule : ∀ {n} {Γ : Ctx n} {u} (o : Val Γ (obs u))
    (P : Pay) → ValOK (obs u) P o → obsDepthᵉ o < proj₂ P
