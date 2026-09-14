------------------------------------------------------------------
-- THE CARRIED BOUND: a sketch of the evaluator change that kills the
-- door, written as declarations rather than as prose because the whole
-- point is the SHAPE of the clauses.

-- NOTHING HERE TYPECHECKS AND NOTHING IMPORTS IT.  It is a design
-- handover: `Rx.Evaluator` is the file that has to change, this module
-- says how, and it is deleted in the commit that makes the change.  It
-- redeclares the three declarations the change touches — the frame, the
-- hop and the *All install — so that a reader can diff them against the
-- real ones without reading a paragraph describing a diff.
------------------------------------------------------------------

-- WHAT THE DOOR IS AND WHY IT CANNOT BE CLOSED WHERE IT STANDS.  The
-- hop asks `obsDepthᵉ o <? r`: `r` is the rank the machine is standing
-- at, and `o` is a runtime VALUE that arrived up a chain.  Nothing
-- relates the two, because nothing about the caller's TERM constrains
-- what a flattener's outer will emit — so the machine has to ask, and
-- the negative arm is the dry marker.  Every syntactic figure that
-- tried to PRICE that comparison in advance died, and `Refuted.Dry-Wrap`
-- is why: a value deepens on the way out, so a seed dominating the term
-- does not dominate the run.

-- THE CARRIED BOUND MOVES THE QUESTION TO THE INSTALL SITE, WHERE IT IS
-- ABOUT A TERM AGAIN.  A `thru-outer` frame is minted exactly once per
-- flattener node, by `subscribeAll`, at a point where the machine holds
-- both the rank it is standing at and the outer EXPRESSION `b`.  Let the
-- frame carry the rank its inners will be subscribed at, and let the hop
-- READ it rather than measure the value.  Then the hop takes no
-- decision: it re-seeds at the carried figure and the drop is `ρ < suc
-- ρ`, which is free.  The arm disappears, and with it the only
-- `dryEvent` the subscribe cycle can produce.

-- AND THE RESIDUE IS DISCHARGEABLE, WHICH IS THE WHOLE CLAIM.  Handing
-- `ρ` down requires the machine to be standing at `suc ρ`, so the
-- install site case-splits the rank and owes the `zero` arm.  That arm
-- is about the TERM being subscribed — a flattener whose outer carries
-- observables is written at rank at least one, since `obsDepthᵗ (strmᵗ
-- e)` is a `suc` — so the entry invariant discharges it.  That is the
-- asymmetry the leg rests on: the hop's arm was a claim about a value no
-- hypothesis mentions, and the install's arm is a claim about a
-- subexpression the entry invariant already bounds.

-- DEAD ROUTE: paying the hop's premise as an ARGUMENT — threading
--   `HandedOK (o ∷ []) τ` into `subscribeInner` and spending it for
--   `ltR`.  It closes the arm and is honest, and it makes the evaluator
--   a proof-carrying function: every caller up to `evaluate` acquires an
--   obligation, and the impl stops mirroring anything a plain rxjs
--   pipeline can do.  That is the one line this repo does not cross.
module Rx.Evaluator.Carried where

open import Data.Bool using (Bool; false)
open import Data.Nat  using (ℕ; zero; suc; _<_; _≤_; n<1+n)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Induction.WellFounded using (Acc; acc)

open import Rx.Prim using (Tick; Id; InstEvent)
open import Rx.Exp  using (Ty; obs; Ctx; Val; Closed; syncSizeᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Strat-Order using (Tri; _≺_; ltR)
open import Rx.Evaluator using (AllOp; NodeId; NodeState; Frame; Path; _↠_;
  Sched; EvalSt; Stream; mintNode; installNode; subscribeE; pushBurst;
  splitBurst; mergeAllᵒ)

variable
  τ  : Tri
  lo : ℕ

------------------------------------------------------------------
-- 1.  THE FRAME GROWS A FIELD, AND ONLY ONE OF THEM DOES.
------------------------------------------------------------------

-- `from-inner` is unchanged: it is an EXIT frame and takes no
-- subscription decision.  `thru-outer` is the one that receives inner
-- observables, so it is the one that says at what rank they are taken.
-- ρ is a plain ℕ — the frame stays a first-order value the way every
-- other field of it is, which is what keeps `evaluate` a function rxjs
-- could mirror.
data Frame′ {n} (Γ : Ctx n) : Ty → Ty → Set where
  thru-outer : ∀ {u} → AllOp → NodeId → (ρ : ℕ) → Frame′ Γ (obs u) u
               -- ρ: the rank this node's inners are subscribed at.
               -- Set once, at install, from the rank the installing
               -- clause is standing at; never recomputed, never
               -- compared against anything a value carries.

-- the other four constructors are copied through unchanged and are
-- omitted here rather than restated, since a sketch that restates them
-- is a second copy of the real datatype

------------------------------------------------------------------
-- 2.  THE HOP LOSES ITS `with`, ITS `no` ARM AND ITS DRY EVENT.
------------------------------------------------------------------

-- Against the real `subscribeInner`, the diff is: the `obsDepthᵉ o <? r`
-- test is gone, the `no` arm (`close drySource dried ∷ []`) is gone, and
-- the recursive witness comes from `n<1+n ρ` instead of from the test's
-- proof.  The rank the inner is subscribed at is ρ, NOT `obsDepthᵉ o` —
-- the value's own depth is never read.
--
-- The signature is what carries the change: the caller's rank is now
-- `suc ρ` rather than an arbitrary `r`, which is exactly the statement
-- "a frame carrying ρ can only be stepped by a machine standing one
-- above it".  Every consumer of the τ variable at this site inherits it.
subscribeInner′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {U ρ s}
                → Acc _≺_ (U , suc ρ , s)
                → AllOp → NodeId → Path Γ lo u t → Id → Tick
                → Val Γ (obs u) → Sched Γ → EvalSt e
                → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t))
                    × Bool × Sched Γ × EvalSt e
subscribeInner′ {ρ = ρ} (acc rec) op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
      (burst , sched′ , st′) =
        subscribeE (rec (ltR {r′ = ρ} {s′ = syncSizeᵉ o} (n<1+n ρ)))
                   o (from-inner op allNid inst ↠ κ) id now
                   (record sched { nextNode = suc inst }) st
      (vs , bs , done) = splitBurst burst
  in inst , vs , bs , done , sched′ , st′

-- THE THREE `thruConsume` CALL SITES CHANGE BY READING ρ OFF THE FRAME
-- RATHER THAN BY BEING REWRITTEN.  Each already looks the node up; the
-- frame it was stepped from is the one that carries ρ, so ρ arrives
-- where `nid` does and no site acquires an argument it did not have.

------------------------------------------------------------------
-- 3.  THE INSTALL SITE IS WHERE THE CASE MOVES TO.
------------------------------------------------------------------

-- `subscribeAll` is the only minter of a `thru-outer`.  It now splits
-- the rank it is standing at: at `suc ρ` it hands ρ to the frame, and at
-- `zero` it has nothing to hand down.  That second arm is the residue,
-- and it is the whole reason this route is better than the door — see
-- `all-entry-pos` below for what kills it.
subscribeAll′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {U r s}
              → Acc _≺_ (U , r , s)
              → AllOp → NodeState Γ → (b : Closed Γ (obs u))
              → Path Γ lo u t
              → Id → Tick → Sched Γ → EvalSt e
              → Stream Γ u × Sched Γ × EvalSt e
subscribeAll′ {r = suc ρ} fuel op initialState b κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE fuel b (thru-outer op nid ρ ↠ κ) id now sched₁
                   (installNode nid initialState st)
  in pushBurst fuel id now (thru-outer op nid ρ) κ burst sched₂ st₁
subscribeAll′ {r = zero} fuel op initialState b κ id now sched st =
  -- UNREACHABLE, and the `all-entry-pos-*` trio below is what says so.
  -- The arm cannot be closed HERE, because `subscribeAll` no longer
  -- knows which operator's clause called it: the entry bound belongs to
  -- the caller's term, so the split moves UP into `subscribeE`'s three
  -- *All clauses and each spends its own.  Stated this way round only
  -- because the frame change is what the reader is being shown.
  -- It must NEVER become a dry emission, which would be the door
  -- rebuilt one clause over.
  ⊥-elim (all-entry-pos-merge b entry-ok)

------------------------------------------------------------------
-- 4.  THE RESIDUE, WHICH IS A FACT ABOUT THE TERM.
------------------------------------------------------------------

-- A flattener's outer has element type `obs u`, so any literal stream
-- of inners inside it goes through `obsDepthᵗ (strmᵗ e) = suc
-- (obsDepthᵉ e)` and the flattener is written at rank at least one.
-- Under the entry invariant `obsDepthᵉ b ≤ r`, the machine standing at
-- an *All therefore stands at `r > 0`.
--
-- Stated over the three constructors separately rather than over a
-- predicate, because the three clauses of `subscribeE` that call
-- `subscribeAll` are what have to spend it, and each knows which one it
-- is.
postulate
  all-entry-pos-merge : ∀ {n} {Γ : Ctx n} {u} {lim}
    (b : Closed Γ (obs (obs u))) {r}
    → obsDepthᵉ (mergeAllᵉ lim b) ≤ r → 0 < r
  all-entry-pos-switch : ∀ {n} {Γ : Ctx n} {u}
    (b : Closed Γ (obs (obs u))) {r}
    → obsDepthᵉ (switchAllᵉ b) ≤ r → 0 < r
  all-entry-pos-exhaust : ∀ {n} {Γ : Ctx n} {u}
    (b : Closed Γ (obs (obs u))) {r}
    → obsDepthᵉ (exhaustAllᵉ b) ≤ r → 0 < r

-- AND THE BOUND ρ IS NOT CLAIMED TO DOMINATE THE INNERS, WHICH IS THE
-- part that looks wrong and is not.  Termination no longer needs it: the
-- descent is `ρ < suc ρ` whatever arrives.  What needs it is the PROOF
-- that the run is the intended one, and that is leg 2's
-- `subscribe-carried` / `burst-handed` — the statement that a burst
-- delivered under a node installed at ρ carries only values of depth
-- ≤ ρ.  So the leg order is: this change makes the evaluator total with
-- no dry arm, and leg 2 then proves the ranks it carries are the right
-- ones.  A wrong ρ under this design is a proof obligation that fails,
-- never a run that emits a marker.

------------------------------------------------------------------
-- 5.  WHAT HAPPENS TO THE DOMAIN RELATION AND TO `hasDry`.
------------------------------------------------------------------

-- `subscribeInner⇓` already has exactly one constructor, whose premise
-- is a real sub-derivation of `subscribeE⇓`.  Today that single
-- constructor is what makes the `no` arm unrelatable — a derivation at
-- the machine's result cannot exist unless the guard passed.  After this
-- change the guard is gone and the constructor is TOTAL: every call has
-- a derivation, `subscribeInner⇓-total` needs no premise about `o`, and
-- `HandedOK` drops out of its signature.
--
-- `Refuted.Dry-Wrap` goes RED at the same commit, because its three
-- `hasDry (evaluate … ) ≡ true` rows are `refl` against an evaluator that
-- no longer has the clause producing them.  That is the tier's close
-- condition: `rank-sufficient` becomes true not when the premise is
-- assumed but when the arm is DELETED, and the refutation going red is
-- the machine saying so.  The two remaining dry sites — `sharedConnect`
-- and the `μᵉ` peel — are unaffected and are the other legs' business.
