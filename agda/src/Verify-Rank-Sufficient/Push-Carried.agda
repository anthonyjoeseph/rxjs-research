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
open import Rx.Exp using (Ctx; Closed; Val; Fn; _×ᵗ_)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃)
open import Rx.Evaluator using (Stream; Frame; Path; Sched; EvalSt; NodeId;
  AllOp; map-f; scan-f; take-f; thru-outer; stepFrame; splitEvents;
  retagEvents; pushBurst; stHop)
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
-- THE THREE NON-FLATTENING FRAMES.  Each is a leaf rather than a body,
-- and for three different reasons the assembly above cannot supply: a
-- map's outputs are a TEMPLATE evaluated at the payload, which is the
-- one place the term reading's own plug clause has to be met; a scan's
-- outputs are the accumulator it is simultaneously rewriting, so both
-- halves move at once; and a take's are a prefix of what it was handed
-- under a node whose reading is zero by construction.
----------------------------------------------------------------------

postulate
  map-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) →
    FrameCarries {e = e} ac id now (map-f fn) κ ψ Rv Rv Rst

  scan-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) → Rv ≤ Rst →
    FrameCarries {e = e} ac id now (scan-f fn nid) κ ψ Rv Rv Rst

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
-- PROBED: `Probed.Hop-Edge` — six frames reached by RUNNING the
--   subscription the flattener arm builds, over all three operators, at
--   a fold that deepens its accumulator once and twice per delivery, at
--   two source lengths, and at one whose limit forces the PARK branch.
--   Every conjunct is positive at every row (the pins carry both sides)
--   and the margin is a constant one.  NOT reached: a frame whose rank
--   is spent, which no root can exhibit since a flattener's own reading
--   is a successor.
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
