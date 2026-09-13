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
open import Data.Nat using (ℕ; _⊔_; _≤_; z≤n)
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
  map-f; scan-f; take-f; stepFrame; splitEvents; retagEvents; pushBurst; stHop)
open import Verify-Rank-Sufficient.Carried using (valsHop; emitHop; burstHop;
  emitHop-++; emitHop-values; emitHop-bk; emitHop-retag; splitEvents-vals)

----------------------------------------------------------------------
-- A FRAME THAT DEEPENS NOTHING: its outputs read under the payload
-- bound it was handed, and whatever it writes leaves the store under
-- the store bound.  This is the hypothesis the walk's four
-- non-flattening operators run on.
----------------------------------------------------------------------

FrameCarries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t →
  (Fin n → Rd₃) → ℕ → ℕ → Set
FrameCarries {Γ = Γ} {e = e} {s = s} {u = u} ac id now f κ ψ Rv Rst =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    valsHop ψ s vals ≤ Rv → stHop ψ st ≤ Rst →
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
    FrameCarries {e = e} ac id now (map-f fn) κ ψ Rv Rst

  scan-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) → Rv ≤ Rst →
    FrameCarries {e = e} ac id now (scan-f fn nid) κ ψ Rv Rst

  take-frame-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (nid : NodeId)
    (κ : Path Γ s t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) →
    FrameCarries {e = e} ac id now (take-f {s = s} nid) κ ψ Rv Rst

----------------------------------------------------------------------
-- THE WALK, on the burst's spine.  Every emit contributes the frame's
-- outputs and nothing else, and the store is threaded emit by emit.
----------------------------------------------------------------------

pushBurst-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (burst : Stream Γ s) (sd : Sched Γ) (st : EvalSt e)
  (ψ : Fin n → Rd₃) (Rv Rst : ℕ) →
  FrameCarries {e = e} ac id now f κ ψ Rv Rst →
  burstHop ψ s burst ≤ Rv → stHop ψ st ≤ Rst →
  burstHop ψ u (proj₁ (pushBurst ac id now f κ burst sd st)) ≤ Rv
  × stHop ψ (proj₂ (proj₂ (pushBurst ac id now f κ burst sd st))) ≤ Rst
pushBurst-carried ac id now f κ []  sd st ψ Rv Rst fc hb hs = z≤n , hs
pushBurst-carried {Γ = Γ} {t = t} {e = e} {s = s} {u = u}
                  ac id now f κ (em ∷ ems) sd st ψ Rv Rst fc hb hs =
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
  hvals : valsHop ψ s (proj₁ sp) ≤ Rv
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
  ih = pushBurst-carried ac id now f κ ems sd₁ st₁ ψ Rv Rst fc
         (≤-trans (m≤n⊔m _ _) hb) (proj₂ step)
