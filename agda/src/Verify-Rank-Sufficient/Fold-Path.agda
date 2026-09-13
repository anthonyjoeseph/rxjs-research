------------------------------------------------------------------
-- ONE CHAIN, FOLDED — and then every chain an arrival reaches.  This
-- is the composition the shelf was always for: the per-template
-- obligations are threaded down the path by the fold, and what comes
-- out the other end is dry-freedom of the whole cascade.
--
-- THE THREE ARMS ARE THREE DIFFERENT ARGUMENTS AND NOT THREE CASES OF
-- ONE.  A root builds its own event list out of a payload run and a
-- completion, neither of which can hold a close at all, so it asks the
-- fit for nothing — which is exactly why `at-root` is a constructor
-- with no field.  A sink ends the chain and hands the values to every
-- chain registered on the share, so the only thing that can speak for
-- the fan-out is the sink's own obligation.  And a frame is the one
-- place a number is spent: what it emits is decided by the shelf's dry
-- clause, and what it HANDS ON is decided by the shelf's carrying
-- clause, which is what lets the tail's obligation be stated at a
-- bound the frame produced rather than at the one the chain entered
-- with.
--
-- SO THE PAYLOAD BOUND IS THREADED AND THE STORE BOUND IS NOT.  Each
-- frame hands the next a bound of its own choosing, which is the
-- existential in `through`; the store bound is the same number the
-- whole chain through, because a frame that writes a node is obliged
-- to leave the store under the bound it found it under.  A statement
-- threading both would be strictly weaker and would need a second
-- existential nothing ever instantiates.
--
-- AND NOTHING HERE KNOWS WHAT A RANK IS.  The arithmetic lives in the
-- shelf, one template at a time; this module only applies it in the
-- order the machine applies the templates.  That is what makes it a
-- structural induction on the fit rather than on the path: the fit's
-- own `through` carries the tail's bound, so there is no point at
-- which a number has to be guessed.
--
-- TWIN: `Verify-Well-Formed.Part9.foldPath-wf` — the same fold, the
--   same three arms, the same threading of the witness; and
--   `Verify-Well-Formed.Part12.cascadeGo-wf` for the chain list.  Both
--   are proven, and the correspondence is clause for clause, which is
--   what says the induction below is the one the machine performs.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Fold-Path where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; suc; _≡ᵇ_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ⊔-identityʳ;
  m≤m⊔n; m≤n⊔m; m≤n+m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick; Id; Source; InstEvent; value;
  close; complete; handoff; exhausted; delivery; _at_from_as_)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; depthᵉ; depthᵛ; rdᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; Sched; EvalSt; RegId; Arrival;
  arrTy; arrVal; arrTick; arrSource; arrivalWitness;
  foldPath; shareGo; shareAdmit; shareLatch;
  chainStep; cascadeGo; dispatchShare; stepFrame; dryEvent; hasDry;
  stHop)
open import Verify-Rank-Sufficient.Carried using (valsRd; _⊑_)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-++; hasDry-single)
open import Verify-Rank-Sufficient.Push-Dry using (any-dry-++; tailPart-dry)
open import Verify-Rank-Sufficient.Fits using (PathFits; at-root; at-sink;
  through; arrivalRank; ChainsFit; ShareChainsFit; ShareFits)

----------------------------------------------------------------------
-- THE FOLD.  Induction on the fit, which forces the path: a chain is
-- as long as its obligation is deep, and the obligation runs out
-- exactly where the path does.
----------------------------------------------------------------------

foldPath-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
  (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  {ψ : Fin n → Rd₃} {R : Rd} {Rst : ℕ} {κ : Path Γ u t}
  (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sd : Sched Γ) (st : EvalSt e) →
  PathFits {e = e} ac gas id now ψ Rst κ R →
  valsRd ψ u vals ⊑ R → stHop ψ st ≤ Rst →
  any dryEvent evs ≡ false →
  hasDry (proj₁ (foldPath ac gas id now envSrc κ vals evs fin sd st)) ≡ false

foldPath-dry-free ac gas id now envSrc vals evs fin sd st at-root hv hs he =
  hasDry-single (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    id envSrc delivery
    (any-dry-++ evs (map value vals ++ (if fin then complete ∷ [] else []))
      he (tailPart-dry vals fin))

foldPath-dry-free ac gas id now envSrc vals evs fin sd st
  (at-sink {i = i} sdu) hv hs he =
  hasDry-++ (((evs ++ handoff (toℕ i) ∷ []) at id from envSrc as delivery) ∷ [])
    (proj₁ (dispatchShare ac gas id now i vals fin sd st))
    (hasDry-single (evs ++ handoff (toℕ i) ∷ []) id envSrc delivery
      (any-dry-++ evs (handoff (toℕ i) ∷ []) he refl))
    (sdu vals fin sd st hv hs)

foldPath-dry-free {Γ = Γ} {t = t} {e = e} ac gas id now envSrc vals evs fin sd st
  (through {u = w} {f = f} {κ = κ′} carr fdry fits) hv hs he =
  foldPath-dry-free ac gas id now envSrc
    (proj₁ sf) (evs ++ proj₁ (proj₂ sf)) (proj₁ (proj₂ (proj₂ sf)))
    (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
    fits (proj₁ (carr vals fin sd st hv hs)) (proj₂ (carr vals fin sd st hv hs))
    (any-dry-++ evs (proj₁ (proj₂ sf)) he (fdry vals fin sd st hv hs))
  where
  sf : List (Val Γ w) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  sf = stepFrame ac id now f κ′ vals fin sd st

----------------------------------------------------------------------
-- AND EVERY CHAIN THE SHARE'S DISPATCH REACHES.  This is the same fold
-- as the arrival's, one level in: the admitted chains are folded
-- threading one state, each is seeded with the share's own close when
-- the definition is spent, and a registration cancelled earlier in the
-- cascade contributes no emit at all.
--
-- WHAT MAKES IT A BODY RATHER THAN A LEAF IS THE BOUND EACH CHAIN IS
-- STATED AT.  The premise joins the chain's own store reading onto the
-- entering bound, so the store hypothesis the fold below needs is
-- discharged by `m≤m⊔n` and nothing has to be transported across the
-- threading — which is the step every refuted reading of this face
-- died on.
----------------------------------------------------------------------

shareGo-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
  (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  {ψ : Fin n → Rd₃} {Rin : Rd} {Rst : ℕ}
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sd : Sched Γ) (st : EvalSt e) →
  valsRd ψ (lookup Γ i) vals ⊑ Rin →
  ShareChainsFit {e = e} ac gas id now i ψ Rin Rst vals fin ps sd st →
  hasDry (proj₁ (shareGo ac gas id now i vals fin ps sd st)) ≡ false
shareGo-dry-free ac gas id now i vals fin []              sd st hv fits = refl
shareGo-dry-free {Γ = Γ} {t = t} {e = e} ac gas id now i {ψ = ψ}
  vals fin ((rid , p) ∷ ps) sd st hv fits
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | fits
... | true  | tl =
      shareGo-dry-free ac gas id now i vals fin ps sd st hv tl
... | false | (hc , tl) =
      hasDry-++ (proj₁ fp)
        (proj₁ (shareGo ac gas id now i vals fin ps
                 (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp))))
        (foldPath-dry-free ac gas id now (toℕ i) vals seed fin sd st′
          hc hv (m≤m⊔n (stHop ψ st′) _) (seed-dry fin))
        (shareGo-dry-free ac gas id now i vals fin ps
          (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp)) hv tl)
  where
  st′ : EvalSt e
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }

  seed : List (InstEvent (Val Γ t))
  seed = if fin then close (toℕ i) exhausted ∷ [] else []

  fp = foldPath ac gas id now (toℕ i) p vals seed fin sd st′

  seed-dry : ∀ (b : Bool) →
    any (dryEvent {A = Val Γ t})
      (if b then close (toℕ i) exhausted ∷ [] else []) ≡ false
  seed-dry true  = refl
  seed-dry false = refl

----------------------------------------------------------------------
-- THE DISPATCH ITSELF, which is that fold at the list the share admits
-- and at the state its latch leaves.  The finish step rewrites the
-- registry and the live set and hands the emits through untouched, so
-- there is nothing here for the dry claim to do but peel the gas.
----------------------------------------------------------------------

dispatchShare-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
  (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  {ψ : Fin n → Rd₃} {Rin : Rd} {Rst : ℕ}
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sd : Sched Γ) (st : EvalSt e) →
  valsRd ψ (lookup Γ i) vals ⊑ Rin →
  ShareFits {e = e} ac gas id now i ψ Rin Rst vals fin sd st →
  hasDry (proj₁ (dispatchShare ac (suc gas) id now i vals fin sd st))
    ≡ false
dispatchShare-dry-free {e = e} ac gas id now i vals false sd st hv fits =
  shareGo-dry-free {e = e} ac gas id now i vals false
    (shareAdmit i (EvalSt.registry st)) sd (shareLatch i false st) hv fits
dispatchShare-dry-free {e = e} ac gas id now i vals true sd st hv fits =
  shareGo-dry-free {e = e} ac gas id now i vals true
    (shareAdmit i (EvalSt.registry st)) sd (shareLatch i true st) hv fits

----------------------------------------------------------------------
-- ONE ARRIVAL INTO ONE CHAIN.  The seed is the arriving value and, on
-- a spent source, its own exhausted close — neither of which is the
-- dry marker — so the whole of the work is the fold's, and the two
-- bounds are read off the rank the arrival enters at.
--
-- THE STORE BOUND IS AVAILABLE BY CONSTRUCTION HERE, which is what
-- makes the arrival rank the right number to state the chain against:
-- it is the term's reading PLUS the join of the payload with the
-- store, so the store sits under it with the term's reading to spare,
-- and that spare is what a flattener descends by.
----------------------------------------------------------------------

chainStep-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (c : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  PathFits {e = e} (arrivalWitness a sched st) n id (arrTick a)
    (slotRd (Sched.slots sched)) (arrivalRank a sched st) c
    (rdᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a)) →
  hasDry (proj₁ (chainStep id a c sched st)) ≡ false
chainStep-dry-free {n = n} {Γ = Γ} {t = t} {e = e} id a c sched st fit =
  foldPath-dry-free (arrivalWitness a sched st) n id (arrTick a) (arrSource a)
    (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st fit
    (≤-reflexive (⊔-identityʳ _) , ≤-reflexive (⊔-identityʳ _))
    (≤-trans (m≤n⊔m (depthᵛ ψ (arrTy a) (arrVal a)) (stHop ψ st))
             (m≤n+m (depthᵛ ψ (arrTy a) (arrVal a) ⊔ stHop ψ st) (depthᵉ ψ e)))
    (seed-dry (Arrival.isLast a))
  where
  ψ : Fin n → Rd₃
  ψ = slotRd (Sched.slots sched)

  seed-dry : ∀ (b : Bool) →
    any (dryEvent {A = Val Γ t})
      (if b then close (arrSource a) exhausted ∷ [] else []) ≡ false
  seed-dry true  = refl
  seed-dry false = refl

----------------------------------------------------------------------
-- AND EVERY CHAIN THE ARRIVAL REACHES.  The premise recurses on the
-- chain list exactly as the fold does, so each conjunct is handed to
-- the chain it was stated at and the tail is handed to the recursive
-- call.  A chain cut earlier in this same cascade contributes no emit
-- at all, and the premise skips it for the same reason.
----------------------------------------------------------------------

cascadeGo-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (cs : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  ChainsFit a id cs sched st →
  hasDry (proj₁ (cascadeGo a id cs sched st)) ≡ false
cascadeGo-dry-free a id []               sched st fits = refl
cascadeGo-dry-free a id ((rid , c) ∷ cs) sched st fits
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | fits
... | true  | tl        = cascadeGo-dry-free a id cs sched st tl
... | false | (hc , tl) =
      hasDry-++ (proj₁ (chainStep id a c sched st′))
        (proj₁ (cascadeGo a id cs (proj₁ (proj₂ (chainStep id a c sched st′)))
                                  (proj₂ (proj₂ (chainStep id a c sched st′)))))
        (chainStep-dry-free id a c sched st′ hc)
        (cascadeGo-dry-free a id cs
          (proj₁ (proj₂ (chainStep id a c sched st′)))
          (proj₂ (proj₂ (chainStep id a c sched st′))) tl)
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
