------------------------------------------------------------------
-- ROADMAP: tier-1 #1/#2 — the CAPS-INDEXED burst walk, the corrected
--   route to `chainStep-demand` / `foldPath-demand` (.Anchor-Dry § 1).
-- DELETE WHEN: assembled into src as Verify-Budget-Sufficient/Burst-Walk.agda
--   with `foldPath-demand` a real definition over it.
--
-- WHY THIS SHAPE, and what it replaces (PROOF-STATE, tier-1 update
-- 2026-08-10).  The obvious instantiation — demand ledgers CONSTANT in
-- the walk level, so that `Res.burst` lands directly on
-- `burstB? Dm Ψ` — was built, typechecked, and is FALSE: the walk
-- threads its ledger through every frame, so a level-constant `Vb`
-- demands that every single frame preserve a fixed size bound, and
-- `stepFrame` on `map-f fn` is `map (applyFn fn) vals` (Evaluator:1250)
-- — a duplicating `fn` roughly doubles `sizeᵛ`.  Dm is not a fixed
-- point of the growth map.  `Walk`'s `*-widen` fields are the walk
-- saying the ledger must GROW WITH THE LEVEL.
--
-- So the ledger here is CAPS-INDEXED, and everything but the events
-- half of one frame is already proven:
--
--   Vb / Pb / OK   exactly `walkH`'s (.Caps-Face:4752), verbatim
--   Bb J str = burstCaps? (frameStep J c) sl str          ← NEW, non-trivial
--   Eb J es  = all (eventCaps? (frameStep J c) sl) es     ← NEW, non-trivial
--
-- and every closure fact it needs exists: `burstCaps?-widen`,
-- `eventsCaps?-widen` (Caps-Face:3548/3541) under `frameStep-mono-j`.
--
-- WHAT THIS BUYS OVER `foldPath-caps` (.Subscribe-Face:3243), which
-- ALREADY proves the same recursion and already concludes
-- `burstCaps? (frameStep (j + j′) c) sl`: **one witness instead of two.**
-- foldPath-caps's Σ reports `j′` with NO bound on it — both its
-- conjuncts are monotone in `j′`, so that receipt is upward-closed in
-- its witness and says nothing quantitative about the level.  The level
-- bound lives in a different Σ (`Res.hi`).  Two receipts with two
-- witnesses cannot be intersected — the same trap `walkH`'s `sf-step`
-- hits.  A walk whose Bb IS the burst predicate returns both at once.
--
-- THE ONE NEW OBLIGATION: `stepFrame-burst-face` (§ 1).  Its first four
-- conjuncts are `FrameFace` (Caps-Face:4655), i.e. `stepFrame-face`,
-- PROVEN.  The fifth is genuinely missing: **FrameFace bounds the output
-- VALUES (`proj₁ r`) and says nothing about the emitted EVENTS
-- (`proj₁ (proj₂ r)`)**.  Same shape the subscribeInner face already
-- carries (`siC`'s `all (eventCaps? …)` conjunct, Caps-Face:4699).
------------------------------------------------------------------
module Caps-Burst-Walk-Probe where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat     using (ℕ; suc; _+_; _≤_)
open import Data.List    using (List; []; _∷_; all; map; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent;
                           close; value; complete; exhausted; InstEmit)
open import Rx.Exp  using (Ty; Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; Slots; Arrival; Path; Frame; _↠_; Stream;
         RegId; Chain; stepFrame; foldPath; chainStep;
         lvls; iterL;
         arrTy; arrVal; arrTick; arrSource; budgetAt; fLvlD)

open import Verify-Budget-Sufficient.Delivery-Walk
  using (Walk-Hyps; module Walk; regP?; Caps; frameStep; pathLen; delivN;
         ∧-intro; ∧-true; all-++-intro; all-impl)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthFold; depthChain)

open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; walkOK; walkOK-finish;
         valCaps?; valsCaps?; eventCaps?; burstCaps?;
         eventsCaps?-widen; burstCaps?-widen; valsCaps?-lvl;
         pathSz?-len; pathSz?-tail; pathSz?-widen;
         capsOK?-count; capsOK?-delivered; capsOK?-regs; shareLatch-caps;
         frameStep-mono-j; frameStep-0)

------------------------------------------------------------------
-- § 1  THE ONE NEW OBLIGATION — `stepFrame-face` plus the events half.
--
-- Conjuncts 1–4 ARE `FrameFace c d J sl r` (Caps-Face:4655), which
-- `stepFrame-face` proves.  Conjunct 5 (the emitted events) is the
-- genuinely open one, and conjunct 4 (the registry ledger at the new
-- level) is `capsOK?-regs` of conjunct 2 — both are stated here rather
-- than spliced because the walk needs them AT THE SAME `j′`.
------------------------------------------------------------------

postulate
  stepFrame-burst-face : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (d : ℕ)
    (J : ℕ) {s u} (sf : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    walkOK c sl J sched st →
    pathSz? (Caps.cSize (frameStep J c)) (f ↠ path′) ≡ true →
    valsCaps? (frameStep J c) sl vals ≡ true →
    regP? (pathSz? (Caps.cSize (frameStep J c))) (EvalSt.registry st) ≡ true →
    depthFrame sf id now f path′ vals fin sched st ≤ d →
    let r = stepFrame sf id now f path′ vals fin sched st in
    Σ ℕ λ j′ → (J + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) d J)
      × walkOK c sl (J + j′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                              (proj₂ (proj₂ (proj₂ (proj₂ r))))
      × (valsCaps? (frameStep (J + j′) c) sl (proj₁ r) ≡ true)
      × (regP? (pathSz? (Caps.cSize (frameStep (J + j′) c)))
               (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
      × (all (eventCaps? (frameStep (J + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- § 2  THE INSTANTIATION.
------------------------------------------------------------------

module BurstWalk
  {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (d : ℕ)
  (2≤S : 2 ≤ Caps.cSize c)
  where

  S = Caps.cSize c
  W = Caps.cWid  c
  R = Caps.cReg  c

  -- `map value` carries the payload ledger's FIRST conjunct across;
  -- `eventCaps? c sl (value v)` IS `valCaps? c sl _ v` (Caps-Face:679)
  all-map-value : ∀ (c′ : Caps) (vs : List (Val Γ t)) →
    all (valCaps? c′ sl t) vs ≡ true →
    all (eventCaps? c′ sl) (map value vs) ≡ true
  all-map-value c′ []       h = refl
  all-map-value c′ (v ∷ vs) h =
    ∧-intro (proj₁ (∧-true _ _ h)) (all-map-value c′ vs (proj₂ (∧-true _ _ h)))

  fin-tail : ∀ (c′ : Caps) (fin : Bool) →
    all (eventCaps? {Γ = Γ} {u = t} c′ sl)
        (if fin then complete ∷ [] else []) ≡ true
  fin-tail c′ true  = refl
  fin-tail c′ false = refl

  burstH : Walk-Hyps e S W R d
  burstH = record
    { OK        = walkOK c sl
    ; Pb        = λ J p → pathSz? (Caps.cSize (frameStep J c)) p
    ; Vb        = λ J vs → valsCaps? (frameStep J c) sl vs
    ; Eb        = λ J es → all (eventCaps? (frameStep J c) sl) es
    ; Bb        = λ J str → burstCaps? (frameStep J c) sl str
    ; e-nil     = λ _ → refl
    ; e-close   = λ _ _ _ → refl
    ; e-app     = λ J es₁ es₂ h₁ h₂ → all-++-intro _ es₁ es₂ h₁ h₂
    ; e-widen   = λ le es h → eventsCaps?-widen sl es (frameStep-mono-j c 2≤S le) h
    ; b-nil     = λ _ → refl
    ; b-app     = λ J s₁ s₂ h₁ h₂ → all-++-intro _ s₁ s₂ h₁ h₂
    ; b-widen   = λ le str h → burstCaps?-widen sl str (frameStep-mono-j c 2≤S le) h
    ; b-deliv   = λ J id src evs vals fin hE hV →
                    ∧-intro (all-++-intro _ evs _ hE
                              (all-++-intro _ (map value vals) _
                                (all-map-value (frameStep J c) vals
                                  (proj₁ (∧-true _ _ hV)))
                                (fin-tail (frameStep J c) fin)))
                            refl
    ; b-handoff = λ J id src evs i hE →
                    ∧-intro (all-++-intro _ evs _ hE refl) refl
    ; p-len     = λ J p h → pathSz?-len (Caps.cSize (frameStep J c)) p h
    ; p-tail    = λ J f p h → pathSz?-tail (Caps.cSize (frameStep J c)) f p h
    ; p-widen   = λ le p h → pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le)) h
    ; v-widen   = λ le vs h → valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le) h
    ; ok-reg    = λ J sched st ok → capsOK?-count (frameStep J c) sched st (proj₂ ok)
    ; ok-cons   = λ J rid sched st ok →
                    proj₁ ok , capsOK?-delivered (frameStep J c) rid sched st (proj₂ ok)
    ; ok-latch  = λ J i fin sched st ok →
                    proj₁ ok , shareLatch-caps (frameStep J c) i fin sched st (proj₂ ok)
    ; ok-finish = λ J i fin out ok → walkOK-finish c sl J i fin out ok
    ; sf-step   = stepFrame-burst-face {e = e} c sl d
    }

  module V = Walk {e = e} S W R d 2≤S burstH

  ----------------------------------------------------------------
  -- § 3  THE PAYOFF — the burst AND the level it is good at, at ONE
  -- witness.  This is the receipt `foldPath-caps` cannot give.
  ----------------------------------------------------------------

  foldPath-burst : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
    (envSrc : Source) {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? c sched st ≡ true →
    pathSz? (Caps.cSize c) path ≡ true →
    valsCaps? c sl vals ≡ true →
    all (eventCaps? c sl) evs ≡ true →
    depthFold sf gas id now envSrc path vals evs fin sched st ≤ d →
    let fp = foldPath sf gas id now envSrc path vals evs fin sched st in
    Σ ℕ λ lvl →
      (lvl ≤ lvls S W d (iterL S W d (pathLen path) 0)
                        (delivN st (proj₂ (proj₂ fp))))
      × (burstCaps? (frameStep lvl c) sl (proj₁ fp) ≡ true)
  foldPath-burst sf gas id now envSrc path vals evs fin sched st
                 slEq inv hP hV hE hD =
    V.Res.lvl GO , V.Res.hi GO , V.Res.burst GO
    where
    inv0 : capsOK? (frameStep 0 c) sched st ≡ true
    inv0 = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
    hP0 : pathSz? (Caps.cSize (frameStep 0 c)) path ≡ true
    hP0 = subst (λ x → pathSz? (Caps.cSize x) path ≡ true) (sym (frameStep-0 c)) hP
    hV0 : valsCaps? (frameStep 0 c) sl vals ≡ true
    hV0 = subst (λ x → valsCaps? x sl vals ≡ true) (sym (frameStep-0 c)) hV
    hE0 : all (eventCaps? (frameStep 0 c) sl) evs ≡ true
    hE0 = subst (λ x → all (eventCaps? x sl) evs ≡ true) (sym (frameStep-0 c)) hE
    GO = V.foldPath-go 0 sf gas id now envSrc path vals evs fin sched st
           ((slEq , inv0) , capsOK?-regs c sched st inv)
           hP0 hV0 hE0 hD
