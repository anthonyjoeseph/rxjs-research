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
         lvls; iterL; dCapᶜ;
         arrTy; arrVal; arrTick; arrSource; budgetAt; fLvlD)

open import Verify-Budget-Sufficient.Delivery-Walk
  using (Walk-Hyps; module Walk; regP?; Caps; frameStep; pathLen; delivN;
         ∧-intro; ∧-true; all-++-intro; all-impl)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthFold; depthChain)

-- the WET side, for the bridge's INV?/Ψ premise and its conclusion
open import Verify-Budget-Sufficient.Wet using (INV?; burstB?; sizeCapAt)

open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; walkOK; walkOK-finish; sizeCount; capsAt; capsH;
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

------------------------------------------------------------------
-- § 4  THE REST OF THE ROUTE, REHEARSED.
--
-- § 3 hands back the burst at `frameStep lvl c` together with a bound
-- on `lvl`, at ONE witness.  Two things stand between that and
-- `foldPath-dry`'s conclusion (.Anchor-Dry § 2), and both are
-- postulated here so the ASSEMBLY typechecks before either is ground —
-- the point being that a wrong assembly is cheap to amend and proven
-- pieces without one are not.
--
-- THE PAYOFF OF STATING IT THIS WAY: `Dm = (2·B + 12) · towerℕ (suc sz)`
-- APPEARS NOWHERE BELOW.  `capsAt-suc-full` (Caps.agda:893) is `refl` —
-- `capsAt e sl (suc id)` IS `frameStep (sizeCount (capsAt e sl id)
-- (capsH e sl id)) (capsAt e sl id)` — so a burst good at `frameStep
-- lvl c` for ANY `lvl` under that count widens straight onto the dry
-- family's own target `Ŝ`, and the tower constant is off the path.
------------------------------------------------------------------

-- (i) THE LEVEL ARITHMETIC.  The walk's landing level fits the count
-- `capsAt (suc id)` is built from.  Same shape `cascadeGo-caps`
-- (Caps-Face:4345) already proves for the CASCADE — `lvls-mono` over
-- `cascadeGo-deliveries`, closed by `sizeCount-body` — restated for one
-- fold, whose base is `iterL` over the chain and whose count is
-- `dCapᶜ` rather than `cDel`.
-- BUCKET (c): needs the foldPath analogue of `cascadeGo-deliveries`.
postulate
  fold-level-fits : ∀ (c : Caps) (d gas lvl : ℕ) (plen : ℕ) (D : ℕ) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    D ≤ dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d gas
                (iterL (Caps.cSize c) (Caps.cWid c) d plen 0) →
    lvl ≤ lvls (Caps.cSize c) (Caps.cWid c) d
               (iterL (Caps.cSize c) (Caps.cWid c) d plen 0) D →
    lvl ≤ sizeCount c d

-- (ii) THE CAPS→WET FLAVOUR BRIDGE, and the one genuinely new
-- mathematics on this route.  `valCaps?` bounds `sizeᵛ` against
-- `cSize`; `valB? B Ψ` bounds `sizeᵛ ≤ B` **and** `fnCapᵛ ≤ Ψ`
-- (Measures:4853).  The second conjunct is WET-ONLY and cannot come
-- from the caps face at all — it is Ψ-invariance, whose supplier is
-- `INV?`'s own `fnCapBounded?` conjunct ("Ψ never grows — caseW is
-- substitution-invariant", Measures:4835).  So the `INV?` premise is
-- NOT decoration: without it the statement is false, not merely
-- unproven.  Same shape as `pathSz? → pathBΨ? → pathB?` (Caps-Bridge:673).
postulate
  burstCaps→burstB : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
    (sched : Sched Γ) (st : EvalSt e) (str : Stream Γ t) →
    Sched.slots sched ≡ sl →
    INV? Ψ (Caps.cSize c′) sched st ≡ true →
    burstCaps? c′ sl str ≡ true →
    burstB? (Caps.cSize c′) Ψ str ≡ true

------------------------------------------------------------------
-- § 5  THE ASSEMBLY — `foldPath-dry`'s conclusion, with no `Dm`.
--
-- Right to left: the walk's burst at `frameStep lvl c`, widened along
-- `frameStep lvl c ⊑ᶜ frameStep (sizeCount c d) c` (frameStep-mono-j
-- over § 4 (i)), landed on `capsAt e sl (suc id)` by `capsAt-suc-full`,
-- and converted to the wet flavour by § 4 (ii) — whose `Caps.cSize` IS
-- `sizeCapAt e sl (suc id)` by definition (Wet.agda:4110).
------------------------------------------------------------------

module DryRoute
  {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (Ψ : ℕ) (id : Id)
  (2≤S : 2 ≤ Caps.cSize (capsAt e sl id))
  (1≤R : 1 ≤ Caps.cReg (capsAt e sl id))
  where

  c = capsAt e sl id
  d = capsH e sl id

  foldPath-dry-route : ∀ (sf : Gas) (gas : ℕ) (now : Tick) (envSrc : Source)
    {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? c sched st ≡ true →
    pathSz? (Caps.cSize c) path ≡ true →
    valsCaps? c sl vals ≡ true →
    all (eventCaps? c sl) evs ≡ true →
    depthFold sf gas id now envSrc path vals evs fin sched st ≤ d →
    let fp = foldPath sf gas id now envSrc path vals evs fin sched st in
    -- the two facts the OUTPUT state carries, at Ŝ — the caller's,
    -- exactly as in .Anchor-Dry's dry family
    INV? Ψ (sizeCapAt e sl (suc id)) (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp)) ≡ true →
    Sched.slots (proj₁ (proj₂ fp)) ≡ sl →
    -- and the delivery count fits, which § 4 (i) consumes
    delivN st (proj₂ (proj₂ fp))
      ≤ dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d gas
               (iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) 0) →
    burstB? (sizeCapAt e sl (suc id)) Ψ (proj₁ fp) ≡ true
  foldPath-dry-route sf gas now envSrc path vals evs fin sched st
                     slEq inv hP hV hE hD invOut slEqOut hCnt =
    burstCaps→burstB (capsAt e sl (suc id)) sl Ψ
      (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp)) (proj₁ fp) slEqOut invOut
      (burstCaps?-widen sl (proj₁ fp)
         (frameStep-mono-j c 2≤S
            (fold-level-fits c d gas (proj₁ B) (pathLen path)
               (delivN st (proj₂ (proj₂ fp))) 2≤S 1≤R hCnt (proj₁ (proj₂ B))))
         (proj₂ (proj₂ B)))
    where
    fp = foldPath sf gas id now envSrc path vals evs fin sched st
    B  = BurstWalk.foldPath-burst c sl d 2≤S sf gas id now envSrc path vals evs fin
           sched st slEq inv hP hV hE hD
