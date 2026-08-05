-- GAP 4's ASSEMBLY (Wet.agda:4125-4199).  THE JOINT INVARIANT BRIDGE
-- between the caps face's `capsOK?` (Caps-Face.agda) and the wet
-- family's `INV?` (Measures.agda).  Task #16 of PROOF-STATE.md.
--
-- capsOK? and INV? do not imply each other: capsOK? carries two WIDTH
-- conjuncts (widLive, widNode) INV? has no counterpart for, and INV?
-- carries the fn face (fnCapBounded?, the Ψ half of regsB?) and the
-- slots conjuncts (slotsSize ≤ B, slotsFnCap ≤ Ψ) capsOK? has no
-- counterpart for.  They also read registry cardinality at DIFFERENT
-- indices (INV? at cSize, capsOK? at cReg).  So this module threads a
-- JOINT invariant through one cascade, each face fed by its own tick:
-- `caps-tick` (Caps-Face:6752, PROVEN) supplies the boundedness half,
-- and the four postulated suppliers below (S1-S4) supply the rest.
-- `cascadeGo-caps` concludes boundedness only, no dry — dryness stays
-- on the gas axis (S3, P2's unchanged dry half).
--
-- CONSUMERS.  `cascade-dry` and `burst-wet` (.Wet) migrate to consume
-- `cascade-wet-via-caps` here once its suppliers are proven, in place
-- of the postulated `cascadeGo-wet`.  P1's analogue
-- (`subscribeE-wet-via-caps`) is DELIBERATELY NOT STATED YET: it waits
-- on S4's misalignment report, below — and S4 turned out to have none,
-- so that statement is the natural next task, not a blocked one.
module Verify-Budget-Sufficient.Caps-Bridge where

open import Data.Bool    using (Bool; true; false; T; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; _⊔_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; m≤n+m)
open import Data.List    using (List; []; _∷_; all; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Prim      using (Gas; Tick; Id; Source)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; sizeᵉ)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; RegId; Chain;
                                Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                arrTy; arrVal; cascade; hasDry;
                                subscribeE; budgetAt; slotsSize; opIterD)

-- the whole wet family (INV?, ΨAt, sizeCapAt, sizeCapAt-mono, valB?,
-- fnCapBounded?, regsB?, slotsFnCap, INV-parts, pathLen, the Bool
-- toolkit ∧-true/∧-intro/all-impl/≤ᵇ-widen/T-to/T⇒≡true) via the public
-- chain Wet → Caps → Keeps-Ring → Measures
open import Verify-Budget-Sufficient.Wet

-- the caps face and the subscribe clique (capsOK?, capsOK?-parts,
-- capsOK?-count, caps-tick, pathSz?/regsSz?/frameSz?, slotsCaps?,
-- valCaps?, burstCaps?/burstCount?, subscribeE-caps, nest) via the
-- public chain Subscribe-Face → Caps-Face → {Delivery-Walk, Caps-Nest}
open import Verify-Budget-Sufficient.Subscribe-Face

-- the depth mirror (S4's currency)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

------------------------------------------------------------------
-- (A) BRIDGE LEMMAS.  What `capsAt`'s two numeric fields ARE, related
-- to the wet family's own reading of them.
------------------------------------------------------------------

-- B1 : capsAt's cSize field IS sizeCapAt, by the very definition of
-- sizeCapAt (Wet.agda:4101-4102: `sizeCapAt e sl id = Caps.cSize
-- (capsAt e sl id)`).  PROVEN, by refl — there is no bridging content
-- here at all, only a naming one.
B1-cSize≡sizeCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) → Caps.cSize (capsAt e sl id) ≡ sizeCapAt e sl id
B1-cSize≡sizeCapAt e sl id = refl

-- B2 : the registration count never outruns the size cap.  TRUE at the
-- base (capsAt e sl zero's pre-blowup triple has cReg = suc (sizeᵉ e +
-- slotsSize sl) = cSize - 1, strictly under cSize), and cSize's growth
-- (iterSize, exponential-shaped per fold) plausibly dominates cReg's
-- (a single multiplicative factor `suc (j * cSize)` per frameStep) at
-- every later level too — but nobody has proven that domination
-- through frameBlowup's iteration, and doing so is a joint induction
-- over frameStep/frameBlowup in the shape of `2≤capsAt-size` /
-- `1≤capsAt-reg` (Caps.agda), not a one-liner.  POSTULATED; the route
-- is that joint induction, bootstrapped from the base-case fact above.
postulate
  B2-cReg≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → Caps.cReg (capsAt e sl id) ≤ Caps.cSize (capsAt e sl id)

------------------------------------------------------------------
-- (B3, EARLY) THE Ψ-ONLY HALVES, defined before the suppliers that
-- state facts about them.  `frameB? B Ψ f` bundles a size test and a
-- weight test per frame (`(sizeᵗ fn ≤ᵇ B) ∧ ((caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ
-- Ψ)` on map-f/scan-f, `true` elsewhere) — and `frameSz? B f` (the
-- caps side, Caps-Face.agda:254) is EXACTLY its size half, clause for
-- clause.  So the missing half is the Ψ-only one, mirrored here; the
-- recombination lemmas that reunite it with the caps side's size-only
-- half into the real `frameB?`/`pathB?`/`regsB?` (Measures.agda) that
-- INV? reads live below, next to where the assembly consumes them.
------------------------------------------------------------------

frameBΨ? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameBΨ? Ψ (map-f fn)         = (caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ
frameBΨ? Ψ (scan-f fn _)      = (caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ
frameBΨ? Ψ (take-f _)         = true
frameBΨ? Ψ (from-inner _ _ _) = true
frameBΨ? Ψ (thru-outer _ _)   = true

pathBΨ? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathBΨ? Ψ root           = true
pathBΨ? Ψ (share-sink i) = true
pathBΨ? Ψ (f ↠ p)        = frameBΨ? Ψ f ∧ pathBΨ? Ψ p

regsBΨ? : ∀ {n} {Γ : Ctx n} {t} → ℕ
        → List (RegId × Source × Chain Γ t) → Bool
regsBΨ? Ψ = all (λ en → pathBΨ? Ψ (proj₂ (proj₂ (proj₂ en))))

------------------------------------------------------------------
-- (B) POSTULATED SUPPLIERS.
------------------------------------------------------------------

-- S1 `fn-tick` : the fn face is preserved across a cascade.  Ψ never
-- grows (caseW is substitution-invariant, per INV?'s own header at
-- Measures.agda:5316-5323), so this is PRESERVATION, not accounting —
-- but proving it means walking fnCapBounded?'s own two conjuncts
-- (fnCapLive over Sched.live, fnCapNode over EvalSt.nodes) through the
-- whole delivery clique (stepFrame/pushBurst/subscribeInner/...), the
-- same shape latch-bounded/finish-bounded/sweepLive-bounded already
-- did for stBounded? in .Measures and .Wet.  Not yet done; postulated.
-- The "fn half of regsB?" is stated as `regsBΨ?` below (part (B3)) —
-- the Ψ-only conjunct regsB? bundles with the size-only one capsOK?'s
-- `regsSz?` already supplies.
postulate
  fn-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
    in INV? Ψ B sched st ≡ true →
       valB? B Ψ (arrTy a) (arrVal a) ≡ true →
       let r   = cascade a id sched st
           sl′ = Sched.slots (proj₁ (proj₂ r))
           Ψ′  = ΨAt e sl′
       in (fnCapBounded? Ψ′ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
          × (regsBΨ? Ψ′ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- S2 `slots-tick` : STRONGER than what was asked (the two slots
-- conjuncts at the output slots) and stated as the raw fact underneath
-- them instead, because the two conjuncts alone cannot bridge
-- `caps-tick`'s fixed entry-time `sl` to the wet family's own
-- convention of re-reading `Sched.slots` off whatever the current
-- schedule is — and that bridge is load-bearing below (`capsOut`).
--
-- The raw equality is also, unlike the two-conjunct version, a
-- genuinely STRUCTURAL fact: grepping Rx.Evaluator.agda for `slots =`
-- finds exactly ONE occurrence in the whole file — `sched-init`'s own
-- construction.  No `record sched { ... }` update anywhere in the
-- mutual delivery clique (chainStep/foldPath/dispatchShare/shareGo/
-- stepFrame/pushBurst/subscribeInner/subscribeAll/
-- subscribeSharedSlot/sharedConnect/thruConsume/thruWalk/concatDrain/
-- innerFinish/innerReact) ever touches the `slots` field; every one of
-- them only ever writes nextOrdinal/nextSource/nextNode/live.  Measures
-- already proves the two BOUNDARY special cases this fact generalises
-- (`pop-slots` for the schedule pop, `finish-slots` for
-- cascadeFinish); what is missing is the INTERIOR (cascadeGo's fold
-- over chains), and closing it is a mechanical induction over that
-- whole mutual block — clause `refl` or a trivial recursive call
-- throughout, since none of them constructs a `slots`-updating record
-- — but it is real work belonging to .Measures/.Wet, not this thin
-- module, so it stays postulated here.
postulate
  slots-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots (proj₁ (proj₂ (cascade a id sched st))) ≡ Sched.slots sched

-- S3 `dry-tick` : P2 (`cascadeGo-wet`, Wet.agda:4335)'s dry half,
-- unchanged — the gas-peel axis (dBound-μ/hop/connect).  Interim
-- postulate; not touched by the caps/INV? bridging problem at all.
postulate
  dry-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
    in INV? Ψ B sched st ≡ true →
       valB? B Ψ (arrTy a) (arrVal a) ≡ true →
       hasDry (proj₁ (cascade a id sched st)) ≡ false

------------------------------------------------------------------
-- S4 `sub-charge` : GAP 4 (a)'s missing subscribe-level charge.  NO
-- MISALIGNMENT FOUND, and no postulate needed — `subscribeE-caps`
-- (Subscribe-Face.agda:906, GROUND) already carries the hypothesis
-- `depthE g b κ bid now sched st ≤ dep` and already concludes
-- `j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j` as the
-- fourth component of its Σ.  `depthE`'s argument list (g, b, κ, bid,
-- now, sched, st) is LITERALLY subscribeE-caps' own argument list in
-- the same order, so instantiating `dep := depthE g b κ bid now sched
-- st` discharges that hypothesis by `≤-refl` and reports j′'s bound
-- "via the Caps-Depth mirror's family applied at the same call
-- arguments" exactly as asked.  `j′ ≤ j + j′ ≤ opIterD (...)` is the
-- one arithmetic step (`m≤n+m`) separating subscribeE-caps' own
-- receipt from the shape asked for here.
sub-charge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (bud ops j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c → Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  suc (sizeᵉ b) ≤ ops →
  let r = subscribeE g b κ bid now sched st in
  Σ ℕ λ j′ →
    (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
    × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
    × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
    × (j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                     (depthE g b κ bid now sched st) bud ops j)
sub-charge {n = n} c bud ops j g b κ bid now sl sched st
           2≤S 1≤R slEq slC slSz capOK szB dwB pκ pLen nB opsB =
  j′ , capOut , burC , burN , ≤-trans (m≤n+m j′ j) jj′≤
  where
  IH   = subscribeE-caps c (depthE g b κ bid now sched st) bud ops j g b κ
                          bid now sl sched st
                          2≤S 1≤R slEq slC slSz capOK szB dwB pκ pLen nB opsB
                          ≤-refl
  j′    = proj₁ IH
  capOut = proj₁ (proj₂ IH)
  burC  = proj₁ (proj₂ (proj₂ IH))
  burN  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  jj′≤  = proj₂ (proj₂ (proj₂ (proj₂ IH)))

------------------------------------------------------------------
-- (B3, CONTINUED) THE RECOMBINATION LEMMAS: capsOK?'s size-only half
-- (regsSz?) plus S1's Ψ-only half (regsBΨ?, above) reunite into the
-- real `frameB?`/`pathB?`/`regsB?` (Measures.agda) that INV? reads,
-- one line of ∧-intro per clause.
------------------------------------------------------------------

frameB?-of-parts : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) {B Ψ : ℕ} →
  frameSz? B f ≡ true → frameBΨ? Ψ f ≡ true → frameB? B Ψ f ≡ true
frameB?-of-parts (map-f fn)         hb hΨ = ∧-intro hb hΨ
frameB?-of-parts (scan-f fn _)      hb hΨ = ∧-intro hb hΨ
frameB?-of-parts (take-f _)         hb hΨ = refl
frameB?-of-parts (from-inner _ _ _) hb hΨ = refl
frameB?-of-parts (thru-outer _ _)   hb hΨ = refl

pathB?-of-parts : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) {B Ψ : ℕ} →
  pathSz? B p ≡ true → pathBΨ? Ψ p ≡ true → pathB? B Ψ p ≡ true
pathB?-of-parts root           hsz hΨ = refl
pathB?-of-parts (share-sink i) hsz hΨ = refl
pathB?-of-parts (f ↠ p) {B} {Ψ} hsz hΨ
  with ∧-true (frameSz? B f) _ hsz
... | hf , hrest with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hrest
... | _ , hp with ∧-true (frameBΨ? Ψ f) (pathBΨ? Ψ p) hΨ
... | hfΨ , hpΨ = ∧-intro (frameB?-of-parts f hf hfΨ) (pathB?-of-parts p hp hpΨ)

-- generic: two pointwise `all`s zip into an `all` of their combined
-- predicate — the two-hypothesis sibling of Measures.agda's all-impl
all-zip : ∀ {A : Set} (P Q R : A → Bool) →
  (∀ x → P x ≡ true → Q x ≡ true → R x ≡ true) →
  ∀ (xs : List A) → all P xs ≡ true → all Q xs ≡ true → all R xs ≡ true
all-zip P Q R imp []       hp hq = refl
all-zip P Q R imp (x ∷ xs) hp hq
  with ∧-true (P x) (all P xs) hp | ∧-true (Q x) (all Q xs) hq
... | (px , pxs) | (qx , qxs) = ∧-intro (imp x px qx) (all-zip P Q R imp xs pxs qxs)

regsB?-of-parts : ∀ {n} {Γ : Ctx n} {t}
  (rs : List (RegId × Source × Chain Γ t)) {B Ψ : ℕ} →
  regsSz? B rs ≡ true → regsBΨ? Ψ rs ≡ true → regsB? B Ψ rs ≡ true
regsB?-of-parts rs hsz hΨ =
  all-zip _ _ _ (λ en psz pΨ → pathB?-of-parts (proj₂ (proj₂ (proj₂ en))) psz pΨ)
                rs hsz hΨ

------------------------------------------------------------------
-- (C) THE ASSEMBLY.  Mirrors .Wet's `cascade-dry` (Wet.agda:4607) plus
-- a `capsOK?`/`valCaps?` hypothesis, concluding dryness, INV? at the
-- output, AND capsOK? at the output — the joint invariant a future
-- `cascade-dry`/`burst-wet` migrate to consume in place of the
-- postulated `cascadeGo-wet`.
--
-- THE INV? ASSEMBLY CLOSED CONJUNCT-BY-CONJUNCT — no `inv-assemble`
-- fallback was needed.  stBounded? and the registry-length bound come
-- off `caps-tick`'s own conclusion via B1/B2 (transported across the
-- `sl ≡ Sched.slots sched′` fact S2 supplies); the fn face and the Ψ
-- half of regsB? come off S1; the size half of regsB? comes off
-- `caps-tick`'s conclusion too (capsOK?'s own `regsSz?` conjunct,
-- recombined with S1's Ψ half via `regsB?-of-parts`); the two slots
-- conjuncts widen the INPUT's own INV? hypothesis across the tick
-- (`sizeCapAt-mono`) and transport it across S2's slots equality.
------------------------------------------------------------------

cascade-wet-via-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
  in INV? Ψ B sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     capsOK? (capsAt e sl id) sched st ≡ true →
     valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
     let r    = cascade a id sched st
         sl′  = Sched.slots (proj₁ (proj₂ r))
         Ψ′   = ΨAt e sl′
         Ŝ    = sizeCapAt e sl′ (suc id)
     in (hasDry (proj₁ r) ≡ false)
        × (INV? Ψ′ Ŝ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (capsOK? (capsAt e sl′ (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascade-wet-via-caps {e = e} a id sched st inv val pre valC =
  dry , invOut , capsOut
  where
  sl     = Sched.slots sched
  Ψ      = ΨAt e sl
  B      = sizeCapAt e sl id
  r      = cascade a id sched st
  sched′ = proj₁ (proj₂ r)
  st′    = proj₂ (proj₂ r)
  sl′    = Sched.slots sched′
  Ψ′     = ΨAt e sl′
  Ŝ      = sizeCapAt e sl′ (suc id)

  dry : hasDry (proj₁ r) ≡ false
  dry = dry-tick a id sched st inv val

  -- S2, instantiated: the output's slots equal the entry's
  slEq : sl′ ≡ sl
  slEq = slots-tick a id sched st

  ŜEq : Ŝ ≡ sizeCapAt e sl (suc id)
  ŜEq = cong (λ s → sizeCapAt e s (suc id)) slEq

  ΨEq : Ψ′ ≡ Ψ
  ΨEq = cong (ΨAt e) slEq

  B≤Ŝ : B ≤ Ŝ
  B≤Ŝ = ≤-trans (sizeCapAt-mono e sl id) (≤-reflexive (sym ŜEq))

  -- caps-tick, at the entry `sl` it is stated against, then
  -- transported to `sl′` via S2 so it can feed INV? at the level INV?
  -- (which reads Sched.slots sched′ = sl′ directly) actually needs
  capsOut : capsOK? (capsAt e sl′ (suc id)) sched′ st′ ≡ true
  capsOut =
    subst (λ s → capsOK? (capsAt e s (suc id)) sched′ st′ ≡ true) (sym slEq)
          (caps-tick sl id a id sched st refl pre valC)

  capsParts = capsOK?-parts (capsAt e sl′ (suc id)) sched′ st′ capsOut

  -- conjunct 1 : stBounded?.  Definitionally at Ŝ by B1.
  stB : stBounded? Ŝ sched′ st′ ≡ true
  stB = proj₁ capsParts

  -- conjunct 2 : fnCapBounded?, from S1
  fnB : fnCapBounded? Ψ′ sched′ st′ ≡ true
  fnB = proj₁ (fn-tick a id sched st inv val)

  -- conjunct 3 : registry length ≤ B, via capsOK?'s cReg bound (B2)
  -- transported to cSize (B1)
  lenOK : (length (EvalSt.registry st′) ≤ᵇ Ŝ) ≡ true
  lenOK = T⇒≡true _
    (≤⇒≤ᵇ (≤-trans (capsOK?-count (capsAt e sl′ (suc id)) sched′ st′ capsOut)
                   (B2-cReg≤cSize e sl′ (suc id))))

  -- conjunct 4 : regsB?, the size half from capsOK?'s regsSz? (B1),
  -- the Ψ half from S1, recombined
  regSz : regsSz? Ŝ (EvalSt.registry st′) ≡ true
  regSz = proj₁ (proj₂ capsParts)

  regBΨ : regsBΨ? Ψ′ (EvalSt.registry st′) ≡ true
  regBΨ = proj₂ (fn-tick a id sched st inv val)

  regB : regsB? Ŝ Ψ′ (EvalSt.registry st′) ≡ true
  regB = regsB?-of-parts (EvalSt.registry st′) regSz regBΨ

  -- conjuncts 5, 6 : the slots bounds, widened across the tick
  -- (sizeCapAt-mono) from the INPUT's own INV? hypothesis, then
  -- transported from `sl` to `sl′` via S2
  invParts = INV-parts Ψ B sched st inv
  ss-in : (slotsSize sl ≤ᵇ B) ≡ true
  ss-in = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ invParts))))
  sf-in : (slotsFnCap sl ≤ᵇ Ψ) ≡ true
  sf-in = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ invParts))))

  ssOut : (slotsSize sl′ ≤ᵇ Ŝ) ≡ true
  ssOut = trans (cong (λ v → v ≤ᵇ Ŝ) (cong slotsSize slEq))
                (≤ᵇ-widen (slotsSize sl) B≤Ŝ ss-in)

  sfOut : (slotsFnCap sl′ ≤ᵇ Ψ′) ≡ true
  sfOut = trans (cong₂ _≤ᵇ_ (cong slotsFnCap slEq) ΨEq) sf-in

  invOut : INV? Ψ′ Ŝ sched′ st′ ≡ true
  invOut = ∧-intro stB (∧-intro fnB (∧-intro lenOK (∧-intro regB (∧-intro ssOut sfOut))))
