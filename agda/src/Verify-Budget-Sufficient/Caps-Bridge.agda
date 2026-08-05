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

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; _≡ᵇ_; _⊔_;
                                z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; m≤n+m; n≤1+n;
                                       *-mono-≤; *-monoʳ-≤; +-mono-≤; *-comm;
                                       *-distribˡ-+; *-identityʳ; +-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; all; any; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open import Rx.Prim      using (Gas; Tick; Id; Source; close; exhausted)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; sizeᵉ)
open import Rx.Frame-Width using (dWᵉ; entryCeil)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; RegId; Chain;
                                Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                arrTy; arrVal; arrTick; arrSource; cascade;
                                cascadeGo; cascadeLatch; cascadeFinish;
                                chainStep; chainsOf; hasDry;
                                subscribeE; budgetAt; slotsSize; opIterD;
                                sizeStep; capsBase)

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

-- B2 : the registration count never outruns the size cap.  PROVEN — the
-- domination guessed at above is real: one `sizeStep` unfolds to a sum
-- containing `2 * (S * X)`, which already dominates both the
-- registration increment `Rc * S` (via `Rc ≤ S` and `S ≤ X`) and the
-- carried registration count `R` (via `R ≤ X` and `X ≤ S * X`, `S ≥ 1`
-- always holding).  `frameStep-reg≤size` is that joint induction over
-- frameStep's own recurrence, bootstrapped from the base triple's own
-- `cReg₀ = suc k ≤ suc (suc k) = cSize₀` (`capsAt`'s zero clause hard-
-- codes a "2 +"/"suc" floor on both fields, so the base is never the
-- vacuous (0,0,0) case) and carried through every later frameBlowup.
2X≡X+X : ∀ (X : ℕ) → 2 * X ≡ X + X
2X≡X+X X = cong (X +_) (+-identityʳ X)

sizeStep-eqn : ∀ (S X : ℕ) → sizeStep S X ≡ S + (S * X + S * X)
sizeStep-eqn S X =
  begin
    S * suc (2 * X)
  ≡⟨ *-distribˡ-+ S 1 (2 * X) ⟩
    S * 1 + S * (2 * X)
  ≡⟨ cong (_+ S * (2 * X)) (*-identityʳ S) ⟩
    S + S * (2 * X)
  ≡⟨ cong (λ y → S + S * y) (2X≡X+X X) ⟩
    S + S * (X + X)
  ≡⟨ cong (S +_) (*-distribˡ-+ S X X) ⟩
    S + (S * X + S * X)
  ∎
  where open ≡-Reasoning

frameStep-reg≤size : ∀ (c : Caps) (j : ℕ) → 1 ≤ Caps.cSize c →
  Caps.cReg c ≤ Caps.cSize c →
  Caps.cReg (frameStep j c) ≤ Caps.cSize (frameStep j c)
frameStep-reg≤size c zero hS h =
  subst (λ x → Caps.cReg x ≤ Caps.cSize x) (sym (frameStep-0 c)) h
frameStep-reg≤size c (suc j) hS h = final
  where
  S  = Caps.cSize c
  X  = Caps.cSize (frameStep j c)
  R  = Caps.cReg (frameStep j c)
  Rc = Caps.cReg c

  IH : R ≤ X
  IH = frameStep-reg≤size c j hS h

  S≤X : S ≤ X
  S≤X = iterSize-infl S hS j S

  Rc*S≤S*X : Rc * S ≤ S * X
  Rc*S≤S*X = ≤-trans (*-mono-≤ h ≤-refl) (*-monoʳ-≤ S S≤X)

  step1 : R + Rc * S ≤ X + S * X
  step1 = +-mono-≤ IH Rc*S≤S*X

  X≤S*X : X ≤ S * X
  X≤S*X =
    ≤-trans (≤-reflexive (sym (*-identityʳ X)))
            (≤-trans (*-monoʳ-≤ X hS) (≤-reflexive (*-comm X S)))

  step2 : X + S * X ≤ S * X + S * X
  step2 = +-mono-≤ X≤S*X ≤-refl

  step3 : S * X + S * X ≤ S + (S * X + S * X)
  step3 = m≤n+m (S * X + S * X) S

  chain : R + Rc * S ≤ S + (S * X + S * X)
  chain = ≤-trans step1 (≤-trans step2 step3)

  result : R + Rc * S ≤ sizeStep S X
  result = subst (λ y → R + Rc * S ≤ y) (sym (sizeStep-eqn S X)) chain

  final : Caps.cReg (frameStep (suc j) c) ≤ Caps.cSize (frameStep (suc j) c)
  final = subst₂ _≤_ (frameStep-reg-suc c j) (sym (frameStep-size-suc c j)) result

B2-cReg≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) → Caps.cReg (capsAt e sl id) ≤ Caps.cSize (capsAt e sl id)
B2-cReg≤cSize {n = n} e sl zero =
  frameStep-reg≤size c₀ (sizeCount c₀ (capsBase e sl)) 1≤S₀ hReg₀
  where
  c₀ = caps (2 + sizeᵉ e + slotsSize sl) (suc (entryCeil n sl e))
            (suc (sizeᵉ e + slotsSize sl))
  1≤S₀ : 1 ≤ Caps.cSize c₀
  1≤S₀ = ≤-trans (s≤s z≤n) (s≤s (s≤s z≤n))
  hReg₀ : Caps.cReg c₀ ≤ Caps.cSize c₀
  hReg₀ = s≤s (n≤1+n (sizeᵉ e + slotsSize sl))
B2-cReg≤cSize e sl (suc id) =
  frameStep-reg≤size (capsAt e sl id) (sizeCount (capsAt e sl id) (capsH e sl id))
                     (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))
                     (B2-cReg≤cSize e sl id)

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
-- (B) THE SUPPLIERS.  S2 lands first: S1's proof calls it.
------------------------------------------------------------------

-- S2 `slots-tick` : the raw `Sched.slots` equality across a cascade.
-- PROVEN.  STRONGER than the two-conjunct version first asked for,
-- and deliberately so — the two conjuncts alone cannot bridge
-- `caps-tick`'s fixed entry-time `sl` to the wet family's own
-- convention of re-reading `Sched.slots` off whatever the current
-- schedule is, and that bridge is load-bearing below (`capsOut`).
--
-- The raw equality is a genuinely STRUCTURAL fact: grepping
-- Rx.Evaluator.agda for `slots =` finds exactly ONE occurrence in the
-- whole file — `sched-init`'s own construction.  No `record sched
-- { ... }` update anywhere in the mutual delivery clique ever touches
-- the `slots` field.  Most of the clique's own slots-invariance is
-- ALREADY PROVEN one layer down and reachable via the public chain:
-- `Keeps-Ring.agda:952` (`subscribeE-slots`) carries it through the
-- whole subscribe clique via the `Keeps` invariant, `Caps-Face.agda:
-- 3690+` (`foldPath-slots`/`dispatchShare-slots`/`shareGo-slots`) has
-- the delivery side, and `Measures.agda:493` (`finish-slots`) covers
-- `cascadeFinish`.  Only two thin wrappers were missing — `chainStep`
-- (one call into `foldPath`) and `cascadeGo`'s own fold over chains —
-- and both are direct compositions of what already exists.
chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st))) ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st

cascadeGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))) ≡ Sched.slots sched₀
cascadeGo-slots a id [] sched₀ st₀ = refl
cascadeGo-slots a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true = cascadeGo-slots a id chains sched₀ st₀
... | false =
      let (emits , sched₁ , st₁) =
            chainStep id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      in trans (cascadeGo-slots a id chains sched₁ st₁)
               (chainStep-slots id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }))

slots-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascade a id sched st))) ≡ Sched.slots sched
slots-tick a id sched st =
  let (emits , sched′ , st′) = cascadeGo a id (chainsOf a st) sched (cascadeLatch a st)
  in trans (finish-slots a sched′ st′)
           (cascadeGo-slots a id (chainsOf a st) sched (cascadeLatch a st))

------------------------------------------------------------------
-- S1 `fn-tick` : the fn face is preserved across a cascade.  PROVEN,
-- and NOT by the from-scratch walk over stepFrame/pushBurst/
-- subscribeInner/... this module's header once anticipated.  Ψ never
-- needs to grow (caseW is substitution-invariant, per INV?'s own
-- header at Measures.agda:5316-5323), so `fn-tick`'s conclusion —
-- Ψ-indexed only, no numeric B/E reading — is satisfied by ANY witness
-- INV? holds at, regardless of the size-axis bound reached.  That
-- means the already-proven `cascadeGo-walk` (Wet.agda:2145, folding
-- the WHOLE six-conjunct INV? over the chains list at a GROWING
-- ledger bound) is directly usable here: embed the caps-level input
-- bound `B` into `capᴱ B 3` (via `pow1`), widen the input facts across
-- that embedding, run cascadeLatch-INV → cascadeGo-walk →
-- cascadeFinish-INV, then project `fnCapBounded?` and the Ψ half of
-- `regsB?` out of the landed INV? at whatever bound the walk reached.
-- GAP 4's refuted size-axis composition (why P2/`cascadeGo-wet` is
-- still stuck) never enters, because nothing here needs to land back
-- at the fixed `sizeCapAt e sl (suc id)`.  The one remaining seam —
-- the conclusion is stated at `Ψ′ = ΨAt e sl′` (output slots), the
-- walk runs at `Ψ = ΨAt e sl` (input slots) — closes by S2 above.
------------------------------------------------------------------

-- reverse projections: pulling the Ψ-only half back OUT of an already
-- landed frameB?/pathB?/regsB? (Measures.agda) — the other direction
-- of frameB?-of-parts/pathB?-of-parts/regsB?-of-parts below.
frameBΨ?-of : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) {B Ψ : ℕ} →
  frameB? B Ψ f ≡ true → frameBΨ? Ψ f ≡ true
frameBΨ?-of (map-f fn)         h = proj₂ (∧-true _ _ h)
frameBΨ?-of (scan-f fn _)      h = proj₂ (∧-true _ _ h)
frameBΨ?-of (take-f _)         h = refl
frameBΨ?-of (from-inner _ _ _) h = refl
frameBΨ?-of (thru-outer _ _)   h = refl

pathBΨ?-of : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) {B Ψ : ℕ} →
  pathB? B Ψ p ≡ true → pathBΨ? Ψ p ≡ true
pathBΨ?-of root           h = refl
pathBΨ?-of (share-sink i) h = refl
pathBΨ?-of (f ↠ p) {B} {Ψ} h
  with ∧-true (frameB? B Ψ f) (pathB? B Ψ p) h
... | hf , hp = ∧-intro (frameBΨ?-of f hf) (pathBΨ?-of p hp)

regsBΨ?-of : ∀ {n} {Γ : Ctx n} {t}
  (rs : List (RegId × Source × Chain Γ t)) {B Ψ : ℕ} →
  regsB? B Ψ rs ≡ true → regsBΨ? Ψ rs ≡ true
regsBΨ?-of rs h =
  all-impl _ _ (λ en → pathBΨ?-of (proj₂ (proj₂ (proj₂ en)))) rs h

-- embedding a fixed bound B into capᴱ form: B ≤ 2 + 2·B ≤ capᴱ B 3,
-- the second step by `pow1` (Measures.agda, already proven).
2+b+b≡2+2b : ∀ b → (2 + b) + b ≡ 2 + 2 * b
2+b+b≡2+2b = solve 1 (λ b → (con 2 :+ b) :+ b := con 2 :+ (con 2 :* b)) refl

b≤2+2b : ∀ b → b ≤ 2 + 2 * b
b≤2+2b b = ≤-trans (m≤n+m b (2 + b)) (≤-reflexive (2+b+b≡2+2b b))

b≤capᴱ-b-3 : ∀ b → b ≤ capᴱ b 3
b≤capᴱ-b-3 b = ≤-trans (b≤2+2b b) (pow1 b {3} (s≤s z≤n))

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
fn-tick {e = e} a id sched st inv val =
  subst (λ ψ → fnCapBounded? ψ sched″ st″ ≡ true) (sym Ψ′≡Ψ) fcΨ ,
  subst (λ ψ → regsBΨ? ψ (EvalSt.registry st″) ≡ true) (sym Ψ′≡Ψ) regsBΨF
  where
  sl  = Sched.slots sched
  Ψ   = ΨAt e sl
  B   = sizeCapAt e sl id
  W   = B
  E₀  = 3

  3≤E₀ : 3 ≤ E₀
  3≤E₀ = ≤-refl

  B≤ : B ≤ capᴱ W E₀
  B≤ = b≤capᴱ-b-3 B

  inv-caps : INV? Ψ (capᴱ W E₀) sched st ≡ true
  inv-caps = INV?-widen sched st B≤ inv

  val-caps : valB? (capᴱ W E₀) Ψ (arrTy a) (arrVal a) ≡ true
  val-caps = valB?-widen (arrTy a) (arrVal a) B≤ val

  parts0 = INV-parts Ψ B sched st inv
  regsB0 : regsB? B Ψ (EvalSt.registry st) ≡ true
  regsB0 = proj₁ (proj₂ (proj₂ (proj₂ parts0)))

  chains = chainsOf a st

  chainsB : all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true
  chainsB = chainsOf-B B Ψ a st regsB0

  chainsB-caps : all (λ rc → pathB? (capᴱ W E₀) Ψ (proj₂ rc)) chains ≡ true
  chainsB-caps = chainsB?-widen chains B≤ chainsB

  latched = cascadeLatch a st

  inv-latch : INV? Ψ (capᴱ W E₀) sched latched ≡ true
  inv-latch = cascadeLatch-INV Ψ (capᴱ W E₀) a sched st inv-caps

  GO = cascadeGo-walk Ψ W a id chains sched latched E₀ 3≤E₀
                      inv-latch chainsB-caps val-caps

  E′ = proj₁ GO

  sched′ = proj₁ (proj₂ (cascadeGo a id chains sched latched))
  st′    = proj₂ (proj₂ (cascadeGo a id chains sched latched))

  invGo : INV? Ψ (capᴱ W E′) sched′ st′ ≡ true
  invGo = proj₁ (proj₂ (proj₂ GO))

  sched″ = proj₁ (cascadeFinish a sched′ st′)
  st″    = proj₂ (cascadeFinish a sched′ st′)

  invFinish : INV? Ψ (capᴱ W E′) sched″ st″ ≡ true
  invFinish = cascadeFinish-INV Ψ (capᴱ W E′) a sched′ st′ invGo

  partsF = INV-parts Ψ (capᴱ W E′) sched″ st″ invFinish

  fcΨ : fnCapBounded? Ψ sched″ st″ ≡ true
  fcΨ = proj₁ (proj₂ partsF)

  regsBF : regsB? (capᴱ W E′) Ψ (EvalSt.registry st″) ≡ true
  regsBF = proj₁ (proj₂ (proj₂ (proj₂ partsF)))

  regsBΨF : regsBΨ? Ψ (EvalSt.registry st″) ≡ true
  regsBΨF = regsBΨ?-of (EvalSt.registry st″) regsBF

  slotsEq : Sched.slots sched″ ≡ Sched.slots sched
  slotsEq = slots-tick a id sched st

  Ψ′≡Ψ : ΨAt e (Sched.slots sched″) ≡ Ψ
  Ψ′≡Ψ = cong (ΨAt e) slotsEq

------------------------------------------------------------------
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
