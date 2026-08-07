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
-- CONSUMERS.  CORRECTED 2026-08-05 (PROOF-STATE.md § "RULING:
-- Caps-Bridge was built UPSIDE DOWN") — the original text here said
-- "`cascade-dry` and `burst-wet` (.Wet) migrate to consume
-- `cascade-wet-via-caps`", which is IMPOSSIBLE: `.Caps-Bridge` imports
-- `.Wet` (below), so `.Wet` can never import `.Caps-Bridge` back. The
-- real fix moves the TOP of the tower UP instead: `cascade-dry`/
-- `drain-dry`/`budget-sufficient` MOVED here from `.Wet`, caps-threaded,
-- consuming `cascade-wet-via-caps` directly (§ D below). `.Wet` keeps
-- `burst-wet`/`burst-dry`/`burst-bounded`/`pop-INV`/`pop-head-bounded`,
-- which this module consumes unchanged. P1's analogue
-- (`subscribeE-wet-via-caps`) is NOW STATED as a postulate (§ D below),
-- with its sub-postulate `init-capsOK?`
-- also stated.  `burst-caps` is proved as a corollary of it.
-- Open: discharging the three postulates (the next task on the caps side).
module Verify-Budget-Sufficient.Caps-Bridge where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; _≡ᵇ_; _⊔_;
                                z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; m≤n+m; m≤m+n; n≤1+n;
                                       m≤m⊔n; m≤m*n;
                                       *-mono-≤; *-monoʳ-≤; +-mono-≤; *-comm;
                                       *-distribˡ-+; *-identityʳ; +-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; all; any; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
-- Fin/Vec vocabulary: the assembled cores' hypothesis types quantify over
-- slot indices (`residAt-connected`, `share-step-resid`).
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open import Rx.Prim      using (Gas; Tick; Id; Fuel; Source; close; exhausted)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; sizeᵉ; syncSizeᵉ;
                                -- named by the assembled cores' hypothesis types
                                Exp; Tm; sizeᵗˢ; μᵉ; unfoldμ)
open import Rx.Frame-Width using (dWᵉ; ceilᵉ; dW≤ceil; entryCeil; pWᵛ;
                                -- the three ceiling injections init-capsOK?-base is
                                -- assembled over, and the measures they bound
                                pmOⱽ; pmIⱽ; pWⱽ;
                                pmO≤ceil; pmI≤ceil; pWᵉ≤entryCeil)
open import Rx.Hop-Depth  using (hopDᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                RegId; Chain;
                                Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                arrTy; arrVal; arrTick; arrSource; cascade;
                                cascadeGo; cascadeLatch; cascadeFinish;
                                chainStep; chainsOf; hasDry;
                                subscribeE; budgetAt; slotsSize; opIterD;
                                sizeStep; capsBase;
                                sched-next; schedGo; schedHeadOf; schedEarlier;
                                drain; evaluate; sched-init; st-init;
                                -- named by the assembled cores' hypothesis types
                                shared; memberSource; foldStep;
                                sLvlD; sizeAt; lvls)

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
-- `depthChain` joins `depthE` here because `dry-tick`'s assembly consumes
-- `chainStep-caps`, whose statement is stated at the chain depth measure.
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthChain)
-- depth-capped (proven in Depth-Bound): depthE ≤ 3·cSize when capsOK?.
-- Consumed by subscribeE-wet-via-caps once proved (via depth-capped
-- supplying dep ≤ capsH, then sizeCount-body closing the sizeCount gap).
-- Acyclic: Depth-Bound imports Wet and Subscribe-Face, NOT Caps-Bridge.
open import Verify-Budget-Sufficient.Depth-Bound using (depth-capped)
open import Verify-Budget-Sufficient.Op-Dominance using (opIterD-dominated)
open import Verify-Budget-Sufficient.Caps
  using (2≤capsAt-size; capsAt-base-size; capsAt-base-wid; sizeCount-body; three-size-le-blowH)
open import Verify-Budget-Sufficient.Anchor-Dry
  using (chainStep-dry; foldPath-dry; subscribeInner-dry; dry-hop)
open import Verify-Budget-Sufficient.Occurrences using (pathOccs?)
open import Rx.Evaluator using (foldPath; subscribeInner; AllOp; NodeId)
open import Rx.Prim using (InstEvent)
open import Rx.Exp using (obs; sizeᵛ)

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
--
-- ASSEMBLY (2026-08-06): narrowed over the cascade-level facts it was
-- written to be built from.  `cascade` IS cascadeLatch → cascadeGo →
-- cascadeFinish, so the pieces are .Wet's `cascadeGo-wet` (the walk's
-- own dry half — this is what makes that postulate reachable at all),
-- .Subscribe-Face's per-chain caps step, and .Deliveries' four cascade
-- counts, which say the latch clears the ledger and the two walk lines
-- account for it.
postulate
  dry-tick-core :
    -- cascadeGo-wet  (Verify-Budget-Sufficient/Wet.agda:4343)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (a : Arrival Γ) (id : Id)
        (chains : List (RegId × Path Γ (arrTy a) t))
        (sched : Sched Γ) (st : EvalSt e) →
        let sl = Sched.slots sched
            Ψ  = ΨAt e sl
            B  = sizeCapAt e sl id
        in INV? Ψ B sched st ≡ true →
           valB? B Ψ (arrTy a) (arrVal a) ≡ true →
           all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true →
           let r = cascadeGo a id chains sched st
           in (hasDry (proj₁ r) ≡ false)
              × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                      (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                      (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     ) →
    -- chainStep-caps  (Verify-Budget-Sufficient/Subscribe-Face.agda:3464)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (c : Caps) (dep bud j : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
      (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
      2 ≤ Caps.cSize c →
      1 ≤ Caps.cReg c →
      Sched.slots sched ≡ sl →
      slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
      slotsSize sl ≤ Caps.cSize c →
      capsOK? (frameStep j c) sched st ≡ true →
      pathSz? (Caps.cSize (frameStep j c)) path ≡ true →
      valCaps? (frameStep j c) sl (arrTy a) (arrVal a) ≡ true →
      depthChain id a path sched st ≤ dep →
      let r = chainStep id a path sched st
      in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
         × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     ) →
    -- cascadeGo-skip-N  (Verify-Budget-Sufficient/Deliveries.agda:868)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (a : Arrival Γ) (id : Id) (rid : RegId) (c : Path Γ (arrTy a) t)
        (chains : List (RegId × Path Γ (arrTy a) t))
        (sched : Sched Γ) (st : EvalSt e) →
        any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
        delivN st (proj₂ (proj₂ (cascadeGo a id ((rid , c) ∷ chains) sched st)))
          ≡ delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
     ) →
    -- cascadeGo-cons-N  (Verify-Budget-Sufficient/Deliveries.agda:879)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (a : Arrival Γ) (id : Id) (rid : RegId) (c : Path Γ (arrTy a) t)
        (chains : List (RegId × Path Γ (arrTy a) t))
        (sched : Sched Γ) (st : EvalSt e) →
        any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
        let st₀ = consᵈ rid st
            cs  = chainStep id a c sched st₀
            st₁ = proj₂ (proj₂ cs) in
        delivN st (proj₂ (proj₂ (cascadeGo a id ((rid , c) ∷ chains) sched st)))
          ≡ suc (delivN st₀ st₁
                 + delivN st₁ (proj₂ (proj₂ (cascadeGo a id chains
                                              (proj₁ (proj₂ cs)) st₁))))
     ) →
    -- cascadeLatch-deliv  (Verify-Budget-Sufficient/Deliveries.agda:915)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (a : Arrival Γ) (st : EvalSt e) → EvalSt.delivered (cascadeLatch a st) ≡ []
     ) →
    -- cascade-delivN  (Verify-Budget-Sufficient/Deliveries.agda:929)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
        length (EvalSt.delivered (proj₂ (proj₂ (cascade a id sched st))))
          ≡ delivN (cascadeLatch a st)
                   (proj₂ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st))))
     ) →
    -- THE DRY FAMILY (Verify-Budget-Sufficient/Anchor-Dry.agda) — the
    -- reachability-sourced anchor facts (Phase 1b step 3).  Threaded
    -- here so the eventual clause grind consumes them where the
    -- cascade meets chainStep/foldPath/subscribeInner; their premises
    -- are exactly the INV?/capsOK? conjuncts this core's own driver
    -- carries.  dry-hop closes hop-edge's size premise from valB?.
    -- chainStep-dry  (Anchor-Dry.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
      (sched : Sched Γ) (st : EvalSt e) →
      let sl = Sched.slots sched
          Ψ  = ΨAt e sl
          B  = sizeCapAt e sl id
          sz = sizeᵉ e + slotsSize sl
          Ŝ  = sizeCapAt e sl (suc id)
      in INV? Ψ B sched st ≡ true →
         capsOK? (capsAt e sl id) sched st ≡ true →
         valB? B Ψ (arrTy a) (arrVal a) ≡ true →
         pathB? B Ψ path ≡ true →
         pathOccs? sz path ≡ true →
         burstB? Ŝ Ψ (proj₁ (chainStep id a path sched st)) ≡ true
     ) →
    -- foldPath-dry  (Anchor-Dry.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
      (path : Path Γ u t) (vals : List (Val Γ u))
      (evs : List (InstEvent (Val Γ t))) (fin : Bool)
      (sched : Sched Γ) (st : EvalSt e) →
      let sl = Sched.slots sched
          Ψ  = ΨAt e sl
          B  = sizeCapAt e sl id
          sz = sizeᵉ e + slotsSize sl
          Ŝ  = sizeCapAt e sl (suc id)
      in INV? Ψ B sched st ≡ true →
         capsOK? (capsAt e sl id) sched st ≡ true →
         pathB? B Ψ path ≡ true →
         pathOccs? sz path ≡ true →
         all (valB? B Ψ u) vals ≡ true →
         all (eventB? B Ψ) evs ≡ true →
         burstB? Ŝ Ψ (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st)) ≡ true
     ) →
    -- subscribeInner-dry  (Anchor-Dry.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
      (id : Id) (now : Tick) (o : Val Γ (obs u))
      (sched : Sched Γ) (st : EvalSt e) →
      let sl = Sched.slots sched
          Ψ  = ΨAt e sl
          B  = sizeCapAt e sl id
          sz = sizeᵉ e + slotsSize sl
          Ŝ  = sizeCapAt e sl (suc id)
      in INV? Ψ B sched st ≡ true →
         capsOK? (capsAt e sl id) sched st ≡ true →
         valB? B Ψ (obs u) o ≡ true →
         pathB? B Ψ κ ≡ true →
         pathOccs? sz κ ≡ true →
         all (valB? Ŝ Ψ u)
             (proj₁ (proj₂ (subscribeInner g op allNid κ id now o sched st))) ≡ true
     ) →
    -- dry-hop  (Anchor-Dry.agda)
    (∀ {n} {Γ : Ctx n} {u : Ty} (B Ŝ Ψ : ℕ) (o : Val Γ (obs u)) →
      B ≤ Ŝ → valB? B Ψ (obs u) o ≡ true → sizeᵛ (obs u) o ≤ Ŝ
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
    in INV? Ψ B sched st ≡ true →
       valB? B Ψ (arrTy a) (arrVal a) ≡ true →
       hasDry (proj₁ (cascade a id sched st)) ≡ false

dry-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
  in INV? Ψ B sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     hasDry (proj₁ (cascade a id sched st)) ≡ false
dry-tick =
  dry-tick-core
    (λ {n} {Γ} {t} {e} → cascadeGo-wet {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → chainStep-caps {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → cascadeGo-skip-N {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → cascadeGo-cons-N {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → cascadeLatch-deliv {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → cascade-delivN {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} → chainStep-dry {n} {Γ} {t} {e})
    (λ {n} {Γ} {t} {e} {u} → foldPath-dry {n} {Γ} {t} {e} {u})
    (λ {n} {Γ} {t} {e} {u} → subscribeInner-dry {n} {Γ} {t} {e} {u})
    (λ {n} {Γ} {u} → dry-hop {n} {Γ} {u})

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

------------------------------------------------------------------
-- (D) THE THREADED TOP OF THE TOWER.  MOVED here from .Wet
-- (PROOF-STATE.md § "RULING: Caps-Bridge was built UPSIDE DOWN") — this
-- is not a copy beside `cascade-dry`/`drain-dry`/`budget-sufficient`,
-- it IS them, generalised to also carry `capsOK?` beside `INV?` through
-- the fuel loop.  `.Wet` cannot state this (it imports `.Wet`... no —
-- it cannot consume `cascade-wet-via-caps`, since `.Caps-Bridge` imports
-- `.Wet` and not the other way around), so the top of the tower had to
-- move UP to where `cascade-wet-via-caps` already lives, not down to
-- where `cascadeGo-wet` (P2) does.  `.Wet` keeps `burst-wet`/`burst-dry`/
-- `burst-bounded`/`pop-INV`/`pop-head-bounded` — this module consumes
-- all five, unchanged, as the INV?-only half of its own burst and pop.
--
-- REHEARSED in `agda/probe/Caps-Thread-Probe.agda` (2026-08-05) as
-- `drain-dry-threaded`/`budget-sufficient-threaded`; landed here under
-- their FINAL names (`drain-dry`, `budget-sufficient`) since they
-- replace, not sit beside, `.Wet`'s versions of the same name.
------------------------------------------------------------------

-- § 1  THE HEAD, WIDTH HALF.  capsOK?'s `widLive` conjunct, extracted
-- at the popped arrival — the width sibling of GAP 3's
-- schedHeadOf-head/schedGo-head.
--
-- NOTE ON `cOK`: the first attempt named this hypothesis `caps` and
-- Agda rejected the LHS with "caps is not a constructor of the
-- datatype _≡_".  CAUSE, confirmed: `caps` IS a constructor in scope —
-- it is the `Caps` record's own constructor (Caps.agda:105,
-- `constructor caps`) — so in a pattern the name resolves to that
-- constructor instead of binding fresh.  Same family as the
-- PatternShadowsConstructor warning `make agda-all` prints for
-- CLI/Encode.agda's `dried`, except fatal here because the argument's
-- type is `_≡_` and `caps` belongs to a different datatype.  Any
-- lowercase record-constructor name is a landmine as a variable:
-- `caps`, `slots`, `sched` are all worth checking before use.

schedHeadOf-widHead : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  widLive W sl l ≡ true →
  (pWᵛ n sl (arrTy a) (arrVal a) ≤ᵇ W) ≡ true
schedHeadOf-widHead W sl l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₁ (∧-true _ _ bnd′)

schedGo-widHead : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (widLive W sl) ls ≡ true →
  (pWᵛ n sl (arrTy a) (arrVal a) ≤ᵇ W) ≡ true
schedGo-widHead W sl (l ∷ ls) eq bs
  with ∧-true (widLive W sl l) (all (widLive W sl) ls) bs
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-widHead W sl (l ∷ ls) refl bs | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  schedGo-widHead W sl ls eqR bls
schedGo-widHead W sl (l ∷ ls) refl bs | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  schedHeadOf-widHead W sl l eqH bl
schedGo-widHead W sl (l ∷ ls) eq bs | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = schedHeadOf-widHead W sl l eqH bl
... | false | refl = schedGo-widHead W sl ls eqR bls

pop-head-widCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  capsOK? c sched st ≡ true →
  (pWᵛ n (Sched.slots sched) (arrTy a) (arrVal a) ≤ᵇ Caps.cWid c) ≡ true
pop-head-widCaps c sched st eq cOK
  with capsOK?-parts c sched st cOK
... | _ , _ , wl , _ , _ with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      schedGo-widHead (Caps.cWid c) (Sched.slots sched) (Sched.live sched) eqL wl

-- the joint reader cascade-dry's caps face wants.  The SIZE half is
-- free: `sizeCapAt e sl id` IS `Caps.cSize (capsAt e sl id)` by
-- definition (Wet.agda:4117), so GAP 3's pop-head-bounded already
-- supplies it; only the width half above is new content.
pop-head-valCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? (ΨAt e (Sched.slots sched)) (sizeCapAt e (Sched.slots sched) id) sched st ≡ true →
  capsOK? (capsAt e (Sched.slots sched) id) sched st ≡ true →
  valCaps? (capsAt e (Sched.slots sched) id) (Sched.slots sched) (arrTy a) (arrVal a) ≡ true
-- `valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)` (Measures:5337)
-- and `valCaps? c sl u v = (sizeᵛ u v ≤ᵇ cSize c) ∧ (pWᵛ n sl u v ≤ᵇ cWid c)`
-- (Caps-Face:667).  At `B = sizeCapAt e sl id = cSize (capsAt e sl id)`
-- the two FIRST conjuncts are literally the same Bool, so the size half
-- is a projection off pop-head-bounded — via ∧-true, since valB? is a
-- Bool conjunction and not a Σ (the first attempt used proj₁ directly
-- and that is what the probe caught).
pop-head-valCaps {e = e} id sched st eq inv cOK =
  ∧-intro
    (proj₁ (∧-true _ _
      (pop-head-bounded (ΨAt e (Sched.slots sched))
                        (sizeCapAt e (Sched.slots sched) id) sched st eq inv)))
    (pop-head-widCaps (capsAt e (Sched.slots sched) id) sched st eq cOK)

------------------------------------------------------------------
-- § 2  THE TAIL.  capsOK? survives a pop — the capsOK? sibling of
-- `pop-INV`.  Four of the five conjuncts are pop-bounded /
-- untouched / pop-slots-transported exactly as pop-INV's are; only
-- widLive needs a new tail-preserving induction, the same shape as
-- `pop-fnCap`'s `schedGo-fnCap`.
------------------------------------------------------------------

schedHeadOf-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  widLive W sl l ≡ true → widLive W sl l′ ≡ true
schedHeadOf-widLive W sl l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (widLive W sl) ls ≡ true → all (widLive W sl) ls′ ≡ true
schedGo-widLive W sl (l ∷ ls) eq bnd
  with ∧-true (widLive W sl l) (all (widLive W sl) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-widLive W sl (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-widLive W sl ls eqR bls)
schedGo-widLive W sl (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-widLive W sl l eqH bl) bls
schedGo-widLive W sl (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-widLive W sl l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-widLive W sl ls eqR bls)

pop-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sched : Sched Γ)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  all (widLive W (Sched.slots sched)) (Sched.live sched) ≡ true →
  all (widLive W (Sched.slots sched′)) (Sched.live sched′) ≡ true
pop-widLive W sched eq h with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl = schedGo-widLive W (Sched.slots sched) (Sched.live sched) eqL h

pop-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  capsOK? c sched st ≡ true → capsOK? c sched′ st ≡ true
pop-caps c sched st eq h with capsOK?-parts c sched st h
... | sb , rg , wl , wn , rl =
  ∧-intro (pop-bounded (Caps.cSize c) sched st eq sb)
  (∧-intro rg
  (∧-intro (pop-widLive (Caps.cWid c) sched eq wl)
  (∧-intro (subst (λ sl → all (λ kv → widNode (Caps.cWid c) sl (proj₂ kv)) (EvalSt.nodes st) ≡ true)
                  (sym (pop-slots sched eq)) wn)
           rl)))

------------------------------------------------------------------
-- § 3  THE ASSEMBLY.  The fuel loop and the theorem, with `capsOK?`
-- travelling beside `INV?`.
--
-- NOTE what is NOT restated here: the one-cascade step.  `cascade-dry`
-- threaded with a caps face has EXACTLY `cascade-wet-via-caps`'s
-- conclusion, character for character (above), so that step is a
-- relocation and not a proof.  Its dryness half rests on `dry-tick`,
-- which is where the ANCHOR PROBLEM sits — the postulate this route
-- trades P2 (`cascadeGo-wet`) for.
------------------------------------------------------------------

-- Historical note: burst-caps was previously a postulate in this block.
-- The two open problems that blocked it — (i) `capsOK?` at the initial
-- state (no analogue of init-INV existed) and (ii) opIterD vs. the
-- sizeCount/capsH recurrence — are now stated as sub-postulates below,
-- and burst-caps is proved as a corollary of subscribeE-wet-via-caps.
-- The original reasoning is preserved here for traceability.

postulate
  -- (1) INIT-CAPSOK?-SUC — the general id ≥ 1 case.  The id = 0 case is
  -- proved as `init-capsOK?-0` (real definition below), which lifts
  -- `init-capsOK?-base` via `capsOK?-mono`.  `init-capsOK?` (below) is
  -- the assembly dispatching both cases, kept at its original type so
  -- call sites need not change.
  init-capsOK?-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    (id : ℕ) →
    capsOK? (capsAt e ins (suc id)) (sched-init e ins) (st-init e) ≡ true

------------------------------------------------------------------
-- (2) THE SUBSCRIBE-SIDE MEASURE BRIDGE, and it is now an ASSEMBLY
-- rather than a postulate — which is what gives `depth-capped`
-- (Depth-Bound) its first real consumer.
--
-- SPEND `depth-capped` AT THE PRE-BLOWUP BASE CAPS, NOT AT
-- `capsAt e ins 0`.  This is the whole content of the arrangement and
-- it is not visible from the goal, so it is written here as well as in
-- PROOF-STATE.md § "RULING: `depth-capped` must be spent at the SMALL
-- caps".  `capsAt e sl zero` is ITSELF a `frameBlowup` (Caps.agda:452;
-- `baseCaps-is-inner` below pins that by `refl`), so its `cSize` is
-- `sizeStep` iterated `sizeCount`-many times.  Routing the depth bound
-- through THAT number demands `3 · cSize (capsAt e ins 0) ≤ capsH`,
-- i.e. that `poolCount` at `M = towerℕ capsBase` dominate an
-- EXPONENTIAL of `sizeCount` at `M = S₀` — a cross-`M` growth-rate
-- argument that exists nowhere in this repo.  The one chain relating
-- the two, `capsAt-tower` (Caps.agda:1322), points the WRONG WAY: it
-- gives `cSize ≤ towerℕ capsH`, and `towerℕ h ≫ h`, so it makes the
-- goal harder.  `depth-capped` quantifies over ANY caps satisfying
-- `capsOK?`; nothing forces the blown-up one.
--
-- AND THE SMALL CAPS IS THE HONEST PLACE TO STAND, because at the ROOT
-- the state is `st-init`/`sched-init`: three of `capsOK?`'s five
-- conjuncts (Caps-Face.agda:299) are then VACUOUS — empty registry
-- kills `regsSz?` and the `length … ≤ᵇ cReg` bound, empty
-- `EvalSt.nodes` kills the `widNode` sweep — and the two that survive
-- (`stBounded?`, the `widLive` sweep) are bounded by SYNTAX-level
-- ceilings, which is exactly what `baseCaps`'s fields ARE.
------------------------------------------------------------------

-- the caps `capsAt e sl zero` blows up from, named so the depth bound
-- can be taken at it.  That it IS that blowup's inner argument holds by
-- `refl` — checked as `baseCaps-is-inner` in
-- agda/probe/Depth-Wire-Probe.agda, which is where it lives because
-- nothing in the claim graph consumes it and the wiring law admits no
-- orphans here.
baseCaps : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Caps
baseCaps {n = n} e sl = caps (2 + sizeᵉ e + slotsSize sl)
                             (suc (entryCeil n sl e))
                             (suc (sizeᵉ e + slotsSize sl))

postulate
  -- capsOK? at the SMALL caps at the initial state.  NOT vacuous: five
  -- real ≡ true conjuncts, three of them discharged by the emptiness of
  -- `st-init` once someone grinds it.  `init-capsOK?` above is the same
  -- fact at the blown-up caps and should eventually be DERIVED from
  -- this one through `capsOK?-mono` (Caps-Face.agda:365) plus
  -- `cSize≤frameBlowup` (Caps.agda:946), retiring one of the two.
  --
  -- ASSEMBLY (2026-08-06): narrowed to `-core` over the eight proven
  -- facts this was written to be built from — the three Frame-Width
  -- ceiling injections that put the base caps' width field under
  -- `entryCeil`, the slot-condition widening, the init state's
  -- boundedness, and the two size ceilings.  Each hypothesis is an
  -- already-proven proposition, so `-core` is equivalent to the
  -- original, not stronger and not weaker.
  init-capsOK?-base-core :
    -- pmO≤ceil  (Rx/Frame-Width.agda:782)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ)
      (e : Exp Γ Δᵍ Δ Θ t) → pmOⱽ j [] sl k e ≤ ceilᵉ j sl e
     ) →
    -- pmI≤ceil  (Rx/Frame-Width.agda:787)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ) (k : ℕ)
      (e : Exp Γ Δᵍ Δ Θ t) → pmIⱽ j [] sl k e ≤ ceilᵉ j sl e
     ) →
    -- pWᵉ≤entryCeil  (Rx/Frame-Width.agda:831)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ)
      (e : Exp Γ Δᵍ Δ Θ t) → pWⱽ j [] sl e ≤ entryCeil j sl e
     ) →
    -- slotsCaps?-widen  (Verify-Budget-Sufficient/Caps-Face.agda:813)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) {B B′ W W′ : ℕ} →
      B ≤ B′ → W ≤ W′ → slotsCaps? B W sl ≡ true → slotsCaps? B′ W′ sl ≡ true
     ) →
    -- init-bounded  (Verify-Budget-Sufficient/Measures.agda:1163)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
      (id : Id) → stBounded? (sizeBudgetAt e ins id) (sched-init e ins)
                             (st-init e) ≡ true
     ) →
    -- size≤budget  (Verify-Budget-Sufficient/Measures.agda:195)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : Id) → sizeᵉ e ≤ sizeBudgetAt e sl id
     ) →
    -- 1≤sizeᵗˢ  (Verify-Budget-Sufficient/Measures.agda:1419)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
      1 ≤ sizeᵗˢ ts
     ) →
    -- B1-cSize≡sizeCapAt  (Verify-Budget-Sufficient/Caps-Bridge.agda:94)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : ℕ) → Caps.cSize (capsAt e sl id) ≡ sizeCapAt e sl id
     ) →
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true

init-capsOK?-base : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true
init-capsOK?-base =
  init-capsOK?-base-core
    (λ {n} {Γ} {Δᵍ} {Δ} {Θ} {t} → pmO≤ceil {n} {Γ} {Δᵍ} {Δ} {Θ} {t})
    (λ {n} {Γ} {Δᵍ} {Δ} {Θ} {t} → pmI≤ceil {n} {Γ} {Δᵍ} {Δ} {Θ} {t})
    (λ {n} {Γ} {Δᵍ} {Δ} {Θ} {t} → pWᵉ≤entryCeil {n} {Γ} {Δᵍ} {Δ} {Θ} {t})
    (λ {n} {Γ} → slotsCaps?-widen {n} {Γ})
    (λ {n} {Γ} {t} → init-bounded {n} {Γ} {t})
    (λ {n} {Γ} {t} → size≤budget {n} {Γ} {t})
    (λ {n} {Γ} {Δᵍ} {Δ} {Θ} {t} → 1≤sizeᵗˢ {n} {Γ} {Δᵍ} {Δ} {Θ} {t})
    (λ {n} {Γ} {t} → B1-cSize≡sizeCapAt {n} {Γ} {t})

-- Lifts init-capsOK?-base from the small caps (baseCaps) to the actual
-- initial caps (capsAt e ins 0 = frameBlowup (baseCaps e ins) (capsBase e ins))
-- via capsOK?-mono at the ⊑ᶜ witnessed by:
--   cSize: capsAt-base-size e ins 0
--   cWid:  capsAt-base-wid e ins 0
--   cReg:  m≤m*n — frameBlowup multiplies cReg by suc (sizeCount * cSize) ≥ 1
-- This wires init-capsOK?-base to burst-caps as a real code consumer,
-- retiring the monolithic `init-capsOK?` postulate at that call site.
init-capsOK?-0 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  capsOK? (capsAt e ins 0) (sched-init e ins) (st-init e) ≡ true
init-capsOK?-0 {n = n} e ins =
  capsOK?-mono
    (baseCaps e ins) (capsAt e ins 0)
    (sched-init e ins) (st-init e)
    ( capsAt-base-size e ins 0
    , capsAt-base-wid  e ins 0
    , m≤m*n (Caps.cReg (baseCaps e ins)) _
    )
    (init-capsOK?-base e ins)

-- Assembly: dispatches to init-capsOK?-0 (proven) at id = 0 and to
-- init-capsOK?-suc (postulate) for id ≥ 1.  Keeps the original type so
-- call sites (burst-caps below) need not change.  This wires
-- init-capsOK?-0 (and transitively init-capsOK?-base) into the proof.
init-capsOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (id : ℕ) →
  capsOK? (capsAt e ins id) (sched-init e ins) (st-init e) ≡ true
init-capsOK? e ins zero    = init-capsOK?-0 e ins
init-capsOK? e ins (suc n) = init-capsOK?-suc e ins n

-- Wires three-size-le-blowH (Caps.agda:1413): three pre-blowup sizes ≤ capsH e ins 0.
-- cSize(baseCaps e ins) = 2 + sizeᵉ e + slotsSize ins = 2 + X definitionally
-- (both sides reduce to suc(suc(sizeᵉ e + slotsSize ins))), so
-- three-size-le-blowH X E (s≤s (s≤s z≤n)) with X = sizeᵉ e + slotsSize ins and
-- E = entryCeil n ins e applies directly.
three-size≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Caps.cSize (baseCaps e ins) + Caps.cSize (baseCaps e ins)
    + Caps.cSize (baseCaps e ins)
    ≤ capsH e ins 0
three-size≤capsH {n = n} e ins =
  three-size-le-blowH (sizeᵉ e + slotsSize ins) (entryCeil n ins e) (s≤s (s≤s z≤n))

-- Wires depth-capped (Depth-Bound.agda:244): root depth bound via the base caps.
-- Applies depth-capped at c := baseCaps e ins (the PRE-BLOWUP inner argument of
-- capsAt e ins 0's frameBlowup), then chains with three-size≤capsH.
-- Four side-conditions at baseCaps / sched-init / st-init / root:
--   (i)   init-capsOK?-base e ins
--   (ii)  slotsSize ins ≤ cSize(baseCaps e ins):  m≤n+m (slotsSize ins) (2 + sizeᵉ e)
--   (iii) sizeᵉ e ≤ cSize(baseCaps e ins):  ≤-trans (m≤n+m sizeᵉ e 2) (m≤m+n ...)
--   (iv)  suc(pathLen root) = 1 ≤ cSize(baseCaps e ins):  s≤s z≤n
depthE≤capsH-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
    ≤ capsH e ins 0
depthE≤capsH-root e ins =
  ≤-trans
    (depth-capped (baseCaps e ins) (budgetAt e ins 0) e root 0 0
       (sched-init e ins) (st-init e)
       (init-capsOK?-base e ins)
       (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
       (≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize ins)))
       (s≤s z≤n))
    (three-size≤capsH e ins)

-- (3) SUBSCRIBEE-WET-VIA-CAPS — P1's subscribe-side mirror.
-- Mirrors cascade-wet-via-caps (~line 526) structurally.
-- Wet hypotheses: those of subscribeE-wet (Wet.agda:~4303).
-- Caps additions: capsOK? at the entry level + dWᵉ ≤ cWid.
-- burst-caps (below) is a closed corollary at the root call.
-- WIRING NOTE: depth-capped and three-size-le-blowH are now wired:
-- depth-capped feeds depthE≤capsH-root (above) via three-size≤capsH;
-- depthE≤capsH-root is passed as depth-bound-root to sub-charge-capsOK-lift-core
-- and supplied at sub-charge-capsOK-lift below.
postulate
  -- THE ONE REMAINING GAP on the subscribe side: `capsOK?` at the growth
  -- index `frameStep j′ c` lifts to `capsAt e sl (suc id)`.
  -- ROUTE (2026-08-06): `opIterD-dominated` (hypothesis 5) at general id,
  -- with 2 ≤ S from `2≤capsAt-size` and 1 ≤ R from `1≤capsAt-reg` (both
  -- free).  `nestOK`/`opsOK` (the new trailing premises) supply k≤S/m≤S;
  -- `sizeCount-body` identifies the lvls output with `sizeCount c dep`;
  -- `frameStep-mono-j` + `capsAt-suc-full` + `capsOK?-mono` close the lift.
  --
  -- ASSEMBLY (2026-08-06): narrowed over exactly the facts that route
  -- names — the two refl endpoints identifying `capsAt (suc id)` with
  -- the full `frameStep`, the ⊑ᶜ reflexivity and frame-size widening
  -- the `capsOK?-mono` step runs on, `opIterD-dominated` at general id
  -- (the replaced root-only bound), and the one-more-item fold headroom.
  sub-charge-capsOK-lift-core :
    -- frameStep-full  (Verify-Budget-Sufficient/Caps.agda:888)
    (∀ (c : Caps) (d : ℕ) →
      frameStep (sizeCount c d) c ≡ frameBlowup c d
     ) →
    -- capsAt-suc-full  (Verify-Budget-Sufficient/Caps.agda:893)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
      capsAt e sl (suc id)
        ≡ frameStep (sizeCount (capsAt e sl id) (capsH e sl id)) (capsAt e sl id)
     ) →
    -- ⊑ᶜ-refl  (Verify-Budget-Sufficient/Caps-Face.agda:3425)
    (∀ (c : Caps) → c ⊑ᶜ c
     ) →
    -- frameSz?-⊑  (Verify-Budget-Sufficient/Caps-Face.agda:3603)
    (∀ {n} {Γ : Ctx n} {s u} {c c′ : Caps} (f : Frame Γ s u) →
      c ⊑ᶜ c′ → frameSz? (Caps.cSize c) f ≡ true → frameSz? (Caps.cSize c′) f ≡ true
     ) →
    -- opIterD-dominated  (Verify-Budget-Sufficient/Op-Dominance.agda:103)
    (∀ (S W d k m R : ℕ) → 2 ≤ S → k ≤ S → m ≤ S → 1 ≤ R →
      opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)
     ) →
    -- prepend-fits  (Verify-Budget-Sufficient/Subscribe-Face.agda:553)
    (∀ (S W L : ℕ) → 2 ≤ S → L ≤ suc W → suc L ≤ suc (foldStep S W)
     ) →
    -- depth-bound-root  (Caps-Bridge.agda:depthE≤capsH-root)
    -- Root depth bound; used in the id=0 branch of the eventual lift proof.
    -- Proved by depth-capped (at baseCaps) composed with three-size≤capsH.
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
      depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
        ≤ capsH e ins 0
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
    let sl = Sched.slots sched
        c  = capsAt e sl id
        r  = subscribeE g b κ id now sched st
    in capsOK? (frameStep j′ c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                    (depthE g b κ id now sched st)
                    (nest b sl (EvalSt.connectedShares st))
                    (suc (sizeᵉ b)) 0 →
       nest b sl (EvalSt.connectedShares st) ≤ Caps.cSize c →    -- nestOK
       suc (sizeᵉ b) ≤ Caps.cSize c →                            -- opsOK
       capsOK? (capsAt e sl (suc id))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

sub-charge-capsOK-lift : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
  let sl = Sched.slots sched
      c  = capsAt e sl id
      r  = subscribeE g b κ id now sched st
  in capsOK? (frameStep j′ c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                  (depthE g b κ id now sched st)
                  (nest b sl (EvalSt.connectedShares st))
                  (suc (sizeᵉ b)) 0 →
     nest b sl (EvalSt.connectedShares st) ≤ Caps.cSize c →    -- nestOK
     suc (sizeᵉ b) ≤ Caps.cSize c →                            -- opsOK
     capsOK? (capsAt e sl (suc id))
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
sub-charge-capsOK-lift =
  sub-charge-capsOK-lift-core
    frameStep-full
    (λ {n} {Γ} {t} → capsAt-suc-full {n} {Γ} {t})
    ⊑ᶜ-refl
    (λ {n} {Γ} {s} {u} {c} {c′} → frameSz?-⊑ {n} {Γ} {s} {u} {c} {c′})
    opIterD-dominated
    prepend-fits
    depthE≤capsH-root

-- THE SUBSCRIBE-SIDE ASSEMBLY.  A real definition, and the reason
-- `sub-charge` (above, PROVEN) is no longer an orphan.
--
-- IT DOES NOT REPLACE P1 — IT RESTS ON IT.  `hasDry` and `INV?` come
-- straight out of `subscribeE-wet` (Wet.agda, P1); this adds only the
-- third conjunct, `capsOK?` at `suc id`.  So read the caps route's
-- subscribe side as "P1 PLUS a caps conclusion", not as an alternative
-- to P1.  An earlier plan had this mirroring P1 rather than consuming
-- it; that would need `hasDry`/`INV?` re-derived from the caps face,
-- which nothing here does.
--
-- THE TWO PATH HYPOTHESES ARE NEW, and they are load-bearing.
-- `pathB?` carries NO length conjunct
-- (`pathB? B Ψ (f ↠ p) = frameB? B Ψ f ∧ pathB? B Ψ p`) while `pathSz?`
-- requires `suc (pathLen p) ≤ᵇ B` at every suffix — so deriving the
-- latter from the former is not merely unproven, it is FALSE: take a
-- tiny `e` (small `B`), a tiny `b`, and a long chain of `map-f` frames
-- with small step functions, and every hypothesis holds while the
-- conclusion fails.  The information has to be supplied, and it is free
-- at the only call site (`κ := root`, below).
subscribeE-wet-via-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     pathSz? B κ ≡ true →
     suc (pathLen κ) ≤ B →
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
     capsOK? (capsAt e sl id) sched st ≡ true →
     dWᵉ n sl b ≤ Caps.cWid (capsAt e sl id) →
     nest b sl (EvalSt.connectedShares st) ≤ B →    -- nestOK
     suc (sizeᵉ b) ≤ B →                            -- opsOK
     let r   = subscribeE g b κ id now sched st
         sl′ = Sched.slots (proj₁ (proj₂ r))
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e sl′) (sizeCapAt e sl′ (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (capsOK? (capsAt e sl′ (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
subscribeE-wet-via-caps {n = n} {e = e} g b κ id now sched st
                        inv pathB pathSzκ lenκ szB fnB gas cOK dW nestOK opsOK =
  dry , invOut , capsOut
  where
  sl      = Sched.slots sched
  Ψ       = ΨAt e sl
  B       = sizeCapAt e sl id
  c       = capsAt e sl id
  r       = subscribeE g b κ id now sched st
  sched′  = proj₁ (proj₂ r)
  st′     = proj₂ (proj₂ r)

  sl′Eq : Sched.slots sched′ ≡ sl
  sl′Eq = subscribeE-slots g b κ id now sched st

  invP    = INV-parts Ψ B sched st inv
  ss-in   : (slotsSize sl ≤ᵇ B) ≡ true
  ss-in   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ invP))))
  slotsOK : slotsSize sl ≤ Caps.cSize c
  slotsOK = ≤ᵇ⇒≤ (slotsSize sl) B (T-to ss-in)

  wet     = subscribeE-wet g b κ id now sched st inv pathB szB fnB gas
  dry     : hasDry (proj₁ r) ≡ false
  dry     = proj₁ wet
  invOut  : INV? (ΨAt e (Sched.slots sched′))
                 (sizeCapAt e (Sched.slots sched′) (suc id))
                 sched′ st′ ≡ true
  invOut  = proj₂ wet

  f0 = frameStep-0 c

  pκSz  : pathSz? (Caps.cSize (frameStep 0 c)) κ ≡ true
  pκSz  = subst (λ x → pathSz? (Caps.cSize x) κ ≡ true) (sym f0) pathSzκ

  pκLen : suc (pathLen κ) ≤ Caps.cSize (frameStep 0 c)
  pκLen = subst (λ x → suc (pathLen κ) ≤ Caps.cSize x) (sym f0) lenκ

  IH = sub-charge c
                  (nest b sl (EvalSt.connectedShares st))
                  (suc (sizeᵉ b))
                  0
                  g b κ id now sl sched st
                  (2≤capsAt-size e sl id)
                  (1≤capsAt-reg e sl id)
                  refl
                  (slotsCaps?-capsAt e sl id)
                  slotsOK
                  (subst (λ x → capsOK? x sched st ≡ true) (sym f0) cOK)
                  (subst (λ x → sizeᵉ b ≤ Caps.cSize x) (sym f0) szB)
                  (subst (λ x → dWᵉ n sl b ≤ Caps.cWid x) (sym f0) dW)
                  pκSz
                  pκLen
                  ≤-refl
                  ≤-refl

  j′      = proj₁ IH
  capOut  = proj₁ (proj₂ IH)
  jBound  = proj₂ (proj₂ (proj₂ (proj₂ IH)))

  capsOut₀ : capsOK? (capsAt e sl (suc id)) sched′ st′ ≡ true
  capsOut₀ = sub-charge-capsOK-lift g b κ id now sched st j′ capOut jBound nestOK opsOK

  capsOut : capsOK? (capsAt e (Sched.slots sched′) (suc id)) sched′ st′ ≡ true
  capsOut = subst (λ x → capsOK? (capsAt e x (suc id)) sched′ st′ ≡ true)
                  (sym sl′Eq) capsOut₀

-- helpers for burst-caps corollary

-- dWᵉ n ins e ≤ Caps.cWid (capsAt e ins 0)
-- Route: dW≤ceil → m≤m⊔n (ceilᵉ ≤ entryCeil) → n≤1+n → capsAt-base-wid
dWe≤cWid : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  dWᵉ n ins e ≤ Caps.cWid (capsAt e ins 0)
dWe≤cWid {n = n} e ins =
  ≤-trans (dW≤ceil n ins e)
  (≤-trans (m≤m⊔n (ceilᵉ n ins e) _)
  (≤-trans (n≤1+n _)
           (capsAt-base-wid e ins 0)))

-- sizeᵉ e ≤ sizeCapAt e ins 0
-- Route: sizeᵉ e ≤ 2+sizeᵉ+slotsSize ≤ cSize (capsAt-base-size)
sizeE≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  sizeᵉ e ≤ sizeCapAt e ins 0
sizeE≤cap e ins =
  ≤-trans (≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize ins)))
          (capsAt-base-size e ins 0)

-- burst-caps: proven corollary of subscribeE-wet-via-caps.
-- pathLen root = 0, so suc (pathLen root) = 1 ≤ B (option 3 from the
-- design brief: moot at the root call).
burst-caps : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in capsOK? (capsAt e ins 1) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-caps {n = n} e ins =
  let r      = subscribeE (budgetAt e ins 0) e root 0 0
                           (sched-init e ins) (st-init e)
      sched₁ = proj₁ (proj₂ r)
      st₁    = proj₂ (proj₂ r)
      sl′    = Sched.slots sched₁
      slEq   : sl′ ≡ ins
      slEq   = subscribeE-slots (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e)
      -- `EvalSt.connectedShares (st-init e) = []` (Evaluator:943)
      -- `Sched.slots (sched-init e ins) = ins` (Evaluator:118)
      -- so the premises reduce to the root bounds at (capsAt e ins 0).
      nestOK : nest e ins [] ≤ Caps.cSize (capsAt e ins 0)
      nestOK = ≤-trans (nest≤ e ins [])
                 (≤-trans (≤-trans (n≤1+n (sizeᵉ e + slotsSize ins))
                                   (s≤s (n≤1+n (sizeᵉ e + slotsSize ins))))
                          (capsAt-base-size e ins 0))
      opsOK  : suc (sizeᵉ e) ≤ Caps.cSize (capsAt e ins 0)
      opsOK  = ≤-trans (s≤s (≤-trans (m≤m+n (sizeᵉ e) (slotsSize ins))
                                     (n≤1+n (sizeᵉ e + slotsSize ins))))
                       (capsAt-base-size e ins 0)
      result = subscribeE-wet-via-caps
                 (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
                 (init-INV e ins 0)
                 refl
                 refl                                    -- pathSz? B root
                 (≤-trans (s≤s z≤n) (2≤capsAt-size e ins 0))  -- 1 ≤ B
                 (sizeE≤cap e ins)
                 (m≤m+n (fnCapᵉ e) _)
                 (caps-fuel-root e ins)
                 (init-capsOK? e ins 0)
                 (dWe≤cWid e ins)
                 nestOK
                 opsOK
      capsOK-out : capsOK? (capsAt e sl′ 1) sched₁ st₁ ≡ true
      capsOK-out = proj₂ (proj₂ result)
  in subst (λ s → capsOK? (capsAt e s 1) sched₁ st₁ ≡ true) slEq capsOK-out

drain-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  INV? (ΨAt e (Sched.slots sched)) (sizeCapAt e (Sched.slots sched) id)
       sched st ≡ true →
  capsOK? (capsAt e (Sched.slots sched) id) sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry zero    id sched st inv cOK = refl
drain-dry (suc k) id sched st inv cOK with sched-next sched in eq
... | inj₁ _            = refl
drain-dry {e = e} (suc k) id sched st inv cOK | inj₂ (a , sched′) =
  let Ψ = ΨAt e (Sched.slots sched)
      B = sizeCapAt e (Sched.slots sched) id
      C = capsAt e (Sched.slots sched) id
      inv′ : INV? (ΨAt e (Sched.slots sched′))
                  (sizeCapAt e (Sched.slots sched′) id) sched′ st ≡ true
      inv′ = subst
               (λ sl → INV? (ΨAt e sl) (sizeCapAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-INV Ψ B sched st eq inv)
      val′ : valB? (sizeCapAt e (Sched.slots sched′) id)
                   (ΨAt e (Sched.slots sched′)) (arrTy a) (arrVal a) ≡ true
      val′ = subst
               (λ sl → valB? (sizeCapAt e sl id) (ΨAt e sl)
                             (arrTy a) (arrVal a) ≡ true)
               (sym (pop-slots sched eq))
               (pop-head-bounded Ψ B sched st eq inv)
      caps′ : capsOK? (capsAt e (Sched.slots sched′) id) sched′ st ≡ true
      caps′ = subst
               (λ sl → capsOK? (capsAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-caps C sched st eq cOK)
      valC′ : valCaps? (capsAt e (Sched.slots sched′) id) (Sched.slots sched′)
                       (arrTy a) (arrVal a) ≡ true
      valC′ = subst
               (λ sl → valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true)
               (sym (pop-slots sched eq))
               (pop-head-valCaps id sched st eq inv cOK)
      (dry₁ , inv″ , caps″) = cascade-wet-via-caps a id sched′ st inv′ val′ caps′ valC′
  in hasDry-append (proj₁ (cascade a id sched′ st)) _
       dry₁
       (drain-dry k (suc id)
         (proj₁ (proj₂ (cascade a id sched′ st)))
         (proj₂ (proj₂ (cascade a id sched′ st)))
         inv″
         caps″)

-- THE THEOREM.  Same face as .Wet's `budget-sufficient` — it does not
-- move.  Only the interior changes: it now also seeds and carries
-- capsOK?, transported from `ins` to the post-burst sched's own slots by
-- subscribeE-slots.
budget-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
budget-sufficient fuel e ins =
  hasDry-append
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)))
    _
    (burst-dry e ins)
    (drain-dry fuel 1 sched₁ st₁ (burst-bounded e ins) caps₁)
  where
  sched₁ = proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                    (sched-init e ins) (st-init e)))
  st₁    = proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                    (sched-init e ins) (st-init e)))
  slEq : Sched.slots sched₁ ≡ ins
  slEq = subscribeE-slots (budgetAt e ins 0) e root 0 0
                          (sched-init e ins) (st-init e)
  caps₁ : capsOK? (capsAt e (Sched.slots sched₁) 1) sched₁ st₁ ≡ true
  caps₁ = subst (λ s → capsOK? (capsAt e s 1) sched₁ st₁ ≡ true)
                (sym slEq)
                (burst-caps e ins)
