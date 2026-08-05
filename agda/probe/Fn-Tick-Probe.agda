-- Probe for S1 `fn-tick` (Caps-Bridge.agda) — the fn-weight face
-- (fnCapBounded?, the Ψ-half of regsB?) preserved across one whole
-- cascade.  Task per WORKER-HANDOFF: replace the postulate with a
-- real proof, or report precisely why not.
--
-- THE ROUTE FOUND, and it is NOT the route the header comment in
-- Caps-Bridge.agda names (a from-scratch walk over
-- stepFrame/pushBurst/subscribeInner/...).  It is instead:
--
--   1. Ψ never needs to grow, so we do NOT need to land the cascade's
--      output within the caps-level fixed bound `sizeCapAt e sl
--      (suc id)` at all — that landing problem is GAP 4 / the
--      cascadeGo-wet fold-threading obstruction, and it is a SIZE-axis
--      problem only.  fn-tick's own conclusion only reads Ψ-indexed
--      predicates (fnCapBounded?, regsBΨ?), so any witness INV? holds
--      AT — regardless of the numeric B/E value — is enough.
--   2. `cascadeGo-walk` (Wet.agda:2145) is already PROVEN: it folds
--      chainStep-wet over the chains list at a GROWING ledger bound
--      capᴱ W E (E′ ≥ E existentially), landing the FULL six-conjunct
--      INV? (Ψ fixed throughout — only the B/E axis grows).  This is
--      exactly the interior-fold lemma cascadeGo-wet (P2) needs for
--      the size face too, but P2 is stuck because relating E′ back to
--      the fixed sizeCapAt(suc id) is refuted.  We never need that
--      relation, so cascadeGo-walk is directly usable here.
--   3. Embed the caps-level input bound B = sizeCapAt e sl id into SOME
--      capᴱ W E (choosing W := B, E := 3) via `pow1` (Measures.agda),
--      widen the input facts (INV?-widen / valB?-widen /
--      chainsB?-widen), run cascadeLatch-INV → cascadeGo-walk →
--      cascadeFinish-INV, then project fnCapBounded? and regsB?'s
--      Ψ-half (regsB?→regsBΨ?, a new one-line reverse of
--      Caps-Bridge's regsB?-of-parts) out of the landed INV?, at
--      WHATEVER numeric bound it landed at.
--   4. The remaining gap: fn-tick's conclusion is stated at Ψ′ = ΨAt e
--      (output slots), not Ψ = ΨAt e (input slots).  These are
--      propositionally equal because `Sched.slots` is never touched by
--      the whole delivery clique (S2 `slots-tick`'s own claim) — but
--      S2 is a SEPARATE postulate we were told not to import.  So this
--      probe proves the slots-invariance fact itself, from pieces that
--      already exist for exactly this reason: `foldPath-slots` /
--      `dispatchShare-slots` / `shareGo-slots` (Caps-Face.agda:3690+,
--      PROVEN, composing `KeepsC.slotsEq` under the hood) cover
--      everything below `chainStep`; `finish-slots` (Measures.agda)
--      covers cascadeFinish.  All that was missing was `chainStep-slots`
--      (one line, chainStep IS a foldPath call) and `cascadeGo-slots`
--      (one small list-fold induction, mirroring cascadeGo-walk's own
--      structure).  Both are proven below.  (This is, incidentally,
--      almost the entire content of S2 `slots-tick` too — worth
--      flagging to the design session as a near-free discharge.)
--
-- RESULT: fn-tick is proven below, no postulates, and it does NOT need
-- the from-scratch stepFrame/pushBurst/subscribeInner/... walk the
-- Caps-Bridge header comment anticipated — cascadeGo-walk (already
-- proven for the WHOLE six-conjunct INV?, Ψ held fixed throughout)
-- already contains it.
module Fn-Tick-Probe where

open import Data.Bool    using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; _≡ᵇ_;
                                _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤n+m)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; all; any; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Gas; Tick; Id; Source; InstEvent; close; exhausted)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; sizeᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; RegId; Chain;
                                Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                arrTy; arrVal; arrTick; arrSource;
                                cascade; cascadeGo; cascadeLatch; cascadeFinish;
                                chainStep; foldPath; chainsOf;
                                hasDry; subscribeE; budgetAt; slotsSize)

-- the whole wet family (INV?, ΨAt, sizeCapAt, valB?, fnCapBounded?,
-- regsB?, slotsFnCap, INV-parts, pathLen, capᴱ/capᴱ-mono/pow1,
-- INV?-widen, chainsOf-B, chainsB?-widen, valB?-widen, cascadeLatch-INV,
-- cascadeFinish-INV, cascadeGo-walk, finish-slots, the Bool toolkit
-- ∧-true/∧-intro/all-impl/≤ᵇ-widen/T-to/T⇒≡true) via the public chain
-- Wet → Caps → Keeps-Ring → Measures
open import Verify-Budget-Sufficient.Wet

-- the caps face / subscribe clique, needed for `foldPath-slots` (the
-- slots-invariance corollary chainStep-slots/cascadeGo-slots below
-- build on) via the public chain Subscribe-Face → Caps-Face →
-- {Delivery-Walk, Caps-Nest}
open import Verify-Budget-Sufficient.Subscribe-Face

------------------------------------------------------------------
-- THE Ψ-ONLY HALVES — copied verbatim from Caps-Bridge.agda (S1's own
-- header names them as the shape fn-tick must deliver).  Not imported
-- (Caps-Bridge holds the postulate this probe replaces).
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
-- THE REVERSE PROJECTIONS — Caps-Bridge already has frameB?-of-parts /
-- pathB?-of-parts / regsB?-of-parts (combining a size-only half and a
-- Ψ-only half INTO frameB?/pathB?/regsB?).  fn-tick needs the other
-- direction: pulling the Ψ-only half back OUT of an already-landed
-- frameB?/pathB?/regsB?.  One line per clause, mirroring frameB?-widen
-- / pathB?-widen / regsB?-widen's own structure (Measures.agda:5468+).
------------------------------------------------------------------

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

------------------------------------------------------------------
-- EMBEDDING A FIXED BOUND B INTO capᴱ FORM.  Any B fits under
-- capᴱ B 3 = (2 + 2·B) ^ 3: B ≤ 2 + 2·B ≤ (2 + 2·B) ^ 3, the second
-- step by `pow1` (Measures.agda:3939, already proven).
------------------------------------------------------------------

2+b+b≡2+2b : ∀ b → (2 + b) + b ≡ 2 + 2 * b
2+b+b≡2+2b = solve 1 (λ b → (con 2 :+ b) :+ b := con 2 :+ (con 2 :* b)) refl

b≤2+2b : ∀ b → b ≤ 2 + 2 * b
b≤2+2b b = ≤-trans (m≤n+m b (2 + b)) (≤-reflexive (2+b+b≡2+2b b))

b≤capᴱ-b-3 : ∀ b → b ≤ capᴱ b 3
b≤capᴱ-b-3 b = ≤-trans (b≤2+2b b) (pow1 b {3} (s≤s z≤n))

------------------------------------------------------------------
-- THE SLOTS-INVARIANCE COROLLARIES fn-tick needs (Ψ′ ≡ Ψ, since Ψ is
-- read off `Sched.slots` and slots are untouched by a whole cascade).
-- `foldPath-slots`/`dispatchShare-slots`/`shareGo-slots`
-- (Caps-Face.agda:3690+) already cover everything chainStep calls
-- into; `finish-slots` (Measures.agda) already covers cascadeFinish.
-- Only the two links in between — chainStep itself (a direct foldPath
-- call) and cascadeGo's own fold over chains — were missing, and both
-- are one-line-per-clause given those.  (This is nearly all of S2
-- `slots-tick`'s own content too — see the report.)
------------------------------------------------------------------

chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st)))
    ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id
                 (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ []
                  else [])
                 (Arrival.isLast a) sched st

cascadeGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascadeGo a id chains sched st)))
    ≡ Sched.slots sched
cascadeGo-slots a id []                   sched st = refl
cascadeGo-slots a id ((rid , c) ∷ chains) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-slots a id chains sched st
... | false =
  trans (cascadeGo-slots a id chains sched₁ st₁)
        (chainStep-slots id a c sched st₀)
  where
  st₀    = record st { delivered = rid ∷ EvalSt.delivered st }
  sched₁ = proj₁ (proj₂ (chainStep id a c sched st₀))
  st₁    = proj₂ (proj₂ (chainStep id a c sched st₀))

cascade-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascade a id sched st))) ≡ Sched.slots sched
cascade-slots a id sched st =
  trans (finish-slots a sched′ st′)
        (cascadeGo-slots a id (chainsOf a st) sched (cascadeLatch a st))
  where
  sched′ = proj₁ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  st′    = proj₂ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))

------------------------------------------------------------------
-- fn-tick ITSELF.  Signature copied verbatim from Caps-Bridge.agda.
------------------------------------------------------------------

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
  slotsEq = cascade-slots a id sched st

  Ψ′≡Ψ : ΨAt e (Sched.slots sched″) ≡ Ψ
  Ψ′≡Ψ = cong (ΨAt e) slotsEq
