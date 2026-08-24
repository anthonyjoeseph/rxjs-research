-- ══════════════════════════════════════════════════════════════════
-- THE *All OUTER WALK'S LOOP INVARIANT, as stated, is FALSE.
--
-- REFUTATION: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT IS WRONG.  `thruConsume-nodry-loop` claims `OKB c sl Ψ J` is
-- preserved across ONE `thruConsume` step, at the SAME J on both sides.
-- But mergeAll's park clause is a pure growth step: with every lane of
-- the node's limit already spent it appends the element to the queue
-- (`mergeAll-st lim act (q ++ o ∷ []) od`) and emits nothing — which is
-- exactly why the *nodry* conclusion is `refl` there, and why nothing
-- else in that block notices.  Meanwhile `capsOK?`'s width conjunct
-- bounds that queue's LENGTH: `widNode W sl (mergeAll-st _ _ q _)` carries
-- `length q ≤ᵇ W`.  So a queue sitting AT the width cap — which the
-- hypothesis permits, since `length q ≤ᵇ W` is all it says — is one park
-- away from breaching it, and no hypothesis forbids that state.
--
-- THIS IS NOT A ZERO-CAP ARTIFACT, and the witness is built to make that
-- unarguable: the caps are read off the value itself (`cSize = sizeᵉ eₚ`,
-- `cWid = suc (pWᵉ … eₚ)`), so every OTHER conjunct holds with room to
-- spare and the queue is a legitimate `replicate cWid` — the honest
-- worst case, not a degenerate one.  No numeral is needed anywhere and no
-- measure has to reduce; only `frameStep-0` is spent, to read the entry
-- level's cWid back off `cₚ`.
--
-- CLAUDE.md's first almost-always-wrong shape again: the conclusion needs
-- `suc (length q) ≤ cWid`, and NO hypothesis mentions the queue at all.
--
-- WHICH REPAIR — and this one is not a hypothesis.  Caps-Face.Part1's own
-- header says what the design intends: "One level of width pays for one
-- cons, with the same `suc w ≤ foldStep S w` margin the count receipts
-- already spend."  A cons is therefore a LEVEL step, so the honest
-- conclusion reports a `j′` and re-establishes OKB at `J + j′` — the
-- same shape `stepFrame-face` already uses for every other growth step,
-- and the same conclusion `Refuted.Caps-Face.caps-frame-boundary-absurd`
-- forced on the caps face for the fold.  Conditioning on the queue
-- instead would be the "call site happens to supply it" trade CLAUDE.md
-- forbids: the outer walk's SECOND element cannot supply it, because the
-- first element is what filled the queue.
--
-- IT WAS CLASSED GRINDABLE on the grounds that it is "pure preservation,
-- hypothesis P at state₀ and conclusion P at state₁".  That reading is
-- the trap: a preservation statement is only cheap when the step cannot
-- grow the thing being preserved, and this step exists precisely to grow
-- it.  Shape-checking a statement against `hypothesis ⇒ conclusion` says
-- nothing about the STEP in between.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Loop where

open import Data.Bool using (true; false)
open import Data.Nat  using (ℕ; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (just)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; Gas; g0)
open import Rx.Exp  using (Ctx; Closed; Val; obs; natᵗ; ofᵉ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; mergeAll-st;
                               AllOp; mergeAllᵒ; Path; root;
                               sched-init; st-init; thruConsume)
open import Rx.Frame-Width using (pWᵉ)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Measures using (fnCapᵉ)
open import Verify-Budget-Sufficient.Delivery-Walk using (regP?)
open import Verify-Budget-Sufficient.Burst-Walk using (OKB; PbB)

false≢true : false ≡ true → ⊥
false≢true ()

----------------------------------------------------------------------
-- THE WITNESS — named with a `ₚ` (park) suffix rather than the `₀` this
-- tree's other witnesses use, DELIBERATELY: two files defining `c₀` and
-- `e₀` merge into one node in the wiring checker's name-keyed index, and
-- the collision silently unwires a sibling refutation's helper.
--
-- The empty context, so the schedule and the registry are
-- empty and every conjunct about them is vacuous; ONE mergeAll node with
-- every lane of its limit spent, holding a queue exactly as long as the
-- width cap.
--
-- The caps are read off `eₚ` rather than chosen: `cSize` is the value's
-- own size and `cWid` is one past its own width, so every per-element
-- conjunct holds with a margin and the ONLY tight one is the queue's
-- LENGTH — which is the one the park breaks.  `cReg` is 0 because the
-- registry is empty and stays empty; this clause never registers.
----------------------------------------------------------------------

Γₚ : Ctx 0
Γₚ = []ⱽ

slₚ : Slots Γₚ
slₚ = λ ()

eₚ : Closed Γₚ natᵗ
eₚ = ofᵉ (nat̂ 1 ∷ [])

Wₚ : ℕ
Wₚ = suc (pWᵉ 0 slₚ eₚ)

cₚ : Caps
cₚ = caps (sizeᵉ eₚ) Wₚ 0

-- pinned, because "the cap is 0" would make this a degenerate-zero
-- refutation and not a real one: the width cap is 2, and the queue holds
-- exactly 2, and the size cap (3) has room to spare
_ : Caps.cWid cₚ ≡ 2
_ = refl

_ : Caps.cSize cₚ ≡ 3
_ = refl

qₚ : List (Closed Γₚ natᵗ)
qₚ = replicate Wₚ eₚ

schedₚ : Sched Γₚ
schedₚ = sched-init eₚ slₚ

stₚ : EvalSt eₚ
stₚ = record (st-init eₚ) { nodes = (0 , mergeAll-st {t = natᵗ} (just 1) 1 qₚ false) ∷ [] }

-- every conjunct at the entry level, by computation
okbₚ : OKB {e = eₚ} cₚ slₚ (fnCapᵉ eₚ) 0 schedₚ stₚ
okbₚ = (refl , refl) , refl

----------------------------------------------------------------------
-- THE DEFECT.  One park makes the queue one longer than the cap the
-- conclusion is still measured against, so its `capsOK?` computes to
-- `false` while the statement demands `true`.
----------------------------------------------------------------------

thruConsume-nodry-loop-absurd :
  (∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
     (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sf : Gas)
     (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
     (id : Id) (now : Tick) (o : Val Γ (obs u))
     (sched : Sched Γ) (st : EvalSt e) →
     OKB {e = e} c sl Ψ J sched st →
     regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
     let r      = thruConsume sf op nid κ id now o sched st
         sched₁ = proj₁ (proj₂ (proj₂ r))
         st₁    = proj₂ (proj₂ (proj₂ r))
     in OKB {e = e} c sl Ψ J sched₁ st₁
        × regP? (PbB c Ψ J) (EvalSt.registry st₁) ≡ true)
  → ⊥
thruConsume-nodry-loop-absurd lp =
  false≢true (proj₂ (proj₁ (proj₁
    (lp {u = natᵗ} {e = eₚ} cₚ slₚ (fnCapᵉ eₚ) 0 g0 mergeAllᵒ 0 root 0 0 eₚ
        schedₚ stₚ okbₚ refl))))
