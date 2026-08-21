-- ══════════════════════════════════════════════════════════════════
-- THE INNER-NODRY INV? ASSEMBLY, as stated, is FALSE.
--
-- REFUTATION: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT IS WRONG.  `subscribeE-inner-nodry-inv` claims INV? at the inner
-- frame's level from `OKB` plus a registry path ledger plus the two slot
-- bounds.  INV?'s THIRD conjunct is the registry CARDINALITY against the
-- size cap — `length (EvalSt.registry st) ≤ᵇ cSize (frameStep J c)` —
-- and the only hypothesis that mentions that length is capsOK?'s own
-- last conjunct, which bounds it against `cReg (frameStep J c)`.  The
-- two caps dimensions are INDEPENDENT: nothing in the statement orders
-- cReg below cSize, so a caps whose registration cap exceeds its size
-- cap satisfies every hypothesis and breaks the conclusion.
--
-- CLAUDE.md's first almost-always-wrong shape, again: the conclusion
-- needs `cReg (frameStep J c) ≤ cSize (frameStep J c)` and NO hypothesis
-- mentions cReg and cSize together.
--
-- THIS IS NOT A DEGENERATE-ZERO ARTIFACT.  The caps are read off the
-- witness value (`cSize = sizeᵉ eᵣ`, `cWid = suc (pWᵉ … eᵣ)`), so every
-- other conjunct holds with margin; the registry holds four entries
-- against a registration cap of exactly four, which is the honest
-- boundary the hypothesis permits, and the size cap is three.  Every
-- registered chain is `root`, so the path ledgers are vacuously true and
-- the ONLY thing that fails is the count.
--
-- WHICH REPAIR — and it is the ladder's own side condition, not a new
-- fact.  `frameStep-reg≤size` (.Caps) delivers exactly
-- `cReg (frameStep j c) ≤ cSize (frameStep j c)` from `1 ≤ cSize c` and
-- `cReg c ≤ cSize c`, both of which the consumer
-- (`subscribeE-inner-nodry-core`) carries as `2≤S` and `hCR` and threads
-- at every level of this stack.  So the repair is to premise the derived
-- form at the level the conclusion is stated at, which is what the
-- restated postulate does.
--
-- IT WAS CLASSED GRINDABLE on the grounds that "every conjunct now has a
-- named source IN SCOPE", and `frameStep-reg≤size` was one of the names.
-- That reading is the trap: a lemma being PROVEN and in scope says
-- nothing about its own hypotheses being available where it is applied.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Inner-Nodry where

open import Data.Bool using (true; false)
open import Data.Nat  using (ℕ; suc; _≤_; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp  using (Ctx; Closed; natᵗ; ofᵉ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Prim using (Source)
open import Rx.Evaluator using (Sched; EvalSt; RegId; Chain; root;
                               sched-init; st-init)
open import Rx.Frame-Width using (pWᵉ)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Measures using (fnCapᵉ; slotsFnCap; INV?)
open import Verify-Budget-Sufficient.Delivery-Walk using (regP?)
open import Verify-Budget-Sufficient.Burst-Walk using (OKB; PbB)

false≢true : false ≡ true → ⊥
false≢true ()

----------------------------------------------------------------------
-- THE WITNESS.  The empty context, so both slot bounds are `z≤n` and
-- every conjunct about the slot store is vacuous; the registry holds
-- four `root` chains, so every PATH ledger over it is `true` and only
-- the COUNT is in play.  The `ᵣ` suffix (registry) rather than this
-- tree's `₀`: two files defining `c₀` merge into one node in the wiring
-- checker's name-keyed index.
----------------------------------------------------------------------

Γᵣ : Ctx 0
Γᵣ = []ⱽ

slᵣ : Slots Γᵣ
slᵣ = λ ()

eᵣ : Closed Γᵣ natᵗ
eᵣ = ofᵉ (nat̂ 1 ∷ [])

-- cSize and cWid are read off the value; cReg is set to the registry's
-- own length, which is the boundary capsOK? permits and the conclusion
-- does not
cᵣ : Caps
cᵣ = caps (sizeᵉ eᵣ) (suc (pWᵉ 0 slᵣ eᵣ)) 4

-- pinned, because "the cap is 0" would make this degenerate: the size
-- cap is 3, the registration cap is 4, and the registry holds 4
_ : Caps.cSize cᵣ ≡ 3
_ = refl

_ : Caps.cReg cᵣ ≡ 4
_ = refl

regᵣ : List (RegId × Source × Chain Γᵣ natᵗ)
regᵣ = (0 , 0 , natᵗ , root)
     ∷ (1 , 0 , natᵗ , root)
     ∷ (2 , 0 , natᵗ , root)
     ∷ (3 , 0 , natᵗ , root)
     ∷ []

schedᵣ : Sched Γᵣ
schedᵣ = sched-init eᵣ slᵣ

stᵣ : EvalSt eᵣ
stᵣ = record (st-init eᵣ) { registry = regᵣ }

-- every hypothesis at the entry level, by computation
okbᵣ : OKB {e = eᵣ} cᵣ slᵣ (fnCapᵉ eᵣ) 0 schedᵣ stᵣ
okbᵣ = (refl , refl) , refl

slSzᵣ : slotsSize slᵣ ≤ Caps.cSize cᵣ
slSzᵣ = z≤n

slFcᵣ : slotsFnCap slᵣ ≤ fnCapᵉ eᵣ
slFcᵣ = z≤n

----------------------------------------------------------------------
-- THE DEFECT.  Four registered chains under a registration cap of four
-- and a size cap of three: capsOK? computes to `true` and INV?'s
-- cardinality conjunct to `false`.
----------------------------------------------------------------------

inner-nodry-inv-regLen-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sched : Sched Γ) (st : EvalSt e) →
     slotsSize sl ≤ Caps.cSize c →
     slotsFnCap sl ≤ Ψ →
     OKB {e = e} c sl Ψ J sched st →
     regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
     INV? Ψ (Caps.cSize (frameStep J c)) sched st ≡ true)
  → ⊥
inner-nodry-inv-regLen-absurd h =
  false≢true (h {e = eᵣ} cᵣ slᵣ (fnCapᵉ eᵣ) 0 schedᵣ stᵣ slSzᵣ slFcᵣ okbᵣ refl)
