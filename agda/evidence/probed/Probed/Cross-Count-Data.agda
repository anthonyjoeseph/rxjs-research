-- ══════════════════════════════════════════════════════════════════
-- THE CROSSING'S COUNT, FORKED A SECOND TIME: the arrival's SIZE
-- against the arrival's OPERATORS.  The first fork chose the size over
-- a constant and displaced the cost onto the ceiling; the ceiling is
-- since refuted at every advance rule from a join to a sum, so the
-- displacement has nowhere left to go and the count itself is what
-- must move.  This file stands at that choice.

-- WHY THE SIZE IS THE WRONG CURRENCY, AND IT IS A PROPERTY OF THE WALK
-- RATHER THAN OF THE ARM.  A crossing charges rungs because running an
-- arrival can grow what it emits, and growth is per OPERATOR LAYER --
-- each substitution multiplies, so a k-layer chain emits at two to the
-- k and k rungs pay for it.  But the walk does not manufacture layers:
-- a frame applies a closed function, so a crossing arrival's operators
-- grow by the program's own syntax per frame and no faster.  What the
-- walk multiplies is the arrival's DATA, and data emits itself.  So a
-- count read off `sizeᵉ` reads the one part of an arrival the ladder
-- inflates and the subscription does not spend.

-- THE TWO CANDIDATES.  `ownV` is the count as it stands, the arrival's
-- own `sizeᵛ`.  `opsV` charges the operator spine only: a map or a scan
-- costs its function's syntax, a `*All` layer one, a defer nothing, and
-- everything that carries a payload -- a pair, a burst, a list of
-- terms -- takes the MAX of its parts rather than the sum, because two
-- payloads abreast are entered separately from the same frame.  That
-- max is the whole of the difference, and it is the same clause shape
-- `nestDᵛ` already carries for the depth face, charging a function's
-- size where that measure charges its nesting.

-- FORK: stepFrame-sz-outer

-- WHY THE ANSWER IS NOT KNOWN FROM THE FIRST FORK.  That file's second
-- shape -- a reified arrival -- is recorded there as degenerate,
-- because no count can lose where the subscription computes nothing.
-- Degenerate for a LOWER bound is not degenerate for an UPPER one: the
-- question here is whether a count can be small at that shape and still
-- cover it, and the margin is two nodes wide, so the row could have
-- failed and a count reading anything of the payload would have.

-- THE ROWS.  At the reified arrival the two part by four thousand and
-- ninety-seven against nothing, and the emission still fits with zero
-- rungs bought -- which is what says the size was paying for a run that
-- never happens.  At the duplication chain, the shape whose emission is
-- genuinely exponential and where the constant charge dies, the
-- operator count is thirty-six where the size is fifty-one and the
-- emission clears both, so the reading that separates at the first
-- shape does not collapse into the refuted constant at the second.

-- WHAT THE ROWS DO NOT BUY.  Nothing about the `from-inner` arm, which
-- reaches its program through the store and cannot read an operator
-- spine it is not handed; nothing about either store half; nothing
-- about an arrival naming a shared slot, where the telescope summand is
-- what pays and both candidates here read the slot as one node
-- (`Refuted.Frame-Step-Size-Slot`); and nothing about a scan inside an
-- arrival, whose growth is per ELEMENT, so the operator reading owes a
-- width there that these two shapes never exercise.  Nor is a green
-- here a claim that the walk cannot inflate the operator spine -- that
-- is the property the repair turns on and it is not instantiated by any
-- row below.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Data where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Ty; Exp; Tm; Val; obs; unitᵗ; boolᵗ; natᵗ;
  _×ᵗ_; _+ᵗ_; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
  inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; sizeᵗ; sizeᵛ)
open import Rx.Evaluator using (iterSize)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Refuted.Frame-Step-Size-Cross using (Γ₁; Pow; chain)
open import Probed.Cross-Count-Fork using (bigObs; out₂; out₃)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE OPERATOR SPINE.  Every clause that carries a payload joins by
-- `⊔`; every clause that runs one charges the closed syntax it runs.
----------------------------------------------------------------------
mutual
  opsᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  opsᵉ (input i)         = 0
  opsᵉ (ofᵉ ts)          = opsᵗˢ ts
  opsᵉ emptyᵉ            = 0
  opsᵉ (mapᵉ f e)        = sizeᵗ f + opsᵉ e
  opsᵉ (takeᵉ c e)       = opsᵉ e
  opsᵉ (scanᵉ f z e)     = sizeᵗ z + sizeᵗ f + opsᵉ e
  opsᵉ (mergeAllᵉ lim e) = suc (opsᵉ e)
  opsᵉ (switchAllᵉ e)    = suc (opsᵉ e)
  opsᵉ (exhaustAllᵉ e)   = suc (opsᵉ e)
  opsᵉ (μᵉ e)            = opsᵉ e
  opsᵉ (varᵉ x)          = 0
  opsᵉ (deferᵉ e)        = 0

  opsᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  opsᵗ (varᵗ x)      = 0
  opsᵗ unit̂          = 0
  opsᵗ (bool̂ _)      = 0
  opsᵗ (nat̂ _)       = 0
  opsᵗ (pairᵗ a b)   = opsᵗ a ⊔ opsᵗ b
  opsᵗ (fstᵗ p)      = opsᵗ p
  opsᵗ (sndᵗ p)      = opsᵗ p
  opsᵗ (inlᵗ a)      = opsᵗ a
  opsᵗ (inrᵗ a)      = opsᵗ a
  opsᵗ (caseᵗ s l r) = opsᵗ s ⊔ (opsᵗ l ⊔ opsᵗ r)
  opsᵗ (ifᵗ c a b)   = opsᵗ c ⊔ opsᵗ a ⊔ opsᵗ b
  opsᵗ (primᵗ _ a)   = opsᵗ a
  opsᵗ (strmᵗ e)     = opsᵉ e

  opsᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  opsᵗˢ []       = 0
  opsᵗˢ (y ∷ ys) = opsᵗ y ⊔ opsᵗˢ ys

opsᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
opsᵛ unitᵗ    _        = 0
opsᵛ boolᵗ    _        = 0
opsᵛ natᵗ     _        = 0
opsᵛ (s ×ᵗ t) (a , b)  = opsᵛ s a ⊔ opsᵛ t b
opsᵛ (s +ᵗ t) (inj₁ a) = opsᵛ s a
opsᵛ (s +ᵗ t) (inj₂ b) = opsᵛ t b
opsᵛ (obs t)  e        = opsᵉ e

----------------------------------------------------------------------
-- THE TWO CANDIDATES AT ONE SIGNATURE, so the disagreement is a value.
-- The argument is the arriving observable itself, which is what the
-- frame is handed and what a count of it may read.
----------------------------------------------------------------------
ownV : Val Γ₁ (obs (Pow 11)) → ℕ
ownV v = sizeᵛ (obs (Pow 11)) v

opsV : Val Γ₁ (obs (Pow 11)) → ℕ
opsV v = opsᵛ (obs (Pow 11)) v

-- LOAD-BEARING, and it is this file's product: the two part at the
-- arrival the walk's own ladder manufactures.  `apart` cannot be
-- written where they agree.
separates : Separates ownV opsV
separates = separates-at bigObs (λ ())

----------------------------------------------------------------------
-- SHAPE ONE — THE REIFIED ARRIVAL, where the subscription computes
-- nothing and the size charges four thousand rungs for it.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the gap itself, and it is what a count blind to
-- the data/operator split cannot report.  Any reading that descends
-- into the payload loses this row.
charges₃ : ℕ
charges₃ = ownV bigObs + 10000 * opsV bigObs

charges₃≡ : charges₃ ≡ 4097
charges₃≡ = refl

-- LOAD-BEARING, and the margin is two nodes: `iterSize` at zero rungs
-- is the base untouched, so the emission has to fit under the arrival's
-- own size with nothing bought.  It fails for an emission one pair
-- wider, and for every count that reads the payload it is not even
-- reached.
opsRow₃ : valsSz? {Γ = Γ₁} {s = Pow 11}
            (iterSize 60 (opsV bigObs) 4097) out₃ ≡ true
opsRow₃ = refl

----------------------------------------------------------------------
-- SHAPE TWO — THE DUPLICATION CHAIN, where the emission is genuinely
-- exponential and one rung is refuted.  The operator count is below
-- the size and above the constant.
----------------------------------------------------------------------
opsChain : ℕ
opsChain = opsᵛ (obs (Pow 12)) (chain 12)

-- LOAD-BEARING jointly with the row below: it says the operator
-- reading has not collapsed into the refuted constant along the axis
-- the emission grows on -- it moves by three per rung of the chain
-- while the constant does not move at all.
opsChain≡ : opsChain ≡ 36
opsChain≡ = refl

-- LOAD-BEARING: eight thousand one hundred and ninety-one against a
-- cap of fifty-one, at the count beside it.  One rung loses here, which
-- is the row `Refuted.Frame-Step-Size-Cross` already owns.
opsRow₂ : valsSz? {Γ = Γ₁} {s = Pow 12}
            (iterSize 51 opsChain 51) out₂ ≡ true
opsRow₂ = refl
