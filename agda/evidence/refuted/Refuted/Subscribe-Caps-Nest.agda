-- ══════════════════════════════════════════════════════════════════
-- THE CAPS PREMISE SAYS NOTHING ABOUT THE THING BEING SUBSCRIBED, so
-- charging the descent `2 ^ cSize` is FALSE, and unboundedly so.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A subscription of `o` under a path deepens
-- what it emits and what it installs by at most `2 ^ cSize` times the
-- depth it was handed, where `cSize` comes from a `capsOK? c` on the
-- SCHEDULER AND STORE it starts from.  The factor reads as generous:
-- `capsOK?` is the bundle that bounds sizes, and two to a size cap is
-- the ceiling on how many times a step function can name its payload.
--
-- WHERE IT BREAKS.  `capsOK?` constrains the STATE -- node sizes,
-- registry widths, the slots -- and `o` is in NEITHER.  At a state the
-- evaluator genuinely reaches, `st-init`, the node table is empty, so
-- `capsOK? (caps 0 0 0)` holds outright and the factor is `2 ^ 0`.  The
-- descent is then charged the incoming depth and nothing else, while a
-- stack of `mapᵉ` frames each naming its payload twice DOUBLES per
-- layer: four, eight, sixteen against a charge that stays at six.  The
-- gap is a factor of two per stacked frame, so no constant, no summand
-- and no larger `B` repairs it.
--
-- WHAT DIES AND WHAT DOES NOT.  Nothing here says the descent is
-- unbounded -- `applyFn-nest` bounds ONE substitution at two to the
-- SUBSTITUTED FUNCTION'S size, and the layers above compose their own
-- sizes.  What dies is taking the exponent from the STORE's cap: the
-- quantity that has to be in it is the size of `o`, which the statement
-- never mentions.  The repair is a premise tying `o` to the cap, and the
-- consumer that must supply it is the drain -- which reads its queue out
-- of a node table `capsOK?` really does bound.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Caps-Nest where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; switchAllᵉ; varᵗ; nat̂; strmᵗ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Refuted.Demand-Programs using (Γ₂; insT)

----------------------------------------------------------------------
-- THE WITNESS.  A stack of `mapᵉ` frames, each naming its payload on
-- both sides of the sum, subscribed at `root` from the state the
-- evaluator actually starts in.  The stack is a free parameter: every
-- layer doubles the emitted depth and leaves the charge alone.
----------------------------------------------------------------------

slots : Slots Γ₂
slots = insT 0 0 0

gas : Gas
gas = gs (gs (gs (gs (gs (gs g0)))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

dup₁ : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dup₁ = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

dup₂ : Fn Γ₂ [] [] [] (obs (obs natᵗ)) (obs (obs (obs natᵗ)))
dup₂ = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

dup₃ : Fn Γ₂ [] [] [] (obs (obs (obs natᵗ))) (obs (obs (obs (obs natᵗ))))
dup₃ = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

p₁ : Closed Γ₂ (obs (obs natᵗ))
p₁ = mapᵉ dup₁ (ofᵉ (strmᵗ (deepV 2) ∷ []))

p₂ : Closed Γ₂ (obs (obs (obs natᵗ)))
p₂ = mapᵉ dup₂ p₁

p₃ : Closed Γ₂ (obs (obs (obs (obs natᵗ))))
p₃ = mapᵉ dup₃ p₂

-- the cap the premise really demands, and it is nothing: an empty node
-- table satisfies `capsOK?` at every cap, zero included
c₀ : Caps
c₀ = caps 0 0 0

capsZero : capsOK? c₀ (sched-init p₃ slots) (st-init p₃) ≡ true
capsZero = refl

capsZero₂ : capsOK? c₀ (sched-init p₂ slots) (st-init p₂) ≡ true
capsZero₂ = refl

read : ∀ {t} (e : Closed Γ₂ t) → ℕ × ℕ
read {t} e =
  let r = subscribeE gas e root 0 0 (sched-init e slots) (st-init e)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ t} (proj₁ r)))
   , 2 ^ Caps.cSize c₀ * (nestDᵉ e + nestUnit e slots)

row₃ : ℕ × ℕ
row₃ = read p₃

row₂ : ℕ × ℕ
row₂ = read p₂

-- THE FIGURES, PINNED.  The charge is the same six at both stack
-- heights, so the two rows together are the unboundedness and not one
-- crossing that a bigger constant would close.
delivered≡16 : proj₁ row₃ ≡ 16
delivered≡16 = refl

charged≡6 : proj₂ row₃ ≡ 6
charged≡6 = refl

delivered₂≡8 : proj₁ row₂ ≡ 8
delivered₂≡8 = refl

charged₂≡6 : proj₂ row₂ ≡ 6
charged₂≡6 = refl

subscribeE-nest-absurd : proj₁ row₃ ≤ proj₂ row₃ → ⊥
subscribeE-nest-absurd h = ≤⇒≤ᵇ h

subscribeE-nest-two-absurd : proj₁ row₂ ≤ proj₂ row₂ → ⊥
subscribeE-nest-two-absurd h = ≤⇒≤ᵇ h

-- AND THE REPAIR IS LOAD-BEARING, not incidental to the witness.  A
-- premise tying the subscribed observable to the cap -- the caps face's
-- own `valCaps?` -- is FALSE at exactly the two programs above, so the
-- rows stop being instances of the restated form rather than surviving
-- it under a different reading.
valCapsFails₃ : valCaps? c₀ slots (obs (obs (obs (obs (obs natᵗ))))) p₃ ≡ false
valCapsFails₃ = refl

valCapsFails₂ : valCaps? c₀ slots (obs (obs (obs (obs natᵗ)))) p₂ ≡ false
valCapsFails₂ = refl
