-- THE SEGMENT CLAIMS, INSTANTIATED AT A STATE A RUN ACTUALLY ENTERS.
-- `Sound` quantifies over every sane state at or below its entry
-- watermark, so at first reading it is not a computation at all.  It
-- becomes one the moment the probe CHOOSES the state: the quantifier is
-- applied at `protocol-init`, whose sanity is proven and whose watermark
-- is the least there is, and what is left is the automaton's run over a
-- concrete burst, which reduces.
--
-- WHAT THAT COVERS AND WHAT IT DOES NOT.  The rows below reach the
-- initial state and the segment that opens there, which is the one
-- segment of every run whose entry state is not a choice.  They do not
-- reach a mid-run state, where the watermark has advanced and the
-- freshness comparison is the thing that could reject an otherwise
-- impeccable segment -- that is the region the exit index was introduced
-- for, and covering it needs a reached state rather than a written one.
module Probed.Protocol-Segments where

open import Data.Fin using (zero)
open import Data.List using (_∷_; [])
open import Data.Maybe using (from-just)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₂)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (after_,_; hot)
open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; ofᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (root; sched-init; st-init; sched-next; Arrival;
  Sched; EvalSt; Stream)
open import Rx.Evaluator.Domain using (cascade⇓)
open import Rx.Evaluator.Builder using (subscribeE!; cascade!)
open import Rx.Protocol using (protocol-init; runProtocol)
open import Rx.Protocol.Sound using (Sound; Sane-init)
open import Readme-Theorems using (noSlots)
open import Verify-Well-Formed using (sound-subscribe; sound-cascade)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- two values from one synchronous source: the whole emission lands in
-- the subscribe burst, so the segment under test is the burst itself
pair₀ : Closed Γ₀ natᵗ
pair₀ = ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])

-- TARGET: sound-subscribe @754ca7
row-subscribe :
  Confirms (Sound.run
             (sound-subscribe pair₀ noSlots
               (proj₂ (subscribeE! noSlots pair₀ root 0 0
                        (sched-init pair₀ noSlots) refl (st-init pair₀))))
             protocol-init Sane-init z≤n)
row-subscribe = _ , refl , (λ i o _ → z≤n) , z≤n

-- ONE HOT SLOT, SO THE RUN HAS A DRAIN AT ALL.  `ofᵉ` empties itself
-- into the subscribe burst, which is why the row above reaches no
-- cascade: a scripted arrival is what puts an instant after the seed.
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ []

ins₁ : Slots Γ₁
ins₁ zero = scripted (hot ((after 1 , 5) ∷ []))

prog₁ : Closed Γ₁ natᵗ
prog₁ = input zero

sub₁ = subscribeE! ins₁ prog₁ (root {lo = 1}) 0 0 (sched-init prog₁ ins₁) refl
         (st-init prog₁)

sched₀ : Sched Γ₁
sched₀ = proj₁ (proj₂ (proj₁ sub₁))

st₀ : EvalSt prog₁
st₀ = proj₂ (proj₂ (proj₁ sub₁))

-- THE ENTRY STATE IS THE ONE THE SUBSCRIBE LEFT, NOT ONE WRITTEN DOWN.
-- A hand-built state is the probe lie this rule exists for: the row
-- would be evidence about a configuration no run reaches.
ps₁ = from-just (runProtocol protocol-init (proj₁ (proj₁ sub₁)))

-- The arrival and the schedule after it are READ OFF the scheduler by
-- an equation that holds at this program by computation, so the point
-- is reached rather than asserted.
record CascPoint : Set where
  constructor casc-at
  field
    {arr}  : Arrival Γ₁
    {rest} : Sched Γ₁
    {res}  : Stream Γ₁ natᵗ × Sched Γ₁ × EvalSt prog₁
    deriv  : cascade⇓ {e = prog₁} arr 1 rest st₀ res

point₁ : ∀ {a sc} → sched-next sched₀ ≡ inj₂ (a , sc) → CascPoint
point₁ {a} {sc} _ = casc-at (proj₂ (cascade! a 1 sc st₀))

-- TARGET: sound-cascade @a03ad3
row-cascade :
  Confirms (Sound.run (sound-cascade (CascPoint.deriv (point₁ refl)))
             ps₁ (λ i o _ → z≤n) z≤n)
row-cascade = _ , refl , (λ { i o refl → s≤s z≤n }) , s≤s z≤n
