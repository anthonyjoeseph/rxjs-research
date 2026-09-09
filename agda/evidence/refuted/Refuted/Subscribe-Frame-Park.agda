-- ══════════════════════════════════════════════════════════════════
-- THE PARK READING ACROSS A SUBSCRIBE, IN ITS FREE FORM: one refutation
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks — unlike a
-- prose note, which decays silently.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Frame-Park where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; Tick; Id)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; _×ᵗ_; natᵗ; obs; ofᵉ;
                          emptyᵉ; scanᵉ; input; strmᵗ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Frame; Path; root; scan-f; Sched; EvalSt;
                                sched-init; st-init; subscribeE)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (framePark?)

------------------------------------------------------------------
-- THE WITNESS PROGRAM.  A scan whose SEED names an input, subscribed at
-- a floor of nought.  Two slots for the same reason the sibling
-- stratification refutation needs two: an accumulator a floor can be
-- wrong about must be an `obs`, since `inputsBelowᵛ` reads nothing on a
-- data type -- so slot nought carries the observable and slot one the
-- data the seed's stream names.  Both are `shared`, because `isData`
-- refuses to script an observable.
------------------------------------------------------------------

Γₚ : Ctx 2
Γₚ = obs natᵗ ∷ natᵗ ∷ []

d₀ : Closed Γₚ (obs natᵗ)
d₀ = ofᵉ (strmᵗ emptyᵉ ∷ [])

slₚ : Slots Γₚ
slₚ fzero        = shared d₀
slₚ (fsuc fzero) = shared emptyᵉ

-- the seed the reading is wrong about: a stream naming input one, which
-- sits ABOVE the floor the frame is read at
badSeed : Tm Γₚ [] [] [] (obs natᵗ)
badSeed = strmᵗ (input (fsuc fzero))

accFn : Fn Γₚ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
accFn = strmᵗ emptyᵉ

progₚ : Closed Γₚ (obs natᵗ)
progₚ = scanᵉ accFn badSeed emptyᵉ

schedₚ : Sched Γₚ
schedₚ = sched-init progₚ slₚ

stₚ : EvalSt progₚ
stₚ = st-init progₚ

-- THE FRAME THE READING IS KEYED BY, naming the node this subscribe is
-- ABOUT TO MINT.  `st-init` carries an empty table and `sched-init`
-- starts its counter at nought, so the frame names a cell that does not
-- exist yet -- which is exactly the state a caller holding a frame
-- cannot rule out, since nothing in a `Frame` says which node it names.
fₚ : Frame Γₚ natᵗ (obs natᵗ)
fₚ = scan-f accFn 0

------------------------------------------------------------------
-- THE SEPARATION.  Both rows are LOAD-BEARING and they fail for
-- different reasons: the first would read `false` if a miss were not
-- free, and the second would read `true` if the scan clause installed
-- its seed anywhere but the id it minted, or if `inputsBelowᵛ` read an
-- `obs` payload as data.
------------------------------------------------------------------

before≡true : framePark? 0 fₚ stₚ ≡ true
before≡true = refl

after≡false :
  framePark? 0 fₚ (proj₂ (proj₂ (subscribeE g0 progₚ root 0 0 schedₚ stₚ)))
    ≡ false
after≡false = refl

-- THE FINDING, and it is a DISJOINTNESS defect rather than an
-- arithmetic one.  A subscribe writes only cells it minted, so a frame
-- minted BEFORE it comes back untouched -- but the statement quantifies
-- the frame freely, and a frame naming a cell at or above the
-- scheduler's counter is one the subscribe is entitled to overwrite.
-- The repair is the premise that the read cells sit strictly below the
-- watermark the callee receives, which every real caller supplies by
-- `≤-refl` because it pushes through the id it just minted.
subscribeE-framePark-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u w}
     (k : ℕ) (g : Gas) (b : Closed Γ w) (κ : Path Γ w t)
     (bid : Id) (now : Tick) (f : Frame Γ s u)
     (sched : Sched Γ) (st : EvalSt e) →
     framePark? k f st ≡ true →
     framePark? k f (proj₂ (proj₂ (subscribeE g b κ bid now sched st)))
       ≡ true) →
  ⊥
subscribeE-framePark-absurd h
  with h {e = progₚ} 0 g0 progₚ root 0 0 fₚ schedₚ stₚ before≡true
... | ()
