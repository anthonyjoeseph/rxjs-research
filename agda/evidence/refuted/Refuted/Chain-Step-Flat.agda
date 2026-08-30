-- ══════════════════════════════════════════════════════════════════
-- ONE CHAIN'S STEP DOES NOT PRESERVE A FLAT CAP, so the step leaf
-- cannot be discharged in the form it is stated in.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  The selection's caps are packaged as a
-- predicate asserting one FLAT cap at every state the fold passes
-- through, and the fold over the chains is a real body that hands each
-- chain the state its predecessor's step produced.  So the leaf the
-- body rests on is that a step returns a state inside the cap it was
-- handed, and the plan was a walk over the step's own arms.
--
-- WHERE IT BREAKS, AND IT IS THE REGISTRY AND THE STORE, NOT AN ARM.
-- A step is a whole path fold, and a `mergeAll` drain SUBSCRIBES the
-- inners it releases -- so it installs nodes and registrations that
-- nothing in the same step retires.  Retirement happens at the
-- cascade's FINISH, one level up, which is why a fit read either side
-- of a whole cascade sees the registry come back at zero and reports
-- preservation.  Read either side of a single step, at the same
-- programs, the smallest cap the state fits rises by better than a
-- factor of two, and the rows below pin the crossing at a cap the
-- pre-state satisfies.
--
-- SO THE GAP IS THAT THE HYPOTHESIS CARRIES NO LEVEL.  The frame-wise
-- receipt this would be assembled from concludes at `frameStep (j + j')`
-- and never back at its own cap, and the caps ordering only ever runs
-- the other way -- so no amount of arm-by-arm work recovers the flat
-- form.  What the predicate needs is the level its own consumers
-- already speak in: the nodes face states one chain's walk as a Σ over
-- the level reached, bounded by the recurrence's count, and lands at
-- the next instant's cap by that route.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing against the CASCADE-level
-- preservation, which is proven and which these numbers are consistent
-- with -- the finish is what pays for the step.  Nor does it reach the
-- statement at its OWN cap: `capsAt` does not reduce, so no witness
-- discharges the hypothesis there, and the escape left is that the
-- instant's real cap has slack a level-free argument can still spend.
-- That escape is what the level would make unnecessary.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Flat where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainsOf; chainStep)
open import Rx.Slots using (Slots)

open import Refuted.Demand-Programs using (Γ₂; progU; insF; sucGU)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?)

prog : Closed Γ₂ natᵗ
prog = progU 2 2

slots : Slots Γ₂
slots = insF 1 2 2

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE (gasPad (sucGU 1 2 2 2 2) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the state the FIRST cascade leaves, which is where a drain has
-- something parked to release
after1 : Sched Γ₂ × EvalSt prog
after1 with sched-next (proj₁ sub)
... | inj₁ _        = sub
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ sub)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- THE CAP IS THE SMALLEST ONE THE PRE-STEP STATE FITS, so the row is a
-- crossing rather than a comparison against a number chosen to fail.
-- Its other two components are given room deliberately: what moves
-- here is the size, and pinning the width and the registry as well
-- would make the row fail for a reason it is not evidence about.
cap : Caps
cap = caps 26 4000 4000

-- both sides of ONE chain's step on the second arrival, at the first
-- live chain.  The defaults are `false , true`, so a run that
-- degenerated -- no arrival, or no chain -- fails the pins below
-- rather than passing them.
row : Bool × Bool × Bool
row with sched-next (proj₁ after1)
... | inj₁ _        = false , false , true
... | inj₂ (a , sd) with chainsOf a (proj₂ after1)
...   | []            = false , false , true
...   | (rid , p) ∷ _ =
  let st₀ = cascadeLatch a (proj₂ after1)
      st₁ = record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }
      r   = chainStep 1 a p sd st₁
  in capsOK? cap sd st₀
   , capsOK? cap sd st₁
   , capsOK? cap (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- THE TWO SIDES, PINNED.  Spelled out rather than left inline so that
-- a repair moving either one fails here, naming the side, instead of
-- quietly turning the crossing into an agreement.
latched≡true : proj₁ row ≡ true
latched≡true = refl

pre≡true : proj₁ (proj₂ row) ≡ true
pre≡true = refl

post≡false : proj₂ (proj₂ row) ≡ false
post≡false = refl

chain-step-flat-absurd :
  (proj₁ (proj₂ row) ≡ true → proj₂ (proj₂ row) ≡ true) → ⊥
chain-step-flat-absurd h with h refl
... | ()
