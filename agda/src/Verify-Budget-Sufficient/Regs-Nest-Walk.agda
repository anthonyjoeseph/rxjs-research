-- THE REGISTRY'S DEPTH ALONG ONE CHAIN, walked frame by frame.
--
-- `chainStep` IS `foldPath`, so a statement about what one chain leaves
-- in the registry is an induction over the path with one leaf per
-- clause -- and the quantity that survives the induction is not the
-- registry alone but the POTENTIAL: the nesting of the values in flight
-- plus the depth of the path still to come, scaled by the factor that
-- path can still apply to them.  Every frame spends its own charge into
-- one of the three and never into two, which is why the potential is
-- what the walk carries and the registry is only read off it: a map
-- frame trades its factor for the values it produces, and a thru-outer
-- spends one unit of depth into the registration it mints.
--
-- WHY THE TWO STEP LEAVES ARE SEPARATE.  One says the registry does not
-- outrun the potential; the other says the potential itself survives
-- the frame.  Only the second is an invariant, and stating them
-- together would make the induction's own hypothesis a conjunct of the
-- thing being proven at every frame kind.
module Verify-Budget-Sufficient.Regs-Nest-Walk where

open import Data.Bool using (Bool; true)
open import Data.Bool.ListAction using (all)
open import Data.Fin using (Fin)
open import Data.List using (List; _++_)
open import Data.Nat using (ℕ; _+_; _*_; _⊔_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; m≤m⊔n; m≤n⊔m)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_;
         foldPath; stepFrame; dispatchShare)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; pathNestD; pathNestF)

-- the potential, read off the values still in flight and the path they
-- have left to climb -- and SCALED by the path's own factor, because
-- what a frame does to a value is substitution and substitution is
-- multiplicative in this currency.  The factor is spent frame by frame:
-- each one hands its share to the value it produces, so the product
-- shrinks exactly as fast as the value it multiplies can grow.
valsΦ? : ∀ {n} {Γ : Ctx n} {s t} (U : ℕ) (path : Path Γ s t)
  (vals : List (Val Γ s)) → Bool
valsΦ? {s = s} U path vals =
  all (λ v → pathNestF path * (nestDᵛ s v + pathNestD path) ≤ᵇ U) vals

postulate
  -- ONE FRAME'S REGISTRATIONS, under the potential it was handed.  The
  -- charge is the potential rather than the frame's own size because
  -- what a `thru-outer` mints is the subscribed value's frames over the
  -- rest of the path, which is the potential exactly.
  --
  -- INSTANTIATION SAID THE TIE IS EXACT, at the one shape that can
  -- deepen a registration at all: *All frames stacked ROOTWARD of the
  -- leaf, over a `deferᵉ` at an iterated observable type, read at two
  -- stack depths.  The fold moved with the stack and was EQUAL either
  -- side of the chain at both -- a frame is charged the `thru-outer`
  -- frames the observable it carries will push, and where that count
  -- stops at a defer gate the defer's own registration adds back the
  -- frame the gate dropped.  So this leaf has no slack to spend at the
  -- shapes reached so far, and a frame kind that raised the fold by one
  -- would refute it.
  --
  -- RECOVERY: git show f38a902:agda/evidence/probed/Probed/Chain-Step-Regs-Rootward.agda
  --   restores that program and its readings.
  stepFrame-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (U : ℕ) →
    valsΦ? U (f ↠ path) vals ≡ true →
    regsNestMax (EvalSt.registry
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U

  -- AND THE POTENTIAL ITSELF ACROSS THE FRAME, which is the induction's
  -- own hypothesis.  A step function may name its payload on both sides
  -- of an additive `nestDᵉ`, so ONE substitution installs the payload's
  -- nesting twice while the path gives up only the function's own --
  -- which is why the potential carries the path's factor and not just
  -- its depth.  A map frame surrenders two to its own size and the
  -- value it produces may claim exactly that, so the two moves cancel
  -- and nothing accumulates along the walk.
  --
  -- REFUTED: `Refuted.Apply-Fn-Nest` kills the additive reading of this
  --   same statement, at the smallest term of that shape -- a `mapᵉ`
  --   whose source and whose step function are the same outer variable,
  --   applied to a payload one `switchAllᵉ` deep.  Two against a charge
  --   of one, and that is the factor this form pays.
  --
  -- PROBED: `Probed.Step-Frame-Nest-Phi` walks that very term through
  --   this statement's map clause -- the factor sixty-four against a
  --   substituted depth of two -- with the additive reading run beside
  --   it as a control, reading false.  Covered: the `map-f` clause at
  --   the refuting step function, over the empty path.  NOT covered:
  --   `scan-f`, which substitutes by the same rule but also moves a
  --   node; `from-inner`, whose emitted value comes from the inner run
  --   rather than from the frame; and `thru-outer`, which spends depth
  --   where these spend factor.
  stepFrame-nest-Φ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (U : ℕ) →
    valsΦ? U (f ↠ path) vals ≡ true →
    valsΦ? U path (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

  -- THE SHARE BOUNDARY, where the walk leaves this chain and re-enters
  -- on every chain registered at the sink.  Those chains' own depths
  -- are under the registry's join by construction, which is why the
  -- same charge covers the fan-out.
  dispatchShare-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ _)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (U : ℕ) →
    valsΦ? U (share-sink {t = t} i) vals ≡ true →
    regsNestMax (EvalSt.registry
      (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U

foldPath-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (U : ℕ) →
  valsΦ? U path vals ≡ true →
  regsNestMax (EvalSt.registry
    (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
    ≤ regsNestMax (EvalSt.registry st) ⊔ U
foldPath-nest-regs sf gas id now envSrc root vals evs fin sched st U hΦ =
  m≤m⊔n (regsNestMax (EvalSt.registry st)) U
foldPath-nest-regs sf gas id now envSrc (share-sink i) vals evs fin sched st U hΦ =
  dispatchShare-nest-regs sf gas id now i vals fin sched st U hΦ
foldPath-nest-regs sf gas id now envSrc (f ↠ p) vals evs fin sched st U hΦ =
  ≤-trans (foldPath-nest-regs sf gas id now envSrc p
             (proj₁ step) (evs ++ proj₁ (proj₂ step))
             (proj₁ (proj₂ (proj₂ step)))
             (proj₁ (proj₂ (proj₂ (proj₂ step))))
             (proj₂ (proj₂ (proj₂ (proj₂ step)))) U
             (stepFrame-nest-Φ sf id now f p vals fin sched st U hΦ))
          (⊔-lub (stepFrame-nest-regs sf id now f p vals fin sched st U hΦ)
                 (m≤n⊔m (regsNestMax (EvalSt.registry st)) U))
  where
  step = stepFrame sf id now f p vals fin sched st
