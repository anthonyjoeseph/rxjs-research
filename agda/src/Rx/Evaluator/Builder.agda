------------------------------------------------------------------
-- THE BUILDER: THE RUN, CONSTRUCTED RATHER THAN TESTED.
------------------------------------------------------------------

-- WHAT A BUILDER IS.  Every family in `Rx.Evaluator.Domain` is a graph
-- relation, so a member of it is a complete run; this module inhabits
-- the ones the reducibility candidate does not.  The result is not
-- fixed by a machine -- the builder RETURNS the pair, so it CHOOSES
-- which clause ran, and a clause it does not write is a run that does
-- not exist.  That is why no arm here tests a rank and no arm answers
-- a negative case: there is no negative case to answer.
--
-- AND THE SUBSCRIBE CYCLE IS NOT HERE, BECAUSE IT IS ALREADY PROVEN
-- NEXT DOOR.  `Rx.Evaluator.Reducible` builds every subscribe, push,
-- frame step and flattening walk a SUBSCRIPTION reaches, carrying the
-- candidate through each; re-deriving them here would be a second copy
-- of the same induction with the satisfaction column thrown away.
-- What is left for this module is what a subscription never enters:
-- the completion side, the share fan-out, and the arrival spine.
--
-- AND THE ONE THING THAT USED TO BE A LEAF IS NOW A CALL.  A merge's
-- parked lane hands back a value the store kept, and a store keeps
-- values rather than premises -- so the drain used to be short of the
-- candidate that value arrived with.  With a value at observable type
-- being a body paired with an environment, and the claim at an
-- environment's entries being the whole of the claim at the pair, the
-- fundamental theorem at VALUES is total and the drain simply calls
-- it.
--
-- SO THE EVALUATOR IS A PROJECTION.  `evaluate↓` is `proj₁` of
-- `evaluate!`, and a projection computes only as far as the thing
-- projected is a real body.
module Rx.Evaluator.Builder where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (zero; suc; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; []ᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; root; Arrival; arrTick; arrTy; arrVal; AtFloor; RegId; chainsOf;
  cascadeLatch; sched-next; sched-init; st-init)
open import Rx.Evaluator.Domain using (chainStep⇓; cascadeGo⇓; cascade⇓; drain⇓; evaluate⇓;
  chain-step; casc-nil; casc-cut; casc-live; casc-run;
  drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Reducible using (reducible; foldPath!)

------------------------------------------------------------------
-- THE ARRIVAL SPINE.
------------------------------------------------------------------

chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (c : AtFloor Γ (arrTy a) t)
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               chainStep⇓ {e = e} a c sched st r
chainStep! {n = n} a (lo , path) sched st =
  let (_ , f) = foldPath! (<-wellFounded (n ∸ lo)) (arrTick a) path
                  (arrVal a ∷ []) (Arrival.isLast a) sched st
                  (<-wellFounded _) ≤-refl
  in _ , chain-step f

cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (chains : List (RegId × AtFloor Γ (arrTy a) t))
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               cascadeGo⇓ {e = e} a chains sched st r
cascadeGo! a []               sched st = _ , casc-nil
cascadeGo! a ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (_ , g) = cascadeGo! a cs sched st in _ , casc-cut eqc g
... | false =
      let ((emits , sched₁ , st₁) , s) =
            chainStep! a c sched
              (record st { delivered = rid ∷ EvalSt.delivered st })
          (_ , g) = cascadeGo! a cs sched₁ st₁
      in _ , casc-live eqc s g

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e)
         → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
             cascade⇓ {e = e} a sched st r
cascade! a sched st =
  let (_ , g) = cascadeGo! a (chainsOf a st) sched (cascadeLatch a sched st)
  in _ , casc-run g

drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e)
       → Σ (Stream Γ t) λ s → drain⇓ {e = e} fuel sched st s
drain! zero    sched st = _ , drain-done
drain! (suc k) sched st with sched-next sched in eqn
... | inj₁ _            = _ , drain-empty eqn
... | inj₂ (a , sched′) =
      let ((out , sched″ , st′) , c) = cascade! a sched′ st
          (_ , d)                    = drain! k sched″ st′
      in _ , drain-step eqn c d

------------------------------------------------------------------
-- THE TOP LINE.
------------------------------------------------------------------

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, and the relation
-- says so in one constructor -- so this is the assembly and the two
-- builders are its leaves.
evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
          → Σ (Stream Γ t) λ s → evaluate⇓ fuel e ins s
evaluate! {n = n} fuel e ins =
  let ((segs , sched₀ , st₀) , s , _) =
        reducible e []ᵉ tt (root {lo = n}) 0 (sched-init e ins) (st-init e)
          (<-wellFounded _) ≤-refl
      (rest , d) = drain! fuel sched₀ st₀
  in _ , eval-run s d

-- AND THE EVALUATOR IS THE PROJECTION.  Not a new machine -- the same
-- machine reached through the builder rather than through a witness it
-- seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
