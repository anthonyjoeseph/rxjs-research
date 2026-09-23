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
-- NEXT DOOR.  `Rx.Evaluator.Reducible` builds every subscribe, frame
-- step, flattening walk, completion and share fan-out a SUBSCRIPTION
-- reaches, carrying the candidate down each in the continuation the
-- fold runs through; re-deriving them here would be a second copy of
-- the same induction with the candidates thrown away.  What is left
-- for this module is the arrival spine alone.
--
-- AND A CHAIN DELIVERED FROM THE SCHEDULE IS FOLDED RAW.  Nothing on
-- the arrival side holds a candidate for what it delivers -- a
-- registry path was read out of the store -- so the fold runs under
-- the RAW continuation, which draws every candidate it wants from the
-- fundamental theorem at values, at the ceiling the room stands at
-- when the arrival is folded.  The ceiling is the current count
-- itself, witnessed by reflexivity; a tick sits at the top of the
-- measure and is free.
--
-- SO THE EVALUATOR IS A PROJECTION.  `evaluate↓` is `proj₁` of
-- `evaluate!`, and a projection computes only as far as the thing
-- projected is a real body.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (zero; suc; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; []ᵉ; Val; listᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; root; Arrival; arrTick; arrTy; arrVal; AtFloor; RegId; chainsOf;
  cascadeOpen; cascadeClose; sched-next; sched-init; st-init)
open import Rx.Evaluator.Domain using (chainStep⇓; cascadeGo⇓; cascade⇓; drain⇓; evaluate⇓;
  chain-step; casc-nil; casc-cut; casc-live; casc-run; casc-run-last;
  drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Reducible using (reducible; rawRP; rootRP; red-val; fold; ofColumn; standing; rawAll; rawAll-holds)

------------------------------------------------------------------
-- THE ARRIVAL SPINE.
------------------------------------------------------------------

chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (vs : List (Val Γ (arrTy a))) (fin : Bool)
             (c : AtFloor Γ (arrTy a) t)
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               chainStep⇓ {e = e} a vs fin c sched st r
-- AN ARRIVAL IS FOLDED OUTSIDE THE BLOCK, so any fresh accessibility
-- funds the candidate for every value it carries: a scheduled body is
-- a closure, and `red-val` rebuilds its candidate by recursion on it.
chainStep! {n = n} a vs fin (lo , path) sched st =
  let ((_ , f , _) , _) =
        fold (rawRP (<-wellFounded (n ∸ lo)) ≤-refl (<-wellFounded _) path (standing (rawAll path))) tt
          (arrTick a) vs (ofColumn path (standing (rawAll path)) (red-val (<-wellFounded _) (listᵗ (arrTy a)) vs))
          fin sched st ≤-refl (rawAll-holds path sched st)
  in _ , chain-step f

cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (vs : List (Val Γ (arrTy a))) (fin : Bool)
             (chains : List (RegId × AtFloor Γ (arrTy a) t))
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               cascadeGo⇓ {e = e} a vs fin chains sched st r
cascadeGo! a vs fin []               sched st = _ , casc-nil
cascadeGo! a vs fin ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (_ , g) = cascadeGo! a vs fin cs sched st in _ , casc-cut eqc g
... | false =
      let ((emits , sched₁ , st₁) , s) =
            chainStep! a vs fin c sched
              (record st { delivered = rid ∷ EvalSt.delivered st })
          (_ , g) = cascadeGo! a vs fin cs sched₁ st₁
      in _ , casc-live eqc s g

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e)
         → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
             cascade⇓ {e = e} a sched st r
cascade! a sched st with Arrival.isLast a in eql
... | false =
      let (_ , g) = cascadeGo! a (arrVal a ∷ []) false (chainsOf a st) sched
                      (cascadeOpen st)
      in _ , casc-run eql g
... | true  =
      let ((_ , sched₁ , st₁) , g) =
            cascadeGo! a (arrVal a ∷ []) false (chainsOf a st) sched
              (cascadeOpen st)
          (_ , g′) = cascadeGo! a [] true (chainsOf a st₁) sched₁
                       (cascadeClose a st₁)
      in _ , casc-run-last eql g g′

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
  let (((out , sched₀ , st₀) , s , _) , _) =
        reducible (<-wellFounded _) e []ᵉ tt (root {lo = n}) (standing tt) rootRP tt 0
          (sched-init e ins) (st-init e) ≤-refl tt
      (rest , d) = drain! fuel sched₀ st₀
  in _ , eval-run s d

-- AND THE EVALUATOR IS THE PROJECTION.  Not a new machine -- the same
-- machine reached through the builder rather than through a witness it
-- seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
