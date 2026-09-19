------------------------------------------------------------------
-- THE BUILDER: THE RUN, CONSTRUCTED RATHER THAN TESTED.
------------------------------------------------------------------

-- WHAT A BUILDER IS.  Every family in `Rx.Evaluator.Domain` is a graph
-- relation, so a member of it is a complete run; this module inhabits
-- them.  The result is not fixed by a machine -- the builder RETURNS
-- the pair, so it CHOOSES which clause ran, and a clause it does not
-- write is a run that does not exist.  That is why no arm here tests a
-- rank and no arm answers a negative case: there is no negative case to
-- answer.
--
-- SO THE EVALUATOR IS A PROJECTION.  `evaluate↓` is `proj₁` of
-- `evaluate!`, and a projection computes only as far as the thing
-- projected is a real body -- so while a leaf below is a postulate a
-- run typechecks and does not reduce, which is why the bug cache is a
-- target to type rather than one the gate types for you.
--
-- WHY IT SITS BELOW THE PROOF THAT CONSUMES IT.  Its cone is
-- `Rx.Evaluator`, `Rx.Evaluator.Domain` and `Rx.Evaluator.Reducible`,
-- all of which check in seconds, so the dev loop stays a loop while
-- this is being written.

-- HOW THE BUILDER LAYERS, ACROSS THREE FILES.  A path builder for an
-- EXTENDED path is constructed from the `Handles` its caller was handed
-- -- never by walking the path again -- so the frame helpers bottom out
-- in their argument and mention no recursion at all.  `Frames` holds
-- everything polymorphic in the bound, `Level` is indexed by the bound
-- and takes the levels below it as a parameter, and this file closes
-- the loop by well-founded recursion on the bound and then runs the
-- arrival spine over it.
--
-- WHAT THE THREE-WAY CUT BUYS.  A connect subscribes a share's
-- definition under a walk at the floor above the slot, which is the one
-- edge in the whole builder that RAISES the walk's own measure.  What
-- pays for it is a count of unconnected shares, which that same connect
-- strictly drops -- so the pair the connect spends is the pair a
-- strictly smaller bound offers, and that is a recursion no single file
-- can state.
module Rx.Evaluator.Builder where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc; acc)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ty; obs; Ctx; Closed; Val; Exp; Env; []ᵉ)
open import Rx.Exp.Guarded using (gsizeᵉ)
open import Rx.Inputs-Below using (ib-topᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; Arrival; AtFloor; RegId; arrTick; arrTy; arrVal; chainsOf;
  cascadeLatch; sched-next; sched-init; st-init)
open import Rx.Evaluator.Domain using (chainStep⇓; cascadeGo⇓; cascade⇓; drain⇓; evaluate⇓; chain-more; chain-last; casc-nil;
  casc-cut; casc-live; casc-run; drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Reducible using (Out; Red; Handles; RedEnv; count; parked; _∣_)
open import Rx.Evaluator.Builder.Frames using (handles-root; Below)
import Rx.Evaluator.Builder.Level as L

------------------------------------------------------------------
-- THE KNOT.
------------------------------------------------------------------

-- ONE FUNCTION, RECURSING ON THE BOUND, AND THE ONLY PLACE THE TWO
-- FACES MEET.  A level is built from the levels strictly below it,
-- which is exactly what the share connect asked for and what no single
-- file could state; everything else about the builder is either free in
-- the bound or already inside a level.
level : ∀ (m : ℕ) → Acc _<_ m → Below m
level m (acc rec) =
  record { walk = λ {_} {_} {_} {_} {p} →
                    L.handles!  m p (λ {m′} lt → level m′ (rec lt))
         ; term = λ {_} {_} {_} {_} {p} →
                    L.redExpAcc m p (λ {m′} lt → level m′ (rec lt))
         ; val  = λ {_} {_} {p} →
                    L.red-val   m p (λ {m′} lt → level m′ (rec lt))
         }

builder : ∀ (m : ℕ) → Below m
builder m = level m (<-wellFounded-fast m)

-- THE BOUND IS TAKEN APART HERE AND NOWHERE ELSE.  A level is built at
-- a COUNT, and offers every backlog; a caller names a whole bound.  The
-- two meet by reading the pair's components off it, which is why these
-- three are the only definitions in the builder that mention either.
handles! : ∀ {n} {Γ : Ctx n} {t u lo m} (κ : Path Γ lo u t) → Handles {m = m} u κ
handles! {m = m} = Below.walk (builder (count m)) {p = parked m}

red-val : ∀ {n} {Γ : Ctx n} {m} (u : Ty) (v : Val Γ u) → Red m u v
red-val {m = m} = Below.val (builder (count m)) {p = parked m}

reducible : ∀ {n} {Γ : Ctx n} {Θ t m} (b : Exp Γ [] [] Θ t) (σ : Env Γ Θ)
          → RedEnv m σ → Red m (obs t) (Θ , b , σ)
reducible {m = m} b σ rσ =
  Below.term (builder (count m)) {p = parked m} b σ rσ _ (ib-topᵉ b)
    (<-wellFounded-fast _) (<-wellFounded-fast (gsizeᵉ b))

------------------------------------------------------------------
-- THE ARRIVAL SPINE.
------------------------------------------------------------------

-- A SCRIPTED SOURCE'S LAST VALUE IS FOLLOWED BY ITS END, IN THAT ORDER
-- AND DOWN THE SAME CHAIN, which is what an rxjs observer sees.
chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (c : AtFloor Γ (arrTy a) t)
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Out e) λ r → chainStep⇓ {e = e} a c sched st r
chainStep! a (lo , path) sched st with Arrival.isLast a in leq
... | false = let (r , d) = proj₁ (handles! path) (red-val (arrTy a) (arrVal a))
                              (arrTick a) sched st (≤-refl ∣ inj₂ ≤-refl)
              in r , chain-more leq d
... | true  = let ((out , sched₁ , st₁) , d) =
                    proj₁ (handles! path) (red-val (arrTy a) (arrVal a))
                      (arrTick a) sched st (≤-refl ∣ inj₂ ≤-refl)
                  (r , c) = proj₂ (handles! path) (arrTick a) sched₁ st₁ (≤-refl ∣ inj₂ ≤-refl)
              in _ , chain-last leq d c

cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (chains : List (RegId × AtFloor Γ (arrTy a) t))
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Out e) λ r → cascadeGo⇓ {e = e} a chains sched st r
cascadeGo! a []               sched st = _ , casc-nil
cascadeGo! a ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (r , g) = cascadeGo! a cs sched st in r , casc-cut eqc g
... | false =
      let ((emits , sched₁ , st₁) , s) =
            chainStep! a c sched (record st { delivered = rid ∷ EvalSt.delivered st })
          (_ , g) = cascadeGo! a cs sched₁ st₁
      in _ , casc-live eqc s g

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e)
         → Σ (Out e) λ r → cascade⇓ {e = e} a sched st r
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

evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
          → Σ (Stream Γ t) λ s → evaluate⇓ fuel e ins s
evaluate! {n = n} fuel e ins =
  let ((burst , sched₀ , st₀) , s) =
        reducible e []ᵉ tt (root {lo = n}) handles-root 0
          (sched-init e ins) (st-init e) (≤-refl ∣ inj₂ ≤-refl)
      (rest , d) = drain! fuel sched₀ st₀
  in _ , eval-run s d

-- AND THE EVALUATOR IS THE PROJECTION.  Not a new machine -- the same
-- machine with every rank reading and every `<?` gone, reached through
-- the builder rather than through a witness it seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
