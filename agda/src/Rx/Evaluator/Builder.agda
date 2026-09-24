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
-- AND THE RULE IS WHAT THE SPINE CARRIES INSTEAD.  The raw fold owes
-- the rule for the path it folds, and a path read out of the store has
-- it from the store's rule: a chain is a row, so its nodes are the
-- row's nodes and its end is the row's end.  The store's rule starts
-- vacuous at the empty registry and every fold keeps it; a cascade's
-- chains are a snapshot, so what is threaded along it is the rule for
-- every chain still to come, kept past each fold because the snapshot
-- agrees with itself.
--
-- SO THE EVALUATOR IS A PROJECTION.  `evaluate↓` is `proj₁` of
-- `evaluate!`, and a projection computes only as far as the thing
-- projected is a real body.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)

open import Rx.Prim using (Fuel; Source)
open import Rx.Exp using (Ctx; Closed; []ᵉ; Val; _≟ᵗ_)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; Arrival; arrTick; arrTy; arrVal; arrSource; AtFloor;
  RegId; RegRow; regSource; sameSource; pathHasNode; chainsGo; chainsOf; schedGo; dropSource;
  cascadeOpen; cascadeClose; cascadeFinish; sched-next; sched-init; st-init)
open import Rx.Evaluator.Domain using (chainStep⇓; cascadeGo⇓; cascade⇓; drain⇓; evaluate⇓;
  chain-step; casc-nil; casc-cut; casc-live; casc-run; casc-run-last;
  drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Reducible using (reducible; rawFold; rootRP; red-env; standing; Rule; rule; termini;
  fresh-rows; distinct-rows; Distinct; rowDistinct; Sound; sound; ruled; grounded; sounds; Agree; rowThrough; rowEnd; endOf;
  sub-rule; sub-ot; fold-kept)

------------------------------------------------------------------
-- THE ARRIVAL SPINE.
------------------------------------------------------------------

-- a chain is the path of a row the registry holds
chain-row : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ) (reg : List (RegRow Γ t))
              {x : RegId × AtFloor Γ (arrTy a) t}
          → x ∈ chainsGo a reg
          → Σ (RegRow Γ t) (λ r₀ → r₀ ∈ reg × (∀ k → rowThrough k r₀ ≡ pathHasNode k (proj₂ (proj₂ x)))
                                  × rowEnd r₀ ≡ endOf (proj₂ (proj₂ x)))
chain-row a [] ()
chain-row a ((rid , s , (u , p)) ∷ reg) x∈ with sameSource (arrSource a) (regSource s) | u ≟ᵗ arrTy a
... | false | _        = let (r₀ , m , ek , ee) = chain-row a reg x∈ in r₀ , there m , ek , ee
... | true  | no _     = let (r₀ , m , ek , ee) = chain-row a reg x∈ in r₀ , there m , ek , ee
... | true  | yes refl with x∈
...   | here refl = _ , here refl , (λ k → refl) , refl
...   | there x∈′ = let (r₀ , m , ek , ee) = chain-row a reg x∈′ in r₀ , there m , ek , ee

-- and a chain is distinct if every row's path is
chain-distinct : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ) (reg : List (RegRow Γ t))
                   {x : RegId × AtFloor Γ (arrTy a) t}
               → (∀ {r} → r ∈ reg → rowDistinct r) → x ∈ chainsGo a reg → Distinct (proj₂ (proj₂ x))
chain-distinct a [] dr ()
chain-distinct a ((rid , s , (u , p)) ∷ reg) dr x∈ with sameSource (arrSource a) (regSource s) | u ≟ᵗ arrTy a
... | false | _        = chain-distinct a reg (λ m → dr (there m)) x∈
... | true  | no _     = chain-distinct a reg (λ m → dr (there m)) x∈
... | true  | yes refl with x∈
...   | here refl = dr (here refl)
...   | there x∈′ = chain-distinct a reg (λ m → dr (there m)) x∈′

-- so the store's rule is the rule for each chain
chain-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (a : Arrival Γ) {sched : Sched Γ} {st : EvalSt e}
            → Rule sched st → ∀ {x} → x ∈ chainsOf a st → Sound (proj₂ (proj₂ x)) sched st
chain-sound a {st = st} ru x∈ =
  let (r₀ , m , ek , ee) = chain-row a (EvalSt.registry st) x∈
  in sound ru (λ k h r∈ th → trans (termini ru k r∈ m th (subst T (sym (ek k)) h)) ee)
              (λ k h → fresh-rows ru m k (subst T (sym (ek k)) h))
              (chain-distinct a (EvalSt.registry st) (distinct-rows ru) x∈)

-- and a snapshot's chains agree with each other
chain-agree : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (a : Arrival Γ) {sched : Sched Γ} {st : EvalSt e}
            → Rule sched st → ∀ {x y} → x ∈ chainsOf a st → y ∈ chainsOf a st
            → Agree (proj₂ (proj₂ x)) (proj₂ (proj₂ y))
chain-agree a {st = st} ru x∈ y∈ k hx hy =
  let (r₀ , m₀ , kx , ex) = chain-row a (EvalSt.registry st) x∈
      (r₁ , m₁ , ky , ey) = chain-row a (EvalSt.registry st) y∈
  in trans (sym ex) (trans (termini ru k m₀ m₁ (subst T (sym (kx k)) hx) (subst T (sym (ky k)) hy)) ey)

-- the end of a cascade drops rows and moves nothing else the rule reads
drop-sub : ∀ {n} {Γ : Ctx n} {t} (src : Source) (reg : List (RegRow Γ t)) {r}
         → r ∈ dropSource src reg → r ∈ reg
drop-sub src [] ()
drop-sub src ((rid , s , c) ∷ reg) r∈ with sameSource src (regSource s)
... | true  = there (drop-sub src reg r∈)
... | false with r∈
...   | here refl = here refl
...   | there r∈′ = there (drop-sub src reg r∈′)

finish-rule : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e)
            → Rule sched st → Rule (proj₁ (cascadeFinish a sched st)) (proj₂ (cascadeFinish a sched st))
finish-rule a sched st ru with Arrival.isLast a
... | false = ru
... | true  = sub-rule (drop-sub (arrSource a) (EvalSt.registry st)) ≤-refl ru

-- and popping an arrival moves only the queue
pop-rule : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {sched sched′ : Sched Γ} {a : Arrival Γ} {st : EvalSt e}
         → sched-next sched ≡ inj₂ (a , sched′) → Rule sched st → Rule sched′ st
pop-rule {sched = sched} eqn ru with schedGo (Sched.live sched)
pop-rule {sched = sched} ()   ru | inj₁ _
pop-rule {sched = sched} refl ru | inj₂ (a , ls) = sub-rule (λ r∈ → r∈) ≤-refl ru

chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (vs : List (Val Γ (arrTy a))) (fin : Bool)
             (c : AtFloor Γ (arrTy a) t)
             (sched : Sched Γ) (st : EvalSt e) → Sound (proj₂ c) sched st
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               chainStep⇓ {e = e} a vs fin c sched st r
             × (∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree (proj₂ c) κ₂
                → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
-- AN ARRIVAL IS FOLDED OUTSIDE THE BLOCK, so any fresh accessibility
-- funds the raw fold, which rebuilds the candidate for every value it
-- carries from the store.
chainStep! {n = n} a vs fin (lo , path) sched st so =
  let (_ , d) = rawFold (<-wellFounded (n ∸ lo)) ≤-refl (<-wellFounded _) path (arrTick a) vs fin sched st ≤-refl so
  in _ , chain-step d , (λ κ₂ → fold-kept d so κ₂)

cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (vs : List (Val Γ (arrTy a))) (fin : Bool)
             (chains : List (RegId × AtFloor Γ (arrTy a) t))
             (sched : Sched Γ) (st : EvalSt e) → Rule sched st
           → (∀ {x} → x ∈ chains → Sound (proj₂ (proj₂ x)) sched st)
           → (∀ {x y} → x ∈ chains → y ∈ chains → Agree (proj₂ (proj₂ x)) (proj₂ (proj₂ y)))
           → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
               cascadeGo⇓ {e = e} a vs fin chains sched st r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
cascadeGo! a vs fin []               sched st ru sds ag = _ , casc-nil , ru
cascadeGo! a vs fin ((rid , c) ∷ cs) sched st ru sds ag
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (_ , g , ru′) = cascadeGo! a vs fin cs sched st ru (λ x∈ → sds (there x∈))
                                    (λ x∈ y∈ → ag (there x∈) (there y∈))
              in _ , casc-cut eqc g , ru′
... | false =
      let so = sub-ot (λ r∈ → r∈) ≤-refl (sds (here refl))
          ((emits , sched₁ , st₁) , s , kept) =
            chainStep! a vs fin c sched
              (record st { delivered = rid ∷ EvalSt.delivered st }) so
          (_ , g , ru′) = cascadeGo! a vs fin cs sched₁ st₁ (ruled (kept (proj₂ c) so (λ _ _ _ → refl)))
                            (λ x∈ → kept _ (sub-ot (λ r∈ → r∈) ≤-refl (sds (there x∈))) (ag (here refl) (there x∈)))
                            (λ x∈ y∈ → ag (there x∈) (there y∈))
      in _ , casc-live eqc s g , ru′

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) → Rule sched st
         → Σ (Stream Γ t × Sched Γ × EvalSt e) λ r →
             cascade⇓ {e = e} a sched st r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
cascade! a sched st ru with Arrival.isLast a in eql
... | false =
      let ((_ , sched′ , st′) , g , ru′) =
            cascadeGo! a (arrVal a ∷ []) false (chainsOf a st) sched (cascadeOpen st)
              (sub-rule (λ r∈ → r∈) ≤-refl ru)
              (λ x∈ → sub-ot (λ r∈ → r∈) ≤-refl (chain-sound a ru x∈)) (chain-agree a ru)
      in _ , casc-run eql g , finish-rule a sched′ st′ ru′
... | true  =
      let ((_ , sched₁ , st₁) , g , ru₁) =
            cascadeGo! a (arrVal a ∷ []) false (chainsOf a st) sched (cascadeOpen st)
              (sub-rule (λ r∈ → r∈) ≤-refl ru)
              (λ x∈ → sub-ot (λ r∈ → r∈) ≤-refl (chain-sound a ru x∈)) (chain-agree a ru)
          ((_ , sched₂ , st₂) , g′ , ru₂) =
            cascadeGo! a [] true (chainsOf a st₁) sched₁ (cascadeClose a st₁)
              (sub-rule (λ r∈ → r∈) ≤-refl ru₁)
              (λ x∈ → sub-ot (λ r∈ → r∈) ≤-refl (chain-sound a ru₁ x∈)) (chain-agree a ru₁)
      in _ , casc-run-last eql g g′ , finish-rule a sched₂ st₂ ru₂

drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e) → Rule sched st
       → Σ (Stream Γ t) λ s → drain⇓ {e = e} fuel sched st s
drain! zero    sched st ru = _ , drain-done
drain! (suc k) sched st ru with sched-next sched in eqn
... | inj₁ _            = _ , drain-empty eqn
... | inj₂ (a , sched′) =
      let ((out , sched″ , st′) , c , ru′) = cascade! a sched′ st (pop-rule eqn ru)
          (_ , d)                          = drain! k sched″ st′ ru′
      in _ , drain-step eqn c d

------------------------------------------------------------------
-- THE TOP LINE.
------------------------------------------------------------------

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, and the relation
-- says so in one constructor -- so this is the assembly and the two
-- builders are its leaves.
evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
          → Σ (Stream Γ t) λ s → evaluate⇓ fuel e ins s
evaluate! {n = n} {Γ = Γ} fuel e ins =
  let aM = <-wellFounded _
      ((out , sched₀ , st₀) , s , _ , hs , _) =
        reducible aM e []ᵉ (red-env {Γ = Γ} aM []ᵉ) (root {lo = n}) (standing tt) rootRP tt 0
          (sched-init e ins) (st-init e) ≤-refl
          (grounded tt (sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt))
      (rest , d) = drain! fuel sched₀ st₀ (ruled (sounds hs))
  in _ , eval-run s d

-- AND THE EVALUATOR IS THE PROJECTION.  Not a new machine -- the same
-- machine reached through the builder rather than through a witness it
-- seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
