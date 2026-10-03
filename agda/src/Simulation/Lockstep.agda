------------------------------------------------------------------
-- A RUN IS ITS SUBSCRIBE FOLLOWED BY ONE ARRIVAL PER UNIT OF FUEL, read
-- one arrival at a time.  The drain pops the front of the schedule and
-- cascades it, so the run at `suc k` is the run at `k` followed by what
-- the machine sends from the configuration `k` arrivals in.  Stated
-- over a configuration -- the schedule, the store and the rule the
-- builder carries between them -- so two machines can be stepped side
-- by side.
--
-- ONE STEP IS THE DRAIN'S OWN STEP, BY PROJECTION.  `stepOn` reads the
-- cascade the drain runs through the same projections the drain's
-- pattern lambda unfolds to, so the drain at `suc k` is the step's
-- output followed by the drain at `k` without a lemma about the
-- cascade.  A dry schedule sends nothing and leaves the configuration
-- where it is, which is what the drain does at every later fuel.
------------------------------------------------------------------
module Simulation.Lockstep where

open import Data.List    using (List; []; _∷_; _++_; concat)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat     using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Prim      using (Fuel; PlainEvent; valueᵖ; completeᵖ; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Slots     using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Stream; sched-next)
open import Rx.Evaluator.Builder using (drain!; drainOn; evaluate↓; subscribe!; cascade!; pop-rule)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; Rule)
open import Batchable.Inst-Extract using (instExtract; emitValues)
open import SExp.InstEmit.Decode using (decodeEmits)
open import SExp.Plain   using (plainValues)

record Conf {n} {Γ : Ctx n} {t} (e : Closed Γ t) : Set where
  constructor conf
  field sched : Sched Γ
        st    : EvalSt e
        ru    : Rule sched st
open Conf

module _ {n} {Γ : Ctx n} {t} {e : Closed Γ t} where

  -- the arrival the schedule pops, as the drain cascades it
  stepOn : (c : Conf e) (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) → sched-next (sched c) ≡ x
         → Stream Γ t × Conf e
  stepOn c (inj₁ _)         eqn = [] , c
  stepOn c (inj₂ (a , s′)) eqn =
    proj₁ (Σ⁰.fst⁰ C) , conf (proj₁ (proj₂ (Σ⁰.fst⁰ C))) (proj₂ (proj₂ (Σ⁰.fst⁰ C))) (proj₂ (Σ⁰.snd⁰ C))
    where C = cascade! a s′ (st c) (pop-rule eqn (ru c))

  out : Conf e → Stream Γ t
  out c = proj₁ (stepOn c (sched-next (sched c)) refl)

  next : Conf e → Conf e
  next c = proj₂ (stepOn c (sched-next (sched c)) refl)

  iter : Fuel → Conf e → Conf e
  iter zero    c = c
  iter (suc k) c = next (iter k c)

  drain↓ : Fuel → Conf e → Stream Γ t
  drain↓ k c = Σ⁰.fst⁰ (drain! k (sched c) (st c) (ru c))

  iter-next : ∀ k (c : Conf e) → iter k (next c) ≡ next (iter k c)
  iter-next zero    c = refl
  iter-next (suc k) c = cong next (iter-next k c)

  -- a dry schedule drains nothing, at any fuel
  dryOn : ∀ k (c : Conf e) (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) (eqn : sched-next (sched c) ≡ x) {u : ⊤}
        → sched-next (sched c) ≡ inj₁ u → Σ⁰.fst⁰ (drainOn k (sched c) (st c) (ru c) x eqn) ≡ []
  dryOn k c (inj₁ _) eqn dry = refl
  dryOn k c (inj₂ _) eqn dry with trans (sym dry) eqn
  ... | ()

  dry-drain : ∀ k (c : Conf e) {u : ⊤} → sched-next (sched c) ≡ inj₁ u → drain↓ k c ≡ []
  dry-drain zero    c dry = refl
  dry-drain (suc k) c dry = dryOn k c (sched-next (sched c)) refl dry

  consOn : ∀ k (c : Conf e) (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) (eqn : sched-next (sched c) ≡ x)
         → Σ⁰.fst⁰ (drainOn k (sched c) (st c) (ru c) x eqn)
           ≡ proj₁ (stepOn c x eqn) ++ drain↓ k (proj₂ (stepOn c x eqn))
  consOn k c (inj₁ _)         eqn = sym (dry-drain k c eqn)
  consOn k c (inj₂ (a , s′)) eqn = refl

  -- the drain at `suc k` is one step followed by the drain at `k`
  drain-cons : ∀ k (c : Conf e) → drain↓ (suc k) c ≡ out c ++ drain↓ k (next c)
  drain-cons k c = consOn k c (sched-next (sched c)) refl

  -- and the drain at `k` followed by the step `k` arrivals in
  drain-snoc : ∀ k (c : Conf e) → drain↓ (suc k) c ≡ drain↓ k c ++ out (iter k c)
  drain-snoc zero    c = trans (drain-cons zero c) (++-identityʳ (out c))
  drain-snoc (suc k) c =
    trans (drain-cons (suc k) c)
   (trans (cong (out c ++_) (drain-snoc k (next c)))
   (trans (sym (++-assoc (out c) (drain↓ k (next c)) (out (iter k (next c)))))
   (trans (cong (λ d → (out c ++ drain↓ k (next c)) ++ out d) (iter-next k c))
          (cong (_++ out (iter (suc k) c)) (sym (drain-cons k c))))))

-- the configuration the root subscribe leaves, and what it sends
start : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Conf e
start e ins = conf (proj₁ (proj₂ (Σ⁰.fst⁰ (subscribe! e ins)))) (proj₂ (proj₂ (Σ⁰.fst⁰ (subscribe! e ins))))
                   (proj₂ (Σ⁰.snd⁰ (subscribe! e ins)))

opening : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
opening e ins = proj₁ (Σ⁰.fst⁰ (subscribe! e ins))

run-opening : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
            → evaluate↓ zero e ins ≡ opening e ins
run-opening e ins = ++-identityʳ (opening e ins)

-- A RUN AT ONE MORE UNIT OF FUEL IS THE RUN BEFORE IT AND ONE ARRIVAL
run-snoc : ∀ {n} {Γ : Ctx n} {t} (k : Fuel) (e : Closed Γ t) (ins : Slots Γ)
         → evaluate↓ (suc k) e ins ≡ evaluate↓ k e ins ++ out (iter k (start e ins))
run-snoc k e ins =
  trans (cong (opening e ins ++_) (drain-snoc k (start e ins)))
        (sym (++-assoc (opening e ins) (drain↓ k (start e ins)) (out (iter k (start e ins)))))

------------------------------------------------------------------
-- THE READINGS ARE HOMOMORPHISMS, so a slice of a run reads as the
-- reading of the arrival that sent it.
------------------------------------------------------------------

concat-++ : ∀ {A : Set} (xss yss : List (List A)) → concat (xss ++ yss) ≡ concat xss ++ concat yss
concat-++ []         yss = refl
concat-++ (xs ∷ xss) yss = trans (cong (xs ++_) (concat-++ xss yss)) (sym (++-assoc xs (concat xss) (concat yss)))

values-++ : ∀ {A : Set} (xs ys : List (PlainEvent A)) → plainValues (xs ++ ys) ≡ plainValues xs ++ plainValues ys
values-++ []               ys = refl
values-++ (valueᵖ v ∷ xs) ys = cong (v ∷_) (values-++ xs ys)
values-++ (completeᵖ ∷ xs) ys = values-++ xs ys

decode-++ : ∀ {n} {Γ : Ctx n} {a} xs ys → decodeEmits {Γ = Γ} {a = a} (xs ++ ys) ≡ decodeEmits xs ++ decodeEmits ys
decode-++ []               ys = refl
decode-++ (valueᵖ v ∷ xs) ys = cong (_ ∷_) (decode-++ xs ys)
decode-++ (completeᵖ ∷ xs) ys = decode-++ xs ys

extract-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) → instExtract (xs ++ ys) ≡ instExtract xs ++ instExtract ys
extract-++ []       ys = refl
extract-++ (x ∷ xs) ys = trans (cong (emitValues x ++_) (extract-++ xs ys))
                               (sym (++-assoc (emitValues x) (instExtract xs) (instExtract ys)))
