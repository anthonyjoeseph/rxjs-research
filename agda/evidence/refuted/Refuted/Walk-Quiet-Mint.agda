-- A WALK OVER AN ARBITRARY SCHEDULE CAN LEAVE A ROW OF A SOURCE THAT
-- DIED INSIDE IT.  Slot numbers and minted source numbers are one
-- namespace, and only the counter keeps them apart: a share ending in
-- the walk puts its slot's number in `dying`, and a `defer` subscribed
-- later in the same walk mints a source and registers a row there.
-- Nothing in `cascadeGo⇓` or in `Rule` puts the source counter above
-- the slots, so a counter lowered to a slot's number makes the minted
-- row's source the dying share's.
--
-- THE STATE IS REACHED BY THE REAL SUBSCRIBE AND THE WALK IS RUN; only
-- the counter is lowered, and that is the claim.
module Refuted.Walk-Quiet-Mint where

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (hot; after_,_)
open import Rx.Exp using (Ctx; Closed; natᵗ; mergeᶠ)
open import Rx.Mint using (setAt; sourceᵏ)
open import Rx.Evaluator using (Arrival; Sched; EvalSt; cascadeOpen; chainsOf)
open import Rx.Evaluator.Domain using (cascadeGo⇓)
open import Rx.Evaluator.Builder using (cascadeGo!; chain-sound; chain-agree)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; sub-rule; sub-ot)
open import SExp.Syntax using (SExp; inputˢ; emptyˢ; mapˢ; strmˢ; deferˢ; ofˢ; takeWhileˢ; boolˢ)
open import SExp.Plain using (plainExp)
open import SExp.Simul-Slots using (plainSlots)
open import Simulation.Lockstep using (Conf; start)
open import Simulation.Stores using (dyingᵇ)
open import CLI.Unit-Test.Prelude using (Γ₂; mkSlots; flatAllˢ)

-- the hot slot's one value, and the share over it that ends at the first
d₀ = hot ((after 1 , 5) ∷ [])

d₁ : SExp Γ₂ [] [] [] natᵗ
d₁ = takeWhileˢ (boolˢ false) (inputˢ zero)

-- the share read first, so its row is walked first; then a merge that
-- subscribes a `defer` at every value of the hot
prog : SExp Γ₂ [] [] [] natᵗ
prog = flatAllˢ (mergeᶠ nothing) (ofˢ (strmˢ (inputˢ (suc zero))
                                   ∷ strmˢ (flatAllˢ (mergeᶠ nothing) (mapˢ (strmˢ (deferˢ emptyˢ)) (inputˢ zero))) ∷ []))

e : Closed Γ₂ natᵗ
e = plainExp prog

c : Conf e
c = start e (plainSlots (mkSlots d₀ d₁))

st₀ : EvalSt e
st₀ = Conf.st c

-- THE ONE THING NOT REACHED: the next source minted is the share's slot
low : Sched Γ₂
low = record (Conf.sched c) { mint = setAt sourceᵏ 1 (Sched.mint (Conf.sched c)) }

a : Arrival Γ₂
a = record { tick = 1 ; ordinal = 0 ; source = 0 ; elemTy = natᵗ ; payload = 5 ; isLast = false }

run = cascadeGo! a (5 ∷ []) false (chainsOf a st₀) low (cascadeOpen st₀)
        (sub-rule (λ r∈ → r∈) ≤-refl (Conf.ru c))
        (λ x∈ → sub-ot (λ r∈ → r∈) ≤-refl (chain-sound a (Conf.ru c) x∈))
        (chain-agree a (Conf.ru c))

final : EvalSt e
final = proj₂ (proj₂ (Σ⁰.fst⁰ run))

pick : ∀ {A : Set} (P : A → Bool) (xs : List A) → T (any P xs) → Σ A λ x → x ∈ xs × P x ≡ true
pick P (x ∷ xs) t with P x in eq
... | true  = x , here refl , eq
... | false with pick P xs t
...   | y , m , q = y , there m , q

walk-quiet-needs-counter :
  (∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {a vs fin cs sched} {st : EvalSt e} {r}
   → cascadeGo⇓ a vs fin cs sched st r
   → ∀ {x} → x ∈ EvalSt.registry (proj₂ (proj₂ r)) → dyingᵇ (proj₂ (proj₂ r)) x ≡ true → dyingᵇ st x ≡ true)
  → ⊥
walk-quiet-needs-counter wq with pick (dyingᵇ final) (EvalSt.registry final) tt
... | x , x∈ , d with wq (proj₁ (Σ⁰.snd⁰ run)) x∈ d
... | ()
