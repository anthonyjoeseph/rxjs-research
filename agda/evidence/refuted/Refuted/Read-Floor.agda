-- `hot-read` OVER UNRELATED FLOORS IS FALSE.  A path's floor decides
-- whether a read at it reads anything at all, and nothing the read takes
-- relates the plain path's floor to the impl's: `PathRel`'s `root~` pairs
-- two roots at any two floors.  Here the plain read stands above the hot
-- slot and registers, the impl's stands at its own stamped slot and folds
-- the empty end, and no `RegRel` pairs a plain row with an empty impl
-- registry.  The runs only ever subscribe at aligned floors -- the roots
-- at `n` and `n + n`, a connect at a slot and its stamped one -- so what
-- this rules out is the read over a pair no run builds.
--
-- THE STATES ARE BUILT, NOT REACHED, and that is the claim: the
-- hypotheses `hot-read` takes admit them.
module Refuted.Read-Floor where

open import Data.Fin using (Fin; zero; suc; _↑ʳ_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Vec using (lookup)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Closed; Env; FnClo; natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_; varᵗ; renTm; Ren∈; ext∈; input)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; map-f; _↠[_]_; sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-floor; subs-hot-live; fold-step; fold-root; step-map)
open import Rx.Evaluator.Reducible.Support using (Sound; sound; rule)
open import SExp.Syntax using (Kinds; plainᵏ; emitᵗ; inputˢ; emptyˢ)
open import SExp.Plain using (plainExp)
open import SExp.Elaborate using (plainᶜ⁺; frameᵛ; restampᵛ; subscribeᵛ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Stores using (Store; PathRel; EnvRel; root~; [])
open import Simulation.Schedules using ([])
open import Simulation.After using (module Kept)
open Kept using (After; module After)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots)
open import Rx.Prim using (hot)

κ₀ : Kinds 2
κ₀ = κOf (hot [])

ins : SimulSlots Γ₂ κ₀
ins = mkSlots (hot []) emptyˢ

Γ′ = plainᵏ Γ₂ κ₀

ep : Closed Γ₂ natᵗ
ep = plainExp (inputˢ zero)

ei : Closed Γ′ (emitᵗ natᵗ)
ei = elaborateImpl {Γ = Γ₂} κ₀ (inputˢ zero)

-- the two runs before anything is subscribed, no source live
sP : Sched Γ₂
sP = record (sched-init ep (plainSlots ins)) { live = [] }

stP : EvalSt ep
stP = st-init ep

sI : Sched Γ′
sI = record (sched-init ei (embedSlotsImpl ins)) { live = [] }

stI : EvalSt ei
stI = st-init ei

S : Store {Γ = Γ₂} κ₀ sP stP sI stI
S = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; pairs-below = [] , []
  ; sources = []
  ; numbers = []
  ; distinct = [] , []
  ; sync    = []
  ; rows    = []
  ; dlv-alike = _
  ; dying-alike = _
  ; latches = λ { zero → (λ _ → refl , refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; bounded = [] , []
  ; swept   = []
  ; uncut   = [] , []
  ; named   = record { slots-below = ≤-refl ; ords-below = [] ; srcs-below = [] ; cut-below = [] ; dlv-below = [] ; dying-below = [] }
            , record { slots-below = ≤-refl ; ords-below = [] ; srcs-below = [] ; cut-below = [] ; dlv-below = [] ; dying-below = [] }
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ { zero _ → inj₂ (refl , refl , λ ()) ; (suc zero) () }
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = ins , refl , refl
  }

-- THE PLAIN ROOT STANDS ABOVE BOTH SLOTS, THE IMPL'S AT ZERO
p : Path Γ₂ 2 natᵗ natᵗ
p = root

q : Path Γ′ 0 (emitᵗ natᵗ) (emitᵗ natᵗ)
q = root

ρ′ : Env Γ′ (uniqᵗ ∷ [])
ρ′ = 0 ∷ᵉ []ᵉ

stamp : FnClo Γ′ (emitᵗ natᵗ) (emitᵗ natᵗ)
stamp = uniqᵗ ∷ [] , renTm (λ x → x) (λ x → x) (ext∈ (λ x → x))
                       (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ [])) subscribeᵛ (varᵗ (here refl))) , ρ′

-- the plain read registers at the live hot; the impl's is at its floor
dP : subscribeE⇓ {e = ep} ([] , input zero , []ᵉ) p 0 sP stP _
dP = subs-hot-live (s≤s z≤n) refl refl refl

dI : subscribeE⇓ {e = ei} (uniqᵗ ∷ [] , input (2 ↑ʳ zero) , ρ′) (map-f stamp ↠[ ≤-refl ] q) 0 sI stI _
dI = subs-floor z≤n (fold-step step-map fold-root)

i : Fin 2
i = zero

HotRead : Set
HotRead =
  ∀ {Θ Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel {Γ = Γ₂} κ₀ Θ w ρ′ ρ
  → (eq : lookup Γ′ (2 ↑ʳ i) ≡ emitᵗ (lookup Γ₂ i))
  → ∀ {lo lo′} {p : Path Γ₂ lo (lookup Γ₂ i) natᵗ} {q : Path Γ′ lo′ (emitᵗ (lookup Γ₂ i)) (emitᵗ natᵗ)} {now}
      {sP : Sched Γ₂} {stP : EvalSt ep} {sI : Sched Γ′} {stI : EvalSt ei} {rP rI}
  → (S : Store {Γ = Γ₂} κ₀ sP stP sI stI)
  → PathRel {Γ = Γ₂} κ₀ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
  → Sound p sP stP → Sound q sI stI
  → subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP
  → subscribeE⇓ {e = ei} (Θ′ , input (2 ↑ʳ i) , ρ′)
      (subst (λ u → Path Γ′ lo′ u (emitᵗ natᵗ)) (sym eq)
        (map-f (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w)
                       (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ Θ)) subscribeᵛ (varᵗ (here refl))) , ρ′) ↠[ ≤-refl ] q))
      now sI stI rI
  → Σ (After {Γ = Γ₂} κ₀ S rP rI) λ A
      → PathRel {Γ = Γ₂} κ₀ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

-- the plain registry gains the read's row and the impl's stays empty
hot-read-needs-floors : ¬ HotRead
hot-read-needs-floors SR with Store.rows (After.store (proj₁ (SR (λ x → x) (λ ()) refl S root~
                                 (sound (Store.ruleP S) (λ k ()) (λ k ()) _) (sound (Store.ruleI S) (λ k ()) (λ k ()) _) dP dI)))
... | ()
