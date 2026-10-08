-- `shared-read` WITHOUT `Sound` OF ITS PATHS IS FALSE.  `Store` and
-- `PathRel` say every frame of the two paths is related and say nothing
-- about the plain path's nodes being distinct, so a path may pass one
-- merge twice, as two of its lanes.  A read of a connected share joins
-- it, and the join registers the path as a row, which `Rule.distinct-rows`
-- refuses; the store `After` hands back must carry that rule.
--
-- THE STATES ARE BUILT, NOT REACHED, and that is the claim: the
-- hypotheses `shared-read` takes admit them.
module Refuted.Shared-Read-Sound where

open import Data.Bool using (false)
open import Data.Fin using (Fin; zero; suc; _↑ʳ_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (suc; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Vec using (lookup)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Closed; Val; Env; FnClo; _×ᵗ_; mergeᶠ; natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_; sndᵗ; varᵗ; renTm; Ren∈; ext∈; input)
open import Rx.Mint using (setAt; nodeᵏ)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; map-f; scan-f; from-inner; _↠[_]_;
  sched-init; st-init; mergeAll-st; cell-st; mergeAllᵒ)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-shared; slot-join)
open import Rx.Evaluator.Reducible.Support using (rule; distinct-rows)
open import SExp.Syntax using (Kinds; plainᵏ; emitᵗ; inputˢ; emptyˢ)
open import SExp.Plain using (plainExp)
open import SExp.Elaborate using (flatStepᵛ; FlatSᵗ; plainᶜ⁺; frameᵛ; restampᵛ; subscribeᵛ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Stores using (Store; PathRel; Flattener; EnvRel; inner~; root~; merge~; [])
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

-- the two runs before the read: no source live, the share connected on
-- both sides, one merge, and the impl's flattener cell
sP : Sched Γ₂
sP = record (sched-init ep (plainSlots ins)) { mint = setAt nodeᵏ 3 (Sched.mint (sched-init ep (plainSlots ins))) ; live = [] }

stP : EvalSt ep
stP = record (st-init ep) { nodes = (0 , mergeAll-st {t = natᵗ} nothing 0 [] false) ∷ [] ; connectedShares = 1 ∷ [] }

sI : Sched Γ′
sI = record (sched-init ei (embedSlotsImpl ins)) { mint = setAt nodeᵏ 4 (Sched.mint (sched-init ei (embedSlotsImpl ins))) ; live = [] }

cell : Val Γ′ (FlatSᵗ natᵗ)
cell = (0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)

stI : EvalSt ei
stI = record (st-init ei) { nodes = (0 , mergeAll-st {t = emitᵗ natᵗ} nothing 0 [] false) ∷ (1 , cell-st {t = FlatSᵗ natᵗ} cell) ∷ []
                          ; connectedShares = 3 ∷ [] }

S : Store {Γ = Γ₂} κ₀ sP stP sI stI
S = record
  { π       = (0 , 0 ∷ 1 ∷ []) ∷ (1 , 2 ∷ []) ∷ (2 , 3 ∷ []) ∷ []
  ; π-keys  = ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ [] ∷ []
  ; π-vals  = ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ [] ∷ []
  ; pairs-below = (s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ s≤s (s≤s (s≤s z≤n)) ∷ [])
                , ((s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []) ∷ (s≤s (s≤s (s≤s z≤n)) ∷ []) ∷ (s≤s (s≤s (s≤s (s≤s z≤n))) ∷ []) ∷ [])
  ; sources = []
  ; numbers = []
  ; distinct = [] , []
  ; sync    = []
  ; rows    = []
  ; dlv-alike = tt
  ; dying-alike = tt
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

-- THE PATH PASSES ITS MERGE TWICE, as two of its lanes.  Every frame is
-- related, and `PathRel` asks nothing more.
p : Path Γ₂ 2 natᵗ natᵗ
p = from-inner mergeAllᵒ 0 1 ↠[ ≤-refl ] (from-inner mergeAllᵒ 0 2 ↠[ ≤-refl ] root)

snd′ : FnClo Γ′ (FlatSᵗ natᵗ) (emitᵗ natᵗ)
snd′ = [] , sndᵗ (varᵗ (here refl)) , []ᵉ

flat′ : FnClo Γ′ (FlatSᵗ natᵗ ×ᵗ emitᵗ natᵗ) (FlatSᵗ natᵗ)
flat′ = [] , flatStepᵛ , []ᵉ

q : Path Γ′ 4 (emitᵗ natᵗ) (emitᵗ natᵗ)
q = from-inner mergeAllᵒ 0 2 ↠[ ≤-refl ]
    (scan-f flat′ 1 ↠[ ≤-refl ]
     (map-f snd′ ↠[ ≤-refl ]
      (from-inner mergeAllᵒ 0 3 ↠[ ≤-refl ]
       (scan-f flat′ 1 ↠[ ≤-refl ]
        (map-f snd′ ↠[ ≤-refl ] root)))))

flat : Flattener {Γ = Γ₂} κ₀ (Store.π S) {t = natᵗ} (EvalSt.nodes stP) (EvalSt.nodes stI) natᵗ (mergeᶠ nothing) 0 0 1 []
flat = here refl , _ , _ , refl , refl , merge~ [] , cell , refl

related : PathRel {Γ = Γ₂} κ₀ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
related = inner~ refl flat (there (here refl)) (inner~ refl flat (there (there (here refl))) root~)

-- the impl's frame at the empty telescope, and its restamp
ρ′ : Env Γ′ (uniqᵗ ∷ [])
ρ′ = 0 ∷ᵉ []ᵉ

stamp : FnClo Γ′ (emitᵗ natᵗ) (emitᵗ natᵗ)
stamp = uniqᵗ ∷ [] , renTm (λ x → x) (λ x → x) (ext∈ (λ x → x))
                       (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ [])) subscribeᵛ (varᵗ (here refl))) , ρ′

-- each side reads the share, connected already, so the read is one row
-- joining it
dP : subscribeE⇓ {e = ep} ([] , input (suc zero) , []ᵉ) p 0 sP stP _
dP = subs-shared {below = s≤s (s≤s z≤n)} refl (slot-join refl refl refl)

dI : subscribeE⇓ {e = ei} (uniqᵗ ∷ [] , input (2 ↑ʳ suc zero) , ρ′) (map-f stamp ↠[ ≤-refl ] q) 0 sI stI _
dI = subs-shared {below = s≤s (s≤s (s≤s (s≤s z≤n)))} refl (slot-join refl refl refl)

i : Fin 2
i = suc zero

SharedRead : Set
SharedRead =
  ∀ {Θ Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel {Γ = Γ₂} κ₀ Θ w ρ′ ρ
  → (eq : lookup Γ′ (2 ↑ʳ i) ≡ emitᵗ (lookup Γ₂ i))
  → ∀ {lo lo′} {p : Path Γ₂ lo (lookup Γ₂ i) natᵗ} {q : Path Γ′ lo′ (emitᵗ (lookup Γ₂ i)) (emitᵗ natᵗ)} {now}
      {sP : Sched Γ₂} {stP : EvalSt ep} {sI : Sched Γ′} {stI : EvalSt ei} {rP rI}
  → (S : Store {Γ = Γ₂} κ₀ sP stP sI stI)
  → PathRel {Γ = Γ₂} κ₀ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
  → subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP
  → subscribeE⇓ {e = ei} (Θ′ , input (2 ↑ʳ i) , ρ′)
      (subst (λ u → Path Γ′ lo′ u (emitᵗ natᵗ)) (sym eq)
        (map-f (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w)
                       (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ Θ)) subscribeᵛ (varᵗ (here refl))) , ρ′) ↠[ ≤-refl ] q))
      now sI stI rI
  → Σ (After {Γ = Γ₂} κ₀ S rP rI) λ A
      → PathRel {Γ = Γ₂} κ₀ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

-- the read's row passes the merge twice, and the rule after the read
-- holds of every row
shared-read-needs-sound : ¬ SharedRead
shared-read-needs-sound SR =
  proj₁ (distinct-rows (Store.ruleP (After.store (proj₁ (SR (λ x → x) (λ ()) refl S related dP dI)))) (here refl)) 0 tt tt
