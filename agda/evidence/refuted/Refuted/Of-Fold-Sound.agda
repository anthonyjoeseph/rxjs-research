-- `of-fold` WITHOUT `Sound` OF ITS PATHS IS FALSE.  `Store` and
-- `PathRel` say every frame of the two paths is related and say nothing
-- about the plain path's nodes being distinct, so a path may pass one
-- merge twice: as the outer, then as one of its own lanes.  An outer
-- emit through it subscribes a new lane, and the lane's row is the new
-- inner frame over the rest of the path, which passes that merge again.
-- The registry after the fold then holds a row `Rule.distinct-rows`
-- refuses, and the store `After` hands back must carry that rule.
--
-- THE STATES ARE BUILT, NOT REACHED, and that is the claim: the
-- hypotheses `of-fold` takes admit them.
module Refuted.Of-Fold-Sound where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Closed; Val; obs; FnClo; _×ᵗ_; mergeᶠ; natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_; sndᵗ; varᵗ; renExp; applyClo)
open import Rx.Mint using (setAt; nodeᵏ; sourceᵏ; freshId)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; map-f; scan-f; thru-outer; from-inner; _↠[_]_;
  sched-init; st-init; mergeAll-st; cell-st; mergeAllᵒ; echoᵗ)
open import Rx.Evaluator.Domain using (foldPath⇓; fold-root; fold-step; step-map; step-scan; step-thru-outer;
  step-from-inner; react-false; walk-cons; walk-echo; walk-nil; consume-all-sub; inner; subs-shared; subs-map; slot-join)
open import Rx.Evaluator.Reducible.Support using (rule; distinct-rows)
open import SExp.Syntax using (SExp; Kinds; plainᵏ; emitᵗ; inputˢ; emptyˢ)
open import SExp.Plain using (plainExp)
open import SExp.Elaborate using (toInstEmit; elemᵛ; flatStepᵛ; FlatSᵗ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Stores using (Store; PathRel; Flattener; outerElem~; inner~; root~; merge~; elab; [])
open import Simulation.Schedules using ([])
open import Simulation.After using (module Kept)
open Kept using (After; module After)
open import Simulation.Arm using (module Arms)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots)
open import Rx.Prim using (hot)

κ₀ : Kinds 2
κ₀ = κOf (hot [])

ins : SimulSlots Γ₂ κ₀
ins = mkSlots (hot []) emptyˢ

open Arms {Γ = Γ₂} κ₀ using (Carries; one; [])

Γ′ = plainᵏ Γ₂ κ₀

ep : Closed Γ₂ natᵗ
ep = plainExp (inputˢ zero)

ei : Closed Γ′ (emitᵗ natᵗ)
ei = elaborateImpl {Γ = Γ₂} κ₀ (inputˢ zero)

-- the two runs before the fold: no source live, the share connected on
-- both sides, one merge with no lane taken, and the impl's restamp cell
sP : Sched Γ₂
sP = record (sched-init ep (plainSlots ins)) { mint = setAt nodeᵏ 2 (Sched.mint (sched-init ep (plainSlots ins))) ; live = [] }

stP : EvalSt ep
stP = record (st-init ep) { nodes = (0 , mergeAll-st {t = natᵗ} nothing 0 [] false) ∷ [] ; connectedShares = 1 ∷ [] }

sI : Sched Γ′
sI = record (sched-init ei (embedSlotsImpl ins)) { mint = setAt nodeᵏ 3 (Sched.mint (sched-init ei (embedSlotsImpl ins))) ; live = [] }

cell : Val Γ′ (FlatSᵗ natᵗ)
cell = (0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)

stI : EvalSt ei
stI = record (st-init ei) { nodes = (0 , mergeAll-st {t = emitᵗ natᵗ} nothing 0 [] false) ∷ (1 , cell-st {t = FlatSᵗ natᵗ} cell) ∷ []
                          ; connectedShares = 3 ∷ [] }

S : Store {Γ = Γ₂} κ₀ sP stP sI stI
S = record
  { π       = (0 , 0 ∷ 1 ∷ []) ∷ (1 , 2 ∷ []) ∷ []
  ; π-keys  = ((λ ()) ∷ []) ∷ [] ∷ []
  ; π-vals  = ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ [] ∷ []
  ; pairs-below = (s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []) , ((s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []) ∷ (s≤s (s≤s (s≤s z≤n)) ∷ []) ∷ [])
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
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ { zero _ → inj₂ (refl , refl , λ ()) ; (suc zero) () }
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = ins , refl , refl
  }

-- THE PATH PASSES ITS MERGE TWICE: as the outer, then as one of its own
-- lanes.  Every frame is related, and `PathRel` asks nothing more.
p : Path Γ₂ 2 (echoᵗ natᵗ) natᵗ
p = thru-outer mergeAllᵒ 0 ↠[ ≤-refl ] (from-inner mergeAllᵒ 0 1 ↠[ ≤-refl ] root)

snd′ : FnClo Γ′ (FlatSᵗ natᵗ) (emitᵗ natᵗ)
snd′ = [] , sndᵗ (varᵗ (here refl)) , []ᵉ

flat′ : FnClo Γ′ (FlatSᵗ natᵗ ×ᵗ emitᵗ natᵗ) (FlatSᵗ natᵗ)
flat′ = [] , flatStepᵛ , []ᵉ

-- the path below the impl's outer frame
restq : Path Γ′ 4 (emitᵗ natᵗ) (emitᵗ natᵗ)
restq = scan-f flat′ 1 ↠[ ≤-refl ]
        (map-f snd′ ↠[ ≤-refl ]
         (from-inner mergeAllᵒ 0 2 ↠[ ≤-refl ]
          (scan-f flat′ 1 ↠[ ≤-refl ]
           (map-f snd′ ↠[ ≤-refl ] root))))

q : Path Γ′ 4 (emitᵗ (echoᵗ natᵗ)) (emitᵗ natᵗ)
q = map-f ([] , elemᵛ , []ᵉ) ↠[ ≤-refl ] (thru-outer mergeAllᵒ 0 ↠[ ≤-refl ] restq)

flat : Flattener {Γ = Γ₂} κ₀ (Store.π S) {t = natᵗ} (EvalSt.nodes stP) (EvalSt.nodes stI) natᵗ (mergeᶠ nothing) 0 0 1 []
flat = here refl , _ , _ , refl , refl , merge~ [] , cell , refl

related : PathRel {Γ = Γ₂} κ₀ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
related = outerElem~ flat (inner~ refl flat (there (here refl)) root~)

-- the merge's outer emits one observable, the share
sh : SExp Γ₂ [] [] [] natᵗ
sh = inputˢ (suc zero)

oP : Val Γ₂ (obs natᵗ)
oP = [] , plainExp sh , []ᵉ

oI : Val Γ′ (obs (emitᵗ natᵗ))
oI = uniqᵗ ∷ [] , renExp (λ x → x) (λ x → x) (λ x → x) (toInstEmit κ₀ sh) , 0 ∷ᵉ []ᵉ

vs : List (Val Γ₂ (echoᵗ natᵗ))
vs = (inj₁ tt , inj₂ oP) ∷ []

e′ : Val Γ′ (emitᵗ (echoᵗ natᵗ))
e′ = inj₂ (inj₁ (inj₁ tt , inj₂ oI)) ∷ [] , 0 , 0 , inj₁ tt

car : Carries {echoᵗ natᵗ} (e′ ∷ []) vs
car = one e′ ((refl , elab sh (λ x → x) (λ ())) ∷ []) []

-- each side subscribes the share as one more lane of the merge, and the
-- share is connected already, so the lane is one row joining it
dP : foldPath⇓ 0 p vs true sP stP _
dP = fold-step (step-thru-outer
       (walk-cons (consume-all-sub refl refl (inner refl (subs-shared {below = s≤s (s≤s z≤n)} refl (slot-join refl refl refl))))
        walk-nil))
     (fold-step (step-from-inner react-false) fold-root)

sI′ : Sched Γ′
sI′ = record sI { mint = setAt sourceᵏ (suc (freshId sourceᵏ (Sched.mint sI))) (Sched.mint sI) }

-- THE IMPL'S FOLD IS CHECKED OVER ITS ECHO AS A VARIABLE: the element
-- carries the outer emit's echo, empty, ahead of its lane, nothing
-- downstream inspects it, and at the concrete value the check runs out
-- of memory
module Tail (v : Val Γ′ (emitᵗ natᵗ)) where
  tail : Σ _ λ r → foldPath⇓ 0 (thru-outer mergeAllᵒ 0 ↠[ ≤-refl ] restq) ((inj₂ v , inj₂ oI) ∷ []) true sI′ stI r
  tail = _ , fold-step (step-thru-outer
       (walk-echo (fold-step step-scan (fold-step step-map (fold-step (step-from-inner react-false) (fold-step step-scan (fold-step step-map fold-root)))))
       (walk-cons (consume-all-sub refl refl (inner refl (subs-map (subs-shared {below = s≤s (s≤s (s≤s (s≤s z≤n)))} refl (slot-join refl refl refl))))) walk-nil)))
     (fold-step step-scan (fold-step step-map
     (fold-step (step-from-inner react-false)
     (fold-step step-scan (fold-step step-map fold-root)))))

echoOf : List (Val Γ′ (echoᵗ (emitᵗ natᵗ))) → Val Γ′ (emitᵗ natᵗ)
echoOf ((inj₂ v , _) ∷ _) = v
echoOf _                  = [] , 0 , 0 , inj₁ tt

dI : Σ _ (foldPath⇓ 0 q (e′ ∷ []) true sI′ stI)
dI = _ , fold-step step-map (proj₂ (Tail.tail (echoOf (map (applyClo ([] , elemᵛ , []ᵉ)) (e′ ∷ [])))))

OfFold : Set
OfFold = ∀ {u lo lo′} {p : Path Γ₂ lo u natᵗ} {q : Path Γ′ lo′ (emitᵗ u) (emitᵗ natᵗ)} {now}
           {sP : Sched Γ₂} {stP : EvalSt ep} {sI : Sched Γ′} {stI : EvalSt ei} {rP rI src es vs}
       → (S : Store {Γ = Γ₂} κ₀ sP stP sI stI)
       → PathRel {Γ = Γ₂} κ₀ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
       → freshId sourceᵏ (Sched.mint sI) ≡ src
       → Carries {u} es vs
       → foldPath⇓ now p vs true sP stP rP
       → foldPath⇓ now q es true (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) stI rI
       → Σ (After {Γ = Γ₂} κ₀ S rP rI) λ A
           → PathRel {Γ = Γ₂} κ₀ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

-- the lane's row passes the merge twice, and the rule after the fold
-- holds of every row
of-fold-needs-sound : ¬ OfFold
of-fold-needs-sound OF =
  proj₁ (distinct-rows (Store.ruleP (After.store (proj₁ (OF S related refl car dP (proj₂ dI))))) (here refl)) 0 tt tt
