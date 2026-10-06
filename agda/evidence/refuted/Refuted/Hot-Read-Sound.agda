-- `hot-read` WITHOUT `Sound` OF ITS PATHS IS FALSE.  `Store` and
-- `PathRel` say every frame of the two paths is related and say nothing
-- about the plain path's nodes being distinct, so a path may pass one
-- merge twice, as two of its lanes.  A read of a live hot registers the
-- path as a row, which `Rule.distinct-rows` refuses; the store `After`
-- hands back must carry that rule.
--
-- THE STATES ARE BUILT, NOT REACHED, and that is the claim: the
-- hypotheses `hot-read` takes admit them.
module Refuted.Hot-Read-Sound where

open import Data.Bool using (true; false; T)
open import Data.Fin using (Fin; zero; suc; _↑ʳ_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Vec using (lookup)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Closed; Val; Env; FnClo; obs; listᵗ; _×ᵗ_; _+ᵗ_; unitᵗ; mergeᶠ; natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_; sndᵗ; varᵗ; inrᵗ; inlᵗ; pairᵗ; unit̂; renTm; Ren∈; ext∈; input)
open import Rx.Mint using (setAt; nodeᵏ; regᵏ)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; RegRow; atSlot; frameNodes; pathHasNode; root; share-sink; map-f; scan-f; from-inner; thru-outer;
  batchSync-f; batchSync-st; echoᵗ; _↠[_]_;
  sched-init; st-init; mergeAll-st; cell-st; mergeAllᵒ)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-shared; subs-hot-live; slot-join)
open import Rx.Evaluator.Reducible.Support using (rule; distinct-rows; Apart)
open import SExp.Syntax using (Kinds; plainᵏ; emitᵗ; inputˢ; emptyˢ)
open import SExp.Plain using (plainExp)
open import SExp.Elaborate using (flatStepᵛ; FlatSᵗ; plainᶜ⁺; frameᵛ; restampᵛ; subscribeᵛ; inputStampᵖ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Stores using (Store; PathRel; Flattener; EnvRel; hotEq; inner~; root~; merge~; mach; hot~; block; [])
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
-- both sides, one merge, and the impl's flattener cell.  The impl's hot
-- share is connected too, its raw row the input block over the hot
sP : Sched Γ₂
sP = record (sched-init ep (plainSlots ins)) { mint = setAt nodeᵏ 3 (Sched.mint (sched-init ep (plainSlots ins))) ; live = [] }

stP : EvalSt ep
stP = record (st-init ep) { nodes = (0 , mergeAll-st {t = natᵗ} nothing 0 [] false) ∷ [] ; connectedShares = 1 ∷ [] }

sI : Sched Γ′
sI = record (sched-init ei (embedSlotsImpl ins)) { mint = setAt nodeᵏ 8 (setAt regᵏ 1 (Sched.mint (sched-init ei (embedSlotsImpl ins)))) ; live = [] }

cell : Val Γ′ (FlatSᵗ natᵗ)
cell = (0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)

-- the hot's input block: the marked merge and its lane, the bracket, the
-- stamp, and the merge that flattens the stamped emits into the sink
Fi : FnClo Γ′ natᵗ (unitᵗ +ᵗ natᵗ)
Fi = [] , inrᵗ (varᵗ (here refl)) , []ᵉ

Fs : FnClo Γ′ ((unitᵗ +ᵗ natᵗ) ×ᵗ listᵗ (unitᵗ +ᵗ natᵗ)) (obs (emitᵗ natᵗ))
Fs = uniqᵗ ∷ uniqᵗ ∷ [] , inputStampᵖ (varᵗ (here refl)) , 0 ∷ᵉ 0 ∷ᵉ []ᵉ

Fp : FnClo Γ′ (obs (emitᵗ natᵗ)) (echoᵗ (emitᵗ natᵗ))
Fp = [] , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , []ᵉ

sink : Path Γ′ 1 (emitᵗ natᵗ) (emitᵗ natᵗ)
sink = subst (λ u → Path Γ′ 1 u (emitᵗ natᵗ)) (hotEq {Γ = Γ₂} κ₀ zero refl) (share-sink (2 ↑ʳ zero) (s≤s z≤n))

k₆ : Path Γ′ 1 (echoᵗ (emitᵗ natᵗ)) (emitᵗ natᵗ)
k₆ = thru-outer mergeAllᵒ 6 ↠[ ≤-refl ] sink

k₅ : Path Γ′ 1 (obs (emitᵗ natᵗ)) (emitᵗ natᵗ)
k₅ = map-f Fp ↠[ ≤-refl ] k₆

k₄ : Path Γ′ 1 ((unitᵗ +ᵗ natᵗ) ×ᵗ listᵗ (unitᵗ +ᵗ natᵗ)) (emitᵗ natᵗ)
k₄ = map-f Fs ↠[ ≤-refl ] k₅

k₃ : Path Γ′ 1 (unitᵗ +ᵗ natᵗ) (emitᵗ natᵗ)
k₃ = batchSync-f 5 ↠[ ≤-refl ] k₄

k₂ : Path Γ′ 1 (unitᵗ +ᵗ natᵗ) (emitᵗ natᵗ)
k₂ = from-inner mergeAllᵒ 4 7 ↠[ ≤-refl ] k₃

full : Path Γ′ 1 natᵗ (emitᵗ natᵗ)
full = map-f Fi ↠[ ≤-refl ] k₂

raw : RegRow Γ′ (emitᵗ natᵗ)
raw = 0 , atSlot zero , (natᵗ , full)

stI : EvalSt ei
stI = record (st-init ei)
  { nodes = (0 , mergeAll-st {t = emitᵗ natᵗ} nothing 0 [] false) ∷ (1 , cell-st {t = FlatSᵗ natᵗ} cell)
          ∷ (4 , mergeAll-st {t = unitᵗ +ᵗ natᵗ} nothing 1 [] true) ∷ (5 , batchSync-st {s = unitᵗ +ᵗ natᵗ} false [] false)
          ∷ (6 , mergeAll-st {t = emitᵗ natᵗ} nothing 0 [] false) ∷ []
  ; registry = raw ∷ []
  ; connectedShares = 2 ∷ 3 ∷ [] }

-- a node listed is the one asked about
spot : ∀ {k} (P : ℕ → Set) (xs : List ℕ) → All P xs → T (any (_≡ᵇ k) xs) → P k
spot {k} P (x ∷ xs) (px ∷ ps) t with x ≡ᵇ k in e
... | true  = subst P (≡ᵇ⇒≡ x k (subst T (sym e) tt)) px
... | false = spot P xs ps t

Nodes : ∀ {lo s u} → (ℕ → Set) → Path Γ′ lo s u → Set
Nodes P root             = ⊤
Nodes P (share-sink _ _) = ⊤
Nodes P (f ↠[ _ ] κ)     = All P (frameNodes f) × Nodes P κ

has : ∀ {k lo s u} (P : ℕ → Set) (κ : Path Γ′ lo s u) → Nodes P κ → T (pathHasNode k κ) → P k
has P root             _         ()
has P (share-sink _ _) _         ()
has {k} P (f ↠[ _ ] κ) (pf , pκ) t with any (_≡ᵇ k) (frameNodes f) in e
... | true  = spot P (frameNodes f) pf (subst T (sym e) tt)
... | false = has P κ pκ t

apart : ∀ {lo s u v} (f : Frame Γ′ v s) (κ : Path Γ′ lo s u) → All (λ k → T (pathHasNode k κ) → ⊥) (frameNodes f) → Apart κ f
apart f κ ps k a = spot (λ k → T (pathHasNode k κ) → ⊥) (frameNodes f) ps a

-- the block's nodes are π's strangers
U : ∀ {k} → k ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) → 4 ≤ k → ⊥
U (here refl) ()
U (there (here refl)) (s≤s ())
U (there (there (here refl))) (s≤s (s≤s ()))
U (there (there (there (here refl)))) (s≤s (s≤s (s≤s ())))
U (there (there (there (there ())))) _

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
  ; rows    = mach (hot~ refl (block {m1 = 4} {j1 = 7} {b = 5} {m2 = 6} refl (s≤s z≤n) refl refl (λ m → U m (s≤s (s≤s (s≤s (s≤s z≤n))))) (λ m → U m (s≤s (s≤s (s≤s (s≤s z≤n))))) (λ m → U m (s≤s (s≤s (s≤s (s≤s z≤n))))) (λ m → U m (s≤s (s≤s (s≤s (s≤s z≤n)))))) refl) []
  ; dlv-alike = tt
  ; dying-alike = tt
  ; latches = λ { zero → (λ _ → refl , refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; bounded = [] , []
  ; swept   = []
  ; uncut   = [] , (refl ∷ [])
  ; rids    = [] , ([] ∷ [])
  ; fresh-ids = [] , (s≤s z≤n ∷ [])
  ; above   = [] , (refl ∷ [])
  ; census  = λ { zero _ → inj₁ (refl , refl) ; (suc zero) () }
  ; owned   = (λ _ _ → (λ _ → refl) ∷ []) ∷ []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ { k (here refl) (here refl) _ _ → refl })
                     (λ { (here refl) k t → has (_< 8) full ([] , (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) ∷ []) , (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) ∷ []) , [] , [] , (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) ∷ []) , _) t })
                     (λ { (here refl) → apart (map-f Fi) k₂ [] , apart (from-inner mergeAllᵒ 4 7) k₃ ((λ ()) ∷ (λ ()) ∷ [])
                                        , apart (batchSync-f 5) k₄ ((λ ()) ∷ []) , apart (map-f Fs) k₅ [] , apart (map-f Fp) k₆ []
                                        , apart (thru-outer mergeAllᵒ 6) sink ((λ ()) ∷ []) , _ })
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

-- the plain read registers at the live hot; the impl's joins the share
-- wrapping it
dP : subscribeE⇓ {e = ep} ([] , input zero , []ᵉ) p 0 sP stP _
dP = subs-hot-live (s≤s z≤n) refl refl refl

dI : subscribeE⇓ {e = ei} (uniqᵗ ∷ [] , input (2 ↑ʳ zero) , ρ′) (map-f stamp ↠[ ≤-refl ] q) 0 sI stI _
dI = subs-shared {below = s≤s (s≤s (s≤s z≤n))} refl (slot-join refl refl refl)

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
hot-read-needs-sound : ¬ HotRead
hot-read-needs-sound SR =
  proj₁ (distinct-rows (Store.ruleP (After.store (proj₁ (SR (λ x → x) (λ ()) refl S related dP dI)))) (here refl)) 0 tt tt
