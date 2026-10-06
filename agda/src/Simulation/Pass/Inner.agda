------------------------------------------------------------------
-- AN INNER'S ARMS: the pass's type, the leaves per plain frame, and
-- an inner's step by the rule its react takes, over the quiet arms
------------------------------------------------------------------
module Simulation.Pass.Inner where

open import Data.Bool    using (true; false; not; _∧_; _∨_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (nothing; just)
open import Data.Nat     using (suc; _≤_; _≡ᵇ_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec     using (lookup)
open import Data.List.Properties using (map-id; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)

open import Rx.Exp       using (Ctx; Closed; Val; mergeᶠ; switchᶠ; exhaustᶠ; uniqᵗ; obs; applyClo; Tm; varᵗ; unit̂; pairᵗ;
  inlᵗ; inrᵗ; sndᵗ)
open import Rx.Evaluator using (EvalSt; NodeId; shareSpend; shareDying; Path; _↠[_]_; scan-f; map-f; thru-outer; from-inner;
  mergeAllᵒ; lookupNode; echoᵗ; thruEvents; thruWrap; switchᵒ; exhaustᵒ; RegId; AtFloor;
  shareFinish; aliveThroughᶠ; Sched; pathHasNode; mergeAll-st; cell-st)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-step; stepFrame⇓; step-map; step-thru-outer; step-from-inner;
  react-false; react-alive; react-dead; innerFinish⇓; finish-switch-clear;
  finish-exhaust-clear; finish-nil; thruWalk⇓; thruConsume⇓; walk-nil; walk-echo; walk-cons)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ; hotᵏ; sharedᵏ)
open import SExp.Elaborate using (restampᵛ; subscribeᵛ; deliveryᵛ; flatStepᵛ; explodeᵛ)
open import Simulation.Stores using (EmitRel; Flattener; FlatNodes; switch~; exhaust~; sharedEq; PathRel; inner~;
  deferInner~; []; _∷_; Store; Partners; RegRel; RowRel; MachRow; mach; Spent; dlvᵇ; dyingᵇ)
open import Simulation.Cut using (module At; module Third)
open import Simulation.After using (module Kept)
open import Simulation.Take using (module Takes)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (Clear; missed; fold-unmoved; on-drop; unthru; step-clear; consume-clear; reclear; thru)
open import Simulation.Sweep using (t≢f)
open import Rx.Evaluator.Reducible.Support using (Sound; drop-ot; head-on; self-node)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; Thru; thruWalk-rule)
open import Simulation.Pass.Quiet using (module PassQ; ShareSlot; SlotPair; cur-here; cur-there; delivered; delivered-arr; dying; dying-arr; slotpair; tail-of)

-- A WALK OVER TWO RUNS OF EVENTS IS THE FIRST WALK, THEN THE SECOND
-- from where it left the state
walk-split : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {w lo op nid} {κ : Path Δ lo w u} {now} xs ys {sched st r}
           → thruWalk⇓ {e = e} op nid κ now (xs ++ ys) sched st r
           → Σ _ λ r₁ → thruWalk⇓ op nid κ now xs sched st r₁
               × Σ _ λ r₂ → thruWalk⇓ op nid κ now ys (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) r₂
               × r ≡ (proj₁ r₁ ++ proj₁ r₂ , proj₂ r₂)
walk-split [] ys W = _ , walk-nil , _ , W , refl
walk-split (inj₁ v ∷ xs) ys (walk-echo {out₁ = o} F W) with walk-split xs ys W
... | r₁ , W₁ , r₂ , W₂ , refl = _ , walk-echo F W₁ , _ , W₂ , cong (_, proj₂ r₂) (sym (++-assoc o (proj₁ r₁) (proj₁ r₂)))
walk-split (inj₂ x ∷ xs) ys (walk-cons {out₁ = o} C W) with walk-split xs ys W
... | r₁ , W₁ , r₂ , W₂ , refl = _ , walk-cons C W₁ , _ , W₂ , cong (_, proj₂ r₂) (sym (++-assoc o (proj₁ r₁) (proj₁ r₂)))

-- an echo's events, ahead of the rest
events-cons : ∀ {m} {Δ : Ctx m} {u} (x : Val Δ (echoᵗ u)) xs → thruEvents (x ∷ xs) ≡ thruEvents (x ∷ []) ++ thruEvents xs
events-cons (inj₁ _ , inj₁ _) xs = refl
events-cons (inj₁ _ , inj₂ _) xs = refl
events-cons (inj₂ _ , inj₁ _) xs = refl
events-cons (inj₂ _ , inj₂ _) xs = refl

walk-head : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {w lo op nid} {κ : Path Δ lo w u} {now} (x : Val Δ (echoᵗ w)) xs {sched st r}
          → thruWalk⇓ {e = e} op nid κ now (thruEvents (x ∷ xs)) sched st r
          → Σ _ λ r₁ → thruWalk⇓ op nid κ now (thruEvents (x ∷ [])) sched st r₁
              × Σ _ λ r₂ → thruWalk⇓ op nid κ now (thruEvents xs) (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) r₂
              × r ≡ (proj₁ r₁ ++ proj₁ r₂ , proj₂ r₂)
walk-head x xs W = walk-split (thruEvents (x ∷ [])) (thruEvents xs) (subst (λ ys → thruWalk⇓ _ _ _ _ ys _ _ _) (events-cons x xs) W)

-- AN EMIT'S RELATION NEVER READS ITS INSTANT: retagging every value's
-- instant keeps the values related
retag : ∀ {I A B : Set} {R : I × A → B → Set} {i j : I} {xs : List A} {ws : List B}
      → (∀ {x w} → R (i , x) w → R (j , x) w)
      → Pointwise R (map (i ,_) xs) ws → Pointwise R (map (j ,_) xs) ws
retag {xs = []}     f []       = []
retag {xs = _ ∷ _} f (r ∷ rs) = f r ∷ retag f rs

-- a walk through a flattener keeps its node off the path below it
walk-clear : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo w} {k} {κ : Path Δ lo w u} {op now xs}
               {sched sched′ st st′ out}
           → thruWalk⇓ {e = e} op k κ now xs sched st (out , sched′ , st′)
           → Clear k κ sched st → Clear k κ sched′ st′
walk-clear {e = e} {k = k} {κ = κ} d c = reclear {π = Thru {e = e} k κ} refl c (thruWalk-rule d (thru c))

module PassI {n} {Γ : Ctx n} (κ : Kinds n) where

  open PassQ {Γ = Γ} κ public
  open Takes {Γ = Γ} κ using (module While)
  open Scans {Γ = Γ} κ using (module Cells)

  module InI {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open InQ {t} {ep} {ei} public
    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open While {t} {ep} {ei} using (takeWhile-arm)
    open Cells {t} {ep} {ei} using (scan-arm)

    -- TWO RELATED PATHS KEEP THE PASS, AND ARE RELATED AGAIN WHERE IT
    -- LEAVES THEM: a flattener's outer folds its tail once per emit
    Pass : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Pass p q =
      ∀ {now vs es fin sP stP sI stI rP rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es vs
      → Sound p sP stP → Sound q sI stI
      → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now q es fin sI stI rI
      → Σ (After S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q


    -- ONE LEAF PER PLAIN FRAME A CONSTRUCTOR STARTS WITH.  An outer's
    -- two constructors and an inner's three are split once their arm is
    -- the riskiest.
    postulate
      -- A SHARE CLOSED ON BOTH SIDES, before its end is delivered
      share-spend  : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} → lookup κ i ≡ sharedᵏ
                   → After S ([] , sP , shareSpend i stP) ([] , sI , shareSpend (n ↑ʳ i) stI)
      -- A SHARE'S READERS DROPPED ON BOTH SIDES, once its end is delivered
      share-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} → lookup κ i ≡ sharedᵏ
                   → After S ([] , proj₂ (shareFinish i true ([] , sP , stP))) ([] , proj₂ (shareFinish (n ↑ʳ i) true ([] , sI , stI)))
      -- AN OUTER'S EMIT CARRYING NOTHING, EXPLODED: the impl's merge
      -- subscribes its empty run of elements, and the plain side does not
      -- move
      explode-quiet : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                      {rI}
                  → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                  → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                  → ∀ e′ → Bare {echoᵗ u} e′
                  → thruConsume⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                      (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI stI rI
                  → Σ (After S ([] , sP , stP) rI) λ A
                      → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                          u op m m′ ks (mX ∷ [])
                        × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
      -- AN OUTER'S EMIT CARRYING ONE VALUE, EXPLODED: the impl's merge
      -- subscribes its run of elements, and they walk into the flattener
      -- where the plain outer's walk hands the value's events on
      explode-one : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                      {rP rI}
                  → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                  → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                  → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                  → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP
                  → thruConsume⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                      (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI stI rI
                  → Σ (After S rP rI) λ A
                      → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                          u op m m′ ks (mX ∷ [])
                        × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
      -- THE EXPLODED OUTER'S END: the impl's merge ends where the plain
      -- outer does, and the flattener's end follows on both sides
      explode-end : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r}
                  → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
                  → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                  → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP′) (EvalSt.nodes stI′) u op m m′ ks (mX ∷ [])
                    × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI′) p q
                  → Sound (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)
                      (proj₁ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′))))
                  → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) []
                      (proj₁ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))
                      (proj₁ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) r
                  → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                      (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                      p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                      (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                         (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                          (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                           (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                            (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))))
                      (oI ++ proj₁ r , proj₂ r)
      -- A MERGE'S INNER ENDED ON BOTH SIDES: each finish folds the group
      -- down its tail, then drains the queue its node holds, and the
      -- related nodes hold related queues
      merge-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u lim m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                       {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                   → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u (mergeᶠ lim) m m′ ks xs
                   → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Carries es vs
                   → Sound (from-inner mergeAllᵒ m j ↠[ h ] p) sP stP
                   → Sound (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI
                   → innerFinish⇓ mergeAllᵒ m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
                   → innerFinish⇓ mergeAllᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (lookupNode m′ (EvalSt.nodes stI))
                       (o₁ , es₁ , f₁ , sI₁ , stI₁)
                   → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
                   → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                       (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ m j ↠[ h ] p)
                          (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
      -- A DEAD DEFERRED BODY FINISHES ON BOTH SIDES: the plain merge's
      -- finish, against the hop's marker merge's and the restamp and hop
      -- node the group then reaches
      defer-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                       {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                       (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                        (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                         (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
                   → Carries es vs
                   → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
                   → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                            (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                             (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
                   → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
                   → innerFinish⇓ mergeAllᵒ nid j p now vs sP stP (lookupNode nid (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
                   → innerFinish⇓ mergeAllᵒ m2 j2
                       (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                        (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)) now es sI stI (lookupNode m2 (EvalSt.nodes stI)) (o₁ , es₁ , f₁ , sI₁ , stI₁)
                   → foldPath⇓ now (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                       (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)) es₁ f₁ sI₁ stI₁ rI
                   → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                       (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                          (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                           (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                            (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) (o₁ ++ proj₁ rI , proj₂ rI)

    -- A DELIVERED EMIT CARRIES WHAT IT CARRIED: the hop's restamp
    -- retags a subscribe as a delivery over its own events
    delivery-rel : ∀ {u Θx ρ₀} e′ {ws}
                 → EmitRel {Γ = Γ} κ u e′ ws
                 → EmitRel {Γ = Γ} κ u (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) e′) ws
    delivery-rel (evs , i , s , inj₁ k) r = retag (λ q → q) r
    delivery-rel (evs , i , s , inj₂ k) r = r

    -- A PAIR OF NODES EVERY PAIR OF ROWS NAMES ALIKE, AND THE IMPL'S OWN
    -- ROWS NEVER THE IMPL ONE, HAS A CHAIN RUNNING THROUGH IT ON BOTH SIDES
    -- OR ON NEITHER: neither row of a pair is cancelled, and the two are
    -- delivered and dying alike
    alive-by : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′}
             → (∀ {x x′} → RowRel κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) x x′
                         → pathHasNode j (proj₂ (proj₂ (proj₂ x))) ≡ pathHasNode j′ (proj₂ (proj₂ (proj₂ x′))))
             → (∀ {x′} → MachRow κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) x′
                         → pathHasNode j′ (proj₂ (proj₂ (proj₂ x′))) ≡ false)
             → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j′ stI) (EvalSt.registry stI)
    alive-by {sP} {stP} {sI} {stI} S {j} {j′} rc mc = go rows (proj₁ uncut) (proj₂ uncut) dlv-alike dying-alike
      where
        open Store S

        off : ∀ {a} b c → a ≡ false → (a ∧ b) ∨ c ≡ c
        off b c refl = refl

        go : ∀ {rs rs′} (q : RegRel κ π {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) rs rs′)
           → All (λ r → any (_≡ᵇ proj₁ r) (EvalSt.cancelled stP) ≡ false) rs
           → All (λ r → any (_≡ᵇ proj₁ r) (EvalSt.cancelled stI) ≡ false) rs′
           → Spent κ π (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) q (dlvᵇ stP) (dlvᵇ stI)
           → Spent κ π (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) q (dyingᵇ stP) (dyingᵇ stI)
           → any (aliveThroughᶠ j stP) rs ≡ any (aliveThroughᶠ j′ stI) rs′
        go [] _ _ _ _ = refl
        go (rr ∷ q) (u ∷ us) (u′ ∷ us′) (d , ds) (y , ys) =
          cong₂ _∨_ (cong₂ _∧_ (rc rr) (cong₂ _∧_ (cong not (trans u (sym u′))) (cong₂ _∨_ (cong not y) (cong not d))))
                    (go q us us′ ds ys)
        go (mach m q) us (_ ∷ us′) ds ys = trans (go q us us′ ds ys) (sym (off _ _ (mc m)))

    -- AN INNER HAS A CHAIN RUNNING THROUGH IT ON THE PLAIN SIDE EXACTLY
    -- WHEN ITS PAIR DOES ON THE IMPL'S: a pair of rows names the pair of
    -- nodes alike, and the impl's own rows name no paired node
    inner-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′}
                → (j , j′ ∷ []) ∈ Store.π S
                → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j′ stI) (EvalSt.registry stI)
    inner-alive S ce = alive-by S (λ rr → C.row-cut rr) (λ m → C.mach-cut m)
      where module C = At {Γ = Γ} κ (Store.π-keys S) (Store.π-vals S) ce (here refl)

    -- A DEFERRED BODY'S INNER IS LIVE ON THE PLAIN SIDE EXACTLY WHEN THE
    -- HOP'S MARKER MERGE'S INNER IS ON THE IMPL'S: that inner is the third
    -- of the run `π` pairs the body's inner with, and the marker merge
    -- being a merge tells the run from an exploding flattener's
    defer-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′ m2 j2 u a}
                → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ Store.π S
                → lookupNode m2 (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
                → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j2 stI) (EvalSt.registry stI)
    defer-alive {stI = stI} S {m2 = m2} ce l2 = alive-by S (λ rr → D.row-cut ly rr) (λ m → D.mach-cut m)
      where
        module D = Third {Γ = Γ} κ (Store.π-keys S) (Store.π-vals S) ce
        ly : ∀ {w} {v : Val (plainᵏ Γ κ) w} → lookupNode m2 (EvalSt.nodes stI) ≢ just (cell-st v)
        ly lk with trans (sym l2) lk
        ... | ()

    -- AN INNER LEFT OPEN: the impl's lets the group past as the plain one
    -- does, its restamp moves the cell alone, and the tails are related
    inner-on : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {stP₁ stI₁ vs es fin rI}
             → (A₀ : After S ([] , sP , stP₁) ([] , sI , stI₁))
             → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ (Store.π (After.store A₀)) {t} (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) u op m m′ ks xs)
               × (j , j′ ∷ []) ∈ Store.π (After.store A₀) × PathRel κ (Store.π (After.store A₀)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
             → Carries es vs
             → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP₁
             → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI₁
             → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es fin sI stI₁ rI
             → Arm S now [] sP stP₁ p vs fin
                 (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                    (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) rI
    inner-on {m = m} {m′} {j = j} {j′} {stP₁ = stP₁} A₀ ((_ , f) , ip , pr) b sp si (fold-step d₁ (fold-step step-map dq))
      with restamp-echo (After.store A₀) f pr b d₁
    ... | A , f′ , pr′ , c′ , refl =
      arm (A₀ ⨾ A) pr′ c′ (proj₂ (proj₁ cI)) dq λ {rP} dP B rel′ →
        inner~ refl (flat-move (EvalSt.nodes stP₁) _ (EvalSt.nodes (proj₂ (proj₂ rP))) _ (After.grows B)
                       (missed dP (head-on _ _ _ m (self-node m (j ∷ [])) sp , drop-ot _ _ _ sp))
                       (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) f′)
               (After.grows B (After.grows A ip)) rel′
      where
      cI = tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))

    -- leaving an inner: the flattener's lane, then its restamp
    inner-pass : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
               → InnerPasses (flatOp op) m j h p
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-pass {op = op} S R b sp si _ (fold-step (step-from-inner react-false) dR) = inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) (leave op R) b sp si dR
    inner-pass {op = op} S R b sp si _ (fold-step (step-from-inner (react-alive _)) dR) = inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) (leave op R) b sp si dR
    inner-pass S R b sp si (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    inner-pass {op = op} S R b sp si (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (inner-alive S (proj₁ (proj₂ (leave op R))))) al)) dd))

    -- A SWITCH'S INNER ENDED: both sides clear their current inner and let
    -- the group on, or neither does -- `CurRel` pairs the two currents,
    -- so the dying inner is current on both sides or on neither
    switch-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
               → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u switchᶠ m m′ ks xs
               → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u switchᶠ x x′
               → Carries es vs
               → Sound (from-inner switchᵒ m j ↠[ h ] p) sP₁ stP₁
               → Sound (from-inner switchᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
               → innerFinish⇓ switchᵒ m j p now vs sP stP (just x) (oP , vs₁ , fin₁ , sP₁ , stP₁)
               → innerFinish⇓ switchᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′) (o₁ , es₁ , f₁ , sI₁ , stI₁)
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner switchᵒ m j ↠[ h ] p)
                     (from-inner switchᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
    switch-finish S f ip pr (switch~ _) b sp si (finish-switch-clear _) (finish-switch-clear _) dR =
      let W = flat-write S (f , pr) (switch~ tt) in inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , ip , proj₂ (proj₂ W)) b sp si dR
    switch-finish S f ip pr (switch~ {cur′ = nothing} ()) b sp si (finish-switch-clear _) (finish-nil _) dR
    switch-finish S f ip pr (switch~ {cur′ = just _} c) b sp si (finish-switch-clear e) (finish-nil e′) dR =
      ⊥-elim (t≢f (trans (sym (cur-here (Store.π-keys S) c ip e)) e′))
    switch-finish S f ip pr (switch~ {cur = nothing} ()) b sp si (finish-nil _) (finish-switch-clear _) dR
    switch-finish S f ip pr (switch~ {cur = just _} c) b sp si (finish-nil e) (finish-switch-clear e′) dR =
      ⊥-elim (t≢f (trans (sym (cur-there (Store.π-vals S) c ip e′)) e))
    switch-finish S f ip pr (switch~ _) b sp si (finish-nil _) (finish-nil _) dR =
      inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) ((_ , f) , ip , pr) b sp si dR

    -- AN EXHAUST'S INNER ENDED: both sides clear their lane and let the
    -- group on
    exhaust-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
               → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u exhaustᶠ m m′ ks xs
               → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u exhaustᶠ x x′
               → Carries es vs
               → Sound (from-inner exhaustᵒ m j ↠[ h ] p) sP₁ stP₁
               → Sound (from-inner exhaustᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
               → innerFinish⇓ exhaustᵒ m j p now vs sP stP (just x) (oP , vs₁ , fin₁ , sP₁ , stP₁)
               → innerFinish⇓ exhaustᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′) (o₁ , es₁ , f₁ , sI₁ , stI₁)
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner exhaustᵒ m j ↠[ h ] p)
                     (from-inner exhaustᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
    exhaust-finish S f ip pr exhaust~ b sp si finish-exhaust-clear finish-exhaust-clear dR =
      let W = flat-write S (f , pr) (exhaust~ {ia = false}) in inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , ip , proj₂ (proj₂ W)) b sp si dR
    exhaust-finish S f ip pr exhaust~ b sp si (finish-nil ()) _ dR
    exhaust-finish S f ip pr exhaust~ b sp si finish-exhaust-clear (finish-nil ()) dR

    -- AN INNER ENDED ON BOTH SIDES, by its flattener's operator
    finish-by : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                  {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
              → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs)
                × (j , j′ ∷ []) ∈ Store.π S × PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Carries es vs
              → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP
              → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI
              → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP₁ stP₁
              → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
              → innerFinish⇓ (flatOp op) m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁)
              → innerFinish⇓ (flatOp op) m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (lookupNode m′ (EvalSt.nodes stI))
                  (o₁ , es₁ , f₁ , sI₁ , stI₁)
              → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
              → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                  (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                     (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (o₁ ++ proj₁ rI , proj₂ rI)
    finish-by S {op = mergeᶠ _} ((_ , f) , ip , pr) b sp si _ _ F F′ dR = merge-finish S f ip pr b sp si F F′ dR
    finish-by S {op = switchᶠ} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b _ _ sp si F F′ dR =
      switch-finish S f ip pr fn b sp si (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lP F)
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR
    finish-by S {op = exhaustᶠ} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b _ _ sp si F F′ dR =
      exhaust-finish S f ip pr fn b sp si (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lP F)
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR

    -- AN INNER NO LIVE CHAIN RUNS THROUGH: its pair is dead too, and
    -- both sides finish it
    inner-dies : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
               → InnerDies (flatOp op) m j h p
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-dies {op = op} S R b sp si dd F (fold-step (step-from-inner (react-alive al′)) _) =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (inner-alive S (proj₁ (proj₂ (leave op R))))) dd)))
    inner-dies {op = op} S R b sp si dd F (fold-step d′@(step-from-inner (react-dead _ F′)) dR) =
      finish-by S (leave op R) b sp si (step-kept _ (step-from-inner (react-dead dd F)) sp) (step-kept _ d′ si) F F′ dR

    -- A DEFERRED BODY NO LIVE CHAIN RUNS THROUGH: the hop's marker
    -- merge's inner is dead too, and both sides finish it
    deferInner-dies : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → InnerDies mergeAllᵒ nid j h p
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-dies S R@(deferInner~ _ ip₂ _ _ l2 _ _) b sp si dd F (fold-step (step-from-inner (react-alive al′)) _) =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (defer-alive S ip₂ l2)) dd)))
    deferInner-dies S R b sp si dd F (fold-step (step-from-inner (react-dead _ F′)) dR) = defer-finish S R b sp si dd F F′ dR

    delivery-carries : ∀ {u Θx ρ₀} {es vs}
                     → Carries {s = u} es vs
                     → Carries (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es) vs
    delivery-carries []              = []
    delivery-carries (quiet e′ r bs) = quiet _ (delivery-rel e′ r) (delivery-carries bs)
    delivery-carries (one e′ r bs)   = one _ (delivery-rel e′ r) (delivery-carries bs)

    -- A DEFERRED BODY'S INNER LEFT OPEN: the hop's marker merge and its
    -- node let the group past, and the restamp between moves no node
    defer-on : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {vs es rI}
             → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                 (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                  (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                   (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
             → Carries es vs
             → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
             → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                      (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                       (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
             → foldPath⇓ now q (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es)
                 false sI stI rI
             → Arm S now [] sP stP p vs false
                 (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                    (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                     (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                      (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) rI
    defer-on S {nid = nid} {nid′} {j} {j′} {m2} {j2} (deferInner~ ip₁ ip₂ lP lI l2 a1 pr) b sp si dq =
      arm (after S (λ x → x) (λ x → x) [] (λ x → x)) pr (delivery-carries b) s3 dq λ {rP} dP B rel′ →
        deferInner~ (After.grows B ip₁) (After.grows B ip₂) (trans (fold-unmoved dP cP) lP)
                    (trans (fold-unmoved dq c′) lI) (trans (fold-unmoved dq c2) l2) a1 rel′
      where
      s2 = drop-ot _ _ _ (drop-ot _ _ _ si)
      s3 = drop-ot _ _ _ s2
      cP = head-on _ _ _ nid (self-node nid (j ∷ [])) sp , drop-ot _ _ _ sp
      c′ = head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) s2 , s3
      c2 = on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) , s3

    -- a deferred body: the hop's marker merge, its restamp, the hop's node
    deferInner-pass : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → InnerPasses mergeAllᵒ nid j h p
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-pass S R b sp si _
      (fold-step (step-from-inner react-false) (fold-step step-map (fold-step (step-from-inner react-false) dq))) =
      defer-on S R b sp si dq
    deferInner-pass S R b sp si _
      (fold-step (step-from-inner (react-alive _)) (fold-step step-map (fold-step (step-from-inner react-false) dq))) =
      defer-on S R b sp si dq
    deferInner-pass S R b sp si (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    deferInner-pass S R@(deferInner~ _ ip₂ _ _ l2 _ _) b sp si (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (defer-alive S ip₂ l2)) al)) dd))

    -- AN OUTER'S ELEMENTS EXPLODED: each emit's run of elements is an
    -- inner the impl's merge subscribes, and its elements walk into the
    -- flattener where the plain outer's walk hands them on.  One emit at
    -- a time, in the order the impl walks them
    explode-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                     {es vs rP rI}
                 → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                 → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Carries {echoᵗ u} es vs
                 → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                 → thruWalk⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                     (thruEvents (map (applyClo {s = obs (echoᵗ (emitᵗ u))} {t = echoᵗ (echoᵗ (emitᵗ u))}
                                                (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅))
                                      (map (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀)) es))) sI stI rI
                 → Σ (After S rP rI) λ A
                     → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                         u op m m′ ks (mX ∷ [])
                       × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
    -- one emit carrying a value: the plain walk already split at it
    explode-cons : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                     {es vs rP rI r₁ r₂}
                 → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                 → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ []) → Carries {echoᵗ u} es vs
                 → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP r₁
                 → thruWalk⇓ (flatOp op) m p now (thruEvents vs) (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) r₂
                 → rP ≡ (proj₁ r₁ ++ proj₁ r₂ , proj₂ r₂)
                 → thruWalk⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                     (thruEvents (map (applyClo {s = obs (echoᵗ (emitᵗ u))} {t = echoᵗ (echoᵗ (emitᵗ u))}
                                                (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅))
                                      (map (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀)) (e′ ∷ es)))) sI stI rI
                 → Σ (After S rP rI) λ A
                     → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                         u op m m′ ks (mX ∷ [])
                       × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
    explode-walk S cp ci fl r [] walk-nil walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , fl , r
    explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                 cp ci fl r (quiet e′ bare b) W (walk-cons C W′) =
      let X = explode-quiet S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r e′ bare C
          Y = explode-walk (After.store (proj₁ X)) {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                cp (consume-clear C ci) (proj₁ (proj₂ X)) (proj₂ (proj₂ X)) b W W′
      in (proj₁ X ⨾ proj₁ Y) , proj₂ Y
    explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                 cp ci fl r (one e′ {w = w} {vs = vs} rel b) W WI =
      let H = walk-head w vs W
      in explode-cons S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
           cp ci fl r e′ rel b (proj₁ (proj₂ H)) (proj₁ (proj₂ (proj₂ (proj₂ H)))) (proj₂ (proj₂ (proj₂ (proj₂ H)))) WI
    explode-cons S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                 cp ci fl r e′ rel b W₁ W₂ refl (walk-cons C W′) =
      let X = explode-one S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r e′ rel W₁ C
          Y = explode-walk (After.store (proj₁ X)) {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                (walk-clear W₁ cp) (consume-clear C ci) (proj₁ (proj₂ X)) (proj₂ (proj₂ X)) b W₂ W′
      in (proj₁ X ⨾ proj₁ Y) , proj₂ Y

    -- an outer's elements, each inner a sync outer hands the flattener
    -- subscribed before the step returns: the explode and its merge
    outerExplode-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                         {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                         {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                         {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                         {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                     → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                       × PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                     → Carries {echoᵗ u} es vs
                     → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                     → Sound (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) sI stI
                     → stepFrame⇓ now (thru-outer (flatOp op) m) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                     → foldPath⇓ now (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) es fin sI stI rI
                     → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                         (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                            (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                             (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                              (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                               (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q))))) rI
    outerExplode-arm S {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} {fin = fin} (fl , r) b sp si dW@(step-thru-outer W)
                     (fold-step step-map (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR))) =
      let si′ = drop-ot _ _ _ (drop-ot _ _ _ si)
          X   = explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} (unthru sp) (unthru si′) fl r b W W′
      in explode-end {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} {fin = fin} (proj₁ X) (unthru (step-kept _ dW sp)) (proj₂ X)
           (drop-ot _ _ _ (step-kept _ dW′ si′)) dR

    -- AN INNER'S STEP, by the rule its react takes: open or alive, it
    -- passes the group on; dead, it finishes
    inner-arm     : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                  → Steps (from-inner (flatOp op) m j) h p
                      (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                       (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                        (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-arm {op = op} S R b sp si (step-from-inner react-false)        dI = inner-pass {op = op} S R b sp si (inj₁ refl) dI
    inner-arm {op = op} S R b sp si (step-from-inner (react-alive al))   dI = inner-pass {op = op} S R b sp si (inj₂ al) dI
    inner-arm {op = op} S R b sp si (step-from-inner (react-dead dd fz)) dI = inner-dies {op = op} S R b sp si dd fz dI

    deferInner-arm : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   → Steps (from-inner mergeAllᵒ nid j) h p
                       (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                        (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                         (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-arm S R b sp si (step-from-inner react-false)        dI = deferInner-pass S R b sp si (inj₁ refl) dI
    deferInner-arm S R b sp si (step-from-inner (react-alive al))   dI = deferInner-pass S R b sp si (inj₂ al) dI
    deferInner-arm S R b sp si (step-from-inner (react-dead dd fz)) dI = deferInner-dies S R b sp si dd fz dI

    -- A RESTAMPED EMIT CARRIES WHAT IT CARRIED: the restamp rebuilds the
    -- emit over its own events, so the values it holds are the ones
    restamp-rel : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} e′ {ws}
                → EmitRel {Γ = Γ} κ (lookup Γ i) e′ ws
                → EmitRel {Γ = Γ} κ (lookup Γ i) (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) e′) ws
    restamp-rel (evs , i , s , inj₁ k) r = retag (λ q → q) r
    restamp-rel (evs , i , s , inj₂ k) r = r

    restamp-carries : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {es vs}
                    → Carries {s = lookup Γ i} es vs
                    → Carries (map (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀)) es) vs
    restamp-carries []             = []
    restamp-carries {i = i} {X = X} (quiet e′ r bs) = quiet _ (restamp-rel {i = i} {X = X} e′ r) (restamp-carries {i = i} {X = X} bs)
    restamp-carries {i = i} {X = X} (one e′ r bs)   = one _ (restamp-rel {i = i} {X = X} e′ r) (restamp-carries {i = i} {X = X} bs)

    -- A SLOT'S READER: the impl runs the restamp where the plain path runs
    -- on, so the arm is the one frame the impl moves alone, and the plain
    -- side has not moved
    read-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {Θ₀ ρ₀ ℓ′}
                   {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {h : suc (toℕ (n ↑ʳ i)) ≤ ℓ′}
                   {p : Path Γ (suc (toℕ i)) (lookup Γ i) t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ (lookup Γ i)) (emitᵗ t)}
                 → lookup κ i ≡ hotᵏ ⊎ lookup κ i ≡ sharedᵏ
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → ∀ {now vs es fin rI} → Carries es vs
                 → Sound (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) sI stI
                 → foldPath⇓ now (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) es fin sI stI rI
                 → Arm S now [] sP stP p vs fin none rI
    read-arm S {i = i} {X = X} _ r c si (fold-step step-map dq) =
      arm (after S (λ x → x) (λ x → x) [] (λ x → x)) r (restamp-carries {i = i} {X = X} c) (drop-ot _ _ _ si) dq (λ _ _ _ → tt)

    -- the emits of a stamped slot against the plain values, at types the
    -- share's own is only propositionally the emit of
    CarriesU : ∀ {u u′} → u′ ≡ emitᵗ u → List (Val (plainᵏ Γ κ) u′) → List (Val Γ u) → Set
    CarriesU refl = Carries

    carriesU-nil : ∀ {u u′} (e : u′ ≡ emitᵗ u) → CarriesU e [] []
    carriesU-nil refl = []

    -- a partnered pair stays partnered once the store moves
    slot-keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {u}
                   {c : RegId × AtFloor Γ u t} {d}
               → Keeps S S₁
               → SlotPair (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i c d
               → SlotPair (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i c d
    slot-keeps K (slotpair x) = slotpair (K x)

    -- the same pass, started from the store as it stood before the row was marked
    rebase : ∀ {sP stP sI stI x x′ rP rI} {S : St sP stP sI stI} {pr : Partners κ _ _ _ _ _ (Store.rows S) x x′}
           → After (delivered S pr) rP rI → After S rP rI
    rebase (after s k q v g) = after s k (λ ar → q (delivered-arr ar)) v g

    -- a fan-out's pairs stay paired once the store moves
    share-keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S₀ : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {cs ds}
                → Keeps S₀ S₁
                → Pointwise (ShareSlot (Store.rows S₀) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) cs ds
                → Pointwise (ShareSlot (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i) cs ds
    share-keeps K []       = []
    share-keeps {S₀ = S₀} {S₁ = S₁} K (r ∷ rs) = slot-keeps {S = S₀} {S₁ = S₁} K r ∷ share-keeps {S₀ = S₀} {S₁ = S₁} K rs

    -- the share's emits at the type its stamped slot holds them
    slot-cast : ∀ {i : Fin n} → lookup κ i ≡ sharedᵏ → Val (plainᵏ Γ κ) (emitᵗ (lookup Γ i)) → Val (plainᵏ Γ κ) (lookup (plainᵏ Γ κ) (n ↑ʳ i))
    slot-cast {i} sh = subst (Val (plainᵏ Γ κ)) (sym (sharedEq {Γ = Γ} κ i sh))

    carries-cast : ∀ {u u′} (ε : u′ ≡ emitᵗ u) {es : List (Val (plainᵏ Γ κ) (emitᵗ u))} {vs}
                 → Carries es vs → CarriesU ε (map (subst (Val (plainᵏ Γ κ)) (sym ε)) es) vs
    carries-cast refl {es} c = subst (λ xs → Carries xs _) (sym (map-id es)) c

    -- a share marked dying on both sides
    dying-after : ∀ {sP stP sI stI} (S : St sP stP sI stI) (i : Fin n) → lookup κ i ≡ sharedᵏ
                → After S ([] , sP , shareDying i true stP) ([] , sI , shareDying (n ↑ʳ i) true stI)
    dying-after S i sh = after (dying S i sh) (λ x → x) (dying-arr {S = S} {i = i} {sh = sh}) [] (λ x → x)
