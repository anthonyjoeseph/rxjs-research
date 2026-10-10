-- `fold-unmoved` AND `fold-off` ARE FALSE AT A STORE HOLDING A ROW ON A
-- SHARE THAT NEVER CONNECTED.  `Clear` asks only that the node's rows
-- end where the path does, and a stale reader of share 0 through node 1
-- ends at the root as the path does.  The fold hands the merge at node
-- 0 an inner reading share 0, whose connect walks every row on the
-- share: the stale one's take at node 1 cuts and is written spent.
-- The connecting row's own id is cancelled so the walk passes it.
module Refuted.Stale-Reader where

open import Data.Nat     using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.List    using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (nothing; just)
open import Data.Bool    using (false; T)
open import Data.Fin     using () renaming (zero to fz)
import Data.Vec as V
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit    using (tt)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Rx.Exp       using (Ctx; Closed; Val; unitᵗ; emptyᵉ; ofᵉ; unit̂; input; []ᵉ)
open import Rx.Mint      using (mint; nodeᵏ; regᵏ)
open import Rx.Slots     using (shared)
open import Rx.Evaluator using (EvalSt; Sched; Path; root; thru-outer; take-f; _↠[_]_; mergeAllᵒ; mergeAll-st; take-st;
  setNode; lookupNode; NodeState; echoᵗ; atSlot; pathHasNode)
open import Rx.Evaluator.Domain using (foldPath⇓; fold-step; fold-root; fold-sink; step-thru-outer; step-take; walk-cons; walk-nil;
  walk-more; walk-end; disp; go-live; go-cut; go-nil; consume-all-sub; inner; subs-shared; slot-connect; connect; subs-of)
open import Rx.Evaluator.Freshness using (lookup-set)
open import Rx.Evaluator.Reducible.Support using (sound; node-on; rule; Termini; FreshRows; FreshPath; EndsAt)
open import Simulation.Arm using (Clear)
open import Simulation.Size using (sz-foldPath)
open import Data.Product using (Σ; _×_)

FoldUnmoved : Set
FoldUnmoved = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {κ : Path Γ lo s t} {k now vals fin sched st r}
            → foldPath⇓ {e = e} now κ vals fin sched st r → Clear k κ sched st
            → lookupNode k (EvalSt.nodes (proj₂ (proj₂ r))) ≡ lookupNode k (EvalSt.nodes st)

FoldOff : Set
FoldOff = ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} {κ : Path Δ lo s t} {k x y now vals fin sched st r}
        → lookupNode k (EvalSt.nodes st) ≡ just x
        → Clear k κ sched st
        → (d : foldPath⇓ {e = e} now κ vals fin sched (record st { nodes = setNode k y (EvalSt.nodes st) }) r)
        → Σ _ λ r′ → Σ (foldPath⇓ now κ vals fin sched st r′) λ d′
            → sz-foldPath d′ ≡ sz-foldPath d
            × r ≡ (proj₁ r′ , proj₁ (proj₂ r′) , record (proj₂ (proj₂ r′)) { nodes = setNode k y (EvalSt.nodes (proj₂ (proj₂ r′))) })

Γ : Ctx 1
Γ = unitᵗ V.∷ V.[]

E : Closed Γ unitᵗ
E = emptyᵉ

v : Val Γ (echoᵗ unitᵗ)
v = inj₁ tt , inj₂ ([] , input fz , []ᵉ)

κ : Path Γ 1 (echoᵗ unitᵗ) unitᵗ
κ = thru-outer mergeAllᵒ 0 ↠[ ≤-refl ] root

stale : Path Γ 1 unitᵗ unitᵗ
stale = take-f nothing 1 ↠[ ≤-refl ] root

sched₀ : Sched Γ
sched₀ = record { mint = mint (λ { nodeᵏ → 2 ; regᵏ → 6 ; _ → 0 }) ; live = []
                ; slots = λ { fz → shared (ofᵉ (unit̂ ∷ [])) } }

st₀ : EvalSt E
st₀ = record { registry = (5 , atSlot fz , (unitᵗ , stale)) ∷ []
             ; nodes = (0 , mergeAll-st {t = unitᵗ} nothing 0 [] false) ∷ (1 , take-st 1) ∷ []
             ; connectedShares = [] ; completedSources = []
             ; delivered = [] ; cancelled = 6 ∷ [] ; dying = [] }

clear : Clear 1 κ sched₀ st₀
clear = node-on (λ { (here refl) _ → refl ; (there ()) _ }) (s≤s (s≤s z≤n)) (λ ())
      , sound (rule termini fresh-rows (λ { (here refl) → (λ _ _ ()) , _ ; (there ()) }))
              ends fresh-path ((λ _ _ ()) , _)
  where
  termini : Termini st₀
  termini k (here refl) (here refl) _ _ = refl
  termini k (here refl) (there ())  _ _
  termini k (there ())  _           _ _
  fresh-rows : FreshRows sched₀ st₀
  fresh-rows (here refl) (suc zero) _ = s≤s (s≤s z≤n)
  fresh-rows (there ())  _          _
  ends : ∀ k → T (pathHasNode k κ) → EndsAt k nothing st₀
  ends zero    _ (here refl) ()
  ends zero    _ (there ())  _
  ends (suc k) ()
  fresh-path : FreshPath κ sched₀
  fresh-path zero    _ = s≤s z≤n
  fresh-path (suc k) ()

d : foldPath⇓ {e = E} 0 κ (v ∷ []) false sched₀ st₀ _
d = fold-step
      (step-thru-outer (walk-cons
        (consume-all-sub refl refl (inner refl
          (subs-shared {below = s≤s z≤n} refl (slot-connect refl refl (connect refl
            (subs-of (fold-sink (disp
              (walk-more (go-live refl (fold-step step-take fold-root) (go-cut refl go-nil))
                (walk-end (go-cut refl go-nil))))))))))) walk-nil))
      fold-root

refuted-unmoved : ¬ FoldUnmoved
refuted-unmoved fu with fu d clear
... | ()

refuted-off : ¬ FoldOff
refuted-off fo with fo refl clear d
... | r′ , _ , _ , eq with trans (cong (λ r → lookupNode 1 (EvalSt.nodes (proj₂ (proj₂ r)))) eq)
                                (lookup-set 1 (take-st 1) (EvalSt.nodes (proj₂ (proj₂ r′))))
... | ()
