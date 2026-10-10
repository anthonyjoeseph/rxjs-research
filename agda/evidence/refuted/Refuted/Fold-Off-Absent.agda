-- `fold-off` WITHOUT THE NODE IN THE TABLE IS FALSE.  Rewriting an
-- absent node appends it; a fold that then installs a fresh node
-- appends that after it, while the fold run first and rewritten after
-- lays the two down the other way round.  Here: a merge at node 0 is
-- handed an inner `defer`, whose subscribe installs node 3, with node 1
-- below the counter and never installed.
module Refuted.Fold-Off-Absent where

open import Data.Nat     using (ℕ; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.List    using (List; []; _∷_; map)
open import Data.Maybe   using (nothing)
open import Data.Bool    using (false)
import Data.Vec as V
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Data.Empty   using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Exp       using (Ctx; Closed; Val; unitᵗ; emptyᵉ; deferᵉ; []ᵉ)
open import Rx.Mint      using (mint; nodeᵏ)
open import Rx.Evaluator using (EvalSt; Sched; Path; root; thru-outer; _↠[_]_; mergeAllᵒ; mergeAll-st; setNode; NodeState; echoᵗ)
open import Rx.Evaluator.Domain using (foldPath⇓; fold-step; fold-root; step-thru-outer; walk-cons; walk-nil;
  consume-all-sub; consume-all-enqueue; consume-all-nil; inner; subs-defer)
open import Rx.Evaluator.Reducible.Support using (sound; node-on; rule)
open import Simulation.Arm using (Clear)
open import Simulation.Size using (sz-foldPath)

FoldOff : Set
FoldOff = ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} {κ : Path Δ lo s t} {k y now vals fin sched st r}
        → Clear k κ sched st
        → (d : foldPath⇓ {e = e} now κ vals fin sched (record st { nodes = setNode k y (EvalSt.nodes st) }) r)
        → Σ _ λ r′ → Σ (foldPath⇓ now κ vals fin sched st r′) λ d′
            → sz-foldPath d′ ≡ sz-foldPath d
            × r ≡ (proj₁ r′ , proj₁ (proj₂ r′) , record (proj₂ (proj₂ r′)) { nodes = setNode k y (EvalSt.nodes (proj₂ (proj₂ r′))) })

Γ : Ctx 0
Γ = V.[]

E : Closed Γ unitᵗ
E = emptyᵉ

m₀ : NodeState Γ
m₀ = mergeAll-st {t = unitᵗ} nothing 0 [] false

v : Val Γ (echoᵗ unitᵗ)
v = inj₁ tt , inj₂ ([] , deferᵉ emptyᵉ , []ᵉ)

κ : Path Γ 0 (echoᵗ unitᵗ) unitᵗ
κ = thru-outer mergeAllᵒ 0 ↠[ ≤-refl ] root

sched₀ : Sched Γ
sched₀ = record { mint = mint (λ { nodeᵏ → 2 ; _ → 0 }) ; live = [] ; slots = λ () }

st₀ : EvalSt E
st₀ = record { registry = [] ; nodes = (0 , m₀) ∷ [] ; connectedShares = [] ; completedSources = []
             ; delivered = [] ; cancelled = [] ; dying = [] }

clear : Clear 1 κ sched₀ st₀
clear = node-on (λ ()) (s≤s (s≤s z≤n)) (λ ())
      , sound (rule (λ _ ()) (λ ()) (λ ())) (λ _ _ ()) fresh ((λ _ _ ()) , _)
  where
  fresh : ∀ k → _ → _
  fresh zero    _ = s≤s z≤n
  fresh (suc k) ()

d : foldPath⇓ {e = E} 0 κ (v ∷ []) false sched₀ (record st₀ { nodes = setNode 1 m₀ (EvalSt.nodes st₀) }) _
d = fold-step (step-thru-outer (walk-cons (consume-all-sub refl refl (inner refl (subs-defer refl refl refl refl))) walk-nil)) fold-root

refuted : ¬ FoldOff
refuted fo with fo clear d
... | _ , fold-step (step-thru-outer (walk-cons (consume-all-enqueue refl ()) walk-nil)) _ , _
... | _ , fold-step (step-thru-outer (walk-cons (consume-all-nil ()) walk-nil)) _ , _
... | _ , fold-step (step-thru-outer (walk-cons (consume-all-sub refl refl (inner refl (subs-defer refl refl refl refl))) walk-nil)) fold-root , _ , eq
  with cong (λ x → map proj₁ (EvalSt.nodes (proj₂ (proj₂ x)))) eq
... | ()
