------------------------------------------------------------------
-- A CELL'S ARM: the plain scan steps once where the impl runs its
-- scan over the author's state beside the emit, then the projection
-- of the emit.  The impl's scan carries what the plain scan passes and
-- ends on a related state (`scan-group`), so both cells are written
-- and the tails stay related; the write itself is a leaf.
------------------------------------------------------------------
module Simulation.Scan where

open import Data.List    using ([]; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe   using (just)
open import Data.Nat     using (_≤_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Rx.Exp       using (Ctx; Closed; Val; FnClo; _×ᵗ_; applyClo; sndᵗ; varᵗ)
open import Rx.Evaluator using (EvalSt; Path; _↠[_]_; scan-f; map-f; lookupNode; setNode; cell-st; scanVals)
open import Rx.Evaluator.Domain using (fold-step; step-map)
open import Rx.Evaluator.Freshness using (lookup-set)
open import Rx.Evaluator.Reducible.Support using (Sound; drop-ot; head-on; self-node)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Elaborate using (ScanAᵗ)
open import Simulation.Stores using (V; ScanLifts; PathRel; scan~; Store)
open import Simulation.After using (module Kept)
open import Simulation.Arm using (module Arms; Clear; fold-unmoved; on-drop; out-quiet; scan-c)
open import Simulation.Take using (scan-at)

module Scans {n} {Γ : Ctx n} (κ : Kinds n) where

  open Arms {Γ = Γ} κ

  -- THE IMPL'S SCAN OVER A GROUP CARRIES WHAT THE PLAIN SCAN PASSES:
  -- each emit's step is one plain step over the value it carries, if
  -- any, so the projected emits carry the plain outputs and the states
  -- end related
  scan-group : ∀ {s u} {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u)} {Θ₀ ρ₀}
             → ScanLifts κ s u F′ F → ∀ {es vs} → Carries es vs → ∀ a′ em a → V κ u a′ a
             → Carries (map (applyClo {s = ScanAᵗ u} {t = emitᵗ u} (Θ₀ , sndᵗ (varᵗ (here refl)) , ρ₀)) (proj₁ (scanVals F′ (a′ , em) es)))
                       (proj₁ (scanVals F a vs))
             × V κ u (proj₁ (proj₂ (scanVals F′ (a′ , em) es))) (proj₂ (scanVals F a vs))
  scan-group L [] a′ em a v = [] , v
  scan-group {F′ = F′} {Θ₀} {ρ₀} L (quiet e′ r bs) a′ em a v = quiet _ (proj₁ (proj₂ SL)) (proj₁ IH) , proj₂ IH
    where
      SL = L a′ em a e′ [] v r
      IH = scan-group {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs (proj₁ (applyClo F′ ((a′ , em) , e′))) (proj₂ (applyClo F′ ((a′ , em) , e′))) a (proj₁ SL)
  scan-group {F = F} {F′} {Θ₀} {ρ₀} L (one e′ {w = w} r bs) a′ em a v = one _ (proj₁ (proj₂ SL)) (proj₁ IH) , proj₂ IH
    where
      SL = L a′ em a e′ (w ∷ []) v r
      IH = scan-group {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs (proj₁ (applyClo F′ ((a′ , em) , e′))) (proj₂ (applyClo F′ ((a′ , em) , e′)))
                      (applyClo F (a , w)) (proj₁ SL)

  -- AND KEEPS EVERY EMIT'S STAMP, so a group delivered at `I` stays so
  scan-del : ∀ {s u} {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u)} {Θ₀ ρ₀} {I}
           → ScanLifts κ s u F′ F → ∀ {es vs} → Carries es vs → ∀ a′ em a → V κ u a′ a → All (DelAt I) es
           → All (DelAt I) (map (applyClo {s = ScanAᵗ u} {t = emitᵗ u} (Θ₀ , sndᵗ (varᵗ (here refl)) , ρ₀)) (proj₁ (scanVals F′ (a′ , em) es)))
  scan-del L [] a′ em a v [] = []
  scan-del {F′ = F′} {Θ₀} {ρ₀} L (quiet e′ r bs) a′ em a v (d ∷ ds) =
    del-keep (proj₂ (applyClo F′ ((a′ , em) , e′))) e′ (proj₂ (proj₂ SL)) d
      ∷ scan-del {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs (proj₁ (applyClo F′ ((a′ , em) , e′))) (proj₂ (applyClo F′ ((a′ , em) , e′))) a (proj₁ SL) ds
    where SL = L a′ em a e′ [] v r
  scan-del {F = F} {F′} {Θ₀} {ρ₀} L (one e′ {w = w} r bs) a′ em a v (d ∷ ds) =
    del-keep (proj₂ (applyClo F′ ((a′ , em) , e′))) e′ (proj₂ (proj₂ SL)) d
      ∷ scan-del {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs (proj₁ (applyClo F′ ((a′ , em) , e′))) (proj₂ (applyClo F′ ((a′ , em) , e′)))
                 (applyClo F (a , w)) (proj₁ SL) ds
    where SL = L a′ em a e′ (w ∷ []) v r

  module Cells {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open Run {t} {ep} {ei}

    postulate
      -- A CELL WRITTEN ON BOTH SIDES keeps the stores and the tails
      -- related
      -- PROBED: make qc-store QC='51 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[1,1,1,2,1,0,1,1,0,0,0,0,2],"leaf":[2,0,1],"script":[1,1,1,1,1,0],"reach":["scan","flatten"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 15 writes two scans at subscribe, one over the other through
      --   an echoing flattener; case 28 writes one at each of two hot
      --   arrivals under a switch.
      scan-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′ ℓ ℓ₁ ℓ₂ s u k k′ Θ₀ ρ₀}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂}
                     {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u)}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (scan-f F k ↠[ h ] p)
                     (scan-f F′ k′ ↠[ h₁ ] (map-f (Θ₀ , sndᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ] q))
                 → Sound (scan-f F k ↠[ h ] p) sP stP
                 → Sound (scan-f F′ k′ ↠[ h₁ ] (map-f (Θ₀ , sndᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ] q)) sI stI
                 → ∀ (a : Val Γ u) (aI : Val (plainᵏ Γ κ) (ScanAᵗ u))
                 → Σ (After S ([] , sP , record stP { nodes = setNode k (cell-st {t = u} a) (EvalSt.nodes stP) })
                              ([] , sI , record stI { nodes = setNode k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI) })) λ A
                     → PathRel κ (Store.π (After.store A)) (setNode k (cell-st {t = u} a) (EvalSt.nodes stP))
                         (setNode k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)) p q

    -- A CELL STEPS ALIKE ON BOTH SIDES: the impl's scan and its
    -- projection write the one cell, which the tails' folds do not read
    scan-arm : ∀ {lo lo′ ℓ s u} {F : FnClo Γ (u ×ᵗ s) u} {k} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
             → Steps (scan-f F k) h p Q
    scan-arm {Q = _ ↠[ hS ] qT} {vs = vs} {es = es} {sP = sP} {stP = stP} {sI = sI} {stI = stI} S
             R@(scan~ {u = u} {k = k} {k′ = k′} {a = a} {a′ = a′} {em = em} {Θ₀ = Θ₀} {ρ₀ = ρ₀}
                      {h = h} {h₁ = h₁} {h₂ = h₂} {F = F} {F′ = F′} {p = p} {q = q} e lk lk′ v L r)
             bs sp si g d dI@(fold-step d₁ (fold-step step-map dq))
      with scan-at lk d | scan-at lk′ d₁
    ... | refl | refl =
      arm (proj₁ SW) (proj₂ SW) (proj₁ G) soq (λ e → gone-cell S {f = scan-f F′ k′} {h = hS} {q = qT} scan-c (g e)) dq (λ {rP} dP B rel′ →
        scan~ (After.grows B (After.grows (proj₁ SW) e)) (trans (fold-unmoved dP cP) lkP) (trans (fold-unmoved dq c′) lkI) (proj₂ G) L rel′
      ) λ { (f , ds) → out-quiet [] refl , inj₂ (f , scan-del {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs a′ em a v ds) }
      where
      G = scan-group {Θ₀ = Θ₀} {ρ₀ = ρ₀} L bs a′ em a v
      aP : Val Γ u
      aP = proj₂ (scanVals F a vs)
      aI : Val (plainᵏ Γ κ) (ScanAᵗ u)
      aI = proj₂ (scanVals F′ (a′ , em) es)
      SW = scan-write S R sp si aP aI
      lkP : lookupNode k (setNode k (cell-st {t = u} aP) (EvalSt.nodes stP)) ≡ just (cell-st {t = u} aP)
      lkP = lookup-set k (cell-st {t = u} aP) (EvalSt.nodes stP)
      lkI : lookupNode k′ (setNode k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)) ≡ just (cell-st {t = ScanAᵗ u} (proj₁ aI , proj₂ aI))
      lkI = lookup-set k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)
      -- the plain cell off its tail, once stepped
      spK = step-kept h d sp
      cP : Clear k p sP _
      cP = head-on (scan-f F k) h p k (self-node k []) spK , drop-ot (scan-f F k) h p spK
      -- the impl's cell off its tail, once stepped
      so₁ = step-kept h₁ d₁ si
      soq = drop-ot _ _ _ (drop-ot _ _ _ so₁)
      c′ : Clear k′ q sI _
      c′ = on-drop (head-on (scan-f F′ k′) h₁ _ k′ (self-node k′ []) so₁) , soq
