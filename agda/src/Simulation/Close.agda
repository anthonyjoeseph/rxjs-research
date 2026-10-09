------------------------------------------------------------------
-- A MINTED SOURCE'S CLOSE keeps the stores related.  It latches a number
-- no input slot carries, on each side, and the latches compare slots only.
------------------------------------------------------------------
module Simulation.Close where

open import Data.Bool    using (_∨_; _∧_)
open import Data.Fin     using (toℕ; _↑ʳ_; _↑ˡ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ʳ; toℕ-↑ˡ)
open import Data.Empty   using (⊥-elim)
open import Data.List    using (List; []; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Nat     using (_+_; _<_)
open import Rx.Evaluator.Reducible.Support using (sub-rule)
open import Data.Nat.Properties using (≤-refl; <⇒≢; <-trans; <-≤-trans; m≤m+n; +-monoʳ-<)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Arrival; Sched; EvalSt; memberSource; sameSource; cascadeClose)
open import Rx.Prim      using (Source)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Stores using (Store; Arr; Census; spent-off; inv-close; DyingFree)
open import Simulation.Sweep using (sameSource-no; dies-rows; close-named; t≢f)

-- a source number no slot has is not the slot's
member-skip : ∀ {m k} (xs : List Source) → m < k → memberSource m (k ∷ xs) ≡ memberSource m xs
member-skip {m} xs lt = cong (_∨ any (sameSource m) xs) (sameSource-no (<⇒≢ lt))

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- A DYN SOURCE'S CLOSE keeps the stores related: it latches a number
  -- no slot carries, and the latches compare slots only.
  close-store : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                  {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {a a′}
    → (s : Store κ sP stP sI stI) → (na : n < Arrival.source a) → (na′ : n + n < Arrival.source a′) → ∀ {u u′} → Arr s (Arrival.source a) (Arrival.source a′) u u′
    → DyingFree stI → Store κ sP (cascadeClose a stP) sI (cascadeClose a′ stI)
  close-store {stP = stP} {stI = stI} {a = a} {a′} s na na′ ar df = record
    { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
    ; sync = sync ; rows = rows ; bounded = bounded ; swept = swept ; uncut = uncut ; named = close-named {a = a} (proj₁ named) (Arr.boundP ar) , close-named {a = a′} (proj₂ named) (Arr.boundI ar) ; rids = rids ; fresh-ids = fresh-ids ; above = above ; owned = owned ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI
    ; scripts = scripts ; inv = inv-close a′ df inv
    ; dlv-alike = spent-off κ π _ _ _ _ rows (λ _ → refl) (λ _ → refl)
    ; dying-alike = dies-rows κ na na′ rows (Arr.rows ar)
    ; dying-done = λ i _ → (λ m → ⊥-elim (t≢f (trans (sym m) (member-skip [] (<-trans (toℕ<n i) na)))))
                         , (λ m → ⊥-elim (t≢f (trans (sym m) (member-skip []
                                    (subst (_< Arrival.source a′) (sym (toℕ-↑ʳ n i)) (<-trans (+-monoʳ-< n (toℕ<n i)) na′))))))
    ; census = λ i hk → subst (Census _ _ (EvalSt.registry stI) _) (sym (mr i)) (census i hk)
    ; latches = λ i → let h , sh = latches i
                          lt  = <-trans (toℕ<n i) na
                          lt′ = subst (_< Arrival.source a′) (sym (toℕ-↑ʳ n i)) (<-trans (+-monoʳ-< n (toℕ<n i)) na′)
                          mp  = member-skip (EvalSt.completedSources stP) lt
                          mi  = member-skip (EvalSt.completedSources stI) lt′
                      in (λ hk → let c , d = h hk
                                 in trans mp (trans c (sym (mr i)))
                                  , trans mi (trans d (cong (_∧ memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI)) (sym (mr i)))))
                       , (λ sk → let c , d = sh sk in trans mp (trans c (sym mi)) , d)
    }
    where
      open Store s
      -- a raw slot is below every minted number too
      mr : ∀ i → memberSource (toℕ (i ↑ˡ n)) (Arrival.source a′ ∷ EvalSt.completedSources stI)
               ≡ memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI)
      mr i = member-skip (EvalSt.completedSources stI)
               (subst (_< Arrival.source a′) (sym (toℕ-↑ˡ i n)) (<-trans (<-≤-trans (toℕ<n i) (m≤m+n n n)) na′))

  -- and the arrival's pair against the rows with it, since the rows are the same
  close-arr : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)}
                {S : Store κ sP stP sI stI} (na : n < Arrival.source a) (na′ : n + n < Arrival.source a′) {u u′}
    → (ar : Arr S (Arrival.source a) (Arrival.source a′) u u′) (df : DyingFree stI)
    → Arr (close-store {sP = sP} {stP = stP} {sI = sI} {stI = stI} {a = a} {a′ = a′} S na na′ ar df) (Arrival.source a) (Arrival.source a′) u u′
  close-arr na na′ ar _ = record { boundP = boundP ; boundI = boundI ; rows = rows ; lists = lists } where open Arr ar
