------------------------------------------------------------------
-- PROBE for Depth-Bound.agda's `storeNest-capped` postulate:
--
--     storeNest-capped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
--       (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
--       capsOK? c sched st ≡ true →
--       slotsSize (Sched.slots sched) ≤ Caps.cSize c →
--       storeNestMax sched st ≤ Caps.cSize c
--
-- where `storeNestMax sched st = slotsNestMax (Sched.slots sched) ⊔
-- nodesNestMax (EvalSt.nodes st)`.  Measure definitions below are
-- COPIED VERBATIM from Depth-Bound.agda (not imported — that module
-- holds the postulate this probe replaces).
--
-- ROUTE TAKEN (matches the design session's brief exactly):
--
--   · `⊔` splits via `⊔-lub`.
--   · NODE HALF: `capsOK?`'s first conjunct is
--     `stBounded? (Caps.cSize c) sched st`, whose second conjunct is
--     `all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st)`.
--     `boundedNode`'s two live clauses (scan-st's `sizeᵛ t v ≤ᵇ B`,
--     concat-st's `all (λ o → sizeᵉ o ≤ᵇ B) q`) are EXACTLY
--     `nodeNestMax`'s two live clauses read as a `≤ᵇ` test — the other
--     four clauses report 0 both sides.  So the node half is a
--     two-step inversion (capsOK? → stBounded? → boundedNode) landing
--     on a single reusable "foldr _⊔_ bounded by a pointwise ≤ᵇ test"
--     lemma, applied once for the queue (inside `node-nest-bounded`)
--     and once for the node list itself.
--   · SLOT HALF: `slotSize (shared d) = sizeᵉ d = slotNest (shared d)`
--     (EQUAL, not just dominated) and `slotSize (scripted i) =
--     inputSize i ≥ 0 = slotNest (scripted i)`.  So `slotNest` is
--     pointwise ≤ `slotSize`, and `slotsNestMax sl = foldr _⊔_ 0
--     (tabulate (slotNest ∘ sl))` is ≤ `slotsSize sl = sum (tabulate
--     (slotSize ∘ sl))` by a clean induction on the `Fin`/`tabulate`
--     structure (max of a pointwise-dominated tabulation ≤ the sum of
--     the dominating one). Chained with the supplied `slotsSize ≤
--     cSize` closes the slot half.
--
-- So the SLOTSSIZE-DOMINATION QUESTION the brief flagged as the most
-- likely obstacle is NOT an obstacle: `slotNest` is dominated by
-- `slotSize` at every slot (equality on `shared`, `0 ≤ anything` on
-- `scripted`), so `slotsSize` is a legitimate hypothesis for this
-- statement.  No design finding to report there.
--
-- RESULT: closes with NO POSTULATES.  See the report for the verbatim
-- text and the two helper lemmas this needed
-- (`foldr-⊔-bounded`, not previously in the source tree, and
-- `tabulate-⊔≤-sum`, ditto) — both belong in Measures.agda /
-- Depth-Bound.agda respectively, per their headers below.
------------------------------------------------------------------

module Store-Nest-Probe where

open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _⊔_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ⊔-lub; m≤m+n; m≤n+m; ≤ᵇ⇒≤)
open import Data.Bool    using (Bool; true)
open import Data.List    using (List; []; _∷_; foldr; tabulate; sum; all)
open import Data.Fin     using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp       using (Ctx; Closed; sizeᵉ; sizeᵛ)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; scripted; shared;
                                NodeId; NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                slotSize; slotsSize)

-- the caps face's public chain (Subscribe-Face → Caps-Face → … →
-- Keeps-Ring `open …  public`) is what carries `Caps`, `capsOK?`,
-- `stBounded?`, `boundedNode`, `∧-true`, `T-to` all the way out to
-- here — the SAME chain Depth-Bound.agda itself relies on
open import Verify-Budget-Sufficient.Subscribe-Face
  using (Caps; capsOK?; capsOK?-parts; stBounded?; stB-nodes; boundedNode;
        ∧-true; T-to)

------------------------------------------------------------------
-- the measure definitions, copied verbatim from Depth-Bound.agda
------------------------------------------------------------------

nodeNestMax : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeNestMax (scan-st {t} v)       = sizeᵛ t v
nodeNestMax (concat-st {t} q _ _) = foldr (λ o acc → sizeᵉ o ⊔ acc) 0 q
nodeNestMax (take-st _)           = 0
nodeNestMax (merge-st _ _)        = 0
nodeNestMax (switch-st _ _)       = 0
nodeNestMax (exhaust-st _ _)      = 0

nodesNestMax : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
nodesNestMax = foldr (λ kv acc → nodeNestMax (proj₂ kv) ⊔ acc) 0

slotNest : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotNest (shared d)   = sizeᵉ d
slotNest (scripted _) = 0

slotsNestMax : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestMax {n} sl = foldr _⊔_ 0 (tabulate {n = n} (λ i → slotNest (sl i)))

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
storeNestMax sched st =
  slotsNestMax (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

------------------------------------------------------------------
-- HELPER 1 — general enough to serve BOTH the concat-st queue
-- (inside the node half) and the node list itself: a `foldr _⊔_ 0`
-- over a list whose elements are each `≤ B` per a `Bool` test `p`
-- (with `p x ≡ true` cashed to `f x ≤ B` by `dom`) is itself `≤ B`.
-- Belongs in Measures.agda (or Depth-Bound.agda) once lifted from the
-- probe — it is the "fold-⊔ bounded" lemma the brief anticipated.
------------------------------------------------------------------

foldr-⊔-bounded : ∀ {A : Set} (B : ℕ) (f : A → ℕ) (p : A → Bool) →
  (∀ x → p x ≡ true → f x ≤ B) →
  (xs : List A) → all p xs ≡ true → foldr (λ x acc → f x ⊔ acc) 0 xs ≤ B
foldr-⊔-bounded B f p dom []       h = z≤n
foldr-⊔-bounded B f p dom (x ∷ xs) h
  with ∧-true (p x) (all p xs) h
... | px , pxs = ⊔-lub (dom x px) (foldr-⊔-bounded B f p dom xs pxs)

------------------------------------------------------------------
-- NODE HALF — `boundedNode`'s two live clauses read as `nodeNestMax`
-- tests; the four vacuous clauses (take/merge/switch/exhaust) report
-- 0 ≤ B unconditionally.
------------------------------------------------------------------

node-nest-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (ns : NodeState Γ) →
  boundedNode B ns ≡ true → nodeNestMax ns ≤ B
node-nest-bounded B (scan-st {t} v)   h = ≤ᵇ⇒≤ (sizeᵛ t v) B (T-to h)
node-nest-bounded B (concat-st q _ _) h =
  foldr-⊔-bounded B sizeᵉ (λ o → sizeᵉ o ≤ᵇ B)
    (λ o ho → ≤ᵇ⇒≤ (sizeᵉ o) B (T-to ho)) q h
node-nest-bounded B (take-st _)      h = z≤n
node-nest-bounded B (merge-st _ _)   h = z≤n
node-nest-bounded B (switch-st _ _)  h = z≤n
node-nest-bounded B (exhaust-st _ _) h = z≤n

nodesNestMax-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) nodes ≡ true →
  nodesNestMax nodes ≤ B
nodesNestMax-bounded B nodes h =
  foldr-⊔-bounded B (λ kv → nodeNestMax (proj₂ kv))
    (λ kv → boundedNode B (proj₂ kv))
    (λ kv → node-nest-bounded B (proj₂ kv)) nodes h

------------------------------------------------------------------
-- SLOT HALF — `slotNest` pointwise ≤ `slotSize` (equal on `shared`,
-- `0 ≤ anything` on `scripted`), then "max of a pointwise-dominated
-- tabulation ≤ the sum of the dominating one" by induction on the
-- `Fin`/`tabulate` structure.  Belongs in Depth-Bound.agda once
-- lifted — it is the "max of summands ≤ sum over tabulate" lemma the
-- brief anticipated, generalised to a DOMINATING pair of functions
-- rather than assuming `f` is literally a summand of `g`'s sum
-- (`scripted`'s 0 is not a summand of anything — `slotSize` there is
-- unrelated to `slotNest`, merely ≥ it).
------------------------------------------------------------------

slotNest-≤-slotSize : ∀ {n} {Γ : Ctx n} {t} (s : Slot Γ t) →
  slotNest s ≤ slotSize s
slotNest-≤-slotSize (scripted _) = z≤n
slotNest-≤-slotSize (shared _)   = ≤-refl

tabulate-⊔≤-sum : ∀ {n} (f g : Fin n → ℕ) → (∀ i → f i ≤ g i) →
  foldr _⊔_ 0 (tabulate f) ≤ sum (tabulate g)
tabulate-⊔≤-sum {zero}  f g dom = z≤n
tabulate-⊔≤-sum {suc n} f g dom =
  ⊔-lub (≤-trans (dom fzero)
                 (m≤m+n (g fzero) (sum (tabulate (λ i → g (fsuc i))))))
        (≤-trans (tabulate-⊔≤-sum (λ i → f (fsuc i)) (λ i → g (fsuc i))
                                  (λ i → dom (fsuc i)))
                 (m≤n+m (sum (tabulate (λ i → g (fsuc i)))) (g fzero)))

slots-nest-≤-size : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) →
  slotsNestMax sl ≤ slotsSize sl
slots-nest-≤-size {n} sl =
  tabulate-⊔≤-sum {n} (λ i → slotNest (sl i)) (λ i → slotSize (sl i))
    (λ i → slotNest-≤-slotSize (sl i))

------------------------------------------------------------------
-- THE ASSEMBLY — no postulates.
------------------------------------------------------------------

storeNest-capped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  slotsSize (Sched.slots sched) ≤ Caps.cSize c →
  storeNestMax sched st ≤ Caps.cSize c
storeNest-capped c sched st cap slB =
  ⊔-lub (≤-trans (slots-nest-≤-size (Sched.slots sched)) slB)
        (nodesNestMax-bounded (Caps.cSize c) (EvalSt.nodes st)
          (stB-nodes (Caps.cSize c) sched st (proj₁ (capsOK?-parts c sched st cap))))
