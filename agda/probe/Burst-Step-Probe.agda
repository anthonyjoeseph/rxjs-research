------------------------------------------------------------------
-- THE fIterD ROW OF THE GATE, which .Caps-Chain does not have.
--
-- The gate holds `walk-step`/`walk-index` for the sIterD family and
-- `index-mono` for opIterD, but nothing for fIterD — and `pushBurst-caps`
-- is an fIterD head: it recurses on `em ∷ ems`, so its index is the emit
-- count, and `op-step`'s pushBurst premise reads the index at
-- `suc (widAt S W A)`.  Both halves are named in .Caps-Face's pass memo
-- (~6090) as what the signature pass would need.  Proved here first.
------------------------------------------------------------------
module Burst-Step-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-assoc; +-identityʳ; n≤1+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fIterD-suc; sIterD-suc; sLvlD-suc; fIterD-0; sIterD-0)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; fIterD-infl; fIterD-mono; sIterD-infl; opIterD-infl)
open import Verify-Budget-Sufficient.Caps-Chain
  using (op-step; op-step-mu; frame-step; walk-index;
         burst-step; burst-index)
open import Verify-Budget-Sufficient.Caps-Sadd using (walk-step-suc)
open import Verify-Budget-Sufficient.Caps-Face using (frameBud)

-- § 1 IS NOW IN THE TREE: `burst-step` and `burst-index` live in
-- .Caps-Chain next to their sIterD twins, and are imported below.
------------------------------------------------------------------
-- § 2.  AND THE TWO CONSUMERS GO THROUGH WITH THEM, at abstract
-- receipts under exactly the bound the clauses hand back.
--
-- (a) a chain edge: the source's own conjunct verbatim, and pushBurst's
-- at the emit count, converted once
------------------------------------------------------------------

op-clause : ∀ (S W d k m j j₁ j₂ len : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ opIterD S W d k m (suc j) →
  (suc j + j₁) + j₂ ≤ fIterD S W d k len (suc j + j₁) →
  len ≤ suc (widAt S W (suc j + j₁)) →
  j + suc (j₁ + j₂) ≤ opIterD S W d k (suc m) j
op-clause S W d k m j j₁ j₂ len 2≤S src pb hlen =
  op-step S W d k m j j₁ j₂ 2≤S src
    (≤-trans pb (burst-index S W d k len (suc j + j₁) (suc j + j₁) 2≤S hlen))

-- (b) one payload of a walk: the head reported STRICTLY at `suc j` — the
-- shape a payload head can actually supply, since it subscribes at
-- `suc j` and the walk charges one fold per cons
walk-clause : ∀ (S W d k j j₁ j₂ len : ℕ) → 2 ≤ S →
  suc (j + j₁) ≤ sLvlD S W d k (suc j) →
  (j + j₁) + j₂ ≤ sIterD S W d k len (j + j₁) →
  j + suc (j₁ + j₂) ≤ sIterD S W d k (suc len) j
walk-clause S W d k j j₁ j₂ len 2≤S = walk-step-suc S W d k len j j₁ j₂ 2≤S

-- (c) and the parked branch of a concat drain, which reports the head's
-- receipt alone: the walk's remaining payloads cost nothing to skip
park-clause : ∀ (S W d k j j₁ len : ℕ) → 2 ≤ S →
  suc (j + j₁) ≤ sLvlD S W d k (suc j) →
  j + j₁ ≤ sIterD S W d k (suc len) j
park-clause S W d k j j₁ len 2≤S hd =
  ≤-trans (≤-trans (≤-trans (n≤1+n (j + j₁)) hd)
                   (sIterD-infl S W d k len (sLvlD S W d k (suc j))))
          (≤-reflexive (sym (sIterD-suc S W d k len j)))

-- (d) THE μ UNFOLDING, and the budget really does have to descend here:
-- the clause's own budget is `suc k`, its IH runs at k, and the two meet
-- by `sLvlD-suc` alone.  `unfoldμ-caps` pays exactly `m₀ + suc (m₀ * m₀)`
mu-clause : ∀ (S W d k m j m₀ j₁ : ℕ) → 2 ≤ S → m₀ ≤ sizeAt S j →
  (j + (m₀ + suc (m₀ * m₀))) + j₁
    ≤ opIterD S W d k (suc (sizeAt S (j + (m₀ + suc (m₀ * m₀)))))
              (j + (m₀ + suc (m₀ * m₀))) →
  j + ((m₀ + suc (m₀ * m₀)) + j₁) ≤ opIterD S W d (suc k) (suc m) j
mu-clause S W d k m j m₀ j₁ 2≤S hm₀ ih =
  op-step-mu S W d (suc k) m j m₀ j₁ 2≤S hm₀
    (≤-trans ih (≤-reflexive (sym (sLvlD-suc S W d k (j + (m₀ + suc (m₀ * m₀)))))))

-- (e) ONE FRAME, receipt-free: the thru-outer clause of stepFrame is its
-- payload walk and nothing else, and the walk runs at the REFRESHED
-- budget `frameBud c j` rather than at the inherited one — which is why
-- the clause has to split the DEPTH FUEL and hand the walk `d`
frame-clause : ∀ (S W d j j₁ len : ℕ) → 2 ≤ S →
  j + j₁ ≤ sIterD S W d (suc (sizeAt S (suc j))) len j →
  len ≤ suc (widAt S W j) →
  j + j₁ ≤ fLvlD S W (suc d) j
frame-clause S W d j j₁ len 2≤S walk hlen =
  frame-step S W d j 0 j₁ 2≤S z≤n
    (subst (λ x → x + j₁
                    ≤ sIterD S W d (suc (sizeAt S (suc j))) (suc (widAt S W j)) x)
           (sym (+-identityʳ j))
           (≤-trans walk
              (walk-index S W d (suc (sizeAt S (suc j))) len j j 2≤S hlen)))

-- (f) AND A LEAF: nothing is subscribed, so the level does not move
leaf-clause : ∀ (S W d k m j : ℕ) → j + 0 ≤ opIterD S W d k m j
leaf-clause S W d k m j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (opIterD-infl S W d k m j)

burst-nil : ∀ (S W d k j : ℕ) → j + 0 ≤ fIterD S W d k 0 j
burst-nil S W d k j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (≤-reflexive (sym (fIterD-0 S W d k j)))

walk-nil : ∀ (S W d k j : ℕ) → j + 0 ≤ sIterD S W d k 0 j
walk-nil S W d k j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (≤-reflexive (sym (sIterD-0 S W d k j)))

------------------------------------------------------------------
-- § 3.  THE THREE DEFINITIONAL FACTS the clauses read the caps through,
-- so no conversion sits between a caps hypothesis and a transformer
------------------------------------------------------------------

wid-is-widAt : ∀ (c : Caps) (j : ℕ) →
  Caps.cWid (frameStep j c) ≡ widAt (Caps.cSize c) (Caps.cWid c) j
wid-is-widAt c j = refl

size-is-sizeAt : ∀ (c : Caps) (j : ℕ) →
  Caps.cSize (frameStep j c) ≡ sizeAt (Caps.cSize c) j
size-is-sizeAt c j = refl

bud-is-refresh : ∀ (c : Caps) (j : ℕ) →
  frameBud c j ≡ suc (sizeAt (Caps.cSize c) (suc j))
bud-is-refresh c j = refl
