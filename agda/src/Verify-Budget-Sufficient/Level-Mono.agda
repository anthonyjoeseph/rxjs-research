-- sizeCount-mono-d: sizeCount is monotone in its depth-fuel
-- argument.  Full proof — zero postulates.
--
-- sizeCount c d = lvls S W d 0 (cDel c d) (sizeCount-body), where d
-- occurs in TWO places: lvls's depth-fuel slot and cDel's delivery count.
-- The proof chains six monotonicity lemmas, all by structural induction:
--
--   iterL-mono-d : d ≤ d′ → iterL S W d k J ≤ iterL S W d′ k J
--     Induction on k; uses fLvlD-mono (depth varies) + iterL-mono (J varies).
--
--   dLvl-mono-d  : d ≤ d′ → dLvl S W d J ≤ dLvl S W d′ J
--     Immediate from iterL-mono-d at k = suc (sizeAt S J).
--
--   lvls-mono-d  : d ≤ d′ → lvls S W d J n ≤ lvls S W d′ J n
--     Induction on n; uses dLvl-mono-d (d varies) + dLvl-mono (J varies).
--
--   dCapᶜ-mono-d / dWalkᶜ-mono-d  (mutual, varies both d AND J):
--     d ≤ d′ → J ≤ J′ → dCapᶜ S W R d g J ≤ dCapᶜ S W R d′ g J′
--     Induction on gas g / position i; uses lvls-mono-d + lvls-mono.
--
--   cDel-mono-d  : d ≤ d′ → cDel c d ≤ cDel c d′
--     Unpacks cDel-body, applies dCapᶜ-mono-d at J = 0, repacks.
--
--   sizeCount-mono-d : the exported result.
--     Unpacks sizeCount-body, chains lvls-mono-d + lvls-mono (count varies
--     via cDel-mono-d), repacks.
--
-- RECHECK ECONOMICS: this module imports only Caps and Rx.Evaluator.
-- Caps.agda is upstream of Wet/Subscribe-Face; dirtying it costs an
-- hour+ rebuild, so this module lives DOWNSTREAM in its own file.
-- A solo recheck is cheap (< 20s) — no heavyweight SCC.
module Verify-Budget-Sufficient.Level-Mono where

open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤)
open import Relation.Binary.PropositionalEquality using (sym)

open import Verify-Budget-Sufficient.Caps
  using (Caps; cDel; cDel-body; sizeCount; sizeCount-body; fLvlD-mono; iterL-mono; dLvl-mono;
  lvls-mono; regAt-mono)

open import Rx.Evaluator using (iterL; dLvl; lvls; dCapᶜ; dWalkᶜ; fLvlD; sizeAt; regAt)

-- ----------------------------------------------------------------
-- iterL-mono-d : d ≤ d′ → iterL S W d k J ≤ iterL S W d′ k J
--
-- Proof: induction on k.
-- suc k: IH at J := fLvlD S W d J, then iterL-mono {d = d′} for the
--   J step from fLvlD S W d J to fLvlD S W d′ J (fLvlD-mono d≤d′).
-- ----------------------------------------------------------------

iterL-mono-d : ∀ (S W d d′ : ℕ) → 2 ≤ S → d ≤ d′ → ∀ (k J : ℕ) →
  iterL S W d k J ≤ iterL S W d′ k J
iterL-mono-d S W d d′ 2≤S hd zero    J = ≤-refl
iterL-mono-d S W d d′ 2≤S hd (suc k) J =
  ≤-trans
    (iterL-mono-d S W d d′ 2≤S hd k (fLvlD S W d J))
    (iterL-mono {d = d′} k k 2≤S ≤-refl ≤-refl
                (fLvlD-mono d d′ 2≤S ≤-refl ≤-refl ≤-refl hd)
                ≤-refl)

-- ----------------------------------------------------------------
-- dLvl-mono-d : d ≤ d′ → dLvl S W d J ≤ dLvl S W d′ J
-- ----------------------------------------------------------------

dLvl-mono-d : ∀ (S W d d′ : ℕ) → 2 ≤ S → d ≤ d′ → ∀ (J : ℕ) →
  dLvl S W d J ≤ dLvl S W d′ J
dLvl-mono-d S W d d′ 2≤S hd J = iterL-mono-d S W d d′ 2≤S hd (suc (sizeAt S J)) J

-- ----------------------------------------------------------------
-- lvls-mono-d : d ≤ d′ → lvls S W d J n ≤ lvls S W d′ J n
--
-- Proof: induction on n.
-- suc n: dLvl-mono-d at (lvls S W d J n) — d varies, J fixed.
--   Then dLvl-mono {d = d′} — d fixed at d′, J step from IH.
-- ----------------------------------------------------------------

lvls-mono-d : ∀ (S W d d′ : ℕ) → 2 ≤ S → d ≤ d′ → ∀ (J n : ℕ) →
  lvls S W d J n ≤ lvls S W d′ J n
lvls-mono-d S W d d′ 2≤S hd J zero    = ≤-refl
lvls-mono-d S W d d′ 2≤S hd J (suc n) =
  let IH = lvls-mono-d S W d d′ 2≤S hd J n
  in ≤-trans
       (dLvl-mono-d S W d d′ 2≤S hd (lvls S W d J n))
       (dLvl-mono {d = d′} 2≤S ≤-refl ≤-refl IH)

-- ----------------------------------------------------------------
-- dCapᶜ-mono-d / dWalkᶜ-mono-d : mutual.
-- Vary both d (d ≤ d′) AND J (J ≤ J′); gas g and position i are
-- the structural arguments.
--
-- dCapᶜ-mono-d: induction on g.
-- dWalkᶜ-mono-d: induction on i / i′.
--   suc i, suc i′: IH for (w ≤ w′), then:
--     lvls-mono-d (d step) + lvls-mono (J and count steps) gives
--     lvls S W d J (suc w) ≤ lvls S W d′ J′ (suc w′);
--     dCapᶜ-mono-d at that J bound closes the s≤s part.
-- ----------------------------------------------------------------

mutual
  dCapᶜ-mono-d : ∀ (S W R d d′ g J J′ : ℕ) →
    2 ≤ S → d ≤ d′ → J ≤ J′ →
    dCapᶜ S W R d g J ≤ dCapᶜ S W R d′ g J′
  dCapᶜ-mono-d S W R d d′ zero    J J′ 2≤S hd hJ = z≤n
  dCapᶜ-mono-d S W R d d′ (suc g) J J′ 2≤S hd hJ =
    dWalkᶜ-mono-d S W R d d′ g J J′ 2≤S hd hJ
                  (regAt S R J) (regAt S R J′)
                  (regAt-mono {S} {S} {R} {R} ≤-refl ≤-refl hJ)

  dWalkᶜ-mono-d : ∀ (S W R d d′ g J J′ : ℕ) →
    2 ≤ S → d ≤ d′ → J ≤ J′ →
    ∀ (i i′ : ℕ) → i ≤ i′ →
    dWalkᶜ S W R d g J i ≤ dWalkᶜ S W R d′ g J′ i′
  dWalkᶜ-mono-d S W R d d′ g J J′ 2≤S hd hJ zero    i′       z≤n      = z≤n
  dWalkᶜ-mono-d S W R d d′ g J J′ 2≤S hd hJ (suc i) zero     ()
  dWalkᶜ-mono-d S W R d d′ g J J′ 2≤S hd hJ (suc i) (suc i′) (s≤s hi) =
    let w  = dWalkᶜ S W R d  g J  i
        w′ = dWalkᶜ S W R d′ g J′ i′
        IH : w ≤ w′
        IH = dWalkᶜ-mono-d S W R d d′ g J J′ 2≤S hd hJ i i′ hi
        -- build lvls S W d J (suc w) ≤ lvls S W d′ J′ (suc w′) in two steps:
        step1 : lvls S W d J (suc w) ≤ lvls S W d′ J (suc w)
        step1 = lvls-mono-d S W d d′ 2≤S hd J (suc w)
        step2 : lvls S W d′ J (suc w) ≤ lvls S W d′ J′ (suc w′)
        step2 = lvls-mono {d = d′} (suc w) (suc w′) 2≤S ≤-refl ≤-refl hJ (s≤s IH)
        lvls≤ : lvls S W d J (suc w) ≤ lvls S W d′ J′ (suc w′)
        lvls≤ = ≤-trans step1 step2
    in +-mono-≤ IH (s≤s (dCapᶜ-mono-d S W R d d′ g
                           (lvls S W d  J  (suc w))
                           (lvls S W d′ J′ (suc w′))
                           2≤S hd lvls≤))

-- ----------------------------------------------------------------
-- cDel-mono-d : d ≤ d′ → cDel c d ≤ cDel c d′
-- cDel c d = dCapᶜ S W R d (suc S) 0 (by cDel-body).
-- ----------------------------------------------------------------

cDel-mono-d : ∀ (c : Caps) {d d′ : ℕ} → 2 ≤ Caps.cSize c → d ≤ d′ →
  cDel c d ≤ cDel c d′
cDel-mono-d c {d} {d′} 2≤S hd =
  let S = Caps.cSize c
      W = Caps.cWid c
      R = Caps.cReg c
  in ≤-trans
       (≤-reflexive (cDel-body c d))
       (≤-trans
         (dCapᶜ-mono-d S W R d d′ (suc S) 0 0 2≤S hd ≤-refl)
         (≤-reflexive (sym (cDel-body c d′))))

-- ----------------------------------------------------------------
-- sizeCount-mono-d (exported): the main result.
-- sizeCount c d = lvls S W d 0 (cDel c d) (sizeCount-body).
-- Chain: unpack → lvls-mono-d (d step) → lvls-mono (count step) → repack.
-- ----------------------------------------------------------------

sizeCount-mono-d : ∀ (c : Caps) {d d′ : ℕ} → 2 ≤ Caps.cSize c →
  d ≤ d′ → sizeCount c d ≤ sizeCount c d′
sizeCount-mono-d c {d} {d′} 2≤S hd =
  let S   = Caps.cSize c
      W   = Caps.cWid c
      nd  = cDel c d
      nd′ = cDel c d′
      hn  : nd ≤ nd′
      hn  = cDel-mono-d c 2≤S hd
  in ≤-trans
       (≤-reflexive (sizeCount-body c d))
       (≤-trans
         (lvls-mono-d S W d d′ 2≤S hd 0 nd)
         (≤-trans
           (lvls-mono {d = d′} nd nd′ 2≤S ≤-refl ≤-refl ≤-refl hn)
           (≤-reflexive (sym (sizeCount-body c d′)))))
