------------------------------------------------------------------
-- +1-SUPERADDITIVITY OF THE BUDGET FAMILY, and the walk step it buys.
--
-- The receipt pass charges a fold PER CONS (Concat-Sum-Probe § 3), so
-- the three concatenating clauses of the subscribe clique report
-- `suc (j₁ + j₂)` where the composition gate's `walk-step` concludes
-- `j + (j₁ + j₂)`.  That extra unit is NOT free: at k = 0 the subscribe
-- budget is empty and `sIterD S W d 0 m J` is exactly `J + m` — one rung
-- per cons and not one unit more — so the naive strengthening of
-- `walk-step` is refutable (Rung-Count-Probe § 3,
-- `weak-walk-step-absurd`).
--
-- What buys it is that every transformer in the family climbs at least
-- as fast as its argument: `suc (f J) ≤ f (suc J)`.  Each of the five is
-- proven below by the SAME mutual recursion and the SAME argument order
-- (m, then d, then k) as .Caps's `-mono` block, which is what makes the
-- termination check go through unchanged.  This module is not mutual
-- with any of them — it consumes the `-mono` family as finished facts —
-- so it is its own compilation unit and the clique imports it.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Sadd where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-assoc;
         +-mono-≤; +-monoʳ-≤; *-mono-≤; n≤1+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Evaluator
  using (sizeAt; widAt; fCharge; fLvl;
         fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fLvlD-0; fLvlD-suc; sIterD-0; sIterD-suc; sLvlD-0; sLvlD-suc;
         opIterD-0; opIterD-suc; fIterD-0; fIterD-suc)
open import Verify-Budget-Sufficient.Caps
  using (sizeAt-mono; widAt-mono; fCharge-mono;
         sIterD-mono; sLvlD-mono; opIterD-mono; fIterD-mono)

------------------------------------------------------------------
-- § 1.  THE FAMILY.
------------------------------------------------------------------

-- the seed: the per-frame charge is strictly monotone in the level
fLvl-sadd : ∀ (S W J : ℕ) → 2 ≤ S → suc (fLvl S W J) ≤ fLvl S W (suc J)
fLvl-sadd S W J 2≤S =
  +-monoʳ-≤ (suc J) (fCharge-mono 2≤S ≤-refl ≤-refl (n≤1+n J))

fLvlD-sadd  : ∀ {S W J : ℕ} (d : ℕ) → 2 ≤ S →
  suc (fLvlD S W d J) ≤ fLvlD S W d (suc J)
sIterD-sadd : ∀ {S W J : ℕ} (m d k : ℕ) → 2 ≤ S →
  suc (sIterD S W d k m J) ≤ sIterD S W d k m (suc J)
sLvlD-sadd  : ∀ {S W J : ℕ} (d k : ℕ) → 2 ≤ S →
  suc (sLvlD S W d k J) ≤ sLvlD S W d k (suc J)
opIterD-sadd : ∀ {S W J : ℕ} (m d k : ℕ) → 2 ≤ S →
  suc (opIterD S W d k m J) ≤ opIterD S W d k m (suc J)
fIterD-sadd : ∀ {S W J : ℕ} (m d k : ℕ) → 2 ≤ S →
  suc (fIterD S W d k m J) ≤ fIterD S W d k m (suc J)

fLvlD-sadd {S} {W} {J} zero 2≤S =
  ≤-trans (≤-trans (≤-reflexive (cong suc (fLvlD-0 S W J)))
                   (+-mono-≤ (fLvl-sadd S W J 2≤S)
                             (s≤s (widAt-mono 2≤S ≤-refl ≤-refl (n≤1+n J)))))
          (≤-reflexive (sym (fLvlD-0 S W (suc J))))
fLvlD-sadd {S} {W} {J} (suc d) 2≤S =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (cong suc (fLvlD-suc S W d J)))
                            (sIterD-sadd {S} {W} {fLvl S W J}
                               (suc (widAt S W J)) d (suc (sizeAt S (suc J))) 2≤S))
                   (sIterD-mono (suc (widAt S W J)) (suc (widAt S W (suc J))) d d
                      (suc (sizeAt S (suc J))) (suc (sizeAt S (suc (suc J))))
                      2≤S ≤-refl ≤-refl
                      (fLvl-sadd S W J 2≤S) ≤-refl
                      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl
                              (s≤s (n≤1+n J))))
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl (n≤1+n J)))))
          (≤-reflexive (sym (fLvlD-suc S W d (suc J))))

sIterD-sadd {S} {W} {J} zero d k 2≤S =
  ≤-reflexive (trans (cong suc (sIterD-0 S W d k J))
                     (sym (sIterD-0 S W d k (suc J))))
sIterD-sadd {S} {W} {J} (suc m) d k 2≤S =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (cong suc (sIterD-suc S W d k m J)))
                            (sIterD-sadd {S} {W} {sLvlD S W d k (suc J)} m d k 2≤S))
                   (sIterD-mono m m d d k k 2≤S ≤-refl ≤-refl
                      (sLvlD-sadd {S} {W} {suc J} d k 2≤S) ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (sIterD-suc S W d k m (suc J))))

sLvlD-sadd {S} {W} {J} d zero 2≤S =
  ≤-reflexive (trans (cong suc (sLvlD-0 S W d J))
                     (sym (sLvlD-0 S W d (suc J))))
sLvlD-sadd {S} {W} {J} d (suc k) 2≤S =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (cong suc (sLvlD-suc S W d k J)))
                            (opIterD-sadd {S} {W} {J} (suc (sizeAt S J)) d k 2≤S))
                   (opIterD-mono (suc (sizeAt S J)) (suc (sizeAt S (suc J))) d d k k
                      2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl (n≤1+n J)))))
          (≤-reflexive (sym (sLvlD-suc S W d k (suc J))))

opIterD-sadd {S} {W} {J} zero d k 2≤S =
  ≤-reflexive (trans (cong suc (opIterD-0 S W d k J))
                     (sym (opIterD-0 S W d k (suc J))))
opIterD-sadd {S} {W} {J} (suc m) d k 2≤S =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (cong suc (opIterD-suc S W d k m J)))
                            (fIterD-sadd {S} {W} {X} (suc (widAt S W X)) d k 2≤S))
                   (fIterD-mono (suc (widAt S W X)) (suc (widAt S W X′)) d d k k
                      2≤S ≤-refl ≤-refl X≤ ≤-refl ≤-refl
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl
                              (≤-trans (n≤1+n X) X≤)))))
          (≤-reflexive (sym (opIterD-suc S W d k m (suc J))))
  where
  J₀  = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
  J₀′ = suc (suc J + suc (sizeAt S (suc J)) * suc (sizeAt S (suc J)))
  X   = opIterD S W d k m (sLvlD S W d k J₀)
  X′  = opIterD S W d k m (sLvlD S W d k J₀′)
  sz≤ : sizeAt S J ≤ sizeAt S (suc J)
  sz≤ = sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl (n≤1+n J)
  J₀≤ : suc J₀ ≤ J₀′
  J₀≤ = s≤s (s≤s (+-monoʳ-≤ J (*-mono-≤ (s≤s sz≤) (s≤s sz≤))))
  X≤ : suc X ≤ X′
  X≤ = ≤-trans (opIterD-sadd {S} {W} {sLvlD S W d k J₀} m d k 2≤S)
               (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl
                  (≤-trans (sLvlD-sadd {S} {W} {J₀} d k 2≤S)
                           (sLvlD-mono d d k k 2≤S ≤-refl ≤-refl J₀≤ ≤-refl ≤-refl))
                  ≤-refl ≤-refl ≤-refl)

fIterD-sadd {S} {W} {J} zero d k 2≤S =
  ≤-reflexive (trans (cong suc (fIterD-0 S W d k J))
                     (sym (fIterD-0 S W d k (suc J))))
fIterD-sadd {S} {W} {J} (suc m) d k 2≤S =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (cong suc (fIterD-suc S W d k m J)))
                            (fIterD-sadd {S} {W} {fLvlD S W d J} m d k 2≤S))
                   (fIterD-mono m m d d k k 2≤S ≤-refl ≤-refl
                      (fLvlD-sadd {S} {W} {J} d 2≤S) ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (fIterD-suc S W d k m (suc J))))


------------------------------------------------------------------
-- § 2.  THE WALK STEP THE CONCATENATING CLAUSES NEED: `walk-step` with
-- the `suc` the per-cons fold charge puts on the reported witness.  Its
-- head premise is STRICT, and that is not a choice — a payload head
-- subscribes at `suc j`, so `sLvlD S W d k (suc j)` is the only level it
-- can report in, and the walk's own witness is one fold beyond what the
-- head handed back.  (A companion that read the head receipt at the
-- walk's own level `j` and lifted it here was carried for a while and
-- deleted: no clause can supply it, since a bound at `j` is the wrong
-- direction for a subscribe that begins at `suc j`.)
------------------------------------------------------------------

walk-step-suc : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  suc (j + j₁) ≤ sLvlD S W d k (suc j) →
  (j + j₁) + j₂ ≤ sIterD S W d k m (j + j₁) →
  j + suc (j₁ + j₂) ≤ sIterD S W d k (suc m) j
walk-step-suc S W d k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-trans (≤-trans (≤-reflexive lvlW) (s≤s tl))
                            (sIterD-sadd {S} {W} {j + j₁} m d k 2≤S))
                   (sIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (sIterD-suc S W d k m j)))
  where
  lvlW : j + suc (j₁ + j₂) ≡ suc ((j + j₁) + j₂)
  lvlW = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))
