------------------------------------------------------------------
-- THE CONCAT-SUM PROBE: does the count receipt of a CONCATENATING
-- clause fit the witness its caps receipt already reports?
--
-- Two clauses of the subscribe clique output a CONCATENATION and are
-- therefore the cost centre of the per-emit half of the count:
--
--   · thruWalk-caps's step (.Subscribe-Face:730-767) outputs
--     `proj₁ TC ++ proj₁ REST` and reports the witness `j₁ + j₂`, with
--     TC's receipt read at `frameStep (j + j₁) c` and REST's at
--     `frameStep ((j + j₁) + j₂) c` — i.e. AT THE REPORTED LEVEL.
--   · concatDrain-caps's drain-on branch (:807-837) is the same shape:
--     `vs ++ proj₁ REST`, witness `j₁ + j₂`, `vs` at `j + j₁` and REST
--     at the reported level.
--   · innerFinish-caps's concat clause (:912) concatenates once more,
--     `vals ++ proj₁ DR`, at the witness concatDrain hands it.
--
-- § 1  THE SUM DOES NOT FIT, and not for want of folds IN BETWEEN.  A
--   receipt is `length ≤ suc (cWid …)`; the tail's is read AT THE
--   REPORTED LEVEL, so it alone spends the whole budget and the head has
--   nothing left however many folds j₂ contains.  `no-fold-absurd` is
--   that, machine-checked, at `caps 2 1 1` with j = j₁ = j₂ = 0.
--
-- § 2  ONE MORE FOLD CLEARS IT, unconditionally.  `foldStep S w =
--   S ^ suc w` and `suc w ≤ 2 ^ w` give `2 * suc w ≤ S ^ suc w` for
--   S ≥ 2, so two receipts at level L add to one at level `suc L`.
--   `sum-fold` is the arithmetic and `concat-fits` is it at caps levels.
--
-- § 3  SO THE REPAIR IS A WITNESS MOVE, not a conjunct: each of the
--   three concatenating clauses reports `suc (j₁ + j₂)` in place of
--   `j₁ + j₂`, reads both sub-receipts at `(j + j₁) + j₂`, and widens.
--   The caps conjuncts do not notice — they are upward closed in the
--   level (capsOK?-mono, burstCaps?-widen, valsCaps?-widen along
--   frameStep-mono-j) — so the move costs one widening per clause and
--   nothing else.  The COUNT is what needs the fold, and it is charged
--   PER CONS, so a walk of k payloads charges k folds: that is what
--   keeps the induction free of any length hypothesis on the list being
--   walked (neither `vals` in thruWalk nor the queue `q` in concatDrain
--   is bounded in cardinality by anything upstream).
--
-- § 4  AND THE MARGIN ON THE WORST KNOWN ROWS is not tight: the
--   eight-value script row (`caps 9 1 1`) and the four-share ladder
--   (`caps 2 1 1`) both clear their sums with room, computed below.
------------------------------------------------------------------
module Concat-Sum-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive;
                                       *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; *-identityʳ;
                                       ^-monoˡ-≤; ^-monoʳ-≤; n≤1+n;
                                       +-mono-≤; m≤m+n; <⇒≤;
                                       *-comm; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Evaluator using (foldStep; iterFold)
open import Verify-Budget-Sufficient.Measures using (n<2^n)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; frameStep; frameStep-wid-suc; _⊑ᶜ_; frameStep-mono-j)

------------------------------------------------------------------
-- § 1.  THE SUM AT THE REPORTED WITNESS.  This is the obligation the
-- clause bodies would have to discharge if the witness stayed `j₁ + j₂`:
-- the head's receipt one step down, the tail's at the top, the
-- concatenation at the top
------------------------------------------------------------------

No-Fold : Set₁
No-Fold = ∀ {A : Set} (c : Caps) (j j₁ j₂ : ℕ) (xs ys : List A) →
  2 ≤ Caps.cSize c →
  length xs ≤ suc (Caps.cWid (frameStep (j + j₁) c)) →
  length ys ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c)) →
  length (xs ++ ys) ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))

c₀ : Caps
c₀ = caps 2 1 1

_ : Caps.cWid (frameStep 0 c₀) ≡ 1
_ = refl

-- two payload lists of two values each, at the level `caps 2 1 1`
-- admits: each receipt holds, their sum does not
xs₂ ys₂ : List ℕ
xs₂ = 0 ∷ 1 ∷ []
ys₂ = 2 ∷ 3 ∷ []

_ : length xs₂ ≤ suc (Caps.cWid (frameStep 0 c₀))
_ = s≤s (s≤s z≤n)

_ : length ys₂ ≤ suc (Caps.cWid (frameStep 0 c₀))
_ = s≤s (s≤s z≤n)

_ : length (xs₂ ++ ys₂) ≡ 4
_ = refl

no-fold-absurd : No-Fold → ⊥
no-fold-absurd H
  with H {A = ℕ} c₀ 0 0 0 xs₂ ys₂ (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n))
... | s≤s (s≤s ())

------------------------------------------------------------------
-- AND THE FAILURE IS NOT AN ARTEFACT OF j₂ = 0.  However many folds sit
-- between the two receipts, the TAIL's receipt is read at the REPORTED
-- level and already exhausts it: any head at all overshoots.  The
-- statement below is the same obligation with the tail's receipt TIGHT,
-- which is the shape every nonempty tail actually has
------------------------------------------------------------------

No-Fold-Tight : Set
No-Fold-Tight = ∀ (W a : ℕ) → 1 ≤ a → a + suc W ≤ suc W

no-fold-tight-absurd : No-Fold-Tight → ⊥
no-fold-tight-absurd H with H 0 1 (s≤s z≤n)
... | s≤s ()

------------------------------------------------------------------
-- § 2.  ONE MORE FOLD CLEARS THE SUM.  `suc w ≤ 2 ^ w` is n<2^n with
-- the `<⇒≤`, so `2 * suc w ≤ 2 ^ suc w ≤ S ^ suc w = foldStep S w`
------------------------------------------------------------------

2*suc≤2^suc : ∀ (w : ℕ) → 2 * suc w ≤ 2 ^ suc w
2*suc≤2^suc w = *-monoʳ-≤ 2 {suc w} {2 ^ w} (n<2^n w)

double≤foldStep : ∀ (S w : ℕ) → 2 ≤ S → 2 * suc w ≤ foldStep S w
double≤foldStep S w hS =
  ≤-trans (2*suc≤2^suc w) (^-monoˡ-≤ (suc w) hS)

-- the arithmetic the repaired clause runs on
sum-fold : ∀ (S W a b : ℕ) → 2 ≤ S →
  a ≤ suc W → b ≤ suc W → a + b ≤ suc (foldStep S W)
sum-fold S W a b hS ha hb =
  ≤-trans (+-mono-≤ ha hb)
          (≤-trans (≤-reflexive (dbl W))
                   (≤-trans (double≤foldStep S W hS) (n≤1+n (foldStep S W))))
  where
  dbl : ∀ (w : ℕ) → suc w + suc w ≡ 2 * suc w
  dbl w = sym (trans (cong (λ x → suc w + x) (+-identityʳ (suc w))) refl)

-- and the same at caps levels, which is what the clause writes
concat-fits : ∀ {A : Set} (c : Caps) (L : ℕ) (xs ys : List A) →
  2 ≤ Caps.cSize c →
  length xs ≤ suc (Caps.cWid (frameStep L c)) →
  length ys ≤ suc (Caps.cWid (frameStep L c)) →
  length (xs ++ ys) ≤ suc (Caps.cWid (frameStep (suc L) c))
concat-fits c L xs ys hS hx hy =
  subst (λ x → length (xs ++ ys) ≤ suc x) (sym (frameStep-wid-suc c L))
    (≤-trans (≤-reflexive (length-++ xs))
             (sum-fold (Caps.cSize c) (Caps.cWid (frameStep L c))
                       (length xs) (length ys) hS hx hy))

------------------------------------------------------------------
-- THE PER-EMIT HALF ADDS THE SAME WAY.  A concatenating clause's value
-- lists are what the emit carries, so the identical lemma serves both
-- conjuncts of burstCount?; and a clause that CONSES one item (pushBurst
-- per emit, sharedConnect's `init` envelope) needs only the successor
-- form, which one fold clears with far more room
------------------------------------------------------------------

suc-fits : ∀ (c : Caps) (L a : ℕ) → 2 ≤ Caps.cSize c →
  a ≤ suc (Caps.cWid (frameStep L c)) →
  suc a ≤ suc (Caps.cWid (frameStep (suc L) c))
suc-fits c L a hS ha =
  ≤-trans (s≤s ha)
          (≤-trans (≤-reflexive refl)
                   (subst (λ x → suc (suc (Caps.cWid (frameStep L c))) ≤ suc x)
                          (sym (frameStep-wid-suc c L))
                          (s≤s (≤-trans (m≤m+n (suc (Caps.cWid (frameStep L c)))
                                               (suc (Caps.cWid (frameStep L c))))
                                        (≤-trans (≤-reflexive (dbl _))
                                                 (double≤foldStep (Caps.cSize c)
                                                    (Caps.cWid (frameStep L c)) hS))))))
  where
  dbl : ∀ (w : ℕ) → suc w + suc w ≡ 2 * suc w
  dbl w = sym (trans (cong (λ x → suc w + x) (+-identityʳ (suc w))) refl)

------------------------------------------------------------------
-- § 4.  THE WORST KNOWN ROWS, computed.
--
--   · the eight-value script row (Count-Level-Probe § 7) at `caps 9 1 1`:
--     the leaf's one fold takes the width 1 ↦ 81, so a sum of two
--     eight-value payloads has a budget of 82 at the next fold's level
--     — and the next fold takes it to 9 ^ 82.
--   · the four-share ladder (Share-Count-Probe) at `caps 2 1 1`: one
--     fold takes 1 ↦ 4, a second 4 ↦ 32, so the ladder's five emits and
--     any sum of two such bursts clear with room
------------------------------------------------------------------

c₈ : Caps
c₈ = caps 9 1 1

_ : Caps.cWid (frameStep 1 c₈) ≡ 81
_ = refl

-- two eight-value payloads at the leaf's own level, summed one fold up
_ : 8 + 8 ≤ suc (Caps.cWid (frameStep 1 c₈))
_ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
    (s≤s z≤n)))))))))))))))

_ : Caps.cWid (frameStep 1 c₀) ≡ 4
_ = refl

_ : Caps.cWid (frameStep 2 c₀) ≡ 32
_ = refl

-- the ladder's five emits, and two ladders' worth summed one fold up
_ : 5 ≤ suc (Caps.cWid (frameStep 1 c₀))
_ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

_ : 5 + 5 ≤ suc (Caps.cWid (frameStep 2 c₀))
_ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
