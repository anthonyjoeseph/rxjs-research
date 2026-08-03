------------------------------------------------------------------
-- THE RUNG-COUNT PROBE: does the per-cons fold charge fit the rung
-- count `fLvlD` supplies?
--
-- The receipt pass adds a fourth conjunct to the subscribe clique's Σ —
-- a BOUND on the reported witness — and the collision flagged before any
-- restatement was this: charging a fold PER CONS (Concat-Sum-Probe § 3)
-- means a concatenating clause's reported level grows with the length of
-- the list it walks, and the transformer family has to absorb that.  Two
-- facts were expected to close it:
--
--   (i)  the walked list arrives inside a receipt whose COUNT conjunct
--        bounds its length at that receipt's level, and
--   (ii) `fLvlD`'s iterators read `widAt` at CLIMBED levels, not at
--        entry syntax.
--
-- (ii) holds — that is what `frame-step` (Sub-Charge-Probe § 5) already
-- says.  (i) HOLDS FOR ONE OF THE TWO WALKS AND FAILS FOR THE OTHER, and
-- the failure is structural.
--
-- § 1  THE MATCH IS EXACT FOR thruWalk.  Its `vals` arrives under
--   `valsCaps? (frameStep j c) sl vals`, whose second conjunct is
--   `length vals ≤ suc (Caps.cWid (frameStep j c))` — and
--   `Caps.cWid (frameStep j c)` IS `widAt (Caps.cSize c) (Caps.cWid c) j`
--   definitionally, which is EXACTLY the rung count `frame-step` budgets:
--   `sIterD S W d (suc (sizeAt S j)) (suc (widAt S W j)) …`.  One rung per
--   cons, `suc (widAt S W j)` rungs, `suc (widAt S W j)` payloads.
--   `walk-rungs` is that, machine-checked, with no arithmetic in it.
--
-- § 2  AND IT IS ABSENT FOR concatDrain — THE GAP.  Its walked list is
--   the concat node's QUEUE, and the queue arrives under
--   `all (obsCaps? (frameStep j c) sl) q` — an `all`, pointwise, no
--   cardinality.  Nor is one recoverable from the state invariant:
--   `capsOK?`'s only node conjunct is `widNode`, and
--
--     widNode W sl (concat-st q _ _) = all (λ o → pWᵉ n sl o ≤ᵇ W) q
--
--   is likewise an `all`.  `no-queue-bound` and `no-node-bound` are the
--   refutations: given ONE admissible observable, a queue of ANY length
--   satisfies both predicates, so no function of (S, W, j) bounds
--   `length q`.  A drain of L queued inners costs at least L rungs (one
--   `suc` per cons at :1487, plus ≥ 3 per `subscribeInner`), against
--   `suc (widAt S W j)` rungs — so an unbounded L breaches any
--   level-read bound, and NO CHOICE OF THE FOLD CHARGE fixes it.  The
--   repair needs a NEW CARDINALITY SOURCE, and it is two-part (§ 2b).
--
-- § 2b THE WITNESS HALF OF THE REPAIR, and why a conjunct alone is not
--   enough.  `thruConsume-caps`'s concat-push clause (.Subscribe-Face
--   :1261-1276) reports witness `0` and appends `o` to the queue.  So a
--   `thruWalk` of L payloads pushes L items onto the queue with EVERY
--   intermediate receipt read at the SAME level j — a length invariant
--   indexed by the level would have to hold `length q ≤ f j` while q
--   grows and j does not.  A queue-length conjunct on `widNode` therefore
--   has to come WITH a witness bump on that clause (report `1`, not `0`),
--   and one level is generous: `cWid (frameStep (suc j) c) = S ^ suc
--   (cWid (frameStep j c))` dwarfs `suc (length q)`.
--
-- § 3  THE SECOND ARITHMETIC OBLIGATION, INDEPENDENT OF § 2, AND IT IS
--   DISCHARGED HERE.  `walk-step` concludes `j + (j₁ + j₂) ≤ sIterD …
--   (suc m) j`, but the three concatenating clauses report
--   `suc (j₁ + j₂)`.  The missing unit is NOT free — `weak-walk-step-absurd`
--   refutes the naive form at k = 0, where `sIterD S W d 0 m J = J + m`
--   exactly (`sIterD-k0`).  What buys it is +1-SUPERADDITIVITY of the
--   whole family, `suc (f J) ≤ f (suc J)`, proven below for all five
--   transformers (`fLvlD-sadd`, `sIterD-sadd`, `sLvlD-sadd`,
--   `opIterD-sadd`, `fIterD-sadd`) by the same recursion and argument
--   order as .Caps's `-mono` block.  `walk-step-suc` is then the
--   concat-clause form of `walk-step`, and `walk-step-lift` says the
--   head premise may be stated at `j` or at `suc j` interchangeably.
--
-- § 4  subscribeInner's THREE RUNGS are not a separate problem.  The
--   clause reports `suc (suc (suc j₂))` and `walk-step`'s head premise
--   absorbs any witness whatever — `sLvlD S W d k (suc j)` is one
--   transformer application, not a unit count.  What it needs instead is
--   `1 ≤ k`: `sLvlD S W d 0 J = J` pays for NO subscribe at all, so every
--   bound conjunct of the clique carries the nesting hypothesis
--   (`nestᵛ ≤ sizeᵛ`, owed by Nest-Budget-Probe) as a side condition.
--   The square `splitBurst` produces is paid by TWO folds, and two folds
--   dominate it with room at every row measured below.
------------------------------------------------------------------
module Rung-Count-Probe where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-assoc; +-identityʳ;
         +-mono-≤; +-monoʳ-≤; *-mono-≤; n≤1+n)
open import Data.List using (List; []; _∷_; all; length)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Frame-Width using (pWᵉ)
open import Rx.Evaluator
  using (Slots; NodeState; concat-st;
         sizeAt; widAt; fCharge; fLvl;
         fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fLvlD-0; fLvlD-suc; sIterD-0; sIterD-suc; sLvlD-0; sLvlD-suc;
         opIterD-0; opIterD-suc; fIterD-0; fIterD-suc)

open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; frameStep;
         sizeAt-mono; widAt-mono; fCharge-mono;
         sLvlD-infl;
         sIterD-mono; sLvlD-mono; opIterD-mono; fIterD-mono)
open import Verify-Budget-Sufficient.Caps-Face
  using (widNode; obsCaps?; valsCaps?)
open import Verify-Budget-Sufficient.Subscribe-Face using (valsLen)

------------------------------------------------------------------
-- § 1.  thruWalk's RUNG COUNT IS ITS RECEIPT'S COUNT CONJUNCT, on the
-- nose.  No arithmetic: `Caps.cWid (frameStep j c)` and
-- `widAt (Caps.cSize c) (Caps.cWid c) j` are the same normal form, so
-- the bound `valsCaps?` already carries IS the `m` that `frame-step`
-- instantiates `sIterD` with
------------------------------------------------------------------

walk-rungs : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (vals : List (Val Γ s)) → valsCaps? (frameStep j c) sl vals ≡ true →
  length vals ≤ suc (widAt (Caps.cSize c) (Caps.cWid c) j)
walk-rungs c j sl vals h = valsLen (frameStep j c) sl vals h

-- the rung counts the frame actually supplies, at the smallest caps the
-- face admits
_ : suc (widAt 2 1 0) ≡ 2
_ = refl

_ : suc (widAt 2 1 1) ≡ 5
_ = refl

_ : suc (widAt 2 1 2) ≡ 33
_ = refl

------------------------------------------------------------------
-- § 2.  concatDrain's QUEUE CARRIES NO CARDINALITY, from either source.
-- Both statements are POSITIVE: they exhibit, for any bound B, a queue
-- longer than B that satisfies the hypothesis.  So no `f` whatever makes
-- `length q ≤ f (Caps.cSize c) (Caps.cWid c) j` derivable
------------------------------------------------------------------

rep-list : ∀ {A : Set} → ℕ → A → List A
rep-list zero    x = []
rep-list (suc k) x = x ∷ rep-list k x

rep-len : ∀ {A : Set} (k : ℕ) (x : A) → length (rep-list k x) ≡ k
rep-len zero    x = refl
rep-len (suc k) x = cong suc (rep-len k x)

rep-all : ∀ {A : Set} (P : A → Bool) (k : ℕ) (x : A) → P x ≡ true →
  all P (rep-list k x) ≡ true
rep-all P zero    x h = refl
rep-all P (suc k) x h rewrite h = rep-all P k x h

-- (a) THE HYPOTHESIS concatDrain-caps IS GIVEN (.Subscribe-Face:1458)
no-queue-bound : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (o : Closed Γ s) → obsCaps? c sl o ≡ true → (B : ℕ) →
  Σ (List (Closed Γ s)) λ q →
    (all (obsCaps? c sl) q ≡ true) × (B < length q)
no-queue-bound c sl o ho B =
  rep-list (suc B) o
  , rep-all (obsCaps? c sl) (suc B) o ho
  , subst (λ x → B < x) (sym (rep-len (suc B) o)) ≤-refl

-- (b) AND THE STATE INVARIANT DOES NOT SUPPLY ONE EITHER: capsOK?'s only
-- node conjunct is widNode, and widNode on a concat node is an `all`
no-node-bound : ∀ {n} {Γ : Ctx n} {s} (W : ℕ) (sl : Slots Γ)
  (o : Closed Γ s) (act od : Bool) → (pWᵉ n sl o ≤ᵇ W) ≡ true → (B : ℕ) →
  Σ (List (Closed Γ s)) λ q →
    (widNode W sl (concat-st q act od) ≡ true) × (B < length q)
no-node-bound {n = n} W sl o act od ho B =
  rep-list (suc B) o
  , rep-all (λ x → pWᵉ n sl x ≤ᵇ W) (suc B) o ho
  , subst (λ x → B < x) (sym (rep-len (suc B) o)) ≤-refl

------------------------------------------------------------------
-- § 3.  +1-SUPERADDITIVITY OF THE WHOLE FAMILY.  `suc (f J) ≤ f (suc J)`
-- for each of the five transformers, by the same mutual recursion and
-- the same argument order (m, then d, then k) as .Caps's `-mono` block,
-- which is what makes the termination check go through unchanged
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
                               (suc (widAt S W J)) d (suc (sizeAt S J)) 2≤S))
                   (sIterD-mono (suc (widAt S W J)) (suc (widAt S W (suc J))) d d
                      (suc (sizeAt S J)) (suc (sizeAt S (suc J))) 2≤S ≤-refl ≤-refl
                      (fLvl-sadd S W J 2≤S) ≤-refl
                      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl (n≤1+n J)))
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
-- AND THE UNIT IS NOT FREE.  At k = 0 the subscribe budget is empty and
-- `sIterD` degenerates to `J + m` — one rung per cons and not one unit
-- more — so the naive strengthening of `walk-step` is FALSE
------------------------------------------------------------------

sIterD-k0 : ∀ (S W d m J : ℕ) → sIterD S W d 0 m J ≡ J + m
sIterD-k0 S W d zero    J =
  trans (sIterD-0 S W d 0 J) (sym (+-identityʳ J))
sIterD-k0 S W d (suc m) J =
  trans (sIterD-suc S W d 0 m J)
        (trans (cong (sIterD S W d 0 m) (sLvlD-0 S W d (suc J)))
               (trans (sIterD-k0 S W d m (suc J)) (sym (+-suc J m))))

Weak-Walk-Step : Set
Weak-Walk-Step = ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlD S W d k (suc j) →
  (j + j₁) + j₂ ≤ sIterD S W d k m (j + j₁) →
  j + suc (j₁ + j₂) ≤ sIterD S W d k (suc m) j

weak-walk-step-absurd : Weak-Walk-Step → ⊥
weak-walk-step-absurd H = bad (H 2 0 0 0 0 0 1 0 (s≤s (s≤s z≤n)) p₁ p₂)
  where
  p₁ : 0 + 1 ≤ sLvlD 2 0 0 0 (suc 0)
  p₁ = subst (λ x → 1 ≤ x) (sym (sLvlD-0 2 0 0 1)) ≤-refl
  p₂ : (0 + 1) + 0 ≤ sIterD 2 0 0 0 0 (0 + 1)
  p₂ = subst (λ x → 1 ≤ x) (sym (sIterD-0 2 0 0 0 1)) ≤-refl
  bad : 0 + suc (1 + 0) ≤ sIterD 2 0 0 0 1 0 → ⊥
  bad h with subst (λ x → 2 ≤ x) (sIterD-k0 2 0 0 1 0) h
  ... | s≤s ()

------------------------------------------------------------------
-- SO THE CONCAT CLAUSE'S STEP IS `walk-step` WITH A STRICT HEAD PREMISE,
-- and `walk-step-lift` says the strict form is what a head receipt read
-- at the walk's OWN level j gives — one application of `sLvlD-sadd`
------------------------------------------------------------------

walk-step-lift : ∀ (S W d k j j₁ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlD S W d k j → suc (j + j₁) ≤ sLvlD S W d k (suc j)
walk-step-lift S W d k j j₁ 2≤S h =
  ≤-trans (s≤s h) (sLvlD-sadd {S} {W} {j} d k 2≤S)

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

------------------------------------------------------------------
-- § 4.  subscribeInner's THREE RUNGS, and the SQUARE.  The witness the
-- clause reports is absorbed whole by one `sLvlD` — the head premise is
-- a transformer application, not a unit count — so what the clause needs
-- from the budget is `1 ≤ k`, nothing more.  `sLvlD-0` is why: an empty
-- subscribe budget is the identity, and the identity pays for no
-- subscribe.  The square `splitBurst` produces (burst length × per-emit
-- value count, each ≤ `suc cWid`) is cleared by TWO folds with room
------------------------------------------------------------------

-- the empty budget is the identity: nothing is derivable at k = 0
sLvlD-k0 : ∀ (S W d J : ℕ) → sLvlD S W d 0 J ≡ J
sLvlD-k0 S W d J = sLvlD-0 S W d J

-- one non-empty rung of budget already dominates any reported witness,
-- because `sLvlD` at `suc k` is a full `opIterD` sweep
1≤k-suffices : ∀ (S W d k J : ℕ) → J ≤ sLvlD S W d (suc k) J
1≤k-suffices S W d k J = sLvlD-infl S W d (suc k) J

-- and the square against two folds, at the smallest caps the face admits
_ : (suc (widAt 2 1 0) * suc (widAt 2 1 0) ≤ᵇ suc (widAt 2 1 2)) ≡ true
_ = refl

_ : (suc (widAt 2 1 1) * suc (widAt 2 1 1) ≤ᵇ suc (widAt 2 1 3)) ≡ true
_ = refl

_ : (suc (widAt 9 1 1) * suc (widAt 9 1 1) ≤ᵇ suc (widAt 9 1 2)) ≡ true
_ = refl
