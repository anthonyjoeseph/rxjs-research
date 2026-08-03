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
--   whole family, `suc (f J) ≤ f (suc J)`, which is .Caps-Sadd:
--   `walk-step-suc` there is the concat-clause form of `walk-step`, and
--   `walk-step-lift` says the head premise may be stated at `j` or at
--   `suc j` interchangeably.  What stays HERE is the refutation that
--   makes them necessary.
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
  using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-identityʳ; +-comm;
         n≤1+n; m≤m+n; ≤ᵇ⇒≤)
open import Data.List using (List; []; _∷_; _++_; all; length)
open import Data.List.Properties using (length-++)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Frame-Width using (pWᵉ)
open import Rx.Evaluator
  using (Slots; concat-st; widAt; sIterD; sLvlD;
         sIterD-0; sIterD-suc; sLvlD-0)

open import Verify-Budget-Sufficient.Measures
  using (∧-true; ∧-intro; all-impl; ≤ᵇ-widen; T-to)
open import Verify-Well-Formed using (≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; frameStep-wid-suc; widAt-mono; sLvlD-infl)
open import Verify-Budget-Sufficient.Caps-Face
  using (widNode; obsCaps?; valsCaps?; suc≤foldStep)
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

-- (b) AND THE STATE INVARIANT DID NOT SUPPLY ONE EITHER, which is why
-- `widNode`'s concat clause GAINED a cardinality conjunct.  The row
-- below is the old clause — a bare pointwise `all` — and it admits a
-- queue of any length whatever, so it could never have bounded the
-- drain.  Stated about the `all` itself rather than about `widNode`,
-- because widNode has since moved past it
no-node-bound : ∀ {n} {Γ : Ctx n} {s} (W : ℕ) (sl : Slots Γ)
  (o : Closed Γ s) → (pWᵉ n sl o ≤ᵇ W) ≡ true → (B : ℕ) →
  Σ (List (Closed Γ s)) λ q →
    (all (λ x → pWᵉ n sl x ≤ᵇ W) q ≡ true) × (B < length q)
no-node-bound {n = n} W sl o ho B =
  rep-list (suc B) o
  , rep-all (λ x → pWᵉ n sl x ≤ᵇ W) (suc B) o ho
  , subst (λ x → B < x) (sym (rep-len (suc B) o)) ≤-refl

------------------------------------------------------------------
-- § 3.  +1-SUPERADDITIVITY OF THE WHOLE FAMILY.  `suc (f J) ≤ f (suc J)`
-- for each of the five transformers, by the same mutual recursion and
-- the same argument order (m, then d, then k) as .Caps's `-mono` block,
-- which is what makes the termination check go through unchanged
------------------------------------------------------------------

-- All five are proven in .Caps-Sadd, which this probe imports: the
-- statement is arithmetic about the transformer family, consumed as a
-- finished fact, so it is a compilation unit of its own.

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

-- `walk-step-lift` and `walk-step-suc` are in .Caps-Sadd § 2.

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

------------------------------------------------------------------
-- § 5.  THE THREE LIFECYCLE ROWS of the queue-length invariant § 2b
-- calls for.  `qOK` below is the concat clause `widNode` is to be
-- changed to; the rows are the three ways a concat node's queue is ever
-- written, read off the evaluator:
--
--   BIRTH   .Evaluator:1433 — `concat-st [] false false`, the ONLY site
--           that installs a fresh concat node.  Empty.
--   PUSH    .Evaluator:1107 — `concat-st (q ++ o ∷ []) true od`, the
--           inner-busy branch of `thruConsume`.  The one growing write.
--   RE-PARK .Evaluator:1114 — `concat-st [] (not done) od`, the
--           inner-idle branch.  Empty again, so it is BIRTH's row.
--   MARK    .Evaluator:1161 — `concat-st q act true`, `thruWrap`'s
--           outer-done flag.  q untouched, so widening alone.
--   DRAIN   .Evaluator:1207 — `concat-st q′ act′ od`, where `q′` is what
--           `concatDrain` returns: `[]`, or the tail after one cons.
--
-- So exactly one row does arithmetic, and it is the push.
------------------------------------------------------------------

allB-++ : ∀ {A : Set} (p : A → Bool) (xs ys : List A) →
  all p xs ≡ true → all p ys ≡ true → all p (xs ++ ys) ≡ true
allB-++ p []       ys hx hy = hy
allB-++ p (x ∷ xs) ys hx hy with ∧-true (p x) (all p xs) hx
... | h₁ , h₂ = ∧-intro h₁ (allB-++ p xs ys h₂ hy)

-- THE PROPOSED CLAUSE.  The pointwise bound `widNode` already carries,
-- and the cardinality § 2 proved is not derivable from it
qOK : ∀ {n} {Γ : Ctx n} {t} → ℕ → Slots Γ → List (Closed Γ t) → Bool
qOK {n = n} W sl q = all (λ o → pWᵉ n sl o ≤ᵇ W) q ∧ (length q ≤ᵇ W)

-- ROW 1 — ESTABLISHMENT.  The birth queue is `[]` at every install
-- site, so the row holds at EVERY width, with no side condition and no
-- appeal to `capsAt`'s cSize construction at all.  Not structural
birth-row : ∀ {n} {Γ : Ctx n} {t} (W : ℕ) (sl : Slots Γ) →
  qOK {Γ = Γ} {t = t} W sl [] ≡ true
birth-row W sl = refl

-- one level of width dominates one more queue item, with the same
-- `suc w ≤ foldStep S w` margin the count receipts already use
wid-suc-step : ∀ (c : Caps) (L : ℕ) → 2 ≤ Caps.cSize c →
  suc (Caps.cWid (frameStep L c)) ≤ Caps.cWid (frameStep (suc L) c)
wid-suc-step c L hS =
  subst (λ x → suc (Caps.cWid (frameStep L c)) ≤ x)
        (sym (frameStep-wid-suc c L))
        (suc≤foldStep (Caps.cSize c) (Caps.cWid (frameStep L c)) hS)

-- ROW 2 — PUSH PRESERVATION, at the witness `1` § 2b demands.  The
-- pushed observable arrives admissible at the READ level j (that is
-- `thruConsume-caps`'s own hypothesis), and one level pays for the cons.
-- LANDED as .Caps-Face's `widNode-push` (on `wid-suc-step`), with the
-- witness bumped 0 ↦ 1 at thruConsume-caps's concat-push clause; the
-- drain row landed as `concatDrain-qlen`, read off the evaluator's three
-- returns rather than off `qOK`.  Kept here because these are the rows
-- the shape was CHOSEN from, and § 2 above is why it had to change
push-row : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (q : List (Closed Γ t)) (o : Closed Γ t) → 2 ≤ Caps.cSize c →
  qOK (Caps.cWid (frameStep j c)) sl q ≡ true →
  (pWᵉ n sl o ≤ᵇ Caps.cWid (frameStep j c)) ≡ true →
  qOK (Caps.cWid (frameStep (suc j) c)) sl (q ++ o ∷ []) ≡ true
push-row {n = n} c j sl q o hS hq ho
  with ∧-true (all (λ x → pWᵉ n sl x ≤ᵇ Caps.cWid (frameStep j c)) q)
              (length q ≤ᵇ Caps.cWid (frameStep j c)) hq
... | hall , hlen = ∧-intro pw card
  where
  W  = Caps.cWid (frameStep j c)
  W′ = Caps.cWid (frameStep (suc j) c)

  wide : W ≤ W′
  wide = ≤-trans (n≤1+n W) (wid-suc-step c j hS)

  pw : all (λ x → pWᵉ n sl x ≤ᵇ W′) (q ++ o ∷ []) ≡ true
  pw = allB-++ (λ x → pWᵉ n sl x ≤ᵇ W′) q (o ∷ [])
         (all-impl _ _ (λ x → ≤ᵇ-widen (pWᵉ n sl x) wide) q hall)
         (∧-intro (≤ᵇ-widen (pWᵉ n sl o) wide ho) refl)

  card : (length (q ++ o ∷ []) ≤ᵇ W′) ≡ true
  card = ≤ᵇ-true (length (q ++ o ∷ [])) W′
           (≤-trans (≤-reflexive (trans (length-++ q) (+-comm (length q) 1)))
                    (≤-trans (s≤s (≤ᵇ⇒≤ (length q) W (T-to hlen)))
                             (wid-suc-step c j hS)))

-- ROW 3 — DRAIN PRESERVATION.  `concatDrain` only ever SHORTENS: its
-- drain-on branch returns the tail after one cons, its exhausted branch
-- returns `[]` (ROW 1).  So the row is one cons off the front plus the
-- widening every clause of the clique performs anyway
drain-row : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (j j′ : ℕ) (sl : Slots Γ)
  (o : Closed Γ t) (q : List (Closed Γ t)) → 2 ≤ Caps.cSize c →
  qOK (Caps.cWid (frameStep j c)) sl (o ∷ q) ≡ true →
  qOK (Caps.cWid (frameStep (j + j′) c)) sl q ≡ true
drain-row {n = n} c j j′ sl o q hS hq
  with ∧-true ((pWᵉ n sl o ≤ᵇ Caps.cWid (frameStep j c))
                 ∧ all (λ x → pWᵉ n sl x ≤ᵇ Caps.cWid (frameStep j c)) q)
              (suc (length q) ≤ᵇ Caps.cWid (frameStep j c)) hq
... | hall , hlen
  with ∧-true (pWᵉ n sl o ≤ᵇ Caps.cWid (frameStep j c))
              (all (λ x → pWᵉ n sl x ≤ᵇ Caps.cWid (frameStep j c)) q) hall
... | _ , hq′ = ∧-intro pw card
  where
  W  = Caps.cWid (frameStep j c)
  W′ = Caps.cWid (frameStep (j + j′) c)

  wide : W ≤ W′
  wide = widAt-mono hS ≤-refl ≤-refl (m≤m+n j j′)

  pw : all (λ x → pWᵉ n sl x ≤ᵇ W′) q ≡ true
  pw = all-impl _ _ (λ x → ≤ᵇ-widen (pWᵉ n sl x) wide) q hq′

  card : (length q ≤ᵇ W′) ≡ true
  card = ≤ᵇ-true (length q) W′
           (≤-trans (≤-trans (n≤1+n (length q))
                             (≤ᵇ⇒≤ (suc (length q)) W (T-to hlen)))
                    wide)

-- ROW 4 — MARK, and the RE-PARK that is ROW 1 again.  Both are pure
-- widenings of a queue already admitted, so they need nothing new; the
-- statement is here so the four writes are all accounted for
mark-row : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (j j′ : ℕ) (sl : Slots Γ)
  (q : List (Closed Γ t)) → 2 ≤ Caps.cSize c →
  qOK (Caps.cWid (frameStep j c)) sl q ≡ true →
  qOK (Caps.cWid (frameStep (j + j′) c)) sl q ≡ true
mark-row {n = n} c j j′ sl q hS hq
  with ∧-true (all (λ x → pWᵉ n sl x ≤ᵇ Caps.cWid (frameStep j c)) q)
              (length q ≤ᵇ Caps.cWid (frameStep j c)) hq
... | hall , hlen = ∧-intro
  (all-impl _ _ (λ x → ≤ᵇ-widen (pWᵉ n sl x) wide) q hall)
  (≤ᵇ-widen (length q) wide hlen)
  where
  wide : Caps.cWid (frameStep j c) ≤ Caps.cWid (frameStep (j + j′) c)
  wide = widAt-mono hS ≤-refl ≤-refl (m≤m+n j j′)

-- and the margin, computed: a push at the smallest caps the face admits
-- takes the queue budget 1 ↦ 4 ↦ 32, so the invariant is nowhere tight
_ : (suc 1 ≤ᵇ widAt 2 1 1) ≡ true
_ = refl

_ : (suc 4 ≤ᵇ widAt 2 1 2) ≡ true
_ = refl
