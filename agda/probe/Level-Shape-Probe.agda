------------------------------------------------------------------
-- THE LEVEL CONJUNCT'S SHAPE, PER MEMBER, before any of it is ground.
--
-- Step C gives each member of the subscribe clique a conjunct bounding
-- the level it LEAVES, in the transformer that member's own iteration
-- is priced by.  Three things are worth settling before forty-two
-- clauses are rewritten to report one, and none of them is arithmetic
-- about the transformers — that is § 5 of Sub-Charge-Probe, already
-- proven.  These are about whether the conjunct SAYS anything and
-- whether each member can supply the index its transformer reads.
--
-- § 1  THE Σ-WITNESS LAW, discharged rather than asserted.  The clique's
--   Σ reports a witness j′ and three conjuncts about it, and every one
--   of those three is UPWARD-CLOSED: `capsOK?`, `burstCaps?` and
--   `burstCount?` are all read at `frameStep (j + j′) c`, and the caps
--   only widen as j′ grows (that is `capsOK?-mono` and friends, which
--   the clique spends everywhere).  So the Σ as it stands is satisfiable
--   by making j′ enormous, and its content is exactly zero.
--
--   The level conjunct is the one that is DOWNWARD-closed in j′ — it is
--   an upper bound — so adding it is what gives the whole Σ content.
--   § 1 states both halves and proves them, so the law is discharged
--   with a witness rather than by inspection.
--
-- § 2  THE WALK'S INDEX IS THE PAYLOAD COUNT, and the face supplies it.
--   `sIterD S W d k m J` prices m payloads in sequence, so a walk's
--   conjunct reads `m = length vals` — while `frame-step` consumes the
--   walk at `m = suc (widAt S W j)`.  Those meet because `valsCaps?`
--   carries a length conjunct, and `Caps.cWid (frameStep j c)` IS
--   `widAt (cSize c) (cWid c) j` definitionally.
--
-- § 3  AND THE BUDGET DOES NOT DESCEND AT A CARRYING EDGE.  Batch C's
--   finding, stated as the rows Step C will actually spend: a chain edge
--   and a μ edge both keep the budget, and only the clause that REPORTS
--   `sLvlD S W d (suc k) J` turns it into an `opIterD` at k.  So no
--   clause needs a case split on the budget to carry the hypothesis;
--   the split belongs to whichever clause reports the descent.
------------------------------------------------------------------
module Level-Shape-Probe where

open import Data.Bool using (Bool; true)
open import Data.Nat  using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤ᵇ⇒≤; n≤1+n; +-monoʳ-≤)
open import Data.List using (List; length)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; Ty)
open import Rx.Evaluator
  using (Slots; sizeAt; widAt; sLvlD; sIterD; opIterD; sLvlD-suc; sLvlD-0)
open import Verify-Budget-Sufficient.Measures using (T-to)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; sIterD-mono; sLvlD-infl)
open import Verify-Budget-Sufficient.Caps-Face using (valsCaps?)
open import Verify-Budget-Sufficient.Subscribe-Face using (valsLen)

------------------------------------------------------------------
-- § 1.  THE Σ-WITNESS LAW.
------------------------------------------------------------------

-- the OLD conjuncts survive enlarging the witness — stated on the
-- level index they are all read at, which is the only way j′ enters
-- them.  `capsOK?`/`burstCaps?`/`burstCount?` are monotone in that
-- index (capsOK?-mono, burstCaps?-widen, …), so this is their shape
Upward-Closed : Set
Upward-Closed = ∀ (j a b : ℕ) → a ≤ b → j + a ≤ j + b

upward-closed : Upward-Closed
upward-closed j a b h = +-monoʳ-≤ j h

-- so a Σ whose every conjunct is upward-closed in the witness is
-- satisfied by any large enough one, and says nothing about the witness
-- the clause actually reports
vacuous-if-only-upward : ∀ (P : ℕ → Set) →
  (∀ a b → a ≤ b → P a → P b) → P 0 → ∀ n → P n
vacuous-if-only-upward P mono p0 n = mono 0 n z≤n p0

-- THE LEVEL CONJUNCT IS THE OTHER DIRECTION: an upper bound on the
-- witness, so enlarging j′ breaks it.  That is exactly why adding it
-- gives the Σ content, and the refutation is the smallest there is —
-- an empty budget is the identity transformer, so at j = 0 the level a
-- subscribe may leave is 0, and a witness of 1 does not fit in it
Level-Upward-Closed : Set
Level-Upward-Closed = ∀ (S W d k j a b : ℕ) →
  a ≤ b → j + a ≤ sLvlD S W d k j → j + b ≤ sLvlD S W d k j

level-not-upward-closed : Level-Upward-Closed → ⊥
level-not-upward-closed H = bad (H 2 1 0 0 0 0 1 z≤n ok)
  where
  ok : 0 + 0 ≤ sLvlD 2 1 0 0 0
  ok rewrite sLvlD-0 2 1 0 0 = z≤n

  bad : 0 + 1 ≤ sLvlD 2 1 0 0 0 → ⊥
  bad h with sLvlD-0 2 1 0 0
  ... | e rewrite e = absurd h
    where
    absurd : 1 ≤ 0 → ⊥
    absurd ()

------------------------------------------------------------------
-- § 2.  THE WALK'S INDEX.
------------------------------------------------------------------

-- the frame's width cap IS the transformer's width, definitionally, so
-- a payload count read off `valsCaps?` is a count the walk transformer
-- can be instantiated at with no arithmetic in between
frameStep-wid : ∀ (c : Caps) (j : ℕ) →
  Caps.cWid (frameStep j c) ≡ widAt (Caps.cSize c) (Caps.cWid c) j
frameStep-wid c j = refl

-- and the walk at the payload count is dominated by the walk at the
-- count `frame-step` reads, which is the one inequality the two shapes
-- need to meet
walk-index : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (vals : List (Val Γ s)) (d k J : ℕ) → 2 ≤ Caps.cSize c →
  valsCaps? (frameStep j c) sl vals ≡ true →
  sIterD (Caps.cSize c) (Caps.cWid c) d k (length vals) J
    ≤ sIterD (Caps.cSize c) (Caps.cWid c) d k
        (suc (widAt (Caps.cSize c) (Caps.cWid c) j)) J
walk-index c j sl vals d k J 2≤S vC =
  sIterD-mono (length vals)
    (suc (widAt (Caps.cSize c) (Caps.cWid c) j)) d d k k 2≤S
    ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
    (valsLen (frameStep j c) sl vals vC)

------------------------------------------------------------------
-- § 3.  THE BUDGET DESCENDS ONLY WHERE IT IS REPORTED.
------------------------------------------------------------------

-- The ONE place a unit of budget is spent is the clause that REPORTS the
-- descent, and it is a clause equation rather than a choice: `sIterD`,
-- `opIterD` and `fIterD` all pass k through untouched, so a carrying
-- edge cannot spend one even if it wanted to.  That is why no clause
-- needs a case split on the budget to thread the hypothesis — batch C's
-- finding, read off the family rather than off the clique
spend-at-report : ∀ (S W d k J : ℕ) →
  sLvlD S W d (suc k) J ≡ opIterD S W d k (suc (sizeAt S J)) J
spend-at-report = sLvlD-suc
