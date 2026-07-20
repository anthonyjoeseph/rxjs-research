-- THE PROOF (in progress) of budget sufficiency: the seeded sync
-- budget never runs dry on a canonical run — the old TERMINATING
-- pragma's claim, decomposed.
--
-- Architecture: an instant-indexed size invariant.  The only things
-- that grow across a run are the runtime values stored in the
-- machine (schedule pendings, scan accumulators, concat queues);
-- everything else is fixed program syntax.  One cascade's work is
-- template instantiation over those stores, so per instant the
-- largest stored value multiplies by at most the program's own
-- size — dominated by the budget's 2^size-per-instant growth.
--
--   stBounded? B          — every stored value's size ≤ B (decidable)
--   INV at instant id     — stBounded? (budgetAt … id)
--   burst-dry/-bounded    — the root burst neither dries nor escapes
--   cascade-dry           — one cascade preserves INV and stays wet
--   drain-dry (PROVEN)    — the fuel loop composes cascades
--   budget-sufficient     — (PROVEN from the above) the whole run
--
-- pop-slots/pop-bounded are PROVEN (by inverting liveNext, hoisted
-- to top level for exactly this).  Three postulated cores remain:
-- burst-* and cascade-dry, the real termination content, to be
-- proven by fuel-accounting induction over the subscription
-- machine's clauses (each of the three decrement edges consumes one
-- unit; the work between decrements is structural), with the growth
-- arithmetic closing the loop.  Not imported by Main until the
-- splice into Verify-Well-Formed replaces its postulate.
module Verify-Budget-Sufficient where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans)
open import Data.List    using (List; []; _∷_; _++_; all; any)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                                Ctx; Closed; Val; sizeᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                root; sched-init; st-init; sched-next;
                                liveHead; liveNext; arrEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                dropSource; arrSource;
                                subscribeE; cascade; drain; evaluate;
                                hasDry; dryEvent; drySource; sameSource;
                                budgetAt)

------------------------------------------------------------------
-- dry-freeness composes over ++ (the other direction from
-- Verify-Well-Formed's hasDry-++ split)
------------------------------------------------------------------

∨-false : ∀ (a b : Bool) → a ∨ b ≡ false → (a ≡ false) × (b ≡ false)
∨-false false b h = refl , h
∨-false true  b ()

hasDry-append : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry xs ≡ false → hasDry ys ≡ false → hasDry (xs ++ ys) ≡ false
hasDry-append []        ys h₁ h₂ = h₂
hasDry-append (em ∷ xs) ys h₁ h₂
  with ∨-false (sameSource (InstEmit.source em) drySource) _ h₁
... | e₁ , h₁′
  with ∨-false (any dryEvent (InstEmit.events em)) _ h₁′
... | e₂ , h₁″ rewrite e₁ | e₂ = hasDry-append xs ys h₁″ h₂

------------------------------------------------------------------
-- the size of a runtime value: embedded observables count their
-- full syntax; base payloads are opaque
------------------------------------------------------------------

sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
sizeᵛ unitᵗ    _        = 1
sizeᵛ boolᵗ    _        = 1
sizeᵛ natᵗ     _        = 1
sizeᵛ (s ×ᵗ t) (a , b)  = suc (sizeᵛ s a + sizeᵛ t b)
sizeᵛ (s +ᵗ t) (inj₁ a) = suc (sizeᵛ s a)
sizeᵛ (s +ᵗ t) (inj₂ b) = suc (sizeᵛ t b)
sizeᵛ (obs t)  e        = sizeᵉ e

------------------------------------------------------------------
-- the machine's value stores, bounded: schedule pendings, scan
-- accumulators, concat queues.  Registry paths and slot defs are
-- fixed syntax — no growth, no clause
------------------------------------------------------------------

boundedLive : ∀ {n} {Γ : Ctx n} → ℕ → LiveSource Γ → Bool
boundedLive B l =
  all (λ tv → sizeᵛ (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ B)
      (LiveSource.pending l)

boundedNode : ∀ {n} {Γ : Ctx n} → ℕ → NodeState Γ → Bool
boundedNode B (scan-st {t} v)      = sizeᵛ t v ≤ᵇ B
boundedNode B (concat-st q _ _)    = all (λ o → sizeᵉ o ≤ᵇ B) q
boundedNode B (take-st _)          = true
boundedNode B (merge-st _ _)       = true
boundedNode B (switch-st _ _)      = true
boundedNode B (exhaust-st _ _)     = true

stBounded? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → ℕ → Sched Γ → EvalSt e → Bool
stBounded? B sched st =
  all (boundedLive B) (Sched.live sched)
  ∧ all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st)

------------------------------------------------------------------
-- popping the next arrival: the slots are fixed by the record
-- update, and boundedness survives because one pending list shrinks
-- and everything else is untouched — PROVEN by inverting liveNext
------------------------------------------------------------------

∧-true : ∀ (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true true  b h = refl , h
∧-true false b ()

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-intro refl refl = refl

liveHead-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  liveHead l ≡ inj₂ (a , l′) →
  boundedLive B l ≡ true → boundedLive B l′ ≡ true
liveHead-bounded B l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

liveNext-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  liveNext ls ≡ inj₂ (a , ls′) →
  all (boundedLive B) ls ≡ true → all (boundedLive B) ls′ ≡ true
liveNext-bounded B (l ∷ ls) eq bnd
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) bnd
... | bl , bls with liveHead l in eqH | liveNext ls in eqR
liveNext-bounded B (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (liveNext-bounded B ls eqR bls)
liveNext-bounded B (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (liveHead-bounded B l eqH bl) bls
liveNext-bounded B (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with arrEarlier a″ a′ | eq
... | true  | refl = ∧-intro (liveHead-bounded B l eqH bl) bls
... | false | refl = ∧-intro bl (liveNext-bounded B ls eqR bls)

pop-slots : ∀ {n} {Γ : Ctx n}
  (sched : Sched Γ) {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  Sched.slots sched′ ≡ Sched.slots sched
pop-slots sched eq with liveNext (Sched.live sched) | eq
... | inj₂ (a″ , ls) | refl = refl

pop-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  stBounded? B sched st ≡ true → stBounded? B sched′ st ≡ true
pop-bounded B sched st eq bnd
  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
... | bls , bns with liveNext (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      ∧-intro (liveNext-bounded B (Sched.live sched) eqL bls) bns

------------------------------------------------------------------
-- structural preservation around the cascade — PROVEN pieces the
-- eventual cascade-dry proof composes, whatever its core shape
------------------------------------------------------------------

T-to : ∀ {b : Bool} → b ≡ true → T b
T-to refl = tt

-- generic: a pointwise implication lifts through all
all-impl : ∀ {A : Set} (p q : A → Bool) →
  (∀ x → p x ≡ true → q x ≡ true) →
  ∀ (xs : List A) → all p xs ≡ true → all q xs ≡ true
all-impl p q imp []       h = refl
all-impl p q imp (x ∷ xs) h
  with ∧-true (p x) (all p xs) h
... | px , pxs = ∧-intro (imp x px) (all-impl p q imp xs pxs)

≤ᵇ-widen : ∀ (v : ℕ) {B B′ : ℕ} → B ≤ B′ → (v ≤ᵇ B) ≡ true → (v ≤ᵇ B′) ≡ true
≤ᵇ-widen v {B} {B′} le h with ≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ v B (T-to h)) le)
... | w = T-elim w
  where
  T-elim : ∀ {b : Bool} → T b → b ≡ true
  T-elim {true} _ = refl

-- a bound only ever needs to be respected upward: the id-level bound
-- entails the suc-id-level one (budgets grow monotonically)
bounded-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {B B′ : ℕ} → B ≤ B′ → (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true → stBounded? B′ sched st ≡ true
bounded-mono {B = B} {B′} le sched st bnd
  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
... | bls , bns =
  ∧-intro
    (all-impl (boundedLive B) (boundedLive B′)
      (λ l → all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ (LiveSource.elemTy l) (proj₂ tv)) le) (LiveSource.pending l))
      (Sched.live sched) bls)
    (all-impl _ _ (λ kv → node-mono (proj₂ kv)) (EvalSt.nodes st) bns)
  where
  node-mono : ∀ nd → boundedNode B nd ≡ true → boundedNode B′ nd ≡ true
  node-mono (scan-st {t} v)   h = ≤ᵇ-widen (sizeᵛ t v) le h
  node-mono (concat-st q _ _) h = all-impl _ _ (λ o → ≤ᵇ-widen (sizeᵉ o) le) q h
  node-mono (take-st _)       h = refl
  node-mono (merge-st _ _)    h = refl
  node-mono (switch-st _ _)   h = refl
  node-mono (exhaust-st _ _)  h = refl

-- the latch touches only per-cascade ledger fields — the value
-- stores are untouched
latch-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (sched : Sched Γ) (a : Arrival Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true →
  stBounded? B sched (cascadeLatch a st) ≡ true
latch-bounded B sched a st bnd with Arrival.isLast a
... | true  = bnd
... | false = bnd

-- the sweep is a filter: every survivor was already bounded
sweepLive-bounded : ∀ {n} {Γ : Ctx n} {t} (B : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (boundedLive B) ls ≡ true →
  all (boundedLive B) (sweepLive reg ls) ≡ true
sweepLive-bounded B reg []       h = refl
sweepLive-bounded {n = n} B reg (l ∷ ls) h
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) h
... | bl , bls
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ∧-intro bl (sweepLive-bounded B reg ls bls)
... | false = sweepLive-bounded B reg ls bls

-- the finish drops registry entries (unread by stBounded?) and
-- filters the live schedule
finish-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true →
  stBounded? B (proj₁ (cascadeFinish a sched st))
               (proj₂ (cascadeFinish a sched st)) ≡ true
finish-bounded B a sched st bnd with Arrival.isLast a
... | false = bnd
... | true  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
...   | bls , bns =
        ∧-intro (sweepLive-bounded B
                  (dropSource (arrSource a) (EvalSt.registry st))
                  (Sched.live sched) bls)
                bns

------------------------------------------------------------------
-- the three cores
------------------------------------------------------------------

postulate
  -- the root burst neither dries nor escapes instant 1's budget:
  -- fuel-accounting over subscribeE's clauses — the subscribe frame's
  -- values are evalTm outputs over empty environments, sized within
  -- the program's own syntax
  burst-dry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                              (sched-init e ins) (st-init e))) ≡ false

  burst-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in stBounded? (budgetAt e (Sched.slots (proj₁ (proj₂ r))) 1)
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

  -- THE termination content, one instant at a time: from a state
  -- within instant id's budget, the cascade at id stays wet (its
  -- chainStep seeds exactly this budget) and lands within instant
  -- suc id's — one cascade's template instantiation multiplies
  -- stored-value sizes by at most a program-syntax factor, and the
  -- budget grows by 2^size per instant.  Stated self-referentially
  -- through each sched's own slots, so no threading lemmas leak in
  cascade-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    stBounded? (budgetAt e (Sched.slots sched) id) sched st ≡ true →
    let r = cascade a id sched st
    in (hasDry (proj₁ r) ≡ false)
       × (stBounded? (budgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                     (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- the fuel loop composes cascades — PROVEN
------------------------------------------------------------------

drain-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (budgetAt e (Sched.slots sched) id) sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry zero    id sched st bnd = refl
drain-dry (suc k) id sched st bnd with sched-next sched in eq
... | inj₁ _            = refl
drain-dry {e = e} (suc k) id sched st bnd | inj₂ (a , sched′) =
  let bnd′ : stBounded? (budgetAt e (Sched.slots sched′) id) sched′ st ≡ true
      bnd′ = subst
               (λ sl → stBounded? (budgetAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-bounded (budgetAt e (Sched.slots sched) id) sched st eq bnd)
      (dry₁ , bnd″) = cascade-dry a id sched′ st bnd′
  in hasDry-append (proj₁ (cascade a id sched′ st)) _
       dry₁
       (drain-dry k (suc id)
         (proj₁ (proj₂ (cascade a id sched′ st)))
         (proj₂ (proj₂ (cascade a id sched′ st)))
         bnd″)

------------------------------------------------------------------
-- the theorem: same statement as Verify-Well-Formed's postulate;
-- the splice (coordinated, later) replaces that postulate with this
------------------------------------------------------------------

budget-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
budget-sufficient fuel e ins =
  hasDry-append
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)))
    _
    (burst-dry e ins)
    (drain-dry fuel 1
      (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e))))
      (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e))))
      (burst-bounded e ins))
