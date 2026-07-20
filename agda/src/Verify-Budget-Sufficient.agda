-- THE PROOF (in progress) of budget sufficiency: the seeded sync
-- budget never runs dry on a canonical run — the old TERMINATING
-- pragma's claim, decomposed.
--
-- Architecture: an instant-indexed size invariant.  The only things
-- that grow across a run are the runtime values stored in the
-- machine (schedule pendings, scan accumulators, concat queues);
-- everything else is fixed program syntax.  Both fuel demand and
-- stored-value sizes TOWER (chained obs-typed scans exponentiate at
-- each story — the 2026-07-19 attack, see syncBudget's comment in
-- Rx.Evaluator), so the Gas budget is a tower and sizeBudgetAt is
-- its ℕ shadow for the ≤ᵇ-decidable store invariant.
--
--   stBounded? B          — every stored value's size ≤ B (decidable)
--   INV at instant id     — stBounded? (sizeBudgetAt … id)
--   burst-dry/-bounded    — the root burst neither dries nor escapes
--   cascadeGo-wet         — the chain fold stays wet, lands bounded
--   cascade-dry (PROVEN)  — latch + fold core + finish, composed
--   drain-dry (PROVEN)    — the fuel loop composes cascades
--   budget-sufficient     — (PROVEN from the above) the whole run
--
-- PROVEN: pop-slots/pop-bounded (inverting schedGo, hoisted for
-- exactly this), the cascade's structural ring (latch/sweep/finish/
-- mono), cascade-dry, drain-dry, and the theorem.  Three postulated
-- cores remain — burst-dry, burst-bounded, cascadeGo-wet — the real
-- termination content: fuel-accounting induction over the
-- subscription machine's clauses (the three decrement edges each
-- consume one unit; everything between is structural), the
-- registration-disjointness argument at the fold, and the tower
-- monotonicity/dominance arithmetic.  Not imported by Main until the splice into
-- Verify-Well-Formed replaces its postulate.
module Verify-Budget-Sufficient where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.List    using (List; []; _∷_; _++_; all; any; length;
                                sum; tabulate; concat; map)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                                Ctx; Closed; Val; sizeᵉ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                root; sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                dropSource; arrSource; chainsOf; cascadeGo;
                                Path; arrTy;
                                subscribeE; cascade; drain; evaluate;
                                hasDry; dryEvent; drySource; sameSource;
                                budgetAt; slotsSize)

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
-- the ℕ-valued SIZE budget for the stored-value invariant: the same
-- tower shape as the Gas fuel budget (stored values tower exactly as
-- fuel demand does — the scan attack compounds both), but as a ℕ so
-- it can bound sizeᵛ via ≤ᵇ.  Proof-side only: never computed on a
-- concrete program, so strictness is irrelevant here
------------------------------------------------------------------

n<2^n : ∀ n → n < 2 ^ n
n<2^n zero    = s≤s z≤n
n<2^n (suc n) = ≤-trans step (≤-reflexive shape)
  where
  step : suc (suc n) ≤ 2 ^ n + 2 ^ n
  step = ≤-trans (+-monoˡ-≤ (suc n) (s≤s z≤n))
                 (+-mono-≤ (n<2^n n) (n<2^n n))
  shape : 2 ^ n + 2 ^ n ≡ 2 ^ suc n
  shape = cong (2 ^ n +_) (sym (+-identityʳ (2 ^ n)))

towerℕ : ℕ → ℕ
towerℕ zero    = 1
towerℕ (suc h) = 2 ^ towerℕ h

sizeBudgetAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Id → ℕ
sizeBudgetAt e sl id = towerℕ (suc (sizeᵉ e + slotsSize sl) * suc id)

towerℕ-mono : ∀ {m n} → m ≤ n → towerℕ m ≤ towerℕ n
towerℕ-mono {zero}  {zero}  h = ≤-refl
towerℕ-mono {zero}  {suc n} h =
  ≤-trans (towerℕ-mono {zero} {n} z≤n)
          (≤-trans (n≤1+n (towerℕ n)) (n<2^n (towerℕ n)))
towerℕ-mono {suc m} {suc n} (s≤s h) = ^-monoʳ-≤ 2 (towerℕ-mono h)

sizeBudgetAt-mono : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
  (sl : Slots Γ) {id id′ : Id} → id ≤ id′ →
  sizeBudgetAt e sl id ≤ sizeBudgetAt e sl id′
sizeBudgetAt-mono e sl h =
  towerℕ-mono (*-monoʳ-≤ (suc (sizeᵉ e + slotsSize sl)) (s≤s h))

------------------------------------------------------------------
-- the Gas ordering: `g hasAtLeast n` — n peels are available.  The
-- wet-contract lemmas consume fuel through this view (an `hs` match
-- exposes the `gs` the machine's decrement edges pattern-match on),
-- and the budget lemmas below discharge it: the gasPad literal head
-- alone covers any n ≤ 2^(sz·(id+1)²), and head+tower covers the
-- tower-sized needs of chained-scan programs
------------------------------------------------------------------

data _hasAtLeast_ : Gas → ℕ → Set where
  hz : ∀ {g} → g hasAtLeast zero
  hs : ∀ {g n} → g hasAtLeast n → gs g hasAtLeast suc n

hasAtLeast-mono : ∀ {g m n} → n ≤ m → g hasAtLeast m → g hasAtLeast n
hasAtLeast-mono z≤n       _        = hz
hasAtLeast-mono (s≤s le) (hs h) = hs (hasAtLeast-mono le h)

hasAtLeast-pad : ∀ (m : ℕ) (g : Gas) {n} → n ≤ m → gasPad m g hasAtLeast n
hasAtLeast-pad m       g z≤n      = hz
hasAtLeast-pad (suc m) g (s≤s le) = hs (hasAtLeast-pad m g le)

hasAtLeast-pad-plus : ∀ (m : ℕ) {g : Gas} {n} →
  g hasAtLeast n → gasPad m g hasAtLeast (m + n)
hasAtLeast-pad-plus zero    h = h
hasAtLeast-pad-plus (suc m) h = hs (hasAtLeast-pad-plus m h)

hasAtLeast-double : ∀ {g n} → g hasAtLeast n → gasDouble g hasAtLeast (n + n)
hasAtLeast-double hz = hz
hasAtLeast-double (hs {g} {n} h) =
  hs (subst (λ k → gs (gasDouble g) hasAtLeast k) (sym (+-suc n n))
       (hs (hasAtLeast-double h)))

-- 2^g is never empty, whatever g is
pow2-min : ∀ (g : Gas) → gasPow2 g hasAtLeast 1
pow2-min g0     = hs hz
pow2-min (gs g) =
  hasAtLeast-mono (s≤s z≤n) (hasAtLeast-double (pow2-min g))

hasAtLeast-pow2 : ∀ {g n} → g hasAtLeast n → gasPow2 g hasAtLeast (2 ^ n)
hasAtLeast-pow2 {g} hz = pow2-min g
hasAtLeast-pow2 {n = suc n} (hs {g} h) =
  subst (λ k → gasDouble (gasPow2 g) hasAtLeast (2 ^ n + k))
        (sym (+-identityʳ (2 ^ n)))
        (hasAtLeast-double (hasAtLeast-pow2 h))

hasAtLeast-tower : ∀ (h : ℕ) → gasTower h hasAtLeast towerℕ h
hasAtLeast-tower zero    = hs hz
hasAtLeast-tower (suc h) = hasAtLeast-pow2 (hasAtLeast-tower h)

-- what the seeded budget guarantees: the full head plus the tower
-- (height (4+sz)·(id+1) — three stories above sizeBudgetAt's, the
-- headroom the wet contract's rank demand consumes)
budget-hasAtLeast : ∀ (sz : ℕ) (id : Id) →
  gasPad (2 ^ (sz * suc id * suc id)) (gasTower ((4 + sz) * suc id))
    hasAtLeast (2 ^ (sz * suc id * suc id) + towerℕ ((4 + sz) * suc id))
budget-hasAtLeast sz id =
  hasAtLeast-pad-plus (2 ^ (sz * suc id * suc id))
                      (hasAtLeast-tower ((4 + sz) * suc id))

-- the peel every decrement-edge clause performs: enough fuel means
-- the machine's gs-match succeeds and the tail still has enough
hasAtLeast-peel : ∀ {g : Gas} {m : ℕ} → g hasAtLeast suc m →
  Σ Gas (λ g′ → (g ≡ gs g′) × (g′ hasAtLeast m))
hasAtLeast-peel (hs h) = _ , refl , h

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
-- and everything else is untouched — PROVEN by inverting schedGo
------------------------------------------------------------------

∧-true : ∀ (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true true  b h = refl , h
∧-true false b ()

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-intro refl refl = refl

schedHeadOf-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  boundedLive B l ≡ true → boundedLive B l′ ≡ true
schedHeadOf-bounded B l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (boundedLive B) ls ≡ true → all (boundedLive B) ls′ ≡ true
schedGo-bounded B (l ∷ ls) eq bnd
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-bounded B (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-bounded B ls eqR bls)
schedGo-bounded B (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-bounded B l eqH bl) bls
schedGo-bounded B (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-bounded B l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-bounded B ls eqR bls)

pop-slots : ∀ {n} {Γ : Ctx n}
  (sched : Sched Γ) {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  Sched.slots sched′ ≡ Sched.slots sched
pop-slots sched eq with schedGo (Sched.live sched) | eq
... | inj₂ (a″ , ls) | refl = refl

pop-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  stBounded? B sched st ≡ true → stBounded? B sched′ st ≡ true
pop-bounded B sched st eq bnd
  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
... | bls , bns with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      ∧-intro (schedGo-bounded B (Sched.live sched) eqL bls) bns

------------------------------------------------------------------
-- structural preservation around the cascade — PROVEN pieces the
-- eventual cascade-dry proof composes, whatever its core shape
------------------------------------------------------------------

T-to : ∀ {b : Bool} → b ≡ true → T b
T-to refl = tt

T⇒≡true : ∀ b → T b → b ≡ true
T⇒≡true true _ = refl

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

boundedLive-widen : ∀ {n} {Γ : Ctx n} {B B′ : ℕ} → B ≤ B′ →
  (l : LiveSource Γ) → boundedLive B l ≡ true → boundedLive B′ l ≡ true
boundedLive-widen le l =
  all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ (LiveSource.elemTy l) (proj₂ tv)) le)
           (LiveSource.pending l)

boundedNode-widen : ∀ {n} {Γ : Ctx n} {B B′ : ℕ} → B ≤ B′ →
  (ns : NodeState Γ) → boundedNode B ns ≡ true → boundedNode B′ ns ≡ true
boundedNode-widen le (scan-st {t} v)   h = ≤ᵇ-widen (sizeᵛ t v) le h
boundedNode-widen le (concat-st q _ _) h =
  all-impl _ _ (λ o → ≤ᵇ-widen (sizeᵉ o) le) q h
boundedNode-widen le (take-st _)       h = refl
boundedNode-widen le (merge-st _ _)    h = refl
boundedNode-widen le (switch-st _ _)   h = refl
boundedNode-widen le (exhaust-st _ _)  h = refl

-- the invariant survives raising the bound — composes cascades:
-- landing within (suc id)'s budget IS starting within (suc id)'s
stBounded-widen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {B B′ : ℕ} →
  B ≤ B′ → (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true → stBounded? B′ sched st ≡ true
stBounded-widen le sched st h
  with ∧-true _ _ h
... | hl , hn =
  ∧-intro (all-impl _ _ (λ l → boundedLive-widen le l) (Sched.live sched) hl)
          (all-impl _ _ (λ kv → boundedNode-widen le (proj₂ kv))
                    (EvalSt.nodes st) hn)

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

-- the finish never touches the slots either (record updates only)
finish-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (cascadeFinish a sched st)) ≡ Sched.slots sched
finish-slots a sched st with Arrival.isLast a
... | false = refl
... | true  = refl

------------------------------------------------------------------
-- LAYERED VALUES — the substrate the subscription measure lives on
-- (proof-design edge 3 below).  Every runtime obs value is a LAYER:
-- a template instantiated over embedded layered values.  subΘTm
-- reifies environment values in at var positions, so the embedded
-- values are literal subtrees of the resulting closed expression;
-- a value's layer tree is the derivation here, and its measure is
-- the multiset of its layers' template sizes.  The layer index is
-- `evalWith (strmᵗ tpl) env` — NOT subΘExp — so BOTH evaluator
-- clauses (closed template / instantiation) are definitional and
-- the closure lemma needs no substitution-identity lemma.
--
-- evalWith-layered is the machine-checked core of the edge-3
-- design: the evaluator never leaves the family, so neither can
-- the machine — every value it subscribes is an evalWith output
-- (map/scan fns, of-list elements, seeds) over layered inputs.
-- evalTm-layered/applyFn-layered are the forms the contract will
-- consume (evalTm at scan seeds and of-lists, applyFn at scan
-- steps).
------------------------------------------------------------------

mutual
  LayeredV : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → Set
  LayeredV unitᵗ    v = ⊤
  LayeredV boolᵗ    v = ⊤
  LayeredV natᵗ     v = ⊤
  LayeredV (s ×ᵗ t) v = LayeredV s (proj₁ v) × LayeredV t (proj₂ v)
  LayeredV (s +ᵗ t) (inj₁ a) = LayeredV s a
  LayeredV (s +ᵗ t) (inj₂ b) = LayeredV t b
  LayeredV (obs t)  e = LayeredObs e

  data LayeredObs {n} {Γ : Ctx n} {t : Ty} : Closed Γ t → Set where
    layer : ∀ {Θ} (tpl : Exp Γ [] [] Θ t) (env : All (Val Γ) Θ) →
            LayeredEnv env → LayeredObs (evalWith (strmᵗ tpl) env)

  data LayeredEnv {n} {Γ : Ctx n} : ∀ {Θ} → All (Val Γ) Θ → Set where
    []ˡ  : LayeredEnv []ᵃ
    _∷ˡ_ : ∀ {t Θ} {v : Val Γ t} {vs : All (Val Γ) Θ} →
           LayeredV t v → LayeredEnv vs → LayeredEnv (v ∷ᵃ vs)

lookupLayered : ∀ {n} {Γ : Ctx n} {Θ t} {env : All (Val Γ) Θ} →
  LayeredEnv env → (x : t ∈ Θ) → LayeredV t (lookupEnv env x)
lookupLayered (l ∷ˡ ls) (here refl) = l
lookupLayered (l ∷ˡ ls) (there x)   = lookupLayered ls x

evalWith-layered : ∀ {n} {Γ : Ctx n} {Θ t} (f : Tm Γ [] [] Θ t)
  (env : All (Val Γ) Θ) → LayeredEnv env → LayeredV t (evalWith f env)
evalWith-layered (varᵗ x)      env le = lookupLayered le x
evalWith-layered unit̂          env le = tt
evalWith-layered (bool̂ b)      env le = tt
evalWith-layered (nat̂ n)       env le = tt
evalWith-layered (pairᵗ a b)   env le =
  evalWith-layered a env le , evalWith-layered b env le
evalWith-layered (fstᵗ p)      env le = proj₁ (evalWith-layered p env le)
evalWith-layered (sndᵗ p)      env le = proj₂ (evalWith-layered p env le)
evalWith-layered (inlᵗ a)      env le = evalWith-layered a env le
evalWith-layered (inrᵗ a)      env le = evalWith-layered a env le
evalWith-layered (caseᵗ sc l r) env le
  with evalWith sc env | evalWith-layered sc env le
... | inj₁ x | lx = evalWith-layered l (x ∷ᵃ env) (lx ∷ˡ le)
... | inj₂ y | ly = evalWith-layered r (y ∷ᵃ env) (ly ∷ˡ le)
evalWith-layered (ifᵗ c a b)   env le with evalWith c env
... | true  = evalWith-layered a env le
... | false = evalWith-layered b env le
evalWith-layered (primᵗ add arg)  env le = tt
evalWith-layered (primᵗ sub arg)  env le = tt
evalWith-layered (primᵗ mul arg)  env le = tt
evalWith-layered (primᵗ eqᵖ arg)  env le = tt
evalWith-layered (primᵗ ltᵖ arg)  env le = tt
evalWith-layered (primᵗ notᵖ arg) env le = tt
evalWith-layered (strmᵗ e)     env le = layer e env le

evalTm-layered : ∀ {n} {Γ : Ctx n} {t} (f : Tm Γ [] [] [] t) →
  LayeredV t (evalTm f)
evalTm-layered f = evalWith-layered f []ᵃ []ˡ

applyFn-layered : ∀ {n} {Γ : Ctx n} {s t} (fn : Fn Γ [] [] [] s t)
  (v : Val Γ s) → LayeredV s v → LayeredV t (applyFn fn v)
applyFn-layered fn v lv = evalWith-layered fn (v ∷ᵃ []ᵃ) (lv ∷ˡ []ˡ)

-- every value admits the trivial one-layer derivation (its measure
-- is the coarse singleton {syncSize}; the contract carries finer
-- derivations where it matters, but existence is unconditional —
-- the theorem's hypotheses stay empty)
layeredV-any : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → LayeredV t v
layeredV-any unitᵗ    v        = tt
layeredV-any boolᵗ    v        = tt
layeredV-any natᵗ     v        = tt
layeredV-any (s ×ᵗ t) v        =
  layeredV-any s (proj₁ v) , layeredV-any t (proj₂ v)
layeredV-any (s +ᵗ t) (inj₁ a) = layeredV-any s a
layeredV-any (s +ᵗ t) (inj₂ b) = layeredV-any t b
layeredV-any (obs t)  e        = layer e []ᵃ []ˡ


------------------------------------------------------------------
-- THE MEASURE — edge 3's Dershowitz–Manna multiset, concretely.
-- A layer derivation reads off the multiset of its templates'
-- sync-sizes (layerSizes); the order is count-vector lex with the
-- HIGH size class first (counts B).  All templates come from
-- program+slot syntax, so B is fixed per program and the vector
-- length is fixed — lex over Vec ℕ is then well-founded (≺ᵛ-wf,
-- proven below), and that Acc is the induction principle the wet
-- contract recurses on.  measureObs is the end-to-end reading.
------------------------------------------------------------------

mutual
  layerSizes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
    LayeredObs e → List ℕ
  layerSizes (layer tpl env le) = syncSizeᵉ tpl ∷ layerSizesEnv le

  layerSizesV : ∀ {n} {Γ : Ctx n} (t : Ty) {v : Val Γ t} →
    LayeredV t v → List ℕ
  layerSizesV unitᵗ    _  = []
  layerSizesV boolᵗ    _  = []
  layerSizesV natᵗ     _  = []
  layerSizesV (s ×ᵗ t) (la , lb) = layerSizesV s la ++ layerSizesV t lb
  layerSizesV (s +ᵗ t) {inj₁ a} l = layerSizesV s l
  layerSizesV (s +ᵗ t) {inj₂ b} l = layerSizesV t l
  layerSizesV (obs t)  l  = layerSizes l

  layerSizesEnv : ∀ {n} {Γ : Ctx n} {Θ} {env : All (Val Γ) Θ} →
    LayeredEnv env → List ℕ
  layerSizesEnv []ˡ       = []
  layerSizesEnv (_∷ˡ_ {t = t} l ls) = layerSizesV t l ++ layerSizesEnv ls

-- count-vector lex, high class first
data _≺ᵛ_ : ∀ {m} → Vec ℕ m → Vec ℕ m → Set where
  ≺-here  : ∀ {m x y} {xs ys : Vec ℕ m} → x < y → (x ∷ᵛ xs) ≺ᵛ (y ∷ᵛ ys)
  ≺-there : ∀ {m x} {xs ys : Vec ℕ m} → xs ≺ᵛ ys → (x ∷ᵛ xs) ≺ᵛ (x ∷ᵛ ys)

-- well-foundedness: nested induction — vector length outside, then
-- (Acc of the head, Acc of the tail) lexicographically.  accHead is
-- handed the tail relation's full well-foundedness (wfm) so a head
-- decrease can restart the tail at ANY vector.
accHead : ∀ {m} (wfm : WellFounded (_≺ᵛ_ {m})) (x : ℕ) → Acc _<_ x →
  (xs : Vec ℕ m) → Acc (_≺ᵛ_ {m}) xs → Acc _≺ᵛ_ (x ∷ᵛ xs)
accHead wfm x (acc rx) = go
  where
  go : ∀ xs → Acc _≺ᵛ_ xs → Acc _≺ᵛ_ (x ∷ᵛ xs)
  go xs (acc rxs) = acc λ where
    (≺-here  y<x) → accHead wfm _ (rx y<x) _ (wfm _)
    (≺-there ys≺) → go _ (rxs ys≺)

≺ᵛ-wf : ∀ {m} → WellFounded (_≺ᵛ_ {m})
≺ᵛ-wf {zero}  []ᵛ       = acc λ ()
≺ᵛ-wf {suc m} (x ∷ᵛ xs) = accHead ≺ᵛ-wf x (<-wellFounded x) xs (≺ᵛ-wf xs)

-- counts: the multiset → count-vector reading.  Index 0 is size
-- class B (high first); oversized elements clamp into class B — the
-- contract only ever reads it with all elements ≤ B.
zerosᵛ : ∀ {m} → Vec ℕ m
zerosᵛ {zero}  = []ᵛ
zerosᵛ {suc m} = 0 ∷ᵛ zerosᵛ

oneAt : (B x : ℕ) → Vec ℕ (suc B)     -- a single element of size x
oneAt zero    x = 1 ∷ᵛ []ᵛ
oneAt (suc B) x = if suc B ≤ᵇ x then 1 ∷ᵛ zerosᵛ else 0 ∷ᵛ oneAt B x

_⊕ᵛ_ : ∀ {m} → Vec ℕ m → Vec ℕ m → Vec ℕ m
[]ᵛ       ⊕ᵛ []ᵛ       = []ᵛ
(x ∷ᵛ xs) ⊕ᵛ (y ∷ᵛ ys) = x + y ∷ᵛ (xs ⊕ᵛ ys)

counts : (B : ℕ) → List ℕ → Vec ℕ (suc B)
counts B []      = zerosᵛ
counts B (x ∷ M) = oneAt B x ⊕ᵛ counts B M

-- the wet contract's measure of a subscribed value, end to end
measureObs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B : ℕ) →
  LayeredObs e → Vec ℕ (suc B)
measureObs B l = counts B (layerSizes l)

------------------------------------------------------------------
-- EDGE 2, DISCHARGED: μ-unfolding preserves sync-reachable size.
-- elimG never substitutes outside a deferᵉ (the μ-var is guarded in
-- Δᵍ; only deferᵉ moves it into Δ where elimD can hit it), and
-- syncSize treats deferᵉ as a leaf — so every clause is homomorphic
-- and the deferᵉ clause is refl on both sides, subst cast and all.
-- Hence the μ-unfold decrement edge strictly shrinks syncSize:
-- the machine swaps μᵉ body (suc …) for unfoldμ body (…).
------------------------------------------------------------------

mutual
  syncSize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    syncSizeᵉ (elimGExp x cl e) ≡ syncSizeᵉ e
  syncSize-elimG x cl (input i)       = refl
  syncSize-elimG x cl (ofᵉ ts)        = cong suc (syncSize-elimGᵗˢ x cl ts)
  syncSize-elimG x cl emptyᵉ          = refl
  syncSize-elimG x cl (mapᵉ f e)      =
    cong suc (cong₂ _+_ (syncSize-elimGᵗ x cl f) (syncSize-elimG x cl e))
  syncSize-elimG x cl (takeᵉ c e)     =
    cong suc (cong₂ _+_ (syncSize-elimGᵗ x cl c) (syncSize-elimG x cl e))
  syncSize-elimG x cl (scanᵉ f z e)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGᵗ x cl f)
                                   (syncSize-elimGᵗ x cl z))
                        (syncSize-elimG x cl e))
  syncSize-elimG x cl (mergeAllᵉ e)   = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (concatAllᵉ e)  = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (switchAllᵉ e)  = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (exhaustAllᵉ e) = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (μᵉ e)          = cong suc (syncSize-elimG (there x) cl e)
  syncSize-elimG x cl (varᵉ y)        = refl
  syncSize-elimG x cl (deferᵉ e)      = refl

  syncSize-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    syncSizeᵗ (elimGTm x cl f) ≡ syncSizeᵗ f
  syncSize-elimGᵗ x cl (varᵗ y)      = refl
  syncSize-elimGᵗ x cl unit̂          = refl
  syncSize-elimGᵗ x cl (bool̂ b)      = refl
  syncSize-elimGᵗ x cl (nat̂ k)       = refl
  syncSize-elimGᵗ x cl (pairᵗ a b)   =
    cong suc (cong₂ _+_ (syncSize-elimGᵗ x cl a) (syncSize-elimGᵗ x cl b))
  syncSize-elimGᵗ x cl (fstᵗ p)      = cong suc (syncSize-elimGᵗ x cl p)
  syncSize-elimGᵗ x cl (sndᵗ p)      = cong suc (syncSize-elimGᵗ x cl p)
  syncSize-elimGᵗ x cl (inlᵗ a)      = cong suc (syncSize-elimGᵗ x cl a)
  syncSize-elimGᵗ x cl (inrᵗ a)      = cong suc (syncSize-elimGᵗ x cl a)
  syncSize-elimGᵗ x cl (caseᵗ s l r) =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGᵗ x cl s)
                                   (syncSize-elimGᵗ x cl l))
                        (syncSize-elimGᵗ x cl r))
  syncSize-elimGᵗ x cl (ifᵗ c a b)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGᵗ x cl c)
                                   (syncSize-elimGᵗ x cl a))
                        (syncSize-elimGᵗ x cl b))
  syncSize-elimGᵗ x cl (primᵗ op a)  = cong suc (syncSize-elimGᵗ x cl a)
  syncSize-elimGᵗ x cl (strmᵗ e)     = cong suc (syncSize-elimG x cl e)

  syncSize-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    syncSizeᵗˢ (elimGTms x cl ts) ≡ syncSizeᵗˢ ts
  syncSize-elimGᵗˢ x cl []       = refl
  syncSize-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _+_ (syncSize-elimGᵗ x cl y) (syncSize-elimGᵗˢ x cl ys)

syncSize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body
syncSize-unfoldμ body = syncSize-elimG (here refl) (μᵉ body) body

unfoldμ-shrinks : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  syncSizeᵉ (unfoldμ body) < syncSizeᵉ (μᵉ body)
unfoldμ-shrinks body rewrite syncSize-unfoldμ body = ≤-refl

------------------------------------------------------------------
-- THE STORE INVARIANT — every runtime value the machine holds
-- carries a layer derivation.  The value-carrying stores are
-- exactly: scan accumulators and concat queues (NodeState), a
-- LiveSource's scheduled payloads, an Arrival's payload, and the
-- slot scripts/defs.  Frames need NOTHING: their Fns are terms, and
-- evalWith-layered is unconditional in the term — only the env must
-- be layered.  The wet contract threads StLayered/SchedLayered
-- alongside stBounded?: preservation is part of the cores' own
-- induction (every stored value is an evalWith output over layered
-- inputs); only the base cases live here.
------------------------------------------------------------------

SlotLayered : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → Set
SlotLayered {t = t} (scripted (hot async))       =
  All (λ tv → LayeredV t (Timed.val tv)) async
SlotLayered {t = t} (scripted (cold sync async)) =
  All (LayeredV t) sync × All (λ tv → LayeredV t (Timed.val tv)) async
SlotLayered           (shared def)               = LayeredObs def

SlotsLayered : ∀ {n} {Γ : Ctx n} → Slots Γ → Set
SlotsLayered sl = ∀ i → SlotLayered (sl i)

LiveLayered : ∀ {n} {Γ : Ctx n} → LiveSource Γ → Set
LiveLayered l = All (λ p → LayeredV (LiveSource.elemTy l) (proj₂ p))
                    (LiveSource.pending l)

SchedLayered : ∀ {n} {Γ : Ctx n} → Sched Γ → Set
SchedLayered sched = All LiveLayered (Sched.live sched)
                   × SlotsLayered (Sched.slots sched)

ArrLayered : ∀ {n} {Γ : Ctx n} → Arrival Γ → Set
ArrLayered a = LayeredV (arrTy a) (arrVal a)

NodeLayered : ∀ {n} {Γ : Ctx n} → NodeState Γ → Set
NodeLayered (scan-st {t} v)     = LayeredV t v
NodeLayered (take-st _)         = ⊤
NodeLayered (merge-st _ _)      = ⊤
NodeLayered (concat-st q _ _)   = All LayeredObs q
NodeLayered (switch-st _ _)     = ⊤
NodeLayered (exhaust-st _ _)    = ⊤

StLayered : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → Set
StLayered st = All (λ kv → NodeLayered (proj₂ kv)) (EvalSt.nodes st)

-- base cases: the initial machine is layered
st-init-layered : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) →
  StLayered (st-init e)
st-init-layered e = []ᵃ

slotLayered-any : ∀ {n} {Γ : Ctx n} {t} (s : Slot Γ t) → SlotLayered s
slotLayered-any {t = t} (scripted (hot async))       = anyAll async
  where
  anyAll : ∀ xs → All (λ tv → LayeredV t (Timed.val tv)) xs
  anyAll []        = []ᵃ
  anyAll (tv ∷ xs) = layeredV-any t (Timed.val tv) ∷ᵃ anyAll xs
slotLayered-any {t = t} (scripted (cold sync async)) = anyS sync , anyA async
  where
  anyS : ∀ xs → All (LayeredV t) xs
  anyS []       = []ᵃ
  anyS (v ∷ xs) = layeredV-any t v ∷ᵃ anyS xs
  anyA : ∀ xs → All (λ tv → LayeredV t (Timed.val tv)) xs
  anyA []        = []ᵃ
  anyA (tv ∷ xs) = layeredV-any t (Timed.val tv) ∷ᵃ anyA xs
slotLayered-any           (shared def)               = layer def []ᵃ []ˡ

slotsLayered-any : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → SlotsLayered sl
slotsLayered-any sl i = slotLayered-any (sl i)

------------------------------------------------------------------
-- popping an arrival keeps everything layered — the Set-valued
-- mirror of the proven pop-bounded ring, and the cascade-side init
-- leg: cascadeGo receives a layered payload from a layered schedule
------------------------------------------------------------------

schedHeadOf-layered : ∀ {n} {Γ : Ctx n} (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  LiveLayered l → ArrLayered a × LiveLayered l′
schedHeadOf-layered l eq ll with LiveSource.pending l | eq | ll
... | (t , v) ∷ ps | refl | (lv ∷ᵃ lps) = lv , lps

schedGo-layered : ∀ {n} {Γ : Ctx n} (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  All LiveLayered ls → ArrLayered a × All LiveLayered ls′
schedGo-layered (l ∷ ls) eq (ll ∷ᵃ lls)
  with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-layered (l ∷ ls) refl (ll ∷ᵃ lls) | inj₁ _ | inj₂ (a′ , ls″) =
  let (la , lls′) = schedGo-layered ls eqR lls
  in la , ll ∷ᵃ lls′
schedGo-layered (l ∷ ls) refl (ll ∷ᵃ lls) | inj₂ (a″ , l′) | inj₁ _ =
  let (la , ll′) = schedHeadOf-layered l eqH ll
  in la , ll′ ∷ᵃ lls
schedGo-layered (l ∷ ls) eq (ll ∷ᵃ lls) | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl =
  let (la , ll′) = schedHeadOf-layered l eqH ll
  in la , ll′ ∷ᵃ lls
... | false | refl =
  let (la , lls′) = schedGo-layered ls eqR lls
  in la , ll ∷ᵃ lls′

pop-layered : ∀ {n} {Γ : Ctx n}
  (sched : Sched Γ) {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  SchedLayered sched → ArrLayered a × SchedLayered sched′
pop-layered sched eq (lls , lsl)
  with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
  let (la , lls′) = schedGo-layered (Sched.live sched) eqL lls
  in la , (lls′ , lsl)

-- the latch and finish mirrors: ledger fields only, value stores
-- and slots untouched — layeredness rides along
latch-layered : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  StLayered st → StLayered (cascadeLatch a st)
latch-layered a st sl with Arrival.isLast a
... | true  = sl
... | false = sl

sweepLive-layered : ∀ {n} {Γ : Ctx n} {t}
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  All LiveLayered ls → All LiveLayered (sweepLive reg ls)
sweepLive-layered reg []       []ᵃ        = []ᵃ
sweepLive-layered {n = n} reg (l ∷ ls) (ll ∷ᵃ lls)
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ll ∷ᵃ sweepLive-layered reg ls lls
... | false = sweepLive-layered reg ls lls

finish-layered : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  SchedLayered sched → StLayered st →
  SchedLayered (proj₁ (cascadeFinish a sched st))
    × StLayered (proj₂ (cascadeFinish a sched st))
finish-layered a sched st (lls , lsl) sl with Arrival.isLast a
... | false = (lls , lsl) , sl
... | true  =
  (sweepLive-layered (dropSource (arrSource a) (EvalSt.registry st))
                     (Sched.live sched) lls , lsl) , sl

resolve-layered : ∀ {n} {Γ : Ctx n} {t : Ty} (anchor : Tick)
  (xs : List (Timed (Val Γ t))) →
  All (λ tv → LayeredV t (Timed.val tv)) xs →
  All (λ p → LayeredV t (proj₂ p)) (resolve anchor xs)
resolve-layered anchor []                 []ᵃ        = []ᵃ
resolve-layered anchor ((after w , v) ∷ r) (lv ∷ᵃ lr) =
  lv ∷ᵃ resolve-layered (anchor + suc w) r lr

sched-init-layered : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
  (ins : Slots Γ) → SlotsLayered ins → SchedLayered (sched-init e ins)
sched-init-layered {n = n} {Γ = Γ} e ins sli =
  concat⁺ (tabulate⁺ perSlot) , sli
  where
  perSlot : ∀ i → All LiveLayered (mkHot ins i)
  perSlot i with ins i | sli i
  ... | scripted (hot async) | la      = resolve-layered 0 async la ∷ᵃ []ᵃ
  ... | scripted (cold _ _)  | _       = []ᵃ
  ... | shared _             | _       = []ᵃ

-- the first preservation piece: a scan step keeps the store layered.
-- Every emitted running output and the landed accumulator are applyFn
-- images over layered inputs — evalWith-layered does all the work
scanVals-layered : ∀ {n} {Γ : Ctx n} {s u}
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (a₀ : Val Γ u) (vs : List (Val Γ s)) →
  LayeredV u a₀ → All (LayeredV s) vs →
  All (LayeredV u) (proj₁ (scanVals fn a₀ vs))
    × LayeredV u (proj₂ (scanVals fn a₀ vs))
scanVals-layered fn a₀ []       la []ᵃ         = []ᵃ , la
scanVals-layered fn a₀ (v ∷ vs) la (lv ∷ᵃ lvs) =
  let la′ = applyFn-layered fn (a₀ , v) (la , lv)
      (louts , llast) = scanVals-layered fn (applyFn fn (a₀ , v)) vs la′ lvs
  in la′ ∷ᵃ louts , llast

------------------------------------------------------------------
-- the INIT leg: the initial machine satisfies the size invariant.
-- Provable exactly because the budget seeds from script CONTENT
-- (slotSize counts scripted values): every hot pending value is ≤
-- its slot's inputSize ≤ slotsSize ≤ the tower.
------------------------------------------------------------------

k≤towerℕ : ∀ k → k ≤ towerℕ k
k≤towerℕ zero    = z≤n
k≤towerℕ (suc k) =
  ≤-trans (n<2^n k) (^-monoʳ-≤ 2 (k≤towerℕ k))

all-++-intro : ∀ {A : Set} (p : A → Bool) (xs ys : List A) →
  all p xs ≡ true → all p ys ≡ true → all p (xs ++ ys) ≡ true
all-++-intro p []       ys hx hy = hy
all-++-intro p (x ∷ xs) ys hx hy
  with ∧-true (p x) (all p xs) hx
... | px , pxs = ∧-intro px (all-++-intro p xs ys pxs hy)

all-concat-tab : ∀ {A : Set} (p : A → Bool) {m} (f : Fin m → List A) →
  (∀ i → all p (f i) ≡ true) → all p (concat (tabulate f)) ≡ true
all-concat-tab p {zero}  f h = refl
all-concat-tab p {suc m} f h =
  all-++-intro p (f Fin.zero) (concat (tabulate (λ i → f (Fin.suc i))))
               (h Fin.zero)
               (all-concat-tab p (λ i → f (Fin.suc i)) (λ i → h (Fin.suc i)))

fᵢ≤sum-tab : ∀ {m} (f : Fin m → ℕ) (i : Fin m) → f i ≤ sum (tabulate f)
fᵢ≤sum-tab {suc m} f Fin.zero    = m≤m+n (f Fin.zero) _
fᵢ≤sum-tab {suc m} f (Fin.suc i) =
  ≤-trans (fᵢ≤sum-tab (λ j → f (Fin.suc j)) i) (m≤n+m _ (f Fin.zero))

-- pending values of a resolved script stay under any bound that
-- covers the script's total content
resolve-bounded : ∀ {n} {Γ : Ctx n} {t : Ty} (B : ℕ) (anchor : Tick)
  (xs : List (Timed (Val Γ t))) →
  sum (map (λ tv → sizeᵛ t (Timed.val tv)) xs) ≤ B →
  all (λ p → sizeᵛ t (proj₂ p) ≤ᵇ B) (resolve anchor xs) ≡ true
resolve-bounded B anchor [] h = refl
resolve-bounded {t = t} B anchor ((after w , v) ∷ r) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (sizeᵛ t v) _) h)))
          (resolve-bounded B (anchor + suc w) r
            (≤-trans (m≤n+m _ (sizeᵛ t v)) h))

mkHot-bounded : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (B : ℕ) (i : Fin n) →
  slotSize (ins i) ≤ B → all (boundedLive B) (mkHot ins i) ≡ true
mkHot-bounded ins B i h with ins i | h
... | scripted (hot async) | h′ =
      ∧-intro (resolve-bounded B 0 async (≤-trans (n≤1+n _) h′)) refl
... | scripted (cold _ _)  | _ = refl
... | shared _             | _ = refl

init-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (id : Id) → stBounded? (sizeBudgetAt e ins id) (sched-init e ins)
                         (st-init e) ≡ true
init-bounded {n = n} e ins id =
  ∧-intro (all-concat-tab (boundedLive B) (mkHot ins) perSlot) refl
  where
  B = sizeBudgetAt e ins id
  slots≤B : slotsSize ins ≤ B
  slots≤B =
    ≤-trans (m≤n+m (slotsSize ins) (sizeᵉ e))
    (≤-trans (n≤1+n _)
    (≤-trans (m≤m*n (suc (sizeᵉ e + slotsSize ins)) (suc id))
             (k≤towerℕ (suc (sizeᵉ e + slotsSize ins) * suc id))))
  perSlot : ∀ i → all (boundedLive B) (mkHot ins i) ≡ true
  perSlot i = mkHot-bounded ins B i
                (≤-trans (fᵢ≤sum-tab (λ j → slotSize (ins j)) i) slots≤B)

------------------------------------------------------------------
-- EDGE 1 — the connect latch, counted.  subscribeSharedSlot's
-- connect fires only behind memberSource … ≡ false and prepends to
-- connectedShares, which no machine function ever shrinks; so the
-- number of still-unconnected shared slots is the edge-1 component
-- of the demand: it strictly drops at every connect (unconn-insert)
-- and never rises (unconn-cons-≤).
------------------------------------------------------------------

unconnAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
unconnAt sl cs i with sl i
... | shared _   = if memberSource (toℕ i) cs then 0 else 1
... | scripted _ = 0

unconn : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
unconn sl cs = sum (tabulate (unconnAt sl cs))

-- pointwise sums over Fin n
sum-tab-mono : ∀ {m} (f g : Fin m → ℕ) → (∀ i → f i ≤ g i) →
  sum (tabulate f) ≤ sum (tabulate g)
sum-tab-mono {zero}  f g h = z≤n
sum-tab-mono {suc m} f g h =
  +-mono-≤ (h Fin.zero) (sum-tab-mono _ _ (λ i → h (Fin.suc i)))

sum-tab-strict : ∀ {m} (f g : Fin m → ℕ) → (∀ j → f j ≤ g j) →
  (i : Fin m) → f i < g i → sum (tabulate f) < sum (tabulate g)
sum-tab-strict {suc m} f g h Fin.zero    fi<gi =
  +-mono-<-≤ fi<gi (sum-tab-mono _ _ (λ j → h (Fin.suc j)))
sum-tab-strict {suc m} f g h (Fin.suc i) fi<gi =
  +-mono-≤-< (h Fin.zero) (sum-tab-strict _ _ (λ j → h (Fin.suc j)) i fi<gi)

-- adding a member never raises any slot's contribution
unconnAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → unconnAt sl (s ∷ cs) i ≤ unconnAt sl cs i
unconnAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

unconn-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
unconn-cons-≤ sl cs s =
  sum-tab-mono _ _ (unconnAt-cons-≤ sl cs s)

-- connecting a fresh share strictly drops the count: its own slot
-- goes 1 → 0 and no other slot rises
unconn-insert : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  memberSource (toℕ i) cs ≡ false →
  unconn sl (toℕ i ∷ cs) < unconn sl cs
unconn-insert sl cs i eqi fresh =
  sum-tab-strict _ _ (unconnAt-cons-≤ sl cs (toℕ i)) i strict
  where
  strict : unconnAt sl (toℕ i ∷ cs) i < unconnAt sl cs i
  strict rewrite eqi | fresh
               | T⇒≡true (toℕ i ≡ᵇ toℕ i) (≡⇒≡ᵇ (toℕ i) (toℕ i) refl)
               = s≤s z≤n


------------------------------------------------------------------
-- RANK — the ≺ᵛ order collapsed to ℕ.  Sync fuel is DEPTH-consumed
-- (siblings share the remaining gas; only nested decrement edges
-- stack), so the contract needs to bound the deepest decrement
-- chain, and with the entry sum bounded by V a count vector IS a
-- base-(suc V) numeral (high class = high digit): any ≺ᵛ step
-- strictly decreases its numeric value (rank-mono-≺).  The wet
-- contract therefore inducts on this plain ℕ — no Acc plumbing —
-- converting hop decreases (≺-embed/≺-replace) via rank-mono-≺,
-- and discharging the entry-sum side condition via totᵛ-counts
-- (the sum is the layer count, bounded by the store invariant).
------------------------------------------------------------------

totᵛ : ∀ {m} → Vec ℕ m → ℕ
totᵛ []ᵛ       = 0
totᵛ (x ∷ᵛ xs) = x + totᵛ xs

rank : ∀ {m} (V : ℕ) → Vec ℕ m → ℕ
rank           V []ᵛ       = 0
rank {suc m}   V (x ∷ᵛ xs) = x * (suc V) ^ m + rank V xs

-- a bounded-sum vector reads below the next power (the carry bound)
rank-lt-pow : ∀ {m} (V : ℕ) (c : Vec ℕ m) →
  totᵛ c ≤ V → rank V c < (suc V) ^ m
rank-lt-pow {zero}  V []ᵛ       h = s≤s z≤n
rank-lt-pow {suc m} V (x ∷ᵛ xs) h =
  <-≤-trans (subst (x * (suc V) ^ m + rank V xs <_)
                   (+-comm (x * (suc V) ^ m) ((suc V) ^ m))
                   (+-monoʳ-< (x * (suc V) ^ m)
                      (rank-lt-pow V xs (≤-trans (m≤n+m (totᵛ xs) x) h))))
            (*-monoˡ-≤ ((suc V) ^ m)
               (s≤s (≤-trans (m≤m+n x (totᵛ xs)) h)))

-- THE BRIDGE: a ≺ᵛ step on a bounded-sum vector is a numeral decrease
rank-mono-≺ : ∀ {m} (V : ℕ) {c′ c : Vec ℕ m} →
  c′ ≺ᵛ c → totᵛ c′ ≤ V → rank V c′ < rank V c
rank-mono-≺ V (≺-here {m} {x} {y} {xs} {ys} x<y) tot≤V =
  <-≤-trans (subst (x * (suc V) ^ m + rank V xs <_)
                   (+-comm (x * (suc V) ^ m) ((suc V) ^ m))
                   (+-monoʳ-< (x * (suc V) ^ m)
                      (rank-lt-pow V xs (≤-trans (m≤n+m (totᵛ xs) x) tot≤V))))
            (≤-trans (*-monoˡ-≤ ((suc V) ^ m) x<y)
                     (m≤m+n (y * (suc V) ^ m) (rank V ys)))
rank-mono-≺ V (≺-there {m} {x} {xs} {ys} xs≺ys) tot≤V =
  +-monoʳ-< (x * (suc V) ^ m)
            (rank-mono-≺ V xs≺ys (≤-trans (m≤n+m (totᵛ xs) x) tot≤V))

-- the entry-sum of a count vector is the multiset's cardinality
totᵛ-⊕ᵛ : ∀ {m} (a b : Vec ℕ m) → totᵛ (a ⊕ᵛ b) ≡ totᵛ a + totᵛ b
totᵛ-⊕ᵛ []ᵛ       []ᵛ       = refl
totᵛ-⊕ᵛ (x ∷ᵛ xs) (y ∷ᵛ ys)
  rewrite totᵛ-⊕ᵛ xs ys
        | +-assoc x y (totᵛ xs + totᵛ ys)
        | sym (+-assoc y (totᵛ xs) (totᵛ ys))
        | +-comm y (totᵛ xs)
        | +-assoc (totᵛ xs) y (totᵛ ys)
        | sym (+-assoc x (totᵛ xs) (y + totᵛ ys)) = refl

totᵛ-zeros : ∀ {m} → totᵛ (zerosᵛ {m}) ≡ 0
totᵛ-zeros {zero}  = refl
totᵛ-zeros {suc m} = totᵛ-zeros {m}

totᵛ-oneAt : ∀ B x → totᵛ (oneAt B x) ≡ 1
totᵛ-oneAt zero    x = refl
totᵛ-oneAt (suc B) x with suc B ≤ᵇ x
... | true  = cong suc (totᵛ-zeros {suc B})
... | false = totᵛ-oneAt B x

totᵛ-counts : ∀ B (M : List ℕ) → totᵛ (counts B M) ≡ length M
totᵛ-counts B []      = totᵛ-zeros {suc B}
totᵛ-counts B (x ∷ M)
  rewrite totᵛ-⊕ᵛ (oneAt B x) (counts B M)
        | totᵛ-oneAt B x
        | totᵛ-counts B M = refl

------------------------------------------------------------------
-- THE DEMAND FUNCTION.  Fuel is depth-consumed, so the wet contract
-- carries `fuel hasAtLeast suc (dBound V R U r s)` where V bounds
-- store sizes, R bounds store ranks ((suc V)^(suc B), rank-lt-pow),
-- U = unconn, r = the current value's rank, s = the current
-- expression's syncSize.  The three decrement edges each consume
-- one gs against a strictly smaller demand — the suc V coefficient
-- absorbs the post-hop reset s′ ≤ V exactly, and suc R absorbs the
-- post-connect reset r′ ≤ R exactly; all three interface lemmas are
-- proven below, so the contract's clause proofs only ever apply
-- them, never redo arithmetic.
------------------------------------------------------------------

dBound : (V R U r s : ℕ) → ℕ
dBound V R U r s = s + suc V * (r + suc R * U)

-- edge 2 (μ-unfold): syncSize drops at fixed (U, r)
dBound-μ : ∀ {V R U r s′ s} → s′ < s →
  dBound V R U r s′ < dBound V R U r s
dBound-μ {V} {R} {U} {r} s′<s = +-monoˡ-≤ (suc V * (r + suc R * U)) s′<s

-- edge 3 (inner hop): rank drops, syncSize resets within the store
dBound-hop : ∀ {V R U r′ r s′ s} → r′ < r → s′ ≤ V →
  suc (dBound V R U r′ s′) ≤ dBound V R U r s
dBound-hop {V} {R} {U} {r′} {r} {s′} {s} r′<r s′≤V =
  ≤-trans (+-monoˡ-≤ (suc V * (r′ + suc R * U)) (s≤s s′≤V))
  (≤-trans (≤-reflexive (sym (*-suc (suc V) (r′ + suc R * U))))
  (≤-trans (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) r′<r))
           (m≤n+m (suc V * (r + suc R * U)) s)))

-- edge 1 (connect): unconn drops, rank and syncSize reset within
-- the store bounds
dBound-connect : ∀ {V R U′ U r′ r s′ s} → U′ < U → r′ ≤ R → s′ ≤ V →
  suc (dBound V R U′ r′ s′) ≤ dBound V R U r s
dBound-connect {V} {R} {U′} {U} {r′} {r} {s′} {s} U′<U r′≤R s′≤V =
  ≤-trans (+-monoˡ-≤ (suc V * (r′ + suc R * U′)) (s≤s s′≤V))
  (≤-trans (≤-reflexive (sym (*-suc (suc V) (r′ + suc R * U′))))
  (≤-trans (*-monoʳ-≤ (suc V)
             (≤-trans (+-monoˡ-≤ (suc R * U′) (s≤s r′≤R))
             (≤-trans (≤-reflexive (sym (*-suc (suc R) U′)))
                      (*-monoʳ-≤ (suc R) U′<U))))
  (≤-trans (*-monoʳ-≤ (suc V) (m≤n+m (suc R * U) r))
           (m≤n+m (suc V * (r + suc R * U)) s))))

-- the two decrease lemmas the hop analysis needs (proof-design memo
-- below), PROVEN: ≺-embed (embedded-value hop — a value reified
-- into the carrier measures strictly below it, regardless of
-- relative template sizes) and ≺-replace (scan-produced hop —
-- replacing the carrier top with elements strictly below it
-- decreases; t must be a real size class).

⊕ᵛ-identityˡ : ∀ {m} (v : Vec ℕ m) → zerosᵛ ⊕ᵛ v ≡ v
⊕ᵛ-identityˡ []ᵛ       = refl
⊕ᵛ-identityˡ (x ∷ᵛ v) = cong (x ∷ᵛ_) (⊕ᵛ-identityˡ v)

⊕ᵛ-assoc : ∀ {m} (a b c : Vec ℕ m) → (a ⊕ᵛ b) ⊕ᵛ c ≡ a ⊕ᵛ (b ⊕ᵛ c)
⊕ᵛ-assoc []ᵛ       []ᵛ       []ᵛ       = refl
⊕ᵛ-assoc (x ∷ᵛ a) (y ∷ᵛ b) (z ∷ᵛ c) =
  cong₂ _∷ᵛ_ (+-assoc x y z) (⊕ᵛ-assoc a b c)

⊕ᵛ-comm : ∀ {m} (a b : Vec ℕ m) → a ⊕ᵛ b ≡ b ⊕ᵛ a
⊕ᵛ-comm []ᵛ       []ᵛ       = refl
⊕ᵛ-comm (x ∷ᵛ a) (y ∷ᵛ b) = cong₂ _∷ᵛ_ (+-comm x y) (⊕ᵛ-comm a b)

counts-++ : ∀ B (xs ys : List ℕ) →
  counts B (xs ++ ys) ≡ counts B xs ⊕ᵛ counts B ys
counts-++ B []       ys = sym (⊕ᵛ-identityˡ (counts B ys))
counts-++ B (x ∷ xs) ys rewrite counts-++ B xs ys =
  sym (⊕ᵛ-assoc (oneAt B x) (counts B xs) (counts B ys))

-- adding any vector with mass strictly grows the lex reading
≺ᵛ-grow : ∀ {m} (w v : Vec ℕ m) → 1 ≤ totᵛ w → v ≺ᵛ (w ⊕ᵛ v)
≺ᵛ-grow []ᵛ           []ᵛ       ()
≺ᵛ-grow (zero  ∷ᵛ w) (y ∷ᵛ v) h = ≺-there (≺ᵛ-grow w v h)
≺ᵛ-grow (suc x ∷ᵛ w) (y ∷ᵛ v) h = ≺-here (s≤s (m≤n+m y x))

≺-embed : ∀ B t (xs ys M : List ℕ) →
  counts B M ≺ᵛ counts B (t ∷ xs ++ M ++ ys)
≺-embed B t xs ys M =
  subst (counts B M ≺ᵛ_) (sym eq) (≺ᵛ-grow W (counts B M) tot1)
  where
  W = oneAt B t ⊕ᵛ (counts B xs ⊕ᵛ counts B ys)
  eq : counts B (t ∷ xs ++ M ++ ys) ≡ W ⊕ᵛ counts B M
  eq = trans (cong (oneAt B t ⊕ᵛ_)
               (trans (counts-++ B xs (M ++ ys))
                      (cong (counts B xs ⊕ᵛ_) (counts-++ B M ys))))
       (trans (cong (λ z → oneAt B t ⊕ᵛ (counts B xs ⊕ᵛ z))
                    (⊕ᵛ-comm (counts B M) (counts B ys)))
       (trans (cong (oneAt B t ⊕ᵛ_)
                    (sym (⊕ᵛ-assoc (counts B xs) (counts B ys) (counts B M))))
              (sym (⊕ᵛ-assoc (oneAt B t)
                             (counts B xs ⊕ᵛ counts B ys) (counts B M)))))
  tot1 : 1 ≤ totᵛ W
  tot1 = subst (1 ≤_)
           (sym (trans (totᵛ-⊕ᵛ (oneAt B t) (counts B xs ⊕ᵛ counts B ys))
                       (cong (_+ totᵛ (counts B xs ⊕ᵛ counts B ys))
                             (totᵛ-oneAt B t))))
           (s≤s z≤n)

-- lex is compatible with adding a common vector
≺ᵛ-⊕ʳ : ∀ {m} {u v : Vec ℕ m} (w : Vec ℕ m) → u ≺ᵛ v → (u ⊕ᵛ w) ≺ᵛ (v ⊕ᵛ w)
≺ᵛ-⊕ʳ (z ∷ᵛ w) (≺-here  x<y) = ≺-here (+-monoˡ-< z x<y)
≺ᵛ-⊕ʳ (z ∷ᵛ w) (≺-there u≺v) = ≺-there (≺ᵛ-⊕ʳ w u≺v)

-- (suc B ≤ᵇ y) unfolds to (B <ᵇ y), so state the false case there
≤⇒<ᵇ-false : ∀ y B → y ≤ B → (B <ᵇ y) ≡ false
≤⇒<ᵇ-false zero    B       z≤n       = refl
≤⇒<ᵇ-false (suc y) (suc B) (s≤s y≤B) = ≤⇒<ᵇ-false y B y≤B

-- every element strictly below suc B ⇒ the top class stays empty
counts-tail : ∀ B (Y : List ℕ) → All (_< suc B) Y →
  counts (suc B) Y ≡ 0 ∷ᵛ counts B Y
counts-tail B []      []ᵃ        = refl
counts-tail B (y ∷ Y) (py ∷ᵃ pY)
  rewrite ≤⇒<ᵇ-false y B (≤-pred py) | counts-tail B Y pY = refl

-- a multiset entirely below class t sits under a single t element
counts-below : ∀ B t (Y : List ℕ) → All (_< t) Y → t ≤ B →
  counts B Y ≺ᵛ oneAt B t
counts-below zero    zero    []      []ᵃ        h = ≺-here (s≤s z≤n)
counts-below zero    zero    (y ∷ Y) (() ∷ᵃ _)  h
counts-below zero    (suc t) Y       aY         ()
counts-below (suc B) t       Y       aY         t≤
  with m≤n⇒m<n∨m≡n t≤
... | inj₂ refl
  rewrite counts-tail B Y aY
        | T⇒≡true (suc B ≤ᵇ suc B) (≤⇒≤ᵇ (≤-refl {suc B})) = ≺-here (s≤s z≤n)
... | inj₁ t<sB
  rewrite counts-tail B Y
            (mapᴬ (λ py → ≤-trans py (≤-trans (≤-pred t<sB) (n≤1+n B))) aY)
        | ≤⇒<ᵇ-false t B (≤-pred t<sB)
  = ≺-there (counts-below B t Y aY (≤-pred t<sB))

≺-replace : ∀ B t (Y Z : List ℕ) → All (_< t) Y → t ≤ B →
  counts B (Y ++ Z) ≺ᵛ counts B (t ∷ Z)
≺-replace B t Y Z aY t≤B rewrite counts-++ B Y Z =
  ≺ᵛ-⊕ʳ (counts B Z) (counts-below B t Y aY t≤B)

------------------------------------------------------------------
-- the three cores
------------------------------------------------------------------

------------------------------------------------------------------
-- THE PROOF DESIGN for the three cores (2026-07-19, after the tower
-- attack).  The wet contract for the mutual subscription block is one
-- strengthened induction, consumed through `hasAtLeast`:
--
--   fuel hasAtLeast need(args) → no dry × stores land bounded
--
-- and the induction that defines/bounds `need` is LEXICOGRAPHIC over
-- the three decrement edges:
--
--   1. share connect — decreases the UNCONNECTED-SLOT COUNT
--      (connectedShares latches; a def's walk can only shrink it).
--   2. μ-unfold — decreases SYNC-REACHABLE SIZE (syncSizeᵉ, deferᵉ
--      a leaf): unfoldμ substitutes `μᵉ body` only at var positions,
--      and vars are TYPE-GUARANTEED defer-gated (Δᵍ→Δ moves only at
--      deferᵉ), so the substituted copies are invisible to the
--      synchronous walk.  DISCHARGED above: syncSize-unfoldμ /
--      unfoldμ-shrinks, machine-checked.
--   3. subscribeInner — decreases the DERSHOWITZ–MANNA MULTISET of
--      layer template sizes (the Layered section above: every
--      runtime obs value is a template instantiated over embedded
--      layered values, and evalWith-layered proves the evaluator
--      never leaves the family).  A value's measure is the multiset
--      of its layer tree's template sync-sizes — concretely
--      measureObs = counts B ∘ layerSizes above, ordered by ≺ᵛ
--      (count-vector lex, high class first), with ≺ᵛ-wf as the
--      contract's induction principle.  The hops:
--        · embedded-value hop (subscribing a value subΘTm reified
--          into the carrier): strict SUB-multiset, regardless of
--          relative template sizes — ≺-embed.
--        · scan-produced hop: the carrier-top element is replaced
--          by strictly smaller ones (≺-replace) — the fn body is a
--          proper subterm of the carrier's template, and the
--          consumed values' layers either cancel against the
--          carrier's embedded copies (within one instant,
--          deliveries ≤ syntactic occurrences because subΘ COPIES
--          trees — the sync-linearity lemma, to be proven with the
--          contract) or sit strictly below the top.
--        · share-crossing hop (a template's `input` hits a slot):
--          exits the per-value measure — it anchors against the
--          slot's own element of the GLOBAL multiset {program} ⊎
--          {slots}; that re-anchoring is the ownership half of the
--          ledger (cascadeGo-wet), not the per-value order.
--      (The previous edge-3 design — lex (skeleton, value size)
--      with skeletons ordered by subterm — is REFUTED: chain two
--      obs-typed scans directly, second fn λ(b,v). mergeAll(of[snd
--      x]), and the embedded-value hop lands on a first-scan acc
--      whose template is subterm-incomparable with the carrier's
--      and can dwarf it.  The S-probes missed this only because
--      their dup discards v.)
--
-- THE DEMAND, closed-form and PROVEN (dBound above).  Fuel is
-- depth-consumed, so the contract carries
--
--   fuel hasAtLeast suc (dBound V R U r s)
--
-- with V the store size bound, R = (suc V)^(suc B) the store rank
-- cap (rank-lt-pow), U = unconn, r = the current value's rank, s =
-- the current expression's syncSize.  Each decrement edge consumes
-- one gs against a strictly smaller demand: dBound-μ
-- (unfoldμ-shrinks drops s), dBound-hop (rank-mono-≺ over
-- ≺-embed/≺-replace drops r, s resets ≤ V), dBound-connect
-- (unconn-insert drops U, r resets ≤ R) — all three proven, so the
-- clause proofs only apply them.  dBound < (suc V)^(B+3)·suc U:
-- one exponential story above the store bound, while the seeded
-- budget's tower gains (suc sz) stories per instant —
-- budget-hasAtLeast's tower summand dominates with room to spare,
-- and every literal-headed demand (no chained scans) is already
-- covered by the 2^(sz·(id+1)²) summand alone.
--
-- The cores below are the contract instantiated at
-- the root burst (burst-dry/-bounded) and at the chain fold
-- (cascadeGo-wet); the disjointness argument (each registration's
-- path owns its minted nodes, so per-cascade store traffic is
-- structure-bounded) supplies the store-boundedness half.
--
-- TWO NOTES FOR THE CONTRACT SESSION (2026-07-20 night):
-- 1. The entry-sum side condition (totᵛ ≤ V) does NOT ride on
--    stBounded?: a scan fn that discards its input leaves UNUSED
--    env entries in the derivation — layers with no syntactic
--    footprint — so layer count is not bounded by sizeᵉ.  Either
--    track a layer-count invariant alongside stBounded?, or:
-- 2. THE SHELL OPTION (likely better): make the measure a pure
--    function of the closed expression — shellSize = syncSize with
--    strmᵗ subtrees as leaves; M(e) = {shellSize e} ⊎ ⋃ M over
--    sync-reachable strmᵗ subtrees.  Embedded hop = sub-multiset
--    SYNTACTICALLY; eval/scan hops preserve shells up to reified
--    GROUND plugs (elements inflate ≤ B·suc V — a tower absorbs
--    that inside the +3-story headroom).  Kills all derivation
--    bookkeeping in the store invariant: the caps become decidable
--    Bool checks like stBounded?.  The Layered family stays as the
--    proof that eval outputs are template instances (the closure
--    lemma is the content of the eval-hop decrease either way).
------------------------------------------------------------------

postulate
  -- the chain fold at instant id, from a latched state within id's
  -- size budget, stays wet and lands within suc id's
  cascadeGo-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
    let r = cascadeGo a id chains sched st
    in (hasDry (proj₁ r) ≡ false)
       × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                     (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

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
    in stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) 1)
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true


------------------------------------------------------------------
-- one cascade — PROVEN: latch, the postulated fold core, finish
------------------------------------------------------------------

cascade-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
  let r = cascade a id sched st
  in (hasDry (proj₁ r) ≡ false)
     × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascade-dry {e = e} a id sched st bnd
  with cascadeGo-wet a id (chainsOf a st) sched (cascadeLatch a st)
         (latch-bounded (sizeBudgetAt e (Sched.slots sched) id) sched a st bnd)
... | dry , bnd' = dry , final
  where
  sched' = proj₁ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  st'    = proj₂ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  final : stBounded?
            (sizeBudgetAt e (Sched.slots (proj₁ (cascadeFinish a sched' st')))
                      (suc id))
            (proj₁ (cascadeFinish a sched' st'))
            (proj₂ (cascadeFinish a sched' st')) ≡ true
  final = subst
            (λ sl → stBounded? (sizeBudgetAt e sl (suc id))
                      (proj₁ (cascadeFinish a sched' st'))
                      (proj₂ (cascadeFinish a sched' st')) ≡ true)
            (sym (finish-slots a sched' st'))
            (finish-bounded (sizeBudgetAt e (Sched.slots sched') (suc id))
                            a sched' st' bnd')

------------------------------------------------------------------
-- the fuel loop composes cascades — PROVEN
------------------------------------------------------------------

drain-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry zero    id sched st bnd = refl
drain-dry (suc k) id sched st bnd with sched-next sched in eq
... | inj₁ _            = refl
drain-dry {e = e} (suc k) id sched st bnd | inj₂ (a , sched′) =
  let bnd′ : stBounded? (sizeBudgetAt e (Sched.slots sched′) id) sched′ st ≡ true
      bnd′ = subst
               (λ sl → stBounded? (sizeBudgetAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-bounded (sizeBudgetAt e (Sched.slots sched) id) sched st eq bnd)
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
