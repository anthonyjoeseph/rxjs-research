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
                                       ^-monoʳ-≤; *-assoc;
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
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ)
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
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                shellsᵉ; shellsᵛ;
                                subΘExp; subΘTm; subΘTms;
                                renExp; renTm; renTms; Ren∈; ext∈;
                                wkExp; wkTm; reify;
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
-- THE MEASURE — edge 3's Dershowitz–Manna multiset, SYNTACTICALLY
-- (the shell reading, Rx.Exp).  A runtime obs value is a closed
-- expression; its measure is the multiset of its shells — the
-- operator-skeleton sizes of the value and of every sync-reachable
-- embedded observable (shellsᵉ).  Shells count Exp constructors
-- only: Tm material is weightless and subΘ rewrites only Tm
-- material, so INSTANTIATION PRESERVES EVERY SHELL EXACTLY
-- (shellSize-subΘ below) — an evaluated template's multiset is a
-- class-preserved copy of the template's, plus the plugged obs
-- values' own shells.  The order is count-vector lex with the HIGH
-- size class first (counts B); ≺ᵛ-wf is the semantic justification
-- and rank (below) the ℕ collapse the contract actually inducts
-- on.  Both side conditions ride on stBounded? for free: every
-- shell of e is ≤ sizeᵉ e (shells-≤) and there are ≤ sizeᵉ e of
-- them (shells-len), so a sizeᵛ cap bounds classes AND entry sum.
------------------------------------------------------------------

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

-- the wet contract's measure of a subscribed value, end to end —
-- a pure function of the value's syntax
measureE : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) → Closed Γ t → Vec ℕ (suc B)
measureE B e = counts B (shellsᵉ e)

------------------------------------------------------------------
-- the free side conditions: shells are pointwise ≤ the syntax size
-- and no more numerous than it, at every level (expression, term,
-- runtime value) — so stBounded?'s sizeᵛ cap bounds the measure's
-- classes (≤ B) and entry sum (≤ V) with no new invariant.
------------------------------------------------------------------

shellSize≤size : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  shellSizeᵉ e ≤ sizeᵉ e
shellSize≤size (input i)       = ≤-refl
shellSize≤size (ofᵉ ts)        = s≤s z≤n
shellSize≤size emptyᵉ          = ≤-refl
shellSize≤size (mapᵉ f e)      = s≤s (≤-trans (shellSize≤size e) (m≤n+m _ _))
shellSize≤size (takeᵉ c e)     = s≤s (≤-trans (shellSize≤size e) (m≤n+m _ _))
shellSize≤size (scanᵉ f z e)   = s≤s (≤-trans (shellSize≤size e) (m≤n+m _ _))
shellSize≤size (mergeAllᵉ e)   = s≤s (shellSize≤size e)
shellSize≤size (concatAllᵉ e)  = s≤s (shellSize≤size e)
shellSize≤size (switchAllᵉ e)  = s≤s (shellSize≤size e)
shellSize≤size (exhaustAllᵉ e) = s≤s (shellSize≤size e)
shellSize≤size (μᵉ e)          = s≤s (shellSize≤size e)
shellSize≤size (varᵉ x)        = ≤-refl
shellSize≤size (deferᵉ e)      = s≤s z≤n

mutual
  inner-≤ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    All (_≤ sizeᵉ e) (innerᵉ e)
  inner-≤ᵉ (input i)       = []ᵃ
  inner-≤ᵉ (ofᵉ ts)        = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗˢ ts)
  inner-≤ᵉ emptyᵉ          = []ᵃ
  inner-≤ᵉ (mapᵉ f e)      = all-++
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (inner-≤ᵗ f))
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (inner-≤ᵉ e))
  inner-≤ᵉ (takeᵉ c e)     = all-++
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (inner-≤ᵗ c))
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (inner-≤ᵉ e))
  inner-≤ᵉ (scanᵉ f z e)   = all-++
    (mapᴬ (λ p → ≤-trans p
            (≤-trans (m≤m+n _ _) (≤-trans (m≤m+n _ _) (n≤1+n _))))
          (inner-≤ᵗ f))
    (all-++
      (mapᴬ (λ p → ≤-trans p
              (≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f))
                       (≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ e))
                                (n≤1+n _))))
            (inner-≤ᵗ z))
      (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _)))
            (inner-≤ᵉ e)))
  inner-≤ᵉ (mergeAllᵉ e)   = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (concatAllᵉ e)  = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (switchAllᵉ e)  = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (exhaustAllᵉ e) = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (μᵉ e)          = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (varᵉ x)        = []ᵃ
  inner-≤ᵉ (deferᵉ e)      = []ᵃ

  inner-≤ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    All (_≤ sizeᵗ tm) (innerᵗ tm)
  inner-≤ᵗ (varᵗ x)      = []ᵃ
  inner-≤ᵗ unit̂          = []ᵃ
  inner-≤ᵗ (bool̂ _)      = []ᵃ
  inner-≤ᵗ (nat̂ _)       = []ᵃ
  inner-≤ᵗ (pairᵗ a b)   = all-++
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (inner-≤ᵗ a))
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (inner-≤ᵗ b))
  inner-≤ᵗ (fstᵗ p)      = mapᴬ (λ q → ≤-trans q (n≤1+n _)) (inner-≤ᵗ p)
  inner-≤ᵗ (sndᵗ p)      = mapᴬ (λ q → ≤-trans q (n≤1+n _)) (inner-≤ᵗ p)
  inner-≤ᵗ (inlᵗ a)      = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗ a)
  inner-≤ᵗ (inrᵗ a)      = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗ a)
  inner-≤ᵗ (caseᵗ s l r) = all-++
    (mapᴬ (λ p → ≤-trans p
            (≤-trans (m≤m+n _ _) (≤-trans (m≤m+n _ _) (n≤1+n _))))
          (inner-≤ᵗ s))
    (all-++
      (mapᴬ (λ p → ≤-trans p
              (≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ s))
                       (≤-trans (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))
                                (n≤1+n _))))
            (inner-≤ᵗ l))
      (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _)))
            (inner-≤ᵗ r)))
  inner-≤ᵗ (ifᵗ c a b)   = all-++
    (mapᴬ (λ p → ≤-trans p
            (≤-trans (m≤m+n _ _) (≤-trans (m≤m+n _ _) (n≤1+n _))))
          (inner-≤ᵗ c))
    (all-++
      (mapᴬ (λ p → ≤-trans p
              (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                       (≤-trans (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))
                                (n≤1+n _))))
            (inner-≤ᵗ a))
      (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _)))
            (inner-≤ᵗ b)))
  inner-≤ᵗ (primᵗ _ a)   = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗ a)
  inner-≤ᵗ (strmᵗ e)     =
    ≤-trans (shellSize≤size e) (n≤1+n _)
    ∷ᵃ mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)

  inner-≤ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    All (_≤ sizeᵗˢ ts) (innerᵗˢ ts)
  inner-≤ᵗˢ []       = []ᵃ
  inner-≤ᵗˢ (y ∷ ys) = all-++
    (mapᴬ (λ p → ≤-trans p (m≤m+n _ _)) (inner-≤ᵗ y))
    (mapᴬ (λ p → ≤-trans p (m≤n+m _ _)) (inner-≤ᵗˢ ys))

shells-≤ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  All (_≤ sizeᵉ e) (shellsᵉ e)
shells-≤ e = shellSize≤size e ∷ᵃ inner-≤ᵉ e

shellsᵛ-≤ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  All (_≤ sizeᵛ t v) (shellsᵛ t v)
shellsᵛ-≤ unitᵗ    v        = []ᵃ
shellsᵛ-≤ boolᵗ    v        = []ᵃ
shellsᵛ-≤ natᵗ     v        = []ᵃ
shellsᵛ-≤ (s ×ᵗ t) (a , b)  = all-++
  (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (shellsᵛ-≤ s a))
  (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (shellsᵛ-≤ t b))
shellsᵛ-≤ (s +ᵗ t) (inj₁ a) = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (shellsᵛ-≤ s a)
shellsᵛ-≤ (s +ᵗ t) (inj₂ b) = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (shellsᵛ-≤ t b)
shellsᵛ-≤ (obs t)  e        = shells-≤ e

mutual
  inner-lenᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    length (innerᵉ e) < sizeᵉ e
  inner-lenᵉ (input i)       = s≤s z≤n
  inner-lenᵉ (ofᵉ ts)        = s≤s (inner-lenᵗˢ ts)
  inner-lenᵉ emptyᵉ          = s≤s z≤n
  inner-lenᵉ (mapᵉ f e)      rewrite length-++ (innerᵗ f) {innerᵉ e} =
    s≤s (≤-trans (n≤1+n _) (+-mono-≤-< (inner-lenᵗ f) (inner-lenᵉ e)))
  inner-lenᵉ (takeᵉ c e)     rewrite length-++ (innerᵗ c) {innerᵉ e} =
    s≤s (≤-trans (n≤1+n _) (+-mono-≤-< (inner-lenᵗ c) (inner-lenᵉ e)))
  inner-lenᵉ (scanᵉ f z e)
    rewrite length-++ (innerᵗ f) {innerᵗ z ++ innerᵉ e}
          | length-++ (innerᵗ z) {innerᵉ e} =
    s≤s (≤-trans (≤-reflexive (sym (+-assoc (length (innerᵗ f))
                                            (length (innerᵗ z)) _)))
        (≤-trans (n≤1+n _)
                 (+-mono-≤-< (+-mono-≤ (inner-lenᵗ f) (inner-lenᵗ z))
                             (inner-lenᵉ e))))
  inner-lenᵉ (mergeAllᵉ e)   = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (concatAllᵉ e)  = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (switchAllᵉ e)  = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (exhaustAllᵉ e) = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (μᵉ e)          = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (varᵉ x)        = s≤s z≤n
  inner-lenᵉ (deferᵉ e)      = s≤s z≤n

  inner-lenᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    length (innerᵗ tm) ≤ sizeᵗ tm
  inner-lenᵗ (varᵗ x)      = z≤n
  inner-lenᵗ unit̂          = z≤n
  inner-lenᵗ (bool̂ _)      = z≤n
  inner-lenᵗ (nat̂ _)       = z≤n
  inner-lenᵗ (pairᵗ a b)   rewrite length-++ (innerᵗ a) {innerᵗ b} =
    ≤-trans (+-mono-≤ (inner-lenᵗ a) (inner-lenᵗ b)) (n≤1+n _)
  inner-lenᵗ (fstᵗ p)      = ≤-trans (inner-lenᵗ p) (n≤1+n _)
  inner-lenᵗ (sndᵗ p)      = ≤-trans (inner-lenᵗ p) (n≤1+n _)
  inner-lenᵗ (inlᵗ a)      = ≤-trans (inner-lenᵗ a) (n≤1+n _)
  inner-lenᵗ (inrᵗ a)      = ≤-trans (inner-lenᵗ a) (n≤1+n _)
  inner-lenᵗ (caseᵗ s l r)
    rewrite length-++ (innerᵗ s) {innerᵗ l ++ innerᵗ r}
          | length-++ (innerᵗ l) {innerᵗ r} =
    ≤-trans (≤-reflexive (sym (+-assoc (length (innerᵗ s))
                                       (length (innerᵗ l)) _)))
    (≤-trans (+-mono-≤ (+-mono-≤ (inner-lenᵗ s) (inner-lenᵗ l))
                       (inner-lenᵗ r))
             (n≤1+n _))
  inner-lenᵗ (ifᵗ c a b)
    rewrite length-++ (innerᵗ c) {innerᵗ a ++ innerᵗ b}
          | length-++ (innerᵗ a) {innerᵗ b} =
    ≤-trans (≤-reflexive (sym (+-assoc (length (innerᵗ c))
                                       (length (innerᵗ a)) _)))
    (≤-trans (+-mono-≤ (+-mono-≤ (inner-lenᵗ c) (inner-lenᵗ a))
                       (inner-lenᵗ b))
             (n≤1+n _))
  inner-lenᵗ (primᵗ _ a)   = ≤-trans (inner-lenᵗ a) (n≤1+n _)
  inner-lenᵗ (strmᵗ e)     = ≤-trans (inner-lenᵉ e) (n≤1+n _)

  inner-lenᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    length (innerᵗˢ ts) ≤ sizeᵗˢ ts
  inner-lenᵗˢ []       = z≤n
  inner-lenᵗˢ (y ∷ ys) rewrite length-++ (innerᵗ y) {innerᵗˢ ys} =
    +-mono-≤ (inner-lenᵗ y) (inner-lenᵗˢ ys)

shells-len : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  length (shellsᵉ e) ≤ sizeᵉ e
shells-len e = inner-lenᵉ e

------------------------------------------------------------------
-- THE CLOSURE, exactly: substitution preserves every shell size.
-- subΘ rewrites only Tm material — Exp constructors map 1-1 and a
-- plugged value sits behind ground literals and strmᵗ leaves, both
-- weightless — so an instantiated template's own shell is its
-- template's shell, on the nose.  This is what makes the scan hop
-- an EMBED hop: the produced value's multiset is a class-preserved
-- copy of the fn-body subtree's sub-multiset (plus plugged obs
-- values' shells, owned by the ledger).
------------------------------------------------------------------

shellSize-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
  (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  shellSizeᵉ (subΘExp Θloc σ e) ≡ shellSizeᵉ e
shellSize-subΘ Θloc σ (input i)       = refl
shellSize-subΘ Θloc σ (ofᵉ ts)        = refl
shellSize-subΘ Θloc σ emptyᵉ          = refl
shellSize-subΘ Θloc σ (mapᵉ f e)      = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (takeᵉ c e)     = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (scanᵉ f z e)   = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (mergeAllᵉ e)   = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (concatAllᵉ e)  = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (switchAllᵉ e)  = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (exhaustAllᵉ e) = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (μᵉ e)          = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (varᵉ x)        = refl
shellSize-subΘ Θloc σ (deferᵉ e)      = refl

-- renamings never touch shells: shellSizeᵉ reads only Exp
-- constructors and renExp maps them 1-1 (weakening included —
-- wkExp/wkTm are renamings from empty contexts)
shellSize-ren : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
  (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
  (e : Exp Γ Δᵍ Δ Θ t) →
  shellSizeᵉ (renExp ρg ρd ρt e) ≡ shellSizeᵉ e
shellSize-ren ρg ρd ρt (input i)       = refl
shellSize-ren ρg ρd ρt (ofᵉ ts)        = refl
shellSize-ren ρg ρd ρt emptyᵉ          = refl
shellSize-ren ρg ρd ρt (mapᵉ f e)      = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (takeᵉ c e)     = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (scanᵉ f z e)   = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (mergeAllᵉ e)   = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (concatAllᵉ e)  = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (switchAllᵉ e)  = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (exhaustAllᵉ e) = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (μᵉ e)          = cong suc (shellSize-ren (ext∈ ρg) ρd ρt e)
shellSize-ren ρg ρd ρt (varᵉ x)        = refl
shellSize-ren ρg ρd ρt (deferᵉ e)      = refl

mutual
  inner-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) →
    innerᵉ (renExp ρg ρd ρt e) ≡ innerᵉ e
  inner-renᵉ ρg ρd ρt (input i)       = refl
  inner-renᵉ ρg ρd ρt (ofᵉ ts)        = inner-renᵗˢ ρg ρd ρt ts
  inner-renᵉ ρg ρd ρt emptyᵉ          = refl
  inner-renᵉ ρg ρd ρt (mapᵉ f e)      =
    cong₂ _++_ (inner-renᵗ ρg ρd (ext∈ ρt) f) (inner-renᵉ ρg ρd ρt e)
  inner-renᵉ ρg ρd ρt (takeᵉ c e)     =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt c) (inner-renᵉ ρg ρd ρt e)
  inner-renᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _++_ (inner-renᵗ ρg ρd (ext∈ ρt) f)
               (cong₂ _++_ (inner-renᵗ ρg ρd ρt z) (inner-renᵉ ρg ρd ρt e))
  inner-renᵉ ρg ρd ρt (mergeAllᵉ e)   = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (concatAllᵉ e)  = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (switchAllᵉ e)  = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (exhaustAllᵉ e) = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (μᵉ e)          = inner-renᵉ (ext∈ ρg) ρd ρt e
  inner-renᵉ ρg ρd ρt (varᵉ x)        = refl
  inner-renᵉ ρg ρd ρt (deferᵉ e)      = refl

  inner-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) →
    innerᵗ (renTm ρg ρd ρt tm) ≡ innerᵗ tm
  inner-renᵗ ρg ρd ρt (varᵗ x)      = refl
  inner-renᵗ ρg ρd ρt unit̂          = refl
  inner-renᵗ ρg ρd ρt (bool̂ _)      = refl
  inner-renᵗ ρg ρd ρt (nat̂ _)       = refl
  inner-renᵗ ρg ρd ρt (pairᵗ a b)   =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt a) (inner-renᵗ ρg ρd ρt b)
  inner-renᵗ ρg ρd ρt (fstᵗ p)      = inner-renᵗ ρg ρd ρt p
  inner-renᵗ ρg ρd ρt (sndᵗ p)      = inner-renᵗ ρg ρd ρt p
  inner-renᵗ ρg ρd ρt (inlᵗ a)      = inner-renᵗ ρg ρd ρt a
  inner-renᵗ ρg ρd ρt (inrᵗ a)      = inner-renᵗ ρg ρd ρt a
  inner-renᵗ ρg ρd ρt (caseᵗ sc l r) =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt sc)
               (cong₂ _++_ (inner-renᵗ ρg ρd (ext∈ ρt) l)
                           (inner-renᵗ ρg ρd (ext∈ ρt) r))
  inner-renᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt c)
               (cong₂ _++_ (inner-renᵗ ρg ρd ρt a) (inner-renᵗ ρg ρd ρt b))
  inner-renᵗ ρg ρd ρt (primᵗ _ a)   = inner-renᵗ ρg ρd ρt a
  inner-renᵗ ρg ρd ρt (strmᵗ e)     =
    cong₂ _∷_ (shellSize-ren ρg ρd ρt e) (inner-renᵉ ρg ρd ρt e)

  inner-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    innerᵗˢ (renTms ρg ρd ρt ts) ≡ innerᵗˢ ts
  inner-renᵗˢ ρg ρd ρt []       = refl
  inner-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt y) (inner-renᵗˢ ρg ρd ρt ys)

-- a reified value's embedded shells are exactly the value's own:
-- ground skeleton contributes nothing, obs components sit behind
-- strmᵗ verbatim
reify-inner : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  innerᵗ (reify v) ≡ shellsᵛ t v
reify-inner unitᵗ    v        = refl
reify-inner boolᵗ    v        = refl
reify-inner natᵗ     v        = refl
reify-inner (s ×ᵗ t) (a , b)  = cong₂ _++_ (reify-inner s a) (reify-inner t b)
reify-inner (s +ᵗ t) (inj₁ a) = reify-inner s a
reify-inner (s +ᵗ t) (inj₂ b) = reify-inner t b
reify-inner (obs t)  e        = refl

-- the cap closure: instantiating a capped template over a capped
-- environment yields capped shells — the substrate of invariant
-- preservation at every evalWith/applyFn site.  (The host shell is
-- covered separately and exactly by shellSize-subΘ.)
EnvCap : ∀ {n} {Γ : Ctx n} {Θ} (B : ℕ) → All (Val Γ) Θ → Set
EnvCap B []ᵃ              = ⊤
EnvCap B (_∷ᵃ_ {x = t} v σ) = All (_≤ B) (shellsᵛ t v) × EnvCap B σ

envCap-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (B : ℕ) (σ : All (Val Γ) Θ) →
  EnvCap B σ → (z : t ∈ Θ) → All (_≤ B) (shellsᵛ t (lookupEnv σ z))
envCap-lookup B (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envCap-lookup B (v ∷ᵃ σ) (hv , hσ) (there z)   = envCap-lookup B σ hσ z

mutual
  subΘ-capᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    All (_≤ B) (innerᵉ e) → EnvCap B σ →
    All (_≤ B) (innerᵉ (subΘExp Θloc σ e))
  subΘ-capᵉ B Θloc σ (input i)       h hσ = []ᵃ
  subΘ-capᵉ B Θloc σ (ofᵉ ts)        h hσ = subΘ-capᵗˢ B Θloc σ ts h hσ
  subΘ-capᵉ B Θloc σ emptyᵉ          h hσ = []ᵃ
  subΘ-capᵉ B Θloc σ (mapᵉ {s = s} f e) h hσ = all-++
    (subΘ-capᵗ B (s ∷ Θloc) σ f (all-++ˡ (innerᵗ f) h) hσ)
    (subΘ-capᵉ B Θloc σ e (all-++ʳ (innerᵗ f) h) hσ)
  subΘ-capᵉ B Θloc σ (takeᵉ c e)     h hσ = all-++
    (subΘ-capᵗ B Θloc σ c (all-++ˡ (innerᵗ c) h) hσ)
    (subΘ-capᵉ B Θloc σ e (all-++ʳ (innerᵗ c) h) hσ)
  subΘ-capᵉ B Θloc σ (scanᵉ {s = s} {t = t} f z e) h hσ = all-++
    (subΘ-capᵗ B ((t ×ᵗ s) ∷ Θloc) σ f (all-++ˡ (innerᵗ f) h) hσ)
    (all-++
      (subΘ-capᵗ B Θloc σ z
        (all-++ˡ (innerᵗ z) (all-++ʳ (innerᵗ f) h)) hσ)
      (subΘ-capᵉ B Θloc σ e
        (all-++ʳ (innerᵗ z) (all-++ʳ (innerᵗ f) h)) hσ))
  subΘ-capᵉ B Θloc σ (mergeAllᵉ e)   h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (concatAllᵉ e)  h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (switchAllᵉ e)  h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (exhaustAllᵉ e) h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (μᵉ e)          h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (varᵉ x)        h hσ = []ᵃ
  subΘ-capᵉ B Θloc σ (deferᵉ e)      h hσ = []ᵃ

  subΘ-capᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    All (_≤ B) (innerᵗ tm) → EnvCap B σ →
    All (_≤ B) (innerᵗ (subΘTm Θloc σ tm))
  subΘ-capᵗ B Θloc σ (varᵗ x) h hσ with ∈-++⁻ Θloc x
  ... | inj₁ y = []ᵃ
  ... | inj₂ z = subst (All (_≤ B))
      (sym (trans (inner-renᵗ (λ ()) (λ ()) (λ ())
                              (reify (lookupEnv σ z)))
                  (reify-inner _ (lookupEnv σ z))))
      (envCap-lookup B σ hσ z)
  subΘ-capᵗ B Θloc σ unit̂          h hσ = []ᵃ
  subΘ-capᵗ B Θloc σ (bool̂ _)      h hσ = []ᵃ
  subΘ-capᵗ B Θloc σ (nat̂ _)       h hσ = []ᵃ
  subΘ-capᵗ B Θloc σ (pairᵗ a b)   h hσ = all-++
    (subΘ-capᵗ B Θloc σ a (all-++ˡ (innerᵗ a) h) hσ)
    (subΘ-capᵗ B Θloc σ b (all-++ʳ (innerᵗ a) h) hσ)
  subΘ-capᵗ B Θloc σ (fstᵗ p)      h hσ = subΘ-capᵗ B Θloc σ p h hσ
  subΘ-capᵗ B Θloc σ (sndᵗ p)      h hσ = subΘ-capᵗ B Θloc σ p h hσ
  subΘ-capᵗ B Θloc σ (inlᵗ a)      h hσ = subΘ-capᵗ B Θloc σ a h hσ
  subΘ-capᵗ B Θloc σ (inrᵗ a)      h hσ = subΘ-capᵗ B Θloc σ a h hσ
  subΘ-capᵗ B Θloc σ (caseᵗ {s = s} {t = t} sc l r) h hσ = all-++
    (subΘ-capᵗ B Θloc σ sc (all-++ˡ (innerᵗ sc) h) hσ)
    (all-++
      (subΘ-capᵗ B (s ∷ Θloc) σ l
        (all-++ˡ (innerᵗ l) (all-++ʳ (innerᵗ sc) h)) hσ)
      (subΘ-capᵗ B (t ∷ Θloc) σ r
        (all-++ʳ (innerᵗ l) (all-++ʳ (innerᵗ sc) h)) hσ))
  subΘ-capᵗ B Θloc σ (ifᵗ c a b)   h hσ = all-++
    (subΘ-capᵗ B Θloc σ c (all-++ˡ (innerᵗ c) h) hσ)
    (all-++
      (subΘ-capᵗ B Θloc σ a
        (all-++ˡ (innerᵗ a) (all-++ʳ (innerᵗ c) h)) hσ)
      (subΘ-capᵗ B Θloc σ b
        (all-++ʳ (innerᵗ a) (all-++ʳ (innerᵗ c) h)) hσ))
  subΘ-capᵗ B Θloc σ (primᵗ _ a)   h hσ = subΘ-capᵗ B Θloc σ a h hσ
  subΘ-capᵗ B Θloc σ (strmᵗ e) (hd ∷ᵃ tl) hσ =
    subst (_≤ B) (sym (shellSize-subΘ Θloc σ e)) hd
    ∷ᵃ subΘ-capᵉ B Θloc σ e tl hσ

  subΘ-capᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    All (_≤ B) (innerᵗˢ ts) → EnvCap B σ →
    All (_≤ B) (innerᵗˢ (subΘTms Θloc σ ts))
  subΘ-capᵗˢ B Θloc σ []       h hσ = []ᵃ
  subΘ-capᵗˢ B Θloc σ (y ∷ ys) h hσ = all-++
    (subΘ-capᵗ B Θloc σ y (all-++ˡ (innerᵗ y) h) hσ)
    (subΘ-capᵗˢ B Θloc σ ys (all-++ʳ (innerᵗ y) h) hσ)

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
-- (the sum is the shell count, ≤ sizeᵉ by shells-len — free on
-- stBounded?).
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

-- the whole demand under one product — what the seed inequality
-- compares against the budget tower: dBound ≤ (1+V)(1+R)(1+U)
dBound-bound : ∀ {V R U r s} → s ≤ V → r ≤ R →
  dBound V R U r s ≤ suc V * suc R * suc U
dBound-bound {V} {R} {U} {r} {s} s≤V r≤R =
  ≤-trans (+-mono-≤ s≤V
            (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) r≤R)))
  (≤-trans (+-monoˡ-≤ (suc V * (R + suc R * U)) (n≤1+n V))
  (≤-trans (≤-reflexive (sym (*-suc (suc V) (R + suc R * U))))
  (≤-trans (*-monoʳ-≤ (suc V) (≤-reflexive shuffle))
           (≤-reflexive (sym (*-assoc (suc V) (suc R) (suc U)))))))
  where
  -- suc (R + suc R * U) ≡ suc R * suc U, definitionally via *-suc
  shuffle : suc (R + suc R * U) ≡ suc R * suc U
  shuffle = sym (*-suc (suc R) U)

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
--      SHELL sizes (2026-07-20: the SHELL DESIGN, adopted with
--      Anthony's approval, replacing the layer-derivation reading).
--      A runtime obs value IS a closed expression; its measure is
--      measureE = counts B ∘ shellsᵉ — the multiset of operator-
--      skeleton sizes of the value and every sync-reachable
--      embedded observable (Rx.Exp.shellsᵉ), a pure function of
--      syntax.  Shells count Exp constructors ONLY (Tm material
--      weightless, strmᵗ/deferᵉ leaves), which buys the design's
--      two load-bearing facts, both PROVEN above:
--        · substitution invariance (shellSize-subΘ): subΘ rewrites
--          only Tm material, so instantiation preserves every
--          shell size EXACTLY.  No inflation — an instantiated
--          template's multiset is a class-preserved copy of the
--          template's plus the plugged obs values' own shells
--          (reify-inner: a plug's footprint is void, its shells
--          join the inner multiset verbatim).
--        · free side conditions: every shell of e is ≤ sizeᵉ e
--          (shells-≤/shellsᵛ-≤) and shells number ≤ sizeᵉ e
--          (shells-len) — so stBounded?'s sizeᵛ cap bounds both
--          the classes (≤ B) and the entry sum (≤ V, the rank
--          bridge's side condition).  NO new invariant; the whole
--          Layered derivation apparatus is deleted (git: 1fbc59c).
--      The hops:
--        · embedded-value hop (subscribing a value that sits as a
--          strmᵗ subtree of the carrier — of-list literals under
--          closed evaluation, evalWith (strmᵗ e) []ᵃ = e): its
--          shellsᵉ is a CONTIGUOUS sublist of the carrier's inner
--          (innerᵗ (strmᵗ e) = shellsᵉ e), and the carrier's own
--          shell rides on top — strict sub-multiset, ≺-embed.
--        · eval/scan-produced hop (applyFn/evalWith instantiates a
--          template): by shellSize-subΘ the produced multiset =
--          the fn-body strmᵗ subtree's sub-multiset, classes on
--          the nose, ⊎ the plugged obs values' shells.  The first
--          part is the embed shape again; the plugged part is
--          where the LEDGER lives — the plugs are prior stored
--          values whose shells the global multiset already owns
--          (deliveries ≤ syntactic occurrences because subΘ
--          COPIES trees — the sync-linearity lemma, to be proven
--          with the contract).  The exact bookkeeping input is
--          the subΘ multiset equation: counts of the instantiated
--          inner ≡ counts of the template inner ⊕ᵛ counts of the
--          plug shells (per obs-var occurrence) — state it with
--          a plugsᵉ mirror of subΘ when the contract needs it;
--          subΘ-capᵉ above is its All-cap shadow, already proven.
--        · share-crossing hop (a template's `input` hits a slot):
--          exits the per-value measure — it anchors against the
--          slot's own element of the GLOBAL multiset {program} ⊎
--          {slots}; that re-anchoring is the ownership half of the
--          ledger (cascadeGo-wet), not the per-value order.
--      (The 2026-07-19 layer-derivation design worked but carried
--      an unfixable wart: unused env entries gave layers with no
--      syntactic footprint, so the entry-sum side condition needed
--      its own invariant.  The design before THAT — lex (skeleton,
--      value size), subterm-ordered — is REFUTED: chain two
--      obs-typed scans directly, second fn λ(b,v). mergeAll(of[snd
--      x]), and the embedded-value hop lands on a first-scan acc
--      whose template is subterm-incomparable with the carrier's
--      and can dwarf it.)
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
