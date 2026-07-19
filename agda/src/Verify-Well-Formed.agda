-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation, in three layers.
--   1. Inv (CONCRETE below) relates evaluator state to automaton
--      state between cascades.
--   2. Two frame relations — BurstInv (mid-subscribe-frame) and Mid
--      (mid-cascade, indexed by the chains still to fold) — both
--      CONCRETE records now, with entry/step/exit lemmas.  Proven:
--      burst-init, burst-final.  Postulated: the step lemmas
--      (subscribeE-wf, mid-step — the per-clause preservation
--      grind), mid-init, mid-skip, mid-final, and the single
--      budget-sufficient totality conjecture at the bottom.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; 1+n≰n; ≤⇒≤ᵇ)
open import Data.List    using (List; []; _∷_; _++_; any; length; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Relation.Nullary using (Dec; yes; no)

open import Rx.Prim      using (Fuel; Tick; Id; Source; Ordinal; InstEmit;
                                InstEvent; init; value; close; handoff; complete;
                                EmitKind; delivery; CloseReason; exhausted;
                                cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty; _≟ᵗ_; Val)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_; Frame;
                                sched-init; st-init; sched-next; LiveSource;
                                schedGo; schedHeadOf; schedFinish; schedEarlier;
                                arrTy; arrSource; arrVal; arrTick;
                                chainsOf; chainsGo; chainStep;
                                foldPath; dispatchShare; stepFrame;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate;
                                sameSource; drySource; dryEvent; hasDry;
                                dropSource; sweepLive; budgetAt)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; protocol-init;
                                stepProtocol; runProtocol; paidUp; settle; hasOwed;
                                payOwed; paidOff; applyEvents; removeOne;
                                cancelOwed; bumpOwed; settleInstant;
                                checkFinal; Accepted; accepted; WellFormed)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

_>>=ᴹ_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=ᴹ f = f a
nothing >>=ᴹ f = nothing

runProtocol-++ : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A)) →
  runProtocol S (xs ++ ys)
    ≡ (runProtocol S xs >>=ᴹ λ S′ → runProtocol S′ ys)
runProtocol-++ S []       ys = refl
runProtocol-++ S (x ∷ xs) ys with stepProtocol x S
... | just S′ = runProtocol-++ S′ xs ys
... | nothing = refl

run-++-just : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A))
              {S₁ S₂ : ProtocolSt} →
  runProtocol S xs ≡ just S₁ → runProtocol S₁ ys ≡ just S₂ →
  runProtocol S (xs ++ ys) ≡ just S₂
run-++-just S xs ys {S₁} e₁ e₂ =
  trans (runProtocol-++ S xs ys)
        (trans (cong (λ m → m >>=ᴹ (λ S′ → runProtocol S′ ys)) e₁) e₂)

acceptPaid : (S : ProtocolSt) → paidUp S ≡ true → Accepted (checkFinal (just S))
acceptPaid S eq rewrite eq = accepted

-- dry-freeness splits over ++ (the step lemmas are conditioned on it;
-- budget-sufficient below asserts it for the whole seeded run)
true≢false : {A : Set} → true ≡ false → A
true≢false ()

hasDry-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry (xs ++ ys) ≡ false →
  (hasDry xs ≡ false) × (hasDry ys ≡ false)
hasDry-++ []        ys h = refl , h
hasDry-++ (em ∷ xs) ys h
  with sameSource (InstEmit.source em) drySource
     | any dryEvent (InstEmit.events em)
... | true  | _     = true≢false h
... | false | true  = true≢false h
... | false | false = hasDry-++ xs ys h

------------------------------------------------------------------
-- Inv, CONCRETE: the between-cascades simulation relation
------------------------------------------------------------------

-- registrations of s, counted off the registry (the writer's ledger
-- the automaton's live multiset must shadow)
countRegs : ∀ {n} {Γ : Ctx n} {t}
          → Source → List (RegId × Source × Chain Γ t) → ℕ
countRegs s [] = zero
countRegs s ((_ , x , _) ∷ r) =
  if s ≡ᵇ x then suc (countRegs s r) else countRegs s r

-- snapshot entries still obliged to fire: not yet forgiven by a
-- cutPending (the automaton's remaining owed for the arrival source)
countRemaining : ∀ {X : Set} → List (RegId × X) → List RegId → ℕ
countRemaining []               c = zero
countRemaining ((rid , _) ∷ ps) c =
  if any (_≡ᵇ rid) c then countRemaining ps c else suc (countRemaining ps c)

-- association-list reads on the automaton's owed table
lookupOwed : Source → Owed → ℕ
lookupOwed s []            = zero
lookupOwed s ((x , n) ∷ o) = if s ≡ᵇ x then n else lookupOwed s o

-- every source but s is paid to zero (bumped shares get paid back
-- down within the very chainStep that announced them)
zeroExcept : Source → Owed → Bool
zeroExcept s []            = true
zeroExcept s ((x , n) ∷ o) =
  (if s ≡ᵇ x then true else n ≡ᵇ 0) ∧ zeroExcept s o

-- the owed table's keys never repeat (bumpOwed adds to an existing
-- entry, never a second one): with `zeroExcept s` this pins down every
-- entry, so a zero at s means the whole table is zero (allZero-clean)
notKeyOwed : Source → Owed → Bool
notKeyOwed s []            = true
notKeyOwed s ((x , _) ∷ o) = not (s ≡ᵇ x) ∧ notKeyOwed s o

UniqueOwed : Owed → Bool
UniqueOwed []            = true
UniqueOwed ((x , _) ∷ o) = notKeyOwed x o ∧ UniqueOwed o

-- a path that never reaches the root delivers no values there
sinksToShare : ∀ {n} {Γ : Ctx n} {u t} → Path Γ u t → Bool
sinksToShare root           = false
sinksToShare (share-sink i) = true
sinksToShare (f ↠ p)        = sinksToShare p

allShareSunk : ∀ {n} {Γ : Ctx n} {t}
             → List (RegId × Source × Chain Γ t) → Bool
allShareSunk []                      = true
allShareSunk ((_ , _ , (u , p)) ∷ r) = sinksToShare p ∧ allShareSunk r

-- the registry↔schedule type-consistency invariant (replaces the old
-- one-lookahead chains-count): every registration's source-type matches
-- every live source of the same source.  Share-sunk registrations whose
-- source has no live entry are unconstrained — chainsOf only ever reads
-- entries of a SCHEDULED source, and those all trace to a LiveSource, so
-- this pins their type-check to pass (chains-count-derived below)
sameTy : Ty → Ty → Bool
sameTy s u with s ≟ᵗ u
... | yes _ = true
... | no  _ = false

liveTypeOK? : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveTypeOK? s u []       = true
liveTypeOK? s u (l ∷ ls) =
  (if LiveSource.source l ≡ᵇ s then sameTy u (LiveSource.elemTy l) else true)
    ∧ liveTypeOK? s u ls

regTyped? : ∀ {n} {Γ : Ctx n} {t} → List (RegId × Source × Chain Γ t)
          → List (LiveSource Γ) → Bool
regTyped? []                      live = true
regTyped? ((_ , s , (u , _)) ∷ r) live = liveTypeOK? s u live ∧ regTyped? r live

≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

≡ᵇ-refl : ∀ (m : ℕ) → (m ≡ᵇ m) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc m) = ≡ᵇ-refl m

∧-trueˡ : ∀ {a b : Bool} → (a ∧ b) ≡ true → a ≡ true
∧-trueˡ {true} _ = refl

∧-trueʳ : ∀ {a b : Bool} → (a ∧ b) ≡ true → b ≡ true
∧-trueʳ {true} h = h

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro refl refl = refl

if-false : ∀ {A : Set} {x y : A} (b : Bool) → b ≡ false → (if b then x else y) ≡ y
if-false b eq rewrite eq = refl

if-true : ∀ {A : Set} {x y : A} (b : Bool) → b ≡ true → (if b then x else y) ≡ x
if-true b eq rewrite eq = refl

sameTy-sound : ∀ (a b : Ty) → sameTy a b ≡ true → a ≡ b
sameTy-sound a b h with a ≟ᵗ b
... | yes p = p
... | no  _ = true≢false (sym h)

sameTy-refl : ∀ (a : Ty) → sameTy a a ≡ true
sameTy-refl a with a ≟ᵗ a
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)

-- the arrival a live source pops carries its source and elemTy
schedHeadOf-match : ∀ {n} {Γ : Ctx n} (l : LiveSource Γ) {a : Arrival Γ} {l′} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  (arrSource a ≡ LiveSource.source l) × (arrTy a ≡ LiveSource.elemTy l)
schedHeadOf-match l eq with LiveSource.pending l | eq
... | (t , v) ∷ ps | refl = refl , refl

-- a's source/type is present among the live sources sched-next drew from
liveHas : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveHas s τ []       = false
liveHas s τ (l ∷ ls) =
  ((LiveSource.source l ≡ᵇ s) ∧ sameTy τ (LiveSource.elemTy l)) ∨ liveHas s τ ls

∨-trueʳ : ∀ (x : Bool) → (x ∨ true) ≡ true
∨-trueʳ false = refl
∨-trueʳ true  = refl

-- the arrival schedGo pops is one of the live sources it drew from
schedGo-mem : ∀ {n} {Γ : Ctx n} (live : List (LiveSource Γ)) {a : Arrival Γ} {ls} →
  schedGo live ≡ inj₂ (a , ls) → liveHas (arrSource a) (arrTy a) live ≡ true
schedGo-mem (l ∷ ls) eq with schedHeadOf l in heq | schedGo ls in geq
... | inj₁ _        | inj₁ _         with eq
...   | ()
schedGo-mem (l ∷ ls) eq | inj₁ _ | inj₂ (a′ , ls′) with eq
...   | refl rewrite schedGo-mem ls geq = ∨-trueʳ _
schedGo-mem (l ∷ ls) eq | inj₂ (a₀ , l′) | inj₁ _ with eq
...   | refl rewrite proj₁ (schedHeadOf-match l heq)
                   | proj₂ (schedHeadOf-match l heq)
                   | ≡ᵇ-refl (LiveSource.source l)
                   | sameTy-refl (LiveSource.elemTy l) = refl
schedGo-mem (l ∷ ls) eq | inj₂ (a₀ , l′) | inj₂ (a′ , ls′) with schedEarlier a₀ a′ | eq
...   | true  | refl rewrite proj₁ (schedHeadOf-match l heq)
                           | proj₂ (schedHeadOf-match l heq)
                           | ≡ᵇ-refl (LiveSource.source l)
                           | sameTy-refl (LiveSource.elemTy l) = refl
...   | false | refl rewrite schedGo-mem ls geq = ∨-trueʳ _

-- a source-matching live source pins the registration's type via regTyped?
liveTypeOK?-extract : ∀ {n} {Γ : Ctx n} (s : Source) (u τ : Ty)
  (live : List (LiveSource Γ)) →
  liveTypeOK? s u live ≡ true → liveHas s τ live ≡ true → sameTy u τ ≡ true
liveTypeOK?-extract s u τ []       ok has = true≢false (sym has)
liveTypeOK?-extract s u τ (l ∷ ls) ok has with LiveSource.source l ≡ᵇ s
... | false = liveTypeOK?-extract s u τ ls (∧-trueʳ ok) has
... | true  with sameTy τ (LiveSource.elemTy l) in seq
...   | true  = subst (λ z → sameTy u z ≡ true)
                  (trans (sameTy-sound u (LiveSource.elemTy l) (∧-trueˡ ok))
                         (sym (sameTy-sound τ (LiveSource.elemTy l) seq)))
                  (sameTy-refl u)
...   | false = liveTypeOK?-extract s u τ ls (∧-trueʳ ok) has

-- the registry induction: every entry of a's source is a's-typed (else
-- regTyped? + the live source would contradict), so no chainsGo drop
count-eq : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → liveHas (arrSource a) (arrTy a) live ≡ true →
  countRegs (arrSource a) reg ≡ length (chainsGo a reg)
count-eq a []                      live rt lh = refl
count-eq a ((rid , s , (u , p)) ∷ r) live rt lh
  with sameSource (arrSource a) s in sseq
... | false = count-eq a r live (∧-trueʳ rt) lh
... | true  with u ≟ᵗ arrTy a
...   | yes refl = cong suc (count-eq a r live (∧-trueʳ rt) lh)
...   | no ¬p    = ⊥-elim (¬p (sameTy-sound u (arrTy a)
                    (liveTypeOK?-extract (arrSource a) u (arrTy a) live
                      (subst (λ z → liveTypeOK? z u live ≡ true)
                             (sym (≡ᵇ→≡ (arrSource a) s sseq)) (∧-trueˡ rt))
                      lh)))

-- THE derived fact, recovering the old one-lookahead chains-count from
-- the pointwise registry↔schedule type-consistency invariant
chains-count-derived : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched sched″ : Sched Γ) (st : EvalSt e) →
  regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true →
  sched-next sched ≡ inj₂ (a , sched″) →
  countRegs (arrSource a) (EvalSt.registry st) ≡ length (chainsOf a st)
chains-count-derived a sched sched″ st rt eq with schedGo (Sched.live sched) in geq
... | inj₁ _ with eq
...   | ()
chains-count-derived a sched sched″ st rt eq | inj₂ (a₀ , ls) with eq
...   | refl = count-eq a₀ (EvalSt.registry st) (Sched.live sched) rt
                 (schedGo-mem (Sched.live sched) geq)

-- popping an arrival only shortens a live source's pending — source and
-- elemTy are untouched, so liveTypeOK? (hence regTyped?) is preserved
schedHeadOf-l′ : ∀ {n} {Γ : Ctx n} (l : LiveSource Γ) {a : Arrival Γ} {l′} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  (LiveSource.source l′ ≡ LiveSource.source l) × (LiveSource.elemTy l′ ≡ LiveSource.elemTy l)
schedHeadOf-l′ l eq with LiveSource.pending l | eq
... | (t , v) ∷ ps | refl = refl , refl

liveTypeOK?-swap : ∀ {n} {Γ : Ctx n} (s : Source) (u : Ty)
  (l l′ : LiveSource Γ) (rest : List (LiveSource Γ)) →
  LiveSource.source l′ ≡ LiveSource.source l →
  LiveSource.elemTy l′ ≡ LiveSource.elemTy l →
  liveTypeOK? s u (l′ ∷ rest) ≡ liveTypeOK? s u (l ∷ rest)
liveTypeOK?-swap s u l l′ rest seq teq rewrite seq | teq = refl

schedGo-liveTypeOK : ∀ {n} {Γ : Ctx n} (live : List (LiveSource Γ)) {a : Arrival Γ} {ls} →
  schedGo live ≡ inj₂ (a , ls) →
  ∀ (s : Source) (u : Ty) → liveTypeOK? s u ls ≡ liveTypeOK? s u live
schedGo-liveTypeOK (l ∷ ls) eq s u with schedHeadOf l in heq | schedGo ls in geq
... | inj₁ _        | inj₁ _         with eq
...   | ()
schedGo-liveTypeOK (l ∷ ls) eq s u | inj₁ _ | inj₂ (a′ , ls′) with eq
...   | refl = cong (_∧_ (if LiveSource.source l ≡ᵇ s
                          then sameTy u (LiveSource.elemTy l) else true))
                    (schedGo-liveTypeOK ls geq s u)
schedGo-liveTypeOK (l ∷ ls) eq s u | inj₂ (a₀ , l′) | inj₁ _ with eq
...   | refl = liveTypeOK?-swap s u l l′ ls
                 (proj₁ (schedHeadOf-l′ l heq)) (proj₂ (schedHeadOf-l′ l heq))
schedGo-liveTypeOK (l ∷ ls) eq s u | inj₂ (a₀ , l′) | inj₂ (a′ , ls′)
  with schedEarlier a₀ a′ | eq
...   | true  | refl = liveTypeOK?-swap s u l l′ ls
                         (proj₁ (schedHeadOf-l′ l heq)) (proj₂ (schedHeadOf-l′ l heq))
...   | false | refl = cong (_∧_ (if LiveSource.source l ≡ᵇ s
                                  then sameTy u (LiveSource.elemTy l) else true))
                            (schedGo-liveTypeOK ls geq s u)

regTyped?-pop : ∀ {n} {Γ : Ctx n} {t} (reg : List (RegId × Source × Chain Γ t))
  (live : List (LiveSource Γ)) {a : Arrival Γ} {ls} →
  schedGo live ≡ inj₂ (a , ls) → regTyped? reg live ≡ true → regTyped? reg ls ≡ true
regTyped?-pop []                      live sgeq rt = refl
regTyped?-pop ((_ , s , (u , _)) ∷ r) live sgeq rt =
  ∧-intro (trans (schedGo-liveTypeOK live sgeq s u) (∧-trueˡ rt))
          (regTyped?-pop r live sgeq (∧-trueʳ rt))

regTyped?-pop-sched : ∀ {n} {Γ : Ctx n} {t} (sched sched′ : Sched Γ)
  (reg : List (RegId × Source × Chain Γ t)) {a : Arrival Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  regTyped? reg (Sched.live sched) ≡ true → regTyped? reg (Sched.live sched′) ≡ true
regTyped?-pop-sched sched sched′ reg eq rt with schedGo (Sched.live sched) in geq
... | inj₁ _ with eq
...   | ()
regTyped?-pop-sched sched sched′ reg eq rt | inj₂ (a₀ , ls) with eq
...   | refl = regTyped?-pop reg (Sched.live sched) geq rt

-- cascadeFinish preserves type-consistency: dropSource only removes
-- registrations, sweepLive only removes live sources — both loosen
-- regTyped?, never tighten it
regTyped?-dropReg : ∀ {n} {Γ : Ctx n} {t} (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → regTyped? (dropSource src reg) live ≡ true
regTyped?-dropReg src []                      live rt = refl
regTyped?-dropReg src ((rid , s , (u , p)) ∷ r) live rt with sameSource src s
... | true  = regTyped?-dropReg src r live (∧-trueʳ rt)
... | false = ∧-intro (∧-trueˡ rt) (regTyped?-dropReg src r live (∧-trueʳ rt))

liveTypeOK?-sweepLive : ∀ {n} {Γ : Ctx n} {t}
  (sweepReg : List (RegId × Source × Chain Γ t)) (s : Source) (u : Ty)
  (live : List (LiveSource Γ)) →
  liveTypeOK? s u live ≡ true → liveTypeOK? s u (sweepLive sweepReg live) ≡ true
liveTypeOK?-sweepLive sweepReg s u []       ok = refl
liveTypeOK?-sweepLive {n = n} sweepReg s u (l ∷ ls) ok
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) sweepReg
... | true  = ∧-intro (∧-trueˡ ok) (liveTypeOK?-sweepLive sweepReg s u ls (∧-trueʳ ok))
... | false = liveTypeOK?-sweepLive sweepReg s u ls (∧-trueʳ ok)

regTyped?-sweepLive : ∀ {n} {Γ : Ctx n} {t}
  (sweepReg reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → regTyped? reg (sweepLive sweepReg live) ≡ true
regTyped?-sweepLive sweepReg []                      live rt = refl
regTyped?-sweepLive sweepReg ((_ , s , (u , _)) ∷ r) live rt =
  ∧-intro (liveTypeOK?-sweepLive sweepReg s u live (∧-trueˡ rt))
          (regTyped?-sweepLive sweepReg r live (∧-trueʳ rt))

reg-typed-finish : ∀ {n} {Γ : Ctx n} {t} (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true →
  regTyped? (dropSource src reg) (sweepLive (dropSource src reg) live) ≡ true
reg-typed-finish src reg live rt =
  regTyped?-sweepLive (dropSource src reg) (dropSource src reg) live
    (regTyped?-dropReg src reg live rt)

-- the open (or last) instant is strictly in the past
CurrentPast : Maybe (Id × Owed) → Id → Set
CurrentPast nothing        nextId = ⊤
CurrentPast (just (j , _)) nextId = suc j ≤ nextId

record Inv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    -- the automaton's live multiset shadows the registry: per source,
    -- one for one
    live-matches : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    -- registry entries are well-typed for their scheduled source (each
    -- registration's type matches its live source's elemTy), so chainsOf's
    -- type check drops nothing — countRegs ≡ length chainsOf for every
    -- scheduled arrival (chains-count-derived).  A pointwise fact, unlike
    -- the old one-lookahead form, so it threads across scheduler pops
    reg-typed    : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    -- freshness is one comparison: ids mint from arrival position
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    current-past : CurrentPast (ProtocolSt.current S) nextId
    -- after the root completes, only share plumbing survives — no
    -- registration can ever carry a value to the root again
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true

------------------------------------------------------------------
-- the subscribe frame: BurstInv and its entry/step/exit lemmas
------------------------------------------------------------------

-- mid-subscribe-frame, CONCRETE: live shadows the registry exactly
-- (burst closes and registry cuts move in lockstep), and the open
-- instant — if any emit has landed — is `id` with a LITERALLY EMPTY
-- owed table: subscribe/plumbing settle to net zero, handoffs are
-- minted only by foldPath (never in a burst), and cancelOwed on []
-- is a no-op, so nothing ever writes an entry
record BurstInv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                (id : Id) (sched : Sched Γ) (st : EvalSt e)
                (S : ProtocolSt) : Set where
  field
    live-matches  : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    reg-typed     : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low   : ProtocolSt.horizon S ≤ id
    current-frame : (ProtocolSt.current S ≡ nothing)
                  ⊎ (ProtocolSt.current S ≡ just (id , []))
    done-plumbed  : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true

-- the empty states are related
burst-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  BurstInv {e = e} 0 (sched-init e ins) (st-init e) protocol-init
burst-init e ins = record
  { live-matches  = λ s → refl
  ; reg-typed     = refl
  ; horizon-low   = z≤n
  ; current-frame = inj₁ refl
  ; done-plumbed  = λ ()
  }

postulate
  -- ONE subscription's burst preserves the frame relation.  The
  -- per-primitive preservation induction: one obligation per
  -- subscribeE clause, mirrored on its (now fuel-structural)
  -- recursion.  Conditioned on the run not going dry: a fuel-starved
  -- burst carries the dry sentinel, which the protocol rejects by
  -- design — the unconditioned statement would be false at fuel 0
  subscribeE-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : ℕ) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel b κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel b κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

-- an instant standing on an empty (or absent) owed table settles
≤-up : ∀ {a b : ℕ} → a ≤ b → a ≤ suc b
≤-up z≤n     = z≤n
≤-up (s≤s p) = s≤s (≤-up p)

paid-nothing : (S : ProtocolSt) → ProtocolSt.current S ≡ nothing →
               paidUp S ≡ true
paid-nothing S ceq with ProtocolSt.current S | ceq
... | nothing | refl = refl

paid-empty : (S : ProtocolSt) {j : Id} →
             ProtocolSt.current S ≡ just (j , []) → paidUp S ≡ true
paid-empty S ceq with ProtocolSt.current S | ceq
... | just (j , []) | refl = refl

-- leaving the frame: the open instant settles (owed never seeded ⇒
-- paid), landing Inv-related for the first arrival
burst-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv 0 sched st S →
  Inv 1 sched st S × (paidUp S ≡ true)
burst-final sched st S binv = inv , paid (BurstInv.current-frame binv)
  where
  past : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       CurrentPast (ProtocolSt.current S) 1
  past (inj₁ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) tt
  past (inj₂ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) (s≤s z≤n)

  paid : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       paidUp S ≡ true
  paid (inj₁ ceq) = paid-nothing S ceq
  paid (inj₂ ceq) = paid-empty S ceq

  inv : Inv 1 sched st S
  inv = record
    { live-matches = BurstInv.live-matches binv
    ; reg-typed    = BurstInv.reg-typed binv
    ; horizon-low  = ≤-up (BurstInv.horizon-low binv)
    ; current-past = past (BurstInv.current-frame binv)
    ; done-plumbed = BurstInv.done-plumbed binv
    }

-- the root subscription, composed (at the budget evaluate seeds)
subscribe-wf :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false →
  Σ ProtocolSt λ S →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in (runProtocol protocol-init (proj₁ r) ≡ just S)
       × Inv 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
       × (paidUp S ≡ true)
subscribe-wf e ins nodry
  with subscribeE-wf (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
                     protocol-init (burst-init e ins) nodry
... | S , run , binv
  with burst-final _ _ S binv
... | inv , paid = S , run , inv , paid

------------------------------------------------------------------
-- one cascade: Mid and its entry/step/exit lemmas, the chain fold
-- composed
------------------------------------------------------------------

-- mid-cascade, CONCRETE, indexed by the chains still to fold.  Two
-- asymmetries a naive "live shadows registry" misses:
--   · for a spent (isLast) arrival the automaton runs AHEAD of the
--     registry — each delivered chain's exhausted close retires its
--     live entry on the spot, but the registry entries drop only at
--     cascadeFinish — so the arrival source's live count equals the
--     obliged remainder of the snapshot, not the registry count;
--   · the owed table exists only once the first chain emit has
--     opened the instant (seeding happens at first delivery), so the
--     ledger is a sum: not-yet-opened (the automaton still stands on
--     the previous, settled instant) or opened with owed[arrSource]
--     = the not-yet-cancelled remainder and every share paid back to
--     zero (a handoff's bump is repaid within its own chainStep).
-- fold-live carries dry-freeness for the remaining fold: Mid's
-- arguments determine every future chainStep, so the premise lives
-- here instead of infecting every step statement
record Mid {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (nextId : Id)
           (ps : List (RegId × Path Γ (arrTy a) t))
           (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    live-others  : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    live-source  : countIn (arrSource a) (ProtocolSt.live S)
      ≡ (if Arrival.isLast a
         then countRemaining ps (EvalSt.cancelled st)
         else countRegs (arrSource a) (EvalSt.registry st))
    reg-typed    : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    ledger       :
        (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
      ⊎ (Σ Owed λ ow →
           (ProtocolSt.current S ≡ just (nextId , ow))
         × (lookupOwed (arrSource a) ow
              ≡ countRemaining ps (EvalSt.cancelled st))
         × (zeroExcept (arrSource a) ow ≡ true))
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true
    fold-live    : hasDry (proj₁ (cascadeGo a nextId ps sched st)) ≡ false
    -- ADDED (owed-key uniqueness): the open instant's owed table has no
    -- repeated key, so ledger's zeroExcept + the arrival's zero remainder
    -- force allZero — the payoff mid-final reads out.  Preserved by
    -- mid-skip (same S); established by mid-init/mid-step (postulated).
    owed-unique  : ∀ (ow : Owed) →
      ProtocolSt.current S ≡ just (nextId , ow) → UniqueOwed ow ≡ true

------------------------------------------------------------------
-- Protocol foundation for foldPath-wf: a CONSTRUCTIVE stepProtocol.
-- enterInstant abstracts stepProtocol's enter/openFresh split (idle,
-- held, continue) into one Maybe (base-owed × horizon-for-go): `just`
-- means the automaton admits instant i, seeding `go` with that owed and
-- horizon.  stepProtocol-enter then rebuilds stepProtocol's result from
-- that plus the settle and applyEvents outcomes — the reverse of
-- The-Proof's stepProtocol-idle/held/cont (construction, not analysis).
------------------------------------------------------------------

openFreshᴵ : ProtocolSt → Id → Maybe (Owed × Id)
openFreshᴵ S i with settleInstant S
... | nothing = nothing
... | just hz = if hz ≤ᵇ i then just ([] , hz) else nothing

enterInstant : ProtocolSt → Id → Maybe (Owed × Id)
enterInstant S i with ProtocolSt.current S
... | nothing         = openFreshᴵ S i
... | just (j , owed) = if i ≡ᵇ j
      then (if paidOff owed then nothing else just (owed , ProtocolSt.horizon S))
      else openFreshᴵ S i

stepProtocol-enter-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (cur : Maybe (Id × Owed))
  {ob hz′ ob′} {L : List Source} {O : Owed} {D : Bool} →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just (ob , hz′) →
  settle k s lv ob ≡ just ob′ →
  applyEvents es lv ob′ dn ≡ just (L , O , D) →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = dn })
    ≡ just (record { live = L ; horizon = hz′ ; current = just (i , O) ; done = D })
stepProtocol-enter-aux es i s k lv hz dn nothing entEq stEq apEq
  with hz ≤ᵇ i | entEq
... | true | refl rewrite stEq | apEq = refl
stepProtocol-enter-aux es i s k lv hz dn (just (j , owed)) entEq stEq apEq
  with i ≡ᵇ j | entEq
... | true  | e with paidOff owed | e
...   | false | refl rewrite stEq | apEq = refl
stepProtocol-enter-aux es i s k lv hz dn (just (j , owed)) entEq stEq apEq
    | false | e
  with allZero owed | e
...   | true | e′ with suc j ≤ᵇ i | e′
...     | true | refl rewrite stEq | apEq = refl

stepProtocol-enter : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S : ProtocolSt) {ob hz′ ob′} {L : List Source} {O : Owed} {D : Bool} →
  enterInstant S i ≡ just (ob , hz′) →
  settle k s (ProtocolSt.live S) ob ≡ just ob′ →
  applyEvents es (ProtocolSt.live S) ob′ (ProtocolSt.done S) ≡ just (L , O , D) →
  stepProtocol (es at i from s as k) S
    ≡ just (record { live = L ; horizon = hz′ ; current = just (i , O) ; done = D })
stepProtocol-enter es i s k S entEq stEq apEq =
  stepProtocol-enter-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) (ProtocolSt.current S) entEq stEq apEq

-- applyEvents plumbing for the root emit: it splits over ++, the
-- accumulated bookkeeping (init/close only — never value/complete, which
-- splitEvents routes to the value list / done flag) leaves `done`
-- untouched, and the value list + optional complete tack on cleanly.
just-injᵂ : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-injᵂ refl = refl

applyEvents-++just : ∀ {A : Set} (es₁ es₂ : List (InstEvent A))
  (lv : List Source) (o : Owed) (d : Bool) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es₁ lv o d ≡ just (L , O , D) →
  applyEvents (es₁ ++ es₂) lv o d ≡ applyEvents es₂ L O D
applyEvents-++just [] es₂ lv o d eq with just-injᵂ eq
... | refl = refl
applyEvents-++just (init x ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ (x ∷ lv) o d eq
applyEvents-++just (value v ∷ es) es₂ lv o d eq with d | eq
... | false | eq′ = applyEvents-++just es es₂ lv o false eq′
... | true  | ()
applyEvents-++just (handoff x ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ lv (bumpOwed x (countIn x lv) o) d eq
applyEvents-++just (complete ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ lv o true eq
applyEvents-++just (close x cutPending ∷ es) es₂ lv o d eq
  with removeOne x lv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ = applyEvents-++just es es₂ lv′ o′ d eq′
... | just lv′ | nothing | ()
... | nothing  | just o′ | ()
... | nothing  | nothing | ()
applyEvents-++just (close x cut ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()
applyEvents-++just (close x exhausted ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()

-- the value list changes nothing but must not ride behind a `complete`
-- (done-nil: a done automaton delivers no value) — so it folds to identity
applyEvents-values : ∀ {A : Set} (vals : List A) (lv : List Source) (o : Owed) (d : Bool) →
  (d ≡ true → vals ≡ []) →
  applyEvents (map value vals) lv o d ≡ just (lv , o , d)
applyEvents-values []       lv o d _    = refl
applyEvents-values (v ∷ vs) lv o d cond with d | cond
... | false | _ = applyEvents-values vs lv o false (λ ())
... | true  | c with c refl
...   | ()

-- the optional trailing complete sets done exactly when fin
applyEvents-maybeComplete : ∀ {A : Set} (fin : Bool) (lv : List Source) (o : Owed) (d : Bool) →
  applyEvents {A} (if fin then complete ∷ [] else []) lv o d
    ≡ just (lv , o , (if fin then true else d))
applyEvents-maybeComplete true  lv o d = refl
applyEvents-maybeComplete false lv o d = refl

-- the whole root tail (values then optional complete) after the evs
applyEvents-vc : ∀ {A : Set} (vals : List A) (fin : Bool)
  (lv : List Source) (o : Owed) (d : Bool) → (d ≡ true → vals ≡ []) →
  applyEvents (map value vals ++ (if fin then complete ∷ [] else [])) lv o d
    ≡ just (lv , o , (if fin then true else d))
applyEvents-vc vals fin lv o d cond =
  trans (applyEvents-++just (map value vals) (if fin then complete ∷ [] else [])
          lv o d (applyEvents-values vals lv o d cond))
        (applyEvents-maybeComplete fin lv o d)

runProtocol-one : ∀ {A : Set} (S : ProtocolSt) (x : InstEmit A) →
  runProtocol S (x ∷ []) ≡ stepProtocol x S
runProtocol-one S x with stepProtocol x S
... | just S′ = refl
... | nothing = refl

-- foldPath-wf, ROOT clause (PROVEN): a chain that reaches the root emits
-- its ONE delivery — accumulated bookkeeping evs, then the (possibly
-- empty) value list, then complete iff the source is spent.  The
-- automaton admits it (enterInstant), pays envSrc's owed (settle), folds
-- the evs (which never touch `done`), and the values ride only if not
-- already done (done-nil).  sched/st are untouched at root.
foldPath-root-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (vals : List (Val Γ t)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
  (ob : Owed) (hz : Id) (ob′ : Owed) (Lv : List Source) (Ov : Owed) →
  enterInstant S id ≡ just (ob , hz) →
  settle delivery envSrc (ProtocolSt.live S) ob ≡ just ob′ →
  applyEvents evs (ProtocolSt.live S) ob′ (ProtocolSt.done S)
    ≡ just (Lv , Ov , ProtocolSt.done S) →
  (ProtocolSt.done S ≡ true → vals ≡ []) →
  runProtocol S (proj₁ (foldPath sf gas id now envSrc root vals evs fin sched st))
    ≡ just (record { live = Lv ; horizon = hz ; current = just (id , Ov)
                   ; done = (if fin then true else ProtocolSt.done S) })
foldPath-root-wf sf gas id now envSrc vals evs fin sched st S ob hz ob′ Lv Ov
  entEq payEq apEq dn =
  trans (runProtocol-one S _) stepEq
  where
  target : ProtocolSt
  target = record { live = Lv ; horizon = hz ; current = just (id , Ov)
                  ; done = (if fin then true else ProtocolSt.done S) }
  apply-full :
    applyEvents (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
      (ProtocolSt.live S) ob′ (ProtocolSt.done S)
      ≡ just (Lv , Ov , (if fin then true else ProtocolSt.done S))
  apply-full = trans
    (applyEvents-++just evs (map value vals ++ (if fin then complete ∷ [] else []))
      (ProtocolSt.live S) ob′ (ProtocolSt.done S) apEq)
    (applyEvents-vc vals fin Lv Ov (ProtocolSt.done S) dn)
  stepEq :
    stepProtocol
      ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
        at id from envSrc as delivery) S
      ≡ just target
  stepEq = stepProtocol-enter
    (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    id envSrc delivery S entEq payEq apply-full

------------------------------------------------------------------
-- foldPath-wf: one chain's fold, by induction on the Path (free source
-- type u — the split lives HERE, not at mid-step, see the blueprint).
-- FoldInv is the mid-fold relation: the automaton admits instant id,
-- pays envSrc, and the bookkeeping accumulated so far (evs) folds
-- cleanly, with the value list gated by done-nil.  root is PROVEN
-- (foldPath-root-wf); the frame case is IH ∘ stepFrame-wf (same emits,
-- definitionally — a frame accumulates evs, never emits); share defers
-- to dispatchShare-wf.  Acceptance only for now; the Mid-preservation
-- half (the POST) is the next layer.
------------------------------------------------------------------

record FoldInv {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
       (id : Id) (envSrc : Source) (vals : List (Val Γ u))
       (evs : List (InstEvent (Val Γ t))) (fin : Bool)
       (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) : Set where
  field
    ob   : Owed
    hz   : Id
    ob′  : Owed
    Lv   : List Source
    Ov   : Owed
    enters   : enterInstant S id ≡ just (ob , hz)
    pays     : settle delivery envSrc (ProtocolSt.live S) ob ≡ just ob′
    applies  : applyEvents evs (ProtocolSt.live S) ob′ (ProtocolSt.done S)
                 ≡ just (Lv , Ov , ProtocolSt.done S)
    -- once the root completes only share plumbing survives: every
    -- registration sinks to a share, so a share fan-out's inners are all
    -- share-bound (their own done-discipline, for dispatchShare-wf)
    done-plumbed : ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true

postulate
  -- a frame preserves FoldInv (S untouched — frames don't step the
  -- automaton): stepFrame's bookkeeping evs′ brackets against its
  -- registry mutation, and the value transform keeps done-nil.  The
  -- delivery-side twin of subscribeE-wf's per-clause grind (map/scan/
  -- take/*All), one obligation per stepFrame clause.
  stepFrame-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {w u}
    (sf : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (f : Frame Γ w u) (path′ : Path Γ u t)
    (vals : List (Val Γ w)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc vals evs fin sched st S →
    let (vals′ , evs′ , fin′ , sched₁ , st₁) = stepFrame sf id now f path′ vals fin sched st
    in FoldInv id envSrc vals′ (evs ++ evs′) fin′ sched₁ st₁ S

  -- the share fan-out: one handoff emit, then one delivery per share
  -- registration (each its own foldPath) — mutually recursive with
  -- foldPath-wf.  The handoff's owed bump is repaid across the fan-out.
  dispatchShare-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i)))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc vals evs fin sched st S →
    Σ ProtocolSt λ S′ →
      runProtocol S (proj₁ (foldPath sf gas id now envSrc (share-sink i) vals evs fin sched st))
        ≡ just S′

-- the done-discipline, as a precondition: a done automaton (root already
-- completed) admits only share-bound folds — a chain reaching the root
-- after completion would be a value-after-complete, which the protocol
-- rejects.  At root (sinksToShare = false) this forces done S ≡ false, so
-- the value list rides; it transfers unchanged through a frame and is
-- vacuous at a share-sink.
-- a hypothesis whose codomain reduces to false forces its subject false
force-false : (b : Bool) → (b ≡ true → false ≡ true) → b ≡ false
force-false false _ = refl
force-false true  d with d refl
... | ()

foldPath-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  FoldInv id envSrc vals evs fin sched st S →
  (ProtocolSt.done S ≡ true → sinksToShare path ≡ true) →
  Σ ProtocolSt λ S′ →
    runProtocol S (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st))
      ≡ just S′
foldPath-wf sf gas id now envSrc root vals evs fin sched st S fi ds =
  _ , foldPath-root-wf sf gas id now envSrc vals evs fin sched st S
        (FoldInv.ob fi) (FoldInv.hz fi) (FoldInv.ob′ fi) (FoldInv.Lv fi) (FoldInv.Ov fi)
        (FoldInv.enters fi) (FoldInv.pays fi) (FoldInv.applies fi) done-nil
  where
  df : ProtocolSt.done S ≡ false
  df = force-false (ProtocolSt.done S) ds
  done-nil : ProtocolSt.done S ≡ true → vals ≡ []
  done-nil deq with trans (sym df) deq
  ... | ()
foldPath-wf sf gas id now envSrc (f ↠ path′) vals evs fin sched st S fi ds =
  foldPath-wf sf gas id now envSrc path′
    (proj₁ (stepFrame sf id now f path′ vals fin sched st))
    (evs ++ proj₁ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))
    (proj₁ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st))))
    (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
    S (stepFrame-wf sf id now envSrc f path′ vals evs fin sched st S fi) ds
foldPath-wf sf gas id now envSrc (share-sink i) vals evs fin sched st S fi ds =
  dispatchShare-wf sf gas id now envSrc i vals evs fin sched st S fi

------------------------------------------------------------------
-- The seed: Mid (head ∷ ps) ⇒ FoldInv at the chainStep seed.  The
-- "counting machine" arithmetic — a key with a positive owed is not
-- paid-off; paying it decrements the key; a source present in `live`
-- can be removed.  These are the owed/live manipulations the enter,
-- pay, and applyEvents seed fields turn on.
------------------------------------------------------------------

lookup-pos-not-allZero : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → allZero ow ≡ false
lookup-pos-not-allZero s [] k ()
lookup-pos-not-allZero s ((x , zero)  ∷ ow) k eq with s ≡ᵇ x | eq
... | true  | ()
... | false | eq′ = lookup-pos-not-allZero s ow k eq′
lookup-pos-not-allZero s ((x , suc n) ∷ ow) k eq = refl

lookup-pos-not-paidOff : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → paidOff ow ≡ false
lookup-pos-not-paidOff s [] k ()
lookup-pos-not-paidOff s (e ∷ ow) k eq = lookup-pos-not-allZero s (e ∷ ow) k eq

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true _ = refl

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → (m ≤ᵇ n) ≡ true
≤→≤ᵇ {m} {n} p = T→≡ (m ≤ᵇ n) (≤⇒≤ᵇ p)

-- the automaton admits an OPEN unpaid instant: enterInstant continues it,
-- seeding go with the running owed and the standing horizon.  Fields taken
-- literally so enterInstant's `with current` reduces (enterInstant reads
-- only current/horizon, never live/done, so the dummies are harmless)
enterInstant-cont-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) (ow : Owed) →
  cur ≡ just (i , ow) → paidOff ow ≡ false →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just (ow , hz)
enterInstant-cont-aux lv hz i .(just (i , ow)) dn ow refl pf rewrite ≡ᵇ-refl i | pf = refl

enterInstant-cont : ∀ (S : ProtocolSt) (i : Id) (ow : Owed) →
  ProtocolSt.current S ≡ just (i , ow) → paidOff ow ≡ false →
  enterInstant S i ≡ just (ow , ProtocolSt.horizon S)
enterInstant-cont S i ow cur pf =
  enterInstant-cont-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i
    (ProtocolSt.current S) (ProtocolSt.done S) ow cur pf

-- DECOMPOSITION BLUEPRINT (mid-step, the delivery-side sibling of
-- subscribeE-wf — "the per-clause preservation grind").  One surviving
-- chain's emits — its own delivery, any share fan-outs it triggers, any
-- cut closes — are accepted, paying/bumping/cancelling exactly per the
-- ledger.  The tower to grind, mirroring the evaluator's own recursion:
--
--   mid-step  ⇐  foldPath-wf  (induction on the Path)
--                ├─ root         : the chain's ONE delivery emit — the
--                │                  only place a linear path touches the
--                │                  protocol; frames merely accumulate
--                │                  evs/vals (they never step it)
--                ├─ f ↠ path′    : stepFrame-wf transforms the fold state
--                │                  (vals,evs,fin,sched,st) WITHOUT
--                │                  stepping the protocol, then the IH
--                │                  continues down path′ — the direct
--                │                  analog of subscribeE-wf's per-clause
--                │                  induction (map/scan/take/*All)
--                └─ share-sink i : one handoff emit, then dispatchShare-wf
--                                   (MUTUALLY RECURSIVE with foldPath-wf,
--                                   gas-structural) fans out to share i's
--                                   registrations — the handoff's owed
--                                   bump is repaid one-per-fan-out, so the
--                                   share subtree nets owed back to zero
--                                   (the diamond, batched by construction)
--
-- The missing piece is FoldInv — the mid-fold relation foldPath-wf is
-- stated over (BurstInv's delivery-side analog): unlike BurstInv's
-- literally-empty owed table, FoldInv carries the PARTIALLY-PAID open
-- instant (owed[envSrc] = the chain's own unpaid delivery; each pending
-- share bumped-then-being-repaid across its dispatch).  Once FoldInv is
-- pinned, mid-step is the chainStep seed (owed[arrSource] = the snapshot
-- remainder) plus reading Mid back off the FoldInv result.  Kept as ONE
-- postulate until FoldInv lands, so no half-stated (possibly-false) leaf
-- enters the development early — the whole point of the outside-in rule.
--
-- WHERE TO SPLIT (verified empirically, 2026-07): the Path-constructor
-- case split MUST live at foldPath-wf, which — like foldPath itself —
-- quantifies the chain's SOURCE type `u` FREELY (path : Path Γ u t).
-- It CANNOT live at mid-step, where the source type is pinned to the
-- stuck projection `arrTy a`: matching `share-sink i : Path Γ (lookup Γ i) t`
-- there demands `lookup Γ i ≡ arrTy a`, which Agda's unifier rejects
-- (two neutrals), so `mid-step {p = share-sink i} = …` will not even
-- typecheck (root and `f ↠ path′` do — only share-sink clashes).  With a
-- free `u`, matching share-sink cleanly sets `u := lookup Γ i`.  So:
-- mid-step invokes foldPath-wf at `u := arrTy a` with the seed; the
-- three-way induction (root / frame / share) is foldPath-wf's own.
postulate
  mid-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    {a : Arrival Γ} {nextId : Id} {rid : RegId}
    {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
    {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = chainStep nextId a p sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      in (runProtocol S (proj₁ r) ≡ just S′)
         × Mid a nextId ps (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

-- a cancelled head contributes nothing to countRemaining (the `if`
-- takes the then-branch)
cr-skip : ∀ {X : Set} (rid : RegId) (x : X)
          (ps : List (RegId × X)) (c : List RegId) →
          any (_≡ᵇ rid) c ≡ true →
          countRemaining ((rid , x) ∷ ps) c ≡ countRemaining ps c
cr-skip rid x ps c h rewrite h = refl

-- and nothing to cascadeGo: its first clause skips a cancelled head
-- outright, folding the tail with the SAME state (two-column trick —
-- cascadeGo's `with` won't unfold under rewrite)
cascadeGo-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id) (rid : RegId)
  (p : Path Γ (arrTy a) t) (ps : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  cascadeGo {e = e} a nextId ((rid , p) ∷ ps) sched st
    ≡ cascadeGo {e = e} a nextId ps sched st
cascadeGo-skip a nextId rid p ps sched st ceq
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | ceq
... | true | refl = refl

-- a cancelled chain folds to nothing (its close already rode the
-- cutting emit; its owed was forgiven right there): every Mid field is
-- stable when the snapshot head drops, given the head is cancelled
mid-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id} {rid : RegId}
  {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  Mid a nextId ps sched st S
mid-skip {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq = record
  { live-others  = Mid.live-others mid
  ; live-source  = trans (Mid.live-source mid)
      (cong (λ z → if Arrival.isLast a then z
                   else countRegs (arrSource a) (EvalSt.registry st))
            (cr-skip rid p ps (EvalSt.cancelled st) ceq))
  ; reg-typed    = Mid.reg-typed mid       -- same sched, st
  ; horizon-low  = Mid.horizon-low mid
  ; ledger       = ledger′
  ; done-plumbed = Mid.done-plumbed mid
  ; fold-live    = subst (λ z → hasDry (proj₁ z) ≡ false)
      (cascadeGo-skip a nextId rid p ps sched st ceq)
      (Mid.fold-live mid)
  ; owed-unique  = Mid.owed-unique mid      -- same S, nextId
  }
  where
  ledger′ :
      (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
    ⊎ (Σ Owed λ ow →
         (ProtocolSt.current S ≡ just (nextId , ow))
       × (lookupOwed (arrSource a) ow
            ≡ countRemaining ps (EvalSt.cancelled st))
       × (zeroExcept (arrSource a) ow ≡ true))
  ledger′ with Mid.ledger mid
  ... | inj₁ x                    = inj₁ x
  ... | inj₂ (ow , cur , lk , zx) =
        inj₂ (ow , cur
             , trans lk (cr-skip rid p ps (EvalSt.cancelled st) ceq)
             , zx)

------------------------------------------------------------------
-- mid-final: leaving the cascade.  Bool/ℕ glue first, then registry
-- lemmas for the finish sweep, then the assembly.
------------------------------------------------------------------

-- a key absent from the table reads zero
lookupOwed-absent : ∀ (s : Source) (o : Owed) →
  notKeyOwed s o ≡ true → lookupOwed s o ≡ 0
lookupOwed-absent s []            _ = refl
lookupOwed-absent s ((x , n) ∷ o) h with s ≡ᵇ x | h
... | false | h′ = lookupOwed-absent s o h′
... | true  | h′ = true≢false (sym h′)

-- with unique keys, zeroExcept + a zero at s forces the whole table
-- zero.  `with s ≡ᵇ x in seq` rewrites ze/lk in each branch: at the key
-- (true) lk reads n ≡ 0 and ze drops to the tail; off-key (false) ze's
-- head gives n ≡ᵇ 0 and lk passes to the tail
allZero-clean : ∀ (s : Source) (o : Owed) →
  UniqueOwed o ≡ true → zeroExcept s o ≡ true → lookupOwed s o ≡ 0 →
  allZero o ≡ true
allZero-clean s []            _  _  _  = refl
allZero-clean s ((x , n) ∷ o) uq ze lk with s ≡ᵇ x in seq
... | true  =
      subst (λ m → allZero ((x , m) ∷ o) ≡ true) (sym lk)
        (allZero-clean s o (∧-trueʳ uq) ze
          (lookupOwed-absent s o
            (subst (λ z → notKeyOwed z o ≡ true)
                   (sym (≡ᵇ→≡ s x seq)) (∧-trueˡ uq))))
... | false =
      subst (λ m → allZero ((x , m) ∷ o) ≡ true)
            (sym (≡ᵇ→≡ n 0 (∧-trueˡ ze)))
        (allZero-clean s o (∧-trueʳ uq) (∧-trueʳ ze) lk)

-- an all-zero owed table settles: paidUp holds
paid-allzero : (S : ProtocolSt) {j : Id} {ow : Owed} →
  ProtocolSt.current S ≡ just (j , ow) → allZero ow ≡ true → paidUp S ≡ true
paid-allzero S ceq az with ProtocolSt.current S | ceq
... | just (j , ow) | refl rewrite az = refl

-- CurrentPast only weakens as the bound grows
currentPast-up : (c : Maybe (Id × Owed)) (N : Id) →
  CurrentPast c N → CurrentPast c (suc N)
currentPast-up nothing        N cp = tt
currentPast-up (just (j , _)) N cp = ≤-up cp

-- registry sweep: dropping s zeroes s's own count and leaves others'
dropSource-self : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  countRegs s (dropSource s reg) ≡ 0
dropSource-self s []                  = refl
dropSource-self s ((rid , x , c) ∷ r) with s ≡ᵇ x in eq
... | true             = dropSource-self s r
... | false rewrite eq = dropSource-self s r

dropSource-other : ∀ {n} {Γ : Ctx n} {t}
  (s s′ : Source) (reg : List (RegId × Source × Chain Γ t)) →
  (s ≡ᵇ s′) ≡ false →
  countRegs s (dropSource s′ reg) ≡ countRegs s reg
dropSource-other s s′ []                  neq = refl
dropSource-other s s′ ((rid , x , c) ∷ r) neq with s ≡ᵇ x in sx | s′ ≡ᵇ x in s′x
... | true  | true  =
      let s≡s′ = trans (≡ᵇ→≡ s x sx) (sym (≡ᵇ→≡ s′ x s′x))
          p    = trans (sym (cong (s ≡ᵇ_) s≡s′)) (≡ᵇ-refl s)
      in true≢false (trans (sym p) neq)
... | true  | false rewrite sx = cong suc (dropSource-other s s′ r neq)
... | false | true             = dropSource-other s s′ r neq
... | false | false rewrite sx = dropSource-other s s′ r neq

-- dropping preserves "every registration is share-sunk"
allShareSunk-drop : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  allShareSunk reg ≡ true → allShareSunk (dropSource s reg) ≡ true
allShareSunk-drop s []                        h = refl
allShareSunk-drop s ((rid , x , (u , p)) ∷ r) h with s ≡ᵇ x
... | true  = allShareSunk-drop s r (∧-trueʳ h)
... | false = ∧-intro (∧-trueˡ h) (allShareSunk-drop s r (∧-trueʳ h))

-- cascadeFinish reduced under each isLast branch (two-column trick: the
-- `with Arrival.isLast a` won't unfold under rewrite).  isLast=false
-- leaves the state; isLast=true sweeps the spent source's registry
cascadeFinish-false : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ false → cascadeFinish a sched st ≡ (sched , st)
cascadeFinish-false a sched st eq with Arrival.isLast a | eq
... | false | refl = refl

finishReg-true : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ true →
  EvalSt.registry (proj₂ (cascadeFinish a sched st))
    ≡ dropSource (arrSource a) (EvalSt.registry st)
finishReg-true a sched st eq with Arrival.isLast a | eq
... | true | refl = refl

finishSched-true : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ true →
  Sched.live (proj₁ (cascadeFinish a sched st))
    ≡ sweepLive (dropSource (arrSource a) (EvalSt.registry st)) (Sched.live sched)
finishSched-true a sched st eq with Arrival.isLast a | eq
... | true | refl = refl

-- leaving: all chains folded ⇒ fully paid; finish (drop the spent
-- source, sweep) lands Inv-related at suc nextId
mid-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId [] sched st S →
  Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                   (proj₂ (cascadeFinish a sched st)) S
  × (paidUp S ≡ true)
mid-final {a = a} {nextId} {sched} {st} {S} mid = inv , paidUp-S
  where
  paidUp-S : paidUp S ≡ true
  paidUp-S with Mid.ledger mid
  ... | inj₁ (_ , pd)             = pd
  ... | inj₂ (ow , cur , lk , zx) =
        paid-allzero S cur
          (allZero-clean (arrSource a) ow (Mid.owed-unique mid ow cur) zx lk)

  cpast : CurrentPast (ProtocolSt.current S) (suc nextId)
  cpast with Mid.ledger mid
  ... | inj₁ (cp , _)        = currentPast-up (ProtocolSt.current S) nextId cp
  ... | inj₂ (ow , cur , _ , _) =
        subst (λ c → CurrentPast c (suc nextId)) (sym cur) ≤-refl

  -- the arrival source's live count, read off Mid.live-source per isLast
  live-src-nl : Arrival.isLast a ≡ false →
    countIn (arrSource a) (ProtocolSt.live S)
      ≡ countRegs (arrSource a) (EvalSt.registry st)
  live-src-nl isL = trans (Mid.live-source mid) (if-false (Arrival.isLast a) isL)

  live-src-tl : Arrival.isLast a ≡ true →
    countIn (arrSource a) (ProtocolSt.live S) ≡ 0
  live-src-tl isL = trans (Mid.live-source mid) (if-true (Arrival.isLast a) isL)

  lm-false : Arrival.isLast a ≡ false → ∀ (s : Source) →
    countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
  lm-false isL s with sameSource s (arrSource a) in seq
  ... | false = Mid.live-others mid s seq
  ... | true  =
        subst (λ z → countIn z (ProtocolSt.live S)
                       ≡ countRegs z (EvalSt.registry st))
              (sym (≡ᵇ→≡ s (arrSource a) seq)) (live-src-nl isL)

  lm-true : Arrival.isLast a ≡ true → ∀ (s : Source) →
    countIn s (ProtocolSt.live S)
      ≡ countRegs s (dropSource (arrSource a) (EvalSt.registry st))
  lm-true isL s with sameSource s (arrSource a) in seq
  ... | false = trans (Mid.live-others mid s seq)
                  (sym (dropSource-other s (arrSource a) (EvalSt.registry st) seq))
  ... | true  =
        let s≡ = ≡ᵇ→≡ s (arrSource a) seq in
        trans (subst (λ z → countIn z (ProtocolSt.live S) ≡ 0) (sym s≡)
                 (live-src-tl isL))
              (sym (subst (λ z → countRegs z (dropSource (arrSource a)
                                   (EvalSt.registry st)) ≡ 0) (sym s≡)
                     (dropSource-self (arrSource a) (EvalSt.registry st))))

  inv : Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                         (proj₂ (cascadeFinish a sched st)) S
  inv = go (Arrival.isLast a) refl
    where
    go : (b : Bool) → Arrival.isLast a ≡ b →
         Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                          (proj₂ (cascadeFinish a sched st)) S
    -- isLast=false: cascadeFinish is the identity; rewrite the goal flat
    go false isL rewrite cascadeFinish-false a sched st isL = record
      { live-matches = lm-false isL
      ; reg-typed    = Mid.reg-typed mid
      ; horizon-low  = ≤-up (Mid.horizon-low mid)
      ; current-past = cpast
      ; done-plumbed = Mid.done-plumbed mid
      }
    -- isLast=true: keep cascadeFinish symbolic; convert registry and live
    -- field-by-field, reg-typed via the dropSource/sweepLive preservation
    go true isL = record
      { live-matches = λ s →
          subst (λ reg → countIn s (ProtocolSt.live S) ≡ countRegs s reg)
                (sym (finishReg-true a sched st isL)) (lm-true isL s)
      ; reg-typed    =
          subst (λ reg → regTyped? reg (Sched.live (proj₁ (cascadeFinish a sched st))) ≡ true)
                (sym (finishReg-true a sched st isL))
                (subst (λ lv → regTyped? (dropSource (arrSource a) (EvalSt.registry st)) lv ≡ true)
                       (sym (finishSched-true a sched st isL))
                       (reg-typed-finish (arrSource a) (EvalSt.registry st)
                          (Sched.live sched) (Mid.reg-typed mid)))
      ; horizon-low  = ≤-up (Mid.horizon-low mid)
      ; current-past = cpast
      ; done-plumbed = λ deq →
          subst (λ reg → allShareSunk reg ≡ true)
                (sym (finishReg-true a sched st isL))
                (allShareSunk-drop (arrSource a) (EvalSt.registry st)
                  (Mid.done-plumbed mid deq))
      }

-- the chain fold, composed (mirrors cascadeGo's own recursion —
-- structural on the snapshot, no termination debt at this level)
cascadeGo-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  Mid a nextId chains sched st S →
  Σ ProtocolSt λ S′ →
    let r = cascadeGo {e = e} a nextId chains sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Mid a nextId [] (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
cascadeGo-wf a nextId [] sched st S mid = S , refl , mid
cascadeGo-wf a nextId ((rid , p) ∷ ps) sched st S mid
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in ceq
... | true  = cascadeGo-wf a nextId ps sched st S (mid-skip mid ceq)
... | false
  with mid-step {ps = ps} mid ceq
... | S₁ , run₁ , mid₁
  with cascadeGo-wf a nextId ps
         (proj₁ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         (proj₂ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         S₁ mid₁
... | S₂ , run₂ , mid₂ =
  S₂
  , run-++-just S
      (proj₁ (chainStep nextId a p sched
               (record st { delivered = rid ∷ EvalSt.delivered st })))
      _ run₁ run₂
  , mid₂

-- the latch leaves the registry untouched (it only resets the per-cascade
-- ledger and stamps the watermark / dying set)
latch-registry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  EvalSt.registry (cascadeLatch a st) ≡ EvalSt.registry st
latch-registry a st with Arrival.isLast a
... | true  = refl
... | false = refl

-- an all-fresh snapshot (no cancellations yet) has every entry obliged
countRemaining-[] : ∀ {X : Set} (ps : List (RegId × X)) →
  countRemaining ps [] ≡ length ps
countRemaining-[] []             = refl
countRemaining-[] ((rid , _) ∷ ps) = cong suc (countRemaining-[] ps)

-- entering: the latch opens the ledger; the automaton, Inv-related and
-- paid, stands ready to open instant nextId (still on the previous,
-- settled instant, so the ledger is the paid branch).  reg-typed threads
-- from Inv across the scheduler pop; the count fact live-source needs is
-- read off chains-count-derived
mid-init : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
  (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascadeGo a nextId (chainsOf a st) sched′
                           (cascadeLatch a st))) ≡ false →
  Mid a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
mid-init nextId sched a sched′ st S eq inv paid nodry = record
  { live-others  = λ s _ → trans (Inv.live-matches inv s)
                     (cong (countRegs s) (sym (latch-registry a st)))
  ; live-source  = live-src
  ; reg-typed    = subst (λ reg → regTyped? reg (Sched.live sched′) ≡ true)
                     (sym (latch-registry a st))
                     (regTyped?-pop-sched sched sched′ (EvalSt.registry st) eq
                       (Inv.reg-typed inv))
  ; horizon-low  = Inv.horizon-low inv
  ; ledger       = inj₁ (Inv.current-past inv , paid)
  ; done-plumbed = λ deq → subst (λ reg → allShareSunk reg ≡ true)
                     (sym (latch-registry a st)) (Inv.done-plumbed inv deq)
  ; fold-live    = nodry
  ; owed-unique  = λ ow cur → ⊥-elim (1+n≰n
                     (subst (λ c → CurrentPast c nextId) cur (Inv.current-past inv)))
  }
  where
  live-src : countIn (arrSource a) (ProtocolSt.live S)
    ≡ (if Arrival.isLast a
       then countRemaining (chainsOf a st) (EvalSt.cancelled (cascadeLatch a st))
       else countRegs (arrSource a) (EvalSt.registry (cascadeLatch a st)))
  live-src with Arrival.isLast a
  ... | true  = trans (Inv.live-matches inv (arrSource a))
                  (trans (chains-count-derived a sched sched′ st (Inv.reg-typed inv) eq)
                         (sym (countRemaining-[] (chainsOf a st))))
  ... | false = Inv.live-matches inv (arrSource a)

-- one arrival's cascade, composed.  The dry-freeness premise is
-- stated on the cascade's own emits — definitionally the cascadeGo
-- fold's emits, which is the shape mid-init wants
cascade-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascade a nextId sched′ st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = cascade a nextId sched′ st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Inv (suc nextId) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (paidUp S′ ≡ true)
cascade-wf nextId sched a sched′ st S eq inv paid nodry
  with cascadeGo-wf a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
         (mid-init nextId sched a sched′ st S eq inv paid nodry)
... | S′ , run , mid
  with mid-final mid
... | inv′ , paid′ = S′ , run , inv′ , paid′

------------------------------------------------------------------
-- the composition: fuel induction over drain, then the theorem
------------------------------------------------------------------

drain-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
    (S : ProtocolSt) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (drain {e = e} fuel nextId sched st) ≡ false →
  Σ ProtocolSt λ S′ →
    (runProtocol S (drain {e = e} fuel nextId sched st) ≡ just S′)
    × (paidUp S′ ≡ true)
drain-wf zero    nextId sched st S inv paid _  = S , refl , paid
drain-wf (suc k) nextId sched st S inv paid hd with sched-next sched in eq
... | inj₁ _            = S , refl , paid
... | inj₂ (a , sched′)
  -- the with-abstraction has already rewritten hd's type to the
  -- unfolded `cascade emits ++ drain k …` shape — split it there
  with hasDry-++ (proj₁ (cascade a nextId sched′ st))
         (drain k (suc nextId)
           (proj₁ (proj₂ (cascade a nextId sched′ st)))
           (proj₂ (proj₂ (cascade a nextId sched′ st))))
         hd
... | nodry₁ , nodry₂
  with cascade-wf nextId sched a sched′ st S eq inv paid nodry₁
... | S₁ , run₁ , inv₁ , paid₁
  with drain-wf k (suc nextId)
         (proj₁ (proj₂ (cascade a nextId sched′ st)))
         (proj₂ (proj₂ (cascade a nextId sched′ st)))
         S₁ inv₁ paid₁ nodry₂
... | S₂ , run₂ , paid₂ =
  S₂
  , run-++-just S (proj₁ (cascade a nextId sched′ st)) _ run₁ run₂
  , paid₂

-- the reified termination debt: the seeded sync budget never runs
-- dry on a canonical run.  This is the old TERMINATING pragma's
-- claim, now a provable statement — the evaluator is total either
-- way, and QuickCheck's WellFormed check falsifies this postulate at
-- runtime the moment any program exhausts its budget
postulate
  budget-sufficient :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (evaluate fuel e ins) ≡ false

-- the primitives' half of the sandwich: remaining debt is the frame
-- relations, their step lemmas, and budget sufficiency above
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins
  with hasDry-++
         (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e)))
         (drain fuel 1
           (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e))))
           (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e)))))
         (budget-sufficient fuel e ins)
... | nodry₀ , nodry₁
  with subscribe-wf e ins nodry₀
... | S₀ , run₀ , inv₀ , paid₀
  with drain-wf fuel 1
         (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         S₀ inv₀ paid₀ nodry₁
... | S₁ , run₁ , paid₁
  rewrite run-++-just protocol-init
            (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                               (sched-init e ins) (st-init e)))
            (drain fuel 1
              (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e))))
              (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e)))))
            run₀ run₁
  = acceptPaid S₁ paid₁
