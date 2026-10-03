------------------------------------------------------------------
-- THE SIMULATION: the elaborated run, decoded, is the plain run with
-- each value stamped by the arrival that caused it.
--
-- TWO CONJUNCTS, ONE PER THING A STAMPED VALUE CARRIES.  Its value
-- agrees with the plain run's value at the same position, and its
-- stamp is a NAME for that value's arrival: one name per arrival, no
-- two arrivals sharing one.
--
-- AN ARRIVAL IS A DRAIN STEP, AND THE PLAIN RUN SAYS WHICH ONE A VALUE
-- CAME FROM ONLY THROUGH ITS FUEL.  Fuel counts drain steps, so the
-- values the plain run has delivered at fuel k and not at k - 1 are
-- the k-th arrival's, and fuel 0 is the subscription's.  A burst is not
-- the unit: one arrival reaching the root twice is two bursts and one
-- instant.  The counts never fall, since each fuel's run extends the
-- last (`run-prefix`), so a run is its arrivals' slices joined.
--
-- VALUES AGREE AT DATA AND ARE NOT COMPARED AT `obs`.  The two runs
-- stand in different contexts -- the elaboration's reads a share at
-- the InstEmit -- and an observable value is a closure over its own.
-- What an observable does is compared where it is run, as its emits.
--
-- THE IMPL'S SHARED-SLOT FALLBACK IS OWED BY `correspondence`.
-- `embedSlotsImpl` checks stratification of the elaborated definition
-- and falls back to `empty` if it fails; the table only certifies the
-- plain one, so the values are where "the check never fails" is paid.
------------------------------------------------------------------
module Simulation.Statement where

open import Data.Bool    using (Bool; true; false; T)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.List    using (List; []; _∷_; _++_; map; length; replicate; drop; concat)
open import Data.List.Properties using (map-++; map-replicate; length-drop)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties using (fromPointwise)
  renaming (trans to prefix-trans)
open import Data.List.Relation.Binary.Pointwise.Properties using (Pointwise-length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺)
  renaming (refl to pointwise-refl)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; _≤ᵇ_; _≤′_; ≤′-reflexive; ≤′-step)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; ≤⇒≤′; ≤⇒≤ᵇ; ≤ᵇ⇒≤; <-≤-trans; <-irrefl; <-cmp; m≤m+n; +-cancelˡ-≡)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Rx.Prim      using (Fuel; Id; PlainEvent; valueᵖ; completeᵖ; InstEmit)
open import Rx.Exp       using (Ctx; Val; isData; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs)
open import SExp.Syntax  using (SExp; Kinds; plainᵏ; plainᵗ)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import SExp.Plain   using (unplainᵈ; ∧ˡ; ∧ʳ; plainExp; plainValues)
open import SExp.Pipeline using (runᴵ; runᴾ; elaborateImpl; embedSlotsImpl)
open import Batchable.Inst-Extract using (instExtract; emitValues)
open import Simulation.Prefix using (prefix-++; run-prefix)
open import Simulation.Lockstep using (Conf; start; opening; out; next; iter; run-opening; run-snoc;
  concat-++; values-++; decode-++; extract-++)
open import Rx.Evaluator using (Stream)
open import Rx.Evaluator.Builder using (evaluate↓)

module _ {n m} (Γ′ : Ctx m) (Γ : Ctx n) where

  -- a value of the elaborated run against one of the plain run
  Agrees : ∀ t → Val Γ′ (plainᵗ t) → Val Γ t → Set
  Agrees unitᵗ     v        w        = v ≡ w
  Agrees boolᵗ     v        w        = v ≡ w
  Agrees natᵗ      v        w        = v ≡ w
  Agrees uniqᵗ     v        w        = v ≡ w
  Agrees (s ×ᵗ t)  (a , b)  (c , d)  = Agrees s a c × Agrees t b d
  Agrees (s +ᵗ t)  (inj₁ a) (inj₁ c) = Agrees s a c
  Agrees (s +ᵗ t)  (inj₂ b) (inj₂ d) = Agrees t b d
  Agrees (s +ᵗ t)  (inj₁ _) (inj₂ _) = ⊥
  Agrees (s +ᵗ t)  (inj₂ _) (inj₁ _) = ⊥
  Agrees (listᵗ t) vs       ws       = Pointwise (Agrees t) vs ws
  Agrees (obs t)   _        _        = ⊤

  -- at data, agreeing is being the same value
  agrees-unplain : ∀ t (ok : T (isData t)) {v w} → Agrees t v w
                 → unplainᵈ {Γ = Γ} {Γ′ = Γ′} t ok v ≡ w
  agrees-unplain unitᵗ     ok a = a
  agrees-unplain boolᵗ     ok a = a
  agrees-unplain natᵗ      ok a = a
  agrees-unplain uniqᵗ     ok a = a
  agrees-unplain (s ×ᵗ t)  ok (p , q) =
    cong₂ _,_ (agrees-unplain s (∧ˡ (isData s) ok) p) (agrees-unplain t (∧ʳ (isData s) ok) q)
  agrees-unplain (s +ᵗ t)  ok {inj₁ _} {inj₁ _} a = cong inj₁ (agrees-unplain s (∧ˡ (isData s) ok) a)
  agrees-unplain (s +ᵗ t)  ok {inj₂ _} {inj₂ _} a = cong inj₂ (agrees-unplain t (∧ʳ (isData s) ok) a)
  agrees-unplain (s +ᵗ t)  ok {inj₁ _} {inj₂ _} ()
  agrees-unplain (s +ᵗ t)  ok {inj₂ _} {inj₁ _} ()
  agrees-unplain (listᵗ t) ok a = go a
    where
      go : ∀ {vs ws} → Pointwise (Agrees t) vs ws → map (unplainᵈ {Γ = Γ} {Γ′ = Γ′} t ok) vs ≡ ws
      go []       = refl
      go (p ∷ ps) = cong₂ _∷_ (agrees-unplain t ok p) (go ps)

  -- a run's stamped values against the plain run's, read at data
  agrees-values : ∀ t (ok : T (isData t)) {xs : List (Id × Val Γ′ (plainᵗ t))} {ws}
                → Pointwise (λ p w → Agrees t (proj₂ p) w) xs ws
                → map (unplainᵈ {Γ = Γ} {Γ′ = Γ′} t ok) (map proj₂ xs) ≡ ws
  agrees-values t ok []       = refl
  agrees-values t ok (p ∷ ps) = cong₂ _∷_ (agrees-unplain t ok p) (agrees-values t ok ps)

-- each plain value's ARRIVAL, given how many values the run has
-- delivered at each fuel: 0 for the subscription, k for the k-th drain
-- step
arrivalsᴾ : (ℕ → ℕ) → ℕ → List ℕ
arrivalsᴾ c zero    = replicate (c zero) zero
arrivalsᴾ c (suc k) = arrivalsᴾ c k ++ replicate (c (suc k) ∸ c k) (suc k)

-- the plain run's arrivals at a fuel
arrivalsOf : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ → List ℕ
arrivalsOf {κ = κ} fuel e ins = arrivalsᴾ (λ k → length (runᴾ {κ = κ} k e ins)) fuel

-- THE IMPL RUNS AT ITS OWN FUEL, NEVER LESS THAN THE PLAIN RUN'S
-- (Anthony).
Simulation : Set
Simulation =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ Fuel λ fuelᴵ → fuel ≤ fuelᴵ ×
  Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
            (instExtract (runᴵ κ fuelᴵ e ins)) (runᴾ fuel e ins) ×
  Σ (ℕ → Id) λ name → (∀ {a b} → name a ≡ name b → a ≡ b) ×
    map proj₁ (instExtract (runᴵ κ fuelᴵ e ins)) ≡ map name (arrivalsOf fuel e ins)

-- THE k-TH ARRIVAL'S SLICE of a run read at successive fuels: the
-- subscription's at 0, and what one more unit of fuel added after it
sliceAt : ∀ {A : Set} → (ℕ → List A) → ℕ → List A
sliceAt r zero    = r zero
sliceAt r (suc k) = drop (length (r k)) (r (suc k))

-- the two runs, at every fuel
stampedAt : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) → SExp Γ [] [] [] t → SimulSlots Γ κ
          → ℕ → List (Id × Val (plainᵏ Γ κ) (plainᵗ t))
stampedAt κ e ins k = instExtract (runᴵ κ k e ins)

plainAt : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) → SExp Γ [] [] [] t → SimulSlots Γ κ
        → ℕ → List (Val Γ t)
plainAt κ e ins k = runᴾ {κ = κ} k e ins

-- EACH PLAIN ARRIVAL IS ONE IMPL ARRIVAL: the plain run's k-th slice
-- agrees with the impl run's k-th, and every value of it carries one
-- instant, `name k`, no two arrivals sharing one.
Arrival-Runs : Set
Arrival-Runs =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ (ℕ → Id) λ name → (∀ {a b} → name a ≡ name b → a ≡ b) ×
    (∀ k → k ≤ fuel →
      Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
                (sliceAt (stampedAt κ e ins) k) (sliceAt (plainAt κ e ins) k) ×
      All (λ p → proj₁ p ≡ name k) (sliceAt (stampedAt κ e ins) k))

-- what a run's arrival is read as, plain and stamped
readᴾ : ∀ {n} {Γ : Ctx n} {t} → Stream Γ t → List (Val Γ t)
readᴾ s = plainValues (concat s)

readᴵ : ∀ {m} {Γ′ : Ctx m} {t} → Stream Γ′ (instEmitᵗ uniqᵗ t) → List (Id × Val Γ′ t)
readᴵ s = instExtract (decodeEmits (concat s))

-- ONE INSTANT TO AN ARRIVAL'S VALUES, minted between `lo` and `hi`
OneIn : ∀ {A : Set} → ℕ → ℕ → List (Id × A) → Set
OneIn lo hi []             = ⊤
OneIn lo hi ((i , _) ∷ xs) = lo ≤ i × i < hi × All (λ p → proj₁ p ≡ i) xs

-- A RELATION BETWEEN THE TWO MACHINES' CONFIGURATIONS THAT ONE ARRIVAL
-- EACH PRESERVES, and under which the two arrivals send agreeing
-- values: the plain run's from its configuration, the impl's from its,
-- the impl's stamped by one instant its clock passes.  The root
-- subscribes start in it.
record Correspondence {n} {Γ : Ctx n} {t} (κ : Kinds n) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) : Set₁ where
  field
    Corr  : Conf (plainExp e) → Conf (elaborateImpl κ e) → Set
    clock : Conf (elaborateImpl κ e) → ℕ
    open-corr   : Corr (start (plainExp e) (plainSlots ins)) (start (elaborateImpl κ e) (embedSlotsImpl ins))
    open-agree  : Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
                            (readᴵ (opening (elaborateImpl κ e) (embedSlotsImpl ins)))
                            (readᴾ (opening (plainExp e) (plainSlots ins)))
    open-stamps : OneIn 0 (clock (start (elaborateImpl κ e) (embedSlotsImpl ins)))
                          (readᴵ (opening (elaborateImpl κ e) (embedSlotsImpl ins)))
    step-corr   : ∀ {c d} → Corr c d → Corr (next c) (next d)
    step-agree  : ∀ {c d} → Corr c d → Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
                                                 (readᴵ (out d)) (readᴾ (out c))
    step-clock  : ∀ {c d} → Corr c d → clock d ≤ clock (next d)
    step-stamps : ∀ {c d} → Corr c d → OneIn (clock d) (clock (next d)) (readᴵ (out d))

postulate
  -- WHERE IT CAN STILL FAIL: AN IMPL ARRIVAL THE PLAIN SCHEDULE DOES NOT
  -- HAVE, or one plain arrival's values delivered across two.  Either is
  -- a former whose elaboration schedules something its plain program
  -- does not, or answers an arrival a hop late.
  --
  -- THE TWO SCHEDULES ARE ONE WHERE THE COMPILED CHECKS REACH.  On every
  -- row of the bug cache, untimed and timed, the impl's arrival keys --
  -- tick and ranked source -- are the plain run's in order, as far as
  -- both were read, and each impl slice holds as many values as its
  -- plain slice.  Among them are the rows built to split an arrival: a
  -- value and its END under a `take` of a cold, exhausted or merged, and
  -- every way the cache subscribes a `take` late.  The compiled sweep at
  -- depth 3, fuel one, matched each plain arrival's key to the next impl
  -- arrival's with none unmatched between: seed 20, 300 cases, 299
  -- agreeing and one undecided at its clock; seed 19, 60, all agreeing.
  --
  -- PROBED: `Probed.Simulation`, read back by
  --   `git show SHA:agda/evidence/probed/Probed/Simulation.agda`.
  --   Its rows pin `arrival-runs`'s conclusion -- every slice through fuel
  --   3 over three first-order programs and the timed translations of two,
  --   all over a hot slot with the map the identity, the empty slices
  --   included, each slice's instant its arrival plus a shift -- so they
  --   reach this leaf only along the run from the root subscribes.
  correspondence : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
                 → Correspondence κ e ins

readᴾ-++ : ∀ {n} {Γ : Ctx n} {t} (xs ys : Stream Γ t) → readᴾ (xs ++ ys) ≡ readᴾ xs ++ readᴾ ys
readᴾ-++ xs ys = trans (cong plainValues (concat-++ xs ys)) (values-++ (concat xs) (concat ys))

readᴵ-++ : ∀ {m} {Γ′ : Ctx m} {t} (xs ys : Stream Γ′ (instEmitᵗ uniqᵗ t)) → readᴵ (xs ++ ys) ≡ readᴵ xs ++ readᴵ ys
readᴵ-++ xs ys =
  trans (cong (λ z → instExtract (decodeEmits z)) (concat-++ xs ys))
 (trans (cong instExtract (decode-++ (concat xs) (concat ys)))
        (extract-++ (decodeEmits (concat xs)) (decodeEmits (concat ys))))

drop-front : ∀ {A : Set} (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
drop-front []       ys = refl
drop-front (x ∷ xs) ys = drop-front xs ys

-- an arrival's name: its slice's instant while the slice holds a value
-- and the fuel reaches it, a default otherwise
pick : ∀ {A : Set} → Bool → List (Id × A) → Id → Id
pick false _             d = d
pick true  []            d = d
pick true  ((i , _) ∷ _) d = i

pick-all : ∀ {A : Set} b {lo hi} (xs : List (Id × A)) d → b ≡ true → OneIn lo hi xs
         → All (λ p → proj₁ p ≡ pick b xs d) xs
pick-all .true []             d refl _            = []
pick-all .true ((i , _) ∷ xs) d refl (_ , _ , is) = refl ∷ is

pick-cases : ∀ {A : Set} b {lo hi} (xs : List (Id × A)) d → OneIn lo hi xs
           → (T b × lo ≤ pick b xs d × pick b xs d < hi) ⊎ pick b xs d ≡ d
pick-cases false xs             d _            = inj₂ refl
pick-cases true  []             d _            = inj₂ refl
pick-cases true  ((i , _) ∷ xs) d (l , h , _) = inj₁ (tt , l , h)

true-of : ∀ {b} → T b → b ≡ true
true-of {true} _ = refl

-- EACH PLAIN ARRIVAL IS ONE IMPL ARRIVAL, BY INDUCTION ON THE ARRIVALS.
-- The correspondence holds `k` arrivals in, so the `k`-th arrivals send
-- agreeing values; the clock never runs back, so an arrival's instant
-- is past every earlier one's and short of every later one's.  Past
-- the fuel, or at an arrival that sends nothing, the name is the
-- clock's reading at the fuel plus the arrival, which no instant
-- through the fuel reaches.
arrival-runs : Arrival-Runs
arrival-runs {Γ = Γ} {t = t} κ fuel e ins = name , name-inj , λ k le → slice k , one k le
  where
    open Correspondence (correspondence κ e ins)
    eᴾ = plainExp e
    sᴾ = plainSlots ins
    eᴵ = elaborateImpl κ e
    sᴵ = embedSlotsImpl ins
    R = λ (p : Id × Val (plainᵏ Γ κ) (plainᵗ t)) (w : Val Γ t) → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w

    cᴾ : ℕ → Conf eᴾ
    cᴾ k = iter k (start eᴾ sᴾ)
    cᴵ : ℕ → Conf eᴵ
    cᴵ k = iter k (start eᴵ sᴵ)

    corr : ∀ k → Corr (cᴾ k) (cᴵ k)
    corr zero    = open-corr
    corr (suc k) = step-corr (corr k)

    sentᴾ : ℕ → List (Val Γ t)
    sentᴾ zero    = readᴾ (opening eᴾ sᴾ)
    sentᴾ (suc k) = readᴾ (out (cᴾ k))
    sentᴵ : ℕ → List (Id × Val (plainᵏ Γ κ) (plainᵗ t))
    sentᴵ zero    = readᴵ (opening eᴵ sᴵ)
    sentᴵ (suc k) = readᴵ (out (cᴵ k))

    sliceᴾ : ∀ k → sliceAt (plainAt κ e ins) k ≡ sentᴾ k
    sliceᴾ zero    = cong readᴾ (run-opening eᴾ sᴾ)
    sliceᴾ (suc k) =
      trans (cong (λ s → drop (length (plainAt κ e ins k)) (readᴾ s)) (run-snoc k eᴾ sᴾ))
     (trans (cong (drop (length (plainAt κ e ins k))) (readᴾ-++ (evaluate↓ k eᴾ sᴾ) (out (cᴾ k))))
            (drop-front (plainAt κ e ins k) (sentᴾ (suc k))))
    sliceᴵ : ∀ k → sliceAt (stampedAt κ e ins) k ≡ sentᴵ k
    sliceᴵ zero    = cong readᴵ (run-opening eᴵ sᴵ)
    sliceᴵ (suc k) =
      trans (cong (λ s → drop (length (stampedAt κ e ins k)) (readᴵ s)) (run-snoc k eᴵ sᴵ))
     (trans (cong (drop (length (stampedAt κ e ins k))) (readᴵ-++ (evaluate↓ k eᴵ sᴵ) (out (cᴵ k))))
            (drop-front (stampedAt κ e ins k) (sentᴵ (suc k))))

    agree : ∀ k → Pointwise R (sentᴵ k) (sentᴾ k)
    agree zero    = open-agree
    agree (suc k) = step-agree (corr k)

    slice : ∀ k → Pointwise R (sliceAt (stampedAt κ e ins) k) (sliceAt (plainAt κ e ins) k)
    slice k = subst₂ (Pointwise R) (sym (sliceᴵ k)) (sym (sliceᴾ k)) (agree k)

    -- the clock `k` arrivals in, and the floor of the `k`-th arrival's instants
    U : ℕ → ℕ
    U k = clock (cᴵ k)
    L : ℕ → ℕ
    L zero    = 0
    L (suc k) = U k

    stamped : ∀ k → OneIn (L k) (U k) (sentᴵ k)
    stamped zero    = open-stamps
    stamped (suc k) = step-stamps (corr k)

    U-mono′ : ∀ {a b} → a ≤′ b → U a ≤ U b
    U-mono′ (≤′-reflexive refl) = ≤-refl
    U-mono′ (≤′-step {b} le)    = ≤-trans (U-mono′ le) (step-clock (corr b))

    U-mono : ∀ {a b} → a ≤ b → U a ≤ U b
    U-mono le = U-mono′ (≤⇒≤′ le)

    sep : ∀ {a b} → a < b → U a ≤ L b
    sep {b = suc b} (s≤s le) = U-mono le

    BIG = U fuel

    name : ℕ → Id
    name k = pick (k ≤ᵇ fuel) (sentᴵ k) (BIG + k)

    one : ∀ k → k ≤ fuel → All (λ p → proj₁ p ≡ name k) (sliceAt (stampedAt κ e ins) k)
    one k le = subst (All (λ p → proj₁ p ≡ name k)) (sym (sliceᴵ k))
                     (pick-all (k ≤ᵇ fuel) (sentᴵ k) (BIG + k) (true-of (≤⇒≤ᵇ le)) (stamped k))

    cases : ∀ k → (T (k ≤ᵇ fuel) × L k ≤ name k × name k < U k) ⊎ name k ≡ BIG + k
    cases k = pick-cases (k ≤ᵇ fuel) (sentᴵ k) (BIG + k) (stamped k)

    under : ∀ {a b} → T (a ≤ᵇ fuel) → name a < U a → name b ≡ BIG + b → name a < name b
    under {a} {b} ta ha nb =
      <-≤-trans ha (≤-trans (U-mono (≤ᵇ⇒≤ a fuel ta)) (subst (BIG ≤_) (sym nb) (m≤m+n BIG b)))

    name-inj : ∀ {a b} → name a ≡ name b → a ≡ b
    name-inj {a} {b} eq with cases a | cases b
    ... | inj₁ (_ , la , ha) | inj₁ (_ , lb , hb) with <-cmp a b
    ...   | tri< a<b _ _ = ⊥-elim (<-irrefl eq (<-≤-trans ha (≤-trans (sep a<b) lb)))
    ...   | tri≈ _ a≡b _ = a≡b
    ...   | tri> _ _ b<a = ⊥-elim (<-irrefl (sym eq) (<-≤-trans hb (≤-trans (sep b<a) la)))
    name-inj {a} {b} eq | inj₁ (ta , _ , ha) | inj₂ nb = ⊥-elim (<-irrefl eq (under {a} {b} ta ha nb))
    name-inj {a} {b} eq | inj₂ na | inj₁ (tb , _ , hb) = ⊥-elim (<-irrefl (sym eq) (under {b} {a} tb hb na))
    name-inj {a} {b} eq | inj₂ na | inj₂ nb = +-cancelˡ-≡ BIG a b (trans (sym na) (trans eq nb))

-- a prefix survives every reading the runs are taken through
concat-prefix : ∀ {A : Set} {xss yss : List (List A)} → Prefix _≡_ xss yss
              → Prefix _≡_ (concat xss) (concat yss)
concat-prefix []                   = []
concat-prefix (_∷_ {a = x} refl p) = prefix-++ x (concat-prefix p)

decode-prefix : ∀ {n} {Γ : Ctx n} {a} {xs ys : List (PlainEvent (Val Γ (instEmitᵗ uniqᵗ a)))}
              → Prefix _≡_ xs ys → Prefix _≡_ (decodeEmits xs) (decodeEmits ys)
decode-prefix []                           = []
decode-prefix (_∷_ {a = valueᵖ _} refl p)  = refl ∷ decode-prefix p
decode-prefix (_∷_ {a = completeᵖ} refl p) = decode-prefix p

extract-prefix : ∀ {A : Set} {xs ys : List (InstEmit A)} → Prefix _≡_ xs ys
               → Prefix _≡_ (instExtract xs) (instExtract ys)
extract-prefix []                   = []
extract-prefix (_∷_ {a = x} refl p) = prefix-++ (emitValues x) (extract-prefix p)

values-prefix : ∀ {A : Set} {xs ys : List (PlainEvent A)} → Prefix _≡_ xs ys
              → Prefix _≡_ (plainValues xs) (plainValues ys)
values-prefix []                           = []
values-prefix (_∷_ {a = valueᵖ _} refl p)  = refl ∷ values-prefix p
values-prefix (_∷_ {a = completeᵖ} refl p) = values-prefix p

-- a prefix is its extension's head
prefix-drop : ∀ {A : Set} {xs ys : List A} → Prefix _≡_ xs ys → xs ++ drop (length xs) ys ≡ ys
prefix-drop []         = refl
prefix-drop (refl ∷ p) = cong (_ ∷_) (prefix-drop p)

-- the impl run at a fuel is a prefix of it at any more
stamped-prefix : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
               → ∀ {a b} → a ≤ b → Prefix _≡_ (stampedAt κ e ins a) (stampedAt κ e ins b)
stamped-prefix κ e ins le = go (≤⇒≤′ le)
  where
    go : ∀ {a b} → a ≤′ b → Prefix _≡_ (stampedAt κ e ins a) (stampedAt κ e ins b)
    go (≤′-reflexive refl) = fromPointwise (pointwise-refl refl)
    go (≤′-step {b} le)    = prefix-trans trans (go le)
      (extract-prefix (decode-prefix (concat-prefix (run-prefix b (elaborateImpl κ e) (embedSlotsImpl ins)))))

-- stamps all equal to one are that one, once per value
uniform : ∀ {A B : Set} {c : A} {xs : List (A × B)} → All (λ p → proj₁ p ≡ c) xs
        → map proj₁ xs ≡ replicate (length xs) c
uniform []       = refl
uniform (q ∷ qs) = cong₂ _∷_ q (uniform qs)

-- THE RUN IS ITS ARRIVALS' SLICES, JOINED, BECAUSE EACH FUEL EXTENDS THE
-- LAST -- so a claim made one arrival at a time is a claim about the
-- run at every fuel.  The impl run is read at the plain run's own fuel,
-- and an arrival's name is its slice's one instant.
simulation : Simulation
simulation {Γ = Γ} {t = t} κ fuel e ins =
  fuel , ≤-refl , values fuel ≤-refl , name , name-inj , stamps fuel ≤-refl
  where
    X = stampedAt κ e ins
    P = plainAt κ e ins
    R = λ (p : Id × Val (plainᵏ Γ κ) (plainᵗ t)) (w : Val Γ t) → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w
    ar = arrival-runs κ fuel e ins
    name = proj₁ ar
    name-inj : ∀ {a b} → name a ≡ name b → a ≡ b
    name-inj = proj₁ (proj₂ ar)
    Y = X
    slice : ∀ k → k ≤ fuel → Pointwise R (sliceAt Y k) (sliceAt P k)
    slice k le = proj₁ (proj₂ (proj₂ ar) k le)
    one : ∀ k → k ≤ fuel → All (λ p → proj₁ p ≡ name k) (sliceAt Y k)
    one k le = proj₂ (proj₂ (proj₂ ar) k le)

    Y-grows : ∀ k → Y k ++ sliceAt Y (suc k) ≡ Y (suc k)
    Y-grows k = prefix-drop (stamped-prefix κ e ins (n≤1+n k))
    P-grows : ∀ k → P k ++ sliceAt P (suc k) ≡ P (suc k)
    P-grows k = prefix-drop (values-prefix (concat-prefix (run-prefix k (plainExp e) (plainSlots ins))))

    values : ∀ k → k ≤ fuel → Pointwise R (Y k) (P k)
    values zero    le = slice zero le
    values (suc k) le = subst₂ (Pointwise R) (Y-grows k) (P-grows k)
                          (++⁺ (values k (≤-trans (n≤1+n k) le)) (slice (suc k) le))

    stamps : ∀ k → k ≤ fuel → map proj₁ (Y k) ≡ map name (arrivalsOf {κ = κ} k e ins)
    stamps zero le = begin
      map proj₁ (Y zero)                         ≡⟨ uniform (one zero le) ⟩
      replicate (length (Y zero)) (name zero)    ≡⟨ cong (λ m → replicate m (name zero)) (Pointwise-length (values zero le)) ⟩
      replicate (length (P zero)) (name zero)    ≡⟨ sym (map-replicate name (length (P zero)) zero) ⟩
      map name (arrivalsOf {κ = κ} zero e ins)   ∎
    stamps (suc k) le = begin
      map proj₁ (Y (suc k))                                     ≡⟨ cong (map proj₁) (sym (Y-grows k)) ⟩
      map proj₁ (Y k ++ sliceAt Y (suc k))                      ≡⟨ map-++ proj₁ (Y k) (sliceAt Y (suc k)) ⟩
      map proj₁ (Y k) ++ map proj₁ (sliceAt Y (suc k))          ≡⟨ cong₂ _++_ (stamps k (≤-trans (n≤1+n k) le)) (uniform (one (suc k) le)) ⟩
      map name (arrivalsOf {κ = κ} k e ins) ++ replicate (length (sliceAt Y (suc k))) (name (suc k))
                                                                ≡⟨ cong (λ m → map name (arrivalsOf {κ = κ} k e ins) ++ replicate m (name (suc k))) count ⟩
      map name (arrivalsOf {κ = κ} k e ins) ++ replicate (length (P (suc k)) ∸ length (P k)) (name (suc k))
                                                                ≡⟨ cong (map name (arrivalsOf {κ = κ} k e ins) ++_) (sym (map-replicate name _ (suc k))) ⟩
      map name (arrivalsOf {κ = κ} k e ins) ++ map name (replicate (length (P (suc k)) ∸ length (P k)) (suc k))
                                                                ≡⟨ sym (map-++ name (arrivalsOf {κ = κ} k e ins) _) ⟩
      map name (arrivalsOf {κ = κ} (suc k) e ins)               ∎
      where
        count : length (sliceAt Y (suc k)) ≡ length (P (suc k)) ∸ length (P k)
        count = trans (Pointwise-length (slice (suc k) le)) (length-drop (length (P k)) (P (suc k)))
