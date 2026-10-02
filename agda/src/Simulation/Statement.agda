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
-- THE IMPL'S SHARED-SLOT FALLBACK IS OWED BY `arrival-runs`.
-- `embedSlotsImpl` checks stratification of the elaborated definition
-- and falls back to `empty` if it fails; the table only certifies the
-- plain one, so the values are where "the check never fails" is paid.
------------------------------------------------------------------
module Simulation.Statement where

open import Data.Bool    using (T)
open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤)
open import Data.List    using (List; []; _∷_; _++_; map; length; replicate; drop; concat)
open import Data.List.Properties using (map-++; map-replicate; length-drop)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties using (fromPointwise)
  renaming (trans to prefix-trans)
open import Data.List.Relation.Binary.Pointwise.Properties using (Pointwise-length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺)
  renaming (refl to pointwise-refl)
open import Data.Nat     using (ℕ; zero; suc; _∸_; _≤_; _<_; z≤n; _≤′_; ≤′-reflexive; ≤′-step)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <⇒≤; ≤-<-trans; ≤⇒≤′)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst₂)
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
-- (Anthony).  The elaboration's `takeᵖ` subscribes its upstream twice,
-- so over a cold one the impl spends more arrivals delivering what the
-- plain run delivers in fewer.
-- REFUTED: `simulation-false` -- the equal-fuel form, at `take 2` over
--   a cold with two async values.
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

-- EACH PLAIN ARRIVAL IS A RUN OF IMPL ARRIVALS, `ψ` SAYING WHERE EACH
-- RUN ENDS: the plain run's k-th slice agrees with what the impl run
-- delivers past `ψ (k - 1)` through `ψ k`, and every value of that run
-- carries one instant, `name k`, no two plain arrivals sharing one.
-- `ψ` rises strictly, so every run holds at least one impl arrival.
--
-- THE VALUES AND THE INSTANTS SHARE `ψ`, SO ONE STATEMENT CARRIES BOTH.
-- An instant names a PLAIN arrival: the impl arrivals of one run may
-- share theirs, and do wherever one plain arrival's values come out
-- across several.
Arrival-Runs : Set
Arrival-Runs =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ (ℕ → ℕ) λ ψ → (∀ k → ψ k < ψ (suc k)) ×
  Σ (ℕ → Id) λ name → (∀ {a b} → name a ≡ name b → a ≡ b) ×
    (∀ k → k ≤ fuel →
      Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
                (sliceAt (λ j → stampedAt κ e ins (ψ j)) k) (sliceAt (plainAt κ e ins) k) ×
      All (λ p → proj₁ p ≡ name k) (sliceAt (λ j → stampedAt κ e ins (ψ j)) k))

postulate
  -- WHERE IT CAN STILL FAIL: A RUN THAT IS NOT CONTIGUOUS -- one plain
  -- arrival's values interleaved with the next's in the impl's order,
  -- or an impl arrival carrying the tail of one plain arrival and the
  -- head of the next.  Read off the definitions, not instantiated.
  --
  -- A PLAIN ARRIVAL DOES SPLIT, so no form sending it to ONE impl
  -- arrival holds, nor one instant per impl arrival.  Found by the
  -- compiled QuickCheck at the bug cache's row "seed 5 depth 2 fuel 4
  -- timing-correct": the timed translation of a `take 5` over a cold,
  -- under `exhaust`, delivers plain arrival 1's value and its END at impl
  -- arrivals 1 and 2, both at instant 29.  Not stated in Agda: the timed
  -- `take` does not reduce in the typechecker in useful time.
  --
  -- RUNS LONGER THAN ONE IMPL ARRIVAL HOLD WHERE THE SWEEP REACHES THEM.
  -- Compiled, every statement decided: the bug cache's rows "a cold
  -- under two takes in one merge" -- the cut lane's empty arrival folds
  -- into the next run, and timed, a value and its END land at two impl
  -- arrivals of one instant -- and "a take of a cold exhausted beside an
  -- of", timed, the same split; "an of buffered behind a take of a
  -- cold", untimed, splits VALUES: the cut lane's copy of the cold's first
  -- event completes the `take`, so the buffered `of` emits one impl
  -- arrival later, at the same instant.  CI's sweep, seeds 1..12 at
  -- fifteen cases of depth 2, adds no counterexample.  No row reached an impl arrival carrying two plain
  -- arrivals' values, which is where this can still fail.
  --
  -- REFUTED: `arrival-values-false` -- the equal-fuel form with the map
  --   the identity, at `take 2` over a cold with two async values;
  --   `takeᵖ` subscribes the cold twice, so the impl's slice at arrival 2
  --   is empty where the plain run's holds 6.
  -- PROBED: `Probed.Simulation` -- every slice through fuel 3 over three
  --   first-order programs and the timed translations of two, all over a
  --   hot slot with the map the identity, the empty slices included.  No
  --   run longer than one impl arrival, which is the compiled sweep's.
  arrival-runs : Arrival-Runs

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

-- a strictly rising fuel map outruns the identity
outruns : (ψ : ℕ → ℕ) → (∀ k → ψ k < ψ (suc k)) → ∀ k → k ≤ ψ k
outruns ψ up zero    = z≤n
outruns ψ up (suc k) = ≤-<-trans (outruns ψ up k) (up k)

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
-- run at every fuel.  The impl run is read at `ψ`'s fuels, so its fuel
-- is `ψ fuel`, and an arrival's name is its run's one instant.
simulation : Simulation
simulation {Γ = Γ} {t = t} κ fuel e ins =
  ψ fuel , outruns ψ up fuel , values fuel ≤-refl , name , name-inj , stamps fuel ≤-refl
  where
    X = stampedAt κ e ins
    P = plainAt κ e ins
    R = λ (p : Id × Val (plainᵏ Γ κ) (plainᵗ t)) (w : Val Γ t) → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w
    ar = arrival-runs κ fuel e ins
    ψ = proj₁ ar
    up : ∀ k → ψ k < ψ (suc k)
    up = proj₁ (proj₂ ar)
    name = proj₁ (proj₂ (proj₂ ar))
    name-inj : ∀ {a b} → name a ≡ name b → a ≡ b
    name-inj = proj₁ (proj₂ (proj₂ (proj₂ ar)))
    Y = λ j → X (ψ j)
    slice : ∀ k → k ≤ fuel → Pointwise R (sliceAt Y k) (sliceAt P k)
    slice k le = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ar))) k le)
    one : ∀ k → k ≤ fuel → All (λ p → proj₁ p ≡ name k) (sliceAt Y k)
    one k le = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ar))) k le)

    Y-grows : ∀ k → Y k ++ sliceAt Y (suc k) ≡ Y (suc k)
    Y-grows k = prefix-drop (stamped-prefix κ e ins (<⇒≤ (up k)))
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
