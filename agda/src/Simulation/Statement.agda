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
-- THE IMPL'S SHARED-SLOT FALLBACK IS OWED BY `arrival-values`.
-- `embedSlotsImpl` checks stratification of the elaborated definition
-- and falls back to `empty` if it fails; the table only certifies the
-- plain one, so the values are where "the check never fails" is paid.
------------------------------------------------------------------
module Simulation.Statement where

open import Data.Bool    using (T)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤)
open import Data.List    using (List; []; _∷_; _++_; map; length; replicate; drop; concat)
open import Data.List.Properties using (map-++; map-replicate; length-drop; ++-identityʳ)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties using (fromPointwise)
  renaming (trans to prefix-trans)
open import Data.List.Relation.Binary.Pointwise.Properties using (Pointwise-length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺)
  renaming (refl to pointwise-refl)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-reflexive; ≤′-step)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <⇒≤; <-≤-trans; ≤-<-trans; <-irrefl; <-cmp; ≤⇒≤′;
  <-asym; <-trans; ≤-pred; ≤-reflexive; n<1+n; +-suc; +-identityʳ; m≤m+n; m+[n∸m]≡n)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
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

-- EACH PLAIN ARRIVAL'S VALUES ARE ONE IMPL ARRIVAL'S, `ψ` SAYING WHICH,
-- and every impl arrival `ψ` skips sends nothing.  `ψ` rises strictly,
-- so no two plain arrivals share an impl one.
Arrival-Values : Set
Arrival-Values =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ (ℕ → ℕ) λ ψ → (∀ k → ψ k < ψ (suc k)) ×
    (∀ j → j ≤ ψ fuel → (∀ k → ψ k ≢ j) → sliceAt (stampedAt κ e ins) j ≡ []) ×
    (∀ k → k ≤ fuel →
      Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
                (sliceAt (stampedAt κ e ins) (ψ k)) (sliceAt (plainAt κ e ins) k))

-- ONE INSTANT PER ARRIVAL, AND NONE SHARED.  A claim about the
-- elaborated run alone: the plain run carries no instants to compare.
Arrival-Instants : Set
Arrival-Instants =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Σ (ℕ → Id) λ σ → (∀ {a b} → σ a ≡ σ b → a ≡ b) ×
    (∀ k → k ≤ fuel → All (λ p → proj₁ p ≡ σ k) (sliceAt (stampedAt κ e ins) k))

postulate
  -- WHERE IT CAN STILL FAIL: ONE PLAIN ARRIVAL'S VALUES SPLIT ACROSS TWO
  -- IMPL ARRIVALS, which no rising map pairs.  A QuickCheck deciding
  -- `simulation` with both runs at one fuel past both ends sees a split
  -- -- two instants naming one arrival -- and cannot see a lag, which
  -- this statement allows.  Read off the definitions, not instantiated.
  --
  -- REFUTED: `arrival-values-false` -- the equal-fuel form, at `take 2`
  --   over a cold with two async values; `takeᵖ` subscribes the cold
  --   twice, so the impl's slice at arrival 2 is empty where the plain
  --   run's holds 6.
  -- PROBED: `Probed.Simulation` -- every slice through fuel 3 over three
  --   first-order programs and the timed translations of two, all over a
  --   hot slot with the map the identity, the empty slices included; and
  --   `take 2` over a cold, the map skipping the cut lane's arrival.  No
  --   cold under two subscriptions at once, which is where a split lives.
  arrival-values   : Arrival-Values
  -- PROBED: `Probed.Simulation` -- at fuel 3 over the same five programs,
  --   with two values in one slice and values in two slices both
  --   reached.  The same five shapes are `make quickcheck`'s alone.
  arrival-instants : Arrival-Instants

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

-- A STRICTLY RISING FUEL MAP never falls, outruns the identity, and
-- names no fuel twice
module _ (ψ : ℕ → ℕ) (up : ∀ k → ψ k < ψ (suc k)) where

  climbs′ : ∀ {a b} → a ≤′ b → ψ a ≤ ψ b
  climbs′ (≤′-reflexive refl) = ≤-refl
  climbs′ (≤′-step {b} le)    = ≤-trans (climbs′ le) (<⇒≤ (up b))

  climbs : ∀ {a b} → a ≤ b → ψ a ≤ ψ b
  climbs le = climbs′ (≤⇒≤′ le)

  rises : ∀ {a b} → a < b → ψ a < ψ b
  rises {a} lt = <-≤-trans (up a) (climbs lt)

  reflects : ∀ {a b} → ψ a < ψ b → a < b
  reflects {a} {b} lt with <-cmp a b
  ... | tri< a<b _ _ = a<b
  ... | tri≈ _ refl _ = ⊥-elim (<-irrefl refl lt)
  ... | tri> _ _ b<a = ⊥-elim (<-asym lt (rises b<a))

  -- no fuel strictly between two neighbours, nor below the first, is named
  unnamed-between : ∀ {k j} → ψ k < j → j < ψ (suc k) → ∀ k′ → ψ k′ ≢ j
  unnamed-between {k} lo hi k′ refl =
    <-irrefl refl (<-≤-trans (reflects lo) (≤-pred (reflects hi)))

  unnamed-below : ∀ {j} → j < ψ 0 → ∀ k′ → ψ k′ ≢ j
  unnamed-below lt k′ refl = <-irrefl refl (<-≤-trans lt (climbs z≤n))

  outruns : ∀ k → k ≤ ψ k
  outruns zero    = z≤n
  outruns (suc k) = ≤-<-trans (outruns k) (up k)

  rises-injective : ∀ {a b} → ψ a ≡ ψ b → a ≡ b
  rises-injective {a} {b} eq with <-cmp a b
  ... | tri< lt _ _ = ⊥-elim (<-irrefl eq (rises lt))
  ... | tri≈ _ ab _ = ab
  ... | tri> _ _ gt = ⊥-elim (<-irrefl (sym eq) (rises gt))

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
-- run at every fuel, and the naming is the instant of each slice.  The
-- impl run is read at `ψ`'s fuels, so its fuel is `ψ fuel` and an
-- arrival's name is the instant of the impl arrival `ψ` sends it to.
simulation : Simulation
simulation {Γ = Γ} {t = t} κ fuel e ins =
  ψ fuel , outruns ψ up fuel , values fuel ≤-refl ,
  name , (λ {a} {b} eq → rises-injective ψ up (σ-inj eq)) , stamps fuel ≤-refl
  where
    X = stampedAt κ e ins
    P = plainAt κ e ins
    R = λ (p : Id × Val (plainᵏ Γ κ) (plainᵗ t)) (w : Val Γ t) → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w
    av = arrival-values κ fuel e ins
    ψ = proj₁ av
    up : ∀ k → ψ k < ψ (suc k)
    up = proj₁ (proj₂ av)
    skipped : ∀ j → j ≤ ψ fuel → (∀ k → ψ k ≢ j) → sliceAt X j ≡ []
    skipped = proj₁ (proj₂ (proj₂ av))
    Y = λ j → X (ψ j)

    X-grows : ∀ k → X k ++ sliceAt X (suc k) ≡ X (suc k)
    X-grows k = prefix-drop (stamped-prefix κ e ins (n≤1+n k))

    -- the run stands still below `ψ 0` and between neighbours
    empty-below : ∀ m → m < ψ 0 → X m ≡ []
    empty-below zero    lt = skipped zero (<⇒≤ (<-≤-trans lt (climbs ψ up z≤n))) (unnamed-below ψ up lt)
    empty-below (suc m) lt = begin
      X (suc m)                ≡⟨ sym (X-grows m) ⟩
      X m ++ sliceAt X (suc m) ≡⟨ cong₂ _++_ (empty-below m (<-trans (n<1+n m) lt))
                                    (skipped (suc m) (<⇒≤ (<-≤-trans lt (climbs ψ up z≤n))) (unnamed-below ψ up lt)) ⟩
      []                       ∎

    still : ∀ k d → suc k ≤ fuel → ψ k + d < ψ (suc k) → X (ψ k + d) ≡ X (ψ k)
    still k zero    le lt = cong X (+-identityʳ (ψ k))
    still k (suc d) le lt = begin
      X (ψ k + suc d)                          ≡⟨ cong X e′ ⟩
      X (suc (ψ k + d))                        ≡⟨ sym (X-grows (ψ k + d)) ⟩
      X (ψ k + d) ++ sliceAt X (suc (ψ k + d)) ≡⟨ cong (X (ψ k + d) ++_)
                                                    (skipped _ (<⇒≤ (<-≤-trans lt′ (climbs ψ up le)))
                                                       (unnamed-between ψ up (s≤s (m≤m+n (ψ k) d)) lt′)) ⟩
      X (ψ k + d) ++ []                        ≡⟨ ++-identityʳ (X (ψ k + d)) ⟩
      X (ψ k + d)                              ≡⟨ still k d le (<-trans (n<1+n _) lt′) ⟩
      X (ψ k)                                  ∎
      where
        e′ = +-suc (ψ k) d
        lt′ : suc (ψ k + d) < ψ (suc k)
        lt′ = subst (_< ψ (suc k)) e′ lt

    -- read at `ψ`'s fuels, the impl run's slices are its own
    head-slice : ∀ m → (∀ i → i < m → X i ≡ []) → X m ≡ sliceAt X m
    head-slice zero    h = refl
    head-slice (suc m) h = sym (cong (λ xs → drop (length xs) (X (suc m))) (h m (n<1+n m)))

    gap : ∀ k → k ≤ fuel → sliceAt Y k ≡ sliceAt X (ψ k)
    gap zero    le = head-slice (ψ 0) empty-below
    gap (suc k) le = sym (begin
      sliceAt X (ψ (suc k))                           ≡⟨ cong (sliceAt X) (sym eq) ⟩
      drop (length (X (ψ k + d))) (X (suc (ψ k + d))) ≡⟨ cong (λ xs → drop (length xs) (X (suc (ψ k + d))))
                                                           (still k d le (≤-reflexive eq)) ⟩
      drop (length (X (ψ k))) (X (suc (ψ k + d)))     ≡⟨ cong (λ m → drop (length (X (ψ k))) (X m)) eq ⟩
      sliceAt Y (suc k)                               ∎)
      where
        d = ψ (suc k) ∸ suc (ψ k)
        eq : suc (ψ k + d) ≡ ψ (suc k)
        eq = m+[n∸m]≡n (up k)

    slice : ∀ k → k ≤ fuel → Pointwise R (sliceAt Y k) (sliceAt P k)
    slice k le = subst (λ s → Pointwise R s (sliceAt P k)) (sym (gap k le)) (proj₂ (proj₂ (proj₂ av)) k le)

    inst = arrival-instants κ (ψ fuel) e ins
    σ = proj₁ inst
    σ-inj : ∀ {a b} → σ a ≡ σ b → a ≡ b
    σ-inj = proj₁ (proj₂ inst)
    name = λ j → σ (ψ j)
    one : ∀ k → k ≤ fuel → All (λ p → proj₁ p ≡ name k) (sliceAt Y k)
    one k le = subst (All (λ p → proj₁ p ≡ name k)) (sym (gap k le)) (proj₂ (proj₂ inst) (ψ k) (climbs ψ up le))

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
