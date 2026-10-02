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
-- instant.  The counts are read, never assumed monotone: a run that
-- took a value back at a higher fuel makes `arrivalsᴾ` disagree with
-- the stamps in length, so the statement says that too.
--
-- VALUES AGREE AT DATA AND ARE NOT COMPARED AT `obs`.  The two runs
-- stand in different contexts -- the elaboration's reads a share at
-- the InstEmit -- and an observable value is a closure over its own.
-- What an observable does is compared where it is run, as its emits.
--
-- THE IMPL'S SHARED-SLOT FALLBACK IS OWED HERE.  `embedSlotsImpl`
-- checks stratification of the elaborated definition and falls back to
-- `empty` if it fails; the table only certifies the plain one, so this
-- statement is where "the check never fails" is paid.
------------------------------------------------------------------
module Simulation.Statement where

open import Data.Bool    using (T)
open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤)
open import Data.List    using (List; []; _∷_; _++_; map; length; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Nat     using (ℕ; zero; suc; _∸_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Prim      using (Fuel; Id)
open import Rx.Exp       using (Ctx; Val; isData; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs)
open import SExp.Syntax  using (SExp; Kinds; plainᵏ; plainᵗ)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.Plain   using (unplainᵈ; ∧ˡ; ∧ʳ)
open import SExp.Pipeline using (runᴵ; runᴾ)
open import Batchable.Inst-Extract using (instExtract)

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

Simulation : Set
Simulation =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
            (instExtract (runᴵ κ fuel e ins)) (runᴾ fuel e ins) ×
  Σ (ℕ → Id) λ name → (∀ {a b} → name a ≡ name b → a ≡ b) ×
    map proj₁ (instExtract (runᴵ κ fuel e ins)) ≡ map name (arrivalsOf fuel e ins)

postulate
  -- PROBED: `Probed.Simulation` -- decided at fuel 3 over three
  --   first-order programs and their timed translations: a take of one
  --   of two arrivals, both arrivals kept, and a literal of two at the
  --   subscription.  Not a flattener, a share, a `μ` nor a cold slot,
  --   which are `make quickcheck`'s alone: it decides this statement on
  --   drawn programs and on every bug-cache row.
  simulation : Simulation
