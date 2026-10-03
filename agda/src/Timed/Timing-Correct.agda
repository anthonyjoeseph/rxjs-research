------------------------------------------------------------------
-- TIMING-CORRECT: the impl's instant stamps group emits exactly as the
-- timed translation's packets do.
--
-- CLOSES A CHEAT THE OTHER TOP-LINE STATEMENTS LEAVE OPEN.  Stamping
-- every emit with one instant, or each with its own, fails
-- timing-correct, since the packets are the translation's and not the
-- impl's to arrange.
--
-- EVERY PAIR OF VALUES THE IMPL EMITS FOR A TIMED PROGRAM: same stamp
-- exactly when same packet.  END items carry packets too, so a
-- completion's instant is pinned as well as a value's.
------------------------------------------------------------------
module Timed.Timing-Correct where

open import Data.List    using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-≡⇒≡)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_×_; Σ; proj₁; proj₂)
open import Function     using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Prim      using (Fuel; Id)
open import Rx.Exp        using (Ctx; Val)
open import SExp.Syntax      using (SExp; Kinds; plainᵏ; plainᵗ)
open import SExp.Simul-Slots using (SimulSlots)
open import Timed.Translation     using (timed; timedSlots; packetOf; timedᶜ; itemᵗ)
open import SExp.Pipeline using (runᴵ; runᴾ)
open import Simulation.Statement using (Agrees; simulation; arrivalsOf; stamped-prefix)
open import Batchable.Inst-Extract using (instExtract)

-- the impl's run of the timed program: each value with its stamp
stampedᵀ : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ
         → List (Id × Val (plainᵏ (timedᶜ Γ κ) κ) (plainᵗ (itemᵗ t)))
stampedᵀ κ fuel e ins = instExtract (runᴵ κ fuel (timed κ e) (timedSlots ins))

-- same stamp exactly when same packet
Coherent : ∀ {m} {Γ′ : Ctx m} t → (p q : Id × Val Γ′ (plainᵗ (itemᵗ t))) → Set
Coherent t p q = (proj₁ p ≡ proj₁ q) ⇔ (packetOf t (proj₂ p) ≡ packetOf t (proj₂ q))

Timing-Correct : Set
Timing-Correct =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  AllPairs (Coherent t) (stampedᵀ κ fuel e ins)

-- THE PLAIN RUN OF THE TIMED PROGRAM, PACKETS READ: one packet per
-- arrival, no two arrivals sharing one.  This is the translation's half
-- of the claim; the simulation is the impl's.
Packets-Name-Arrivals : Set
Packets-Name-Arrivals =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  Σ (ℕ → List ℕ) λ pname → (∀ {a b} → pname a ≡ pname b → a ≡ b) ×
    map proj₁ (runᴾ {κ = κ} fuel (timed κ e) (timedSlots ins))
      ≡ map pname (arrivalsOf {κ = κ} fuel (timed κ e) (timedSlots ins))

postulate
  -- THE COMPILED SWEEP REACHES THE FLATTENERS, AND FOUND NOTHING.
  -- `make qc-packets-name-arrivals` decides this statement itself; at
  -- depth 3, fuel one, seed 18 had 98 cases with values on two plain
  -- arrivals under an author flattener, every one agreeing.  Those
  -- counts are read at fuel one only.
  --
  -- PROBED: `Probed.Timing-Correct` -- one naming pinned at fuel 3 over
  --   the same three first-order programs.  No flattener, whose inner
  --   packets are where a naming could fail to be a function of the
  --   arrival.
  packets-name-arrivals : Packets-Name-Arrivals

-- STAMP AND PACKET BOTH NAMING ONE ARRIVAL, INJECTIVELY, IS COHERENCE:
-- each side is equal exactly when the arrivals are.
module _ {A I P : Set} (stamp : A → I) (pkt : A → P) {name : ℕ → I} {pname : ℕ → P}
         (name-inj : ∀ {a b} → name a ≡ name b → a ≡ b)
         (pname-inj : ∀ {a b} → pname a ≡ pname b → a ≡ b) where

  named-pair : ∀ {x y a b} → stamp x ≡ name a → pkt x ≡ pname a → stamp y ≡ name b → pkt y ≡ pname b
             → (stamp x ≡ stamp y) ⇔ (pkt x ≡ pkt y)
  named-pair sx px sy py =
    mk⇔ (λ s → trans px (trans (cong pname (name-inj (trans (sym sx) (trans s sy)))) (sym py)))
        (λ p → trans sx (trans (cong name (pname-inj (trans (sym px) (trans p py)))) (sym sy)))

  named-all : ∀ {x a} ys bs → stamp x ≡ name a → pkt x ≡ pname a
            → map stamp ys ≡ map name bs → map pkt ys ≡ map pname bs
            → All (λ y → (stamp x ≡ stamp y) ⇔ (pkt x ≡ pkt y)) ys
  named-all []       _        _  _  _  _  = []
  named-all (y ∷ ys) (b ∷ bs) sx px ss ps =
    named-pair sx px (∷-injectiveˡ ss) (∷-injectiveˡ ps) ∷
    named-all ys bs sx px (∷-injectiveʳ ss) (∷-injectiveʳ ps)
  named-all (y ∷ ys) []       _  _  () _

  named-coherent : ∀ xs bs → map stamp xs ≡ map name bs → map pkt xs ≡ map pname bs
                 → AllPairs (λ x y → (stamp x ≡ stamp y) ⇔ (pkt x ≡ pkt y)) xs
  named-coherent []       _        _  _  = []
  named-coherent (x ∷ xs) (b ∷ bs) ss ps =
    named-all xs bs (∷-injectiveˡ ss) (∷-injectiveˡ ps) (∷-injectiveʳ ss) (∷-injectiveʳ ps) ∷
    named-coherent xs bs (∷-injectiveʳ ss) (∷-injectiveʳ ps)
  named-coherent (x ∷ xs) []       () _

-- agreeing items carry the same packets
packets-agree : ∀ {n m} {Γ′ : Ctx m} {Γ : Ctx n} t {xs : List (Id × Val Γ′ (plainᵗ (itemᵗ t)))}
                {ws : List (Val Γ (itemᵗ t))}
              → Pointwise (λ p w → Agrees Γ′ Γ (itemᵗ t) (proj₂ p) w) xs ws
              → map (λ p → packetOf {Γ = Γ′} t (proj₂ p)) xs ≡ map proj₁ ws
packets-agree t []       = refl
packets-agree t (q ∷ qs) = cong₂ _∷_ (Pointwise-≡⇒≡ (proj₁ q)) (packets-agree t qs)

-- a relation every pair of a list satisfies, every pair of its prefix
-- does
all-prefix : ∀ {A : Set} {P : A → Set} {xs ys : List A} → Prefix _≡_ xs ys → All P ys → All P xs
all-prefix []         _        = []
all-prefix (refl ∷ p) (q ∷ qs) = q ∷ all-prefix p qs

allPairs-prefix : ∀ {A : Set} {R : A → A → Set} {xs ys : List A} → Prefix _≡_ xs ys
                → AllPairs R ys → AllPairs R xs
allPairs-prefix []         _        = []
allPairs-prefix (refl ∷ p) (q ∷ qs) = all-prefix p q ∷ allPairs-prefix p qs

-- THE SIMULATION NAMES THE IMPL RUN AT ITS OWN, LARGER FUEL, so
-- coherence is proven there and read back down the prefix
timing-correct : Timing-Correct
timing-correct {Γ = Γ} {t = t} κ fuel e ins =
  allPairs-prefix (stamped-prefix κ (timed κ e) (timedSlots ins) (proj₁ (proj₂ sim)))
    (named-coherent proj₁ (λ p → packetOf {Γ = plainᵏ (timedᶜ Γ κ) κ} t (proj₂ p))
      (λ {a} {b} → proj₁ (proj₂ named) {a} {b}) (λ {a} {b} → proj₁ (proj₂ pkt) {a} {b})
      (stampedᵀ κ (proj₁ sim) e ins) _ (proj₂ (proj₂ named))
      (trans (packets-agree t (proj₁ (proj₂ (proj₂ sim)))) (proj₂ (proj₂ pkt))))
  where
    sim = simulation κ fuel (timed κ e) (timedSlots ins)
    named = proj₂ (proj₂ (proj₂ sim))
    pkt = packets-name-arrivals κ fuel e ins
