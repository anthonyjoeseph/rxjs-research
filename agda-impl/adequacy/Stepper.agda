{-# OPTIONS --guardedness #-}

-- THE STEPPER IS THE MEANING, skips included: a sane, placed ghost's
-- meaning is what its step shows, then the meaning of the node it
-- leaves.  Stated at the root, where no connect's source is in scope;
-- inside a body the step is the run's next event only if it comes before
-- each running source's, its pool's and each ended source's rest.
module port.Stepper where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁; [_,_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; map₂; uncurry)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; idle; ix; _<ᵖ_; _∪_; Tail; pin; <ᵖ-trans;
  <ᵖ-irrefl; <ᵖ-asym; <ᵖ-below; <ᵖ-split; <ᵖ-step)
open import denotation.MonotonicList using (Agree; Agreeᵀ; stop; stopᵀ; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agreeᵀ-refl; agreeᵀ-sym; agree-trans)
open import denotation.NonExpansive using (Agreeˢ; _,ˢ_; beside-ne; body-ne; before-agree; ∪-ne; burstOn-ne)
open import port.Stepper.Past using (Belowᴱ; Clear; Clearᴱ; First; Firsts; Firstᴸ; Firstᴹ; Floor; Floorᴱ; Past; Pastᴱ; Shy; Skips;
  Skipsᴸ; Skipsᴹ; _≃_; afterᴱ; alike; before-after; clear-floor; clear-lower; first-join;
  floorᴱ-agree; head-map; head-scan; join-skips; one-map; one-scan; one-take; past-before;
  past-map; past-scan; past-take; past-under; shows; under-≡)
open import port.Stepper.Flat using (earliest-found; flat-first)
open import port.Stepper.Parts using (<ᵖ-either; after-map; after-scan; after-take; agree-hush; agree-shown; ahead-split; before-false; before-pos; belowᴱ-shown; burst-after; bursting-skips; clear-take; defer-skips; ended-hush; ended-skips; ended-split; feed-alike; first-bursting; first-defer; first-rest; first-under; first-union; flat-skips; frames-after; head-body; head-shut; hush?; hushˢ?; move; of-after; one-body; one-bodyˢ; one-shut; one-shutˢ; over-before; pastᴱ-body; pastᴱ-pos; pick; pos-pastᴱ; pos-shown; posᴱ; rest-skips; shownˢ; shut-alike; side-ahead; source-hush; source-split; under-before; under-or; under-shownˢ; under-skips; union-skips)

open Agreeˢ using (nowˢ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import port.Sane using (Sane; Saneᴹ; Saneᴸ; Mode; runs; over; Rested; step-rested)
open import port.Placed.Order using (still; Placed; Placedᴹ; Placedᴸ; Sides)
open import port.Placed.Heads using (apart-sides)
open import port.Placed.Keys using (ahead-quiet)

open _≃_
open Events∞

module Beside {Γ A B} (ν : All (λ _ → Mode) Γ) (m₀ : Mode) r (ρ : NEnv Γ) (x₀ : Events A)
              (e : Events A) (σ : Events∞ A) (ts : U.Step Γ A) (β : Events∞ B) (tb : U.Step (A ∷ Γ) B)
              (bodyF : U.Step (A ∷ Γ) B → U.Step Γ B) (step : U.Step Γ B)
              (entry : ∀ {h m} → Past (m₀ ∷ᴬ ν) h m (x₀ ∷ᴬ ρ) → Belowᴱ e h m ⊎ Past ν h m ρ)
              (head-F : U.headˢ (bodyF tb) ≡ U.headˢ tb)
              (one-F : ∀ k {x} → Agree 1 x (afterᴱ (x₀ ∷ᴬ ρ) tb) → Agree 1 (M′.body r σ k x) (afterᴱ ρ (bodyF tb)))
              (one-Fˢ : ∀ {x} → Agree 1 x (afterᴱ (x₀ ∷ᴬ ρ) tb) → Agree 1 x (afterᴱ ρ (bodyF tb)))
              (quiet : ts ≡ U.hushˢ → step ≡ bodyF tb)
              (route : ts ≢ U.hushˢ → (U.beforeˢ (shownˢ ts) tb ≡ true × Σ (U.Node Γ B) (λ n → step ≡ U.skipˢ (shownˢ ts) n))
                                     ⊎ (U.beforeˢ (shownˢ ts) tb ≡ false × step ≡ bodyF tb)) where

  env : NEnv (A ∷ Γ)
  env = x₀ ∷ᴬ ρ

  mb : Events B
  mb = force β

  K : Pos
  K = M′.shownAt e

  -- The body's past event: the head entry's witness, or one in scope.
  seen : Pastᴱ (m₀ ∷ᴬ ν) env tb mb → mb ≢ hush × (Belowᴱ e (posᴱ mb) (U.headˢ tb) ⊎ Past ν (posᴱ mb) (U.headˢ tb) ρ)
  seen pa = map₂ entry (pastᴱ-pos (m₀ ∷ᴬ ν) env tb mb pa)

  case-seen : ∀ {X : Set} → Pastᴱ (m₀ ∷ᴬ ν) env tb mb
            → (mb ≢ hush → Belowᴱ e (posᴱ mb) (U.headˢ tb) → X) → (mb ≢ hush → Past ν (posᴱ mb) (U.headˢ tb) ρ → X) → X
  case-seen pa f g = uncurry (λ nh → [_,_] (f nh) (g nh)) (seen pa)

  -- The body's event is no witness past the source's when the body shows
  -- at or before it.
  below-false : ∀ {m} → Belowᴱ e (posᴱ mb) m → M′.before K mb ≡ false → mb ≢ hush → ⊥
  below-false bl ff nh = ⊥-elim (subst T (trans (sym (proj₁ (belowᴱ-shown e (posᴱ mb) _ bl))) (trans (sym (before-pos K mb nh)) ff)) tt)

  -- The source shown first, past a body stepping no later.
  skip-past : U.beforeˢ K tb ≡ false → M′.before K mb ≡ true → First (m₀ ∷ᴬ ν) env tb mb → Past ν K (U.headˢ tb) ρ
  skip-past bf bt (inj₁ ag) = ⊥-elim (subst T (trans (sym bt) (trans (before-agree K ag) (trans (before-after env K tb) bf))) tt)
  skip-past bf bt (inj₂ pa) = case-seen pa
    (λ nh bl → ⊥-elim (subst T (trans (sym (under-before tb K K bf (proj₂ (belowᴱ-shown e (posᴱ mb) (U.headˢ tb) bl)))) (<ᵖ-irrefl K)) tt))
    (λ nh px → move ν ρ (posᴱ mb) (U.headˢ tb) K (U.headˢ tb) (λ a ab u → under-before tb K a bf u , u) px)

  -- The body shown first, past a source step `k` showing no earlier.
  skip-body : ∀ k → U.beforeˢ k tb ≡ true → k <ᵖ posᴱ mb ≡ false → M′.before K mb ≡ false → First (m₀ ∷ᴬ ν) env tb mb
            → Past ν (posᴱ mb) (just k) ρ
  skip-body k bt kf ff (inj₁ ag) =
    ⊥-elim (subst T (trans (sym bt) (trans (sym (before-after env k tb)) (trans (sym (before-agree k ag)) (trans (before-pos k mb (before-false K mb ff)) kf)))) tt)
  skip-body k bt kf ff (inj₂ pa) = case-seen pa
    (λ nh bl → ⊥-elim (below-false bl ff nh))
    (λ nh px → move ν ρ (posᴱ mb) (U.headˢ tb) (posᴱ mb) (just k) (λ a ab u → ab , still a (posᴱ mb) k ab kf) px)

  -- The body's step taken, shown first.
  body-body : M′.before K mb ≡ false → First (m₀ ∷ᴬ ν) env tb mb → First ν ρ (bodyF tb) (M′.body r σ K mb)
  body-body ff (inj₁ ag) = inj₁ (one-F K ag)
  body-body ff (inj₂ pa) = case-seen pa
    (λ nh bl → ⊥-elim (below-false bl ff nh))
    (λ nh px → inj₂ (pastᴱ-body ν ρ r σ K (bodyF tb) mb nh (past-under ν ρ (posᴱ mb) _ _ (under-≡ (sym head-F)) px)))

  -- The body's step taken, the source shown first.
  body-skip : ∀ {τ} → U.beforeˢ K tb ≡ false → M′.before K mb ≡ true → First (m₀ ∷ᴬ ν) env tb mb
            → First ν ρ (bodyF tb) (skip K τ)
  body-skip bf bt fb = inj₂ (past-under ν ρ K _ _ (under-≡ (sym head-F)) (skip-past bf bt fb))

  -- The source hushed: the connect is its body.
  hushed : e ≡ hush → First ν ρ ts e → First (m₀ ∷ᴬ ν) env tb mb → First ν ρ step (M′.side r β σ e)
  hushed eq fs fb = subst (λ x → First ν ρ step (M′.side r β σ x)) (sym eq) (subst (λ t → First ν ρ t mb) (sym (quiet (hushes fs))) (body fb))
    where
      hushes : First ν ρ ts e → ts ≡ U.hushˢ
      hushes (inj₁ ag) = agree-hush ρ ts (subst (λ x → Agree 1 x (afterᴱ ρ ts)) eq ag)
      hushes (inj₂ pa) = ⊥-elim (proj₁ (pastᴱ-pos ν ρ ts e pa) eq)
      past : mb ≢ hush × (Belowᴱ e (posᴱ mb) (U.headˢ tb) ⊎ Past ν (posᴱ mb) (U.headˢ tb) ρ) → First ν ρ (bodyF tb) mb
      past (nh , inj₁ bl) = ⊥-elim (subst (λ x → Belowᴱ x (posᴱ mb) (U.headˢ tb)) eq bl)
      past (nh , inj₂ px) = inj₂ (pos-pastᴱ ν ρ _ mb nh (past-under ν ρ (posᴱ mb) _ _ (under-≡ (sym head-F)) px))
      body : First (m₀ ∷ᴬ ν) env tb mb → First ν ρ (bodyF tb) mb
      body (inj₁ ag) = inj₁ (one-Fˢ ag)
      body (inj₂ pa) = case-seen pa (λ nh bl → past (nh , inj₁ bl)) (λ nh px → past (nh , inj₂ px))

  -- What the connect shows: the source's shown step when the body shows
  -- past it, else the body's event.
  Shape : Events B → Set
  Shape M = (M′.before K mb ≡ true × Σ (Events∞ B) (λ τ → M ≡ skip K τ)) ⊎ (M′.before K mb ≡ false × M ≡ M′.body r σ K mb)

  -- The source shown, its step agreeing: the connect takes whichever
  -- step shows first.
  told : e ≢ hush → Agree 1 e (afterᴱ ρ ts) → First (m₀ ∷ᴬ ν) env tb mb → ∀ {M} → Shape M → First ν ρ step M
  told nh ag fb sp with agree-shown ρ ts e ag nh
  ... | tnh , sh with route tnh | sp
  ...   | inj₁ (sbt , n , eqS) | inj₁ (bt , τ , refl) =
            subst (λ t → First ν ρ t (skip K τ)) (sym eqS) (inj₁ (subst (λ k → Agree 1 (skip K τ) (skip k _)) (sym sh) (skip⁼ stopᵀ stop)))
  ...   | inj₁ (sbt , n , eqS) | inj₂ (bf , refl) =
            subst (λ t → First ν ρ t (M′.body r σ K mb)) (sym eqS)
              (inj₂ (pastᴱ-body ν ρ r σ K _ mb (before-false K mb bf)
                (skip-body (shownˢ ts) sbt (subst (λ k → k <ᵖ posᴱ mb ≡ false) (sym sh) (trans (sym (before-pos K mb (before-false K mb bf))) bf)) bf fb)))
  ...   | inj₂ (sbf , eqS) | inj₁ (bt , τ , refl) =
            subst (λ t → First ν ρ t (skip K τ)) (sym eqS) (body-skip (subst (λ k → U.beforeˢ k tb ≡ false) sh sbf) bt fb)
  ...   | inj₂ (sbf , eqS) | inj₂ (bf , refl) =
            subst (λ t → First ν ρ t (M′.body r σ K mb)) (sym eqS) (body-body bf fb)

  -- The source preempted by a running source's witness `px`, the body's
  -- step taken: the witness kept, or the body's when it shows first.
  bodied : e ≢ hush → Past ν (posᴱ e) (U.headˢ ts) ρ → First (m₀ ∷ᴬ ν) env tb mb → ∀ {M} → Shape M → First ν ρ (bodyF tb) M
  bodied nh px fb (inj₂ (bf , refl)) = body-body bf fb
  bodied nh px fb (inj₁ (bt , τ , refl))
    with pick ν ρ (posᴱ e) (U.headˢ ts) K (U.headˢ tb) (λ a ab u → map₁ ((<ᵖ-trans a (posᴱ e) K ab (pos-shown e nh)) ,_) (under-or (U.headˢ tb) a K (<ᵖ-trans a (posᴱ e) K ab (pos-shown e nh)))) px
  ... | inj₁ p = inj₂ (past-under ν ρ K _ _ (under-≡ (sym head-F)) p)
  ... | inj₂ o = body-skip (over-before tb K o) bt fb

  -- The source preempted, its step taken: the witness kept, or the body's
  -- when it shows first.
  skipped : e ≢ hush → Past ν (posᴱ e) (U.headˢ ts) ρ → First (m₀ ∷ᴬ ν) env tb mb → (tnh : ts ≢ U.hushˢ) → U.beforeˢ (shownˢ ts) tb ≡ true
          → ∀ n {M} → Shape M → First ν ρ (U.skipˢ (shownˢ ts) n) M
  skipped nh px fb tnh sbt n (inj₁ (bt , τ , refl)) =
    inj₂ (move ν ρ (posᴱ e) (U.headˢ ts) K (just (shownˢ ts)) (λ a ab u → <ᵖ-trans a (posᴱ e) K ab (pos-shown e nh) , under-shownˢ ts a tnh u) px)
  skipped nh px fb tnh sbt n (inj₂ (bf , refl))
    with pick ν ρ (posᴱ e) (U.headˢ ts) (posᴱ mb) (just (shownˢ ts)) (λ a ab u → map₁ (_, under-shownˢ ts a tnh u) (<ᵖ-either a (posᴱ mb) (shownˢ ts) (under-shownˢ ts a tnh u))) px
  ... | inj₁ p  = inj₂ (pastᴱ-body ν ρ r σ K _ mb (before-false K mb bf) p)
  ... | inj₂ hk = inj₂ (pastᴱ-body ν ρ r σ K _ mb (before-false K mb bf) (skip-body (shownˢ ts) sbt (<ᵖ-asym (posᴱ mb) (shownˢ ts) hk) bf fb))

  preempted : e ≢ hush → Past ν (posᴱ e) (U.headˢ ts) ρ → First (m₀ ∷ᴬ ν) env tb mb → ∀ {M} → Shape M → First ν ρ step M
  preempted nh px fb sp with hushˢ? ts
  ... | inj₁ eqt = subst (λ t → First ν ρ t _) (sym (quiet eqt)) (bodied nh px fb sp)
  ... | inj₂ tnh with route tnh
  ...   | inj₂ (sbf , eqS)     = subst (λ t → First ν ρ t _) (sym eqS) (bodied nh px fb sp)
  ...   | inj₁ (sbt , n , eqS) = subst (λ t → First ν ρ t _) (sym eqS) (skipped nh px fb tnh sbt n sp)

  conn : First ν ρ ts e → First (m₀ ∷ᴬ ν) env tb mb → First ν ρ step (M′.side r β σ e)
  conn fs fb = by (hush? e) fs
    where
      shape : Shape (M′.ahead r β σ K (M′.before K mb))
      shape = ahead-split r β σ K
      by : e ≡ hush ⊎ e ≢ hush → First ν ρ ts e → First ν ρ step (M′.side r β σ e)
      by (inj₁ eq) fs′       = hushed eq fs′ fb
      by (inj₂ nh) (inj₁ ag) = subst (First ν ρ step) (sym (side-ahead r β σ e nh)) (told nh ag fb shape)
      by (inj₂ nh) (inj₂ pa) = subst (First ν ρ step) (sym (side-ahead r β σ e nh)) (preempted nh (proj₂ (pastᴱ-pos ν ρ ts e pa)) fb shape)

-- A rest-like's meaning starts with its step's event, else past a
-- running source's shown event.
first-rested : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (t : U.Node Γ A) (ρ : NEnv Γ) → Rested t → Firsts ν t ρ
first-rested ν (U.restᶜ n)       ρ _ = first-rest {ν = ν} n ρ
first-rested ν U.idleᶜ           ρ _ = inj₁ hush⁼
first-rested ν (U.unionᶜ x y)    ρ _ = first-union {ν = ν} x y ρ
first-rested ν (U.burstingᶜ r t) ρ _ = first-bursting {ν = ν} r t ρ
first-rested ν (U.underᶜ s b)    ρ _ = first-under {ν = ν} s b ρ

-- A node's meaning starts with the event its step shows, else past
-- a running source's shown event: a joiner's.
first : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ → Firsts ν c ρ
firstᴹ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴹ ν o → Placedᴹ o ρ → Firstᴹ ν o ρ
firstᴸ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴸ ν ls → Placedᴸ ls ρ → Firstᴸ ν ls ρ
first (U.framesᶜ τ e m)  ρ _ _ = inj₁ (agreeing (frames-after ρ τ e m) 1)
first (U.burstᶜ τ r i b) ρ _ _ = inj₁ (agreeing (burst-after ρ τ r i b) 1)
first (U.ofᶜ p i xs)     ρ _ _ = inj₁ (agreeing (of-after ρ p i xs) 1)
first {ν = ν} (U.mapᶜ f c) ρ sn (_ , pl) with first c ρ sn pl
... | inj₁ ag = inj₁ (one-map ρ f (U.step c) ag)
... | inj₂ pa = inj₂ (past-map ν ρ f (U.step c) (U.meaning c ρ) pa)
first {ν = ν} (U.scanᶜ f z c) ρ sn (_ , pl) with first c ρ sn pl
... | inj₁ ag = inj₁ (one-scan ρ f z (U.step c) ag)
... | inj₂ pa = inj₂ (past-scan ν ρ f z (U.step c) (U.meaning c ρ) pa)
first {ν = ν} (U.takeWhileᶜ i p c) ρ sn (_ , pl) with first c ρ sn pl
... | inj₁ ag = inj₁ (one-take ρ i p (U.step c) ag)
... | inj₂ pa = inj₂ (past-take ν ρ i p (U.step c) (U.meaning c ρ) pa)
first {ν = ν} (U.flatMapᶜ op g o ls qs pl) ρ (so , sl , _ , rp) (_ , po , pls , _) =
  flat-first op g o ls qs pl ρ (firstᴹ o ρ so po) (firstᴸ ls ρ sl pls) rp (first-rested ν pl ρ rp)
first {ν = ν} (U.joinᶜ i p xs e) ρ sn (_ , al) = first-join ν i p xs e ρ sn al
first {ν = ν} (U.connectᶜ r b (U.live s)) ρ (sb , ss) (_ , pb , ps , _) =
  Beside.conn ν runs r ρ (U.meaning s ρ) (U.meaning s ρ) (U.stateᴺ s ρ) (U.step s) (U.stateᴺ b (U.meaning s ρ ∷ᴬ ρ)) (U.step b)
    (U.bodyˢ r (U.live s)) (U.step (U.connectᶜ r b (U.live s))) (λ p → p) (head-body r (U.live s) (U.step b))
    (λ k → one-body ρ _ r (U.stateᴺ s ρ) k (U.live s) (U.step b)) (one-bodyˢ ρ _ r (U.live s) (U.step b))
    (source-hush r b (U.step b) s (U.step s)) (source-split r b (U.step b) s (U.step s))
    (first s ρ ss ps) (first b (U.meaning s ρ ∷ᴬ ρ) sb pb)
first {ν = ν} (U.connectᶜ r b (U.ended c t)) ρ (sb , rt) (_ , pb) =
  Beside.conn ν over r ρ (end c) (U.meaning t ρ) (U.stateᴺ t ρ) (U.step t) (U.stateᴺ b (end c ∷ᴬ ρ)) (U.step b)
    (U.shutˢᵗ r c t) (U.step (U.connectᶜ r b (U.ended c t))) inj₂ (head-shut r c t (U.step b))
    (λ k → one-shut ρ _ r (U.stateᴺ t ρ) k c t (U.step b)) (one-shutˢ ρ _ r c t (U.step b))
    (ended-hush r b (U.step b) c t (U.step t)) (ended-split r b (U.step b) c t (U.step t) (step-rested t rt))
    (first-rested ν t ρ rt) (first b (end c ∷ᴬ ρ) sb pb)
first {ν = ν} (U.deferᶜ l p ns) ρ _ pd = first-defer {ν = ν} l p ns ρ pd
first (U.endingᶜ p n)   ρ _ _ = inj₁ end⁼
first {ν = ν} (U.restᶜ n)       ρ _ _ = first-rest {ν = ν} n ρ
first U.idleᶜ           ρ _ _ = inj₁ hush⁼
first {ν = ν} (U.unionᶜ x y)    ρ _ _ = first-union {ν = ν} x y ρ
first {ν = ν} (U.burstingᶜ r t) ρ _ _ = first-bursting {ν = ν} r t ρ
first {ν = ν} (U.underᶜ s b)    ρ _ _ = first-under {ν = ν} s b ρ

firstᴹ nothing  ρ _  _  = tt
firstᴹ (just c) ρ sc pc = first c ρ sc pc

firstᴸ []       ρ _          _          = tt
firstᴸ (c ∷ cs) ρ (sc , ss) (pc , ps) = first c ρ sc pc , firstᴸ cs ρ ss ps

-- A node whose step shows past `k`, among sources showing nothing
-- before `k`, shows nothing before it.
floor : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) k → Sane ν c → Placed c ρ
      → U.beforeˢ k (U.step c) ≡ true → Floor ν k ρ → M′.before k (U.meaning c ρ) ≡ true
floor {ν = ν} c ρ k sn pl bs fl with first c ρ sn pl
... | inj₁ ag = trans (before-agree k ag) (trans (before-after ρ k (U.step c)) bs)
... | inj₂ pa = past-before ν ρ k (U.step c) (U.meaning c ρ) fl pa

-- A source's step shown first: the body fed it, its next event later.
module SourceFirst {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
                   (sb : Sane (runs ∷ᴬ ν) b) (pb : Placed b (U.meaning s ρ ∷ᴬ ρ)) where

  β : Events∞ B
  β = U.stateᴺ b (U.meaning s ρ ∷ᴬ ρ)

  σ : Events∞ A
  σ = U.stateᴺ s ρ

  -- What the source shows, as a state the connect can read.
  as : Events A → Events∞ A
  as e .force = e
  as e .cut   = U.cutᴺ s ρ

  as-alike : ∀ {e} → U.meaning s ρ ≃ e → ∀ d → Agreeˢ d σ (as e)
  as-alike al d = agreeᵀ-refl d _ ,ˢ agreeing al d

  -- The body's meaning shows after the source's shown step.
  body-floor : ∀ {e} k → U.meaning s ρ ≃ e → Floorᴱ k e → U.beforeˢ k (U.step b) ≡ true → Clear ν (just k) ρ
             → M′.before k (U.meaning b (U.meaning s ρ ∷ᴬ ρ)) ≡ true
  body-floor k al fe fb cl = floor b (U.meaning s ρ ∷ᴬ ρ) k sb pb fb (floorᴱ-agree (agreeing al 1) fe , clear-floor ν ρ cl)

  -- The connect reads its source's step at `q` as the source shows it.
  side-shows : ∀ q (a : Maybe A) (β₁ : Events∞ B) σ₁ d
             → Agree d (M′.beside r β₁ (as (shows q a σ₁))) (M′.ahead r β₁ (as (shows q a σ₁)) (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β₁)))
  side-shows q (just x) β₁ σ₁ d = agree-refl d _
  side-shows q nothing  β₁ σ₁ d = agree-refl d _

  -- Past the shown step, the connect runs on: the body as fed, the
  -- source from its next node.
  shown-next : ∀ q (a : Maybe A) (b″ : U.Node (A ∷ Γ) B) (s″ : U.Node Γ A) d
             → Agree d (M′.ahead r (U.stateᴺ b″ (U.meaning s″ ρ ∷ᴬ ρ)) (as (shows q a (U.stateᴺ s″ ρ))) (q ++ [ ix 0 ]) true)
                       (skip (q ++ [ ix 0 ]) (U.stateᴺ (U.connectᶜ r b″ (U.live s″)) ρ))
  shown-next q a        b″ s″ zero    = stop
  shown-next q (just x) b″ s″ (suc d) = skip⁼ (agreeᵀ-refl d _) (agree-refl d _)
  shown-next q nothing  b″ s″ (suc d) = skip⁼ (agreeᵀ-refl d _) (agree-refl d _)

  fed-first : ∀ q (a : Maybe A) (s′ : U.Node Γ A) → U.meaning s ρ ≃ shows q a (U.stateᴺ s′ ρ)
            → U.beforeˢ (q ++ [ ix 0 ]) (U.step b) ≡ true → Clear ν (just (q ++ [ ix 0 ])) ρ
            → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ skip (q ++ [ ix 0 ]) (U.stateᴺ (U.connectᶜ r (U.feed (here refl) q a b) (U.live s′)) ρ)
  fed-first q a s′ al fb cl = alike λ d → agree-trans (beside-ne r (fa d) (as-alike al d)) (top d)
    where
      σ′ = U.stateᴺ s′ ρ
      b′ = U.feed (here refl) q a b
      β′ = U.stateᴺ b′ (U.meaning s′ ρ ∷ᴬ ρ)
      k  = q ++ [ ix 0 ]
      fa = feed-alike b q a σ′ ρ sb al
      flag : M′.before k (U.meaning b′ (U.meaning s′ ρ ∷ᴬ ρ)) ≡ true
      flag = trans (sym (before-agree k (nowˢ (fa 1)))) (body-floor k al (shown a) fb cl)
        where shown : ∀ a → Floorᴱ k (shows q a σ′)
              shown (just _) = <ᵖ-irrefl k
              shown nothing  = <ᵖ-irrefl k
      target = skip k (U.stateᴺ (U.connectᶜ r b′ (U.live s′)) ρ)
      top : ∀ d → Agree d (M′.beside r β′ (as (shows q a σ′))) target
      top d = agree-trans (side-shows q a β′ σ′ d) (subst (λ f → Agree d (M′.ahead r β′ (as (shows q a σ′)) k f) target) (sym flag) (shown-next q a b′ s′ d))

  shut-first : ∀ c → U.meaning s ρ ≃ end c → U.beforeˢ (c ++ [ ix 0 ]) (U.step b) ≡ true → Clear ν (just (c ++ [ ix 0 ])) ρ
             → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ skip (c ++ [ ix 0 ]) (U.stateᴺ (U.connectᶜ r (U.shut (here refl) c b) (U.ended c (U.restᶜ s))) ρ)
  shut-first c al fb cl = alike λ d → agree-trans (beside-ne r (sa d) (as-alike al d)) (top d)
    where
      b′ = U.shut (here refl) c b
      β′ = U.stateᴺ b′ (end c ∷ᴬ ρ)
      k  = c ++ [ ix 0 ]
      sa = shut-alike b c ρ sb al
      flag : M′.before k (U.meaning b′ (end c ∷ᴬ ρ)) ≡ true
      flag = trans (sym (before-agree k (nowˢ (sa 1)))) (body-floor k al (<ᵖ-irrefl k) fb cl)
      target = skip k (U.stateᴺ (U.connectᶜ r b′ (U.ended c (U.restᶜ s))) ρ)
      -- Past its end the source runs on as its rest.
      next : ∀ d → Agree d (M′.ahead r β′ (as (end c)) k true) target
      rest : ∀ d → Agreeˢ d (M′.onward∞ (as (end c)) (end c)) (U.stateᴺ (U.restᶜ s) ρ)
      rest d = agreeᵀ-refl d _ ,ˢ agree-refl d _
      next zero    = stop
      next (suc d) = skip⁼ (∪-ne (burstOn-ne r (rest d)) (agreeᵀ-refl d _)) (beside-ne r (agreeᵀ-refl d _ ,ˢ agree-refl d _) (rest d))
      top : ∀ d → Agree d (M′.beside r β′ (as (end c))) target
      top d = subst (λ f → Agree d (M′.ahead r β′ (as (end c)) k f) target) (sym flag) (next d)

-- The body's step shown first: the connect shows it, the source carried.
module BodyFirst {Γ A B} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ) where

  env : NEnv (A ∷ Γ)
  env = U.meaning s ρ ∷ᴬ ρ

  β : Events∞ B
  β = U.stateᴺ b env

  σ : Events∞ A
  σ = U.stateᴺ s ρ

  onward : ∀ {e} → U.meaning s ρ ≡ e → ∀ K → (∀ (β′ : Events∞ B) → M′.side r β′ σ e ≡ M′.ahead r β′ σ K (M′.before K (force β′)))
         → ∀ (b′ : U.Node (A ∷ Γ) B) d
         → Agree d (M′.ahead r (U.stateᴺ b′ env) σ K (M′.before K (U.meaning b′ env))) (M′.side r (U.stateᴺ b′ env) σ (U.meaning s ρ))
  onward eq K sd b′ d = subst (λ x → Agree d _ (M′.side r (U.stateᴺ b′ env) σ x)) (sym eq) (subst (Agree d _) (sym (sd (U.stateᴺ b′ env))) (agree-refl d _))

  -- The body's step, run beside the source as the connect runs it.
  past : ∀ {e} → U.meaning s ρ ≡ e → ∀ K → (∀ (β′ : Events∞ B) → M′.side r β′ σ e ≡ M′.ahead r β′ σ K (M′.before K (force β′)))
       → ∀ t d → Agree (suc d) (M′.body r σ K (afterᴱ env t)) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  past eq K sd (U.outˢ k a b′) d = out⁼ (agreeᵀ-refl d _) (onward eq K sd b′ d)
  past eq K sd (U.skipˢ k b′)  d = skip⁼ (agreeᵀ-refl d _) (onward eq K sd b′ d)
  past eq K sd (U.endˢ c)      d = end⁼
  past eq K sd U.hushˢ         d = hush⁼

  -- The source showing at `K`, past the body's step.
  shown : ∀ {e} → U.meaning s ρ ≡ e → ∀ K → (∀ (β′ : Events∞ B) → M′.side r β′ σ e ≡ M′.ahead r β′ σ K (M′.before K (force β′)))
        → ∀ t → U.meaning b env ≃ afterᴱ env t → M′.before K (U.meaning b env) ≡ false
        → ∀ d → Agree d (M′.side r β σ e) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  shown eq K sd t al fl zero    = stop
  shown eq K sd t al fl (suc d) =
    subst (λ x → Agree (suc d) x _) (sym (sd β))
      (subst (λ f → Agree (suc d) (M′.ahead r β σ K f) _) (sym fl)
        (agree-trans (body-ne r (agreeᵀ-refl (suc d) _ ,ˢ agree-refl (suc d) _) (agreeing al (suc d))) (past eq K sd t d)))

  left : U.meaning s ρ ≡ hush → (∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle) → ∀ (b′ : U.Node (A ∷ Γ) B) d
       → Agreeᵀ d (U.cutᴺ b′ env) (M′.burstOn r σ ∪ U.cutᴺ b′ env)
  left eq hc b′ d = subst (λ x → Agreeᵀ d (U.cutᴺ b′ env) (M′.runOn r x (U.cutᴺ s ρ) ∪ U.cutᴺ b′ env)) (sym eq)
                      (agreeᵀ-sym (∪-ne (hc d) (agreeᵀ-refl d _)))

  kept-side : U.meaning s ρ ≡ hush → ∀ (b′ : U.Node (A ∷ Γ) B) d → Agree d (U.meaning b′ env) (M′.side r (U.stateᴺ b′ env) σ (U.meaning s ρ))
  kept-side eq b′ d = subst (λ x → Agree d (U.meaning b′ env) (M′.side r (U.stateᴺ b′ env) σ x)) (sym eq) (agree-refl d _)

  -- The source hushed: the connect is its body, nothing left running.
  hushed : U.meaning s ρ ≡ hush → (∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle)
         → ∀ t → U.meaning b env ≃ afterᴱ env t → ∀ d → Agree d (U.meaning b env) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  hushed eq hc t al zero = stop
  hushed eq hc (U.outˢ k a b′) al (suc d) = agree-trans (agreeing al (suc d)) (out⁼ (left eq hc b′ d) (kept-side eq b′ d))
  hushed eq hc (U.skipˢ k b′)  al (suc d) = agree-trans (agreeing al (suc d)) (skip⁼ (left eq hc b′ d) (kept-side eq b′ d))
  hushed eq hc (U.endˢ c)      al (suc d) = agreeing al (suc d)
  hushed eq hc U.hushˢ         al (suc d) = agreeing al (suc d)

  -- The source shown at `e`: hushed, or past the body's step.
  main : ∀ t (e : Events A) → U.meaning s ρ ≡ e → U.meaning b env ≃ afterᴱ env t → Clearᴱ (U.headˢ t) e
       → (U.meaning s ρ ≡ hush → ∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle)
       → ∀ d → Agree d (M′.side r β σ e) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  main t      hush         eq al ce hc d = hushed eq (hc eq) t al d
  main U.hushˢ (out _ _ _) eq al () hc d
  main U.hushˢ (skip _ _)  eq al () hc d
  main U.hushˢ (end _)     eq al () hc d
  main t@(U.outˢ k a b′) (out q x τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.outˢ k a b′) (skip q τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.outˢ k a b′) (end q) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.skipˢ k b′) (out q x τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.skipˢ k b′) (skip q τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.skipˢ k b′) (end q) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.endˢ k) (out q x τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.endˢ k) (skip q τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.endˢ k) (end q) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d

-- Of no step, a step hushed.
head-none : ∀ {Γ A} (t : U.Step Γ A) → U.headˢ t ≡ nothing → t ≡ U.hushˢ
head-none U.hushˢ refl = refl

-- A meaning showing nothing before `k` shows past `k`.
shown-past : ∀ {A} k (e : Events A) → M′.before k e ≡ true → Clearᴱ (just k) e
shown-past k hush        h = tt
shown-past k (out q a σ) h = <ᵖ-trans k q (q ++ [ ix 0 ]) h (<ᵖ-below q [])
shown-past k (skip q σ)  h = <ᵖ-trans k q (q ++ [ ix 0 ]) h (<ᵖ-below q [])
shown-past k (end c)     h = <ᵖ-trans k c (c ++ [ ix 0 ]) h (<ᵖ-below c [])

-- A hushed body beside a source whose step is hushed too.
quiet : ∀ {Δ Γ A C} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Skips ν s ρ → Clear ν nothing ρ
      → ∀ t → U.step s ≡ t → Shy {Δ = Δ} {B = C} U.hushˢ t → Clearᴱ nothing (U.meaning s ρ)
quiet {ν = ν} s ρ sks cl U.hushˢ es _ =
  subst (Clearᴱ nothing) (sym (agreed (agreeing (sks (subst (λ t → Clear ν (U.headˢ t) ρ) (sym es) cl)) 1) es)) tt
  where agreed : ∀ {x} → Agree 1 x (afterᴱ ρ (U.step s)) → U.step s ≡ U.hushˢ → x ≡ hush
        agreed a e with U.step s | e
        agreed hush⁼ e | .U.hushˢ | refl = refl
quiet s ρ sks cl (U.outˢ q a s′) es ()
quiet s ρ sks cl (U.skipˢ q s′)  es ()
quiet s ρ sks cl (U.endˢ c)      es ()

-- Not past just beyond `q`, and neither `q` nor just beyond it: before
-- `q`.
shy-order : ∀ q k → (q ++ [ ix 0 ]) <ᵖ k ≡ false → k ≢ q → k ≢ q ++ [ ix 0 ] → k <ᵖ q ≡ true
shy-order q k f n₀ n₁ with <ᵖ-split k (q ++ [ ix 0 ]) f
... | inj₂ e = ⊥-elim (n₁ e)
... | inj₁ lt with k <ᵖ q in kq
...   | true  = refl
...   | false with <ᵖ-split q k kq
...     | inj₂ refl = ⊥-elim (n₀ refl)
...     | inj₁ qk with trans (sym lt) (<ᵖ-step q k qk)
...       | ()

head-before : ∀ {Γ B} x k (sb : U.Step Γ B) → U.headˢ sb ≡ just k → U.beforeˢ x sb ≡ x <ᵖ k
head-before x k (U.outˢ _ _ _) refl = refl
head-before x k (U.skipˢ _ _)  refl = refl
head-before x k (U.endˢ _)     refl = refl
head-before x k U.hushˢ        ()

-- Apart from its source's step and where that shows, a shy body steps
-- strictly before it.
shy-at : ∀ {Δ Γ A B} k (sb : U.Step Δ B) (t : U.Step Γ A) → U.headˢ sb ≡ just k → Shy sb t
       → (∀ q → U.headˢ t ≡ just q → k ≢ q × k ≢ q ++ [ ix 0 ]) → U.beforeˢ k t ≡ true
shy-at k sb (U.outˢ q _ _) hb shy ap = shy-order q k (trans (sym (head-before (q ++ [ ix 0 ]) k sb hb)) shy) (proj₁ (ap q refl)) (proj₂ (ap q refl))
shy-at k sb (U.skipˢ q _)  hb shy ap = shy-order q k (trans (sym (head-before (q ++ [ ix 0 ]) k sb hb)) shy) (proj₁ (ap q refl)) (proj₂ (ap q refl))
shy-at k sb (U.endˢ c)     hb shy ap = shy-order c k (trans (sym (head-before (c ++ [ ix 0 ]) k sb hb)) shy) (proj₁ (ap c refl)) (proj₂ (ap c refl))
shy-at k sb U.hushˢ        hb shy ap = refl

-- A connect's body stepping no later than its source's step, among
-- sources clear of the body's step: the source's meaning shows past it.
shy-clear : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
          → Sane ν s → Placed s ρ → Sides (U.step b) (U.step s) → Skips ν s ρ → Shy (U.step b) (U.step s)
          → Clear ν (U.headˢ (U.step b)) ρ → Clearᴱ (U.headˢ (U.step b)) (U.meaning s ρ)
shy-clear {ν = ν} b s ρ ss ps sd sks shy cl with U.headˢ (U.step b) in hb
... | just k  = shown-past k (U.meaning s ρ) (floor s ρ k ss ps (shy-at k (U.step b) (U.step s) hb shy (λ q → sd k q refl)) (clear-floor ν ρ cl))
... | nothing = quiet {ν = ν} s ρ sks cl (U.step s) refl (subst (λ t → Shy t (U.step s)) (head-none (U.step b) hb) shy)

-- A tail run silent is idle.
tail-hush : ∀ {A} (t : Tail) → M′.tailᴱ {A} t ≡ hush → t ≡ idle
tail-hush (pin k r) ()
tail-hush idle      _ = refl

map-hush : ∀ {A B} (f : A → B) (x : Events A) → M′.mapᴱ f x ≡ hush → x ≡ hush
map-hush f (out k a r) ()
map-hush f (skip k r)  ()
map-hush f (end k)     ()
map-hush f hush        _ = refl

scan-hush : ∀ {A B} (f : B → A → B) z (x : Events A) → M′.scanᴱ f z x ≡ hush → x ≡ hush
scan-hush f z (out k a r) ()
scan-hush f z (skip k r)  ()
scan-hush f z (end k)     ()
scan-hush f z hush        _ = refl

taking-loud : ∀ {A} i (p : A → Bool) k a b r → M′.taking i p k a b r ≢ hush
taking-loud i     p k a true  r ()
taking-loud true  p k a false r ()
taking-loud false p k a false r ()

take-hush : ∀ {A} i (p : A → Bool) (x : Events A) → M′.takeWhileᴱ i p x ≡ hush → x ≡ hush
take-hush i p (out k a r) eq = ⊥-elim (taking-loud i p k a (p a) r eq)
take-hush i p (skip k r)  ()
take-hush i p (end k)     ()
take-hush i p hush        _ = refl

body-loud : ∀ {A B} r (σ : Events∞ A) q (y : Events B) → y ≢ hush → M′.body r σ q y ≢ hush
body-loud r σ q (out k a β) nh ()
body-loud r σ q (skip k β)  nh ()
body-loud r σ q (end c)     nh ()
body-loud r σ q hush        nh _ = nh refl

skip-loud : ∀ {A} k (τ : Events∞ A) → skip k τ ≢ hush
skip-loud k τ ()

-- A connect silent: its source silent, and its body.
side-hush : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) (x : Events A) → M′.side r β σ x ≡ hush → x ≡ hush × force β ≡ hush
side-hush r β σ x eq with hush? x
... | inj₁ ex = ex , subst (λ y → M′.side r β σ y ≡ hush) ex eq
... | inj₂ nx with ahead-split r β σ (M′.shownAt x)
...   | inj₁ (bt , τ , ea) = ⊥-elim (skip-loud _ τ (trans (sym ea) (trans (sym (side-ahead r β σ x nx)) eq)))
...   | inj₂ (bf , ea)     = ⊥-elim (body-loud r σ _ (force β) (before-false _ (force β) bf) (trans (sym ea) (trans (sym (side-ahead r β σ x nx)) eq)))

run-hush : ∀ {A} r (x : Events A) t → x ≡ hush → M′.runOn r x t ≡ t
run-hush r .hush t refl = refl

idle-∪ : ∀ {t u} → t ≡ idle → u ≡ idle → t ∪ u ≡ idle
idle-∪ refl refl = refl

head-hush : ∀ {A} (x : Events A) → M′.head x ≡ nothing → x ≡ hush
head-hush (out k a r) ()
head-hush (skip k r)  ()
head-hush (end k)     ()
head-hush hush        _ = refl

earliest-none : ∀ {B} (ls : List (Events∞ B)) → M′.earliest ls ≡ M′.none → All (λ l → M′.head (force l) ≡ nothing) ls
earliest-none []       _ = []ᴬ
earliest-none (l ∷ ls) with M′.head (force l) in hl | M′.earliest ls in el
... | nothing | M′.none           = λ _ → hl ∷ᴬ earliest-none ls el
... | nothing | M′.found _ _ _ _  = λ ()
... | just k  | M′.none           = λ ()
... | just k  | M′.found k′ _ _ _ with k <ᵖ k′
...   | true  = λ ()
...   | false = λ ()

outer-hush : ∀ {B} op (e : Events∞ (M′.MonotonicList B)) ls qs t (x : Events (M′.MonotonicList B)) → M′.outer op e ls qs t x ≡ hush → x ≡ hush
outer-hush op e ls qs t (out q m r) with M′.admit op (q ++ [ ix 1 ]) m ls qs
... | _ , _ , _ = λ ()
outer-hush op e ls       qs       t (skip q r) ()
outer-hush op e []       []       t (end c)    ()
outer-hush op e []       (m ∷ qs) t (end c)    ()
outer-hush op e (l ∷ ls) qs       t (end c)    ()
outer-hush op e ls       qs       t hush       _ = refl

lane-hush : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) bs l as qs t (x : Events B) → M′.lane op o bs l as qs t x ≡ hush → x ≡ hush
lane-hush op o        bs       l as       qs       t (out k b r) ()
lane-hush op o        bs       l as       qs       t (skip k r)  ()
lane-hush op o        bs       l as       (m ∷ qs) t (end c)     ()
lane-hush op nothing  []       l []       []       t (end c)     ()
lane-hush op nothing  []       l (a ∷ as) []       t (end c)     ()
lane-hush op nothing  (b ∷ bs) l as       []       t (end c)     ()
lane-hush op (just e) bs       l as       []       t (end c)     ()
lane-hush op o        bs       l as       qs       t hush        _ = refl

just-loud : ∀ {A} (x : Events A) {k} → M′.head x ≡ just k → x ≢ hush
just-loud (out k a r) _ ()
just-loud (skip k r)  _ ()
just-loud (end k)     _ ()
just-loud hush        () _

race-loud : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) k bs (l : Events∞ B) as qs t
          → M′.head (force l) ≡ just k → M′.race op o k bs l as qs t ≢ hush
race-loud op nothing  k bs l as qs t hl eq = just-loud (force l) hl (lane-hush op nothing bs l as qs t (force l) eq)
race-loud op (just e) k bs l as qs t hl with M′.head (force e) in he
... | nothing = λ eq → just-loud (force l) hl (lane-hush op (just e) bs l as qs t (force l) eq)
... | just k′ with k′ <ᵖ k
...   | true  = λ eq → just-loud (force e) he (outer-hush op e (bs ++ l ∷ as) qs t (force e) eq)
...   | false = λ eq → just-loud (force l) hl (lane-hush op (just e) bs l as qs t (force l) eq)

parts-hush : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) ls qs t → M′.parts op o ls qs t ≡ hush
           → M′.headᴼ o ≡ nothing × All (λ l → M′.head (force l) ≡ nothing) ls
parts-hush op o ls qs t with M′.earliest ls in el
... | M′.found k bs l as = λ eq → ⊥-elim (race-loud op o k bs l as qs t (earliest-found ls el) eq)
... | M′.none with o
...   | nothing = λ _ → refl , earliest-none ls el
...   | just e  = λ eq → cong M′.head (outer-hush op e ls qs t (force e) eq) , earliest-none ls el

-- A flatMap's run silent: nothing its ended parts left, its outer gone
-- or silent, and every lane silent.
go-hush : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) ls qs t → M′.go op o ls qs t ≡ hush
        → t ≡ idle × M′.headᴼ o ≡ nothing × All (λ l → M′.head (force l) ≡ nothing) ls
go-hush op o ls qs idle      eq = refl , parts-hush op o ls qs idle eq
go-hush op o ls qs (pin k u) with M′.ahead-of k o ls in ah
... | true  = λ ()
... | false = λ eq → ⊥-elim (bool-split (trans (sym ah) (uncurry (ahead-quiet k o ls) (parts-hush op o ls qs (pin k u) eq))))
  where bool-split : false ≡ true → ⊥
        bool-split ()

-- A rest-like that never shows again leaves nothing running.
rested-idle : ∀ {Γ A} (t : U.Node Γ A) (ρ : NEnv Γ) → Rested t → U.meaning t ρ ≡ hush → U.cutᴺ t ρ ≡ idle
rested-idle (U.restᶜ n)               ρ _ eq = tail-hush _ eq
rested-idle U.idleᶜ                   ρ _ _  = refl
rested-idle (U.unionᶜ x y)            ρ _ eq = tail-hush _ eq
rested-idle (U.burstingᶜ r t)         ρ _ eq = tail-hush _ eq
rested-idle (U.underᶜ (U.live s) b)   ρ _ eq = tail-hush _ eq
rested-idle (U.underᶜ (U.ended c t) b) ρ _ eq = tail-hush _ eq
rested-idle (U.framesᶜ τ e m)            ρ () _
rested-idle (U.burstᶜ τ r k f)           ρ () _
rested-idle (U.ofᶜ p k xs)               ρ () _
rested-idle (U.mapᶜ f c)                 ρ () _
rested-idle (U.scanᶜ f z c)              ρ () _
rested-idle (U.takeWhileᶜ k p c)         ρ () _
rested-idle (U.flatMapᶜ op g o ls qs pl) ρ () _
rested-idle (U.joinᶜ j p xs e)           ρ () _
rested-idle (U.connectᶜ r b s)           ρ () _
rested-idle (U.deferᶜ l p ns)            ρ () _
rested-idle (U.endingᶜ p n)              ρ () _

-- A node that never shows again leaves nothing running when cut.
mutual
  cut-idle : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Sane ν s → Placed s ρ
           → U.meaning s ρ ≡ hush → U.cutᴺ s ρ ≡ idle
  cut-idle (U.framesᶜ τ e m)  ρ _ _ _ = refl
  cut-idle (U.burstᶜ τ r i b) ρ _ _ _ = refl
  cut-idle (U.ofᶜ p i xs)     ρ _ _ _ = refl
  cut-idle (U.mapᶜ f c)         ρ sn (_ , pl) eq = cut-idle c ρ sn pl (map-hush f _ eq)
  cut-idle (U.scanᶜ f z c)      ρ sn (_ , pl) eq = cut-idle c ρ sn pl (scan-hush f z _ eq)
  cut-idle (U.takeWhileᶜ i p c) ρ sn (_ , pl) eq = cut-idle c ρ sn pl (take-hush i p _ eq)
  cut-idle (U.flatMapᶜ op g o ls qs pl) ρ (so , sl , _) (_ , po , pls , _) eq
    with go-hush _ (U.outerᴺ g o ρ) (U.states ls ρ) _ (U.cutᴺ pl ρ) eq
  ... | te , ho , hl = idle-∪ (cut-idleᴼ g o ρ so po ho) (idle-∪ (cut-idleᴸ ls ρ sl pls hl) te)
  cut-idle (U.joinᶜ i p xs e) ρ _ _ _ = refl
  cut-idle (U.connectᶜ r b (U.live s)) ρ (sb , ss) (_ , pb , ps , _) eq with side-hush r (U.stateᴺ b (U.meaning s ρ ∷ᴬ ρ)) (U.stateᴺ s ρ) (U.meaning s ρ) eq
  ... | es , eb = idle-∪ (trans (run-hush r _ _ es) (cut-idle s ρ ss ps es)) (cut-idle b _ sb pb eb)
  cut-idle (U.connectᶜ r b (U.ended c t)) ρ (sb , rt) (_ , pb) eq with side-hush r (U.stateᴺ b (end c ∷ᴬ ρ)) (U.stateᴺ t ρ) (U.meaning t ρ) eq
  ... | et , eb = idle-∪ (trans (run-hush r _ _ et) (rested-idle t ρ rt et)) (cut-idle b _ sb pb eb)
  cut-idle (U.deferᶜ l p ns)  ρ _ _ _ = refl
  cut-idle (U.endingᶜ p n)    ρ _ _ ()
  cut-idle (U.restᶜ n)        ρ _ _ eq = rested-idle (U.restᶜ n) ρ tt eq
  cut-idle U.idleᶜ            ρ _ _ _  = refl
  cut-idle (U.unionᶜ x y)     ρ _ _ eq = rested-idle (U.unionᶜ x y) ρ tt eq
  cut-idle (U.burstingᶜ r t)  ρ _ _ eq = rested-idle (U.burstingᶜ r t) ρ tt eq
  cut-idle (U.underᶜ s b)     ρ _ _ eq = rested-idle (U.underᶜ s b) ρ tt eq

  cut-idleᴼ : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴹ ν o → Placedᴹ o ρ
            → M′.headᴼ (U.outerᴺ g o ρ) ≡ nothing → M′.cutᴼ (U.outerᴺ g o ρ) ≡ idle
  cut-idleᴼ g nothing  ρ _ _ _  = refl
  cut-idleᴼ g (just c) ρ s p ho = cut-idle c ρ s p (map-hush _ (U.meaning c ρ) (head-hush _ ho))

  cut-idleᴸ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴸ ν ls → Placedᴸ ls ρ
            → All (λ l → M′.head (force l) ≡ nothing) (U.states ls ρ) → M′.cuts (U.states ls ρ) ≡ idle
  cut-idleᴸ []       ρ _        _        _          = refl
  cut-idleᴸ (c ∷ cs) ρ (s , ss) (p , ps) (h ∷ᴬ hs) = idle-∪ (cut-idle c ρ s p (head-hush _ h)) (cut-idleᴸ cs ρ ss ps hs)

hushed-cut : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Sane ν s → Placed s ρ
           → U.meaning s ρ ≡ hush → ∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle
hushed-cut s ρ ss ps eq d = subst (λ t → Agreeᵀ d t idle) (sym (cut-idle s ρ ss ps eq)) (agreeᵀ-refl d idle)

-- A connect's body showing first: what it shows, the source carried.
body-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
           → Sane ν s → Placed s ρ → Sides (U.step b) (U.step s)
           → Skips (runs ∷ᴬ ν) b (U.meaning s ρ ∷ᴬ ρ) → Skips ν s ρ → Shy (U.step b) (U.step s)
           → Clear ν (U.headˢ (U.bodyˢ r (U.live s) (U.step b))) ρ
           → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ afterᴱ ρ (U.bodyˢ r (U.live s) (U.step b))
body-skips {ν = ν} r b s ρ ss ps sd skb sks shy cl =
  alike (BodyFirst.main r b s ρ (U.step b) (U.meaning s ρ) refl (skb (ce , cl′)) ce (λ eq → hushed-cut s ρ ss ps eq))
  where cl′ = subst (λ h → Clear ν h ρ) (head-body r (U.live s) (U.step b)) cl
        ce  = shy-clear b s ρ ss ps sd sks shy cl′

-- A node's skips, read off its step.
back : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {s : U.Node Γ A} {ρ : NEnv Γ} {t} → U.step s ≡ t
     → (Clear ν (U.headˢ t) ρ → U.meaning s ρ ≃ afterᴱ ρ t) → Skips ν s ρ
back refl k = k

-- A connect runs its source's step first when it shows before the
-- body's, the body fed it; else the body's.
connect-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
              → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ
              → Skips (runs ∷ᴬ ν) b (U.meaning s ρ ∷ᴬ ρ) → Skips ν s ρ → Skips ν (U.connectᶜ r b (U.live s)) ρ
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl with U.step s in es
... | U.outˢ q a s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.fed-first r b s ρ sb (proj₁ (proj₂ pl)) q (just a) s′ (sks (clear-lower ν ρ (<ᵖ-below q []) cl)) fb cl
...   | false = body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (apart-sides r b s ρ (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.skipˢ q s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.fed-first r b s ρ sb (proj₁ (proj₂ pl)) q nothing s′ (sks (clear-lower ν ρ (<ᵖ-below q []) cl)) fb cl
...   | false = body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (apart-sides r b s ρ (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.endˢ c with U.beforeˢ (c ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.shut-first r b s ρ sb (proj₁ (proj₂ pl)) c (sks (clear-lower ν ρ (<ᵖ-below c []) cl)) fb cl
...   | false = body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (apart-sides r b s ρ (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.hushˢ =
  body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (apart-sides r b s ρ (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) tt) cl

-- Node by node, each part stepping as it does alone.
--
-- REFUTED: 3e2af71f stated of every node, by a told joiner under a live source
-- REFUTED: 082ad778 stated without the body sane, by a joiner told its end
mutual
  skips : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ → Skips ν c ρ
  skips (U.framesᶜ τ e m)  ρ _ _ _ = frames-after ρ τ e m
  skips (U.burstᶜ τ r i b) ρ _ _ _ = burst-after ρ τ r i b
  skips (U.ofᶜ p i xs)     ρ _ _ _ = of-after ρ p i xs
  skips {ν = ν} (U.mapᶜ f c) ρ sn (_ , pl) cl =
    after-map ρ f (U.step c) (skips c ρ sn pl (subst (λ h → Clear ν h ρ) (head-map f (U.step c)) cl))
  skips {ν = ν} (U.scanᶜ f z c) ρ sn (_ , pl) cl =
    after-scan ρ f z (U.step c) (skips c ρ sn pl (subst (λ h → Clear ν h ρ) (head-scan f z (U.step c)) cl))
  skips {ν = ν} (U.takeWhileᶜ i p c) ρ sn (_ , pl) cl = after-take ρ i p (U.step c) (skips c ρ sn pl (clear-take {ν = ν} {ρ = ρ} i p (U.step c) cl))
  skips (U.flatMapᶜ op g o ls qs pl) ρ sn@(so , sl , _) pd@(_ , po , pls , _) cl =
    flat-skips op g o ls qs pl ρ sn pd (skipsᴹ o ρ so po) (skipsᴸ ls ρ sl pls) cl
  skips {ν = ν} (U.joinᶜ i p xs e) ρ sn _ cl = join-skips {ν = ν} i p xs e ρ sn cl
  skips (U.connectᶜ r b (U.live s)) ρ sn@(sb , ss) pd@(_ , pb , ps , _) cl =
    connect-skips r b s ρ sn pd (skips b (U.meaning s ρ ∷ᴬ ρ) sb pb) (skips s ρ ss ps) cl
  skips (U.connectᶜ r b (U.ended c t)) ρ sn@(sb , _) pd@(_ , pb) cl = ended-skips r b c t ρ sn pd (skips b (end c ∷ᴬ ρ) sb pb) cl
  skips {ν = ν} (U.deferᶜ l p ns) ρ _ pd cl = defer-skips {ν = ν} l p ns ρ pd cl
  skips (U.endingᶜ p n)   ρ _ _ _  = alike λ d → agree-refl d (end p)
  skips {ν = ν} (U.restᶜ n)       ρ _ _ cl = rest-skips {ν = ν} n ρ cl
  skips U.idleᶜ           ρ _ _ _  = alike λ d → agree-refl d hush
  skips {ν = ν} (U.unionᶜ x y)    ρ _ _ cl = union-skips {ν = ν} x y ρ cl
  skips {ν = ν} (U.burstingᶜ r t) ρ _ _ cl = bursting-skips {ν = ν} r t ρ cl
  skips {ν = ν} (U.underᶜ s b)    ρ _ _ cl = under-skips {ν = ν} s b ρ cl

  skipsᴹ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴹ ν o → Placedᴹ o ρ → Skipsᴹ ν o ρ
  skipsᴹ nothing  ρ _ _ = tt
  skipsᴹ (just c) ρ s p = skips c ρ s p

  skipsᴸ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴸ ν ls → Placedᴸ ls ρ → Skipsᴸ ν ls ρ
  skipsᴸ []       ρ _        _        = tt
  skipsᴸ (c ∷ cs) ρ (s , ss) (p , ps) = skips c ρ s p , skipsᴸ cs ρ ss ps

-- THE STEPPER IS THE MEANING, skips included: at the root no source is
-- in scope to show first.
step-skips : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → U.meaning g []ᴬ ≃ afterᴱ []ᴬ (U.step g)
step-skips g sn pl = skips g []ᴬ sn pl tt
