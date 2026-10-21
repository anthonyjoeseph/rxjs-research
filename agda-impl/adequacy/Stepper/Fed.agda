{-# OPTIONS --guardedness #-}

-- A FED NODE STAYS PLACED: a node placed reading its sources, fed a
-- running source's step and read past it, is placed.  Its meaning runs
-- alike (`feed-alikeⁱ`), so stays in order; a joiner's source and a
-- connect's scope run on from what they kept, so stay alien; a connect's
-- body keeps its key, fed where every key holds, and its source keeps
-- its own, the step alien to the body's region; a lane yet to subscribe
-- is reached alike.
module adequacy.Stepper.Fed where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Events∞; Pos; ix)
open import denotation.MonotonicList using (agree-refl; agree-sym)
open import denotation.NonExpansive using (Agreeˢ)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Saneᴹ; Saneᴸ; Mode; runs; allLive)
open import adequacy.Placed.Order using (Alienᴱ; Every; Everyᴱ; Placed; Placedᴸ; Placedᴹ; Sorted; Within; every)
open import adequacy.Placed.Keys using (ordered-≈; every-≈)
open import adequacy.Placed.Rising using (apart-join)
open import adequacy.Placed.Heads using (apart-closed; feed-keyed; owned-closed; owned-fit)
open import adequacy.Env using (everyᴱ-agree; lookup-ne; reaches-agree)
open import adequacy.Stepper.Past using (_≃_; alike; shows)
open import adequacy.Stepper.Parts using (Fed; fed-here; fed-there; feed-alikeⁱ)

open _≃_
open Agreeˢ using (nowˢ)
open Events∞

-- What a source showing a step keeps, its step and what follows.
every-shows : ∀ {A} {P : Pos → Set} q (a : Maybe A) (σ : Events∞ A) → Every P (shows q a σ) → P q × Every P (force σ)
every-shows q (just _) σ pe = proj₁ (every pe) , proj₁ (proj₂ (every pe))
every-shows q nothing  σ pe = proj₁ (every pe) , proj₁ (proj₂ (every pe))

-- Past a source's step, each source keeps what it kept at every step.
fed-every : ∀ {Γ A C} {P : Pos → Set} {q} {a : Maybe A} {i : A ∈ Γ} {ρ ρ′ : NEnv Γ}
          → Fed q a i ρ ρ′ → (j : C ∈ Γ) → Every P (lookup ρ j) → Every P (lookup ρ′ j)
fed-every {q = q} {a} (fed-here σ al S) (here refl) pe = proj₂ (every-shows q a σ (every-≈ _ _ (agreeing al) pe))
fed-every (fed-here σ al S) (there j)   pe = every-≈ _ _ (λ m → lookup-ne (S m) j) pe
fed-every (fed-there al fd) (here refl) pe = every-≈ _ _ (agreeing al) pe
fed-every (fed-there al fd) (there j)   pe = fed-every fd j pe

fed-everyᴱ : ∀ {Γ A} {P : Pos → Set} {q} {a : Maybe A} {i : A ∈ Γ} {ρ ρ′ : NEnv Γ} → Fed q a i ρ ρ′ → Everyᴱ P ρ → Everyᴱ P ρ′
fed-everyᴱ {q = q} {a} (fed-here σ al S) (pe , pρ) =
  proj₂ (every-shows q a σ (every-≈ _ _ (agreeing al) pe)) , everyᴱ-agree S pρ
fed-everyᴱ (fed-there al fd) (pe , pρ) = every-≈ _ _ (agreeing al) pe , fed-everyᴱ fd pρ

-- The step itself, where every source keeps it.
fed-at : ∀ {Γ A} {P : Pos → Set} {q} {a : Maybe A} {i : A ∈ Γ} {ρ ρ′ : NEnv Γ} → Fed q a i ρ ρ′ → Everyᴱ P ρ → P q
fed-at {q = q} {a} (fed-here σ al S) (pe , _) = proj₁ (every-shows q a σ (every-≈ _ _ (agreeing al) pe))
fed-at (fed-there al fd) (_ , pρ) = fed-at fd pρ

lookup-live : ∀ {Γ A} (i : A ∈ Γ) → lookup (allLive Γ) i ≡ runs
lookup-live (here refl) = refl
lookup-live (there i)   = lookup-live i

postulate
  -- A defer's sources as it subscribed, the step put back: in order,
  -- headed and alien to it as before.
  defer-fed : ∀ {Γ A} {q} {a : Maybe A} {i : A ∈ Γ} {ρ ρ′ : NEnv Γ} p (ns : List (U.Notice Γ)) → Fed q a i ρ ρ′
            → Sorted (U.replay ns ρ) → Alienᴱ p (U.replay ns ρ)
            → Sorted (U.replay (ns ++ [ U.notice i q a ]) ρ′) × Alienᴱ p (U.replay (ns ++ [ U.notice i q a ]) ρ′)

-- A FED NODE STAYS PLACED.
mutual
  placed-fed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q (a : Maybe A) (c : U.Node Γ B) {ρ ρ′ : NEnv Γ}
             → Sane ν c → lookup ν i ≡ runs → Fed q a i ρ ρ′ → Placed c ρ → Placed (U.feed i q a c) ρ′
  placed-fed i q a c sn lr fd (o , w) =
    ordered-≈ _ _ (λ d → nowˢ (feed-alikeⁱ i q a c sn lr fd d)) o , within-fed i q a c sn lr fd w

  within-fed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q (a : Maybe A) (c : U.Node Γ B) {ρ ρ′ : NEnv Γ}
             → Sane ν c → lookup ν i ≡ runs → Fed q a i ρ ρ′ → Within c ρ → Within (U.feed i q a c) ρ′
  within-fed i q a (U.mapᶜ f c)         sn lr fd w = placed-fed i q a c sn lr fd w
  within-fed i q a (U.scanᶜ f z c)      sn lr fd w = placed-fed i q a c sn lr fd w
  within-fed i q a (U.takeWhileᶜ b p c) sn lr fd w = placed-fed i q a c sn lr fd w
  within-fed {ν = ν} i q a (U.flatMapᶜ op g o ls qs pl) {ρ} {ρ′} sn@(so , sl , sg , _) lr fd (po , pls , pr) =
      placedᴹ-fed i q a o so lr fd po
    , placedᴸ-fed i q a ls sl lr fd pls
    , λ x y re → placed-fed i q a (g x (y ++ [ ix 1 ])) (sg x _) (lookup-live i) fd
        (pr x y (reaches-agree (λ d → agree-sym (nowˢ (feed-alikeⁱ i q a (U.flatMapᶜ op g o ls qs pl) sn lr fd d))) re))
  within-fed i q a (U.joinᶜ j p xs e)   sn lr fd w = fed-every fd j w
  within-fed i q a (U.connectᶜ r b (U.live s)) {ρ} {ρ′} (sb , ss) lr fd (pb , ps , p , er , hp , kb , ks , al) =
      placed-fed (there i) q a b sb lr (fed-there (alike λ d → nowˢ (feed-alikeⁱ i q a s ss lr fd d)) fd) pb
    , placed-fed i q a s ss lr fd ps
    , p , er , hp
    , feed-keyed (owned-closed (p ++ [ ix 0 ])) (there i) q a b (owned-fit (p ++ [ ix 0 ]) q) kb
    , feed-keyed (apart-closed p hp) i q a s (λ j dj → apart-join (p ++ [ ix 0 ]) q j (fed-at fd al) dj) ks
    , fed-everyᴱ fd al
  within-fed i q a (U.connectᶜ r b (U.ended c t)) (sb , _) lr fd w =
    placed-fed (there i) q a b sb lr (fed-there (alike λ d → agree-refl d _) fd) w
  within-fed i q a (U.deferᶜ l p ns)    sn lr fd (hp , so , al) = hp , defer-fed p ns fd so al
  within-fed i q a (U.framesᶜ τ e m)    sn lr fd w = tt
  within-fed i q a (U.burstᶜ τ r n b)   sn lr fd w = tt
  within-fed i q a (U.ofᶜ p n xs)       sn lr fd w = tt
  within-fed i q a (U.endingᶜ p n)      sn lr fd w = tt
  within-fed i q a (U.restᶜ n)          sn lr fd w = tt
  within-fed i q a U.idleᶜ              sn lr fd w = tt
  within-fed i q a (U.unionᶜ x y)       sn lr fd w = tt
  within-fed i q a (U.burstingᶜ r t)    sn lr fd w = tt
  within-fed i q a (U.underᶜ s b)       sn lr fd w = tt

  placedᴹ-fed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q (a : Maybe A) (o : Maybe (U.Node Γ B)) {ρ ρ′ : NEnv Γ}
              → Saneᴹ ν o → lookup ν i ≡ runs → Fed q a i ρ ρ′ → Placedᴹ o ρ → Placedᴹ (U.feedᴹ i q a o) ρ′
  placedᴹ-fed i q a nothing  sn lr fd w = tt
  placedᴹ-fed i q a (just c) sn lr fd w = placed-fed i q a c sn lr fd w

  placedᴸ-fed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q (a : Maybe A) (cs : List (U.Node Γ B)) {ρ ρ′ : NEnv Γ}
              → Saneᴸ ν cs → lookup ν i ≡ runs → Fed q a i ρ ρ′ → Placedᴸ cs ρ → Placedᴸ (U.feedᴸ i q a cs) ρ′
  placedᴸ-fed i q a []       sn         lr fd w          = tt
  placedᴸ-fed i q a (c ∷ cs) (sc , scs) lr fd (pc , pcs) = placed-fed i q a c sc lr fd pc , placedᴸ-fed i q a cs scs lr fd pcs
