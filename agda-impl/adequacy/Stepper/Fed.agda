{-# OPTIONS --guardedness #-}

-- A FED NODE STAYS PLACED: a node placed reading its sources, fed a
-- running source's step and read past it, is placed.  Its meaning runs
-- alike (`feed-alikeⁱ`), so stays in order; a joiner's source and a
-- connect's scope run on from what they kept, so stay alien; a connect's
-- body keeps its key, fed where every key holds, and its source keeps
-- its own, the step alien to the body's region; a lane yet to subscribe
-- is reached alike.  Likewise a node told a source's end, its sources
-- alike at every depth, the end alien where its source was.
module adequacy.Stepper.Fed where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Events∞; Pos; end; ix)
open import denotation.MonotonicList using (agree-refl; agree-sym)
open import denotation.NonExpansive using (Agreeˢ)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Saneᴹ; Saneᴸ; Mode; runs; allLive)
open import adequacy.Placed.Order using (Alienᴱ; Every; Everyᴱ; Placed; Placedᴸ; Placedᴹ; Sorted; Within; every; every-lookup)
open import adequacy.Placed.Keys using (ordered-≈; every-≈)
open import adequacy.Placed.Rising using (apart-join)
open import adequacy.Placed.Heads using (apart-closed; feed-keyed; owned-closed; owned-fit; shut-keyed)
open import adequacy.Env using (Same; everyᴱ-agree; lookup-ne; meaning-same; reaches-agree; replay-ne; same-cons; sorted-agree)
open import adequacy.Stepper.Past using (_≃_; alike; shows)
open import adequacy.Stepper.Parts using (Fed; fed-here; fed-there; feed-alikeⁱ; shut-alikeⁱ)

open _≃_
open Agreeˢ using (nowˢ)
open Events∞

private

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

-- A node placed is placed reading sources alike at every depth.
private
  mutual
    placed-same : ∀ {Γ B} (c : U.Node Γ B) {ρ ρ′ : NEnv Γ} → Same ρ ρ′ → Placed c ρ → Placed c ρ′
    placed-same c S (o , w) = ordered-≈ _ _ (meaning-same c S) o , within-same c S w

    within-same : ∀ {Γ B} (c : U.Node Γ B) {ρ ρ′ : NEnv Γ} → Same ρ ρ′ → Within c ρ → Within c ρ′
    within-same (U.mapᶜ f c)         S w = placed-same c S w
    within-same (U.scanᶜ f z c)      S w = placed-same c S w
    within-same (U.takeWhileᶜ b p c) S w = placed-same c S w
    within-same (U.flatMapᶜ op g o ls qs pl) S (po , pls , pr) =
        placedᴹ-same o S po
      , placedᴸ-same ls S pls
      , λ x y re → placed-same (g x (y ++ [ ix 1 ])) S (pr x y (reaches-agree (λ d → agree-sym (meaning-same (U.flatMapᶜ op g o ls qs pl) S d)) re))
    within-same (U.joinᶜ j p xs e)   S w = every-≈ _ _ (λ m → lookup-ne (S m) j) w
    within-same (U.connectᶜ r b (U.live s)) S (pb , ps , p , er , hp , kb , ks , al) =
      placed-same b (same-cons (meaning-same s S) S) pb , placed-same s S ps , p , er , hp , kb , ks , everyᴱ-agree S al
    within-same (U.connectᶜ r b (U.ended c t)) S w = placed-same b (same-cons (λ m → agree-refl m (end c)) S) w
    within-same (U.deferᶜ l p ns)    S (hp , so , al) =
      hp , sorted-agree (λ m → replay-ne ns (S m)) so , everyᴱ-agree (λ m → replay-ne ns (S m)) al
    within-same (U.framesᶜ τ e m)    S w = tt
    within-same (U.burstᶜ τ r n b)   S w = tt
    within-same (U.ofᶜ p n xs)       S w = tt
    within-same (U.endingᶜ p n)      S w = tt
    within-same (U.restᶜ n)          S w = tt
    within-same U.idleᶜ              S w = tt
    within-same (U.unionᶜ x y)       S w = tt
    within-same (U.burstingᶜ r t)    S w = tt
    within-same (U.underᶜ s b)       S w = tt

    placedᴹ-same : ∀ {Γ B} (o : Maybe (U.Node Γ B)) {ρ ρ′ : NEnv Γ} → Same ρ ρ′ → Placedᴹ o ρ → Placedᴹ o ρ′
    placedᴹ-same nothing  S w = tt
    placedᴹ-same (just c) S w = placed-same c S w

    placedᴸ-same : ∀ {Γ B} (cs : List (U.Node Γ B)) {ρ ρ′ : NEnv Γ} → Same ρ ρ′ → Placedᴸ cs ρ → Placedᴸ cs ρ′
    placedᴸ-same []       S w          = tt
    placedᴸ-same (c ∷ cs) S (pc , pcs) = placed-same c S pc , placedᴸ-same cs S pcs

-- The end itself, where every source keeps it.
private
  shut-at : ∀ {Γ A} {P : Pos → Set} (i : A ∈ Γ) c {ρ : NEnv Γ} → lookup ρ i ≃ end c → Everyᴱ P ρ → P c
  shut-at {P = P} i c {ρ} al pρ = every (every-≈ _ _ (agreeing al) (every-lookup P ρ pρ i))

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

-- A NODE TOLD AN END STAYS PLACED.
mutual
  placed-shut : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) {ρ ρ′ : NEnv Γ} → lookup ρ i ≃ end c → Same ρ ρ′
              → Placed n ρ → Placed (U.shut i c n) ρ′
  placed-shut i c n al S (o , w) = ordered-≈ _ _ (λ d → nowˢ (shut-alikeⁱ i c n al S d)) o , within-shut i c n al S w

  within-shut : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) {ρ ρ′ : NEnv Γ} → lookup ρ i ≃ end c → Same ρ ρ′
              → Within n ρ → Within (U.shut i c n) ρ′
  within-shut i c (U.mapᶜ f n)         al S w = placed-shut i c n al S w
  within-shut i c (U.scanᶜ f z n)      al S w = placed-shut i c n al S w
  within-shut i c (U.takeWhileᶜ b p n) al S w = placed-shut i c n al S w
  within-shut i c (U.flatMapᶜ op g o ls qs pl) al S (po , pls , pr) =
      placedᴹ-shut i c o al S po
    , placedᴸ-shut i c ls al S pls
    , λ x y re → placed-same (g x (y ++ [ ix 1 ])) S
        (pr x y (reaches-agree (λ d → agree-sym (nowˢ (shut-alikeⁱ i c (U.flatMapᶜ op g o ls qs pl) al S d))) re))
  within-shut i c (U.joinᶜ j p xs e)   al S w = every-≈ _ _ (λ m → lookup-ne (S m) j) w
  within-shut i c (U.connectᶜ r b (U.live s)) al S (pb , ps , p , er , hp , kb , ks , ap) =
      placed-shut (there i) c b al (same-cons (λ d → nowˢ (shut-alikeⁱ i c s al S d)) S) pb
    , placed-shut i c s al S ps
    , p , er , hp
    , shut-keyed (owned-closed (p ++ [ ix 0 ])) (there i) c b (owned-fit (p ++ [ ix 0 ]) c) kb
    , shut-keyed (apart-closed p hp) i c s (λ j dj → apart-join (p ++ [ ix 0 ]) c j (shut-at i c al ap) dj) ks
    , everyᴱ-agree S ap
  within-shut i c (U.connectᶜ r b (U.ended c′ t)) al S w =
    placed-shut (there i) c b al (same-cons (λ m → agree-refl m _) S) w
  within-shut i c (U.deferᶜ l p ns)    al S w = within-same (U.deferᶜ l p ns) S w
  within-shut i c (U.framesᶜ τ e m)    al S w = tt
  within-shut i c (U.burstᶜ τ r n b)   al S w = tt
  within-shut i c (U.ofᶜ p n xs)       al S w = tt
  within-shut i c (U.endingᶜ p n)      al S w = tt
  within-shut i c (U.restᶜ n)          al S w = tt
  within-shut i c U.idleᶜ              al S w = tt
  within-shut i c (U.unionᶜ x y)       al S w = tt
  within-shut i c (U.burstingᶜ r t)    al S w = tt
  within-shut i c (U.underᶜ s b)       al S w = tt

  placedᴹ-shut : ∀ {Γ A B} (i : A ∈ Γ) c (o : Maybe (U.Node Γ B)) {ρ ρ′ : NEnv Γ} → lookup ρ i ≃ end c → Same ρ ρ′
               → Placedᴹ o ρ → Placedᴹ (U.shutᴹ i c o) ρ′
  placedᴹ-shut i c nothing  al S w = tt
  placedᴹ-shut i c (just n) al S w = placed-shut i c n al S w

  placedᴸ-shut : ∀ {Γ A B} (i : A ∈ Γ) c (ns : List (U.Node Γ B)) {ρ ρ′ : NEnv Γ} → lookup ρ i ≃ end c → Same ρ ρ′
               → Placedᴸ ns ρ → Placedᴸ (U.shutᴸ i c ns) ρ′
  placedᴸ-shut i c []       al S w          = tt
  placedᴸ-shut i c (n ∷ ns) al S (pn , pns) = placed-shut i c n al S pn , placedᴸ-shut i c ns al S pns
