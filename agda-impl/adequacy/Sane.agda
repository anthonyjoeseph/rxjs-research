-- THE GHOST IS A RUN'S CONFIGURATION (`Sane`): which joiners are told
-- their end, per connect in scope.
module adequacy.Sane where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Level using (lower)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Pos; From; Timeline; at) renaming (done to doneᶠ; quiet to quietᶠ)
import denotation.Unfold as U

-- A joiner untold while its connect's source runs, told once it ends.
Told : Bool → Maybe Pos → Set
Told true  nothing  = ⊤
Told true  (just _) = ⊥
Told false nothing  = ⊥
Told false (just _) = ⊤

-- Every connect in scope, running.
allLive : ∀ (Γ : List Set) → All (λ _ → Bool) Γ
allLive []      = []ᴬ
allLive (_ ∷ Γ) = true ∷ᴬ allLive Γ

-- THE GHOST IS A RUN'S CONFIGURATION: each joiner told its end exactly
-- when its connect's source has ended; each lane a flatMap will
-- subscribe, untold, as `subscribe` makes it.  `ν` says, per connect
-- in scope, whether its source runs.
mutual
  Sane : ∀ {Γ A} → All (λ _ → Bool) Γ → U.Node Γ A → Set
  Sane ν (U.mapᶜ f c)              = Sane ν c
  Sane ν (U.scanᶜ f z c)           = Sane ν c
  Sane ν (U.takeWhileᶜ i p c)      = Sane ν c
  Sane {Γ} ν (U.flatMapᶜ op g o ls qs) = Saneᴹ ν o × Saneᴸ ν ls × (∀ a q → Sane (allLive Γ) (g a q))
  Sane ν (U.joinᶜ i p xs e)        = Told (lookup ν i) e
  Sane ν (U.connectᶜ b (U.live s)) = Sane (true ∷ᴬ ν) b × Sane ν s
  Sane ν (U.connectᶜ b (U.ended c)) = Sane (false ∷ᴬ ν) b
  Sane ν _                         = ⊤

  Saneᴹ : ∀ {Γ A} → All (λ _ → Bool) Γ → Maybe (U.Node Γ A) → Set
  Saneᴹ ν nothing  = ⊤
  Saneᴹ ν (just c) = Sane ν c

  Saneᴸ : ∀ {Γ A} → All (λ _ → Bool) Γ → List (U.Node Γ A) → Set
  Saneᴸ ν []       = ⊤
  Saneᴸ ν (c ∷ cs) = Sane ν c × Saneᴸ ν cs

-- Every connect in scope still running.
Running : ∀ {Γ : List Set} → All (λ _ → Bool) Γ → Set₁
Running {Γ} ν = ∀ {A} (i : A ∈ Γ) → lookup ν i ≡ true

running-∷ : ∀ {Γ : List Set} {B : Set} {ν : All (λ _ → Bool) Γ} → Running ν → Running {B ∷ Γ} (true ∷ᴬ ν)
running-∷ r (Any.here refl) = refl
running-∷ r (Any.there i)   = r i

running-all : ∀ {Γ : List Set} → Running (allLive Γ)
running-all {_ ∷ Γ} (Any.here refl) = refl
running-all {_ ∷ Γ} (Any.there i)   = running-all i

sane-start : ∀ {Γ : List Set} {A : Set} {ν : All (λ _ → Bool) Γ} p (m : From A 0) → Sane ν (U.startᶜ {Γ} p m)
sane-start p (at zero _ b)    = tt
sane-start p (at (suc _) _ b) = tt
sane-start p doneᶠ            = tt
sane-start p quietᶠ           = tt

-- A program subscribed while its connects run is a run's configuration.
sane-subscribe : ∀ {Γ : List Set} {A : Set} {ν : All (λ _ → Bool) Γ} (o : Obs Timeline Γ A) p → Running ν → Sane ν (U.subscribe o p)
sane-subscribe (T.cold c)          p r = sane-start p (lower c)
sane-subscribe T.empty             p r = tt
sane-subscribe (T.of xs)           p r = tt
sane-subscribe (T.map f s)         p r = sane-subscribe s p r
sane-subscribe (T.scan f z s)      p r = sane-subscribe s p r
sane-subscribe (T.takeWhile i q s) p r = sane-subscribe s p r
sane-subscribe (T.flatMap op f s)  p r = sane-subscribe s p r , tt , λ a q → sane-subscribe (f a) q running-all
sane-subscribe (T.connect s b)     p r = sane-subscribe b _ (running-∷ r) , sane-subscribe s _ r
sane-subscribe (T.connected i)     p r rewrite r i = tt
sane-subscribe (T.defer l)         p r = tt

-- A feed keeps a run's configuration: it tells no joiner its end.
mutual
  sane-feed : ∀ {Γ A B} {ν : All (λ _ → Bool) Γ} (i : A ∈ Γ) q (a : Maybe A) (c : U.Node Γ B) → Sane ν c → Sane ν (U.feed i q a c)
  sane-feed i q a (U.framesᶜ t p m)          sc = tt
  sane-feed i q a (U.burstᶜ t p n f)         sc = tt
  sane-feed i q a (U.endᶜ p)                 sc = tt
  sane-feed i q a (U.ofᶜ p n xs)             sc = tt
  sane-feed i q a (U.mapᶜ f c)               sc = sane-feed i q a c sc
  sane-feed i q a (U.scanᶜ f z c)            sc = sane-feed i q a c sc
  sane-feed i q a (U.takeWhileᶜ b p c)       sc = sane-feed i q a c sc
  sane-feed i q a (U.flatMapᶜ op g o ls qs) (so , sl , sg) =
    sane-feedᴹ i q a o so , sane-feedᴸ i q a ls sl , λ x r → sane-feed i q a (g x r) (sg x r)
  sane-feed i q a (U.joinᶜ j p xs e)         sc = sc
  sane-feed i q a (U.connectᶜ b (U.live s))  (sb , ss) = sane-feed (Any.there i) q a b sb , sane-feed i q a s ss
  sane-feed i q a (U.connectᶜ b (U.ended c)) sb = sane-feed (Any.there i) q a b sb
  sane-feed i q a (U.deferᶜ l p ns)          sc = tt

  sane-feedᴹ : ∀ {Γ A B} {ν : All (λ _ → Bool) Γ} (i : A ∈ Γ) q (a : Maybe A) (o : Maybe (U.Node Γ B)) → Saneᴹ ν o → Saneᴹ ν (U.feedᴹ i q a o)
  sane-feedᴹ i q a nothing  so = tt
  sane-feedᴹ i q a (just c) so = sane-feed i q a c so

  sane-feedᴸ : ∀ {Γ A B} {ν : All (λ _ → Bool) Γ} (i : A ∈ Γ) q (a : Maybe A) (ls : List (U.Node Γ B)) → Saneᴸ ν ls → Saneᴸ ν (U.feedᴸ i q a ls)
  sane-feedᴸ i q a []       sl        = tt
  sane-feedᴸ i q a (c ∷ cs) (sc , sl) = sane-feed i q a c sc , sane-feedᴸ i q a cs sl
