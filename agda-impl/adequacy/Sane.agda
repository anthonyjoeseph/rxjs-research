-- THE GHOST IS A RUN'S CONFIGURATION (`Sane`): which joiners are told
-- their end, per connect in scope.
module adequacy.Sane where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; _<ᵇ_)
open import Data.Empty using (⊥)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (timelineAt; Pos; From; Frame; Timeline; at; emit; stall; close; ix; _<ᵖ_; inside) renaming (done to doneᶠ; quiet to quietᶠ)
import denotation.Unfold as U

-- Per connect in scope: its source runs, it has ended and its joiners
-- are told, or it has ended and a step has yet to tell the joiners it
-- made (`loose`).
data Mode : Set where
  runs over loose : Mode

-- A joiner untold while its connect's source runs, told once it ends.
Told : Mode → Maybe Pos → Set
Told runs  nothing  = ⊤
Told runs  (just _) = ⊥
Told over  nothing  = ⊥
Told over  (just _) = ⊤
Told loose _        = ⊤

-- Every connect in scope, running.
allLive : ∀ (Γ : List Set) → All (λ _ → Mode) Γ
allLive []      = []ᴬ
allLive (_ ∷ Γ) = runs ∷ᴬ allLive Γ

-- What a cut leaves running: a node whose meaning is its tail.
Rested : ∀ {Γ A} → U.Node Γ A → Set
Rested (U.restᶜ n)       = ⊤
Rested U.idleᶜ           = ⊤
Rested (U.unionᶜ x y)    = ⊤
Rested (U.burstingᶜ r t) = ⊤
Rested (U.underᶜ s b)    = ⊤
Rested _                 = ⊥

-- THE GHOST IS A RUN'S CONFIGURATION: each joiner told its end exactly
-- when its connect's source has ended; each lane a flatMap will
-- subscribe, untold, as `subscribe` makes it; of a rest, nothing; an ended
-- connect's source, and a flatMap's pool, what a cut left running.  `ν`
-- says, per connect in scope, whether its source runs (`Mode`).
--
-- REFUTED: 8f59ad1a `first-flat` without its pool `Rested`, by a defer for a pool
mutual
  Sane : ∀ {Γ A} → All (λ _ → Mode) Γ → U.Node Γ A → Set
  Sane ν (U.mapᶜ f c)              = Sane ν c
  Sane ν (U.scanᶜ f z c)           = Sane ν c
  Sane ν (U.takeWhileᶜ i p c)      = Sane ν c
  Sane {Γ} ν (U.flatMapᶜ op g o ls qs pl) = Saneᴹ ν o × Saneᴸ ν ls × (∀ a q → Sane (allLive Γ) (g a q)) × Rested pl
  Sane ν (U.joinᶜ i p xs e)        = Told (lookup ν i) e
  Sane ν (U.connectᶜ r b (U.live s))    = Sane (runs ∷ᴬ ν) b × Sane ν s
  Sane ν (U.connectᶜ r b (U.ended c t)) = Sane (over ∷ᴬ ν) b × Rested t
  Sane ν _                         = ⊤

  Saneᴹ : ∀ {Γ A} → All (λ _ → Mode) Γ → Maybe (U.Node Γ A) → Set
  Saneᴹ ν nothing  = ⊤
  Saneᴹ ν (just c) = Sane ν c

  Saneᴸ : ∀ {Γ A} → All (λ _ → Mode) Γ → List (U.Node Γ A) → Set
  Saneᴸ ν []       = ⊤
  Saneᴸ ν (c ∷ cs) = Sane ν c × Saneᴸ ν cs

-- No connect in scope whose joiners must already be told.
Running : ∀ {Γ : List Set} → All (λ _ → Mode) Γ → Set₁
Running {Γ} ν = ∀ {A} (i : A ∈ Γ) → Told (lookup ν i) nothing

running-∷ : ∀ {Γ : List Set} {B : Set} {ν : All (λ _ → Mode) Γ} → Running ν → Running {B ∷ Γ} (runs ∷ᴬ ν)
running-∷ r (Any.here refl) = tt
running-∷ r (Any.there i)   = r i

running-all : ∀ {Γ : List Set} → Running (allLive Γ)
running-all {_ ∷ Γ} (Any.here refl) = tt
running-all {_ ∷ Γ} (Any.there i)   = running-all i

sane-start : ∀ {Γ : List Set} {A : Set} {ν : All (λ _ → Mode) Γ} p (m : From A 0) → Sane ν (U.startᶜ {Γ} p m)
sane-start p (at zero _ b)    = tt
sane-start p (at (suc _) _ b) = tt
sane-start p doneᶠ            = tt
sane-start p quietᶠ           = tt

-- A program subscribed while no connect in scope needs its joiners told
-- is a run's configuration.
sane-subscribe : ∀ {Γ : List Set} {A : Set} {ν : All (λ _ → Mode) Γ} (o : Obs Timeline Γ A) p → Running ν → Sane ν (U.subscribe o p)
sane-subscribe (T.cold c)          p r = sane-start p (timelineAt c p)
sane-subscribe T.empty             p r = tt
sane-subscribe (T.of xs)           p r = tt
sane-subscribe (T.map f s)         p r = sane-subscribe s p r
sane-subscribe (T.scan f z s)      p r = sane-subscribe s p r
sane-subscribe (T.takeWhile i q s) p r = sane-subscribe s p r
sane-subscribe (T.flatMap op f s)  p r = sane-subscribe s p r , tt , (λ a q → sane-subscribe (f a) q running-all) , tt
sane-subscribe (T.connect s b)     p r = sane-subscribe b _ (running-∷ r) , sane-subscribe s _ r
sane-subscribe (T.connected i)     p r = r i
sane-subscribe (T.defer l)         p r = tt

------------------------------------------------------------------------
-- A STEP KEEPS THE GHOST SANE.  A body stepping past its source's end
-- may admit a lane whose joiners are untold, and its connect tells them
-- (`U.shutˢᵗ` shuts the stepped body): so a step leaves each ended
-- connect `loose`, and the connect above it ties it `over` again.

loose₁ : Mode → Mode
loose₁ runs  = runs
loose₁ over  = loose
loose₁ loose = loose

loosen : ∀ {Γ : List Set} → All (λ _ → Mode) Γ → All (λ _ → Mode) Γ
loosen []ᴬ       = []ᴬ
loosen (m ∷ᴬ ν) = loose₁ m ∷ᴬ loosen ν

-- One mode asking less of a joiner than another.
Pt : Mode → Mode → Set
Pt _    loose = ⊤
Pt runs runs  = ⊤
Pt over over  = ⊤
Pt _    _     = ⊥

Below : ∀ {Γ : List Set} → All (λ _ → Mode) Γ → All (λ _ → Mode) Γ → Set
Below []ᴬ       []ᴬ       = ⊤
Below (m ∷ᴬ μ) (n ∷ᴬ ν) = Pt m n × Below μ ν

told-pt : ∀ {m n} e → Pt m n → Told m e → Told n e
told-pt {runs}  {runs}  e _ t = t
told-pt {over}  {over}  e _ t = t
told-pt {runs}  {loose} e _ t = tt
told-pt {over}  {loose} e _ t = tt
told-pt {loose} {loose} e _ t = tt

lookup-pt : ∀ {Γ : List Set} {A : Set} {μ ν : All (λ _ → Mode) Γ} → Below μ ν → (i : A ∈ Γ) → Pt (lookup μ i) (lookup ν i)
lookup-pt {μ = _ ∷ᴬ _} {_ ∷ᴬ _} (p , _) (Any.here refl) = p
lookup-pt {μ = _ ∷ᴬ _} {_ ∷ᴬ _} (_ , b) (Any.there i)   = lookup-pt b i

below-loosen : ∀ {Γ : List Set} (ν : All (λ _ → Mode) Γ) → Below ν (loosen ν)
below-loosen []ᴬ           = tt
below-loosen (runs ∷ᴬ ν)  = tt , below-loosen ν
below-loosen (over ∷ᴬ ν)  = tt , below-loosen ν
below-loosen (loose ∷ᴬ ν) = tt , below-loosen ν

below-all : ∀ {Γ : List Set} (ν : All (λ _ → Mode) Γ) → Below (allLive Γ) (loosen ν)
below-all []ᴬ           = tt
below-all (runs ∷ᴬ ν)  = tt , below-all ν
below-all (over ∷ᴬ ν)  = tt , below-all ν
below-all (loose ∷ᴬ ν) = tt , below-all ν

running-loosen : ∀ {Γ : List Set} (ν : All (λ _ → Mode) Γ) → Running (loosen ν)
running-loosen (runs ∷ᴬ ν)  (Any.here refl) = tt
running-loosen (over ∷ᴬ ν)  (Any.here refl) = tt
running-loosen (loose ∷ᴬ ν) (Any.here refl) = tt
running-loosen (_ ∷ᴬ ν)     (Any.there i)   = running-loosen ν i

mutual
  weaken : ∀ {Γ A} {μ ν : All (λ _ → Mode) Γ} → Below μ ν → (c : U.Node Γ A) → Sane μ c → Sane ν c
  weaken b (U.framesᶜ τ e m)            s = tt
  weaken b (U.burstᶜ τ r i f)           s = tt
  weaken b (U.ofᶜ p i xs)               s = tt
  weaken b (U.mapᶜ f c)                 s = weaken b c s
  weaken b (U.scanᶜ f z c)              s = weaken b c s
  weaken b (U.takeWhileᶜ i p c)         s = weaken b c s
  weaken b (U.flatMapᶜ op g o ls qs pl) (so , sl , sg) = weakenᴹ b o so , weakenᴸ b ls sl , sg
  weaken b (U.joinᶜ i p xs e)           s = told-pt e (lookup-pt b i) s
  weaken b (U.connectᶜ r c (U.live t))  (sc , st) = weaken (tt , b) c sc , weaken b t st
  weaken b (U.connectᶜ r c (U.ended k t)) (sc , rt) = weaken (tt , b) c sc , rt
  weaken b (U.deferᶜ l p ns)            s = tt
  weaken b (U.endingᶜ p n)              s = tt
  weaken b (U.restᶜ n)                  s = tt
  weaken b U.idleᶜ                      s = tt
  weaken b (U.unionᶜ x y)               s = tt
  weaken b (U.burstingᶜ r t)            s = tt
  weaken b (U.underᶜ t c)               s = tt

  weakenᴹ : ∀ {Γ A} {μ ν : All (λ _ → Mode) Γ} → Below μ ν → (o : Maybe (U.Node Γ A)) → Saneᴹ μ o → Saneᴹ ν o
  weakenᴹ b nothing  s = tt
  weakenᴹ b (just c) s = weaken b c s

  weakenᴸ : ∀ {Γ A} {μ ν : All (λ _ → Mode) Γ} → Below μ ν → (ls : List (U.Node Γ A)) → Saneᴸ μ ls → Saneᴸ ν ls
  weakenᴸ b []       s        = tt
  weakenᴸ b (c ∷ cs) (sc , s) = weaken b c sc , weakenᴸ b cs s

saneᴸ-++ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (bs : List (U.Node Γ A)) {cs} → Saneᴸ ν bs → Saneᴸ ν cs → Saneᴸ ν (bs ++ cs)
saneᴸ-++ []       sb        sc = sc
saneᴸ-++ (b ∷ bs) (s , sb) sc = s , saneᴸ-++ bs sb sc

-- Fed or shut, a rest stays one.
feed-rested : ∀ {Γ : List Set} {A B : Set} (i : A ∈ Γ) q a (t : U.Node Γ B) → Rested t → Rested (U.feed i q a t)
feed-rested i q a (U.restᶜ n)       _ = tt
feed-rested i q a U.idleᶜ           _ = tt
feed-rested i q a (U.unionᶜ x y)    _ = tt
feed-rested i q a (U.burstingᶜ r t) _ = tt
feed-rested i q a (U.underᶜ s b)    _ = tt
feed-rested i q a (U.framesᶜ τ e m)            ()
feed-rested i q a (U.burstᶜ τ r k f)           ()
feed-rested i q a (U.ofᶜ p k xs)               ()
feed-rested i q a (U.mapᶜ f c)                 ()
feed-rested i q a (U.scanᶜ f z c)              ()
feed-rested i q a (U.takeWhileᶜ k p c)         ()
feed-rested i q a (U.flatMapᶜ op g o ls qs pl) ()
feed-rested i q a (U.joinᶜ j p xs e)           ()
feed-rested i q a (U.connectᶜ r b s)           ()
feed-rested i q a (U.deferᶜ l p ns)            ()
feed-rested i q a (U.endingᶜ p n)              ()

shut-rested : ∀ {Γ : List Set} {A B : Set} (i : A ∈ Γ) c (t : U.Node Γ B) → Rested t → Rested (U.shut i c t)
shut-rested i c (U.restᶜ n)       _ = tt
shut-rested i c U.idleᶜ           _ = tt
shut-rested i c (U.unionᶜ x y)    _ = tt
shut-rested i c (U.burstingᶜ r t) _ = tt
shut-rested i c (U.underᶜ s b)    _ = tt
shut-rested i c (U.framesᶜ τ e m)            ()
shut-rested i c (U.burstᶜ τ r k f)           ()
shut-rested i c (U.ofᶜ p k xs)               ()
shut-rested i c (U.mapᶜ f n)                 ()
shut-rested i c (U.scanᶜ f z n)              ()
shut-rested i c (U.takeWhileᶜ k p n)         ()
shut-rested i c (U.flatMapᶜ op g o ls qs pl) ()
shut-rested i c (U.joinᶜ j p xs e)           ()
shut-rested i c (U.connectᶜ r b s)           ()
shut-rested i c (U.deferᶜ l p ns)            ()
shut-rested i c (U.endingᶜ p n)              ()

-- Feeding a joiner leaves it as told as it was.
mutual
  feed-sane : ∀ {Γ : List Set} {A B : Set} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q a (c : U.Node Γ B) → Sane ν c → Sane ν (U.feed i q a c)
  feed-sane i q a (U.framesᶜ τ e m)            s = tt
  feed-sane i q a (U.burstᶜ τ r k f)           s = tt
  feed-sane i q a (U.ofᶜ p k xs)               s = tt
  feed-sane i q a (U.mapᶜ f c)                 s = feed-sane i q a c s
  feed-sane i q a (U.scanᶜ f z c)              s = feed-sane i q a c s
  feed-sane i q a (U.takeWhileᶜ k p c)         s = feed-sane i q a c s
  feed-sane i q a (U.flatMapᶜ op g o ls qs pl) (so , sl , sg , rp) =
    feedᴹ-sane i q a o so , feedᴸ-sane i q a ls sl , (λ x r → feed-sane i q a (g x r) (sg x r)) , feed-rested i q a pl rp
  feed-sane i q a (U.joinᶜ j p xs e)           s = s
  feed-sane i q a (U.connectᶜ r b (U.live t))  (sb , st) = feed-sane (Any.there i) q a b sb , feed-sane i q a t st
  feed-sane i q a (U.connectᶜ r b (U.ended k t)) (sb , rt) = feed-sane (Any.there i) q a b sb , feed-rested i q a t rt
  feed-sane i q a (U.deferᶜ l p ns)            s = tt
  feed-sane i q a (U.endingᶜ p n)              s = tt
  feed-sane i q a (U.restᶜ n)                  s = tt
  feed-sane i q a U.idleᶜ                      s = tt
  feed-sane i q a (U.unionᶜ x y)               s = tt
  feed-sane i q a (U.burstingᶜ r t)            s = tt
  feed-sane i q a (U.underᶜ t b)               s = tt

  feedᴹ-sane : ∀ {Γ : List Set} {A B : Set} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q a (o : Maybe (U.Node Γ B)) → Saneᴹ ν o → Saneᴹ ν (U.feedᴹ i q a o)
  feedᴹ-sane i q a nothing  s = tt
  feedᴹ-sane i q a (just c) s = feed-sane i q a c s

  feedᴸ-sane : ∀ {Γ : List Set} {A B : Set} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q a (ls : List (U.Node Γ B)) → Saneᴸ ν ls → Saneᴸ ν (U.feedᴸ i q a ls)
  feedᴸ-sane i q a []       s        = tt
  feedᴸ-sane i q a (c ∷ cs) (sc , s) = feed-sane i q a c sc , feedᴸ-sane i q a cs s

feeds-sane : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (ns : List (U.Notice Γ)) (c : U.Node Γ B) → Sane ν c → Sane ν (U.feeds ns c)
feeds-sane []                    c s = s
feeds-sane (U.notice i q a ∷ ns) c s = feeds-sane ns (U.feed i q a c) (feed-sane i q a c s)

-- Shutting connect `i` ties it `over`: each of its joiners told.
setₘ : ∀ {Γ : List Set} {A : Set} → All (λ _ → Mode) Γ → A ∈ Γ → All (λ _ → Mode) Γ
setₘ (_ ∷ᴬ μ) (Any.here _)  = over ∷ᴬ μ
setₘ (m ∷ᴬ μ) (Any.there i) = m ∷ᴬ setₘ μ i

told-set : ∀ {Γ : List Set} {A B : Set} (μ : All (λ _ → Mode) Γ) (i : A ∈ Γ) (j : B ∈ Γ) c p e
         → Told (lookup μ j) e → Told (lookup (setₘ μ i) j) (U.told i c j p e (U.same? i j))
told-set (m ∷ᴬ μ) (Any.here refl) (Any.here refl) c p nothing  t = tt
told-set (m ∷ᴬ μ) (Any.here refl) (Any.here refl) c p (just _) t = tt
told-set (m ∷ᴬ μ) (Any.here refl) (Any.there j)   c p nothing  t = t
told-set (m ∷ᴬ μ) (Any.here refl) (Any.there j)   c p (just _) t = t
told-set (m ∷ᴬ μ) (Any.there i)   (Any.here refl) c p nothing  t = t
told-set (m ∷ᴬ μ) (Any.there i)   (Any.here refl) c p (just _) t = t
told-set (m ∷ᴬ μ) (Any.there i)   (Any.there j)   c p e        t = told-set μ i j c p e t

mutual
  shut-sane : ∀ {Γ : List Set} {A B : Set} {μ : All (λ _ → Mode) Γ} (i : A ∈ Γ) c (n : U.Node Γ B) → Sane μ n → Sane (setₘ μ i) (U.shut i c n)
  shut-sane i c (U.framesᶜ τ e m)            s = tt
  shut-sane i c (U.burstᶜ τ r k f)           s = tt
  shut-sane i c (U.ofᶜ p k xs)               s = tt
  shut-sane i c (U.mapᶜ f n)                 s = shut-sane i c n s
  shut-sane i c (U.scanᶜ f z n)              s = shut-sane i c n s
  shut-sane i c (U.takeWhileᶜ k p n)         s = shut-sane i c n s
  shut-sane i c (U.flatMapᶜ op g o ls qs pl) (so , sl , sg , rp) = shutᴹ-sane i c o so , shutᴸ-sane i c ls sl , sg , shut-rested i c pl rp
  shut-sane {μ = μ} i c (U.joinᶜ j p xs e)   s = told-set μ i j c p e s
  shut-sane i c (U.connectᶜ r b (U.live t))  (sb , st) = shut-sane (Any.there i) c b sb , shut-sane i c t st
  shut-sane i c (U.connectᶜ r b (U.ended k t)) (sb , rt) = shut-sane (Any.there i) c b sb , shut-rested i c t rt
  shut-sane i c (U.deferᶜ l p ns)            s = tt
  shut-sane i c (U.endingᶜ p n)              s = tt
  shut-sane i c (U.restᶜ n)                  s = tt
  shut-sane i c U.idleᶜ                      s = tt
  shut-sane i c (U.unionᶜ x y)               s = tt
  shut-sane i c (U.burstingᶜ r t)            s = tt
  shut-sane i c (U.underᶜ t b)               s = tt

  shutᴹ-sane : ∀ {Γ : List Set} {A B : Set} {μ : All (λ _ → Mode) Γ} (i : A ∈ Γ) c (o : Maybe (U.Node Γ B)) → Saneᴹ μ o → Saneᴹ (setₘ μ i) (U.shutᴹ i c o)
  shutᴹ-sane i c nothing  s = tt
  shutᴹ-sane i c (just n) s = shut-sane i c n s

  shutᴸ-sane : ∀ {Γ : List Set} {A B : Set} {μ : All (λ _ → Mode) Γ} (i : A ∈ Γ) c (ls : List (U.Node Γ B)) → Saneᴸ μ ls → Saneᴸ (setₘ μ i) (U.shutᴸ i c ls)
  shutᴸ-sane i c []       s        = tt
  shutᴸ-sane i c (n ∷ ns) (sn , s) = shut-sane i c n sn , shutᴸ-sane i c ns s

-- What a step leaves, sane.
SaneS : ∀ {Γ A} → All (λ _ → Mode) Γ → U.Step Γ A → Set
SaneS ν (U.outˢ k a c) = Sane ν c
SaneS ν (U.skipˢ k c)  = Sane ν c
SaneS ν (U.endˢ k)     = ⊤
SaneS ν U.hushˢ        = ⊤

-- What a cut leaves running is rests, sane of anything.
union-sane : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (x : U.Node Γ B) sx y sy → SaneS ν sy → SaneS ν (U.unionˢ x sx y sy)
union-sane x (U.skipˢ k x′) y (U.skipˢ k′ y′) s with k <ᵖ k′
... | true  = tt
... | false = tt
union-sane x (U.skipˢ k x′) y (U.outˢ _ _ _)  s = tt
union-sane x (U.skipˢ k x′) y (U.endˢ _)      s = tt
union-sane x (U.skipˢ k x′) y U.hushˢ         s = tt
union-sane x (U.outˢ _ _ _) y sy              s = s
union-sane x (U.endˢ _)     y sy              s = s
union-sane x U.hushˢ        y sy              s = s

under-sane : ∀ {Γ A B C} {ν : All (λ _ → Mode) Γ} (t : U.Source Γ A) (sb : U.Step (A ∷ Γ) C) → SaneS {A = B} ν (U.underˢ t sb)
under-sane t (U.outˢ _ _ _) = tt
under-sane t (U.skipˢ k b)  = tt
under-sane t (U.endˢ _)     = tt
under-sane t U.hushˢ        = tt

mutual
  rest-sane : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) → SaneS {A = B} ν (U.restˢ c)
  rest-sane (U.framesᶜ τ e m)           = tt
  rest-sane (U.burstᶜ τ r i f)          = tt
  rest-sane (U.ofᶜ p i xs)              = tt
  rest-sane (U.mapᶜ f c)                = rest-sane c
  rest-sane (U.scanᶜ f z c)             = rest-sane c
  rest-sane (U.takeWhileᶜ i p c)        = rest-sane c
  rest-sane (U.flatMapᶜ op g o ls qs p) =
    union-sane (U.outerᶜ o) (U.restᴹ o) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ p)) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p)) (union-sane (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p) (rest-sane p))
  rest-sane (U.joinᶜ i p xs e)          = tt
  rest-sane (U.connectᶜ {B = C} r b (U.live s))    =
    union-sane (U.burstingᶜ r s) (U.burstsˢ r s (U.step s)) (U.underᶜ (U.live s) b) (U.underˢ (U.live s) (U.restˢ {B = C} b)) (under-sane (U.live s) (U.restˢ {B = C} b))
  rest-sane (U.connectᶜ {B = C} r b (U.ended c t)) =
    union-sane (U.burstingᶜ r t) (U.burstsˢ r t (U.step t)) (U.underᶜ (U.ended c t) b) (U.underˢ (U.ended c t) (U.restˢ {B = C} b)) (under-sane (U.ended c t) (U.restˢ {B = C} b))
  rest-sane (U.deferᶜ l p ns)           = tt
  rest-sane (U.endingᶜ p n)             = rest-sane n
  rest-sane (U.restᶜ n)                 = rest-sane n
  rest-sane U.idleᶜ                     = tt
  rest-sane (U.unionᶜ x y)              = union-sane (U.restᶜ x) (U.restˢ x) (U.restᶜ y) (U.restˢ y) (rest-sane y)
  rest-sane (U.burstingᶜ r t)           = bursts-sane r t (U.step t)
  rest-sane (U.underᶜ {C = C} s b)      = under-sane s (U.restˢ {B = C} b)

  bursts-sane : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (t : U.Node Γ A) (st : U.Step Γ A) → SaneS {A = B} ν (U.burstsˢ r t st)
  bursts-sane r t (U.outˢ k _ t′) with inside r k
  ... | true  = tt
  ... | false = rest-sane t
  bursts-sane r t (U.skipˢ k t′)  with inside r k
  ... | true  = tt
  ... | false = rest-sane t
  bursts-sane r t (U.endˢ _)      = rest-sane t
  bursts-sane r t U.hushˢ         = rest-sane t

-- A rest's step: a skip to a rest, or nothing.
RestedS : ∀ {Γ A} → U.Step Γ A → Set
RestedS (U.skipˢ k c)  = Rested c
RestedS U.hushˢ        = ⊤
RestedS (U.outˢ k a c) = ⊥
RestedS (U.endˢ k)     = ⊥

union-rested : ∀ {Γ B} (x : U.Node Γ B) sx y sy → RestedS sy → RestedS (U.unionˢ x sx y sy)
union-rested x (U.skipˢ k x′) y (U.skipˢ k′ y′) s with k <ᵖ k′
... | true  = tt
... | false = tt
union-rested x (U.skipˢ k x′) y (U.outˢ _ _ _)  s = tt
union-rested x (U.skipˢ k x′) y (U.endˢ _)      s = tt
union-rested x (U.skipˢ k x′) y U.hushˢ         s = tt
union-rested x (U.outˢ _ _ _) y sy              s = s
union-rested x (U.endˢ _)     y sy              s = s
union-rested x U.hushˢ        y sy              s = s

under-rested : ∀ {Γ A B C} (t : U.Source Γ A) (sb : U.Step (A ∷ Γ) C) → RestedS {A = B} (U.underˢ t sb)
under-rested t (U.outˢ _ _ _) = tt
under-rested t (U.skipˢ k b)  = tt
under-rested t (U.endˢ _)     = tt
under-rested t U.hushˢ        = tt

mutual
  rest-rested : ∀ {Γ A B} (c : U.Node Γ A) → RestedS {A = B} (U.restˢ c)
  rest-rested (U.framesᶜ τ e m)           = tt
  rest-rested (U.burstᶜ τ r i f)          = tt
  rest-rested (U.ofᶜ p i xs)              = tt
  rest-rested (U.mapᶜ f c)                = rest-rested c
  rest-rested (U.scanᶜ f z c)             = rest-rested c
  rest-rested (U.takeWhileᶜ i p c)        = rest-rested c
  rest-rested (U.flatMapᶜ op g o ls qs p) =
    union-rested (U.outerᶜ o) (U.restᴹ o) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ p)) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p)) (union-rested (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p) (rest-rested p))
  rest-rested (U.joinᶜ i p xs e)          = tt
  rest-rested (U.connectᶜ {B = C} r b (U.live s))    =
    union-rested (U.burstingᶜ r s) (U.burstsˢ r s (U.step s)) (U.underᶜ (U.live s) b) (U.underˢ (U.live s) (U.restˢ {B = C} b)) (under-rested (U.live s) (U.restˢ {B = C} b))
  rest-rested (U.connectᶜ {B = C} r b (U.ended c t)) =
    union-rested (U.burstingᶜ r t) (U.burstsˢ r t (U.step t)) (U.underᶜ (U.ended c t) b) (U.underˢ (U.ended c t) (U.restˢ {B = C} b)) (under-rested (U.ended c t) (U.restˢ {B = C} b))
  rest-rested (U.deferᶜ l p ns)           = tt
  rest-rested (U.endingᶜ p n)             = rest-rested n
  rest-rested (U.restᶜ n)                 = rest-rested n
  rest-rested U.idleᶜ                     = tt
  rest-rested (U.unionᶜ x y)              = union-rested (U.restᶜ x) (U.restˢ x) (U.restᶜ y) (U.restˢ y) (rest-rested y)
  rest-rested (U.burstingᶜ r t)           = bursts-rested r t (U.step t)
  rest-rested (U.underᶜ {C = C} s b)      = under-rested s (U.restˢ {B = C} b)

  bursts-rested : ∀ {Γ A B} r (t : U.Node Γ A) (st : U.Step Γ A) → RestedS {A = B} (U.burstsˢ r t st)
  bursts-rested r t (U.outˢ k _ t′) with inside r k
  ... | true  = tt
  ... | false = rest-rested t
  bursts-rested r t (U.skipˢ k t′)  with inside r k
  ... | true  = tt
  ... | false = rest-rested t
  bursts-rested r t (U.endˢ _)      = rest-rested t
  bursts-rested r t U.hushˢ         = rest-rested t

-- A rest steps as one.
step-rested : ∀ {Γ A} (t : U.Node Γ A) → Rested t → RestedS (U.step t)
step-rested (U.restᶜ n)            _ = rest-rested n
step-rested U.idleᶜ                _ = tt
step-rested (U.unionᶜ x y)         _ = union-rested x (U.restˢ x) y (U.restˢ y) (rest-rested y)
step-rested (U.burstingᶜ r t)      _ = bursts-rested r t (U.step t)
step-rested (U.underᶜ {C = C} s b) _ = under-rested s (U.restˢ {B = C} b)
step-rested (U.framesᶜ τ e m)            ()
step-rested (U.burstᶜ τ r k f)           ()
step-rested (U.ofᶜ p k xs)               ()
step-rested (U.mapᶜ f c)                 ()
step-rested (U.scanᶜ f z c)              ()
step-rested (U.takeWhileᶜ k p c)         ()
step-rested (U.flatMapᶜ op g o ls qs pl) ()
step-rested (U.joinᶜ j p xs e)           ()
step-rested (U.connectᶜ r b s)           ()
step-rested (U.deferᶜ l p ns)            ()
step-rested (U.endingᶜ p n)              ()

-- The flatMap's step, part by part.
OuterOk : ∀ {Γ A} → All (λ _ → Mode) Γ → U.Outer Γ A → Set
OuterOk ν U.doneᵒ       = ⊤
OuterOk ν (U.runᵒ o so) = Sane ν o × SaneS ν so

EarlyOk : ∀ {Γ B} → All (λ _ → Mode) Γ → U.Earliest Γ B → Set
EarlyOk ν U.none                 = ⊤
EarlyOk ν (U.found k bs l s as) = Saneᴸ ν bs × Sane ν l × SaneS ν s × Saneᴸ ν as

admit-sane : ∀ {Γ : List Set} {A B : Set} {ν : All (λ _ → Mode) Γ} op (g : A → Pos → U.Node Γ B) → (∀ a q → Sane ν (g a q))
           → ∀ q a ls qs d → Saneᴸ ν ls → Saneᴸ ν (proj₁ (U.admit op g q a ls qs d))
admit-sane (T.mergeᶠ nothing)  g gν q a ls       qs d sl = gν a q , sl
admit-sane (T.mergeᶠ (just n)) g gν q a ls       qs d sl with length ls <ᵇ n
... | true  = gν a q , sl
... | false = sl
admit-sane T.switchᶠ           g gν q a ls       qs d sl = gν a q , tt
admit-sane T.exhaustᶠ          g gν q a []       qs d sl = gν a q , tt
admit-sane T.exhaustᶠ          g gν q a (l ∷ ls) qs d sl = sl

module _ {Γ : List Set} {A B : Set} {ν : All (λ _ → Mode) Γ} (op : T.FlatOp) (g : A → Pos → U.Node Γ B)
         (gA : ∀ a q → Sane (allLive Γ) (g a q)) (gν : ∀ a q → Sane ν (g a q)) where

  outer-sane : ∀ o so ls qs p → Sane ν o → SaneS ν so → Saneᴸ ν ls → Rested p → SaneS ν (U.outerˢ op g o so ls qs p)
  outer-sane o (U.outˢ q a o′) ls qs p so s′ sl rp
    with U.admit op g (q ++ [ ix 1 ]) a ls qs (U.restsᶜ ls) | admit-sane op g gν (q ++ [ ix 1 ]) a ls qs (U.restsᶜ ls) sl
  ... | ls′ , qs′ , d | sl′ = s′ , sl′ , gA , tt
  outer-sane o (U.skipˢ q o′)  ls       qs       p so s′ sl rp = s′ , sl , gA , rp
  outer-sane o (U.endˢ c)      []       []       p so s′ sl rp = tt
  outer-sane o (U.endˢ c)      []       (x ∷ qs) p so s′ sl rp = tt , tt , gA , tt
  outer-sane o (U.endˢ c)      (l ∷ ls) qs       p so s′ sl rp = tt , sl , gA , tt
  outer-sane o U.hushˢ         ls       qs       p so s′ sl rp = tt

  lane-sane : ∀ o bs l s as qs p → Saneᴹ ν o → Saneᴸ ν bs → SaneS ν s → Saneᴸ ν as → Rested p → SaneS ν (U.laneˢ op g o bs l s as qs p)
  lane-sane o        bs       l (U.outˢ k b c) as       qs       p so sb sc sa rp = so , saneᴸ-++ bs sb (sc , sa) , gA , rp
  lane-sane o        bs       l (U.skipˢ k c)  as       qs       p so sb sc sa rp = so , saneᴸ-++ bs sb (sc , sa) , gA , rp
  lane-sane o        bs       l (U.endˢ c)     as       (a ∷ qs) p so sb sc sa rp = so , (gν a (c ++ [ ix 1 ]) , saneᴸ-++ bs sb sa) , gA , tt
  lane-sane nothing  []       l (U.endˢ c)     []       []       p so sb sc sa rp = tt
  lane-sane nothing  []       l (U.endˢ c)     (x ∷ as) []       p so sb sc sa rp = tt , sa , gA , tt
  lane-sane nothing  (b ∷ bs) l (U.endˢ c)     as       []       p so sb sc sa rp = tt , saneᴸ-++ (b ∷ bs) sb sa , gA , tt
  lane-sane (just o) bs       l (U.endˢ c)     as       []       p so sb sc sa rp = so , saneᴸ-++ bs sb sa , gA , tt
  lane-sane o        bs       l U.hushˢ        as       qs       p so sb sc sa rp = tt

  race-sane : ∀ o so h k bs l s as qs p → Sane ν o → SaneS ν so → Saneᴸ ν bs → Sane ν l → SaneS ν s → Saneᴸ ν as
            → Rested p → SaneS ν (U.raceˢ op g o so h k bs l s as qs p)
  race-sane o so nothing   k bs l s as qs p sO sso sb sl ss sa rp = lane-sane (just o) bs l s as qs p sO sb ss sa rp
  race-sane o so (just k′) k bs l s as qs p sO sso sb sl ss sa rp with k′ <ᵖ k
  ... | true  = outer-sane o so (bs ++ l ∷ as) qs p sO sso (saneᴸ-++ bs sb (sl , sa)) rp
  ... | false = lane-sane (just o) bs l s as qs p sO sb ss sa rp

  go-sane : ∀ oo ls qs p e → OuterOk ν oo → Saneᴸ ν ls → EarlyOk ν e → Rested p → SaneS ν (U.goˢ op g oo ls qs p e)
  go-sane U.doneᵒ       ls qs p U.none                so         sl se rp = tt
  go-sane (U.runᵒ o so) ls qs p U.none                (sO , sso) sl se rp = outer-sane o so ls qs p sO sso sl rp
  go-sane U.doneᵒ       ls qs p (U.found k bs l s as) so         sl (sb , sl′ , ss , sa) rp = lane-sane nothing bs l s as qs p tt sb ss sa rp
  go-sane (U.runᵒ o so) ls qs p (U.found k bs l s as) (sO , sso) sl (sb , sl′ , ss , sa) rp =
    race-sane o so (U.headˢ so) k bs l s as qs p sO sso sb sl′ ss sa rp

  nodeᵒ-sane : ∀ (oo : U.Outer Γ A) → OuterOk ν oo → Saneᴹ ν (U.nodeᵒ oo)
  nodeᵒ-sane U.doneᵒ       _        = tt
  nodeᵒ-sane (U.runᵒ o so) (sO , _) = sO

  flat-sane : ∀ oo ls qs p sp e → OuterOk ν oo → Saneᴸ ν ls → EarlyOk ν e → Rested p → RestedS sp → SaneS ν (U.flatˢ op g oo ls qs p sp e)
  flat-sane oo ls qs p (U.skipˢ k p′)  e so sl se rp rp′ with U.aheadˢ k oo e
  ... | true  = nodeᵒ-sane oo so , sl , gA , rp′
  ... | false = go-sane oo ls qs p e so sl se rp
  flat-sane oo ls qs p (U.outˢ _ _ _) e so sl se rp _ = go-sane oo ls qs p e so sl se rp
  flat-sane oo ls qs p (U.endˢ _)     e so sl se rp _ = go-sane oo ls qs p e so sl se rp
  flat-sane oo ls qs p U.hushˢ        e so sl se rp _ = go-sane oo ls qs p e so sl se rp

pick-sane : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (l : U.Node Γ B) s ls h e → Sane ν l → SaneS ν s → Saneᴸ ν ls → EarlyOk ν e
          → EarlyOk ν (U.pick l s ls h e)
pick-sane l s ls nothing  U.none                  sl ss sls se = tt
pick-sane l s ls nothing  (U.found k bs c sc as)  sl ss sls (sb , r) = (sl , sb) , r
pick-sane l s ls (just k) U.none                  sl ss sls se = tt , sl , ss , sls
pick-sane l s ls (just k) (U.found k′ bs c sc as) sl ss sls (sb , r) with k <ᵖ k′
... | true  = tt , sl , ss , sls
... | false = (sl , sb) , r

-- The body stepped, its source carried along.
body-sane : ∀ {Γ A B} {μ : All (λ _ → Mode) Γ} r (s : U.Node Γ A) (sb : U.Step (A ∷ Γ) B) → Sane μ s → SaneS (runs ∷ᴬ μ) sb
          → SaneS μ (U.bodyˢ r (U.live s) sb)
body-sane r s (U.outˢ k a b) ss sb = sb , ss
body-sane r s (U.skipˢ k b)  ss sb = sb , ss
body-sane r s (U.endˢ c)     ss sb = tt
body-sane r s U.hushˢ        ss sb = tt

source-sane : ∀ {Γ A B} {μ : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) st
            → Sane (runs ∷ᴬ μ) b → SaneS (runs ∷ᴬ μ) sb → Sane μ s → SaneS μ st → SaneS μ (U.sourceˢ r b sb s st)
source-sane r b sb s (U.outˢ q a s′) sB ssb ss sst with U.beforeˢ (q ++ [ ix 0 ]) sb
... | true  = feed-sane (Any.here refl) q (just a) b sB , sst
... | false = body-sane r s sb ss ssb
source-sane r b sb s (U.skipˢ q s′) sB ssb ss sst with U.beforeˢ (q ++ [ ix 0 ]) sb
... | true  = feed-sane (Any.here refl) q nothing b sB , sst
... | false = body-sane r s sb ss ssb
source-sane r b sb s (U.endˢ c) sB ssb ss sst with U.beforeˢ (c ++ [ ix 0 ]) sb
... | true  = shut-sane (Any.here refl) c b sB , tt
... | false = body-sane r s sb ss ssb
source-sane r b sb s U.hushˢ sB ssb ss sst = body-sane r s sb ss ssb

-- Past the source's end: the stepped body shut, its new joiners told.
shutᵗ-sane : ∀ {Γ A B} {μ : All (λ _ → Mode) Γ} r c (t : U.Node Γ A) (sb : U.Step (A ∷ Γ) B) → SaneS (loose ∷ᴬ μ) sb
           → Rested t → SaneS μ (U.shutˢᵗ r c t sb)
shutᵗ-sane r c t (U.outˢ k a b) s rt = shut-sane (Any.here refl) c b s , rt
shutᵗ-sane r c t (U.skipˢ k b)  s rt = shut-sane (Any.here refl) c b s , rt
shutᵗ-sane r c t (U.endˢ e)     s rt = tt
shutᵗ-sane r c t U.hushˢ        s rt = tt

ended-sane : ∀ {Γ A B} {μ : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) sb c (t : U.Node Γ A) st
           → Sane (over ∷ᴬ μ) b → SaneS (loose ∷ᴬ μ) sb → Rested t → RestedS st → SaneS μ (U.endedˢ r b sb c t st)
ended-sane r b sb c t (U.skipˢ k t′) sB ssb rt rs with U.beforeˢ (k ++ [ ix 0 ]) sb
... | true  = sB , rs
... | false = shutᵗ-sane r c t sb ssb rt
ended-sane r b sb c t (U.outˢ _ _ _) sB ssb rt rs = shutᵗ-sane r c t sb ssb rt
ended-sane r b sb c t (U.endˢ _)     sB ssb rt rs = shutᵗ-sane r c t sb ssb rt
ended-sane r b sb c t U.hushˢ        sB ssb rt rs = shutᵗ-sane r c t sb ssb rt

taking-sane : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} i (p : A → Bool) k a (c : U.Node Γ A) b → Sane ν c → SaneS ν (U.taking i p k a c b)
taking-sane i     p k a c true  s = s
taking-sane true  p k a c false s = tt
taking-sane false p k a c false s = tt

map-sane : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (f : A → B) (s : U.Step Γ A) → SaneS ν s → SaneS ν (U.mapˢ f s)
map-sane f (U.outˢ k a c) s = s
map-sane f (U.skipˢ k c)  s = s
map-sane f (U.endˢ k)     s = tt
map-sane f U.hushˢ        s = tt

scan-sane : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (f : B → A → B) z (s : U.Step Γ A) → SaneS ν s → SaneS ν (U.scanˢ f z s)
scan-sane f z (U.outˢ k a c) s = s
scan-sane f z (U.skipˢ k c)  s = s
scan-sane f z (U.endˢ k)     s = tt
scan-sane f z U.hushˢ        s = tt

take-sane : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} i (p : A → Bool) (s : U.Step Γ A) → SaneS ν s → SaneS ν (U.takeWhileˢ i p s)
take-sane i p (U.outˢ k a c) s = taking-sane i p k a c (p a) s
take-sane i p (U.skipˢ k c)  s = s
take-sane i p (U.endˢ k)     s = tt
take-sane i p U.hushˢ        s = tt

join-sane : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) p xs e → Told (lookup ν i) e → SaneS ν (U.joinˢ i p xs e)
join-sane i p ((q , just a) ∷ xs) e        t = t
join-sane i p ((q , nothing) ∷ xs) e       t = t
join-sane i p []                  (just c) t = tt
join-sane i p []                  nothing  t = tt

burst-sane : ∀ {Γ A t} {ν : All (λ _ → Mode) Γ} τ r i (f : Frame A t) → SaneS ν (U.burstˢ {Γ} τ r i f)
burst-sane τ r i (emit a k) = tt
burst-sane τ r i (stall k)  = tt
burst-sane τ r i (close k)  = tt

frames-sane : ∀ {Γ A t} {ν : All (λ _ → Mode) Γ} τ e (m : From A t) → SaneS ν (U.framesˢ {Γ} τ e m)
frames-sane τ e doneᶠ       = tt
frames-sane τ e quietᶠ      = tt
frames-sane τ e (at t _ b) = burst-sane τ _ 0 b

of-sane : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} p i (xs : List A) → SaneS ν (U.ofˢ {Γ} p i xs)
of-sane p i []       = tt
of-sane p i (x ∷ xs) = tt

mutual
  step-sane : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) → Sane ν c → SaneS (loosen ν) (U.step c)
  step-sane (U.framesᶜ τ e m)            s = frames-sane τ e m
  step-sane (U.burstᶜ τ r i f)           s = burst-sane τ r i f
  step-sane (U.ofᶜ p i xs)               s = of-sane p i xs
  step-sane (U.mapᶜ f c)                 s = map-sane f (U.step c) (step-sane c s)
  step-sane (U.scanᶜ f z c)              s = scan-sane f z (U.step c) (step-sane c s)
  step-sane (U.takeWhileᶜ i p c)         s = take-sane i p (U.step c) (step-sane c s)
  step-sane {ν = ν} (U.flatMapᶜ op g o ls qs p) (so , sl , sg , rp) =
    flat-sane op g sg (λ a q → weaken (below-all ν) (g a q) (sg a q)) (U.outerOf o) ls qs p (U.step p) (U.earliest ls)
      (outer-of o so) (weakenᴸ (below-loosen ν) ls sl) (early-sane ls sl) rp (step-rested p rp)
  step-sane {ν = ν} (U.joinᶜ i p xs e)   s = join-sane i p xs e (told-pt e (lookup-pt (below-loosen ν) i) s)
  step-sane {ν = ν} (U.connectᶜ r b (U.live s)) (sb , ss) =
    source-sane r b (U.step b) s (U.step s) (weaken (tt , below-loosen ν) b sb) (step-sane b sb) (weaken (below-loosen ν) s ss) (step-sane s ss)
  step-sane {ν = ν} (U.connectᶜ r b (U.ended c t)) (sb , rt) =
    ended-sane r b (U.step b) c t (U.step t) (weaken (tt , below-loosen ν) b sb) (step-sane b sb) rt (step-rested t rt)
  step-sane {ν = ν} (U.deferᶜ l p ns)    s = feeds-sane ns (U.subscribe (T.Later.force l) (p ++ [ ix 1 ])) (sane-subscribe (T.Later.force l) (p ++ [ ix 1 ]) (running-loosen ν))
  step-sane (U.endingᶜ p n)              s = tt
  step-sane (U.restᶜ n)                  s = rest-sane n
  step-sane U.idleᶜ                      s = tt
  step-sane (U.unionᶜ x y)               s = union-sane x (U.restˢ x) y (U.restˢ y) (rest-sane y)
  step-sane (U.burstingᶜ r t)            s = bursts-sane r t (U.step t)
  step-sane (U.underᶜ {C = C} s b)       _ = under-sane s (U.restˢ {B = C} b)

  outer-of : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (o : Maybe (U.Node Γ A)) → Saneᴹ ν o → OuterOk (loosen ν) (U.outerOf o)
  outer-of nothing  s = tt
  outer-of {ν = ν} (just o) s = weaken (below-loosen ν) o s , step-sane o s

  early-sane : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ B)) → Saneᴸ ν ls → EarlyOk (loosen ν) (U.earliest ls)
  early-sane []       s        = tt
  early-sane {ν = ν} (l ∷ ls) (sl , s) =
    pick-sane l (U.step l) ls (U.headˢ (U.step l)) (U.earliest ls) (weaken (below-loosen ν) l sl) (step-sane l sl)
      (weakenᴸ (below-loosen ν) ls s) (early-sane ls s)

-- A ghost's value shown, the ghost it leaves still sane.
sane-out : ∀ {A} {g : U.Node [] A} {k a g′} → Sane []ᴬ g → U.step g ≡ U.outˢ k a g′ → Sane []ᴬ g′
sane-out {g = g} s e = subst (SaneS []ᴬ) e (step-sane g s)
