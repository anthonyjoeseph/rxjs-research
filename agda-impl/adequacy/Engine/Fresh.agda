{-# OPTIONS --guardedness #-}

-- A SUBSCRIPTION'S ROOM, STORED (`Fresh`): where a configuration
-- subscribes at `p`, every part racing it has room for, and every
-- frame above holds aloft, each key a subscription at `p` can plant
-- (`Sown p`): inside `p`, or a cold's later frame tagged by such a
-- place.  A begin hands it down (`begin-fresh`): a child subscribes at
-- or under its parent's place, and the frames a begin opens race
-- nothing keyed.  What a begun node plants is sown where it subscribed
-- (`tapes-sown`, `ofFut-sown`), so its room and its aloft are read off
-- the field.
module adequacy.Engine.Fresh where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_]; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-cancelˡ; ∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; n≤1+n; ≤-trans; <⇒≱; +-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; Timeline; From; ix; sub; last; tick; done; quiet; emit; stall; close; Frame∞; From∞)
  renaming (at to atᶠ)
open import operation.Key using (Key; at; after)
open import operation.PureObservable using (Tape; play; ending; over; due; rest; opening; module Machine; module Driver)
open import adequacy.Engine.Causal using (Farᴷ; Fut; Aloft⁺; ofFut; Tapes; advance; ahead; keys-map; lanes-map)
open import adequacy.Engine.Room using (Room; aloft-hole)
open import adequacy.Engine.Sown using (Sown; Sownᴷ; inside; framed; Proper; proper-snoc; sown-here; after-sown; sown-mono; sown-ext; sown-trans; sib-apart)

open Machine using (St; pend; connS; cs; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising; closedUp; begin; ofM; _⊕_)

------------------------------------------------------------------------
-- A connect's body sows nowhere at or under its source's place

body-far : ∀ p → Proper p → ∀ {h} → Sownᴷ (p ++ [ ix 0 ]) h → Farᴷ h (at (p ++ [ ix 1 ]))
body-far p pr {after x} s = tt
body-far p pr {at x}    s = λ a b → sib-apart p pr tt tt (λ ()) (sown-trans s a) b

------------------------------------------------------------------------
-- What a begun node plants is sown where it subscribed

-- A tape, and every tape it moves to, playing where `p` sows.
TapeIn : ∀ {A} → Pos → Tape A → Set
TapeIn p (play τ u i t fr) = Sown p u
TapeIn p (ending e)        = Sown p e
TapeIn p over              = ⊤

rest-in : ∀ {A t} p τ e (m : From A t) → Sown p e → TapeIn p (rest τ e m)
rest-in p τ e done           s = s
rest-in p τ e quiet          s = tt
rest-in p τ e (atᶠ t′ le fr) s = framed _ e [] s

advance-in : ∀ {A} p (l : Tape A) → TapeIn p l → TapeIn p (advance l)
advance-in p (play τ u i t (emit a k))  s = s
advance-in p (play τ u i t (stall k))   s = s
advance-in p (play τ u i t (close k))   s = rest-in p τ (u ++ [ last ]) (From∞.force k) (sown-ext [ last ] s)
advance-in p (ending e)                 s = tt
advance-in p over                       s = tt

ahead-in : ∀ {A} p n (l : Tape A) → TapeIn p l → TapeIn p (ahead n l)
ahead-in p zero    l s = s
ahead-in p (suc n) l s = ahead-in p n (advance l) (advance-in p l s)

opening-in : ∀ {A} p (m : From A 0) → TapeIn p (opening p m)
opening-in p (atᶠ zero le b)    = sown-here p
opening-in p (atᶠ (suc t) le b) = framed _ (p ++ [ last ]) [] (inside [ last ])
opening-in p done               = inside [ last ]
opening-in p quiet              = tt

due-in : ∀ {A} p (l : Tape A) {h} → TapeIn p l → due l ≡ just h → Sownᴷ p h
due-in p (play τ u i t fr) s refl = sown-ext [ ix i ] s
due-in p (ending e)        s refl = s
due-in p over              s ()

tapes-sown : ∀ {A} p (m : From A 0) {h} → Tapes (opening p m) h → Sownᴷ p h
tapes-sown p m (n , e) = due-in p (ahead n (opening p m)) (ahead-in p n (opening p m) (opening-in p m)) e

ofFut-sown : ∀ i p {A} (xs : List A) {m h} → (m , h) ∈ ofFut i p xs → Sownᴷ p h
ofFut-sown i p []       (here refl)  = inside [ last ]
ofFut-sown i p []       (there ())
ofFut-sown i p (_ ∷ xs) (here refl)  = inside [ ix i ]
ofFut-sown i p (_ ∷ xs) (there w)    = ofFut-sown (suc i) p xs w

-- A connect begun: its one mark, at its source's place.
conn-sown : ∀ {Γ X A} p (s : St Γ X) (b : St (X ∷ Γ) A) {h}
          → Fut (connS (cs false true false (just p) nothing nothing (p ⊕ [ ix 1 ]) (ix 0 ∷ [])) s b) h → Sownᴷ p h
conn-sown p s b (_ , here refl) = inside [ ix 1 ]
conn-sown p s b (_ , there ())

------------------------------------------------------------------------
-- The field

-- Below the run's root, room for, and aloft, every key the subscription
-- can plant.
FreshS : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Pos → Set
FreshS c (pend o) p = Proper p × Room (Sownᴷ p) c × (∀ {h} → Sownᴷ p h → Aloft⁺ h c (pend o))
FreshS c _        p = ⊤

Subscribing : ∀ {A} → Mode A → Set
Subscribing subscribing = ⊤
Subscribing _           = ⊥

Fresh : ∀ {R} → Conf R → Set
Fresh ⟨ c , s , m , p ⟩ = Subscribing m → FreshS c s p

-- Room for more, room for less.
room-mono : ∀ {R Γ A} {N M : Key → Set} (c : Ctx R Γ A) → (∀ {h} → N h → M h) → Room M c → Room N c
room-mono top                               g r                    = tt
room-mono (inMap f c)                       g r                    = room-mono c g r
room-mono (inScan f z c)                    g r                    = room-mono c g r
room-mono (inCut l a c)                     g r                    = room-mono c g r
room-mono (inLn b c)                        g r                    = room-mono c g r
room-mono (inTake i q w c)                  g r                    = room-mono c g r
room-mono (inOuter op f d n q ls c)         g (kl , r)             = lanes-map (λ cl {h} n′ → cl (g n′)) ls kl , room-mono c g r
room-mono (inLanes op f d n q o pre post c) g (ko , kp , kq , r)   =
  keys-map (λ cl {h} n′ → cl (g n′)) o ko , lanes-map (λ cl {h} n′ → cl (g n′)) pre kp , lanes-map (λ cl {h} n′ → cl (g n′)) post kq , room-mono c g r
room-mono (inSrc kk b c)                    g (kb , r)             = keys-map (λ cl → (λ {h} n′ → proj₁ cl (g n′)) , (λ {h} n′ → proj₂ cl (g n′))) b kb , room-mono c g r
room-mono (inBody kk o c)                   g (ko , r)             = keys-map (λ cl {h} n′ → cl (g n′)) o ko , room-mono c g r

------------------------------------------------------------------------
-- A begin hands it down

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; took)

  NextFresh : Step → Set
  NextFresh (silent t k)    = Fresh k
  NextFresh (value t p a k) = Fresh k
  NextFresh (complete p)    = ⊤
  NextFresh drained         = ⊤

  -- A child begun at or under its parent's place, under frames racing
  -- nothing keyed.
  begin-fresh : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → FreshS c (pend o) p → NextFresh (took (begin c o p))
  begin-fresh c (cold x)          p (pr , r , a) = λ ()
  begin-fresh c empty             p (pr , r , a) = λ ()
  begin-fresh c (of xs)           p (pr , r , a) = λ ()
  begin-fresh c (map f s)         p (pr , r , a) = λ _ → pr , r , λ h → aloft-hole c (a h)
  begin-fresh c (scan f z s)      p (pr , r , a) = λ _ → pr , r , λ h → aloft-hole c (a h)
  begin-fresh c (takeWhile i q s) p (pr , r , a) = λ _ → pr , r , λ h → aloft-hole c (a h)
  begin-fresh c (flatMap op f s)  p (pr , r , a) = λ _ → pr , (tt , r) , λ h → tt , aloft-hole c (a h)
  begin-fresh c (connect s b)     p (pr , r , a) = λ _ → proper-snoc p (ix 0) ,
    (((λ { (_ , ()) }) , tt) , room-mono c (sown-mono p [ ix 0 ]) r) ,
    λ {h} sh → ((λ { (_ , ()) }) , tt) , ((λ { (_ , ()) }) , tt)
             , (λ { (_ , here refl) → body-far p pr sh ; (_ , there ()) })
             , aloft-hole c (a (sown-mono p [ ix 0 ] sh))
  begin-fresh c (connected x)     p (pr , r , a) with closedUp c x
  ... | true  = λ ()
  ... | false = λ ()
  begin-fresh c (defer l)         p (pr , r , a) = λ _ → proper-snoc p (ix 1) , room-mono c (sown-mono p [ ix 1 ]) r , λ h → aloft-hole c (a (sown-mono p [ ix 1 ] h))
