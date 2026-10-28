{-# OPTIONS --guardedness #-}

-- A SUBSCRIPTION'S ROOM, STORED (`Fresh`): where a configuration
-- subscribes at `p`, every frame above holds aloft each key a
-- subscription at `p` can plant (`Plant p`: strictly under `p`, or past
-- it), so every part racing it has room for them.  Where an event rises
-- at `p`, the same of what a subscription there would plant, and its
-- own subtree far from them (`Risen`): what a rise begins is planted
-- there.  A begin hands it down (`begin-fresh`): a child subscribes at
-- or under its parent's place, and the frames a begin opens race
-- nothing keyed.  What a begun node plants is planted where it
-- subscribed (`tapes-plant`, `ofFut-plant`).
module adequacy.Engine.Fresh where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; [_]; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (<-irrefl; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; Timeline; From; ix; sub; last; tick; done; quiet; emit; stall; close; Frame∞; From∞)
  renaming (at to atᶠ)
open import operation.Key using (Key; at; after)
open import operation.PureObservable using (Tape; play; ending; over; due; rest; opening; module Machine; module Driver)
open import adequacy.Engine.Causal using (Farᴷ; Fut; Every; Keys⁺; Aloft⁺; ofFut; Tapes; advance; ahead; keys-map; lanes-map; cut-same;
  cut-fut; own-conn; owned)
open import adequacy.Engine.Room using (Room; Shy; aloft-hole; lanes-rev; keys-all; lanes-all; lanes-ʳ++)
open import adequacy.Engine.Sown using (Sown⁺; Plant; Plain; framed; Proper; proper-snoc; sown-here; sown-trans; sib-apart;
  sown⁺-here; sown⁺-trans; plant-sown; plant-under; sown⁺-up)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; joinS; connS; cs; attAt; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; closed; closedUp; begin; start; settle; ended; _⊕_)

------------------------------------------------------------------------
-- What lies apart from a place's plants

-- Nothing a plant of `p` sows sows `p`.
past-far : ∀ p {h} → Plant p h → Farᴷ h (after p)
past-far p {at z}    (inj₁ s) = sown⁺-up s
past-far p {at z}    (inj₂ ())
past-far p {after z} w        = tt

-- A cut at `p`: past every plant of `p`.
cut-far : ∀ {Γ A} p l (s : St Γ A) {h} → Plant p h → Every (Farᴷ h) (cutS l (attAt p) s)
cut-far p l s w (_ , here refl) = past-far p w
cut-far p l s w (_ , there ())

-- A sibling's place: apart from every plant of another.
sib-far : ∀ p → Proper p → ∀ {a b} → Plain a → Plain b → a ≢ b → ∀ {h} → Plant (p ++ [ a ]) h → Farᴷ h (at (p ++ [ b ]))
sib-far p pr pa pb ne {after z} w = tt
sib-far p pr pa pb ne {at z}    w = λ x y → sib-apart p pr pa pb ne (sown-trans (plant-sown w) x) y

-- A connect's body plants nowhere at or under its source's place.
body-far : ∀ p → Proper p → ∀ {h} → Plant (p ++ [ ix 0 ]) h → Farᴷ h (at (p ++ [ ix 1 ]))
body-far p pr = sib-far p pr tt tt (λ ())

------------------------------------------------------------------------
-- What a begun node plants is planted where it subscribed

-- A tape, and every tape it moves to, playing strictly under `p`.
TapeIn : ∀ {A} → Pos → Tape A → Set
TapeIn p (play τ u i t fr) = ∀ l → Sown⁺ p (u ++ [ l ])
TapeIn p (ending e)        = Sown⁺ p e
TapeIn p over              = ⊤

rest-in : ∀ {A t} p τ e (m : From A t) → Sown⁺ p e → TapeIn p (rest τ e m)
rest-in p τ e done           s = s
rest-in p τ e quiet          s = tt
rest-in p τ e (atᶠ t′ le fr) s = λ l → sown⁺-trans s (framed _ e [ l ] (sown-here e))

advance-in : ∀ {A} p (l : Tape A) → TapeIn p l → TapeIn p (advance l)
advance-in p (play τ u i t (emit a k))  s = s
advance-in p (play τ u i t (stall k))   s = s
advance-in p (play τ u i t (close k))   s = rest-in p τ (u ++ [ last ]) (From∞.force k) (s last)
advance-in p (ending e)                 s = tt
advance-in p over                       s = tt

ahead-in : ∀ {A} p n (l : Tape A) → TapeIn p l → TapeIn p (ahead n l)
ahead-in p zero    l s = s
ahead-in p (suc n) l s = ahead-in p n (advance l) (advance-in p l s)

opening-in : ∀ {A} p (m : From A 0) → TapeIn p (opening p m)
opening-in p (atᶠ zero le b)    = sown⁺-here p
opening-in p (atᶠ (suc t) le b) = λ l → sown⁺-trans (sown⁺-here p last) (framed _ (p ++ [ last ]) [ l ] (sown-here _))
opening-in p done               = sown⁺-here p last
opening-in p quiet              = tt

due-in : ∀ {A} p (l : Tape A) {h} → TapeIn p l → due l ≡ just h → Plant p h
due-in p (play τ u i t fr) s refl = inj₁ (s (ix i))
due-in p (ending e)        s refl = inj₁ s
due-in p over              s ()

tapes-plant : ∀ {A} p (m : From A 0) {h} → Tapes (opening p m) h → Plant p h
tapes-plant p m (n , e) = due-in p (ahead n (opening p m)) (ahead-in p n (opening p m) (opening-in p m)) e

ofFut-plant : ∀ i p {A} (xs : List A) {m h} → (m , h) ∈ ofFut i p xs → Plant p h
ofFut-plant i p []       (here refl)  = inj₁ (sown⁺-here p last)
ofFut-plant i p []       (there ())
ofFut-plant i p (_ ∷ xs) (here refl)  = inj₁ (sown⁺-here p (ix i))
ofFut-plant i p (_ ∷ xs) (there w)    = ofFut-plant (suc i) p xs w

-- An of's values and completion still to come: apart from a past value's plants.
ofFut-far : ∀ p → Proper p → ∀ i j {A} (xs : List A) → i < j → ∀ {m k h} → (m , k) ∈ ofFut j p xs → Plant (p ++ [ ix i ]) h → Farᴷ h k
ofFut-far p pr i j []       lt (here refl) w = sib-far p pr tt tt (λ ()) w
ofFut-far p pr i j []       lt (there ())  w
ofFut-far p pr i j (_ ∷ xs) lt (here refl) w = sib-far p pr tt tt (λ { refl → <-irrefl refl lt }) w
ofFut-far p pr i j (_ ∷ xs) lt (there v)   w = ofFut-far p pr i (suc j) xs (m<n⇒m<1+n lt) v w

-- A connect begun: its one mark, at its source's place.
conn-plant : ∀ {Γ X A} p (s : St Γ X) (b : St (X ∷ Γ) A) {h}
           → Fut (connS (cs false true false (just p) nothing nothing (p ⊕ [ ix 1 ]) (ix 0 ∷ [])) s b) h → Plant p h
conn-plant p s b (_ , here refl) = inj₁ (sown⁺-here p (ix 1))
conn-plant p s b (_ , there ())

------------------------------------------------------------------------
-- The field

-- Below the run's root, and aloft every key the subscription can plant.
FreshS : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Pos → Set
FreshS c (pend o) p = Proper p × (∀ {h} → Plant p h → Aloft⁺ h c (pend o))
FreshS c _        p = ⊤

shy-under : ∀ p l {k} → Shy p k → Shy (p ++ [ l ]) k
shy-under p l sh w = sh (plant-under p l w)

-- Risen at `p`: below the run's root, the hole's every key far from what
-- a subscription at `p` would plant, and every frame above holding them aloft.
Risen : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Pos → Set
Risen c s p = Proper p × Keys⁺ (Shy p) s × (∀ {h} → Plant p h → Aloft⁺ h c s)

Fresh : ∀ {R} → Conf R → Set
Fresh ⟨ c , s , subscribing , p ⟩ = FreshS c s p
Fresh ⟨ c , s , rising e , p ⟩    = Risen c s p
Fresh ⟨ c , s , absorbed , p ⟩    = ⊤

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

-- A lane ended: its keys kept.
keys-ended : ∀ {Γ A} {P : Key → Set} (s : St Γ A) → Keys⁺ P s → Keys⁺ P (ended s)
keys-ended (lnS b (cutS l a s))      (e , ec , k) = (λ { (_ , ()) }) , (λ {_} f → ec (cut-fut {l = l} {l′ = false} {a = a} {a′ = a} {s = s} {s′ = s} cut-same f)) , k
keys-ended (lnS b (pend o))                k = k
keys-ended (lnS b (coldS x l))             k = k
keys-ended (lnS b (ofS i p xs))            k = k
keys-ended (lnS b doneS)                   k = k
keys-ended (lnS b (mapS f s))              k = k
keys-ended (lnS b (scanS f z s))           k = k
keys-ended (lnS b (lnS x s))               k = k
keys-ended (lnS b (takeS i q w s))         k = k
keys-ended (lnS b (flatS op f d n q o ls)) k = k
keys-ended (lnS b (connS kk o x))          k = k
keys-ended (lnS b (joinS j g x ib))        k = k
keys-ended (pend o)                        k = k
keys-ended (coldS x l)                     k = k
keys-ended (ofS i p xs)                    k = k
keys-ended doneS                           k = k
keys-ended (mapS f s)                      k = k
keys-ended (scanS f z s)                   k = k
keys-ended (cutS l a s)                    k = k
keys-ended (takeS i q w s)                 k = k
keys-ended (flatS op f d n q o ls)         k = k
keys-ended (connS kk o x)                  k = k
keys-ended (joinS j g x ib)                k = k

-- A body's end owed: one key more, past where it rose.
conn-owed : ∀ {Γ X A} k (o : St Γ X) (b : St (X ∷ Γ) A) p {h} → Fut (connS (record k { owedAt = just p }) o b) h → Fut (connS k o b) h ⊎ h ≡ after p
conn-owed (cs cl sl sa (just q) (just r) ow t e) o b p (_ , here refl)                 = inj₁ (_ , here refl)
conn-owed (cs cl sl sa (just q) (just r) ow t e) o b p (_ , there (here refl))         = inj₁ (_ , there (here refl))
conn-owed (cs cl sl sa (just q) (just r) ow t e) o b p (_ , there (there (here refl))) = inj₂ refl
conn-owed (cs cl sl sa (just q) (just r) ow t e) o b p (_ , there (there (there ())))
conn-owed (cs cl sl sa (just q) nothing  ow t e) o b p (_ , here refl)                 = inj₁ (_ , here refl)
conn-owed (cs cl sl sa (just q) nothing  ow t e) o b p (_ , there (here refl))         = inj₂ refl
conn-owed (cs cl sl sa (just q) nothing  ow t e) o b p (_ , there (there ()))
conn-owed (cs cl sl sa nothing  (just r) ow t e) o b p (_ , here refl)                 = inj₁ (_ , here refl)
conn-owed (cs cl sl sa nothing  (just r) ow t e) o b p (_ , there (here refl))         = inj₂ refl
conn-owed (cs cl sl sa nothing  (just r) ow t e) o b p (_ , there (there ()))
conn-owed (cs cl sl sa nothing  nothing  ow t e) o b p (_ , here refl)                 = inj₂ refl
conn-owed (cs cl sl sa nothing  nothing  ow t e) o b p (_ , there ())

-- What holds of a connect's keys, and past where its body rose, holds once it is owed.
owed-to : ∀ {Γ X A} {P : Key → Set} k {o o′ : St Γ X} {b b′ : St (X ∷ Γ) A} p → P (after p) → Every P (connS k o b)
        → Every P (connS (record k { owedAt = just p }) o′ b′)
owed-to k {o} {o′} {b} {b′} p pa e f with conn-owed k o′ b′ p f
... | inj₁ f′   = e (owned (own-conn k {o′} {o} {b′} {b}) f′)
... | inj₂ refl = pa

-- Settled: risen if it rises.
settle-fresh : ∀ {R Γ A} {c : Ctx R Γ A} {s : St Γ A} {p} d n e → Risen c s p → Fresh ⟨ c , s , settle d n e , p ⟩
settle-fresh d n e r with d ∧ (n ≡ᵇ 0) ∧ e
... | true  = r
... | false = tt

-- A lane started where a value rose, one level down.
start-fresh : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
            → ∀ {d′ n′ q′} → Risen c (flatS op f d′ n′ q′ o ls) p → Fresh (start c op f d n q o ls a p)
start-fresh c op f d n q o ls a p r with closed c
... | true  = tt
start-fresh c op f d n q o ls a p (pr , (_ , ko , kl) , g) | false = proper-snoc p (ix 1) , λ {h} w →
  let w′ = plant-under p (ix 1) w in
  cut-far (p ++ [ ix 1 ]) true (pend (f a)) w , keys-map (λ sh → sh w′) o ko , lanes-rev ls (lanes-map (λ sh → sh w′) ls kl) , tt , aloft-hole c (g w′)

-- An outer's value or end risen: the flatMap holds its lanes shy.
outer-risen : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls {o : St Γ A} {p} d′
            → Risen (inOuter op f d n q ls c) o p → Risen c (flatS op f d′ n q o ls) p
outer-risen c op f d n q ls d′ (pr , ks , a) =
  pr , ((λ { (_ , ()) }) , ks , lanes-all ls (λ w → proj₁ (a w))) , λ w → aloft-hole c (proj₂ (a w))

-- A lane's value or end risen: the flatMap holds its outer and lanes shy.
lanes-risen : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post {s : St Γ B} {p} n′ (s′ : St Γ B)
            → Keys⁺ (Shy p) s′ → Risen (inLanes op f d n q o pre post c) s p → Risen c (flatS op f d n′ q o (pre ʳ++ s′ ∷ post)) p
lanes-risen c op f d n q o pre post n′ s′ ks′ (pr , ks , a) =
  pr , ((λ { (_ , ()) }) , keys-all o (λ w → proj₁ (a w)) , lanes-ʳ++ pre (lanes-all pre (λ w → proj₁ (proj₂ (a w)))) (ks′ , lanes-all post (λ w → proj₁ (proj₂ (proj₂ (a w))))))
  , λ w → aloft-hole c (proj₂ (proj₂ (proj₂ (a w))))

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
  begin-fresh c (cold x)          p (pr , a) = tt
  begin-fresh c empty             p (pr , a) = tt
  begin-fresh c (of xs)           p (pr , a) = tt
  begin-fresh c (map f s)         p (pr , a) = pr , λ w → aloft-hole c (a w)
  begin-fresh c (scan f z s)      p (pr , a) = pr , λ w → aloft-hole c (a w)
  begin-fresh c (takeWhile i q s) p (pr , a) = pr , λ w → cut-far p true (pend s) w , aloft-hole c (a w)
  begin-fresh c (flatMap op f s)  p (pr , a) = pr , λ w → cut-far p true (pend s) w , tt , aloft-hole c (a w)
  begin-fresh c (connect s b)     p (pr , a) = proper-snoc p (ix 0) ,
    λ {h} w → ((λ { (_ , ()) }) , tt) , ((λ { (_ , ()) }) , tt)
             , (λ { (_ , here refl) → body-far p pr w ; (_ , there ()) })
             , aloft-hole c (a (plant-under p (ix 0) w))
  begin-fresh c (connected x)     p (pr , a) with closedUp c x
  ... | true  = tt
  ... | false = tt
  begin-fresh c (defer l)         p (pr , a) = proper-snoc p (ix 1) , λ w → aloft-hole c (a (plant-under p (ix 1) w))
