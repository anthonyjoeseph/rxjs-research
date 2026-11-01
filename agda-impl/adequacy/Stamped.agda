{-# OPTIONS --guardedness #-}

-- EVERY POSITION IS STAMPED: every position a run keeps begins with a
-- tick, and every cold's cascade is stamped no later than its frame.
-- No step of the engine makes a position but by extending one it holds,
-- or by a frame's cascade at its own tick; so the stamp holds of every
-- conf a run reaches, live subtree or not.  Likewise a run subscribing
-- has its pending subscription in focus: a connect's source stays
-- pending until its body's run subscribes it.
module adequacy.Stamped where

open import Data.Bool using (true; false; not; if_then_else_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; _+_; _≤_; _<ᵇ_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoʳ-≤; m<m+n; +-identityʳ; +-suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Level using (Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect;
  connected; defer)
open import denotation.Events using (Pos; ix; last; tick; _<ᵖ_; <ᵖ-below; <ᵖ-part; <ᵖ-asym; ix-<; From; From∞; done; quiet; at; emit;
  stall; close; timelineAt)
open import operation.PureObservable using (PureObs; module Machine; module Driver; opening; due; Tape; rest; play; ending) renaming (over to overT)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; Mode; Att; attAt; attached; Owe; free; cpAt; cutAt; overAt; Ev; nx; cp; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising;
                    unsub; cut; killAll; unsubIf; feed; feedL; queued; inbox; same?; rise; run; begin; start; dequeue; admit; ended; shutAt; closed; closedUp; alive; settle;
                    search; found; Stepped; moved; starting; turn; quiet; Poke; gone; leaf; own; leafM; joinM)
open import operation.Key using (Key; _<ᴷ_; at-<ᴷ) renaming (at to atᴷ)
open import adequacy.Dispatch using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-mark; found-least; found-plug)
open import adequacy.Path using (Path; []; tau; val)

------------------------------------------------------------------------
-- The stamp

Ix : Pos → Set
Ix (ix _ ∷ _) = ⊤
Ix _          = ⊥

ix-⊕ : ∀ p q → Ix p → Ix (p ++ q)
ix-⊕ (ix _ ∷ _) q _ = tt

TapeOK : ∀ {A} → Tape A → Set
TapeOK (play τ u i t fr) = Ix u × tick u ≤ τ + t
TapeOK (ending e)        = Ix e
TapeOK overT             = ⊤

MOK : Maybe Pos → Set
MOK (just p) = Ix p
MOK nothing  = ⊤

AttOK : Att → Set
AttOK attached  = ⊤
AttOK (attAt p) = Ix p

OweOK : Owe → Set
OweOK free       = ⊤
OweOK (cpAt p)   = Ix p
OweOK (cutAt p)  = Ix p
OweOK (overAt p) = Ix p

CSOK : ∀ {Γ X} → CS Γ X → Set
CSOK k = MOK (CS.bodyAt k) × MOK (CS.attSrc k) × MOK (CS.owedAt k)

-- An entry no earlier than the one before it.
Behind : ∀ {A} → Pos → List (Pos × Ev A) → Set
Behind q []            = ⊤
Behind q ((r , _) ∷ _) = r <ᵖ q ≡ false

-- An inbox stamped and in position order.
QOK : ∀ {A} → List (Pos × Ev A) → Set
QOK []             = ⊤
QOK ((q , _) ∷ ib) = Ix q × Behind q ib × QOK ib

-- A pending subscription, at a position.
IsPend : ∀ {Γ A} → St Γ A → Pos → Set
IsPend (pend o q) r = q ≡ r
IsPend _          _ = ⊥

NotPend : ∀ {Γ A} → St Γ A → Set
NotPend (pend o q) = ⊥
NotPend _          = ⊤

-- A connect whose body is yet to run keeps its source pending where that
-- run subscribes it.
BodyOK : ∀ {Γ A} → Maybe Pos → St Γ A → Set
BodyOK (just p) o = IsPend o (p ++ [ ix 1 ])
BodyOK nothing  o = ⊤

Unbodied : Maybe Pos → Set
Unbodied (just _) = ⊥
Unbodied nothing  = ⊤

-- A subscribing run is at its pending subscription.
ModeOK : ∀ {Γ A} → Mode A → St Γ A → Pos → Set
ModeOK subscribing s p = IsPend s p
ModeOK _           s p = ⊤

mutual
  StOK : ∀ {Γ A} → St Γ A → Set
  StOK (pend o q)             = Ix q
  StOK (coldS b l)            = TapeOK l
  StOK (ofS i p xs)           = Ix p
  StOK doneS                  = ⊤
  StOK (mapS f s)             = StOK s
  StOK (scanS f z s)          = StOK s
  StOK (cutS l a s)           = AttOK a × StOK s
  StOK (lnS b s)              = StOK s
  StOK (takeS i q w s)        = OweOK w × StOK s
  StOK (flatS op f d n q o ls) = StOK o × LOK ls
  StOK (connS k o b)          = CSOK k × StOK o × StOK b × BodyOK (CS.bodyAt k) o
  StOK (joinS j g x ib)       = Ix j × QOK ib

  LOK : ∀ {Γ A} → List (St Γ A) → Set
  LOK []       = ⊤
  LOK (s ∷ ls) = StOK s × LOK ls

CtxOK : ∀ {R Γ A} → Ctx R Γ A → Set
CtxOK top                               = ⊤
CtxOK (inMap f c)                       = CtxOK c
CtxOK (inScan f z c)                    = CtxOK c
CtxOK (inCut l a c)                     = AttOK a × CtxOK c
CtxOK (inLn b c)                        = CtxOK c
CtxOK (inTake i p w c)                  = OweOK w × CtxOK c
CtxOK (inOuter op f d n q ls c)         = LOK ls × CtxOK c
CtxOK (inLanes op f d n q o pre post c) = StOK o × LOK pre × LOK post × CtxOK c
CtxOK (inSrc k b c)                     = CSOK k × StOK b × CtxOK c × Unbodied (CS.bodyAt k)
CtxOK (inBody k o c)                    = CSOK k × StOK o × CtxOK c × BodyOK (CS.bodyAt k) o

ConfOK : ∀ {R} → Conf R → Set
ConfOK ⟨ c , s , m , p ⟩ = CtxOK c × StOK s × Ix p × ModeOK m s p

------------------------------------------------------------------------
-- Pending subscriptions

pend-not : ∀ {Γ A} (s : St Γ A) {r} → IsPend s r → NotPend s → ⊥
pend-not (pend o q)              _ ()
pend-not (coldS b l)             () _
pend-not (ofS i p xs)            () _
pend-not doneS                   () _
pend-not (mapS f s)              () _
pend-not (scanS f z s)           () _
pend-not (cutS l a s)            () _
pend-not (lnS b s)               () _
pend-not (takeS i q w s)         () _
pend-not (flatS op f d n q o ls) () _
pend-not (connS k o b)           () _
pend-not (joinS j g x ib)        () _

-- What holds of every pending subscription at `r` holds of one.
is-pend : ∀ {Γ A} (s : St Γ A) {r} → IsPend s r → (P : St Γ A → Set) → (∀ o → P (pend o r)) → P s
is-pend (pend o q) refl P h = h o
is-pend (coldS b l)             () P h
is-pend (ofS i p xs)            () P h
is-pend doneS                   () P h
is-pend (mapS f s)              () P h
is-pend (scanS f z s)           () P h
is-pend (cutS l a s)            () P h
is-pend (lnS b s)               () P h
is-pend (takeS i q w s)         () P h
is-pend (flatS op f d n q o ls) () P h
is-pend (connS k o b)           () P h
is-pend (joinS j g x ib)        () P h

pend-of : ∀ {Γ A} (s : St Γ A) {r} → IsPend s r → Σ _ λ o → s ≡ pend o r
pend-of (pend o q) refl = o , refl
pend-of (coldS b l)             ()
pend-of (ofS i p xs)            ()
pend-of doneS                   ()
pend-of (mapS f s)              ()
pend-of (scanS f z s)           ()
pend-of (cutS l a s)            ()
pend-of (lnS b s)               ()
pend-of (takeS i q w s)         ()
pend-of (flatS op f d n q o ls) ()
pend-of (connS k o b)           ()
pend-of (joinS j g x ib)        ()

-- A node a mark is on is no pending subscription.
own-notpend : ∀ {Γ A} (s : St Γ A) {x} → x ∈ own s → NotPend s
own-notpend (pend o q)              ()
own-notpend (coldS b l)             _ = tt
own-notpend (ofS i p xs)            _ = tt
own-notpend doneS                   _ = tt
own-notpend (mapS f s)              _ = tt
own-notpend (scanS f z s)           _ = tt
own-notpend (cutS l a s)            _ = tt
own-notpend (lnS b s)               _ = tt
own-notpend (takeS i q w s)         _ = tt
own-notpend (flatS op f d n q o ls) _ = tt
own-notpend (connS k o b)           _ = tt
own-notpend (joinS j g x ib)        _ = tt

unbodied-ok : ∀ {Γ A} m (s : St Γ A) → Unbodied m → BodyOK m s
unbodied-ok nothing  s _ = tt
unbodied-ok (just p) s ()

body-unbodied : ∀ {Γ A} m (s : St Γ A) → NotPend s → BodyOK m s → Unbodied m
body-unbodied nothing  s np h = tt
body-unbodied (just p) s np h = pend-not s h np

body-unsub : ∀ {Γ A} m (o : St Γ A) → BodyOK m o → BodyOK m (proj₁ (unsub o))
body-unsub nothing  o h = tt
body-unsub (just p) o h = is-pend o h (λ o′ → IsPend (proj₁ (unsub o′)) (p ++ [ ix 1 ])) (λ _ → refl)

body-unsubIf : ∀ {Γ A} b m (o : St Γ A) → BodyOK m o → BodyOK m (proj₁ (unsubIf b o))
body-unsubIf true  m o h = body-unsub m o h
body-unsubIf false m o h = h

body-feed : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) m (o : St Γ A) → BodyOK m o → BodyOK m (feed i p e o)
body-feed i p e nothing  o h = tt
body-feed i p e (just r) o h = is-pend o h (λ o′ → IsPend (feed i p e o′) (r ++ [ ix 1 ])) (λ _ → refl)

mode-if : ∀ {Γ A} b {x y : Mode A} {s : St Γ A} {p} → ModeOK x s p → ModeOK y s p → ModeOK (if b then x else y) s p
mode-if true  hx hy = hx
mode-if false hx hy = hy

------------------------------------------------------------------------
-- Lists and plugging

lok-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {post} → LOK pre → LOK post → LOK (pre ʳ++ post)
lok-ʳ++ []        _        hp = hp
lok-ʳ++ (s ∷ pre) (h , hs) hp = lok-ʳ++ pre hs (h , hp)

lok-ʳ++⁻ : ∀ {Γ A} (pre : List (St Γ A)) {post} → LOK (pre ʳ++ post) → LOK pre × LOK post
lok-ʳ++⁻ []        h = tt , h
lok-ʳ++⁻ (s ∷ pre) h with lok-ʳ++⁻ pre h
... | hs , (h₁ , hp) = (h₁ , hs) , hp

behind-inbox : ∀ {A} r (v : Pos × Ev A) ib → Behind r ib → proj₁ v <ᵖ r ≡ false → Behind r (inbox v ib)
behind-inbox r v       []              _  hv = hv
behind-inbox r (q , e) ((r′ , e′) ∷ ib) hb hv with r′ <ᵖ q
... | true  = hb
... | false = hv

qok-inbox : ∀ {A} (v : Pos × Ev A) ib → Ix (proj₁ v) → QOK ib → QOK (inbox v ib)
qok-inbox v       []              hv _             = hv , tt , tt
qok-inbox (q , e) ((r , e′) ∷ ib) hv (h , hb , hs) with r <ᵖ q in lt
... | true  = h , behind-inbox r (q , e) ib hb (<ᵖ-asym r q lt) , qok-inbox (q , e) ib hv hs
... | false = hv , lt , h , hb , hs

plug-ok : ∀ {R Γ A} (c : Ctx R Γ A) {s} → CtxOK c → StOK s → StOK (plug c s)
plug-ok top                               hc                    hs = hs
plug-ok (inMap f c)                       hc                    hs = plug-ok c hc hs
plug-ok (inScan f z c)                    hc                    hs = plug-ok c hc hs
plug-ok (inCut l a c)                     (ha , hc)             hs = plug-ok c hc (ha , hs)
plug-ok (inLn b c)                        hc                    hs = plug-ok c hc hs
plug-ok (inTake i p w c)                  (hw , hc)             hs = plug-ok c hc (hw , hs)
plug-ok (inOuter op f d n q ls c)         (hl , hc)             hs = plug-ok c hc (hs , hl)
plug-ok (inLanes op f d n q o pre post c) (ho , hpr , hpo , hc) hs = plug-ok c hc (ho , lok-ʳ++ pre hpr (hs , hpo))
plug-ok (inSrc k b c)                     (hk , hb , hc , hu)   hs = plug-ok c hc (hk , hs , hb , unbodied-ok (CS.bodyAt k) _ hu)
plug-ok (inBody k o c)                    (hk , ho , hc , hbo)  hs = plug-ok c hc (hk , ho , hs , hbo)

unplug : ∀ {R Γ A} (c : Ctx R Γ A) {s} → NotPend s → StOK (plug c s) → CtxOK c × StOK s
unplug top                               np h = tt , h
unplug (inMap f c)                       np h = unplug c tt h
unplug (inScan f z c)                    np h = unplug c tt h
unplug (inCut l a c)                     np h with unplug c tt h
... | hc , (ha , hs) = (ha , hc) , hs
unplug (inLn b c)                        np h = unplug c tt h
unplug (inTake i p w c)                  np h with unplug c tt h
... | hc , (hw , hs) = (hw , hc) , hs
unplug (inOuter op f d n q ls c)         np h with unplug c tt h
... | hc , (hs , hl) = (hl , hc) , hs
unplug (inLanes op f d n q o pre post c) np h with unplug c tt h
... | hc , (ho , hl) with lok-ʳ++⁻ pre hl
...   | hpr , (hs , hpo) = (ho , hpr , hpo , hc) , hs
unplug (inSrc k b c) {s}                 np h with unplug c tt h
... | hc , (hk , hs , hb , hbo) = (hk , hb , hc , body-unbodied (CS.bodyAt k) s np hbo) , hs
unplug (inBody k o c)                    np h with unplug c tt h
... | hc , (hk , ho , hs , hbo) = (hk , ho , hc , hbo) , hs

------------------------------------------------------------------------
-- Teardown and feed keep the stamp

mutual
  unsub-ok : ∀ {Γ A} (s : St Γ A) → StOK s → StOK (proj₁ (unsub s))
  unsub-ok (coldS true l)          h          = h
  unsub-ok (coldS false l)         h          = h
  unsub-ok (mapS f s)              h          = unsub-ok s h
  unsub-ok (scanS f z s)           h          = unsub-ok s h
  unsub-ok (takeS i p w s)         (hw , hs)  = hw , cut-ok s hs
  unsub-ok (flatS op f d n q o ls) (ho , hl)  = cut-ok o ho , killAll-ok ls hl
  unsub-ok (connS k o b)           (hk , ho , hb , hbo) = hk , unsub-ok o ho , unsub-ok b hb , body-unsub (CS.bodyAt k) o hbo
  unsub-ok (joinS j g x ib)        (hj , _)   = hj , tt
  unsub-ok (pend o q)              h          = h
  unsub-ok (ofS i p xs)            h          = h
  unsub-ok doneS                   h          = h
  unsub-ok (cutS l a s)            h          = h
  unsub-ok (lnS b s)               h          = h

  cut-ok : ∀ {Γ A} (s : St Γ A) → StOK s → StOK (proj₁ (cut s))
  cut-ok (cutS l attached s)  (ha , hs) = tt , unsub-ok s hs
  cut-ok (cutS l (attAt p) s) h         = h
  cut-ok (pend o q)              h = h
  cut-ok (coldS b l)             h = h
  cut-ok (ofS i p xs)            h = h
  cut-ok doneS                   h = h
  cut-ok (mapS f s)              h = h
  cut-ok (scanS f z s)           h = h
  cut-ok (lnS b s)               h = h
  cut-ok (takeS i q w s)         h = h
  cut-ok (flatS op f d n q o ls) h = h
  cut-ok (connS k o b)           h = h
  cut-ok (joinS j g x ib)        h = h

  killAll-ok : ∀ {Γ B} (ls : List (St Γ B)) → LOK ls → LOK (proj₁ (killAll ls))
  killAll-ok []                         _         = tt
  killAll-ok (lnS true s ∷ ls)          (h , hs)  = cut-ok s h , killAll-ok ls hs
  killAll-ok (lnS false s ∷ ls)         (h , hs)  = h , killAll-ok ls hs
  killAll-ok (pend o q ∷ ls)            (h , hs)  = h , killAll-ok ls hs
  killAll-ok (coldS b l ∷ ls)           (h , hs)  = h , killAll-ok ls hs
  killAll-ok (ofS i p xs ∷ ls)          (h , hs)  = h , killAll-ok ls hs
  killAll-ok (doneS ∷ ls)               (h , hs)  = h , killAll-ok ls hs
  killAll-ok (mapS f s ∷ ls)            (h , hs)  = h , killAll-ok ls hs
  killAll-ok (scanS f z s ∷ ls)         (h , hs)  = h , killAll-ok ls hs
  killAll-ok (cutS l a s ∷ ls)          (h , hs)  = h , killAll-ok ls hs
  killAll-ok (takeS i q w s ∷ ls)       (h , hs)  = h , killAll-ok ls hs
  killAll-ok (flatS op f d n q o l ∷ ls) (h , hs) = h , killAll-ok ls hs
  killAll-ok (connS k o b ∷ ls)         (h , hs)  = h , killAll-ok ls hs
  killAll-ok (joinS j g x ib ∷ ls)      (h , hs)  = h , killAll-ok ls hs

unsubIf-ok : ∀ {Γ A} b (s : St Γ A) → StOK s → StOK (proj₁ (unsubIf b s))
unsubIf-ok true  s h = unsub-ok s h
unsubIf-ok false s h = h

queued-ok : ∀ {A} j p (e : Ev A) ib → Ix j → Ix p → QOK ib → QOK (queued j p e ib)
queued-ok j p (nx a) ib hj hp hb with j <ᵖ p
... | true  = qok-inbox _ ib (ix-⊕ p _ hp) hb
... | false = hb
queued-ok j p cp ib hj hp hb with j <ᵖ p
... | true  = qok-inbox _ ib (ix-⊕ p _ hp) hb
... | false = qok-inbox _ ib (ix-⊕ j _ hj) hb

mutual
  feed-ok : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (s : St Γ A) → Ix p → StOK s → StOK (feed i p e s)
  feed-ok i p e (joinS j true x ib) hp (hj , hb) with same? i x
  ... | just refl = hj , queued-ok j p e ib hj hp hb
  ... | nothing   = hj , hb
  feed-ok i p e (joinS j false x ib)    hp h          = h
  feed-ok i p e (mapS f s)              hp h          = feed-ok i p e s hp h
  feed-ok i p e (scanS f z s)           hp h          = feed-ok i p e s hp h
  feed-ok i p e (cutS l a s)            hp (ha , hs)  = ha , feed-ok i p e s hp hs
  feed-ok i p e (lnS b s)               hp h          = feed-ok i p e s hp h
  feed-ok i p e (takeS v q w s)         hp (hw , hs)  = hw , feed-ok i p e s hp hs
  feed-ok i p e (flatS op f d n q o ls) hp (ho , hl)  = feed-ok i p e o hp ho , feedL-ok i p e ls hp hl
  feed-ok i p e (connS k o b)           hp (hk , ho , hb , hbo) = hk , feed-ok i p e o hp ho , feed-ok (there i) p e b hp hb , body-feed i p e (CS.bodyAt k) o hbo
  feed-ok i p e (pend o q)              hp h          = h
  feed-ok i p e (coldS b l)             hp h          = h
  feed-ok i p e (ofS j q xs)            hp h          = h
  feed-ok i p e doneS                   hp h          = h

  feedL-ok : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (ls : List (St Γ A)) → Ix p → LOK ls → LOK (feedL i p e ls)
  feedL-ok i p e []       hp _        = tt
  feedL-ok i p e (s ∷ ls) hp (h , hs) = feed-ok i p e s hp h , feedL-ok i p e ls hp hs

ended-ok : ∀ {Γ B} (s : St Γ B) → StOK s → StOK (ended s)
ended-ok (lnS b (cutS l a s))    h = h
ended-ok (lnS b (pend o q))      h = h
ended-ok (lnS b (coldS x l))     h = h
ended-ok (lnS b (ofS i p xs))    h = h
ended-ok (lnS b doneS)           h = h
ended-ok (lnS b (mapS f s))      h = h
ended-ok (lnS b (scanS f z s))   h = h
ended-ok (lnS b (lnS x s))       h = h
ended-ok (lnS b (takeS i q w s)) h = h
ended-ok (lnS b (flatS op f d n q o ls)) h = h
ended-ok (lnS b (connS k o x))   h = h
ended-ok (lnS b (joinS j g x ib)) h = h
ended-ok (pend o q)              h = h
ended-ok (coldS b l)             h = h
ended-ok (ofS i p xs)            h = h
ended-ok doneS                   h = h
ended-ok (mapS f s)              h = h
ended-ok (scanS f z s)           h = h
ended-ok (cutS l a s)            h = h
ended-ok (takeS i q w s)         h = h
ended-ok (flatS op f d n q o ls) h = h
ended-ok (connS k o b)           h = h
ended-ok (joinS j g x ib)        h = h

------------------------------------------------------------------------
-- A step keeps the stamp

-- What a step hands on is stamped: a conf, or a conf for every stamped
-- tape the runtime gives back.
↑ : Set → Set₁
↑ X = Lift (lsuc lzero) X

SOK : ∀ {R} → Stepped R → Set₁
SOK (moved k _ _)              = ↑ (ConfOK k)
SOK (starting x p k)           = ↑ (Ix p) × (∀ l → TapeOK l → ConfOK (k l))
SOK (turn gone)                = ↑ ⊤
SOK (turn (leaf b l cl dv st)) = ↑ (TapeOK l) × (∀ e l′ b′ p′ → TapeOK l′ → Ix p′ → ConfOK (dv e l′ b′ p′)) × (∀ l′ → TapeOK l′ → ConfOK (st l′))
SOK quiet                      = ↑ ⊤

begin-ok : ∀ {R Γ A} (c : Ctx R Γ A) (o : PureObs Γ A) p → CtxOK c → Ix p → SOK (begin c o p)
begin-ok c (cold x)          p hc hp = lift hp , λ l hl → hc , hl , hp , tt
begin-ok c empty             p hc hp = lift (hc , hp , hp , tt)
begin-ok c (of xs)           p hc hp = lift (hc , hp , hp , tt)
begin-ok c (map f s)         p hc hp = lift (hc , hp , hp , refl)
begin-ok c (scan f z s)      p hc hp = lift (hc , hp , hp , refl)
begin-ok c (takeWhile i q s) p hc hp = lift ((hp , tt , hc) , hp , hp , refl)
begin-ok c (flatMap op f s)  p hc hp = lift ((hp , tt , hc) , hp , hp , refl)
begin-ok c (connect s b)     p hc hp = lift (((hp , tt , tt) , ix-⊕ p _ hp , hc , refl) , ix-⊕ p _ hp , ix-⊕ p _ hp , refl)
begin-ok c (connected x)     p hc hp with closedUp c x
... | true  = lift (hc , hp , hp , tt)
... | false = lift (hc , (hp , tt) , hp , tt)
begin-ok c (defer l)         p hc hp = lift (hc , ix-⊕ p _ hp , ix-⊕ p _ hp , refl)

start-ok : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls a p → CtxOK c → StOK o → LOK ls → Ix p
         → ConfOK (start c op f d n q o ls a p)
start-ok c op f d n q o ls a p hc ho hl hp with closed c
... | true  = hc , (ho , hl) , hp , tt
... | false = (ix-⊕ p _ hp , ho , lok-ʳ++ ls hl tt , tt , hc) , ix-⊕ p _ hp , ix-⊕ p _ hp , refl

dequeue-ok : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls p → CtxOK c → StOK o → LOK ls → Ix p
           → ConfOK (dequeue c op f d n q o ls p)
dequeue-ok c op f d n []      o ls p hc ho hl hp = hc , (ho , hl) , hp , mode-if (d ∧ (n ≡ᵇ 0) ∧ true) tt tt
dequeue-ok c op f d n (a ∷ q) o ls p hc ho hl hp = start-ok c op f d n q o ls a p hc ho hl hp

admit-ok : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls a p → CtxOK c → StOK o → LOK ls → Ix p
         → SOK (admit c op f d n q o ls a p)
admit-ok c (mergeᶠ nothing)  f d n q o ls a p hc ho hl hp = lift (start-ok c _ f d n q o ls a p hc ho hl hp)
admit-ok c (mergeᶠ (just m)) f d n q o ls a p hc ho hl hp with n <ᵇ m
... | true  = lift (start-ok c _ f d n q o ls a p hc ho hl hp)
... | false = lift (hc , (ho , hl) , hp , tt)
admit-ok c switchᶠ           f d n q o ls a p hc ho hl hp with killAll ls | killAll-ok ls hl
... | ls′ , t | hl′ = lift (start-ok c _ f d 0 q o ls′ a p hc ho hl′ hp)
admit-ok c exhaustᶠ          f d n q o ls a p hc ho hl hp with n ≡ᵇ 0
... | true  = lift (start-ok c _ f d n q o ls a p hc ho hl hp)
... | false = lift (hc , (ho , hl) , hp , tt)

rise-ok : ∀ {R Γ A} (c : Ctx R Γ A) s (e : Ev A) p → CtxOK c → StOK s → Ix p → SOK (rise c s e p)
rise-ok top                 s e      p hc hs hp = lift (tt , hs , hp , tt)
rise-ok (inMap f c)         s e      p hc hs hp = lift (hc , hs , hp , tt)
rise-ok (inScan f z c)      s (nx a) p hc hs hp = lift (hc , hs , hp , tt)
rise-ok (inScan f z c)      s cp     p hc hs hp = lift (hc , hs , hp , tt)
rise-ok (inCut l a c)       s e      p (ha , hc) hs hp = lift (hc , (ha , hs) , hp , mode-if l tt tt)
rise-ok (inLn b c)          s e      p hc hs hp = lift (hc , hs , hp , tt)
rise-ok (inTake i q free c) s (nx a) p (_ , hc) hs hp with q a | i
... | true  | _     = lift (hc , (tt , hs) , hp , tt)
... | false | true  = lift (hc , (hp , hs) , ix-⊕ p _ hp , tt)
... | false | false = lift (hc , (hp , hs) , hp , tt)
rise-ok (inTake i q free c)       s cp p (_ , hc)  hs hp = lift (hc , (tt , hs) , hp , tt)
rise-ok (inTake i q (cpAt r) c)   s e  p (hw , hc) hs hp = lift (hc , (hw , hs) , hp , tt)
rise-ok (inTake i q (cutAt r) c)  s e  p (hw , hc) hs hp = lift (hc , (hw , hs) , hp , tt)
rise-ok (inTake i q (overAt r) c) s e  p (hw , hc) hs hp = lift (hc , (hw , hs) , hp , tt)
rise-ok (inOuter op f d n q ls c) o (nx a) p (hl , hc) ho hp = admit-ok c op f d n q o ls a p hc ho hl hp
rise-ok (inOuter op f d n q ls c) o cp     p (hl , hc) ho hp = lift (hc , (ho , hl) , hp , mode-if d tt (mode-if (true ∧ (n ≡ᵇ 0) ∧ null q) tt tt))
rise-ok (inLanes op f d n q o pre post c) s (nx b) p (ho , hpr , hpo , hc) hs hp with alive s
... | true  = lift (hc , (ho , lok-ʳ++ pre hpr (hs , hpo)) , hp , tt)
... | false = lift (hc , (ho , lok-ʳ++ pre hpr (hs , hpo)) , hp , tt)
rise-ok (inLanes op f d n q o pre post c) s cp     p (ho , hpr , hpo , hc) hs hp with alive s
... | true  = lift (dequeue-ok c op f d _ q o (pre ʳ++ ended s ∷ post) p hc ho (lok-ʳ++ pre hpr (ended-ok s hs , hpo)) hp)
... | false = lift (hc , (ho , lok-ʳ++ pre hpr (hs , hpo)) , hp , tt)
rise-ok (inSrc k b c) s (nx a) p (hk , hb , hc , hu) hs hp = lift (hc , (hk , hs , feed-ok (here refl) p (nx a) b hp hb , unbodied-ok (CS.bodyAt k) s hu) , hp , tt)
rise-ok (inSrc (cs cl true sa ba as ow ca ea sr sc) b c)  s cp p (hk , hb , hc , hu) hs hp = lift (hc , (hk , hs , feed-ok (here refl) p cp b hp hb , unbodied-ok ba s hu) , hp , tt)
rise-ok (inSrc (cs cl false sa ba as ow ca ea sr sc) b c) s cp p (hk , hb , hc , hu) hs hp = lift (hc , (hk , hs , feed-ok (here refl) p cp b hp hb , unbodied-ok ba s hu) , hp , tt)
rise-ok (inBody (cs cl true sa ba as ow ca ea sr sc) o c)  s (nx b) p (hk , ho , hc , hbo) hs hp = lift (hc , (hk , ho , hs , hbo) , hp , tt)
rise-ok (inBody (cs cl false sa ba as ow ca ea sr sc) o c) s (nx b) p (hk , ho , hc , hbo) hs hp = lift (hc , (hk , ho , hs , hbo) , hp , tt)
rise-ok (inBody (cs cl true sa ba as ow ca ea sr sc) o c)  s cp p ((hba , has , _) , ho , hc , hbo) hs hp = lift (hc , ((hba , has , hp) , ho , hs , hbo) , hp , tt)
rise-ok (inBody (cs cl false sa ba as ow ca ea sr sc) o c) s cp p (hk , ho , hc , hbo) hs hp = lift (hc , (hk , ho , hs , hbo) , hp , tt)

run-ok : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} → Marked s m → ∀ r → CtxOK c → StOK s → Ix r → SOK (run c s m r)
run-ok c (ofK i p xs) r hc hs hr with closed c | xs
... | true  | _       = lift (hc , tt , hs , tt)
... | false | []      = lift (hc , tt , ix-⊕ p _ hs , tt)
... | false | x ∷ xs′ = lift (hc , hs , ix-⊕ p _ hs , tt)
run-ok c (attK l p s) r hc (hp , hs) hr with unsubIf (not l) s | unsubIf-ok (not l) s hs
... | s′ , t | h = lift (hc , (tt , h) , hp , tt)
run-ok c (conK (cs cl sl sa (just p) as ow ca ea sr sc) o b _ (inj₁ refl)) r hc ((hp , has , how) , ho , hb , hbo) hr =
  lift (((tt , ix-⊕ p _ hp , how) , hb , hc , tt) , ho , ix-⊕ p _ hp , hbo)
run-ok c (conK (cs cl sl sa nothing as ow ca ea sr sc) o b _ (inj₁ refl)) r hc hs hr = lift (hc , hs , hr , tt)
run-ok c (conK (cs cl sl sa ba (just p) ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) r hc ((hba , hp , how) , ho , hb , hbo) hr
  with unsubIf (not sl) o | unsubIf-ok (not sl) o ho | body-unsubIf (not sl) ba o hbo
... | o′ , t | h | hbo′ = lift (hc , ((hba , tt , how) , h , hb , hbo′) , hp , tt)
run-ok c (conK (cs cl sl sa ba nothing ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) r hc hs hr = lift (hc , hs , hr , tt)
run-ok c (conK (cs cl sl sa ba as (just p) ca ea sr sc) o b _ (inj₂ (inj₂ refl))) r hc ((hba , has , hp) , ho , hb , hbo) hr
  with unsubIf sa o | unsubIf-ok sa o ho | body-unsubIf sa ba o hbo
... | o′ , t | h | hbo′ = lift (hc , ((hba , has , tt) , h , hb , hbo′) , hp , tt)
run-ok c (conK (cs cl sl sa ba as nothing ca ea sr sc) o b _ (inj₂ (inj₂ refl))) r hc hs hr = lift (hc , hs , hr , tt)
run-ok c (joinK j g x q (nx a) ib) r hc (hj , hq , _ , hb) hr = lift (hc , (hj , hb) , hq , mode-if (g ∧ not (closed c)) tt tt)
run-ok c (joinK j g x q cp ib)     r hc (hj , hq , _ , hb) hr = lift (hc , (hj , hb) , hq , mode-if (g ∧ not (closed c)) tt tt)
run-ok c (leafK b l) r hc hl hr = lift hl , (λ e l′ b′ p′ hl′ hp′ → hc , hl′ , hp′ , mode-if (not (closed c)) tt tt) , (λ l′ hl′ → hc , hl′ , hr , tt)
run-ok c (stopK i q p s) r hc (hp , hs) hr = lift (hc , (hp , hs) , ix-⊕ p _ hp , mode-if (not (closed c)) tt tt)
run-ok c (cutK i q p s) r hc (hp , hs) hr with cut s | cut-ok s hs
... | s′ , t | h = lift (hc , (hp , h) , hp , tt)

step-ok : ∀ {R} (k : Conf R) → ConfOK k → SOK (Machine.step k)
step-ok ⟨ c , s , rising e , p ⟩ (hc , hs , hp , _) = rise-ok c s e p hc hs hp
step-ok ⟨ c , pend o q , subscribing , p ⟩ (hc , hq , hp , _) = begin-ok c o q hc hq
step-ok ⟨ c , coldS b l , subscribing , p ⟩ h = lift h
step-ok ⟨ c , ofS i q xs , subscribing , p ⟩ h = lift h
step-ok ⟨ c , doneS , subscribing , p ⟩ h = lift h
step-ok ⟨ c , mapS f s , subscribing , p ⟩ h = lift h
step-ok ⟨ c , scanS f z s , subscribing , p ⟩ h = lift h
step-ok ⟨ c , cutS l a s , subscribing , p ⟩ h = lift h
step-ok ⟨ c , lnS b s , subscribing , p ⟩ h = lift h
step-ok ⟨ c , takeS i q w s , subscribing , p ⟩ h = lift h
step-ok ⟨ c , flatS op f d n q o ls , subscribing , p ⟩ h = lift h
step-ok ⟨ c , connS k o b , subscribing , p ⟩ h = lift h
step-ok ⟨ c , joinS j g x ib , subscribing , p ⟩ h = lift h
step-ok ⟨ c , s , absorbed , p ⟩ (hc , hs , hp , _) with search top (plug c s) in fd
... | nothing = lift tt
... | just (found (_ , _ , c′ , s′) m κ)
  with unplug c′ (own-notpend s′ (proj₁ (found-least {t = plug c s} fd))) (subst StOK (sym (found-plug c s fd)) (plug-ok c hc hs))
...   | hc′ , hs′ = run-ok c′ (found-mark c s fd) p hc′ hs′ hp

------------------------------------------------------------------------
-- The runtime's tapes

rest-ok : ∀ {A t} τ e (m : From A t) → Ix e → TapeOK (rest τ e m)
rest-ok τ e done          he = he
rest-ok τ e quiet         he = tt
rest-ok τ e (at t′ _ fr)  he = tt , ≤-refl

opening-ok : ∀ {A} p (m : From A 0) → Ix p → TapeOK (opening p m)
opening-ok p (at zero _ b)    hp = hp , ≤-reflexive (sym (+-identityʳ (tick p)))
opening-ok p done             hp = ix-⊕ p _ hp
opening-ok p quiet            hp = tt
opening-ok p (at (suc t) _ b) hp = tt , ≤-refl

module _ {R : Set} where
  open Driver R using (took; played; silent; value)

  played-ok : (pk : Poke R) → SOK (turn pk) → ∀ {t k′} → played pk ≡ silent t k′ → ConfOK k′
  played-ok gone _ ()
  played-ok (leaf true (ending e) cl dv st) (lift he , d , s) refl = d cp overT false e tt he
  played-ok (leaf false l cl dv st) (_ , d , s) refl = s overT tt
  played-ok (leaf true (play τ u i t fr) true dv st) (_ , d , s) refl = s overT tt
  played-ok (leaf true overT true dv st) (_ , d , s) refl = s overT tt
  played-ok (leaf true (play τ u i t (emit a k)) false dv st) (lift (hu , ht) , d , s) refl =
    d (nx a) (play τ u (suc i) t k) true (u ++ [ ix i ]) (hu , ht) (ix-⊕ u _ hu)
  played-ok (leaf true (play τ u i t (stall k)) false dv st) (lift (hu , ht) , d , s) refl = s _ (hu , ht)
  played-ok (leaf true (play τ u i t (close k)) false dv st) (lift (hu , ht) , d , s) refl =
    s _ (rest-ok τ (u ++ [ last ]) (From∞.force k) (ix-⊕ u _ hu))
  played-ok (leaf true overT false dv st) (_ , d , s) refl = s overT tt

  played-val : (pk : Poke R) → ∀ {t p a k′} → played pk ≡ value t p a k′ → ⊥
  played-val gone ()
  played-val (leaf true (ending e) cl dv st) ()
  played-val (leaf false l cl dv st) ()
  played-val (leaf true (play τ u i t fr) true dv st) ()
  played-val (leaf true overT true dv st) ()
  played-val (leaf true (play τ u i t (emit a k)) false dv st) ()
  played-val (leaf true (play τ u i t (stall k)) false dv st) ()
  played-val (leaf true (play τ u i t (close k)) false dv st) ()
  played-val (leaf true overT false dv st) ()

  took-silent : (x : Stepped R) → SOK x → ∀ {t k′} → took x ≡ silent t k′ → ConfOK k′
  took-silent (moved k [] _)               (lift h) refl = h
  took-silent (moved k ((p , nx a) ∷ _) _) _ ()
  took-silent (moved k ((p , cp) ∷ _) _)   _ ()
  took-silent (starting x p k) (lift hp , f) refl = f _ (opening-ok p (timelineAt x p) hp)
  took-silent (turn pk) h e = played-ok pk h e
  took-silent quiet _ ()

  took-value : (x : Stepped R) → SOK x → ∀ {t p a k′} → took x ≡ value t p a k′ → ConfOK k′
  took-value (moved k [] _)               _ ()
  took-value (moved k ((p , nx a) ∷ _) _) (lift h) refl = h
  took-value (moved k ((p , cp) ∷ _) _)   _ ()
  took-value (starting x p k) _ ()
  took-value (turn pk) _ e = ⊥-elim (played-val pk e)
  took-value quiet _ ()

  path-ok : ∀ {k k″ rs} → ConfOK k → Path k rs k″ → ConfOK k″
  path-ok h []          = h
  path-ok h (tau {k} e pth) = path-ok (took-silent (Machine.step k) (step-ok k h) e) pth
  path-ok h (val {k} e pth) = path-ok (took-value (Machine.step k) (step-ok k h) e) pth

-- EVERY CONF A RUN REACHES IS STAMPED.
stamped : ∀ {R} (o : PureObs [] R) {rs k} → Path (load o) rs k → ConfOK k
stamped o pth = path-ok (tt , tt , tt , refl) pth

------------------------------------------------------------------------
-- Consequences

-- A COLD'S NEXT FRAME IS AHEAD: a cold closing its frame comes due next
-- strictly after the due it played.
next-ahead : ∀ {A} τ u i {t} (m : From A (suc t)) {κ′} → Ix u → tick u ≤ τ + t
           → due (rest τ (u ++ [ last ]) m) ≡ just κ′ → atᴷ (u ++ [ ix i ]) <ᴷ κ′ ≡ true
next-ahead τ u i done hu ht refl = trans (at-<ᴷ (u ++ [ ix i ]) (u ++ [ last ])) (<ᵖ-part u {ix i} {last} [] [] refl)
next-ahead τ u i quiet hu ht ()
next-ahead τ (ix h ∷ u′) i {t} (at t′ le fr) hu ht refl =
  trans (at-<ᴷ (ix h ∷ u′ ++ [ ix i ]) (ix (τ + t′) ∷ _)) (<ᵖ-part [] {ix h} {ix (τ + t′)} (u′ ++ [ ix i ]) _ (ix-< (≤-trans (s≤s ht) (subst (_≤ τ + t′) (+-suc τ t) (+-monoʳ-≤ τ le)))))

frame-ahead : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q Γ′ A′} {c′ : Ctx R Γ′ A′} {b τ u i t f κ κ′}
            → Path (load o) rs ⟨ c , s , absorbed , q ⟩
            → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS b (play τ u i t (close f))) leafM κ)
            → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true
frame-ahead o {c = c} {s} {c′ = c′} {τ = τ} {u} {i} {f = f} pth fd dr with stamped o pth
... | hc , hs , _ with unplug c′ tt (subst StOK (sym (found-plug c s fd)) (plug-ok c hc hs)) | proj₁ (found-least {t = plug c s} fd)
...   | _ , (hu , ht) | here refl = next-ahead τ u i (From∞.force f) hu ht dr

-- A JOINER'S INBOX ASCENDS: the entry behind the head is no earlier.
inbox-asc : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q Γ′ A′} {c′ : Ctx R Γ′ A′} {j g x q₀ e q₁ e₁ ib κ}
          → Path (load o) rs ⟨ c , s , absorbed , q ⟩
          → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , joinS j g x ((q₀ , e) ∷ (q₁ , e₁) ∷ ib)) joinM κ)
          → atᴷ q₁ <ᴷ atᴷ q₀ ≡ false
inbox-asc o {c = c} {s} {c′ = c′} {q₀ = q₀} {q₁ = q₁} pth fd with stamped o pth
... | hc , hs , _ with unplug c′ tt (subst StOK (sym (found-plug c s fd)) (plug-ok c hc hs))
...   | _ , (_ , (_ , b , _)) = trans (at-<ᴷ q₁ q₀) b

-- A COLD OPENS AHEAD: a cold a run subscribes first comes due strictly
-- after where it was subscribed.
open-ahead : ∀ {A} q (m : From A 0) {κ} → Ix q → due (opening q m) ≡ just κ → atᴷ q <ᴷ κ ≡ true
open-ahead q (at zero _ b) hq refl = trans (at-<ᴷ q _) (<ᵖ-below q [])
open-ahead q done hq refl = trans (at-<ᴷ q _) (<ᵖ-below q [])
open-ahead q quiet hq ()
open-ahead (ix h ∷ q′) (at (suc t′) _ b) hq refl =
  trans (at-<ᴷ (ix h ∷ q′) (ix (h + suc t′) ∷ _)) (<ᵖ-part [] {ix h} {ix (h + suc t′)} q′ _ (ix-< (m<m+n h (s≤s z≤n))))

opening-ahead : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {x q κ}
              → Path (load o) rs ⟨ c , pend (cold x) q , subscribing , q ⟩
              → due (opening q (timelineAt x q)) ≡ just κ → atᴷ q <ᴷ κ ≡ true
opening-ahead o {x = x} {q} pth dk with stamped o pth
... | _ , hq , _ = open-ahead q (timelineAt x q) hq dk

-- A SUBSCRIBING RUN IS AT ITS SUBSCRIPTION: every conf a run reaches
-- subscribing has a pending subscription in focus, owed where the run is.
pend-focus : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q}
           → Path (load o) rs ⟨ c , s , subscribing , q ⟩ → Σ (PureObs Γ A) λ o′ → s ≡ pend o′ q
pend-focus o {s = s} pth with stamped o pth
... | _ , _ , _ , hm = pend-of s hm
