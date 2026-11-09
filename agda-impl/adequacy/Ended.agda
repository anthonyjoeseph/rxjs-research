{-# OPTIONS --guardedness #-}

-- A CLOSED SUBJECT ENDED BEHIND THE CLOCK: every connect a run has
-- closed ended no later than the run's clock.  The engine closes a
-- connect only rising its source's end, at that rise's own position,
-- which is the clock there; every other step copies the flag and the
-- end, and the clock never runs back.  So a run subscribing at `q`
-- reads every closed subject in scope as ended at or before `q`.
module adequacy.Ended where

open import Level using (Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Data.Bool using (true; false; T; not; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect;
  connected; defer)
open import denotation.Events using (Pos; emit; stall; close)
open import denotation.EmissionSet using (_≼_)
open import operation.PureObservable using (PureObs; module Machine; module Driver; play; ending) renaming (over to overT)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; attAt; attached; free; cpAt; cutAt; overAt; Ev; nx; cp; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising;
                    unsub; cut; killAll; unsubIf; off; offL; offIf; feed; feedL; same?; rise; run; begin; start; dequeue; admit; ended; shutAt; closed; closedUp; alive;
                    search; found; Stepped; moved; starting; turn; quiet; Poke; gone; leaf)
open import operation.Key using (Key; at; after; at-<ᴷ)
open import adequacy.Least using (Lo)
open import adequacy.Found using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-mark; found-plug)
open import adequacy.Path using (Path; []; tau; val; _▸_; _⊑_; ⊑-trans)
open import adequacy.Weight using (Clock)
open import adequacy.Apart.Floor using (floor)
open import adequacy.Floor using (clock-abs; clock-mono)
open import adequacy.Floor.Keys using (lo-weaken; at-after₀; ⊑-refl)
open import adequacy.Stamped using (played-val)

------------------------------------------------------------------------
-- Every closed connect ended no later than `κ`

CE : ∀ {Γ X} → Key → CS Γ X → Set
CE κ k = T (CS.closed k) → at (CS.endAt k) ⊑ κ

mutual
  StE : ∀ {Γ A} → Key → St Γ A → Set
  StE κ (mapS f s)                = StE κ s
  StE κ (scanS f z s)             = StE κ s
  StE κ (cutS l a s)              = StE κ s
  StE κ (lnS b s)                 = StE κ s
  StE κ (takeS i q w s)           = StE κ s
  StE κ (flatS op f ω d n q o ls) = StE κ o × LE κ ls
  StE κ (connS k o b)             = CE κ k × StE κ o × StE κ b
  StE κ (pend o q)                = ⊤
  StE κ (coldS b l)               = ⊤
  StE κ (ofS i p xs)              = ⊤
  StE κ doneS                     = ⊤
  StE κ (joinS j g x ib)          = ⊤

  LE : ∀ {Γ A} → Key → List (St Γ A) → Set
  LE κ []       = ⊤
  LE κ (s ∷ ls) = StE κ s × LE κ ls

CtxE : ∀ {R Γ A} → Key → Ctx R Γ A → Set
CtxE κ top                                 = ⊤
CtxE κ (inMap f c)                         = CtxE κ c
CtxE κ (inScan f z c)                      = CtxE κ c
CtxE κ (inCut l a c)                       = CtxE κ c
CtxE κ (inLn b c)                          = CtxE κ c
CtxE κ (inTake i p w c)                    = CtxE κ c
CtxE κ (inOuter op f ω d n q ls c)         = LE κ ls × CtxE κ c
CtxE κ (inLanes op f ω d n q o pre post c) = StE κ o × LE κ pre × LE κ post × CtxE κ c
CtxE κ (inSrc k b c)                       = CE κ k × StE κ b × CtxE κ c
CtxE κ (inBody k o c)                      = CE κ k × StE κ o × CtxE κ c

ConfE : ∀ {R} → Key → Conf R → Set
ConfE κ ⟨ c , s , m , p ⟩ = CtxE κ c × StE κ s

------------------------------------------------------------------------
-- A later key keeps it

ce-mono : ∀ {Γ X κ κ′} (k : CS Γ X) → κ ⊑ κ′ → CE κ k → CE κ′ k
ce-mono k le h t = ⊑-trans (h t) le

mutual
  st-mono : ∀ {Γ A κ κ′} (s : St Γ A) → κ ⊑ κ′ → StE κ s → StE κ′ s
  st-mono (mapS f s)                le h              = st-mono s le h
  st-mono (scanS f z s)             le h              = st-mono s le h
  st-mono (cutS l a s)              le h              = st-mono s le h
  st-mono (lnS b s)                 le h              = st-mono s le h
  st-mono (takeS i q w s)           le h              = st-mono s le h
  st-mono (flatS op f ω d n q o ls) le (ho , hl)      = st-mono o le ho , le-mono ls le hl
  st-mono (connS k o b)             le (hk , ho , hb) = ce-mono k le hk , st-mono o le ho , st-mono b le hb
  st-mono (pend o q)                le h              = tt
  st-mono (coldS b l)               le h              = tt
  st-mono (ofS i p xs)              le h              = tt
  st-mono doneS                     le h              = tt
  st-mono (joinS j g x ib)          le h              = tt

  le-mono : ∀ {Γ A κ κ′} (ls : List (St Γ A)) → κ ⊑ κ′ → LE κ ls → LE κ′ ls
  le-mono []       le _        = tt
  le-mono (s ∷ ls) le (h , hs) = st-mono s le h , le-mono ls le hs

ctx-mono : ∀ {R Γ A κ κ′} (c : Ctx R Γ A) → κ ⊑ κ′ → CtxE κ c → CtxE κ′ c
ctx-mono top                                 le h                     = tt
ctx-mono (inMap f c)                         le h                     = ctx-mono c le h
ctx-mono (inScan f z c)                      le h                     = ctx-mono c le h
ctx-mono (inCut l a c)                       le h                     = ctx-mono c le h
ctx-mono (inLn b c)                          le h                     = ctx-mono c le h
ctx-mono (inTake i p w c)                    le h                     = ctx-mono c le h
ctx-mono (inOuter op f ω d n q ls c)         le (hl , hc)             = le-mono ls le hl , ctx-mono c le hc
ctx-mono (inLanes op f ω d n q o pre post c) le (ho , hpr , hpo , hc) = st-mono o le ho , le-mono pre le hpr , le-mono post le hpo , ctx-mono c le hc
ctx-mono (inSrc k b c)                       le (hk , hb , hc)        = ce-mono k le hk , st-mono b le hb , ctx-mono c le hc
ctx-mono (inBody k o c)                      le (hk , ho , hc)        = ce-mono k le hk , st-mono o le ho , ctx-mono c le hc

------------------------------------------------------------------------
-- Lists and plugging

module _ {κ : Key} where
  le-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {post} → LE κ pre → LE κ post → LE κ (pre ʳ++ post)
  le-ʳ++ []        _        hp = hp
  le-ʳ++ (s ∷ pre) (h , hs) hp = le-ʳ++ pre hs (h , hp)

  le-ʳ++⁻ : ∀ {Γ A} (pre : List (St Γ A)) {post} → LE κ (pre ʳ++ post) → LE κ pre × LE κ post
  le-ʳ++⁻ []        h = tt , h
  le-ʳ++⁻ (s ∷ pre) h with le-ʳ++⁻ pre h
  ... | hs , (h₁ , hp) = (h₁ , hs) , hp

  plug-e : ∀ {R Γ A} (c : Ctx R Γ A) {s} → CtxE κ c → StE κ s → StE κ (plug c s)
  plug-e top                                 hc                    hs = hs
  plug-e (inMap f c)                         hc                    hs = plug-e c hc hs
  plug-e (inScan f z c)                      hc                    hs = plug-e c hc hs
  plug-e (inCut l a c)                       hc                    hs = plug-e c hc hs
  plug-e (inLn b c)                          hc                    hs = plug-e c hc hs
  plug-e (inTake i p w c)                    hc                    hs = plug-e c hc hs
  plug-e (inOuter op f ω d n q ls c)         (hl , hc)             hs = plug-e c hc (hs , hl)
  plug-e (inLanes op f ω d n q o pre post c) (ho , hpr , hpo , hc) hs = plug-e c hc (ho , le-ʳ++ pre hpr (hs , hpo))
  plug-e (inSrc k b c)                       (hk , hb , hc)        hs = plug-e c hc (hk , hs , hb)
  plug-e (inBody k o c)                      (hk , ho , hc)        hs = plug-e c hc (hk , ho , hs)

  unplug-e : ∀ {R Γ A} (c : Ctx R Γ A) {s} → StE κ (plug c s) → CtxE κ c × StE κ s
  unplug-e top                                 h = tt , h
  unplug-e (inMap f c)                         h = unplug-e c h
  unplug-e (inScan f z c)                      h = unplug-e c h
  unplug-e (inCut l a c)                       h = unplug-e c h
  unplug-e (inLn b c)                          h = unplug-e c h
  unplug-e (inTake i p w c)                    h = unplug-e c h
  unplug-e (inOuter op f ω d n q ls c)         h with unplug-e c h
  ... | hc , (hs , hl) = (hl , hc) , hs
  unplug-e (inLanes op f ω d n q o pre post c) h with unplug-e c h
  ... | hc , (ho , hl) with le-ʳ++⁻ pre hl
  ...   | hpr , (hs , hpo) = (ho , hpr , hpo , hc) , hs
  unplug-e (inSrc k b c)                       h with unplug-e c h
  ... | hc , (hk , hs , hb) = (hk , hb , hc) , hs
  unplug-e (inBody k o c)                      h with unplug-e c h
  ... | hc , (hk , ho , hs) = (hk , ho , hc) , hs

------------------------------------------------------------------------
-- Teardown and feed copy every flag

  mutual
    unsub-e : ∀ {Γ A} (s : St Γ A) → StE κ s → StE κ (proj₁ (unsub s))
    unsub-e (coldS true l)            h              = tt
    unsub-e (coldS false l)           h              = tt
    unsub-e (mapS f s)                h              = unsub-e s h
    unsub-e (scanS f z s)             h              = unsub-e s h
    unsub-e (takeS i p w s)           h              = cut-e s h
    unsub-e (flatS op f ω d n q o ls) (ho , hl)      = cut-e o ho , killAll-e ls hl
    unsub-e (connS k o b)             (hk , ho , hb) = hk , unsubIf-e (CS.srcAtt k) o ho , unsub-e b hb
    unsub-e (joinS j g x ib)          h              = tt
    unsub-e (pend o q)                h              = h
    unsub-e (ofS i p xs)              h              = h
    unsub-e doneS                     h              = h
    unsub-e (cutS l a s)              h              = h
    unsub-e (lnS b s)                 h              = h

    cut-e : ∀ {Γ A} (s : St Γ A) → StE κ s → StE κ (proj₁ (cut s))
    cut-e (cutS l attached s)       h = unsub-e s h
    cut-e (cutS l (attAt p) s)      h = off-e s h
    cut-e (pend o q)                h = h
    cut-e (coldS b l)               h = h
    cut-e (ofS i p xs)              h = h
    cut-e doneS                     h = h
    cut-e (mapS f s)                h = h
    cut-e (scanS f z s)             h = h
    cut-e (lnS b s)                 h = h
    cut-e (takeS i q w s)           h = h
    cut-e (flatS op f ω d n q o ls) h = h
    cut-e (connS k o b)             h = h
    cut-e (joinS j g x ib)          h = h

    killAll-e : ∀ {Γ B} (ls : List (St Γ B)) → LE κ ls → LE κ (proj₁ (killAll ls))
    killAll-e []                            _        = tt
    killAll-e (lnS true s ∷ ls)             (h , hs) = cut-e s h , killAll-e ls hs
    killAll-e (lnS false s ∷ ls)            (h , hs) = h , killAll-e ls hs
    killAll-e (pend o q ∷ ls)               (h , hs) = h , killAll-e ls hs
    killAll-e (coldS b l ∷ ls)              (h , hs) = h , killAll-e ls hs
    killAll-e (ofS i p xs ∷ ls)             (h , hs) = h , killAll-e ls hs
    killAll-e (doneS ∷ ls)                  (h , hs) = h , killAll-e ls hs
    killAll-e (mapS f s ∷ ls)               (h , hs) = h , killAll-e ls hs
    killAll-e (scanS f z s ∷ ls)            (h , hs) = h , killAll-e ls hs
    killAll-e (cutS l a s ∷ ls)             (h , hs) = h , killAll-e ls hs
    killAll-e (takeS i q w s ∷ ls)          (h , hs) = h , killAll-e ls hs
    killAll-e (flatS op f ω d n q o l ∷ ls) (h , hs) = h , killAll-e ls hs
    killAll-e (connS k o b ∷ ls)            (h , hs) = h , killAll-e ls hs
    killAll-e (joinS j g x ib ∷ ls)         (h , hs) = h , killAll-e ls hs

    unsubIf-e : ∀ {Γ A} b (s : St Γ A) → StE κ s → StE κ (proj₁ (unsubIf b s))
    unsubIf-e true  s h = unsub-e s h
    unsubIf-e false s h = h

    off-e : ∀ {Γ A} (s : St Γ A) → StE κ s → StE κ (off s)
    off-e (mapS f s)                h              = off-e s h
    off-e (scanS f z s)             h              = off-e s h
    off-e (cutS l a s)              h              = off-e s h
    off-e (lnS b s)                 h              = off-e s h
    off-e (takeS i p w s)           h              = off-e s h
    off-e (flatS op f ω d n q o ls) (ho , hl)      = off-e o ho , offL-e ls hl
    off-e (connS k o b)             (hk , ho , hb) = hk , offIf-e (CS.srcAtt k) o ho , off-e b hb
    off-e (joinS j g x ib)          h              = tt
    off-e (pend o q)                h              = h
    off-e (coldS b l)               h              = h
    off-e (ofS i p xs)              h              = h
    off-e doneS                     h              = h

    offL-e : ∀ {Γ A} (ls : List (St Γ A)) → LE κ ls → LE κ (offL ls)
    offL-e []       _        = tt
    offL-e (s ∷ ls) (h , hs) = off-e s h , offL-e ls hs

    offIf-e : ∀ {Γ A} b (s : St Γ A) → StE κ s → StE κ (offIf b s)
    offIf-e true  s h = off-e s h
    offIf-e false s h = h

  mutual
    feed-e : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (s : St Γ A) → StE κ s → StE κ (feed i p e s)
    feed-e i p e (joinS j true x ib) h with same? i x
    ... | just refl = tt
    ... | nothing   = tt
    feed-e i p e (joinS j false x ib)      h              = h
    feed-e i p e (mapS f s)                h              = feed-e i p e s h
    feed-e i p e (scanS f z s)             h              = feed-e i p e s h
    feed-e i p e (cutS l a s)              h              = feed-e i p e s h
    feed-e i p e (lnS b s)                 h              = feed-e i p e s h
    feed-e i p e (takeS v q w s)           h              = feed-e i p e s h
    feed-e i p e (flatS op f ω d n q o ls) (ho , hl)      = feed-e i p e o ho , feedL-e i p e ls hl
    feed-e i p e (connS k o b)             (hk , ho , hb) = hk , feed-e i p e o ho , feed-e (there i) p e b hb
    feed-e i p e (pend o q)                h              = h
    feed-e i p e (coldS b l)               h              = h
    feed-e i p e (ofS j q xs)              h              = h
    feed-e i p e doneS                     h              = h

    feedL-e : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (ls : List (St Γ A)) → LE κ ls → LE κ (feedL i p e ls)
    feedL-e i p e []       _        = tt
    feedL-e i p e (s ∷ ls) (h , hs) = feed-e i p e s h , feedL-e i p e ls hs

  ended-e : ∀ {Γ B} (s : St Γ B) → StE κ s → StE κ (ended s)
  ended-e (lnS b (cutS l a s))              h = h
  ended-e (lnS b (pend o q))                h = h
  ended-e (lnS b (coldS x l))               h = h
  ended-e (lnS b (ofS i p xs))              h = h
  ended-e (lnS b doneS)                     h = h
  ended-e (lnS b (mapS f s))                h = h
  ended-e (lnS b (scanS f z s))             h = h
  ended-e (lnS b (lnS x s))                 h = h
  ended-e (lnS b (takeS i q w s))           h = h
  ended-e (lnS b (flatS op f ω d n q o ls)) h = h
  ended-e (lnS b (connS k o x))             h = h
  ended-e (lnS b (joinS j g x ib))          h = h
  ended-e (pend o q)                        h = h
  ended-e (coldS b l)                       h = h
  ended-e (ofS i p xs)                      h = h
  ended-e doneS                             h = h
  ended-e (mapS f s)                        h = h
  ended-e (scanS f z s)                     h = h
  ended-e (cutS l a s)                      h = h
  ended-e (takeS i q w s)                   h = h
  ended-e (flatS op f ω d n q o ls)         h = h
  ended-e (connS k o b)                     h = h
  ended-e (joinS j g x ib)                  h = h

  -- The one write: a source's end closes its connect where it rose.
  shut-e : ∀ {Γ X} p (k : CS Γ X) → CE κ k → at p ⊑ κ → CE κ (shutAt p k)
  shut-e p k hk hp with CS.srcLive k
  ... | true  = λ _ → hp
  ... | false = hk

------------------------------------------------------------------------
-- A step keeps it: a silent step's at the key given, a shown step's at
-- the clock it moves to.

↑ : Set → Set₁
↑ X = Lift (lsuc lzero) X

module _ {R : Set} where
  SE : Key → Stepped R → Set₁
  SE κ (moved k [] _)              = ↑ (ConfE κ k)
  SE κ (moved k (_ ∷ _) _)         = ↑ (ConfE (Clock k) k)
  SE κ (starting x p k)            = ∀ l → ConfE κ (k l)
  SE κ (turn gone)                 = ↑ ⊤
  SE κ (turn (leaf b l cl dv st))  = (∀ e l′ b′ p′ → ConfE κ (dv e l′ b′ p′)) × (∀ l′ → ConfE κ (st l′))
  SE κ quiet                       = ↑ ⊤

  module _ {κ : Key} where
    begin-e : ∀ {Γ A} (c : Ctx R Γ A) (o : PureObs Γ A) p → CtxE κ c → SE κ (begin c o p)
    begin-e c (cold x)          p hc = λ l → hc , tt
    begin-e c empty             p hc = lift (hc , tt)
    begin-e c (of xs)           p hc = lift (hc , tt)
    begin-e c (map f s)         p hc = lift (hc , tt)
    begin-e c (scan f z s)      p hc = lift (hc , tt)
    begin-e c (takeWhile i q s) p hc = lift (hc , tt)
    begin-e c (flatMap op f s)  p hc = lift ((tt , hc) , tt)
    begin-e c (connect s b)     p hc = lift (((λ ()) , tt , hc) , tt)
    begin-e c (connected x)     p hc with closedUp c x
    ... | true  = lift (hc , tt)
    ... | false = lift (hc , tt)
    begin-e c (defer l)         p hc = lift (hc , tt)

    start-e : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) ω d n q o ls a p → CtxE κ c → StE κ o → LE κ ls
            → ConfE κ (start c op f ω d n q o ls a p)
    start-e c op f ω d n q o ls a p hc ho hl with closed c
    ... | true  = hc , (ho , hl)
    ... | false = (ho , le-ʳ++ ls hl tt , tt , hc) , tt

    dequeue-e : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) ω d n q o ls p → CtxE κ c → StE κ o → LE κ ls
              → ConfE κ (dequeue c op f ω d n q o ls p)
    dequeue-e c op f ω d n []      o ls p hc ho hl = hc , (ho , hl)
    dequeue-e c op f ω d n (a ∷ q) o ls p hc ho hl = start-e c op f ω d n q o ls a p hc ho hl

    admit-e : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) ω d n q o ls a p → CtxE κ c → StE κ o → LE κ ls
            → SE κ (admit c op f ω d n q o ls a p)
    admit-e c (mergeᶠ nothing)  f ω d n q o ls a p hc ho hl = lift (start-e c _ f ω d n q o ls a p hc ho hl)
    admit-e c (mergeᶠ (just m)) f ω d n q o ls a p hc ho hl with n <ᵇ m
    ... | true  = lift (start-e c _ f ω d n q o ls a p hc ho hl)
    ... | false = lift (hc , (ho , hl))
    admit-e c switchᶠ           f ω d n q o ls a p hc ho hl with killAll ls | killAll-e ls hl
    ... | ls′ , t | hl′ = lift (start-e c _ f ω d 0 q o ls′ a p hc ho hl′)
    admit-e c exhaustᶠ          f ω d n q o ls a p hc ho hl with n ≡ᵇ 0
    ... | true  = lift (start-e c _ f ω d n q o ls a p hc ho hl)
    ... | false = lift (hc , (ho , hl))

    -- A rise: the root's shows, at the clock it moves to; any other, at a
    -- key no earlier than where it is.
    rise-e : ∀ {Γ A} (c : Ctx R Γ A) s (e : Ev A) p → StE (at p) s → Lo (plug c s) (after p)
           → CtxE κ c → StE κ s → at p ⊑ κ → SE κ (rise c s e p)
    rise-e top s e p hs₀ fl hc hs hp = lift (tt , st-mono s (clock-abs top s p (lo-weaken (at p) (after p) fl (at-after₀ p))) hs₀)
    rise-e (inMap f c)         s e      p _ _ hc hs hp = lift (hc , hs)
    rise-e (inScan f z c)      s (nx a) p _ _ hc hs hp = lift (hc , hs)
    rise-e (inScan f z c)      s cp     p _ _ hc hs hp = lift (hc , hs)
    rise-e (inCut l a c)       s e      p _ _ hc hs hp = lift (hc , hs)
    rise-e (inLn b c)          s e      p _ _ hc hs hp = lift (hc , hs)
    rise-e (inTake i q free c) s (nx a) p _ _ hc hs hp with q a | i
    ... | true  | _     = lift (hc , hs)
    ... | false | true  = lift (hc , hs)
    ... | false | false = lift (hc , hs)
    rise-e (inTake i q free c)       s cp p _ _ hc hs hp = lift (hc , hs)
    rise-e (inTake i q (cpAt r) c)   s e  p _ _ hc hs hp = lift (hc , hs)
    rise-e (inTake i q (cutAt r) c)  s e  p _ _ hc hs hp = lift (hc , hs)
    rise-e (inTake i q (overAt r) c) s e  p _ _ hc hs hp = lift (hc , hs)
    rise-e (inOuter op f ω d n q ls c) o (nx a) p _ _ (hl , hc) ho hp = admit-e c op f ω d n q o ls a p hc ho hl
    rise-e (inOuter op f ω d n q ls c) o cp     p _ _ (hl , hc) ho hp = lift (hc , (ho , hl))
    rise-e (inLanes op f ω d n q o pre post c) s (nx b) p _ _ (ho , hpr , hpo , hc) hs hp with alive s
    ... | true  = lift (hc , (ho , le-ʳ++ pre hpr (hs , hpo)))
    ... | false = lift (hc , (ho , le-ʳ++ pre hpr (hs , hpo)))
    rise-e (inLanes op f ω d n q o pre post c) s cp     p _ _ (ho , hpr , hpo , hc) hs hp with alive s
    ... | true  = lift (dequeue-e c op f ω d _ q o (pre ʳ++ ended s ∷ post) p hc ho (le-ʳ++ pre hpr (ended-e s hs , hpo)))
    ... | false = lift (hc , (ho , le-ʳ++ pre hpr (hs , hpo)))
    rise-e (inSrc k b c) s (nx a) p _ _ (hk , hb , hc) hs hp = lift (hc , (hk , hs , feed-e (here refl) p (nx a) b hb))
    rise-e (inSrc k b c) s cp     p _ _ (hk , hb , hc) hs hp = lift (hc , (shut-e p k hk hp , hs , feed-e (here refl) p cp b hb))
    rise-e (inBody k o c) s (nx b) p _ _ (hk , ho , hc) hs hp with CS.srcLive k
    ... | true  = lift (hc , (hk , ho , hs))
    ... | false = lift (hc , (hk , ho , hs))
    rise-e (inBody k o c) s cp     p _ _ (hk , ho , hc) hs hp with CS.srcLive k
    ... | true  = lift (hc , (hk , ho , hs))
    ... | false = lift (hc , (hk , ho , hs))

    run-e : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} → Marked s m → ∀ r → CtxE κ c → StE κ s → SE κ (run c s m r)
    run-e c (ofK i p xs) r hc hs with closed c | xs
    ... | true  | _       = lift (hc , tt)
    ... | false | []      = lift (hc , tt)
    ... | false | x ∷ xs′ = lift (hc , tt)
    run-e c (attK l p s) r hc hs with unsubIf (not l) s | unsubIf-e (not l) s hs
    ... | s′ , t | h = lift (hc , h)
    run-e c (conK (cs cl sl sa (just p) as ow ca ea sr sc) o b _ (inj₁ refl)) r hc (hk , ho , hb) = lift ((hk , hb , hc) , ho)
    run-e c (conK (cs cl sl sa nothing as ow ca ea sr sc) o b _ (inj₁ refl)) r hc hs = lift (hc , hs)
    run-e c (conK (cs cl sl sa ba (just p) ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) r hc (hk , ho , hb)
      with unsubIf (not sl ∨ closed c) o | unsubIf-e (not sl ∨ closed c) o ho
    ... | o′ , t | h = lift (hc , (hk , h , hb))
    run-e c (conK (cs cl sl sa ba nothing ow ca ea sr sc) o b _ (inj₂ (inj₁ refl))) r hc hs = lift (hc , hs)
    run-e c (conK (cs cl sl sa ba as (just p) ca ea sr sc) o b _ (inj₂ (inj₂ refl))) r hc (hk , ho , hb)
      with unsubIf sa o | unsubIf-e sa o ho
    ... | o′ , t | h = lift (hc , (hk , h , hb))
    run-e c (conK (cs cl sl sa ba as nothing ca ea sr sc) o b _ (inj₂ (inj₂ refl))) r hc hs = lift (hc , hs)
    run-e c (joinK j g x q (nx a) ib) r hc hs = lift (hc , tt)
    run-e c (joinK j g x q cp ib)     r hc hs = lift (hc , tt)
    run-e c (leafK b l) r hc hs = (λ e l′ b′ p′ → hc , tt) , (λ l′ → hc , tt)
    run-e c (stopK i q p s) r hc hs = lift (hc , hs)
    run-e c (cutK i q p s) r hc hs with cut s | cut-e s hs
    ... | s′ , t | h = lift (hc , h)

  module _ (o : PureObs [] R) where
    step-e : ∀ {rs} (k : Conf R) → Path (load o) rs k → ∀ κ → Clock k ⊑ κ → ConfE (Clock k) k → SE κ (Machine.step k)
    step-e ⟨ c , s , rising e , p ⟩ pth κ le (hc , hs) = rise-e c s e p hs (floor o pth tt) (ctx-mono c le hc) (st-mono s le hs) le
    step-e ⟨ c , pend o′ q , subscribing , p ⟩ pth κ le (hc , _) = begin-e c o′ q (ctx-mono c le hc)
    step-e ⟨ c , coldS b l , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , tt)
    step-e ⟨ c , ofS i q xs , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , tt)
    step-e ⟨ c , doneS , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , tt)
    step-e ⟨ c , mapS f s , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono s le hs)
    step-e ⟨ c , scanS f z s , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono s le hs)
    step-e ⟨ c , cutS l a s , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono s le hs)
    step-e ⟨ c , lnS b s , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono s le hs)
    step-e ⟨ c , takeS i q w s , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono s le hs)
    step-e ⟨ c , flatS op f ω d n q o′ ls , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono (flatS op f ω d n q o′ ls) le hs)
    step-e ⟨ c , connS k o′ b , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , st-mono (connS k o′ b) le hs)
    step-e ⟨ c , joinS j g x ib , subscribing , p ⟩ pth κ le (hc , hs) = lift (ctx-mono c le hc , tt)
    step-e ⟨ c , s , absorbed , p ⟩ pth κ le (hc , hs) with search top (plug c s) in fd
    ... | nothing = lift (tt)
    ... | just (found (_ , _ , c′ , s′) m κ′)
      with unplug-e c′ (subst (StE κ) (sym (found-plug c s fd)) (plug-e c (ctx-mono c le hc) (st-mono s le hs)))
    ...   | hc′ , hs′ = run-e c′ (found-mark c s fd) p hc′ hs′

------------------------------------------------------------------------
-- Along a run

module _ {R : Set} where
  open Driver R using (took; played; silent; value)

  played-e : ∀ {κ} (pk : Poke R) → SE κ (turn pk) → ∀ {t k′} → played pk ≡ silent t k′ → ConfE κ k′
  played-e gone _ ()
  played-e (leaf true (ending e) cl dv st) (d , s) refl = d cp overT false e
  played-e (leaf false l cl dv st) (d , s) refl = s overT
  played-e (leaf true (play τ u i t fr) true dv st) (d , s) refl = s overT
  played-e (leaf true overT true dv st) (d , s) refl = s overT
  played-e (leaf true (play τ u i t (emit a k)) false dv st) (d , s) refl = d (nx a) _ true _
  played-e (leaf true (play τ u i t (stall k)) false dv st) (d , s) refl = s _
  played-e (leaf true (play τ u i t (close k)) false dv st) (d , s) refl = s _
  played-e (leaf true overT false dv st) (d , s) refl = s overT

  took-silent : ∀ {κ} (x : Stepped R) → SE κ x → ∀ {t k′} → took x ≡ silent t k′ → ConfE κ k′
  took-silent (moved k [] _)               (lift h) refl = h
  took-silent (moved k ((p , nx a) ∷ _) _) _ ()
  took-silent (moved k ((p , cp) ∷ _) _)   _ ()
  took-silent (starting x p k) f refl = f _
  took-silent (turn pk) h e = played-e pk h e
  took-silent quiet _ ()

  took-value : ∀ {κ} (x : Stepped R) → SE κ x → ∀ {t p a k′} → took x ≡ value t p a k′ → ConfE (Clock k′) k′
  took-value (moved k [] _)               _ ()
  took-value (moved k ((p , nx a) ∷ _) _) (lift h) refl = h
  took-value (moved k ((p , cp) ∷ _) _)   _ ()
  took-value (starting x p k) _ ()
  took-value (turn pk) _ e = ⊥-elim (played-val pk e)
  took-value quiet _ ()

  module _ (o : PureObs [] R) where
    go : ∀ {rs k} → Path (load o) rs k → ConfE (Clock k) k → ∀ {rs′ k″} → Path k rs′ k″ → ConfE (Clock k″) k″
    go pre h [] = h
    go pre h (tau {k} {k′} e pth) =
      go (pre ▸ tau e []) (took-silent (Machine.step k) (step-e o k pre (Clock k′) (clock-mono o pre (_ , e)) h) e) pth
    go pre h (val {k} e pth) =
      go (pre ▸ val e []) (took-value (Machine.step k) (step-e o k pre (Clock k) ⊑-refl h) e) pth

------------------------------------------------------------------------
-- The ends behind a subscription

-- The end of the binder `x` up the context.
endUp : ∀ {R Γ A X} → Ctx R Γ A → X ∈ Γ → Pos
endUp top                                 ()
endUp (inMap f c)                         x = endUp c x
endUp (inScan f z c)                      x = endUp c x
endUp (inCut l a c)                       x = endUp c x
endUp (inLn b c)                          x = endUp c x
endUp (inTake i p w c)                    x = endUp c x
endUp (inOuter op f ω d n q ls c)         x = endUp c x
endUp (inLanes op f ω d n q o pre post c) x = endUp c x
endUp (inSrc k b c)                       x = endUp c x
endUp (inBody k o c)              (here refl) = CS.endAt k
endUp (inBody k o c)              (there x)   = endUp c x

up-e : ∀ {R Γ A X κ} (c : Ctx R Γ A) (x : X ∈ Γ) → CtxE κ c → closedUp c x ≡ true → at (endUp c x) ⊑ κ
up-e top                                 () hc cu
up-e (inMap f c)                         x hc cu                    = up-e c x hc cu
up-e (inScan f z c)                      x hc cu                    = up-e c x hc cu
up-e (inCut l a c)                       x hc cu                    = up-e c x hc cu
up-e (inLn b c)                          x hc cu                    = up-e c x hc cu
up-e (inTake i p w c)                    x hc cu                    = up-e c x hc cu
up-e (inOuter op f ω d n q ls c)         x (_ , hc) cu              = up-e c x hc cu
up-e (inLanes op f ω d n q o pre post c) x (_ , _ , _ , hc) cu      = up-e c x hc cu
up-e (inSrc k b c)                       x (_ , _ , hc) cu          = up-e c x hc cu
up-e (inBody k o c)              (here refl) (hk , _ , _) cu        = hk (subst T (sym cu) tt)
up-e (inBody k o c)              (there x)   (_ , _ , hc) cu        = up-e c x hc cu

-- EVERY CLOSED SUBJECT IN SCOPE ENDED AT OR BEFORE THE SUBSCRIPTION.
ends-behind : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Machine.Ctx R Γ A} {s q}
            → Path (load o) rs ⟨ c , s , subscribing , q ⟩
            → ∀ {X} (x : X ∈ Γ) → closedUp c x ≡ true → endUp c x ≼ q
ends-behind o {c = c} {q = q} pth x cu lt with go o [] (tt , tt) pth
... | hc , _ = no (trans (sym (at-<ᴷ q (endUp c x))) (_⊑_.un (up-e c x hc cu))) lt
  where
    no : ∀ {b} → b ≡ false → T b → ⊥
    no refl ()
