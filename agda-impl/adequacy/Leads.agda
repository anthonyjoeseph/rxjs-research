{-# OPTIONS --guardedness #-}

-- WHAT A FIND LEADS: every part a find rose through lies past its event,
-- or exactly at it where the find is tight.  A lead under a cap asks it
-- only of a find no later than the cap; a race's loser lies past the
-- winner strictly, or on a tie owns nothing there.
module adequacy.Leads where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Events using (Pos; ix; <ᵖ-split)
open import denotation.EmissionSet using (EmissionSet; Ev; Truncate; out; skip; pin; end; _≺_; MapT; map-out; map-skip; map-pin;
  map-end; module Scan)
open import operation.Key using (Key; at; _<ᴷ_; ≮ᴷ-trans; at-<ᵖ; clash)
open import operation.PureObservable using (module Machine; Tape; play; ending; over)

open Machine using (St; Ctx; CS; Cand; found; Mark; ofM; attM; leafM; Att; Out; still; shows; nx; cp; seek; search; kids; lanes; own; ownBest; first; retag;
                    raceT; outerT; laneT; mapT; scanT; cutT; alive; outOf; closed; attached; attAt;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; rowsL; Lanes; Each; Hot; ∅)
open import adequacy.Bound using (rooted-single; _⊑_; ⊑i; ⊑-refl; ⊑-trans; <→⊑; ext-⊑; From; Bd; OK; OKL; Live; Apart; Spread;
  Parts; rooted-parts; ⊑→≼; MergeG; G; GL; GLn; Good; ofPos; from-weak; lane-ok; raise-map; raise-scan; raise-cut; raise-outer; raise-lane)
  renaming (After to Afterᶜ)
open import adequacy.Cap using (Before; OKᶜ; OKLᶜ; each-map)
open import adequacy.Skip using (After; LeadC; LeadT)

open _⊑_
open Bd

------------------------------------------------------------------------
-- Keys

⊑-< : ∀ {a b c} → a ⊑ b → b <ᴷ c ≡ true → a <ᴷ c ≡ true
⊑-< {a} {b} {c} ab bc with a <ᴷ c in ac
... | true  = refl
... | false = ⊥-elim (clash bc (≮ᴷ-trans b a c (un ab) ac))

<-⊑ : ∀ {a b c} → a <ᴷ b ≡ true → b ⊑ c → a <ᴷ c ≡ true
<-⊑ {a} {b} {c} ab bc with a <ᴷ c in ac
... | true  = refl
... | false = ⊥-elim (clash ab (≮ᴷ-trans a c b ac (un bc)))

<→≺ : ∀ {p q} → at p <ᴷ at q ≡ true → p ≺ q
<→≺ {p} {q} h = subst T (sym (trans (sym (at-<ᵖ p q)) h)) tt

------------------------------------------------------------------------
-- The winner's key against its own rows

-- A row there the event's own: a value only as the value shown, an end
-- only as the end shown.
Fits : ∀ {A} → Out A → Ev A → Set
Fits o (out a) = o ≡ shows (nx a)
Fits o skip    = ⊤
Fits o (pin _) = ⊤
Fits o end     = o ≡ shows cp

-- Some row at `Q`, short of saying which.
record Occ {A} (t : EmissionSet A) (Q : Pos) (o : Out A) : Set where
  constructor occ
  field unocc : (∀ {e} → t Q e → Fits o e → ⊥) → ⊥
open Occ

hit : ∀ {A} {t : EmissionSet A} {Q o e} → t Q e → Fits o e → Occ t Q o
hit r fe = occ λ k → k r fe

occ-bind : ∀ {A B} {t : EmissionSet A} {u : EmissionSet B} {Q Q′ o o′} → Occ t Q o → (∀ {e} → t Q e → Fits o e → Occ u Q′ o′) → Occ u Q′ o′
occ-bind (occ oc) h = occ λ k → oc λ r fe → unocc (h r fe) k

-- The key strictly past the event's position, or at a row of its own no
-- earlier than it.
data Tight {A} (t : EmissionSet A) (P : Pos) (K : Key) (o : Out A) : Set where
  strict : at P <ᴷ K ≡ true → Tight t P K o
  tie    : ∀ Q → K ≡ at Q → at P ⊑ at Q → Occ t Q o → Tight t P K o

tight-⊑ : ∀ {A} {t : EmissionSet A} {P K o} → Tight t P K o → at P ⊑ K
tight-⊑ {P = P} {K} (strict lt)                = <→⊑ (at P) K lt
tight-⊑         (tie Q refl pq _) = pq

tight-occ : ∀ {A B} {t : EmissionSet A} {u : EmissionSet B} {P K o o′} → (∀ {Q} → Occ t Q o → Occ u Q o′) → Tight t P K o → Tight u P K o′
tight-occ h (strict lt)                = strict lt
tight-occ h (tie Q eq pq oc) = tie Q eq pq (h oc)

-- A loser strictly past the winner's key.
past-strict : ∀ {B} {u : EmissionSet B} {P K K′} → at P ⊑ K → K <ᴷ K′ ≡ true → From K′ u → After P u
past-strict {P = P} {K} {K′} pk kk fr {q} r = <→≺ {P} {q} (⊑-< {at P} {K} {at q} pk (<-⊑ {K} {K′} {at q} kk (fr r)))

-- A loser on a tie, apart from the winner.
past-tie : ∀ {A B} {t : EmissionSet A} {u : EmissionSet B} {P K o} → Tight t P K o → From K u → Apart t u → After P u
past-tie {P = P} {K} (strict lt) fr ap {q} r = <→≺ {P} {q} (<-⊑ {at P} {K} {at q} lt (fr r))
past-tie {P = P} (tie Q refl pq oc) fr ap {q} r with <ᵖ-split Q q (trans (sym (at-<ᵖ q Q)) (un (fr r)))
... | inj₁ lt   = <→≺ {P} {q} (⊑-< {at P} {at Q} {at q} pq (trans (at-<ᵖ Q q) lt))
... | inj₂ refl = ⊥-elim (unocc oc λ r′ _ → ap r′ r)

each-past : ∀ {A B} {t : EmissionSet A} {P K o} (Ls : List (EmissionSet B)) → Tight t P K o → Apart t (Lanes Ls) → Each (From K) Ls → Each (After P) Ls
each-past []       tg ap _        = tt
each-past {P = P} {K} (u ∷ Ls) tg ap (f , fs) = past-tie {u = u} {P = P} {K} tg f (λ {q} {e} {e′} r x → ap {q} {e} {e′} r (inj₁ x)) , each-past {P = P} {K} Ls tg (λ {q} {e} {e′} r x → ap {q} {e} {e′} r (inj₂ x)) fs

each-strict : ∀ {B} {P K K′} (Ls : List (EmissionSet B)) → at P ⊑ K → K <ᴷ K′ ≡ true → Each (From K′) Ls → Each (After P) Ls
each-strict []       pk kk _        = tt
each-strict {P = P} {K} {K′} (u ∷ Ls) pk kk (f , fs) = past-strict {u = u} {P} {K} {K′} pk kk f , each-strict {P = P} {K} {K′} Ls pk kk fs

------------------------------------------------------------------------
-- Under a cap

-- No later than a key no later than the cap.
up : ∀ {K K′ C} → K ⊑ K′ → C <ᴷ K′ ≡ false → K ⊑ C
up kk b = ⊑-trans kk (⊑i b)

-- Past the cap, past whatever is no later than it.
aft : ∀ {B} {t : EmissionSet B} {P K C} → at P ⊑ K → K ⊑ C → Afterᶜ C t → After P t
aft {P = P} {K} {C} pk kc a {q} r = <→≺ {P} {q} (⊑-< {at P} {C} {at q} (⊑-trans pk kc) (a r))

from-cap : ∀ {B} {t : EmissionSet B} {K C} → K ⊑ C → Afterᶜ C t → From K t
from-cap {K = K} {C} kc a {q} r = <→⊑ K (at q) (⊑-< {K} {C} {at q} kc (a r))

-- A find at or before the cap: exact.
exact : ∀ {R A} C {t : EmissionSet A} (y : Maybe (Cand R A)) → Before C y → OKᶜ C t y → OK t y
exact C nothing  ()
exact C (just _) b (inj₁ (p , _)) = ⊥-elim (clash p b)
exact C (just _) b (inj₂ (_ , o)) = o

before-retag : ∀ {R A B} C (T′ : Key → Out A → Key × Out B) → (∀ h o → h ⊑ proj₁ (T′ h o)) → (y : Maybe (Cand R A)) → Before C (retag T′ y) → Before C y
before-retag C T′ r nothing            ()
before-retag C T′ r (just (f , K , o)) b = un (up {K} {proj₁ (T′ K o)} {C} (r K o) b)

-- Nothing found under the cap: every row past it.
none-aft : ∀ {R B} {t : EmissionSet B} {C K} → K ⊑ C → OKᶜ {R} C t nothing → ∀ P → at P ⊑ K → After P t
none-aft {t = t} kc (inj₁ (_ , a)) P pk = aft {t = t} pk kc a
none-aft kc (inj₂ (() , _)) P pk

nones-aft : ∀ {R B} {C K} (Ls : List (EmissionSet B)) → K ⊑ C → OKLᶜ {R} C Ls nothing → ∀ P → at P ⊑ K → Each (After P) Ls
nones-aft {C = C} Ls kc (inj₁ (_ , a)) P pk = each-map {P = Afterᶜ C} {Q = After P} Ls (λ {t} (x : Afterᶜ C t) → aft {t = t} pk kc x) a
nones-aft Ls kc (inj₂ (() , _)) P pk

from-none : ∀ {R B} {t : EmissionSet B} {C K} → K ⊑ C → OKᶜ {R} C t nothing → From K t
from-none {t = t} kc (inj₁ (_ , a)) = from-cap {t = t} kc a
from-none kc (inj₂ (() , _))

-- A loser to a strict win, the winner no later than the cap.
lost-strict : ∀ {R B} {t : EmissionSet B} {C P K K′} {g} {o : Out B} → at P ⊑ K′ → K′ ⊑ C → K′ <ᴷ K ≡ true → OKᶜ {R} C t (just (g , K , o)) → After P t
lost-strict {t = t} pk kc lt (inj₁ (_ , a))  = aft {t = t} pk kc a
lost-strict {t = t} {P = P} {K} {K′} pk kc lt (inj₂ (_ , bx)) = past-strict {u = t} {P} {K′} {K} pk lt (λ {q} {e} r → Bd.from bx {q} {e} r)

lost-strict-each : ∀ {R B} {C P K K′} {g} {o : Out B} (Ls : List (EmissionSet B)) → at P ⊑ K → K ⊑ C → K <ᴷ K′ ≡ true → OKLᶜ {R} C Ls (just (g , K′ , o)) → Each (After P) Ls
lost-strict-each {C = C} {P = P} Ls pk kc lt (inj₁ (_ , a))  = each-map {P = Afterᶜ C} {Q = After P} Ls (λ {t} (x : Afterᶜ C t) → aft {t = t} pk kc x) a
lost-strict-each Ls pk kc lt (inj₂ (_ , bl)) = each-strict Ls pk lt (proj₁ bl)

-- Lost on a tie or after, the winner no later than the cap: no earlier
-- than the winner.
from-lost : ∀ {R A} {t : EmissionSet A} {C h k} {f} {o : Out A} → k ⊑ C → h <ᴷ k ≡ false → OKᶜ {R} C t (just (f , h , o)) → From k t
from-lost {t = t} kc lt (inj₁ (_ , a)) = from-cap {t = t} kc a
from-lost kc lt (inj₂ (_ , b)) = λ r → ⊑-trans (⊑i lt) (Bd.from b r)

froms-lost : ∀ {R B} {C K K′} {g} {o : Out B} (Ls : List (EmissionSet B)) → K ⊑ C → K ⊑ K′ → OKLᶜ {R} C Ls (just (g , K′ , o)) → Each (From K) Ls
froms-lost {C = C} {K = K} Ls kc kk (inj₁ (_ , a))  = each-map {P = Afterᶜ C} {Q = From K} Ls (λ {t} (x : Afterᶜ C t) → from-cap {t = t} kc x) a
froms-lost Ls kc kk (inj₂ (_ , bl)) = from-weak Ls kk (proj₁ bl)

------------------------------------------------------------------------
-- The frames between a node and what its search found

data Ext {R} {Γ′ A′} (c′ : Ctx R Γ′ A′) : ∀ {Γ A} → Ctx R Γ A → Set₁ where
  stop   : Ext c′ c′
  eMap   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} → Ext c′ (inMap f c) → Ext c′ c
  eScan  : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} → Ext c′ (inScan f z c) → Ext c′ c
  eCut   : ∀ {Γ A} {l a} {c : Ctx R Γ A} → Ext c′ (inCut l a c) → Ext c′ c
  eTake  : ∀ {Γ A} {i q w} {c : Ctx R Γ A} → Ext c′ (inTake i q w c) → Ext c′ c
  eLn    : ∀ {Γ A} {b} {c : Ctx R Γ A} → Ext c′ (inLn b c) → Ext c′ c
  eOuter : ∀ {Γ A B} {op f d n q ls} {c : Ctx R Γ B} → Ext c′ (inOuter {A = A} op f d n q ls c) → Ext c′ c
  eLanes : ∀ {Γ A B} {op f d n q} {o : St Γ A} {pre post} {c : Ctx R Γ B} → Ext c′ (inLanes op f d n q o pre post c) → Ext c′ c
  eSrc   : ∀ {Γ X B} {k} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} → Ext c′ (inSrc k b c) → Ext c′ c
  eBody  : ∀ {Γ X B} {k} {o : St Γ X} {c : Ctx R Γ B} → Ext c′ (inBody k o c) → Ext c′ c

-- Each merge's other parts past `P`, over the added frames.
LeadE : ∀ {R Γ′ A′ Γ A} {c′ : Ctx R Γ′ A′} {c : Ctx R Γ A} → Ext c′ c → Pos → Set
LeadE stop                                        P = ⊤
LeadE (eMap e)                                    P = LeadE e P
LeadE (eScan e)                                   P = LeadE e P
LeadE (eCut e)                                    P = LeadE e P
LeadE (eTake {w = w} e)                           P = LeadT w P × LeadE e P
LeadE (eLn e)                                     P = LeadE e P
LeadE (eOuter {ls = ls} {c = c} e)                P = Each (After P) (rowsL (env c) ls) × LeadE e P
LeadE (eLanes {o = o} {pre = pre} {post = post} {c = c} e) P =
  After P (rows (env c) o) × Each (After P) (rowsL (env c) pre) × Each (After P) (rowsL (env c) post) × LeadE e P
LeadE (eSrc {k = k} {b = b} {c = c} e)            P = After P (rows (Hot (env c) ∅ k ∷ᴬ env c) b) × LeadE e P
LeadE (eBody {o = o} {c = c} e)                   P = After P (rows (env c) o) × LeadE e P

lead-ext : ∀ {R Γ′ A′ Γ A} {c′ : Ctx R Γ′ A′} {c : Ctx R Γ A} (e : Ext c′ c) {P} → LeadE e P → LeadC c P → LeadC c′ P
lead-ext stop       _                  lc = lc
lead-ext (eMap e)   le                 lc = lead-ext e le lc
lead-ext (eScan e)  le                 lc = lead-ext e le lc
lead-ext (eCut e)   le                 lc = lead-ext e le lc
lead-ext (eTake e)  (a , le)           lc = lead-ext e le (a , lc)
lead-ext (eLn e)    le                 lc = lead-ext e le lc
lead-ext (eOuter e) (a , le)           lc = lead-ext e le (a , lc)
lead-ext (eLanes e) (a , b , d , le)   lc = lead-ext e le (a , b , d , lc)
lead-ext (eSrc e)   (a , le)           lc = lead-ext e le (a , lc)
lead-ext (eBody e)  (a , le)           lc = lead-ext e le (a , lc)

∨-true : ∀ b → (b Data.Bool.∨ true) ≡ true
∨-true true  = refl
∨-true false = refl

ext-closed : ∀ {R Γ′ A′ Γ A} {c′ : Ctx R Γ′ A′} {c : Ctx R Γ A} → Ext c′ c → closed c ≡ true → closed c′ ≡ true
ext-closed stop       h = h
ext-closed (eMap e)   h = ext-closed e h
ext-closed (eScan e)  h = ext-closed e h
ext-closed (eCut {l = l} {c = c} e) h = ext-closed e (subst (λ b → (Data.Bool.not l Data.Bool.∨ b) ≡ true) (sym h) (∨-true (Data.Bool.not l)))
ext-closed (eLn e)    h = ext-closed e h
ext-closed (eTake e)  h = ext-closed e h
ext-closed (eOuter e) h = ext-closed e h
ext-closed (eLanes e) h = ext-closed e h
ext-closed (eSrc {k = k} e) h = ext-closed e (subst (λ b → (CS.closed k Data.Bool.∨ b) ≡ true) (sym h) (∨-true (CS.closed k)))
ext-closed (eBody e)  h = ext-closed e h

------------------------------------------------------------------------
-- What a search finds, read at the of it found

-- A started cold's next step: a frame's at its index, or its completion.
TapeAt : ∀ {A} → Tape A → Pos → Set
TapeAt (play τ u i t fr) P = P ≡ u ++ [ ix i ]
TapeAt (ending e)        P = P ≡ e
TapeAt over              P = ⊥

-- An of's own mark, or a live cold's: the position of its next row.
OfAt : ∀ {Γ A} → St Γ A → Mark → Pos → Set
OfAt (ofS i p xs) ofM P = P ≡ ofPos p i xs
OfAt (coldS true l) leafM P = TapeAt l P
OfAt _            _   P = ⊥

Leads : ∀ {R Γ A} → Bool → Ctx R Γ A → EmissionSet A → Maybe (Cand R A) → Set₁
Leads v c t nothing                                    = ⊤₁
Leads v c t (just (found (_ , _ , c′ , s′) m κ , K , o)) =
  Σ (Ext c′ c) λ e → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight t P K o)

lmap : ∀ v {X Y : Set} → (X → Y) → Live v X → Live v Y
lmap true  h x = h x
lmap false h x = tt

lzip : ∀ v {X Y Z : Set} → (X → Y → Z) → Live v X → Live v Y → Live v Z
lzip true  h x y = h x y
lzip false h x y = tt

lpure : ∀ v {X : Set} → X → Live v X
lpure true  x = x
lpure false x = tt

-- The tight half rewritten, the rest kept.
relive : ∀ v {C : Set} {O L T₁ T₂ : Pos → Set} → (∀ {P} → T₁ P → T₂ P) → Live v (C → ∀ P → O P → L P × T₁ P) → Live v (C → ∀ P → O P → L P × T₂ P)
relive true  h l cl P oa = proj₁ (l cl P oa) , h (proj₂ (l cl P oa))
relive false h l         = tt

-- `y` taken over `x`: strictly earlier, or `x` nothing.
Beats : ∀ {R A} → Maybe (Cand R A) → Maybe (Cand R A) → Set
Beats nothing            y                    = ⊤
Beats (just x)           nothing              = ⊤
Beats (just (_ , h , _)) (just (_ , h′ , _))  = h′ <ᴷ h ≡ true

first-leads : ∀ {R Γ A} {v} {c : Ctx R Γ A} {t} (x y : Maybe (Cand R A)) → Leads v c t x → (Beats x y → Leads v c t y) → Leads v c t (first x y)
first-leads nothing            y                    lx ly = ly tt
first-leads (just x)           nothing              lx ly = lx
first-leads (just (f , h , o)) (just (g , h′ , o′)) lx ly with h′ <ᴷ h
... | true  = ly refl
... | false = lx

-- Under a cap: a find at or before it leads, past it nothing is asked.
Leadsᶜ : ∀ {R Γ A} → Key → Bool → Ctx R Γ A → EmissionSet A → Maybe (Cand R A) → Set₁
Leadsᶜ C v c t y = Before C y → Leads v c t y

first-leadsᶜ : ∀ {R Γ A} C {v} {c : Ctx R Γ A} {t} (x y : Maybe (Cand R A)) → Leads v c t x → (Beats x y → Leadsᶜ C v c t y) → Leadsᶜ C v c t (first x y)
first-leadsᶜ C nothing            y                    lx ly b = ly tt b
first-leadsᶜ C (just x)           nothing              lx ly b = lx
first-leadsᶜ C (just (f , h , o)) (just (g , h′ , o′)) lx ly b with h′ <ᴷ h
... | true  = ly refl b
... | false = lx

-- At every cap: uncapped.
uncap-lead : ∀ {R Γ A} {v} {c : Ctx R Γ A} {t} (y : Maybe (Cand R A)) → (∀ C → Leadsᶜ C v c t y) → Leads v c t y
uncap-lead nothing            _ = tt₁
uncap-lead (just (f , K , o)) h = h K (un (⊑-refl K))

-- Read as entered: the winner's own row has nothing of its node before it.
leads-trunc : ∀ {R Γ A} v {c : Ctx R Γ A} {t : EmissionSet A} (y : Maybe (Cand R A)) → Live v (OK t y) → Leads v c t y → Leads v c (Truncate t) y
leads-trunc v     nothing                                  _ _       = tt₁
leads-trunc false (just (found (_ , _ , c′ , s′) m κ , K , o)) _ (e , _) = e , tt
leads-trunc true  {t = t} (just (found (_ , _ , c′ , s′) m κ , K , o)) b (e , l) = e , λ cl P oa → proj₁ (l cl P oa) , tr (proj₂ (l cl P oa))
  where
    tr : ∀ {P} → Tight t P K o → Tight (Truncate t) P K o
    tr (strict lt)        = strict lt
    tr (tie Q refl pq oc) = tie Q refl pq (occ-bind oc λ r fe → hit (r , ([] , λ {k} y lt _ → ⊥-elim (⊑→≼ {Q} {k} (Bd.from b y) lt))) fe)

------------------------------------------------------------------------
-- One frame

map-leads : ∀ {R Γ A B} v (f : A → B) {c : Ctx R Γ B} {t} (y : Maybe (Cand R A)) → Leads v (inMap f c) t y → Leads v c (MapT f t) (retag (mapT f) y)
map-leads v f nothing                                        _ = tt₁
map-leads {A = A} v f {t = t} (just (found (_ , _ , c′ , s′) m κ , K , still))     (e , l) =
  eMap e , relive v (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits {A} still e → Occ (MapT f t) Q still
    mv {e = out _} r ()
    mv {e = skip}  r _ = hit (map-skip r) tt
    mv {e = pin _} r _ = hit (map-pin r) tt
    mv {e = end}   r ()
map-leads {A = A} v f {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows (nx a))) (e , l) =
  eMap e , relive v (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits (shows (nx a)) e → Occ (MapT f t) Q (shows (nx (f a)))
    mv {e = out _} r refl = hit (map-out r) refl
    mv {e = skip}  r _    = hit (map-skip r) tt
    mv {e = pin _} r _    = hit (map-pin r) tt
    mv {e = end}   r ()
map-leads {A = A} v f {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows cp)) (e , l) =
  eMap e , relive v (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits {A} (shows cp) e → Occ (MapT f t) Q (shows cp)
    mv {e = out _} r ()
    mv {e = skip}  r _ = hit (map-skip r) tt
    mv {e = pin _} r _ = hit (map-pin r) tt
    mv {e = end}   r refl = hit (map-end r) refl

-- A scan's value at its source's least one: the fold of that value alone.
scan-leads : ∀ {R Γ A B} v (f : B → A → B) z {c : Ctx R Γ B} {t} (y : Maybe (Cand R A)) → Live v (OK t y) → Leads v (inScan f z c) t y → Leads v c (Scan.ScanT f z t) (retag (scanT f z) y)
scan-leads v f z nothing _ _ = tt₁
scan-leads false f z (just (found (_ , _ , c′ , s′) m κ , K , still))     _ (e , l) = eScan e , tt
scan-leads false f z (just (found (_ , _ , c′ , s′) m κ , K , shows (nx a))) _ (e , l) = eScan e , tt
scan-leads false f z (just (found (_ , _ , c′ , s′) m κ , K , shows cp))  _ (e , l) = eScan e , tt
scan-leads {A = A} true f z {t = t} (just (found (_ , _ , c′ , s′) m κ , K , still)) _ (e , l) =
  eScan e , relive true (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits {A} still e → Occ (Scan.ScanT f z t) Q still
    mv {e = out _} r ()
    mv {e = skip}  r _ = hit (Scan.sstep r) tt
    mv {e = pin _} r _ = hit (Scan.spin r) tt
    mv {e = end}   r ()
scan-leads {A = A} true f z {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows (nx a))) b (e , l) =
  eScan e , λ cl P oa → proj₁ (l cl P oa) , tr (proj₂ (l cl P oa))
  where
    mv : ∀ {Q e} → K ≡ at Q → t Q e → Fits (shows (nx a)) e → Occ (Scan.ScanT f z t) Q (shows (nx (f z a)))
    mv {e = out _} eq r refl = hit (Scan.sval (Scan.acc₀ r (λ r′ → ⊑→≼ (subst (_⊑ at _) eq (from b r′))))) refl
    mv {e = skip}  eq r _    = hit (Scan.sstep r) tt
    mv {e = pin _} eq r _    = hit (Scan.spin r) tt
    mv {e = end}   eq r ()
    tr : ∀ {P} → Tight t P K (shows (nx a)) → Tight (Scan.ScanT f z t) P K (shows (nx (f z a)))
    tr (strict lt)       = strict lt
    tr (tie Q eq pq oc)  = tie Q eq pq (occ-bind oc (mv eq))
scan-leads {A = A} true f z {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows cp)) _ (e , l) =
  eScan e , relive true (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits {A} (shows cp) e → Occ (Scan.ScanT f z t) Q (shows cp)
    mv {e = out _} r ()
    mv {e = skip}  r _ = hit (Scan.sstep r) tt
    mv {e = pin _} r _ = hit (Scan.spin r) tt
    mv {e = end}   r refl = hit (Scan.send r) refl

cut-on : ∀ {R Γ A} v {a} {c : Ctx R Γ A} {t} (y : Maybe (Cand R A)) → Leads (v Data.Bool.∧ true) (inCut true a c) t y → Leads v c t (retag (cutT true) y)
cut-on v     nothing                                 _       = tt₁
cut-on true  (just (found (_ , _ , c′ , s′) m κ , K , o)) (e , l) = eCut e , l
cut-on false (just (found (_ , _ , c′ , s′) m κ , K , o)) (e , l) = eCut e , tt

-- Under a cut switched off, whatever is found is closed.
cut-off : ∀ {R Γ A} v {a} {c : Ctx R Γ A} {t u} (y : Maybe (Cand R A)) → Leads (v Data.Bool.∧ false) (inCut false a c) t y → Leads v c u (retag (cutT false) y)
cut-off v nothing                                 _       = tt₁
cut-off v (just (found (_ , _ , c′ , s′) m κ , K , o)) (e , _) =
  eCut e , lpure v (λ cl → ⊥-elim (clash (ext-closed e refl) cl))

ln-leads : ∀ {R Γ A} {v} {b} {c : Ctx R Γ A} {t} (y : Maybe (Cand R A)) → Leads v (inLn b c) t y → Leads v c t y
ln-leads nothing                                 _       = tt₁
ln-leads (just (found (_ , _ , c′ , s′) m κ , K , o)) (e , l) = eLn e , l
