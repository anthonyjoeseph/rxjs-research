{-# OPTIONS --guardedness #-}

-- THE FOUND OF LEADS: whatever the search finds, every other part of each
-- merge it rose through lies strictly past it.  A part lost a race: either
-- strictly, so its rows lie past the winner's key, or on a tie, where the
-- winner owns a row at that key and the parts are apart, so the loser's
-- rows there are none.  The winner's key is its event's position or past
-- it, and a lane's later siblings lose ties to it.
module adequacy.Lead where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; <ᵖ-split; emit; stall; close)
open import denotation.EmissionSet using (EmissionSet; DenEnv; Ev; Truncate; module Joining; out; skip; pin; end; _≺_; MapT; map-out; map-skip; map-pin; map-end; module Scan; at-out; at-skip; at-end)
open import operation.Key using (Key; at; _<ᴷ_; ≮ᴷ-trans; at-<ᵖ; clash)
open import operation.PureObservable using (module Machine; Tape; play; ending; over)
open Machine using (St; Ctx; CS; Cand; found; Mark; ofM; attM; leafM; Att; Out; still; shows; nx; cp; seek; search; kids; lanes; own; ownBest; first; retag;
                    raceT; outerT; laneT; mapT; scanT; cutT; alive; outOf; closed; attached; attAt;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; rowsL; pendRows; toEv; Lanes; Each; module BoundedF; Hot; ∅)
open import adequacy.Bound using (rooted-single; _⊑_; ⊑i; ⊑-refl; ⊑-trans; <→⊑; ext-⊑; From; Bd; OK; OKL; Live; Apart; Spread;
  Parts; rooted-parts; ⊑→≼; MergeG; G; GL; GLn; Good; ofPos; from-weak; lane-ok; raise-map; raise-scan; raise-cut; raise-outer; raise-lane)
  renaming (After to Afterᶜ)
open import adequacy.Cap using (Before; OKᶜ; OKLᶜ; each-map; cap-retag; Quiet; QuietL; EnvSingle)
open import adequacy.Search using (seek-okᶜ; seek-lnᶜ; lanes-okᶜ; join-okᶜ; calm-fst; calm-snd; flat-race; switch-race; exhaust-race; bounded-race; switch-at; bounded-unqueued)
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

-- A row there the event's own: a value only as the value shown.
Fits : ∀ {A} → Out A → Ev A → Set
Fits o (out a) = o ≡ shows (nx a)
Fits o skip    = ⊤
Fits o (pin _) = ⊤
Fits o end     = ⊤

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

each-empty : ∀ {B} {P} (Ls : List (EmissionSet B)) → Each (λ t → ∀ {q e} → t q e → ⊥) Ls → Each (After P) Ls
each-empty []       _        = tt
each-empty {P = P} (_ ∷ Ls) (n , ns) = (λ {q} {e} r → ⊥-elim (n {q} {e} r)) , each-empty {P = P} Ls ns

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
LeadE (eSrc {k = k} {b = b} {c = c} e)            P = After P (rows (Hot ∅ k ∷ᴬ env c) b) × LeadE e P
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
    mv {e = end}   r _ = hit (map-end r) tt
map-leads {A = A} v f {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows (nx a))) (e , l) =
  eMap e , relive v (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits (shows (nx a)) e → Occ (MapT f t) Q (shows (nx (f a)))
    mv {e = out _} r refl = hit (map-out r) refl
    mv {e = skip}  r _    = hit (map-skip r) tt
    mv {e = pin _} r _    = hit (map-pin r) tt
    mv {e = end}   r _    = hit (map-end r) tt
map-leads {A = A} v f {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows cp)) (e , l) =
  eMap e , relive v (tight-occ (λ oc → occ-bind oc mv)) l
  where
    mv : ∀ {Q e} → t Q e → Fits {A} (shows cp) e → Occ (MapT f t) Q (shows cp)
    mv {e = out _} r ()
    mv {e = skip}  r _ = hit (map-skip r) tt
    mv {e = pin _} r _ = hit (map-pin r) tt
    mv {e = end}   r _ = hit (map-end r) tt

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
    mv {e = end}   r _ = hit (Scan.send r) tt
scan-leads {A = A} true f z {t = t} (just (found (_ , _ , c′ , s′) m κ , K , shows (nx a))) b (e , l) =
  eScan e , λ cl P oa → proj₁ (l cl P oa) , tr (proj₂ (l cl P oa))
  where
    mv : ∀ {Q e} → K ≡ at Q → t Q e → Fits (shows (nx a)) e → Occ (Scan.ScanT f z t) Q (shows (nx (f z a)))
    mv {e = out _} eq r refl = hit (Scan.sval (Scan.acc₀ r (λ r′ → ⊑→≼ (subst (_⊑ at _) eq (from b r′))))) refl
    mv {e = skip}  eq r _    = hit (Scan.sstep r) tt
    mv {e = pin _} eq r _    = hit (Scan.spin r) tt
    mv {e = end}   eq r _    = hit (Scan.send r) tt
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
    mv {e = end}   r _ = hit (Scan.send r) tt

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

------------------------------------------------------------------------
-- A lane


------------------------------------------------------------------------
-- The lanes of a merge, raced among themselves

-- The winning lane's place in its list: the lanes before it lose to it
-- strictly, as the walk saw them; the ones after it lose, ties included.
LL : ∀ {R Γ A B} → Bool → Ctx R Γ B → FlatOp → (A → _) → Bool → _ → St Γ A → List (St Γ B) → List (St Γ B) → Maybe (Cand R B) → Set₁
LL v c op f d n o pre ls nothing = ⊤₁
LL {Γ = Γ} {B = B} v c op f d n o pre ls (just (found (_ , _ , c′ , s′) m κ , K , o′)) =
  Σ (List (St Γ B)) λ pre₁ → Σ (List (St Γ B)) λ post₁ → Σ (Ext c′ (inLanes op f d n [] o pre₁ post₁ c)) λ e →
    Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P →
      LeadE e P × (Each (After P) (rowsL (env c) pre) → Each (After P) (rowsL (env c) pre₁)) × Each (After P) (rowsL (env c) post₁) × Tight (Lanes (rowsL (env c) ls)) P K o′)

LLᶜ : ∀ {R Γ A B} → Key → Bool → Ctx R Γ B → FlatOp → (A → _) → Bool → _ → St Γ A → List (St Γ B) → List (St Γ B) → Maybe (Cand R B) → Set₁
LLᶜ C v c op f d n o pre ls y = Before C y → LL v c op f d n o pre ls y

lzip3 : ∀ v {X Y Z W : Set} → (X → Y → Z → W) → Live v X → Live v Y → Live v Z → Live v W
lzip3 true  h x y z = h x y z
lzip3 false h x y z = tt

-- A lane's rows read in its list: switched off, it owes nothing there.
x-tight : ∀ {Γ B} {ρ : DenEnv Γ} l a (s₀ : St Γ B) Ls {P K} {ox : Out B} → Tight (rows ρ (lnS l (cutS l a s₀))) P K ox
        → Tight (Lanes (rows ρ (lnS l (cutS l a s₀)) ∷ Ls)) P K (Data.Bool.if l then ox else still)
x-tight true  a s₀ Ls tg               = tight-occ (λ oc → occ-bind oc λ x fe → hit (inj₁ x) fe) tg
x-tight false a s₀ Ls (strict lt)      = strict lt
x-tight false a s₀ Ls (tie Q eq pq oc) = ⊥-elim (unocc oc λ ())

-- One lane against the lanes after it: on a tie the earlier wins.
module Step {R Γ A B} (v : Bool) (c : Ctx R Γ B) (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (pre post : List (St Γ B))
            (l : Bool) (a : Att) (s₀ : St Γ B) where

  ρ : DenEnv Γ
  ρ = env c

  s : St Γ B
  s = lnS l (cutS l a s₀)

  ll-shift : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K} {o′ : Out B}
           → LL v c op f d n o (s ∷ pre) post (just (found (Γ′ , A′ , c′ , s′) m κ , K , o′))
           → Live v (∀ P → Tight (Lanes (rowsL ρ post)) P K o′ → After P (rows ρ s))
           → LL v c op f d n o pre (s ∷ post) (just (found (Γ′ , A′ , c′ , s′) m κ , K , o′))
  ll-shift (pre₁ , post₁ , e , ly) as = pre₁ , post₁ , e , lzip v go ly as
    where
      go : _ → _ → _
      go ly as cl P oa = let r = ly cl P oa ; tg = proj₂ (proj₂ (proj₂ r)) in
        proj₁ r , (λ ea → proj₁ (proj₂ r) (as P tg , ea)) , proj₁ (proj₂ (proj₂ r)) , tight-occ (λ oc → occ-bind oc λ x fe → hit (inj₂ x) fe) tg

  x-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K} (ox : Out B) (e : Ext c′ (inLanes op f d n [] o pre post c))
         → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight (rows ρ s) P K ox)
         → Live v (∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post))
         → LL v c op f d n o pre (s ∷ post) (just (found (Γ′ , A′ , c′ , s′) m κ , cutT l K ox))
  x-wins ox e lx ap = pre , post , e , lzip v go lx ap
    where
      go : _ → _ → _
      go lx ap cl P oa = let r = lx cl P oa in proj₁ r , (λ ea → ea) , ap P (proj₂ r) , x-tight {ρ = ρ} l a s₀ (rowsL ρ post) (proj₂ r)

  step : ∀ C (x y : Maybe (Cand R B)) → Leadsᶜ C v (inLanes op f d n [] o pre post c) (rows ρ s) x → LLᶜ C v c op f d n o (s ∷ pre) post y
       → Live v (OKᶜ C (rows ρ s) (retag (cutT l) x)) → Live v (OKLᶜ C (rowsL ρ post) y) → Live v (Spread (rows ρ s ∷ rowsL ρ post))
       → LLᶜ C v c op f d n o pre (s ∷ post) (first (retag (cutT l) x) y)
  step C nothing nothing _ _ _ _ _ ()
  step C nothing (just (found (_ , _ , c′ , s′) m κ , K , o′)) _ ly okx _ _ b =
    ll-shift {c′ = c′} {s′} {m} {κ} {K} {o′} (ly b)
      (lmap v {X = OKᶜ {R} C (rows ρ s) nothing} {Y = ∀ P → Tight (Lanes (rowsL ρ post)) P K o′ → After P (rows ρ s)}
         (λ ok P tg → none-aft {R = R} {t = rows ρ s} {C = C} {K = K} (⊑i b) ok P (tight-⊑ tg)) okx)
  step C (just (found (_ , _ , c′ , s′) m κ , K , ox)) nothing lx _ _ oky _ b =
    x-wins {c′ = c′} {s′} {m} {κ} {K} ox (proj₁ (lx b)) (proj₂ (lx b))
      (lmap v {X = OKLᶜ {R} C (rowsL ρ post) nothing} {Y = ∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post)}
         (λ ok P tg → nones-aft {R = R} {C = C} {K = K} (rowsL ρ post) (⊑i b) ok P (tight-⊑ tg)) oky)
  step C (just (found (_ , _ , c′ , s′) m κ , K , ox)) (just (found (_ , _ , c″ , s″) m′ κ′ , K′ , o′)) lx ly okx oky sp b with K′ <ᴷ K in lt
  ... | true  = ll-shift {c′ = c″} {s″} {m′} {κ′} {K′} {o′} (ly b)
                  (lmap v {X = OKᶜ C (rows ρ s) (retag (cutT l) (just (found (_ , _ , c′ , s′) m κ , K , ox)))} {Y = ∀ P → Tight (Lanes (rowsL ρ post)) P K′ o′ → After P (rows ρ s)}
                     (λ ok P tg → lost-strict {R = R} {t = rows ρ s} {C = C} {P = P} {K = K} {K′ = K′} {g = found (_ , _ , c′ , s′) m κ} (tight-⊑ tg) (⊑i b) lt ok) okx)
  ... | false = x-wins {c′ = c′} {s′} {m} {κ} {K} ox (proj₁ (lx b)) (proj₂ (lx b))
                  (lzip v {X = OKLᶜ C (rowsL ρ post) (just (found (_ , _ , c″ , s″) m′ κ′ , K′ , o′))} {Z = ∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post)}
                     (λ ok (sp : Spread (rows ρ s ∷ rowsL ρ post)) P tg → each-past (rowsL ρ post) tg (proj₁ sp) (froms-lost {R = R} {C = C} {K = K} {K′ = K′} {g = found (_ , _ , c″ , s″) m′ κ′} (rowsL ρ post) (⊑i b) (⊑i lt) ok)) oky sp)

------------------------------------------------------------------------
-- A merge: the outer against the lanes

module Race {R Γ A B} (v : Bool) (c : Ctx R Γ B) (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (ls : List (St Γ B))
            (Ln : Pos → A → EmissionSet B) (Bg : EmissionSet B) (Over Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set)
            (bg-at : ∀ {Q e} → From (at Q) (rows (env c) o) → Lanes (rowsL (env c) ls) Q e → Bg Q e)
            (no-hand : ∀ {Q} → Apart (rows (env c) o) (Lanes (rowsL (env c) ls)) → From (at Q) (rows (env c) o) → Lanes (rowsL (env c) ls) Q end → ¬ Hand Q) where

  ρ : DenEnv Γ
  ρ = env c

  module J = Joining Ln (rows ρ o) Bg Over Runs Cut Hand

  FR : EmissionSet B
  FR = J.JoinT

  -- A lane's row no later than every outer row: begun, and ending
  -- handing off to none.
  lane-occ : ∀ {Q} (o′ o″ : Out B) → (∀ {b} → Fits o′ (out b) → Fits o″ (out b)) → Apart (rows ρ o) (Lanes (rowsL ρ ls)) → From (at Q) (rows ρ o)
           → Occ (Lanes (rowsL ρ ls)) Q o′ → Occ FR Q o″
  lane-occ {Q} o′ o″ fo ap fk oc = occ-bind oc go
    where
      go : ∀ {e} → Lanes (rowsL ρ ls) Q e → Fits o′ e → Occ FR Q o″
      go {e = out b} x fe = hit (J.run (bg-at fk x) tt) (fo fe)
      go {e = skip}  x _  = hit (J.run (bg-at fk x) tt) tt
      go {e = pin _} x _  = hit (J.run (bg-at fk x) tt) tt
      go {e = end}   x _  = occ λ k → k (J.rpass (bg-at fk x) (no-hand ap fk x) λ dn → k (J.rend (bg-at fk x) (no-hand ap fk x) dn) tt) tt

  outer-still : ∀ {Q} → Occ (rows ρ o) Q still → Occ FR Q still
  outer-still oc = occ-bind oc go
    where
      go : ∀ {Q e} → rows ρ o Q e → Fits still e → Occ FR Q still
      go {e = out _} r ()
      go {e = skip}  r _ = hit (J.step r) tt
      go {e = pin _} r _ = hit (J.opin r) tt
      go {e = end}   r _ = occ λ k → k (J.opass r λ dn → k (J.oend r dn) tt) tt

  -- On a tie, the outer no earlier than the lane's row.
  tight-from : ∀ {P k} {o′ o″ : Out B} → (∀ {Q} → From (at Q) (rows ρ o) → Occ (Lanes (rowsL ρ ls)) Q o′ → Occ FR Q o″) → From k (rows ρ o)
             → Tight (Lanes (rowsL ρ ls)) P k o′ → Tight FR P k o″
  tight-from h fk (strict lt)      = strict lt
  tight-from h fk (tie Q eq pq oc) = tie Q eq pq (h (subst (λ K → From K (rows ρ o)) eq fk) oc)

  lane-tight : ∀ {P k} (o′ : Out B) → Apart (rows ρ o) (Lanes (rowsL ρ ls)) → From k (rows ρ o) → Tight (Lanes (rowsL ρ ls)) P k o′
             → Tight FR P (proj₁ (laneT {A = A} d n [] k o′)) (proj₂ (laneT {A = A} d n [] k o′))
  lane-tight still          ap fk tg = tight-from (lane-occ still still (λ ()) ap) fk tg
  lane-tight (shows (nx b)) ap fk tg = tight-from (lane-occ (shows (nx b)) (shows (nx b)) (λ fe → fe) ap) fk tg
  lane-tight (shows cp)     ap fk tg = tight-from (lane-occ (shows cp) _ (λ ()) ap) fk tg

  outer-tight : ∀ {P h} (ox : Out A) → Tight (rows ρ o) P h ox → (∀ {e} → ox ≡ shows e → Σ Pos λ q → h ≡ at q × rows ρ o q (toEv e))
              → Tight FR P (proj₁ (outerT {B = B} n [] h ox)) (proj₂ (outerT {B = B} n [] h ox))
  outer-tight still tg sh = tight-occ outer-still tg
  outer-tight (shows (nx x)) tg sh with sh refl
  ... | q , refl , r = tie (q ++ [ ix 0 ]) refl (⊑-trans (tight-⊑ tg) (ext-⊑ q [ ix 0 ])) (hit (J.val r) tt)
  outer-tight (shows cp) tg sh with sh refl
  ... | q , refl , r = tie q refl (tight-⊑ tg) (occ λ k → k (J.opass r λ dn → k (J.oend r dn) tt) tt)

  outer-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ h} (ox : Out A) (e : Ext c′ (inOuter op f d n [] ls c))
             → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight (rows ρ o) P h ox)
             → Live v (Bd (rows ρ o) κ h ox)
             → Live v (∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls))
             → Leads v c FR (just (found (Γ′ , A′ , c′ , s′) m κ , outerT n [] h ox))
  outer-wins ox e lx b al = eOuter e , lzip3 v go lx b al
    where
      go : _ → _ → _ → _
      go lx b al cl P oa = let r = lx cl P oa in (al P (tight-⊑ (proj₂ r)) , proj₁ r) , outer-tight ox (proj₂ r) (Bd.shown b)

  lane-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ k} (o′ : Out B) pre₁ post₁ (e : Ext c′ (inLanes op f d n [] o pre₁ post₁ c))
            → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × (⊤ → Each (After P) (rowsL ρ pre₁)) × Each (After P) (rowsL ρ post₁) × Tight (Lanes (rowsL ρ ls)) P k o′)
            → Live v (∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o))
            → Live v (From k (rows ρ o) × Parts (rows ρ o) (rowsL ρ ls))
            → Leads v c FR (just (found (Γ′ , A′ , c′ , s′) m κ , laneT {A = A} d n [] k o′))
  lane-wins o′ pre₁ post₁ e ly ao fp = eLanes e , lzip3 v go ly ao fp
    where
      go : _ → _ → _ → _
      go ly ao (fk , pa) cl P oa = let r = ly cl P oa ; tg = proj₂ (proj₂ (proj₂ r)) in
        (ao P tg , proj₁ (proj₂ r) tt , proj₁ (proj₂ (proj₂ r)) , proj₁ r) , lane-tight o′ (proj₁ pa) fk tg

  race-leads : ∀ C (x : Maybe (Cand R A)) (y : Maybe (Cand R B))
             → Leadsᶜ C v (inOuter op f d n [] ls c) (rows ρ o) x → LLᶜ C v c op f d n o [] ls y
             → Live v (OKᶜ C (rows ρ o) x) → Live v (OKLᶜ C (rowsL ρ ls) y) → Live v (Parts (rows ρ o) (rowsL ρ ls))
             → Leadsᶜ C v c FR (raceT d n [] x y)
  race-leads C nothing nothing _ _ _ _ _ ()
  race-leads C nothing (just (found (_ , _ , c′ , s′) m κ , k , o′)) _ ly okx _ pa b =
    let kC = up {K = k} {C = C} (raise-lane {A} d n [] k o′) b ; (pre₁ , post₁ , e , l) = ly (un kC) in
    lane-wins {c′ = c′} {s′} {m} {κ} {k} o′ pre₁ post₁ e l
      (lmap v {X = OKᶜ {R} C (rows ρ o) nothing} {Y = ∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o)}
         (λ ok P tg → none-aft {R = R} {t = rows ρ o} {C = C} {K = k} kC ok P (tight-⊑ tg)) okx)
      (lzip v {X = OKᶜ {R} C (rows ρ o) nothing} {Z = From k (rows ρ o) × Parts (rows ρ o) (rowsL ρ ls)}
         (λ ok p → from-none {R = R} {t = rows ρ o} {C = C} {K = k} kC ok , p) okx pa)
  race-leads C (just (found (_ , _ , c′ , s′) m κ , h , ox)) nothing lx _ okx oky _ b =
    let hC = up {K = h} {C = C} (raise-outer {B = B} n [] h ox) b in
    outer-wins {c′ = c′} {s′} {m} {κ} {h} ox (proj₁ (lx (un hC))) (proj₂ (lx (un hC)))
      (lmap v (exact C (just (found (_ , _ , c′ , s′) m κ , h , ox)) (un hC)) okx)
      (lmap v {X = OKLᶜ {R} C (rowsL ρ ls) nothing} {Y = ∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls)}
         (λ ok P ph → nones-aft {R = R} {C = C} {K = h} (rowsL ρ ls) hC ok P ph) oky)
  race-leads C (just (found (_ , _ , c′ , s′) m κ , h , ox)) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′)) lx ly okx oky pa b
    with h <ᴷ k in lt
  ... | true  =
    let hC = up {K = h} {C = C} (raise-outer {B = B} n [] h ox) b in
    outer-wins {c′ = c′} {s′} {m} {κ} {h} ox (proj₁ (lx (un hC))) (proj₂ (lx (un hC)))
      (lmap v (exact C (just (found (_ , _ , c′ , s′) m κ , h , ox)) (un hC)) okx)
      (lmap v {X = OKLᶜ C (rowsL ρ ls) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′))} {Y = ∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls)}
         (λ ok P ph → lost-strict-each {R = R} {C = C} {P = P} {K = h} {K′ = k} {g = found (_ , _ , c″ , s″) m′ κ′} (rowsL ρ ls) ph hC lt ok) oky)
  ... | false =
    let kC = up {K = k} {C = C} (raise-lane {A} d n [] k o′) b ; (pre₁ , post₁ , e′ , l) = ly (un kC) in
    lane-wins {c′ = c″} {s″} {m′} {κ′} {k} o′ pre₁ post₁ e′ l
      (lzip v {X = OKᶜ C (rows ρ o) (just (found (_ , _ , c′ , s′) m κ , h , ox))} {Z = ∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o)}
         (λ ok (pa : Parts (rows ρ o) (rowsL ρ ls)) P tg → past-tie {u = rows ρ o} tg (from-lost {R = R} {t = rows ρ o} {C = C} {h = h} {k = k} {f = found (_ , _ , c′ , s′) m κ} kC lt ok)
                                                            (λ {q} {e} {e′} x r → proj₁ pa {q} {e′} {e} r x)) okx pa)
      (lzip v {X = OKᶜ C (rows ρ o) (just (found (_ , _ , c′ , s′) m κ , h , ox))} {Z = From k (rows ρ o) × Parts (rows ρ o) (rowsL ρ ls)}
         (λ ok p → from-lost {R = R} {t = rows ρ o} {C = C} {h = h} {k = k} {f = found (_ , _ , c′ , s′) m κ} kC lt ok , p) okx pa)

------------------------------------------------------------------------
-- Every node

of-out : ∀ {R Γ A} (c : Ctx R Γ A) {i p x xs} → closed c ≡ false → outOf c (ofS i p (x ∷ xs)) ofM ≡ shows (nx x)
of-out c cl with closed c
of-out c () | true
of-out c cl | false = refl

-- Marks no of owns lead nothing.
own-none : ∀ {R Γ A} v (c : Ctx R Γ A) {s : St Γ A} {t} ms → (∀ {m P} → OfAt s m P → ⊥) → Leads v c t (ownBest c s ms)
own-none v     c []       no = tt₁
own-none v c {s} {t} ((m , k) ∷ ms) no = first-leads {v = v} {c = c} {t = t} (just (found (_ , _ , c , s) m k , k , outOf c s m)) (ownBest c s ms) (one v) (λ _ → own-none v c ms no)
  where
    one : ∀ v → Leads v c t (just (found (_ , _ , c , s) m k , k , outOf c s m))
    one true  = stop , λ cl P oa → ⊥-elim (no oa)
    one false = stop , tt

-- A cold's own mark leads: its tape's next step keys its rows, tight.
cold-lead : ∀ {R Γ A} v (c : Ctx R Γ A) b (l : Tape A) → Leads v c (rows (env c) (coldS b l)) (ownBest c (coldS b l) (own (coldS {Γ = Γ} b l)))
cold-lead v     c b     over                       = tt₁
cold-lead false c b     (play τ u i t fr)          = stop , tt
cold-lead false c b     (ending e)                 = stop , tt
cold-lead true  c false (play τ u i t fr)          = stop , λ _ _ ()
cold-lead true  c false (ending e)                 = stop , λ _ _ ()
cold-lead true  c true  (play τ u i t (emit a k))  with closed c
... | false = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-out refl)
... | true  = stop , λ ()
cold-lead true  c true  (play τ u i t (stall k))   = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-skip tt)
cold-lead true  c true  (play τ u i t (close k))   = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-skip tt)
cold-lead true  c true  (ending e)                 = stop , λ _ _ eq → tt , tie _ refl (subst (λ q → at _ ⊑ at q) eq (⊑-refl _)) (hit at-end tt)

-- What is asked of a live node only: nothing under a cut switched off.
data Gate (P : Set₁) : Bool → Set₁ where
  on  : P → Gate P true
  off : Gate P false

gate : ∀ {P Q v} → (P → Q) → Gate P v → Gate Q v
gate f (on p) = on (f p)
gate f off    = off

gate-on : ∀ {P Q} v → (P → Q) → Gate P v → Gate Q (v Data.Bool.∧ true)
gate-on .true  f (on p) = on (f p)
gate-on .false f off    = off

gate-off : ∀ {Q} v → Gate Q (v Data.Bool.∧ false)
gate-off true  = off
gate-off false = off

postulate
  -- A CONNECT'S SEARCH LEADS: whatever its source or its body finds, the
  -- source winning only strictly before the body, keys the connect's rows,
  -- and the part that lost lies past it: the body's own rows past a
  -- source's find, the source's rows past a body's.  Under a cap, at
  -- any binder: the body's rows read its binder, so its search leads only
  -- up to a cap no later than the source's find, as `conn-okᶜ` bounds it.
  --
  -- Only a find that beats the connect's own marks: with a completed
  -- body's teardown owed, the source's find is keyed where it sits, and
  -- a tie there has no connect row at its key, its echoes lying one
  -- `ix 0` below.  The owed mark, just past the body's end, keys before
  -- any source row, so that find never wins.
  conn-leadᶜ : ∀ {R Γ A X} C v (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) → EnvSingle (env c) → G (env c) v (connS k o b) → Gate (Quiet C (env c) (connS k o b)) v
             → Beats (ownBest c (connS k o b) (own (connS k o b))) (kids c (connS k o b))
             → Leadsᶜ C v c (rows (env c) (connS k o b)) (kids c (connS k o b))

  -- A TAKE'S SEARCH LEADS: unfailed, its child's find through the take,
  -- every part it lost past the shown event; failed, nothing shown.
  take-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) i q w (s : St Γ A) → EnvSingle (env c) → G (env c) v (takeS i q w s) → Gate (Quiet C (env c) (takeS i q w s)) v
             → Leadsᶜ C v c (rows (env c) (takeS i q w s)) (kids c (takeS i q w s))

  -- A BOUNDED MERGE'S SEARCH WITH VALUES WAITING LEADS: the raced find,
  -- every other part past it, a lane's end handing off to the queue.
  bounded-wait-leadᶜ : ∀ {R Γ A B} C v (c : Ctx R Γ B) m (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) ls → EnvSingle (env c)
                     → G (env c) v (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls) → Gate (Quiet C (env c) (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls)) v
                     → Leadsᶜ C v c (rows (env c) (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls)) (kids c (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls))

own-lead : ∀ {R Γ A} v (c : Ctx R Γ A) (s : St Γ A) → G (env c) v s → Leads v c (rows (env c) s) (ownBest c s (own s))
own-lead true  c (ofS i p [])         _ = stop , λ { cl _ refl → tt , tie (p ++ [ last ]) refl (⊑-refl _) (hit at-end tt) }
own-lead true  c (ofS i p (x ∷ xs))   _ = stop , λ { cl _ refl → tt , tie (p ++ [ ix i ]) refl (⊑-refl _) (hit {e = out x} at-out (of-out c {i} {p} {x} {xs} cl)) }
own-lead true  c (cutS l (attAt q) s) _ = stop , λ cl P ()
own-lead false c (ofS i p [])         _ = stop , tt
own-lead false c (ofS i p (x ∷ xs))   _ = stop , tt
own-lead false c (cutS l (attAt q) s) _ = stop , tt
own-lead v c (cutS l attached s)  _ = tt₁
own-lead v c (mapS f s)           _ = tt₁
own-lead v c doneS                _ = tt₁
own-lead v c (pend o _)             _ = tt₁
own-lead v c (flatS op f d n q o ls) _ = tt₁
own-lead v c (lnS b s)            ()
own-lead v c (scanS f z s)        _ = tt₁
own-lead v c (coldS b l)          _ = cold-lead v c b l
own-lead v c (takeS i q w s)      _ = own-none v c {takeS i q w s} (own (takeS i q w s)) (λ ())
own-lead v c (connS k o b)        _ = own-none v c {connS k o b} (own (connS k o b)) (λ ())
own-lead v c (joinS j g x ib)     _ = own-none v c {joinS j g x ib} (own (joinS j g x ib)) (λ ())

-- A live node's search, at or before the cap.
okᵛ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → EnvSingle (env c) → G (env c) v s → Gate (Quiet C (env c) s) v → Before C (seek c s) → Live v (OK (rows (env c) s) (seek c s))
okᵛ C true  c s es g (on qt) b = exact C (seek c s) b (seek-okᶜ C c s es g qt)
okᵛ C false c s es g qt b = tt

mutual
  seek-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → EnvSingle (env c) → G (env c) v s → Gate (Quiet C (env c) s) v → Leadsᶜ C v c (rows (env c) s) (seek c s)
  seek-leadᶜ C v c s es g qt = first-leadsᶜ C (ownBest c s (own s)) (kids c s) (own-lead v c s g) (λ w → kids-leadᶜ C v c s es g qt w)

  kids-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → EnvSingle (env c) → G (env c) v s → Gate (Quiet C (env c) s) v
             → Beats (ownBest c s (own s)) (kids c s) → Leadsᶜ C v c (rows (env c) s) (kids c s)
  kids-leadᶜ C v c (mapS f s) es g qt _ b =
    map-leads v f (seek (inMap f c) s) (seek-leadᶜ C v (inMap f c) s es g (gate (λ q {X} → q {X}) qt) (before-retag C (mapT f) (raise-map f) (seek (inMap f c) s) b))
  kids-leadᶜ C v c (cutS true a s) es g qt _ b =
    cut-on v (seek (inCut true a c) s) (seek-leadᶜ C (v Data.Bool.∧ true) (inCut true a c) s es g (gate-on v (λ q {X} → q {X}) qt) (before-retag C (cutT true) (raise-cut true) (seek (inCut true a c) s) b))
  kids-leadᶜ C v c (cutS false a s) es g qt _ b =
    cut-off v (seek (inCut false a c) s) (seek-leadᶜ C (v Data.Bool.∧ false) (inCut false a c) s es g (gate-off v) (before-retag C (cutT false) (raise-cut false) (seek (inCut false a c) s) b))
  kids-leadᶜ C true c (flatS (mergeᶠ nothing) f d n q o ls) es g (on qt) _ with MergeG.fresh g
  ... | refl = join-leadᶜ C true c (mergeᶠ nothing) f d n o ls (λ _ x → x) (λ _ _ _ ()) es outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
                 (join-okᶜ C c (mergeᶠ nothing) f d n [] o ls (flat-race (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
                    es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
  kids-leadᶜ C false c (flatS (mergeᶠ nothing) f d n q o ls) es g qt _ with MergeG.fresh g
  ... | refl = join-leadᶜ C false c (mergeᶠ nothing) f d n o ls (λ _ x → x) (λ _ _ _ ()) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
  kids-leadᶜ C true c (flatS (mergeᶠ (just m)) f d n [] o ls) es (g , _) (on qt) _ =
    join-leadᶜ C true c (mergeᶠ (just m)) f d n o ls (λ _ x → begun x) (bounded-unqueued m _ _ _ d n) es outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
      (join-okᶜ C c (mergeᶠ (just m)) f d n [] o ls (bounded-race m (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
         es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
          open BoundedF m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n [] (rowsL (env c) ls) using (begun)
  kids-leadᶜ C false c (flatS (mergeᶠ (just m)) f d n [] o ls) es (g , _) qt _ =
    join-leadᶜ C false c (mergeᶠ (just m)) f d n o ls (λ _ x → begun x) (bounded-unqueued m _ _ _ d n) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
    where open BoundedF m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n [] (rowsL (env c) ls) using (begun)
  kids-leadᶜ C v c (flatS (mergeᶠ (just m)) f d n (a ∷ q) o ls) es g qt _ = bounded-wait-leadᶜ C v c m f d n a q o ls es g qt
  kids-leadᶜ C true c (flatS switchᶠ f d n q o ls) es g (on qt) _ with MergeG.fresh g
  ... | refl = join-leadᶜ C true c switchᶠ f d n o ls (switch-at _ _ _ d n) (λ _ _ _ ()) es outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
                 (join-okᶜ C c switchᶠ f d n [] o ls (switch-race (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
                    es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
  kids-leadᶜ C false c (flatS switchᶠ f d n q o ls) es g qt _ with MergeG.fresh g
  ... | refl = join-leadᶜ C false c switchᶠ f d n o ls (switch-at _ _ _ d n) (λ _ _ _ ()) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
  kids-leadᶜ C true c (flatS exhaustᶠ f d n q o ls) es g (on qt) _ with MergeG.fresh g
  ... | refl = join-leadᶜ C true c exhaustᶠ f d n o ls (λ _ x → x) (λ _ _ _ ()) es outer lanesG (on (calm-fst C (env c) qt)) (on (calm-snd C (env c) qt)) (rooted-parts rooted)
                 (join-okᶜ C c exhaustᶠ f d n [] o ls (exhaust-race (λ a → pendRows (env c) (f a)) (rows (env c) o) (rowsL (env c) ls) d n (rooted-single rooted) spent)
                    es outer lanesG (calm-fst C (env c) qt) (calm-snd C (env c) qt))
    where open MergeG g
  kids-leadᶜ C false c (flatS exhaustᶠ f d n q o ls) es g qt _ with MergeG.fresh g
  ... | refl = join-leadᶜ C false c exhaustᶠ f d n o ls (λ _ x → x) (λ _ _ _ ()) es (MergeG.outer g) (MergeG.lanesG g) off off tt tt
  kids-leadᶜ C v c (ofS _ _ _)    _ _ _ _ ()
  kids-leadᶜ C v c doneS          _ _ _ _ ()
  kids-leadᶜ C v c (pend _ _)     _ _ _ _ ()
  kids-leadᶜ C v c (coldS _ _)    _ _ _ _ ()
  kids-leadᶜ C v c (joinS _ _ _ _) _ _ _ _ ()
  kids-leadᶜ C v c (lnS _ _)      _ () _ _
  kids-leadᶜ C true c (scanS f z s) es g qt _ b =
    let b′ = before-retag C (scanT f z) (raise-scan f z) (seek (inScan f z c) s) b in
    scan-leads true f z (seek (inScan f z c) s) (okᵛ C true (inScan f z c) s es g qt b′) (seek-leadᶜ C true (inScan f z c) s es g qt b′)
  kids-leadᶜ C false c (scanS f z s) es g qt _ b =
    scan-leads false f z (seek (inScan f z c) s) tt (seek-leadᶜ C false (inScan f z c) s es g qt (before-retag C (scanT f z) (raise-scan f z) (seek (inScan f z c) s) b))
  kids-leadᶜ C v c (takeS i q w s) es g qt _ = take-leadᶜ C v c i q w s es g qt
  kids-leadᶜ C v c (connS k o b) es g qt w = conn-leadᶜ C v c k o b es g qt w

  -- A joiner with nothing queued, by its policy: the race's find leads.
  join-leadᶜ : ∀ {R Γ A B} C v (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n (o : St Γ A) ls
               {Ln : Pos → A → EmissionSet B} {Bg : EmissionSet B} {Over Runs : Pos → Set} {Cut : Pos → Pos → Set} {Hand : Pos → Set}
             → (∀ {Q e} → From (at Q) (rows (env c) o) → Lanes (rowsL (env c) ls) Q e → Bg Q e)
             → (∀ {Q} → Apart (rows (env c) o) (Lanes (rowsL (env c) ls)) → From (at Q) (rows (env c) o) → Lanes (rowsL (env c) ls) Q end → ¬ Hand Q)
             → EnvSingle (env c) → G (env c) v o → GL (env c) v ls → Gate (Quiet C (env c) o) v → Gate (QuietL C (env c) ls) v
             → Live v (Parts (rows (env c) o) (rowsL (env c) ls))
             → Live v (OKᶜ C (Joining.JoinT Ln (rows (env c) o) Bg Over Runs Cut Hand)
                          (raceT d n [] (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls)))
             → Leadsᶜ C v c (Truncate (Joining.JoinT Ln (rows (env c) o) Bg Over Runs Cut Hand))
                            (raceT d n [] (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls))
  join-leadᶜ C true c op f d n o ls {Ln} {Bg} {Over} {Runs} {Cut} {Hand} ba nh es go gl (on qo) (on ql) pa ok b =
    leads-trunc true (raceT d n [] (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls))
      (exact C (raceT d n [] (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls)) b ok)
      (Race.race-leads true c op f d n o ls Ln Bg Over Runs Cut Hand ba nh C
        (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls)
        (seek-leadᶜ C true (inOuter op f d n [] ls c) o es go (on qo)) (lanes-leadᶜ C true c op f d n o [] ls es gl (on ql) (proj₂ pa))
        (seek-okᶜ C (inOuter op f d n [] ls c) o es go qo) (lanes-okᶜ C c op f d n [] o [] ls es gl ql) pa b)
  join-leadᶜ C false c op f d n o ls {Ln} {Bg} {Over} {Runs} {Cut} {Hand} ba nh es go gl qo ql pa ok b =
    leads-trunc false (raceT d n [] (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls)) tt
      (Race.race-leads false c op f d n o ls Ln Bg Over Runs Cut Hand ba nh C
        (seek (inOuter op f d n [] ls c) o) (lanes c op f d n [] o [] ls)
        (seek-leadᶜ C false (inOuter op f d n [] ls c) o es go qo) (lanes-leadᶜ C false c op f d n o [] ls es gl ql tt) tt tt tt b)

  seek-ln-leadᶜ : ∀ {R Γ A} C v (c : Ctx R Γ A) (s : St Γ A) → EnvSingle (env c) → GLn (env c) v s → Gate (Quiet C (env c) s) v → Leadsᶜ C v c (rows (env c) s) (seek c s)
  seek-ln-leadᶜ C v c (lnS true (cutS .true a s₀)) es (refl , g₀ , _) qt b =
    ln-leads (seek (inLn true c) (cutS true a s₀)) (seek-leadᶜ C v (inLn true c) (cutS true a s₀) es g₀ qt b)
  seek-ln-leadᶜ C v c (lnS false (cutS .false a s₀)) es (refl , g₀ , _) qt b =
    ln-leads (seek (inLn false c) (cutS false a s₀)) (seek-leadᶜ C v (inLn false c) (cutS false a s₀) es g₀ qt b)
  seek-ln-leadᶜ C v c (lnS _ (pend _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (coldS _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (ofS _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (doneS)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (mapS _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (scanS _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (lnS _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (takeS _ _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (flatS _ _ _ _ _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (connS _ _ _)) _ ()
  seek-ln-leadᶜ C v c (lnS _ (joinS _ _ _ _)) _ ()
  seek-ln-leadᶜ C v c (pend _ _) _ ()
  seek-ln-leadᶜ C v c (coldS _ _) _ ()
  seek-ln-leadᶜ C v c (ofS _ _ _) _ ()
  seek-ln-leadᶜ C v c doneS _ ()
  seek-ln-leadᶜ C v c (mapS _ _) _ ()
  seek-ln-leadᶜ C v c (scanS _ _ _) _ ()
  seek-ln-leadᶜ C v c (cutS _ _ _) _ ()
  seek-ln-leadᶜ C v c (takeS _ _ _ _) _ ()
  seek-ln-leadᶜ C v c (flatS _ _ _ _ _ _ _) _ ()
  seek-ln-leadᶜ C v c (connS _ _ _) _ ()
  seek-ln-leadᶜ C v c (joinS _ _ _ _) _ ()

  lanes-leadᶜ : ∀ {R Γ A B} C v (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre (ls : List (St Γ B)) → EnvSingle (env c) → GL (env c) v ls → Gate (QuietL C (env c) ls) v
              → Live v (Spread (rowsL (env c) ls)) → LLᶜ C v c op f d n o pre ls (lanes c op f d n [] o pre ls)
  lanes-leadᶜ C v c op f d n o pre [] _ _ _ _ ()
  lanes-leadᶜ C false c op f d n o pre (lnS l (cutS .l a s₀) ∷ post) es (gs@(refl , _) , gp) ql sp =
    Step.step false c op f d n o pre post l a s₀ C
      (seek (inLanes op f d n [] o pre post c) (lnS l (cutS l a s₀))) (lanes c op f d n [] o (lnS l (cutS l a s₀) ∷ pre) post)
      (seek-ln-leadᶜ C false (inLanes op f d n [] o pre post c) (lnS l (cutS l a s₀)) es gs off)
      (lanes-leadᶜ C false c op f d n o (lnS l (cutS l a s₀) ∷ pre) post es gp off tt) tt tt tt
  lanes-leadᶜ C true c op f d n o pre (lnS l (cutS .l a s₀) ∷ post) es (gs@(refl , _) , gp) (on ql) sp =
    Step.step true c op f d n o pre post l a s₀ C
      (seek (inLanes op f d n [] o pre post c) (lnS l (cutS l a s₀))) (lanes c op f d n [] o (lnS l (cutS l a s₀) ∷ pre) post)
      (seek-ln-leadᶜ C true (inLanes op f d n [] o pre post c) (lnS l (cutS l a s₀)) es gs (on (calm-fst C (env c) ql)))
      (lanes-leadᶜ C true c op f d n o (lnS l (cutS l a s₀) ∷ pre) post es gp (on (calm-snd C (env c) ql)) (proj₂ sp))
      (cap-retag C (cutT l) (raise-cut l) (λ r → _ , _ , r , ⊑-refl _) (λ y → lane-ok (lnS l (cutS l a s₀)) y)
         (seek (inLanes op f d n [] o pre post c) (lnS l (cutS l a s₀))) (seek-lnᶜ C (inLanes op f d n [] o pre post c) (lnS l (cutS l a s₀)) es gs (calm-fst C (env c) ql)))
      (lanes-okᶜ C c op f d n [] o (lnS l (cutS l a s₀) ∷ pre) post es gp (calm-snd C (env c) ql))
      sp
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (pend _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (coldS _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (ofS _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (doneS)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (mapS _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (scanS _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (lnS _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (takeS _ _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (flatS _ _ _ _ _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (connS _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((lnS _ (joinS _ _ _ _)) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((pend _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((coldS _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((ofS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre (doneS ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((mapS _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((scanS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((cutS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((takeS _ _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((flatS _ _ _ _ _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((connS _ _ _) ∷ post) _ (() , _) _ _
  lanes-leadᶜ C v c op f d n o pre ((joinS _ _ _ _) ∷ post) _ (() , _) _ _

-- At no binder, every cap at once.
seek-lead : ∀ {R A} v (c : Ctx R [] A) (s : St [] A) → G (env c) v s → Leads v c (rows (env c) s) (seek c s)
seek-lead true  c s g = uncap-lead (seek c s) (λ C → seek-leadᶜ C true c s (λ ()) g (on (λ ())))
seek-lead false c s g = uncap-lead (seek c s) (λ C → seek-leadᶜ C false c s (λ ()) g off)

-- What the search finds at an of, every merge above it led.
lead-found : ∀ {R Γ A} {t : St [] R} {c : Ctx R Γ A} {s : St Γ A} {m κ P} → closed c ≡ false → OfAt s m P → Good [] t
           → search top t ≡ just (found (Γ , A , c , s) m κ) → LeadC c P
lead-found {R} {Γ} {A} {t} {c} {s} {m} {κ} {P} cl oa g fd = go (seek top t) (seek-lead true top t g) fd
  where
    go : (y : Maybe (Cand R R)) → Leads true top (rows [] t) y → mapᴹ proj₁ y ≡ just (found (Γ , A , c , s) m κ) → LeadC c P
    go (just (found (_ , _ , c′ , s′) m′ κ′ , K , o)) (e , l) refl = lead-ext e (proj₁ (l cl P oa)) tt
