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
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; <ᵖ-split)
open import denotation.EmissionSet using (EmissionSet; DenEnv; Ev; Truncate; out; skip; pin; end; _≺_; MapT; map-out; map-skip; map-pin; map-end; at-out; at-end)
open import operation.Key using (Key; at; _<ᴷ_; ≮ᴷ-trans; at-<ᵖ; clash)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Cand; found; Mark; ofM; attM; Att; Out; still; shows; nx; cp; seek; search; kids; lanes; own; ownBest; first; retag;
                    raceT; outerT; laneT; mapT; cutT; alive; outOf; closed; attached; attAt;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inCut; inLn; inOuter; inLanes)
open import adequacy.Rows using (env; rows; rowsL; pendRows; toEv; Lanes; Each; module Flat)
open import adequacy.Bound using (_⊑_; ⊑i; ⊑-refl; ⊑-trans; <→⊑; ext-⊑; From; Bd; OK; OKL; Live;
                                         Apart; Spread; Parts; rooted-parts; ⊑→≼; join-ok; MergeG; G; GL; GLn; Good; ofPos; from-weak; seek-ok; seek-ln; lane-ok; lanes-ok)
open import adequacy.Skip using (After; LeadC)

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
-- The frames between a node and what its search found

data Ext {R} {Γ′ A′} (c′ : Ctx R Γ′ A′) : ∀ {Γ A} → Ctx R Γ A → Set₁ where
  stop   : Ext c′ c′
  eMap   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} → Ext c′ (inMap f c) → Ext c′ c
  eCut   : ∀ {Γ A} {l a} {c : Ctx R Γ A} → Ext c′ (inCut l a c) → Ext c′ c
  eLn    : ∀ {Γ A} {b} {c : Ctx R Γ A} → Ext c′ (inLn b c) → Ext c′ c
  eOuter : ∀ {Γ A B} {f d n q ls} {c : Ctx R Γ B} → Ext c′ (inOuter {A = A} (mergeᶠ nothing) f d n q ls c) → Ext c′ c
  eLanes : ∀ {Γ A B} {f d n q} {o : St Γ A} {pre post} {c : Ctx R Γ B} → Ext c′ (inLanes (mergeᶠ nothing) f d n q o pre post c) → Ext c′ c

-- Each merge's other parts past `P`, over the added frames.
LeadE : ∀ {R Γ′ A′ Γ A} {c′ : Ctx R Γ′ A′} {c : Ctx R Γ A} → Ext c′ c → Pos → Set
LeadE stop                                        P = ⊤
LeadE (eMap e)                                    P = LeadE e P
LeadE (eCut e)                                    P = LeadE e P
LeadE (eLn e)                                     P = LeadE e P
LeadE (eOuter {ls = ls} {c = c} e)                P = Each (After P) (rowsL (env c) ls) × LeadE e P
LeadE (eLanes {o = o} {pre = pre} {post = post} {c = c} e) P =
  After P (rows (env c) o) × Each (After P) (rowsL (env c) pre) × Each (After P) (rowsL (env c) post) × LeadE e P

lead-ext : ∀ {R Γ′ A′ Γ A} {c′ : Ctx R Γ′ A′} {c : Ctx R Γ A} (e : Ext c′ c) {P} → LeadE e P → LeadC c P → LeadC c′ P
lead-ext stop       _                  lc = lc
lead-ext (eMap e)   le                 lc = lead-ext e le lc
lead-ext (eCut e)   le                 lc = lead-ext e le lc
lead-ext (eLn e)    le                 lc = lead-ext e le lc
lead-ext (eOuter e) (a , le)           lc = lead-ext e le (a , lc)
lead-ext (eLanes e) (a , b , d , le)   lc = lead-ext e le (a , b , d , lc)

∨-true : ∀ b → (b Data.Bool.∨ true) ≡ true
∨-true true  = refl
∨-true false = refl

ext-closed : ∀ {R Γ′ A′ Γ A} {c′ : Ctx R Γ′ A′} {c : Ctx R Γ A} → Ext c′ c → closed c ≡ true → closed c′ ≡ true
ext-closed stop       h = h
ext-closed (eMap e)   h = ext-closed e h
ext-closed (eCut {l = l} {c = c} e) h = ext-closed e (subst (λ b → (Data.Bool.not l Data.Bool.∨ b) ≡ true) (sym h) (∨-true (Data.Bool.not l)))
ext-closed (eLn e)    h = ext-closed e h
ext-closed (eOuter e) h = ext-closed e h
ext-closed (eLanes e) h = ext-closed e h

------------------------------------------------------------------------
-- What a search finds, read at the of it found

-- An of's own mark: the position of its next row.
OfAt : ∀ {Γ A} → St Γ A → Mark → Pos → Set
OfAt (ofS i p xs) ofM P = P ≡ ofPos p i xs
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

first-leads : ∀ {R Γ A} {v} {c : Ctx R Γ A} {t} (x y : Maybe (Cand R A)) → Leads v c t x → Leads v c t y → Leads v c t (first x y)
first-leads nothing            y                    lx ly = ly
first-leads (just x)           nothing              lx ly = lx
first-leads (just (f , h , o)) (just (g , h′ , o′)) lx ly with h′ <ᴷ h
... | true  = ly
... | false = lx

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
LL : ∀ {R Γ A B} → Bool → Ctx R Γ B → (A → _) → Bool → _ → St Γ A → List (St Γ B) → List (St Γ B) → Maybe (Cand R B) → Set₁
LL v c f d n o pre ls nothing = ⊤₁
LL {Γ = Γ} {B = B} v c f d n o pre ls (just (found (_ , _ , c′ , s′) m κ , K , o′)) =
  Σ (List (St Γ B)) λ pre₁ → Σ (List (St Γ B)) λ post₁ → Σ (Ext c′ (inLanes (mergeᶠ nothing) f d n [] o pre₁ post₁ c)) λ e →
    Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P →
      LeadE e P × (Each (After P) (rowsL (env c) pre) → Each (After P) (rowsL (env c) pre₁)) × Each (After P) (rowsL (env c) post₁) × Tight (Lanes (rowsL (env c) ls)) P K o′)

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
module Step {R Γ A B} (v : Bool) (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (pre post : List (St Γ B))
            (l : Bool) (a : Att) (s₀ : St Γ B) where

  ρ : DenEnv Γ
  ρ = env c

  s : St Γ B
  s = lnS l (cutS l a s₀)

  ll-shift : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K} {o′ : Out B}
           → LL v c f d n o (s ∷ pre) post (just (found (Γ′ , A′ , c′ , s′) m κ , K , o′))
           → Live v (∀ P → Tight (Lanes (rowsL ρ post)) P K o′ → After P (rows ρ s))
           → LL v c f d n o pre (s ∷ post) (just (found (Γ′ , A′ , c′ , s′) m κ , K , o′))
  ll-shift (pre₁ , post₁ , e , ly) as = pre₁ , post₁ , e , lzip v go ly as
    where
      go : _ → _ → _
      go ly as cl P oa = let r = ly cl P oa ; tg = proj₂ (proj₂ (proj₂ r)) in
        proj₁ r , (λ ea → proj₁ (proj₂ r) (as P tg , ea)) , proj₁ (proj₂ (proj₂ r)) , tight-occ (λ oc → occ-bind oc λ x fe → hit (inj₂ x) fe) tg

  x-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K} (ox : Out B) (e : Ext c′ (inLanes (mergeᶠ nothing) f d n [] o pre post c))
         → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight (rows ρ s) P K ox)
         → Live v (∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post))
         → LL v c f d n o pre (s ∷ post) (just (found (Γ′ , A′ , c′ , s′) m κ , cutT l K ox))
  x-wins ox e lx ap = pre , post , e , lzip v go lx ap
    where
      go : _ → _ → _
      go lx ap cl P oa = let r = lx cl P oa in proj₁ r , (λ ea → ea) , ap P (proj₂ r) , x-tight {ρ = ρ} l a s₀ (rowsL ρ post) (proj₂ r)

  step : (x y : Maybe (Cand R B)) → Leads v (inLanes (mergeᶠ nothing) f d n [] o pre post c) (rows ρ s) x → LL v c f d n o (s ∷ pre) post y
       → Live v (OK (rows ρ s) (retag (cutT l) x)) → Live v (OKL (rowsL ρ post) y) → Live v (Spread (rows ρ s ∷ rowsL ρ post))
       → LL v c f d n o pre (s ∷ post) (first (retag (cutT l) x) y)
  step nothing nothing _ _ _ _ _ = tt₁
  step nothing (just (found (_ , _ , c′ , s′) m κ , K , o′)) _ ly okx _ _ =
    ll-shift {c′ = c′} {s′} {m} {κ} {K} {o′} ly (lmap v {X = OK {R} (rows ρ s) nothing} {Y = ∀ P → Tight (Lanes (rowsL ρ post)) P K o′ → After P (rows ρ s)} (λ em P _ {q} {e} r → ⊥-elim (em {q} {e} r)) okx)
  step (just (found (_ , _ , c′ , s′) m κ , K , ox)) nothing (e , lx) _ _ oky _ =
    x-wins {c′ = c′} {s′} {m} {κ} {K} ox e lx (lmap v {X = OKL {R} (rowsL ρ post) nothing} {Y = ∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post)} (λ em P _ → each-empty {P = P} (rowsL ρ post) em) oky)
  step (just (found (_ , _ , c′ , s′) m κ , K , ox)) (just (found (_ , _ , c″ , s″) m′ κ′ , K′ , o′)) (e , lx) ly okx oky sp with K′ <ᴷ K in lt
  ... | true  = ll-shift {c′ = c″} {s″} {m′} {κ′} {K′} {o′} ly (lmap v {X = OK (rows ρ s) (retag (cutT l) (just (found (_ , _ , c′ , s′) m κ , K , ox)))} {Y = ∀ P → Tight (Lanes (rowsL ρ post)) P K′ o′ → After P (rows ρ s)} (λ bx P tg → past-strict {u = rows ρ s} {P} {K′} {K} (tight-⊑ tg) lt (λ {q} {e} r → Bd.from bx {q} {e} r)) okx)
  ... | false = x-wins {c′ = c′} {s′} {m} {κ} {K} ox e lx (lzip v {X = OKL (rowsL ρ post) (just (found (_ , _ , c″ , s″) m′ κ′ , K′ , o′))} {Z = ∀ P → Tight (rows ρ s) P K ox → Each (After P) (rowsL ρ post)} (λ bl (sp : Spread (rows ρ s ∷ rowsL ρ post)) P tg → each-past (rowsL ρ post) tg (proj₁ sp) (from-weak (rowsL ρ post) (⊑i lt) (proj₁ bl))) oky sp)

------------------------------------------------------------------------
-- A merge: the outer against the lanes

module Race {R Γ A B} (v : Bool) (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (ls : List (St Γ B)) where

  ρ : DenEnv Γ
  ρ = env c

  FR : EmissionSet B
  FR = Flat.JoinT (λ x → pendRows ρ (f x)) (rows ρ o) d (rowsL ρ ls)

  lane-occ : ∀ {Q} (o′ o″ : Out B) → (∀ {b} → Fits o′ (out b) → Fits o″ (out b)) → Occ (Lanes (rowsL ρ ls)) Q o′ → Occ FR Q o″
  lane-occ o′ o″ fo oc = occ-bind oc go
    where
      go : ∀ {Q e} → Lanes (rowsL ρ ls) Q e → Fits o′ e → Occ FR Q o″
      go {e = out b} x fe = hit (Flat.run x tt) (fo fe)
      go {e = skip}  x _  = hit (Flat.run x tt) tt
      go {e = pin _} x _  = hit (Flat.run x tt) tt
      go {e = end}   x _  = occ λ k → k (Flat.rpass x (λ ()) λ dn → k (Flat.rend x (λ ()) dn) tt) tt

  outer-still : ∀ {Q} → Occ (rows ρ o) Q still → Occ FR Q still
  outer-still oc = occ-bind oc go
    where
      go : ∀ {Q e} → rows ρ o Q e → Fits still e → Occ FR Q still
      go {e = out _} r ()
      go {e = skip}  r _ = hit (Flat.step r) tt
      go {e = pin _} r _ = hit (Flat.opin r) tt
      go {e = end}   r _ = occ λ k → k (Flat.opass r λ dn → k (Flat.oend r dn) tt) tt

  lane-tight : ∀ {P k} (o′ : Out B) → Tight (Lanes (rowsL ρ ls)) P k o′ → Tight FR P (proj₁ (laneT {A = A} d n [] k o′)) (proj₂ (laneT {A = A} d n [] k o′))
  lane-tight still          tg = tight-occ (lane-occ still still λ ()) tg
  lane-tight (shows (nx b)) tg = tight-occ (lane-occ (shows (nx b)) (shows (nx b)) λ fe → fe) tg
  lane-tight (shows cp)     tg = tight-occ (lane-occ (shows cp) _ λ ()) tg

  outer-tight : ∀ {P h} (ox : Out A) → Tight (rows ρ o) P h ox → (∀ {e} → ox ≡ shows e → Σ Pos λ q → h ≡ at q × rows ρ o q (toEv e))
              → Tight FR P (proj₁ (outerT {B = B} n [] h ox)) (proj₂ (outerT {B = B} n [] h ox))
  outer-tight still tg sh = tight-occ outer-still tg
  outer-tight (shows (nx x)) tg sh with sh refl
  ... | q , refl , r = tie (q ++ [ ix 0 ]) refl (⊑-trans (tight-⊑ tg) (ext-⊑ q [ ix 0 ])) (hit (Flat.val r) tt)
  outer-tight (shows cp) tg sh with sh refl
  ... | q , refl , r = tie q refl (tight-⊑ tg) (occ λ k → k (Flat.opass r λ dn → k (Flat.oend r dn) tt) tt)

  outer-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ h} (ox : Out A) (e : Ext c′ (inOuter (mergeᶠ nothing) f d n [] ls c))
             → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × Tight (rows ρ o) P h ox)
             → Live v (Bd (rows ρ o) κ h ox)
             → Live v (∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls))
             → Leads v c FR (just (found (Γ′ , A′ , c′ , s′) m κ , outerT n [] h ox))
  outer-wins ox e lx b al = eOuter e , lzip3 v go lx b al
    where
      go : _ → _ → _ → _
      go lx b al cl P oa = let r = lx cl P oa in (al P (tight-⊑ (proj₂ r)) , proj₁ r) , outer-tight ox (proj₂ r) (Bd.shown b)

  lane-wins : ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ k} (o′ : Out B) pre₁ post₁ (e : Ext c′ (inLanes (mergeᶠ nothing) f d n [] o pre₁ post₁ c))
            → Live v (closed c′ ≡ false → ∀ P → OfAt s′ m P → LeadE e P × (⊤ → Each (After P) (rowsL ρ pre₁)) × Each (After P) (rowsL ρ post₁) × Tight (Lanes (rowsL ρ ls)) P k o′)
            → Live v (∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o))
            → Leads v c FR (just (found (Γ′ , A′ , c′ , s′) m κ , laneT {A = A} d n [] k o′))
  lane-wins o′ pre₁ post₁ e ly ao = eLanes e , lzip v go ly ao
    where
      go : _ → _ → _
      go ly ao cl P oa = let r = ly cl P oa ; tg = proj₂ (proj₂ (proj₂ r)) in
        (ao P tg , proj₁ (proj₂ r) tt , proj₁ (proj₂ (proj₂ r)) , proj₁ r) , lane-tight o′ tg

  race-leads : (x : Maybe (Cand R A)) (y : Maybe (Cand R B))
             → Leads v (inOuter (mergeᶠ nothing) f d n [] ls c) (rows ρ o) x → LL v c f d n o [] ls y
             → Live v (OK (rows ρ o) x) → Live v (OKL (rowsL ρ ls) y) → Live v (Parts (rows ρ o) (rowsL ρ ls))
             → Leads v c FR (raceT d n [] x y)
  race-leads nothing nothing _ _ _ _ _ = tt₁
  race-leads nothing (just (found (_ , _ , c′ , s′) m κ , k , o′)) _ (pre₁ , post₁ , e , ly) okx _ _ =
    lane-wins {c′ = c′} {s′} {m} {κ} {k} o′ pre₁ post₁ e ly (lmap v {X = OK {R} (rows ρ o) nothing} {Y = ∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o)} (λ em P _ {q} {e} r → ⊥-elim (em {q} {e} r)) okx)
  race-leads (just (found (_ , _ , c′ , s′) m κ , h , ox)) nothing (e , lx) _ okx oky _ =
    outer-wins {c′ = c′} {s′} {m} {κ} {h} ox e lx okx (lmap v {X = OKL {R} (rowsL ρ ls) nothing} {Y = ∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls)} (λ em P _ → each-empty {P = P} (rowsL ρ ls) em) oky)
  race-leads (just (found (_ , _ , c′ , s′) m κ , h , ox)) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′)) (e , lx) (pre₁ , post₁ , e′ , ly) okx oky pa
    with h <ᴷ k in lt
  ... | true  = outer-wins {c′ = c′} {s′} {m} {κ} {h} ox e lx okx (lmap v {X = OKL (rowsL ρ ls) (just (found (_ , _ , c″ , s″) m′ κ′ , k , o′))} {Y = ∀ P → at P ⊑ h → Each (After P) (rowsL ρ ls)} (λ bl P ph → each-strict (rowsL ρ ls) ph lt (proj₁ bl)) oky)
  ... | false = lane-wins {c′ = c″} {s″} {m′} {κ′} {k} o′ pre₁ post₁ e′ ly
                  (lzip v {X = OK (rows ρ o) (just (found (_ , _ , c′ , s′) m κ , h , ox))} {Z = ∀ P → Tight (Lanes (rowsL ρ ls)) P k o′ → After P (rows ρ o)} (λ b (pa : Parts (rows ρ o) (rowsL ρ ls)) P tg → past-tie {u = rows ρ o} tg (λ {q} {e} r → ⊑-trans (⊑i lt) (Bd.from b {q} {e} r))
                                                  (λ {q} {e} {e′} x r → proj₁ pa {q} {e′} {e} r x)) okx pa)

------------------------------------------------------------------------
-- Every node

of-out : ∀ {R Γ A} (c : Ctx R Γ A) {i p x xs} → closed c ≡ false → outOf c (ofS i p (x ∷ xs)) ofM ≡ shows (nx x)
of-out c cl with closed c
of-out c () | true
of-out c cl | false = refl

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
own-lead v c (scanS _ _ _)        ()
own-lead v c (coldS _ _)          ()
own-lead v c (takeS _ _ _ _)      ()
own-lead v c (connS _ _ _)        ()
own-lead v c (joinS _ _ _ _)      ()

mutual
  seek-lead : ∀ {R Γ A} v (c : Ctx R Γ A) (s : St Γ A) → G (env c) v s → Leads v c (rows (env c) s) (seek c s)
  seek-lead v c s g = first-leads (ownBest c s (own s)) (kids c s) (own-lead v c s g) (kids-lead v c s g)

  kids-lead : ∀ {R Γ A} v (c : Ctx R Γ A) (s : St Γ A) → G (env c) v s → Leads v c (rows (env c) s) (kids c s)
  kids-lead v c (mapS f s)       g = map-leads v f (seek (inMap f c) s) (seek-lead v (inMap f c) s g)
  kids-lead v c (cutS true a s)  g = cut-on v (seek (inCut true a c) s) (seek-lead (v Data.Bool.∧ true) (inCut true a c) s g)
  kids-lead v c (cutS false a s) g = cut-off v (seek (inCut false a c) s) (seek-lead (v Data.Bool.∧ false) (inCut false a c) s g)
  kids-lead true c (flatS (mergeᶠ nothing) f d n q o ls) m with MergeG.fresh m
  ... | refl =
    leads-trunc true (raceT d n [] (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls))
      (join-ok c f d n o ls m)
    (Race.race-leads true c f d n o ls
      (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
      (seek-lead true (inOuter (mergeᶠ nothing) f d n [] ls c) o outer)
      (lanes-lead true c f d n o [] ls lanesG (proj₂ (rooted-parts rooted)))
      (seek-ok (inOuter (mergeᶠ nothing) f d n [] ls c) o outer)
      (lanes-ok c f d n o [] ls lanesG)
      (rooted-parts rooted))
    where open MergeG m
  kids-lead false c (flatS (mergeᶠ nothing) f d n q o ls) m with MergeG.fresh m
  ... | refl =
    leads-trunc false (raceT d n [] (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)) tt
    (Race.race-leads false c f d n o ls
      (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
      (seek-lead false (inOuter (mergeᶠ nothing) f d n [] ls c) o (MergeG.outer m))
      (lanes-lead false c f d n o [] ls (MergeG.lanesG m) tt) tt tt tt)
  kids-lead v c (ofS _ _ _)      _ = tt₁
  kids-lead v c doneS            _ = tt₁
  kids-lead v c (pend _ _)         _ = tt₁
  kids-lead v c (flatS (mergeᶠ (just _)) _ _ _ _ _ _) ()
  kids-lead v c (flatS switchᶠ _ _ _ _ _ _)           ()
  kids-lead v c (flatS exhaustᶠ _ _ _ _ _ _)          ()
  kids-lead v c (lnS _ _)        ()
  kids-lead v c (scanS _ _ _)    ()
  kids-lead v c (coldS _ _)      ()
  kids-lead v c (takeS _ _ _ _)  ()
  kids-lead v c (connS _ _ _)    ()
  kids-lead v c (joinS _ _ _ _)  ()

  seek-ln-lead : ∀ {R Γ A} v (c : Ctx R Γ A) (s : St Γ A) → GLn (env c) v s → Leads v c (rows (env c) s) (seek c s)
  seek-ln-lead v c (lnS true (cutS .true a s₀)) (refl , g₀ , _) = ln-leads (seek (inLn true c) (cutS true a s₀)) (seek-lead v (inLn true c) (cutS true a s₀) g₀)
  seek-ln-lead v c (lnS false (cutS .false a s₀)) (refl , g₀ , _) = ln-leads (seek (inLn false c) (cutS false a s₀)) (seek-lead v (inLn false c) (cutS false a s₀) g₀)
  seek-ln-lead v c (lnS _ (pend _ _)) ()
  seek-ln-lead v c (lnS _ (coldS _ _)) ()
  seek-ln-lead v c (lnS _ (ofS _ _ _)) ()
  seek-ln-lead v c (lnS _ doneS) ()
  seek-ln-lead v c (lnS _ (mapS _ _)) ()
  seek-ln-lead v c (lnS _ (scanS _ _ _)) ()
  seek-ln-lead v c (lnS _ (lnS _ _)) ()
  seek-ln-lead v c (lnS _ (takeS _ _ _ _)) ()
  seek-ln-lead v c (lnS _ (flatS _ _ _ _ _ _ _)) ()
  seek-ln-lead v c (lnS _ (connS _ _ _)) ()
  seek-ln-lead v c (lnS _ (joinS _ _ _ _)) ()
  seek-ln-lead v c (pend _ _) ()
  seek-ln-lead v c (coldS _ _) ()
  seek-ln-lead v c (ofS _ _ _) ()
  seek-ln-lead v c doneS ()
  seek-ln-lead v c (mapS _ _) ()
  seek-ln-lead v c (scanS _ _ _) ()
  seek-ln-lead v c (cutS _ _ _) ()
  seek-ln-lead v c (takeS _ _ _ _) ()
  seek-ln-lead v c (flatS _ _ _ _ _ _ _) ()
  seek-ln-lead v c (connS _ _ _) ()
  seek-ln-lead v c (joinS _ _ _ _) ()

  lanes-lead : ∀ {R Γ A B} v (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre (ls : List (St Γ B)) → GL (env c) v ls → Live v (Spread (rowsL (env c) ls))
             → LL v c f d n o pre ls (lanes c (mergeᶠ nothing) f d n [] o pre ls)
  lanes-lead v c f d n o pre []         _         _  = tt₁
  lanes-lead false c f d n o pre (lnS l (cutS .l a s₀) ∷ post) (gs@(refl , _) , gp) sp =
    Step.step false c f d n o pre post l a s₀
      (seek (inLanes (mergeᶠ nothing) f d n [] o pre post c) (lnS l (cutS l a s₀))) (lanes c (mergeᶠ nothing) f d n [] o (lnS l (cutS l a s₀) ∷ pre) post)
      (seek-ln-lead false (inLanes (mergeᶠ nothing) f d n [] o pre post c) (lnS l (cutS l a s₀)) gs)
      (lanes-lead false c f d n o (lnS l (cutS l a s₀) ∷ pre) post gp tt) tt tt tt
  lanes-lead true c f d n o pre (lnS l (cutS .l a s₀) ∷ post) (gs@(refl , _) , gp) sp =
    Step.step true c f d n o pre post l a s₀
      (seek (inLanes (mergeᶠ nothing) f d n [] o pre post c) (lnS l (cutS l a s₀))) (lanes c (mergeᶠ nothing) f d n [] o (lnS l (cutS l a s₀) ∷ pre) post)
      (seek-ln-lead true (inLanes (mergeᶠ nothing) f d n [] o pre post c) (lnS l (cutS l a s₀)) gs)
      (lanes-lead true c f d n o (lnS l (cutS l a s₀) ∷ pre) post gp (proj₂ sp))
      (lane-ok (lnS l (cutS l a s₀)) _ (seek-ln (inLanes (mergeᶠ nothing) f d n [] o pre post c) (lnS l (cutS l a s₀)) gs))
      (lanes-ok c f d n o (lnS l (cutS l a s₀) ∷ pre) post gp)
      sp
  lanes-lead v c f d n o pre ((lnS _ (pend _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (coldS _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (ofS _ _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ doneS) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (mapS _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (scanS _ _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (lnS _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (takeS _ _ _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (flatS _ _ _ _ _ _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (connS _ _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((lnS _ (joinS _ _ _ _)) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((pend _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((coldS _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((ofS _ _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre (doneS ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((mapS _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((scanS _ _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((cutS _ _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((takeS _ _ _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((flatS _ _ _ _ _ _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((connS _ _ _) ∷ post) (() , _) sp
  lanes-lead v c f d n o pre ((joinS _ _ _ _) ∷ post) (() , _) sp

-- What the search finds at an of, every merge above it led.
lead-found : ∀ {R Γ A} {t : St [] R} {c : Ctx R Γ A} {s : St Γ A} {m κ P} → closed c ≡ false → OfAt s m P → Good [] t
           → search top t ≡ just (found (Γ , A , c , s) m κ) → LeadC c P
lead-found {R} {Γ} {A} {t} {c} {s} {m} {κ} {P} cl oa g fd = go (seek top t) (seek-lead true top t g) fd
  where
    go : (y : Maybe (Cand R R)) → Leads true top (rows [] t) y → mapᴹ proj₁ y ≡ just (found (Γ , A , c , s) m κ) → LeadC c P
    go (just (found (_ , _ , c′ , s′) m′ κ′ , K , o)) (e , l) refl = lead-ext e (proj₁ (l cl P oa)) tt
