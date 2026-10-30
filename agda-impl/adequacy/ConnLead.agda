{-# OPTIONS --guardedness #-}

-- A CONNECT'S SEARCH LEADS: whatever its source or its body finds, the
-- source winning only strictly before the body, keys the connect's rows,
-- and the part that lost lies past it.  The body's search leads under a
-- cap no later than the source's find, its binder past that cap.
module adequacy.ConnLead where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (ix; inside)
open import denotation.EmissionSet using (EmissionSet; module Connecting; _≺_; Proper)
open import denotation.Laws.Modulus using (upto; ≼-or-≻; ≺-irrefl; ≼-≺-≺; ≺-≼-≺; ≺→≼)
open import denotation.Laws using (ag-cons; hot-below)
open import operation.Key using (Key; at; _<ᴷ_)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; Cand; found; still; shift; seek; own; ownBest; sourceT; closed; connS; inSrc; inBody)
open import adequacy.Rows using (env; rows; Hot; ∅; _∪_; Closed)
open import adequacy.Causal using (rows-causal; env-refl)
open import adequacy.Bound using (_⊑_; ⊑i; ⊑-refl; ⊑-trans; <→⊑; ext-⊑; shift-⊑; Bd; From; Good; ⊑→≼; apart-before)
open import adequacy.Cap using (OKᶜ; EnvSingle; Air; bind-after; bind-past; meet; meet-ˡ; meet-ʳ; meet-hi; ext-<; ⊑-<; <-⊑; ≮; StillAt; still-at)
open import adequacy.Skip using (After)
open import adequacy.Leads using (Leads; Leadsᶜ; Beats; eSrc; eBody; OfAt; Occ; Tight; strict; tie; occ-bind; hit; tight-⊑; tight-occ;
  past-strict; aft; none-aft; lost-strict; exact; up)

open _⊑_
open Bd

------------------------------------------------------------------------
-- Keys

meet-glb : ∀ {K} a b → K ⊑ a → K ⊑ b → K ⊑ meet a b
meet-glb a b ka kb with a <ᴷ b
... | true  = ka
... | false = kb

-- A body's row is its connect's.
body-occ : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} {Q o} → Occ β Q o → Occ (Connecting.ConnT p σ β) Q o
body-occ oc = occ-bind oc (λ r fe → hit (Connecting.body r) fe)

-- A source's event raised as its connect reads it: strictly past.
raise-tight : ∀ {X B} {σ : EmissionSet X} {τ : EmissionSet B} {P h₀ o′} → Tight σ P h₀ o′ → Tight τ P (shift h₀) still
raise-tight {P = P} {h₀} (strict lt)      = strict (<-⊑ (at P) lt (shift-⊑ h₀))
raise-tight              (tie Q refl pq _) = strict (⊑-< (at (Q ++ [ ix 0 ])) pq (ext-< Q (ix 0)))

------------------------------------------------------------------------
-- The gaps

-- A BODY'S EVENT IS UNDER NO ROW ITS SOURCE STILL OWES: a body's events
-- lie under its own subscriptions or under source rows already fed to
-- its binder, never at or under one still to come.
postulate
  body-apart : ∀ {R Γ A X} (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) → EnvSingle (env c) → Good (env c) (connS k o b)
             → ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K o″} → seek (inBody k o c) b ≡ just (found (Γ′ , A′ , c′ , s′) m κ , K , o″)
             → closed c′ ≡ false → ∀ P → OfAt s′ m P → ∀ {q e} → rows (env c) o q e → ¬ T (inside q P)

-- A BODY'S FIND NO LATER THAN ITS SOURCE'S RAISED ONE: the source's
-- rows lie strictly past the body's event.
conn-body-src : ∀ {R Γ A X} (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) → EnvSingle (env c) → Good (env c) (connS k o b)
              → ∀ {Γ₁ A₁} {c₁ : Ctx R Γ₁ A₁} {s₁ m₁ κ₁ h₀ o′} → seek (inSrc k b c) o ≡ just (found (Γ₁ , A₁ , c₁ , s₁) m₁ κ₁ , h₀ , o′)
              → Bd (rows (env c) o) κ₁ h₀ o′
              → ∀ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K o″} → seek (inBody k o c) b ≡ just (found (Γ′ , A′ , c′ , s′) m κ , K , o″)
              → K ⊑ (shift h₀)
              → closed c′ ≡ false → ∀ P → OfAt s′ m P → Tight (rows (Hot (rows (env c) o) k ∷ᴬ env c) b) P K o″
              → After P (rows (env c) o)
conn-body-src c k o b es g xe bσ ye Ksh cl P oa tg {q} x =
  apart-before _ (⊑-trans (tight-⊑ tg) Ksh) (from bσ x) (body-apart c k o b es g ye cl P oa x)

------------------------------------------------------------------------
-- The body, under a cap no later

BodyL : ∀ {R Γ A X} → Key → (c : Ctx R Γ A) → CS → St Γ X → St (X ∷ Γ) A → Maybe (Cand R A) → Set₁
BodyL C c k o b y = ∀ C₂ → C₂ ⊑ C → (¬ T (CS.closed k) → Air C₂ (Hot (rows (env c) o) k ∷ᴬ env c) (here refl))
                  → Leadsᶜ C₂ true (inBody k o c) (rows (Hot (rows (env c) o) k ∷ᴬ env c) b) y × OKᶜ C₂ (rows (Hot (rows (env c) o) k ∷ᴬ env c) b) y

-- The body's find, the source's rows past its event.
body-win : ∀ {R Γ A X} C (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) C₂ {Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ K o″}
         → C₂ ⊑ C → (¬ T (CS.closed k) → Air C₂ (Hot (rows (env c) o) k ∷ᴬ env c) (here refl)) → K ⊑ C₂
         → BodyL C c k o b (just (found (Γ′ , A′ , c′ , s′) m κ , K , o″))
         → (closed c′ ≡ false → ∀ P → OfAt s′ m P → Tight (rows (Hot (rows (env c) o) k ∷ᴬ env c) b) P K o″ → After P (rows (env c) o))
         → Leads true c (rows (env c) (connS k o b)) (just (found (Γ′ , A′ , c′ , s′) m κ , K , o″))
body-win C c k o b C₂ c₂ air kc bl aσ =
  eBody (proj₁ ly) , λ cl P oa → let (le , tg) = proj₂ ly cl P oa in (aσ cl P oa tg , le) , tight-occ body-occ tg
  where
    ly = proj₁ (bl C₂ c₂ air) (un kc)

-- A BODY UNFED IS NO EARLIER THAN FED, UP TO ITS SOURCE'S FIRST ROW: a
-- binder row heard at `x` lands under `x`, so with no source row before
-- `P` the body's rows up to `P` are the same with its source or without.
unfed-after : ∀ {Γ X A} (ρ : _) k (o : St Γ X) (b : St (X ∷ Γ) A) → ∀ P
            → From (at P) (rows ρ o) → After P (rows (Hot (rows ρ o) k ∷ᴬ ρ) b) → After P (rows (Hot ∅ k ∷ᴬ ρ) b)
unfed-after ρ k o b P fr aft {q} x with ≼-or-≻ q P
... | inj₂ Pq = Pq
... | inj₁ qP = aft (proj₂ (upto (rows-causal (ag-cons (hot-below fed unfed) (env-refl ρ)) b) {q} qP) x)
  where
    fed : ∀ {y e} → y ≺ P → Proper (rows ρ o ∪ Closed k) y e → Proper (∅ ∪ Closed k) y e
    fed {y} yP (inj₁ s , _)  = ⊥-elim (≺-irrefl {P} (≼-≺-≺ {P} {y} {P} (⊑→≼ (fr s)) yP))
    fed     yP (inj₂ c , pr) = inj₂ c , λ { (inj₁ ()) ; (inj₂ c′) → pr (inj₂ c′) }
    unfed : ∀ {y e} → y ≺ P → Proper (∅ ∪ Closed k) y e → Proper (rows ρ o ∪ Closed k) y e
    unfed     yP (inj₁ () , _)
    unfed {y} yP (inj₂ c , pr) = inj₂ c , λ { {c′} (inj₁ s) → ≺→≼ {y} {c′} (≺-≼-≺ {y} {P} {c′} yP (⊑→≼ (fr s))) ; (inj₂ c′) → pr (inj₂ c′) }

-- The source's find raised, the body's rows unfed past its event.
src-win : ∀ {R Γ A X} C (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) → Good (env c) (connS k o b)
        → ∀ {Γ₁ A₁} {c₁ : Ctx R Γ₁ A₁} {s₁ m κ h₀ o′}
        → Leadsᶜ C true (inSrc k b c) (rows (env c) o) (just (found (Γ₁ , A₁ , c₁ , s₁) m κ , h₀ , o′))
        → OKᶜ C (rows (env c) o) (just (found (Γ₁ , A₁ , c₁ , s₁) m κ , h₀ , o′))
        → (C <ᴷ (shift h₀) ≡ false → ∀ P → at P ⊑ (shift h₀) → After P (rows (Hot (rows (env c) o) k ∷ᴬ env c) b))
        → Leadsᶜ C true c (rows (env c) (connS k o b)) (just (found (Γ₁ , A₁ , c₁ , s₁) m κ , (shift h₀) , still))
src-win C c k o b g {c₁ = c₁} {s₁} {m} {κ} {h₀} {o′} lx ox ab bf =
  eSrc (proj₁ lx′) , λ cl P oa →
    let (le , tg) = proj₂ lx′ cl P oa
        pk        = tight-⊑ tg
    in (unfed-after (env c) k o b P (λ r → ⊑-trans pk (from okx r)) (ab bf P (⊑-trans pk (shift-⊑ h₀))) , le)
       , raise-tight tg
  where
    bx  = un (up {h₀} {shift h₀} {C} (shift-⊑ h₀) bf)
    lx′ = lx bx
    okx = exact C (just (found (_ , _ , c₁ , s₁) m κ , h₀ , o′)) bx ox

-- An open source's binder past the cap, nothing found.
none-air : ∀ {R Γ X} {ρ : _} C k {σ : EmissionSet X} → OKᶜ {R} C σ nothing → ¬ T (CS.closed k) → Air {Γ = X ∷ Γ} C (Hot σ k ∷ᴬ ρ) (here refl)
none-air C k {σ} (inj₁ (_ , aσ)) nc = bind-after σ k C (λ a → C <ᴷ a ≡ true) (λ d e → <-⊑ C d e) aσ (λ {x} l _ c → <-⊑ C c (ext-⊑ x [ l ])) nc
none-air C k (inj₂ (() , _)) nc

-- An open source's binder past the earlier of the cap and its raised find.
src-air : ∀ {R Γ X} {ρ : _} C k {σ : EmissionSet X} {f h₀ o′} → OKᶜ {R} C σ (just (f , h₀ , o′)) → ¬ T (CS.closed k)
        → Air {Γ = X ∷ Γ} (meet C (shift h₀)) (Hot σ k ∷ᴬ ρ) (here refl)
src-air C k {σ} {h₀ = h₀} (inj₁ (_ , aσ)) nc =
  bind-after σ k (meet C h) (λ a → C <ᴷ a ≡ true) (λ d e → <-⊑ C d e) aσ (λ {x} l _ c → ⊑-< (at (x ++ [ l ])) (meet-ˡ C h) (<-⊑ C c (ext-⊑ x [ l ]))) nc
  where h = shift h₀
src-air C k {σ} {h₀ = h₀} (inj₂ (_ , bσ)) nc =
  bind-after σ k (meet C h) (h₀ ⊑_) ⊑-trans (from bσ) (λ {x} l lt d → ⊑-< (at (x ++ [ l ])) (meet-ʳ C h) (bind-past h₀ x l lt d)) nc
  where h = shift h₀

------------------------------------------------------------------------
-- The connect

-- Its source subscribed.
conn-free-lead : ∀ {R Γ A X} C (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) → EnvSingle (env c) → Good (env c) (connS k o b)
               → (x : Maybe (Cand R X)) (y : Maybe (Cand R A)) → seek (inSrc k b c) o ≡ x → seek (inBody k o c) b ≡ y
               → Leadsᶜ C true (inSrc k b c) (rows (env c) o) x → OKᶜ C (rows (env c) o) x → BodyL C c k o b y
               → Leadsᶜ C true c (rows (env c) (connS k o b)) (sourceT x y)
conn-free-lead C c k o b es g nothing nothing xe ye lx ox bl ()
conn-free-lead {R} C c k o b es g nothing (just (found (_ , _ , c′ , s′) m κ , K , o″)) xe ye lx ox bl bf =
  body-win C c k o b C {c′ = c′} {s′} {m} (⊑-refl C) (none-air {R = R} {ρ = env c} C k {σ = rows (env c) o} ox) (⊑i bf) bl (λ _ P _ tg → none-aft {R = R} {t = rows (env c) o} {C = C} (⊑i bf) ox P (tight-⊑ tg))
conn-free-lead {R} C c k o b es g (just (found f₁ m₁ κ₁ , h₀ , o′)) nothing xe ye lx ox bl =
  src-win C c k o b g {Γ₁ = proj₁ f₁} {proj₁ (proj₂ f₁)} {c₁ = proj₁ (proj₂ (proj₂ f₁))} {proj₂ (proj₂ (proj₂ f₁))} {m₁} {κ₁} {h₀} {o′} lx ox
    (λ bf P pk → none-aft {R = R} {t = rows (Hot (rows (env c) o) k ∷ᴬ env c) b} {C = meet C h} (meet-hi C h (⊑i bf))
                   (proj₂ (bl (meet C h) (meet-ˡ C h) (src-air {R = R} {ρ = env c} C k {σ = rows (env c) o} {f = found f₁ m₁ κ₁} {h₀ = h₀} {o′ = o′} ox))) P pk)
  where h = shift h₀
conn-free-lead {R} C c k o b es g (just (found f₁ m₁ κ₁ , h₀ , o′)) (just (found (_ , _ , c′ , s′) m κ , K , o″)) xe ye lx ox bl
  with (shift h₀) <ᴷ K in lt
... | true  =
  src-win C c k o b g {Γ₁ = proj₁ f₁} {proj₁ (proj₂ f₁)} {c₁ = proj₁ (proj₂ (proj₂ f₁))} {proj₂ (proj₂ (proj₂ f₁))} {m₁} {κ₁} {h₀} {o′} lx ox
    (λ bf P pk → lost-strict {R = R} {t = rows (Hot (rows (env c) o) k ∷ᴬ env c) b} {C = meet C (shift h₀)} {P = P} {K = K} {K′ = shift h₀} {g = found (_ , _ , c′ , s′) m κ} {o = o″}
                   pk (meet-hi C (shift h₀) (⊑i bf)) lt
                   (proj₂ (bl (meet C (shift h₀)) (meet-ˡ C _) (src-air {R = R} {ρ = env c} C k {σ = rows (env c) o} {f = found f₁ m₁ κ₁} {h₀ = h₀} {o′ = o′} ox))))
... | false = λ bf →
  body-win C c k o b (meet C h) {c′ = c′} {s′} {m} (meet-ˡ C h) (src-air {R = R} {ρ = env c} C k {σ = rows (env c) o} {f = found f₁ m₁ κ₁} {h₀ = h₀} {o′ = o′} ox) (meet-glb C h (⊑i bf) (≮ K h lt)) bl (aσ bf ox)
  where
    h = shift h₀
    aσ : C <ᴷ K ≡ false → OKᶜ C (rows (env c) o) (just (found f₁ m₁ κ₁ , h₀ , o′))
       → closed c′ ≡ false → ∀ P → OfAt s′ m P → Tight (rows (Hot (rows (env c) o) k ∷ᴬ env c) b) P K o″ → After P (rows (env c) o)
    aσ bf (inj₁ (_ , a))  cl P oa tg = aft {t = rows (env c) o} {C = C} (tight-⊑ tg) (⊑i bf) a
    aσ bf (inj₂ (_ , bσ)) cl P oa tg = conn-body-src c k o b es g xe bσ ye (≮ K h lt) cl P oa tg

-- Its body subscribing, its source owing nothing before the body's mark.
conn-held-lead : ∀ {R Γ A X} C (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) q → From (at q) (rows (env c) o)
               → (x y : Maybe (Cand R A)) → StillAt (at q) x → BodyL C c k o b y → Beats x y
               → Leadsᶜ C true c (rows (env c) (connS k o b)) y
conn-held-lead C c k o b q fσ x nothing _ _ _ ()
conn-held-lead C c k o b q fσ _ (just (found (_ , _ , c′ , s′) m κ , K , o″)) (still-at {h = h} kh hq) bl w bf =
  body-win C c k o b (meet C h) {c′ = c′} {s′} {m} (meet-ˡ C h) air (meet-glb C h (⊑i bf) (<→⊑ K h w)) bl
    (λ _ P _ tg → past-strict {u = rows (env c) o} {P} {K} {h} (tight-⊑ tg) w (λ r → ⊑-trans hq (fσ r)))
  where
    air : ¬ T (CS.closed k) → Air (meet C h) (Hot (rows (env c) o) k ∷ᴬ env c) (here refl)
    air nc = bind-after (rows (env c) o) k (meet C h) (at q ⊑_) ⊑-trans fσ
               (λ {x} l _ d → ⊑-< (at (x ++ [ l ])) (⊑-trans (meet-ʳ C h) (⊑-trans hq d)) (ext-< x l)) nc

-- Switched off: only the frames.
conn-off-lead : ∀ {R Γ A X} C (c : Ctx R Γ A) k (o : St Γ X) (b : St (X ∷ Γ) A) (x : Maybe (Cand R X)) (y : Maybe (Cand R A))
              → Leadsᶜ C false (inSrc k b c) (rows (env c) o) x → Leadsᶜ C false (inBody k o c) (rows (Hot (rows (env c) o) k ∷ᴬ env c) b) y
              → Leadsᶜ C false c (rows (env c) (connS k o b)) (sourceT x y)
conn-off-lead C c k o b nothing nothing lx ly ()
conn-off-lead C c k o b nothing (just (found (_ , _ , _ , _) _ _ , _ , _)) lx ly bf = eBody (proj₁ (ly bf)) , _
conn-off-lead C c k o b (just (found (_ , _ , _ , _) _ _ , h₀ , _)) nothing lx ly bf =
  eSrc (proj₁ (lx (un (up {h₀} {shift h₀} {C} (shift-⊑ h₀) bf)))) , _
conn-off-lead C c k o b (just (found (_ , _ , _ , _) _ _ , h₀ , _)) (just (found (_ , _ , _ , _) _ _ , K , _)) lx ly
  with (shift h₀) <ᴷ K
... | true  = λ bf → eSrc (proj₁ (lx (un (up {h₀} {shift h₀} {C} (shift-⊑ h₀) bf)))) , _
... | false = λ bf → eBody (proj₁ (ly bf)) , _
