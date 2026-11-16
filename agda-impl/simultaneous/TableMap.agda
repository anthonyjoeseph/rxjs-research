{-# OPTIONS --guardedness #-}

-- A ROW-WISE MAP OF EVENTS CARRIES A SUBTERM'S RECORD (`ev-tab`): each
-- side's tables mapped row by row, positions and constructors kept, so
-- the map, the late placement and every lifting fact are the child's.
-- Agreement crosses the map forward row by row, and back through the
-- child's coherence: a mapped table keeps its child's shape.  `map`'s
-- case (`map-tab`) matches a plain value with the elaborated one carrying
-- it, mapped alike.
module simultaneous.TableMap where

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind; mapRow; mapRows)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown)
open import simultaneous.TableCorr using (TR; M; Corr; Rel; module Rel; ev; Sh; ag-≃)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; mapIE)

------------------------------------------------------------------------
-- A table mapped row by row

Mapped : ∀ {A B : Set} → (A → B) → Maybe (Tb.Listed A) → Maybe (Tb.Listed B)
Mapped f m = bind m λ l → just (mapRows f l)

mapRow-ev : ∀ {A B : Set} (f : A → B) k (e : Ev A) → mapRow f (k , e) ≡ (k , ev f e)
mapRow-ev f k (out a) = refl
mapRow-ev f k skip    = refl
mapRow-ev f k end     = refl
mapRow-ev f k (pin r) = refl

tr-map→ : ∀ {A B : Set} (f : A → B) (m : Maybe (Tb.Listed A)) {k e} → TR (Mapped f m) k e → Σ (Ev A) λ e₀ → TR m k e₀ × e ≡ ev f e₀
tr-map→ f nothing (_ , () , _)
tr-map→ f (just L) (_ , refl , r) with ∈-map⁻ (mapRow f) r
... | (k₀ , e₀) , r₀ , eq =
  let eq′ = trans eq (mapRow-ev f k₀ e₀) in
  e₀ , subst (λ z → TR (just L) z e₀) (sym (cong proj₁ eq′)) (L , refl , r₀) , cong proj₂ eq′

tr-map← : ∀ {A B : Set} (f : A → B) (m : Maybe (Tb.Listed A)) {k e} → TR m k e → TR (Mapped f m) k (ev f e)
tr-map← f m {k} {e} (L , refl , r) = mapRows f L , refl , subst (_∈ rows (mapRows f L)) (mapRow-ev f k e) (∈-map⁺ (mapRow f) r)

ev-ev : ∀ {A B : Set} (f : A → B) (e : Ev A) → ev (λ _ → tt) (ev f e) ≡ ev (λ _ → tt) e
ev-ev f (out a) = refl
ev-ev f skip    = refl
ev-ev f end     = refl
ev-ev f (pin r) = refl

-- A mapped table keeps its child's shape.
sh-map→ : ∀ {A B : Set} (f : A → B) (m : Maybe (Tb.Listed A)) {k e} → Sh (TR (Mapped f m)) k e → Sh (TR m) k e
sh-map→ f m (e₁ , x , refl) with tr-map→ f m x
... | e₀ , x₀ , refl = e₀ , x₀ , ev-ev f e₀

sh-map← : ∀ {A B : Set} (f : A → B) (m : Maybe (Tb.Listed A)) {k e} → Sh (TR m) k e → Sh (TR (Mapped f m)) k e
sh-map← f m (e₀ , x , refl) = ev f e₀ , tr-map← f m x , sym (ev-ev f e₀)

-- Two runs agreeing agree in shape.
sh-of : ∀ {X : Set} {a b : EmissionSet X} {q} → AgreeTo q a b → AgreeTo q (Sh a) (Sh b)
sh-of ag = ⟨ (λ yq → (λ { (e₀ , x , eq) → e₀ , proj₁ (upto ag yq) x , eq }) , (λ { (e₀ , x , eq) → e₀ , proj₂ (upto ag yq) x , eq })) ⟩

-- Two tables agreeing, mapped, agree.
ag-map : ∀ {A B : Set} (f : A → B) {m m′ : Maybe (Tb.Listed A)} {q} → AgreeTo q (TR m) (TR m′) → AgreeTo q (TR (Mapped f m)) (TR (Mapped f m′))
ag-map f {m} {m′} ag = ⟨ (λ {y} yq → mv m m′ (λ {e₀} → proj₁ (upto ag {y} {e₀} yq)) , mv m′ m (λ {e₀} → proj₂ (upto ag {y} {e₀} yq))) ⟩
  where
    mv : ∀ n n′ {y e} → (∀ {e₀} → TR n y e₀ → TR n′ y e₀) → TR (Mapped f n) y e → TR (Mapped f n′) y e
    mv n n′ h x with tr-map→ f n x
    ... | e₀ , x₀ , refl = tr-map← f n′ (h x₀)

un→ : ∀ {A B : Set} (f : A → B) (e : Ev A) → Unpinned (ev f e) → Unpinned e
un→ f (out a) _ = tt
un→ f skip    _ = tt
un→ f end     _ = tt
un→ f (pin r) ()

un← : ∀ {A B : Set} (f : A → B) (e : Ev A) → Unpinned e → Unpinned (ev f e)
un← f (out a) _ = tt
un← f skip    _ = tt
un← f end     _ = tt
un← f (pin r) ()

------------------------------------------------------------------------
-- The record, mapped

module EvTab {A B : Set} (f : A → B) (g : IE A → IE B)
  (lift : ∀ {e e′} → M e e′ → M (ev f e) (ev g e′))
  (back : ∀ e′ → Shown (One valuesOf) (ev g e′) → Shown (One valuesOf) e′)
  {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {s s* : Pos} (R : Rel P Q s s*) where

  module R = Rel R

  P′ : ℕ → Maybe (Tb.Listed B)
  P′ N = Mapped f (P N)

  Q′ : ℕ → Maybe (Tb.Listed (IE B))
  Q′ N = Mapped g (Q N)

  -- Agreement back through the map, by the child's coherence.
  ag← : ∀ {N N′ k} → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → AgreeTo k (TR (P N)) (TR (P N′))
  ag← {N} {N′} ag = R.coh (ag-≃ (sh-map→ f (P N)) (sh-map← f (P N)) (sh-map→ f (P N′)) (sh-map← f (P N′)) (sh-of ag))

  ag←* : ∀ {N N′ k} → AgreeTo k (TR (Q′ N)) (TR (Q′ N′)) → AgreeTo k (TR (Q N)) (TR (Q N′))
  ag←* {N} {N′} ag = R.coh* (ag-≃ (sh-map→ g (Q N)) (sh-map← g (Q N)) (sh-map→ g (Q N′)) (sh-map← g (Q N′)) (sh-of ag))

  back-row : ∀ N {k e} → TR (P′ N) k e → Unpinned e → Σ (Ev A) λ e₀ → TR (P N) k e₀ × Unpinned e₀
  back-row N x un with tr-map→ f (P N) x
  ... | e₀ , x₀ , refl = e₀ , x₀ , un→ f e₀ un

  Img′ : ℕ → Pos → Ev B → Set
  Img′ N k e = Σ (Ev (IE B)) λ e′ → TR (Q′ N) (R.φ N k) e′ × M e e′

  img→ : ∀ {N k e} → Corr.Imaged (R.corr N) k e → Img′ N k (ev f e)
  img→ {N} (e′ , y , mt) = ev g e′ , tr-map← g (Q N) y , lift mt

  Homed′ : ℕ → Pos → Set
  Homed′ N k = instantOf k ≡ instantOf s
             ⊎ Σ Pos λ k₀ → Σ (Ev B) λ e₀ → TR (P′ N) k₀ e₀ × Unpinned e₀ × Img′ N k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  homed→ : ∀ {N k} → Corr.Homed (R.corr N) k → Homed′ N k
  homed→ (inj₁ e) = inj₁ e
  homed→ {N} (inj₂ (k₀ , e₀ , x , un , im , lt , ie)) = inj₂ (k₀ , ev f e₀ , tr-map← f (P N) x , un← f e₀ un , img→ im , lt , ie)

  PutAt′ : ℕ → Pos → Set
  PutAt′ N k = (Σ Pos λ l → Σ (Ev (IE B)) λ e′ → TR (Q′ N) l e′ × R.Put N k l) × Homed′ N k

  put→ : ∀ {N k} → Corr.PutAt (R.corr N) k → PutAt′ N k
  put→ {N} ((l , e′ , y , pl) , h) = (l , ev g e′ , tr-map← g (Q N) y , pl) , homed→ h

  Leads′ : ℕ → Pos → Set
  Leads′ N k = ∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  leads→ : ∀ {N k} → Corr.Leads (R.corr N) k → Leads′ N k
  leads→ {N} ld x′ un′ ie′ with tr-map→ f (P N) x′
  ... | e₀ , x₀ , refl = ld x₀ (un→ f e₀ un′) ie′

  leads← : ∀ {N k} → Leads′ N k → Corr.Leads (R.corr N) k
  leads← {N} ld {k′} {e′} x′ un′ ie′ = ld (tr-map← f (P N) x′) (un← f e′ un′) ie′

  leadsOr : ∀ {N k m} → R.φ N k ≼ m ⊎ Corr.Leads (R.corr N) k → R.φ N k ≼ m ⊎ Leads′ N k
  leadsOr (inj₁ le) = inj₁ le
  leadsOr (inj₂ ld) = inj₂ (leads→ ld)

  row→′ : ∀ N {k e} → TR (P′ N) k e → Unpinned e → Img′ N k e ⊎ (e ≡ skip × PutAt′ N k)
  row→′ N x un with tr-map→ f (P N) x
  ... | e₀ , x₀ , refl with Corr.row→ (R.corr N) x₀ (un→ f e₀ un)
  ...   | inj₁ im          = inj₁ (img→ im)
  ...   | inj₂ (refl , pa) = inj₂ (refl , put→ pa)

  pin→′ : ∀ N {k p} → TR (P′ N) k (pin p) → PutAt′ N k
  pin→′ N x with tr-map→ f (P N) x
  ... | pin r , x₀ , refl = put→ (Corr.pin→ (R.corr N) x₀)
  ... | out _ , _ , ()
  ... | skip  , _ , ()
  ... | end   , _ , ()

  shown←′ : ∀ N {l e′} → TR (Q′ N) l e′ → Shown (One valuesOf) e′
          → Σ Pos λ k → Σ (Ev B) λ e → l ≡ R.φ N k × TR (P′ N) k e × Unpinned e × M e e′
  shown←′ N y sh with tr-map→ g (Q N) y
  ... | e₀′ , y₀ , refl with Corr.shown← (R.corr N) y₀ (back e₀′ sh)
  ...   | k , e , eq , x , un , mt = k , ev f e , eq , tr-map← f (P N) x , un← f e un , lift mt

  place′ : ∀ N {m e′} → TR (Q′ N) m e′
         → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev B) λ e → TR (P′ N) k e × Unpinned e × Img′ N k e × (R.φ N k ≼ m ⊎ Leads′ N k) × instantOf (R.φ N k) ≡ instantOf m
  place′ N {m} y with tr-map→ g (Q N) y
  ... | e₀′ , y₀ , refl with Corr.place (R.corr N) y₀
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ (k , e , x , un , im , le , ie) = inj₂ (k , ev f e , tr-map← f (P N) x , un← f e un , img→ im , leadsOr {m = m} le , ie)

  corr′ : ∀ N → Corr s s* (R.φ N) (R.Put N) (TR (P′ N)) (TR (Q′ N))
  corr′ N = record
    { row→ = row→′ N ; pin→ = pin→′ N ; shown← = shown←′ N ; place = place′ N
    ; mono = λ x x′ un un′ lt → let (_ , x₀ , u₀) = back-row N x un ; (_ , x₁ , u₁) = back-row N x′ un′ in Corr.mono (R.corr N) x₀ x₁ u₀ u₁ lt
    ; inst = λ x x′ un un′ → let (_ , x₀ , u₀) = back-row N x un ; (_ , x₁ , u₁) = back-row N x′ un′ in Corr.inst (R.corr N) x₀ x₁ u₀ u₁
    ; home = λ x un → let (_ , x₀ , u₀) = back-row N x un in Corr.home (R.corr N) x₀ u₀ }

  rel′ : Rel P′ Q′ s s*
  rel′ = record
    { φ = R.φ ; Put = R.Put ; corr = corr′
    ; φ-agree = λ ag → R.φ-agree (ag← ag)
    ; bk = R.bk
    ; in-bk = λ {N} x un → let (_ , x₀ , u₀) = back-row N x un in R.in-bk x₀ u₀
    ; pb-few = R.pb-few
    ; elab-causal = λ {N} le x un ag → let (_ , x₀ , u₀) = back-row N x un in ag-map g (R.elab-causal le x₀ u₀ (ag← ag))
    ; stable← = λ {N} le x un ag* → let (_ , x₀ , u₀) = back-row N x un in ag-map f (R.stable← le x₀ u₀ (ag←* ag*))
    ; stable-put = λ {N} le ag y pl → ag-map g (R.stable-put le (ag← ag) (proj₁ (proj₂ (tr-map→ g (Q N) y))) pl)
    ; stable-lead = λ {N} le x un ld ie ag* → let (_ , x₀ , u₀) = back-row N x un in
        ag-map g (R.stable-lead le x₀ u₀ (leads← ld) ie (ag←* ag*))
    ; elab-all = λ {N} {N′} le all y → let (_ , y₀ , eq) = tr-map→ g (Q N′) y in
        subst (TR (Q′ N) _) (sym eq) (tr-map← g (Q N) (R.elab-all le (λ q → ag← (all q)) y₀))
    ; coh = λ {N} {N′} ag → ag-map f (R.coh (ag-≃ (sh-map→ f (P N)) (sh-map← f (P N)) (sh-map→ f (P N′)) (sh-map← f (P N′)) ag))
    ; coh* = λ {N} {N′} ag → ag-map g (R.coh* (ag-≃ (sh-map→ g (Q N)) (sh-map← g (Q N)) (sh-map→ g (Q N′)) (sh-map← g (Q N′)) ag)) }

ev-tab : ∀ {A B : Set} (f : A → B) (g : IE A → IE B)
       → (∀ {e e′} → M e e′ → M (ev f e) (ev g e′))
       → (∀ e′ → Shown (One valuesOf) (ev g e′) → Shown (One valuesOf) e′)
       → ∀ {P Q s s*} → Rel P Q s s* → Rel (λ N → Mapped f (P N)) (λ N → Mapped g (Q N)) s s*
ev-tab f g lift back R = EvTab.rel′ f g lift back R

------------------------------------------------------------------------
-- `map`

private
  vals-map : ∀ {A B : Set} (f : A → B) (x : IE A) {a} → valuesOf x ≡ a ∷ [] → valuesOf (mapIE f x) ≡ f a ∷ []
  vals-map f (instEmit (value b) n) refl = refl
  vals-map f (instEmit (mark m) n) ()

  shown-map : ∀ {A B : Set} (f : A → B) (e′ : Ev (IE A)) → Shown (One valuesOf) (ev (mapIE f) e′) → Shown (One valuesOf) e′
  shown-map f (out (instEmit (value a) n)) _ = a , refl
  shown-map f (out (instEmit (mark m) n)) (_ , ())
  shown-map f end _ = tt
  shown-map f skip ()
  shown-map f (pin r) ()

  m-map : ∀ {A B : Set} (f : A → B) {e : Ev A} {e′ : Ev (IE A)} → M e e′ → M (ev f e) (ev (mapIE f) e′)
  m-map f {out a} (c , _) with c tt
  ... | x , refl , rd = (λ _ → mapIE f x , refl , vals-map f x rd) , (λ n → ⊥-elim (n tt))
  m-map f {end} (c , _) with c tt
  ... | refl = (λ _ → refl) , (λ n → ⊥-elim (n tt))
  m-map f {skip} {e′} (_ , d) = (λ ()) , (λ _ sh → d (λ ()) (shown-map f e′ sh))
  m-map f {pin r} {e′} (_ , d) = (λ ()) , (λ _ sh → d (λ ()) (shown-map f e′ sh))

map-tab : ∀ {A B} (f : A → B) {P Q s s*} → Rel P Q s s*
        → Rel (λ N → bind (P N) λ l → just (mapRows f l)) (λ N → bind (Q N) λ l → just (mapRows (mapIE f) l)) s s*
map-tab f = ev-tab f (mapIE f) (m-map f) (shown-map f)
