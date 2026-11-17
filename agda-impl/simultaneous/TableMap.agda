{-# OPTIONS --guardedness #-}

-- A ROW-WISE MAP OF EVENTS CARRIES A SUBTERM'S RECORD (`ev-tab`): each
-- side's tables mapped row by row, positions and constructors kept, so
-- the map, the late placement and every lifting fact are the child's.
-- Agreement crosses the map forward row by row, and back through the
-- child's coherence: a mapped table keeps its child's shape.  `map`'s
-- case (`map-tab`) matches a plain value with the elaborated one carrying
-- it, mapped alike.
module simultaneous.TableMap where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind; mapRow; mapRows)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.TableCorr using (TR; M; Corr; Rel; module Rel; ev; Sh; ag-≃; coh-of; tr-few; got-bind)

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

-- A mapped row's constructor is its source row's.
ev-pin : ∀ {A B : Set} (f : A → B) (e₀ : Ev A) {r} → ev f e₀ ≡ pin r → e₀ ≡ pin r
ev-pin f (out _) ()
ev-pin f skip    ()
ev-pin f end     ()
ev-pin f (pin r) refl = refl

ev-skip : ∀ {A B : Set} (f : A → B) (e₀ : Ev A) → ev f e₀ ≡ skip → e₀ ≡ skip
ev-skip f (out _) ()
ev-skip f skip    refl = refl
ev-skip f end     ()
ev-skip f (pin r) ()

ev-out : ∀ {A B : Set} (f : A → B) (e₀ : Ev A) {b} → ev f e₀ ≡ out b → Σ A λ a → e₀ ≡ out a × b ≡ f a
ev-out f (out a) refl = a , refl , refl
ev-out f skip    ()
ev-out f end     ()
ev-out f (pin r) ()

module _ {A B : Set} (f : A → B) (m : Maybe (Tb.Listed A)) where
  tr-pin← : ∀ {k r} → TR (Mapped f m) k (pin r) → TR m k (pin r)
  tr-pin← x with tr-map→ f m x
  ... | e₀ , x₀ , eq = subst (TR m _) (ev-pin f e₀ (sym eq)) x₀

  tr-skip← : ∀ {k} → TR (Mapped f m) k skip → TR m k skip
  tr-skip← x with tr-map→ f m x
  ... | e₀ , x₀ , eq = subst (TR m _) (ev-skip f e₀ (sym eq)) x₀

  -- Live alike: an end maps to an end.
  live-map← : ∀ {k} → Live (TR (Mapped f m)) k → Live (TR m) k
  live-map← lv x = lv (tr-map← f m x)

  -- A run's table, mapped, is a run's.
  func-map : (∀ {y e e′} → TR m y e → TR m y e′ → e ≡ e′) → ∀ {y e e′} → TR (Mapped f m) y e → TR (Mapped f m) y e′ → e ≡ e′
  func-map fn x x′ with tr-map→ f m x | tr-map→ f m x′
  ... | e₀ , x₀ , refl | e₁ , x₁ , refl = cong (ev f) (fn x₀ x₁)

  flat-map : (∀ {y e l ys e′} → TR m y e → TR m (y ⊕ (l ∷ ys)) e′ → ⊥) → ∀ {y e l ys e′} → TR (Mapped f m) y e → TR (Mapped f m) (y ⊕ (l ∷ ys)) e′ → ⊥
  flat-map fl x x′ = fl (proj₁ (proj₂ (tr-map→ f m x))) (proj₁ (proj₂ (tr-map→ f m x′)))

  pin-in-map : (∀ {l r} → TR m l (pin r) → T (inside r l)) → ∀ {l r} → TR (Mapped f m) l (pin r) → T (inside r l)
  pin-in-map pi x = pi (tr-pin← x)

-- Two mapped tables agreeing below a value, one with a row at or past it:
-- their sources do, so both hold the source's value.
cons-map : ∀ {A B : Set} (f : A → B) {m m′ : Maybe (Tb.Listed A)}
         → (∀ {q} → AgreeTo q (TR (Mapped f m)) (TR (Mapped f m′)) → AgreeTo q (TR m) (TR m′))
         → (∀ {y y′ a e′} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ (TR m) (TR m′)) → TR m y (out a) → TR m′ y′ e′ → y ≼ y′ → TR m′ y (out a))
         → ∀ {y y′ b e′} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ (TR (Mapped f m)) (TR (Mapped f m′)))
         → TR (Mapped f m) y (out b) → TR (Mapped f m′) y′ e′ → y ≼ y′ → TR (Mapped f m′) y (out b)
cons-map f {m} {m′} ag← cn below x x′ yy with tr-map→ f m x | tr-map→ f m′ x′
... | e₀ , x₀ , eq | e₁ , x₁ , _ with ev-out f e₀ (sym eq)
...   | a , refl , refl = tr-map← f m′ (cn (λ lt → ag← (below lt)) x₀ x₁ yy)

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
  ag← {N} {N′} ag = coh-of (tr-few (P N) (P N′)) R.cons R.cons (ag-≃ (sh-map→ f (P N)) (sh-map← f (P N)) (sh-map→ f (P N′)) (sh-map← f (P N′)) (sh-of ag))

  ag←* : ∀ {N N′ k} → AgreeTo k (TR (Q′ N)) (TR (Q′ N′)) → AgreeTo k (TR (Q N)) (TR (Q N′))
  ag←* {N} {N′} ag = coh-of (tr-few (Q N) (Q N′)) R.cons* R.cons* (ag-≃ (sh-map→ g (Q N)) (sh-map← g (Q N)) (sh-map→ g (Q N′)) (sh-map← g (Q N′)) (sh-of ag))

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

  PinAt′ : ℕ → Pos → Pos → Set
  PinAt′ N k p = (Σ Pos λ l → Σ Pos λ p′ → TR (Q′ N) l (pin p′) × R.Put N k l
                   × (∀ {k₀ b} → TR (P′ N) k₀ (out b) → R.φ N k₀ ≺ p′ → k₀ ≺ p))
               × Homed′ N k

  out-back : ∀ N {k b} → TR (P′ N) k (out b) → Σ A λ a → TR (P N) k (out a)
  out-back N x with tr-map→ f (P N) x
  ... | e₀ , x₀ , eq with ev-out f e₀ (sym eq)
  ...   | a , refl , _ = a , x₀

  pin→′ : ∀ N {k p} → TR (P′ N) k (pin p) → Live (TR (P′ N)) k → PinAt′ N k p
  pin→′ N x lv with Corr.pin→ (R.corr N) (tr-pin← f (P N) x) (live-map← f (P N) lv)
  ... | (l , p′ , y , pl , past) , h =
    (l , p′ , tr-map← g (Q N) y , pl , λ x′ lt → past (proj₂ (out-back N x′)) lt) , homed→ h

  put-before′ : ∀ N {k l k′ e′} → TR (P′ N) k skip → R.Put N k l → TR (P′ N) k′ e′ → Unpinned e′ → k ≺ k′ → l ≼ R.φ N k′
  put-before′ N x pl x′ un′ lt = let (_ , x₀ , u₀) = back-row N x′ un′ in Corr.put-before (R.corr N) (tr-skip← f (P N) x) pl x₀ u₀ lt

  shown←′ : ∀ N {l e′} → TR (Q′ N) l e′ → Shown (One valuesOf) e′
          → Σ Pos λ k → Σ (Ev B) λ e → l ≡ R.φ N k × TR (P′ N) k e × Unpinned e × M e e′
  shown←′ N y sh with tr-map→ g (Q N) y
  ... | e₀′ , y₀ , refl with Corr.shown← (R.corr N) y₀ (back e₀′ sh)
  ...   | k , e , eq , x , un , mt = k , ev f e , eq , tr-map← f (P N) x , un← f e un , lift mt

  place′ : ∀ N {m e′} → TR (Q′ N) m e′ → Live (TR (Q′ N)) m
         → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev B) λ e → TR (P′ N) k e × Unpinned e × Img′ N k e × (R.φ N k ≼ m ⊎ Leads′ N k) × instantOf (R.φ N k) ≡ instantOf m
  place′ N {m} y lv with tr-map→ g (Q N) y
  ... | e₀′ , y₀ , refl with Corr.place (R.corr N) y₀ (live-map← g (Q N) lv)
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ (k , e , x , un , im , le , ie) = inj₂ (k , ev f e , tr-map← f (P N) x , un← f e un , img→ im , leadsOr {m = m} le , ie)

  corr′ : ∀ N → Corr s s* (R.φ N) (R.Put N) (TR (P′ N)) (TR (Q′ N))
  corr′ N = record
    { row→ = row→′ N ; pin→ = pin→′ N ; put-before = put-before′ N ; shown← = shown←′ N ; place = place′ N
    ; mono = λ x x′ un un′ lt → let (_ , x₀ , u₀) = back-row N x un ; (_ , x₁ , u₁) = back-row N x′ un′ in Corr.mono (R.corr N) x₀ x₁ u₀ u₁ lt
    ; inst = λ x x′ un un′ → let (_ , x₀ , u₀) = back-row N x un ; (_ , x₁ , u₁) = back-row N x′ un′ in Corr.inst (R.corr N) x₀ x₁ u₀ u₁
    ; home = λ x un → let (_ , x₀ , u₀) = back-row N x un in Corr.home (R.corr N) x₀ u₀ }

  rel′ : Rel P′ Q′ s s*
  rel′ = record
    { φ = R.φ ; Put = R.Put ; corr = corr′
    ; φ-agree = λ {N} x un ag → let (_ , x₀ , u₀) = back-row N x un in R.φ-agree x₀ u₀ (ag← ag)
    ; bk = R.bk
    ; in-bk = λ {N} x un → let (_ , x₀ , u₀) = back-row N x un in R.in-bk x₀ u₀
    ; pb-few = R.pb-few
    ; back = λ {_} {N′} le x un ag* → let (_ , x₀ , u₀) = back-row N′ x un in ag-map f (R.back le x₀ u₀ (ag←* ag*))
    ; put-up = λ le ag → R.put-up le (ag← ag)
    ; back-put = λ le pl ag* → R.back-put le pl (ag←* ag*)
    ; elab-causal = λ {N} le x un ag → let (_ , x₀ , u₀) = back-row N x un in ag-map g (R.elab-causal le x₀ u₀ (ag← ag))
    ; stable← = λ {N} le x un y ag* → let (_ , x₀ , u₀) = back-row N x un in
        ag-map f (R.stable← le x₀ u₀ (proj₁ (proj₂ (tr-map→ g (Q N) y))) (ag←* ag*))
    ; stable-put = λ {N} le ag y pl → ag-map g (R.stable-put le (ag← ag) (proj₁ (proj₂ (tr-map→ g (Q N) y))) pl)
    ; stable-lead = λ {N} le x un y ld z ie ag* → let (_ , x₀ , u₀) = back-row N x un in
        ag-map g (R.stable-lead le x₀ u₀ (proj₁ (proj₂ (tr-map→ g (Q N) y))) (leads← ld) (proj₁ (proj₂ (tr-map→ g (Q N) z))) ie (ag←* ag*))
    ; elab-all = λ {N} {N′} le all y → let (_ , y₀ , eq) = tr-map→ g (Q N′) y in
        subst (TR (Q′ N) _) (sym eq) (tr-map← g (Q N) (R.elab-all le (λ q → ag← (all q)) y₀))
    ; func = λ {N} → func-map f (P N) R.func
    ; func* = λ {N} → func-map g (Q N) R.func*
    ; flat = λ {N} → flat-map f (P N) R.flat
    ; flat* = λ {N} → flat-map g (Q N) R.flat*
    ; pin-in = λ {N} → pin-in-map f (P N) R.pin-in
    ; pin-in* = λ {N} → pin-in-map g (Q N) R.pin-in*
    ; cons = λ {N} {N′} → cons-map f {P N} {P N′} ag← (R.cons {N} {N′})
    ; cons* = λ {N} {N′} → cons-map g {Q N} {Q N′} ag←* (R.cons* {N} {N′})
    ; got = λ N → got-bind (mapRows f) (R.got N)
    ; got* = λ N → got-bind (mapRows g) (R.got* N)
    ; after = λ {N} x → R.after (proj₁ (proj₂ (tr-map→ f (P N) x)))
    ; after* = λ {N} y → R.after* (proj₁ (proj₂ (tr-map→ g (Q N) y)))
    ; after-φ = λ {N} x un → let (_ , x₀ , u₀) = back-row N x un in R.after-φ x₀ u₀
    ; pin-after* = λ {N} y → R.pin-after* (tr-pin← g (Q N) y)
    ; pin-stable = λ {N} {N′} le x un ag hp rk y → let (_ , x₀ , u₀) = back-row N x un in
        tr-map← g (Q N) (R.pin-stable le x₀ u₀ (ag← ag) (λ r₀k x₁ → tr-pin← f (P N) (hp r₀k (tr-map← f (P N′) x₁))) rk (tr-pin← g (Q N′) y)) }

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
