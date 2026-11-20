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
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; _≺_; _≼_)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind; mapRow; mapRows)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.Horizon using (Tag; module Cuts)
open import denotation.Laws.Modulus using (⟨_⟩; upto)
open import simultaneous.HorizonCorr using (module Sub)
open import simultaneous.TableCorr using (Corr; Rel; module Rel; module Across)
open import simultaneous.TableKit using (TR; M; ev; got-bind)

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

-- A MAP KEEPS ITS CHILD'S HANGS: the mapped cuts hold the child's rows
-- in place, so they stop where the child's do.
map-bounded : ∀ {X Y : Set} (f : X → Y) (P : ℕ → Maybe (Tb.Listed X)) {Bd : ℕ → Pos → Tag → Set}
            → Cuts.Bounded (λ N → TR (P N)) Bd → Cuts.Bounded (λ N → TR (Mapped f (P N))) Bd
map-bounded {X} {Y} f P {Bd} B = record
  { gap     = λ {N} bd′ x → B.gap bd′ (proj₁ (proj₂ (tr-map→ f (P N) x)))
  ; held-in = λ {N} {b} {q} → B.held-in {N} {b} {q}
  ; held-under = λ {N} {b} {q} → B.held-under {N} {b} {q}
  ; fwd     = λ {N} {k} cl {N′} le →
      ⟨ (λ {y} yk → (λ x → mv N N′ (λ {e₀} → proj₁ (upto (B.fwd {N} {k} cl le) {y} {e₀} yk)) x)
                  , (λ x → mv N′ N (λ {e₀} → proj₂ (upto (B.fwd {N} {k} cl le) {y} {e₀} yk)) x)) ⟩
  ; fwd-pin = λ {N} {q} {k} cl hc {N′} le {y} yk →
      (λ x → pn N N′ (proj₁ (B.fwd-pin {N} {q} {k} cl hc le yk)) x) , (λ x → pn N′ N (proj₂ (B.fwd-pin {N} {q} {k} cl hc le yk)) x)
  }
  where
    module B = Cuts.Bounded B

    mv : ∀ M M′ {y e} → (∀ {e₀} → TR (P M) y e₀ → TR (P M′) y e₀) → TR (Mapped f (P M)) y e → TR (Mapped f (P M′)) y e
    mv M M′ h x with tr-map→ f (P M) x
    ... | e₀ , x₀ , refl = tr-map← f (P M′) (h x₀)

    pn : ∀ M M′ {y q} → (TR (P M) y (pin q) → TR (P M′) y (pin q)) → TR (Mapped f (P M)) y (pin q) → TR (Mapped f (P M′)) y (pin q)
    pn M M′ {y} {q} h x with tr-map→ f (P M) x
    ... | pin q′ , x₀ , refl = tr-map← f (P M′) (h x₀)

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

  ev-bounded  : Cuts.Bounded (λ N → TR (P′ N)) R.Bd
  ev-bounded  = map-bounded f P R.bounded

  ev-bounded* : Cuts.Bounded (λ N → TR (Q′ N)) R.Bd*
  ev-bounded* = map-bounded g Q R.bounded*

  back-row : ∀ N {k e} → TR (P′ N) k e → Unpinned e → Σ (Ev A) λ e₀ → TR (P N) k e₀ × Unpinned e₀
  back-row N x un with tr-map→ f (P N) x
  ... | e₀ , x₀ , refl = e₀ , x₀ , un→ f e₀ un

  Img′ : ℕ → Pos → Ev B → Set
  Img′ N k e = Σ (Ev (IE B)) λ e′ → TR (Q′ N) (R.φ N k) e′ × M e e′

  img→ : ∀ {N k e} → Corr.Imaged (R.corr N) k e → Img′ N k (ev f e)
  img→ {N} (e′ , y , mt) = ev g e′ , tr-map← g (Q N) y , lift mt

  Homed′ : ℕ → Pos → Set
  Homed′ N k = instantOf k ≡ instantOf s
             ⊎ Σ Pos λ k₀ → Σ (Ev B) λ e₀ → TR (P′ N) k₀ e₀ × Unpinned e₀ × ¬ R.Late N k₀ × Img′ N k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  homed→ : ∀ {N k} → Corr.Homed (R.corr N) k → Homed′ N k
  homed→ (inj₁ e) = inj₁ e
  homed→ {N} (inj₂ (k₀ , e₀ , x , un , nl , im , lt , ie)) = inj₂ (k₀ , ev f e₀ , tr-map← f (P N) x , un← f e₀ un , nl , img→ im , lt , ie)

  PutAt′ : ℕ → Pos → Set
  PutAt′ N k = (Σ Pos λ l → Σ (Ev (IE B)) λ e′ → TR (Q′ N) l e′ × R.Put N k l) × Homed′ N k

  put→ : ∀ {N k} → Corr.PutAt (R.corr N) k → PutAt′ N k
  put→ {N} ((l , e′ , y , pl) , h) = (l , ev g e′ , tr-map← g (Q N) y , pl) , homed→ h

  Leads′ : ℕ → Pos → Set
  Leads′ N k = ∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  leads→ : ∀ {N k} → Corr.Leads (R.corr N) k → Leads′ N k
  leads→ {N} ld x′ un′ ie′ with tr-map→ f (P N) x′
  ... | e₀ , x₀ , refl = ld x₀ (un→ f e₀ un′) ie′

  leadsOr : ∀ {N k m} → R.φ N k ≼ m ⊎ Corr.Leads (R.corr N) k → R.φ N k ≼ m ⊎ Leads′ N k
  leadsOr (inj₁ le) = inj₁ le
  leadsOr (inj₂ ld) = inj₂ (leads→ ld)

  row→′ : ∀ N {k e} → TR (P′ N) k e → Unpinned e → (Img′ N k e × ¬ R.Late N k) ⊎ (e ≡ skip × PutAt′ N k)
  row→′ N x un with tr-map→ f (P N) x
  ... | e₀ , x₀ , refl with Corr.row→ (R.corr N) x₀ (un→ f e₀ un)
  ...   | inj₁ (im , nl)   = inj₁ (img→ im , nl)
  ...   | inj₂ (refl , pa) = inj₂ (refl , put→ pa)

  late-put′ : ∀ N {k e} → R.Late N k → TR (P′ N) k e → e ≡ skip × PutAt′ N k
  late-put′ N lt x with tr-map→ f (P N) x
  ... | e₀ , x₀ , refl with Corr.late-put (R.corr N) lt x₀
  ...   | refl , pa = refl , put→ pa

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

  put-before′ : ∀ N {k l k′ e′} → TR (P′ N) k skip → R.Put N k l → TR (P′ N) k′ e′ → Unpinned e′ → ¬ R.Late N k′ → k ≺ k′ → l ≼ R.φ N k′
  put-before′ N x pl x′ un′ nl′ lt = let (_ , x₀ , u₀) = back-row N x′ un′ in Corr.put-before (R.corr N) (tr-skip← f (P N) x) pl x₀ u₀ nl′ lt

  pin-before′ : ∀ N {k p l k′ e′} → TR (P′ N) k (pin p) → R.Put N k l → TR (P′ N) k′ e′ → Unpinned e′ → ¬ R.Late N k′ → k ≺ k′ → l ≼ R.φ N k′
  pin-before′ N x pl x′ un′ nl′ lt = let (_ , x₀ , u₀) = back-row N x′ un′ in Corr.pin-before (R.corr N) (tr-pin← f (P N) x) pl x₀ u₀ nl′ lt

  shown←′ : ∀ N {l e′} → TR (Q′ N) l e′ → Shown (One valuesOf) e′
          → Σ Pos λ k → Σ (Ev B) λ e → l ≡ R.φ N k × TR (P′ N) k e × Unpinned e × ¬ R.Late N k × M e e′
  shown←′ N y sh with tr-map→ g (Q N) y
  ... | e₀′ , y₀ , refl with Corr.shown← (R.corr N) y₀ (back e₀′ sh)
  ...   | k , e , eq , x , un , nl , mt = k , ev f e , eq , tr-map← f (P N) x , un← f e un , nl , lift mt

  place′ : ∀ N {m e′} → TR (Q′ N) m e′ → Live (TR (Q′ N)) m
         → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev B) λ e → TR (P′ N) k e × Unpinned e × ¬ R.Late N k × Img′ N k e
             × (R.φ N k ≼ m ⊎ Leads′ N k) × instantOf (R.φ N k) ≡ instantOf m
  place′ N {m} y lv with tr-map→ g (Q N) y
  ... | e₀′ , y₀ , refl with Corr.place (R.corr N) y₀ (live-map← g (Q N) lv)
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ (k , e , x , un , nl , im , le , ie) = inj₂ (k , ev f e , tr-map← f (P N) x , un← f e un , nl , img→ im , leadsOr {m = m} le , ie)

  corr′ : ∀ N → Corr s s* (R.φ N) (R.Put N) (R.Late N) (TR (P′ N)) (TR (Q′ N))
  corr′ N = record
    { row→ = row→′ N ; late-put = late-put′ N ; pin→ = pin→′ N ; put-before = put-before′ N ; pin-before = pin-before′ N
    ; shown← = shown←′ N ; place = place′ N
    ; mono = λ x x′ un un′ nl nl′ lt → let (_ , x₀ , u₀) = back-row N x un ; (_ , x₁ , u₁) = back-row N x′ un′ in Corr.mono (R.corr N) x₀ x₁ u₀ u₁ nl nl′ lt
    ; inst = λ x x′ un un′ nl nl′ → let (_ , x₀ , u₀) = back-row N x un ; (_ , x₁ , u₁) = back-row N x′ un′ in Corr.inst (R.corr N) x₀ x₁ u₀ u₁ nl nl′
    ; home = λ x un nl → let (_ , x₀ , u₀) = back-row N x un in Corr.home (R.corr N) x₀ u₀ nl }

  rel′ : Rel P′ Q′ s s*
  rel′ = record
    { φ = R.φ ; Put = R.Put ; Late = R.Late ; corr = corr′
    ; bk = R.bk
    ; in-bk = λ {N} x un nl → let (_ , x₀ , u₀) = back-row N x un in R.in-bk x₀ u₀ nl
    ; pb-few = R.pb-few
    ; func = λ {N} → func-map f (P N) R.func
    ; func* = λ {N} → func-map g (Q N) R.func*
    ; flat = λ {N} → flat-map f (P N) R.flat
    ; flat* = λ {N} → flat-map g (Q N) R.flat*
    ; pin-in = λ {N} → pin-in-map f (P N) R.pin-in
    ; pin-in* = λ {N} → pin-in-map g (Q N) R.pin-in*
    ; got = λ N → got-bind (mapRows f) (R.got N)
    ; got* = λ N → got-bind (mapRows g) (R.got* N)
    ; after = λ {N} x → R.after (proj₁ (proj₂ (tr-map→ f (P N) x)))
    ; after* = λ {N} y → R.after* (proj₁ (proj₂ (tr-map→ g (Q N) y)))
    ; after-φ = λ {N} x un nl → let (_ , x₀ , u₀) = back-row N x un in R.after-φ x₀ u₀ nl
    ; pin-after* = λ {N} y → R.pin-after* (tr-pin← g (Q N) y)
    ; Bd = R.Bd ; Bd* = R.Bd* ; bounded = ev-bounded ; bounded* = ev-bounded*
    ; bcorr = λ N → Sub.restrict (λ { (_ , x , un , nl) → let (e₀ , x₀ , u₀) = back-row N x un in e₀ , x₀ , u₀ , nl })
        (λ { ((_ , x) , pl) → (_ , proj₁ (proj₂ (tr-map→ f (P N) x))) , pl }) (R.bcorr N)
    ; across = record
      { back-clear = λ {N} {N′} le x un nl cl* → let (_ , x₀ , u₀) = back-row N′ x un in Across.back-clear R.across le x₀ u₀ nl cl*
      ; put-clear = λ {N} {N′} le x pl cl* → Across.put-clear R.across le (proj₁ (proj₂ (tr-map→ f (P N′) x))) pl cl*
      ; lead-clear = λ {N} x un nl ld y ie cl* → let (_ , x₀ , u₀) = back-row N x un in
          Across.lead-clear R.across x₀ u₀ nl (λ {_} {e′} x′ un′ ie′ → ld (tr-map← f (P N) x′) (un← f e′ un′) ie′)
            (proj₁ (proj₂ (tr-map→ g (Q N) y))) ie cl* } }

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
