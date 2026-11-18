{-# OPTIONS --guardedness #-}

-- A GUARD ROW CARRIES A SUBTERM'S RECORD (`defer-tab`): a `defer`'s
-- tables hold a skip at the subscription's first tick, before every row
-- of the child's, subscribed at its second.  The plain guard is imaged on
-- the elaborated one; every child row keeps the child's image, its late
-- placement and its lifting facts.  Agreement crosses the guard because
-- both cuts hold it, and nothing of the child's lies at or under it.
module simultaneous.TableDefer where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (yes; no; ¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; inside; ix; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-part)
open import denotation.EmissionSet using (Ev; out; skip; pin; Unpinned; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺-irrefl; ≺-absurd; ≺→≼; ≺-≼-≺; ≼-trans; ≺-ext; ticks)
open import denotation.Laws.Worlds using (⊕-assoc)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; short; bind; _⊣_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.TableCorr using (TR; M; Got; Cons; Corr; Rel; module Rel; Same; same; φ≡; nl→; Scope; module Scope; got-bind; m-ss)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- A table with a skip at `q` before its rows

Guarded : ∀ {X : Set} → Pos → Maybe (Tb.Listed X) → Maybe (Tb.Listed X)
Guarded q m = bind m λ b → just (((q , skip) ∷ rows b) ⊣ short b)

tr-g→ : ∀ {X : Set} q (m : Maybe (Tb.Listed X)) {k e} → TR (Guarded q m) k e → (k ≡ q × e ≡ skip) ⊎ TR m k e
tr-g→ q nothing (_ , () , _)
tr-g→ q (just L) (_ , refl , here refl) = inj₁ (refl , refl)
tr-g→ q (just L) (_ , refl , there r)   = inj₂ (L , refl , r)

tr-g← : ∀ {X : Set} q (m : Maybe (Tb.Listed X)) {k e} → TR m k e → TR (Guarded q m) k e
tr-g← q _ (L , refl , r) = _ , refl , there r

tr-g0 : ∀ {X : Set} q (m : Maybe (Tb.Listed X)) → Got m → TR (Guarded q m) q skip
tr-g0 q _ (L , refl) = _ , refl , here refl

-- Every row of `m` past `q`.
Past : ∀ {X : Set} → Pos → Maybe (Tb.Listed X) → Set
Past {X} q m = ∀ {y} {e : Ev X} → TR m y e → q ≺ y

module _ {X : Set} (q : Pos) where
  -- A guarded row past the guard is the child's.
  strip : ∀ (n : Maybe (Tb.Listed X)) {y e} → q ≺ y → TR (Guarded q n) y e → TR n y e
  strip n lt x with tr-g→ q n x
  ... | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q} lt)
  ... | inj₂ x₀         = x₀

  -- Agreement crosses the guard both ways.
  ag-strip : ∀ {m m′ : Maybe (Tb.Listed X)} {k} → Past q m → Past q m′
           → AgreeTo k (TR (Guarded q m)) (TR (Guarded q m′)) → AgreeTo k (TR m) (TR m′)
  ag-strip {m} {m′} a a′ ag =
    ⟨ (λ {y} {e} yk → (λ x → strip m′ (a x) (proj₁ (upto ag {y} {e} yk) (tr-g← q m x)))
                    , (λ x → strip m (a′ x) (proj₂ (upto ag {y} {e} yk) (tr-g← q m′ x)))) ⟩

  ag-add : ∀ {m m′ : Maybe (Tb.Listed X)} {k} → Got m → Got m′
         → AgreeTo k (TR m) (TR m′) → AgreeTo k (TR (Guarded q m)) (TR (Guarded q m′))
  ag-add {m} {m′} gm gm′ ag =
    ⟨ (λ {y} yk → add m m′ gm′ (λ {e} → proj₁ (upto ag {y} {e} yk)) , add m′ m gm (λ {e} → proj₂ (upto ag {y} {e} yk))) ⟩
    where
      add : ∀ n n′ {y} → Got n′ → (∀ {e} → TR n y e → TR n′ y e) → ∀ {e} → TR (Guarded q n) y e → TR (Guarded q n′) y e
      add n n′ gt h x with tr-g→ q n x
      ... | inj₁ (refl , refl) = tr-g0 q n′ gt
      ... | inj₂ x₀            = tr-g← q n′ (h x₀)

  -- Up to the guard, two guarded tables hold only it.
  ag-low : ∀ {m m′ : Maybe (Tb.Listed X)} → Past q m → Past q m′ → Got m → Got m′
         → AgreeTo q (TR (Guarded q m)) (TR (Guarded q m′))
  ag-low {m} {m′} a a′ gm gm′ = ⟨ (λ yq → low m m′ a gm′ yq , low m′ m a′ gm yq) ⟩
    where
      low : ∀ n n′ → Past q n → Got n′ → ∀ {y e} → y ≼ q → TR (Guarded q n) y e → TR (Guarded q n′) y e
      low n n′ ab gt yq x with tr-g→ q n x
      ... | inj₁ (refl , refl) = tr-g0 q n′ gt
      ... | inj₂ x₀            = ⊥-elim (yq (ab x₀))

  -- A run's table, guarded, is a run's.
  func-g : ∀ {m : Maybe (Tb.Listed X)} → Past q m → (∀ {y e e′} → TR m y e → TR m y e′ → e ≡ e′)
         → ∀ {y e e′} → TR (Guarded q m) y e → TR (Guarded q m) y e′ → e ≡ e′
  func-g {m} ab fn x x′ with tr-g→ q m x | tr-g→ q m x′
  ... | inj₁ (refl , refl) | inj₁ (_ , refl) = refl
  ... | inj₁ (refl , _)    | inj₂ x₁         = ⊥-elim (≺-irrefl {q} (ab x₁))
  ... | inj₂ x₀            | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q} (ab x₀))
  ... | inj₂ x₀            | inj₂ x₁         = fn x₀ x₁

  flat-g : ∀ {m : Maybe (Tb.Listed X)} → Past q m → (∀ {l ys e} → TR m (q ⊕ (l ∷ ys)) e → ⊥)
         → (∀ {y e l ys e′} → TR m y e → TR m (y ⊕ (l ∷ ys)) e′ → ⊥)
         → ∀ {y e l ys e′} → TR (Guarded q m) y e → TR (Guarded q m) (y ⊕ (l ∷ ys)) e′ → ⊥
  flat-g {m} ab und fl {y} {l = l} {ys} x x′ with tr-g→ q m x | tr-g→ q m x′
  ... | inj₁ (refl , _) | inj₁ (eq , _) = ≺-irrefl {q} (subst (q ≺_) eq (≺-ext q {l} ys))
  ... | inj₁ (refl , _) | inj₂ x₁       = und x₁
  ... | inj₂ x₀         | inj₁ (eq , _) = ≺-absurd {q} {y} (ab x₀) (subst (y ≺_) eq (≺-ext y {l} ys))
  ... | inj₂ x₀         | inj₂ x₁       = fl x₀ x₁

  pin-in-g : ∀ {m : Maybe (Tb.Listed X)} → (∀ {l r} → TR m l (pin r) → T (inside r l))
           → ∀ {l r} → TR (Guarded q m) l (pin r) → T (inside r l)
  pin-in-g {m} pi x with tr-g→ q m x
  ... | inj₁ (_ , ())
  ... | inj₂ x₀ = pi x₀

  cons-g : ∀ {m m′ : Maybe (Tb.Listed X)} {G : Pos → Set} → Past q m → Past q m′ → Cons G (TR m) (TR m′) → Cons G (TR (Guarded q m)) (TR (Guarded q m′))
  cons-g {m} {m′} ab ab′ cn gy below x x′ yy with tr-g→ q m x | tr-g→ q m′ x′
  ... | inj₁ (_ , ())  | _
  ... | inj₂ x₀ | inj₁ (refl , _) = ⊥-elim (yy (ab x₀))
  ... | inj₂ x₀ | inj₂ x₁         = tr-g← q m′ (cn gy (λ lt → ag-strip ab ab′ (below lt)) x₀ x₁ yy)

------------------------------------------------------------------------
-- The record, guarded

-- A guard's map over its child's: the guard on its image, any other row
-- along the child's.
guardφ : Pos → Pos → (Pos → Pos) → Pos → Pos
guardφ g g* ψ k with k ≟ᵖ g
... | yes _ = g*
... | no _  = ψ k

-- Children mapping alike, guarded alike.
guardφ-cong : ∀ g g* {ψ ψ′ : Pos → Pos} → (∀ k → ψ k ≡ ψ′ k) → ∀ k → guardφ g g* ψ k ≡ guardφ g g* ψ′ k
guardφ-cong g g* e k with k ≟ᵖ g
... | yes _ = refl
... | no _  = e k

module DeferTab {A : Set} (p p* : Pos) {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))}
  {S : Scope} (R : Rel P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) S) where

  module R = Rel R
  module Sc = Scope S

  g g* o o* : Pos
  g  = p ⊕ [ ix 0 ]
  g* = p* ⊕ [ ix 0 ]
  o  = p ⊕ [ ix 1 ]
  o* = p* ⊕ [ ix 1 ]

  P′ : ℕ → Maybe (Tb.Listed A)
  P′ N = Guarded g (P N)

  Q′ : ℕ → Maybe (Tb.Listed (IE A))
  Q′ N = Guarded g* (Q N)

  -- The guard's first tick before the child's second.
  ab : ∀ N → Past g (P N)
  ab N {y} x = ≺-≼-≺ {g} {o} {y} (ticks p 0) (R.after x)

  ab* : ∀ N → Past g* (Q N)
  ab* N {y} y₀ = ≺-≼-≺ {g*} {o*} {y} (ticks p* 0) (R.after* y₀)

  -- Nothing of the child's lies under the guard.
  under : ∀ l ys → (g ⊕ (l ∷ ys)) ≺ o
  under l ys = subst (_≺ o) (sym (⊕-assoc p [ ix 0 ] (l ∷ ys))) (Equivalence.from T-≡ (<ᵖ-part p (l ∷ ys) [] refl))

  under* : ∀ l ys → (g* ⊕ (l ∷ ys)) ≺ o*
  under* l ys = subst (_≺ o*) (sym (⊕-assoc p* [ ix 0 ] (l ∷ ys))) (Equivalence.from T-≡ (<ᵖ-part p* (l ∷ ys) [] refl))

  und : ∀ N {l ys e} → TR (P N) (g ⊕ (l ∷ ys)) e → ⊥
  und N {l} {ys} x = R.after x (under l ys)

  und* : ∀ N {l ys e} → TR (Q N) (g* ⊕ (l ∷ ys)) e → ⊥
  und* N {l} {ys} y = R.after* y (under* l ys)

  ig : instantOf g ≡ instantOf o
  ig = trans (inst-⊕ p [ ix 0 ]) (sym (inst-⊕ p [ ix 1 ]))

  ig* : instantOf g* ≡ instantOf o*
  ig* = trans (inst-⊕ p* [ ix 0 ]) (sym (inst-⊕ p* [ ix 1 ]))

  -- The map: the guard on the guard, the child's rows on their images.
  φ′ : ℕ → Pos → Pos
  φ′ N = guardφ g g* (R.φ N)

  φ-g : ∀ {N} → φ′ N g ≡ g*
  φ-g with g ≟ᵖ g
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  φ-c : ∀ {N k} → g ≺ k → φ′ N k ≡ R.φ N k
  φ-c {N} {k} lt with k ≟ᵖ g
  ... | yes refl = ⊥-elim (≺-irrefl {g} lt)
  ... | no _     = refl

  ab-φ : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ R.Late N k → g* ≺ R.φ N k
  ab-φ {N} {k} x un nl = ≺-≼-≺ {g*} {o*} {R.φ N k} (ticks p* 0) (R.after-φ x un nl)

  -- A late placement only of the child's rows, and only they are late.
  Put′ : ℕ → Pos → Pos → Set
  Put′ N k l = o ≼ k × R.Put N k l

  Late′ : ℕ → Pos → Set
  Late′ N k = o ≼ k × R.Late N k

  nl-c : ∀ {N k e} → TR (P N) k e → ¬ Late′ N k → ¬ R.Late N k
  nl-c x nl lt = nl (R.after x , lt)

  nl-g : ∀ {N} → ¬ Late′ N g
  nl-g (ok , _) = ok (ticks p 0)

  -- A guard on the child's image moves to its own.
  g*-c : ∀ {N N′ M k e} → TR (P M) k e → Sc.G* N N′ (φ′ M k) → Sc.G* N N′ (R.φ M k)
  g*-c {N} {N′} {M} {k} x = subst (Sc.G* N N′) (φ-c {M} {k} (ab M x))

  Img′ : ℕ → Pos → Ev A → Set
  Img′ N k e = Σ (Ev (IE A)) λ e′ → TR (Q′ N) (φ′ N k) e′ × M e e′

  img→ : ∀ {N k e} → TR (P N) k e → Corr.Imaged (R.corr N) k e → Img′ N k e
  img→ {N} {k} x (e′ , y , mt) = e′ , subst (λ z → TR (Q′ N) z e′) (sym (φ-c {N} {k} (ab N x))) (tr-g← g* (Q N) y) , mt

  img-g : ∀ N → Img′ N g skip
  img-g N = skip , subst (λ z → TR (Q′ N) z skip) (sym (φ-g {N})) (tr-g0 g* (Q N) (R.got* N)) , m-ss {A}

  Homed′ : ℕ → Pos → Set
  Homed′ N k = instantOf k ≡ instantOf p
             ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → TR (P′ N) k₀ e₀ × Unpinned e₀ × ¬ Late′ N k₀ × Img′ N k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  homed→ : ∀ {N k} → Corr.Homed (R.corr N) k → Homed′ N k
  homed→ (inj₁ e) = inj₁ (trans e (inst-⊕ p [ ix 1 ]))
  homed→ {N} (inj₂ (k₀ , e₀ , x , un , nl , im , lt , ie)) = inj₂ (k₀ , e₀ , tr-g← g (P N) x , un , (λ { (_ , l) → nl l }) , img→ x im , lt , ie)

  PutAt′ : ℕ → Pos → Set
  PutAt′ N k = (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → TR (Q′ N) l e′ × Put′ N k l) × Homed′ N k

  Leads′ : ℕ → Pos → Set
  Leads′ N k = ∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  -- A child's row leading its instant leads it guarded, the guard's
  -- instant aside.
  leads→ : ∀ {N k} → Corr.Leads (R.corr N) k → ¬ (instantOf k ≡ instantOf o) → Leads′ N k
  leads→ {N} ld ne x′ un′ ie′ with tr-g→ g (P N) x′
  ... | inj₁ (refl , refl) = ⊥-elim (ne (trans (sym ie′) ig))
  ... | inj₂ x₁            = ld x₁ un′ ie′

  leads← : ∀ {N k} → Leads′ N k → Corr.Leads (R.corr N) k
  leads← {N} ld x′ un′ ie′ = ld (tr-g← g (P N) x′) un′ ie′

  row→′ : ∀ N {k e} → TR (P′ N) k e → Unpinned e → (Img′ N k e × ¬ Late′ N k) ⊎ (e ≡ skip × PutAt′ N k)
  row→′ N x un with tr-g→ g (P N) x
  ... | inj₁ (refl , refl) = inj₁ (img-g N , nl-g {N})
  ... | inj₂ x₀ with Corr.row→ (R.corr N) x₀ un
  ...   | inj₁ (im , nl)                  = inj₁ (img→ x₀ im , λ { (_ , l) → nl l })
  ...   | inj₂ (eq , (l , e′ , y , pl) , h) = inj₂ (eq , (l , e′ , tr-g← g* (Q N) y , R.after x₀ , pl) , homed→ h)

  late-put′ : ∀ N {k e} → Late′ N k → TR (P′ N) k e → e ≡ skip × PutAt′ N k
  late-put′ N (ok , lt) x with tr-g→ g (P N) x
  ... | inj₁ (refl , _) = ⊥-elim (ok (ticks p 0))
  ... | inj₂ x₀ with Corr.late-put (R.corr N) lt x₀
  ...   | eq , (l , e′ , y , pl) , h = eq , (l , e′ , tr-g← g* (Q N) y , R.after x₀ , pl) , homed→ h

  PinAt′ : ℕ → Pos → Pos → Set
  PinAt′ N k r = (Σ Pos λ l → Σ Pos λ p′ → TR (Q′ N) l (pin p′) × Put′ N k l
                   × (∀ {k₀ b} → TR (P′ N) k₀ (out b) → φ′ N k₀ ≺ p′ → k₀ ≺ r))
               × Homed′ N k

  pin→′ : ∀ N {k r} → TR (P′ N) k (pin r) → Live (TR (P′ N)) k → PinAt′ N k r
  pin→′ N x lv with tr-g→ g (P N) x
  ... | inj₁ (_ , ())
  ... | inj₂ x₀ with Corr.pin→ (R.corr N) x₀ (λ xc → lv (tr-g← g (P N) xc))
  ...   | (l , p′ , y , pl , past) , h = (l , p′ , tr-g← g* (Q N) y , (R.after x₀ , pl) , past′) , homed→ h
    where
      past′ : ∀ {k₀ b} → TR (P′ N) k₀ (out b) → φ′ N k₀ ≺ p′ → k₀ ≺ _
      past′ {k₀} x′ lt with tr-g→ g (P N) x′
      ... | inj₁ (_ , ())
      ... | inj₂ x₁ = past x₁ (subst (_≺ p′) (φ-c {N} {k₀} (ab N x₁)) lt)

  put-before′ : ∀ N {k l k′ e′} → TR (P′ N) k skip → Put′ N k l → TR (P′ N) k′ e′ → Unpinned e′ → ¬ Late′ N k′ → k ≺ k′ → l ≼ φ′ N k′
  put-before′ N {k} {l} {k′} x (ok , pl) x′ un′ nl′ lt with tr-g→ g (P N) x | tr-g→ g (P N) x′
  ... | inj₁ (refl , _) | _               = ⊥-elim (ok (ticks p 0))
  ... | inj₂ x₀         | inj₁ (refl , _) = ⊥-elim (≺-absurd {g} {k} (ab N x₀) lt)
  ... | inj₂ x₀         | inj₂ x₁         =
    subst (l ≼_) (sym (φ-c {N} {k′} (ab N x₁))) (Corr.put-before (R.corr N) x₀ pl x₁ un′ (nl-c x₁ nl′) lt)

  pin-before′ : ∀ N {k r l k′ e′} → TR (P′ N) k (pin r) → Put′ N k l → TR (P′ N) k′ e′ → Unpinned e′ → ¬ Late′ N k′ → k ≺ k′ → l ≼ φ′ N k′
  pin-before′ N {k} {l = l} {k′} x (ok , pl) x′ un′ nl′ lt with tr-g→ g (P N) x | tr-g→ g (P N) x′
  ... | inj₁ (_ , ())   | _
  ... | inj₂ x₀         | inj₁ (refl , _) = ⊥-elim (≺-absurd {g} {k} (ab N x₀) lt)
  ... | inj₂ x₀         | inj₂ x₁         =
    subst (l ≼_) (sym (φ-c {N} {k′} (ab N x₁))) (Corr.pin-before (R.corr N) x₀ pl x₁ un′ (nl-c x₁ nl′) lt)

  shown←′ : ∀ N {l e′} → TR (Q′ N) l e′ → Shown (One valuesOf) e′
          → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ′ N k × TR (P′ N) k e × Unpinned e × ¬ Late′ N k × M e e′
  shown←′ N y sh with tr-g→ g* (Q N) y
  ... | inj₁ (refl , refl) = ⊥-elim sh
  ... | inj₂ y₀ with Corr.shown← (R.corr N) y₀ sh
  ...   | k , e , eq , x , un , nl , mt = k , e , trans eq (sym (φ-c {N} {k} (ab N x))) , tr-g← g (P N) x , un , (λ { (_ , l) → nl l }) , mt

  place′ : ∀ N {m e′} → TR (Q′ N) m e′ → Live (TR (Q′ N)) m
         → instantOf m ≡ instantOf p* ⊎ Σ Pos λ k → Σ (Ev A) λ e → TR (P′ N) k e × Unpinned e × ¬ Late′ N k × Img′ N k e
             × (φ′ N k ≼ m ⊎ Leads′ N k) × instantOf (φ′ N k) ≡ instantOf m
  place′ N {m} y lv with tr-g→ g* (Q N) y
  ... | inj₁ (refl , refl) = inj₁ (inst-⊕ p* [ ix 0 ])
  ... | inj₂ y₀ with Corr.place (R.corr N) y₀ (λ yc → lv (tr-g← g* (Q N) yc))
  ...   | inj₁ e = inj₁ (trans e (inst-⊕ p* [ ix 1 ]))
  ...   | inj₂ (k , e , x , un , nl , im , inj₁ le , ie) =
    inj₂ (k , e , tr-g← g (P N) x , un , (λ { (_ , l) → nl l }) , img→ x im , inj₁ (subst (_≼ m) (sym (φ-c {N} {k} (ab N x))) le)
         , trans (cong instantOf (φ-c {N} {k} (ab N x))) ie)
  ...   | inj₂ (k , e , x , un , nl , im , inj₂ ld , ie) with instantOf k ≟ⁱ instantOf o
  ...     | yes eq = inj₁ (trans (sym ie) (trans (Equivalence.from (Corr.home (R.corr N) x un nl) eq) (inst-⊕ p* [ ix 1 ])))
  ...     | no ne  = inj₂ (k , e , tr-g← g (P N) x , un , (λ { (_ , l) → nl l }) , img→ x im , inj₂ (leads→ ld ne) , trans (cong instantOf (φ-c {N} {k} (ab N x))) ie)

  -- The guard's instant and a child row's, mapped.
  inst-gc : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ R.Late N k → (instantOf g* ≡ instantOf (R.φ N k) ⇔ instantOf g ≡ instantOf k)
  inst-gc {N} x un nl =
    mk⇔ (λ h → trans ig (sym (Equivalence.to (Corr.home (R.corr N) x un nl) (trans (sym h) ig*))))
        (λ h → trans ig* (sym (Equivalence.from (Corr.home (R.corr N) x un nl) (trans (sym h) ig))))

  ⇔-sym : ∀ {a b c d : Pos} → (instantOf a ≡ instantOf b ⇔ instantOf c ≡ instantOf d) → (instantOf b ≡ instantOf a ⇔ instantOf d ≡ instantOf c)
  ⇔-sym h = mk⇔ (λ e → sym (Equivalence.to h (sym e))) (λ e → sym (Equivalence.from h (sym e)))

  corr′ : ∀ N → Corr p p* (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))
  corr′ N = record
    { row→ = row→′ N ; late-put = late-put′ N ; pin→ = pin→′ N ; put-before = put-before′ N ; pin-before = pin-before′ N
    ; shown← = shown←′ N ; place = place′ N
    ; mono = mono′ ; inst = inst′ ; home = home′ }
    where
      mono′ : ∀ {k k′ e e′} → TR (P′ N) k e → TR (P′ N) k′ e′ → Unpinned e → Unpinned e′ → ¬ Late′ N k → ¬ Late′ N k′ → k ≺ k′ → φ′ N k ≺ φ′ N k′
      mono′ {k} {k′} x x′ un un′ nl nl′ lt with tr-g→ g (P N) x | tr-g→ g (P N) x′
      ... | inj₁ (refl , _) | inj₁ (refl , _) = ⊥-elim (≺-irrefl {g} lt)
      ... | inj₁ (refl , _) | inj₂ x₁         = subst₂ _≺_ (sym (φ-g {N})) (sym (φ-c {N} {k′} (ab N x₁))) (ab-φ x₁ un′ (nl-c x₁ nl′))
      ... | inj₂ x₀         | inj₁ (refl , _) = ⊥-elim (≺-absurd {g} {k} (ab N x₀) lt)
      ... | inj₂ x₀         | inj₂ x₁         =
        subst₂ _≺_ (sym (φ-c {N} {k} (ab N x₀))) (sym (φ-c {N} {k′} (ab N x₁))) (Corr.mono (R.corr N) x₀ x₁ un un′ (nl-c x₀ nl) (nl-c x₁ nl′) lt)

      inst′ : ∀ {k k′ e e′} → TR (P′ N) k e → TR (P′ N) k′ e′ → Unpinned e → Unpinned e′ → ¬ Late′ N k → ¬ Late′ N k′
            → (instantOf (φ′ N k) ≡ instantOf (φ′ N k′) ⇔ instantOf k ≡ instantOf k′)
      inst′ {k} {k′} x x′ un un′ nl nl′ with tr-g→ g (P N) x | tr-g→ g (P N) x′
      ... | inj₁ (refl , _) | inj₁ (refl , _) = mk⇔ (λ _ → refl) (λ _ → refl)
      ... | inj₁ (refl , _) | inj₂ x₁         =
        subst₂ (λ a b → instantOf a ≡ instantOf b ⇔ instantOf g ≡ instantOf k′) (sym (φ-g {N})) (sym (φ-c {N} {k′} (ab N x₁))) (inst-gc x₁ un′ (nl-c x₁ nl′))
      ... | inj₂ x₀         | inj₁ (refl , _) =
        subst₂ (λ a b → instantOf a ≡ instantOf b ⇔ instantOf k ≡ instantOf g) (sym (φ-c {N} {k} (ab N x₀))) (sym (φ-g {N}))
               (⇔-sym {g*} {R.φ N k} {g} {k} (inst-gc x₀ un (nl-c x₀ nl)))
      ... | inj₂ x₀         | inj₂ x₁         =
        subst₂ (λ a b → instantOf a ≡ instantOf b ⇔ instantOf k ≡ instantOf k′) (sym (φ-c {N} {k} (ab N x₀))) (sym (φ-c {N} {k′} (ab N x₁)))
               (Corr.inst (R.corr N) x₀ x₁ un un′ (nl-c x₀ nl) (nl-c x₁ nl′))

      home′ : ∀ {k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → (instantOf (φ′ N k) ≡ instantOf p* ⇔ instantOf k ≡ instantOf p)
      home′ {k} x un nl with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = mk⇔ (λ _ → inst-⊕ p [ ix 0 ]) (λ _ → subst (λ z → instantOf z ≡ instantOf p*) (sym (φ-g {N})) (inst-⊕ p* [ ix 0 ]))
      ... | inj₂ x₀ =
        let φk = φ-c {N} {k} (ab N x₀) ; H = Corr.home (R.corr N) x₀ un (nl-c x₀ nl) in
        mk⇔ (λ h → trans (Equivalence.to H (trans (sym (cong instantOf φk)) (trans h (sym (inst-⊕ p* [ ix 1 ]))))) (inst-⊕ p [ ix 1 ]))
            (λ h → trans (cong instantOf φk) (trans (Equivalence.from H (trans h (sym (inst-⊕ p [ ix 1 ])))) (inst-⊕ p* [ ix 1 ])))

  rel′ : Rel P′ Q′ p p* S
  rel′ = record
    { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = corr′
    ; φ-agree = φ-agree′
    ; late-agree = late-agree′
    ; bk = λ N l → g ∷ R.bk N l
    ; in-bk = in-bk′
    ; pb-few = λ N l → proj₁ (R.pb-few N l) , λ pt → proj₂ (R.pb-few N l) (proj₂ pt)
    ; back = back′
    ; put-up = λ { {N} {N′} le gk gq* ag (ok , pl) → ok , R.put-up le gk gq* (ag-strip g (ab N′) (ab N) ag) pl }
    ; back-put = λ { {N} {N′} le gk gq* (ok , pl) ag* → ok , R.back-put le gk gq* pl (ag-strip g* (ab* N′) (ab* N) ag*) }
    ; elab-causal = elab-causal′
    ; stable← = stable←′
    ; stable-put = stable-put′
    ; stable-lead = stable-lead′
    ; elab-all = elab-all′
    ; func = λ {N} → func-g g (ab N) R.func
    ; func* = λ {N} → func-g g* (ab* N) R.func*
    ; flat = λ {N} → flat-g g (ab N) (und N) R.flat
    ; flat* = λ {N} → flat-g g* (ab* N) (und* N) R.flat*
    ; pin-in = λ {N} → pin-in-g g R.pin-in
    ; pin-in* = λ {N} → pin-in-g g* R.pin-in*
    ; cons = λ {N} {N′} → cons-g g (ab N) (ab N′) (R.cons {N} {N′})
    ; cons* = λ {N} {N′} → cons-g g* (ab* N) (ab* N′) (R.cons* {N} {N′})
    ; got = λ N → got-bind (λ b → ((g , skip) ∷ rows b) ⊣ short b) (R.got N)
    ; got* = λ N → got-bind (λ b → ((g* , skip) ∷ rows b) ⊣ short b) (R.got* N)
    ; after = after′
    ; after* = after*′
    ; after-φ = after-φ′
    ; pin-after* = pin-after*′
    ; pin-stable = pin-stable′ }
    where
      φ-agree′ : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Sc.G N N′ k → Sc.G* N N′ (φ′ N k)
               → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
      φ-agree′ {N} {N′} {k} x un nl gk gq* ag with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = trans (φ-g {N}) (sym (φ-g {N′}))
      ... | inj₂ x₀ =
        trans (φ-c {N} {k} (ab N x₀)) (trans (R.φ-agree x₀ un (nl-c x₀ nl) gk (g*-c x₀ gq*) (ag-strip g (ab N) (ab N′) ag)) (sym (φ-c {N′} {k} (ab N x₀))))

      late-agree′ : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Sc.G N N′ k → Sc.G* N N′ (φ′ N k)
                  → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → ¬ Late′ N′ k
      late-agree′ {N} {N′} {k} x un nl gk gq* ag with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = nl-g {N′}
      ... | inj₂ x₀ = λ lt → R.late-agree x₀ un (nl-c x₀ nl) gk (g*-c x₀ gq*) (ag-strip g (ab N) (ab N′) ag) (proj₂ lt)

      in-bk′ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ (g ∷ R.bk N (φ′ N k))
      in-bk′ {N} {k} x un nl with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = here refl
      ... | inj₂ x₀ = there (subst (λ z → k ∈ R.bk N z) (sym (φ-c {N} {k} (ab N x₀))) (R.in-bk x₀ un (nl-c x₀ nl)))

      back′ : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → ¬ Late′ N′ k → Sc.G N′ N k → Sc.G* N′ N (φ′ N′ k)
            → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      back′ {N} {N′} {k} le x un nl gk gq* ag* with tr-g→ g (P N′) x
      ... | inj₁ (refl , _) = ag-low g (ab N′) (ab N) (R.got N′) (R.got N)
      ... | inj₂ x₀ =
        let a₀ = ag-strip g* (ab* N′) (ab* N) (subst (λ z → AgreeTo z (TR (Q′ N′)) (TR (Q′ N))) (φ-c {N′} {k} (ab N′ x₀)) ag*)
        in ag-add g (R.got N′) (R.got N) (R.back le x₀ un (nl-c x₀ nl) gk (g*-c x₀ gq*) a₀)

      elab-causal′ : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Sc.G N′ N k → Sc.G* N′ N (φ′ N k)
                   → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      elab-causal′ {N} {N′} {k} le x un nl gk gq* ag with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = subst (λ z → AgreeTo z (TR (Q′ N′)) (TR (Q′ N))) (sym (φ-g {N})) (ag-low g* (ab* N′) (ab* N) (R.got* N′) (R.got* N))
      ... | inj₂ x₀ =
        subst (λ z → AgreeTo z (TR (Q′ N′)) (TR (Q′ N))) (sym (φ-c {N} {k} (ab N x₀)))
              (ag-add g* (R.got* N′) (R.got* N) (R.elab-causal le x₀ un (nl-c x₀ nl) gk (g*-c x₀ gq*) (ag-strip g (ab N′) (ab N) ag)))

      stable←′ : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Sc.G N′ N k → Sc.G* N′ N (φ′ N k)
               → TR (Q′ N) (φ′ N k) e′ → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      stable←′ {N} {N′} {k} {e′ = e′} le x un nl gk gq* y ag* with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = ag-low g (ab N′) (ab N) (R.got N′) (R.got N)
      ... | inj₂ x₀ =
        let φk = φ-c {N} {k} (ab N x₀)
            nl₀ = nl-c x₀ nl
            y₀ = strip g* (Q N) (ab-φ x₀ un nl₀) (subst (λ z → TR (Q′ N) z e′) φk y)
            a₀ = ag-strip g* (ab* N′) (ab* N) (subst (λ z → AgreeTo z (TR (Q′ N′)) (TR (Q′ N))) φk ag*)
        in ag-add g (R.got N′) (R.got N) (R.stable← le x₀ un nl₀ gk (g*-c x₀ gq*) y₀ a₀)

      stable-put′ : ∀ {N N′ k l e′} → N Data.Nat.≤ N′ → Sc.G N′ N k → Sc.G* N′ N l → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                  → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      stable-put′ {N} {N′} le gk gq* ag y (_ , pl) with tr-g→ g* (Q N) y
      ... | inj₁ (refl , _) = ag-low g* (ab* N′) (ab* N) (R.got* N′) (R.got* N)
      ... | inj₂ y₀ = ag-add g* (R.got* N′) (R.got* N) (R.stable-put le gk gq* (ag-strip g (ab N′) (ab N) ag) y₀ pl)

      stable-lead′ : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Sc.G N′ N k → Sc.G* N′ N (φ′ N k)
                   → TR (Q′ N) (φ′ N k) e′ → Leads′ N k
                   → TR (Q′ N) m e* → Sc.G* N′ N m → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N))
                   → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      stable-lead′ {N} {N′} {k} {e′ = e′} le x un nl gk gq* y ld z gm ie ag* with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym (φ-g {N})) (ag-low g* (ab* N′) (ab* N) (R.got* N′) (R.got* N))
      ... | inj₂ x₀ with tr-g→ g* (Q N) z
      ...   | inj₁ (refl , _) =
        ⊥-elim (ld (tr-g0 g (P N) (R.got N)) tt (Equivalence.to (inst-gc x₀ un (nl-c x₀ nl)) (trans ie (cong instantOf (φ-c {N} {k} (ab N x₀))))) (ab N x₀))
      ...   | inj₂ z₀ =
        let φk = φ-c {N} {k} (ab N x₀)
            nl₀ = nl-c x₀ nl
            y₀ = strip g* (Q N) (ab-φ x₀ un nl₀) (subst (λ w → TR (Q′ N) w e′) φk y)
        in subst (λ w → AgreeTo w (TR (Q′ N′)) (TR (Q′ N))) (sym φk)
                 (ag-add g* (R.got* N′) (R.got* N)
                   (R.stable-lead le x₀ un nl₀ gk (g*-c x₀ gq*) y₀ (leads← ld) z₀ gm (trans ie (cong instantOf φk)) (ag-strip g* (ab* N′) (ab* N) ag*)))

      elab-all′ : ∀ {N N′} → N Data.Nat.≤ N′ → (∀ q → Sc.G N′ N q) → (∀ q → Sc.G* N′ N q) → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N)))
                → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      elab-all′ {N} {N′} le gs gs* all y with tr-g→ g* (Q N′) y
      ... | inj₁ (refl , refl) = tr-g0 g* (Q N) (R.got* N)
      ... | inj₂ y₀ = tr-g← g* (Q N) (R.elab-all le gs gs* (λ q → ag-strip g (ab N′) (ab N) (all q)) y₀)

      p≼o : p ≼ o
      p≼o = ≺→≼ {p} {o} (≺-ext p [])

      p*≼o* : p* ≼ o*
      p*≼o* = ≺→≼ {p*} {o*} (≺-ext p* [])

      after′ : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      after′ {N} {k} x with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = ≺→≼ {p} {g} (≺-ext p [])
      ... | inj₂ x₀ = ≼-trans {p} {o} {k} p≼o (R.after x₀)

      after*′ : ∀ {N l e} → TR (Q′ N) l e → p* ≼ l
      after*′ {N} {l} y with tr-g→ g* (Q N) y
      ... | inj₁ (refl , _) = ≺→≼ {p*} {g*} (≺-ext p* [])
      ... | inj₂ y₀ = ≼-trans {p*} {o*} {l} p*≼o* (R.after* y₀)

      pin-after*′ : ∀ {N l r} → TR (Q′ N) l (pin r) → p* ≼ r
      pin-after*′ {N} {r = r} y with tr-g→ g* (Q N) y
      ... | inj₁ (_ , ())
      ... | inj₂ y₀ = ≼-trans {p*} {o*} {r} p*≼o* (R.pin-after* y₀)

      -- A child's pin, read off the guarded table.
      unguard : ∀ {X : Set} q (m : Maybe (Tb.Listed X)) {l r} → TR (Guarded q m) l (pin r) → TR m l (pin r)
      unguard q m y with tr-g→ q m y
      ... | inj₁ (_ , ())
      ... | inj₂ y₀ = y₀

      -- Below the guard no pin's connect lies: the child's lie past its
      -- subscription, the guard's second tick.
      pin-stable′ : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Sc.G N′ N k → Sc.G* N′ N (φ′ N k)
                  → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                  → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                  → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)
      pin-stable′ {N} {N′} {k} le x un nl gk gq* ag hp {y} {r} rk yq with tr-g→ g (P N) x
      ... | inj₁ (refl , _) =
        ⊥-elim (subst (r ≼_) (φ-g {N}) rk (≺-≼-≺ {g*} {o*} {r} (ticks p* 0) (R.pin-after* (unguard g* (Q N′) yq))))
      ... | inj₂ x₀ =
        tr-g← g* (Q N) (R.pin-stable le x₀ un (nl-c x₀ nl) gk (g*-c x₀ gq*) (ag-strip g (ab N′) (ab N) ag)
          (λ r₀k x₁ → unguard g (P N) (hp r₀k (tr-g← g (P N′) x₁)))
          (subst (r ≼_) (φ-c {N} {k} (ab N x₀)) rk) (unguard g* (Q N′) yq))

      after-φ′ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → p* ≼ φ′ N k
      after-φ′ {N} {k} x un nl with tr-g→ g (P N) x
      ... | inj₁ (refl , _) = subst (p* ≼_) (sym (φ-g {N})) (≺→≼ {p*} {g*} (≺-ext p* []))
      ... | inj₂ x₀ = subst (p* ≼_) (sym (φ-c {N} {k} (ab N x₀))) (≼-trans {p*} {o*} {R.φ N k} p*≼o* (R.after-φ x₀ un (nl-c x₀ nl)))

defer-tab : ∀ {A} p p* {P Q S} → Rel {A} P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) S
          → Rel (λ N → bind (P N) λ b → just (((p ⊕ [ ix 0 ] , skip) ∷ rows b) ⊣ short b))
                (λ N → bind (Q N) λ b → just (((p* ⊕ [ ix 0 ] , skip) ∷ rows b) ⊣ short b)) p p* S
defer-tab p p* R = DeferTab.rel′ p p* R

-- Children mapping alike, deferred alike.
defer-cong : ∀ {A} p p* {P Q S} (R R′ : Rel {A} P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) S)
           → (∀ N y → Same R R′ N y) → ∀ N y → Same (defer-tab p p* R) (defer-tab p p* R′) N y
defer-cong p p* R R′ e N y = same (guardφ-cong (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (λ y → φ≡ (e N y)) y) (λ { nl (o , lt) → nl→ (e N y) (λ lt₀ → nl (o , lt₀)) lt })
