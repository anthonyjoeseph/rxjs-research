-- ORDER ACROSS AN EMBEDDING: carriers of two ordered points, neither
-- under the other, keep their order (`emb-≺`).  Two rows of a flat
-- reading are never one under the other (`row-apart`), and a later row
-- is over nothing in an earlier row's child's world (`row-kid`).
--
-- UP TO A POSITION, or past it and outside it (`upto-or`).
--
-- A LISTING'S VALUES, each with its row (`Outs`).
--
-- THE EARLIEST LISTED: a list searched for the earliest element a
-- decidable test picks, with what the search proves of the rest.
module simultaneous.FlatOrder where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Position using (Pos; _<ᵖ_; _⊕_)
open import denotation.EmissionSet using (Ev; out; end; skip; pin; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺→≼; ≺-irrefl; ≼-or-≻; ≼-antisym; ≼-refl; ≼-split; ≼-trans)
open import denotation.Laws.Worlds using (InvAt; Ok; W⁼; Plain; leads; same-lead; _⊑_; ⊑-refl; ⊑-snoc; ⊑-snoc⁺; ⊑-≼)
open import denotation.Laws.Count using (⊑?)
open import simultaneous.SimPos using (UpTo; apart)
open import simultaneous.Sim using (PMap; Emb)

------------------------------------------------------------------------
-- Order across an embedding

-- Under two ordered positions, neither under the other: ordered.
apart-⊑ : ∀ {y y′ x x′} → y ⊑ x → y′ ⊑ x′ → y ≺ y′ → ¬ y ⊑ y′ → x ≺ x′
apart-⊑ (σ , refl) (σ′ , refl) lt ny = apart lt ny σ σ′

-- Carriers of two ordered points, neither under the other.
emb-≺ : ∀ {M : PMap} (em : Emb M) {x x′ y y′ l l′} → M x y → M x′ y′ → y ⊑ l → y′ ⊑ l′ → x ≺ x′ → ¬ x ⊑ x′ → l ≺ l′
emb-≺ em {y = y} {y′} ay ay′ yl yl′ lt nx with ⊑? y y′
... | yes yy = ⊥-elim (nx (Emb.reflect em ay ay′ yy))
... | no ny  = apart-⊑ yl yl′ (Emb.mono em ay ay′ lt) ny

-- Two rows of a flat reading, one before the other: not one under it.
row-apart : ∀ {C H p} {X : EmissionSet C} → InvAt H p X → ∀ {q q′ e e′} → X q e → X q′ e′ → q ≺ q′ → ¬ q ⊑ q′
row-apart I {q} x x′ lt qq with same-lead I x x′ qq
... | refl = ≺-irrefl {q} lt

-- A later row of a reading lies over nothing in an earlier row's
-- child's world.
row-kid : ∀ {C H p} {X : EmissionSet C} → Ok H p → InvAt H p X → ∀ {q q′ e e′ l y} → X q e → X q′ e′ → Plain l
        → q ≺ q′ → W⁼ H (q ⊕ [ l ]) y → ¬ q′ ⊑ y
row-kid ok I {q} {q′} {l = l} x x′ pl lt = leads (proj₂ ok) (InvAt.world I x′) (λ u → InvAt.under I x x′ pl u (⊑-refl q′)) nr
  where
    nr : ¬ q′ ⊑ (q ⊕ [ l ])
    nr r with ⊑-snoc q r
    ... | inj₁ le   = ⊑-≼ {q′} {q} le lt
    ... | inj₂ refl = row-apart I x x′ lt (⊑-snoc⁺ q)

------------------------------------------------------------------------
-- Up to a position

-- Up to a position, or past it and outside it.
upto-or : ∀ y l → UpTo y l ⊎ (y ≺ l × ¬ y ⊑ l)
upto-or y l with T? (l <ᵖ y) | ⊑? y l
... | yes ly | _      = inj₁ (inj₁ ly)
... | no _   | yes yl = inj₁ (inj₂ yl)
... | no nly | no nyl with ≼-or-≻ l y
...   | inj₂ yl = inj₂ (yl , nyl)
...   | inj₁ ly with ≼-antisym {l} {y} ly nly
...     | refl = ⊥-elim (nyl (⊑-refl l))

-- At or before a position: before it, or it.
≼-elim : ∀ {k m} (P : Pos → Set) → k ≼ m → (k ≺ m → P k) → P m → P k
≼-elim {k} {m} P km f pm with ≼-split {k} {m} km
... | inj₁ lt   = f lt
... | inj₂ refl = pm

-- At or before a position: up to it.
upto-≼ : ∀ {k m} → k ≼ m → UpTo m k
upto-≼ {k} {m} km with ≼-split {k} {m} km
... | inj₁ lt   = inj₁ lt
... | inj₂ refl = inj₂ (⊑-refl k)

------------------------------------------------------------------------
-- A listing's values

module Outs {A : Set} (t : EmissionSet A) where

  Row : Set
  Row = Σ Pos λ q → Σ A λ a → t q (out a)

  add : ∀ q → Σ (Ev A) (t q) → List Row → List Row
  add q (out a , x) rs = (q , a , x) ∷ rs
  add q (end , _)   rs = rs
  add q (skip , _)  rs = rs
  add q (pin _ , _) rs = rs

  outs : (ks : List Pos) → (∀ {k} → k ∈ ks → Σ (Ev A) (t k)) → List Row
  outs []       _  = []
  outs (k ∷ ks) ev = add k (ev (here refl)) (outs ks (λ m → ev (there m)))

  add-here : ∀ q (w : Σ (Ev A) (t q)) rs {a} → proj₁ w ≡ out a → Σ Row λ r → r ∈ add q w rs × proj₁ r ≡ q
  add-here q (out a , x) rs refl = (q , a , x) , here refl , refl

  add-there : ∀ q (w : Σ (Ev A) (t q)) {rs r} → r ∈ rs → r ∈ add q w rs
  add-there q (out _ , _) m = there m
  add-there q (end , _)   m = m
  add-there q (skip , _)  m = m
  add-there q (pin _ , _) m = m

  -- Every listed value is kept, rows being functional.
  outs-∈ : (∀ {q e e′} → t q e → t q e′ → e ≡ e′) → ∀ ks (ev : ∀ {k} → k ∈ ks → Σ (Ev A) (t k)) {q a} → t q (out a) → q ∈ ks → Σ Row λ r → r ∈ outs ks ev × proj₁ r ≡ q
  outs-∈ fu (k ∷ ks) ev x (here refl) = add-here k (ev (here refl)) _ (fu (proj₂ (ev (here refl))) x)
  outs-∈ fu (k ∷ ks) ev x (there m) =
    let (r , i , e) = outs-∈ fu ks (λ m′ → ev (there m′)) x m in r , add-there k (ev (here refl)) i , e

------------------------------------------------------------------------
-- The earliest listed

module Earliest {X : Set} (key : X → Pos) {P : X → Set} (P? : ∀ x → Dec (P x)) where

  -- The earlier of two picked.
  earlier : ∀ x → P x → ∀ m → P m → key x ≼ key m ⊎ key m ≺ key x → Σ X P
  earlier x px _ _  (inj₁ _) = x , px
  earlier _ _  m pm (inj₂ _) = m , pm

  join : ∀ x → P x → Maybe (Σ X P) → Σ X P
  join x px nothing         = x , px
  join x px (just (m , pm)) = earlier x px m pm (≼-or-≻ (key x) (key m))

  step : ∀ x → Dec (P x) → Maybe (Σ X P) → Maybe (Σ X P)
  step x (yes px) r = just (join x px r)
  step x (no _)   r = r

  first : List X → Maybe (Σ X P)
  first []       = nothing
  first (x ∷ xs) = step x (P? x) (first xs)

  -- Nothing picked, or the earliest of those picked.
  Least : List X → Maybe (Σ X P) → Set
  Least xs nothing        = ∀ {x} → x ∈ xs → ¬ P x
  Least xs (just (m , _)) = ∀ {x} → x ∈ xs → P x → key m ≼ key x

  earlier-least : ∀ x px m pm xs (d : key x ≼ key m ⊎ key m ≺ key x) → (∀ {z} → z ∈ xs → P z → key m ≼ key z)
                → Least (x ∷ xs) (just (earlier x px m pm d))
  earlier-least x px m pm xs (inj₁ xm) h (here refl) _  = ≼-refl {key x}
  earlier-least x px m pm xs (inj₁ xm) h {z} (there i) pz = ≼-trans {key x} {key m} {key z} xm (h i pz)
  earlier-least x px m pm xs (inj₂ mx) h (here refl) _  = ≺→≼ {key m} {key x} mx
  earlier-least x px m pm xs (inj₂ mx) h (there i)   pz = h i pz

  step-least : ∀ x xs (d : Dec (P x)) (r : Maybe (Σ X P)) → Least xs r → Least (x ∷ xs) (step x d r)
  step-least x xs (yes px) nothing         h (here refl) _  = ≼-refl {key x}
  step-least x xs (yes px) nothing         h (there i)   pz = ⊥-elim (h i pz)
  step-least x xs (yes px) (just (m , pm)) h = earlier-least x px m pm xs (≼-or-≻ (key x) (key m)) h
  step-least x xs (no nx)  nothing         h (here refl) = nx
  step-least x xs (no nx)  nothing         h (there i)   = h i
  step-least x xs (no nx)  (just (m , pm)) h (here refl) px = ⊥-elim (nx px)
  step-least x xs (no nx)  (just (m , pm)) h (there i)   = h i

  least : ∀ xs → Least xs (first xs)
  least []       = λ ()
  least (x ∷ xs) = step-least x xs (P? x) (first xs) (least xs)
