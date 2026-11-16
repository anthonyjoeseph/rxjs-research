-- A POSITION MAP READ OFF A TRANSDUCER KEEPS THE ORDER.  A map that
-- walks a path label by label, from a state, writing a segment for each
-- label and a last segment where the path stops, keeps the order of
-- every two paths it walks when, in each state, the segments of two
-- different labels compare as the labels do whatever follows them, and
-- the last segment comes before every label's.  A position is mapped by
-- mapping its instant, a cascade's creator by the map itself, and its
-- path from the instant's own state: so the order of positions is kept
-- too, the creators' order included.
module simultaneous.Transducer where

open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Label; Instant; Pos; Path; _∙_; frame; cascade; Cmp; lt; eq; gt; lexi; cmpℕ;
  cmpLabel; cmpInstant; cmpPath; cmpPos; _≟ˡ_)
open import denotation.Simultaneity using (reflˡ; reflⁱ; reflᵗ; eqˡ; eqⁱ; flipᵗ; lexi-eq₁)

-- A common prefix compares as nothing.
cmp-++ : ∀ xs (p q : Path) → cmpPath (xs ++ p) (xs ++ q) ≡ cmpPath p q
cmp-++ []       p q = refl
cmp-++ (a ∷ xs) p q = trans (lexi-eq₁ (cmpLabel a a) _ (reflˡ a)) (cmp-++ xs p q)

-- A first difference decides.
lexi-ne : ∀ x y → ¬ x ≡ eq → lexi x y ≡ x
lexi-ne lt y _ = refl
lexi-ne gt y _ = refl
lexi-ne eq y n with n refl
... | ()

module Walk {S : Set} (σ : S → Label → Path) (δ : S → Label → S) (fin : S → Path) (ok : S → Label → Set) where

  walk : S → Path → Path
  walk s []      = fin s
  walk s (l ∷ π) = σ s l ++ walk (δ s l) π

  -- A path the transducer reads: every label allowed where it falls.
  Valid : S → Path → Set
  Valid s []      = ⊤
  Valid s (l ∷ π) = ok s l × Valid (δ s l) π

  record Good : Set where
    field
      split : ∀ {s l l′} x y → ok s l → ok s l′ → ¬ l ≡ l′ → cmpPath (σ s l ++ x) (σ s l′ ++ y) ≡ cmpLabel l l′
      first : ∀ {s l} x → ok s l → cmpPath (fin s) (σ s l ++ x) ≡ lt

  module _ (g : Good) where
    open Good g

    walk-cmp : ∀ s π π′ → Valid s π → Valid s π′ → cmpPath (walk s π) (walk s π′) ≡ cmpPath π π′
    walk-cmp s []      []        _       _         = reflᵗ (fin s)
    walk-cmp s []      (l ∷ π′)  _       (o , _)   = first (walk (δ s l) π′) o
    walk-cmp s (l ∷ π) []        (o , _) _         = flipᵗ (fin s) _ (first (walk (δ s l) π) o)
    walk-cmp s (l ∷ π) (l′ ∷ π′) (o , v) (o′ , v′) with l ≟ˡ l′
    ... | yes refl = trans (cmp-++ (σ s l) _ _) (trans (walk-cmp (δ s l) π π′ v v′) (sym (lexi-eq₁ (cmpLabel l l) _ (reflˡ l))))
    ... | no ne    = trans (split _ _ o o′ ne) (sym (lexi-ne (cmpLabel l l′) _ (λ h → ne (eqˡ l l′ h))))

-- A position's map: its instant's, the creator mapped by the map itself,
-- and its path walked from the instant's state.
module Map {S : Set} (σ : S → Label → Path) (δ : S → Label → S) (fin : S → Path) (ok : S → Label → Set)
           (start : Instant → S) where
  open Walk σ δ fin ok public

  mutual
    Φ : Pos → Pos
    Φ (i ∙ π) = Φⁱ i ∙ walk (start i) π

    Φⁱ : Instant → Instant
    Φⁱ frame           = frame
    Φⁱ (cascade t e l) = cascade t (Φ e) l

  mutual
    ValidP : Pos → Set
    ValidP (i ∙ π) = ValidI i × Valid (start i) π

    ValidI : Instant → Set
    ValidI frame           = ⊤
    ValidI (cascade _ e _) = ValidP e

  module _ (g : Good) where

    mutual
      -- THE MAP KEEPS THE ORDER of every two positions it reads.
      Φ-cmp : ∀ x y → ValidP x → ValidP y → cmpPos (Φ x) (Φ y) ≡ cmpPos x y
      Φ-cmp (i ∙ π) (j ∙ π′) (vi , v) (vj , v′) =
        trans (cong (λ c → lexi c (cmpPath (walk (start i) π) (walk (start j) π′))) (Φⁱ-cmp i j vi vj))
              (go (cmpInstant i j) refl)
        where
          go : ∀ c → cmpInstant i j ≡ c → lexi c (cmpPath (walk (start i) π) (walk (start j) π′)) ≡ lexi c (cmpPath π π′)
          go lt _ = refl
          go gt _ = refl
          go eq h = subst (λ k → cmpPath (walk (start i) π) (walk (start k) π′) ≡ cmpPath π π′) (eqⁱ i j h)
                      (walk-cmp g (start i) π π′ v (subst (λ k → Valid (start k) π′) (sym (eqⁱ i j h)) v′))

      Φⁱ-cmp : ∀ i j → ValidI i → ValidI j → cmpInstant (Φⁱ i) (Φⁱ j) ≡ cmpInstant i j
      Φⁱ-cmp frame           frame           _  _  = refl
      Φⁱ-cmp frame           (cascade _ _ _) _  _  = refl
      Φⁱ-cmp (cascade _ _ _) frame           _  _  = refl
      Φⁱ-cmp (cascade t e l) (cascade u d m) ve vd = cong (λ c → lexi (cmpℕ t u) (lexi c (cmpLabel l m))) (Φ-cmp e d ve vd)
