{-# OPTIONS --guardedness #-}

-- CUTS BY TICK HAVE ONE MAP.  Where each cut holds the rows up to its
-- tick, the same rows at every cut reaching them, and an image keeps its
-- row's tick, the correspondences of the cuts (`Corr`, one per cut, each
-- along a map of its own) give every cut a correspondence along ONE map
-- (`Canon.canon`): a row's image at the cut of its own tick.  What
-- crosses between two cuts then needs nothing of the subterm: a row whose
-- image a cut holds, the cut holds (`Canon.settle`), an image of a row a
-- cut holds, the cut holds (`Canon.ahead`), and two cuts agree up to any
-- position either's tick reaches (`Canon.agree`).
--
-- Rows of different ticks are ordered by their ticks, on both sides, so
-- an order fact is read off one cut only between rows of one tick.
--
-- The cuts here differ in their tick alone.  A cut that also bounds a
-- hang's rows (`denotation.Laws.Cut.spinN`) holds the same rows as a
-- deeper one only up to the first hang either exhausts, which `mv` does
-- not say.
module simultaneous.TickCut where

open import Data.Bool using (T; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List)
open import Data.Nat using (ℕ; _<_; _≤_; _<ᵇ_; _≟_; _<?_)
open import Data.Nat.Properties using (<⇒<ᵇ; <ᵇ⇒<; <-asym; <-cmp; ≤-refl; ≤-reflexive; ≤-trans; ≮⇒≥; <-irrefl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position
  using (Pos; Instant; frame; cascade; _∙_; instant; root; _≟ᵖ_; inside; Cmp; cmpℕ; cmpInstant; cmpPos; cmpLabel; cmpPath; lexi; isLt)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; ≺→≼; ≺-absurd)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Shown; One; Live)
open import simultaneous.TableCorr using (Corr; nl-ev)
open import simultaneous.TableKit using (M)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- A position's tick

tickⁱ : Instant → ℕ
tickⁱ frame           = 0
tickⁱ (cascade t _ _) = t

tick : Pos → ℕ
tick p = tickⁱ (instant p)

private
  cmpℕ-lt : ∀ {m n} → m < n → cmpℕ m n ≡ Cmp.lt
  cmpℕ-lt {m} {n} lt with m <ᵇ n | <⇒<ᵇ lt
  ... | true | _ = refl

  cmpℕ-gt : ∀ {m n} → n < m → cmpℕ m n ≡ Cmp.gt
  cmpℕ-gt {m} {n} lt with m <ᵇ n | <ᵇ⇒< m n
  ... | true  | f = ⊥-elim (<-asym lt (f tt))
  ... | false | _ with n <ᵇ m | <⇒<ᵇ lt
  ...   | true | _ = refl

  cmpI-tick : ∀ i j → cmpInstant i j ≡ Cmp.eq → tickⁱ i ≡ tickⁱ j
  cmpI-tick frame           frame           _ = refl
  cmpI-tick (cascade t e a) (cascade u d b) h with <-cmp t u
  ... | tri≈ _ teq _ = teq
  ... | tri< lt _ _ with trans (sym (cong (λ c → lexi c (lexi (cmpPos e d) (cmpLabel a b))) (cmpℕ-lt lt))) h
  ...   | ()
  cmpI-tick (cascade t e a) (cascade u d b) h | tri> _ _ gt with trans (sym (cong (λ c → lexi c (lexi (cmpPos e d) (cmpLabel a b))) (cmpℕ-gt gt))) h
  ...   | ()

-- A later tick is later.
tick-≺ : ∀ k k′ → tick k < tick k′ → k ≺ k′
tick-≺ (frame ∙ p)         (cascade u d b ∙ q) _  = tt
tick-≺ (cascade t e a ∙ p) (cascade u d b ∙ q) lt =
  subst (λ c → T (isLt (lexi (lexi c (lexi (cmpPos e d) (cmpLabel a b))) (cmpPath p q)))) (sym (cmpℕ-lt lt)) tt

tick-mono : ∀ {y q} → y ≼ q → tick y ≤ tick q
tick-mono {y} {q} yq with tick q <? tick y
... | yes lt = ⊥-elim (yq (tick-≺ q y lt))
... | no ¬lt = ≮⇒≥ ¬lt

-- What lies under a position lies in its tick.
tick-in : ∀ r l → T (inside r l) → tick r ≡ tick l
tick-in (i ∙ r) (j ∙ k) w with cmpInstant i j in h
... | Cmp.eq = cmpI-tick i j h

------------------------------------------------------------------------
-- One map for every cut

module Canon {A : Set} (s s* : Pos)
  (L : ℕ → EmissionSet A) (L* : ℕ → EmissionSet (IE A))
  (φ : ℕ → Pos → Pos) (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set)
  (C : ∀ N → Corr s s* (φ N) (Put N) (Late N) (L N) (L* N))
  -- a cut holds the rows up to its tick, the same at every cut reaching them
  (low  : ∀ {N y e} → L N y e → tick y ≤ N)
  (low* : ∀ {N y e} → L* N y e → tick y ≤ N)
  (mv   : ∀ {N N′ y e} → tick y ≤ N′ → L N y e → L N′ y e)
  (mv*  : ∀ {N N′ y e} → tick y ≤ N′ → L* N y e → L* N′ y e)
  -- an image and a late placement keep the tick
  (tick-φ   : ∀ {N k e} → L N k e → Unpinned e → ¬ Late N k → tick (φ N k) ≡ tick k)
  (tick-put : ∀ {N k l} → Put N k l → tick l ≡ tick k)
  -- a pin lies under its connect
  (pin-in  : ∀ {N l r} → L N l (pin r) → T (inside r l))
  (pin-in* : ∀ {N l r} → L* N l (pin r) → T (inside r l))
  where

  φ′ : Pos → Pos
  φ′ k = φ (tick k) k

  Put′ : Pos → Pos → Set
  Put′ k l = Put (tick k) k l

  Late′ : Pos → Set
  Late′ k = Late (tick k) k

  -- A row at the cut of its own tick.
  own : ∀ {N y e} → L N y e → L (tick y) y e
  own = mv ≤-refl

  own* : ∀ {N y e} → L* N y e → L* (tick y) y e
  own* = mv* ≤-refl

  tφ : ∀ {N k e} → L N k e → Unpinned e → ¬ Late′ k → tick (φ′ k) ≡ tick k
  tφ x un nl = tick-φ (own x) un nl

  module _ (N : ℕ) where
    private
      Imaged : Pos → Ev A → Set
      Imaged k e = Σ (Ev (IE A)) λ e′ → L* N (φ′ k) e′ × M e e′

      Homed : Pos → Set
      Homed k = instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → L N k₀ e₀ × Unpinned e₀ × ¬ Late′ k₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

      Leads : Pos → Set
      Leads k = ∀ {k′ e′} → L N k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

      -- A row imaged at the cut of its tick, read at this one.
      carried : ∀ {n k e} → tick k ≡ n → n ≤ N → L n k e → Unpinned e → ¬ Late n k → Corr.Imaged (C n) k e
              → L N k e × ¬ Late′ k × Imaged k e
      carried refl le x un nl (e′ , y , m) = mv le x , nl , e′ , mv* (≤-trans (≤-reflexive (tick-φ x un nl)) le) y , m

      homed : ∀ {k} → tick k ≤ N → Corr.Homed (C (tick k)) k → Homed k
      homed le (inj₁ eq) = inj₁ eq
      homed le (inj₂ (k₀ , e₀ , x , un , nl , im , lt , eq)) =
        let (x′ , nl′ , im′) = carried (cong tickⁱ eq) le x un nl im in inj₂ (k₀ , e₀ , x′ , un , nl′ , im′ , lt , eq)

      putAt : ∀ {k} → tick k ≤ N → Corr.PutAt (C (tick k)) k → (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → L* N l e′ × Put′ k l) × Homed k
      putAt le ((l , e′ , y , pl) , h) = (l , e′ , mv* (≤-trans (≤-reflexive (tick-put pl)) le) y , pl) , homed le h

      live : ∀ {k} → tick k ≤ N → Live (L N) k → Live (L (tick k)) k
      live le lv xc = lv (mv (≤-trans (low xc) le) xc)

      live* : ∀ {m} → tick m ≤ N → Live (L* N) m → Live (L* (tick m)) m
      live* le lv yc = lv (mv* (≤-trans (low* yc) le) yc)

      -- A row a cut of its tick places, placed at this one.
      placed : ∀ {n k e m} → tick k ≡ n → n ≤ N → L n k e → Unpinned e → ¬ Late n k → Corr.Imaged (C n) k e
             → φ n k ≼ m ⊎ Corr.Leads (C n) k → instantOf (φ n k) ≡ instantOf m
             → Σ Pos λ k → Σ (Ev A) λ e → L N k e × Unpinned e × ¬ Late′ k × Imaged k e × (φ′ k ≼ m ⊎ Leads k) × instantOf (φ′ k) ≡ instantOf m
      placed {k = k} {e} {m} refl le x un nl im at ie =
        let (x′ , nl′ , im′) = carried refl le x un nl im in k , e , x′ , un , nl′ , im′ , lead at , ie
        where
          lead : φ′ k ≼ m ⊎ Corr.Leads (C (tick k)) k → φ′ k ≼ m ⊎ Leads k
          lead (inj₁ a) = inj₁ a
          lead (inj₂ ld) = inj₂ λ x″ un″ eq → ld (mv (≤-reflexive (cong tickⁱ eq)) x″) un″ eq

      -- A shown row's preimage at the cut of its tick, read at this one.
      shown : ∀ {n l k e} → tick l ≡ n → n ≤ N → l ≡ φ n k → L n k e → Unpinned e → ¬ Late n k
            → l ≡ φ′ k × L N k e × ¬ Late′ k
      shown {l = l} {k} {e} refl le eq x un nl = at (trans (cong tick eq) (tick-φ x un nl))
        where
          at : tick l ≡ tick k → l ≡ φ′ k × L N k e × ¬ Late′ k
          at teq = subst (λ n → l ≡ φ n k) teq eq , mv (subst (_≤ N) teq le) x , subst (λ n → ¬ Late n k) teq nl

    canon : Corr s s* φ′ Put′ Late′ (L N) (L* N)
    canon = record
      { row→ = row
      ; late-put = λ lt x → let (eq , pa) = Corr.late-put (C _) lt (own x) in eq , putAt (low x) pa
      ; pin→ = pinned
      ; put-before = λ {k} {l} {k′} x pl x′ un′ nl′ lt →
          before (λ b → Corr.put-before (C (tick k′)) (mv (≤-reflexive b) x) (subst (λ n → Put n k l) b pl) (own x′) un′ nl′ lt) pl x′ un′ nl′ lt
      ; pin-before = λ {k} {p} {l} {k′} x pl x′ un′ nl′ lt →
          before (λ b → Corr.pin-before (C (tick k′)) (mv (≤-reflexive b) x) (subst (λ n → Put n k l) b pl) (own x′) un′ nl′ lt) pl x′ un′ nl′ lt
      ; shown← = λ {l} y sh →
          let (k , e , eq , x , un , nl , m) = Corr.shown← (C (tick l)) (own* y) sh
              (eq′ , x′ , nl′) = shown refl (low* y) eq x un nl
          in k , e , eq′ , x′ , un , nl′ , m
      ; place = place
      ; mono = mono
      ; inst = inst
      ; home = λ x un nl → Corr.home (C _) (own x) un nl
      }
      where
        row : ∀ {k e} → L N k e → Unpinned e → (Imaged k e × ¬ Late′ k) ⊎ (e ≡ skip × ((Σ Pos λ l → Σ (Ev (IE A)) λ e′ → L* N l e′ × Put′ k l) × Homed k))
        row {k} x un with Corr.row→ (C (tick k)) (own x) un
        ... | inj₁ (im , nl) = let (_ , nl′ , im′) = carried refl (low x) (own x) un nl im in inj₁ (im′ , nl′)
        ... | inj₂ (eq , pa) = inj₂ (eq , putAt (low x) pa)

        pinned : ∀ {k p} → L N k (pin p) → Live (L N) k
               → (Σ Pos λ l → Σ Pos λ p′ → L* N l (pin p′) × Put′ k l × (∀ {k₀ a} → L N k₀ (out a) → φ′ k₀ ≺ p′ → k₀ ≺ p)) × Homed k
        pinned {k} {p} x lv with Corr.pin→ (C (tick k)) (own x) (live (low x) lv)
        ... | (l , p′ , y , pl , past) , h = (l , p′ , y′ , pl , past′) , homed (low x) h
          where
            y′ : L* N l (pin p′)
            y′ = mv* (≤-trans (≤-reflexive (tick-put pl)) (low x)) y

            tp : tick p ≡ tick k
            tp = tick-in p k (pin-in x)

            tp′ : tick p′ ≡ tick k
            tp′ = trans (tick-in p′ l (pin-in* y)) (tick-put pl)

            past′ : ∀ {k₀ a} → L N k₀ (out a) → φ′ k₀ ≺ p′ → k₀ ≺ p
            past′ {k₀} x₀ lt with <-cmp (tick k₀) (tick k)
            ... | tri< a _ _ = tick-≺ k₀ p (subst (tick k₀ <_) (sym tp) a)
            ... | tri≈ _ b _ = past (mv (≤-reflexive b) x₀) (subst (λ n → φ n k₀ ≺ p′) b lt)
            ... | tri> _ _ c = ⊥-elim (≺-absurd {φ′ k₀} {p′} lt
              (tick-≺ p′ (φ′ k₀) (subst (_< tick (φ′ k₀)) (sym tp′) (subst (tick k <_) (sym (tφ x₀ tt (nl-ev (C _) (own x₀) (λ ())))) c))))

        before : ∀ {k l k′ e′} → (tick k ≡ tick k′ → l ≼ φ′ k′) → Put′ k l → L N k′ e′ → Unpinned e′ → ¬ Late′ k′ → k ≺ k′ → l ≼ φ′ k′
        before {k} {l} {k′} same pl x′ un′ nl′ lt with <-cmp (tick k) (tick k′)
        ... | tri≈ _ b _ = same b
        ... | tri< a _ _ = ≺→≼ {l} {φ′ k′} (tick-≺ l (φ′ k′) (subst (_< tick (φ′ k′)) (sym (tick-put pl)) (subst (tick k <_) (sym (tφ x′ un′ nl′)) a)))
        ... | tri> _ _ c = ⊥-elim (≺-absurd {k} {k′} lt (tick-≺ k′ k c))

        place : ∀ {m e′} → L* N m e′ → Live (L* N) m
              → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev A) λ e → L N k e × Unpinned e × ¬ Late′ k × Imaged k e × (φ′ k ≼ m ⊎ Leads k) × instantOf (φ′ k) ≡ instantOf m
        place {m} y lv with Corr.place (C (tick m)) (own* y) (live* (low* y) lv)
        ... | inj₁ eq = inj₁ eq
        ... | inj₂ (k , e , x , un , nl , im , at , ie) =
          inj₂ (placed {m = m} (trans (sym (tick-φ x un nl)) (cong tickⁱ ie)) (low* y) x un nl im at ie)

        mono : ∀ {k k′ e e′} → L N k e → L N k′ e′ → Unpinned e → Unpinned e′ → ¬ Late′ k → ¬ Late′ k′ → k ≺ k′ → φ′ k ≺ φ′ k′
        mono {k} {k′} x x′ un un′ nl nl′ lt with <-cmp (tick k) (tick k′)
        ... | tri< a _ _ = tick-≺ (φ′ k) (φ′ k′) (subst (_< tick (φ′ k′)) (sym (tφ x un nl)) (subst (tick k <_) (sym (tφ x′ un′ nl′)) a))
        ... | tri≈ _ b _ = subst (λ n → φ n k ≺ φ′ k′) (sym b)
              (Corr.mono (C (tick k′)) (mv (≤-reflexive b) x) (own x′) un un′ (subst (λ n → ¬ Late n k) b nl) nl′ lt)
        ... | tri> _ _ c = ⊥-elim (≺-absurd {k} {k′} lt (tick-≺ k′ k c))

        inst : ∀ {k k′ e e′} → L N k e → L N k′ e′ → Unpinned e → Unpinned e′ → ¬ Late′ k → ¬ Late′ k′
             → (instantOf (φ′ k) ≡ instantOf (φ′ k′) ⇔ instantOf k ≡ instantOf k′)
        inst {k} {k′} x x′ un un′ nl nl′ with tick k ≟ tick k′
        ... | yes b = subst (λ n → instantOf (φ n k) ≡ instantOf (φ′ k′) ⇔ instantOf k ≡ instantOf k′) (sym b)
              (Corr.inst (C (tick k′)) (mv (≤-reflexive b) x) (own x′) un un′ (subst (λ n → ¬ Late n k) b nl) nl′)
        ... | no ¬b = mk⇔ (λ eq → ⊥-elim (¬b (trans (sym (tφ x un nl)) (trans (cong tickⁱ eq) (tφ x′ un′ nl′)))))
                          (λ eq → ⊥-elim (¬b (cong tickⁱ eq)))

  ------------------------------------------------------------------------
  -- Across two cuts

  -- A row whose image a cut holds, the cut holds.
  settle : ∀ {N N′ k e e′} → L N′ k e → Unpinned e → ¬ Late′ k → L* N (φ′ k) e′ → L N k e
  settle x un nl y = mv (subst (_≤ _) (tφ x un nl) (low* y)) x

  -- The image of a row a cut holds, the cut holds.
  ahead : ∀ {N N′ k e e′} → L N k e → Unpinned e → ¬ Late′ k → L* N′ (φ′ k) e′ → L* N (φ′ k) e′
  ahead x un nl y = mv* (subst (_≤ _) (sym (tφ x un nl)) (low x)) y

  -- A late placement of a row a cut holds, the cut holds.
  ahead-put : ∀ {N N′ k e l e′} → L N k e → Put′ k l → L* N′ l e′ → L* N l e′
  ahead-put x pl y = mv* (subst (_≤ _) (sym (tick-put pl)) (low x)) y

  -- Two cuts agree up to any position either's tick reaches.
  agree : ∀ {N N′ q} → tick q ≤ N → tick q ≤ N′ → AgreeTo q (L N) (L N′)
  agree {q = q} a b = ⟨ (λ {y} yq → mv (≤-trans (tick-mono {y} {q} yq) b) , mv (≤-trans (tick-mono {y} {q} yq) a)) ⟩

  agree* : ∀ {N N′ q} → tick q ≤ N → tick q ≤ N′ → AgreeTo q (L* N) (L* N′)
  agree* {q = q} a b = ⟨ (λ {y} yq → mv* (≤-trans (tick-mono {y} {q} yq) b) , mv* (≤-trans (tick-mono {y} {q} yq) a)) ⟩
