{-# OPTIONS --guardedness #-}

-- AN APPROXIMANT NEVER LIES.  It stops short at a cut `defer`, whose spin
-- runs forever in one instant and shows nothing, but every value, mark
-- and end it shows is one the meaning shows, with the same past.  Before
-- a spin's instant it is the meaning; within it, a row past the spin's
-- first has endlessly many before it.  So wherever finitely many rows
-- precede, the approximant agrees with the meaning up to a row it shows
-- and up to the first row of an instant; and an approximant with
-- finitely many rows in all reached no cut, so it is the meaning.
--
-- Each approximant is read against the next (`Truth`), and the next
-- against the meaning by counting (`denotation.Laws.from`): a row with
-- `m` rows before it is the meaning's from the `m`-th approximant on.
--
-- Conversely the meaning is reached: up to a row with finitely many
-- before it, every deep enough approximant agrees with it (`reached`).
module denotation.Laws.Truthful where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import Tree using (Obs)
open import denotation.Position using (Pos; _∙_; ix; sub; last; instant; _⊕_)
open import denotation.Events using (Timeline; ix-<; <ᵖ-part; <ᵖ-below; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; EmissionSet; DenEnv; Few; Silent; _≺_; _≼_; enter; approx; ⟦_⟧)
open import denotation.Read using (Visible; loud)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻)
open import denotation.Laws.Count using (ag-cnt; ⊑?)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; _⊑_; ⊑-refl; ⊑-≼; ⊕-assoc; ⊕-identityʳ)
open import denotation.Laws using (from)

-- `x` opens its instant: no row of it lies before.
Opens : ∀ {A} → EmissionSet A → Pos → Set
Opens t x = ∀ {k e} → t k e → instant k ≡ instant x → x ≼ k

-- Finitely many rows in all.
Finite : ∀ {A} → EmissionSet A → Set
Finite t = Σ (List Pos) λ ks → ∀ {k e} → t k e → k ∈ ks

-- Finitely many before, under an agreement: the same ones.
few-ag : ∀ {A Q} {t t′ : EmissionSet A} {q} → AgreeTo Q t t′ → q ≼ Q → Few t q → Few t′ q
few-ag {Q = Q} {q = q} ag qQ (ks , h) = ks , λ {k} x kq → h (proj₂ (upto ag {k} (≺→≼ {k} {Q} (≺-≼-≺ {k} {q} {Q} kq qQ))) x) kq

-- A row shown, or an instant's first.
Safe : ∀ {A} → EmissionSet A → Pos → Set
Safe {A} t x = Opens t x ⊎ Σ (Ev A) λ e → t x e × Visible e

-- Safe, under an agreement: safe there too.
safe-ag : ∀ {A} {t t′ : EmissionSet A} {x} → AgreeTo x t t′ → Safe t x → Safe t′ x
safe-ag {t′ = t′} {x = x} ag (inj₁ op) = inj₁ λ {k} {e} tk eq → back (≼-or-≻ x k) tk eq
  where
    back : ∀ {k e} → x ≼ k ⊎ k ≺ x → t′ k e → instant k ≡ instant x → x ≼ k
    back (inj₁ xk) _ _ = xk
    back {k} (inj₂ kx) tk eq = ⊥-elim (op (proj₂ (upto ag {k} (≺→≼ {k} {x} kx)) tk) eq kx)
safe-ag {x = x} ag (inj₂ (e , tx , v)) = inj₂ (e , proj₁ (upto ag {x} (≼-refl {x})) tx , v)

------------------------------------------------------------------------
-- A spin's rows

-- Under a spin subscribed at `s`: under one of its rows `s ⊕ [ ix i ]`.
Spun : Pos → Pos → Set
Spun s y = Σ ℕ λ i → (s ⊕ [ ix i ]) ⊑ y

-- Under one past its first.
Lies : Pos → Pos → Set
Lies s y = Σ ℕ λ i → (s ⊕ [ ix (suc i) ]) ⊑ y

private
  instant-⊑ : ∀ {w y} → w ⊑ y → instant y ≡ instant w
  instant-⊑ {i ∙ _} (_ , refl) = refl

  instant-⊕ : ∀ s ys → instant (s ⊕ ys) ≡ instant s
  instant-⊕ (i ∙ _) _ = refl

  -- Under the first row, before every row under a later one.
  first-before : ∀ s {i z y} → (s ⊕ [ ix 0 ]) ⊑ z → (s ⊕ [ ix (suc i) ]) ⊑ y → z ≺ y
  first-before s {i} (u , refl) (v , refl) rewrite ⊕-assoc s [ ix 0 ] u | ⊕-assoc s [ ix (suc i) ] v =
    Equivalence.from T-≡ (<ᵖ-part s u v (ix-< {0} {suc i} (s≤s z≤n)))

-- Past every row of the spin.
past : ∀ s i → (s ⊕ [ ix i ]) ≺ (s ⊕ [ last ])
past s i = Equivalence.from T-≡ (<ᵖ-part s [] [] refl)

-- Before the spin, under it, or past all of it.
where? : ∀ s x → x ≺ (s ⊕ [ ix 0 ]) ⊎ Spun s x ⊎ (∀ i → (s ⊕ [ ix i ]) ≺ x)
where? s x with ≼-or-≻ (s ⊕ [ ix 0 ]) x
... | inj₂ xs = inj₁ xs
... | inj₁ sx with ⊑? s x
...   | no ns = inj₂ (inj₂ λ i → Equivalence.from T-≡ (<ᵖ-apart s x [ ix i ] (Equivalence.to T-≡ (≺-≼-≺ {s} {s ⊕ [ ix 0 ]} {x} (Equivalence.from T-≡ (<ᵖ-below s [])) sx)) λ ys eq → ns (ys , eq)))
...   | yes ([] , refl) = ⊥-elim (sx (subst (λ a → a ≺ (s ⊕ [ ix 0 ])) (sym (⊕-identityʳ s)) (Equivalence.from T-≡ (<ᵖ-below s []))))
...   | yes (ix j ∷ r , refl) = inj₂ (inj₁ (j , r , sym (⊕-assoc s [ ix j ] r)))
...   | yes (sub q ∷ r , refl) = inj₂ (inj₂ λ i → Equivalence.from T-≡ (<ᵖ-part s [] r refl))
...   | yes (last ∷ r , refl) = inj₂ (inj₂ λ i → Equivalence.from T-≡ (<ᵖ-part s [] r refl))

------------------------------------------------------------------------
-- One approximant against the next

-- THE NEXT APPROXIMANT, past the cuts.  Each cut `defer` (`Cut`) spins
-- at its subscription: every row under its spin is silent; none is
-- shown if a position past the whole spin has finitely many before it;
-- every row past its first row is joined by one under its first.
-- Wherever no row past a spin's first lies at or before a few-bounded
-- `x`, the next approximant agrees up to `x`.
record Truth {A : Set} (t t′ : EmissionSet A) : Set₁ where
  field
    Cut     : Pos → Set
    silent  : ∀ {s y e} → Cut s → Spun s y → t y e → Silent e
    blocked : ∀ {s x y e} → Cut s → (∀ i → (s ⊕ [ ix i ]) ≺ x) → Few t x → Spun s y → t y e → ⊥
    first   : ∀ {s y e} → Cut s → Lies s y → t y e → Σ Pos λ z → Σ (Ev A) λ e′ → (s ⊕ [ ix 0 ]) ⊑ z × t z e′
    agree   : ∀ {x} → Few t x → (∀ {s y e} → Cut s → Lies s y → y ≼ x → t y e → ⊥) → AgreeTo x t t′

module _ {A : Set} {t t′ : EmissionSet A} (tr : Truth t t′) where
  open Truth tr

  -- Nothing past a spin's first row lies at or before a safe row.
  private
    clear : ∀ {x} → Few t x → Safe t x → ∀ {s y e} → Cut s → Lies s y → y ≼ x → t y e → ⊥
    clear {x} F safe {s} {y} c (i , l) yx ty = at safe (where? s x) (first c (i , l) ty)
      where
        at : Safe t x → x ≺ (s ⊕ [ ix 0 ]) ⊎ Spun s x ⊎ (∀ j → (s ⊕ [ ix j ]) ≺ x)
           → (Σ Pos λ z → Σ (Ev A) λ e′ → (s ⊕ [ ix 0 ]) ⊑ z × t z e′) → ⊥
        at _ (inj₁ xs) _ =
          ≺→≼ {s ⊕ [ ix 0 ]} {s ⊕ [ ix (suc i) ]} (Equivalence.from T-≡ (<ᵖ-part s [] [] (ix-< {0} {suc i} (s≤s z≤n))))
            (≼-≺-≺ {s ⊕ [ ix (suc i) ]} {x} {s ⊕ [ ix 0 ]} (≼-trans {s ⊕ [ ix (suc i) ]} {y} {x} (⊑-≼ {s ⊕ [ ix (suc i) ]} {y} l) yx) xs)
        at _ (inj₂ (inj₂ after)) _ = blocked c after F (suc i , l) ty
        at (inj₂ (e₀ , tx , v)) (inj₂ (inj₁ (j , sx))) _ = loud v (silent c (j , sx) tx)
        at (inj₁ opens) (inj₂ (inj₁ (j , sx))) (z , e′ , z0 , tz) =
          opens tz (trans (trans (instant-⊑ z0) (instant-⊕ s [ ix 0 ])) (sym (trans (instant-⊑ sx) (instant-⊕ s [ ix j ]))))
            (≺-≼-≺ {z} {y} {x} (first-before s z0 l) yx)

  -- SAFE, THE NEXT: a few-bounded safe row's past is the next's.
  truth-lies : ∀ {x} → Few t x → Safe t x → AgreeTo x t t′
  truth-lies F safe = agree F (clear F safe)

  -- FINITE, THE NEXT: finitely many rows reach no cut.
  truth-finite : Finite t → ∀ {y e} → (t y e → t′ y e) × (t′ y e → t y e)
  truth-finite (ks , h) {y} = upto (agree (few y) none) (≼-refl {y})
    where
      few : ∀ x → Few t x
      few x = ks , λ tk _ → h tk

      none : ∀ {s y′ e′} → Cut s → Lies s y′ → y′ ≼ y → t y′ e′ → ⊥
      none {s} c (i , l) _ ty = blocked c (past s) (few (s ⊕ [ last ])) (suc i , l) ty

-- EACH APPROXIMANT IS THE NEXT, past its cuts.
--
-- DEAD ROUTE: an invariant on positions alone.  A connect whose source
--   spins under burst pins makes rows the next approximant drops, so the
--   induction must say which source cuts each operator reads.
-- DEAD ROUTE: a body reading a hot handle only after its source's cut
--   meets the cut with no row of its own, yet the next approximant shows
--   it the source's later rows: an open program's invariant carries its
--   environment's cuts, past which it claims nothing, and a connect turns
--   its source's cuts into its own by the burst or echo rows it shows.
postulate
  truth : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p
        → Truth (enter (approx n o ρ) p) (enter (approx (suc n) o ρ) p)

------------------------------------------------------------------------
-- The meaning

-- THE MEANING IS REACHED: up to a row with finitely many before it, every
-- approximant past their count agrees with the meaning.
reached : ∀ {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p
        → ∀ {q} → Few (enter (⟦ o ⟧ ρ) p) q
        → Σ ℕ λ N → ∀ m → N ≤ m → AgreeTo q (enter (⟦ o ⟧ ρ) p) (enter (approx m o ρ) p)
reached o ρ g p ok {q} (ks , h) =
  length ks , λ m le → ag-cnt (from m o ρ g p ok) q (inj₁ (ks , le , λ x kq → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h x kq))))

module _ {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) (g : GoodEnv ρ) (p : Pos) (ok : Ok (Hots ρ) p) where
  private
    T : ℕ → EmissionSet A
    T n = enter (approx n o ρ) p

    M : EmissionSet A
    M = enter (⟦ o ⟧ ρ) p

    -- Up to a row few in the `m`-th, by its own count: the meaning's.
    counted : ∀ m {x} (ks : List Pos) → length ks ≤ m → (∀ {k e} → T m k e → k ≺ x → k ∈ ks) → AgreeTo x M (T m)
    counted m {x} ks le h = ag-cnt (from m o ρ g p ok) x (inj₂ (ks , le , λ y kq → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h y kq))))

    -- Down the approximants from the `n`-th, the same few before `x`,
    -- still safe, and the same past.
    deeper : ∀ n {x} (ks : List Pos) → (∀ {y e} → T n y e → y ≺ x → y ∈ ks) → Safe (T n) x
           → ∀ k → (∀ {y e} → T (k + n) y e → y ≺ x → y ∈ ks) × Safe (T (k + n)) x × AgreeTo x (T n) (T (k + n))
    deeper n ks h safe zero = h , safe , ⟨ (λ _ → (λ a → a) , (λ a → a)) ⟩
    deeper n {x} ks h safe (suc k) with deeper n ks h safe k
    ... | h′ , s′ , ag = proj₂ (few-ag ag′ (≼-refl {x}) (ks , h′)) , safe-ag ag′ s′ , AgreeTo-trans ag ag′
      where
        ag′ : AgreeTo x (T (k + n)) (T (suc k + n))
        ag′ = truth-lies (truth (k + n) o ρ g p ok) (ks , h′) s′

    -- Down the approximants from a finite `n`-th, the same rows.
    finer : ∀ n (ks : List Pos) → (∀ {y e} → T n y e → y ∈ ks)
          → ∀ k → (∀ {y e} → T (k + n) y e → y ∈ ks) × (∀ {y e} → (T n y e → T (k + n) y e) × (T (k + n) y e → T n y e))
    finer n ks h zero = h , (λ a → a) , (λ a → a)
    finer n ks h (suc k) with finer n ks h k
    ... | h′ , eq = (λ x → h′ (proj₂ step x)) , (λ x → proj₁ step (proj₁ eq x)) , (λ x → proj₂ eq (proj₂ step x))
      where
        step : ∀ {y e} → (T (k + n) y e → T (suc k + n) y e) × (T (suc k + n) y e → T (k + n) y e)
        step = truth-finite (truth (k + n) o ρ g p ok) (ks , h′)

  -- NEVER A LIE, at a row shown or an instant's first.
  never-lies : ∀ n {x} → Few (T n) x → Safe (T n) x → AgreeTo x (T n) M
  never-lies n {x} (ks , h) safe with deeper n ks h safe (length ks)
  ... | h′ , _ , ag = AgreeTo-trans ag (AgreeTo-sym (counted (length ks + n) ks (m≤m+n (length ks) n) h′))

  -- FINITE, THE MEANING: an approximant with finitely many rows met no cut.
  finite-true : ∀ n → Finite (T n) → ∀ {y e} → (T n y e → M y e) × (M y e → T n y e)
  finite-true n (ks , h) {y} with finer n ks h (length ks)
  ... | h′ , eq = (λ x → proj₂ (upto ag {y} (≼-refl {y})) (proj₁ eq x)) , (λ x → proj₂ eq (proj₁ (upto ag {y} (≼-refl {y})) x))
    where
      ag : AgreeTo y M (T (length ks + n))
      ag = counted (length ks + n) ks (m≤m+n (length ks) n) (λ x _ → h′ x)
