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

open import Data.List using (List; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Data.Bool using (Bool; true; false; not) renaming (T to Tr)
open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet; Den; hot; DenEnv; Few; _≺_; enter; approx; ⟦_⟧; module Op)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; ≼-refl)
open import denotation.Laws.Count using (ag-cnt)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; InvD; Lawful; _∪ʰ_; ⊑-refl)
open import denotation.Laws.ConnectNe using (Causal)
open import denotation.Laws using (from; inv-approx; good-cons; causal-at)
open import denotation.Laws.Truth using (Finite; Rel; Safe; few-ag; safe-ag; spin-truth; truth-finite; truth-lies; placed-refl; Placed)
open import denotation.Laws.Truth.Ops using (defer-truth; map-truth; scan-truth; take-truth)
open import denotation.Laws.Truth.Flat using (flat-truth)
open import denotation.Laws.ShowsEv using (sk-approx)

-- EACH OPERATOR KEEPS THE TRUTH: every operator over children each
-- against the next.  A connect's body is read against its next under ONE
-- handle, and across the two handles by causality (`Causal`), as the
-- order modulus is (`settle`).
postulate
  connect-truth : ∀ {A B H} {s s′ : Den A} {F F′ : Den A → Den B}
                → InvD H s → InvD H s′
                → (∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) → (∀ {t} → Lawful t → InvD (H ∪ʰ t) (F′ (hot t)))
                → Causal F → Causal F′
                → Rel H s s′ → (∀ {t} → Lawful t → Rel (H ∪ʰ t) (F (hot t)) (F′ (hot t)))
                → Rel H (Op.connect s F) (Op.connect s′ F′)

-- EACH APPROXIMANT IS THE NEXT, past its cuts.
--
-- DEAD ROUTE: an invariant on positions alone.  A connect whose source
--   spins under burst pins makes rows the next approximant drops, so the
--   induction must say which source cuts each operator reads.
-- DEAD ROUTE: a connect's body against its next across the two handles.
--   A body reading the handle only after its source's cut meets the cut
--   with no row of its own, yet the next handle shows it the source's
--   later rows.
truth : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → Rel (Hots ρ) (approx n o ρ) (approx (suc n) o ρ)
truth n       (cold c)          ρ g p ok = placed-refl
truth n       empty             ρ g p ok = placed-refl
truth n       (of xs)           ρ g p ok = placed-refl
truth n       (map f s)         ρ g = map-truth f {approx n s ρ} {approx (suc n) s ρ} (truth n s ρ g)
truth n       (scan f z s)      ρ g = scan-truth f z {approx n s ρ} {approx (suc n) s ρ} (truth n s ρ g)
truth n       (takeWhile i k s) ρ g =
  take-truth i k {approx n s ρ} {approx (suc n) s ρ} (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (truth n s ρ g)
truth n       (flatMap op f s)  ρ g =
  flat-truth op (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (λ a → inv-approx n (f a) ρ g) (λ a → inv-approx (suc n) (f a) ρ g)
    (λ m q okq → sk-approx m n s ρ g q okq) (λ m a q okq → sk-approx m n (f a) ρ g q okq)
    (truth n s ρ g) (λ a → truth n (f a) ρ g)
truth n       (connect s b)     ρ g =
  connect-truth {s = approx n s ρ} {approx (suc n) s ρ} {λ h → approx n b (h ∷ ρ)} {λ h → approx (suc n) b (h ∷ ρ)}
    (inv-approx n s ρ g) (inv-approx (suc n) s ρ g)
    (λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx (suc n) b (hot t ∷ ρ) (good-cons L g))
    (causal-at n b ρ) (causal-at (suc n) b ρ)
    (truth n s ρ g) (λ {t} L → truth n b (hot t ∷ ρ) (good-cons L g))
truth n       (connected i)     ρ g p ok = placed-refl
truth zero    (defer l)         ρ g = spin-truth (inv-approx zero (Later.force l) ρ g)
truth (suc n) (defer l)         ρ g =
  defer-truth (inv-approx n (Later.force l) ρ g) (inv-approx (suc n) (Later.force l) ρ g) (truth n (Later.force l) ρ g)

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
        ag′ = truth-lies (Placed.tr (truth (k + n) o ρ g p ok)) (ks , h′) s′

    -- Down the approximants from a finite `n`-th, the same rows.
    finer : ∀ n (ks : List Pos) → (∀ {y e} → T n y e → y ∈ ks)
          → ∀ k → (∀ {y e} → T (k + n) y e → y ∈ ks) × (∀ {y e} → (T n y e → T (k + n) y e) × (T (k + n) y e → T n y e))
    finer n ks h zero = h , (λ a → a) , (λ a → a)
    finer n ks h (suc k) with finer n ks h k
    ... | h′ , eq = (λ x → h′ (proj₂ step x)) , (λ x → proj₁ step (proj₁ eq x)) , (λ x → proj₂ eq (proj₂ step x))
      where
        step : ∀ {y e} → (T (k + n) y e → T (suc k + n) y e) × (T (suc k + n) y e → T (k + n) y e)
        step = truth-finite (Placed.tr (truth (k + n) o ρ g p ok)) (ks , h′)

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
