{-# OPTIONS --guardedness #-}

-- A SUBTERM'S ROWS BEFORE A POSITION, LISTED, under an environment whose
-- every handle is a functional hot listed there (`listed-in`).  Each hot
-- agrees below the position with the table of its rows there
-- (`denotation.Laws.hot-below`), so the program over the tables agrees
-- with it up to the position; cut at its count, that program is listed in
-- full (`simultaneous.Listing.listC`).
module simultaneous.ListedIn where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs)
open import denotation.Events using (Timeline)
open import denotation.Position using (Pos)
open import denotation.EmissionSet using (Ev; EmissionSet; hot; coldAt; enter; DenEnv; Few; approx)
open import denotation.Laws.Modulus using (_~⟨_⟩_)
open import denotation.Laws.Count using (Cnt; AgC; ag-cnt; AgC-sym)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; ⊑-refl)
open import denotation.Laws using (EnvAg; hot-below; ag-cons)
open import denotation.Laws.Cut using (capprox; cut-ne; causal-capprox)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; _⊣_; rejoin)
open import quickcheck.Tabled.Exact.Base using (Exactly)
open import quickcheck.Tabled.Exact using (truncate-exact; rejoin-exact; EnvRel; []; _∷_)
open import simultaneous.Listing using (Listed; UncutEnv; listC-ok; listC-exact; listed-exact; listed-ag)
open import simultaneous.Carry using (HotsListed)

-- One event per row.
Func : ∀ {A} → EmissionSet A → Set
Func t = ∀ {k e e′} → t k e → t k e′ → e ≡ e′

-- EVERY HANDLE A FUNCTIONAL HOT.
HotsFunc : ∀ {Γ} → DenEnv Γ → Set
HotsFunc []             = ⊤
HotsFunc (hot t ∷ ρ)    = Func t × HotsFunc ρ
HotsFunc (coldAt _ ∷ ρ) = ⊥

private
  -- The rows at the listed positions, one each.
  tab : ∀ {A} {t : EmissionSet A} (ks : List Pos) → (∀ {k} → k ∈ ks → Σ (Ev A) (t k)) → List (Row A)
  tab []       w = []
  tab (k ∷ ks) w = (k , proj₁ (w (here refl))) ∷ tab ks (λ m → w (there m))

  tab-sound : ∀ {A} {t : EmissionSet A} ks (w : ∀ {k} → k ∈ ks → Σ (Ev A) (t k)) {k e} → (k , e) ∈ tab ks w → t k e
  tab-sound (k ∷ ks) w (here refl) = proj₂ (w (here refl))
  tab-sound (k ∷ ks) w (there m)   = tab-sound ks (λ m′ → w (there m′)) m

  tab-complete : ∀ {A} {t : EmissionSet A} → Func t → ∀ ks (w : ∀ {k} → k ∈ ks → Σ (Ev A) (t k)) {k e} → t k e → k ∈ ks → (k , e) ∈ tab ks w
  tab-complete f (k ∷ ks) w x (here refl) with f x (proj₂ (w (here refl)))
  ... | refl = here refl
  tab-complete f (k ∷ ks) w x (there m) = there (tab-complete f ks (λ m′ → w (there m′)) x m)

  -- A listed hot, and the table of its rows before the position.
  module Hot {A} {t : EmissionSet A} {q} (f : Func t) (L : Listed t q) where
    w : ∀ {k} → k ∈ proj₁ L → Σ (Ev A) (t k)
    w m = proj₂ (proj₂ (proj₂ L) m)

    T : EmissionSet A
    T k e = (k , e) ∈ tab (proj₁ L) w

    l : Tb.Listed A
    l = tab (proj₁ L) w ⊣ false

    exact : ∀ p → Exactly (rejoin p l) (enter (hot T) p)
    exact p = truncate-exact (rejoin-exact {l = l} {t = T} (λ _ → record { sound = λ m → m ; complete = λ m → m }) p)

    agree : hot t ~⟨ q ⟩ hot T
    agree = hot-below (λ kq x → tab-complete f (proj₁ L) w x (proj₁ (proj₂ L) x kq)) (λ _ m → tab-sound (proj₁ L) w m)

  -- An environment of tables agreeing with it up to the position.
  record Tables {Γ} (ρ : DenEnv Γ) (q : Pos) : Set₁ where
    field
      ρL    : All Tb.Listed Γ
      ρD    : DenEnv Γ
      rel   : EnvRel ρL ρD
      uncut : UncutEnv ρL
      ag    : EnvAg q ρ ρD

  tables : ∀ {Γ} (ρ : DenEnv Γ) {q} → HotsFunc ρ → HotsListed ρ q → Tables ρ q
  tables []             _        _        = record { ρL = [] ; ρD = [] ; rel = [] ; uncut = tt ; ag = λ () }
  tables (hot t ∷ ρ)    (f , fs) (L , Ls) = record
    { ρL = Hot.l f L ∷ R.ρL ; ρD = hot (Hot.T f L) ∷ R.ρD ; rel = Hot.exact f L ∷ R.rel
    ; uncut = refl , R.uncut ; ag = ag-cons (Hot.agree f L) R.ag }
    where module R = Tables (tables ρ fs Ls)
  tables (coldAt _ ∷ ρ) ()       _

-- WHEREVER FINITELY MANY ROWS PRECEDE, THEY ARE LISTED, at a subterm whose
-- every handle is a functional hot listed there: the approximant is within
-- the count of its cut program, which agrees up to the position with the
-- cut program over the handles' tables.
listed-in : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → HotsFunc ρ
          → ∀ p → Ok (Hots ρ) p → ∀ {q} → HotsListed ρ q → Few (enter (approx n o ρ) p) q → Listed (enter (approx n o ρ) p) q
listed-in n o ρ g hf p ok {q} hl (ks , few) = listed-ag agq (listed-ag agc (listed-exact ex q))
  where
    module E = Tables (tables ρ hf hl)

    ag : AgC (length ks) (enter (approx n o ρ) p) (enter (capprox (suc (suc (length ks))) n o ρ) p)
    ag = AgC-sym (cut-ne {m = length ks} ≤-refl n o ρ g p ok)

    cnt : Cnt (length ks) (enter (approx n o ρ) p) q
    cnt = ks , ≤-refl , λ x lt → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (few x lt))

    agq = ag-cnt ag q (inj₁ cnt)
    agc = causal-capprox (suc (suc (length ks))) n o E.ag p

    lc = listC-ok (suc (suc (length ks))) n o E.uncut p
    ex = listC-exact (suc (suc (length ks))) n o E.rel p (proj₁ (proj₂ lc)) (proj₂ (proj₂ lc))
