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
open import Data.List.Relation.Unary.All using (_∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; n≮n; m≤n⇒m<n∨m≡n)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Data.Bool using (Bool; true; false; not) renaming (T to Tr)
open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; _∙_; ix; sub; last; instant; inside; _⊕_)
open import denotation.Events using (Timeline; ix-<; <ᵖ-part; <ᵖ-below; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; hot; DenEnv; Few; Dep; Reach; Truncate; Silent; hush; held; Spin; spin; DeferT; guard; body; MapT; map-out; map-skip; map-pin; map-end; module Scan; module TakeWhile; PDep; _≺_; _≼_; enter; approx; ⟦_⟧; module Op)
open import denotation.Read using (Visible; loud)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≼-split; ≺-irrefl; ≺-trans; ticks; reach-via; entered-reach; entered-few; few-ind; ≺-ext)
open import denotation.Laws.Count using (Cov; ag-cnt; ⊑?; cov-down; dep-trans; cov-stable; em)
open import denotation.Laws.Worlds using (ok-step; Ok; Hots; GoodEnv; InvD; Lawful; _∪ʰ_; _⊑_; ⊑-refl; ⊑-≼; ⊕-assoc; ⊕-identityʳ; inside-⊑; ⊑-trans; ⊑-cmp; ⊑-snoc; ⊑-snoc⁺; conv; InvAt)
open import denotation.Laws.Cut using (module SpinB; spinIx; ix-back)
open import denotation.Laws.ConnectNe using (Causal)
open import denotation.Laws using (from; inv-approx; good-cons; causal-at; aft; scan-ag)
open import denotation.Laws.Fold using (fold)

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

private
  -- Past a row of a subtree, and not in it: past all of it.
  past-sub : ∀ {s w y z} → s ⊑ w → w ≺ y → ¬ s ⊑ y → s ⊑ z → z ≺ y
  past-sub {s} {w} {y} {z} sw wy ny sz with ≼-or-≻ y z
  ... | inj₂ zy = zy
  ... | inj₁ yz with ≼-split {y} {z} yz
  ...   | inj₁ lt   = ⊥-elim (ny (conv sw (≺→≼ {w} {y} wy) lt sz))
  ...   | inj₂ refl = ⊥-elim (ny sz)

  -- Under one spin row, before every later one.
  below-next : ∀ s {a b z} → (s ⊕ [ ix a ]) ⊑ z → a < b → z ≺ (s ⊕ [ ix b ])
  below-next s {a} {b} (zs , refl) lt rewrite ⊕-assoc s [ ix a ] zs = Equivalence.from T-≡ (<ᵖ-part s zs [] (ix-< lt))

------------------------------------------------------------------------
-- One approximant against the next

-- Under a row past the first of a cut's spin.
Lie : (Pos → Set) → Pos → Set
Lie C y = Σ Pos λ s → C s × Lies s y

-- CLEAN: not past a cut's first row, nor is anything it waits on, and
-- finitely many positions cover what it waits on.
Clean : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Ev A → Set
Clean C t q e = ¬ Lie C q × Σ (List Pos) λ ks → ∀ {k e′} → t k e′ → k ≺ q → Dep q e k e′ → Cov q ks k × ¬ Lie C k

-- Clean before `r`: finitely many positions cover the rows before it,
-- none past a cut's first.
Before : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
Before C t r = Σ (List Pos) λ ks → ∀ {k e′} → t k e′ → k ≺ r → Cov r ks k × ¬ Lie C k

-- Past a cut's first, so is what lies under.
lie-up : ∀ {C y z} → Lie C y → y ⊑ z → Lie C z
lie-up (c , cc , j , l) yz = c , cc , j , ⊑-trans l yz

-- Clean before, clean before what comes earlier.
before-down : ∀ {A C} {u : EmissionSet A} {b g} → Before C u b → g ≼ b → Before C u g
before-down {b = b} {g} (ks , h) gb = ks , λ {k} x kg → let a = h x (≺-≼-≺ {k} {g} {b} kg gb) in cov-down (proj₁ a) kg gb , proj₂ a

-- Clean before and not past a cut's first: clean.
clean-of : ∀ {A C} {u : EmissionSet A} {g e} → Before C u g → ¬ Lie C g → Clean C u g e
clean-of (ks , h) nl = nl , ks , λ x kg _ → h x kg

-- Clean, clean before what it waits on all of.
before-of : ∀ {A C} {u : EmissionSet A} {q e b} → Clean C u q e → b ≼ q → (∀ {k e₀} → k ≺ b → Dep q e k e₀) → Before C u b
before-of {q = q} {b = b} (_ , ks , h) bq dp = ks , λ {k} x kb → let a = h x (≺-≼-≺ {k} {b} {q} kb bq) (dp kb) in cov-down (proj₁ a) kb bq , proj₂ a

-- THE NEXT APPROXIMANT, past the cuts.  Each cut `defer` (`Cut`) spins
-- at its subscription: every row under its spin is silent, and each of
-- its rows shows.  A pin past its first, of a connect leading the cut,
-- recurs under each; one the next shows there, clean before its connect,
-- shows under its second.  Wherever a row is clean, the next has it too,
-- and nothing else there.
record Truth {A : Set} (t t′ : EmissionSet A) : Set₁ where
  field
    Cut     : Pos → Set
    silent  : ∀ {s y e} → Cut s → Spun s y → t y e → Silent e
    shows   : ∀ {s} → Cut s → ∀ i → Σ Pos λ z → Σ (Ev A) λ e → (s ⊕ [ ix i ]) ⊑ z × t z e
    again   : ∀ {s w r} → Cut s → t w (pin r) → Lies s w → r ⊑ s → ∀ i → Σ Pos λ z → (s ⊕ [ ix i ]) ⊑ z × t z (pin r)
    shadow  : ∀ {s w r} → Cut s → t′ w (pin r) → Lies s w → r ⊑ s → Before Cut t r → Σ Pos λ z → (s ⊕ [ ix 1 ]) ⊑ z × t z (pin r)
    agree   : ∀ q e → Clean Cut t q e → (t q e → t′ q e) × (t′ q e → t q e)

module _ {A : Set} {t t′ : EmissionSet A} (tr : Truth t t′) where
  open Truth tr

  private
    -- Past the whole spin, endlessly many rows before.
    blocked : ∀ {s x} → Cut s → (∀ i → (s ⊕ [ ix i ]) ≺ x) → Few t x → ⊥
    blocked {s} {x} c after (ks , h) = n≮n (length ks) (SpinB.bound {A} s (spin (suc (length ks))) (suc (length ks)) ks ≤-refl cov)
      where
        cov : ∀ {k e} (y : Spin s k e) → spinIx y < suc (length ks) → Any (k ⊑_) ks
        cov (spin j) _ with shows c j
        ... | z , _ , sz , tz = Any.map (λ { refl → sz }) (h tz (≺-trans {z} {s ⊕ [ ix (suc j) ]} {x} (below-next s sz ≤-refl) (after (suc j))))

    -- Nothing at or before a safe few-bounded row lies past a cut's first.
    clear : ∀ {x} → Few t x → Safe t x → ∀ {y} → y ≼ x → ¬ Lie Cut y
    clear {x} F safe {y} yx (s , c , i , l) = at safe (where? s x) (shows c 0)
      where
        at : Safe t x → x ≺ (s ⊕ [ ix 0 ]) ⊎ Spun s x ⊎ (∀ j → (s ⊕ [ ix j ]) ≺ x)
           → (Σ Pos λ z → Σ (Ev A) λ e′ → (s ⊕ [ ix 0 ]) ⊑ z × t z e′) → ⊥
        at _ (inj₁ xs) _ =
          ≺→≼ {s ⊕ [ ix 0 ]} {s ⊕ [ ix (suc i) ]} (Equivalence.from T-≡ (<ᵖ-part s [] [] (ix-< {0} {suc i} (s≤s z≤n))))
            (≼-≺-≺ {s ⊕ [ ix (suc i) ]} {x} {s ⊕ [ ix 0 ]} (≼-trans {s ⊕ [ ix (suc i) ]} {y} {x} (⊑-≼ {s ⊕ [ ix (suc i) ]} {y} l) yx) xs)
        at _ (inj₂ (inj₂ after)) _ = blocked c after F
        at (inj₂ (e₀ , tx , v)) (inj₂ (inj₁ (j , sx))) _ = loud v (silent c (j , sx) tx)
        at (inj₁ opens) (inj₂ (inj₁ (j , sx))) (z , e′ , z0 , tz) =
          opens tz (trans (trans (instant-⊑ z0) (instant-⊕ s [ ix 0 ])) (sym (trans (instant-⊑ sx) (instant-⊕ s [ ix j ]))))
            (≺-≼-≺ {z} {y} {x} (first-before s z0 l) yx)

    -- With finitely many rows, nothing lies past a cut's first.
    none : Finite t → ∀ {y} → ¬ Lie Cut y
    none (ks , h) (s , c , _) = blocked c (past s) (ks , λ tk _ → h tk)

  -- SAFE, THE NEXT: a few-bounded safe row's past is the next's.
  truth-lies : ∀ {x} → Few t x → Safe t x → AgreeTo x t t′
  truth-lies {x} F@(ks , h) safe = ⟨ (λ {y} {e} yx → agree y e (clear F safe yx , ks , λ {k} tk ky _ →
    inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h tk (≺-≼-≺ {k} {y} {x} ky yx))) , clear F safe (≼-trans {k} {y} {x} (≺→≼ {k} {y} ky) yx))) ⟩

  -- FINITE, THE NEXT: finitely many rows reach no cut.
  truth-finite : Finite t → ∀ {y e} → (t y e → t′ y e) × (t′ y e → t y e)
  truth-finite fin@(ks , h) {y} {e} =
    agree y e (none fin , ks , λ tk _ _ → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h tk)) , none fin)

  -- Clean, so is what it waits on, if it does not lie.
  clean-down : ∀ {q e w e′} → Clean Cut t q e → w ≺ q → Dep q e w e′ → ¬ Lie Cut w → Clean Cut t w e′
  clean-down {q} {e} {w} {e′} (_ , ks , h) wq d nw = nw , ks , down
    where
      down : ∀ {k e″} → t k e″ → k ≺ w → Dep w e′ k e″ → Cov w ks k × ¬ Lie Cut k
      down {k} y kw d′ with h y (≺-trans {k} {w} {q} kw wq) (dep-trans {k = k} kw wq d d′)
      ... | cv , nk = cov-down cv kw (≺→≼ {w} {q} wq) , nk

  private
    -- A row of the next past a cut's first, that a row not past it waits
    -- on: that row waits on one of these past it too.
    dirty : ∀ {q e w e′} → Clean Cut t q e → Lie Cut w → t′ w e′ → w ≺ q → Dep q e w e′
          → Σ Pos λ z → Σ (Ev A) λ e″ → Lie Cut z × t z e″ × z ≺ q × Dep q e z e″
    dirty {q} {e} {w} {e′} (nq , ks , h) (s , c , i , sw) x wq d = go e e′ h x d
      where
        S : Pos
        S = s ⊕ [ ix (suc i) ]

        nSq : ¬ S ⊑ q
        nSq l = nq (s , c , i , l)

        before : ∀ {a z y} → a ≤ suc i → (s ⊕ [ ix a ]) ⊑ z → w ≺ y → ¬ S ⊑ y → z ≺ y
        before {a} {z} {y} le za wy ny with m≤n⇒m<n∨m≡n le
        ... | inj₂ refl = past-sub sw wy ny za
        ... | inj₁ lt   = ≺-trans {z} {w} {y} (≺-≼-≺ {z} {S} {w} (below-next s za lt) (⊑-≼ {S} {w} sw)) wy

        one : Σ Pos λ z → Σ (Ev A) λ e″ → (s ⊕ [ ix 1 ]) ⊑ z × t z e″
        one = shows c 1

        z₁ : Pos
        z₁ = proj₁ one

        lie₁ : Lie Cut z₁
        lie₁ = s , c , 0 , proj₁ (proj₂ (proj₂ one))

        t₁ : t z₁ (proj₁ (proj₂ one))
        t₁ = proj₂ (proj₂ (proj₂ one))

        under₁ : ∀ {y} → w ≺ y → ¬ S ⊑ y → z₁ ≺ y
        under₁ wy ny = before (s≤s z≤n) (proj₁ (proj₂ (proj₂ one))) wy ny

        go : ∀ e e′ → (∀ {k e″} → t k e″ → k ≺ q → Dep q e k e″ → Cov q ks k × ¬ Lie Cut k)
           → t′ w e′ → Dep q e w e′ → Σ Pos λ z → Σ (Ev A) λ e″ → Lie Cut z × t z e″ × z ≺ q × Dep q e z e″
        go (out _) _ _ _ _ = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , tt
        go skip    _ _ _ _ = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , tt
        go end     _ _ _ _ = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , tt
        go (pin r) e′ h x d with T? (inside r q)
        ... | no ni = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , λ ins → ⊥-elim (ni ins)
        ... | yes ins = by (d ins) x
          where
            rq : r ⊑ q
            rq = inside-⊑ r q ins

            nSr : ¬ S ⊑ r
            nSr l = nSq (⊑-trans l rq)

            bf : Before Cut t r
            bf = ks , λ {k} y kr → let a = h y (≺-≼-≺ {k} {r} {q} kr (⊑-≼ rq)) (λ _ → inj₁ kr) in cov-down (proj₁ a) kr (⊑-≼ rq) , proj₂ a

            early : w ≺ r → Σ Pos λ z → Σ (Ev A) λ e″ → Lie Cut z × t z e″ × z ≺ q × Dep q (pin r) z e″
            early wr = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , λ _ → inj₁ (under₁ wr nSr)

            by : w ≺ r ⊎ e′ ≡ pin r → t′ w e′ → Σ Pos λ z → Σ (Ev A) λ e″ → Lie Cut z × t z e″ × z ≺ q × Dep q (pin r) z e″
            by (inj₁ wr)   _ = early wr
            by (inj₂ refl) x with ≼-or-≻ r w
            ... | inj₂ wr = early wr
            ... | inj₁ rw with ⊑-cmp r S (conv (⊑-refl r) rw wq rq) sw
            ...   | inj₂ Sr = ⊥-elim (nSr Sr)
            ...   | inj₁ rS with ⊑-snoc s rS
            ...     | inj₂ refl = ⊥-elim (nSr (⊑-refl _))
            ...     | inj₁ rs with shadow c x (i , sw) rs bf
            ...       | z , z1 , tz = z , pin r , (s , c , 0 , z1) , tz , before (s≤s z≤n) z1 wq nSq , λ _ → inj₂ refl

  -- WHAT A CLEAN ROW WAITS ON IN THE NEXT, THIS ONE HAS.
  pull : ∀ {q e w e′} → Clean Cut t q e → t′ w e′ → w ≺ q → Dep q e w e′ → t w e′
  pull {q} {e} {w} {e′} cl@(nq , ks , h) x wq d = proj₂ (agree w e′ (clean-down cl wq d nw)) x
    where
      nw : ¬ Lie Cut w
      nw lw with dirty cl lw x wq d
      ... | z , _ , lz , tz , zq , dz = proj₂ (h tz zq dz) lz

-- Nothing cut: the same rows.
truth-refl : ∀ {A} {t : EmissionSet A} → Truth t t
truth-refl = record
  { Cut     = λ _ → ⊥
  ; silent  = λ ()
  ; shows   = λ ()
  ; again   = λ ()
  ; shadow  = λ ()
  ; agree   = λ _ _ _ → (λ a → a) , (λ a → a)
  }

-- Every admissible subscription of `d′` is that of `d`, past its cuts.
Rel : ∀ {A} → (Pos → Set) → Den A → Den A → Set₁
Rel H d d′ = ∀ p → Ok H p → Truth (enter d p) (enter d′ p)

------------------------------------------------------------------------
-- A cut against its unfolding

private
  -- The spin's rows before its `i`-th.
  spins : Pos → ℕ → List Pos
  spins p zero    = []
  spins p (suc i) = (p ⊕ [ ix i ]) ∷ spins p i

  spins-∈ : ∀ p {i j} → j < i → (p ⊕ [ ix j ]) ∈ spins p i
  spins-∈ p {suc i} {j} (s≤s le) with m≤n⇒m<n∨m≡n le
  ... | inj₁ lt   = there (spins-∈ p lt)
  ... | inj₂ refl = here refl

  spin-reach : ∀ {A} p i → Reach (Spin {A} p) (p ⊕ [ ix i ]) skip
  spin-reach p i = spins p i , λ { (spin j) lt _ → spins-∈ p (ix-back p lt) }

  -- The guard waits on nothing: the body lies past it.
  guarded : ∀ {A H} (d : Den A) → InvD H d → ∀ p → Ok H p → Reach (DeferT d p) (p ⊕ [ ix 0 ]) skip
  guarded d inv p ok = [] , λ { guard lt _ → ⊥-elim (≺-irrefl {p ⊕ [ ix 0 ]} lt)
                              ; (body {y} x) lt _ → ⊥-elim (proj₁ (aft d inv p ok x) (≺-trans {y} {p ⊕ [ ix 0 ]} {p ⊕ [ ix 1 ]} lt (ticks p 0))) }

-- A CUT IS ITS SPIN: the unfolding's guard is the spin's first row, and
-- its body lies at or past the second, which every row past it waits on.
spin-truth : ∀ {A H} {d : Den A} → InvD H d → Rel H Op.⊥ (Op.defer d)
spin-truth {A} {H} {d} inv p ok = record
  { Cut     = _≡ p
  ; silent  = λ { refl _ (spin _ , _) → hush }
  ; shows   = λ { refl i → p ⊕ [ ix i ] , skip , ⊑-refl _ , spin i , spin-reach p i }
  ; again   = λ { refl (() , _) }
  ; shadow  = λ { refl (body x , _) _ rp _ → ⊥-elim (proj₂ (aft d inv p ok x) refl (≼-≺-≺ {_} {p} {b₀} (⊑-≼ rp) (Equivalence.from T-≡ (<ᵖ-below p [])))) }
  ; agree   = λ q e c → to c , back c
  }
  where
    b₀ : Pos
    b₀ = p ⊕ [ ix 1 ]

    to : ∀ {q e} → Clean (_≡ p) (Truncate (Spin p)) q e → Truncate (Spin p) q e → Truncate (DeferT d p) q e
    to _        (spin zero , _)    = guard , guarded d inv p ok
    to (nl , _) (spin (suc j) , _) = ⊥-elim (nl (p , refl , j , ⊑-refl _))

    back : ∀ {q e} → Clean (_≡ p) (Truncate (Spin p)) q e → Truncate (DeferT d p) q e → Truncate (Spin p) q e
    back _ (guard , _) = spin 0 , spin-reach p 0
    back {q} {e} (nl , ks , h) (body x , _) = waits (aft d inv p ok x)
      where
        under : b₀ ⊑ q → ⊥
        under l = nl (p , refl , 0 , l)

        dep : ∀ {e′} → (∀ {r} → e′ ≡ pin r → b₀ ≼ r) → Dep q e′ b₀ skip
        dep {e′ = out _} _ = tt
        dep {e′ = skip}  _ = tt
        dep {e′ = end}   _ = tt
        dep {e′ = pin r} br i with ≼-split {b₀} {r} (br refl)
        ... | inj₁ lt   = inj₁ lt
        ... | inj₂ refl = ⊥-elim (under (inside-⊑ b₀ q i))

        waits : b₀ ≼ q × (∀ {r} → e ≡ pin r → b₀ ≼ r) → Truncate (Spin p) q e
        waits (bq , br) with ≼-split {b₀} {q} bq
        ... | inj₂ refl = ⊥-elim (under (⊑-refl _))
        ... | inj₁ lt   = ⊥-elim (proj₂ (h (spin 1 , spin-reach p 1) lt (dep br)) (p , refl , 0 , ⊑-refl _))

------------------------------------------------------------------------
-- Operators that relabel rows where they lie

private
  -- The same kind of row, values aside.
  data Lbl {A B : Set} : Ev A → Ev B → Set where
    l-out  : ∀ {a b} → Lbl (out a) (out b)
    l-skip : Lbl skip skip
    l-pin  : ∀ {r} → Lbl (pin r) (pin r)
    l-end  : Lbl end end

  lbl-sym : ∀ {A B} {e₀ : Ev A} {e : Ev B} → Lbl e₀ e → Lbl e e₀
  lbl-sym l-out  = l-out
  lbl-sym l-skip = l-skip
  lbl-sym l-pin  = l-pin
  lbl-sym l-end  = l-end

  -- What a row waits on is read off the kinds alone.
  dep-lbl : ∀ {A B q k} {e₀ e₀′ : Ev A} {e e′ : Ev B} → Lbl e₀ e → Lbl e₀′ e′ → Dep q e₀ k e₀′ → Dep q e k e′
  dep-lbl l-out  _ _ = tt
  dep-lbl l-skip _ _ = tt
  dep-lbl l-end  _ _ = tt
  dep-lbl l-pin l-out d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ ()
  dep-lbl l-pin l-skip d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ ()
  dep-lbl l-pin l-end d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ ()
  dep-lbl l-pin l-pin d i with d i
  ... | inj₁ kr   = inj₁ kr
  ... | inj₂ refl = inj₂ refl

  lbl-silent : ∀ {A B} {e₀ : Ev A} {e : Ev B} → Lbl e₀ e → Silent e₀ → Silent e
  lbl-silent l-skip hush = hush
  lbl-silent l-pin  held = held

  -- Rows each on a reached row of the same kind are reached.
  lifted : ∀ {A B} {u : EmissionSet A} {v : EmissionSet B}
         → (src : ∀ {q e} → v q e → Ev A) → (∀ {q e} (x : v q e) → u q (src x)) → (∀ {q e} (x : v q e) → Lbl (src x) e)
         → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : v q e) → Reach v q e
  lifted src row lbl re x = reach-via (λ y _ d → src y , row y , dep-lbl (lbl-sym (lbl x)) (lbl-sym (lbl y)) d) (re (row x))

  -- A map's row, the row it lies on, and that row's image.
  module Mapped {A B : Set} (f : A → B) where
    src : ∀ {u : EmissionSet A} {q e} → MapT f u q e → Ev A
    src (map-out {a = a} _) = out a
    src (map-skip _)        = skip
    src (map-pin {r = r} _) = pin r
    src (map-end _)         = end

    row : ∀ {u : EmissionSet A} {q e} (x : MapT f u q e) → u q (src x)
    row (map-out x)  = x
    row (map-skip x) = x
    row (map-pin x)  = x
    row (map-end x)  = x

    lbl : ∀ {u : EmissionSet A} {q e} (x : MapT f u q e) → Lbl (src x) e
    lbl (map-out _)  = l-out
    lbl (map-skip _) = l-skip
    lbl (map-pin _)  = l-pin
    lbl (map-end _)  = l-end

    via : ∀ {u u′ : EmissionSet A} {q e} (x : MapT f u q e) → (u q (src x) → u′ q (src x)) → MapT f u′ q e
    via (map-out x)  h = map-out (h x)
    via (map-skip x) h = map-skip (h x)
    via (map-pin x)  h = map-pin (h x)
    via (map-end x)  h = map-end (h x)

    up : ∀ {u : EmissionSet A} {q e₀} → u q e₀ → Σ (Ev B) λ e → MapT f u q e × Lbl e₀ e
    up {e₀ = out _} x = _ , map-out x , l-out
    up {e₀ = skip}  x = _ , map-skip x , l-skip
    up {e₀ = pin _} x = _ , map-pin x , l-pin
    up {e₀ = end}   x = _ , map-end x , l-end

    lift : ∀ {u : EmissionSet A} → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : MapT f u q e) → Reach (MapT f u) q e
    lift {u} = lifted (λ {q} {e} → src {u} {q} {e}) (λ {q} {e} → row {u} {q} {e}) (λ {q} {e} → lbl {u} {q} {e})

  -- A scan's row, the row it lies on, a value on the one it folds in.
  module Scanned {A B : Set} (f : B → A → B) (z : B) where
    final : ∀ {u : EmissionSet A} {q b} → Scan.Acc f z u q b → Σ A λ a → u q (out a)
    final (Scan.acc₀ x _)    = _ , x
    final (Scan.acc _ x _ _) = _ , x

    src : ∀ {u : EmissionSet A} {q e} → Scan.ScanT f z u q e → Ev A
    src (Scan.sval ac)         = out (proj₁ (final ac))
    src (Scan.sstep _)         = skip
    src (Scan.spin {r = r} _)  = pin r
    src (Scan.send _)          = end

    row : ∀ {u : EmissionSet A} {q e} (x : Scan.ScanT f z u q e) → u q (src x)
    row (Scan.sval ac) = proj₂ (final ac)
    row (Scan.sstep x) = x
    row (Scan.spin x)  = x
    row (Scan.send x)  = x

    lbl : ∀ {u : EmissionSet A} {q e} (x : Scan.ScanT f z u q e) → Lbl (src x) e
    lbl (Scan.sval _)  = l-out
    lbl (Scan.sstep _) = l-skip
    lbl (Scan.spin _)  = l-pin
    lbl (Scan.send _)  = l-end

    lift : ∀ {u : EmissionSet A} → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : Scan.ScanT f z u q e) → Reach (Scan.ScanT f z u) q e
    lift {u} = lifted (λ {q} {e} → src {u} {q} {e}) (λ {q} {e} → row {u} {q} {e}) (λ {q} {e} → lbl {u} {q} {e})

  -- A takeWhile's row, the row it lies on, and the point before which
  -- no value failed.
  module Taken {A : Set} (incl : Bool) (keep : A → Bool) where
    open TakeWhile incl keep using (TakeT; Failed; pass; fail; stop; step; tend; left)

    spos : ∀ {u q e} → TakeT u q e → Pos
    spos (pass {q} _ _ _)   = q
    spos (fail {q} _ _ _ _) = q
    spos (stop {q} _ _ _)   = q
    spos (step {q} _ _)     = q
    spos (tend {q} _ _)     = q
    spos (left {q} _ _ _)   = q

    sev : ∀ {u q e} → TakeT u q e → Ev A
    sev (pass {a = a} _ _ _)   = out a
    sev (fail {a = a} _ _ _ _) = out a
    sev (stop {a = a} _ _ _)   = out a
    sev (step _ _)             = skip
    sev (tend _ _)             = end
    sev (left {r = r} _ _ _)   = pin r

    srow : ∀ {u q e} (x : TakeT u q e) → u (spos x) (sev x)
    srow (pass y _ _)   = y
    srow (fail y _ _ _) = y
    srow (stop y _ _)   = y
    srow (step y _)     = y
    srow (tend y _)     = y
    srow (left y _ _)   = y

    bound : ∀ {u q e} → TakeT u q e → Pos
    bound (pass {q} _ _ _)   = q
    bound (fail {q} _ _ _ _) = q
    bound (stop {q} _ _ _)   = q
    bound (step {q} _ _)     = q
    bound (tend {q} _ _)     = q
    bound (left {r = r} _ _ _) = r

    unf : ∀ {u q e} (x : TakeT u q e) → ¬ Failed u (bound x)
    unf (pass _ _ nf)   = nf
    unf (fail _ _ nf _) = nf
    unf (stop _ _ nf)   = nf
    unf (step _ nf)     = nf
    unf (tend _ nf)     = nf
    unf (left _ nf _)   = nf

    -- The same row over another source.
    move : ∀ {u u′ q e} (x : TakeT u q e) → u′ (spos x) (sev x) → ¬ Failed u′ (bound x) → TakeT u′ q e
    move (pass _ k _)   y nf = pass y k nf
    move (fail _ k _ i) y nf = fail y k nf i
    move (stop _ k _)   y nf = stop y k nf
    move (step _ _)     y nf = step y nf
    move (tend _ _)     y nf = tend y nf
    move (left _ _ i)   y nf = left y nf i

    under : ∀ {u q e} (x : TakeT u q e) → spos x ⊑ q
    under (pass _ _ _)       = ⊑-refl _
    under (fail {q} _ _ _ _) = ⊑-snoc⁺ q
    under (stop {q} _ _ _)   = ⊑-snoc⁺ q
    under (step _ _)         = ⊑-refl _
    under (tend _ _)         = ⊑-refl _
    under (left _ _ _)       = ⊑-refl _

    -- What lies before the bound, the source waits on.
    bounded : ∀ {u q e g e″} (x : TakeT u q e) → g ≺ bound x → g ≺ spos x × Dep (spos x) (sev x) g e″
    bounded (pass _ _ _)   gb = gb , tt
    bounded (fail _ _ _ _) gb = gb , tt
    bounded (stop _ _ _)   gb = gb , tt
    bounded (step _ _)     gb = gb , tt
    bounded (tend _ _)     gb = gb , tt
    bounded {g = g} (left {q} {r} _ _ i) gb = ≺-≼-≺ {g} {r} {q} gb (⊑-≼ (inside-⊑ r q i)) , λ _ → inj₁ gb

    -- ... and so does the row.
    bound-dep : ∀ {u q e} (x : TakeT u q e) → ∀ {k e₀} → k ≺ bound x → Dep q e k e₀
    bound-dep (pass _ _ _)   _  = tt
    bound-dep (fail _ _ _ _) _  = tt
    bound-dep (stop _ _ _)   _  = tt
    bound-dep (step _ _)     _  = tt
    bound-dep (tend _ _)     _  = tt
    bound-dep (left _ _ _)   kr = λ _ → inj₁ kr

    bound-≼ : ∀ {u q e} (x : TakeT u q e) → bound x ≼ q
    bound-≼ (pass {q} _ _ _)       = ≼-refl {q}
    bound-≼ (fail {q} _ _ _ _)     = ⊑-≼ (⊑-snoc⁺ q)
    bound-≼ (stop {q} _ _ _)       = ⊑-≼ (⊑-snoc⁺ q)
    bound-≼ (step {q} _ _)         = ≼-refl {q}
    bound-≼ (tend {q} _ _)         = ≼-refl {q}
    bound-≼ (left {q} {r} _ _ i)   = ⊑-≼ (inside-⊑ r q i)

    ext : List Pos → List Pos
    ext []       = []
    ext (k ∷ ks) = k ∷ (k ⊕ [ ix 0 ]) ∷ (k ⊕ [ last ]) ∷ ext ks

    ext-∈ : ∀ {u q e ks} (x : TakeT u q e) → spos x ∈ ks → q ∈ ext ks
    ext-∈ (pass _ _ _)   (here refl) = here refl
    ext-∈ (fail _ _ _ _) (here refl) = there (here refl)
    ext-∈ (stop _ _ _)   (here refl) = there (there (here refl))
    ext-∈ (step _ _)     (here refl) = here refl
    ext-∈ (tend _ _)     (here refl) = here refl
    ext-∈ (left _ _ _)   (here refl) = here refl
    ext-∈ x (there m) = there (there (there (ext-∈ x m)))

    -- With no source row under another, a row before another lies on a
    -- source at or before the other's.
    order : ∀ {u q e k e′} → (∀ {y e l ys e′} → u y e → u (y ⊕ (l ∷ ys)) e′ → ⊥)
          → (x : TakeT u q e) (y : TakeT u k e′) → k ≺ q → spos y ≺ spos x ⊎ spos y ≡ spos x
    order {u} {q} {k = k} fl x y kq with ≼-or-≻ (spos x) (spos y)
    ... | inj₂ lt = inj₁ lt
    ... | inj₁ xy with ≼-split {spos x} {spos y} xy
    ...   | inj₂ eq = inj₂ (sym eq)
    ...   | inj₁ lt with conv (⊑-refl (spos x)) xy (≼-≺-≺ {spos y} {k} {q} (⊑-≼ (under y)) kq) (under x)
    ...     | [] , eq = ⊥-elim (≺-irrefl {spos x} (subst (spos x ≺_) (trans eq (⊕-identityʳ (spos x))) lt))
    ...     | l ∷ ys , eq = ⊥-elim (fl (srow x) (subst (λ v → u v (sev y)) eq (srow y)))

    pin-dep : ∀ {u k r} (y : TakeT u k (pin r)) → PDep r (spos y) (sev y)
    pin-dep (left _ _ _) = inj₂ refl

    dep-src : ∀ {u q e k e′} (x : TakeT u q e) (y : TakeT u k e′) → Dep q e k e′ → Dep (spos x) (sev x) (spos y) (sev y)
    dep-src (pass _ _ _)   _ _ = tt
    dep-src (fail _ _ _ _) _ _ = tt
    dep-src (stop _ _ _)   _ _ = tt
    dep-src (step _ _)     _ _ = tt
    dep-src (tend _ _)     _ _ = tt
    dep-src {k = k} (left {r = r} _ _ _) y d ins with d ins
    ... | inj₁ kr   = inj₁ (≼-≺-≺ {spos y} {k} {r} (⊑-≼ (under y)) kr)
    ... | inj₂ refl = pin-dep y

    -- With no source row under another, over reached rows, every row is reached.
    lift : ∀ {u} → (∀ {y e l ys e′} → u y e → u (y ⊕ (l ∷ ys)) e′ → ⊥) → (∀ {k e₀} → u k e₀ → Reach u k e₀)
         → ∀ {q e} (x : TakeT u q e) → Reach (TakeT u) q e
    lift {u} fl re {q} {e} x with re (srow x)
    ... | ks , h = ext (spos x ∷ ks) , λ y kq d → ext-∈ y (src y kq d)
      where
        src : ∀ {k e′} (y : TakeT u k e′) → k ≺ q → Dep q e k e′ → spos y ∈ (spos x ∷ ks)
        src y kq d with order fl x y kq
        ... | inj₂ eq = here eq
        ... | inj₁ lt = there (h (srow y) lt (dep-src x y d))

-- A MAP KEEPS THE TRUTH: each row lies on its input's, and is reached
-- once that one is, so a clean row lies on a clean one.
map-truth : ∀ {A B H} (f : A → B) {s s′ : Den A} → Rel H s s′ → Rel H (Op.map f s) (Op.map f s′)
map-truth {A} {B} f {s} {s′} R p ok = record
  { Cut     = Cut
  ; silent  = λ c sp x → lbl-silent (lbl (proj₁ x)) (silent c sp (row (proj₁ x)))
  ; shows   = λ c i → shown (shows c i)
  ; again   = λ { c (map-pin y , _) l rs i → shade (again c y l rs i) }
  ; shadow  = λ { c (map-pin y , _) l rs bf → shade (shadow c y l rs (before bf)) }
  ; agree   = λ q e cl → (λ { (x , _) → let v = via x (proj₁ (agree q (src x) (clean cl (lbl x)))) in v , lift re′ v })
                       , (λ { (x , _) → let v = via x (proj₂ (agree q (src x) (clean cl (lbl x)))) in v , lift re v })
  }
  where
    open Truth (R p ok)
    open Mapped f

    t t′ : EmissionSet A
    t  = enter s p
    t′ = enter s′ p

    re : ∀ {k e} → t k e → Reach t k e
    re = entered-reach s p

    re′ : ∀ {k e} → t′ k e → Reach t′ k e
    re′ = entered-reach s′ p

    image : ∀ {k e₀} → t k e₀ → Σ (Ev B) λ e → Truncate (MapT f t) k e × Lbl e₀ e
    image y with up y
    ... | e , m , l = e , (m , lift re m) , l

    shown : ∀ {c i} → (Σ Pos λ z → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × t z e₀)
          → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × Truncate (MapT f t) z e
    shown (z , _ , z0 , tz) with image tz
    ... | e , m , _ = z , e , z0 , m

    shade : ∀ {c i r} → (Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × t z (pin r)) → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Truncate (MapT f t) z (pin r)
    shade (z , z1 , tz) = z , z1 , map-pin tz , lift re (map-pin tz)

    before : ∀ {r} → Before Cut (Truncate (MapT f t)) r → Before Cut t r
    before (ks , h) = ks , λ y kr → h (proj₁ (proj₂ (image y))) kr

    clean : ∀ {q e e₀} → Clean Cut (Truncate (MapT f t)) q e → Lbl e₀ e → Clean Cut t q e₀
    clean (nl , ks , h) l = nl , ks , λ y kq d → h (proj₁ (proj₂ (image y))) kq (dep-lbl l (proj₂ (proj₂ (image y))) d)

-- A DEFER KEEPS THE TRUTH: its body's cuts are its own, and its guard
-- is the same row either way.
defer-truth : ∀ {A H} {d d′ : Den A} → InvD H d → InvD H d′ → Rel H d d′ → Rel H (Op.defer d) (Op.defer d′)
defer-truth {A} {H} {d} {d′} inv inv′ R p ok = record
  { Cut     = Cut
  ; silent  = λ { _ _ (guard , _) → hush ; c sp (body x , _) → silent c sp x }
  ; shows   = λ c i → shown (shows c i)
  ; again   = λ { c (body y , _) l rs i → shade (again c y l rs i) }
  ; shadow  = λ { c (body y , _) l rs bf → shade (shadow c y l rs (before bf)) }
  ; agree   = λ q e cl → fwd cl , bwd cl
  }
  where
    open Truth (R (p ⊕ [ ix 1 ]) (ok-step p ok))

    -- A body row waits on the guard and on body rows.
    in-body : ∀ (e : Den A) {k e₀} → enter e (p ⊕ [ ix 1 ]) k e₀ → Reach (DeferT e p) k e₀
    in-body e x with entered-reach e (p ⊕ [ ix 1 ]) x
    ... | ks , h = (p ⊕ [ ix 0 ]) ∷ ks , λ { guard _ _ → here refl ; (body y) kq dd → there (h y kq dd) }

    shown : ∀ {c i} → (Σ Pos λ z → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × enter d (p ⊕ [ ix 1 ]) z e₀)
          → Σ Pos λ z → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × Truncate (DeferT d p) z e₀
    shown (z , e₀ , z0 , tz) = z , e₀ , z0 , body tz , in-body d tz

    shade : ∀ {c i r} → (Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × enter d (p ⊕ [ ix 1 ]) z (pin r)) → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Truncate (DeferT d p) z (pin r)
    shade (z , z1 , tz) = z , z1 , body tz , in-body d tz

    before : ∀ {r} → Before Cut (Truncate (DeferT d p)) r → Before Cut (enter d (p ⊕ [ ix 1 ])) r
    before (ks , h) = ks , λ y kr → h (body y , in-body d y) kr

    clean : ∀ {q e} → Clean Cut (Truncate (DeferT d p)) q e → Clean Cut (enter d (p ⊕ [ ix 1 ])) q e
    clean (nl , ks , h) = nl , ks , λ y kq dd → h (body y , in-body d y) kq dd

    fwd : ∀ {q e} → Clean Cut (Truncate (DeferT d p)) q e → Truncate (DeferT d p) q e → Truncate (DeferT d′ p) q e
    fwd _  (guard , _)  = guard , guarded d′ inv′ p ok
    fwd {q} {e} cl (body x , _) = body y , in-body d′ y
      where y = proj₁ (agree q e (clean cl)) x

    bwd : ∀ {q e} → Clean Cut (Truncate (DeferT d p)) q e → Truncate (DeferT d′ p) q e → Truncate (DeferT d p) q e
    bwd _  (guard , _)  = guard , guarded d inv p ok
    bwd {q} {e} cl (body x , _) = body y , in-body d y
      where y = proj₂ (agree q e (clean cl)) x

-- A SCAN KEEPS THE TRUTH: each row lies on its input's, a value on the
-- one it folds in.  A value reads every value before it, so the input
-- agrees up to a clean value, whose past is all clean.  A value's fold is
-- classical, but what it is needed for is decidable or a negation.
scan-truth : ∀ {A B H} (f : B → A → B) z {s s′ : Den A} → Rel H s s′ → Rel H (Op.scan f z s) (Op.scan f z s′)
scan-truth {A} {B} f z {s} {s′} R p ok = record
  { Cut     = Cut
  ; silent  = λ c sp x → lbl-silent (lbl (proj₁ x)) (silent c sp (row (proj₁ x)))
  ; shows   = λ c i → shown c (shows c i)
  ; again   = λ { c (Scan.spin y , _) l rs i → shade (again c y l rs i) }
  ; shadow  = λ { c (Scan.spin y , _) l rs bf → shade (shadow c y l rs (before bf)) }
  ; agree   = λ q e cl → fwd cl , bwd cl
  }
  where
    tr = R p ok
    open Truth tr
    open Scanned f z

    t t′ : EmissionSet A
    t  = enter s p
    t′ = enter s′ p

    S S′ : EmissionSet B
    S  = Scan.ScanT f z t
    S′ = Scan.ScanT f z t′

    re : ∀ {k e} → t k e → Reach t k e
    re = entered-reach s p

    re′ : ∀ {k e} → t′ k e → Reach t′ k e
    re′ = entered-reach s′ p

    -- Each input row shows, a value classically.
    image : ∀ {k e₀} → t k e₀ → ¬ ¬ (Σ (Ev B) λ e → Truncate S k e × Lbl e₀ e)
    image {e₀ = out a} y n = fold f z t (entered-few s p tt y) y λ { (b , ac) → n (out b , (Scan.sval ac , lift re (Scan.sval ac)) , l-out) }
    image {e₀ = skip}  y n = n (skip , (Scan.sstep y , lift re (Scan.sstep y)) , l-skip)
    image {e₀ = pin r} y n = n (pin r , (Scan.spin y , lift re (Scan.spin y)) , l-pin)
    image {e₀ = end}   y n = n (end , (Scan.send y , lift re (Scan.send y)) , l-end)

    quiet : ∀ {k e₀} → t k e₀ → Silent e₀ → Σ (Ev B) λ e → Truncate S k e
    quiet y hush = skip , Scan.sstep y , lift re (Scan.sstep y)
    quiet y held = _ , Scan.spin y , lift re (Scan.spin y)

    shown : ∀ {c i} → Cut c → (Σ Pos λ w → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ w × t w e₀)
          → Σ Pos λ w → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ w × Truncate S w e
    shown {i = i} c (w , _ , w0 , tw) with quiet tw (silent c (i , w0) tw)
    ... | e , m = w , e , w0 , m

    shade : ∀ {c i r} → (Σ Pos λ w → (c ⊕ [ ix i ]) ⊑ w × t w (pin r)) → Σ Pos λ w → (c ⊕ [ ix i ]) ⊑ w × Truncate S w (pin r)
    shade (w , w1 , tw) = w , w1 , Scan.spin tw , lift re (Scan.spin tw)

    firm : ∀ {q ks k} → ¬ ¬ (Cov q ks k × ¬ Lie Cut k) → Cov q ks k × ¬ Lie Cut k
    firm nn = cov-stable (λ n → nn λ c → n (proj₁ c)) , λ l → nn λ c → proj₂ c l

    before : ∀ {r} → Before Cut (Truncate S) r → Before Cut t r
    before (ks , h) = ks , λ y kr → firm λ n → image y λ { (_ , m , _) → n (h m kr) }

    clean : ∀ {q e e₀} → Clean Cut (Truncate S) q e → Lbl e₀ e → Clean Cut t q e₀
    clean (nl , ks , h) l = nl , ks , λ y kq d → firm λ n → image y λ { (_ , m , l′) → n (h m kq (dep-lbl l l′ d)) }

    -- Up to a clean value, the input agrees.
    upto-clean : ∀ {q a} → Clean Cut t q (out a) → AgreeTo q t t′
    upto-clean {q} {a} cl@(nl , ks , h) = ⟨ (λ {y} {e₀} yq → at (≼-split {y} {q} yq)) ⟩
      where
        at : ∀ {y e₀} → y ≺ q ⊎ y ≡ q → (t y e₀ → t′ y e₀) × (t′ y e₀ → t y e₀)
        at {y} {e₀} (inj₁ yq) = (λ x → proj₁ (agree y e₀ (clean-down tr {q} {out a} {y} {e₀} cl yq tt (proj₂ (h x yq tt)))) x) , (λ x → pull tr {q} {out a} {y} {e₀} cl x yq tt)
        at {e₀ = e₀} (inj₂ refl) = agree q e₀ (nl , ks , λ x kq _ → h x kq tt)

    fwd : ∀ {q e} → Clean Cut (Truncate S) q e → Truncate S q e → Truncate S′ q e
    fwd {q} cl (Scan.sval {b = b} ac , _) =
      let v = proj₁ (upto (scan-ag f z (upto-clean {a = proj₁ (final ac)} (clean {e = out b} {e₀ = out (proj₁ (final ac))} cl l-out))) {q} (≼-refl {q})) (Scan.sval ac) in v , lift re′ v
    fwd {q} cl (Scan.sstep x , _) = let v = Scan.sstep (proj₁ (agree q skip (clean cl l-skip)) x) in v , lift re′ v
    fwd {q} cl (Scan.spin {r = r} x , _) = let v = Scan.spin (proj₁ (agree q (pin r) (clean cl l-pin)) x) in v , lift re′ v
    fwd {q} cl (Scan.send x , _) = let v = Scan.send (proj₁ (agree q end (clean cl l-end)) x) in v , lift re′ v

    bwd : ∀ {q e} → Clean Cut (Truncate S) q e → Truncate S′ q e → Truncate S q e
    bwd {q} cl (Scan.sval {b = b} ac , _) =
      let v = proj₂ (upto (scan-ag f z (upto-clean {a = proj₁ (final ac)} (clean {e = out b} {e₀ = out (proj₁ (final ac))} cl l-out))) {q} (≼-refl {q})) (Scan.sval ac) in v , lift re v
    bwd {q} cl (Scan.sstep x , _) = let v = Scan.sstep (proj₂ (agree q skip (clean cl l-skip)) x) in v , lift re v
    bwd {q} cl (Scan.spin {r = r} x , _) = let v = Scan.spin (proj₂ (agree q (pin r) (clean cl l-pin)) x) in v , lift re v
    bwd {q} cl (Scan.send x , _) = let v = Scan.send (proj₂ (agree q end (clean cl l-end)) x) in v , lift re v

-- A TAKEWHILE KEEPS THE TRUTH: each row lies on its source's, unfailed
-- before it.  A cut stays a cut while unfailed before its spin, or while
-- it keeps the pins of a connect leading it; a cut it hides holds no row
-- of either side where a row is clean.  Which failure is the earliest is
-- not decidable, but what it is needed for is a negation.
take-truth : ∀ {A H} (i : Bool) (keep : A → Bool) {s s′ : Den A} → InvD H s → InvD H s′
           → Rel H s s′ → Rel H (Op.takeWhile i keep s) (Op.takeWhile i keep s′)
take-truth {A} {H} i keep {s} {s′} Is Is′ R p ok = record
  { Cut     = Cut′
  ; silent  = λ c sp x → quiet (proj₁ c) sp (proj₁ x)
  ; shows   = shown
  ; again   = λ { c (left x nf _ , _) l rc j → kept-at nf (again (proj₁ c) x l rc j) }
  ; shadow  = λ { c (left x′ nf′ _ , _) l rc bf → kept-at (unfailed bf nf′) (shadow (proj₁ c) x′ l rc (before-in bf (unfailed bf nf′))) }
  ; agree   = λ q e cl → fwd cl , bwd cl
  }
  where
    tr = R p ok
    open Truth tr
    open Taken i keep
    open TakeWhile i keep using (TakeT; Failed; pass; fail; stop; step; tend; left)

    t t′ : EmissionSet A
    t  = enter s p
    t′ = enter s′ p

    O : EmissionSet A
    O = Truncate (TakeT t)

    I  = Is p ok
    I′ = Is′ p ok

    rows : ∀ {q e} → TakeT t q e → O q e
    rows x = x , lift (InvAt.flat I) (entered-reach s p) x

    rows′ : ∀ {q e} → TakeT t′ q e → Truncate (TakeT t′) q e
    rows′ x = x , lift (InvAt.flat I′) (entered-reach s′ p) x

    pinned-in : ∀ {z r} → t z (pin r) → Tr (inside r z)
    pinned-in x = proj₂ (InvAt.pinned I x)

    -- The pins of a connect leading the cut, kept.
    Kept : Pos → Set
    Kept c = Σ Pos λ r → r ⊑ c × ¬ Failed t r × Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × t z (pin r)

    Cut′ : Pos → Set
    Cut′ c = Cut c × (¬ Failed t (c ⊕ [ ix 0 ]) ⊎ Kept c)

    fd-up : ∀ {w z} → Failed t w → w ≼ z → Failed t z
    fd-up {w} {z} (g , a , x , nk , gw) wz = g , a , x , nk , ≺-≼-≺ {g} {w} {z} gw wz

    past-first : ∀ c j {y} → (c ⊕ [ ix (suc j) ]) ⊑ y → Failed t (c ⊕ [ ix 0 ]) → Failed t y
    past-first c j {y} l f = fd-up {c ⊕ [ ix 0 ]} {y} f (≺→≼ {c ⊕ [ ix 0 ]} {y}
      (≺-≼-≺ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc j) ]} {y} (Equivalence.from T-≡ (<ᵖ-part c [] [] (ix-< {0} {suc j} (s≤s z≤n)))) (⊑-≼ l)))

    -- A row one step under a source's position: the source is under the spin.
    snoc-spun : ∀ {c j q l e₀} → Cut c → (c ⊕ [ ix j ]) ⊑ (q ⊕ [ l ]) → t q e₀ → Spun c q
    snoc-spun {c} {j} {q} {l} cc sq x with ⊑-snoc q sq
    ... | inj₁ le = j , le
    ... | inj₂ eq with shows cc j
    ...   | _ , _ , (zs , refl) , tz = ⊥-elim (InvAt.flat I x (subst (λ v → t v _) (trans (cong (_⊕ zs) eq) (⊕-assoc q [ l ] zs)) tz))

    quiet : ∀ {c y e} → Cut c → Spun c y → TakeT t y e → Silent e
    quiet cc sp (pass x _ _) with silent cc sp x
    ... | ()
    quiet cc (_ , l) (fail x _ _ _) with silent cc (snoc-spun cc l x) x
    ... | ()
    quiet cc (_ , l) (stop x _ _) with silent cc (snoc-spun cc l x) x
    ... | ()
    quiet cc sp (step x _) = hush
    quiet cc sp (tend x _) with silent cc sp x
    ... | ()
    quiet cc sp (left x _ _) = held

    -- Unfailed before the spin, unfailed under it.
    unfailed-under : ∀ {c j z} → Cut c → ¬ Failed t (c ⊕ [ ix 0 ]) → (c ⊕ [ ix j ]) ⊑ z → ¬ Failed t z
    unfailed-under {c} {j} {z} cc nf sz (g , a , x , nk , gz) with where? c g
    ... | inj₁ g0 = nf (g , a , x , nk , g0)
    ... | inj₂ (inj₁ sp) with silent cc sp x
    ...   | ()
    unfailed-under {c} {j} {z} cc nf sz (g , a , x , nk , gz) | inj₂ (inj₂ after)
      with silent cc (j , conv (⊑-refl (c ⊕ [ ix j ])) (≺→≼ {c ⊕ [ ix j ]} {g} (after j)) gz sz) x
    ... | ()

    kept-at : ∀ {c j r} → ¬ Failed t r → (Σ Pos λ z → (c ⊕ [ ix j ]) ⊑ z × t z (pin r)) → Σ Pos λ z → (c ⊕ [ ix j ]) ⊑ z × O z (pin r)
    kept-at nf (z , sz , x) = z , sz , rows (left x nf (pinned-in x))

    shown : ∀ {c} → Cut′ c → ∀ j → Σ Pos λ z → Σ (Ev A) λ e → (c ⊕ [ ix j ]) ⊑ z × O z e
    shown (cc , inj₁ nf) j with shows cc j
    ... | z , e₀ , sz , x with silent cc (j , sz) x
    ...   | hush = z , skip , sz , rows (step x (unfailed-under cc nf sz))
    ...   | held {r} = z , pin r , sz , rows (left x (λ g → unfailed-under cc nf sz (fd-up {r} {z} g (⊑-≼ (inside-⊑ r z (pinned-in x))))) (pinned-in x))
    shown (cc , inj₂ (r , rc , nf , z₁ , s1 , x₁)) j with kept-at nf (again cc x₁ (0 , s1) rc j)
    ... | z , sz , o = z , pin r , sz , o

    -- A row past a cut's first, failed before the spin: the cut keeps
    -- the pins of a connect leading it.
    hidden : ∀ {c j q e} → Cut c → TakeT t q e → (c ⊕ [ ix (suc j) ]) ⊑ q → Failed t (c ⊕ [ ix 0 ]) → Kept c
    hidden {j = j} cc (pass y _ _) l _ with silent cc (suc j , l) y
    ... | ()
    hidden cc (fail y _ _ _) l _ with silent cc (snoc-spun cc l y) y
    ... | ()
    hidden cc (stop y _ _) l _ with silent cc (snoc-spun cc l y) y
    ... | ()
    hidden {c} {j} cc (step _ nf) l f = ⊥-elim (nf (past-first c j l f))
    hidden {j = j} cc (tend y _) l _ with silent cc (suc j , l) y
    ... | ()
    hidden {c} {j} cc (left {q} {r} y nf ins) l f with ⊑-cmp r (c ⊕ [ ix (suc j) ]) (inside-⊑ r q ins) l
    ... | inj₂ Sr = ⊥-elim (nf (past-first c j Sr f))
    ... | inj₁ rS with ⊑-snoc c rS
    ...   | inj₂ refl = ⊥-elim (nf (past-first c j (⊑-refl _) f))
    ...   | inj₁ rc with again cc y (j , l) rc 1
    ...     | z , z1 , tz = r , rc , nf , z , z1 , tz

    -- A row not past a cut's first it shows is past none.
    honest : ∀ {q e} → TakeT t q e → ¬ Lie Cut′ q → ¬ Lie Cut q
    honest x nl (c , cc , j , l) = nl (c , (cc , inj₁ λ f → nl (c , (cc , inj₂ (hidden cc x l f)) , j , l)) , j , l)

    -- A value is not past a cut's first.
    honest-val : ∀ {g a} → t g (out a) → ¬ Lie Cut g
    honest-val x (c , cc , j , l) with silent cc (suc j , l) x
    ... | ()

    -- An unfailed row shows where it is.
    img : ∀ {b k e₀} → ¬ Failed t b → t k e₀ → k ≺ b → TakeT t k e₀
    img {b} {k} {out a} nf x kb with keep a in eq
    ... | true  = pass x (subst Tr (sym eq) tt) (λ g → nf (fd-up {k} {b} g (≺→≼ {k} {b} kb)))
    ... | false = ⊥-elim (nf (k , a , x , subst (λ v → Tr (not v)) (sym eq) tt , kb))
    img {b} {k} {skip}  nf x kb = step x (λ g → nf (fd-up {k} {b} g (≺→≼ {k} {b} kb)))
    img {b} {k} {end}   nf x kb = tend x (λ g → nf (fd-up {k} {b} g (≺→≼ {k} {b} kb)))
    img {b} {k} {pin r} nf x kb =
      left x (λ g → nf (fd-up {r} {b} g (≼-trans {r} {k} {b} (⊑-≼ (inside-⊑ r k (pinned-in x))) (≺→≼ {k} {b} kb)))) (pinned-in x)

    before-in : ∀ {b} → Before Cut′ O b → ¬ Failed t b → Before Cut t b
    before-in (ks , h) nf = ks , λ x kb → let o = img nf x kb ; a = h (rows o) kb in proj₁ a , honest o (proj₂ a)

    -- To refute a failure, refute the earliest.
    firstfail : ∀ {b} → (∀ {g a} → ¬ Failed t g → t g (out a) → Tr (not (keep a)) → g ≺ b → ⊥) → ¬ Failed t b
    firstfail {b} refute (g , a , x , nk , gb) = few-ind P stp (entered-few s p tt x) x nk gb
      where
        P : Pos → Set
        P g = ∀ {a} → t g (out a) → Tr (not (keep a)) → g ≺ b → ⊥

        stp : ∀ {g} → Few t g → (∀ {v e} → t v e → v ≺ g → P v) → P g
        stp {g} _ ih x nk gb =
          em {P = Failed t g} {G = ⊥}
             (λ { (g′ , a′ , x′ , nk′ , g′g) _ → ih x′ g′g x′ nk′ (≺-trans {g′} {g} {b} g′g gb) })
             (λ nf _ → refute nf x nk gb)
             (λ z → z)

    -- Clean before a point, the next has failed there only if this has.
    unfailed : ∀ {b} → Before Cut′ O b → ¬ Failed t′ b → ¬ Failed t b
    unfailed {b} bf nf′ = firstfail λ {g} {a} nfg x nk gb →
      nf′ (g , a , proj₁ (agree g (out a) (clean-of {e = out a} (before-in (before-down bf (≺→≼ {g} {b} gb)) nfg) (honest-val x))) x , nk , gb)

    -- A source row of the next past a cut's first, failed before the
    -- spin: the cut keeps the pins of a connect leading it.
    hidden′ : ∀ {c j q e} → Cut c → (x′ : TakeT t′ q e) → ¬ Failed t (bound x′) → Before Cut′ O (bound x′)
            → (c ⊕ [ ix (suc j) ]) ⊑ spos x′ → Failed t (c ⊕ [ ix 0 ]) → Kept c
    hidden′ {c} {j} _ (pass _ _ _)   nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (fail _ _ _ _) nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (stop _ _ _)   nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (step _ _)     nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (tend _ _)     nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} cc (left {q} {r} y′ _ ins) nf bf l f with ⊑-cmp r (c ⊕ [ ix (suc j) ]) (inside-⊑ r q ins) l
    ... | inj₂ Sr = ⊥-elim (nf (past-first c j Sr f))
    ... | inj₁ rS with ⊑-snoc c rS
    ...   | inj₂ refl = ⊥-elim (nf (past-first c j (⊑-refl _) f))
    ...   | inj₁ rc with shadow cc y′ (j , l) rc (before-in bf nf)
    ...     | z , z1 , tz = r , rc , nf , z , z1 , tz

    honest′ : ∀ {q e} (x′ : TakeT t′ q e) → ¬ Failed t (bound x′) → Before Cut′ O (bound x′) → ¬ Lie Cut′ q → ¬ Lie Cut (spos x′)
    honest′ x′ nf bf nl (c , cc , j , l) = nl (c , (cc , inj₁ λ f → nl (c , (cc , inj₂ (hidden′ cc x′ nf bf l f)) , j , lq)) , j , lq)
      where lq = ⊑-trans l (under x′)

    seen-at : ∀ {q e ks k e₀} → (∀ {k′ e′} → O k′ e′ → k′ ≺ q → Dep q e k′ e′ → Cov q ks k′ × ¬ Lie Cut′ k′)
            → TakeT t k e₀ → k ≺ q → Dep q e k e₀ → Cov q ks k × ¬ Lie Cut k
    seen-at h o kq d = let a = h (rows o) kq d in proj₁ a , honest o (proj₂ a)

    down : ∀ {q′ q ks k} → Cov q′ ks k × ¬ Lie Cut k → k ≺ q → q ≼ q′ → Cov q ks k × ¬ Lie Cut k
    down (cv , nl) kq qq′ = cov-down cv kq qq′ , nl

    -- Unfailed to its bound, a source waits only on clean rows.
    deps : ∀ {u q e} (x : TakeT u q e) → ¬ Failed t (bound x) → Clean Cut′ O q e
         → Σ (List Pos) λ ks → ∀ {k e₀} → t k e₀ → k ≺ spos x → Dep (spos x) (sev x) k e₀ → Cov (spos x) ks k × ¬ Lie Cut k
    deps (pass {a = a} _ _ _) nf (_ , ks , h) = ks , λ y kq _ → seen-at {e = out a} h (img nf y kq) kq tt
    deps (step _ _)   nf (_ , ks , h) = ks , λ y kq _ → seen-at {e = skip} h (img nf y kq) kq tt
    deps (tend _ _)   nf (_ , ks , h) = ks , λ y kq _ → seen-at {e = end} h (img nf y kq) kq tt
    deps (fail {q} {a} _ _ _ _) nf (_ , ks , h) = ks , λ {k} y kq _ →
      down (seen-at {e = out a} h (img nf y kq) (≺-trans {k} {q} {q ⊕ [ ix 0 ]} kq (≺-ext q [])) tt) kq (≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q []))
    deps (stop {q} _ _ _) nf (_ , ks , h) = ks , λ {k} y kq _ →
      down (seen-at {e = end} h (img nf y kq) (≺-trans {k} {q} {q ⊕ [ last ]} kq (≺-ext q [])) tt) kq (≺→≼ {q} {q ⊕ [ last ]} (≺-ext q []))
    deps (left {q} {r} _ _ ins) nf (_ , ks , h) = ks , λ y kq d → by (d ins) y kq
      where
        by : ∀ {k e₀} → PDep r k e₀ → t k e₀ → k ≺ q → Cov q ks k × ¬ Lie Cut k
        by (inj₁ kr)   y kq = seen-at h (img nf y kr) kq (λ _ → inj₁ kr)
        by (inj₂ refl) y kq = seen-at h (left y nf (pinned-in y)) kq (λ _ → inj₂ refl)

    src-clean : ∀ {q e} (x : TakeT t q e) → Clean Cut′ O q e → Clean Cut t (spos x) (sev x)
    src-clean x cl@(nl , _) = (λ l → honest x nl (lie-up l (under x))) , deps x (unf x) cl

    src-clean′ : ∀ {q e} (x′ : TakeT t′ q e) → Clean Cut′ O q e → ¬ Failed t (bound x′) × Clean Cut t (spos x′) (sev x′)
    src-clean′ x′ cl@(nl , _) = nfb , honest′ x′ nfb bf nl , deps x′ nfb cl
      where
        bf  = before-of cl (bound-≼ x′) (bound-dep x′)
        nfb = unfailed bf (unf x′)

    fwd : ∀ {q e} → Clean Cut′ O q e → O q e → Truncate (TakeT t′) q e
    fwd cl (x , _) = rows′ (move x (proj₁ (agree (spos x) (sev x) sc) (srow x)) nf′)
      where
        sc = src-clean x cl

        nf′ : ¬ Failed t′ (bound x)
        nf′ (g , a , y′ , nk , gb) with bounded {e″ = out a} x gb
        ... | gs , d = unf x (g , a , pull tr sc y′ gs d , nk , gb)

    bwd : ∀ {q e} → Clean Cut′ O q e → Truncate (TakeT t′) q e → O q e
    bwd cl (x′ , _) with src-clean′ x′ cl
    ... | nfb , sc = rows (move x′ (proj₂ (agree (spos x′) (sev x′) sc) (srow x′)) nfb)

-- EACH OPERATOR KEEPS THE TRUTH: every operator over children each
-- against the next.  A connect's body is read against its next under ONE
-- handle, and across the two handles by causality (`Causal`), as the
-- order modulus is (`settle`).
postulate
  flat-truth    : ∀ {A B H} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
                → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
                → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap op f s) (Op.flatMap op f′ s′)
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
truth n       (cold c)          ρ g p ok = truth-refl
truth n       empty             ρ g p ok = truth-refl
truth n       (of xs)           ρ g p ok = truth-refl
truth n       (map f s)         ρ g = map-truth f {approx n s ρ} {approx (suc n) s ρ} (truth n s ρ g)
truth n       (scan f z s)      ρ g = scan-truth f z {approx n s ρ} {approx (suc n) s ρ} (truth n s ρ g)
truth n       (takeWhile i k s) ρ g =
  take-truth i k {approx n s ρ} {approx (suc n) s ρ} (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (truth n s ρ g)
truth n       (flatMap op f s)  ρ g =
  flat-truth op (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (λ a → inv-approx n (f a) ρ g) (λ a → inv-approx (suc n) (f a) ρ g)
    (truth n s ρ g) (λ a → truth n (f a) ρ g)
truth n       (connect s b)     ρ g =
  connect-truth {s = approx n s ρ} {approx (suc n) s ρ} {λ h → approx n b (h ∷ ρ)} {λ h → approx (suc n) b (h ∷ ρ)}
    (inv-approx n s ρ g) (inv-approx (suc n) s ρ g)
    (λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx (suc n) b (hot t ∷ ρ) (good-cons L g))
    (causal-at n b ρ) (causal-at (suc n) b ρ)
    (truth n s ρ g) (λ {t} L → truth n b (hot t ∷ ρ) (good-cons L g))
truth n       (connected i)     ρ g p ok = truth-refl
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
