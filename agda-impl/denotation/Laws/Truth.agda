{-# OPTIONS --guardedness #-}

-- ONE APPROXIMANT AGAINST THE NEXT (`Truth`): the next unfolds the cuts
-- of this one.  A cut spins silent in one instant; every row clean of
-- the cuts (`Clean`) is the next's, and every row of the next clean here
-- is this one's.  So wherever finitely many rows precede a row shown,
-- the two agree (`truth-lies`), and with finitely many rows in all they
-- are the same (`truth-finite`).
module denotation.Laws.Truth where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; n≮n; m≤n⇒m<n∨m≡n)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Data.Bool using (Bool; true; false; not) renaming (T to Tr)
open import Tree using (map; defer)
open import denotation.Position using (Pos; _∙_; ix; sub; last; instant; inside; _⊕_)
open import denotation.Events using (ix-<; <ᵖ-part; <ᵖ-below; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; Few; Dep; Reach; Truncate; Silent; hush; Spin;
  spin; DeferT; guard; body; _≺_; _≼_; enter; module Op)
open import denotation.Read using (Visible; loud)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≼-split; ≺-irrefl; ≺-trans;
  ticks)
open import denotation.Laws.Count using (Cov; ⊑?; cov-down; dep-trans)
open import denotation.Laws.Worlds using (W⁼; here; Ok; InvD; _⊑_; ⊑-refl; ⊑-≼; ⊕-assoc; ⊕-identityʳ; inside-⊑; ⊑-trans; ⊑-cmp; ⊑-snoc; conv)
open import denotation.Laws.Cut using (module SpinB; spinIx; ix-back)
open import denotation.Laws using (from; aft)

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

-- Under one spin row, before every later one.
below-next : ∀ s {a b z} → (s ⊕ [ ix a ]) ⊑ z → a < b → z ≺ (s ⊕ [ ix b ])
below-next s {a} {b} (zs , refl) lt rewrite ⊕-assoc s [ ix a ] zs = Equivalence.from T-≡ (<ᵖ-part s zs [] (ix-< lt))

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
-- recurs under each; one the next shows there, clean before its connect
-- and its connect past no cut's first, shows under its second.  Wherever a row is clean, the next has it too,
-- and nothing else there.
record Truth {A : Set} (t t′ : EmissionSet A) : Set₁ where
  field
    Cut     : Pos → Set
    silent  : ∀ {s y e} → Cut s → Spun s y → t y e → Silent e
    shows   : ∀ {s} → Cut s → ∀ i → Σ Pos λ z → Σ (Ev A) λ e → (s ⊕ [ ix i ]) ⊑ z × t z e
    again   : ∀ {s w r} → Cut s → t w (pin r) → Lies s w → r ⊑ s → ∀ i → Σ Pos λ z → (s ⊕ [ ix i ]) ⊑ z × t z (pin r)
    shadow  : ∀ {s w r} → Cut s → t′ w (pin r) → Lies s w → r ⊑ s → Before Cut t r → ¬ Lie Cut r → Σ Pos λ z → (s ⊕ [ ix 1 ]) ⊑ z × t z (pin r)
    agree   : ∀ q e → Clean Cut t q e → (t q e → t′ q e) × (t′ q e → t q e)

-- A row under every spin row before `x`: endlessly many before it.
spin-few : ∀ {X} {t : EmissionSet X} {s x} → (∀ i → Σ Pos λ z → Σ (Ev X) λ e → (s ⊕ [ ix i ]) ⊑ z × t z e × z ≺ x) → Few t x → ⊥
spin-few {X} {s = s} sh (ks , h) = n≮n (length ks) (SpinB.bound {X} s (spin (suc (length ks))) (suc (length ks)) ks ≤-refl cov)
  where
    cov : ∀ {k e} (y : Spin s k e) → spinIx y < suc (length ks) → Any (k ⊑_) ks
    cov (spin j) _ with sh j
    ... | z , _ , sz , tz , zx = Any.map (λ { refl → sz }) (h tz zx)

module _ {A : Set} {t t′ : EmissionSet A} (tr : Truth t t′) where
  open Truth tr

  private
    -- Past the whole spin, endlessly many rows before.
    blocked : ∀ {s x} → Cut s → (∀ i → (s ⊕ [ ix i ]) ≺ x) → Few t x → ⊥
    blocked {s} {x} c after = spin-few λ i → let (z , e , sz , tz) = shows c i in
      z , e , sz , tz , ≺-trans {z} {s ⊕ [ ix (suc i) ]} {x} (below-next s sz ≤-refl) (after (suc i))

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
            ...     | inj₁ rs with shadow c x (i , sw) rs bf (λ l → nq (lie-up l rq))
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

-- PLACED: a truth whose every cut is subscribed in the world of the
-- reading at `p`.
record Placed {A : Set} (H : Pos → Set) (p : Pos) (t t′ : EmissionSet A) : Set₁ where
  constructor placing
  field
    tr     : Truth t t′
    placed : ∀ {s} → Truth.Cut tr s → W⁼ H p s

-- Nothing cut, placed anywhere.
placed-refl : ∀ {A H p} {t : EmissionSet A} → Placed H p t t
placed-refl = placing truth-refl λ ()

-- Every admissible subscription of `d′` is that of `d`, past its cuts.
Rel : ∀ {A} → (Pos → Set) → Den A → Den A → Set₁
Rel H d d′ = ∀ p → Ok H p → Placed H p (enter d p) (enter d′ p)

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
spin-truth {A} {H} {d} inv p ok = placing (record
  { Cut     = _≡ p
  ; silent  = λ { refl _ (spin _ , _) → hush }
  ; shows   = λ { refl i → p ⊕ [ ix i ] , skip , ⊑-refl _ , spin i , spin-reach p i }
  ; again   = λ { refl (() , _) }
  ; shadow  = λ { refl (body x , _) _ rp _ _ → ⊥-elim (proj₂ (aft d inv p ok x) refl (≼-≺-≺ {_} {p} {b₀} (⊑-≼ rp) (Equivalence.from T-≡ (<ᵖ-below p [])))) }
  ; agree   = λ q e c → to c , back c
  }) (λ { refl → here })
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
