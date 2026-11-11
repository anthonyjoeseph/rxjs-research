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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Data.Bool using (Bool)
open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; _∙_; ix; sub; last; instant; inside; _⊕_)
open import denotation.Events using (Timeline; ix-<; <ᵖ-part; <ᵖ-below; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; hot; DenEnv; Few; Dep; Reach; Truncate; Silent; hush; held; Spin; spin; DeferT; guard; body; MapT; map-out; map-skip; map-pin; map-end; _≺_; _≼_; enter; approx; ⟦_⟧; module Op)
open import denotation.Read using (Visible; loud)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≼-split; ≺-irrefl; ≺-trans; ticks; reach-via; entered-reach)
open import denotation.Laws.Count using (Cov; ag-cnt; ⊑?; cov-down; dep-trans)
open import denotation.Laws.Worlds using (ok-step; Ok; Hots; GoodEnv; InvD; Lawful; _∪ʰ_; _⊑_; ⊑-refl; ⊑-≼; ⊕-assoc; ⊕-identityʳ; inside-⊑; ⊑-trans; ⊑-cmp; ⊑-snoc; conv)
open import denotation.Laws.Cut using (module SpinB; spinIx; ix-back)
open import denotation.Laws.ConnectNe using (Causal)
open import denotation.Laws using (from; inv-approx; good-cons; causal-at; aft)

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

-- THE NEXT APPROXIMANT, past the cuts.  Each cut `defer` (`Cut`) spins
-- at its subscription: every row under its spin is silent, and each of
-- its rows shows; no position past the whole spin has finitely many rows
-- before it; a pin the next shows past its first, of a connect leading
-- the cut, shows under its second.  Wherever a row is clean, the next
-- has it too, and nothing else there.
record Truth {A : Set} (t t′ : EmissionSet A) : Set₁ where
  field
    Cut     : Pos → Set
    silent  : ∀ {s y e} → Cut s → Spun s y → t y e → Silent e
    shows   : ∀ {s} → Cut s → ∀ i → Σ Pos λ z → Σ (Ev A) λ e → (s ⊕ [ ix i ]) ⊑ z × t z e
    blocked : ∀ {s x} → Cut s → (∀ i → (s ⊕ [ ix i ]) ≺ x) → Few t x → ⊥
    shadow  : ∀ {s w r} → Cut s → t′ w (pin r) → Lies s w → r ⊑ s → Σ Pos λ z → (s ⊕ [ ix 1 ]) ⊑ z × t z (pin r)
    agree   : ∀ q e → Clean Cut t q e → (t q e → t′ q e) × (t′ q e → t q e)

module _ {A : Set} {t t′ : EmissionSet A} (tr : Truth t t′) where
  open Truth tr

  private
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
    dirty : ∀ {q e w e′} → ¬ Lie Cut q → Lie Cut w → t′ w e′ → w ≺ q → Dep q e w e′
          → Σ Pos λ z → Σ (Ev A) λ e″ → Lie Cut z × t z e″ × z ≺ q × Dep q e z e″
    dirty {q} {e} {w} {e′} nq (s , c , i , sw) x wq d = go e e′ x d
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

        go : ∀ e e′ → t′ w e′ → Dep q e w e′ → Σ Pos λ z → Σ (Ev A) λ e″ → Lie Cut z × t z e″ × z ≺ q × Dep q e z e″
        go (out _) _ _ _ = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , tt
        go skip    _ _ _ = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , tt
        go end     _ _ _ = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , tt
        go (pin r) e′ x d with T? (inside r q)
        ... | no ni = z₁ , _ , lie₁ , t₁ , under₁ wq nSq , λ ins → ⊥-elim (ni ins)
        ... | yes ins = by (d ins) x
          where
            rq : r ⊑ q
            rq = inside-⊑ r q ins

            nSr : ¬ S ⊑ r
            nSr l = nSq (⊑-trans l rq)

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
            ...     | inj₁ rs with shadow c x (i , sw) rs
            ...       | z , z1 , tz = z , pin r , (s , c , 0 , z1) , tz , before (s≤s z≤n) z1 wq nSq , λ _ → inj₂ refl

  -- WHAT A CLEAN ROW WAITS ON IN THE NEXT, THIS ONE HAS.
  pull : ∀ {q e w e′} → Clean Cut t q e → t′ w e′ → w ≺ q → Dep q e w e′ → t w e′
  pull {q} {e} {w} {e′} cl@(nq , ks , h) x wq d = proj₂ (agree w e′ (clean-down cl wq d nw)) x
    where
      nw : ¬ Lie Cut w
      nw lw with dirty nq lw x wq d
      ... | z , _ , lz , tz , zq , dz = proj₂ (h tz zq dz) lz

-- Nothing cut: the same rows.
truth-refl : ∀ {A} {t : EmissionSet A} → Truth t t
truth-refl = record
  { Cut     = λ _ → ⊥
  ; silent  = λ ()
  ; shows   = λ ()
  ; blocked = λ ()
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

  -- Past the whole spin, endlessly many rows before.
  endless : ∀ {A} p {x} → (∀ i → (p ⊕ [ ix i ]) ≺ x) → ¬ Few (Truncate (Spin {A} p)) x
  endless {A} p after (ks , h) = n≮n (length ks) (SpinB.bound {A} p (spin (suc (length ks))) (suc (length ks)) ks ≤-refl cov)
    where
      cov : ∀ {k e} (y : Spin p k e) → spinIx y < suc (length ks) → Any (k ⊑_) ks
      cov (spin j) _ = Any.map (λ { refl → ⊑-refl _ }) (h (spin j , spin-reach p j) (after j))

-- A CUT IS ITS SPIN: the unfolding's guard is the spin's first row, and
-- its body lies at or past the second, which every row past it waits on.
spin-truth : ∀ {A H} {d : Den A} → InvD H d → Rel H Op.⊥ (Op.defer d)
spin-truth {A} {H} {d} inv p ok = record
  { Cut     = _≡ p
  ; silent  = λ { refl _ (spin _ , _) → hush }
  ; shows   = λ { refl i → p ⊕ [ ix i ] , skip , ⊑-refl _ , spin i , spin-reach p i }
  ; blocked = λ { refl after F → endless p after F }
  ; shadow  = λ { refl (body x , _) _ rp → ⊥-elim (proj₂ (aft d inv p ok x) refl (≼-≺-≺ {_} {p} {b₀} (⊑-≼ rp) (Equivalence.from T-≡ (<ᵖ-below p [])))) }
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

    -- Over reached rows, every row is reached.
    lift : ∀ {u : EmissionSet A} → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : MapT f u q e) → Reach (MapT f u) q e
    lift re x = reach-via (λ y _ d → src y , row y , dep-lbl (lbl-sym (lbl x)) (lbl-sym (lbl y)) d) (re (row x))

-- A MAP KEEPS THE TRUTH: each row lies on its input's, and is reached
-- once that one is, so a clean row lies on a clean one.
map-truth : ∀ {A B H} (f : A → B) {s s′ : Den A} → Rel H s s′ → Rel H (Op.map f s) (Op.map f s′)
map-truth {A} {B} f {s} {s′} R p ok = record
  { Cut     = Cut
  ; silent  = λ c sp x → lbl-silent (lbl (proj₁ x)) (silent c sp (row (proj₁ x)))
  ; shows   = λ c i → shown (shows c i)
  ; blocked = λ c after F → blocked c after (few F)
  ; shadow  = λ { c (map-pin y , _) l rs → shade (shadow c y l rs) }
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

    shade : ∀ {c r} → (Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × t z (pin r)) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Truncate (MapT f t) z (pin r)
    shade (z , z1 , tz) = z , z1 , map-pin tz , lift re (map-pin tz)

    few : ∀ {x} → Few (Truncate (MapT f t)) x → Few t x
    few (ks , h) = ks , λ y kx → h (proj₁ (proj₂ (image y))) kx

    clean : ∀ {q e e₀} → Clean Cut (Truncate (MapT f t)) q e → Lbl e₀ e → Clean Cut t q e₀
    clean (nl , ks , h) l = nl , ks , λ y kq d → h (proj₁ (proj₂ (image y))) kq (dep-lbl l (proj₂ (proj₂ (image y))) d)

-- EACH OPERATOR KEEPS THE TRUTH: every operator over children each
-- against the next.  A connect's body is read against its next under ONE
-- handle, and across the two handles by causality (`Causal`), as the
-- order modulus is (`settle`).
-- A DEFER KEEPS THE TRUTH: its body's cuts are its own, and its guard
-- is the same row either way.
defer-truth : ∀ {A H} {d d′ : Den A} → InvD H d → InvD H d′ → Rel H d d′ → Rel H (Op.defer d) (Op.defer d′)
defer-truth {A} {H} {d} {d′} inv inv′ R p ok = record
  { Cut     = Cut
  ; silent  = λ { _ _ (guard , _) → hush ; c sp (body x , _) → silent c sp x }
  ; shows   = λ c i → shown (shows c i)
  ; blocked = λ c after F → blocked c after (few F)
  ; shadow  = λ { c (body y , _) l rs → shade (shadow c y l rs) }
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

    shade : ∀ {c r} → (Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × enter d (p ⊕ [ ix 1 ]) z (pin r)) → Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × Truncate (DeferT d p) z (pin r)
    shade (z , z1 , tz) = z , z1 , body tz , in-body d tz

    few : ∀ {x} → Few (Truncate (DeferT d p)) x → Few (enter d (p ⊕ [ ix 1 ])) x
    few (ks , h) = ks , λ y kx → h (body y , in-body d y) kx

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

postulate
  scan-truth    : ∀ {A B H} (f : B → A → B) z {s s′ : Den A} → Rel H s s′ → Rel H (Op.scan f z s) (Op.scan f z s′)
  take-truth    : ∀ {A H} (i : Bool) (keep : A → Bool) {s s′ : Den A} → InvD H s → InvD H s′
                → Rel H s s′ → Rel H (Op.takeWhile i keep s) (Op.takeWhile i keep s′)
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
