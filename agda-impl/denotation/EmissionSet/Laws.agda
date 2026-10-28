{-# OPTIONS --guardedness #-}

-- THE EMISSION SET'S LAWS: the meaning of a node is its operator applied to its
-- children's meanings, so proofs over it go one operator at a time; and
-- `map` fuses.
--
-- THE ROUTE: the meaning is the limit of its approximants only because of
-- recursion through `defer`, so compositionality is the limit commuting
-- with each operator.  A chain CONVERGES to an observable (`Conv`) when,
-- wherever the observable is reached, the chain agrees with it at and
-- below from some index on.  A convergent chain's limit is that
-- observable (`conv-lim`); each operator carries convergence (`-cont`);
-- so the approximants converge to the meaning by structure (`settles`),
-- `defer` excepted, and each former's equation is `conv-lim` of its
-- operator's continuity.
module denotation.EmissionSet.Laws where

open import Data.Bool using (Bool; T)
open import Data.Bool.Properties using (T-≡)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _⊔_)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n; m≤n⊔m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; Equivalence)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline; Pos; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-asym)
open import denotation.EmissionSet
  using (Ev; out; skip; end; EmissionSet; _≺_; _≼_; Few; Truncate; Den; hot; enter; DenEnv; approxᵀ; Lim; from; ⟦_⟧ᵀ; coldᵀ; emptyᵀ; ofᵀ; mapᵀ; scanᵀ; takeWhileᵀ; flatMapᵀ; connectᵀ; deferᵀ;
         MapT; map-out; map-skip; map-end)

-- The same rows at every subscription.
_≅_ : ∀ {A} → Den A → Den A → Set
d ≅ d′ = ∀ p {q e} → (enter d p q e → enter d′ p q e) × (enter d′ p q e → enter d p q e)

private
  -- Rows before `q` in `t′` are rows of `t`, so as few.
  few-via : ∀ {A B} {t : EmissionSet A} {t′ : EmissionSet B} {q} → (∀ {k e} → t′ k e → Σ (Ev A) (t k)) → Few t q → Few t′ q
  few-via back (ks , h) = ks , λ x lt → h (proj₂ (back x)) lt

  -- A row read through `enter` has finitely many rows before it.
  entered-few : ∀ {A} (d : Den A) p {q e} → enter d p q e → Few (enter d p) q
  entered-few (hot t)  p (_ , F) = few-via (λ y → _ , proj₁ y) F
  entered-few (Den.cold f) p (_ , F) = few-via (λ y → _ , proj₁ y) F

  -- Limits of row-for-row alike sequences, truncated, are alike.
  lim-map : ∀ {A} {c c′ : ℕ → EmissionSet A} → (∀ {n q e} → c n q e → c′ n q e) → (∀ {n q e} → c′ n q e → c n q e)
          → ∀ {q e} → Truncate (Lim c) q e → Truncate (Lim c′) q e
  lim-map to back (from N h , F) = from N (λ n le → to (h n le)) , few-via (λ { (from M h′) → _ , from M λ n le → back (h′ n le) }) F

  -- A row of every approximant is a row of the limit, and back.
  constant : ∀ {A} (d : Den A) p {q e} → (Truncate (Lim (λ _ → enter d p)) q e → enter d p q e) × (enter d p q e → Truncate (Lim (λ _ → enter d p)) q e)
  constant d p = (λ { (from N h , _) → h N ≤-refl }) , λ x →
    from 0 (λ _ _ → x) , few-via (λ { (from N h) → _ , h N ≤-refl }) (entered-few d p x)

------------------------------------------------------------------------
-- The order on positions

private
  ≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
  ≺-trans {x} {y} {z} a b = Equivalence.from T-≡ (<ᵖ-trans x y z (Equivalence.to T-≡ a) (Equivalence.to T-≡ b))

  ≼-refl : ∀ {x} → x ≼ x
  ≼-refl {x} = subst (λ b → T b → ⊥) (sym (<ᵖ-irrefl x)) (λ ())

  ≺→≼ : ∀ {x y} → x ≺ y → x ≼ y
  ≺→≼ {x} {y} a = subst (λ b → T b → ⊥) (sym (<ᵖ-asym x y (Equivalence.to T-≡ a))) (λ ())

  ≺-≼ : ∀ {x y z} → x ≺ y → y ≼ z → x ≼ z
  ≺-≼ {x} {y} {z} a b c = b (≺-trans {z} {x} {y} c a)

------------------------------------------------------------------------
-- Convergence

-- At and below `q`, the same rows.
AgreeTo : ∀ {A} → Pos → EmissionSet A → EmissionSet A → Set
AgreeTo q t t′ = ∀ {y e} → y ≼ q → (t y e → t′ y e) × (t′ y e → t y e)

-- `c` CONVERGES to `d`: wherever `d` is reached, the chain agrees with it
-- at and below from some index on.
record Conv {A} (c : ℕ → Den A) (d : Den A) : Set where
  field at : ∀ p {q} → Few (enter d p) q → Σ ℕ λ N → ∀ n → N ≤ n → AgreeTo q (enter (c n) p) (enter d p)

-- A chain's limit.
LimD : ∀ {A} → (ℕ → Den A) → Den A
LimD c = Den.cold λ p → Lim λ n → enter (c n) p

-- Every handle of an environment converges.
record EnvConv {Γ} (ρs : ℕ → DenEnv Γ) (ρ : DenEnv Γ) : Set₁ where
  field at : ∀ {A} (i : A ∈ Γ) → Conv (λ n → lookup (ρs n) i) (lookup ρ i)

record Compositionalᵀ : Set₁ where
  field
    coldᶜ      : ∀ {Γ A} (c : Timeline A) (ρ : DenEnv Γ) → ⟦ cold c ⟧ᵀ ρ ≅ coldᵀ c
    emptyᶜ     : ∀ {Γ A} (ρ : DenEnv Γ) → ⟦ empty {Γ = Γ} {A = A} ⟧ᵀ ρ ≅ emptyᵀ
    ofᶜ        : ∀ {Γ A} (xs : List A) (ρ : DenEnv Γ) → ⟦ of {Γ = Γ} xs ⟧ᵀ ρ ≅ ofᵀ xs
    mapᶜ       : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ map f s ⟧ᵀ ρ ≅ mapᵀ f (⟦ s ⟧ᵀ ρ)
    scanᶜ      : ∀ {Γ A B} (f : B → A → B) z (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ scan f z s ⟧ᵀ ρ ≅ scanᵀ f z (⟦ s ⟧ᵀ ρ)
    takeWhileᶜ : ∀ {Γ A} (i : Bool) (k : A → Bool) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ takeWhile i k s ⟧ᵀ ρ ≅ takeWhileᵀ i k (⟦ s ⟧ᵀ ρ)
    flatMapᶜ   : ∀ {Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
               → ⟦ flatMap op f s ⟧ᵀ ρ ≅ flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ)
    connectᶜ   : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ)
               → ⟦ connect s b ⟧ᵀ ρ ≅ connectᵀ (⟦ s ⟧ᵀ ρ) (λ h → ⟦ b ⟧ᵀ (h ∷ ρ))
    connectedᶜ : ∀ {Γ A} (i : A ∈ Γ) (ρ : DenEnv Γ) → ⟦ connected i ⟧ᵀ ρ ≅ lookup ρ i
    deferᶜ     : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → ⟦ defer l ⟧ᵀ ρ ≅ deferᵀ (⟦ Later.force l ⟧ᵀ ρ)

------------------------------------------------------------------------
-- A convergent chain's limit

-- `_≅_` carries convergence.
conv-resp : ∀ {A} {c : ℕ → Den A} {d d′} → Conv c d → d ≅ d′ → Conv c d′
Conv.at (conv-resp {d = d} {d′} cv eq) p F with Conv.at cv p (few-via (λ y → _ , proj₁ (eq p) y) F)
... | N , ag = N , λ n le yq → (λ x → proj₁ (eq p) (proj₁ (ag n le yq) x)) , λ x → proj₂ (ag n le yq) (proj₂ (eq p) x)

-- A constant chain converges to its value.
conv-const : ∀ {A} (d : Den A) → Conv (λ _ → d) d
Conv.at (conv-const d) p F = 0 , λ n le yq → (λ x → x) , (λ x → x)

-- Convergence is from some index on.
conv-pred : ∀ {A} {c : ℕ → Den A} {d} → Conv (c ∘ suc) d → Conv c d
Conv.at (conv-pred cv) p F with Conv.at cv p F
... | N , ag = suc N , λ { zero () ; (suc n) (s≤s le) → ag n le }

-- THE LIMIT OF A CONVERGENT CHAIN is what it converges to.
conv-lim : ∀ {A} {c : ℕ → Den A} {d} → Conv c d → LimD c ≅ d
conv-lim {c = c} {d} cv p = to , back
  where
    -- A row of `d` is a row of every approximant from some index on.
    down : ∀ {q e} → enter d p q e → Lim (λ n → enter (c n) p) q e
    down {q} x with Conv.at cv p (entered-few d p x)
    ... | N , ag = from N λ n le → proj₂ (ag n le (≼-refl {q})) x

    -- A row of the limit before a reached `q` is a row of `d`.
    up : ∀ {q y e} → Few (enter d p) q → y ≺ q → Lim (λ n → enter (c n) p) y e → enter d p y e
    up {q} {y} F yq (from M h) with Conv.at cv p F
    ... | N , ag = proj₁ (ag (M ⊔ N) (m≤n⊔m M N) (≺→≼ {y} {q} yq)) (h (M ⊔ N) (m≤m⊔n M N))

    back : ∀ {q e} → enter d p q e → Truncate (Lim λ n → enter (c n) p) q e
    back x = down x , few-via-at (entered-few d p x)
      where
        few-via-at : ∀ {q} → Few (enter d p) q → Few (Lim λ n → enter (c n) p) q
        few-via-at F@(ks , cov) = ks , λ y yq → cov (up F yq y) yq

    -- `d` is reached wherever the limit is: each of its rows is a limit row.
    reached : ∀ {q} → Few (Lim λ n → enter (c n) p) q → Few (enter d p) q
    reached (ks , cov) = ks , λ x yq → cov (down x) yq

    to : ∀ {q e} → Truncate (Lim λ n → enter (c n) p) q e → enter d p q e
    to {q} {e} (from M h , F) = up′ (reached F)
      where
        up′ : Few (enter d p) q → enter d p q e
        up′ G with Conv.at cv p G
        ... | N , ag = proj₁ (ag (M ⊔ N) (m≤n⊔m M N) (≼-refl {q})) (h (M ⊔ N) (m≤m⊔n M N))

------------------------------------------------------------------------
-- Each operator carries convergence

-- MAP: a row of the map is a row of its input at the same position.
private
  -- Rows before `q` of `t′` are rows of `t`, so as few.
  few-below : ∀ {A B} {t : EmissionSet A} {t′ : EmissionSet B} {q} → (∀ {k e} → t′ k e → k ≺ q → Σ (Ev A) (t k)) → Few t q → Few t′ q
  few-below back (ks , h) = ks , λ x lt → h (proj₂ (back x lt)) lt

  map-in : ∀ {A B} {f : A → B} {t : EmissionSet A} {k e} → MapT f t k e → Σ (Ev A) (t k)
  map-in (map-out x)  = _ , x
  map-in (map-skip x) = _ , x
  map-in (map-end x)  = _ , x

  map-of : ∀ {A B} {f : A → B} {t : EmissionSet A} {k e} → t k e → Σ (Ev B) (MapT f t k)
  map-of {e = out a} x = _ , map-out x
  map-of {e = skip}  x = _ , map-skip x
  map-of {e = end}   x = _ , map-end x

  map-row : ∀ {A B} {f : A → B} {t t′ : EmissionSet A} {k e} → (∀ {e} → t k e → t′ k e) → MapT f t k e → MapT f t′ k e
  map-row g (map-out x)  = map-out (g x)
  map-row g (map-skip x) = map-skip (g x)
  map-row g (map-end x)  = map-end (g x)

  -- Readings alike at and below `q` map alike.
  map-agree : ∀ {A B} (f : A → B) {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → AgreeTo q (Truncate (MapT f t)) (Truncate (MapT f t′))
  map-agree f {q = q} ag {y} yq =
      (λ { (m , G) → map-row (λ x → proj₁ (ag yq) x) m , few-below (λ {k} m′ kq → _ , map-row (λ x → proj₂ (ag (≺-≼ {k} {y} {q} kq yq)) x) m′) G })
    , (λ { (m , G) → map-row (λ x → proj₂ (ag yq) x) m , few-below (λ {k} m′ kq → _ , map-row (λ x → proj₁ (ag (≺-≼ {k} {y} {q} kq yq)) x) m′) G })

map-cont : ∀ {A B} (f : A → B) {c : ℕ → Den A} {d} → Conv c d → Conv (λ n → mapᵀ f (c n)) (mapᵀ f d)
Conv.at (map-cont f {c} {d} cv) p {q} F with Conv.at cv p (few-below (λ x _ → _ , proj₂ (map-of {f = f} x) , few-via map-in (entered-few d p x)) F)
... | N , ag = N , λ n le → map-agree f {q = q} (ag n le)

postulate
  scan-cont      : ∀ {A B} (f : B → A → B) z {c : ℕ → Den A} {d} → Conv c d → Conv (λ n → scanᵀ f z (c n)) (scanᵀ f z d)
  takeWhile-cont : ∀ {A} (i : Bool) (k : A → Bool) {c : ℕ → Den A} {d} → Conv c d → Conv (λ n → takeWhileᵀ i k (c n)) (takeWhileᵀ i k d)
  defer-cont     : ∀ {A} {c : ℕ → Den A} {d} → Conv c d → Conv (λ n → deferᵀ (c n)) (deferᵀ d)
  flatMap-cont   : ∀ {A B} (op : FlatOp) {fs : ℕ → A → Den B} {g} {c : ℕ → Den A} {d}
                 → Conv c d → (∀ a → Conv (λ n → fs n a) (g a)) → Conv (λ n → flatMapᵀ op (fs n) (c n)) (flatMapᵀ op g d)
  connect-cont   : ∀ {A B} {c : ℕ → Den A} {d} {Fs : ℕ → Den A → Den B} {G}
                 → Conv c d → (∀ {hs : ℕ → EmissionSet A} {h} → Conv (λ n → hot (hs n)) (hot h) → Conv (λ n → Fs n (hot (hs n))) (G (hot h)))
                 → Conv (λ n → connectᵀ (c n) (Fs n)) (connectᵀ d G)

  -- THE RECURSION SETTLES: past enough approximants, a `defer`'s rows at
  -- and below a reached row stop changing.
  settles-defer : ∀ {Γ A} (l : Later Timeline Γ A) {ρs : ℕ → DenEnv Γ} {ρ} → EnvConv ρs ρ
                → Conv (λ n → approxᵀ n (defer l) (ρs n)) (⟦ defer l ⟧ᵀ ρ)

------------------------------------------------------------------------
-- The approximants converge to the meaning

private
  env-const : ∀ {Γ} (ρ : DenEnv Γ) → EnvConv (λ _ → ρ) ρ
  EnvConv.at (env-const ρ) i = conv-const (lookup ρ i)

  env-cons : ∀ {Γ A} {c : ℕ → Den A} {d} {ρs : ℕ → DenEnv Γ} {ρ} → Conv c d → EnvConv ρs ρ → EnvConv (λ n → c n ∷ ρs n) (d ∷ ρ)
  EnvConv.at (env-cons cv ec) (here refl) = cv
  EnvConv.at (env-cons cv ec) (there i)   = EnvConv.at ec i

  -- `conv-resp`, read from the target.
  conv-back : ∀ {A} {c : ℕ → Den A} {d} d′ → Conv c d → d′ ≅ d → Conv c d′
  conv-back d′ cv eq = conv-resp cv λ p → proj₂ (eq p) , proj₁ (eq p)

-- By structure: an operator's chain converges to the operator applied to
-- its children's meanings, which is the operator's meaning by `conv-lim`.
settles : ∀ {Γ A} (o : Obs Timeline Γ A) {ρs : ℕ → DenEnv Γ} {ρ} → EnvConv ρs ρ → Conv (λ n → approxᵀ n o (ρs n)) (⟦ o ⟧ᵀ ρ)

-- An operator's meaning, through the limit: each approximant applies the
-- operator to its children's approximants, and the limit commutes with it.
map-lim : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ map f s ⟧ᵀ ρ ≅ mapᵀ f (⟦ s ⟧ᵀ ρ)
map-lim f s ρ = conv-lim (map-cont f (settles s (env-const ρ)))

scan-lim : ∀ {Γ A B} (f : B → A → B) z (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ scan f z s ⟧ᵀ ρ ≅ scanᵀ f z (⟦ s ⟧ᵀ ρ)
scan-lim f z s ρ = conv-lim (scan-cont f z (settles s (env-const ρ)))

takeWhile-lim : ∀ {Γ A} (i : Bool) (k : A → Bool) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ takeWhile i k s ⟧ᵀ ρ ≅ takeWhileᵀ i k (⟦ s ⟧ᵀ ρ)
takeWhile-lim i k s ρ = conv-lim (takeWhile-cont i k (settles s (env-const ρ)))

flatMap-lim : ∀ {Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
            → ⟦ flatMap op f s ⟧ᵀ ρ ≅ flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ)
flatMap-lim op f s ρ = conv-lim (flatMap-cont op {fs = λ n a → approxᵀ n (f a) ρ} {g = λ a → ⟦ f a ⟧ᵀ ρ} {c = λ n → approxᵀ n s ρ} {d = ⟦ s ⟧ᵀ ρ}
  (settles s (env-const ρ)) λ a → settles (f a) (env-const ρ))

connect-lim : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ)
            → ⟦ connect s b ⟧ᵀ ρ ≅ connectᵀ (⟦ s ⟧ᵀ ρ) (λ h → ⟦ b ⟧ᵀ (h ∷ ρ))
connect-lim s b ρ = conv-lim (connect-cont {c = λ n → approxᵀ n s ρ} {d = ⟦ s ⟧ᵀ ρ} {Fs = λ n h → approxᵀ n b (h ∷ ρ)} {G = λ h → ⟦ b ⟧ᵀ (h ∷ ρ)}
  (settles s (env-const ρ)) λ {hs} {h} hc → settles b {λ n → hot (hs n) ∷ ρ} {hot h ∷ ρ} (env-cons hc (env-const ρ)))

-- The approximants from 1 on are `deferᵀ` of the body's.
defer-lim : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → ⟦ defer l ⟧ᵀ ρ ≅ deferᵀ (⟦ Later.force l ⟧ᵀ ρ)
defer-lim l ρ = conv-lim {c = λ n → approxᵀ n (defer l) ρ} {d = deferᵀ (⟦ Later.force l ⟧ᵀ ρ)}
  (conv-pred {c = λ n → approxᵀ n (defer l) ρ} (defer-cont {c = λ n → approxᵀ n (Later.force l) ρ} {d = ⟦ Later.force l ⟧ᵀ ρ}
    (settles (Later.force l) {λ _ → ρ} {ρ} (env-const ρ))))

settles (cold c)          {ρ = ρ} ec = conv-back (⟦ cold c ⟧ᵀ ρ) (conv-const (coldᵀ c)) (λ p → constant (coldᵀ c) p)
settles empty             {ρ = ρ} ec = conv-back (⟦ empty ⟧ᵀ ρ) (conv-const emptyᵀ) (λ p → constant emptyᵀ p)
settles (of xs)           {ρ = ρ} ec = conv-back (⟦ of xs ⟧ᵀ ρ) (conv-const (ofᵀ xs)) (λ p → constant (ofᵀ xs) p)
settles (map f s) {ρ = ρ} ec =
  conv-back (⟦ map f s ⟧ᵀ ρ) (map-cont f (settles s ec)) (map-lim f s ρ)
settles (scan f z s) {ρ = ρ} ec =
  conv-back (⟦ scan f z s ⟧ᵀ ρ) (scan-cont f z (settles s ec)) (scan-lim f z s ρ)
settles (takeWhile i k s) {ρ = ρ} ec =
  conv-back (⟦ takeWhile i k s ⟧ᵀ ρ) (takeWhile-cont i k (settles s ec)) (takeWhile-lim i k s ρ)
settles (flatMap op f s) {ρs} {ρ} ec =
  conv-back (⟦ flatMap op f s ⟧ᵀ ρ)
    (flatMap-cont op {fs = λ n a → approxᵀ n (f a) (ρs n)} {g = λ a → ⟦ f a ⟧ᵀ ρ} (settles s ec) λ a → settles (f a) ec)
    (flatMap-lim op f s ρ)
settles (connect s b) {ρs} {ρ} ec =
  conv-back (⟦ connect s b ⟧ᵀ ρ)
    (connect-cont {Fs = λ n h → approxᵀ n b (h ∷ ρs n)} {G = λ h → ⟦ b ⟧ᵀ (h ∷ ρ)} (settles s ec)
      λ {hs} {h} hc → settles b {λ n → hot (hs n) ∷ ρs n} {hot h ∷ ρ} (env-cons hc ec))
    (connect-lim s b ρ)
settles (connected i) {ρ = ρ} ec = conv-back (⟦ connected i ⟧ᵀ ρ) (EnvConv.at ec i) (λ p → constant (lookup ρ i) p)
settles (defer l)         ec = settles-defer l ec

-- THE MEANING IS COMPOSITIONAL.
compositionalᵀ : Compositionalᵀ
compositionalᵀ = record
  { coldᶜ      = λ c ρ → constant (coldᵀ c)
  ; emptyᶜ     = λ ρ → constant emptyᵀ
  ; ofᶜ        = λ xs ρ → constant (ofᵀ xs)
  ; mapᶜ       = map-lim
  ; scanᶜ      = scan-lim
  ; takeWhileᶜ = takeWhile-lim
  ; flatMapᶜ   = flatMap-lim
  ; connectᶜ   = connect-lim
  ; connectedᶜ = λ i ρ → constant (lookup ρ i)
  ; deferᶜ     = defer-lim
  }

-- MAP FUSES: `map (f ∘ g)` and `map f ∘ map g` have the same rows.
map-fusionᵀ : ∀ {Γ A B C} (f : B → C) (g : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
            → ⟦ map (f ∘ g) s ⟧ᵀ ρ ≅ ⟦ map f (map g s) ⟧ᵀ ρ
map-fusionᵀ f g s ρ p = lim-map fuse split , lim-map split fuse
  where
    down : ∀ {t k e} → MapT (f ∘ g) t k e → Σ (Ev _) (MapT g t k)
    down (map-out x)  = _ , map-out x
    down (map-skip x) = _ , map-skip x
    down (map-end x)  = _ , map-end x

    up : ∀ {t k e} → MapT g t k e → Σ (Ev _) (MapT (f ∘ g) t k)
    up (map-out x)  = _ , map-out x
    up (map-skip x) = _ , map-skip x
    up (map-end x)  = _ , map-end x

    across : ∀ {t k e} → MapT f (Truncate (MapT g t)) k e → Σ (Ev _) (MapT (f ∘ g) t k)
    across (map-out (map-out x , _))   = _ , map-out x
    across (map-skip (map-skip x , _)) = _ , map-skip x
    across (map-end (map-end x , _))   = _ , map-end x

    fuse : ∀ {t q e} → Truncate (MapT (f ∘ g) t) q e → Truncate (MapT f (Truncate (MapT g t))) q e
    fuse (map-out x , F)  = map-out (map-out x , few-via up F) , few-via across F
    fuse (map-skip x , F) = map-skip (map-skip x , few-via up F) , few-via across F
    fuse (map-end x , F)  = map-end (map-end x , few-via up F) , few-via across F

    split : ∀ {t q e} → Truncate (MapT f (Truncate (MapT g t))) q e → Truncate (MapT (f ∘ g) t) q e
    split (map-out (map-out x , G) , _)   = map-out x , few-via down G
    split (map-skip (map-skip x , G) , _) = map-skip x , few-via down G
    split (map-end (map-end x , G) , _)   = map-end x , few-via down G
