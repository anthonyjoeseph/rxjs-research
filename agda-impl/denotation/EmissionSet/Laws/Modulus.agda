{-# OPTIONS --guardedness #-}

-- THE MODULUS: how far two observables agree, by the size of a row.  A
-- `defer` unfolded once more changes rows only past one more nested
-- subscription, and a nested subscription is a longer position, so two
-- approximants agree on every row that the smaller reaches through rows
-- of bounded size.  The bound is STRICT and the agreement INCLUSIVE: the
-- rows before `q` are small on one side, and then both sides agree at and
-- below `q`.  A row bigger than the bound may itself be the first to
-- differ; nothing past it is promised.
--
-- One side suffices: what is small on one side and agrees is small on the
-- other, so the relation is transitive, and a chain of approximants each
-- within the next agrees with its limit (`limit`).  Agreement at every
-- bound is having the same rows (`agree-all`).
module denotation.EmissionSet.Laws.Modulus where

open import Data.Bool using (T; true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length; filter)
open import Data.List.Properties using (filter-notAll)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _⊔_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; +-mono-≤; m≤n+m; m≤m⊔n; m≤n⊔m; m∸n+n≡m; +-assoc; +-comm; +-identityʳ; n≮n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; _<ᵖ_; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-split; <ᵖ-part; <ᵖ-below)
open import denotation.EmissionSet
  using (Ev; EmissionSet; _≺_; _≼_; Few; Truncate; Den; hot; cold; enter; Lim; from; Spin; spin; ⊥ᵀ; DeferT; guard; body; deferᵀ)

------------------------------------------------------------------------
-- The order on positions

≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
≺-trans {x} {y} {z} a b = Equivalence.from T-≡ (<ᵖ-trans x y z (Equivalence.to T-≡ a) (Equivalence.to T-≡ b))

≺-irrefl : ∀ {x} → x ≺ x → ⊥
≺-irrefl {x} a = subst T (<ᵖ-irrefl x) a

≺-absurd : ∀ {x y} → x ≺ y → y ≺ x → ⊥
≺-absurd {x} {y} a b = ≺-irrefl {x} (≺-trans {x} {y} {x} a b)

≼-refl : ∀ {x} → x ≼ x
≼-refl {x} = ≺-irrefl {x}

≺→≼ : ∀ {x y} → x ≺ y → x ≼ y
≺→≼ {x} {y} a b = subst T (<ᵖ-asym x y (Equivalence.to T-≡ a)) b

private
  ≼-false : ∀ {y q} → y ≼ q → q <ᵖ y ≡ false
  ≼-false {y} {q} h with q <ᵖ y
  ... | true  = ⊥-elim (h tt)
  ... | false = refl

-- Before what is at or before `q`: before `q`.
≺-≼-≺ : ∀ {w y q} → w ≺ y → y ≼ q → w ≺ q
≺-≼-≺ {w} {y} {q} wy yq with <ᵖ-split y q (≼-false {y} {q} yq)
... | inj₁ lt   = ≺-trans {w} {y} {q} wy (Equivalence.from T-≡ lt)
... | inj₂ refl = wy

-- Before what is after what is at or before: before.
≼-≺-≺ : ∀ {x y z} → x ≼ y → y ≺ z → x ≺ z
≼-≺-≺ {x} {y} {z} xy yz with <ᵖ-split x y (≼-false {x} {y} xy)
... | inj₁ lt   = ≺-trans {x} {y} {z} (Equivalence.from T-≡ lt) yz
... | inj₂ refl = yz

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans {x} {y} {z} xy yz zx = yz (≺-≼-≺ {z} {x} {y} zx xy)

-- At or before, or after.
≼-or-≻ : ∀ x q → x ≼ q ⊎ q ≺ x
≼-or-≻ x q with q <ᵖ x
... | true  = inj₂ tt
... | false = inj₁ (λ ())

-- A position comes before its extensions.
≺-ext : ∀ x {l} ys → x ≺ (x ++ l ∷ ys)
≺-ext x ys = Equivalence.from T-≡ (<ᵖ-below x ys)

------------------------------------------------------------------------
-- Few

-- Rows of `t′` are rows of `t`, so as few.
few-via : ∀ {A B} {t : EmissionSet A} {t′ : EmissionSet B} {q} → (∀ {k e} → t′ k e → Σ (Ev A) (t k)) → Few t q → Few t′ q
few-via back (ks , h) = ks , λ x lt → h (proj₂ (back x)) lt

-- Fewer before an earlier position.
few-down : ∀ {A} {t : EmissionSet A} {y w} → Few t y → w ≺ y → Few t w
few-down {y = y} {w} (ks , h) wy = ks , λ {k} x kw → h x (≺-trans {k} {w} {y} kw wy)

-- A row read through `enter` has finitely many rows before it.
entered-few : ∀ {A} (d : Den A) p {q e} → enter d p q e → Few (enter d p) q
entered-few (hot t)  p (_ , F) = few-via (λ y → _ , proj₁ y) F
entered-few (cold f) p (_ , F) = few-via (λ y → _ , proj₁ y) F

-- INDUCTION ON THE ROWS BEFORE: a property that holds of a row once it
-- holds of every row before it holds of every row with few before it.
few-ind : ∀ {A} {t : EmissionSet A} (P : Pos → Set)
        → (∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → P v) → P w)
        → ∀ {w} → Few t w → P w
few-ind {t = t} P step F = go (length (proj₁ F)) F ≤-refl
  where
    go : ∀ n {w} (F : Few t w) → length (proj₁ F) ≤ n → P w
    go zero    ([] , h)    le = step ([] , h) λ x vw → ⊥-elim (none (h x vw))
      where none : ∀ {v : Pos} → v ∈ [] → ⊥
            none ()
    go (suc n) {w} (ks , h) le = step (ks , h) λ {v} x vw →
      go n (filter (λ k → T? (k <ᵖ v)) ks , λ {k} y kv → ∈-filter⁺ (λ k → T? (k <ᵖ v)) (h y (≺-trans {k} {v} {w} kv vw)) kv)
        (≤-pred (≤-trans (filter-notAll (λ k → T? (k <ᵖ v)) ks (Any.map (λ { refl → ≺-irrefl {v} }) (h x vw))) le))

------------------------------------------------------------------------
-- Agreement

-- At and below `q`, the same rows.
record AgreeTo {A} (q : Pos) (t t′ : EmissionSet A) : Set where
  constructor ⟨_⟩
  field upto : ∀ {y e} → y ≼ q → (t y e → t′ y e) × (t′ y e → t y e)

open AgreeTo public

AgreeTo-sym : ∀ {A} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → AgreeTo q t′ t
AgreeTo-sym ⟨ a ⟩ = ⟨ (λ {y} {e} yq → proj₂ (a {y} {e} yq) , proj₁ (a {y} {e} yq)) ⟩

AgreeTo-trans : ∀ {A} {t u v : EmissionSet A} {q} → AgreeTo q t u → AgreeTo q u v → AgreeTo q t v
AgreeTo-trans ⟨ a ⟩ ⟨ b ⟩ = ⟨ (λ {y} {e} yq → proj₁ (b {y} {e} yq) ∘ proj₁ (a {y} {e} yq) , proj₂ (a {y} {e} yq) ∘ proj₂ (b {y} {e} yq)) ⟩

-- Agreeing at and below `q`, rows before `q` are as few.
few-agree : ∀ {A} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → Few t q → Few t′ q
few-agree {q = q} a (ks , h) = ks , λ {k} {e′} x kq → h (proj₂ (upto a {k} {e′} (≺→≼ {k} {q} kq)) x) kq

------------------------------------------------------------------------
-- Size

mutual
  sizeˡ : Label → ℕ
  sizeˡ (ix _)  = 1
  sizeˡ (sub e) = suc (size e)
  sizeˡ last    = 1

  size : Pos → ℕ
  size []      = 0
  size (l ∷ p) = sizeˡ l + size p

size-++ : ∀ p l → size (p ++ [ l ]) ≡ size p + sizeˡ l
size-++ []      l = +-identityʳ (sizeˡ l)
size-++ (x ∷ p) l rewrite size-++ p l = sym (+-assoc (sizeˡ x) (size p) (sizeˡ l))

-- Every row before `q` is of size at most `B`.
Bnd< : ∀ {A} → ℕ → EmissionSet A → Pos → Set
Bnd< B t q = ∀ {y e} → t y e → y ≺ q → size y ≤ B

-- WITHIN `B`: bounded before `q` on either side, the two agree at and
-- below `q`.
AgS : ∀ {A} → ℕ → EmissionSet A → EmissionSet A → Set
AgS B t t′ = ∀ q → Bnd< B t q ⊎ Bnd< B t′ q → AgreeTo q t t′

AgS-refl : ∀ {A B} {t : EmissionSet A} → AgS B t t
AgS-refl q _ = ⟨ (λ yq → (λ x → x) , (λ x → x)) ⟩

AgS-sym : ∀ {A B} {t t′ : EmissionSet A} → AgS B t t′ → AgS B t′ t
AgS-sym ag q (inj₁ b) = AgreeTo-sym (ag q (inj₂ b))
AgS-sym ag q (inj₂ b) = AgreeTo-sym (ag q (inj₁ b))

AgS-mono : ∀ {A B B′} {t t′ : EmissionSet A} → B ≤ B′ → AgS B′ t t′ → AgS B t t′
AgS-mono le ag q (inj₁ b) = ag q (inj₁ λ x yq → ≤-trans (b x yq) le)
AgS-mono le ag q (inj₂ b) = ag q (inj₂ λ x yq → ≤-trans (b x yq) le)

AgS-trans : ∀ {A B} {t u v : EmissionSet A} → AgS B t u → AgS B u v → AgS B t v
AgS-trans {B = B} {t} {u} {v} tu uv q (inj₁ b) = AgreeTo-trans a₁ (uv q (inj₁ bu))
  where
    a₁ = tu q (inj₁ b)
    bu : Bnd< B u q
    bu {y} {e} x yq = b (proj₂ (upto a₁ {y} {e} (≺→≼ {y} {q} yq)) x) yq
AgS-trans {B = B} {t} {u} {v} tu uv q (inj₂ b) = AgreeTo-trans (tu q (inj₂ bu)) a₂
  where
    a₂ = uv q (inj₂ b)
    bu : Bnd< B u q
    bu {y} {e} x yq = b (proj₁ (upto a₂ {y} {e} (≺→≼ {y} {q} yq)) x) yq

-- TRUNCATION KEEPS AGREEMENT: a reached row up to a bounded `q` has only
-- reached rows before it, so they are bounded, and the wholes agree there.
private
  trunc-at : ∀ {A B} {t t′ : EmissionSet A} {q} → AgS B t t′ → Bnd< B (Truncate t) q
           → ∀ {y e} → y ≼ q → (Truncate t y e → Truncate t′ y e) × (Truncate t′ y e → Truncate t y e)
  trunc-at {B = B} {t} {t′} {q} ag bd {y} {e} yq = there′ , back
    where
      there′ : Truncate t y e → Truncate t′ y e
      there′ (x , F) = proj₁ (upto a {y} {e} (≼-refl {y})) x , few-agree a F
        where
          bt : Bnd< B t y
          bt {w} tw wy = bd (tw , few-down F wy) (≺-≼-≺ {w} {y} {q} wy yq)
          a = ag y (inj₁ bt)

      step : ∀ {w} → Few t′ w → (∀ {v e} → t′ v e → v ≺ w → v ≼ q → Bnd< B t′ v) → w ≼ q → Bnd< B t′ w
      step {w} Fw ih wq {v} t′v vw = bd (proj₂ (upto av {v} (≼-refl {v})) t′v , few-agree (AgreeTo-sym av) (few-down Fw vw)) vq
        where
          vq = ≺-≼-≺ {v} {w} {q} vw wq
          av = ag v (inj₂ (ih t′v vw (≺→≼ {v} {q} vq)))

      back : Truncate t′ y e → Truncate t y e
      back (x′ , F′) = proj₂ (upto a {y} {e} (≼-refl {y})) x′ , few-agree (AgreeTo-sym a) F′
        where a = ag y (inj₂ (few-ind (λ w → w ≼ q → Bnd< B t′ w) step F′ yq))

  trunc-ag₁ : ∀ {A B} {t t′ : EmissionSet A} {q} → AgS B t t′ → Bnd< B (Truncate t) q → AgreeTo q (Truncate t) (Truncate t′)
  trunc-ag₁ ag bd = ⟨ trunc-at ag bd ⟩

trunc-ag : ∀ {A B} {t t′ : EmissionSet A} → AgS B t t′ → AgS B (Truncate t) (Truncate t′)
trunc-ag ag q (inj₁ b) = trunc-ag₁ {q = q} ag b
trunc-ag ag q (inj₂ b) = AgreeTo-sym (trunc-ag₁ {q = q} (AgS-sym ag) b)

------------------------------------------------------------------------
-- Observables within a bound

-- Within `k` past the subscription, wherever `R` admits one.
_≈⟨_∣_⟩_ : ∀ {A} → Den A → (Pos → Set) → ℕ → Den A → Set
d ≈⟨ R ∣ k ⟩ d′ = ∀ p → R p → AgS (size p + k) (enter d p) (enter d′ p)

≈-refl : ∀ {A R k} (d : Den A) → d ≈⟨ R ∣ k ⟩ d
≈-refl d p r = AgS-refl

≈-mono : ∀ {A R j k} {d d′ : Den A} → j ≤ k → d ≈⟨ R ∣ k ⟩ d′ → d ≈⟨ R ∣ j ⟩ d′
≈-mono le ag p r = AgS-mono (+-mono-≤ (≤-refl {size p}) le) (ag p r)

≈-sym : ∀ {A R k} {d d′ : Den A} → d ≈⟨ R ∣ k ⟩ d′ → d′ ≈⟨ R ∣ k ⟩ d
≈-sym ag p r = AgS-sym (ag p r)

≈-trans : ∀ {A R k} {d d′ d″ : Den A} → d ≈⟨ R ∣ k ⟩ d′ → d′ ≈⟨ R ∣ k ⟩ d″ → d ≈⟨ R ∣ k ⟩ d″
≈-trans a b p r = AgS-trans (a p r) (b p r)

-- The same rows at every subscription `R` admits.
Same : ∀ {A} → (Pos → Set) → Den A → Den A → Set
Same R d d′ = ∀ p → R p → ∀ {q e} → (enter d p q e → enter d′ p q e) × (enter d′ p q e → enter d p q e)

private
  maxSize : List Pos → ℕ
  maxSize []       = 0
  maxSize (k ∷ ks) = size k ⊔ maxSize ks

  ∈-max : ∀ {k ks} → k ∈ ks → size k ≤ maxSize ks
  ∈-max {ks = k′ ∷ ks} (here refl) = m≤m⊔n (size k′) (maxSize ks)
  ∈-max {ks = k′ ∷ ks} (there i)   = ≤-trans (∈-max i) (m≤n⊔m (size k′) (maxSize ks))

  -- A reached row's predecessors are bounded by the largest of them.
  bounded : ∀ {A} (d : Den A) p {q e} → enter d p q e → Σ ℕ λ k → Bnd< (size p + k) (enter d p) q
  bounded d p x with entered-few d p x
  ... | ks , h = maxSize ks , λ y yq → ≤-trans (∈-max (h y yq)) (m≤n+m (maxSize ks) (size p))

-- AGREEING AT EVERY BOUND IS THE SAME ROWS.
agree-all : ∀ {A R} {d d′ : Den A} → (∀ k → d ≈⟨ R ∣ k ⟩ d′) → Same R d d′
agree-all {d = d} {d′} all p r {q} = to , back
  where
    to : ∀ {e} → enter d p q e → enter d′ p q e
    to x with bounded d p x
    ... | k , b = proj₁ (upto (all k p r q (inj₁ b)) {q} (≼-refl {q})) x

    back : ∀ {e} → enter d′ p q e → enter d p q e
    back x with bounded d′ p x
    ... | k , b = proj₂ (upto (all k p r q (inj₂ b)) {q} (≼-refl {q})) x

------------------------------------------------------------------------
-- The limit of a chain

-- A row every member has from some index on, read where reached.
LimD : ∀ {A} → (ℕ → Den A) → Den A
LimD c = cold λ p → Lim λ n → enter (c n) p

-- THE LIMIT: each member of a chain within the next is within its limit.
-- Bounded before `q` in member `k`, every later member agrees with it, so
-- the limit does; bounded in the limit, member `k` is bounded too — its
-- first big row, its predecessors bounded, would be every later member's,
-- so the limit's.
limit : ∀ {A R} {c : ℕ → Den A} → (∀ n → c n ≈⟨ R ∣ n ⟩ c (suc n)) → ∀ k → c k ≈⟨ R ∣ k ⟩ LimD c
limit {c = c} ch k p r = top
  where
    X : ℕ → EmissionSet _
    X n = enter (c n) p

    B = size p + k

    ahead : ∀ j → AgS B (X k) (X (j + k))
    ahead zero    = AgS-refl
    ahead (suc j) = AgS-trans (ahead j) (AgS-mono (+-mono-≤ (≤-refl {size p}) (m≤n+m k j)) (ch (j + k) p r))

    at : ∀ n → k ≤ n → AgS B (X k) (X n)
    at n le = subst (λ m → AgS B (X k) (X m)) (m∸n+n≡m le) (ahead (n ∸ k))

    L = Truncate (Lim X)

    agrees′ : ∀ {q} → Bnd< B (X k) q → ∀ {y e} → y ≼ q → (X k y e → L y e) × (L y e → X k y e)
    agrees′ {q} bx {y} {e} yq = to , back
      where
        ag : ∀ n → k ≤ n → AgreeTo q (X k) (X n)
        ag n le = at n le q (inj₁ bx)

        to : X k y e → L y e
        to x = from k (λ n le → proj₁ (upto (ag n le) {y} yq) x) , few
          where
            few : Few (Lim X) y
            few with entered-few (c k) p x
            ... | ks , h = ks , λ { {v} (from N l) vy →
              h (proj₂ (upto (ag (N ⊔ k) (m≤n⊔m N k)) {v} (≺→≼ {v} {q} (≺-≼-≺ {v} {y} {q} vy yq))) (l (N ⊔ k) (m≤m⊔n N k))) vy }

        back : L y e → X k y e
        back (from N l , _) = proj₂ (upto (ag (N ⊔ k) (m≤n⊔m N k)) {y} yq) (l (N ⊔ k) (m≤m⊔n N k))

    agrees : ∀ {q} → Bnd< B (X k) q → AgreeTo q (X k) L
    agrees bx = ⟨ agrees′ bx ⟩

    bounds : ∀ {q} → Bnd< B L q → Bnd< B (X k) q
    bounds {q} bl {v} xv vq = few-ind (λ w → w ≺ q → ∀ {e} → X k w e → size w ≤ B) step (entered-few (c k) p xv) vq xv
      where
        step : ∀ {w} → Few (X k) w → (∀ {v e} → X k v e → v ≺ w → v ≺ q → ∀ {e} → X k v e → size v ≤ B)
             → w ≺ q → ∀ {e} → X k w e → size w ≤ B
        step {w} Fw ih wq xw = bl (proj₁ (agrees′ bw {w} (≼-refl {w})) xw) wq
          where
            bw : Bnd< B (X k) w
            bw {u} x′ uw = ih x′ uw (≺-trans {u} {w} {q} uw wq) x′

    top : AgS B (X k) L
    top q (inj₁ bx) = agrees bx
    top q (inj₂ bl) = agrees (bounds bl)

------------------------------------------------------------------------
-- Defer

-- The guard comes before the body.
ticks : ∀ p j → (p ++ [ ix 0 ]) ≺ (p ++ [ ix (suc j) ])
ticks p j = Equivalence.from T-≡ (<ᵖ-part p [] [] refl)

-- DEFER IS CONTRACTIVE: its body sits one label down, so the body's
-- bound is one more.
contract : ∀ {A R k} {s s′ : Den A} → (∀ p → R p → R (p ++ [ ix 1 ])) → s ≈⟨ R ∣ k ⟩ s′ → deferᵀ s ≈⟨ R ∣ suc k ⟩ deferᵀ s′
contract {R = R} {k} {s} {s′} up ag p r = trunc-ag inner
  where
    B = size p + suc k

    same : size (p ++ [ ix 1 ]) + k ≡ B
    same rewrite size-++ p (ix 1) = +-assoc (size p) 1 k

    bod : AgS B (enter s (p ++ [ ix 1 ])) (enter s′ (p ++ [ ix 1 ]))
    bod = subst (λ b → AgS b (enter s (p ++ [ ix 1 ])) (enter s′ (p ++ [ ix 1 ]))) same (ag (p ++ [ ix 1 ]) (up p r))

    lift : ∀ {q} → AgreeTo q (enter s (p ++ [ ix 1 ])) (enter s′ (p ++ [ ix 1 ])) → AgreeTo q (DeferT s p) (DeferT s′ p)
    lift a = ⟨ (λ {y} yq → (λ { guard → guard ; (body x) → body (proj₁ (upto a {y} yq) x) }) , (λ { guard → guard ; (body x) → body (proj₂ (upto a {y} yq) x) })) ⟩

    inner : AgS B (DeferT s p) (DeferT s′ p)
    inner q (inj₁ b) = lift {q} (bod q (inj₁ λ {y} x yq → b {y} (body x) yq))
    inner q (inj₂ b) = lift {q} (bod q (inj₂ λ {y} x yq → b {y} (body x) yq))

-- THE FIRST UNFOLDING: the spin and the unfolded `defer` agree at their
-- first row, the guard, where the body has not begun; at bound 0 nothing
-- past it is promised.
unfold₀ : ∀ {A R} {s : Den A} → (∀ p → R p → ∀ {y e} → enter s (p ++ [ ix 1 ]) y e → (p ++ [ ix 0 ]) ≺ y) → ⊥ᵀ ≈⟨ R ∣ 0 ⟩ deferᵀ s
unfold₀ {s = s} after p r q side = ⟨ agree ⟩
  where
    g = p ++ [ ix 0 ]

    no-room : size g ≤ size p + 0 → ⊥
    no-room le = n≮n (size p) (subst₂ _≤_ (trans′ (size-++ p (ix 0)) (+-comm (size p) 1)) (+-identityʳ (size p)) le)
      where trans′ : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
            trans′ refl refl = refl

    spin-few : Few (Spin p) g
    spin-few = [] , λ { (spin zero) lt → ⊥-elim (≺-irrefl {g} lt) ; (spin (suc j)) lt → ⊥-elim (≺→≼ {g} {p ++ [ ix (suc j) ]} (ticks p j) lt) }

    defer-few : Few (DeferT s p) g
    defer-few = [] , λ { guard lt → ⊥-elim (≺-irrefl {g} lt) ; (body {y} x) lt → ⊥-elim (≺→≼ {g} {y} (after p r x) lt) }

    early′ : Bnd< (size p + 0) (Truncate (Spin p)) q ⊎ Bnd< (size p + 0) (Truncate (DeferT s p)) q → q ≼ g
    early′ (inj₁ b) = λ gq → no-room (b (spin 0 , spin-few) gq)
    early′ (inj₂ b) = λ gq → no-room (b (guard , defer-few) gq)

    early : q ≼ g
    early = early′ side

    agree : ∀ {y e} → y ≼ q → (Truncate (Spin p) y e → Truncate (DeferT s p) y e) × (Truncate (DeferT s p) y e → Truncate (Spin p) y e)
    agree {y} yq = to , back
      where
        to : ∀ {e} → Truncate (Spin p) y e → Truncate (DeferT s p) y e
        to (spin zero , _)    = guard , defer-few
        to (spin (suc j) , _) = ⊥-elim (early (≺-≼-≺ {g} {p ++ [ ix (suc j) ]} {q} (ticks p j) yq))

        back : ∀ {e} → Truncate (DeferT s p) y e → Truncate (Spin p) y e
        back (guard , _)  = spin 0 , spin-few
        back (body x , _) = ⊥-elim (early (≺-≼-≺ {g} {y} {q} (after p r x) yq))

------------------------------------------------------------------------
-- Causality

-- At and below `q`, the same rows at every subscription.
_~⟨_⟩_ : ∀ {A} → Den A → Pos → Den A → Set
d ~⟨ q ⟩ d′ = ∀ p → AgreeTo q (enter d p) (enter d′ p)

-- Agreeing at and below `q` agrees below what is at or before it.
ag-down : ∀ {A} {t t′ : EmissionSet A} {q y} → y ≼ q → AgreeTo q t t′ → AgreeTo y t t′
ag-down {q = q} {y} yq a = ⟨ (λ {v} vy → upto a {v} (≼-trans {v} {y} {q} vy yq)) ⟩

-- TRUNCATION KEEPS AGREEMENT at and below `q`: a row there has its
-- predecessors there too.
trunc-to : ∀ {A} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → AgreeTo q (Truncate t) (Truncate t′)
trunc-to {q = q} a = ⟨ (λ {y} yq →
    (λ { (x , F) → proj₁ (upto a {y} yq) x , few-agree (ag-down {q = q} {y} yq a) F })
  , (λ { (x , F) → proj₂ (upto a {y} yq) x , few-agree (AgreeTo-sym (ag-down {q = q} {y} yq a)) F })) ⟩

-- A cold agreeing at every subscription.
~-cold : ∀ {A q} {f f′ : Pos → EmissionSet A} → (∀ p → AgreeTo q (f p) (f′ p)) → cold f ~⟨ q ⟩ cold f′
~-cold a p = trunc-to (a p)

~-refl : ∀ {A q} (d : Den A) → d ~⟨ q ⟩ d
~-refl d p = ⟨ (λ yq → (λ x → x) , (λ x → x)) ⟩
