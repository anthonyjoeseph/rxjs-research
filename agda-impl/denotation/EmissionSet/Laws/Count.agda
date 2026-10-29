{-# OPTIONS --guardedness #-}

-- THE ORDER MODULUS: how far two observables agree, by how many positions
-- come before a cut.  Two sets agree to `n` at a cut `q` with at most `n`
-- positions before it: the same rows at and below `q`.  A position COVERS
-- every position it extends, and what `q` itself extends is free — so a row
-- an operator moves one label down, or under the row it answers, is still
-- counted once.  Every operator places each row it reads at or under a row
-- it shows, so what is few before `q` in its output is few in its inputs.
--
-- A row past an infinite run has no cut with finitely many before it, so
-- agreeing at every index is having the same truncated rows (`agree-all`).
-- A `defer`'s guard is one more position before its body, so a `defer` is
-- contractive (`contract`), and a chain each within the next agrees with
-- its limit (`limit`).
module denotation.EmissionSet.Laws.Count where

open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; _⊔_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; m≤m⊔n; m≤n⊔m; m≤n+m; m∸n+n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_⊎-dec_)
open import Relation.Nullary.Decidable.Core using (decidable-stable)

open import denotation.MonotonicList.Events using (Pos; ix; <ᵖ-split; <ᵖ-part; <ᵖ-between; _≟ˡ_)
open import denotation.EmissionSet using (Ev; EmissionSet; _≺_; _≼_; Truncate; Den; enter; from; Spin; spin; ⊥ᵀ; DeferT; guard; body; deferᵀ)
open import denotation.EmissionSet.Laws.Modulus
  using (≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-false; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; few-down; few-agree; few-ind; entered-few;
  AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; Same; LimD; ticks)
open import denotation.EmissionSet.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-trans; ⊑-≼; ⊑-cmp; conv)

------------------------------------------------------------------------
-- Counting

-- `k` is covered at `q` by `ks`: `q` or one of `ks` extends it.
Cov : Pos → List Pos → Pos → Set
Cov q ks k = k ⊑ q ⊎ Any (k ⊑_) ks

-- At most `n` positions cover the rows before `q`.
Cnt : ∀ {A} → ℕ → EmissionSet A → Pos → Set
Cnt n t q = Σ (List Pos) λ ks → length ks ≤ n × (∀ {k e} → t k e → k ≺ q → Cov q ks k)

-- What a cover extends, a cover of it extends.
cov-up : ∀ {q ks k k′} → k ⊑ k′ → Cov q ks k′ → Cov q ks k
cov-up kk (inj₁ k′q) = inj₁ (⊑-trans kk k′q)
cov-up kk (inj₂ a)   = inj₂ (Any.map (⊑-trans kk) a)

-- Covered at `q`, before an earlier cut: covered there.
cov-down : ∀ {q w ks k} → Cov q ks k → k ≺ w → w ≼ q → Cov w ks k
cov-down {q} {w} {k = k} (inj₁ kq) kw wq with <ᵖ-split w q (≼-false {w} {q} wq)
... | inj₁ lt   = inj₁ (conv (⊑-refl k) (≺→≼ {k} {w} kw) (Equivalence.from T-≡ lt) kq)
... | inj₂ refl = inj₁ kq
cov-down (inj₂ a) kw wq = inj₂ a

-- Leading is decidable, so is covering.
⊑? : ∀ x y → Dec (x ⊑ y)
⊑? []      y       = yes (y , refl)
⊑? (a ∷ x) []      = no λ { (_ , ()) }
⊑? (a ∷ x) (b ∷ y) with a ≟ˡ b | ⊑? x y
... | no ne    | _             = no λ { (_ , eq) → ne (sym (∷-injectiveˡ eq)) }
... | yes refl | no ne         = no λ { (zs , eq) → ne (zs , ∷-injectiveʳ eq) }
... | yes refl | yes (zs , eq) = yes (zs , cong (a ∷_) eq)

cov-stable : ∀ {q ks k} → ¬ ¬ Cov q ks k → Cov q ks k
cov-stable {q} {ks} {k} = decidable-stable (⊑? k q ⊎-dec any? (⊑? k) ks)

-- Before `q`, a row's child lies before `q`, or `q` under the row.
child : ∀ {v q} l → v ≺ q → v ⊑ q ⊎ (v ++ [ l ]) ≺ q
child {v} {q} l vq with ≼-or-≻ q (v ++ [ l ])
... | inj₂ lt = inj₂ lt
... | inj₁ ql with <ᵖ-split q (v ++ [ l ]) (≼-false {q} {v ++ [ l ]} ql)
...   | inj₁ lt = inj₁ (<ᵖ-between v q [ l ] (Equivalence.to T-≡ vq) lt)
...   | inj₂ eq = inj₁ ([ l ] , eq)

-- Few before `q`, few before an earlier cut.
cnt-down : ∀ {A n} {t : EmissionSet A} {q w} → Cnt n t q → w ≼ q → Cnt n t w
cnt-down {q = q} {w} (ks , le , h) wq = ks , le , λ {k} x kw → cov-down (h x (≺-≼-≺ {k} {w} {q} kw wq)) kw wq

cnt-mono : ∀ {A m n} {t : EmissionSet A} {q} → m ≤ n → Cnt m t q → Cnt n t q
cnt-mono mn (ks , le , h) = ks , ≤-trans le mn , h

-- READ THROUGH ITS IMAGES: each row of `u` before `q` under `q`, or under a
-- row of `t` before `q`: what covers `t` covers `u`.  Covering is
-- decidable, so an image need only be not refuted.
cnt-up : ∀ {A B n} {t : EmissionSet A} {u : EmissionSet B} {q} → Cnt n t q
       → (∀ {k e} → u k e → k ≺ q → ¬ ¬ (k ⊑ q ⊎ Σ Pos λ k′ → Σ (Ev A) (t k′) × k ⊑ k′ × k′ ≺ q))
       → Cnt n u q
cnt-up {A = A} {t = t} {q = q} (ks , le , h) im = ks , le , λ x kq → cov-stable λ ¬c → im x kq λ i → ¬c (go i)
  where
    go : ∀ {k} → k ⊑ q ⊎ Σ Pos (λ k′ → Σ (Ev A) (t k′) × k ⊑ k′ × k′ ≺ q) → Cov q ks k
    go (inj₁ kq)                     = inj₁ kq
    go (inj₂ (k′ , (_ , x) , kk , lt)) = cov-up kk (h x lt)

-- The cut's own rows, agreeing, are as few.
cnt-agree : ∀ {A n} {t t′ : EmissionSet A} {q} → AgreeTo q t t′ → Cnt n t q → Cnt n t′ q
cnt-agree {q = q} a (ks , le , h) = ks , le , λ {k} x kq → h (proj₂ (upto a {k} (≺→≼ {k} {q} kq)) x) kq

-- A list of positions covering every row before `q`.
cnt-few : ∀ {A} {t : EmissionSet A} {q} (ks : List Pos) → (∀ {k e} → t k e → k ≺ q → Any (k ≡_) ks) → Cnt (length ks) t q
cnt-few ks h = ks , ≤-refl , λ x kq → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h x kq))

------------------------------------------------------------------------
-- Agreement

-- WITHIN `n`: few before `q` on either side, the two agree at and below `q`.
AgC : ∀ {A} → ℕ → EmissionSet A → EmissionSet A → Set
AgC n t t′ = ∀ q → Cnt n t q ⊎ Cnt n t′ q → AgreeTo q t t′

AgC-refl : ∀ {A n} {t : EmissionSet A} → AgC n t t
AgC-refl q _ = ⟨ (λ yq → (λ x → x) , (λ x → x)) ⟩

AgC-sym : ∀ {A n} {t t′ : EmissionSet A} → AgC n t t′ → AgC n t′ t
AgC-sym ag q (inj₁ b) = AgreeTo-sym (ag q (inj₂ b))
AgC-sym ag q (inj₂ b) = AgreeTo-sym (ag q (inj₁ b))

AgC-mono : ∀ {A m n} {t t′ : EmissionSet A} → m ≤ n → AgC n t t′ → AgC m t t′
AgC-mono le ag q (inj₁ b) = ag q (inj₁ (cnt-mono le b))
AgC-mono le ag q (inj₂ b) = ag q (inj₂ (cnt-mono le b))

AgC-trans : ∀ {A n} {t u v : EmissionSet A} → AgC n t u → AgC n u v → AgC n t v
AgC-trans tu uv q (inj₁ b) = AgreeTo-trans a₁ (uv q (inj₁ (cnt-agree a₁ b)))
  where a₁ = tu q (inj₁ b)
AgC-trans tu uv q (inj₂ b) = AgreeTo-trans (tu q (inj₂ (cnt-agree (AgreeTo-sym a₂) b))) a₂
  where a₂ = uv q (inj₂ b)

-- TRUNCATION KEEPS AGREEMENT: a reached row up to a few-bounded cut has
-- only reached rows before it, so they are few, and the wholes agree there.
private
  trunc-at : ∀ {A n} {t t′ : EmissionSet A} {q} → AgC n t t′ → Cnt n (Truncate t) q
           → ∀ {y e} → y ≼ q → (Truncate t y e → Truncate t′ y e) × (Truncate t′ y e → Truncate t y e)
  trunc-at {n = n} {t} {t′} {q} ag (ks , le , h) {y} {e} yq = there′ , back
    where
      there′ : Truncate t y e → Truncate t′ y e
      there′ (x , F) = proj₁ (upto a {y} {e} (≼-refl {y})) x , few-agree a F
        where
          ct : Cnt n t y
          ct = ks , le , λ {w} tw wy → cov-down (h (tw , few-down F wy) (≺-≼-≺ {w} {y} {q} wy yq)) wy yq
          a = ag y (inj₁ ct)

      step : ∀ {w} → _ → (∀ {v e} → t′ v e → v ≺ w → v ≼ q → Cnt n t′ v) → w ≼ q → Cnt n t′ w
      step {w} Fw ih wq = ks , le , λ {v} t′v vw →
        let vq = ≺-≼-≺ {v} {w} {q} vw wq
            av = ag v (inj₂ (ih t′v vw (≺→≼ {v} {q} vq)))
        in cov-down (h (proj₂ (upto av {v} (≼-refl {v})) t′v , few-agree (AgreeTo-sym av) (few-down Fw vw)) vq) vw wq

      back : Truncate t′ y e → Truncate t y e
      back (x′ , F′) = proj₂ (upto a {y} {e} (≼-refl {y})) x′ , few-agree (AgreeTo-sym a) F′
        where a = ag y (inj₂ (few-ind (λ w → w ≼ q → Cnt n t′ w) step F′ yq))

  trunc-ag₁ : ∀ {A n} {t t′ : EmissionSet A} {q} → AgC n t t′ → Cnt n (Truncate t) q → AgreeTo q (Truncate t) (Truncate t′)
  trunc-ag₁ ag bd = ⟨ trunc-at ag bd ⟩

trunc-ag : ∀ {A n} {t t′ : EmissionSet A} → AgC n t t′ → AgC n (Truncate t) (Truncate t′)
trunc-ag ag q (inj₁ b) = trunc-ag₁ {q = q} ag b
trunc-ag ag q (inj₂ b) = AgreeTo-sym (trunc-ag₁ {q = q} (AgC-sym ag) b)

------------------------------------------------------------------------
-- Observables within a bound

-- Within `n` at every subscription `R` admits.
_≈ᶜ⟨_∣_⟩_ : ∀ {A} → Den A → (Pos → Set) → ℕ → Den A → Set
d ≈ᶜ⟨ R ∣ n ⟩ d′ = ∀ p → R p → AgC n (enter d p) (enter d′ p)

≈ᶜ-refl : ∀ {A R n} (d : Den A) → d ≈ᶜ⟨ R ∣ n ⟩ d
≈ᶜ-refl d p r = AgC-refl

≈ᶜ-mono : ∀ {A R m n} {d d′ : Den A} → m ≤ n → d ≈ᶜ⟨ R ∣ n ⟩ d′ → d ≈ᶜ⟨ R ∣ m ⟩ d′
≈ᶜ-mono le ag p r = AgC-mono le (ag p r)

≈ᶜ-sym : ∀ {A R n} {d d′ : Den A} → d ≈ᶜ⟨ R ∣ n ⟩ d′ → d′ ≈ᶜ⟨ R ∣ n ⟩ d
≈ᶜ-sym ag p r = AgC-sym (ag p r)

≈ᶜ-trans : ∀ {A R n} {d d′ d″ : Den A} → d ≈ᶜ⟨ R ∣ n ⟩ d′ → d′ ≈ᶜ⟨ R ∣ n ⟩ d″ → d ≈ᶜ⟨ R ∣ n ⟩ d″
≈ᶜ-trans a b p r = AgC-trans (a p r) (b p r)

-- AGREEING AT EVERY INDEX IS THE SAME ROWS: a reached row has finitely
-- many before it, and a list of them is a cover.
agree-all : ∀ {A R} {d d′ : Den A} → (∀ n → d ≈ᶜ⟨ R ∣ n ⟩ d′) → Same R d d′
agree-all {d = d} {d′} all p r {q} = to , back
  where
    to : ∀ {e} → enter d p q e → enter d′ p q e
    to x with entered-few d p x
    ... | ks , h = proj₁ (upto (all (length ks) p r q (inj₁ (cnt-few ks h))) {q} (≼-refl {q})) x

    back : ∀ {e} → enter d′ p q e → enter d p q e
    back x with entered-few d′ p x
    ... | ks , h = proj₂ (upto (all (length ks) p r q (inj₂ (cnt-few ks h))) {q} (≼-refl {q})) x

------------------------------------------------------------------------
-- The limit of a chain

-- THE LIMIT: each member of a chain within the next is within its limit.
-- Few before `q` in member `k`, every later member agrees with it, so the
-- limit does; few in the limit, member `k`'s rows before `q` are the
-- limit's, one at a time from the first, so as few.
limit : ∀ {A R} {c : ℕ → Den A} → (∀ n → c n ≈ᶜ⟨ R ∣ n ⟩ c (suc n)) → ∀ k → c k ≈ᶜ⟨ R ∣ k ⟩ LimD c
limit {c = c} ch k p r = top
  where
    X : ℕ → EmissionSet _
    X n = enter (c n) p

    ahead : ∀ j → AgC k (X k) (X (j + k))
    ahead zero    = AgC-refl
    ahead (suc j) = AgC-trans (ahead j) (AgC-mono (m≤n+m k j) (ch (j + k) p r))

    at : ∀ n → k ≤ n → AgC k (X k) (X n)
    at n le = subst (λ m → AgC k (X k) (X m)) (m∸n+n≡m le) (ahead (n ∸ k))

    L = enter (LimD c) p

    agrees′ : ∀ {q} → Cnt k (X k) q → ∀ {y e} → y ≼ q → (X k y e → L y e) × (L y e → X k y e)
    agrees′ {q} bx {y} {e} yq = to , back
      where
        ag : ∀ n → k ≤ n → AgreeTo q (X k) (X n)
        ag n le = at n le q (inj₁ bx)

        to : X k y e → L y e
        to x = from k (λ n le → proj₁ (upto (ag n le) {y} yq) x) , few
          where
            few : _
            few with entered-few (c k) p x
            ... | ks , h = ks , λ { {v} (from N l) vy →
              h (proj₂ (upto (ag (N ⊔ k) (m≤n⊔m N k)) {v} (≺→≼ {v} {q} (≺-≼-≺ {v} {y} {q} vy yq))) (l (N ⊔ k) (m≤m⊔n N k))) vy }

        back : L y e → X k y e
        back (from N l , _) = proj₂ (upto (ag (N ⊔ k) (m≤n⊔m N k)) {y} yq) (l (N ⊔ k) (m≤m⊔n N k))

    bounds : ∀ {q} → Cnt k L q → Cnt k (X k) q
    bounds {q} (ks , le , h) = ks , le , λ {v} xv vq → h (inL (entered-few (c k) p xv) vq xv) vq
      where
        inL : ∀ {w} → _ → w ≺ q → ∀ {e} → X k w e → L w e
        inL = few-ind (λ w → w ≺ q → ∀ {e} → X k w e → L w e) step
          where
            step : ∀ {w} → _ → (∀ {v e} → X k v e → v ≺ w → v ≺ q → ∀ {e} → X k v e → L v e)
                 → w ≺ q → ∀ {e} → X k w e → L w e
            step {w} Fw ih wq xw = proj₁ (agrees′ cw {w} (≼-refl {w})) xw
              where
                cw : Cnt k (X k) w
                cw = ks , le , λ {u} x′ uw →
                  let uq = ≺-trans {u} {w} {q} uw wq
                  in cov-down (h (ih x′ uw uq x′) uq) uw (≺→≼ {w} {q} wq)

    top : AgC k (X k) L
    top q (inj₁ bx) = ⟨ agrees′ bx ⟩
    top q (inj₂ bl) = ⟨ agrees′ (bounds bl) ⟩

------------------------------------------------------------------------
-- Defer

-- Every row read at a `defer`'s body subscription lies at or past it.
Aft : ∀ {A} → (Pos → Set) → Den A → Set
Aft R s = ∀ p → R p → ∀ {y e} → enter s (p ++ [ ix 1 ]) y e → (p ++ [ ix 1 ]) ≼ y

private
  -- One of `ks`, and the rest.
  pick : ∀ {P : Pos → Set} {ks} → Any P ks
       → Σ Pos λ x → P x × Σ (List Pos) λ ks′ → suc (length ks′) ≡ length ks × (∀ {b} → Any (b ⊑_) ks → b ⊑ x ⊎ Any (b ⊑_) ks′)
  pick {ks = x ∷ ks} (here px) = x , px , ks , refl , λ { (here b) → inj₁ b ; (there a) → inj₂ a }
  pick {ks = y ∷ ks} (there a) with pick a
  ... | x , px , ks′ , eq , sp = x , px , y ∷ ks′ , cong suc eq , λ
    { (here b) → inj₂ (here b)
    ; (there a′) → map₂ there (sp a′) }

  -- Under the guard: before the body.
  under-guard : ∀ p {b} → (p ++ [ ix 0 ]) ⊑ b → b ≺ (p ++ [ ix 1 ])
  under-guard p (zs , refl) = subst (_≺ (p ++ [ ix 1 ])) (sym (++-assoc p [ ix 0 ] zs)) (Equivalence.from T-≡ (<ᵖ-part p zs [] refl))

  ix-past : ∀ p j → (p ++ [ ix 1 ]) ≼ (p ++ [ ix (suc j) ])
  ix-past p zero    = ≼-refl {p ++ [ ix 1 ]}
  ix-past p (suc j) = ≺→≼ {p ++ [ ix 1 ]} {p ++ [ ix (suc (suc j)) ]} (Equivalence.from T-≡ (<ᵖ-part p [] [] refl))

-- A `defer`'s body, with its guard before it: one position fewer.
module Guarded {A : Set} (s : Den A) (p : Pos) (aft : ∀ {y e} → enter s (p ++ [ ix 1 ]) y e → (p ++ [ ix 1 ]) ≼ y) where
  g b₀ : Pos
  g  = p ++ [ ix 0 ]
  b₀ = p ++ [ ix 1 ]

  -- Before the body's subscription: no body row there.
  none-before : ∀ {y e} → enter s b₀ y e → y ≺ b₀ → ⊥
  none-before x yb = aft x yb

  shrink : ∀ {n q} → Cnt (suc n) (DeferT s p) q → Cnt n (enter s b₀) q
  shrink {n} {q} (ks , le , h) with ≼-or-≻ q g
  ... | inj₁ qg = [] , z≤n , λ {y} x yq → ⊥-elim (none-before x (≺-trans {y} {g} {b₀} (≺-≼-≺ {y} {q} {g} yq qg) (ticks p 0)))
  ... | inj₂ gq with h guard gq
  ...   | inj₁ gq′ = [] , z≤n , λ {y} x yq → ⊥-elim (none-before x (≺-trans {y} {q} {b₀} yq (under-guard p gq′)))
  ...   | inj₂ a with pick a
  ...     | x , gx , ks′ , eq , sp = ks′ , ≤-pred (subst (_≤ suc n) (sym eq) le) , cover
    where
      cover : ∀ {y e} → enter s b₀ y e → y ≺ q → Cov q ks′ y
      cover {y} x′ yq with h (body x′) yq
      ... | inj₁ yq′ = inj₁ yq′
      ... | inj₂ a′ with sp a′
      ...   | inj₂ a″ = inj₂ a″
      ...   | inj₁ yx with ⊑-cmp y g yx gx
      ...     | inj₁ yg = ⊥-elim (none-before x′ (≼-≺-≺ {y} {g} {b₀} (⊑-≼ yg) (ticks p 0)))
      ...     | inj₂ gy = ⊥-elim (none-before x′ (under-guard p gy))

-- DEFER IS CONTRACTIVE: its guard is one position before its body.
contract : ∀ {A R k} {s s′ : Den A} → (∀ p → R p → R (p ++ [ ix 1 ])) → Aft R s → Aft R s′
         → s ≈ᶜ⟨ R ∣ k ⟩ s′ → deferᵀ s ≈ᶜ⟨ R ∣ suc k ⟩ deferᵀ s′
contract {R = R} {k} {s} {s′} up as as′ ag p r = trunc-ag inner
  where
    b₀ = p ++ [ ix 1 ]
    bod = ag b₀ (up p r)

    lift : ∀ {q} → AgreeTo q (enter s b₀) (enter s′ b₀) → AgreeTo q (DeferT s p) (DeferT s′ p)
    lift a = ⟨ (λ {y} yq → (λ { guard → guard ; (body x) → body (proj₁ (upto a {y} yq) x) }) , (λ { guard → guard ; (body x) → body (proj₂ (upto a {y} yq) x) })) ⟩

    inner : AgC (suc k) (DeferT s p) (DeferT s′ p)
    inner q (inj₁ b) = lift {q} (bod q (inj₁ (Guarded.shrink s p (as p r) b)))
    inner q (inj₂ b) = lift {q} (bod q (inj₂ (Guarded.shrink s′ p (as′ p r) b)))

-- THE FIRST UNFOLDING: the spin and the unfolded `defer` agree at their
-- first row, the guard, where the body has not begun; with no position
-- before the cut, the cut is at or under the guard.
unfold₀ : ∀ {A R} {s : Den A} → Aft R s → ⊥ᵀ ≈ᶜ⟨ R ∣ 0 ⟩ deferᵀ s
unfold₀ {s = s} as p r q side = ⟨ agree ⟩
  where
    open Guarded s p (as p r) using (g; b₀; none-before)

    spin-few : _
    spin-few = [] , λ { (spin zero) lt → ⊥-elim (≺-irrefl {g} lt) ; (spin (suc j)) lt → ⊥-elim (≺→≼ {g} {p ++ [ ix (suc j) ]} (ticks p j) lt) }

    defer-few : _
    defer-few = [] , λ { guard lt → ⊥-elim (≺-irrefl {g} lt) ; (body {y} x) lt → ⊥-elim (≺→≼ {g} {y} (≺-≼-≺ {g} {b₀} {y} (ticks p 0) (as p r x)) lt) }

    -- The cut is before the body.
    early : q ≺ b₀
    early with ≼-or-≻ q g
    ... | inj₁ qg = ≼-≺-≺ {q} {g} {b₀} qg (ticks p 0)
    ... | inj₂ gq = under-guard p (lone side)
      where
        lone : _ → g ⊑ q
        lone (inj₁ ([] , _ , h)) with h (spin 0 , spin-few) gq
        ... | inj₁ gq′ = gq′
        ... | inj₂ ()
        lone (inj₁ (_ ∷ _ , () , _))
        lone (inj₂ ([] , _ , h)) with h (guard , defer-few) gq
        ... | inj₁ gq′ = gq′
        ... | inj₂ ()
        lone (inj₂ (_ ∷ _ , () , _))

    agree : ∀ {y e} → y ≼ q → (Truncate (Spin p) y e → Truncate (DeferT s p) y e) × (Truncate (DeferT s p) y e → Truncate (Spin p) y e)
    agree {y} yq = to , back
      where
        to : ∀ {e} → Truncate (Spin p) y e → Truncate (DeferT s p) y e
        to (spin zero , _)    = guard , defer-few
        to (spin (suc j) , _) = ⊥-elim (ix-past p j (≼-≺-≺ {p ++ [ ix (suc j) ]} {q} {b₀} yq early))

        back : ∀ {e} → Truncate (DeferT s p) y e → Truncate (Spin p) y e
        back (guard , _)  = spin 0 , spin-few
        back (body x , _) = ⊥-elim (none-before x (≼-≺-≺ {y} {q} {b₀} yq early))
