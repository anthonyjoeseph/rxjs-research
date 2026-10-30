{-# OPTIONS --guardedness #-}

-- THE ORDER MODULUS: how far two observables agree, by how many positions
-- a row waits on.  Two sets agree to `n` on a row whose wait (`Dep`) at
-- most `n` positions cover: either has it exactly when the other does.  A
-- row that waits on everything before it agrees with all of its cut; a
-- pin, only with its own past.  A position COVERS
-- every position it extends, and what `q` itself extends is free — so a row
-- an operator moves one label down, or under the row it answers, is still
-- counted once.  Every operator places each row it reads at or under a row
-- it shows, so what is few before `q` in its output is few in its inputs.
--
-- COUNTED PER ROW, never per cut: a pin that runs past a body that never
-- returns has unboundedly many rows before it, and a downstream cut of that
-- body brings it within one; a count of the cut alone would let two sources
-- agree within any bound and disagree on that pin once a `take` sits on top.
--
-- A row waiting on an infinite run has no finite cover, so agreeing at
-- every index is having the same truncated rows (`agree-all`).
-- A `defer`'s guard is one more position before its body, so a `defer` is
-- contractive (`contract`), and a chain each within the next agrees with
-- its limit (`limit`).
module denotation.Laws.Count where

open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; [_]; length; filter)
open import Data.List.Properties using (++-assoc; ∷-injectiveˡ; ∷-injectiveʳ; filter-notAll)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; _⊔_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; m≤m⊔n; m≤n⊔m; m≤n+m; m∸n+n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂) renaming (map to ⊎-map)
open import Data.Unit using (tt)
open import Function using (Equivalence; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_⊎-dec_)
open import Relation.Nullary.Decidable.Core using (decidable-stable; T?)

open import denotation.Events using (Pos; ix; inside; _<ᵖ_; <ᵖ-split; <ᵖ-part; <ᵖ-between; _≟ˡ_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; _≺_; _≼_; Dep; Reach; Truncate; Den; enter; Lim; from; Spin; spin; DeferT; guard; body; module Op)
open import denotation.Laws.Modulus
  using (≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-false; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; reach-via; entered-reach;
  AgreeTo; ⟨_⟩; Same; LimD; ticks)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-trans; ⊑-≼; ⊑-cmp; conv; ⊑-inside; inside-⊑)

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

-- Covered at a cut, covered at any cut it leads.
cov-lift : ∀ {w q ks k} → Cov w ks k → w ⊑ q → Cov q ks k
cov-lift (inj₁ kw) wq = inj₁ (⊑-trans kw wq)
cov-lift (inj₂ a)  _  = inj₂ a

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

-- Where a read row shows: under the cut, or under a row before it.
Img : ∀ {B} → EmissionSet B → Pos → Pos → Set
Img {B} t Q k = k ⊑ Q ⊎ Σ Pos λ k′ → Σ (Ev B) (t k′) × k ⊑ k′ × k′ ≺ Q

em : ∀ {P G : Set} → (P → ¬ ¬ G) → (¬ P → ¬ ¬ G) → ¬ ¬ G
em p np ¬g = np (λ x → p x ¬g) ¬g

seen : ∀ {B} {t : EmissionSet B} {Q k e} → t k e → k ≺ Q → ¬ ¬ Img t Q k
seen {k = k} x kQ ¬i = ¬i (inj₂ (k , (_ , x) , ⊑-refl k , kQ))

seen-under : ∀ {B} {t : EmissionSet B} {Q k l e} → t (k ++ [ l ]) e → k ≺ Q → ¬ ¬ Img t Q k
seen-under {k = k} {l} x kQ ¬i with child l kQ
... | inj₁ kQ′ = ¬i (inj₁ kQ′)
... | inj₂ lt  = ¬i (inj₂ (k ++ [ l ] , (_ , x) , ([ l ] , refl) , lt))

-- Few before `q`, few before an earlier cut.
cnt-down : ∀ {A n} {t : EmissionSet A} {q w} → Cnt n t q → w ≼ q → Cnt n t w
cnt-down {q = q} {w} (ks , le , h) wq = ks , le , λ {k} x kw → cov-down (h x (≺-≼-≺ {k} {w} {q} kw wq)) kw wq

cnt-mono : ∀ {A m n} {t : EmissionSet A} {q} → m ≤ n → Cnt m t q → Cnt n t q
cnt-mono mn (ks , le , h) = ks , ≤-trans le mn , h

-- READ THROUGH ITS IMAGES: each row of `u` before `q` under `q`, or under a
-- row of `t` before `q`: what covers `t` covers `u`.  Covering is
-- decidable, so an image need only be not refuted.
cnt-up : ∀ {A B n} {t : EmissionSet A} {u : EmissionSet B} {q} → Cnt n t q
       → (∀ {k e} → u k e → k ≺ q → ¬ ¬ Img t q k) → Cnt n u q
cnt-up {A = A} {t = t} {q = q} (ks , le , h) im = ks , le , λ x kq → cov-stable λ ¬c → im x kq λ i → ¬c (go i)
  where
    go : ∀ {k} → Img t q k → Cov q ks k
    go (inj₁ kq)                     = inj₁ kq
    go (inj₂ (k′ , (_ , x) , kk , lt)) = cov-up kk (h x lt)

-- What a row at `q` waits on, covered by at most `n` positions.
DCnt : ∀ {A} → ℕ → EmissionSet A → Pos → Ev A → Set
DCnt n t q e = Σ (List Pos) λ ks → length ks ≤ n × (∀ {k e′} → t k e′ → k ≺ q → Dep q e k e′ → Cov q ks k)

-- Few before the cut, few that a row there waits on.
cnt-dcnt : ∀ {A n} {t : EmissionSet A} {q e} → Cnt n t q → DCnt n t q e
cnt-dcnt (ks , le , h) = ks , le , λ x kq _ → h x kq

-- Few before `q`, few that a row at or before it waits on.
cnt-at : ∀ {A n} {t : EmissionSet A} {q y e} → Cnt n t q → y ≼ q → DCnt n t y e
cnt-at c yq = cnt-dcnt (cnt-down c yq)

-- A row that waits on everything before it.
dcnt-cnt : ∀ {A n} {t : EmissionSet A} {q e} → (∀ {k e′} → Dep q e k e′) → DCnt n t q e → Cnt n t q
dcnt-cnt all (ks , le , h) = ks , le , λ x kq → h x kq all

-- A pin waits on all that came before its connect.
dcnt-pin : ∀ {A n} {t : EmissionSet A} {q r} → T (inside r q) → DCnt n t q (pin r) → Cnt n t r
dcnt-pin {q = q} {r} i (ks , le , h) = ks , le , λ {k} x kr → cov-down (h x (≺-≼-≺ {k} {r} {q} kr rq) (λ _ → inj₁ kr)) kr rq
  where rq = ⊑-≼ (inside-⊑ r q i)

-- WHAT A ROW WAITS ON WAITS ON WHAT IT WAITS ON: past a pin's connect
-- and before the pin lies only its own burst.
dep-trans : ∀ {A} {q w k} {e e₁ e₂ : Ev A} → k ≺ w → w ≺ q → Dep q e w e₁ → Dep w e₁ k e₂ → Dep q e k e₂
dep-trans {e = out _} _ _ _ _ = tt
dep-trans {e = skip}  _ _ _ _ = tt
dep-trans {e = end}   _ _ _ _ = tt
dep-trans {q = q} {w} {k} {e = pin r} kw wq d₁ d₂ i with d₁ i
... | inj₁ wr = inj₁ (≺-trans {k} {w} {r} kw wr)
... | inj₂ refl with ≼-or-≻ r w
...   | inj₂ wr = inj₁ (≺-trans {k} {w} {r} kw wr)
...   | inj₁ rw = d₂ (⊑-inside (conv (⊑-refl r) rw wq (inside-⊑ r q i)))

-- What a row waits on, a row it waits on waits on no more of.
reach-down : ∀ {A} {t : EmissionSet A} {q w e e₁} → Reach t q e → w ≺ q → Dep q e w e₁ → Reach t w e₁
reach-down {q = q} {w} (ks , h) wq d = ks , λ {k} x kw d′ → h x (≺-trans {k} {w} {q} kw wq) (dep-trans {k = k} kw wq d d′)

dcnt-down : ∀ {A n} {t : EmissionSet A} {q w e e₁} → DCnt n t q e → w ≺ q → Dep q e w e₁ → DCnt n t w e₁
dcnt-down {q = q} {w} (ks , le , h) wq d = ks , le , λ {k} x kw d′ →
  cov-down (h x (≺-trans {k} {w} {q} kw wq) (dep-trans {k = k} kw wq d d′)) kw (≺→≼ {w} {q} wq)

dcnt-mono : ∀ {A m n} {t : EmissionSet A} {q e} → m ≤ n → DCnt m t q e → DCnt n t q e
dcnt-mono mn (ks , le , h) = ks , ≤-trans le mn , h

-- INDUCTION ON WHAT A ROW WAITS ON: a property that holds of a row once it
-- holds of every row it waits on holds of every reached row.
reach-ind : ∀ {A} {t : EmissionSet A} (P : Pos → Ev A → Set)
          → (∀ {w e} → t w e → (∀ {v e′} → t v e′ → v ≺ w → Dep w e v e′ → P v e′) → P w e)
          → ∀ {w e} → t w e → Reach t w e → P w e
reach-ind {t = t} P step x R = go (length (proj₁ R)) x R ≤-refl
  where
    go : ∀ n {w e} → t w e → (R : Reach t w e) → length (proj₁ R) ≤ n → P w e
    go zero    x ([] , h) le = step x λ y vw d → ⊥-elim (none (h y vw d))
      where none : ∀ {v : Pos} → v ∈ [] → ⊥
            none ()
    go (suc n) {w} x (ks , h) le = step x λ {v} y vw d →
      go n y (filter (λ k → T? (k <ᵖ v)) ks , λ {k} z kv d′ → ∈-filter⁺ (λ k → T? (k <ᵖ v)) (h z (≺-trans {k} {v} {w} kv vw) (dep-trans {k = k} kv vw d d′)) kv)
        (≤-pred (≤-trans (filter-notAll (λ k → T? (k <ᵖ v)) ks (Any.map (λ { refl → ≺-irrefl {v} }) (h y vw d))) le))

-- READ BACK ONE ROW AT A TIME: a reached row of `t` that `u` has once the
-- rows it waits on are covered is a row of `u`, so what covers `u` covers `t`.
dcnt-pull : ∀ {A n} {t u : EmissionSet A} {q e}
          → (∀ {w e′} → t w e′ → Reach t w e′)
          → (∀ {w e′} → t w e′ → DCnt n t w e′ → u w e′)
          → DCnt n u q e → DCnt n t q e
dcnt-pull {A = A} {n} {t} {u} {q} {e} re ag (ks , le , h) = ks , le , λ x kq d → h (pull x kq d) kq d
  where
    P : Pos → Ev A → Set
    P w e₁ = w ≺ q → (∀ {j e₂} → j ≺ w → Dep w e₁ j e₂ → Dep q e j e₂) → u w e₁

    step : ∀ {w e₁} → t w e₁ → (∀ {v e′} → t v e′ → v ≺ w → Dep w e₁ v e′ → P v e′) → P w e₁
    step {w} x ih wq up = ag x (ks , le , λ {v} y vw d →
      let vq = ≺-trans {v} {w} {q} vw wq
      in cov-down (h (ih y vw d vq (λ {j} jv d′ → up (≺-trans {j} {v} {w} jv vw) (dep-trans {k = j} jv vw d d′))) vq (up vw d)) vw (≺→≼ {w} {q} wq))

    pull : ∀ {k e′} → t k e′ → k ≺ q → Dep q e k e′ → u k e′
    pull {k} x kq d = reach-ind P step x (re x) kq (λ {j} jk d′ → dep-trans {k = j} jk kq d d′)

------------------------------------------------------------------------
-- Agreement

-- WITHIN `n`: a row whose wait at most `n` positions cover on either side
-- is a row of both or of neither.
AgC : ∀ {A} → ℕ → EmissionSet A → EmissionSet A → Set
AgC n t t′ = ∀ q e → DCnt n t q e ⊎ DCnt n t′ q e → (t q e → t′ q e) × (t′ q e → t q e)

AgC-refl : ∀ {A n} {t : EmissionSet A} → AgC n t t
AgC-refl q e _ = (λ x → x) , (λ x → x)

AgC-sym : ∀ {A n} {t t′ : EmissionSet A} → AgC n t t′ → AgC n t′ t
AgC-sym ag q e (inj₁ b) = proj₂ (ag q e (inj₂ b)) , proj₁ (ag q e (inj₂ b))
AgC-sym ag q e (inj₂ b) = proj₂ (ag q e (inj₁ b)) , proj₁ (ag q e (inj₁ b))

AgC-mono : ∀ {A m n} {t t′ : EmissionSet A} → m ≤ n → AgC n t t′ → AgC m t t′
AgC-mono le ag q e (inj₁ b) = ag q e (inj₁ (dcnt-mono le b))
AgC-mono le ag q e (inj₂ b) = ag q e (inj₂ (dcnt-mono le b))

-- What a covered row waits on, the other side has too.
dcnt-back : ∀ {A n} {t t′ : EmissionSet A} {q e k e′} → AgC n t t′ → DCnt n t q e → t′ k e′ → k ≺ q → Dep q e k e′ → t k e′
dcnt-back {k = k} {e′} ag c x kq d = proj₂ (ag k e′ (inj₁ (dcnt-down c kq d))) x

dcnt-agree : ∀ {A n} {t t′ : EmissionSet A} {q e} → AgC n t t′ → DCnt n t q e → DCnt n t′ q e
dcnt-agree ag c = proj₁ c , proj₁ (proj₂ c) , λ x kq d → proj₂ (proj₂ c) (dcnt-back ag c x kq d) kq d

AgC-trans : ∀ {A n} {t u v : EmissionSet A} → AgC n t u → AgC n u v → AgC n t v
AgC-trans tu uv q e (inj₁ b) = proj₁ b₂ ∘ proj₁ b₁ , proj₂ b₁ ∘ proj₂ b₂
  where b₁ = tu q e (inj₁ b)
        b₂ = uv q e (inj₁ (dcnt-agree tu b))
AgC-trans tu uv q e (inj₂ b) = proj₁ b₂ ∘ proj₁ b₁ , proj₂ b₁ ∘ proj₂ b₂
  where b₂ = uv q e (inj₂ b)
        b₁ = tu q e (inj₂ (dcnt-agree (AgC-sym uv) b))

-- Within `n`, agreeing at and below a few-bounded cut.
ag-cnt : ∀ {A n} {t t′ : EmissionSet A} → AgC n t t′ → ∀ q → Cnt n t q ⊎ Cnt n t′ q → AgreeTo q t t′
ag-cnt ag q (inj₁ c) = ⟨ (λ {y} {e} yq → ag y e (inj₁ (cnt-at c yq))) ⟩
ag-cnt ag q (inj₂ c) = ⟨ (λ {y} {e} yq → ag y e (inj₂ (cnt-at c yq))) ⟩

-- Within `n` from agreeing at every few-bounded cut, and on every pin
-- whose past is few.
agc : ∀ {A n} {t t′ : EmissionSet A}
    → (∀ q → Cnt n t q ⊎ Cnt n t′ q → AgreeTo q t t′)
    → (∀ q r → T (inside r q) → DCnt n t q (pin r) ⊎ DCnt n t′ q (pin r) → (t q (pin r) → t′ q (pin r)) × (t′ q (pin r) → t q (pin r)))
    → AgC n t t′
agc lin pn q (out a) c = AgreeTo.upto (lin q (⊎-map (dcnt-cnt {e = out a} tt) (dcnt-cnt {e = out a} tt) c)) (≼-refl {q})
agc lin pn q skip    c = AgreeTo.upto (lin q (⊎-map (dcnt-cnt {e = skip} tt) (dcnt-cnt {e = skip} tt) c)) (≼-refl {q})
agc lin pn q end     c = AgreeTo.upto (lin q (⊎-map (dcnt-cnt {e = end} tt) (dcnt-cnt {e = end} tt) c)) (≼-refl {q})
agc lin pn q (pin r) c with T? (inside r q)
... | yes i = pn q r i c
... | no ¬i = AgreeTo.upto (lin q (⊎-map (dcnt-cnt λ i → ⊥-elim (¬i i)) (dcnt-cnt λ i → ⊥-elim (¬i i)) c)) (≼-refl {q})

-- TRUNCATION KEEPS AGREEMENT: what a reached row waits on is reached, so
-- covered; and on the other side, one row at a time.
private
  trunc-one : ∀ {A n} {t t′ : EmissionSet A} {q e} → AgC n t t′ → DCnt n (Truncate t) q e → Truncate t q e → Truncate t′ q e
  trunc-one {n = n} {t} {q = q} {e} ag (ks , le , h) (x , R) = proj₁ (ag q e (inj₁ c)) x , reach-via (λ y kq d → _ , dcnt-back ag c y kq d , d) R
    where c : DCnt n t q e
          c = ks , le , λ y kq d → h (y , reach-down R kq d) kq d

trunc-ag : ∀ {A n} {t t′ : EmissionSet A} → AgC n t t′ → AgC n (Truncate t) (Truncate t′)
trunc-ag {t′ = t′} ag q e (inj₁ c) = trunc-one ag c , λ x′ → trunc-one (AgC-sym ag) (dcnt-pull re (λ y d → trunc-one (AgC-sym ag) d y) c) x′
  where re : ∀ {w e′} → Truncate t′ w e′ → Reach (Truncate t′) w e′
        re y = reach-via (λ z _ d → _ , proj₁ z , d) (proj₂ y)
trunc-ag ag q e (inj₂ c) = proj₂ b , proj₁ b
  where b = trunc-ag (AgC-sym ag) q e (inj₁ c)

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

-- AGREEING AT EVERY INDEX IS THE SAME ROWS: a reached row waits on
-- finitely many, and a list of them is a cover.
agree-all : ∀ {A R} {d d′ : Den A} → (∀ n → d ≈ᶜ⟨ R ∣ n ⟩ d′) → Same R d d′
agree-all {d = d} {d′} all p r {q} {e} = to , back
  where
    cover : ∀ {t : EmissionSet _} → Reach t q e → Σ ℕ λ n → DCnt n t q e
    cover (ks , h) = length ks , ks , ≤-refl , λ x kq d → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h x kq d))

    to : enter d p q e → enter d′ p q e
    to x = proj₁ (all (proj₁ c) p r q e (inj₁ (proj₂ c))) x
      where c = cover (entered-reach d p x)

    back : enter d′ p q e → enter d p q e
    back x = proj₂ (all (proj₁ c) p r q e (inj₂ (proj₂ c))) x
      where c = cover (entered-reach d′ p x)

------------------------------------------------------------------------
-- The limit of a chain

-- THE LIMIT: each member of a chain within the next is within its limit.
-- A row of member `k` with few it waits on: every later member agrees on
-- it, so the limit does; with few in the limit, member `k`'s rows it waits
-- on are the limit's, one at a time, so as few.
limit : ∀ {A R} {c : ℕ → Den A} → (∀ n → c n ≈ᶜ⟨ R ∣ n ⟩ c (suc n)) → ∀ k → c k ≈ᶜ⟨ R ∣ k ⟩ LimD c
limit {A} {c = c} ch k p r = top
  where
    X : ℕ → EmissionSet _
    X n = enter (c n) p

    ahead : ∀ j → AgC k (X k) (X (j + k))
    ahead zero    = AgC-refl
    ahead (suc j) = AgC-trans (ahead j) (AgC-mono (m≤n+m k j) (ch (j + k) p r))

    at : ∀ n → k ≤ n → AgC k (X k) (X n)
    at n le = subst (λ m → AgC k (X k) (X m)) (m∸n+n≡m le) (ahead (n ∸ k))

    L = enter (LimD c) p

    agrees′ : ∀ {q e} → DCnt k (X k) q e → (X k q e → L q e) × (L q e → X k q e)
    agrees′ {q} {e} bx = to , back
      where
        ag : ∀ n → k ≤ n → (X k q e → X n q e) × (X n q e → X k q e)
        ag n le = at n le q e (inj₁ bx)

        back′ : ∀ {v e′} → Lim X v e′ → v ≺ q → Dep q e v e′ → Σ (Ev A) λ e″ → X k v e″ × Dep q e v e″
        back′ {v} {e′} (from N l) vq d = e′ , proj₂ (at (N ⊔ k) (m≤n⊔m N k) v e′ (inj₁ (dcnt-down bx vq d))) (l (N ⊔ k) (m≤m⊔n N k)) , d

        to : X k q e → L q e
        to x = from k (λ n le → proj₁ (ag n le) x) , reach-via back′ (entered-reach (c k) p x)

        back : L q e → X k q e
        back (from N l , _) = proj₂ (ag (N ⊔ k) (m≤n⊔m N k)) (l (N ⊔ k) (m≤m⊔n N k))

    bounds : ∀ {q e} → DCnt k L q e → DCnt k (X k) q e
    bounds = dcnt-pull (entered-reach (c k) p) (λ x d → proj₁ (agrees′ d) x)

    top : AgC k (X k) L
    top q e (inj₁ bx) = agrees′ bx
    top q e (inj₂ bl) = agrees′ (bounds bl)

------------------------------------------------------------------------
-- Defer

-- Every row read at a `defer`'s body subscription lies at or past it, and
-- so does every connect it pins.
Aft : ∀ {A} → (Pos → Set) → Den A → Set
Aft R s = ∀ p → R p → ∀ {y e} → enter s (p ++ [ ix 1 ]) y e → (p ++ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (p ++ [ ix 1 ]) ≼ r)

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

  -- A body row waits on the guard.
  g-dep : ∀ {A} p {q} {e : Ev A} → (∀ {r} → e ≡ pin r → (p ++ [ ix 1 ]) ≼ r) → Dep q e (p ++ [ ix 0 ]) skip
  g-dep p {e = out _} _ = tt
  g-dep p {e = skip}  _ = tt
  g-dep p {e = end}   _ = tt
  g-dep p {e = pin r} a _ = inj₁ (≺-≼-≺ {p ++ [ ix 0 ]} {p ++ [ ix 1 ]} {r} (ticks p 0) (a refl))

-- A `defer`'s body, with its guard before it: one position fewer.
module Guarded {A : Set} (s : Den A) (p : Pos) (aft : ∀ {y e} → enter s (p ++ [ ix 1 ]) y e → (p ++ [ ix 1 ]) ≼ y × (∀ {r} → e ≡ pin r → (p ++ [ ix 1 ]) ≼ r)) where
  g b₀ : Pos
  g  = p ++ [ ix 0 ]
  b₀ = p ++ [ ix 1 ]

  -- Before the body's subscription: no body row there.
  none-before : ∀ {y e} → enter s b₀ y e → y ≺ b₀ → ⊥
  none-before x yb = proj₁ (aft x) yb

  shrink : ∀ {n q e} → Dep q e g skip → DCnt (suc n) (DeferT s p) q e → DCnt n (enter s b₀) q e
  shrink {n} {q} {e} gd (ks , le , h) with ≼-or-≻ q g
  ... | inj₁ qg = [] , z≤n , λ {y} x yq _ → ⊥-elim (none-before x (≺-trans {y} {g} {b₀} (≺-≼-≺ {y} {q} {g} yq qg) (ticks p 0)))
  ... | inj₂ gq with h guard gq gd
  ...   | inj₁ gq′ = [] , z≤n , λ {y} x yq _ → ⊥-elim (none-before x (≺-trans {y} {q} {b₀} yq (under-guard p gq′)))
  ...   | inj₂ a with pick a
  ...     | x , gx , ks′ , eq , sp = ks′ , ≤-pred (subst (_≤ suc n) (sym eq) le) , cover
    where
      cover : ∀ {y e′} → enter s b₀ y e′ → y ≺ q → Dep q e y e′ → Cov q ks′ y
      cover {y} x′ yq d with h (body x′) yq d
      ... | inj₁ yq′ = inj₁ yq′
      ... | inj₂ a′ with sp a′
      ...   | inj₂ a″ = inj₂ a″
      ...   | inj₁ yx with ⊑-cmp y g yx gx
      ...     | inj₁ yg = ⊥-elim (none-before x′ (≼-≺-≺ {y} {g} {b₀} (⊑-≼ yg) (ticks p 0)))
      ...     | inj₂ gy = ⊥-elim (none-before x′ (under-guard p gy))

-- DEFER IS CONTRACTIVE: its guard is one position before its body, and
-- every body row waits on it.
contract : ∀ {A R k} {s s′ : Den A} → (∀ p → R p → R (p ++ [ ix 1 ])) → Aft R s → Aft R s′
         → s ≈ᶜ⟨ R ∣ k ⟩ s′ → Op.defer s ≈ᶜ⟨ R ∣ suc k ⟩ Op.defer s′
contract {R = R} {k} {s} {s′} up as as′ ag p r = trunc-ag inner
  where
    b₀ = p ++ [ ix 1 ]
    bod = ag b₀ (up p r)

    inner : AgC (suc k) (DeferT s p) (DeferT s′ p)
    inner q e side = to , back
      where
        sh : Dep q e (p ++ [ ix 0 ]) skip → DCnt k (enter s b₀) q e ⊎ DCnt k (enter s′ b₀) q e
        sh gd = ⊎-map (Guarded.shrink s p (as p r) gd) (Guarded.shrink s′ p (as′ p r) gd) side

        to : DeferT s p q e → DeferT s′ p q e
        to guard    = guard
        to (body x) = body (proj₁ (bod q e (sh (g-dep p {q} {e} (proj₂ (as p r x))))) x)

        back : DeferT s′ p q e → DeferT s p q e
        back guard     = guard
        back (body x′) = body (proj₂ (bod q e (sh (g-dep p {q} {e} (proj₂ (as′ p r x′))))) x′)

-- THE FIRST UNFOLDING: the spin and the unfolded `defer` agree at their
-- first row, the guard, where the body has not begun; with no position
-- a body row waits on, it lies at or under the guard.
unfold₀ : ∀ {A R} {s : Den A} → Aft R s → Op.⊥ ≈ᶜ⟨ R ∣ 0 ⟩ Op.defer s
unfold₀ {s = s} as p r q e side = to , back
  where
    open Guarded s p (as p r) using (g; b₀; none-before)

    spin-reach : Reach (Spin p) g skip
    spin-reach = [] , λ { (spin zero) lt _ → ⊥-elim (≺-irrefl {g} lt) ; (spin (suc j)) lt _ → ⊥-elim (≺→≼ {g} {p ++ [ ix (suc j) ]} (ticks p j) lt) }

    defer-reach : Reach (DeferT s p) g skip
    defer-reach = [] , λ { guard lt _ → ⊥-elim (≺-irrefl {g} lt) ; (body {y} x) lt _ → ⊥-elim (≺→≼ {g} {y} (≺-≼-≺ {g} {b₀} {y} (ticks p 0) (proj₁ (as p r x))) lt) }

    -- A row waiting on the guard lies before the body.
    early : Dep q e g skip → q ≺ b₀
    early gd with ≼-or-≻ q g
    ... | inj₁ qg = ≼-≺-≺ {q} {g} {b₀} qg (ticks p 0)
    ... | inj₂ gq = under-guard p (lone side)
      where
        lone : _ → g ⊑ q
        lone (inj₁ ([] , _ , h)) with h (spin 0 , spin-reach) gq gd
        ... | inj₁ gq′ = gq′
        ... | inj₂ ()
        lone (inj₁ (_ ∷ _ , () , _))
        lone (inj₂ ([] , _ , h)) with h (guard , defer-reach) gq gd
        ... | inj₁ gq′ = gq′
        ... | inj₂ ()
        lone (inj₂ (_ ∷ _ , () , _))

    to : Truncate (Spin p) q e → Truncate (DeferT s p) q e
    to (spin zero , _)    = guard , defer-reach
    to (spin (suc j) , _) = ⊥-elim (ix-past p j (early tt))

    back : Truncate (DeferT s p) q e → Truncate (Spin p) q e
    back (guard , _)  = spin 0 , spin-reach
    back (body x , _) = ⊥-elim (none-before x (early (g-dep p {q} {e} (proj₂ (as p r x)))))
