{-# OPTIONS --guardedness #-}

-- A CONNECT KEEPS THE ORDER MODULUS, one row at a time.  What a connect
-- row waits on covers what its own reading waits on: a source row shows
-- one label down, alive or in the burst, so the source rows a shown row
-- waits on are covered, and the sources agree there; a body row waits on
-- the body, and the body on the hot by causality.
--
-- A source row before a body row is alive: an end at or before it would
-- put the body row in that end's burst, under a body position leading the
-- source row.  Before a pin of the body's own lies no source row past the
-- pin's connect, which is a body position; so a pin waiting only on its
-- past still reads the hot no further than its connect.  A kept pin's
-- source rows past its connect are its own pins, outside the burst.
module denotation.Laws.ConnectNe where

open import Data.Bool using (T; not; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _++_; [_])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Events using (Pos; ix; inside)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Dep; EmissionSet; _≺_; _≼_; Den; hot; enter; Proper; module Connect; module Op)
open import denotation.Laws.Modulus
  using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; _~⟨_⟩_;
  ≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≺-ext)
open import denotation.Laws.Count
  using (Cov; Cnt; DCnt; AgC; _≈ᶜ⟨_∣_⟩_; ≈ᶜ-sym; cov-up; cov-down; cov-lift; child; cnt-up; cnt-down; seen; seen-under;
  dcnt-cnt; dcnt-pin; ag-cnt; trunc-ag)
open import denotation.Laws.Worlds
  using (W⁼; Ok; _⊕_; Lawful; InvAt; InvD; ok-step; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc⁺; ⊑-snoc; ⊑-cmp; ⊑-≼; ⊑-inside;
  inside-⊑; conv; in-world; not-up)
import denotation.Laws.Connect as LC

-- A body reads its hot no further than the hot has run.
Causal : ∀ {A B} → (Den A → Den B) → Set₁
Causal F = ∀ {q t t′} → AgreeTo q t t′ → F (hot t) ~⟨ q ⟩ F (hot t′)

private
  proper-to : ∀ {A Q} {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → Proper t y e → Proper t′ y e
  proper-to {Q = Q} {t′ = t′} a {y} yQ (x , pr) = proj₁ (upto a {y} yQ) x , ends
    where
      ends : ∀ {c} → t′ c end → y ≼ c
      ends {c} x′ with ≼-or-≻ c Q
      ... | inj₁ cQ = pr (proj₂ (upto a {c} cQ) x′)
      ... | inj₂ Qc = ≺→≼ {y} {c} (≼-≺-≺ {y} {Q} {c} yQ Qc)

proper-ag : ∀ {A Q} {t t′ : EmissionSet A} → AgreeTo Q t t′ → AgreeTo Q (Proper t) (Proper t′)
proper-ag a = ⟨ (λ {y} yQ → proper-to a yQ , proper-to (AgreeTo-sym a) yQ) ⟩

private
  module Core {A B : Set} {H : Pos → Set} {n : ℕ} {s s′ : Den A} {F F′ : Den A → Den B}
              (Is : InvD H s) (Is′ : InvD H s′)
              (IF : ∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) (IF′ : ∀ {t} → Lawful t → InvD (H ⊕ t) (F′ (hot t)))
              (cF′ : Causal F′)
              (as : s ≈ᶜ⟨ Ok H ∣ n ⟩ s′) (aF : ∀ {t} → Lawful t → F (hot t) ≈ᶜ⟨ Ok (H ⊕ t) ∣ n ⟩ F′ (hot t))
              (p : Pos) (ok : Ok H p) where

    module C  = Connect s F p
    module C′ = Connect s′ F′ p

    p₀ r : Pos
    p₀ = p ++ [ ix 0 ]
    r  = p ++ [ ix 1 ]

    Iσ  = LC.Iσ {s = s} {F = F} Is IF p ok
    Iβ  = LC.Iβ {s = s} {F = F} Is IF p ok
    Iβ′ = LC.Iβ {s = s′} {F = F′} Is′ IF′ p ok

    sw : ∀ {y e} → C.σ y e → W⁼ H r y
    sw = LC.sw {s = s} {F = F} Is IF p ok

    aσ : AgC n C.σ C′.σ
    aσ = as r (ok-step p ok)

    aβ : AgC n C.β (enter (F′ (hot (Proper C.σ))) p₀)
    aβ = aF (LC.lawful {s = s} {F = F} Is IF p ok) p₀ (LC.ok₀ {s = s} {F = F} Is IF p ok)

    σ-ag : ∀ {z} → Cnt n C.σ z → AgreeTo z C.σ C′.σ
    σ-ag {z} b = ag-cnt aσ z (inj₁ b)

    ky : ∀ k → k ≼ (k ++ [ ix 0 ])
    ky k = ≺→≼ {k} {k ++ [ ix 0 ]} (≺-ext k [])

    nin : ∀ {k} → T (not (inside r k)) → T (inside r k) → ⊥
    nin {k} ni i with inside r k
    ... | true  = ni
    ... | false = i

    -- A source row before a body row is alive.
    alive-β : ∀ {y e k e′} → C.β y e → C.σ k e′ → k ≺ y → C.Alive k
    alive-β {y} {k = k} b x lt {c} ce with ≼-or-≻ c k
    ... | inj₂ kc = kc
    ... | inj₁ ck with InvAt.burst Iβ ce b (≼-≺-≺ {c} {k} {y} ck lt)
    ...   | w , w⁼ , ic , iy =
      ⊥-elim (LC.body-leads {s = s} {F = F} Is IF p ok w⁼ (sw x) (conv (inside-⊑ w c ic) ck lt (inside-⊑ w y iy)))

    -- A pin's connect leads it, so is alive with it.
    alive-pin : ∀ {k p′} → C.σ k (pin p′) → C.Alive k → C.Alive p′
    alive-pin {k} {p′} x al {c} ce = ≼-≺-≺ {p′} {k} {c} (⊑-≼ (inside-⊑ p′ k (proj₂ (InvAt.pinned Iσ x)))) (al ce)

    -- What an alive source row outside the burst shows as.
    shown : ∀ {k e} → C.σ k e → C.Alive k → T (not (inside r k)) → Σ (Ev B) (C.ConnT (k ++ [ ix 0 ]))
    shown {e = out _}  x al ni = _ , C.echo x al tt ni
    shown {e = skip}   x al ni = _ , C.echo x al tt ni
    shown {e = end}    x al ni = _ , C.echo x al tt ni
    shown {e = pin _}  x al ni = _ , C.kept x (alive-pin x al) ni (proj₂ (InvAt.pinned Iσ x))

    -- A source row alive or in the burst shows one label down.
    img : ∀ {k e} → C.σ k e → C.Alive k ⊎ T (inside r k) → Σ (Ev B) (C.ConnT (k ++ [ ix 0 ]))
    img {k} x a with inside r k in ik
    img x a          | true  = _ , C.burst x (subst T (sym ik) tt)
    img x (inj₁ al)  | false = shown x al (subst (T ∘ not) (sym ik) tt)
    img x (inj₂ i)   | false = ⊥-elim i

    -- A source pin of a connect outside the burst is outside the burst.
    not-in : ∀ {j k p′} → C.σ j (pin p′) → p′ ⊑ k → T (not (inside r k)) → T (not (inside r j))
    not-in {j} {k} {p′} xj pk ni with inside r j in ij
    ... | false = tt
    ... | true with InvAt.pinned Iσ xj
    ...   | w⁼ , ipj with ⊑-cmp r p′ (inside-⊑ r j (subst T (sym ij) tt)) (inside-⊑ p′ j ipj)
    ...     | inj₁ rp′ = nin ni (⊑-inside (⊑-trans rp′ pk))
    ...     | inj₂ p′r with ⊑-snoc p p′r
    ...       | inj₁ p′p = ⊥-elim (not-up (proj₁ ok) w⁼ p′p)
    ...       | inj₂ refl = nin ni (⊑-inside pk)

    -- Few before a cut.
    module Lin {q : Pos} (c : Cnt n C.ConnT q) where

      sb : ∀ {z} → z ≼ q → (∀ {k e} → C.σ k e → k ≺ z → C.Alive k ⊎ T (inside r k)) → Cnt n C.σ z
      sb zq a = cnt-up (cnt-down c zq) λ x kz → seen-under (proj₂ (img x (a x kz))) kz

      β-ag : ∀ {z} → z ≼ q → Cnt n C.σ z → AgreeTo z C.β C′.β
      β-ag {z} zq b =
        AgreeTo-trans (ag-cnt aβ z (inj₁ (cnt-up (cnt-down c zq) λ x yz → seen (C.body x) yz)))
                      (cF′ (proper-ag (σ-ag b)) p₀)

      end← : ∀ {c} → C.β c end → c ≼ q → C′.β c end
      end← {c} ce cq = proj₁ (upto (β-ag cq (sb cq λ x lt → inj₁ (alive-β ce x lt))) {c} (≼-refl {c})) ce

      -- Below a body row of the other side, every source row is alive.
      alive-β′ : ∀ {y e k e′} → C′.β y e → C.σ k e′ → k ≺ y → k ≼ q → C.Alive k
      alive-β′ {y} {k = k} b x lt kq {c} ce with ≼-or-≻ c k
      ... | inj₂ kc = kc
      ... | inj₁ ck with InvAt.burst Iβ′ (end← ce (≼-trans {c} {k} {q} ck kq)) b (≼-≺-≺ {c} {k} {y} ck lt)
      ...   | w , w⁼ , ic , iy =
        ⊥-elim (LC.body-leads {s = s′} {F = F′} Is′ IF′ p ok w⁼ (sw x) (conv (inside-⊑ w c ic) ck lt (inside-⊑ w y iy)))

      end→ : ∀ {c} → C′.β c end → c ≼ q → C.β c end
      end→ {c} ce cq =
        proj₂ (upto (β-ag cq (sb cq λ {k} x lt → inj₁ (alive-β′ ce x lt (≺→≼ {k} {q} (≺-≼-≺ {k} {c} {q} lt cq))))) {c} (≼-refl {c})) ce

      alive→ : ∀ {k} → C.Alive k → k ≼ q → C′.Alive k
      alive→ {k} al kq {c} ce with ≼-or-≻ c k
      ... | inj₂ kc = kc
      ... | inj₁ ck = ⊥-elim (≺-irrefl {k} (≺-≼-≺ {k} {c} {k} (al (end→ ce (≼-trans {c} {k} {q} ck kq))) ck))

      alive← : ∀ {k} → C′.Alive k → k ≼ q → C.Alive k
      alive← {k} al kq {c} ce with ≼-or-≻ c k
      ... | inj₂ kc = kc
      ... | inj₁ ck = ⊥-elim (≺-irrefl {k} (≺-≼-≺ {k} {c} {k} (al (end← ce (≼-trans {c} {k} {q} ck kq))) ck))

    -- A row's child the row waits on, covered at a cut at or before it.
    via-child : ∀ {y e Q j e′} (d : DCnt n C.ConnT y e) → Q ≼ y → j ≺ Q → C.ConnT (j ++ [ ix 0 ]) e′
              → ((j ++ [ ix 0 ]) ≺ Q → Dep y e (j ++ [ ix 0 ]) e′) → Cov Q (proj₁ d) j
    via-child {y} {Q = Q} {j} (ks , le , h) Qy jQ x dp with child (ix 0) jQ
    ... | inj₁ jQ′ = inj₁ jQ′
    ... | inj₂ lt  = cov-up (⊑-snoc⁺ j) (cov-down (h x (≺-≼-≺ {j ++ [ ix 0 ]} {Q} {y} lt Qy) (dp lt)) lt Qy)

    -- What a burst row's source row waits on: source rows in the burst.
    dσ-burst : ∀ {k e₀} → DCnt n C.ConnT (k ++ [ ix 0 ]) (pin p) → T (inside r k) → DCnt n C.σ k e₀
    dσ-burst {k} d i = proj₁ d , proj₁ (proj₂ d) , λ xj jk _ → via-child d (ky k) jk (C.burst xj (in-world Iσ xj jk i)) λ _ _ → inj₂ refl

    -- An echo's: alive source rows.
    dσ-echo : ∀ {k e₀} → DCnt n C.ConnT (k ++ [ ix 0 ]) skip → C.Alive k → DCnt n C.σ k e₀
    dσ-echo {k} d al = proj₁ d , proj₁ (proj₂ d) , λ {j} xj jk _ →
      via-child {e = skip} d (ky k) jk (proj₂ (img xj (inj₁ λ ce → ≺-trans {j} {k} jk (al ce)))) λ _ → tt

    -- A kept pin's: alive source rows before its connect, and its own pins.
    dσ-kept : ∀ {k p′} → DCnt n C.ConnT (k ++ [ ix 0 ]) (pin p′) → p′ ⊑ k → C.Alive p′ → T (not (inside r k)) → DCnt n C.σ k (pin p′)
    dσ-kept {k} {p′} d pk alp ni = proj₁ d , proj₁ (proj₂ d) , go
      where
        p′y : p′ ≼ (k ++ [ ix 0 ])
        p′y = ⊑-≼ (⊑-trans pk (⊑-snoc⁺ k))

        go : ∀ {j e″} → C.σ j e″ → j ≺ k → Dep k (pin p′) j e″ → Cov k (proj₁ d) j
        go {j} xj jk dp with dp (⊑-inside pk)
        ... | inj₁ jp = cov-lift (via-child d p′y jp (proj₂ (img xj (inj₁ λ ce → ≺-trans {j} {p′} jp (alp ce)))) λ lt _ → inj₁ lt) pk
        ... | inj₂ refl = via-child d (ky k) jk (C.kept xj alp (not-in xj pk ni) (proj₂ (InvAt.pinned Iσ xj))) λ _ _ → inj₂ refl

    -- A body row through the body's agreement and the hot's.
    body-via : ∀ {y e} → DCnt n C.ConnT y e → Cnt n C.σ y → (C.β y e → C′.β y e) × (C′.β y e → C.β y e)
    body-via {y} {e} d b = (λ x → proj₁ g (proj₁ f x)) , (λ x′ → proj₂ f (proj₂ g x′))
      where
        f = aβ y e (inj₁ (proj₁ d , proj₁ (proj₂ d) , λ x → proj₂ (proj₂ d) (C.body x)))
        g = upto (cF′ (proper-ag (σ-ag b)) p₀) {y} {e} (≼-refl {y})

    body-all : ∀ {y e} → DCnt n C.ConnT y e → (∀ {k e′} → Dep y e k e′) → (C.β y e → C′.β y e) × (C′.β y e → C.β y e)
    body-all {y} d all =
        (λ b → proj₁ (body-via d (L.sb (≼-refl {y}) λ x lt → inj₁ (alive-β b x lt))) b)
      , (λ b′ → proj₂ (body-via d (L.sb (≼-refl {y}) λ {k} x lt → inj₁ (L.alive-β′ b′ x lt (≺→≼ {k} {y} lt)))) b′)
      where module L = Lin (dcnt-cnt all d)

    -- A body pin: no source row lies past its connect and before it.
    body-pin : ∀ {y r′} → DCnt n C.ConnT y (pin r′) → T (inside r′ y) → (C.β y (pin r′) → C′.β y (pin r′)) × (C′.β y (pin r′) → C.β y (pin r′))
    body-pin {y} {r′} d i = fwd , bwd
      where
        module L = Lin (dcnt-pin i d)

        r′y : r′ ⊑ y
        r′y = inside-⊑ r′ y i

        below : (∀ {x} → W⁼ H r x → r′ ⊑ x → ⊥) → ∀ {k e′} → C.σ k e′ → k ≺ y → k ≺ r′
        below nl {k} x ky′ with ≼-or-≻ r′ k
        ... | inj₂ kr = kr
        ... | inj₁ rk = ⊥-elim (nl (sw x) (conv (⊑-refl r′) rk ky′ r′y))

        lift : (∀ {k e′} → C.σ k e′ → k ≺ y → k ≺ r′) → Cnt n C.σ r′ → Cnt n C.σ y
        lift bl (ks , le , h) = ks , le , λ x ky′ → cov-lift (h x (bl x ky′)) r′y

        fwd : C.β y (pin r′) → C′.β y (pin r′)
        fwd b = proj₁ (body-via d (lift bl (L.sb (≼-refl {r′}) λ {k} x lt → inj₁ (alive-β b x (≺-≼-≺ {k} {r′} {y} lt (⊑-≼ r′y)))))) b
          where bl = below (LC.body-leads {s = s} {F = F} Is IF p ok (proj₁ (InvAt.pinned Iβ b)))

        bwd : C′.β y (pin r′) → C.β y (pin r′)
        bwd b′ = proj₂ (body-via d (lift bl (L.sb (≼-refl {r′}) λ {k} x lt →
                   inj₁ (L.alive-β′ b′ x (≺-≼-≺ {k} {r′} {y} lt (⊑-≼ r′y)) (≺→≼ {k} {r′} lt))))) b′
          where bl = below (LC.body-leads {s = s′} {F = F′} Is′ IF′ p ok (proj₁ (InvAt.pinned Iβ′ b′)))

    body-row : ∀ {y e} → DCnt n C.ConnT y e → (C.β y e → C′.β y e) × (C′.β y e → C.β y e)
    body-row {e = out a} d = body-all {e = out a} d tt
    body-row {e = skip}  d = body-all {e = skip} d tt
    body-row {e = end}   d = body-all {e = end} d tt
    body-row {y} {pin r′} d with T? (inside r′ y)
    ... | yes i = body-pin d i
    ... | no ¬i = body-all d λ i → ⊥-elim (¬i i)

    fwd : ∀ {y e} → DCnt n C.ConnT y e → C.ConnT y e → C′.ConnT y e
    fwd d (C.body b) = C′.body (proj₁ (body-row d) b)
    fwd d (C.burst {k} {e₀} x i) = C′.burst (proj₁ (aσ k e₀ (inj₁ (dσ-burst d i))) x) i
    fwd d (C.echo {k} {e₀} x al u ni) =
      C′.echo (proj₁ (aσ k e₀ (inj₁ (dσ-echo d al))) x) (Lin.alive→ (dcnt-cnt {e = skip} tt d) al (ky k)) u ni
    fwd d (C.kept {k} {p′} x alp ni ik) =
      C′.kept (proj₁ (aσ k (pin p′) (inj₁ (dσ-kept d pk alp ni))) x) (Lin.alive→ (dcnt-pin (⊑-inside (⊑-trans pk (⊑-snoc⁺ k))) d) alp (≼-refl {p′})) ni ik
      where pk = inside-⊑ p′ k ik

    bwd : ∀ {y e} → DCnt n C.ConnT y e → C′.ConnT y e → C.ConnT y e
    bwd d (C′.body b′) = C.body (proj₂ (body-row d) b′)
    bwd d (C′.burst {k} {e₀} x′ i) = C.burst (proj₂ (aσ k e₀ (inj₁ (dσ-burst d i))) x′) i
    bwd d (C′.echo {k} {e₀} x′ al′ u ni) = C.echo (proj₂ (aσ k e₀ (inj₁ (dσ-echo d al))) x′) al u ni
      where al = Lin.alive← (dcnt-cnt {e = skip} tt d) al′ (ky k)
    bwd d (C′.kept {k} {p′} x′ alp′ ni ik) = C.kept (proj₂ (aσ k (pin p′) (inj₁ (dσ-kept d pk alp ni))) x′) alp ni ik
      where
        pk = inside-⊑ p′ k ik
        alp = Lin.alive← (dcnt-pin (⊑-inside (⊑-trans pk (⊑-snoc⁺ k))) d) alp′ (≼-refl {p′})

    agree : ∀ {y e} → DCnt n C.ConnT y e → (C.ConnT y e → C′.ConnT y e) × (C′.ConnT y e → C.ConnT y e)
    agree d = fwd d , bwd d

connect-ne : ∀ {A B H k} {s s′ : Den A} {F F′ : Den A → Den B}
           → InvD H s → InvD H s′
           → (∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) → (∀ {t} → Lawful t → InvD (H ⊕ t) (F′ (hot t)))
           → Causal F → Causal F′
           → s ≈ᶜ⟨ Ok H ∣ k ⟩ s′ → (∀ {t} → Lawful t → F (hot t) ≈ᶜ⟨ Ok (H ⊕ t) ∣ k ⟩ F′ (hot t))
           → Op.connect s F ≈ᶜ⟨ Ok H ∣ k ⟩ Op.connect s′ F′
connect-ne {H = H} {k} {s} {s′} {F} {F′} Is Is′ IF IF′ cF cF′ as aF p ok = trunc-ag go
  where
    go : AgC k (Connect.ConnT s F p) (Connect.ConnT s′ F′ p)
    go q e (inj₁ c) = Core.agree {s = s} {s′} {F} {F′} Is Is′ IF IF′ cF′ as aF p ok c
    go q e (inj₂ c) = proj₂ b , proj₁ b
      where b = Core.agree {s = s′} {s} {F′} {F} Is′ Is IF′ IF cF
                  (≈ᶜ-sym {R = Ok H} {k} {s} {s′} as)
                  (λ {t} L → ≈ᶜ-sym {R = Ok (H ⊕ t)} {k} {F (hot t)} {F′ (hot t)} (aF L)) p ok c
