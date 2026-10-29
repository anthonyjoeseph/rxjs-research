{-# OPTIONS --guardedness #-}

-- A CONNECT KEEPS THE ORDER MODULUS.  Few before `q` on one side, every
-- connect row at or before `q` is on the other: the source rows before
-- each kind of row are few, so the sources agree there, and so do the
-- bodies — one body against the other's over the same hot, then that
-- against the other hot by causality.
--
-- A source row before a body row is alive: an end at or before it would
-- put the body row in that end's burst, under a body position leading the
-- source row.  An alive source row shows a row one label down.  Only
-- before a pinned row can a source row be past the body's end, and it is
-- then pinned itself.
module denotation.Laws.ConnectNe where

open import Data.Bool using (T)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _++_; [_])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; ix; inside)
open import denotation.EmissionSet using (EmissionSet; end; _≺_; _≼_; Den; hot; enter; Proper; module Connect; module Op)
open import denotation.Laws.Modulus
  using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; _~⟨_⟩_;
  ≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≺-ext)
open import denotation.Laws.Count using (Cnt; AgC; _≈ᶜ⟨_∣_⟩_; ≈ᶜ-sym; cnt-up; cnt-down; trunc-ag; em; seen; seen-under)
open import denotation.Laws.Worlds
  using (Ok; _⊕_; Lawful; InvAt; InvD; ok-step; inside-⊑; conv; in-world)
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

    aσ : AgC n C.σ C′.σ
    aσ = as r (ok-step p ok)

    aβ : AgC n C.β (enter (F′ (hot (Proper C.σ))) p₀)
    aβ = aF (LC.lawful {s = s} {F = F} Is IF p ok) p₀ (LC.ok₀ {s = s} {F = F} Is IF p ok)

    -- A source row lies under the source's subscription once it lies
    -- before a row that does.
    in-r : ∀ {k y e} → C.σ k e → k ≺ y → T (inside r y) → T (inside r k)
    in-r = in-world Iσ

    module _ {q : Pos} (c : Cnt n C.ConnT q) where

      -- Source rows before `z`, few.
      SB : Pos → Set
      SB z = Cnt n C.σ z

      -- An alive source row shows one label down; one past the body's end
      -- before `z` is pinned.
      sb : ∀ {z} → z ≼ q → (∀ {k e} → C.σ k e → k ≺ z → ¬ C.Alive k → T (inside r k)) → SB z
      sb zq pin = cnt-up (cnt-down c zq) λ {k} x kz →
        em {P = C.Alive k} (λ al → seen-under (C.shown x al) kz) (λ nal → seen (C.pinned x nal (pin x kz nal)) kz)

      σ-ag : ∀ {z} → SB z → AgreeTo z C.σ C′.σ
      σ-ag b = aσ _ (inj₁ b)

      β-ag : ∀ {z} → z ≼ q → SB z → AgreeTo z C.β C′.β
      β-ag {z} zq b =
        AgreeTo-trans (aβ z (inj₁ (cnt-up (cnt-down c zq) λ x yz → seen (C.body x) yz)))
                      (cF′ (proper-ag (σ-ag b)) p₀)

      -- Below an alive source row, every source row is alive.
      sb-alive : ∀ {k} → C.Alive k → k ≼ q → SB k
      sb-alive {k} al kq = sb kq λ {j} x lt nal → ⊥-elim (nal λ {c} ce → ≺-trans {j} {k} {c} lt (al ce))

      σ-to : ∀ {k e} → C.σ k e → C.Alive k → k ≼ q → C′.σ k e
      σ-to {k} x al kq = proj₁ (upto (σ-ag (sb-alive al kq)) {k} (≼-refl {k})) x

      -- Below a body row, every source row is alive.
      sb-β : ∀ {y e} → C.β y e → y ≼ q → SB y
      sb-β {y} b yq = sb yq λ x lt nal → ⊥-elim (nal (alive x lt))
        where
          alive : ∀ {k e} → C.σ k e → k ≺ y → C.Alive k
          alive {k} x lt {c} ce with ≼-or-≻ c k
          ... | inj₂ kc = kc
          ... | inj₁ ck with InvAt.burst Iβ ce b (≼-≺-≺ {c} {k} {y} ck lt)
          ...   | w , w⁼ , ic , iy =
            ⊥-elim (LC.body-leads {s = s} {F = F} Is IF p ok w⁼ (LC.sw {s = s} {F = F} Is IF p ok x) (conv (inside-⊑ w c ic) ck lt (inside-⊑ w y iy)))

      end← : ∀ {c} → C.β c end → c ≼ q → C′.β c end
      end← {c} ce cq = proj₁ (upto (β-ag cq (sb-β ce cq)) {c} (≼-refl {c})) ce

      sb-β′ : ∀ {y e} → C′.β y e → y ≼ q → SB y
      sb-β′ {y} b yq = sb yq λ x lt nal → ⊥-elim (nal (alive x lt))
        where
          alive : ∀ {k e} → C.σ k e → k ≺ y → C.Alive k
          alive {k} x lt {c} ce with ≼-or-≻ c k
          ... | inj₂ kc = kc
          ... | inj₁ ck with InvAt.burst Iβ′ (end← ce (≼-trans {c} {y} {q} (≺→≼ {c} {y} (≼-≺-≺ {c} {k} {y} ck lt)) yq)) b (≼-≺-≺ {c} {k} {y} ck lt)
          ...   | w , w⁼ , ic , iy =
            ⊥-elim (LC.body-leads {s = s′} {F = F′} Is′ IF′ p ok w⁼ (LC.sw {s = s} {F = F} Is IF p ok x) (conv (inside-⊑ w c ic) ck lt (inside-⊑ w y iy)))

      end→ : ∀ {c} → C′.β c end → c ≼ q → C.β c end
      end→ {c} ce cq = proj₂ (upto (β-ag cq (sb-β′ ce cq)) {c} (≼-refl {c})) ce

      -- Below a pinned row, every source row is shown or pinned.
      sb-pin : ∀ {y} → T (inside r y) → y ≼ q → SB y
      sb-pin i yq = sb yq λ x lt _ → in-r x lt i

      fwd : ∀ {y e} → y ≼ q → C.ConnT y e → C′.ConnT y e
      fwd {y} yq (C.body b) = C′.body (proj₁ (upto (β-ag yq (sb-β b yq)) {y} (≼-refl {y})) b)
      fwd {y} yq (C.shown {k} x al) = C′.shown (σ-to x al kq) al′
        where
          kq = ≺→≼ {k} {q} (≺-≼-≺ {k} {k ++ [ ix 0 ]} {q} (≺-ext k []) yq)
          al′ : C′.Alive k
          al′ {c} ce with ≼-or-≻ c k
          ... | inj₂ kc = kc
          ... | inj₁ ck = ⊥-elim (≺-irrefl {k} (≺-≼-≺ {k} {c} {k} (al (end→ ce (≼-trans {c} {k} {q} ck kq))) ck))
      fwd {y} yq (C.pinned x nal i) = C′.pinned x′ nal′ i
        where
          x′ = proj₁ (upto (σ-ag (sb-pin i yq)) {y} (≼-refl {y})) x
          nal′ : C′.Alive y → _
          nal′ al′ = nal λ {c} ce → al-c ce
            where
              al-c : ∀ {c} → C.β c end → y ≺ c
              al-c {c} ce with ≼-or-≻ c y
              ... | inj₂ yc = yc
              ... | inj₁ cy = ⊥-elim (≺-irrefl {y} (≺-≼-≺ {y} {c} {y} (al′ (end← ce (≼-trans {c} {y} {q} cy yq))) cy))

      bwd : ∀ {y e} → y ≼ q → C′.ConnT y e → C.ConnT y e
      bwd {y} yq (C′.body b) = C.body (proj₂ (upto (β-ag yq (sb-β′ b yq)) {y} (≼-refl {y})) b)
      bwd {y} yq (C′.shown {k} x′ al′) = C.shown x al
        where
          kq = ≺→≼ {k} {q} (≺-≼-≺ {k} {k ++ [ ix 0 ]} {q} (≺-ext k []) yq)
          al : C.Alive k
          al {c} ce with ≼-or-≻ c k
          ... | inj₂ kc = kc
          ... | inj₁ ck = ⊥-elim (≺-irrefl {k} (≺-≼-≺ {k} {c} {k} (al′ (end← ce (≼-trans {c} {k} {q} ck kq))) ck))
          x = proj₂ (upto (σ-ag (sb-alive al kq)) {k} (≼-refl {k})) x′
      bwd {y} yq (C′.pinned x′ nal′ i) = C.pinned x nal i
        where
          x = proj₂ (upto (σ-ag (sb-pin i yq)) {y} (≼-refl {y})) x′
          nal : C.Alive y → _
          nal al = nal′ λ {c} ce → al-c ce
            where
              al-c : ∀ {c} → C′.β c end → y ≺ c
              al-c {c} ce with ≼-or-≻ c y
              ... | inj₂ yc = yc
              ... | inj₁ cy = ⊥-elim (≺-irrefl {y} (≺-≼-≺ {y} {c} {y} (al (end→ ce (≼-trans {c} {y} {q} cy yq))) cy))

      agree : AgreeTo q C.ConnT C′.ConnT
      agree = ⟨ (λ yq → fwd yq , bwd yq) ⟩

connect-ne : ∀ {A B H k} {s s′ : Den A} {F F′ : Den A → Den B}
           → InvD H s → InvD H s′
           → (∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) → (∀ {t} → Lawful t → InvD (H ⊕ t) (F′ (hot t)))
           → Causal F → Causal F′
           → s ≈ᶜ⟨ Ok H ∣ k ⟩ s′ → (∀ {t} → Lawful t → F (hot t) ≈ᶜ⟨ Ok (H ⊕ t) ∣ k ⟩ F′ (hot t))
           → Op.connect s F ≈ᶜ⟨ Ok H ∣ k ⟩ Op.connect s′ F′
connect-ne {H = H} {k} {s} {s′} {F} {F′} Is Is′ IF IF′ cF cF′ as aF p ok = trunc-ag go
  where
    go : AgC k (Connect.ConnT s F p) (Connect.ConnT s′ F′ p)
    go q (inj₁ c) = Core.agree Is Is′ IF IF′ cF′ as aF p ok c
    go q (inj₂ c) = AgreeTo-sym (Core.agree Is′ Is IF′ IF cF
                      (≈ᶜ-sym {R = Ok H} {k} {s} {s′} as)
                      (λ {t} L → ≈ᶜ-sym {R = Ok (H ⊕ t)} {k} {F (hot t)} {F′ (hot t)} (aF L)) p ok c)
