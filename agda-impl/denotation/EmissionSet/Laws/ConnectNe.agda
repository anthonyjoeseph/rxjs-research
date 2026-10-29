{-# OPTIONS --guardedness #-}

-- A CONNECT KEEPS THE MODULUS.  Within the bound before `q` on one side,
-- every connect row at or before `q` is on the other: each kind of row
-- bounds the source rows before it, so the sources agree there, and so
-- do the bodies — one body against the other's over the same hot, then
-- that against the other hot by causality.
--
-- A source row before a body row is alive: an end at or before it would
-- put the body row in that end's burst, under a body position leading the
-- source row.  An alive source row shows a row one label down, before the
-- cut, so within the bound.  Only before a pinned row can a source row be
-- past the body's end, and it is then pinned itself, so within the bound.
module denotation.EmissionSet.Laws.ConnectNe where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; _≤_; _+_; _≤?_)
open import Data.Nat.Properties using (≤-trans; m≤m+n; +-monoˡ-≤)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (yes; no)

open import denotation.MonotonicList.Events using (Pos; ix; inside; <ᵖ-between; <ᵖ-split; <ᵖ-step)
open import denotation.EmissionSet using (EmissionSet; end; _≺_; _≼_; Den; hot; enter; Proper; module Connect; connectᵀ)
open import denotation.EmissionSet.Laws.Modulus
  using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgreeTo-trans; AgS; Bnd<; trunc-ag; _≈⟨_∣_⟩_; ≈-sym; _~⟨_⟩_;
  size; size-++; ≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≼-false; ≺-ext)
open import denotation.EmissionSet.Laws.Worlds
  using (step; plain-ix; Ok; _⊕_; Lawful; InvAt; InvD; ok-step; world-after; _⊑_; ⊑-refl; ⊑-≼;
  ⊑-inside; inside-⊑; Anc; world-anc; apart)
import denotation.EmissionSet.Laws.Connect as LC

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
  -- Past `k`: past its first child, or that child.
  ≺-succ : ∀ {k y} → k ≺ y → (y ≡ k ++ [ ix 0 ] → ⊥) → (k ++ [ ix 0 ]) ≺ y
  ≺-succ {k} {y} lt ne with <ᵖ-split (k ++ [ ix 0 ]) y (<ᵖ-step k y (Equivalence.to T-≡ lt))
  ... | inj₁ l  = Equivalence.from T-≡ l
  ... | inj₂ eq = ⊥-elim (ne (sym eq))

  -- What lies under `w` is an interval.
  conv : ∀ {w a b y} → w ⊑ a → a ≼ b → b ≺ y → w ⊑ y → w ⊑ b
  conv {w} {a} {b} wa ab by (ys , refl) with <ᵖ-split w b (≼-false {w} {b} (≼-trans {w} {a} {b} (⊑-≼ wa) ab))
  ... | inj₁ lt   = <ᵖ-between w b ys lt (Equivalence.to T-≡ by)
  ... | inj₂ refl = [] , sym (++-identityʳ w)

  sz-snoc : ∀ k → size k ≤ size (k ++ [ ix 0 ])
  sz-snoc k = subst (size k ≤_) (sym (size-++ k (ix 0))) (m≤m+n (size k) 1)

  module Core {A B : Set} {H : Pos → Set} {n : ℕ} {s s′ : Den A} {F F′ : Den A → Den B}
              (Is : InvD H s) (Is′ : InvD H s′)
              (IF : ∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) (IF′ : ∀ {t} → Lawful t → InvD (H ⊕ t) (F′ (hot t)))
              (cF′ : Causal F′)
              (as : s ≈⟨ Ok H ∣ n ⟩ s′) (aF : ∀ {t} → Lawful t → F (hot t) ≈⟨ Ok (H ⊕ t) ∣ n ⟩ F′ (hot t))
              (p : Pos) (ok : Ok H p) where

    module C  = Connect s F p
    module C′ = Connect s′ F′ p

    p₀ r : Pos
    p₀ = p ++ [ ix 0 ]
    r  = p ++ [ ix 1 ]

    Nσ : ℕ
    Nσ = size r + n

    Iσ  = LC.Iσ {s = s} {F = F} Is IF p ok
    Iσ′ = LC.Iσ {s = s′} {F = F′} Is′ IF′ p ok
    Iβ  = LC.Iβ {s = s} {F = F} Is IF p ok
    Iβ′ = LC.Iβ {s = s′} {F = F′} Is′ IF′ p ok

    up : ∀ i {m} → m ≤ size p + n → m ≤ size (p ++ [ ix i ]) + n
    up i le = ≤-trans le (subst (λ z → size p + n ≤ z + n) (sym (size-++ p (ix i))) (+-monoˡ-≤ n (m≤m+n (size p) 1)))

    aσ : AgS Nσ C.σ C′.σ
    aσ = as r (ok-step p ok)

    aβ : AgS (size p₀ + n) C.β (enter (F′ (hot (Proper C.σ))) p₀)
    aβ = aF (LC.lawful {s = s} {F = F} Is IF p ok) p₀ (LC.ok₀ {s = s} {F = F} Is IF p ok)

    -- A source row is not its first child's position, nor a body row's.
    flat-shown : ∀ {k y e e′} → C.σ k e → C.σ y e′ → y ≡ k ++ [ ix 0 ] → ⊥
    flat-shown x y refl = InvAt.flat Iσ x y

    apart-shown : ∀ {k y e} → Anc p₀ y → C.σ k e → y ≡ k ++ [ ix 0 ] → ⊥
    apart-shown a x refl = apart (proj₁ ok) a (world-anc (step (LC.sw {s = s} {F = F} Is IF p ok x) plain-ix))

    -- A source row lies under the source's subscription once it lies
    -- before a row that does.
    in-r : ∀ {k y e} → C.σ k e → k ≺ y → T (inside r y) → T (inside r k)
    in-r {k} {y} x lt i =
      ⊑-inside (conv (⊑-refl r) (≺→≼ {r} {k} (world-after (InvAt.world Iσ x) (InvAt.real Iσ x))) lt (inside-⊑ r y i))

    module _ {q : Pos} (bd : Bnd< (size p + n) C.ConnT q) where

      -- Source rows before `z` within the bound.
      SB : Pos → Set
      SB z = Bnd< Nσ C.σ z

      shown-b : ∀ {k e} → C.σ k e → C.Alive k → (k ++ [ ix 0 ]) ≺ q → size k ≤ Nσ
      shown-b {k} x al lt = up 1 (≤-trans (sz-snoc k) (bd (C.shown x al) lt))

      sb-gen : ∀ {z} → z ≼ q → (∀ {k e} → C.σ k e → k ≺ z → C.Alive k)
             → (∀ {k e} → C.σ k e → C.Alive k → z ≡ k ++ [ ix 0 ] → ⊥) → SB z
      sb-gen {z} zq al ne {k} x lt = shown-b x (al x lt) (≺-≼-≺ {k ++ [ ix 0 ]} {z} {q} (≺-succ lt (ne x (al x lt))) zq)

      σ-ag : ∀ {z} → SB z → AgreeTo z C.σ C′.σ
      σ-ag b = aσ _ (inj₁ b)

      β-ag : ∀ {z} → z ≼ q → SB z → AgreeTo z C.β C′.β
      β-ag {z} zq b =
        AgreeTo-trans (aβ z (inj₁ λ {y} x yz → up 0 (bd (C.body x) (≺-≼-≺ {y} {z} {q} yz zq))))
                      (cF′ (proper-ag (σ-ag b)) p₀)

      -- Below an alive source row, every source row is alive.
      sb-alive : ∀ {k e} → C.σ k e → C.Alive k → k ≼ q → SB k
      sb-alive {k} xk al kq = sb-gen kq (λ {j} x lt {c} ce → ≺-trans {j} {k} {c} lt (al ce)) (λ x _ eq → flat-shown x xk eq)

      σ-to : ∀ {k e} → C.σ k e → C.Alive k → k ≼ q → C′.σ k e
      σ-to {k} x al kq = proj₁ (upto (σ-ag (sb-alive x al kq)) {k} (≼-refl {k})) x

      -- Below a body row, every source row is alive.
      sb-β : ∀ {y e} → C.β y e → y ≼ q → SB y
      sb-β {y} b yq = sb-gen yq alive (λ x _ → apart-shown (world-anc (InvAt.world Iβ b)) x)
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
      sb-β′ {y} b yq = sb-gen yq alive (λ x _ → apart-shown (world-anc (InvAt.world Iβ′ b)) x)
        where
          alive : ∀ {k e} → C.σ k e → k ≺ y → C.Alive k
          alive {k} x lt {c} ce with ≼-or-≻ c k
          ... | inj₂ kc = kc
          ... | inj₁ ck with InvAt.burst Iβ′ (end← ce (≼-trans {c} {y} {q} (≺→≼ {c} {y} (≼-≺-≺ {c} {k} {y} ck lt)) yq)) b (≼-≺-≺ {c} {k} {y} ck lt)
          ...   | w , w⁼ , ic , iy =
            ⊥-elim (LC.body-leads {s = s′} {F = F′} Is′ IF′ p ok w⁼ (LC.sw {s = s} {F = F} Is IF p ok x) (conv (inside-⊑ w c ic) ck lt (inside-⊑ w y iy)))

      end→ : ∀ {c} → C′.β c end → c ≼ q → C.β c end
      end→ {c} ce cq = proj₂ (upto (β-ag cq (sb-β′ ce cq)) {c} (≼-refl {c})) ce

      -- Below a pinned row, a source row too large for the bound would be
      -- neither shown nor pinned.
      sb-pin : ∀ {y} → T (inside r y) → y ≼ q → (∀ {k e} → C.σ k e → C.Alive k → y ≡ k ++ [ ix 0 ] → ⊥) → SB y
      sb-pin {y} i yq ne {k} x lt with size k ≤? Nσ
      ... | yes b = b
      ... | no nb = ⊥-elim (nb (up 1 (bd (C.pinned x nal (in-r x lt i)) (≺-≼-≺ {k} {y} {q} lt yq))))
        where nal : C.Alive k → ⊥
              nal al = nb (shown-b x al (≺-≼-≺ {k ++ [ ix 0 ]} {y} {q} (≺-succ lt (ne x al)) yq))

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
          x′ = proj₁ (upto (σ-ag (sb-pin i yq (λ x″ _ eq → flat-shown x″ x eq))) {y} (≼-refl {y})) x
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
          sb : SB k
          sb = sb-gen kq (λ {j} x″ lt {c} ce → ≺-trans {j} {k} {c} lt (al ce))
                 (λ {j} x″ al″ eq → InvAt.flat Iσ′ (σ-to x″ al″ (≼-trans {j} {k} {q} (≺→≼ {j} {k} (subst (j ≺_) (sym eq) (≺-ext j []))) kq))
                                      (subst (λ z → C′.σ z _) eq x′))
          x = proj₂ (upto (σ-ag sb) {k} (≼-refl {k})) x′
      bwd {y} yq (C′.pinned x′ nal′ i) = C.pinned x nal i
        where
          ne : ∀ {k e} → C.σ k e → C.Alive k → y ≡ k ++ [ ix 0 ] → ⊥
          ne {k} x″ al″ eq = InvAt.flat Iσ′ (σ-to x″ al″ (≼-trans {k} {y} {q} (≺→≼ {k} {y} (subst (k ≺_) (sym eq) (≺-ext k []))) yq))
                               (subst (λ z → C′.σ z _) eq x′)
          x = proj₂ (upto (σ-ag (sb-pin i yq ne)) {y} (≼-refl {y})) x′
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
           → s ≈⟨ Ok H ∣ k ⟩ s′ → (∀ {t} → Lawful t → F (hot t) ≈⟨ Ok (H ⊕ t) ∣ k ⟩ F′ (hot t))
           → connectᵀ s F ≈⟨ Ok H ∣ k ⟩ connectᵀ s′ F′
connect-ne {H = H} {k} {s} {s′} {F} {F′} Is Is′ IF IF′ cF cF′ as aF p ok = trunc-ag go
  where
    go : AgS (size p + k) (Connect.ConnT s F p) (Connect.ConnT s′ F′ p)
    go q (inj₁ bd) = Core.agree Is Is′ IF IF′ cF′ as aF p ok bd
    go q (inj₂ bd) = AgreeTo-sym (Core.agree Is′ Is IF′ IF cF
                       (≈-sym {R = Ok H} {k} {s} {s′} as)
                       (λ {t} L → ≈-sym {R = Ok (H ⊕ t)} {k} {F (hot t)} {F′ (hot t)} (aF L)) p ok bd)
