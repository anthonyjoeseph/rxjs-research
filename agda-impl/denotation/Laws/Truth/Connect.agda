{-# OPTIONS --guardedness #-}

-- A CONNECT KEEPS THE TRUTH, over its cuts and spin rows (`Core`).  Up to
-- a clean bound the source and the body agree with the next, the body
-- across the two handles by causality (`AtBound`).  A pin is read by hand
-- at itself: a body pin up to its connect, a burst pin up to its source
-- row, a kept pin up to its connect.
module denotation.Laws.Truth.Connect where


open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Position using (Pos; ix; _⊕_; inside)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Den; hot; enter; Few; Dep; Reach; Proper; _≺_; _≼_; module Connect;
  module Op)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-trans; ag-down; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split;
  ≺-≼-≺; ≼-≺-≺; ≺-irrefl; ticks; reach-few; trunc-to)
open import denotation.Laws.Count using (Cov; cov-down; cov-lift; cov-stable)
open import denotation.Laws.Shows using (ShowsK; cover; cov-∈; lead-∈; few-down; few-reach)
open import denotation.Laws.Worlds using (notT; W⁼; inW; Ok; Lawful; InvAt; InvD; Shows; _∪ʰ_; ok-step; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc;
  ⊑-snoc⁺; ⊑-cmp; ⊑-≼; ⊑-inside; inside-⊑; conv; plain-ix; world-after; ⊕-injˡ; ⊕-injʳ; not-up; sib; shrink⁼; narrow⁼;
  flat-under; same-lead)
  renaming (step to wstep)
import denotation.Laws.Connect as LC
open import denotation.Laws.ConnectNe using (Causal; proper-ag; module Rows)
open import denotation.Laws.Hush using (Hushes)
import denotation.Laws.ShowsOps as SO
open import denotation.Laws.Truth using (Truth; Rel; Placed; placing; Spun; Lies; Lie; Clean; Before; Hidden; lie-up; before-of;
  few-ag; hid-via; cov-any; where?; below-next; spin-few; lies-≼)
open import denotation.Laws.Truth.Joining using (lies-⊑; lies-spun; lie-split; cov-++ˡ; cov-++ʳ)
open import denotation.Laws.Truth.Connect.Cuts using (step≼; next≺; first-below; lies-img; lies-up; spun-up; spun-⊑; spun-≼; spun-img; pre≼;
  extend; cov-img; cov-pre; module Core)

module Bound {A B : Set} {H : Pos → Set} {s s′ : Den A} {F F′ : Den A → Den B}
             (Is : InvD H s) (Is′ : InvD H s′)
             (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) (IF′ : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F′ (hot t)))
             (cF′ : Causal F′) (hF : Hushes H F)
             (sk-s : ∀ m q → Ok H q → ShowsK m (enter s q))
             (sk-b : ∀ m {t} → Lawful t → ∀ q → Ok (H ∪ʰ t) q → ShowsK m (enter (F (hot t)) q))
             (R : Rel H s s′) (RF : ∀ {t} → Lawful t → Rel (H ∪ʰ t) (F (hot t)) (F′ (hot t)))
             (p : Pos) (ok : Ok H p) where
  open Core {A} {B} {H} {s} {s′} {F} {F′} Is Is′ IF IF′ cF′ hF sk-s sk-b R RF p ok
  open Rows {s = s} {F = F} Is IF p ok using (sw; alive-β; img; not-in)

  ------------------------------------------------------------------------
  -- Up to a clean bound

  -- Every source row before `z` alive or in the burst: each shows.
  Img : Pos → Set
  Img z = ∀ {j e} → C.σ j e → j ≺ z → C.Alive j ⊎ T (inside r j)

  img-down : ∀ {y z} → Img z → y ≼ z → Img y
  img-down {y} {z} im yz {j} x jy = im x (≺-≼-≺ {j} {y} {z} jy yz)

  img-alive : ∀ {z} → C.Alive z → Img z
  img-alive {z} al {j} x jz = inj₁ (λ {c} ce → ≺-trans {j} {z} {c} jz (al ce))

  img-β : ∀ {y e} → C.β y e → Img y
  img-β b x jy = inj₁ (alive-β b x jy)

  img-burst : ∀ {k} → T (inside r k) → Img k
  img-burst {k} ik {j} x jk = inj₂ (in-burst (σ-r x) jk (inside-⊑ r k ik))

  -- Nothing of a source past a body pin's connect, up to the pin.
  gap : ∀ {r₁ q} → (∀ {x} → W⁼ H r x → r₁ ⊑ x → ⊥) → r₁ ⊑ q → ∀ {k} → r₁ ≺ k → k ≼ q → W⁼ H r k → ⊥
  gap {r₁} {q} nb rq {k} r₁k kq kw with ≼-split {k} {q} kq
  ... | inj₁ k≺q = nb kw (conv {r₁} {r₁} {k} {q} (⊑-refl r₁) (≺→≼ {r₁} {k} r₁k) k≺q rq)
  ... | inj₂ refl = nb kw rq

  -- Before a source cut in the burst, a source row with few before shows
  -- as a burst pin a row under the spin waits on.
  img≺ : ∀ {c j e₀} → TS.Cut c → C.σ j e₀ → j ≺ (c ⊕ [ ix 0 ]) → (j ⊕ [ ix 0 ]) ≺ (c ⊕ [ ix 0 ])
  img≺ {c} {j} cc x jc with ≼-split {j ⊕ [ ix 0 ]} {c ⊕ [ ix 0 ]} (step≼ {j} {c ⊕ [ ix 0 ]} jc)
  ... | inj₁ lt = lt
  ... | inj₂ eq = ⊥-elim (s-at cc (subst (λ z → C.σ z _) (⊕-injˡ j c eq) x))

  pre-cut : ∀ {c y e} → TS.Cut c → r ⊑ c → C.ConnT y e → Reach C.ConnT y e → Spun c y
          → Σ (List Pos) λ ks → ∀ {j e₀} → C.σ j e₀ → Few C.σ j → j ≺ (c ⊕ [ ix 0 ]) → (j ⊕ [ ix 0 ]) ∈ ks
  pre-cut {c} {y} {e} cc rc cy ry sp = by e cy ry
    where
      ij : ∀ {j e₀} → C.σ j e₀ → j ≺ (c ⊕ [ ix 0 ]) → T (inside r j)
      ij x jc = in-burst (σ-r x) jc (⊑-trans rc (⊑-snoc⁺ c))

      j≺y : ∀ {j e₀} → C.σ j e₀ → j ≺ (c ⊕ [ ix 0 ]) → (j ⊕ [ ix 0 ]) ≺ y
      j≺y {j} x jc = ≺-≼-≺ {j ⊕ [ ix 0 ]} {c ⊕ [ ix 0 ]} {y} (img≺ cc x jc) (spun-≼ sp)

      few : Few C.ConnT y → Σ (List Pos) λ ks → ∀ {j e₀} → C.σ j e₀ → Few C.σ j → j ≺ (c ⊕ [ ix 0 ]) → (j ⊕ [ ix 0 ]) ∈ ks
      few (ks , h) = ks , λ x _ jc → h (C.burst x (ij x jc)) (j≺y x jc)

      -- A body pin's connect lies under the spin.
      r″-at : ∀ {r″} → Spun c y → W⁼ (H ∪ʰ Proper C.σ) p₀ r″ → T (inside r″ y) → (c ⊕ [ ix 0 ]) ≼ r″
      r″-at {r″} (m , cm) w ins with ⊑-cmp r″ (c ⊕ [ ix m ]) (inside-⊑ r″ y ins) cm
      ... | inj₂ mr = spun-≼ (m , mr)
      ... | inj₁ rm with ⊑-snoc c rm
      ...   | inj₁ r″c = ⊥-elim (bleads w (Placed.placed PS cc) r″c)
      ...   | inj₂ refl = spun-≼ (m , ⊑-refl (c ⊕ [ ix m ]))

      by : ∀ e → C.ConnT y e → Reach C.ConnT y e
         → Σ (List Pos) λ ks → ∀ {j e₀} → C.σ j e₀ → Few C.σ j → j ≺ (c ⊕ [ ix 0 ]) → (j ⊕ [ ix 0 ]) ∈ ks
      by (out a) _ ry′ = few (reach-few {e = out a} (λ {_} {_} → tt) ry′)
      by skip    _ ry′ = few (reach-few {e = skip} (λ {_} {_} → tt) ry′)
      by end     _ ry′ = few (reach-few {e = end} (λ {_} {_} → tt) ry′)
      by (pin r″) (C.body b) (ks , h) =
        ks , λ {j} x _ jc → h (C.burst x (ij x jc)) (j≺y x jc)
               (λ _ → inj₁ (≺-≼-≺ {j ⊕ [ ix 0 ]} {c ⊕ [ ix 0 ]} {r″} (img≺ cc x jc) (r″-at sp (proj₁ (InvAt.pinned Iβ b)) (proj₂ (InvAt.pinned Iβ b)))))
      by (pin _) (C.burst _ _) (ks , h) = ks , λ x _ jc → h (C.burst x (ij x jc)) (j≺y x jc) (λ _ → inj₂ refl)
      by (pin _) (C.kept {k} x _ ni _) _ = ⊥-elim (notT _ ni (⊑-inside (⊑-trans rc (spun-img sp))))

  -- The next's burst pin past a source cut in the burst: the cut's spin
  -- rows show endlessly many burst pins past its first.
  shadow-burst : ∀ {c} → CutS c → r ⊑ c → ¬ Hidden Cut′ Ct c p
  shadow-burst {c} (cc , y , e , (cy , ry) , sp , sh) rc (ks , h) = shS (cover v (proj₁ PA ++ ks) , mem) last
    where
      v : Pos
      v = c ⊕ [ ix 2 ]

      PA = pre-cut cc rc cy ry sp

      ij : ∀ {j} → c ⊑ j → T (inside r j)
      ij cj = ⊑-inside (⊑-trans rc cj)

      ctj : ∀ {j e₀} → C.σ j e₀ → Few C.σ j → c ⊑ j → Ct (j ⊕ [ ix 0 ]) (pin p)
      ctj x Fj cj = C.burst x (ij cj) , S.reach-burst Fj x (ij cj)

      mem : ∀ {j e₀} → C.σ j e₀ → Few C.σ j → j ≺ v → j ∈ cover v (proj₁ PA ++ ks)
      mem {j} x Fj jv with where? c j
      ... | inj₁ jc = cov-∈ {v} {proj₁ PA ++ ks} {j} (cov-++ˡ (inj₂ (lead-∈ (⊑-snoc⁺ j) (proj₂ PA x Fj jc))))
      ... | inj₂ (inj₁ sj) =
        cov-∈ {v} {proj₁ PA ++ ks} {j} (cov-++ʳ {ks = proj₁ PA} (inj₂ (Any.map (λ {z} h′ → ⊑-trans (⊑-snoc⁺ j) h′)
                                                                       (proj₁ (h (ctj x Fj (spun-⊑ sj)) (spun-up sj))))))
      ... | inj₂ (inj₂ far) = ⊥-elim (≺-irrefl {j} (≺-trans {j} {v} {j} jv (far 2)))

      last : ¬ Few C.σ v
      last F =
        let (z , _ , cz , xz) = TS.shows cc 1 F
            Fz = few-down F (≺→≼ {z} {v} (below-next c cz ≤-refl))
        in proj₂ (h (ctj xz Fz (lies-⊑ (0 , cz))) (spun-up (1 , cz)))
                 (c , inj₁ (cc , y , e , (cy , ry) , sp , sh) , lies-up (0 , cz))

  module AtBound {b : Pos} (bf : Before Cut′ Ct b) (nl : ¬ Lie Cut′ b) where
    -- Hangs show, so the rows before the bound are few.
    fewC : Few C.ConnT b
    fewC = cover b (proj₁ bf) , λ {k} ck kb → cov-∈ (cov-stable λ ¬c → ¬F (λ Fb → ¬c (proj₁ (proj₂ bf (ck , few-reach (few-down Fb (≺→≼ {k} {b} kb))) kb))))
      where
        ¬F : ¬ ¬ Few C.ConnT b
        ¬F = shC (cover b (proj₁ bf) , λ ck F kb → cov-∈ (proj₁ (proj₂ bf (ck , few-reach F) kb)))

    K : List Pos
    K = proj₁ fewC

    -- Past a cut's whole spin, endlessly many rows before the bound.
    far-cut : ∀ {c} → Cut′ c → (∀ j → (c ⊕ [ ix j ]) ≺ b) → ⊥
    far-cut {c} cc far =
      let (z , _ , cz , ctz) = shows′ cc 1 (few-down {X = Ct} Fct (≺→≼ {c ⊕ [ ix 2 ]} {b} (far 2)))
      in proj₂ (proj₂ bf ctz (≺-trans {z} {c ⊕ [ ix 2 ]} {b} (below-next c cz ≤-refl) (far 2))) (c , cc , 0 , cz)
      where
        Fct : Few Ct b
        Fct = proj₁ fewC , λ ct kb → proj₂ fewC (proj₁ ct) kb

    clear-at : ∀ {c y i} → Cut′ c → (c ⊕ [ ix (suc i) ]) ⊑ y → y ≼ b
             → b ≺ (c ⊕ [ ix 0 ]) ⊎ Spun c b ⊎ (∀ j → (c ⊕ [ ix j ]) ≺ b) → ⊥
    clear-at {c} {y} {i} _ l yb (inj₁ bc) =
      ≺-irrefl {b} (≺-trans {b} {c ⊕ [ ix 0 ]} {b} bc
        (≺-≼-≺ {c ⊕ [ ix 0 ]} {y} {b} (≺-≼-≺ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} {y} (ticks c i) (⊑-≼ l)) yb))
    clear-at {c} {y} {i} _ l yb (inj₂ (inj₁ (zero , sb))) =
      ≺-irrefl {b} (≺-≼-≺ {b} {y} {b} (≺-≼-≺ {b} {c ⊕ [ ix (suc i) ]} {y} (below-next c sb (s≤s z≤n)) (⊑-≼ l)) yb)
    clear-at {c} cc _ _ (inj₂ (inj₁ (suc j , sb))) = nl (c , cc , j , sb)
    clear-at cc _ _ (inj₂ (inj₂ far)) = far-cut cc far

    -- No position at or before the bound lies past one of the connect's cuts.
    clearC : ∀ {y} → y ≼ b → ¬ Lie Cut′ y
    clearC {y} yb (c , cc , i , l) = clear-at cc l yb (where? c b)

    reached : ∀ {y e} → y ≼ b → C.ConnT y e → Ct y e
    reached yb cy = cy , few-reach (few-down fewC yb)

    -- A reached row at or before the bound lies past no source cut.
    nlRow : ∀ {y e} → Ct y e → y ≼ b → ¬ Lie TS.Cut y
    nlRow {y} {e} ct yb (c , cc , li) = clearC yb (c , inj₁ (cc , y , e , ct , lies-spun li , inj₂ li) , li)

    -- A source row whose image is at or before the bound.
    by-img : ∀ {j e y} → C.ConnT (j ⊕ [ ix 0 ]) e → j ≺ y → y ≼ b → Cov y K j × ¬ Lie TS.Cut j
    by-img {j} {y = y} cj jy yb = cov-down (cov-img fewC jb cj (⊑-snoc⁺ j)) jy yb , λ l → nlRow (reached ib cj) ib (lie-up l (⊑-snoc⁺ j))
      where
        jb : j ≺ b
        jb = ≺-≼-≺ {j} {y} {b} jy yb

        ib : (j ⊕ [ ix 0 ]) ≼ b
        ib = step≼ {j} {b} jb

    -- Where the source rows show: no source cut lies before.
    nlS : ∀ {y} → Img y → y ≼ b → ¬ Lie TS.Cut y
    nlS {y} im yb (c , cc , li) =
      let (z₀ , e₀ , cz , xz) = TS.first cc
          zy = first-below cz li
          a = im xz zy
          (e , ct) = img xz a
          zb = step≼ {z₀} {b} (≺-≼-≺ {z₀} {y} {b} zy yb)
      in clearC yb (c , inj₁ (cc , z₀ ⊕ [ ix 0 ] , e , reached zb ct , (0 , ⊑-trans cz (⊑-snoc⁺ z₀)) , inj₁ (z₀ , e₀ , xz , (0 , cz) , a)) , li)

    by-σ : ∀ {j e y} → Img y → y ≼ b → C.σ j e → j ≺ y → Cov y K j × ¬ Lie TS.Cut j
    by-σ im yb x jy = by-img (proj₂ (img x (im x jy))) jy yb

    beforeS : ∀ {y} → Img y → y ≼ b → Before TS.Cut C.σ y
    beforeS im yb = K , λ x ky → by-σ im yb x ky

    σ-ag : ∀ {z} → Img z → z ≼ b → AgreeTo z C.σ C′.σ
    σ-ag {z} im zb = ⟨ (λ {y} {e} yz → TS.agree y e (nlS (img-down im yz) (yb yz) , K , λ x ky _ → by-σ (img-down im yz) (yb yz) x ky)) ⟩
      where
        yb : ∀ {y} → y ≼ z → y ≼ b
        yb {y} yz = ≼-trans {y} {z} {b} yz zb

    -- The body: no body cut lies before the bound.
    nlB : ∀ {y} → y ≼ b → ¬ Lie TB.Cut y
    nlB {y} yb (c , cb , li) =
      let (z , e , cz , bz) = TB.first cb
          zb = ≺→≼ {z} {b} (≺-≼-≺ {z} {y} {b} (first-below cz li) yb)
      in clearC yb (c , inj₂ (cb , z , e , reached zb (C.body bz) , (0 , cz)) , li)

    covB : ∀ {k e y} → C.β k e → k ≺ y → y ≼ b → Cov y K k
    covB {k} {y = y} bk ky yb = cov-down (cov-img fewC (≺-≼-≺ {k} {y} {b} ky yb) (C.body bk) (⊑-refl k)) ky yb

    beforeB : ∀ {y} → y ≼ b → Before TB.Cut C.β y
    beforeB {y} yb = K , λ {k} bk ky → covB bk ky yb , nlB (≼-trans {k} {y} {b} (≺→≼ {k} {y} ky) yb)

    βB-ag : AgreeTo b C.β β″
    βB-ag = ⟨ (λ {y} {e} yb → TB.agree y e (nlB yb , K , λ bk ky _ → proj₂ (beforeB yb) bk ky)) ⟩

    -- The body across the two handles, by causality.
    β-ag : ∀ {z} → Img z → z ≼ b → AgreeTo z C.β C′.β
    β-ag {z} im zb = AgreeTo-trans (ag-down {q = b} {z} zb βB-ag) (cF′ (proper-ag (σ-ag im zb)) p₀)

    end→ : ∀ {c} → C.β c end → c ≼ b → C′.β c end
    end→ {c} bc cb = proj₁ (upto (β-ag (img-β bc) cb) {c} (≼-refl {c})) bc

    -- A source row before a next's body row, at or before the bound, is alive.
    alive-β′ : ∀ {y e j e₀} → C′.β y e → C.σ j e₀ → j ≺ y → j ≼ b → C.Alive j
    alive-β′ {y} {j = j} b′ x jy jb {c} ce = at (≼-or-≻ c j)
      where
        at : c ≼ j ⊎ j ≺ c → j ≺ c
        at (inj₂ jc) = jc
        at (inj₁ cj) =
          let (w , w⁼ , ic , iy) = InvAt.burst Iβ′ (end→ ce (≼-trans {c} {j} {b} cj jb)) b′ (≼-≺-≺ {c} {j} {y} cj jy)
          in ⊥-elim (bleads′ w⁼ (sw x) (conv {w} {c} {j} {y} (inside-⊑ w c ic) cj jy (inside-⊑ w y iy)))

    img-β′ : ∀ {y z e} → C′.β y e → z ≼ y → z ≼ b → Img z
    img-β′ {y} {z} b′ zy zb {j} x jz = inj₁ (alive-β′ b′ x (≺-≼-≺ {j} {z} {y} jz zy) (≺→≼ {j} {b} (≺-≼-≺ {j} {z} {b} jz zb)))

    end← : ∀ {c} → C′.β c end → c ≼ b → C.β c end
    end← {c} b′ cb = proj₂ (upto (β-ag (img-β′ b′ (≼-refl {c}) cb) cb) {c} (≼-refl {c})) b′

    alive→ : ∀ {k} → C.Alive k → k ≼ b → C′.Alive k
    alive→ {k} al kb {c} ce′ = at (≼-or-≻ c k)
      where
        at : c ≼ k ⊎ k ≺ c → k ≺ c
        at (inj₂ kc) = kc
        at (inj₁ ck) = al (end← ce′ (≼-trans {c} {k} {b} ck kb))

    alive← : ∀ {k} → C′.Alive k → k ≼ b → C.Alive k
    alive← {k} al′ kb {c} ce = at (≼-or-≻ c k)
      where
        at : c ≼ k ⊎ k ≺ c → k ≺ c
        at (inj₂ kc) = kc
        at (inj₁ ck) = al′ (end→ ce (≼-trans {c} {k} {b} ck kb))

    -- A kept pin's source row, its connect alive: clean wherever the row is.
    cleanK : ∀ {k p′} → C.Alive p′ → T (not (inside r k)) → T (inside p′ k) → k ≼ b → ¬ Lie TS.Cut k
           → Clean TS.Cut C.σ k (pin p′)
    cleanK {k} {p′} alp ni ik kb nk = nk , K , dep
      where
        dep : ∀ {j e′} → C.σ j e′ → j ≺ k → Dep k (pin p′) j e′ → Cov k K j × ¬ Lie TS.Cut j
        dep {j} x jk d with d ik
        ... | inj₁ jp   = by-img (proj₂ (img x (img-alive {p′} alp x jp))) jk kb
        ... | inj₂ refl = by-img (kept-img {j = j} {k = k} x alp ni (inside-⊑ p′ k ik)) jk kb

    -- The next's kept pin: hidden under a source cut, hidden there.
    nk-kept : ∀ {k p′} → C′.σ k (pin p′) → C.Alive p′ → T (not (inside r k)) → T (inside p′ k) → k ≼ b → p′ ≼ b
            → ¬ Lie TS.Cut k
    nk-kept {k} {p′} x′ alp ni ik kb pb (c , cc , li) with lie-split li (inside-⊑ p′ k ik)
    ... | inj₁ lp = nlS (img-alive {p′} alp) pb (c , cc , lp)
    ... | inj₂ pc = TS.shadow cc x′ li pc (beforeS (img-alive {p′} alp) pb) (nlS (img-alive {p′} alp) pb) (b ∷ K , hid)
      where
        hid : ∀ {j} → C.σ j (pin p′) → Spun c j → Any.Any (j ⊑_) (b ∷ K) × ¬ Lie TS.Cut j
        hid {j} xj (zero , cj) = cov-any (cov-img fewC jb ct (⊑-snoc⁺ j)) , λ l → nlRow (reached ib ct) ib (lie-up l (⊑-snoc⁺ j))
          where
            ct : C.ConnT (j ⊕ [ ix 0 ]) (pin p′)
            ct = kept-img {j = j} {k = k} xj alp ni (inside-⊑ p′ k ik)

            jb : j ≺ b
            jb = ≺-≼-≺ {j} {c ⊕ [ ix 1 ]} {b} (below-next c cj (s≤s z≤n)) (≼-trans {c ⊕ [ ix 1 ]} {k} {b} (lies-≼ li) kb)

            ib : (j ⊕ [ ix 0 ]) ≼ b
            ib = step≼ {j} {b} jb
        hid {j} xj (suc i , cj) =
          ⊥-elim (clearC kb (c , inj₁ (cc , j ⊕ [ ix 0 ] , pin p′
                                      , (kept-img {j = j} {k = k} xj alp ni (inside-⊑ p′ k ik) , S.reach-kept (few-down fewC pb) xj)
                                      , spun-up (suc i , cj) , inj₂ (lies-up (i , cj))) , li))

    agC→ : ∀ {y e} → y ≼ b → C.ConnT y e → C′.ConnT y e
    agC→ {y} yb (C.body bz) = C′.body (proj₁ (upto (β-ag (img-β bz) yb) {y} (≼-refl {y})) bz)
    agC→ yb (C.burst {k} x ik) = C′.burst (proj₁ (upto (σ-ag (img-burst ik) (pre≼ {k} {b} yb)) {k} (≼-refl {k})) x) ik
    agC→ yb (C.echo {k} x al u ni) = C′.echo (proj₁ (upto (σ-ag (img-alive {k} al) (pre≼ {k} {b} yb)) {k} (≼-refl {k})) x) (alive→ {k} al (pre≼ {k} {b} yb)) u ni
    agC→ yb (C.kept {k} {p′} x alp ni ik) =
      C′.kept (proj₁ (TS.agree k (pin p′) (cleanK alp ni ik (pre≼ {k} {b} yb) (λ l → nlRow (reached yb (C.kept x alp ni ik)) yb (lie-up l (⊑-snoc⁺ k))))) x)
              (alive→ {p′} alp (≼-trans {p′} {k} {b} (⊑-≼ (inside-⊑ p′ k ik)) (pre≼ {k} {b} yb))) ni ik

    agC← : ∀ {y e} → y ≼ b → C′.ConnT y e → C.ConnT y e
    agC← {y} yb (C′.body b′) = C.body (proj₂ (upto (β-ag (img-β′ b′ (≼-refl {y}) yb) yb) {y} (≼-refl {y})) b′)
    agC← yb (C′.burst {k} x′ ik) = C.burst (proj₂ (upto (σ-ag (img-burst ik) (pre≼ {k} {b} yb)) {k} (≼-refl {k})) x′) ik
    agC← yb (C′.echo {k} x′ al′ u ni) =
      C.echo (proj₂ (upto (σ-ag (img-alive {k} (alive← {k} al′ (pre≼ {k} {b} yb))) (pre≼ {k} {b} yb)) {k} (≼-refl {k})) x′) (alive← {k} al′ (pre≼ {k} {b} yb)) u ni
    agC← yb (C′.kept {k} {p′} x′ alp′ ni ik) =
      C.kept (proj₂ (TS.agree k (pin p′) (cleanK alp ni ik (pre≼ {k} {b} yb) (nk-kept x′ alp ni ik (pre≼ {k} {b} yb) pb))) x′) alp ni ik
      where
        pb : p′ ≼ b
        pb = ≼-trans {p′} {k} {b} (⊑-≼ (inside-⊑ p′ k ik)) (pre≼ {k} {b} yb)

        alp : C.Alive p′
        alp = alive← alp′ pb

    agCB : AgreeTo b C.ConnT C′.ConnT
    agCB = ⟨ (λ {y} {e} yb → agC→ yb , agC← yb) ⟩

    agCt : AgreeTo b Ct Ct′
    agCt = trunc-to agCB

    fewC′ : Few C′.ConnT b
    fewC′ = few-ag agCB (≼-refl {b}) fewC

    -- The next's kept pin past a source cut: hidden there, hidden under the source's.
    shadow-kept : ∀ {c k} → CutS c → C′.σ k (pin b) → C′.Alive b → T (not (inside r k)) → T (inside b k)
                → Lies c (k ⊕ [ ix 0 ]) → b ⊑ c → ¬ Hidden Cut′ Ct c b
    shadow-kept {c} {k} (cc , _) x′ alp′ ni ik li pc (ks , h) =
      TS.shadow cc x′ (lies-img li) pc (beforeS (img-alive {b} alp) (≼-refl {b})) (nlS (img-alive {b} alp) (≼-refl {b})) (ks , hid)
      where
        alp : C.Alive b
        alp = alive← alp′ (≼-refl {b})

        hid : ∀ {j} → C.σ j (pin b) → Spun c j → Any.Any (j ⊑_) ks × ¬ Lie TS.Cut j
        hid {j} xj sj =
            Any.map (λ {z} h′ → ⊑-trans (⊑-snoc⁺ j) h′) (proj₁ hj)
          , λ { (c′ , cc′ , l) → proj₂ hj (c′ , inj₁ (cc′ , j ⊕ [ ix 0 ] , pin b , ct , lies-spun (lies-up l) , inj₂ (lies-up l)) , lies-up l) }
          where
            ct : Ct (j ⊕ [ ix 0 ]) (pin b)
            ct = kept-img {j = j} {k = k} xj alp ni (inside-⊑ b k ik) , S.reach-kept fewC xj

            hj = h ct (spun-up sj)

    -- The next's body pin past a body cut: across the handles it is the
    -- body's next's, and the body's pins under the spin are the connect's.
    shadow-body : ∀ {c w} → CutB c → C′.β w (pin b) → Lies c w → b ⊑ c → ¬ Hidden Cut′ Ct c b
    shadow-body {c} {w} (cb , y , e , (cy , _) , sp) b′ li bc hd =
      TB.shadow cb b″ li bc (beforeB (≼-refl {b})) (nlB (≼-refl {b})) (hid-via {Y = C.β} {Z = Ct} im hd)
      where
        imb : Img b
        imb {j} x jb = inj₁ (alive-β (body-in cb cy sp) x (≺-≼-≺ {j} {b} {y} jb (≼-trans {b} {c} {y} (⊑-≼ bc) (⊑-≼ (spun-⊑ sp)))))

        nb : ∀ {x} → W⁼ H r x → b ⊑ x → ⊥
        nb xw le = bleads′ (proj₁ (InvAt.pinned Iβ′ b′)) xw le

        bw : b ⊑ w
        bw = inside-⊑ b w (proj₂ (InvAt.pinned Iβ′ b′))

        σw : AgreeTo w C.σ C′.σ
        σw = extend (σ-ag imb (≼-refl {b})) (λ x bk kw → gap nb bw bk kw (sw x)) (λ x′ bk kw → gap nb bw bk kw (sw′ x′))

        b″ : β″ w (pin b)
        b″ = proj₂ (upto (cF′ (proper-ag σw) p₀) {w} (≼-refl {w})) b′

        im : ∀ {z} → C.β z (pin b) → Spun c z → Ct z (pin b) × (¬ Lie Cut′ z → ¬ Lie TB.Cut z)
        im {z} bz _ = ct , λ n (c′ , cb′ , l′) → n (c′ , inj₂ (cb′ , z , pin b , ct , lies-spun l′) , l′)
          where
            ct : Ct z (pin b)
            ct = C.body bz , S.reach-bpin fewC bz

  ------------------------------------------------------------------------
  -- The rows agree where clean

  -- Clean before itself: read up to itself.
  by-all : ∀ {q e} → Clean Cut′ Ct q e → (∀ {k e₀} → k ≺ q → Dep q e k e₀) → (Ct q e → Ct′ q e) × (Ct′ q e → Ct q e)
  by-all {q} cl dp = upto (AtBound.agCt {q} (before-of cl (≼-refl {q}) dp) (proj₁ cl)) (≼-refl {q})

  -- A body pin: read up to its connect, the body across the handles past it.
  module PinB {q r₁ : Pos} (ins : T (inside r₁ q)) (cl : Clean Cut′ Ct q (pin r₁)) where
    rq : r₁ ⊑ q
    rq = inside-⊑ r₁ q ins

    open AtBound {r₁} (before-of cl (⊑-≼ rq) (λ kr _ → inj₁ kr)) (λ l → proj₁ cl (lie-up l rq))

    cks : List Pos
    cks = proj₁ (proj₂ cl)

    cleanBq : ¬ Lie TB.Cut q → Clean TB.Cut C.β q (pin r₁)
    cleanBq nq = nq , K ++ cks , dep
      where
        dep : ∀ {k e′} → C.β k e′ → k ≺ q → Dep q (pin r₁) k e′ → Cov q (K ++ cks) k × ¬ Lie TB.Cut k
        dep {k} bk kq d with d ins
        ... | inj₁ kr   = cov-++ˡ (cov-lift (covB bk kr (≼-refl {r₁})) rq) , nlB (≺→≼ {k} {r₁} kr)
        ... | inj₂ refl = cov-++ʳ {ks = K} (proj₁ hit) , λ { (c , cb , l) → proj₂ hit (c , inj₂ (cb , k , pin r₁ , ct , lies-spun l) , l) }
          where
            ct : Ct k (pin r₁)
            ct = C.body bk , S.reach-bpin fewC bk

            hit = proj₂ (proj₂ cl) ct kq (λ _ → inj₂ refl)

    -- Either source agrees up to the pin, nothing of it past the connect.
    σ-to : (∀ {x} → W⁼ H r x → r₁ ⊑ x → ⊥) → Img r₁ → AgreeTo q C.σ C′.σ
    σ-to nb im = extend (σ-ag im (≼-refl {r₁})) (λ x rk kq → gap nb rq rk kq (sw x)) (λ x′ rk kq → gap nb rq rk kq (sw′ x′))

    toB : C.β q (pin r₁) → Ct q (pin r₁) → Ct′ q (pin r₁)
    toB bq ct = C′.body b′ , S′.reach-bpin fewC′ b′
      where
        nq : ¬ Lie TB.Cut q
        nq (c , cb , li) = proj₁ cl (c , inj₂ (cb , q , pin r₁ , ct , lies-spun li) , li)

        im : Img r₁
        im {j} x jr = inj₁ (alive-β bq x (≺-≼-≺ {j} {r₁} {q} jr (⊑-≼ rq)))

        nb : ∀ {x} → W⁼ H r x → r₁ ⊑ x → ⊥
        nb xw le = bleads (proj₁ (InvAt.pinned Iβ bq)) xw le

        b′ : C′.β q (pin r₁)
        b′ = proj₁ (upto (cF′ (proper-ag (σ-to nb im)) p₀) {q} (≼-refl {q})) (proj₁ (TB.agree q (pin r₁) (cleanBq nq)) bq)

    fromB : C′.β q (pin r₁) → Ct q (pin r₁)
    fromB b′ = C.body bq , S.reach-bpin fewC bq
      where
        nb : ∀ {x} → W⁼ H r x → r₁ ⊑ x → ⊥
        nb xw le = bleads′ (proj₁ (InvAt.pinned Iβ′ b′)) xw le

        b″ : β″ q (pin r₁)
        b″ = proj₂ (upto (cF′ (proper-ag (σ-to nb (img-β′ b′ (⊑-≼ rq) (≼-refl {r₁})))) p₀) {q} (≼-refl {q})) b′

        nq : ¬ Lie TB.Cut q
        nq (c , cb , li) with lie-split li rq
        ... | inj₁ lr = nlB (≼-refl {r₁}) (c , cb , lr)
        ... | inj₂ rc = TB.shadow cb b″ li rc (beforeB (≼-refl {r₁})) (nlB (≼-refl {r₁}))
                          ([] , λ {z} bz sp → ⊥-elim (proj₁ cl (c , inj₂ (cb , z , pin r₁ , (C.body bz , S.reach-bpin fewC bz) , sp) , li)))

        bq : C.β q (pin r₁)
        bq = proj₂ (TB.agree q (pin r₁) (cleanBq nq)) b″

  -- A burst pin: read up to its source row, whose burst rows before it it waits on.
  module PinS {k : Pos} (ik : T (inside r k)) (cl : Clean Cut′ Ct (k ⊕ [ ix 0 ]) (pin p)) where
    cks : List Pos
    cks = proj₁ (proj₂ cl)

    ij : ∀ {j e₀} → C.σ j e₀ → j ≺ k → T (inside r j)
    ij x jk = in-burst (σ-r x) jk (inside-⊑ r k ik)

    hitj : ∀ {j e₀} → C.σ j e₀ → Few C.σ j → j ≺ k → Cov k cks j × ¬ Lie Cut′ (j ⊕ [ ix 0 ])
    hitj {j} x Fj jk =
      let (cv , n) = proj₂ (proj₂ cl) (C.burst x (ij x jk) , S.reach-burst Fj x (ij x jk)) (next≺ {j} {k} jk) (λ _ → inj₂ refl)
      in cov-pre cv jk , n

    Fk : Few C.σ k
    Fk = σ-few (cover k cks) λ {j} x Fj jk → cov-∈ {k} {cks} {j} (proj₁ (hitj x Fj jk))

    -- No source cut lies at or before the source row.
    nlY : ∀ {y} → y ≼ k → ¬ Lie TS.Cut y
    nlY {y} yk (c , cc , i , l) with where? c k
    ... | inj₁ kc = ≺-irrefl {k} (≺-trans {k} {c ⊕ [ ix 0 ]} {k} kc
                      (≺-≼-≺ {c ⊕ [ ix 0 ]} {y} {k} (≺-≼-≺ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} {y} (ticks c i) (⊑-≼ l)) yk))
    ... | inj₂ (inj₁ (zero , ck)) =
      ≺-irrefl {k} (≺-≼-≺ {k} {y} {k} (≺-≼-≺ {k} {c ⊕ [ ix (suc i) ]} {y} (below-next c ck (s≤s z≤n)) (⊑-≼ l)) yk)
    ... | inj₂ (inj₁ (suc m , ck)) =
      let (z₀ , e₀ , cz , xz) = TS.first cc
          zk = first-below cz (m , ck)
          iz = ij xz zk
          ct₀ = C.burst xz iz , S.reach-burst (few-down Fk (≺→≼ {z₀} {k} zk)) xz iz
      in proj₁ cl (c , inj₁ (cc , z₀ ⊕ [ ix 0 ] , pin p , ct₀ , (0 , ⊑-trans cz (⊑-snoc⁺ z₀)) , inj₁ (z₀ , e₀ , xz , (0 , cz) , inj₂ iz))
                   , lies-up (m , ck))
    ... | inj₂ (inj₂ far) = spin-few {s = c} row Fk
      where
        row : ∀ j → Σ Pos λ z → Σ (Ev A) λ e → (c ⊕ [ ix j ]) ⊑ z × C.σ z e × z ≺ k
        row j =
          let (z , e , cz , xz) = TS.shows cc j (few-down Fk (≺→≼ {c ⊕ [ ix (suc j) ]} {k} (far (suc j))))
          in z , e , cz , xz , ≺-trans {z} {c ⊕ [ ix (suc j) ]} {k} (below-next c cz ≤-refl) (far (suc j))

    agσk : AgreeTo k C.σ C′.σ
    agσk = ⟨ (λ {y} {e} yk → TS.agree y e (nlY yk , cks , λ {j} x jy _ → dep x jy yk)) ⟩
      where
        dep : ∀ {j y e} → C.σ j e → j ≺ y → y ≼ k → Cov y cks j × ¬ Lie TS.Cut j
        dep {j} {y} x jy yk =
          cov-down (proj₁ (hitj x (few-down Fk (≺→≼ {j} {k} jk)) jk)) jy yk , nlY (≺→≼ {j} {k} jk)
          where
            jk : j ≺ k
            jk = ≺-≼-≺ {j} {y} {k} jy yk

    toS : ∀ {e₀} → C.σ k e₀ → Ct′ (k ⊕ [ ix 0 ]) (pin p)
    toS x = C′.burst x′ ik , S′.reach-burst (few-ag agσk (≼-refl {k}) Fk) x′ ik
      where x′ = proj₁ (upto agσk {k} (≼-refl {k})) x

    fromS : ∀ {e₀} → C′.σ k e₀ → Ct (k ⊕ [ ix 0 ]) (pin p)
    fromS x′ = C.burst x ik , S.reach-burst Fk x ik
      where x = proj₂ (upto agσk {k} (≼-refl {k})) x′

  -- A kept pin: read up to its connect, and its kept rows before it.
  module PinK {k p′ : Pos} (ik : T (inside p′ k)) (ni : T (not (inside r k))) (cl : Clean Cut′ Ct (k ⊕ [ ix 0 ]) (pin p′)) where
    pk : p′ ⊑ k
    pk = inside-⊑ p′ k ik

    pq : p′ ⊑ (k ⊕ [ ix 0 ])
    pq = ⊑-trans pk (⊑-snoc⁺ k)

    open AtBound {p′} (before-of cl (⊑-≼ pq) (λ kr _ → inj₁ kr)) (λ l → proj₁ cl (lie-up l pq))

    cks : List Pos
    cks = proj₁ (proj₂ cl)

    -- A kept row of the same connect before it: the connect's, waited on.
    hitk : ∀ {j} → C.σ j (pin p′) → C.Alive p′ → j ≺ k → Cov k cks j × ¬ Lie TS.Cut j
    hitk {j} x alp jk =
      let ct = kept-img {j = j} {k = k} x alp ni pk , S.reach-kept fewC x
          (cv , n) = proj₂ (proj₂ cl) ct (next≺ {j} {k} jk) (λ _ → inj₂ refl)
      in cov-pre cv jk , λ { (c , cc , l) → n (c , inj₁ (cc , j ⊕ [ ix 0 ] , pin p′ , ct , lies-spun (lies-up l) , inj₂ (lies-up l)) , lies-up l) }

    cleanKq : C.Alive p′ → ¬ Lie TS.Cut k → Clean TS.Cut C.σ k (pin p′)
    cleanKq alp nk = nk , K ++ cks , dep
      where
        dep : ∀ {j e′} → C.σ j e′ → j ≺ k → Dep k (pin p′) j e′ → Cov k (K ++ cks) j × ¬ Lie TS.Cut j
        dep {j} x jk d with d ik
        ... | inj₁ jp = let (cv , n) = by-σ (img-alive {p′} alp) (≼-refl {p′}) x jp in cov-++ˡ (cov-lift cv pk) , n
        ... | inj₂ refl = let (cv , n) = hitk x alp jk in cov-++ʳ {ks = K} cv , n

    toK : C.σ k (pin p′) → C.Alive p′ → Ct (k ⊕ [ ix 0 ]) (pin p′) → Ct′ (k ⊕ [ ix 0 ]) (pin p′)
    toK x alp ct = C′.kept x′ (alive→ alp (≼-refl {p′})) ni ik , S′.reach-kept fewC′ x′
      where
        nk : ¬ Lie TS.Cut k
        nk (c , cc , li) = proj₁ cl (c , inj₁ (cc , k ⊕ [ ix 0 ] , pin p′ , ct , lies-spun (lies-up li) , inj₂ (lies-up li)) , lies-up li)

        x′ : C′.σ k (pin p′)
        x′ = proj₁ (TS.agree k (pin p′) (cleanKq alp nk)) x

    fromK : C′.σ k (pin p′) → C′.Alive p′ → Ct (k ⊕ [ ix 0 ]) (pin p′)
    fromK x′ alp′ = C.kept x alp ni ik , S.reach-kept fewC x
      where
        alp : C.Alive p′
        alp = alive← alp′ (≼-refl {p′})

        nk : ¬ Lie TS.Cut k
        nk (c , cc , li) with lie-split li pk
        ... | inj₁ lp = nlS (img-alive {p′} alp) (≼-refl {p′}) (c , cc , lp)
        ... | inj₂ pc = TS.shadow cc x′ li pc (beforeS (img-alive {p′} alp) (≼-refl {p′})) (nlS (img-alive {p′} alp) (≼-refl {p′})) ((k ⊕ [ ix 0 ]) ∷ cks , hid)
          where
            hid : ∀ {j} → C.σ j (pin p′) → Spun c j → Any.Any (j ⊑_) ((k ⊕ [ ix 0 ]) ∷ cks) × ¬ Lie TS.Cut j
            hid {j} xj (zero , cj) =
              let jk = ≺-≼-≺ {j} {c ⊕ [ ix 1 ]} {k} (below-next c cj (s≤s z≤n)) (lies-≼ li)
                  ct = kept-img {j = j} {k = k} xj alp ni pk , S.reach-kept fewC xj
                  (cv , n) = proj₂ (proj₂ cl) ct (next≺ {j} {k} jk) (λ _ → inj₂ refl)
              in Any.map (λ {z} h′ → ⊑-trans (⊑-snoc⁺ j) h′) (cov-any cv)
                 , λ { (c′ , cc′ , l) → n (c′ , inj₁ (cc′ , j ⊕ [ ix 0 ] , pin p′ , ct , lies-spun (lies-up l) , inj₂ (lies-up l)) , lies-up l) }
            hid {j} xj (suc i , cj) =
              ⊥-elim (proj₁ cl (c , inj₁ (cc , j ⊕ [ ix 0 ] , pin p′ , (kept-img {j = j} {k = k} xj alp ni pk , S.reach-kept fewC xj)
                                          , spun-up (suc i , cj) , inj₂ (lies-up (i , cj))) , lies-up li))

        x : C.σ k (pin p′)
        x = proj₂ (TS.agree k (pin p′) (cleanKq alp nk)) x′

  pin-to : ∀ {q r₁} → T (inside r₁ q) → Clean Cut′ Ct q (pin r₁) → Ct q (pin r₁) → Ct′ q (pin r₁)
  pin-to ins cl (C.body bq , rw)            = PinB.toB ins cl bq (C.body bq , rw)
  pin-to _   cl (C.burst x ik , _)          = PinS.toS ik cl x
  pin-to _   cl (C.kept x alp ni ik , rw)   = PinK.toK ik ni cl x alp (C.kept x alp ni ik , rw)

  pin-from : ∀ {q r₁} → T (inside r₁ q) → Clean Cut′ Ct q (pin r₁) → Ct′ q (pin r₁) → Ct q (pin r₁)
  pin-from ins cl (C′.body b′ , _)            = PinB.fromB ins cl b′
  pin-from _   cl (C′.burst x′ ik , _)        = PinS.fromS ik cl x′
  pin-from _   cl (C′.kept x′ alp′ ni ik , _) = PinK.fromK ik ni cl x′ alp′

  agree′ : ∀ q e → Clean Cut′ Ct q e → (Ct q e → Ct′ q e) × (Ct′ q e → Ct q e)
  agree′ q (out _) cl = by-all cl (λ _ → tt)
  agree′ q skip    cl = by-all cl (λ _ → tt)
  agree′ q end     cl = by-all cl (λ _ → tt)
  agree′ q (pin r₁) cl with T? (inside r₁ q)
  ... | no ni   = by-all cl (λ _ i → ⊥-elim (ni i))
  ... | yes ins = pin-to ins cl , pin-from ins cl

  ------------------------------------------------------------------------
  -- The next's pin past a cut: the pins under the spin are not hidden

  shadow′ : ∀ {c w r₁} → Cut′ c → Ct′ w (pin r₁) → Lies c w → r₁ ⊑ c → Before Cut′ Ct r₁ → ¬ Lie Cut′ r₁ → ¬ Hidden Cut′ Ct c r₁
  shadow′ (inj₁ cs) (C′.body b′ , _) li rc _ _ _ = bleads′ (proj₁ (InvAt.pinned Iβ′ b′)) (Placed.placed PS (proj₁ cs)) rc
  shadow′ (inj₁ cs) (C′.burst x′ ik , _) li _ _ _ = shadow-burst cs (burst-r (proj₁ cs) (lies-⊑ (lies-img li)) ik)
  shadow′ (inj₁ cs) (C′.kept x′ alp′ ni ik , _) li rc bf nl = AtBound.shadow-kept bf nl cs x′ alp′ ni ik li rc
  shadow′ (inj₂ cbw) (C′.body b′ , _) li rc bf nl = AtBound.shadow-body bf nl cbw b′ li rc
  shadow′ (inj₂ (cb , _)) (C′.burst x′ _ , _) li _ _ _ _  = b-img cb (sw′ x′) (lies-spun li)
  shadow′ (inj₂ (cb , _)) (C′.kept x′ _ _ _ , _) li _ _ _ _ = b-img cb (sw′ x′) (lies-spun li)

  truth : Truth Ct Ct′
  truth = record
    { Cut    = Cut′
    ; silent = silent′
    ; first  = first′
    ; shows  = shows′
    ; again  = again′
    ; shadow = shadow′
    ; agree  = agree′
    }

  placed : Placed H p Ct Ct′
  placed = placing truth pl
    where
      pl : ∀ {c} → Cut′ c → W⁼ H p c
      pl (inj₁ (cc , _)) = inW (shrink⁼ (Placed.placed PS cc))
      pl (inj₂ (cb , _)) = inW (narrow⁼ (LC.σ-wp {s = s} {F = F} Is IF p ok) (Placed.placed PB cb))

connect-truth : ∀ {A B H} {s s′ : Den A} {F F′ : Den A → Den B}
              → InvD H s → InvD H s′
              → (∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) → (∀ {t} → Lawful t → InvD (H ∪ʰ t) (F′ (hot t)))
              → Causal F′ → Hushes H F
              → (∀ m q → Ok H q → ShowsK m (enter s q))
              → (∀ m {t} → Lawful t → ∀ q → Ok (H ∪ʰ t) q → ShowsK m (enter (F (hot t)) q))
              → Rel H s s′ → (∀ {t} → Lawful t → Rel (H ∪ʰ t) (F (hot t)) (F′ (hot t)))
              → Rel H (Op.connect s F) (Op.connect s′ F′)
connect-truth {s = s} {s′} {F} {F′} Is Is′ IF IF′ cF′ hF sk-s sk-b R RF p ok =
  Bound.placed {s = s} {s′} {F} {F′} Is Is′ IF IF′ cF′ hF sk-s sk-b R RF p ok
