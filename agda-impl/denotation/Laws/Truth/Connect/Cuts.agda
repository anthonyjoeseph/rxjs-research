{-# OPTIONS --guardedness #-}

-- A CONNECT'S CUTS AND SPIN ROWS, over a source and a body each read
-- against the next.  The connect's cuts are its source's cuts it shows a
-- reached row under the spin of, and its body's.  Under a body cut its
-- rows are the body's.  Under a source cut they are source rows one label
-- down, and body rows a source spin row leads: those the handle shows
-- silent, so the body keeps them silent (`Hushes`).  Causality is not
-- enough: a body showing a skip as a value is causal, yet spins loud
-- under its source's cut.
--
-- A source cut's spin row shows wherever the source rows before it are
-- shown: all are, once one under the spin is alive or in the burst
-- (`Shown`); otherwise the cut is shown past its first by a pin whose
-- connect leads it, which recurs (`KeptW`).  A cover of the rows shown
-- before a cut sees every row before it only where hangs show (`Shows`),
-- so the source and body are read as showing theirs, as every
-- approximant does (`sk-approx`).
module denotation.Laws.Truth.Connect.Cuts where


open import Data.Bool using (T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; [_]; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; ix; sub; _⊕_; inside)
open import denotation.Events using (<ᵖ-step; <ᵖ-shift; <ᵖ-next)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; hot; enter; Few; Dep; Reach; Truncate; Proper;
  Silent; hush; held; _≺_; _≼_; module Connect)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺-trans; ≺→≼; ≼-false; ≼-trans; ≼-or-≻; ≼-split; ≺-≼-≺; ≼-≺-≺; ≺-irrefl;
  ≺-ext; ticks; reach-few; entered-reach)
open import denotation.Laws.Count using (Cov; cov-up; cov-down)
open import denotation.Laws.Shows using (ShowsK; k-shows; cover; cov-∈; cov-few; lead-∈; few-down; few-reach; ∈-stable)
open import denotation.Laws.Worlds using (W⁼; inW; Ok; Lawful; InvAt; InvD; Shows; _∪ʰ_; ok-step; _⊑_; ⊑-refl; ⊑-trans; ⊑-snoc;
  ⊑-snoc⁺; ⊑-cmp; ⊑-≼; ⊑-inside; inside-⊑; conv; plain-ix; world-after; ⊕-injˡ; ⊕-injʳ; not-up; sib; shrink⁼; narrow⁼;
  flat-under; same-lead)
  renaming (step to wstep)
import denotation.Laws.Connect as LC
open import denotation.Laws.ConnectNe using (Causal; module Rows)
open import denotation.Laws.Hush using (Hushes; Quiet)
import denotation.Laws.ShowsOps as SO
open import denotation.Laws.Truth using (Truth; Rel; Placed; Spun; Lies; Pins; pins-via; below-next; lies-≼)
open import denotation.Laws.Truth.Joining using (reach-pin; under-c; lies-⊑; lies-spun; lie-split)

------------------------------------------------------------------------
-- A source row and its first child

-- Past a row, its first child is no later than what lies past it.
step≼ : ∀ {k y} → k ≺ y → (k ⊕ [ ix 0 ]) ≼ y
step≼ {k} {y} ky yk = subst T (<ᵖ-step k y (Equivalence.to T-≡ ky)) yk

next≺ : ∀ {j z} → j ≺ z → (j ⊕ [ ix 0 ]) ≺ (z ⊕ [ ix 0 ])
next≺ {j} {z} h = Equivalence.from T-≡ (<ᵖ-next j z (ix 0) (Equivalence.to T-≡ h))

img-≺ : ∀ j z → (j ⊕ [ ix 0 ]) ≺ (z ⊕ [ ix 0 ]) → j ≺ z
img-≺ j z h with ≼-or-≻ z j
... | inj₂ jz = jz
... | inj₁ zj = ⊥-elim (subst T (<ᵖ-shift j z (≼-false {z} {j} zj)) h)

-- Before a spin row past the first, a row's first child is too.
step≺ : ∀ c {i k} → k ≺ (c ⊕ [ ix (suc i) ]) → (k ⊕ [ ix 0 ]) ≺ (c ⊕ [ ix (suc i) ])
step≺ c {i} {k} h with ≼-split {k ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} (step≼ {k} {c ⊕ [ ix (suc i) ]} h)
... | inj₁ lt = lt
... | inj₂ eq with ⊕-injʳ k c eq
...   | ()

first-below : ∀ {c z y} → (c ⊕ [ ix 0 ]) ⊑ z → Lies c y → z ≺ y
first-below {c} {z} {y} cz (i , l) = ≺-≼-≺ {z} {c ⊕ [ ix (suc i) ]} {y} (below-next c cz (s≤s z≤n)) (⊑-≼ l)

lies-img : ∀ {c k} → Lies c (k ⊕ [ ix 0 ]) → Lies c k
lies-img {c} {k} (i , l) with ⊑-snoc k l
... | inj₁ ck = i , ck
... | inj₂ eq with ⊕-injʳ c k eq
...   | ()

lies-up : ∀ {c k l} → Lies c k → Lies c (k ⊕ [ l ])
lies-up {k = k} (i , ck) = i , ⊑-trans ck (⊑-snoc⁺ k)

spun-up : ∀ {c k l} → Spun c k → Spun c (k ⊕ [ l ])
spun-up {k = k} (i , ck) = i , ⊑-trans ck (⊑-snoc⁺ k)

spun-⊑ : ∀ {c k} → Spun c k → c ⊑ k
spun-⊑ {c} (i , ck) = ⊑-trans (⊑-snoc⁺ c) ck

spun-≼ : ∀ {c y} → Spun c y → (c ⊕ [ ix 0 ]) ≼ y
spun-≼ (zero , l) = ⊑-≼ l
spun-≼ {c} {y} (suc i , l) =
  ≼-trans {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} {y} (≺→≼ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc i) ]} (ticks c i)) (⊑-≼ l)

spun-img : ∀ {c k} → Spun c (k ⊕ [ ix 0 ]) → c ⊑ k
spun-img {c} {k} (i , l) with ⊑-snoc k l
... | inj₁ ck = ⊑-trans (⊑-snoc⁺ c) ck
... | inj₂ eq = subst (c ⊑_) (⊕-injˡ c k eq) (⊑-refl c)

-- A row before a source row's first child, at or past it: before the row.
pre≼ : ∀ {k b} → (k ⊕ [ ix 0 ]) ≼ b → k ≼ b
pre≼ {k} {b} kb = ≼-trans {k} {k ⊕ [ ix 0 ]} {b} (≺→≼ {k} {k ⊕ [ ix 0 ]} (≺-ext k [])) kb

-- A pin waits on less, earlier.
reach-sub : ∀ {X} {t : EmissionSet X} {Y y r} → Reach t Y (pin r) → y ≺ Y → T (inside r y) → Reach t y (pin r)
reach-sub {Y = Y} {y} (ks , h) yY iy = ks , λ {k} x ky d → h x (≺-trans {k} {y} {Y} ky yY) (λ _ → d iy)

-- An agreement extends over a stretch where neither side has a row.
extend : ∀ {X} {t t′ : EmissionSet X} {b w} → AgreeTo b t t′ → (∀ {k e} → t k e → b ≺ k → k ≼ w → ⊥)
       → (∀ {k e} → t′ k e → b ≺ k → k ≼ w → ⊥) → AgreeTo w t t′
extend {t = t} {t′} {b} {w} ag n n′ = ⟨ (λ {y} {e} yw → go yw (≼-or-≻ y b)) ⟩
  where
    go : ∀ {y e} → y ≼ w → y ≼ b ⊎ b ≺ y → (t y e → t′ y e) × (t′ y e → t y e)
    go {y} yw (inj₁ yb) = upto ag {y} yb
    go yw (inj₂ by)     = (λ x → ⊥-elim (n x by yw)) , (λ x → ⊥-elim (n′ x by yw))

sib-row : ∀ k {a b} → (a ≡ b → ⊥) → (k ⊕ [ a ]) ⊑ (k ⊕ [ b ]) → ⊥
sib-row k {a} ne le with ⊑-snoc k le
... | inj₁ l  = ⊑-≼ l (≺-ext k {a} [])
... | inj₂ eq = ne (⊕-injʳ k k eq)

-- Two children of one row lead nothing in common.
fork : ∀ k {a b z} → (a ≡ b → ⊥) → (k ⊕ [ a ]) ⊑ z → (k ⊕ [ b ]) ⊑ z → ⊥
fork k ne az bz with ⊑-cmp _ _ az bz
... | inj₁ ab = sib-row k ne ab
... | inj₂ ba = sib-row k (λ e → ne (sym e)) ba

-- A row at or under `k`, with few before the bound: `k` covered.
cov-img : ∀ {X} {t : EmissionSet X} {b k y e} (F : Few t b) → k ≺ b → t y e → k ⊑ y → Cov b (proj₁ F) k
cov-img {b = b} {k} {y} F kb ty ky with ≼-or-≻ b y
... | inj₂ yb = inj₂ (lead-∈ ky (proj₂ F ty yb))
... | inj₁ by with ≼-split {b} {y} by
...   | inj₁ b≺y = inj₁ (conv {k} {k} {b} {y} (⊑-refl k) (≺→≼ {k} {b} kb) b≺y ky)
...   | inj₂ refl = inj₁ ky

-- Covered under a row's first child: covered under the row.
cov-pre : ∀ {k ks j} → Cov (k ⊕ [ ix 0 ]) ks (j ⊕ [ ix 0 ]) → j ≺ k → Cov k ks j
cov-pre {k} {j = j} c jk = cov-down (cov-up (⊑-snoc⁺ j) c) jk (≺→≼ {k} {k ⊕ [ ix 0 ]} (≺-ext k []))

-- Pins whose first children are members: covered.
pins-of : ∀ {X} {t : EmissionSet X} {p′ v} {ks : List Pos} → (∀ {j} → t j (pin p′) → j ≺ v → (j ⊕ [ ix 0 ]) ∈ ks) → Pins t p′ v
pins-of {v = v} {ks} m = cover v ks , λ {j} xj jv → cov-∈ {v} {ks} {j} (inj₂ (lead-∈ (⊑-snoc⁺ j) (m xj jv)))

end-loud : ∀ {X : Set} → Silent {X} end → ⊥
end-loud ()

------------------------------------------------------------------------
-- Either side's connect: where its pins wait

module Side {A B : Set} {H : Pos → Set} {s : Den A} {F : Den A → Den B}
            (Is : InvD H s) (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) (p : Pos) (ok : Ok H p) where
  private
    module C = Connect s F p

    Iσ = LC.Iσ {s = s} {F = F} Is IF p ok
    Iβ = LC.Iβ {s = s} {F = F} Is IF p ok

  open Rows {s = s} {F = F} Is IF p ok using (sw)

  -- Nothing in a child's world leads the subscription.
  no-p : ∀ {H′ i} → W⁼ H′ (p ⊕ [ ix i ]) p → ⊥
  no-p w = not-up (proj₁ ok) w (⊑-refl p)

  σ-past : ∀ {k e} → C.σ k e → p ≺ k
  σ-past {k} x = ≺-trans {p} {C.r} {k} (≺-ext p []) (world-after (InvAt.world Iσ x) (InvAt.real Iσ x))

  after-p : ∀ {k e} → C.ConnT k e → p ≺ k
  after-p (C.body b)               = LC.p-before {s = s} {F = F} Is IF p ok b
  after-p (C.burst {k} x _)        = ≺-trans {p} {k} {k ⊕ [ ix 0 ]} (σ-past x) (≺-ext k [])
  after-p (C.echo {k} x _ _ _)     = ≺-trans {p} {k} {k ⊕ [ ix 0 ]} (σ-past x) (≺-ext k [])
  after-p (C.kept {k} x _ _ _)     = ≺-trans {p} {k} {k ⊕ [ ix 0 ]} (σ-past x) (≺-ext k [])

  ins-C : ∀ {y r′} → C.ConnT y (pin r′) → T (inside r′ y)
  ins-C (C.body b)                 = proj₂ (InvAt.pinned Iβ b)
  ins-C (C.burst {k} _ i)          = ⊑-inside (⊑-trans (LC.pinned-under {s = s} {F = F} Is IF p ok i) (⊑-snoc⁺ k))
  ins-C (C.kept {k} {p′} _ _ _ ik) = ⊑-inside (⊑-trans (inside-⊑ p′ k ik) (⊑-snoc⁺ k))

  -- A pin of the connect itself: a burst row.
  burst-src : ∀ {k} → C.ConnT k (pin p) → Σ Pos λ j → Σ (Ev A) λ e₀ → k ≡ j ⊕ [ ix 0 ] × C.σ j e₀
  burst-src (C.body b)              = ⊥-elim (no-p (proj₁ (InvAt.pinned Iβ b)))
  burst-src (C.burst {j} {e₀} x _)  = j , e₀ , refl , x
  burst-src (C.kept x _ _ _)        = ⊥-elim (no-p (proj₁ (InvAt.pinned Iσ x)))

  -- A pin of a source connect: a kept row.
  kept-src : ∀ {k p′} → W⁼ H C.r p′ → C.ConnT k (pin p′) → Σ Pos λ j → k ≡ j ⊕ [ ix 0 ] × C.σ j (pin p′)
  kept-src w (C.body b)          = ⊥-elim (LC.body-leads {s = s} {F = F} Is IF p ok (proj₁ (InvAt.pinned Iβ b)) w (⊑-refl _))
  kept-src w (C.burst _ _)       = ⊥-elim (no-p w)
  kept-src w (C.kept {j} x _ _ _) = j , refl , x

  -- A pin of a body connect: a body row.
  body-src : ∀ {k r′} → W⁼ (H ∪ʰ Proper C.σ) (p ⊕ [ ix 0 ]) r′ → C.ConnT k (pin r′) → C.β k (pin r′)
  body-src w (C.body b)       = b
  body-src w (C.burst _ _)    = ⊥-elim (no-p w)
  body-src w (C.kept x _ _ _) = ⊥-elim (LC.body-leads {s = s} {F = F} Is IF p ok w (proj₁ (InvAt.pinned Iσ x)) (⊑-refl _))

  -- A burst pin waits on the burst rows before it.
  reach-burst : ∀ {j e₀} → Few C.σ j → C.σ j e₀ → T (inside C.r j) → Reach C.ConnT (j ⊕ [ ix 0 ]) (pin p)
  reach-burst {j} (ks , h) x i = map (_⊕ [ ix 0 ]) ks , go
    where
      go : ∀ {k e′} → C.ConnT k e′ → k ≺ (j ⊕ [ ix 0 ]) → Dep (j ⊕ [ ix 0 ]) (pin p) k e′ → k ∈ map (_⊕ [ ix 0 ]) ks
      go {k} y kj d with d (ins-C (C.burst x i))
      ... | inj₁ kp   = ⊥-elim (≺-irrefl {k} (≺-trans {k} {p} {k} kp (after-p y)))
      ... | inj₂ refl with burst-src y
      ...   | j′ , _ , refl , x′ = ∈-map⁺ (_⊕ [ ix 0 ]) (h x′ (img-≺ j′ j kj))

  -- A kept pin waits on rows before its connect and the kept rows of it.
  reach-kept : ∀ {j p′} → Few C.ConnT p′ → C.σ j (pin p′) → Reach C.ConnT (j ⊕ [ ix 0 ]) (pin p′)
  reach-kept {j} {p′} (ks , h) x with entered-reach s C.r x
  ... | ks′ , h′ = ks ++ map (_⊕ [ ix 0 ]) ks′ , go
    where
      go : ∀ {k e′} → C.ConnT k e′ → k ≺ (j ⊕ [ ix 0 ]) → Dep (j ⊕ [ ix 0 ]) (pin p′) k e′ → k ∈ ks ++ map (_⊕ [ ix 0 ]) ks′
      go y kj d with d (⊑-inside (⊑-trans (inside-⊑ p′ j (proj₂ (InvAt.pinned Iσ x))) (⊑-snoc⁺ j)))
      ... | inj₁ kp   = ∈-++⁺ˡ (h y kp)
      ... | inj₂ refl with kept-src (proj₁ (InvAt.pinned Iσ x)) y
      ...   | j′ , refl , x′ = ∈-++⁺ʳ ks (∈-map⁺ (_⊕ [ ix 0 ]) (h′ x′ (img-≺ j′ j kj) (λ _ → inj₂ refl)))

  -- A body pin waits on rows before its connect and the body's pins of it.
  reach-bpin : ∀ {z r′} → Few C.ConnT r′ → C.β z (pin r′) → Reach C.ConnT z (pin r′)
  reach-bpin {z} {r′} (ks , h) b with entered-reach (F (hot (Proper C.σ))) (p ⊕ [ ix 0 ]) b
  ... | ks′ , h′ = ks ++ ks′ , go
    where
      go : ∀ {k e′} → C.ConnT k e′ → k ≺ z → Dep z (pin r′) k e′ → k ∈ ks ++ ks′
      go y kz d with d (proj₂ (InvAt.pinned Iβ b))
      ... | inj₁ kr   = ∈-++⁺ˡ (h y kr)
      ... | inj₂ refl = ∈-++⁺ʳ ks (h′ (body-src (proj₁ (InvAt.pinned Iβ b)) y) kz (λ _ → inj₂ refl))

  -- A source row's first child leads no body row.
  img-body : ∀ {k e′ z e} → C.σ k e′ → C.β z e → (k ⊕ [ ix 0 ]) ⊑ z → ⊥
  img-body {k} x b kz with LC.source-leads {s = s} {F = F} Is IF p ok (sw x) (inW (InvAt.world Iβ b)) (⊑-trans (⊑-snoc⁺ k) kz)
  ... | h , _ , (_ , σh) , kh , hz with same-lead Iσ x (proj₁ σh) kh
  ...   | refl = fork k (λ ()) kz hz

------------------------------------------------------------------------
-- The connect, against the next

module Core {A B : Set} {H : Pos → Set} {s s′ : Den A} {F F′ : Den A → Den B}
            (Is : InvD H s) (Is′ : InvD H s′)
            (IF : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F (hot t))) (IF′ : ∀ {t} → Lawful t → InvD (H ∪ʰ t) (F′ (hot t)))
            (cF′ : Causal F′) (hF : Hushes H F)
            (sk-s : ∀ m q → Ok H q → ShowsK m (enter s q))
            (sk-b : ∀ m {t} → Lawful t → ∀ q → Ok (H ∪ʰ t) q → ShowsK m (enter (F (hot t)) q))
            (R : Rel H s s′) (RF : ∀ {t} → Lawful t → Rel (H ∪ʰ t) (F (hot t)) (F′ (hot t)))
            (p : Pos) (ok : Ok H p) where
  module C  = Connect s F p
  module C′ = Connect s′ F′ p
  module S  = Side {s = s} {F = F} Is IF p ok
  module S′ = Side {s = s′} {F = F′} Is′ IF′ p ok
  open Rows {s = s} {F = F} Is IF p ok using (sw; alive-β; img; not-in)
  module R′ = Rows {s = s′} {F = F′} Is′ IF′ p ok

  p₀ r : Pos
  p₀ = p ⊕ [ ix 0 ]
  r  = p ⊕ [ ix 1 ]

  Iσ  = LC.Iσ {s = s} {F = F} Is IF p ok
  Iβ  = LC.Iβ {s = s} {F = F} Is IF p ok
  Iβ′ = LC.Iβ {s = s′} {F = F′} Is′ IF′ p ok
  okr = ok-step p ok
  Lσ  = LC.lawful {s = s} {F = F} Is IF p ok
  ok₀ = LC.ok₀ {s = s} {F = F} Is IF p ok

  bleads : ∀ {w x} → W⁼ (H ∪ʰ Proper C.σ) p₀ w → W⁼ H r x → w ⊑ x → ⊥
  bleads = LC.body-leads {s = s} {F = F} Is IF p ok

  bleads′ : ∀ {w x} → W⁼ (H ∪ʰ Proper C′.σ) p₀ w → W⁼ H r x → w ⊑ x → ⊥
  bleads′ = LC.body-leads {s = s′} {F = F′} Is′ IF′ p ok

  Ct Ct′ : EmissionSet B
  Ct  = Truncate C.ConnT
  Ct′ = Truncate C′.ConnT

  PS = R r okr
  module TS = Truth (Placed.tr PS)

  -- The body under this handle, as the next reads it.
  β″ : EmissionSet B
  β″ = enter (F′ (hot (Proper C.σ))) p₀

  PB = RF Lσ p₀ ok₀
  module TB = Truth (Placed.tr PB)

  shS : Shows C.σ
  shS = k-shows (λ m → sk-s m r okr)

  shC : Shows C.ConnT
  shC = k-shows (λ m → SO.Conn.sk-connT {n = m} s F Is p ok (sk-s m r okr) (sk-b m Lσ p₀ ok₀))

  ------------------------------------------------------------------------
  -- Geometry

  σ-r : ∀ {j e} → C.σ j e → r ≺ j
  σ-r x = world-after (InvAt.world Iσ x) (InvAt.real Iσ x)

  sw′ : ∀ {y e} → C′.σ y e → W⁼ H r y
  sw′ = R′.sw

  -- Under the burst, a source row before a position in it is in it.
  in-burst : ∀ {j y} → r ≺ j → j ≺ y → r ⊑ y → T (inside r j)
  in-burst {j} {y} rj jy ry = ⊑-inside (conv {r} {r} {j} {y} (⊑-refl r) (≺→≼ {r} {j} rj) jy ry)

  -- The handle: no hot row leads a row of it, and nothing of it leads the body's subscription.
  ap : ∀ {h e q} → Proper C.σ h e → H q → ¬ h ⊑ q
  ap y hq le = proj₂ okr hq (InvAt.world Iσ (proj₁ y)) (⊑-inside le)

  fr₀ : ∀ {h} → Quiet (Proper C.σ) h → ¬ h ⊑ p₀
  fr₀ (_ , (y , _) , _) = sib (proj₁ ok) plain-ix (⊑-refl p) ne01 (sw y)
    where
      ne01 : p ⊕ [ ix 0 ] ≡ p ⊕ [ ix 1 ] → ⊥
      ne01 e with ⊕-injʳ p p e
      ... | ()

  hushed : ∀ {y e h} → C.β y e → Quiet (Proper C.σ) h → h ⊑ y → Silent e
  hushed = hF Lσ ap p₀ ok₀ fr₀

  -- No source row at a source cut.
  s-at : ∀ {c e} → TS.Cut c → C.σ c e → ⊥
  s-at cc x with TS.first cc
  ... | _ , _ , cz , xz = flat-under Iσ x xz cz

  -- Under a source cut's spin, a body row is led by a source row there.
  body-under : ∀ {c y e} → TS.Cut c → Spun c y → C.β y e → Σ Pos λ h → Σ (Ev A) (Proper C.σ h) × Spun c h × h ⊑ y × h ≺ y
  body-under {c} {y} cc (i , cy) b
    with LC.source-leads {s = s} {F = F} Is IF p ok (inW (wstep (Placed.placed PS cc) plain-ix)) (inW (InvAt.world Iβ b)) cy
  ... | h , g , xh , ch , hy = h , xh , (i , ch) , ⊑-trans (⊑-snoc⁺ h) hy , ≺-≼-≺ {h} {h ⊕ [ sub g ]} {y} (≺-ext h []) (⊑-≼ hy)

  body-silent : ∀ {c y e} → TS.Cut c → Spun c y → C.β y e → Silent e
  body-silent cc sp b with body-under cc sp b
  ... | _ , (_ , xh) , sph , hy , _ = hushed b (_ , xh , TS.silent cc sph (proj₁ xh)) hy

  no-end : ∀ {c y} → TS.Cut c → Spun c y → C.β y end → ⊥
  no-end cc sp b = end-loud (body-silent cc sp b)

  -- A source cut in the burst lies under it.
  burst-r : ∀ {c k} → TS.Cut c → c ⊑ k → T (inside r k) → r ⊑ c
  burst-r {c} {k} cc ck i with ⊑-cmp r c (inside-⊑ r k i) ck
  ... | inj₁ rc = rc
  ... | inj₂ cr with ⊑-snoc p cr
  ...   | inj₁ cp   = ⊥-elim (not-up (proj₁ ok) (Placed.placed PS cc) cp)
  ...   | inj₂ refl = ⊑-refl r

  -- Past a source row alive under a source cut's spin, before a spin row: alive.
  alive-to : ∀ {c k j m} → TS.Cut c → Spun c k → C.Alive k → j ≺ (c ⊕ [ ix m ]) → C.Alive j
  alive-to {c} {k} {j} {m} cc (_ , ck) al jv {ce} b with ≼-or-≻ ce j
  ... | inj₂ jce = jce
  ... | inj₁ cej =
    ⊥-elim (at (under-c c (conv {c} {k} {ce} {c ⊕ [ ix m ]} (⊑-trans (⊑-snoc⁺ c) ck) (≺→≼ {k} {ce} (al b))
                                (≼-≺-≺ {ce} {j} {c ⊕ [ ix m ]} cej jv) (⊑-snoc⁺ c))))
    where
      at : ce ≡ c ⊎ Spun c ce ⊎ (∀ i → (c ⊕ [ ix i ]) ≺ ce) → ⊥
      at (inj₁ eq)         = bleads (subst (W⁼ (H ∪ʰ Proper C.σ) p₀) eq (inW (InvAt.world Iβ b))) (Placed.placed PS cc) (⊑-refl c)
      at (inj₂ (inj₁ sp))  = no-end cc sp b
      at (inj₂ (inj₂ far)) = ≺-irrefl {ce} (≼-≺-≺ {ce} {j} {ce} cej (≺-trans {j} {c ⊕ [ ix m ]} {ce} jv (far m)))

  -- A source row under a source cut's spin, alive or in the burst: every
  -- source row before a spin row is shown.
  Shown : Pos → Set
  Shown c = Σ Pos λ k → Σ (Ev A) λ e₀ → C.σ k e₀ × Spun c k × (C.Alive k ⊎ T (inside r k))

  shown-ab : ∀ {c j e m} → TS.Cut c → Shown c → C.σ j e → j ≺ (c ⊕ [ ix m ]) → C.Alive j ⊎ T (inside r j)
  shown-ab {j = j} {m = m} cc (_ , _ , _ , sp , inj₁ al) xj jv = inj₁ (alive-to {j = j} {m = m} cc sp al jv)
  shown-ab {c} cc (_ , _ , _ , (_ , ck) , inj₂ i) xj jv =
    inj₂ (in-burst (σ-r xj) jv (⊑-trans (burst-r cc (⊑-trans (⊑-snoc⁺ c) ck) i) (⊑-snoc⁺ c)))

  -- A kept pin past a source cut's first, its live connect leading the cut.
  KeptW : Pos → Set
  KeptW c = Σ Pos λ k → Σ Pos λ p′ → C.σ k (pin p′) × Lies c k × p′ ⊑ c × C.Alive p′ × T (not (inside r k))

  kept-img : ∀ {j k p′} → C.σ j (pin p′) → C.Alive p′ → T (not (inside r k)) → p′ ⊑ k → C.ConnT (j ⊕ [ ix 0 ]) (pin p′)
  kept-img xj alp ni pk = C.kept xj alp (not-in xj pk ni) (proj₂ (InvAt.pinned Iσ xj))

  -- No source row's first child under a body cut's spin.
  b-img : ∀ {c k} → TB.Cut c → W⁼ H r k → Spun c (k ⊕ [ ix 0 ]) → ⊥
  b-img {c} {k} cb kw (i , l) with ⊑-snoc k l
  ... | inj₁ ck = bleads (inW (wstep (Placed.placed PB cb) plain-ix)) kw ck
  ... | inj₂ eq = bleads (Placed.placed PB cb) kw (subst (c ⊑_) (⊕-injˡ c k eq) (⊑-refl c))

  body-in : ∀ {c k e′} → TB.Cut c → C.ConnT k e′ → Spun c k → C.β k e′
  body-in cb (C.body b) _          = b
  body-in cb (C.burst x _) sp      = ⊥-elim (b-img cb (sw x) sp)
  body-in cb (C.echo x _ _ _) sp   = ⊥-elim (b-img cb (sw x) sp)
  body-in cb (C.kept x _ _ _) sp   = ⊥-elim (b-img cb (sw x) sp)

  -- No connect row leads a body row from above its children.
  row-over : ∀ {y e′ z e l} → C.β z e → C.ConnT y e′ → (y ⊕ [ l ]) ⊑ z → ⊥
  row-over bz (C.body b) l              = flat-under Iβ b bz l
  row-over bz (C.burst {j} x _) l       = S.img-body x bz (⊑-trans (⊑-snoc⁺ (j ⊕ [ ix 0 ])) l)
  row-over bz (C.echo {j} x _ _ _) l    = S.img-body x bz (⊑-trans (⊑-snoc⁺ (j ⊕ [ ix 0 ])) l)
  row-over bz (C.kept {j} x _ _ _) l    = S.img-body x bz (⊑-trans (⊑-snoc⁺ (j ⊕ [ ix 0 ])) l)

  ------------------------------------------------------------------------
  -- The cuts

  -- A source cut the connect shows a reached row under the spin of: past
  -- the first, or at it with the spin's source rows shown.
  CutS : Pos → Set
  CutS c = TS.Cut c × Σ Pos λ y → Σ (Ev B) λ e → Ct y e × Spun c y × (Shown c ⊎ Lies c y)

  CutB : Pos → Set
  CutB c = TB.Cut c × Σ Pos λ y → Σ (Ev B) λ e → Ct y e × Spun c y

  Cut′ : Pos → Set
  Cut′ c = CutS c ⊎ CutB c

  by-lies : ∀ {c y e} → TS.Cut c → C.ConnT y e → Lies c y → Shown c ⊎ KeptW c
  by-lies cc (C.body b) li with body-under cc (lies-spun li) b
  ... | h , (e₁ , xh) , sph , _ , hy = inj₁ (h , e₁ , proj₁ xh , sph , inj₁ (alive-β b (proj₁ xh) hy))
  by-lies cc (C.burst x i) li       = inj₁ (_ , _ , x , lies-spun (lies-img li) , inj₂ i)
  by-lies cc (C.echo x al _ _) li   = inj₁ (_ , _ , x , lies-spun (lies-img li) , inj₁ al)
  by-lies cc (C.kept {k} {p′} x alp ni ik) li with lie-split (lies-img li) (inside-⊑ p′ k ik)
  ... | inj₂ pc = inj₂ (k , p′ , x , lies-img li , pc , alp , ni)
  ... | inj₁ lp with TS.first cc
  ...   | z₀ , e₀ , cz , xz = inj₁ (z₀ , e₀ , xz , (0 , cz) , inj₁ λ {ce} b → ≺-trans {z₀} {p′} {ce} (first-below cz lp) (alp b))

  mode : ∀ {c} → CutS c → Shown c ⊎ KeptW c
  mode (_ , _ , _ , _ , _ , inj₁ sh)          = inj₁ sh
  mode (cc , _ , _ , (cy , _) , _ , inj₂ li) = by-lies cc cy li

  silent′ : ∀ {c y e} → Cut′ c → Spun c y → Ct y e → Silent e
  silent′ (inj₁ (cc , _)) sp (C.body b , _) = body-silent cc sp b
  silent′ (inj₂ (cb , _)) sp (C.body b , _) = TB.silent cb sp b
  silent′ _ _ (C.burst _ _ , _)             = held
  silent′ _ _ (C.echo _ _ _ _ , _)          = hush
  silent′ _ _ (C.kept _ _ _ _ , _)          = held

  ------------------------------------------------------------------------
  -- The first spin row

  -- A source cut's first row, shown before a row with few before.
  via-first : ∀ {c v} → TS.Cut c → Few C.ConnT v
            → (∀ {z e₀} → (c ⊕ [ ix 0 ]) ⊑ z → C.σ z e₀ → z ≺ v × (C.Alive z ⊎ T (inside r z)))
            → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix 0 ]) ⊑ z × Ct z e
  via-first {c} {v} cc Fv h with TS.first cc
  ... | z₀ , _ , cz , xz with h cz xz
  ...   | zv , a with img xz a
  ...     | e′ , ct = z₀ ⊕ [ ix 0 ] , e′ , ⊑-trans cz (⊑-snoc⁺ z₀) , ct , few-reach (few-down Fv (step≼ {z₀} {v} zv))

  -- Under a body cut's spin the connect's rows are the body's: a body
  -- spin row past few rows before the cut is reached.
  spreadB : ∀ {c b i} → TB.Cut c → c ⊑ b → Few C.ConnT b → (Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × C.β z e)
          → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × Ct z e
  spreadB {c} {b} {i} cb cbb (ks , h) (z , e , cz , bz) with entered-reach (F (hot (Proper C.σ))) p₀ bz
  ... | ks′ , h′ = z , e , cz , C.body bz , (ks ++ ks′ , go)
    where
      go : ∀ {k e′} → C.ConnT k e′ → k ≺ z → Dep z e k e′ → k ∈ ks ++ ks′
      go {k} y kz d with ≼-or-≻ b k
      ... | inj₂ kb = ∈-++⁺ˡ (h y kb)
      ... | inj₁ bk with under-c c (conv {c} {b} {k} {z} cbb bk kz (⊑-trans (⊑-snoc⁺ c) cz))
      ...   | inj₁ refl = ⊥-elim (row-over bz y cz)
      ...   | inj₂ (inj₂ far) =
        ⊥-elim (≺-irrefl {k} (≺-trans {k} {z} {k} kz (≺-trans {z} {c ⊕ [ ix (suc i) ]} {k} (below-next c cz ≤-refl) (far (suc i)))))
      ...   | inj₂ (inj₁ sp) = ∈-++⁺ʳ ks (h′ (body-in cb y sp) kz d)

  firstS : ∀ {c y e} → TS.Cut c → C.ConnT y e → Reach C.ConnT y e → Lies c y → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix 0 ]) ⊑ z × Ct z e
  firstS {e = out a} cc (C.body b) ry li =
    via-first cc (reach-few {e = out a} (λ {_} {_} → tt) ry) (λ cz xz → first-below cz li , inj₁ (alive-β b xz (first-below cz li)))
  firstS {e = skip} cc (C.body b) ry li =
    via-first cc (reach-few {e = skip} (λ {_} {_} → tt) ry) (λ cz xz → first-below cz li , inj₁ (alive-β b xz (first-below cz li)))
  firstS {e = end} cc (C.body b) ry li =
    via-first cc (reach-few {e = end} (λ {_} {_} → tt) ry) (λ cz xz → first-below cz li , inj₁ (alive-β b xz (first-below cz li)))
  firstS {y = y} {pin r″} cc (C.body b) ry li with lie-split li (inside-⊑ r″ y (proj₂ (InvAt.pinned Iβ b)))
  ... | inj₂ rc = ⊥-elim (bleads (proj₁ (InvAt.pinned Iβ b)) (Placed.placed PS cc) rc)
  ... | inj₁ lr = via-first cc (reach-pin (proj₂ (InvAt.pinned Iβ b)) ry)
                    (λ {z} cz xz → first-below cz lr
                                 , inj₁ (alive-β b xz (≺-≼-≺ {z} {r″} {y} (first-below cz lr) (⊑-≼ (inside-⊑ r″ y (proj₂ (InvAt.pinned Iβ b)))))))
  firstS {c} cc (C.burst {k} x i) ry li with TS.first cc
  ... | z₀ , _ , cz , xz =
    z₀ ⊕ [ ix 0 ] , pin p , ⊑-trans cz (⊑-snoc⁺ z₀) , C.burst xz iz , reach-sub ry (next≺ {z₀} {k} (first-below cz (lies-img li))) (S.ins-C (C.burst xz iz))
    where
      iz : T (inside r z₀)
      iz = ⊑-inside (⊑-trans (burst-r cc (lies-⊑ (lies-img li)) i) (⊑-trans (⊑-snoc⁺ c) cz))
  firstS cc (C.echo {k} x al _ _) ry li =
    via-first cc (reach-few {e = skip} (λ {_} {_} → tt) ry)
      (λ {z} cz xz → ≺-trans {z} {k} {k ⊕ [ ix 0 ]} (first-below cz (lies-img li)) (≺-ext k [])
                   , inj₁ (λ {ce} b → ≺-trans {z} {k} {ce} (first-below cz (lies-img li)) (al b)))
  firstS {c} cc (C.kept {k} {p′} x alp ni ik) ry li with lie-split (lies-img li) (inside-⊑ p′ k ik)
  ... | inj₁ lp = via-first cc (reach-pin (S.ins-C (C.kept x alp ni ik)) ry)
                    (λ {z} cz xz → first-below cz lp , inj₁ (λ {ce} b → ≺-trans {z} {p′} {ce} (first-below cz lp) (alp b)))
  ... | inj₂ pc
    with TS.again cc x (lies-img li) pc 0
           (pins-of {t = C.σ} {p′ = p′} {ks = proj₁ ry} λ {j} xj jv →
              proj₂ ry (kept-img xj alp ni (inside-⊑ p′ k ik)) (next≺ {j} {k} (≺-≼-≺ {j} {c ⊕ [ ix 1 ]} {k} jv (lies-≼ (lies-img li))))
                (λ _ → inj₂ refl))
  ...   | z , cz , xz =
    z ⊕ [ ix 0 ] , pin p′ , ⊑-trans cz (⊑-snoc⁺ z) , kept-img xz alp ni (inside-⊑ p′ k ik)
    , reach-sub ry (next≺ {z} {k} (first-below cz (lies-img li))) (S.ins-C (kept-img xz alp ni (inside-⊑ p′ k ik)))

  firstB : ∀ {c y e} → TB.Cut c → C.β y e → Reach C.ConnT y e → Lies c y → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix 0 ]) ⊑ z × Ct z e
  firstB {e = out a} cb b ry li = spreadB cb (lies-⊑ li) (reach-few {e = out a} (λ {_} {_} → tt) ry) (TB.first cb)
  firstB {e = skip}  cb b ry li = spreadB cb (lies-⊑ li) (reach-few {e = skip} (λ {_} {_} → tt) ry) (TB.first cb)
  firstB {e = end}   cb b ry li = spreadB cb (lies-⊑ li) (reach-few {e = end} (λ {_} {_} → tt) ry) (TB.first cb)
  firstB {c} {y} {pin r′} cb b ry li with lie-split li (inside-⊑ r′ y (proj₂ (InvAt.pinned Iβ b)))
  ... | inj₁ lr = spreadB cb (lies-⊑ lr) (reach-pin (proj₂ (InvAt.pinned Iβ b)) ry) (TB.first cb)
  ... | inj₂ rc
    with TB.again cb b li rc 0 (proj₁ ry , λ {k} bk kv → proj₂ ry (C.body bk) (≺-≼-≺ {k} {c ⊕ [ ix 1 ]} {y} kv (lies-≼ li)) (λ _ → inj₂ refl))
  ...   | z , cz , bz = z , pin r′ , cz , C.body bz , reach-sub ry (first-below cz li) (proj₂ (InvAt.pinned Iβ bz))

  first′ : ∀ {c} → Cut′ c → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix 0 ]) ⊑ z × Ct z e
  first′ (inj₁ (_ , y , e , ct , (zero , l) , _))                = y , e , l , ct
  first′ (inj₂ (_ , y , e , ct , (zero , l)))                    = y , e , l , ct
  first′ (inj₁ (cc , y , e , (cy , ry) , (suc j , l) , _))       = firstS cc cy ry (j , l)
  first′ (inj₂ (cb , y , e , (cy , ry) , (suc j , l)))           = firstB cb (body-in cb cy (suc j , l)) ry (j , l)

  ------------------------------------------------------------------------
  -- Later spin rows

  -- Few reached rows before: few rows, where hangs show.
  raw : ∀ {v} → Few Ct v → Few C.ConnT v
  raw {v} (ks , h) = ks , λ {k} ck kv → ∈-stable λ ¬i → ¬F λ Fv → ¬i (h (ck , few-reach (few-down Fv (≺→≼ {k} {v} kv))) kv)
    where
      ¬F : ¬ ¬ Few C.ConnT v
      ¬F = shC (ks , λ ck F kv → h (ck , few-reach F) kv)

  -- Few source rows before, where each past few is a member.
  σ-few : ∀ {v} (L : List Pos) → (∀ {j e} → C.σ j e → Few C.σ j → j ≺ v → j ∈ L) → Few C.σ v
  σ-few {v} L mem = L , λ {j} xj jv → ∈-stable λ ¬m → shS (L , mem) λ Fv → ¬m (mem xj (few-down Fv (≺→≼ {j} {v} jv)) jv)

  Next : Pos → ℕ → Set
  Next c i = Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × Ct z e

  reached′ : ∀ {v z e} → Few C.ConnT v → z ≼ v → C.ConnT z e → Ct z e
  reached′ FC zv cz = cz , few-reach (few-down FC zv)

  showsB : ∀ {c} → TB.Cut c → ∀ i → Few C.ConnT (c ⊕ [ ix (suc i) ]) → Next c i
  showsB {c} cb i FC =
    let (z , e , cz , bz) = TB.shows cb i (proj₁ FC , λ bk kv → proj₂ FC (C.body bk) kv)
    in z , e , cz , reached′ FC (≺→≼ {z} {c ⊕ [ ix (suc i) ]} (below-next c cz ≤-refl)) (C.body bz)

  showsS : ∀ {c} → TS.Cut c → Shown c → ∀ i → Few C.ConnT (c ⊕ [ ix (suc i) ]) → Next c i
  showsS {c} cc sh i FC =
    let (z , _ , cz , xz) = TS.shows cc i (cov-few {X = C.σ} {v = c ⊕ [ ix (suc i) ]} {ks = proj₁ FC}
                              λ {j} xj jv → cov-img FC jv (proj₂ (img xj (shown-ab {j = j} {m = suc i} cc sh xj jv))) (⊑-snoc⁺ j))
        zv = below-next c cz ≤-refl
        (e , ct) = img xz (shown-ab {j = z} {m = suc i} cc sh xz zv)
    in z ⊕ [ ix 0 ] , e , ⊑-trans cz (⊑-snoc⁺ z) , reached′ FC (step≼ {z} {c ⊕ [ ix (suc i) ]} zv) ct

  showsK : ∀ {c} → TS.Cut c → KeptW c → ∀ i → Few C.ConnT (c ⊕ [ ix (suc i) ]) → Next c i
  showsK {c} cc (k , p′ , x , li , pc , alp , ni) i FC =
    let pk = ⊑-trans pc (lies-⊑ li)
        (z , cz , xz) = TS.again cc x li pc i (pins-of {t = C.σ} {p′ = p′} {ks = proj₁ FC}
                          λ {j} xj jv → proj₂ FC (kept-img {j = j} {k = k} xj alp ni pk) (step≺ c {i} {j} jv))
    in z ⊕ [ ix 0 ] , pin p′ , ⊑-trans cz (⊑-snoc⁺ z) , reached′ FC (step≼ {z} {c ⊕ [ ix (suc i) ]} (below-next c cz ≤-refl)) (kept-img {j = z} {k = k} xz alp ni pk)

  showsM : ∀ {c} → TS.Cut c → Shown c ⊎ KeptW c → ∀ i → Few C.ConnT (c ⊕ [ ix (suc i) ]) → Next c i
  showsM cc (inj₁ sh) = showsS cc sh
  showsM cc (inj₂ kw) = showsK cc kw

  shows′ : ∀ {c} → Cut′ c → ∀ i → Few Ct (c ⊕ [ ix (suc i) ]) → Next c i
  shows′ (inj₁ cs) i F = showsM (proj₁ cs) (mode cs) i (raw F)
  shows′ (inj₂ (cb , _)) i F = showsB cb i (raw F)

  -- Under the burst, a source cut's spin row past few shows a burst pin, reached.
  again-burst : ∀ {c i} → TS.Cut c → r ⊑ c → Pins Ct p (c ⊕ [ ix (suc i) ]) → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Ct z (pin p)
  again-burst {c} {i} cc rB (ks , h) =
    let (z , _ , cz , xz) = TS.shows cc i Fv
        zv = below-next c cz ≤-refl
        iz = in-burst (σ-r xz) zv rv
    in z ⊕ [ ix 0 ] , ⊑-trans cz (⊑-snoc⁺ z) , C.burst xz iz , S.reach-burst (few-down Fv (≺→≼ {z} {v} zv)) xz iz
    where
      v : Pos
      v = c ⊕ [ ix (suc i) ]

      rv : r ⊑ v
      rv = ⊑-trans rB (⊑-snoc⁺ c)

      mem : ∀ {j e} → C.σ j e → Few C.σ j → j ≺ v → j ∈ cover v ks
      mem {j} xj Fj jv =
        let ij = in-burst (σ-r xj) jv rv
        in cov-∈ {v} {ks} {j} (inj₂ (lead-∈ (⊑-snoc⁺ j) (h (C.burst xj ij , S.reach-burst Fj xj ij) (step≺ c {i} {j} jv))))

      Fv : Few C.σ v
      Fv = σ-few (cover v ks) mem

  -- A kept pin's spin row past few shows the same pin again, reached.
  again-kept : ∀ {c k p′ i} → TS.Cut c → (x : C.σ k (pin p′)) (alp : C.Alive p′) (ni : T (not (inside r k))) (ik : T (inside p′ k))
             → Reach C.ConnT (k ⊕ [ ix 0 ]) (pin p′) → Lies c (k ⊕ [ ix 0 ]) → p′ ⊑ c → Pins Ct p′ (c ⊕ [ ix (suc i) ])
             → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Ct z (pin p′)
  again-kept {c} {k} {p′} {i} cc x alp ni ik rw li rc (ks , h) =
    let pk = inside-⊑ p′ k ik
        Fk = reach-pin (S.ins-C (C.kept x alp ni ik)) rw
        (z , cz , xz) = TS.again cc x (lies-img li) rc i
                          (pins-of {t = C.σ} {p′ = p′} {ks = ks} λ {j} xj jv →
                             h (kept-img {j = j} {k = k} xj alp ni pk , S.reach-kept Fk xj) (step≺ c {i} {j} jv))
    in z ⊕ [ ix 0 ] , ⊑-trans cz (⊑-snoc⁺ z) , kept-img {j = z} {k = k} xz alp ni pk , S.reach-kept Fk xz

  -- A body pin's spin row past few shows the same pin again, reached.
  again-body : ∀ {c w r₁ i} → TB.Cut c → C.β w (pin r₁) → Reach C.ConnT w (pin r₁) → Lies c w → r₁ ⊑ c → Pins Ct r₁ (c ⊕ [ ix (suc i) ])
             → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Ct z (pin r₁)
  again-body {i = i} cb b rw li rc ps =
    let Fr = reach-pin (proj₂ (InvAt.pinned Iβ b)) rw
        (z , cz , bz) = TB.again cb b li rc i (pins-via {Y = C.β} {Z = Ct} (λ bk _ → C.body bk , S.reach-bpin Fr bk) ps)
    in z , cz , C.body bz , S.reach-bpin Fr bz

  again′ : ∀ {c w r₁} → Cut′ c → Ct w (pin r₁) → Lies c w → r₁ ⊑ c → ∀ i → Pins Ct r₁ (c ⊕ [ ix (suc i) ])
         → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Ct z (pin r₁)
  again′ (inj₁ (cc , _)) (C.body b , _) li rc i ps = ⊥-elim (bleads (proj₁ (InvAt.pinned Iβ b)) (Placed.placed PS cc) rc)
  again′ (inj₁ (cc , _)) (C.burst x ik , _) li rc i ps = again-burst cc (burst-r cc (lies-⊑ (lies-img li)) ik) ps
  again′ (inj₁ (cc , _)) (C.kept x alp ni ik , rw) li rc i ps = again-kept cc x alp ni ik rw li rc ps
  again′ (inj₂ (cb , _)) (C.body b , rw) li rc i ps = again-body cb b rw li rc ps
  again′ (inj₂ (cb , _)) (C.burst x _ , _) li _ _ _    = ⊥-elim (b-img cb (sw x) (lies-spun li))
  again′ (inj₂ (cb , _)) (C.kept x _ _ _ , _) li _ _ _ = ⊥-elim (b-img cb (sw x) (lies-spun li))
