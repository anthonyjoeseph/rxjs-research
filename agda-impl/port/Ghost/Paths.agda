{-# OPTIONS --guardedness #-}

-- PATH OPERATIONS ON THE GHOST: concatenation of two paths, the side
-- conditions `Lifts` reads at each ancestor, what each lift leaves free,
-- the path split along each half, and path-length arithmetic used by the
-- climbing induction.
module port.Ghost.Paths where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat.Properties using (≤-refl; m<m+n)
open import Data.Nat using (ℕ; suc; _<_; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

import denotation.Unfold as U
open import denotation.MonotonicList.Events using (Pos; ix; _<ᵖ_)
open import port.Leaves using (Leaves)
open import port.Strong using (module Strongly)

module GhostingPaths (R : Set) where
  open Strongly R using
    ( Sub; ofˢ; mapˢ; scanˢ; cutˢ; laneˢ; takeWhileˢ; flatMapˢ; connectˢ
    ; Taking; taking; ending; taken
    ; Path; PathLanes
    ; here; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes; in-source; in-body
    ; this-lane; next-lane
    ; part; partLanes; leftover
    ; seen; seenL; isTaking
    ; Heads
    )

  ------------------------------------------------------------------------
  -- PATH CONCATENATION

  mutual
    _⊕_ : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C}
         → Path t u π → Path u v τ → Path t v (π ++ τ)
    here        ⊕ q = q
    in-map p    ⊕ q = in-map (p ⊕ q)
    in-scan p   ⊕ q = in-scan (p ⊕ q)
    in-cut p    ⊕ q = in-cut (p ⊕ q)
    in-lane p   ⊕ q = in-lane (p ⊕ q)
    in-take p   ⊕ q = in-take (p ⊕ q)
    in-outer p  ⊕ q = in-outer (p ⊕ q)
    in-lanes p  ⊕ q = in-lanes (p ⊕ᴸ q)
    in-source p ⊕ q = in-source (p ⊕ q)
    in-body p   ⊕ q = in-body (p ⊕ q)

    _⊕ᴸ_ : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {u : Sub Δ B} {v : Sub Ε C}
          → PathLanes ls u i π → Path u v τ → PathLanes ls v i (π ++ τ)
    this-lane p  ⊕ᴸ q = this-lane (p ⊕ q)
    next-lane πL ⊕ᴸ q = next-lane (πL ⊕ᴸ q)

  ------------------------------------------------------------------------
  -- SIDE CONDITIONS: what each operator on the path requires of its
  -- children's steps to pick the path's step as the ghost's.

  -- The source's next event before the body's: its own skip, the body's
  -- step left for later.  A hushed source never is.
  SourceFirst : ∀ {Γ A B} → U.Step Γ A → U.Step (A ∷ Γ) B → Set
  SourceFirst (U.outˢ q _ _) sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ true
  SourceFirst (U.skipˢ q _)  sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ true
  SourceFirst (U.endˢ c)     sb = U.beforeˢ (c ++ [ ix 0 ]) sb ≡ true
  SourceFirst U.hushˢ        sb = ⊥

  BodyFirst : ∀ {Γ A B} → U.Step Γ A → U.Step (A ∷ Γ) B → Set
  BodyFirst (U.outˢ q _ _) sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false
  BodyFirst (U.skipˢ q _)  sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false
  BodyFirst (U.endˢ c)     sb = U.beforeˢ (c ++ [ ix 0 ]) sb ≡ false
  BodyFirst U.hushˢ        sb = ⊤

  -- A flatMap's outer step ahead of every lane's.
  OuterFirst : ∀ {Γ A B} → U.Step Γ A → List (U.Node Γ B) → Set₁
  OuterFirst S ls = ∀ {k bs l s as} → U.earliest ls ≡ U.found k bs l s as → Σ Pos λ k′ → U.headˢ S ≡ just k′ × k′ <ᵖ k ≡ true

  -- What a flatMap's ended parts left running steps no sooner than its
  -- outer and lanes.
  PoolBehind : ∀ {Γ A B} → U.Node Γ B → U.Outer Γ A → U.Earliest Γ B → Set₁
  PoolBehind p o e = ∀ {k p′} → U.step p ≡ U.skipˢ k p′ → U.aheadˢ k o e ≡ false

  -- What an ended source left running steps no sooner than the body.
  RestBehind : ∀ {Γ A B} → U.Node Γ A → U.Step (A ∷ Γ) B → Set₁
  RestBehind t sb = ∀ {k t′} → U.step t ≡ U.skipˢ k t′ → U.beforeˢ (k ++ [ ix 0 ]) sb ≡ false

  -- The earliest lane's step, at `k`, ahead of the outer's.
  LaneFirst : ∀ {Γ A} → Maybe (U.Node Γ A) → Pos → Set
  LaneFirst nothing  k = ⊤
  LaneFirst (just o) k = ∀ {k′} → U.headˢ (U.step o) ≡ just k′ → k′ <ᵖ k ≡ false

  -- What holds once a step ends, and nothing before.
  OnEnd : ∀ {Γ A} → U.Step Γ A → Set₁ → Set₁
  OnEnd (U.endˢ _) P = P
  OnEnd _          P = Lift _ ⊤

  ------------------------------------------------------------------------
  -- LIFTS: the ghost's step, from a step at the path's end

  mutual
    data Lifts : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → U.Step Δ B → U.Step Γ A → Set₁ where
      lifts-here   : ∀ {Γ A} {t : Sub Γ A} {s} → Lifts (here {t = t}) s s
      lifts-map    : ∀ {Γ X A Δ B π} {f : X → A} {t : Sub Γ X} {u : Sub Δ B} {ρ : Path t u π} {s S}
                   → Lifts ρ s S → Lifts (in-map {f = f} ρ) s (U.mapˢ f S)
      lifts-scan   : ∀ {Γ X A Δ B π} {f : A → X → A} {z} {t : Sub Γ X} {u : Sub Δ B} {ρ : Path t u π} {s S}
                   → Lifts ρ s S → Lifts (in-scan {f = f} {z} ρ) s (U.scanˢ f z S)
      lifts-cut    : ∀ {Γ A Δ B l a π} {t : Sub Γ A} {u : Sub Δ B} {ρ : Path t u π} {s S}
                   → l ≡ true → Lifts ρ s S → Lifts (in-cut {l = l} {a = a} ρ) s S
      lifts-lane   : ∀ {Γ A Δ B r π} {t : Sub Γ A} {u : Sub Δ B} {ρ : Path t u π} {s S}
                   → Lifts ρ s S → Lifts (in-lane {r = r} ρ) s S
      lifts-take   : ∀ {Γ A Δ B i q tk π} {t : Sub Γ A} {u : Sub Δ B} {ρ : Path t u π} {s S}
                   → Lifts ρ s S → Lifts (in-take {i = i} {q} {tk = tk} ρ) s (U.takeWhileˢ i q S)
      lifts-outer  : ∀ {Γ X A Δ B op f d n qs pl π} {t : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Δ B} {ρ : Path t u π} {s S o₀}
                   → OuterFirst S (partLanes ls)
                   → PoolBehind pl (U.outerOf (just o₀)) (U.earliest (partLanes ls)) → Lifts ρ s S
                   → Lifts (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {ls = ls} ρ) s
                       (U.outerˢ op (λ a r → U.subscribe (f a) r) o₀ S (partLanes ls) qs pl)
      lifts-lanes  : ∀ {Γ X A Δ B op f d n qs pl i π} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Δ B} {πL : PathLanes ls u i π}
                       {s bs l S as q}
                   → LiftsLane πL s bs S as → U.earliest (bs ++ l ∷ as) ≡ U.found q bs l S as → LaneFirst (part o) q
                   → PoolBehind pl (U.outerOf (part o)) (U.found q bs l S as)
                   → Lifts (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} πL) s
                       (U.laneˢ op (λ a r → U.subscribe (f a) r) (part o) bs l S as qs pl)
      lifts-source : ∀ {Γ X B Δ C k r e rt π} {t : Sub Γ X} {b : Sub (X ∷ Γ) B} {u : Sub Δ C} {ρ : Path t u π} {s S b₀ c₀}
                   → part b ≡ just b₀ → SourceFirst S (U.step b₀) → Lifts ρ s S
                   → Lifts (in-source {k = k} {r = r} {e = e} {rt = rt} {t = t} {b = b} ρ) s (U.sourceˢ r b₀ (U.step b₀) c₀ S)
      lifts-body   : ∀ {Γ X B Δ C k r e rt π} {s : Sub Γ X} {t : Sub (X ∷ Γ) B} {u : Sub Δ C} {ρ : Path t u π} {x S c₀}
                   → part s ≡ just c₀ → BodyFirst (U.step c₀) S → Lifts ρ x S
                   → Lifts (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) x (U.bodyˢ r (U.live c₀) S)
      lifts-shut   : ∀ {Γ X B Δ C k r e rt π} {s : Sub Γ X} {t : Sub (X ∷ Γ) B} {u : Sub Δ C} {ρ : Path t u π} {x S c₀}
                   → part s ≡ nothing → e ≡ just c₀ → RestBehind rt S → Lifts ρ x S
                   → Lifts (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) x (U.shutˢᵗ r c₀ rt S)

    data LiftsLane : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π
                   → U.Step Δ B → List (U.Node Γ A) → U.Step Γ A → List (U.Node Γ A) → Set₁ where
      lifts-this : ∀ {Γ A Δ B π} {t : Sub Γ A} {ls : List (Sub Γ A)} {u : Sub Δ B} {ρ : Path t u π} {s S}
                 → Lifts ρ s S → LiftsLane (this-lane {ls = ls} ρ) s [] S (partLanes ls)
      lifts-next : ∀ {Γ A Δ B i π} {l : Sub Γ A} {ls : List (Sub Γ A)} {u : Sub Δ B} {πL : PathLanes ls u i π} {s bs S as}
                 → LiftsLane πL s bs S as → LiftsLane (next-lane {l = l} πL) s (partLanes (l ∷ []) ++ bs) S as

  ------------------------------------------------------------------------
  -- LEFTS: what a lift leaves free

  mutual
    Lefts : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} {ρ : Path t u π} {s S} → Lifts ρ s S → Set₁
    Lefts lifts-here                                       = Lift _ ⊤
    Lefts (lifts-map L)                                    = Lefts L
    Lefts (lifts-scan L)                                   = Lefts L
    Lefts (lifts-cut _ L)                                  = Lefts L
    Lefts (lifts-lane L)                                   = Lefts L
    Lefts (lifts-take L)                                   = Lefts L
    Lefts (lifts-outer {t = t} {S = S} {o₀ = o₀} _ _ L)  = OnEnd S (Leaves o₀ (leftover {B = ⊤} t)) × Lefts L
    Lefts (lifts-lanes {l = l} L _ _ _)                   = LeftsL l L
    Lefts (lifts-source {t = t} {c₀ = c₀} {S = S} _ _ L) = OnEnd S (Leaves c₀ (leftover {B = ⊤} t)) × Lefts L
    Lefts (lifts-body _ _ L)                               = Lefts L
    Lefts (lifts-shut _ _ _ L)                             = Lefts L

    LeftsL : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} {πL : PathLanes ls u i π} {s bs S as}
           → U.Node Γ A → LiftsLane πL s bs S as → Set₁
    LeftsL l (lifts-this {t = t} {S = S} L) = OnEnd S (Leaves l (leftover {B = ⊤} t)) × Lefts L
    LeftsL l (lifts-next L)                 = LeftsL l L

  ------------------------------------------------------------------------
  -- LIFTS-SPLIT: lifting along two paths is lifting along each

  mutual
    lifts-split : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C}
                  (ρ : Path t u π) (σ : Path u v τ) {s S}
                → Lifts (ρ ⊕ σ) s S → Σ (U.Step Δ B) λ S′ → Lifts σ s S′ × Lifts ρ S′ S
    lifts-split here          σ L                          = _ , L , lifts-here
    lifts-split (in-map ρ)    σ (lifts-map L)              with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-map Lρ
    lifts-split (in-scan ρ)   σ (lifts-scan L)             with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-scan Lρ
    lifts-split (in-cut ρ)    σ (lifts-cut lv L)           with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-cut lv Lρ
    lifts-split (in-lane ρ)   σ (lifts-lane L)             with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-lane Lρ
    lifts-split (in-take ρ)   σ (lifts-take L)             with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-take Lρ
    lifts-split (in-outer ρ)  σ (lifts-outer of pb L)      with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-outer of pb Lρ
    lifts-split (in-lanes πL) σ (lifts-lanes L ea lf pb)   with liftsL-split πL σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-lanes Lρ ea lf pb
    lifts-split (in-source ρ) σ (lifts-source pb sf L)     with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-source pb sf Lρ
    lifts-split (in-body ρ)   σ (lifts-body pt bf L)       with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-body pt bf Lρ
    lifts-split (in-body ρ)   σ (lifts-shut pt e rb L)     with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-shut pt e rb Lρ

    liftsL-split : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {u : Sub Δ B} {v : Sub Ε C}
                   (πL : PathLanes ls u i π) (σ : Path u v τ) {s bs S as}
                 → LiftsLane (πL ⊕ᴸ σ) s bs S as → Σ (U.Step Δ B) λ S′ → Lifts σ s S′ × LiftsLane πL S′ bs S as
    liftsL-split (this-lane ρ)  σ (lifts-this L)    with lifts-split ρ σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-this Lρ
    liftsL-split (next-lane πL) σ (lifts-next L)    with liftsL-split πL σ L
    ... | S′ , Lσ , Lρ = S′ , Lσ , lifts-next Lρ

  ------------------------------------------------------------------------
  -- LEFTS-SPLIT: what a lift leaves free, each half of it leaves free

  mutual
    lefts-split : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C}
                  (ρ : Path t u π) (σ : Path u v τ) {s S}
                  (L : Lifts (ρ ⊕ σ) s S) → Lefts L
                → Lefts (proj₁ (proj₂ (lifts-split ρ σ L))) × Lefts (proj₂ (proj₂ (lifts-split ρ σ L)))
    lefts-split here          σ L                          lt        = lt , lift tt
    lefts-split (in-map ρ)    σ (lifts-map L)              lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-scan ρ)   σ (lifts-scan L)             lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-cut ρ)    σ (lifts-cut lv L)           lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-lane ρ)   σ (lifts-lane L)             lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-take ρ)   σ (lifts-take L)             lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-outer ρ)  σ (lifts-outer of pb L)      (lo , lt) with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , (lo , lρ)
    lefts-split (in-lanes πL) σ (lifts-lanes {l = l} L ea lf pb) lt  with liftsL-split πL σ L | leftsL-split πL σ {l = l} L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-source ρ) σ (lifts-source pb sf L)     (lc , lt) with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , (lc , lρ)
    lefts-split (in-body ρ)   σ (lifts-body pt bf L)       lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ
    lefts-split (in-body ρ)   σ (lifts-shut pt e rb L)     lt        with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ

    leftsL-split : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {u : Sub Δ B} {v : Sub Ε C}
                   (πL : PathLanes ls u i π) (σ : Path u v τ) {s bs S as l}
                   (L : LiftsLane (πL ⊕ᴸ σ) s bs S as) → LeftsL l L
                 → Lefts (proj₁ (proj₂ (liftsL-split πL σ L))) × LeftsL l (proj₂ (proj₂ (liftsL-split πL σ L)))
    leftsL-split (this-lane ρ)  σ (lifts-this L) (ll , lt) with lifts-split ρ σ L | lefts-split ρ σ L lt
    ... | _ , _ , _ | lσ , lρ = lσ , (ll , lρ)
    leftsL-split (next-lane πL) σ {l = l} (lifts-next L) lt   with liftsL-split πL σ L | leftsL-split πL σ {l = l} L lt
    ... | _ , _ , _ | lσ , lρ = lσ , lρ

  -- Read off a split named by its outcome.
  lefts-up : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C}
             (ρ : Path t u π) (σ : Path u v τ) {s S}
             {L : Lifts (ρ ⊕ σ) s S} {S′} {Lσ : Lifts σ s S′} {Lρ : Lifts ρ S′ S}
           → lifts-split ρ σ L ≡ (S′ , Lσ , Lρ) → Lefts L → Lefts Lρ
  lefts-up ρ σ {L = L} eq lt = subst (λ w → Lefts (proj₂ (proj₂ w))) eq (proj₂ (lefts-split ρ σ L lt))

  -- A source rewritten in place: the free nodes are the derivation's.
  lefts-subst : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} {ρ : Path t u π} {ℓ} {X : Set ℓ} (f : X → U.Step Δ B) {S x y}
                (e : x ≡ y) {L : Lifts ρ (f x) S} → Lefts L → Lefts (subst (λ z → Lifts ρ (f z) S) e L)
  lefts-subst f refl lt = lt

  lefts-subst₂ : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} {ρ : Path t u π} {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} (f : X → Y → U.Step Δ B) {S x₁ x₂ y₁ y₂}
                 (e₁ : x₁ ≡ x₂) (e₂ : y₁ ≡ y₂) {L : Lifts ρ (f x₁ y₁) S} → Lefts L → Lefts (subst₂ (λ x y → Lifts ρ (f x y) S) e₁ e₂ L)
  lefts-subst₂ f refl refl lt = lt

  ------------------------------------------------------------------------
  -- ONE: a path one operator long

  mutual
    data One : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → Set₁ where
      one-map    : ∀ {Γ X A} {f : X → A} {t : Sub Γ X} → One (in-map {f = f} {t = t} here)
      one-scan   : ∀ {Γ X A} {f : A → X → A} {z} {t : Sub Γ X} → One (in-scan {f = f} {z} {t = t} here)
      one-cut    : ∀ {Γ A l a} {t : Sub Γ A} → One (in-cut {l = l} {a = a} {t = t} here)
      one-lane   : ∀ {Γ A r} {t : Sub Γ A} → One (in-lane {r = r} {t = t} here)
      one-take   : ∀ {Γ A i q tk} {t : Sub Γ A} → One (in-take {i = i} {q} {tk} {t = t} here)
      one-outer  : ∀ {Γ X A op f d n qs pl} {t : Sub Γ X} {ls : List (Sub Γ A)}
                 → One (in-outer {op = op} {f} {d} {n} {qs} {pl} {t = t} {ls} here)
      one-lanes  : ∀ {Γ X A Δ B op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Δ B} {i π} {πL : PathLanes ls u i π}
                 → OneLane πL → One (in-lanes {op = op} {f} {d} {n} {qs} {pl} {o = o} πL)
      one-source : ∀ {Γ X A k r e rt} {t : Sub Γ X} {b : Sub (X ∷ Γ) A} → One (in-source {k = k} {r} {e} {rt} {t = t} {b} here)
      one-body   : ∀ {Γ X A k r e rt} {s : Sub Γ X} {t : Sub (X ∷ Γ) A} → One (in-body {k = k} {r} {e} {rt} {s = s} {t} here)

    data OneLane : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π → Set₁ where
      one-this : ∀ {Γ A} {t : Sub Γ A} {ls} → OneLane (this-lane {t = t} {ls} here)
      one-next : ∀ {Γ A Δ B i π} {l : Sub Γ A} {ls : List (Sub Γ A)} {u : Sub Δ B} {πL : PathLanes ls u i π} → OneLane πL → OneLane (next-lane {l = l} πL)

  -- A path read from its far end: none, or a path and one operator more.
  data Last {Γ A} {t : Sub Γ A} : ∀ {Δ B π} {v : Sub Δ B} → Path t v π → Set₁ where
    whole : Last here
    snoc  : ∀ {Δ A′ Ε C π τ} {u : Sub Δ A′} {v : Sub Ε C} (ρ : Path t u π) (s : Path u v τ) → One s → Last (ρ ⊕ s)

  data LastL {Γ A} {ls : List (Sub Γ A)} : ∀ {Δ B i π} {v : Sub Δ B} → PathLanes ls v i π → Set₁ where
    oneL  : ∀ {Δ B i π} {v : Sub Δ B} {πL : PathLanes ls v i π} → OneLane πL → LastL πL
    snocL : ∀ {Δ A′ Ε C i π τ} {u : Sub Δ A′} {v : Sub Ε C} (πL : PathLanes ls u i π) (s : Path u v τ) → One s → LastL (πL ⊕ᴸ s)

  ------------------------------------------------------------------------
  -- VIEW / VIEWL: compute the Last/LastL decomposition

  mutual
    view : ∀ {Γ A Δ B π} {t : Sub Γ A} {v : Sub Δ B} (σ : Path t v π) → Last σ
    view here = whole
    view (in-map p) with view p
    ... | whole      = snoc here (in-map here) one-map
    ... | snoc ρ s o = snoc (in-map ρ) s o
    view (in-scan p) with view p
    ... | whole      = snoc here (in-scan here) one-scan
    ... | snoc ρ s o = snoc (in-scan ρ) s o
    view (in-cut p) with view p
    ... | whole      = snoc here (in-cut here) one-cut
    ... | snoc ρ s o = snoc (in-cut ρ) s o
    view (in-lane p) with view p
    ... | whole      = snoc here (in-lane here) one-lane
    ... | snoc ρ s o = snoc (in-lane ρ) s o
    view (in-take p) with view p
    ... | whole      = snoc here (in-take here) one-take
    ... | snoc ρ s o = snoc (in-take ρ) s o
    view (in-outer p) with view p
    ... | whole      = snoc here (in-outer here) one-outer
    ... | snoc ρ s o = snoc (in-outer ρ) s o
    view (in-lanes p) with viewL p
    ... | oneL o      = snoc here (in-lanes p) (one-lanes o)
    ... | snocL ρ s o = snoc (in-lanes ρ) s o
    view (in-source p) with view p
    ... | whole      = snoc here (in-source here) one-source
    ... | snoc ρ s o = snoc (in-source ρ) s o
    view (in-body p) with view p
    ... | whole      = snoc here (in-body here) one-body
    ... | snoc ρ s o = snoc (in-body ρ) s o

    viewL : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {v : Sub Δ B} (πL : PathLanes ls v i π) → LastL πL
    viewL (this-lane p) with view p
    ... | whole      = oneL one-this
    ... | snoc ρ s o = snocL (this-lane ρ) s o
    viewL (next-lane p) with viewL p
    ... | oneL o      = oneL (one-next o)
    ... | snocL ρ s o = snocL (next-lane ρ) s o

  ------------------------------------------------------------------------
  -- HEIGHT: how many operators a path passes

  mutual
    height : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → ℕ
    height here          = 0
    height (in-map p)    = suc (height p)
    height (in-scan p)   = suc (height p)
    height (in-cut p)    = suc (height p)
    height (in-lane p)   = suc (height p)
    height (in-take p)   = suc (height p)
    height (in-outer p)  = suc (height p)
    height (in-lanes p)  = heightL p
    height (in-source p) = suc (height p)
    height (in-body p)   = suc (height p)

    heightL : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π → ℕ
    heightL (this-lane p) = suc (height p)
    heightL (next-lane p) = heightL p

  mutual
    height-⊕ : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C}
               (ρ : Path t u π) (σ : Path u v τ)
             → height (ρ ⊕ σ) ≡ height ρ + height σ
    height-⊕ here          σ = refl
    height-⊕ (in-map ρ)    σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-scan ρ)   σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-cut ρ)    σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-lane ρ)   σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-take ρ)   σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-outer ρ)  σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-lanes πL) σ = heightL-⊕ πL σ
    height-⊕ (in-source ρ) σ = cong suc (height-⊕ ρ σ)
    height-⊕ (in-body ρ)   σ = cong suc (height-⊕ ρ σ)

    heightL-⊕ : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {u : Sub Δ B} {v : Sub Ε C}
                (πL : PathLanes ls u i π) (σ : Path u v τ)
              → heightL (πL ⊕ᴸ σ) ≡ heightL πL + height σ
    heightL-⊕ (this-lane ρ)  σ = cong suc (height-⊕ ρ σ)
    heightL-⊕ (next-lane πL) σ = heightL-⊕ πL σ

  mutual
    height-one : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} {s : Path t u π} → One s → height s ≡ 1
    height-one one-map       = refl
    height-one one-scan      = refl
    height-one one-cut       = refl
    height-one one-lane      = refl
    height-one one-take      = refl
    height-one one-outer     = refl
    height-one (one-lanes o) = heightL-one o
    height-one one-source    = refl
    height-one one-body      = refl

    heightL-one : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} {πL : PathLanes ls u i π} → OneLane πL → heightL πL ≡ 1
    heightL-one one-this     = refl
    heightL-one (one-next o) = heightL-one o

  one-lower : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C} (ρ : Path t u π) {s : Path u v τ} → One s
            → height ρ < height (ρ ⊕ s)
  one-lower ρ {s} o = subst (height ρ <_) (sym (trans (height-⊕ ρ s) (cong (height ρ +_) (height-one o)))) (m<m+n (height ρ) ≤-refl)

  ------------------------------------------------------------------------
  -- HEALED: an end reaching a connect's source has the connect's own end staged

  mutual
    Healed : ∀ (q : Pos) {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → Set₁
    Healed q here                                       = Lift _ ⊤
    Healed q (in-map p)                                 = Healed q p
    Healed q (in-scan p)                                = Healed q p
    Healed q (in-cut p)                                 = Healed q p
    Healed q (in-lane p)                                = Healed q p
    Healed q (in-take p)                                = Healed q p
    Healed q (in-outer p)                               = Healed q p
    Healed q (in-lanes p)                               = HealedL q p
    Healed q (in-source {e = e} {t = s} p)              = (part s ≡ nothing → e ≡ just q) × Healed q p
    Healed q (in-body p)                                = Healed q p

    HealedL : ∀ (q : Pos) {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π → Set₁
    HealedL q (this-lane p) = Healed q p
    HealedL q (next-lane p) = HealedL q p

  mutual
    healed-split : ∀ {q Γ A Δ B Ε C π τ} {t : Sub Γ A} {u : Sub Δ B} {v : Sub Ε C}
                   (ρ : Path t u π) (σ : Path u v τ)
                 → Healed q (ρ ⊕ σ) → Healed q ρ
    healed-split here          σ _         = lift tt
    healed-split (in-map ρ)    σ hl        = healed-split ρ σ hl
    healed-split (in-scan ρ)   σ hl        = healed-split ρ σ hl
    healed-split (in-cut ρ)    σ hl        = healed-split ρ σ hl
    healed-split (in-lane ρ)   σ hl        = healed-split ρ σ hl
    healed-split (in-take ρ)   σ hl        = healed-split ρ σ hl
    healed-split (in-outer ρ)  σ hl        = healed-split ρ σ hl
    healed-split (in-lanes πL) σ hl        = healedL-split πL σ hl
    healed-split (in-source ρ) σ (x , hl) = x , healed-split ρ σ hl
    healed-split (in-body ρ)   σ hl        = healed-split ρ σ hl

    healedL-split : ∀ {q Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {u : Sub Δ B} {v : Sub Ε C}
                    (πL : PathLanes ls u i π) (σ : Path u v τ)
                  → HealedL q (πL ⊕ᴸ σ) → HealedL q πL
    healedL-split (this-lane ρ)  σ hl = healed-split ρ σ hl
    healedL-split (next-lane πL) σ hl = healedL-split πL σ hl

  -- An end reaching a connect's source: the connect's own end staged.
  mutual
    healed-end : ∀ {q Γ C Δ X B k r e rt π} {o : Sub Γ C} {s : Sub Δ X} {b : Sub (X ∷ Δ) B}
                 (ρ : Path o (connectˢ k r e rt s b) π) → Healed q (ρ ⊕ in-source here) → part s ≡ nothing → e ≡ just q
    healed-end here          (x , _) ns = x ns
    healed-end (in-map ρ)    hl      ns = healed-end ρ hl ns
    healed-end (in-scan ρ)   hl      ns = healed-end ρ hl ns
    healed-end (in-cut ρ)    hl      ns = healed-end ρ hl ns
    healed-end (in-lane ρ)   hl      ns = healed-end ρ hl ns
    healed-end (in-take ρ)   hl      ns = healed-end ρ hl ns
    healed-end (in-outer ρ)  hl      ns = healed-end ρ hl ns
    healed-end (in-lanes πL) hl      ns = healedL-end πL hl ns
    healed-end (in-source ρ) (_ , hl) ns = healed-end ρ hl ns
    healed-end (in-body ρ)   hl      ns = healed-end ρ hl ns

    healedL-end : ∀ {q Γ C Δ X B i π k r e rt} {ls : List (Sub Γ C)} {s : Sub Δ X} {b : Sub (X ∷ Δ) B}
                  (πL : PathLanes ls (connectˢ k r e rt s b) i π) → HealedL q (πL ⊕ᴸ in-source here) → part s ≡ nothing → e ≡ just q
    healedL-end (this-lane ρ)  hl ns = healed-end ρ hl ns
    healedL-end (next-lane πL) hl ns = healedL-end πL hl ns
