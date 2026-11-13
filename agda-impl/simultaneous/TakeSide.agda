{-# OPTIONS --guardedness #-}

-- ONE SIDE OF A TAKEWHILE: a source and its takeWhile, the cuts under
-- its first failing value, and the source's rows it keeps — read alike
-- on the plain and the elaborated run.
module simultaneous.TakeSide where

open import Data.Bool using (Bool; T; not; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Position using (Pos; Label; ix; sub; last; _⊕_; root; _≟ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Truncate; Reach; Few; _≺_; _≼_;
  module TakeWhile)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-≺-≺; ≺-≼-≺; ≼-antisym; ≺-ext;
  T-not; reach-few; few-ind)
open import denotation.Laws.Worlds using (InvAt; step; Plain; plain-ix; plain-last; full; _⊑_; ⊑-≼; ⊕-identityʳ; ⊕-injʳ; inside-⊑)
open import denotation.Laws.Count using (em)
open import denotation.Laws.ShowsOps using (bool)
open import adequacy.SubOne using (take-reach; below-or-under; at-or-before)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf; instEmit; value)
open import simultaneous.Attribution using (Live; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; triⁱ; irrⁱ; transⁱ; instant-≺)
open import simultaneous.CarryBase using (PinList; pins-map; pins-from; unp-pin; Whole; apart)
open import simultaneous.CarryLeaves using (last-max; ix-last)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; passes)

------------------------------------------------------------------------
-- The cuts under a failing value

-- The labels a failing value's rows lie on: its value kept, its end.
Lab : Bool → Label → Set
Lab incl a = (a ≡ ix 0 × T incl) ⊎ a ≡ last

lab-plain : ∀ {incl a} → Lab incl a → Plain a
lab-plain (inj₁ (refl , _)) = plain-ix
lab-plain (inj₂ refl)       = plain-last

-- The row on each.
cutEv : ∀ {X : Set} → X → Label → Ev X
cutEv x (ix _)  = out x
cutEv x (sub _) = end
cutEv x last    = end

cut-unp : ∀ {X : Set} {incl a} {x : X} → Lab incl a → Unpinned (cutEv x a)
cut-unp (inj₁ (refl , _)) = tt
cut-unp (inj₂ refl)       = tt

-- A value's cut and its carrier's, shown alike.
cut-match : ∀ {A : Set} {incl a} {b : A} {n : Pos} → Lab incl a
          → Match Every (One valuesOf) (Reads valuesOf) (cutEv b a) (cutEv (instEmit (value b) n) a)
cut-match (inj₁ (refl , _)) = (λ _ → _ , refl , refl) , λ ns → ⊥-elim (ns tt)
cut-match (inj₂ refl)       = (λ _ → refl) , λ ns → ⊥-elim (ns tt)

private
  ixs : Bool → Pos → List Pos
  ixs true  q = [ q ⊕ [ ix 0 ] ]
  ixs false q = []

  ixs-in : ∀ {b} q → T b → (q ⊕ [ ix 0 ]) ∈ ixs b q
  ixs-in {true} q _ = here refl

  ixs-row : ∀ {b r} q → r ∈ ixs b q → r ≡ q ⊕ [ ix 0 ] × T b
  ixs-row {true} q (here refl) = refl , tt

-- Instants are convex: between two rows of one instant, that instant.
between : ∀ {m f l} → m ≺ f → f ≺ l → instantOf l ≡ instantOf m → instantOf f ≡ instantOf m
between {m} {f} {l} mf fl il with triⁱ (instantOf m) (instantOf f)
... | inj₂ (inj₁ e) = sym e
... | inj₂ (inj₂ fm) = ⊥-elim (≺-absurd {m} {f} mf (instant-≺ f m fm))
... | inj₁ mi with triⁱ (instantOf f) (instantOf l)
...   | inj₁ fi        = ⊥-elim (irrⁱ (subst (instantOf m ≺ⁱ_) il (transⁱ mi fi)))
...   | inj₂ (inj₁ e)  = ⊥-elim (irrⁱ (subst (instantOf m ≺ⁱ_) (trans e il) mi))
...   | inj₂ (inj₂ li) = ⊥-elim (≺-absurd {f} {l} fl (instant-≺ l f li))

-- What a source row needs to be kept.
Keeps : ∀ {X : Set} → (X → Bool) → Ev X → Set
Keeps kp (out a) = T (kp a)
Keeps kp _       = ⊤

------------------------------------------------------------------------
-- One side: a source and its takeWhile

module Side {X : Set} {H : Pos → Set} {s : Pos} (incl : Bool) (kp : X → Bool) (t : EmissionSet X)
            (rc : ∀ {y e} → t y e → Reach t y e) (I : InvAt H s t) where
  open TakeWhile incl kp t public using (Failed; TakeT; pass; fail; stop; step; tend; left)

  T′ : EmissionSet X
  T′ = Truncate TakeT

  -- A failing value at `k`.
  Fails : Pos → Set
  Fails k = Σ X λ a → t k (out a) × T (not (kp a))

  -- The first failing value.
  First : Pos → Set
  First k = Fails k × ¬ Failed k

  Pass : Ev X → Set
  Pass = Keeps kp

  private
    flatT : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥
    flatT = InvAt.flat I

  ins : ∀ {k r} → t k (pin r) → T (inside r k)
  ins x = proj₂ (InvAt.pinned I x)

  lift : ∀ {k e} → TakeT k e → T′ k e
  lift x = x , take-reach (λ {y} {e} → rc {y} {e}) (λ {y} {e} {l} {ys} {e′} → flatT {y} {e} {l} {ys} {e′}) x

  failed-up : ∀ {j k} → Failed j → j ≼ k → Failed k
  failed-up {j} {k} (c , a , x , nk , cj) jk = c , a , x , nk , ≺-≼-≺ {c} {j} {k} cj jk

  unfailed : ∀ {j k} → ¬ Failed k → j ≼ k → ¬ Failed j
  unfailed nf jk fj = nf (failed-up fj jk)

  pass-before : ∀ {x e w} → t x e → x ≺ w → ¬ Failed w → Pass e
  pass-before {x} {out a} tx xw nf with bool (kp a)
  ... | inj₁ k  = k
  ... | inj₂ nk = ⊥-elim (nf (x , a , tx , nk , xw))
  pass-before {e = skip}  _ _ _ = tt
  pass-before {e = end}   _ _ _ = tt
  pass-before {e = pin _} _ _ _ = tt

  pass-fails : ∀ {k e} → t k e → Pass e → ¬ Fails k
  pass-fails x p (a , x′ , nk) = T-not {kp a} (subst Pass (InvAt.func I x x′) p) nk

  pass-of : ∀ {k e} → ¬ Fails k → t k e → Pass e
  pass-of {e = out a} nf x with bool (kp a)
  ... | inj₁ k  = k
  ... | inj₂ nk = ⊥-elim (nf (a , x , nk))
  pass-of {e = skip}  _ _ = tt
  pass-of {e = end}   _ _ = tt
  pass-of {e = pin _} _ _ = tt

  fails? : ∀ {k e} → t k e → Fails k ⊎ ¬ Fails k
  fails? {e = out a} x with bool (kp a)
  ... | inj₁ p  = inj₂ (pass-fails x p)
  ... | inj₂ np = inj₁ (a , x , np)
  fails? {e = skip}  x = inj₂ (pass-fails x tt)
  fails? {e = end}   x = inj₂ (pass-fails x tt)
  fails? {e = pin _} x = inj₂ (pass-fails x tt)

  -- Each row of a takeWhile: its source's, or a cut under the first failure.
  view : ∀ {k e} → TakeT k e → (t k e × Pass e)
       ⊎ Σ Pos λ q → Σ X λ a → t q (out a) × T (not (kp a)) × ¬ Failed q × Σ Label λ b → Lab incl b × k ≡ q ⊕ [ b ] × e ≡ cutEv a b
  view (pass x p _)       = inj₁ (x , p)
  view (step x _)         = inj₁ (x , tt)
  view (tend x _)         = inj₁ (x , tt)
  view (left x _ _)       = inj₁ (x , tt)
  view (fail x nk nf inc) = inj₂ (_ , _ , x , nk , nf , ix 0 , inj₁ (refl , inc) , refl , refl)
  view (stop x nk nf)     = inj₂ (_ , _ , x , nk , nf , last , inj₂ refl , refl , refl)

  -- A pin kept is its source's.
  src-pin : ∀ {k r} → T′ k (pin r) → t k (pin r)
  src-pin {r = r} (y , _) with view y
  ... | inj₁ (x , _) = x
  ... | inj₂ (_ , _ , _ , _ , _ , _ , lb , _ , e) = ⊥-elim (unp-pin {X} {r} (subst Unpinned (sym e) (cut-unp lb)))

  pin-func : ∀ {k e r} → T′ k e → T′ k (pin r) → e ≡ pin r
  pin-func (y , _) y′ with view y
  ... | inj₁ (x , _) = InvAt.func I x (src-pin y′)
  ... | inj₂ (_ , _ , x , _ , _ , _ , _ , refl , _) = ⊥-elim (flatT x (src-pin y′))

  -- The pins of an unfailed connect, across the takeWhile.
  pins← : ∀ {r v} → ¬ Failed r → PinList T′ r v → PinList t r v
  pins← {r} {v} nf = pins-map {a = T′} {b = t} {r = r} {v = v} (λ {k} → src-pin {k}) (λ {k} x → lift (left {k} x nf (ins {k} x)))

  pins→ : ∀ {r v} → ¬ Failed r → PinList t r v → PinList T′ r v
  pins→ {r} {v} nf = pins-map {a = t} {b = T′} {r = r} {v = v} (λ {k} x → lift (left {k} x nf (ins {k} x))) (λ {k} → src-pin {k})

  pins-of : ∀ {r v} → ¬ Failed r → Listed T′ v → PinList t r v
  pins-of {r} {v} nf L = pins-from {a = t} {b = T′} {r = r} {v = v} L (λ {k} → pin-func {k}) (λ {k} x _ → lift (left {k} x nf (ins {k} x))) (λ {k} → src-pin {k})

  up : ∀ {k e} → t k e → ¬ Failed k → Pass e → T′ k e
  up {e = out _} x nf p = lift (pass x p nf)
  up {e = skip}  x nf _ = lift (step x nf)
  up {e = end}   x nf _ = lift (tend x nf)
  up {k} {pin r} x nf _ = lift (left x (λ fr → nf (failed-up fr (⊑-≼ (inside-⊑ r k (ins x))))) (ins x))

  down : ∀ {k e} → T′ k e → ¬ Failed k → t k e × Pass e
  down (y , _) nf with view y
  ... | inj₁ r = r
  ... | inj₂ (q , a , x , nk , _ , b , _ , refl , _) = ⊥-elim (nf (q , a , x , nk , ≺-ext q []))

  cut-row : ∀ {q a b} → t q (out a) → T (not (kp a)) → ¬ Failed q → Lab incl b → T′ (q ⊕ [ b ]) (cutEv a b)
  cut-row x nk nf (inj₁ (refl , inc)) = lift (fail x nk nf inc)
  cut-row x nk nf (inj₂ refl)         = lift (stop x nk nf)

  first : ∀ {q q′} → First q → First q′ → q ≡ q′
  first {q} {q′} ((a , x , nk) , nf) ((a′ , x′ , nk′) , nf′) with ≼-or-≻ q q′ | ≼-or-≻ q′ q
  ... | _       | inj₂ lt  = ⊥-elim (nf′ (q , a , x , nk , lt))
  ... | inj₂ lt | _        = ⊥-elim (nf (q′ , a′ , x′ , nk′ , lt))
  ... | inj₁ le | inj₁ le′ = ≼-antisym {q} {q′} le le′

  few-out : ∀ {q a} → t q (out a) → Few t q
  few-out {q} {a} x = reach-few {e = out a} (λ {k} {e′} → full {q = q} {e = out a} tt {k} {e′}) (rc x)

  live-out : ∀ {y a} → t y (out a) → Live t y
  live-out ty tc cy with InvAt.quiet I tc ty cy
  ... | _ , () , _

  -- A failing value has a first one at or before it, classically.
  first¬¬ : ∀ {q a} → t q (out a) → T (not (kp a)) → ¬ ¬ Σ Pos λ q′ → First q′ × q′ ≼ q
  first¬¬ x nk = few-ind {t = t} P stp (few-out x) x nk
    where
      P : Pos → Set
      P g = ∀ {a} → t g (out a) → T (not (kp a)) → ¬ ¬ Σ Pos λ q′ → First q′ × q′ ≼ g

      stp : ∀ {g} → Few t g → (∀ {v e} → t v e → v ≺ g → P v) → P g
      stp {g} _ ih x nk = em {P = Failed g}
        (λ { (g′ , a′ , x′ , nk′ , g′g) n → ih x′ g′g x′ nk′ λ { (q′ , f , q′g′) → n (q′ , f , ≼-trans {q′} {g′} {g} q′g′ (≺→≼ {g′} {g} g′g)) } })
        (λ nf n → n (g , ((_ , x , nk) , nf) , ≼-refl {g}))

  -- Two rows in order lie apart.
  not-under : ∀ {q k e e′} → t q e → t k e′ → q ≺ k → ¬ (q ⊑ k)
  not-under {q} x x′ qk ([] , refl) = ≺-irrefl {q} (subst (q ≺_) (⊕-identityʳ q) qk)
  not-under x x′ qk (_ ∷ _ , refl)  = flatT x x′

  cut-before : ∀ {q k e e′} → t q e → t k e′ → q ≺ k → ∀ a → (q ⊕ [ a ]) ≺ k
  cut-before {q} {k} x x′ qk a = subst ((q ⊕ [ a ]) ≺_) (⊕-identityʳ k) (apart {q} {k} qk (not-under x x′ qk) [ a ] [])

  -- A row before which the run has not ended has no failure before it.
  live-unfailed : ∀ {k e} → Live T′ k → t k e → ¬ Failed k
  live-unfailed {k} lv x (q , a , xq , nkq , qk) = first¬¬ xq nkq λ { (q′ , ((_ , x′ , nk′) , nf′) , q′q) →
    lv (lift (stop x′ nk′ nf′)) (cut-before x′ x (≼-≺-≺ {q′} {q} {k} q′q qk) last) }

  -- No row at the first failing value itself.
  none-at : ∀ {q e} → First q → TakeT q e → ⊥
  none-at ((a , x , nk) , _) y with view y
  ... | inj₁ (x′ , p) = T-not {kp a} (subst Pass (InvAt.func I x′ x) p) nk
  ... | inj₂ (_ , _ , x″ , _ , _ , _ , _ , refl , _) = flatT x″ x

  unfails : ∀ {l m e} → ¬ Failed m → TakeT m e → l ≼ m → ¬ Fails l
  unfails {l} {m} nf y lm (a , x , nk) with at-or-before {l} {m} lm
  ... | inj₁ refl = none-at ((a , x , nk) , nf) y
  ... | inj₂ lt   = nf (l , a , x , nk , lt)

  -- Listings and counts across the takeWhile.
  lst→ : ∀ {w} → ¬ Failed w → Listed t w → Listed T′ w
  lst→ {w} nf (ks , F , B) = ks , (λ {k} y kw → F (proj₁ (down y (unfailed nf (≺→≼ {k} {w} kw)))) kw)
                           , λ {k} m → let (kw , e , x) = B m in kw , e , up x (unfailed nf (≺→≼ {k} {w} kw)) (pass-before x kw nf)

  lst← : ∀ {w} → ¬ Failed w → Listed T′ w → Listed t w
  lst← {w} nf (ks , F , B) = ks , (λ {k} x kw → F (up x (unfailed nf (≺→≼ {k} {w} kw)) (pass-before x kw nf)) kw)
                           , λ {k} m → let (kw , e , y) = B m in kw , e , proj₁ (down y (unfailed nf (≺→≼ {k} {w} kw)))

  few→ : ∀ {k} → Few t k → Few T′ k
  few→ {k} (ks , F) = ks ++ L.map (λ q → q ⊕ [ ix 0 ]) ks ++ L.map (λ q → q ⊕ [ last ]) ks , pick
    where
      pick : ∀ {k′ e} → T′ k′ e → k′ ≺ k → k′ ∈ ks ++ L.map (λ q → q ⊕ [ ix 0 ]) ks ++ L.map (λ q → q ⊕ [ last ]) ks
      pick (y , _) kk with view y
      ... | inj₁ (x , _) = ∈-++⁺ˡ (F x kk)
      ... | inj₂ (q , _ , x , _ , _ , _ , inj₁ (refl , _) , refl , _) =
        ∈-++⁺ʳ ks (∈-++⁺ˡ (∈-map⁺ (λ q → q ⊕ [ ix 0 ]) (F x (≺-trans {q} {q ⊕ [ ix 0 ]} {k} (≺-ext q []) kk))))
      ... | inj₂ (q , _ , x , _ , _ , _ , inj₂ refl , refl , _) =
        ∈-++⁺ʳ ks (∈-++⁺ʳ (L.map (λ q → q ⊕ [ ix 0 ]) ks) (∈-map⁺ (λ q → q ⊕ [ last ]) (F x (≺-trans {q} {q ⊕ [ last ]} {k} (≺-ext q []) kk))))

  few← : ∀ {k} → ¬ Failed k → Few T′ k → Few t k
  few← {k} nf (ks , F) = ks , λ {k′} x kk → F (up x (unfailed nf (≺→≼ {k′} {k} kk)) (pass-before x kk nf)) kk

  few-snoc : ∀ {q e a} → t q e → Few t q → Few t (q ⊕ [ a ])
  few-snoc {q} {a = a} x (ks , F) = q ∷ ks , pick
    where
      pick : ∀ {k e′} → t k e′ → k ≺ (q ⊕ [ a ]) → k ∈ q ∷ ks
      pick {k} x′ kq with below-or-under k q a kq
      ... | inj₂ (_ , _ , refl) = ⊥-elim (flatT x x′)
      ... | inj₁ le with at-or-before {k} {q} le
      ...   | inj₁ refl = here refl
      ...   | inj₂ lt   = there (F x′ lt)

  live← : ∀ {k} → ¬ Failed k → Live T′ k → Live t k
  live← {k} nf lv {c} tc ck = lv (lift (tend tc (unfailed nf (≺→≼ {c} {k} ck)))) ck

  live→ : ∀ {k} → ¬ Failed k → Live t k → Live T′ k
  live→ {k} nf lv (y , _) ck with view y
  ... | inj₁ (tc , _) = lv tc ck
  ... | inj₂ (q , _ , x , nk , _ , b , _ , refl , _) = nf (q , _ , x , nk , ≺-trans {q} {q ⊕ [ b ]} {k} (≺-ext q []) ck)

  -- At a first failing value nothing ends before its cuts.
  end-before : ∀ {q a c} → First q → t c end → c ≺ (q ⊕ [ a ]) → ⊥
  end-before {q} {a} {c} ((_ , x , _) , _) tc cq with below-or-under c q a cq
  ... | inj₂ (_ , _ , refl) = flatT x tc
  ... | inj₁ le with at-or-before {c} {q} le
  ...   | inj₁ refl with InvAt.func I x tc
  ...     | ()
  end-before {q} {a} {c} ((_ , x , _) , _) tc cq | inj₁ le | inj₂ lt with InvAt.quiet I tc x lt
  ...     | _ , () , _

  cut-end : ∀ {q a b} {v : X} → Lab incl b → end ≡ cutEv v b → Plain a → (q ⊕ [ b ]) ≺ (q ⊕ [ a ]) → ⊥
  cut-end     (inj₁ (refl , _)) () _ _
  cut-end {q} (inj₂ refl)       _  pl cq = last-max q pl cq

  live-cut : ∀ {q a} → First q → Plain a → Live T′ (q ⊕ [ a ])
  live-cut {q} {a} f pl (y , _) cq with view y
  ... | inj₁ (tc , _) = end-before f tc cq
  ... | inj₂ (q′ , _ , x′ , nk′ , nf′ , b , lb′ , refl , ee) =
    cut-end {q} lb′ ee pl (subst (λ z → (z ⊕ [ b ]) ≺ (q ⊕ [ a ])) (sym (first f ((_ , x′ , nk′) , nf′))) cq)

  -- With no end, nothing fails, classically.
  no-fail : (∀ {c} → T′ c end → ⊥) → ∀ {q a} → t q (out a) → T (not (kp a)) → ⊥
  no-fail ne x nk = first¬¬ x nk λ { (_ , ((_ , x′ , nk′) , nf′) , _) → ne (lift (stop x′ nk′ nf′)) }

  -- The stop at a position: the cut ending the takeWhile at its first
  -- failure.
  StopAt : Pos → Set
  StopAt c = Σ Pos λ q → Σ X λ a → t q (out a) × T (not (kp a)) × ¬ Failed q × c ≡ q ⊕ [ last ]

  private
    stop? : ∀ {c e} → TakeT c e → Dec (StopAt c)
    stop? (stop x nk nf)       = yes (_ , _ , x , nk , nf , refl)
    stop? (pass x _ _)         = no λ { (_ , _ , x′ , _ , _ , refl) → flatT x′ x }
    stop? (step x _)           = no λ { (_ , _ , x′ , _ , _ , refl) → flatT x′ x }
    stop? (tend x _)           = no λ { (_ , _ , x′ , _ , _ , refl) → flatT x′ x }
    stop? (left x _ _)         = no λ { (_ , _ , x′ , _ , _ , refl) → flatT x′ x }
    stop? (fail {q} x _ _ _)   = no λ { (q′ , _ , _ , _ , _ , e) → ix≢last (⊕-injʳ q q′ e) }
      where
        ix≢last : ix 0 ≡ last → ⊥
        ix≢last ()

    stops : (cs : List Pos) → (∀ {c} → c ∈ cs → Σ (Ev X) (T′ c)) → Dec (Σ Pos λ c → c ∈ cs × StopAt c)
    stops []       _ = no λ { (_ , () , _) }
    stops (c ∷ cs) R with stop? (proj₁ (proj₂ (R (here refl))))
    ... | yes s = yes (c , here refl , s)
    ... | no ns with stops cs (λ m → R (there m))
    ...   | yes (c′ , m , s) = yes (c′ , there m , s)
    ...   | no ns′ = no λ { (_ , here refl , s) → ns s ; (c′ , there m , s) → ns′ (c′ , m , s) }

  -- Whether a source row lies past a failure, from the takeWhile listed
  -- there: past one, the first failure's stop is listed before it.
  failed-at? : ∀ {k e} → Listed T′ k → t k e → Dec (Failed k)
  failed-at? {k} (ks , F , B) x with stops ks (λ m → proj₂ (B m))
  ... | yes (c , m , (q , a , xq , nk , _ , refl)) = yes (q , a , xq , nk , ≺-trans {q} {q ⊕ [ last ]} {k} (≺-ext q []) (proj₁ (B m)))
  ... | no ns = no λ { (q , a , xq , nkq , qk) → first¬¬ xq nkq λ { (q′ , ((_ , x′ , nk′) , nf′) , q′q) →
                  ns (q′ ⊕ [ last ] , F (lift (stop x′ nk′ nf′)) (cut-before x′ x (≼-≺-≺ {q′} {q} {k} q′q qk) last) , (q′ , _ , x′ , nk′ , nf′ , refl)) } }

  -- The first failure before a row past one, from the takeWhile listed
  -- there.
  first-at : ∀ {k e} → Listed T′ k → t k e → Failed k → Σ Pos λ f → First f × (f ⊕ [ last ]) ≺ k
  first-at {k} (ks , F , B) x (q , a , xq , nkq , qk) with stops ks (λ m → proj₂ (B m))
  ... | yes (_ , m , (f , a′ , xf , nkf , nff , refl)) = f , ((a′ , xf , nkf) , nff) , proj₁ (B m)
  ... | no ns = ⊥-elim (first¬¬ xq nkq λ { (q′ , ((_ , x′ , nk′) , nf′) , q′q) →
                  ns (q′ ⊕ [ last ] , F (lift (stop x′ nk′ nf′)) (cut-before x′ x (≼-≺-≺ {q′} {q} {k} q′q qk) last) , (q′ , _ , x′ , nk′ , nf′ , refl)) })

  never-failed : (∀ {c} → T′ c end → ⊥) → ∀ {k} → ¬ Failed k
  never-failed ne (_ , _ , x , nk , _) = no-fail ne x nk

  passes-all : (∀ {c} → T′ c end → ⊥) → ∀ {k e} → t k e → Pass e
  passes-all ne {e = out a} x with bool (kp a)
  ... | inj₁ k  = k
  ... | inj₂ nk = ⊥-elim (no-fail ne x nk)
  passes-all ne {e = skip}  _ = tt
  passes-all ne {e = end}   _ = tt
  passes-all ne {e = pin _} _ = tt

  whole← : (∀ {c} → T′ c end → ⊥) → Whole T′ → Whole t
  whole← ne (ks , F , B) = ks , (λ x → F (up x (never-failed ne) (passes-all ne x)))
                         , λ m → let (e , y) = B m in e , proj₁ (down y (never-failed ne))

  ended← : (∀ {c} → T′ c end → ⊥) → ∀ {c} → t c end → ⊥
  ended← ne tc = ne (up tc (never-failed ne) tt)

  -- Before a first failing value's cut: its source's rows before it, and
  -- the value kept, before the end.
  src-before : ∀ {q r e e′ a} → First q → T′ r e → t r e′ → r ≺ (q ⊕ [ a ]) → r ≺ q
  src-before {q} {r} {a = a} f@((_ , x , _) , _) y x′ rq with below-or-under r q a rq
  ... | inj₂ (_ , _ , refl) = ⊥-elim (flatT x x′)
  ... | inj₁ le with at-or-before {r} {q} le
  ...   | inj₁ refl = ⊥-elim (none-at f (proj₁ y))
  ...   | inj₂ lt   = lt

  cutL : Pos → Label → List Pos
  cutL q (ix _)  = []
  cutL q (sub _) = []
  cutL q last    = ixs incl q

  lst-cut : ∀ {q a} → First q → Listed t q → Lab incl a → Listed T′ (q ⊕ [ a ])
  lst-cut {q} {a} f@((_ , x , nk) , nf) L lb with lst→ nf L
  ... | ks , F , B = ks ++ cutL q a , F′ , B′
    where
      cut-in : ∀ {a′} → Lab incl a → Lab incl a′ → (q ⊕ [ a′ ]) ≺ (q ⊕ [ a ]) → (q ⊕ [ a′ ]) ∈ cutL q a
      cut-in (inj₁ (refl , _)) (inj₁ (refl , _)) rq = ⊥-elim (≺-irrefl {q ⊕ [ ix 0 ]} rq)
      cut-in (inj₁ (refl , _)) (inj₂ refl)       rq = ⊥-elim (last-max q plain-ix rq)
      cut-in (inj₂ refl)       (inj₁ (refl , i)) rq = ixs-in q i
      cut-in (inj₂ refl)       (inj₂ refl)       rq = ⊥-elim (≺-irrefl {q ⊕ [ last ]} rq)

      F′ : ∀ {r e} → T′ r e → r ≺ (q ⊕ [ a ]) → r ∈ ks ++ cutL q a
      F′ y rq with view (proj₁ y)
      ... | inj₁ (x′ , _) = ∈-++⁺ˡ (F y (src-before f y x′ rq))
      ... | inj₂ (q′ , _ , x′ , nk′ , nf′ , b , lb′ , refl , _) with first f ((_ , x′ , nk′) , nf′)
      ...   | refl = ∈-++⁺ʳ ks (cut-in lb lb′ rq)

      cut-row-in : ∀ {r} → Lab incl a → r ∈ cutL q a → r ≺ (q ⊕ [ a ]) × Σ _ (T′ r)
      cut-row-in (inj₁ (refl , _)) ()
      cut-row-in (inj₂ refl) m with ixs-row q m
      ... | refl , inc = ix-last q , _ , lift (fail x nk nf inc)

      B′ : ∀ {r} → r ∈ ks ++ cutL q a → r ≺ (q ⊕ [ a ]) × Σ _ (T′ r)
      B′ {r} m with ∈-++⁻ ks m
      ... | inj₁ m′ = let (rq , y) = B m′ in ≺-trans {r} {q} {q ⊕ [ a ]} rq (≺-ext q []) , y
      ... | inj₂ m′ = cut-row-in lb m′

  -- The first failing value among those listed before `w`, or none.
  private
    Earliest : Pos → List Pos → Set
    Earliest w ks = (∀ {k} → k ∈ ks → Fails k → ⊥) ⊎ Σ Pos λ f → Fails f × f ≺ w × (∀ {k} → k ∈ ks → Fails k → f ≼ k)

    earliest : ∀ {w} ks → (∀ {k} → k ∈ ks → k ≺ w × Σ (Ev X) (t k)) → Earliest w ks
    earliest []       B = inj₁ λ ()
    earliest (k ∷ ks) B with earliest ks (λ m → B (there m)) | fails? (proj₂ (proj₂ (B (here refl))))
    ... | inj₁ none | inj₂ nk = inj₁ λ { (here refl) fk → nk fk ; (there m) → none m }
    ... | inj₂ (f , ff , fw , mn) | inj₂ nk = inj₂ (f , ff , fw , λ { (here refl) fk → ⊥-elim (nk fk) ; (there m) → mn m })
    ... | inj₁ none | inj₁ fk = inj₂ (k , fk , proj₁ (B (here refl)) , λ { (here refl) _ → ≼-refl {k} ; (there m) fk′ → ⊥-elim (none m fk′) })
    ... | inj₂ (f , ff , fw , mn) | inj₁ fk with ≼-or-≻ f k
    ...   | inj₁ fk′ = inj₂ (f , ff , fw , λ { (here refl) _ → fk′ ; (there m) → mn m })
    ...   | inj₂ kf  = inj₂ (k , fk , proj₁ (B (here refl)) , λ { (here refl) _ → ≼-refl {k} ; {k′} (there m) fk″ → ≼-trans {k} {f} {k′} (≺→≼ {k} {f} kf) (mn m fk″) })

  search : ∀ {l} → Listed t l → ¬ Failed l ⊎ Σ Pos λ f → First f × f ≺ l
  search {l} (ks , F , B) with earliest ks B
  ... | inj₁ none = inj₁ λ { (q , a , x , nk , ql) → none (F x ql) (a , x , nk) }
  ... | inj₂ (f , ff , fl , mn) = inj₂ (f , (ff , λ { (q , a , x , nk , qf) → mn (F x (≺-trans {q} {f} {l} qf fl)) (a , x , nk) qf }) , fl)
