{-# OPTIONS --guardedness #-}

-- A TAKEWHILE CARRIES what its source did.  Before the first failing
-- value the two runs are their sources' rows, carried as the source
-- carried them; the failing value itself is carried by the elaborated
-- run's failing value, shown alike, so the cuts one label under each —
-- the value kept (`ix 0`) and the end (`last`) — are paired by growing
-- the map one label under the pair.  A mark passes, so only values fail.
--
-- A row of the elaborated run is placed from its source's placing: near
-- a carrier at or before it, or near one listed up to, where the listing
-- decides the first failing value between them, whose end is then the
-- nearer carrier.  A run with no end has no failure, since the first one
-- ends it, so its rows are its source's.
module simultaneous.CarryTake where

open import Data.Bool using (Bool; T; not; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_; lose)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-cartesianProduct⁺)
open import Data.List.Relation.Unary.Any using (here; there; any?; satisfied)
open import Data.Bool.Properties using (T?)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (takeWhile)
open import denotation.Position using (Pos; Label; ix; sub; last; _⊕_; root; _≟ᵖ_; _<ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; enter; Truncate; Reach; Few; _≺_; _≼_;
  module TakeWhile; module Op; approx)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split; ≼-≺-≺; ≺-≼-≺; ≼-antisym;
  ≺-ext; T-not; reach-few; few-ind; entered-reach)
open import denotation.Laws.Worlds using (InvAt; W⁼; inW; step; Plain; plain-ix; plain-last; full; _⊑_; ⊑-refl; ⊑-trans; ⊑-≼;
  ⊑-snoc; ⊑-snoc⁺; ⊕-identityʳ; ⊕-assoc; ⊕-injʳ; inside-⊑; ⊑-inside; Disj)
open import denotation.Laws.Count using (em)
open import denotation.Laws.ShowsOps using (bool)
open import denotation.Laws using (inv-approx)
open import adequacy.SubOne using (take-reach; below-or-under; at-or-before)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Readings using (instantOf; parent; parent-snoc)
open import simultaneous.Instants using (_≺ⁱ_; triⁱ; irrⁱ; transⁱ; instant-≺)
open import simultaneous.Carry using (PMap; _⊆ᴹ_; _∪ᴹ_; Emb; CarryAt; Carry; carry; Bare; Within; Near; Whole; Home; module Mono; emb-at; emb-pairs; apart; instant-⊕; sub-listed; few-sub; match-val; carried-val; listed↓; IntoAt; Grown; joins-grow)
open import simultaneous.CarryLeaves using (module OneAt; last-max; ix-last)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; passes)

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

lab? : ∀ incl b → Dec (Lab incl b)
lab? incl last         = yes (inj₂ refl)
lab? incl (sub _)      = no λ { (inj₁ (() , _)) ; (inj₂ ()) }
lab? incl (ix (suc _)) = no λ { (inj₁ (() , _)) ; (inj₂ ()) }
lab? incl (ix zero) with T? incl
... | yes i = yes (inj₁ (refl , i))
... | no ni = no λ { (inj₁ (_ , i)) → ni i ; (inj₂ ()) }

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

  -- Past a failure too: a listing decides each failure before it, so
  -- each listed source row decides whether it is kept, and the first
  -- failure's cuts are found under the rows listed.
  private
    fails-at? : ∀ {w} → Listed t w → ∀ c → c ≺ w → Dec (Fails c)
    fails-at? (ks , F , B) c cw with any? (c ≟ᵖ_) ks
    ... | no ¬m = no λ { (_ , x , _) → ¬m (F x cw) }
    ... | yes m with fails? (proj₂ (proj₂ (B m)))
    ...   | inj₁ f  = yes f
    ...   | inj₂ nf = no nf

    fail-before? : ∀ {w} → Listed t w → ∀ k → k ≼ w → ∀ c → Dec (c ≺ k × Fails c)
    fail-before? {w} Lw k kw c with T? (c <ᵖ k)
    ... | no nck = no λ { (ck , _) → nck ck }
    ... | yes ck with fails-at? Lw c (≺-≼-≺ {c} {k} {w} ck kw)
    ...   | yes f = yes (ck , f)
    ...   | no nf = no λ { (_ , f) → nf f }

    failed? : ∀ {w} → Listed t w → ∀ k → k ≼ w → Dec (Failed k)
    failed? {w} Lw@(ks , F , _) k kw with any? (fail-before? Lw k kw) ks
    ... | yes a = let (c , ck , a′ , x , nk) = satisfied a in yes (c , a′ , x , nk , ck)
    ... | no na = no λ { (q , a , x , nk , qk) → na (lose (F x (≺-≼-≺ {q} {k} {w} qk kw)) (qk , a , x , nk)) }

    -- Past a failure, only a pin whose connect is unfailed is kept.
    past-fail : ∀ {c e e′} → t c e → Failed c → TakeT c e′ → Σ Pos λ r → t c (pin r) × ¬ Failed r
    past-fail x fd (pass _ _ nf)    = ⊥-elim (nf fd)
    past-fail x fd (step _ nf)      = ⊥-elim (nf fd)
    past-fail x fd (tend _ nf)      = ⊥-elim (nf fd)
    past-fail x fd (left x′ nfr _)  = _ , x′ , nfr
    past-fail x fd (fail x′ _ _ _)  = ⊥-elim (flatT x′ x)
    past-fail x fd (stop x′ _ _)    = ⊥-elim (flatT x′ x)

    kept-pin : ∀ {c r e′} → t c (pin r) → Failed c → Failed r → TakeT c e′ → ⊥
    kept-pin x fd fr y with past-fail x fd y
    ... | _ , x′ , nfr with InvAt.func I x x′
    ...   | refl = nfr fr

    no-pin : ∀ {c e e′} → t c e → Unpinned e → Failed c → TakeT c e′ → ⊥
    no-pin x un fd y with past-fail x fd y
    ... | _ , x′ , _ with InvAt.func I x x′
    no-pin x () fd y | _ , x′ , _ | refl

    kept? : ∀ {w c} e → Listed t w → t c e → c ≺ w → Failed c → Dec (Σ _ (T′ c))
    kept? {w} {c} (pin r) Lw x cw fd with failed? Lw r (≼-trans {r} {c} {w} (⊑-≼ (inside-⊑ r c (ins x))) (≺→≼ {c} {w} cw))
    ... | no nfr = yes (pin r , lift (left x nfr (ins x)))
    ... | yes fr = no λ { (_ , y , _) → kept-pin x fd fr y }
    kept? (out _) Lw x cw fd = no λ { (_ , y , _) → no-pin x tt fd y }
    kept? skip    Lw x cw fd = no λ { (_ , y , _) → no-pin x tt fd y }
    kept? end     Lw x cw fd = no λ { (_ , y , _) → no-pin x tt fd y }

    row-src? : ∀ {w c e} → Listed t w → t c e → c ≺ w → Dec (Σ _ (T′ c))
    row-src? {w} {c} Lw x cw with failed? Lw c (≺→≼ {c} {w} cw)
    ... | yes fd = kept? _ Lw x cw fd
    ... | no nf with fails? x
    ...   | inj₂ nfs = yes (_ , up x nf (pass-of nfs x))
    ...   | inj₁ f   = no λ { (_ , y) → pass-fails (proj₁ (down y nf)) (proj₂ (down y nf)) f }

    cutAt : Pos × Label → Pos
    cutAt (q , b) = q ⊕ [ b ]

    labs : List Label
    labs = ix 0 ∷ last ∷ []

  lst-any : ∀ {w} → Listed t w → Listed T′ w
  lst-any {w} Lw@(ks , F , B) = filter src? ks ++ L.map cutAt (filter cut? (L.cartesianProduct ks labs)) , F′ , B′
    where
      src? : ∀ c → Dec (c ≺ w × Σ _ (T′ c) × Σ _ (t c))
      src? c with T? (c <ᵖ w)
      ... | no ncw = no λ { (cw , _) → ncw cw }
      ... | yes cw with any? (c ≟ᵖ_) ks
      ...   | no ¬m = no λ { (_ , _ , (_ , x)) → ¬m (F x cw) }
      ...   | yes m with row-src? Lw (proj₂ (proj₂ (B m))) cw
      ...     | yes r  = yes (cw , r , proj₂ (B m))
      ...     | no ¬r = no λ { (_ , r , _) → ¬r r }

      cut? : ∀ qb → Dec (First (proj₁ qb) × Lab incl (proj₂ qb) × cutAt qb ≺ w)
      cut? (q , b) with T? ((q ⊕ [ b ]) <ᵖ w)
      ... | no nw = no λ { (_ , _ , qw) → nw qw }
      ... | yes qbw with lab? incl b
      ...   | no nl = no λ { (_ , l , _) → nl l }
      ...   | yes l with fails-at? Lw q (≺-trans {q} {q ⊕ [ b ]} {w} (≺-ext q []) qbw)
                       | failed? Lw q (≺→≼ {q} {w} (≺-trans {q} {q ⊕ [ b ]} {w} (≺-ext q []) qbw))
      ...     | no nf′ | _     = no λ { ((f , _) , _) → nf′ f }
      ...     | yes _  | yes fd = no λ { ((_ , nf) , _) → nf fd }
      ...     | yes f  | no nf  = yes ((f , nf) , l , qbw)

      src-in : ∀ {r e e′} → T′ r e → t r e′ → r ≺ w → r ∈ filter src? ks ++ L.map cutAt (filter cut? (L.cartesianProduct ks labs))
      src-in y x rw = ∈-++⁺ˡ (∈-filter⁺ src? (F x rw) (rw , (_ , y) , (_ , x)))

      cut-in : ∀ {q a b} → t q (out a) → T (not (kp a)) → ¬ Failed q → Lab incl b → b ∈ labs → (q ⊕ [ b ]) ≺ w
             → (q ⊕ [ b ]) ∈ filter src? ks ++ L.map cutAt (filter cut? (L.cartesianProduct ks labs))
      cut-in {q} {b = b} x nk nf l bl qw =
        ∈-++⁺ʳ (filter src? ks) (∈-map⁺ cutAt (∈-filter⁺ cut? (∈-cartesianProduct⁺ (F x (≺-trans {q} {q ⊕ [ b ]} {w} (≺-ext q []) qw)) bl)
          (((_ , x , nk) , nf) , l , qw)))

      F′ : ∀ {r e} → T′ r e → r ≺ w → r ∈ filter src? ks ++ L.map cutAt (filter cut? (L.cartesianProduct ks labs))
      F′ y@(pass x _ _ , _)     rw = src-in y x rw
      F′ y@(step x _ , _)       rw = src-in y x rw
      F′ y@(tend x _ , _)       rw = src-in y x rw
      F′ y@(left x _ _ , _)     rw = src-in y x rw
      F′ (fail x nk nf inc , _) rw = cut-in x nk nf (inj₁ (refl , inc)) (here refl) rw
      F′ (stop x nk nf , _)     rw = cut-in x nk nf (inj₂ refl) (there (here refl)) rw

      B′ : ∀ {r} → r ∈ filter src? ks ++ L.map cutAt (filter cut? (L.cartesianProduct ks labs)) → r ≺ w × Σ _ (T′ r)
      B′ m with ∈-++⁻ (filter src? ks) m
      ... | inj₁ ms = let (rw , r , _) = proj₂ (∈-filter⁻ src? {xs = ks} ms) in rw , r
      ... | inj₂ mc with ∈-map⁻ cutAt mc
      ...   | (q , b) , mq , refl with proj₂ (∈-filter⁻ cut? {xs = L.cartesianProduct ks labs} mq)
      ...     | ((a , x , nk) , nf) , l , qbw = qbw , cutEv a b , cut-row x nk nf l

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

------------------------------------------------------------------------
-- The carrier

private
  -- A row not shown is kept by the elaborated takeWhile.
  hid : ∀ {A : Set} {kp : A → Bool} (e′ : Ev (IE A)) → ¬ Shown (One valuesOf) e′ → Keeps (passes kp) e′
  hid (out (instEmit (value b) _)) h = ⊥-elim (h (b , refl))
  hid (out (instEmit (mark _) _))  _ = tt
  hid skip    _ = tt
  hid end     _ = tt
  hid (pin _) _ = tt

  -- A row and its carrier are kept alike.
  keeps→ : ∀ {A : Set} {kp : A → Bool} {e e′} → Match Every (One valuesOf) (Reads valuesOf) e e′ → Keeps kp e → Keeps (passes kp) e′
  keeps→ {e = out a} mt p with carried-val mt
  ... | _ , refl = p
  keeps→ {e = end} (cr , _) _ with cr tt
  ... | refl = tt
  keeps→ {kp = kp} {e = skip}  {e′} (_ , ns) _ = hid {kp = kp} e′ (ns λ ())
  keeps→ {kp = kp} {e = pin _} {e′} (_ , ns) _ = hid {kp = kp} e′ (ns λ ())

  keeps← : ∀ {A : Set} {kp : A → Bool} {e e′} → Match Every (One valuesOf) (Reads valuesOf) e e′ → Keeps (passes kp) e′ → Keeps kp e
  keeps← {e = out a} mt p with carried-val mt
  ... | _ , refl = p
  keeps← {e = end}   _ _ = tt
  keeps← {e = skip}  _ _ = tt
  keeps← {e = pin _} _ _ = tt

  within-∘ : ∀ {H : Pos → Set} {M₀ M M′ : PMap} {p} → Within H M₀ M p → (∀ {x y} → M′ x y → M x y ⊎ W⁼ H p x) → Within H M₀ M′ p
  within-∘ wi wi′ m′ with wi′ m′
  ... | inj₁ m = wi m
  ... | inj₂ w = inj₂ w

module Core {A : Set} (incl : Bool) (keep : A → Bool) {M : PMap} {HP HE LP H₁ H₂ : Pos → Set}
  {t : EmissionSet A} {u : EmissionSet (IE A)} {s s′ : Pos} (hm : Emb M)
  (rcT : ∀ {q e} → t q e → Reach t q e) (rcU : ∀ {q e} → u q e → Reach u q e)
  (It : InvAt H₁ s t) (Iu : InvAt H₂ s′ u) (br : Bare M t) (lp↓ : ∀ {x y} → x ≼ y → LP y → LP x)
  (c : CarryAt valuesOf M HP HE LP t u s s′) where
  private
    module C = CarryAt c
  module P = Side incl keep t (λ {y} {e} → rcT {y} {e}) It
  module Q = Side incl (passes keep) u (λ {y} {e} → rcU {y} {e}) Iu

  private
    flatP : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥
    flatP = InvAt.flat It

    img-mono : ∀ {k k′ l l′} → C.Img k l → C.Img k′ l′ → k ≺ k′ → l ≺ l′
    img-mono = Mono.img-mono hm (λ {y} {e} {l} {ys} {e′} → InvAt.flat It {y} {e} {l} {ys} {e′}) c

    -- A carrier with no failure before it carries a row with none.
    e1 : ∀ {k l} → C.Img k l → ¬ P.Failed k → ¬ Q.Failed l
    e1 i nf (q , instEmit (mark _) _ , _ , () , _)
    e1 {k} {l} i nf (q , instEmit (value b) n , uq , nb , ql) with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | k′ , i′ , e₀ , tk′ , mt with match-val mt
    ...   | refl with ≼-or-≻ k k′
    ...     | inj₂ k′k = nf (k′ , b , tk′ , nb , k′k)
    ...     | inj₁ kk′ with ≼-split {k} {k′} kk′
    ...       | inj₁ k≺k′ = ≺-absurd {l} {q} (img-mono i i′ k≺k′) ql
    ...       | inj₂ refl = ≺-irrefl {q} (subst (q ≺_) (C.img-fun i i′) ql)

    -- A row with no failure before its carrier has none before it.
    e2 : ∀ {k l} → C.Img k l → ¬ Q.Failed l → ¬ P.Failed k
    e2 {k} {l} i nf (q , b , tq , nb , qk) = C.img¬¬ tq tt (P.live-out tq) (P.few-out tq) λ { (inj₁ (l′ , i′ , e′ , ul′ , mt)) → fl i′ ul′ mt ; (inj₂ ()) }
      where
        fl : ∀ {l′ e′} → C.Img q l′ → u l′ e′ → Match Every (One valuesOf) (Reads valuesOf) (out b) e′ → ⊥
        fl i′ ul′ mt with carried-val mt
        ... | _ , refl = nf (_ , _ , ul′ , nb , img-mono i′ i qk)

    -- A row whose carrier does not fail does not fail.
    unfails← : ∀ {k l} → C.Img k l → ¬ Q.Fails l → ¬ P.Fails k
    unfails← {k} {l} i nq (b , tk , nb) = C.img¬¬ tk tt (P.live-out tk) (P.few-out tk) λ { (inj₁ (l′ , i′ , e′ , ul′ , mt)) → fl i′ ul′ mt ; (inj₂ ()) }
      where
        fl : ∀ {l′ e′} → C.Img k l′ → u l′ e′ → Match Every (One valuesOf) (Reads valuesOf) (out b) e′ → ⊥
        fl i′ ul′ mt with carried-val mt
        ... | _ , refl = nq (_ , subst (λ z → u z _) (C.img-fun i′ i) ul′ , nb)

    -- A carrier of a row that does not fail does not fail.
    unfails→ : ∀ {k l} → C.Img k l → ¬ P.Fails k → ¬ Q.Fails l
    unfails→ i nfs (instEmit (mark _) _ , _ , ())
    unfails→ {k} {l} i nfs (instEmit (value b) n , ul , nb) with C.shown ul (b , refl) (Q.live-out ul) (Q.few-out ul)
    ... | k′ , i′ , e₀ , tk′ , mt with match-val mt
    ...   | refl with ≼-or-≻ k k′
    ...     | inj₂ k′k = ≺-irrefl {l} (img-mono i′ i k′k)
    ...     | inj₁ kk′ with ≼-split {k} {k′} kk′
    ...       | inj₁ lt   = ≺-irrefl {l} (img-mono i i′ lt)
    ...       | inj₂ refl = nfs (b , tk′ , nb)

  -- THE CUT UNDER THE FIRST FAILING VALUE, on the same label under its
  -- carrier, the failing value of the elaborated run.
  data Cut (k l : Pos) : Set where
    cut : ∀ {k₀ l₀ a b n} → t k₀ (out b) → T (not (keep b)) → ¬ P.Failed k₀ → C.Img k₀ l₀
        → u l₀ (out (instEmit (value b) n)) → Lab incl a → k ≡ k₀ ⊕ [ a ] → l ≡ l₀ ⊕ [ a ] → Cut k l

  Img′ : Pos → Pos → Set
  Img′ k l = (C.Img k l × ¬ P.Failed k × ¬ P.Fails k) ⊎ Cut k l

  M′ : PMap
  M′ = M ∪ᴹ Cut

  -- WHAT THE TAKEWHILE PUTS INTO ITS INSTANT: its source's, on a row of
  -- its source; and a row before the first failing value, on the end cut
  -- under that value's carrier.
  PB′ : Pos → Pos → Set
  PB′ k m = (Σ (Ev (IE A)) (u m) × C.PB k m)
          ⊎ Σ Pos λ f → Σ Pos λ k₀ → Q.First f × C.Img k₀ f × m ≡ f ⊕ [ last ] × P.First k₀ × k ≺ k₀ × Σ (Ev A) (t k)

  private
    firstQ : ∀ {k₀ l₀ b n} → t k₀ (out b) → T (not (keep b)) → ¬ P.Failed k₀ → C.Img k₀ l₀ → u l₀ (out (instEmit (value b) n)) → Q.First l₀
    firstQ tk nk nf i ul = (_ , ul , nk) , e1 i nf

    -- The cut under a first failing value of `u`, and what it carries.
    cut-shown : ∀ {q y a} → u q (out y) → T (not (passes keep y)) → ¬ Q.Failed q → Lab incl a
              → Σ Pos λ k → Img′ k (q ⊕ [ a ]) × Σ (Ev A) λ e₀ → P.T′ k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ (cutEv y a)
    cut-shown {y = instEmit (mark _) _} _ () _ _
    cut-shown {q} {instEmit (value b) n} {a} uq nb nfq lb with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | k₀ , i , e₀ , tk , mt with match-val mt
    ...   | refl = k₀ ⊕ [ a ] , inj₂ (cut tk nb (e2 i nfq) i uq lb refl refl) , cutEv b a , P.cut-row tk nb (e2 i nfq) lb , cut-match lb

    ----------------------------------------------------------------------
    -- The map grown: two cuts pair under one failing value

    Kc : ∀ {x y} → Cut x y → PMap
    Kc (cut {k₀} {l₀} _ _ _ _ _ _ _ _) = M ∪ᴹ OneAt.N k₀ l₀

    embK : ∀ {x y} (c′ : Cut x y) → Emb (Kc c′)
    embK (cut {k₀} {l₀} tk _ _ i _ _ _ _) with C.ext i
    ... | y₀ , m₀ , pp = emb-at hm (λ m kx → br tk m kx) m₀ pp (OneAt.embN k₀ l₀) λ { (a , _ , refl , refl) → a , [] , a , [] , refl , refl }

    selfK : ∀ {x y} (c′ : Cut x y) → Kc c′ x y
    selfK (cut _ _ _ _ _ lb refl refl) = inj₂ (_ , lab-plain lb , refl , refl)

    otherK : ∀ {x y x′ y′} (c′ : Cut x y) → M′ x′ y′ → Kc c′ x′ y′
    otherK (cut _ _ _ _ _ _ _ _) (inj₁ m) = inj₁ m
    otherK (cut tk nk nf i _ _ _ _) (inj₂ (cut tk′ nk′ nf′ i′ _ lb′ refl refl)) with P.first ((_ , tk , nk) , nf) ((_ , tk′ , nk′) , nf′)
    ... | refl with C.img-fun i i′
    ...   | refl = inj₂ (_ , lab-plain lb′ , refl , refl)

  emb′ : Emb M′
  emb′ = emb-pairs pair
    where
      pair : ∀ {x y x′ y′} → M′ x y → M′ x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′
      pair (inj₁ m) (inj₁ m′) = M , hm , m , m′
      pair (inj₂ c′) n        = Kc c′ , embK c′ , selfK c′ , otherK c′ n
      pair (inj₁ m) (inj₂ c′) = Kc c′ , embK c′ , otherK c′ (inj₁ m) , selfK c′

  -- A cut lies one label under a point of the map, holding no hot row.
  grown′ : Disj H₁ s → ∀ {x y} → M′ x y → M x y ⊎ Grown M H₁ x y
  grown′ _  (inj₁ m) = inj₁ m
  grown′ dj (inj₂ (cut tk _ _ i _ _ refl refl)) with C.ext i
  ... | y₀ , m₀ , pp = inj₂ (_ , y₀ , _ , m₀ , ⊑-trans pp (⊑-snoc⁺ _) , refl , λ hq kq → dj hq (InvAt.world It tk) (⊑-inside kq))

  within′ : ∀ {x y} → M′ x y → M x y ⊎ W⁼ H₁ s x
  within′ (inj₁ m) = inj₁ m
  within′ (inj₂ (cut tk _ _ _ _ lb refl _)) = inj₂ (inW (step (inW (InvAt.world It tk)) (lab-plain lb)))

  private
    bare-M : ∀ {k e x y} → P.TakeT k e → M x y → k ⊑ x → x ≡ k
    bare-M r m kx with P.view r
    ... | inj₁ (tk , _) = br tk m kx
    ... | inj₂ (q , _ , tq , _ , _ , a , _ , refl , _) with br tq m (⊑-trans (⊑-snoc⁺ q) kx)
    ...   | refl = ⊥-elim (⊑-≼ kx (≺-ext q []))

    bare-cut : ∀ {k e x y} → P.TakeT k e → Cut x y → k ⊑ x → x ≡ k
    bare-cut {k} r (cut {k₀} tk₀ nk nf _ _ _ refl _) kx with ⊑-snoc k₀ kx
    ... | inj₂ e = sym e
    ... | inj₁ kk with P.view r
    ...   | inj₂ (q , _ , tq , _ , _ , a′ , _ , refl , _) with kk
    ...     | zs , refl = ⊥-elim (flatP tq (subst (λ z → t z _) (⊕-assoc q [ a′ ] zs) tk₀))
    bare-cut {k} r (cut {k₀} tk₀ nk nf _ _ _ refl _) kx | inj₁ kk | inj₁ (tk , _) with kk
    ... | [] , refl    = ⊥-elim (P.none-at ((_ , tk₀ , nk) , nf) (subst (λ z → P.TakeT z _) (sym (⊕-identityʳ k)) r))
    ... | _ ∷ _ , refl = ⊥-elim (flatP tk tk₀)

  bare′ : Bare M′ P.T′
  bare′ r (inj₁ m)  kx = bare-M (proj₁ r) m kx
  bare′ r (inj₂ c′) kx = bare-cut (proj₁ r) c′ kx

  private
    ----------------------------------------------------------------------
    -- The fields

    ext′ : ∀ {k l} → Img′ k l → Σ Pos λ y → M′ k y × y ⊑ l
    ext′ (inj₁ (i , _)) = let (y , m , yl) = C.ext i in y , inj₁ m , yl
    ext′ (inj₂ c′)      = _ , inj₂ c′ , ⊑-refl _

    img-row′ : ∀ {k l} → Img′ k l → ¬ ¬ Σ (Ev A) λ e → P.T′ k e × Unpinned e
    img-row′ (inj₁ (i , nf , nfs)) n = C.img-row i λ { (e , tk , un) → n (e , P.up tk nf (P.pass-of nfs tk) , un) }
    img-row′ (inj₂ (cut tk nk nf _ _ lb refl _)) n = n (_ , P.cut-row tk nk nf lb , cut-unp lb)

    img-fun′ : ∀ {k l l′} → Img′ k l → Img′ k l′ → l ≡ l′
    img-fun′ (inj₁ (i , _)) (inj₁ (i′ , _)) = C.img-fun i i′
    img-fun′ (inj₁ (i , _)) (inj₂ (cut tk _ _ _ _ _ refl _)) = ⊥-elim (C.img-row i λ { (_ , tk′ , _) → flatP tk tk′ })
    img-fun′ (inj₂ (cut tk _ _ _ _ _ refl _)) (inj₁ (i , _)) = ⊥-elim (C.img-row i λ { (_ , tk′ , _) → flatP tk tk′ })
    img-fun′ (inj₂ (cut {k₀} tk nk nf i _ _ refl refl)) (inj₂ (cut tk′ nk′ nf′ i′ _ _ ek refl))
      with P.first ((_ , tk , nk) , nf) ((_ , tk′ , nk′) , nf′)
    ... | refl with ⊕-injʳ k₀ k₀ ek | C.img-fun i i′
    ...   | refl | refl = refl

    few′ : ∀ {k l} → Img′ k l → Few P.T′ k
    few′ (inj₁ (i , _))                   = P.few→ (C.few i)
    few′ (inj₂ (cut tk _ _ i _ _ refl _)) = P.few→ (P.few-snoc tk (C.few i))

    live′ : ∀ {k l} → Img′ k l → Live P.T′ k → Live Q.T′ l
    live′ (inj₁ (i , nf , _)) lv = Q.live→ (e1 i nf) (C.live i (P.live← nf lv))
    live′ (inj₂ (cut tk nk nf i ul lb refl refl)) _ = Q.live-cut (firstQ tk nk nf i ul) (lab-plain lb)

    bk′ : Pos → List Pos
    bk′ l = C.bk l ++ L.map (λ k → k ⊕ [ ix 0 ]) (C.bk (parent l)) ++ L.map (λ k → k ⊕ [ last ]) (C.bk (parent l))

    in-bk′ : ∀ {k l} → Img′ k l → k ∈ bk′ l
    in-bk′ (inj₁ (i , _)) = ∈-++⁺ˡ (C.in-bk i)
    in-bk′ (inj₂ (cut {k₀} {l₀} _ _ _ i _ (inj₁ (refl , _)) refl refl)) =
      ∈-++⁺ʳ (C.bk (l₀ ⊕ [ ix 0 ])) (∈-++⁺ˡ (∈-map⁺ (λ k → k ⊕ [ ix 0 ]) (subst (λ z → k₀ ∈ C.bk z) (sym (parent-snoc l₀ (ix 0))) (C.in-bk i))))
    in-bk′ (inj₂ (cut {k₀} {l₀} _ _ _ i _ (inj₂ refl) refl refl)) =
      ∈-++⁺ʳ (C.bk (l₀ ⊕ [ last ])) (∈-++⁺ʳ (L.map (λ k → k ⊕ [ ix 0 ]) (C.bk (parent (l₀ ⊕ [ last ]))))
        (∈-map⁺ (λ k → k ⊕ [ last ]) (subst (λ z → k₀ ∈ C.bk z) (sym (parent-snoc l₀ last)) (C.in-bk i))))

    -- A skip carried into its instant keeps a carrier: its own, before
    -- the failure, or the end cut under the first failing value.
    cut-into : ∀ {k f} → t k skip → ¬ P.Failed k → Q.First f → Listed u f
             → Σ Pos λ m → Σ (Ev (IE A)) (Q.T′ m) × Listed Q.T′ m × PB′ k m
    cut-into tk nfk ((instEmit (mark _) _ , _ , ()) , _) L
    cut-into {k} {f} tk nfk ff@((instEmit (value b) n , uf , ny) , nff) L with C.shown uf (b , refl) (Q.live-out uf) (Q.few-out uf)
    ... | k₀ , i₀ , e₀ , tk₀ , mt with match-val mt
    ...   | refl = f ⊕ [ last ] , (end , Q.cut-row uf ny nff (inj₂ refl)) , Q.lst-cut ff L (inj₂ refl)
                 , inj₂ (f , k₀ , ff , i₀ , refl , ((b , tk₀ , ny) , e2 i₀ nff) , before , (skip , tk))
      where
        before : k ≺ k₀
        before with ≼-or-≻ k k₀
        ... | inj₂ k₀k = ⊥-elim (nfk (k₀ , b , tk₀ , ny , k₀k))
        ... | inj₁ kk₀ with ≼-split {k} {k₀} kk₀
        ...   | inj₁ lt   = lt
        ...   | inj₂ refl with InvAt.func It tk tk₀
        ...     | ()

    into-row : ∀ {k l e} → t k skip → ¬ P.Failed k → u l e → Listed u l → C.PB k l
             → Σ Pos λ m → Σ (Ev (IE A)) (Q.T′ m) × Listed Q.T′ m × PB′ k m
    into-row {l = l} tk nfk ul L pb with Q.search L | Q.fails? ul
    ... | inj₁ nfl | inj₂ nfsl       = l , (_ , Q.up ul nfl (Q.pass-of nfsl ul)) , Q.lst→ nfl L , inj₁ ((_ , ul) , pb)
    ... | inj₁ nfl | inj₁ (_ , ul′ , ny) = cut-into tk nfk ((_ , ul′ , ny) , nfl) L
    ... | inj₂ (f , ff , fl) | _     = cut-into tk nfk ff (sub-listed L fl)

    into-at : ∀ {k} → t k skip → ¬ P.Failed k → IntoAt C.Img u C.PB HP s k → IntoAt Img′ Q.T′ PB′ HP s k
    into-at {k} tk nf ((l , (_ , ul) , L , pb) , h) = into-row tk nf ul L pb , at h
      where
        at : _ → _
        at (inj₁ e) = inj₁ e
        at (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (e₀ , ul₀) , L₀))) =
          let nf₀ = P.unfailed nf (≺→≼ {k₀} {k} kk)
              nfs₀ : ¬ P.Fails k₀
              nfs₀ = λ { (a , x , nk) → nf (k₀ , a , x , nk , kk) }
          in inj₂ (inj₁ (k₀ , l₀ , inj₁ (i , nf₀ , nfs₀) , kk , ek
                        , (e₀ , Q.up ul₀ (e1 i nf₀) (Q.pass-of (unfails→ i nfs₀) ul₀)) , Q.lst→ (e1 i nf₀) L₀))
        at (inj₂ (inj₂ h)) = inj₂ (inj₂ h)

    src-img : ∀ {k e} → t k e → Keeps keep e → ¬ P.Failed k → Unpinned e → Live P.T′ k → Listed P.T′ k → LP k
            → (Σ Pos λ l → Img′ k l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Listed Q.T′ l × Match Every (One valuesOf) (Reads valuesOf) e e′)
              ⊎ (e ≡ skip × IntoAt Img′ Q.T′ PB′ HP s k)
    src-img tk pe nf un lv L lp with C.img tk un (P.live← nf lv) (P.lst← nf L) lp
    ... | inj₁ (l , i , e′ , ul , Lu , mt) =
      inj₁ (l , inj₁ (i , nf , P.pass-fails tk pe) , e′ , Q.up ul (e1 i nf) (keeps→ {kp = keep} mt pe) , Q.lst→ (e1 i nf) Lu , mt)
    ... | inj₂ (refl , h) = inj₂ (refl , into-at tk nf h)

    pb-few′ : ∀ {m e} → Q.T′ m e → Σ (List Pos) λ ks → ∀ {k} → PB′ k m → k ∈ ks
    pb-few′ (r , _) with Q.view r
    ... | inj₁ (um , _) = proj₁ (C.pb-few um) , λ { (inj₁ (_ , pb)) → proj₂ (C.pb-few um) pb
                                                   ; (inj₂ (_ , _ , ((_ , uf , _) , _) , _ , eq , _)) → ⊥-elim (InvAt.flat Iu uf (subst (λ z → u z _) eq um)) }
    ... | inj₂ (q , instEmit (mark _) _ , _ , () , _)
    ... | inj₂ (q , instEmit (value b) n , uq , ny , nfq , a , lb , refl , refl) with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ...   | k₀ , i₀ , e₀ , tk₀ , mt with match-val mt
    ...     | refl = proj₁ (C.few i₀) , mem
      where
        mem : ∀ {k} → PB′ k (q ⊕ [ a ]) → k ∈ proj₁ (C.few i₀)
        mem (inj₁ ((_ , um) , _)) = ⊥-elim (InvAt.flat Iu uq um)
        mem (inj₂ (f , k₁ , ff , i₁ , _ , pf , kk , (_ , tk))) with Q.first ((_ , uq , ny) , nfq) ff
        ... | refl with P.first pf ((_ , tk₀ , ny) , e2 i₀ nfq)
        ...   | refl = proj₂ (C.few i₀) tk kk

    cut-img : ∀ {q b a} → t q (out b) → T (not (keep b)) → ¬ P.Failed q → Lab incl a → Listed P.T′ (q ⊕ [ a ]) → LP (q ⊕ [ a ])
            → Σ Pos λ l → Img′ (q ⊕ [ a ]) l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Listed Q.T′ l
              × Match Every (One valuesOf) (Reads valuesOf) (cutEv b a) e′
    cut-img {q} {b} {a} tq nk nf lb L lp
      with C.img tq tt (P.live-out tq) (P.lst← nf (sub-listed L (≺-ext q []))) (lp↓ (≺→≼ {q} {q ⊕ [ a ]} (≺-ext q [])) lp)
    ... | inj₂ (() , _)
    ... | inj₁ (l₀ , i , e′ , ul , Lu , mt) with carried-val mt
    ...   | n , refl = l₀ ⊕ [ a ] , inj₂ (cut tq nk nf i ul lb refl refl) , cutEv (instEmit (value b) n) a
                       , Q.cut-row ul nk (e1 i nf) lb , Q.lst-cut (firstQ tq nk nf i ul) Lu lb , cut-match lb

    img′ : ∀ {k e} → P.T′ k e → Unpinned e → Live P.T′ k → Listed P.T′ k → LP k
         → (Σ Pos λ l → Img′ k l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Listed Q.T′ l × Match Every (One valuesOf) (Reads valuesOf) e e′)
           ⊎ (e ≡ skip × IntoAt Img′ Q.T′ PB′ HP s k)
    img′ (r , _) un lv L lp with P.view r
    ... | inj₁ (tk , pe) = src-img tk pe (P.live-unfailed lv tk) un lv L lp
    ... | inj₂ (_ , _ , tq , nk , nf , _ , lb , refl , refl) = inj₁ (cut-img tq nk nf lb L lp)

    cut¬¬ : ∀ {q b a l₀ e′} → t q (out b) → T (not (keep b)) → ¬ P.Failed q → Lab incl a → C.Img q l₀ → u l₀ e′
          → Match Every (One valuesOf) (Reads valuesOf) (out b) e′
          → ¬ (Σ Pos λ l → Img′ (q ⊕ [ a ]) l × Σ (Ev (IE A)) λ e″ → Q.T′ l e″ × Match Every (One valuesOf) (Reads valuesOf) (cutEv b a) e″)
          → ⊥
    cut¬¬ {a = a} {l₀} tq nk nf lb i ul mt n with carried-val mt
    ... | _ , refl = n (l₀ ⊕ [ a ] , inj₂ (cut tq nk nf i ul lb refl refl) , _ , Q.cut-row ul nk (e1 i nf) lb , cut-match lb)

    img¬¬′ : ∀ {k e} → P.T′ k e → Unpinned e → Live P.T′ k → Few P.T′ k
           → ¬ ¬ ((Σ Pos λ l → Img′ k l × Σ (Ev (IE A)) λ e′ → Q.T′ l e′ × Match Every (One valuesOf) (Reads valuesOf) e e′) ⊎ e ≡ skip)
    img¬¬′ (r , _) un lv fw n with P.view r
    ... | inj₁ (tk , pe) = let nf = P.live-unfailed lv tk in
      C.img¬¬ tk un (P.live← nf lv) (P.few← nf fw) λ { (inj₁ (l , i , e′ , ul , mt)) →
        n (inj₁ (l , inj₁ (i , nf , P.pass-fails tk pe) , e′ , Q.up ul (e1 i nf) (keeps→ {kp = keep} mt pe) , mt))
        ; (inj₂ es) → n (inj₂ es) }
    ... | inj₂ (q , _ , tq , nk , nf , _ , lb , refl , refl) =
      C.img¬¬ tq tt (P.live-out tq) (P.few← nf (few-sub fw (≺-ext q []))) λ { (inj₁ (_ , i , _ , ul , mt)) → cut¬¬ tq nk nf lb i ul mt (λ x → n (inj₁ x))
                                                                            ; (inj₂ ()) }

    src-shown : ∀ {l e} → u l e → Keeps (passes keep) e → ¬ Q.Failed l → Shown (One valuesOf) e → Live Q.T′ l → Few Q.T′ l
              → Σ Pos λ k → Img′ k l × Σ (Ev A) λ e₀ → P.T′ k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
    src-shown ul pe nf sw lv fw with C.shown ul sw (Q.live← nf lv) (Q.few← nf fw)
    ... | k , i , e₀ , tk , mt =
      k , inj₁ (i , e2 i nf , P.pass-fails tk (keeps← {kp = keep} mt pe)) , e₀ , P.up tk (e2 i nf) (keeps← {kp = keep} mt pe) , mt

    shown′ : ∀ {l e} → Q.T′ l e → Shown (One valuesOf) e → Live Q.T′ l → Few Q.T′ l
           → Σ Pos λ k → Img′ k l × Σ (Ev A) λ e₀ → P.T′ k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e
    shown′ (r , _) sw lv fw with Q.view r
    ... | inj₁ (ul , pe) = src-shown ul pe (Q.live-unfailed lv ul) sw lv fw
    ... | inj₂ (_ , _ , uq , ny , nfq , _ , lb , refl , refl) = cut-shown uq ny nfq lb

    ----------------------------------------------------------------------
    -- Placing a row from its source's placing

    Placed : Pos → Set
    Placed m = instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img′ k l × instantOf l ≡ instantOf m × Near Q.T′ m l)
               ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m

    m≺f : ∀ {m e f} → Q.TakeT m e → ¬ Q.Failed m → Q.First f → m ≺ f
    m≺f {m} {f = f} r nfm ff@((y , uf , ny) , _) with ≼-or-≻ f m
    ... | inj₂ mf = mf
    ... | inj₁ fm with at-or-before {f} {m} fm
    ...   | inj₁ refl = ⊥-elim (Q.none-at ff r)
    ...   | inj₂ fm′  = ⊥-elim (nfm (f , y , uf , ny , fm′))

    -- Past the row, a carrier listed up to: the first failing value
    -- between them is found, and its end is the nearer carrier.
    near-past : ∀ {m e k l} → Q.TakeT m e → ¬ Q.Failed m → C.Img k l → instantOf l ≡ instantOf m → m ≺ l → Near u m l → Placed m
    near-past r nfm i il ml (inj₁ lm) = ⊥-elim (lm ml)
    near-past {m} {k = k} {l} r nfm i il ml (inj₂ ((e″ , ul) , Lul)) with Q.search Lul | Q.fails? ul
    ... | inj₁ nfl | inj₂ nfsl =
      inj₂ (inj₁ (k , l , inj₁ (i , e2 i nfl , unfails← i nfsl) , il , inj₂ ((e″ , Q.up ul nfl (Q.pass-of nfsl ul)) , Q.lst→ nfl Lul)))
    ... | inj₁ nfl | inj₁ (y , ul′ , ny) =
      let (k₀ , i₀ , _) = cut-shown ul′ ny nfl (inj₂ refl)
      in inj₂ (inj₁ (k₀ , l ⊕ [ last ] , i₀ , trans (instant-⊕ l [ last ]) il
                    , inj₂ ((end , Q.cut-row ul′ ny nfl (inj₂ refl)) , Q.lst-cut ((y , ul′ , ny) , nfl) Lul (inj₂ refl))))
    ... | inj₂ (f , ff@((y , uf , ny) , nff) , fl) | _ =
      let (k₀ , i₀ , _) = cut-shown uf ny nff (inj₂ refl)
      in inj₂ (inj₁ (k₀ , f ⊕ [ last ] , i₀ , trans (instant-⊕ f [ last ]) (between {m} {f} {l} (m≺f r nfm ff) fl il)
                    , inj₂ ((end , Q.cut-row uf ny nff (inj₂ refl)) , Q.lst-cut ff (sub-listed Lul fl) (inj₂ refl))))

    near-place : ∀ {m e k l} → Q.TakeT m e → ¬ Q.Failed m → C.Img k l → instantOf l ≡ instantOf m → Near u m l → Placed m
    near-place {m} {k = k} {l} r nfm i il near with ≼-or-≻ l m
    ... | inj₁ lm = inj₂ (inj₁ (k , l , inj₁ (i , e2 i (Q.unfailed nfm lm) , unfails← i (Q.unfails nfm r lm)) , il , inj₁ lm))
    ... | inj₂ ml = near-past r nfm i il ml near

    src-place : ∀ {m e} → Q.TakeT m e → u m e → ¬ Q.Failed m → Live Q.T′ m → Listed Q.T′ m → Placed m
    src-place r um nfm lv L with C.place um (Q.live← nfm lv) (Q.lst← nfm L)
    ... | inj₁ e                          = inj₁ e
    ... | inj₂ (inj₂ h)                   = inj₂ (inj₂ h)
    ... | inj₂ (inj₁ (k , l , i , il , near)) = near-place r nfm i il near

    place′ : ∀ {m e} → Q.T′ m e → Live Q.T′ m → Listed Q.T′ m → Placed m
    place′ (r , _) lv L with Q.view r
    ... | inj₁ (um , _) = src-place r um (Q.live-unfailed lv um) lv L
    ... | inj₂ (q , _ , uq , ny , nfq , a , lb , refl , refl) =
      let (k , i , _) = cut-shown uq ny nfq lb in inj₂ (inj₁ (k , q ⊕ [ a ] , i , refl , inj₁ (≼-refl {q ⊕ [ a ]})))

    ----------------------------------------------------------------------
    -- With no end, nothing fails, so every row is its source's

    u-fail : (∀ {c} → P.T′ c end → ⊥) → ∀ {q y} → u q (out y) → T (not (passes keep y)) → ⊥
    u-fail ne {y = instEmit (mark _) _} _ ()
    u-fail ne {y = instEmit (value b) n} uq nb with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | _ , _ , _ , tk , mt with match-val mt
    ...   | refl = P.no-fail ne tk nb

    pickW : (∀ {c} → P.T′ c end → ⊥) → ∀ {ls} → (∀ {r e} → u r e → r ∈ ls) → ∀ {r e} → Q.T′ r e → r ∈ ls
    pickW ne F (r , _) with Q.view r
    ... | inj₁ (ur , _) = F ur
    ... | inj₂ (_ , _ , uq , ny , _) = ⊥-elim (u-fail ne uq ny)

    nfQ : (∀ {c} → P.T′ c end → ⊥) → ∀ {k} → ¬ Q.Failed k
    nfQ ne (_ , _ , x , nk , _) = u-fail ne x nk

    whole′ : Whole P.T′ → (∀ {c} → P.T′ c end → ⊥) → (∀ {q} → LP q) → Whole Q.T′
    whole′ wt ne lp = let (ls , F , B) = C.whole (P.whole← ne wt) (P.ended← ne) lp in
      ls , pickW ne F , λ m → let (e , ur) = B m in e , Q.up ur (nfQ ne) (Q.pass-of (λ { (_ , x , nk) → u-fail ne x nk }) ur)

    ----------------------------------------------------------------------
    -- Pins: kept with their connect unfailed, past no carried failure

    pin-unfailed : ∀ {p p′} → ¬ P.Failed p → (∀ {k′ l′} → C.Img k′ l′ → l′ ≺ p′ → k′ ≺ p) → ¬ Q.Failed p′
    pin-unfailed nfp bd (q , instEmit (mark _) _ , _ , () , _)
    pin-unfailed nfp bd (q , instEmit (value b) n , uq , nb , qp) with C.shown uq (b , refl) (Q.live-out uq) (Q.few-out uq)
    ... | k′ , i′ , _ , tk′ , mt with match-val mt
    ...   | refl = nfp (k′ , b , tk′ , nb , bd i′ qp)

    bound′ : ∀ {p p′} → ¬ Q.Failed p′ → (∀ {k′ l′} → C.Img k′ l′ → l′ ≺ p′ → k′ ≺ p) → ∀ {k′ l′} → Img′ k′ l′ → l′ ≺ p′ → k′ ≺ p
    bound′ nfp′ bd (inj₁ (i , _)) lp = bd i lp
    bound′ {p′ = p′} nfp′ bd (inj₂ (cut {l₀ = l₀} {a = a} _ nk _ _ ul _ _ refl)) lp =
      ⊥-elim (nfp′ (l₀ , _ , ul , nk , ≺-trans {l₀} {l₀ ⊕ [ a ]} {p′} (≺-ext l₀ []) lp))

    home-up : ∀ {p k₀} → ¬ P.Failed p → k₀ ≺ p → Home t k₀ → Home P.T′ k₀
    home-up {p} {k₀} nfp kp h n = h λ { (e , tk , un) → n (e , P.up tk (P.unfailed nfp (≺→≼ {k₀} {p} kp)) (P.pass-before tk kp nfp) , un) }

    pinned′ : ∀ {k p} → P.T′ k (pin p) → Live P.T′ k
            → (Σ Pos λ l → Σ Pos λ p′ → Q.T′ l (pin p′) × PB′ k l × (∀ {k′ l′} → Img′ k′ l′ → l′ ≺ p′ → k′ ≺ p)
                × (Listed P.T′ k → LP k → Listed Q.T′ l))
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home P.T′ k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ (P.left tk nfp _ , _) lv with C.pinned tk (P.live← (P.live-unfailed lv tk) lv) | P.live-unfailed lv tk
    ... | (l , p′ , ul , mb , bd , ls) , inj₁ e | nfk =
      (l , p′ , Q.lift (Q.left ul (pin-unfailed nfp bd) (Q.ins ul)) , inj₁ ((pin p′ , ul) , mb) , bound′ (pin-unfailed nfp bd) bd , λ L lp → Q.lst-any (ls (P.lst← nfk L) lp)) , inj₁ e
    ... | (l , p′ , ul , mb , bd , ls) , inj₂ (inj₁ (k₀ , kp , h , ek)) | nfk =
      (l , p′ , Q.lift (Q.left ul (pin-unfailed nfp bd) (Q.ins ul)) , inj₁ ((pin p′ , ul) , mb) , bound′ (pin-unfailed nfp bd) bd , λ L lp → Q.lst-any (ls (P.lst← nfk L) lp)) , inj₂ (inj₁ (k₀ , kp , home-up nfp kp h , ek))
    ... | (l , p′ , ul , mb , bd , ls) , inj₂ (inj₂ hh) | nfk =
      (l , p′ , Q.lift (Q.left ul (pin-unfailed nfp bd) (Q.ins ul)) , inj₁ ((pin p′ , ul) , mb) , bound′ (pin-unfailed nfp bd) bd , λ L lp → Q.lst-any (ls (P.lst← nfk L) lp)) , inj₂ (inj₂ hh)

  carried′ : CarryAt valuesOf M′ HP HE LP P.T′ Q.T′ s s′
  carried′ = record
    { Img = Img′ ; ext = ext′ ; img = img′ ; img¬¬ = img¬¬′ ; shown = shown′ ; img-row = img-row′ ; img-fun = img-fun′
    ; place = place′ ; live = live′ ; few = few′ ; whole = whole′ ; bk = bk′ ; in-bk = in-bk′ ; PB = PB′ ; pb-few = pb-few′ ; pinned = pinned′ }

------------------------------------------------------------------------
-- The former

-- THE ELABORATED TAKEWHILE CARRIES the plain one, its map grown by the
-- cuts under the first failing value.
take-carry : ∀ {A} incl (keep : A → Bool) (d : Den A) (d′ : Den (IE A)) {M HP HE LP H₁ H₂} p p′ → Emb M
           → InvAt H₁ p (enter d p) → InvAt H₂ p′ (enter d′ p′) → Disj H₁ p → Bare M (enter d p) → (∀ {x y} → x ≼ y → LP y → LP x)
           → CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′
           → Σ PMap λ M′ → M ⊆ᴹ M′ × Emb M′ × (∀ {x y} → M′ x y → M x y ⊎ W⁼ H₁ p x) × Bare M′ (enter (Op.takeWhile incl keep d) p)
             × (∀ {x y} → M′ x y → M x y ⊎ Grown M H₁ x y) × CarryAt valuesOf M′ HP HE LP (enter (Op.takeWhile incl keep d) p) (enter (Op.takeWhile incl (passes keep) d′) p′) p p′
take-carry incl keep d d′ p p′ hm It Iu dj br lp c = K.M′ , inj₁ , K.emb′ , K.within′ , K.bare′ , K.grown′ dj , K.carried′
  where module K = Core incl keep hm (λ {q} {e} → entered-reach d p {q} {e}) (λ {q} {e} → entered-reach d′ p′ {q} {e}) It Iu br lp c

carry-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → Bool) s → Carry m ρ s → Carry m ρ (takeWhile i p s)
carry-takeWhile n ρ i k s (carry h) = carry λ envP envE gP gE M₀ hm er jn ap p p′ m₀ okP okE nh fr →
  let (M , ms , hm′ , wi , br , jn′ , c) = h envP envE gP gE M₀ hm er jn ap p p′ m₀ okP okE nh fr
      (M′ , ms′ , hm″ , wi′ , br′ , gr , c′) = take-carry i k (approx n s envP) (approx n (elab ρ s) envE) p p′ hm′
        (inv-approx n s envP gP p okP) (inv-approx n (elab ρ s) envE gE p′ okE) (proj₂ okP) br (λ {x} {y} → listed↓ envP {x} {y}) c
  in M′ , (λ m → ms′ (ms m)) , hm″ , within-∘ {M₀ = M₀} {M = M} {M′ = M′} {p = p} wi (λ {x} {y} → wi′ {x} {y}) , br′
     , joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} {M = M} {N = M′} (λ {x} {y} → ms′ {x} {y}) jn′ (λ {x} {y} → gr {x} {y}) , c′
