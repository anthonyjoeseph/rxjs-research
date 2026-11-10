{-# OPTIONS --guardedness #-}

-- A PROGRAM CUT FINITE: each cold stream kept to its first `N` rows, each
-- unreached `defer`'s spin to its first `N` (`capprox`).  Cut deep enough,
-- it is within `m` of its approximant (`cut-ne`), so wherever at most `m`
-- positions cover what lies before a row, the cut program has the rows
-- the program has.
--
-- A STREAM'S ROWS ARE APART: each lies later than the one before and none
-- leads another, so a position leads at most one of them.  A row at depth
-- `N` has a row at every depth before it, all before it, each needing a
-- cover of its own: `m` positions and the row's own cover `m + 1` of
-- them, so a stream row whose wait is covered by `m` lies above depth
-- `m + 2` (`Bound.cut-ag`).
module denotation.Laws.Cut where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-≤-trans; ≮⇒≥; _<?_; <-cmp; n≮n)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (Events; Timeline; timelineAt; start; <ᵖ-part; ix-<)
open import denotation.EmissionSet
  using (Ev; out; skip; end; pin; EmissionSet; _≺_; Dep; Truncate; Den; coldAt; hot; DenEnv; approx;
  Spin; spin; InE; at-out; at-skip; at-end; on-out; on-skip; Unpinned; module Op)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; reach-via; _~⟨_⟩_; ~-refl)
open import denotation.Laws.Count using (Cov; AgC; trunc-ag; _≈ᶜ⟨_∣_⟩_; ≈ᶜ-refl; ≈ᶜ-mono; contract; pick)
open import denotation.Laws.Worlds using (_⊑_; ⊑-≼; ⊑-cmp; ⊕-cancelˡ; ⊕-assoc; ⊕-identityʳ; Real; Ok; InvAt; InvD; Hots; GoodEnv; ok-step; full)
open import denotation.Laws.Worlds.Leaves using (ine-pin; empty-inv; of-inv; spin-inv; map-inv; scan-inv; defer-inv)
open import denotation.Laws.ColdInv using (depth; cold-asc; cold-reach; cold-inv)
open import denotation.Laws.TakeInv using (takeWhile-inv)
open import denotation.Laws.FlatInv using (flatMap-inv)
open import denotation.Laws.Connect using (connect-inv)
open import denotation.Laws.ConnectNe using (Causal; connect-ne)
open import denotation.Laws.Join using (flatMap-ne; flatMap-causal)
open import denotation.Laws
  using (map-ne; scan-ne; takeWhile-ne; map-causal; scan-causal; takeWhile-causal; connect-causal; defer-causal; hot-causal;
  EnvAg; ag-cons; good-cons; aft; inv-approx; causal-approx)

------------------------------------------------------------------------
-- A set cut at a depth

-- The rows above depth `N`.
Deep : ∀ {A} (t : EmissionSet A) → (∀ {k e} → t k e → ℕ) → ℕ → EmissionSet A
Deep t d N k e = Σ (t k e) λ y → d y < N

-- A set whose rows run in order by depth, none leading another, a row at
-- every depth up to each.
module Bound {A : Set} (t : EmissionSet A) (d : ∀ {k e} → t k e → ℕ)
  (asc : ∀ {k k′ e e′} (y : t k e) (y′ : t k′ e′) → d y < d y′ → k ≺ k′)
  (flat : ∀ {k e l ys e′} → t k e → t (k ⊕ (l ∷ ys)) e′ → ⊥)
  (row-at : ∀ {k e} (x : t k e) j → j ≤ d x → Σ Pos λ k′ → Σ (Ev A) λ e′ → Σ (t k′ e′) λ z → d z ≡ j)
  where

  -- An earlier row leads no later one, nor the later the earlier.
  apart : ∀ {k k′ e e′} (y : t k e) (y′ : t k′ e′) → d y < d y′ → k ⊑ k′ ⊎ k′ ⊑ k → ⊥
  apart {k} y y′ lt (inj₁ ([] , refl)) = ≺-irrefl {k} (subst (k ≺_) (⊕-identityʳ k) (asc y y′ lt))
  apart y y′ lt (inj₁ (l ∷ ys , refl)) = flat y y′
  apart {k} {k′} y y′ lt (inj₂ le)     = ⊑-≼ le (asc y y′ lt)

  -- Rows at every depth below `j`, each led by one of `cs`, and a row as
  -- deep as `j`: at most as many depths as covers.
  bound : ∀ {k e} (x : t k e) j cs → j ≤ d x → (∀ {k′ e′} (y : t k′ e′) → d y < j → Any (k′ ⊑_) cs) → j ≤ length cs
  bound x zero    cs _  _   = z≤n
  bound x (suc j) cs le cov with row-at x j (≤-trans (n≤1+n j) le)
  ... | k′ , e′ , z , dz with pick (cov z (subst (λ v → suc v ≤ suc j) (sym dz) ≤-refl))
  ...   | c , zc , cs′ , eq , sp = subst (suc j ≤_) eq (s≤s (bound x j cs′ (≤-trans (n≤1+n j) le) cov′))
    where
      cov′ : ∀ {k″ e″} (y : t k″ e″) → d y < j → Any (k″ ⊑_) cs′
      cov′ y lt with sp (cov y (≤-trans lt (n≤1+n j)))
      ... | inj₂ a  = a
      ... | inj₁ yc = ⊥-elim (apart y z (subst (d y <_) (sym dz) lt) (⊑-cmp _ _ yc zc))

  -- CUT DEEP ENOUGH, NO ROW IS LOST: a row whose wait at most `m`
  -- positions cover, on either side, lies above depth `m + 2`.
  cut-ag : ∀ {m N} → suc (suc m) ≤ N → (∀ {q e} → t q e → ∀ {k e′} → Dep q e k e′) → AgC m (Deep t d N) t
  cut-ag {m} {N} mN nd q e side = proj₁ , into
    where
      Covers : Set
      Covers = Σ (List Pos) λ ks → length ks ≤ m × (∀ {k e′} (y : t k e′) → d y < N → k ≺ q → Cov q ks k)

      cover : t q e → _ → Covers
      cover x (inj₁ (ks , le , h)) = ks , le , λ y lt kq → h (y , lt) kq (nd x)
      cover x (inj₂ (ks , le , h)) = ks , le , λ y lt kq → h y kq (nd x)

      too-deep : (x : t q e) → N ≤ d x → Covers → ⊥
      too-deep x ge (ks , le , h) = n≮n (suc m) (≤-trans mN (≤-trans (bound x N (q ∷ ks) ge cov) (s≤s le)))
        where
          cov : ∀ {k′ e′} (y : t k′ e′) → d y < N → Any (k′ ⊑_) (q ∷ ks)
          cov y lt with h y lt (asc y x (<-≤-trans lt ge))
          ... | inj₁ yq = here yq
          ... | inj₂ a  = there a

      into : t q e → Deep t d N q e
      into x with d x <? N
      ... | yes lt = x , lt
      ... | no ge  = ⊥-elim (too-deep x (≮⇒≥ ge) (cover x side))

------------------------------------------------------------------------
-- The leaves, cut

-- Every invariant field reads rows only to constrain them, so a subset
-- keeps it.
inv-sub : ∀ {A H p} {X Y : EmissionSet A} → (∀ {y e} → X y e → Y y e) → InvAt H p Y → InvAt H p X
inv-sub sub I = record
  { world  = λ x → InvAt.world I (sub x)
  ; real   = λ x → InvAt.real I (sub x)
  ; func   = λ x x′ → InvAt.func I (sub x) (sub x′)
  ; flat   = λ x x′ → InvAt.flat I (sub x) (sub x′)
  ; burst  = λ c y cy → InvAt.burst I (sub c) (sub y) cy
  ; under  = λ x y pl v le → InvAt.under I (sub x) (sub y) pl v le
  ; quiet  = λ c y cy → InvAt.quiet I (sub c) (sub y) cy
  ; pinned = λ x → InvAt.pinned I (sub x)
  }

-- A stream's row at every depth up to a row's.
row-at : ∀ {A} {ev : Events A} {k e} (x : InE ev k e) j → j ≤ depth x
       → Σ Pos λ k′ → Σ (Ev A) λ e′ → Σ (InE ev k′ e′) λ z → depth z ≡ j
row-at at-out      zero    _       = _ , _ , at-out , refl
row-at at-skip     zero    _       = _ , _ , at-skip , refl
row-at at-end      zero    _       = _ , _ , at-end , refl
row-at (on-out x)  zero    _       = _ , _ , at-out , refl
row-at (on-skip x) zero    _       = _ , _ , at-skip , refl
row-at (on-out x)  (suc j) (s≤s le) with row-at x j le
... | k′ , e′ , z , refl = k′ , e′ , on-out z , refl
row-at (on-skip x) (suc j) (s≤s le) with row-at x j le
... | k′ , e′ , z , refl = k′ , e′ , on-skip z , refl

ine-unpinned : ∀ {A} {ev : Events A} {k e} → InE ev k e → Unpinned e
ine-unpinned {e = out _} _ = tt
ine-unpinned {e = skip}  _ = tt
ine-unpinned {e = end}   _ = tt
ine-unpinned {e = pin _} x = ine-pin x

-- A cold stream's first `N` rows.
coldN : ∀ {A} → ℕ → Timeline A → Den A
coldN N c = coldAt λ p → Deep (InE (start p (timelineAt c p))) depth N

-- A spin's first `N` rows.
spinIx : ∀ {A} {p y} {e : Ev A} → Spin p y e → ℕ
spinIx (spin i) = i

spinN : ∀ {A} → ℕ → Den A
spinN N = coldAt λ p → Deep (Spin p) spinIx N

-- A spin's rows run in order, and only so.
ix-asc : ∀ p {i j} → i < j → (p ⊕ [ ix i ]) ≺ (p ⊕ [ ix j ])
ix-asc p lt = Equivalence.from T-≡ (<ᵖ-part p [] [] (ix-< lt))

ix-back : ∀ p {i j} → (p ⊕ [ ix i ]) ≺ (p ⊕ [ ix j ]) → i < j
ix-back p {i} {j} lt with <-cmp i j
... | tri< a _ _    = a
... | tri≈ _ refl _ = ⊥-elim (≺-irrefl {p ⊕ [ ix i ]} lt)
... | tri> _ _ c    = ⊥-elim (≺-irrefl {p ⊕ [ ix i ]} (≺-trans {p ⊕ [ ix i ]} {p ⊕ [ ix j ]} {p ⊕ [ ix i ]} lt (ix-asc p c)))

private
  spin-flat : ∀ {A} {p k l ys} {e e′ : Ev A} → Spin p k e → Spin p (k ⊕ (l ∷ ys)) e′ → ⊥
  spin-flat {p = p} {l = l} {ys} (spin i) x′ = go x′ refl
    where
      go : ∀ {y e′} → Spin {A = _} p y e′ → y ≡ (p ⊕ [ ix i ]) ⊕ (l ∷ ys) → ⊥
      go (spin j) eq with ⊕-cancelˡ p [ ix j ] (ix i ∷ l ∷ ys) (trans eq (⊕-assoc p [ ix i ] (l ∷ ys)))
      ... | ()

  spin-at : ∀ {A} {p k} {e : Ev A} (x : Spin p k e) j → j ≤ spinIx x → Σ Pos λ k′ → Σ (Ev A) λ e′ → Σ (Spin p k′ e′) λ z → spinIx z ≡ j
  spin-at {p = p} (spin i) j _ = p ⊕ [ ix j ] , skip , spin j , refl

  module SpinB {A : Set} (p : Pos) = Bound {A} (Spin p) spinIx (λ { (spin i) (spin j) lt → ix-asc p lt }) spin-flat spin-at

  module ColdB {A : Set} (c : Timeline A) (p : Pos) (rp : Real p) (flat : ∀ {k e l ys e′} → InE (start p (timelineAt c p)) k e → InE (start p (timelineAt c p)) (k ⊕ (l ∷ ys)) e′ → ⊥) =
    Bound {A} (InE (start p (timelineAt c p))) depth (cold-asc p (timelineAt c p) rp) flat row-at

-- Cut past `m + 1` rows, a cold stream is within `m`.
coldN-ne : ∀ {A H m N} (c : Timeline A) → suc (suc m) ≤ N → coldN N c ≈ᶜ⟨ Ok H ∣ m ⟩ Op.cold c
coldN-ne {A} {H} c mN p ok@(rp , _) = trunc-ag (ColdB.cut-ag c p rp flat mN λ x → full (ine-unpinned x))
  where
    re = cold-reach p (timelineAt c p) rp
    flat : ∀ {k e l ys e′} → InE (start p (timelineAt c p)) k e → InE (start p (timelineAt c p)) (k ⊕ (l ∷ ys)) e′ → ⊥
    flat x x′ = InvAt.flat (cold-inv {A} {H} c p ok) (x , re x) (x′ , re x′)

-- So is a spin.
spinN-ne : ∀ {A R m N} → suc (suc m) ≤ N → spinN {A} N ≈ᶜ⟨ R ∣ m ⟩ Op.⊥
spinN-ne {A} mN p _ = trunc-ag (SpinB.cut-ag {A} p mN λ { (spin _) → tt })

coldN-inv : ∀ {A H} N (c : Timeline A) → InvD H (coldN N c)
coldN-inv {A} {H} N c p ok@(rp , _) = inv-sub (λ { (x , _) → proj₁ x , cold-reach p (timelineAt c p) rp (proj₁ x) }) (cold-inv {A} {H} c p ok)

spinN-inv : ∀ {A H} N → InvD H (spinN {A} N)
spinN-inv {A} {H} N p ok = inv-sub sub (spin-inv {A} {H} p ok)
  where
    sub : ∀ {y e} → Truncate (Deep (Spin p) spinIx N) y e → Truncate (Spin p) y e
    sub ((spin i , lt) , R) = spin i , reach-via {e = skip} {e₀ = skip} back R
      where
        back : ∀ {k e′} → Spin p k e′ → k ≺ (p ⊕ [ ix i ]) → Dep (p ⊕ [ ix i ]) skip k e′ → Σ (Ev A) λ e″ → Deep (Spin p) spinIx N k e″ × Dep (p ⊕ [ ix i ]) skip k e″
        back (spin j) kq _ = skip , (spin j , ≤-trans (ix-back p kq) (≤-trans (n≤1+n i) lt)) , tt

------------------------------------------------------------------------
-- The program, cut

-- `approx n`, its cold streams and spins cut at `N` rows.
capprox : ∀ {Γ A} → ℕ → ℕ → Obs Timeline Γ A → DenEnv Γ → Den A
capprox N n       (cold c)          ρ = coldN N c
capprox N n       empty             ρ = Op.empty
capprox N n       (of xs)           ρ = Op.of xs
capprox N n       (map f s)         ρ = Op.map f (capprox N n s ρ)
capprox N n       (scan f z s)      ρ = Op.scan f z (capprox N n s ρ)
capprox N n       (takeWhile i p s) ρ = Op.takeWhile i p (capprox N n s ρ)
capprox N n       (flatMap op f s)  ρ = Op.flatMap op (λ a → capprox N n (f a) ρ) (capprox N n s ρ)
capprox N n       (connect s b)     ρ = Op.connect (capprox N n s ρ) λ h → capprox N n b (h ∷ ρ)
capprox N n       (connected i)     ρ = lookup ρ i
capprox N zero    (defer l)         ρ = spinN N
capprox N (suc n) (defer l)         ρ = Op.defer (capprox N n (Later.force l) ρ)

inv-capprox : ∀ {Γ A} N n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (capprox N n o ρ)
inv-capprox N n       (cold c)          ρ g = coldN-inv N c
inv-capprox N n       empty             ρ g = empty-inv
inv-capprox N n       (of xs)           ρ g = of-inv xs
inv-capprox N n       (map f s)         ρ g = map-inv f {capprox N n s ρ} (inv-capprox N n s ρ g)
inv-capprox N n       (scan f z s)      ρ g = scan-inv f z {capprox N n s ρ} (inv-capprox N n s ρ g)
inv-capprox N n       (takeWhile i k s) ρ g = takeWhile-inv i k {capprox N n s ρ} (inv-capprox N n s ρ g)
inv-capprox N n       (flatMap op f s)  ρ g = flatMap-inv op (inv-capprox N n s ρ g) λ a → inv-capprox N n (f a) ρ g
inv-capprox N n       (connect s b)     ρ g =
  connect-inv {s = capprox N n s ρ} {F = λ h → capprox N n b (h ∷ ρ)} (inv-capprox N n s ρ g) λ {t} L → inv-capprox N n b (hot t ∷ ρ) (good-cons L g)
inv-capprox N n       (connected i)     ρ g = proj₁ (g i)
inv-capprox N zero    (defer l)         ρ g = spinN-inv N
inv-capprox N (suc n) (defer l)         ρ g = defer-inv (inv-capprox N n (Later.force l) ρ g)

causal-capprox : ∀ {Γ A q} N n (o : Obs Timeline Γ A) {ρ ρ′ : DenEnv Γ} → EnvAg q ρ ρ′ → capprox N n o ρ ~⟨ q ⟩ capprox N n o ρ′
causal-capprox N n       (cold c)          e = ~-refl (coldN N c)
causal-capprox N n       empty             e = ~-refl Op.empty
causal-capprox N n       (of xs)           e = ~-refl (Op.of xs)
causal-capprox N n       (map f s)         {ρ} {ρ′} e = map-causal f {capprox N n s ρ} {capprox N n s ρ′} (causal-capprox N n s e)
causal-capprox N n       (scan f z s)      {ρ} {ρ′} e = scan-causal f z {capprox N n s ρ} {capprox N n s ρ′} (causal-capprox N n s e)
causal-capprox N n       (takeWhile i k s) {ρ} {ρ′} e = takeWhile-causal i k {capprox N n s ρ} {capprox N n s ρ′} (causal-capprox N n s e)
causal-capprox N n       (flatMap op f s)  e = flatMap-causal op (causal-capprox N n s e) λ a → causal-capprox N n (f a) e
causal-capprox N n       (connect s b)     {ρ} {ρ′} e =
  connect-causal {s = capprox N n s ρ} {capprox N n s ρ′} {λ h → capprox N n b (h ∷ ρ)} {λ h → capprox N n b (h ∷ ρ′)}
    (causal-capprox N n s e) λ a → causal-capprox N n b (ag-cons (hot-causal a) e)
causal-capprox N n       (connected i)     e = e i
causal-capprox N zero    (defer l)         e = ~-refl (spinN N)
causal-capprox N (suc n) (defer l)         e = defer-causal (causal-capprox N n (Later.force l) e)

private
  causal-cat : ∀ {Γ A B} N n (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → Causal (λ h → capprox N n b (h ∷ ρ))
  causal-cat N n b ρ a = causal-capprox N n b (ag-cons (hot-causal a) (λ i → ~-refl (lookup ρ i)))

  causal-at : ∀ {Γ A B} n (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → Causal (λ h → approx n b (h ∷ ρ))
  causal-at n b ρ a = causal-approx n b (ag-cons (hot-causal a) (λ i → ~-refl (lookup ρ i)))

-- CUT PAST `m + 1` ROWS, THE PROGRAM IS WITHIN `m` of its approximant:
-- each operator keeps the modulus, and each leaf is within it.
cut-ne : ∀ {Γ A m N} → suc (suc m) ≤ N → ∀ n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ
       → capprox N n o ρ ≈ᶜ⟨ Ok (Hots ρ) ∣ m ⟩ approx n o ρ
cut-ne mN n       (cold c)          ρ g = coldN-ne c mN
cut-ne mN n       empty             ρ g = ≈ᶜ-refl Op.empty
cut-ne mN n       (of xs)           ρ g = ≈ᶜ-refl (Op.of xs)
cut-ne {N = N} mN n (map f s)       ρ g = map-ne f {capprox N n s ρ} {approx n s ρ} (cut-ne mN n s ρ g)
cut-ne {N = N} mN n (scan f z s)    ρ g = scan-ne f z {capprox N n s ρ} {approx n s ρ} (cut-ne mN n s ρ g)
cut-ne {N = N} mN n (takeWhile i k s) ρ g =
  takeWhile-ne i k {capprox N n s ρ} {approx n s ρ} (inv-capprox N n s ρ g) (inv-approx n s ρ g) (cut-ne mN n s ρ g)
cut-ne {N = N} mN n (flatMap op f s) ρ g =
  flatMap-ne op (inv-capprox N n s ρ g) (inv-approx n s ρ g) (λ a → inv-capprox N n (f a) ρ g) (λ a → inv-approx n (f a) ρ g)
    (cut-ne mN n s ρ g) λ a → cut-ne mN n (f a) ρ g
cut-ne {N = N} mN n (connect s b)   ρ g =
  connect-ne {s = capprox N n s ρ} {approx n s ρ} {λ h → capprox N n b (h ∷ ρ)} {λ h → approx n b (h ∷ ρ)}
    (inv-capprox N n s ρ g) (inv-approx n s ρ g)
    (λ {t} L → inv-capprox N n b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g))
    (causal-cat N n b ρ) (causal-at n b ρ)
    (cut-ne mN n s ρ g) λ {t} L → cut-ne mN n b (hot t ∷ ρ) (good-cons L g)
cut-ne mN n       (connected i)     ρ g = ≈ᶜ-refl (lookup ρ i)
cut-ne mN zero    (defer l)         ρ g = spinN-ne mN
cut-ne {m = m} {N} mN (suc n) (defer l) ρ g =
  ≈ᶜ-mono {R = Ok (Hots ρ)} {m} {suc m} {Op.defer (capprox N n (Later.force l) ρ)} {Op.defer (approx n (Later.force l) ρ)} (n≤1+n m)
    (contract ok-step (aft (capprox N n (Later.force l) ρ) (inv-capprox N n (Later.force l) ρ g))
      (aft (approx n (Later.force l) ρ) (inv-approx n (Later.force l) ρ g)) (cut-ne mN n (Later.force l) ρ g))
