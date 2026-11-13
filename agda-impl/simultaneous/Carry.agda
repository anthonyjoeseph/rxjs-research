{-# OPTIONS --guardedness #-}

-- THE ELABORATION CARRIES EVERY SUBTERM.  The elaboration subscribes
-- each node of the plain program deeper, under wrappers of its own, so a
-- plain position and its elaborated counterpart differ by inserted path.
-- A map of positions `M` puts each plain position the run uses on the
-- elaborated subscription of the node it belongs to, keeping the order
-- and the instants, and reflecting leading (`Emb`).
--
-- A subterm is carried (`CarryAt`) when every row of its plain run is
-- carried by a row of its elaborated run lying under its position's
-- image: the attribution of `simultaneous.Attribution`, read relative to
-- the environment, whose hots may hold rows the subterm only reads.
--
-- By induction on the program (`Carry`), under every environment of
-- carried binders, each subterm extends the map over its own world; the
-- run's map is their union.  A `defer` is reached through its
-- approximants, as in `simultaneous.Held`.
module simultaneous.Carry where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; cold; map; flatMap)
open import denotation.Position using (Pos; Path; Label; ix; sub; _∙_; _⊕_; root; _≟ᵖ_; inside)
open import Data.List.Properties using (∷-injective)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; Unpinned; EmissionSet; Den; hot; coldAt; enter; Proper; DenEnv; _≺_; _≼_; approx)
import denotation.Events as Evs
open import simultaneous.HeldMap using (module MapRun; mapEv)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; W⁼; here; _⊑_; ⊑-refl; ⊑-trans; ⊑-inside; ∙-inj; InvAt)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Attribution using (Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (Ahead; CarryAt; Narrow; module MapCarry; Emb; Fresh; PMap; _⊆ᴹ_; ahead-under; listed-≼; map-carry)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE; elab; annotate)

------------------------------------------------------------------------
-- The induction

-- What an annotated row shows: the values of the emit it carries.
annValues : ∀ {X} → AIE X → List X
annValues (_ , just x) = valuesOf x
annValues (_ , nothing) = []

-- EVERY HOT OF AN ENVIRONMENT LISTED before a position.
HotsListed : ∀ {Γ} → DenEnv Γ → Pos → Set
HotsListed []              q = ⊤
HotsListed (hot t ∷ ρ)     q = Listed t q × HotsListed ρ q
HotsListed (coldAt _ ∷ ρ)  q = HotsListed ρ q

listed↓ : ∀ {Γ} (ρ : DenEnv Γ) {x y} → x ≼ y → HotsListed ρ y → HotsListed ρ x
listed↓ []             _  _       = tt
listed↓ (hot t ∷ ρ)    xy (L , R) = listed-≼ L xy , listed↓ ρ xy R
listed↓ (coldAt _ ∷ ρ) xy R       = listed↓ ρ xy R

-- A connect's binder: the source, read hot past the connect at `at` in
-- the plain run and at `at′` annotated in the elaborated, carried along
-- the map, each reading keeping the invariant.
record Bound (M₀ : PMap) (LP : Pos → Set) {X : Set} (d : Den X) (d′ : Den (AIE X)) : Set₁ where
  field
    {Θ Θ′}  : List Set
    m       : ℕ
    src     : Obs Timeline Θ X
    σ       : ∀ {Y} → Y ∈ L.map AIE Θ → Y ∈ Θ′
    envP    : DenEnv Θ
    envE    : DenEnv Θ′
    at at′  : Pos
    lists   : ∀ {q} → LP q → HotsListed envP q
    carried : CarryAt annValues M₀ (Hots envP) (Hots envE) (HotsListed envP) (enter (approx m src envP) (at ⊕ [ ix 1 ]))
                (enter (approx m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ])) (at ⊕ [ ix 1 ]) (at′ ⊕ [ ix 1 ])
    invP    : InvAt (Hots envP) (at ⊕ [ ix 1 ]) (enter (approx m src envP) (at ⊕ [ ix 1 ]))
    invE    : InvAt (Hots envE) (at′ ⊕ [ ix 1 ]) (enter (approx m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ]))
    isP     : d ≡ hot (Proper (enter (approx m src envP) (at ⊕ [ ix 1 ])))
    isE     : d′ ≡ hot (Proper (enter (approx m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ])))

EnvRel : ∀ {Γ Δ} → PMap → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Γ → DenEnv Δ → Set₁
EnvRel {Γ} M₀ ρ envP envE = ∀ {X} (i : X ∈ Γ) → Bound M₀ (HotsListed envP) (lookup envP i) (lookup envE (ρ (∈-map⁺ AIE i)))

-- What the map adds lies in the world with the subscription.
Within : (Pos → Set) → PMap → PMap → Pos → Set
Within H M₀ M p = ∀ {x y} → M x y → M₀ x y ⊎ W⁼ H p x

-- The map pairs nothing strictly under a row: what a former putting a
-- row under another's position grows the map by.
Bare : ∀ {A : Set} → PMap → EmissionSet A → Set
Bare M t = ∀ {k e x y} → t k e → M x y → k ⊑ x → x ≡ k

-- No hot row at or under a position.
NotHot : (Pos → Set) → Pos → Set
NotHot H p = ∀ {q} → H q → p ⊑ q → ⊥

-- No row inside a world point of a position: what a world point joins
-- under lies outside every position its subscription reaches.
Clear : (Pos → Set) → (Pos → Set) → Pos → Set
Clear R H p = ∀ {q w} → R q → W⁼ H p w → T (inside w q) → ⊥

clear-not : ∀ {R H p} → Clear R H p → NotHot R p
clear-not cl r pq = cl r here (⊑-inside pq)

-- A row of a bound hot.
BoundRow : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → Pos → Set
BoundRow {X = X} b q = Σ (Ev X) (Proper (enter (approx (Bound.m b) (Bound.src b) (Bound.envP b)) (Bound.at b ⊕ [ ix 1 ])) q)

-- A row of a bound source, of any event: alive, or past the source's end.
BoundSrc : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → EmissionSet X
BoundSrc b = enter (approx (Bound.m b) (Bound.src b) (Bound.envP b)) (Bound.at b ⊕ [ ix 1 ])

-- A row of some binder's source.
Rows : ∀ {Γ} {M₀ : PMap} {LP₀ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
     → (∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)) → Pos → Set
Rows {[]}    er q = ⊥
Rows {X ∷ Γ} {dP = dP} {dE} er q =
  Σ (Ev X) (BoundSrc (er (here refl)) q) ⊎ Rows {dP = λ i → dP (there i)} {dE = λ i → dE (there i)} (λ i → er (there i)) q

rows-at : ∀ {Γ} {M₀ : PMap} {LP₀ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
          (er : ∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)) {X} (i : X ∈ Γ) {q e} → BoundSrc (er i) q e → Rows er q
rows-at er (here refl) x = inj₁ (_ , x)
rows-at {dP = dP} {dE} er (there i) x = inj₂ (rows-at {dP = λ j → dP (there j)} {dE = λ j → dE (there j)} (λ j → er (there j)) i x)

-- Rows of one environment's sources, another's, each binder's source a
-- part of the other's.
rows-map : ∀ {Γ} {M₀ M₁ : PMap} {LP₀ LP₁ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
             {dP′ : ∀ {X} → X ∈ Γ → Den X} {dE′ : ∀ {X} → X ∈ Γ → Den (AIE X)}
           (er : ∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)) (er′ : ∀ {X} (i : X ∈ Γ) → Bound M₁ LP₁ (dP′ i) (dE′ i))
         → (∀ {X} (i : X ∈ Γ) {q e} → BoundSrc (er′ i) q e → BoundSrc (er i) q e) → ∀ {q} → Rows er′ q → Rows er q
rows-map {[]} er er′ f ()
rows-map {X ∷ Γ} er er′ f (inj₁ (e , x)) = inj₁ (e , f (here refl) x)
rows-map {X ∷ Γ} {dP = dP} {dE} {dP′} {dE′} er er′ f (inj₂ r) =
  inj₂ (rows-map {dP = λ j → dP (there j)} {dE = λ j → dE (there j)} {dP′ = λ j → dP′ (there j)} {dE′ = λ j → dE′ (there j)}
                 (λ j → er (there j)) (λ j → er′ (there j)) (λ j → f (there j)) r)

hots-at : ∀ {Γ} (envP : DenEnv Γ) {X} (i : X ∈ Γ) {t : EmissionSet X} → lookup envP i ≡ hot t → ∀ {q e} → t q e → Hots envP q
hots-at (hot _ ∷ _)    (here refl) refl tq = inj₁ (_ , tq)
hots-at (coldAt _ ∷ _) (here refl) ()   _
hots-at (hot _ ∷ ρ)    (there i)   e    tq = inj₂ (hots-at ρ i e tq)
hots-at (coldAt _ ∷ ρ) (there i)   e    tq = hots-at ρ i e tq

bound-hot : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} (envP : DenEnv Γ) {envE : DenEnv Δ}
            (er : EnvRel M₀ ρ envP envE) {X} (i : X ∈ Γ) {q} → BoundRow (er i) q → Hots envP q
bound-hot envP er i (_ , x) = hots-at envP i (Bound.isP (er i)) x

-- UNDER A HOT ROW, ONLY A READER'S JOIN: a point the map puts strictly
-- under a row of a bound hot lies under the row joined at a subscription
-- `e`, its image under the row's carrier joined at `e`'s image.  Two
-- readers' rows of one hot row keep their subscriptions' order so.
Joins : ∀ {Γ Δ} {M₀ : PMap} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (envP : DenEnv Γ) (envE : DenEnv Δ)
      → EnvRel M₀ ρ envP envE → PMap → Set₁
Joins {Γ} _ _ _ er M = ∀ {X} (i : X ∈ Γ) {x y q a σ} → M x y → BoundRow (er i) q → x ≡ q ⊕ (a ∷ σ)
  → Σ Pos λ e → a ≡ sub e × Σ Pos λ e′ → M e e′ × Σ Pos λ L → CarryAt.Img (Bound.carried (er i)) q L × (L ⊕ [ sub e′ ]) ⊑ y

-- NO POSITION HOLDS ROWS OF TWO HOTS: a hot's rows lie in its source's
-- world, which holds no row of a hot already bound.
Apart : ∀ {Γ} → DenEnv Γ → Set
Apart []             = ⊤
Apart (hot t ∷ ρ)    = (∀ {q e} → t q e → Hots ρ q → ⊥) × Apart ρ
Apart (coldAt _ ∷ ρ) = Apart ρ

-- One label under a point of the map, imaged under its image, the point
-- holding no hot row at or under it.
Grown : PMap → (Pos → Set) → PMap
Grown M H x y = Σ Pos λ r → Σ Pos λ r₀ → Σ Label λ a → M r r₀ × r₀ ⊑ y × x ≡ r ⊕ [ a ] × NotHot H r

private
  snoc-split : ∀ (ps qs : Path) {a a′ σ} → ps ++ [ a ] ≡ qs ++ a′ ∷ σ → (ps ≡ qs × a ≡ a′) ⊎ Σ Path λ σ′ → ps ≡ qs ++ a′ ∷ σ′
  snoc-split []       []            refl = inj₁ (refl , refl)
  snoc-split (_ ∷ ps) []            refl = inj₂ (ps , refl)
  snoc-split []       (_ ∷ [])      ()
  snoc-split []       (_ ∷ _ ∷ _)   ()
  snoc-split (_ ∷ ps) (_ ∷ qs)      e with ∷-injective e
  ... | refl , e′ with snoc-split ps qs e′
  ...   | inj₁ (refl , refl) = inj₁ (refl , refl)
  ...   | inj₂ (σ′ , refl)   = inj₂ (σ′ , refl)

  -- One label under `r`, read under `q`: `r` is `q`, or lies under `q`'s step.
  pos-split : ∀ r q {a a′ σ} → r ⊕ [ a ] ≡ q ⊕ (a′ ∷ σ) → (r ≡ q × a ≡ a′) ⊎ Σ Path λ σ′ → r ≡ q ⊕ (a′ ∷ σ′)
  pos-split (i ∙ ps) (j ∙ qs) e with ∙-inj e
  ... | refl , e′ with snoc-split ps qs e′
  ...   | inj₁ (refl , refl) = inj₁ (refl , refl)
  ...   | inj₂ (σ′ , refl)   = inj₂ (σ′ , refl)

-- THE JOINS KEPT by a map growing by points one label under points of
-- the map.
joins-grow : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
             {er : EnvRel M₀ ρ envP envE} {M N : PMap}
           → M ⊆ᴹ N → Joins ρ envP envE er M → (∀ {x y} → N x y → M x y ⊎ Grown M (Rows er) x y) → Joins ρ envP envE er N
joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} ms jn gr i n row xe with gr n
... | inj₁ m with jn i m row xe
...   | e , ae , e′ , me , L , il , Ly = e , ae , e′ , ms me , L , il , Ly
joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} ms jn gr i n row xe | inj₂ (r , r₀ , a , m , ry , refl , nh) with pos-split r _ xe
... | inj₁ (refl , refl) = ⊥-elim (nh (rows-at er i (proj₁ (proj₂ row))) (⊑-refl r))
... | inj₂ (σ′ , refl) with jn i m row refl
...   | e , ae , e′ , me , L , il , Ly = e , ae , e′ , ms me , L , il , ⊑-trans Ly ry

-- A CARRY'S LATE CARRIERS STAY PAST a map: past, and apart from, the
-- image of every point before the row they carry and not above it.
PastOver : ∀ {A Y} {f : Y → List A} {M : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
         → CarryAt f M HP HE LP t u s s′ → PMap → Set
PastOver {t = t} {u = u} c N = ∀ {k l e₀ e x y} → CarryAt.PB c k l → t k e₀ → (Unpinned e₀ → Live t k) → u l e → N x y → x ≺ k → ¬ (x ⊑ k) → Ahead y l

-- Every binder's, along a map grown past the binders.
EnvPast : ∀ {Γ} {M₀ : PMap} {LP : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
        → (∀ {X} (i : X ∈ Γ) → Bound M₀ LP (dP i) (dE i)) → PMap → Set₁
EnvPast {Γ} er N = ∀ {X} (i : X ∈ Γ) → PastOver (Bound.carried (er i)) N

-- Every binder's own map.
env-past : ∀ {Γ} {M : PMap} {LP : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
         → (er : ∀ {X} (i : X ∈ Γ) → Bound M LP (dP i) (dE i)) → EnvPast er M
env-past er i = CarryAt.pb-past (Bound.carried (er i))

-- A MAP GROWN ONE LABEL UNDER POINTS HOLDING NO HOT ROW stays past every
-- binder's late carriers: a hot row past such a point is apart from it.
grown-past : ∀ {Γ Δ} {M₀ M M′ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
           → (er : EnvRel M₀ ρ envP envE) → EnvPast er M → (∀ {x y} → M′ x y → M x y ⊎ Grown M (Rows er) x y) → EnvPast er M′
grown-past {ρ = ρ₀} {envP = envP₀} {envE = envE₀} er ep gr i =
  past-grow (Bound.carried (er i)) (λ {k} {e₀} tk → rows-at er i tk) (ep i) gr
  where
    past-grow : ∀ {A Y} {f : Y → List A} {M₁ : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
                (c : CarryAt f M₁ HP HE LP t u s s′) {N N′ : PMap} {H : Pos → Set}
              → (∀ {k e₀} → t k e₀ → H k) → PastOver c N → (∀ {x y} → N′ x y → N x y ⊎ Grown N H x y) → PastOver c N′
    past-grow c hk ep′ gr′ pb tk lv ul m′ xk nxk with gr′ m′
    ... | inj₁ m = ep′ pb tk lv ul m xk nxk
    ... | inj₂ (r , r₀ , a , mr , ry , refl , nh) =
      ahead-under (ep′ pb tk lv ul mr (≺-trans {r} {r ⊕ [ a ]} {_} (≺-ext r []) xk) (λ rk → nh (hk tk) rk)) ry

-- A point of the map at or over a late carrier, itself on the carried
-- row's step under a hot row and over the row, or past the row.
Anchor : PMap → Pos → Pos → Pos → Label → Set
Anchor N k l h a = Σ Pos λ x → Σ Pos λ y → N x y × y ⊑ l × ((((h ⊕ [ a ]) ⊑ x) × x ⊑ k) ⊎ k ≺ x)

-- A LATE CARRIER UNDER A CARRIED HOT ROW IS ANCHORED: a row carried into
-- its instant, lying strictly under a bound hot's row which that hot
-- carries in order, has its carrier under a point of the map on its own
-- step, or past it.
PBNest : ∀ {Γ} {M₀ : PMap} {LP₀ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
       → (∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)) → PMap → ∀ {A Y} {f : Y → List A} {M : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
       → CarryAt f M HP HE LP t u s s′ → Set₁
PBNest {Γ} er N {t = t} c = ∀ {X} (i : X ∈ Γ) {k l e₀ h L a σ} → CarryAt.PB c k l → t k e₀ → (Unpinned e₀ → Live t k) → BoundRow (er i) h
                          → CarryAt.Img (Bound.carried (er i)) h L → k ≡ h ⊕ (a ∷ σ) → Anchor N k l h a

-- Every binder's late carriers, so anchored.
Nests : ∀ {Γ} {M₀ : PMap} {LP₀ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
      → (∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)) → PMap → Set₁
Nests {Γ} er N = ∀ {X} (j : X ∈ Γ) → PBNest er N (Bound.carried (er j))

-- Anchors are kept along a larger map, and over a carrier moved under.
anchor-grow : ∀ {N N′ k l h a} → N ⊆ᴹ N′ → Anchor N k l h a → Anchor N′ k l h a
anchor-grow ss (x , y , n , yl , w) = x , y , ss n , yl , w

anchor-up : ∀ {N k l l′ h a} → Anchor N k l h a → l ⊑ l′ → Anchor N k l′ h a
anchor-up (x , y , n , yl , w) ll = x , y , n , ⊑-trans yl ll , w

-- A CARRY'S ANCHORS FROM ANOTHER'S: each row it carries into its instant
-- the other's, on a carrier under its own, or anchored anew past itself.
nest-or : ∀ {Γ} {M₀ : PMap} {LP₀ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
          {er : ∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)} {N N′ : PMap}
          {A Y A′ Y′} {f : Y → List A} {f′ : Y′ → List A′} {M M′ : PMap} {HP HE LP HP′ HE′ LP′ : Pos → Set}
          {t : EmissionSet A} {u : EmissionSet Y} {t′ : EmissionSet A′} {u′ : EmissionSet Y′} {s₀ s₀′ s₁ s₁′ : Pos}
          {c : CarryAt f M HP HE LP t u s₀ s₀′} {c′ : CarryAt f′ M′ HP′ HE′ LP′ t′ u′ s₁ s₁′}
        → N ⊆ᴹ N′
        → (∀ {k l e₀} → CarryAt.PB c′ k l → t′ k e₀ → (Unpinned e₀ → Live t′ k)
           → (Σ Pos λ l₀ → CarryAt.PB c k l₀ × l₀ ⊑ l × Σ (Ev A) λ e → t k e × (Unpinned e → Live t k)) ⊎ Σ Pos λ x → Σ Pos λ y → N′ x y × y ⊑ l × k ≺ x)
        → PBNest er N c → PBNest er N′ c′
nest-or ss dn ns i pb tk lv br ci e with dn pb tk lv
... | inj₁ (_ , pb₀ , ll , (_ , tk₀ , lv₀)) = anchor-up (anchor-grow ss (ns i pb₀ tk₀ lv₀ br ci e)) ll
... | inj₂ (x , y , n , yl , kx)            = x , y , n , yl , inj₂ kx

-- The same, each row on the other's carrier.
nest-via : ∀ {Γ} {M₀ : PMap} {LP₀ : Pos → Set} {dP : ∀ {X} → X ∈ Γ → Den X} {dE : ∀ {X} → X ∈ Γ → Den (AIE X)}
           {er : ∀ {X} (i : X ∈ Γ) → Bound M₀ LP₀ (dP i) (dE i)} {N N′ : PMap}
           {A Y A′ Y′} {f : Y → List A} {f′ : Y′ → List A′} {M M′ : PMap} {HP HE LP HP′ HE′ LP′ : Pos → Set}
           {t : EmissionSet A} {u : EmissionSet Y} {t′ : EmissionSet A′} {u′ : EmissionSet Y′} {s₀ s₀′ s₁ s₁′ : Pos}
           {c : CarryAt f M HP HE LP t u s₀ s₀′} {c′ : CarryAt f′ M′ HP′ HE′ LP′ t′ u′ s₁ s₁′}
         → N ⊆ᴹ N′ → (∀ {k l e₀} → CarryAt.PB c′ k l → t′ k e₀ → (Unpinned e₀ → Live t′ k) → CarryAt.PB c k l × Σ (Ev A) λ e → t k e × (Unpinned e → Live t k))
         → PBNest er N c → PBNest er N′ c′
nest-via {er = er} {c = c} {c′ = c′} ss dn =
  nest-or {er = er} {c = c} {c′ = c′} ss λ pb tk lv → let (pb₀ , r) = dn pb tk lv in inj₁ (_ , pb₀ , ⊑-refl _ , r)

-- What a carry gives at a pair of subscriptions: the map extended over
-- the subterm's worlds, keeping the joins, every binder's late carriers
-- past it, and the carry, its own late carriers anchored.
CarriesAt : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) (envP : DenEnv Γ) (envE : DenEnv Δ)
            (M₀ : PMap) → EnvRel M₀ ρ envP envE → Pos → Pos → Set₁
CarriesAt n ρ o envP envE M₀ er p p′ =
  Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (enter (approx n o envP) p) × Joins ρ envP envE er M × EnvPast er M
  × Σ (CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter (approx n o envP) p) (enter (approx n (elab ρ o) envE) p′) p p′)
      (λ c → PBNest er M c × Narrow c)

-- CARRIED under every environment of carried binders: subscribed at
-- admissible positions the map pairs, holding no hot row, its worlds
-- untouched.
-- A record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record Carry (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor carry
  field carries : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE
                → ∀ M₀ → Emb M₀ → (er : EnvRel M₀ ρ envP envE) → Joins ρ envP envE er M₀ → Nests er M₀ → Apart envP
                → ∀ p p′ → M₀ p p′ → Ok (Hots envP) p → Ok (Hots envE) p′ → Clear (Rows er) (Hots envP) p → Fresh (Hots envP) M₀ p
                → CarriesAt n ρ o envP envE M₀ er p p′

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER CARRIES its plain counterpart when its children
-- do, under every approximant.
postulate
  carry-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → Carry m ρ (cold c)
  carry-flatMap   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → Carry m ρ s
                  → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry m ρ′ (f a)) → Carry m ρ (flatMap op f s)

carry-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → Carry m ρ s → Carry m ρ (map f s)
carry-map n ρ f s (carry h) = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  mapped envP envE M₀ er p p′ (h envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr)
  where
    mapped : ∀ envP envE M₀ (er : EnvRel M₀ ρ envP envE) p p′ → CarriesAt n ρ s envP envE M₀ er p p′ → CarriesAt n ρ (map f s) envP envE M₀ er p p′
    mapped envP envE M₀ er p p′ (M , ms , hm′ , wi , br , jn′ , ep , c , nc , nr) =
      M , ms , hm′ , wi , (λ tk → br (proj₁ (proj₂ (MapRun.unmap f (approx n s envP) p tk)))) , jn′ , ep , c′
      , nest-via {er = er} {c = c} {c′ = c′} (λ m → m) down nc , MapCarry.narrowed f (approx n s envP) (approx n (elab ρ s) envE) p p′ c nr
      where
        c′ : CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter (approx n (map f s) envP) p) (enter (approx n (elab ρ (map f s)) envE) p′) p p′
        c′ = map-carry f (approx n s envP) (approx n (elab ρ s) envE) p p′ c

        down : ∀ {k l e₀} → CarryAt.PB c′ k l → enter (approx n (map f s) envP) p k e₀ → (Unpinned e₀ → Live (enter (approx n (map f s) envP) p) k)
             → CarryAt.PB c k l × Σ (Ev _) λ e → enter (approx n s envP) p k e × (Unpinned e → Live (enter (approx n s envP) p) k)
        down pb tk lv with MapRun.unmap f (approx n s envP) p tk
        ... | e , tk₀ , refl = pb , e , tk₀ , λ un sc → lv (un-map e un) (MapRun.lift f (approx n s envP) p sc)
          where
            un-map : ∀ {X Y : Set} {g : X → Y} (e : Ev X) → Unpinned e → Unpinned (mapEv g e)
            un-map (out _) _ = tt
            un-map skip    _ = tt
            un-map end     _ = tt
