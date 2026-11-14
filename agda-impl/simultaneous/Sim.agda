{-# OPTIONS --guardedness #-}

-- THE SIMULATION: the elaborated program reads what its plain program
-- reads, up to a bound.  Each plain value and end up to it has a CARRIER,
-- an elaborated row of its kind (`Sim.fwd`); each value shown and each
-- end of the elaborated run before the bound's image carries one
-- (`Sim.val←`, `Sim.end←`); and the elaborated rows before the bound's
-- image are listed (`Sim.upto`).  Unbounded, a finite plain run has a
-- finite elaborated run (`sim-whole`).
--
-- AN EXACT SIMULATION, BOTH WAYS.  Every operator above decides from
-- values, ends and their order across streams (a take's failure, a
-- switch's next outer value, an exhaust's busy lane, a concat's
-- hand-off), and a reading keeps a row only with finitely many before
-- it, so neither side's rows are bounded by the other's unless each
-- decision transfers both ways.  Nothing decides from a skip or a pin,
-- so neither is carried: a skip has no canonical carrier, the marks
-- beside a value being skips of the elaborated run too.
--
-- ORDER ACROSS STREAMS IS ONE EMBEDDING (`Emb`): a plain row maps to the
-- ANCHOR its carrier lies under, and the anchors keep the plain order,
-- an anchor under another only for a row under another.  A carrier is
-- ONE row (`Sim.img-fun`): a reader joins a hot row under its carrier,
-- and two readers' joins of one row must lie under one position.
--
-- UNDER A HOT ROW, ONLY A READER'S JOIN (`Joins`): the ambient map puts
-- a point strictly under a row of a bound hot only as a reader's join at
-- a subscription it maps, under the row's carrier joined at the
-- subscription's image.  So a new reader's joins fall between the
-- earlier ones in their subscriptions' order.
--
-- THE ROWS UP TO THE BOUND ARE LISTED, EACH WITH ITS ROW: the plain
-- (`ListedB`) and the elaborated (`Sim.upto`).  Where an elaborated row
-- lies is data: a reader's joins and a scan's marks count routes, a lane
-- is its outer value's, and a reader's scan folds the annotated rows
-- before it, marks included, which no plain row names.  So the rows
-- before a row are found only from the rows before it AND what they
-- hold, and a position list does not suffice.
--
-- THE SUBSCRIPTION IS NO HOT ROW.  A reader whose hot ended before it
-- ends at once, under its subscription with a plain label; were the
-- subscription a hot row, that end would lie under it as no join.
-- A bound is what a decision cuts a child at: a take at its failure, a
-- switch's lane at the next outer value, a connect's source at its
-- body's end.

module simultaneous.Sim where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Position using (Pos; Label; Path; root; _≟ᵖ_; _⊕_; sub)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; hot; coldAt; Proper; DenEnv; _≺_; _≼_; enter; approx)
open import denotation.Laws.Worlds using (_⊑_; W⁼; Hots; GoodEnv; Ok; Lawful)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- Maps of positions

PMap : Set₁
PMap = Pos → Pos → Set

_∪ᴹ_ : PMap → PMap → PMap
(M ∪ᴹ M′) x y = M x y ⊎ M′ x y

-- AN ORDER EMBEDDING: one image each, the order kept, leading reflected.
record Emb (M : PMap) : Set where
  field
    fun     : ∀ {x y y′} → M x y → M x y′ → y ≡ y′
    mono    : ∀ {x x′ y y′} → M x y → M x′ y′ → x ≺ x′ → y ≺ y′
    reflect : ∀ {x x′ y y′} → M x y → M x′ y′ → y ⊑ y′ → x ⊑ x′

-- `x` lies at or under a position of the world with `p`.
Below : (Pos → Set) → Pos → Pos → Set
Below H p x = Σ Pos λ w → W⁼ H p w × w ⊑ x

-- A map within a subscription pair's worlds.
Local : (Pos → Set) → (Pos → Set) → Pos → Pos → PMap → Set
Local H H′ p p′ M = ∀ {x y} → M x y → Below H p x × Below H′ p′ y

-- Within the pair's worlds, an ambient map holds the pair alone.
Fresh : (Pos → Set) → (Pos → Set) → PMap → Pos → Pos → Set
Fresh H H′ Amb p p′ = ∀ {x y} → Amb x y → (Below H p x → x ≡ p) × (Below H′ p′ y → y ≡ p′)

-- The map pairs nothing strictly under a row.
NoneUnder : ∀ {A} → PMap → EmissionSet A → Set
NoneUnder M t = ∀ {k e x y} → t k e → M x y → k ⊑ x → x ≡ k

------------------------------------------------------------------------
-- The simulation

-- What a simulation carries: a value or an end.
data Carried {A : Set} : Ev A → Set where
  c-out : ∀ {a} → Carried (out a)
  c-end : Carried end

-- A plain event and an elaborated one of its kind: a value and a value
-- showing it, an end and an end.
data Mt {A B : Set} (V : A → B → Set) : Ev A → Ev B → Set where
  m-out : ∀ {a b} → V a b → Mt V (out a) (out b)
  m-end : Mt V end end

-- Up to a plain bound: before it, or at it.
Upto : Maybe Pos → Pos → Set
Upto nothing  _ = ⊤
Upto (just c) k = k ≼ c

-- Up to the bound's image: before its anchor, or under it.
Under : PMap → Maybe Pos → Pos → Set
Under M nothing  _ = ⊤
Under M (just c) l = Σ Pos λ y → M c y × (l ≺ y ⊎ y ⊑ l)

-- The bound has an image.
Mapped : PMap → Maybe Pos → Set
Mapped M nothing  = ⊤
Mapped M (just c) = Σ Pos (M c)

-- One bound within another.
Within : Maybe Pos → Maybe Pos → Set
Within _        nothing   = ⊤
Within nothing  (just _)  = ⊥
Within (just c) (just c₀) = c ≼ c₀

-- THE PLAIN ROWS UP TO A BOUND, listed, each with its row.
ListedB : ∀ {A} → EmissionSet A → Maybe Pos → Set
ListedB {A} T c = Σ (List Pos) λ ks → (∀ {k e} → T k e → Upto c k → k ∈ ks) × (∀ {k} → k ∈ ks → Σ (Ev A) (T k))

-- The elaborated rows `U` simulate the plain rows `T` along `M`, up to
-- the bound `c`, each carried value and end by its carrier (`Img`).
record Sim {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) (c : Maybe Pos)
           (T : EmissionSet A) (U : EmissionSet B) : Set₁ where
  field
    Img     : Pos → Pos → Set
    img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    ext     : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
    bnd     : Mapped M c
    fwd     : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev B) λ e′ → U l e′ × Mt V e e′
    val←    : ∀ {l b} → U l (out b) → Sh b → Under M c l → Σ Pos λ k → Img k l × Σ A λ a → T k (out a) × V a b
    end←    : ∀ {l} → U l end → Under M c l → Σ Pos λ k → Img k l × T k end
    upto    : Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under M c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev B) (U l))

-- A FINITE PLAIN RUN HAS A FINITE ELABORATED RUN.
sim-whole : ∀ {A B} {V : A → B → Set} {Sh M T U} → Sim V Sh M nothing T U → Σ (List Pos) λ ls → ∀ {l e} → U l e → l ∈ ls
sim-whole S = proj₁ (Sim.upto S) , λ y → proj₁ (proj₂ (Sim.upto S)) y tt

------------------------------------------------------------------------
-- The elaboration simulates its program

-- A value shown is the plain value; a mark shows none.
Shows : ∀ {A} → A → IE A → Set
Shows a b = valuesOf b ≡ a ∷ []

Shown : ∀ {A} → IE A → Set
Shown b = ¬ (valuesOf b ≡ [])

-- What an annotated row shows: the values of the emit it carries.
annValues : ∀ {X} → AIE X → List X
annValues (_ , just x)  = valuesOf x
annValues (_ , nothing) = []

AShows : ∀ {A} → A → AIE A → Set
AShows a b = annValues b ≡ a ∷ []

AShown : ∀ {A} → AIE A → Set
AShown b = ¬ (annValues b ≡ [])

-- Every point `P` puts strictly under a row of the hot `t` is a reader's
-- join, at a subscription `S` maps, under the row's carrier joined at
-- the subscription's image.
Joins : ∀ {X} → PMap → PMap → EmissionSet X → (Pos → Pos → Set) → Set
Joins S P t Img = ∀ {x y q a σ e₀} → P x y → t q e₀ → x ≡ q ⊕ (a ∷ σ)
  → Σ Pos λ e → a ≡ sub e × Σ Pos λ e′ → S e e′ × Σ Pos λ L → Img q L × (L ⊕ [ sub e′ ]) ⊑ y

-- A SIMULATED HOT: the plain binder the proper rows of a source a
-- connect subscribed, its elaborated binder the proper rows of that
-- source's elaboration annotated, both lawful, the proper annotated rows
-- simulating the proper source rows up to a bound past the reader's, and
-- every point the ambient map puts under a source row a join.
record HotSim (Amb : PMap) (c : Maybe Pos) {X : Set} (d : Den X) (d′ : Den (AIE X)) : Set₁ where
  field
    {Δ₀}   : List Set
    src    : Den X
    at     : Pos
    m      : ℕ
    core   : Obs Timeline Δ₀ (IE X)
    env₀   : DenEnv Δ₀
    at′    : Pos
    c₀     : Maybe Pos
    isP    : d ≡ hot (Proper (enter src at))
    isE    : d′ ≡ hot (Proper (enter (approx m (annotate core) env₀) at′))
    law    : Lawful (Proper (enter src at))
    law′   : Lawful (Proper (enter (approx m (annotate core) env₀) at′))
    within : Within c c₀
    sim    : Sim AShows AShown Amb c₀ (Proper (enter src at)) (Proper (enter (approx m (annotate core) env₀) at′))
    joins  : Joins Amb Amb (Proper (enter src at)) (Sim.Img sim)

  rows : EmissionSet X
  rows = Proper (enter src at)

  rows′ : EmissionSet (AIE X)
  rows′ = Proper (enter (approx m (annotate core) env₀) at′)

  car : Pos → Pos → Set
  car = Sim.Img sim

EnvSim : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → PMap → Maybe Pos → DenEnv Γ → DenEnv Δ → Set₁
EnvSim {Γ} ρ Amb c env env′ = ∀ {X} (i : X ∈ Γ) → HotSim Amb c (lookup env i) (lookup env′ (ρ (∈-map⁺ AIE i)))

-- What a map adds keeps every bound hot's joins.
EnvJoins : ∀ {Γ Δ} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) {Amb c} env env′ → EnvSim ρ Amb c env env′ → PMap → Set₁
EnvJoins {Γ} _ {Amb = Amb} _ _ es M = ∀ {X} (i : X ∈ Γ) → Joins (Amb ∪ᴹ M) M (HotSim.rows (es i)) (HotSim.car (es i))

-- NO POSITION HOLDS ROWS OF TWO HOTS: a hot's rows lie in its source's
-- world, which holds no row of a hot already bound.
Apart : ∀ {Γ} → DenEnv Γ → Set
Apart []ᴬ              = ⊤
Apart (hot t ∷ᴬ ρ)    = (∀ {q e} → t q e → Hots ρ q → ⊥) × Apart ρ
Apart (coldAt _ ∷ᴬ ρ) = Apart ρ

-- THE BOUND IS A VALUE OR END of the run, or an ambient point whose
-- image leads no elaborated hot row and which leads no subscription at
-- `p`: everything under the image is up to the bound, so an image over a
-- hot's rows, or over the run's own, would bound none of them by the
-- plain bound.
BoundOk : ∀ {A} → (Pos → Set) → PMap → Pos → EmissionSet A → Maybe Pos → Set
BoundOk     H′ Amb p T nothing  = ⊤
BoundOk {A} H′ Amb p T (just c) = (Σ Pos λ y → Amb c y × (∀ {h} → H′ h → y ⊑ h → ⊥) × ¬ (c ⊑ p)) ⊎ Σ (Ev A) λ e → Carried e × T c e

-- SIMULATED under every environment of simulated hots, at every
-- subscription pair the ambient map holds alone in its worlds, up to
-- every bound its rows are listed to; what the map adds lies in the
-- pair's worlds, pairs nothing under a row, and keeps the joins.  A
-- record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record SimIH (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor sih
  field
    sims : ∀ (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (c : Maybe Pos) → GoodEnv env → GoodEnv env′ → Apart env
         → (es : EnvSim ρ Amb c env env′) → Emb Amb
         → ∀ p p′ → Amb p p′ → Fresh (Hots env) (Hots env′) Amb p p′ → Ok (Hots env) p → Ok (Hots env′) p′ → ¬ Hots env p
         → ListedB (enter (approx n o env) p) c → BoundOk (Hots env′) Amb p (enter (approx n o env) p) c
         → Σ PMap λ M → Local (Hots env) (Hots env′) p p′ M × Emb (Amb ∪ᴹ M) × NoneUnder M (enter (approx n o env) p)
           × EnvJoins ρ env env′ es M × Sim Shows Shown (Amb ∪ᴹ M) c (enter (approx n o env) p) (enter (approx n (elab ρ o) env′) p′)
