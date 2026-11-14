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
-- THE CARRIERS ARE FIXED BEFORE THE BOUND (`Run`): a run's anchors and
-- carriers come first, then its simulation up to every bound any later
-- map holding them maps.  A connect's body may be cut at its own row,
-- whose image only the body's carriers give, while its readers need the
-- source simulated up to that same bound; fixed first, the source's
-- carriers are cut there after the body's are known.
--
-- A BOUND CUTS BOTH SIDES ALIKE: before it or under it (`Upto`,
-- `Under`).  Cut at a subscription, a run keeps its whole subscribe
-- burst on both sides, and the plain listing then lists all of it.
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
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; sub)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; hot; coldAt; Proper; DenEnv; _≺_; enter; approx)
open import denotation.Laws.Worlds using (_⊑_; W⁼; Hots; GoodEnv; Ok; Lawful)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SimPos using (UpTo)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- Maps of positions

PMap : Set₁
PMap = Pos → Pos → Set

_∪ᴹ_ : PMap → PMap → PMap
(M ∪ᴹ M′) x y = M x y ⊎ M′ x y

-- AN ORDER EMBEDDING: one image each, the order kept, leading kept and
-- reflected.
record Emb (M : PMap) : Set where
  field
    fun     : ∀ {x y y′} → M x y → M x y′ → y ≡ y′
    mono    : ∀ {x x′ y y′} → M x y → M x′ y′ → x ≺ x′ → y ≺ y′
    reflect : ∀ {x x′ y y′} → M x y → M x′ y′ → y ⊑ y′ → x ⊑ x′
    pres    : ∀ {x x′ y y′} → M x y → M x′ y′ → x ⊑ x′ → y ⊑ y′

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
Upto (just c) k = UpTo c k

-- Up to the bound's image: before its anchor, or under it.
Under : PMap → Maybe Pos → Pos → Set
Under M nothing  _ = ⊤
Under M (just c) l = Σ Pos λ y → M c y × UpTo y l

-- The bound has an image.
Mapped : PMap → Maybe Pos → Set
Mapped M nothing  = ⊤
Mapped M (just c) = Σ Pos (M c)

-- THE PLAIN ROWS UP TO A BOUND, listed, each with its row.
ListedB : ∀ {A} → EmissionSet A → Maybe Pos → Set
ListedB {A} T c = Σ (List Pos) λ ks → (∀ {k e} → T k e → Upto c k → k ∈ ks) × (∀ {k} → k ∈ ks → Σ (Ev A) (T k))

-- The elaborated rows `U` simulate the plain rows `T` along `M`, up to
-- the bound `c`, each carried value and end by its carrier (`Img`).
record Sim {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) (Img : Pos → Pos → Set) (c : Maybe Pos)
           (T : EmissionSet A) (U : EmissionSet B) : Set where
  field
    fwd     : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev B) λ e′ → U l e′ × Mt V e e′
    val←    : ∀ {l b} → U l (out b) → Sh b → Under M c l → Σ Pos λ k → Img k l × Σ A λ a → T k (out a) × V a b
    end←    : ∀ {l} → U l end → Under M c l → Σ Pos λ k → Img k l × T k end
    upto    : Σ (List Pos) λ ls → (∀ {l e′} → U l e′ → Under M c l → l ∈ ls) × (∀ {l} → l ∈ ls → Σ (Ev B) (U l))

-- One map within another.
_⊆ᴹ_ : PMap → PMap → Set
M ⊆ᴹ M′ = ∀ {x y} → M x y → M′ x y

-- A RUN: one carrier each, anchored in `M`, and then the simulation up
-- to every bound a later order embedding holding `M` maps, wherever the
-- plain rows up to it are listed and what the run reads (`L`) is.
record Run {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) (L : PMap → Maybe Pos → Set)
           (T : EmissionSet A) (U : EmissionSet B) : Set₁ where
  field
    Img     : Pos → Pos → Set
    img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    ext     : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
    sim     : ∀ A′ → M ⊆ᴹ A′ → Emb A′ → ∀ c → Mapped A′ c → L A′ c → ListedB T c → Sim V Sh A′ Img c T U

-- A FINITE PLAIN RUN HAS A FINITE ELABORATED RUN.
sim-whole : ∀ {A B} {V : A → B → Set} {Sh M Img T U} → Sim V Sh M Img nothing T U → Σ (List Pos) λ ls → ∀ {l e} → U l e → l ∈ ls
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
-- a run of the proper source rows wherever what the source reads is
-- listed (`need`), and every point the ambient map puts under a source
-- row a join.
record HotSim (Amb : PMap) {X : Set} (d : Den X) (d′ : Den (AIE X)) : Set₁ where
  field
    {Δ₀}   : List Set
    src    : Den X
    at     : Pos
    m      : ℕ
    core   : Obs Timeline Δ₀ (IE X)
    env₀   : DenEnv Δ₀
    at′    : Pos
    need   : PMap → Maybe Pos → Set
    isP    : d ≡ hot (Proper (enter src at))
    isE    : d′ ≡ hot (Proper (enter (approx m (annotate core) env₀) at′))
    law    : Lawful (Proper (enter src at))
    law′   : Lawful (Proper (enter (approx m (annotate core) env₀) at′))
    run    : Run AShows AShown Amb need (Proper (enter src at)) (Proper (enter (approx m (annotate core) env₀) at′))
    joins  : Joins Amb Amb (Proper (enter src at)) (Run.Img run)

  rows : EmissionSet X
  rows = Proper (enter src at)

  rows′ : EmissionSet (AIE X)
  rows′ = Proper (enter (approx m (annotate core) env₀) at′)

  car : Pos → Pos → Set
  car = Run.Img run

EnvSim : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → PMap → DenEnv Γ → DenEnv Δ → Set₁
EnvSim {Γ} ρ Amb env env′ = ∀ {X} (i : X ∈ Γ) → HotSim Amb (lookup env i) (lookup env′ (ρ (∈-map⁺ AIE i)))

-- One fact of each bound hot.
Allᴱ : ∀ (Γ : List Set) → (∀ {X} → X ∈ Γ → Set) → Set
Allᴱ []      _ = ⊤
Allᴱ (_ ∷ Γ) f = f (here refl) × Allᴱ Γ (λ i → f (there i))

allᴱ : ∀ {Γ} {f : ∀ {X} → X ∈ Γ → Set} → Allᴱ Γ f → ∀ {X} (i : X ∈ Γ) → f i
allᴱ (l , _)  (here refl) = l
allᴱ (_ , ls) (there i)   = allᴱ ls i

-- Every bound hot's rows up to the bound listed, and the later map
-- keeping its joins.
EnvListed : ∀ {Γ Δ} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) {Amb} env env′ → EnvSim ρ Amb env env′ → PMap → Maybe Pos → Set
EnvListed {Γ} _ _ _ es A′ c = Allᴱ Γ (λ i → ListedB (HotSim.rows (es i)) c × Joins A′ A′ (HotSim.rows (es i)) (HotSim.car (es i)))

-- What each bound hot reads is listed wherever the hots are.
EnvNeeds : ∀ {Γ Δ} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) {Amb} env env′ → EnvSim ρ Amb env env′ → Set₁
EnvNeeds {Γ} ρ env env′ es = ∀ {X} (i : X ∈ Γ) A′ c → EnvListed ρ env env′ es A′ c → HotSim.need (es i) A′ c

-- What a map adds keeps every bound hot's joins.
EnvJoins : ∀ {Γ Δ} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) {Amb} env env′ → EnvSim ρ Amb env env′ → PMap → Set₁
EnvJoins {Γ} _ {Amb = Amb} _ _ es M = ∀ {X} (i : X ∈ Γ) → Joins (Amb ∪ᴹ M) M (HotSim.rows (es i)) (HotSim.car (es i))

-- NO POSITION HOLDS ROWS OF TWO HOTS: a hot's rows lie in its source's
-- world, which holds no row of a hot already bound.
Apart : ∀ {Γ} → DenEnv Γ → Set
Apart []ᴬ              = ⊤
Apart (hot t ∷ᴬ ρ)    = (∀ {q e} → t q e → Hots ρ q → ⊥) × Apart ρ
Apart (coldAt _ ∷ᴬ ρ) = Apart ρ

-- SIMULATED under every environment of simulated hots, at every
-- subscription pair the ambient map holds alone in its worlds: what the
-- map adds lies in the pair's worlds, pairs nothing under a row, and
-- keeps the joins, and the run is simulated wherever the hots are
-- listed.  A record, so that a statement about a former is compared by
-- its arguments, never by the elaborated tree its meaning unfolds to.
record SimIH (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor sih
  field
    sims : ∀ (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) → GoodEnv env → GoodEnv env′ → Apart env
         → (es : EnvSim ρ Amb env env′) → EnvNeeds ρ env env′ es → Emb Amb
         → ∀ p p′ → Amb p p′ → Fresh (Hots env) (Hots env′) Amb p p′ → Ok (Hots env) p → Ok (Hots env′) p′ → ¬ Hots env p
         → Σ PMap λ M → Local (Hots env) (Hots env′) p p′ M × Emb (Amb ∪ᴹ M) × NoneUnder M (enter (approx n o env) p)
           × EnvJoins ρ env env′ es M
           × Run Shows Shown (Amb ∪ᴹ M) (EnvListed ρ env env′ es) (enter (approx n o env) p) (enter (approx n (elab ρ o) env′) p′)
