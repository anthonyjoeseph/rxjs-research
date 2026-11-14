{-# OPTIONS --guardedness #-}

-- THE SIMULATION: the elaborated program reads what its plain program
-- reads, up to a bound.  Each plain row up to it has an elaborated row
-- of its kind (`Sim.fwd`); each value, end and pin the elaborated run
-- shows before the bound's image is a plain row's (`Sim.val←`,
-- `Sim.end←`, `Sim.pin←`); and the elaborated rows before the bound's
-- image are listed (`Sim.upto`).  Unbounded, a finite plain run has a
-- finite elaborated run (`sim-whole`).
--
-- AN EXACT SIMULATION, BOTH WAYS.  Every operator above decides from
-- values, ends and their order across streams (a take's failure, a
-- switch's next outer value, an exhaust's busy lane, a concat's
-- hand-off), and a reading keeps a row only with finitely many before
-- it, so neither side's rows are bounded by the other's unless each
-- decision transfers both ways.
--
-- ORDER ACROSS STREAMS IS ONE EMBEDDING (`Emb`): a plain row maps to the
-- ANCHOR its elaborated row lies under, and the anchors keep the plain
-- order, an anchor under another only for a row under another.
--
-- THE PLAIN ROWS UP TO THE BOUND ARE LISTED, EACH WITH ITS ROW
-- (`ListedB`).  Where an elaborated row lies is data: a reader's joins
-- and a scan's marks count routes, a lane is its outer value's.  So the
-- elaborated rows before a plain row are found only from the plain rows
-- before it AND what they hold, and a position list does not suffice.
-- A bound is what a decision cuts a child at: a take at its failure, a
-- switch's lane at the next outer value, a connect's source at its
-- body's end.

module simultaneous.Sim where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; _∙_; ix; sub; cascade)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; hot; Proper; DenEnv; _≺_; _≼_; enter; approx)
open import denotation.Laws.Worlds using (_⊑_; Hots; GoodEnv; Ok)
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

-- BELOW A SUBSCRIPTION: under it, joined to a hot by a reader below it,
-- or in an instant a timer created below it fires.
data Desc (p : Pos) : Pos → Set where
  d-in   : ∀ {x} → p ⊑ x → Desc p x
  d-sub  : ∀ {x e zs} → Desc p e → Desc p (x ⊕ (sub e ∷ zs))
  d-fire : ∀ {τ c l zs} → Desc p c → Desc p (cascade τ c l ∙ zs)

-- A map below a subscription pair.
Local : Pos → Pos → PMap → Set
Local p p′ M = ∀ {x y} → M x y → Desc p x × Desc p′ y

-- Below the pair, an ambient map holds the pair alone.
Fresh : PMap → Pos → Pos → Set
Fresh Amb p p′ = ∀ {x y} → Amb x y → (Desc p x → x ≡ p) × (Desc p′ y → y ≡ p′)

------------------------------------------------------------------------
-- The simulation

-- A plain event and an elaborated one of its kind: a value and a value
-- showing it, a skip and a skip or a value showing nothing, an end and an
-- end, a pin and a pin of its connect's image.
data Mt {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) : Ev A → Ev B → Set where
  m-out  : ∀ {a b} → V a b → Mt V Sh M (out a) (out b)
  m-skip : Mt V Sh M skip skip
  m-mark : ∀ {b} → ¬ Sh b → Mt V Sh M skip (out b)
  m-end  : Mt V Sh M end end
  m-pin  : ∀ {r r′} → M r r′ → Mt V Sh M (pin r) (pin r′)

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

-- The elaborated rows `U`, subscribed at `p′`, simulate the plain rows
-- `T`, subscribed at `p`, along `M`, up to the bound `c`.
record Sim {A B : Set} (V : A → B → Set) (Sh : B → Set) (M : PMap) (p : Pos) (c : Maybe Pos)
           (T : EmissionSet A) (U : EmissionSet B) : Set where
  field
    bnd   : Mapped M c
    fwd   : ∀ {k e} → T k e → Upto c k → Σ Pos λ y → M k y × Σ Pos λ l → y ⊑ l × Σ (Ev B) λ e′ → U l e′ × Mt V Sh M e e′
    val←  : ∀ {l b} → U l (out b) → Sh b → Under M c l → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × Σ A λ a → T k (out a) × V a b
    end←  : ∀ {l} → U l end → Under M c l → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × T k end
    pin←  : ∀ {l r r′} → U l (pin r′) → M r r′ → Under M c l → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × T k (pin r)
    upto  : Σ (List Pos) λ ls → ∀ {l e′} → U l e′ → Under M c l → l ∈ ls

-- A FINITE PLAIN RUN HAS A FINITE ELABORATED RUN.
sim-whole : ∀ {A B} {V : A → B → Set} {Sh M p T U} → Sim V Sh M p nothing T U → Σ (List Pos) λ ls → ∀ {l e} → U l e → l ∈ ls
sim-whole S = proj₁ (Sim.upto S) , λ y → proj₂ (Sim.upto S) y tt

------------------------------------------------------------------------
-- The elaboration simulates its program

-- A value shown is the plain value; a mark shows none.
Shows : ∀ {A} → A → IE A → Set
Shows a b = valuesOf b ≡ a ∷ []

Shown : ∀ {A} → IE A → Set
Shown b = ¬ (valuesOf b ≡ [])

-- AN ENVIRONMENT OF SIMULATED HOTS: each plain binder the proper rows of
-- a source a connect subscribed, its elaborated binder the proper rows
-- of that source's elaboration, annotated, subscribed at the image, which
-- subscribes the elaboration below it; the source's rows simulated up to
-- a bound past the reader's.
HotSim : ∀ {X} → PMap → Maybe Pos → Den X → Den (AIE X) → Set₁
HotSim {X} Amb c d d′ =
  Σ (Den X) λ s → Σ Pos λ q → Σ ℕ λ m → Σ (List Set) λ Δ₀ → Σ (Obs Timeline Δ₀ (IE X)) λ x → Σ (DenEnv Δ₀) λ env₀ → Σ Pos λ q′
  → Σ (Maybe Pos) λ c₀ → d ≡ hot (Proper (enter s q)) × d′ ≡ hot (Proper (enter (approx m (annotate x) env₀) q′))
  × Within c c₀ × Sim Shows Shown Amb q c₀ (enter s q) (enter (approx m x env₀) (q′ ⊕ [ ix 1 ]))

EnvSim : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → PMap → Maybe Pos → DenEnv Γ → DenEnv Δ → Set₁
EnvSim {Γ} ρ Amb c env env′ = ∀ {X} (i : X ∈ Γ) → HotSim Amb c (lookup env i) (lookup env′ (ρ (∈-map⁺ AIE i)))

-- The bound is the ambient's, or a row of the run.
BoundOk : ∀ {A} → PMap → EmissionSet A → Maybe Pos → Set
BoundOk     Amb T nothing  = ⊤
BoundOk {A} Amb T (just c) = Σ Pos (Amb c) ⊎ Σ (Ev A) (T c)

-- SIMULATED under every environment of simulated hots, at every
-- subscription pair the ambient map holds alone below it, up to every
-- bound its rows are listed to.  A record, so that a statement about a
-- former is compared by its arguments, never by the elaborated tree its
-- meaning unfolds to.
record SimIH (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor sih
  field
    sims : ∀ (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (c : Maybe Pos) → GoodEnv env → GoodEnv env′ → EnvSim ρ Amb c env env′ → Emb Amb
         → ∀ p p′ → Amb p p′ → Fresh Amb p p′ → Ok (Hots env) p → Ok (Hots env′) p′
         → ListedB (enter (approx n o env) p) c → BoundOk Amb (enter (approx n o env) p) c
         → Σ PMap λ M → Local p p′ M × Emb (Amb ∪ᴹ M)
           × Sim Shows Shown (Amb ∪ᴹ M) p c (enter (approx n o env) p) (enter (approx n (elab ρ o) env′) p′)

