{-# OPTIONS --guardedness #-}

-- THE CONSUMPTION: the elaborated program reads what its plain program
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

module simultaneous.Consume where

open import Data.Bool using (Bool; true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([]; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; _<ᵇ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; <⇒<ᵇ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; _∙_; sub; last; frame; cascade; tick)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; hot; Proper; DenEnv; _≺_; _≼_; enter; approx)
open import denotation.Laws.Worlds using (_⊑_; Hots; GoodEnv; Ok)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Listing using (Listing)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate; elaborate)

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
-- A finite run, listed

maxTick : List Pos → ℕ
maxTick []       = 0
maxTick (k ∷ ks) = tick k ⊔ maxTick ks

tick≤ : ∀ {k ks} → k ∈ ks → tick k ≤ maxTick ks
tick≤ {ks = k′ ∷ ks} (here refl) = m≤m⊔n (tick k′) (maxTick ks)
tick≤ {ks = k′ ∷ ks} (there m)   = ≤-trans (tick≤ m) (m≤n⊔m (tick k′) (maxTick ks))

-- A position past every one of a list: an instant at a later tick.
beyond : List Pos → Pos
beyond ks = cascade (suc (maxTick ks)) root last ∙ []

beyond-≺ : ∀ {k ks} → k ∈ ks → k ≺ beyond ks
beyond-≺ {frame ∙ _}         m = tt
beyond-≺ {cascade t e a ∙ _} {ks} m with t <ᵇ suc (maxTick ks) | <⇒<ᵇ (s≤s (tick≤ m))
... | true | _ = tt

-- A FINITE RUN THAT LISTS IS LISTED WHOLE, each row with its row: all of
-- it lies before a position past its rows.
listed-all : ∀ {A} {T : EmissionSet A} → Listing T → (ks : List Pos) → (∀ {k e} → T k e → k ∈ ks) → ListedB T nothing
listed-all lst ks every with lst {beyond ks} (ks , λ x _ → every x)
... | ks′ , cov , back = ks′ , (λ x _ → cov x (beyond-≺ (every x))) , λ m → proj₂ (back m)

------------------------------------------------------------------------
-- The elaboration simulates its program

-- A value shown is the plain value; a mark shows none.
Shows : ∀ {A} → A → IE A → Set
Shows a b = valuesOf b ≡ a ∷ []

Shown : ∀ {A} → IE A → Set
Shown b = ¬ (valuesOf b ≡ [])

-- AN ENVIRONMENT OF SIMULATED HOTS: each plain binder the proper rows of
-- a source a connect subscribed, its elaborated binder the proper rows
-- of that source's elaboration, annotated, subscribed at the image; the
-- source's rows simulated up to a bound past the reader's.
HotSim : ∀ {X} → PMap → Maybe Pos → Den X → Den (AIE X) → Set₁
HotSim {X} Amb c d d′ =
  Σ (Den X) λ s → Σ Pos λ q → Σ ℕ λ m → Σ (List Set) λ Δ₀ → Σ (Obs Timeline Δ₀ (IE X)) λ x → Σ (DenEnv Δ₀) λ env₀ → Σ Pos λ q′
  → Σ (Maybe Pos) λ c₀ → d ≡ hot (Proper (enter s q)) × d′ ≡ hot (Proper (enter (approx m (annotate x) env₀) q′))
  × Within c c₀ × Sim Shows Shown Amb q c₀ (enter s q) (enter (approx m x env₀) q′)

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

-- EACH ELABORATED FORMER SIMULATES ITS FORMER when its children do.
postulate
  sim-cold      : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → SimIH n ρ (cold c)
  sim-empty     : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → SimIH n ρ (empty {A = A})
  sim-of        : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : List A) → SimIH n ρ (of xs)
  sim-map       : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) (s : Obs Timeline Γ A)
                → SimIH n ρ s → SimIH n ρ (map f s)
  sim-scan      : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) (z : B) (s : Obs Timeline Γ A)
                → SimIH n ρ s → SimIH n ρ (scan f z s)
  sim-takeWhile : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (keep : A → Bool) (s : Obs Timeline Γ A)
                → SimIH n ρ s → SimIH n ρ (takeWhile i keep s)
  sim-flatMap   : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
                → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ s)
                → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ (f a)) → SimIH n ρ (flatMap op f s)
  sim-connect   : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                → SimIH n ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → SimIH n ρ′ b) → SimIH n ρ (connect s b)
  sim-connected : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → SimIH n ρ (connected i)
  -- THE BOTTOM APPROXIMANT, and each further one under a `defer`'s guard.
  sim-⊥         : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → SimIH zero ρ (defer l)
  sim-next      : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
                → SimIH n ρ (Later.force l) → SimIH (suc n) ρ (defer l)

sim-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → SimIH n ρ o
sim-approx n       ρ (cold c)          = sim-cold n ρ c
sim-approx n       ρ empty             = sim-empty n ρ
sim-approx n       ρ (of xs)           = sim-of n ρ xs
sim-approx n       ρ (map f s)         = sim-map n ρ f s (sim-approx n ρ s)
sim-approx n       ρ (scan f z s)      = sim-scan n ρ f z s (sim-approx n ρ s)
sim-approx n       ρ (takeWhile i p s) = sim-takeWhile n ρ i p s (sim-approx n ρ s)
sim-approx n       ρ (flatMap op f s)  = sim-flatMap n ρ op f s (λ ρ′ → sim-approx n ρ′ s) λ a ρ′ → sim-approx n ρ′ (f a)
sim-approx n       ρ (connect s b)     = sim-connect n ρ s b (sim-approx n ρ s) λ ρ′ → sim-approx n ρ′ b
sim-approx n       ρ (connected i)     = sim-connected n ρ i
sim-approx zero    ρ (defer l)         = sim-⊥ ρ l
sim-approx (suc n) ρ (defer l)         = sim-next n ρ l (sim-approx n ρ (Later.force l))

-- THE CLOSED PROGRAM: its elaboration, restamped beside the subscribe
-- and completion marks, simulates it from the root, wherever its rows
-- are listed.
postulate
  sim-top : ∀ n {A} (o : Obs Timeline [] A) → SimIH n (λ i → i) o → ListedB (enter (approx n o []) root) nothing → Σ PMap λ M → Emb M
          × Sim Shows Shown M root nothing (enter (approx n o []) root) (enter (approx n (elaborate o) []) root)

sim-root : ∀ n {A} (o : SObs [] A) → ListedB (enter (approx n (plain o) []) root) nothing → Σ PMap λ M → Emb M
         × Sim Shows Shown M root nothing (enter (approx n (plain o) []) root) (enter (approx n (elaborate (plain o)) []) root)
sim-root n o = sim-top n (plain o) (sim-approx n (λ i → i) (plain o))
