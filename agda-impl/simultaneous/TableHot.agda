{-# OPTIONS --guardedness #-}

-- THE CONNECT'S HOT: the source listed under the connect's second label,
-- its two hots listed off it, the map a body reads them by, and a
-- reader's record of each.
--
-- The plain reader rejoins each hot row past its subscription one label
-- down (`Tb.rejoin`), a pin as a skip.  The elaborated reader reads the
-- annotated hot (`annotate`): each emit of the elaborated source is a
-- value of the annotated hot one label under the annotation's reader
-- (`reader*`), rejoined one label under the reader's subscription, and
-- emitted at `emitAt` of that row by `each₂`; a skip stays a skip.  So a
-- row's image is its hot row's source image carried through both labels
-- and, if the elaborated source emits there, to its emit (`imgAt`).
--
-- A hot pin's skip, and a skip of a source row late for the source, is
-- late for the reader: it has no image, only the source's late
-- placement carried the same way.
module simultaneous.TableHot where

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; T; if_then_else_; _∧_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_; does)

open import Tree using (Obs; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; inside; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; Unpinned; pin; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; Row; properAt; ends; rows; allᵇ; anyᵇ; _≼ᵇ_)
open import quickcheck.Tabled.Exact.Base using (when⁻)
open import simultaneous.SObs using (lone; ext; module Elaborate)
open import simultaneous.Listing using (listC-ok; UncutEnv)
open import simultaneous.TableCorr using (Rel; Same; same; φ≡; nl→; Scope; Rows; TR; Corr; Cons; Got; keys; in-keys)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv
  using (Ren; HotMap; hotMap; π; relMap; scopeOf; Tab; Tab*; got-ok; pin-ok; after-ok; pin-after-ok;
  up; _⊕ˡ_; Linked; Cut; Alike; Aligned; Maps; Rest; Out; _⊢_; HotR; EnvR; maps; lw; lw*;
  Admits; listHot; den-cons; tab-func; tab-flat)
open import simultaneous.TableFlat using (if-≡; module TabRows)
open import simultaneous.LaneEndSched using (emitAt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)
open TabRows using (endAt; endsOf)

-- The annotated hot rows: the elaborated source's own, rejoined under the
-- reader that the annotation's concat subscribes first.
reader* : Pos → Pos
reader* p* = p* ⊕ˡ (ix 1 ∷ ix 0 ∷ ix 0 ∷ ix 1 ∷ [])

-- A hot's proper rows are among its rows.
proper⊆ : ∀ {X} es (rs : List (Row X)) {r} → r ∈ properAt es rs → r ∈ rs
proper⊆ es []             ()
proper⊆ es ((q , e) ∷ rs) m with ∈-++⁻ _ m
... | inj₂ h = there (proper⊆ es rs h)
... | inj₁ h with when⁻ {b = allᵇ (q ≼ᵇ_) es} {x = (q , e)} h
...   | (_ , refl) = here refl

-- THE CONNECT'S SCOPE: the source subscribed under the connect's second
-- label, its two hots listed off it, and the maps a body reads them by.
-- The elaborated source is annotated, one label deeper.
module ConnEnv {Γ A} n (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (a : Admits (lw env) p) (a* : Admits (lw* env) p*) where

  -- The two sources' tables, listed in full.
  σ : ℕ → Tb.Listed A
  σ N = proj₁ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))

  σ* : ℕ → Tb.Listed (AIE A)
  σ* N = proj₁ (listC-ok (3 + N) n (annotate (elab ρι s)) (uρ* N) (p* ⊕ [ ix 1 ]))

  ρ′ : ℕ → All Tb.Listed (A ∷ Γ)
  ρ′ N = hotOf (σ N) ∷ ρ N

  ρ*′ : ℕ → All Tb.Listed (AIE A ∷ Δ)
  ρ*′ N = hotOf (σ* N) ∷ ρ* N

  uρ′ : ∀ N → UncutEnv (ρ′ N)
  uρ′ N = proj₂ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))) , uρ N

  uρ*′ : ∀ N → UncutEnv (ρ*′ N)
  uρ*′ N = proj₂ (proj₂ (listC-ok (3 + N) n (annotate (elab ρι s)) (uρ* N) (p* ⊕ [ ix 1 ]))) , uρ* N

  Src : Set₁
  Src = Out n s ρ ρι ρ* (maps env) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])

  -- The two hots, each listed off its lawful source.
  hD = listHot n s uρ (lw env) p a
  hD* = listHot n (annotate (elab ρι s)) uρ* (lw* env) p* a*
  D′ = den-cons hD (lw env)
  D*′ = den-cons hD* (lw* env)

  -- The source's hot maps each row to its annotated image, each late
  -- placement to its annotated one; its late rows are the source's.
  srcMap : Src → ℕ → HotMap
  srcMap Rs N = hotMap (λ k → Rel.φ (Out.rel Rs) N k ⊕ [ sub (reader* p*) ])
                       (λ k l′ → Σ Pos λ l → π (relMap (Out.rel Rs) N) k l × l′ ≡ l ⊕ [ sub (reader* p*) ])
                       (Rel.Late (Out.rel Rs) N)

  Ψ′ : Src → Maps (A ∷ Γ)
  Ψ′ Rs (here refl) = srcMap Rs
  Ψ′ Rs (there j)   = maps env j

  -- A source row is a row of the source's table.
  src-row : ∀ N {k e} → Rows (hotOf (σ N)) k e → TR (Tab n s ρ (p ⊕ [ ix 1 ]) N) k e
  src-row N x = σ N , proj₁ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))) , proper⊆ (ends (rows (σ N))) (rows (σ N)) x

  -- The new hot, read by a body subscribed in this scope.
  HotS : Src → Set₁
  HotS Rs = HotR (here refl) ρ′ (ext ρι) ρ*′ (Ψ′ Rs) D′ D*′

-- An event is a value.
outᵇ : ∀ {X : Set} → Ev X → Bool
outᵇ (out _) = true
outᵇ _       = false

-- A table holds a value at a position.
outAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
outAt nothing   y = false
outAt (just L)  y = anyᵇ (λ r → does (proj₁ r ≟ᵖ y) ∧ outᵇ (proj₂ r)) (rows L)

-- The first of some positions, or a default.
headOr : Pos → List Pos → Pos
headOr d []      = d
headOr d (c ∷ _) = c

-- A READER OF THE CONNECT'S HOT, subscribed at `q` and `q*`: its rows
-- and its elaborated rows, and the map between them.
module ReaderTab {Γ A} n (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (a : Admits (lw env) p) (a* : Admits (lw* env) p*)
  (Rs : ConnEnv.Src n s ρ uρ ρι ρ* uρ* env p p* a a*) n′ (q q* : Pos) where
  open ConnEnv n s ρ uρ ρι ρ* uρ* env p p* a a*

  -- The two readers' tables.
  P : ℕ → Maybe (Tb.Listed A)
  P = Tab n′ (connected (here refl)) ρ′ q

  Q : ℕ → Maybe (Tb.Listed (IE A))
  Q = Tab* n′ (ext ρι) (connected (here refl)) ρ*′ q*

  Sc : Scope
  Sc = scopeOf ρ′ (ext ρι) ρ*′

  -- The source's record and its two tables.
  R₀ : Rel (Tab n s ρ (p ⊕ [ ix 1 ])) (Tab* n ρι s ρ* (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (scopeOf ρ ρι ρ*)
  R₀ = Out.rel Rs

  S : ℕ → Maybe (Tb.Listed A)
  S = Tab n s ρ (p ⊕ [ ix 1 ])

  S* : ℕ → Maybe (Tb.Listed (IE A))
  S* = Tab* n ρι s ρ* (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])

  -- An elaborated source row's place: under the annotation's reader,
  -- under the reader's subscription, and at its emit if it emits.
  under : Pos → Pos
  under l = l ⊕ [ sub (reader* p*) ] ⊕ [ sub q* ]

  imgAt : ℕ → Pos → Pos
  imgAt N l = if outAt (S* N) l then emitAt (under l) else under l

  -- The reader's end on the elaborated reader's end; any other row on
  -- its hot row's source image, carried under the readers.
  φᵣ : ℕ → Pos → Pos
  φᵣ N y = if endAt (P N) y then headOr (q* ⊕ [ last ]) (endsOf (Q N)) else imgAt N (Rel.φ R₀ N (up y))

  -- A row's late placements: its source row's, carried the same way.
  Putᵣ : ℕ → Pos → Pos → Set
  Putᵣ N y l = (Σ _ λ e → TR (P N) y e)
             × Σ Pos λ l₀ → Rel.Put R₀ N (up y) l₀ × (Σ _ λ e′ → TR (S* N) l₀ e′) × l ≡ imgAt N l₀

  -- A row is late where its source row is a pin or late.
  Lateᵣ : ℕ → Pos → Set
  Lateᵣ N y = endAt (P N) y ≡ false × ((Σ Pos λ r → TR (S N) (up y) (pin r)) ⊎ Rel.Late R₀ N (up y))

  bkᵣ : ℕ → Pos → List Pos
  bkᵣ N _ = keys (P N)

  rd-in-bk : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → k ∈ bkᵣ N (φᵣ N k)
  rd-in-bk x _ _ = in-keys x

  rd-pb-few : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Putᵣ N k l → k ∈ ks
  rd-pb-few N l = keys (P N) , λ pt → in-keys (proj₂ (proj₁ pt))

  -- One event at a position, none under another: each table is listed
  -- off its lawful emission set.
  module Gen (ad : Admits D′ q) (ad* : Admits D*′ q*) where
    rd-func : ∀ {N y e e′} → TR (P N) y e → TR (P N) y e′ → e ≡ e′
    rd-func = tab-func n′ (connected (here refl)) uρ′ D′ ad

    rd-func* : ∀ {N y e e′} → TR (Q N) y e → TR (Q N) y e′ → e ≡ e′
    rd-func* = tab-func n′ (elab (ext ρι) (connected (here refl))) uρ*′ D*′ ad*

    rd-flat : ∀ {N y e l ys e′} → TR (P N) y e → TR (P N) (y ⊕ (l ∷ ys)) e′ → ⊥
    rd-flat = tab-flat n′ (connected (here refl)) uρ′ D′ ad

    rd-flat* : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
    rd-flat* = tab-flat n′ (elab (ext ρι) (connected (here refl))) uρ*′ D*′ ad*

  rd-got : ∀ N → Got (P N)
  rd-got N = got-ok (3 + N) n′ (connected (here refl)) {ρ′ N} (uρ′ N) q

  rd-got* : ∀ N → Got (Q N)
  rd-got* N = got-ok (3 + N) n′ (elab (ext ρι) (connected (here refl))) {ρ*′ N} (uρ*′ N) q*

  rd-pin-in : ∀ {N l r} → TR (P N) l (pin r) → T (inside r l)
  rd-pin-in {N} = pin-ok (3 + N) n′ (connected (here refl)) {ρ′ N} q

  rd-pin-in* : ∀ {N l r} → TR (Q N) l (pin r) → T (inside r l)
  rd-pin-in* {N} = pin-ok (3 + N) n′ (elab (ext ρι) (connected (here refl))) {ρ*′ N} q*

  rd-after : ∀ {N k e} → TR (P N) k e → q ≼ k
  rd-after {N} = after-ok (3 + N) n′ (connected (here refl)) {ρ′ N} q

  rd-after* : ∀ {N l e} → TR (Q N) l e → q* ≼ l
  rd-after* {N} = after-ok (3 + N) n′ (elab (ext ρι) (connected (here refl))) {ρ*′ N} q*

  rd-pin-after* : ∀ {N l r} → TR (Q N) l (pin r) → q* ≼ r
  rd-pin-after* {N} = pin-after-ok (3 + N) n′ (elab (ext ρι) (connected (here refl))) {ρ*′ N} q*

  G G* : ℕ → ℕ → Pos → Set
  G  = Scope.G Sc
  G* = Scope.G* Sc

  -- THE READER'S CORRESPONDENCE AND ITS LIFTING FACTS.
  postulate
    rd-corr        : ∀ N → Corr q q* (φᵣ N) (Putᵣ N) (Lateᵣ N) (TR (P N)) (TR (Q N))
    rd-φ-agree     : ∀ {N N′ k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N N′ k → G* N N′ (φᵣ N k) → AgreeTo k (TR (P N)) (TR (P N′)) → φᵣ N k ≡ φᵣ N′ k
    rd-late-agree  : ∀ {N N′ k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N N′ k → G* N N′ (φᵣ N k) → AgreeTo k (TR (P N)) (TR (P N′)) → ¬ Lateᵣ N′ k
    rd-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P N′) k e → Unpinned e → ¬ Lateᵣ N′ k → G N′ N k → G* N′ N (φᵣ N′ k) → AgreeTo (φᵣ N′ k) (TR (Q N′)) (TR (Q N))
                   → AgreeTo k (TR (P N′)) (TR (P N))
    rd-put-up      : ∀ {N N′ k l} → N ≤ N′ → G N′ N k → G* N′ N l → AgreeTo k (TR (P N′)) (TR (P N)) → Putᵣ N k l → Putᵣ N′ k l
    rd-back-put    : ∀ {N N′ k l} → N ≤ N′ → G N′ N k → G* N′ N l → Putᵣ N′ k l → AgreeTo l (TR (Q N′)) (TR (Q N)) → Putᵣ N k l
    rd-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N′ N k → G* N′ N (φᵣ N k) → AgreeTo k (TR (P N′)) (TR (P N))
                   → AgreeTo (φᵣ N k) (TR (Q N′)) (TR (Q N))
    rd-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N′ N k → G* N′ N (φᵣ N k) → TR (Q N) (φᵣ N k) e′
                   → AgreeTo (φᵣ N k) (TR (Q N′)) (TR (Q N)) → AgreeTo k (TR (P N′)) (TR (P N))
    rd-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → G N′ N k → G* N′ N l → AgreeTo k (TR (P N′)) (TR (P N)) → TR (Q N) l e′ → Putᵣ N k l
                   → AgreeTo l (TR (Q N′)) (TR (Q N))
    rd-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N′ N k → G* N′ N (φᵣ N k) → TR (Q N) (φᵣ N k) e′ → Corr.Leads (rd-corr N) k
                   → TR (Q N) m e* → G* N′ N m → instantOf m ≡ instantOf (φᵣ N k) → AgreeTo m (TR (Q N′)) (TR (Q N)) → AgreeTo (φᵣ N k) (TR (Q N′)) (TR (Q N))
    rd-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ y → G N′ N y) → (∀ y → G* N′ N y) → (∀ y → AgreeTo y (TR (P N′)) (TR (P N))) → ∀ {y e} → TR (Q N′) y e → TR (Q N) y e
    rd-cons        : ∀ {N N′} → Cons (G N N′) (TR (P N)) (TR (P N′))
    rd-cons*       : ∀ {N N′} → Cons (G* N N′) (TR (Q N)) (TR (Q N′))
    rd-after-φ     : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → q* ≼ φᵣ N k
    rd-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N′ N k → G* N′ N (φᵣ N k) → AgreeTo k (TR (P N′)) (TR (P N))
                   → (∀ {y r} → r ≼ k → TR (P N′) y (pin r) → TR (P N) y (pin r))
                   → ∀ {y r} → r ≼ φᵣ N k → TR (Q N′) y (pin r) → TR (Q N) y (pin r)

  rel′ : Admits D′ q → Admits D*′ q* → Rel P Q q q* Sc
  rel′ ad ad* = record
    { φ = φᵣ ; Put = Putᵣ ; Late = Lateᵣ ; corr = rd-corr ; φ-agree = rd-φ-agree ; late-agree = rd-late-agree ; bk = bkᵣ ; in-bk = rd-in-bk ; pb-few = rd-pb-few
    ; back = rd-back ; put-up = rd-put-up ; back-put = rd-back-put
    ; elab-causal = rd-elab-causal ; stable← = rd-stable← ; stable-put = rd-stable-put ; stable-lead = rd-stable-lead
    ; elab-all = rd-elab-all ; func = Gen.rd-func ad ad* ; func* = Gen.rd-func* ad ad* ; flat = Gen.rd-flat ad ad* ; flat* = Gen.rd-flat* ad ad*
    ; pin-in = rd-pin-in ; pin-in* = rd-pin-in* ; cons = rd-cons ; cons* = rd-cons* ; got = rd-got ; got* = rd-got*
    ; after = rd-after ; after* = rd-after* ; after-φ = rd-after-φ ; pin-after* = rd-pin-after* ; pin-stable = rd-pin-stable }

  -- THE READER'S ORDER FACTS: each row linked to its image and cutting
  -- every hot alike with it, and every pair before the reader cutting
  -- its rows alike.
  --
  -- At an old hot (`there`) a row's cuts are its hot row's, the source's
  -- `Rest.cuts` carried one label down on each side.  At the hot itself
  -- (`here`) no record orders the source's rows against its own rows of
  -- another cut, and as stated the claim fails one reader down.
  -- DEAD ROUTE: `rd-cuts` at `here`, read by a reader of this reader.  A
  --   flatMap source shows its outer end as an end in a cut whose lanes
  --   all end and as a skip in a cut that truncates one.  This reader
  --   images that end past the annotation's queued `nothing` lane, under
  --   `ix 1`, and that skip under its own `sub`.  A reader of this reader
  --   then has a row under the end whose image lies before the skip's
  --   image, though its position lies past the skip's: one position, two
  --   cuts, cut unalike.  `Rest.cuts` compares a row's pair with every
  --   cut's hot rows; a restatement confines that to cuts agreeing up to
  --   the row, or excuses rows over the pair, and adds a `Rest` field
  --   ordering a stream's rows against its own rows of other cuts.
  postulate
    rd-linked : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → Aligned (Ψ′ Rs) ρ′ q q* → Linked q q*
              → ∀ N {k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → Linked k (φᵣ N k)
    rd-cuts   : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → Aligned (Ψ′ Rs) ρ′ q q* → Linked q q*
              → ∀ N {k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → Aligned (Ψ′ Rs) ρ′ k (φᵣ N k)
    rd-seen   : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → Aligned (Ψ′ Rs) ρ′ q q* → Linked q q*
              → ∀ {u u*} → Aligned (Ψ′ Rs) ρ′ u u* → Cut u u* q q* → u ≺ q → ∀ N → Alike (relMap (rel′ ad ad*) N) (TR (P N)) u u*

  rest′ : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → Aligned (Ψ′ Rs) ρ′ q q* → Linked q q* → Rest (Ψ′ Rs) ρ′ (rel′ ad ad*)
  rest′ ad ad* al lk = record { linked = rd-linked ad ad* al lk ; cuts = rd-cuts ad ad* al lk ; seen = rd-seen ad ad* al lk }

-- THE CONNECT'S HOT: each reader's record, wherever it is subscribed.
opaque
  conn-hot : ∀ {Γ A} n (s : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) uρ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) uρ*
               (env : EnvR ρ ρι ρ*) p p* (a : Admits (lw env) p) (a* : Admits (lw* env) p*)
           → (Rs : ConnEnv.Src n s ρ uρ ρι ρ* uρ* env p p* a a*) → ConnEnv.HotS n s ρ uρ ρι ρ* uρ* env p p* a a* Rs
  conn-hot n s ρ uρ ρι ρ* uρ* env p p* a a* Rs n′ q q* ad ad* al lk =
    rel′ ad ad* ⊢ rest′ ad ad* al lk
    where open ReaderTab n s ρ uρ ρι ρ* uρ* env p p* a a* Rs n′ q q*

-- THE HOT'S MAP IS ITS SOURCE'S: two scopes whose sources map alike and
-- are late alike give their hots one map and late rows, however the
-- scopes and the readers are admitted.
module ConnTwo {Γ A} n (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (E E′ : EnvR ρ ρι ρ*) (p p* : Pos) (a : Admits (lw E) p) (a′ : Admits (lw E′) p) (a* : Admits (lw* E) p*) (a*′ : Admits (lw* E′) p*) where
  module C  = ConnEnv n s ρ uρ ρι ρ* uρ* E  p p* a  a*
  module C′ = ConnEnv n s ρ uρ ρι ρ* uρ* E′ p p* a′ a*′

  HotCoh : Set₁
  HotCoh = (Rs : C.Src) (Rs′ : C′.Src) → (∀ N y → Same (Out.rel Rs) (Out.rel Rs′) N y)
         → ∀ n′ q q* (ad : Admits C.D′ q) (ad′ : Admits C′.D′ q) (ad* : Admits C.D*′ q*) (ad*′ : Admits C′.D*′ q*)
             (al : Aligned (C.Ψ′ Rs) C.ρ′ q q*) (al′ : Aligned (C′.Ψ′ Rs′) C′.ρ′ q q*) (lk lk′ : Linked q q*) N y
         → Same (Out.rel (conn-hot n s ρ uρ ρι ρ* uρ* E p p* a a* Rs n′ q q* ad ad* al lk))
                (Out.rel (conn-hot n s ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ Rs′ n′ q q* ad′ ad*′ al′ lk′)) N y

-- Two scopes whose sources map alike and are late alike: a reader's
-- image is its source row's, carried alike, and it is late where its
-- source row is a pin or late.
opaque
  unfolding conn-hot
  conn-hot-coh : ∀ {Γ A} n (s : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) uρ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) uρ*
                   (E E′ : EnvR ρ ρι ρ*) p p* a a′ a* a*′ → ConnTwo.HotCoh n s ρ uρ ρι ρ* uρ* E E′ p p* a a′ a* a*′
  conn-hot-coh n s ρ uρ ρι ρ* uρ* E E′ p p* a a′ a* a*′ Rs Rs′ hs n′ q q* ad ad′ ad* ad*′ al al′ lk lk′ N y =
    same (if-≡ {b = endAt (X.P N) y} refl (λ _ → refl) (λ _ → cong (X.imgAt N) (φ≡ (hs N (up y)))))
         (λ { nl (ne , inj₁ pn)  → nl (ne , inj₁ pn)
            ; nl (ne , inj₂ lt′) → nl→ (hs N (up y)) (λ lt → nl (ne , inj₂ lt)) lt′ })
    where
      module X = ReaderTab n s ρ uρ ρι ρ* uρ* E p p* a a* Rs n′ q q*
