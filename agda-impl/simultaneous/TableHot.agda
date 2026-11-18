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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_; does)

open import Tree using (Obs; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; _<ᵖ_; inside; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; Unpinned; pin; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ≺→≼; ≺-ext; ≺-≼-≺; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds using (_⊑_; ⊑-≼; ⊑-inside; ⊑-snoc; ⊕-assoc; step; here; plain-last)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; Row; properAt; ends; rows; allᵇ; anyᵇ; _≼ᵇ_; _⊣_)
open import quickcheck.Tabled.Exact.Base using (when⁻; if⁻; cm⁻; offT; ends⁻; Exact)
open import quickcheck.Tabled.Exact using (proper-exact)
open import simultaneous.SObs using (lone; ext; module Elaborate)
open import simultaneous.Listing using (listC-ok; listC-exact; UncutEnv)
open import simultaneous.TableCorr using (Rel; Same; same; φ≡; nl→; Scope; Rows; TR; Corr; Cons; Got; keys; in-keys)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv
  using (Ren; HotMap; hotMap; π; relMap; scopeOf; Tab; Tab*; got-ok; pin-ok; after-ok; pin-after-ok;
  up; up-⊕; _⊕ˡ_; ⊑-⊕ˡ; Linked; Cut; at-frame; at-step; Lvl; cut; Alike; Aligned; Off; shownᵇ; Maps; Rest; Out; _⊢_; HotR; EnvR; maps; lw; lw*;
  Admits; HotsAll; den-ex; listHot; den-cons; tab-func; tab-flat)
open import simultaneous.TableFlat using (if-≡; in-if; module TabRows)
open import simultaneous.TableRows using (rejoin-in)
open import simultaneous.LaneEndSched using (emitAt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)
open TabRows using (endAt; endsOf; endAt-I)

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

  -- A source hot row is a hot row of its cut, which no admissible
  -- subscription's world holds.
  hot-row : ∀ N {h e} → Rows (hotOf (σ N)) h e → HotsAll D′ h
  hot-row N {h} {e} m = N , inj₁ (e , Exact.sound (proper-exact (listC-exact (3 + N) n s (den-ex (lw env) N) (p ⊕ [ ix 1 ]) (proj₁ (proj₂ ok))) (proj₂ (proj₂ ok))) m)
    where ok = listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ])

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

-- A cut's level.
cut-lvl : ∀ {b q q* y y*} → Cut b q q* y y* → Lvl b q q* y y*
cut-lvl (at-frame v _ _)  = v
cut-lvl (at-step v _ _ _) = v

-- An end listed among a table's ends is a row.
ends-tr : ∀ {X : Set} (m : Maybe (Tb.Listed X)) {c} → c ∈ endsOf m → TR m c end
ends-tr nothing   ()
ends-tr (just Lx) c∈ = Lx , refl , ends⁻ {rs = rows Lx} c∈

-- A pin read as a skip.
unpin : ∀ {X : Set} → Ev X → Ev X
unpin (pin _) = skip
unpin e       = e

-- Shown once unpinned: shown before.
shown-unpin : ∀ {X : Set} (e : Ev X) → T (shownᵇ (unpin e)) → T (shownᵇ e)
shown-unpin (out _) t = t
shown-unpin end     t = t
shown-unpin skip    ()
shown-unpin (pin _) ()

-- Strictly under a position one label down: under the position.
⊕-under : ∀ x {a} y {l} ys → x ⊕ [ a ] ≡ y ⊕ (l ∷ ys) → y ⊑ x
⊕-under x {a} y {l} ys eq with ⊑-snoc {y} x {a} (subst (y ⊑_) (sym eq) (l ∷ ys , refl))
... | inj₁ u = u
... | inj₂ e = ⊥-elim (≺-irrefl {y} (subst (y ≺_) (sym (trans e eq)) (≺-ext y {l} ys)))

private
  onT : ∀ {b} → b ≡ true → T b
  onT refl = tt

  false≢true : ¬ (false ≡ true)
  false≢true ()

-- A REJOINED ROW: a hot row past the subscription one label down, a pin
-- as a skip; or the end, at the subscription's last, of a hot ended at
-- or before it.
RjRow : ∀ {X : Set} → Pos → Tb.Listed X → Pos → Ev X → Set
RjRow {X} q L k e = (Σ Pos λ h → Σ (Ev X) λ e₀ → (h , e₀) ∈ rows L × q ≺ h × k ≡ h ⊕ [ sub q ] × e ≡ unpin e₀)
                  ⊎ (Σ Pos λ h → (h , end) ∈ rows L × ¬ (q ≺ h) × k ≡ q ⊕ [ last ] × e ≡ end)

rejoin-inv : ∀ {X : Set} q (L : Tb.Listed X) {k e} → (k , e) ∈ rows (Tb.rejoin q L) → RjRow q L k e
rejoin-inv q (rs ⊣ _) m with cm⁻ {f = Tb.rejoinRow q} {xs = rs} m
... | ((h , out a) , hm , w) with when⁻ {b = q <ᵖ h} {x = (h ⊕ [ sub q ] , out a)} w
...   | (b , refl) = inj₁ (h , out a , hm , onT b , refl , refl)
rejoin-inv q (rs ⊣ _) m | ((h , skip) , hm , w) with when⁻ {b = q <ᵖ h} {x = (h ⊕ [ sub q ] , skip)} w
...   | (b , refl) = inj₁ (h , skip , hm , onT b , refl , refl)
rejoin-inv q (rs ⊣ _) m | ((h , pin r) , hm , w) with when⁻ {b = q <ᵖ h} {x = (h ⊕ [ sub q ] , skip)} w
...   | (b , refl) = inj₁ (h , pin r , hm , onT b , refl , refl)
rejoin-inv q (rs ⊣ _) m | ((h , end) , hm , w) with if⁻ {b = q <ᵖ h} w
...   | inj₁ (b , here refl) = inj₁ (h , end , hm , onT b , refl , refl)
...   | inj₁ (_ , there ())
...   | inj₂ (b , here refl) = inj₂ (h , hm , offT b , refl , refl)
...   | inj₂ (_ , there ())

-- A rejoined row read through a reader's image: its end on the
-- elaborated reader's end or a default, any other row on its hot row's.
reader-cases : ∀ {X : Set} q (L : Tb.Listed X) (G : Pos → Set) (b : Bool) d (cs : List Pos) (img : Pos → Pos) {k e}
             → RjRow q L k e → (e ≡ end → b ≡ true) → G d → (∀ {c} → c ∈ cs → G c)
             → (∀ {h e₀} → Rows L h e₀ → q ≺ h → k ≡ h ⊕ [ sub q ] → b ≡ false → G (img h))
             → G (if b then headOr d cs else img (up k))
reader-cases q L G true  d []       img _ _ gd gc _ = gd
reader-cases q L G true  d (c ∷ cs) img _ _ gd gc _ = gc (here refl)
reader-cases q L G false d cs img (inj₁ (h , e₀ , m , qh , kk , _)) _ _ _ gi =
  subst (λ z → G (img z)) (sym (trans (cong up kk) (up-⊕ h (sub q)))) (gi m qh kk refl)
reader-cases q L G false d cs img (inj₂ (_ , _ , _ , _ , ee)) eb _ _ _ = ⊥-elim (false≢true (eb ee))

-- No rejoined row of one hot under a shown one of another: under a hot
-- row's, the hots' own flatness; under the end, nothing lies.
rejoin-flat : ∀ {X : Set} q (L L′ : Tb.Listed X)
            → (∀ {h e₀ m ms e₀′} → Rows L h e₀ → T (shownᵇ e₀) → Rows L′ (h ⊕ (m ∷ ms)) e₀′ → ⊥)
            → (∀ {h e₀} → Rows L′ h e₀ → (q ⊕ [ last ]) ⊑ h → ⊥)
            → ∀ {k e l ys e′} → RjRow q L k e → T (shownᵇ e) → RjRow q L′ (k ⊕ (l ∷ ys)) e′ → ⊥
rejoin-flat q L L′ fl dj {ys = ys} (inj₁ (h , e₀ , m , qh , refl , refl)) sh (inj₁ (h′ , e₀′ , m′ , _ , eq , _))
  with ⊕-under h′ (h ⊕ [ sub q ]) ys (sym eq)
... | zs , refl = fl m (shown-unpin e₀ sh) (subst (λ z → Rows L′ z e₀′) (⊕-assoc h [ sub q ] zs) m′)
rejoin-flat q L L′ fl dj {ys = ys} (inj₁ (h , e₀ , m , qh , refl , refl)) sh (inj₂ (_ , _ , _ , eq , _)) =
  ≺-absurd {q} {h} qh (≺-≼-≺ {h} {h ⊕ [ sub q ]} {q} (≺-ext h []) (⊑-≼ {h ⊕ [ sub q ]} {q} (⊕-under q (h ⊕ [ sub q ]) ys (sym eq))))
rejoin-flat q L L′ fl dj {ys = ys} (inj₂ (_ , _ , _ , refl , refl)) sh (inj₁ (h′ , _ , m′ , _ , eq , _)) =
  dj m′ (⊕-under h′ (q ⊕ [ last ]) ys (sym eq))
rejoin-flat q L L′ fl dj {ys = ys} (inj₂ (_ , _ , _ , refl , refl)) sh (inj₂ (_ , _ , _ , eq , _)) =
  ≺-irrefl {q ⊕ [ last ]} (subst ((q ⊕ [ last ]) ≺_) eq (≺-ext (q ⊕ [ last ]) ys))

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

  -- A reader row, read off its hot.
  rd-row : ∀ {N k e} → TR (P N) k e → RjRow q (hotOf (σ N)) k e
  rd-row {N} (_ , refl , r) = rejoin-inv q (hotOf (σ N)) r

  -- A value the reader shows is its hot's, so another cut's hot agreeing
  -- up to it shows it too.
  rd-cons : ∀ {N N′} → Cons (G N N′) (TR (P N)) (TR (P N′))
  rd-cons {N} {N′} g _ x _ _ with rd-row {N} x
  ... | inj₁ (h , out v , hm , qh , refl , refl) =
        _ , refl , rejoin-in q (hotOf (σ N′)) (proj₁ (AgreeTo.upto (proj₁ g) (≺→≼ {h} {h ⊕ [ sub q ]} (≺-ext h []))) hm) qh
  ... | inj₁ (h , skip , _ , _ , _ , ())
  ... | inj₁ (h , end , _ , _ , _ , ())
  ... | inj₁ (h , pin _ , _ , _ , _ , ())
  ... | inj₂ (_ , _ , _ , _ , ())

  -- A reader row off a hot row, not late: that row unpinned and not late
  -- for the source.
  rd-src : ∀ {N k h e₀} → k ≡ h ⊕ [ sub q ] → endAt (P N) k ≡ false → Rows (hotOf (σ N)) h e₀ → ¬ Lateᵣ N k
         → Unpinned e₀ × ¬ Rel.Late R₀ N h
  rd-src {N} {k} {h} {e₀} kk ek m nl = unp e₀ m , λ lt → nl (ek , inj₂ (subst (Rel.Late R₀ N) (sym uk) lt))
    where
      uk : up k ≡ h
      uk = trans (cong up kk) (up-⊕ h (sub q))

      unp : ∀ e → Rows (hotOf (σ N)) h e → Unpinned e
      unp (pin r) m′ = ⊥-elim (nl (ek , inj₁ (r , subst (λ z → TR (S N) z (pin r)) (sym uk) (src-row N m′))))
      unp (out _) _  = tt
      unp skip    _  = tt
      unp end     _  = tt

  -- A source image past the elaborated reader's subscription: carried
  -- under the readers, still past it.
  img-past : ∀ N l → q* ≺ (l ⊕ [ sub (reader* p*) ]) → q* ≼ imgAt N l
  img-past N l lt = in-if (outAt (S* N) l) (q* ≼_)
    (λ _ → ≺→≼ {q*} {emitAt (under l)} (≺-≼-≺ {q*} {under l} {emitAt (under l)} u (⊑-≼ {under l} {emitAt (under l)} (⊑-⊕ˡ (under l) _))))
    (λ _ → ≺→≼ {q*} {under l} u)
    where
      u : q* ≺ under l
      u = ≺-≼-≺ {q*} {l ⊕ [ sub (reader* p*) ]} {under l} lt (⊑-≼ {l ⊕ [ sub (reader* p*) ]} {under l} ([ sub q* ] , refl))

  -- The reader's image past its subscription: its end among the
  -- elaborated reader's rows, any other row's off the source's
  -- alignment with its hot row.
  rd-after-φ : Aligned (Ψ′ Rs) ρ′ q q* → ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → q* ≼ φᵣ N k
  rd-after-φ al {N} {k} {e} x un nl =
    reader-cases q (hotOf (σ N)) (q* ≼_) (endAt (P N) k) (q* ⊕ [ last ]) (endsOf (Q N)) (λ l → imgAt N (Rel.φ R₀ N l)) (rd-row x)
      (λ ee → endAt-I (P N) (subst (TR (P N) k) ee x))
      (≺→≼ {q*} {q* ⊕ [ last ]} (≺-ext q* []))
      (λ c∈ → rd-after* (ends-tr (Q N) c∈))
      (λ {h} m qh kk ek → img-past N (Rel.φ R₀ N h)
         (proj₁ (cut-lvl (cut (al (here refl) N) m (proj₁ (rd-src kk ek m nl)) (proj₂ (rd-src kk ek m nl)))) qh))

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
    rd-cons*       : ∀ {N N′} → Cons (G* N N′) (TR (Q N)) (TR (Q N′))
    rd-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → G N′ N k → G* N′ N (φᵣ N k) → AgreeTo k (TR (P N′)) (TR (P N))
                   → (∀ {y r} → r ≼ k → TR (P N′) y (pin r) → TR (P N) y (pin r))
                   → ∀ {y r} → r ≼ φᵣ N k → TR (Q N′) y (pin r) → TR (Q N) y (pin r)

  rel′ : Admits D′ q → Admits D*′ q* → Aligned (Ψ′ Rs) ρ′ q q* → Rel P Q q q* Sc
  rel′ ad ad* al = record
    { φ = φᵣ ; Put = Putᵣ ; Late = Lateᵣ ; corr = rd-corr ; φ-agree = rd-φ-agree ; late-agree = rd-late-agree ; bk = bkᵣ ; in-bk = rd-in-bk ; pb-few = rd-pb-few
    ; back = rd-back ; put-up = rd-put-up ; back-put = rd-back-put
    ; elab-causal = rd-elab-causal ; stable← = rd-stable← ; stable-put = rd-stable-put ; stable-lead = rd-stable-lead
    ; elab-all = rd-elab-all ; func = Gen.rd-func ad ad* ; func* = Gen.rd-func* ad ad* ; flat = Gen.rd-flat ad ad* ; flat* = Gen.rd-flat* ad ad*
    ; pin-in = rd-pin-in ; pin-in* = rd-pin-in* ; cons = rd-cons ; cons* = rd-cons* ; got = rd-got ; got* = rd-got*
    ; after = rd-after ; after* = rd-after* ; after-φ = rd-after-φ al ; pin-after* = rd-pin-after* ; pin-stable = rd-pin-stable }

  -- THE READER'S ORDER FACTS: each row linked to its image; each shown
  -- row cutting every hot alike with it, and the reader's own rows of
  -- every cut; and every pair before the reader cutting its rows alike.
  --
  -- At an old hot (`there`) a row's cuts are its hot row's, the source's
  -- `Rest.cuts` carried one label down on each side.  At the hot itself
  -- (`here`) and against the reader's own rows they are the source's
  -- `Rest.self`, carried the same way.
  postulate
    rd-linked : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → Aligned (Ψ′ Rs) ρ′ q q* → Linked q q*
              → ∀ N {k e} → TR (P N) k e → Unpinned e → ¬ Lateᵣ N k → Linked k (φᵣ N k)
    rd-cuts   : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → Aligned (Ψ′ Rs) ρ′ q q* → Linked q q*
              → ∀ N {k e} → TR (P N) k e → T (shownᵇ e) → Aligned (Ψ′ Rs) ρ′ k (φᵣ N k)
    rd-self   : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → (al : Aligned (Ψ′ Rs) ρ′ q q*) → Linked q q*
              → ∀ N {k e} → TR (P N) k e → T (shownᵇ e) → ∀ N′ → Alike (relMap (rel′ ad ad* al) N′) (Off k (TR (P N′))) k (φᵣ N k)
    rd-self-at : ∀ {N N′ k e e′} → TR (P N) k e → T (shownᵇ e) → TR (P N′) k e′ → T (shownᵇ e′) → φᵣ N k ≡ φᵣ N′ k
    rd-seen   : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) → (al : Aligned (Ψ′ Rs) ρ′ q q*) → Linked q q*
              → ∀ {u u*} → Aligned (Ψ′ Rs) ρ′ u u* → Cut true u u* q q* → u ≺ q → ∀ N → Alike (relMap (rel′ ad ad* al) N) (TR (P N)) u u*

  -- No reader row of any cut under a shown one: under a hot row's, the
  -- source's flatness; under the reader's end, the subscription's world.
  rd-self-flat : Admits D′ q → ∀ {N N′ k e l ys e′} → TR (P N) k e → T (shownᵇ e) → TR (P N′) (k ⊕ (l ∷ ys)) e′ → ⊥
  rd-self-flat ad {N} {N′} x sh x′ =
    rejoin-flat q (hotOf (σ N)) (hotOf (σ N′))
      (λ m sh₀ m′ → Rest.self-flat (Out.rest Rs) (src-row N m) sh₀ (src-row N′ m′))
      (λ m′ u → proj₂ (proj₁ ad) (hot-row N′ m′) (step here plain-last) (⊑-inside u))
      (rd-row x) sh (rd-row x′)

  rest′ : ∀ (ad : Admits D′ q) (ad* : Admits D*′ q*) (al : Aligned (Ψ′ Rs) ρ′ q q*) → Linked q q* → Rest (Ψ′ Rs) ρ′ (rel′ ad ad* al)
  rest′ ad ad* al lk = record
    { linked = rd-linked ad ad* al lk ; cuts = rd-cuts ad ad* al lk ; self = rd-self ad ad* al lk
    ; self-at = rd-self-at ; self-flat = rd-self-flat ad ; seen = rd-seen ad ad* al lk }

-- THE CONNECT'S HOT: each reader's record, wherever it is subscribed.
opaque
  conn-hot : ∀ {Γ A} n (s : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) uρ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) uρ*
               (env : EnvR ρ ρι ρ*) p p* (a : Admits (lw env) p) (a* : Admits (lw* env) p*)
           → (Rs : ConnEnv.Src n s ρ uρ ρι ρ* uρ* env p p* a a*) → ConnEnv.HotS n s ρ uρ ρι ρ* uρ* env p p* a a* Rs
  conn-hot n s ρ uρ ρι ρ* uρ* env p p* a a* Rs n′ q q* ad ad* al lk =
    rel′ ad ad* al ⊢ rest′ ad ad* al lk
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
