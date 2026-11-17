{-# OPTIONS --guardedness #-}

-- THE POSITION MAP, PER SUBTERM.  A subterm's plain cuts and its
-- elaborated cuts, subscribed at `s` and `s*`, correspond along a map of
-- positions per cut (`Rel`), read off the cuts' tables and never
-- asserted: the map, the late placement, the correspondence of the two
-- tables at each cut, and the lifting facts that carry agreement between
-- cuts across it.  `rel` builds the record by recursion over the tree,
-- each former's case from its children's, in any environment whose hots
-- are related as the record relates them (`EnvR`): a `connected` meets
-- its hot through the environment, and a `connect` relates the plain hot
-- to its annotated, read one for its body.
--
-- A reader's rows keep the hot's own instants, so two readers correspond
-- only where their subscriptions cut the hot alike (`Alike`): a hot
-- carries its map onto the elaborated hot, and the subterm's two
-- subscriptions cut every hot in scope alike (`Aligned`).  A plain reader
-- in the frame before a burst value of the hot sees it; an elaborated
-- reader in a later instant sees nothing of the burst.
--
-- Each case touches only its own operator: a one-to-one former carries
-- its child's record through its operator's table (`map-tab`,
-- `scan-tab`, `take-tab`, `defer-tab`); `flatMap` and `connect` take
-- their children's records for every environment, so their cases never
-- unfold a child's elaboration.  The cuts are at least three rows deep,
-- past the elaboration's own leaves.
module simultaneous.TableRel where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; Unpinned; _≺_)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import denotation.Laws.Worlds using (_⊑_; ⊕-assoc)
open import denotation.Laws.Count using (child)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import simultaneous.SObs using (SObs; fixedˢ; plain; lone; ext; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.TableCorr using (Rel; Rows)
open import simultaneous.TableMap using (map-tab)
open import simultaneous.TableTake using (take-tab)
open import simultaneous.TableScan using (scan-tab)
open import simultaneous.TableDefer using (defer-tab)
open import simultaneous.TableSpin using (spin-tab)
open import simultaneous.TableOf using (of-tab)
open import simultaneous.TableCold using (cold-tab)
open import simultaneous.InstEmit using (instEmit; value)
open import Relation.Binary.PropositionalEquality using (refl)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- The subterm's two families of tables

-- The elaboration's scope for a plain scope.
Ren : List Set → List Set → Set₁
Ren Γ Δ = ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ

Tab : ∀ {Γ A} → ℕ → Obs Timeline Γ A → (ℕ → All Tb.Listed Γ) → Pos → ℕ → Maybe (Tb.Listed A)
Tab n o ρ p N = listC (3 + N) n o (ρ N) p

Tab* : ∀ {Γ Δ A} → ℕ → Ren Γ Δ → Obs Timeline Γ A → (ℕ → All Tb.Listed Δ) → Pos → ℕ → Maybe (Tb.Listed (IE A))
Tab* n ρι o ρ* p N = listC (3 + N) n (elab ρι o) (ρ* N) p

-- A hot cut alike by two subscriptions, along the hot's map: each
-- unpinned row of the plain hot lies past the one exactly when its image
-- lies past the other, in its instant exactly when the image is in the
-- other's, and under neither.
record Alike {X : Set} (ψ : Pos → Pos) (h : Tb.Listed X) (q q* : Pos) : Set where
  constructor alike
  field cut : ∀ {k} {e : Ev X} → Rows h k e → Unpinned e
            → (q ≺ k ⇔ q* ≺ ψ k) × (instantOf k ≡ instantOf q ⇔ instantOf (ψ k) ≡ instantOf q*) × ¬ (q ⊑ k) × ¬ (q* ⊑ ψ k)
open Alike

-- A hot in scope: its map onto the elaborated hot, and its two readers'
-- record wherever they cut it alike.
HotR : ∀ {Γ Δ X} → X ∈ Γ → (ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ℕ → All Tb.Listed Δ) → Set₁
HotR i ρ ρι ρ* = Σ (ℕ → Pos → Pos) λ ψ → ∀ n p p* → (∀ N → Alike (ψ N) (lookup (ρ N) i) p p*)
               → Rel (Tab n (connected i) ρ p) (Tab* n ρι (connected i) ρ* p*) p p*

record EnvR {Γ Δ} (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) : Set₁ where
  constructor envR
  field hot : ∀ {X} (i : X ∈ Γ) → HotR i ρ ρι ρ*
open EnvR

-- Two subscriptions cutting every hot in scope alike.
Aligned : ∀ {Γ Δ} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} → EnvR ρ ρι ρ* → Pos → Pos → Set₁
Aligned {Γ} {ρ = ρ} env p p* = ∀ {X} (i : X ∈ Γ) N → Alike (proj₁ (hot env i) N) (lookup (ρ N) i) p p*

-- Wherever the two are subscribed alike.
Holds : ∀ {Γ Δ A} → ℕ → Obs Timeline Γ A → (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → EnvR ρ ρι ρ* → Set₁
Holds n o ρ ρι ρ* env = ∀ p p* → Aligned env p p* → Rel (Tab n o ρ p) (Tab* n ρι o ρ* p*) p p*

-- In every environment of uncut tables whose hots are related.
Full : ∀ {Γ A} → ℕ → Obs Timeline Γ A → Set₁
Full {Γ} n o = ∀ (ρ : ℕ → All Tb.Listed Γ) → (∀ N → UncutEnv (ρ N))
             → ∀ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → (∀ N → UncutEnv (ρ* N)) → (env : EnvR ρ ρι ρ*) → Holds n o ρ ρι ρ* env

------------------------------------------------------------------------
-- Going down a label

private
  -- Past `v` and not under it: past what lies under it.
  down : ∀ v l {y} → v ≺ y → ¬ (v ⊑ y) → (v ⊕ [ l ]) ≺ y
  down v l lt nv with child l lt
  ... | inj₁ u   = ⊥-elim (nv u)
  ... | inj₂ lt′ = lt′

  up : ∀ v l {y} → (v ⊕ [ l ]) ⊑ y → v ⊑ y
  up v l (zs , refl) = l ∷ zs , ⊕-assoc v [ l ] zs

-- Either subscription, a label down.
alike-l : ∀ {X : Set} {ψ : Pos → Pos} {h : Tb.Listed X} {q q*} → Alike ψ h q q* → ∀ l → Alike ψ h (q ⊕ [ l ]) q*
cut (alike-l {ψ = ψ} {q = q} {q*} al l) {k} x un =
  let (lt , ie , nq , nq*) = cut al x un in
  mk⇔ (λ h → Equivalence.to lt (≺-trans {q} {q ⊕ [ l ]} {k} (≺-ext q []) h))
      (λ h → down q l (Equivalence.from lt h) nq)
  , subst₂ (λ a b → instantOf k ≡ a ⇔ instantOf (ψ k) ≡ b) (sym (inst-⊕ q [ l ])) refl ie
  , (λ u → nq (up q l u)) , nq*

alike-r : ∀ {X : Set} {ψ : Pos → Pos} {h : Tb.Listed X} {q q*} → Alike ψ h q q* → ∀ l* → Alike ψ h q (q* ⊕ [ l* ])
cut (alike-r {ψ = ψ} {q = q} {q*} al l*) {k} x un =
  let (lt , ie , nq , nq*) = cut al x un in
  mk⇔ (λ h → down q* l* (Equivalence.to lt h) nq*)
      (λ h → Equivalence.from lt (≺-trans {q*} {q* ⊕ [ l* ]} {ψ k} (≺-ext q* []) h))
  , subst₂ (λ a b → instantOf k ≡ a ⇔ instantOf (ψ k) ≡ b) refl (sym (inst-⊕ q* [ l* ])) ie
  , nq , (λ u → nq* (up q* l* u))

alike-⊕ : ∀ {X : Set} {ψ : Pos → Pos} {h : Tb.Listed X} {q q*} → Alike ψ h q q* → ∀ l l* → Alike ψ h (q ⊕ [ l ]) (q* ⊕ [ l* ])
alike-⊕ al l l* = alike-l (alike-r al l*) l

aligned-⊕ : ∀ {Γ Δ} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} (env : EnvR ρ ρι ρ*) {p p*}
          → Aligned env p p* → ∀ l l* → Aligned env (p ⊕ [ l ]) (p* ⊕ [ l* ])
aligned-⊕ env al l l* i N = alike-⊕ (al i N) l l*

------------------------------------------------------------------------
-- Each former's case

postulate
  -- THE FLATMAP, over its children's records in every environment.
  --
  -- False as quantified: a lane is subscribed past its creator, a row of
  -- the source, so it cuts a hot in scope where that row falls among the
  -- hot's rows, and the two hots' maps need not agree on it.  An
  -- environment whose plain hot row follows the creator while its image
  -- precedes the creator's image is aligned at the flatMap's own
  -- subscriptions; its plain lane reads the row and its elaborated lane
  -- does not.  The hots' maps and the source's must be one map, shared
  -- by every stream of the run, before the lanes can be aligned.
  --
  -- RECOVERY: git show e63b1f32 restores the per-former inversions of an elaborated run over approx (simultaneous/ReadRows.agda, ReadLane, ReadMap, ReadFold, FlatRows, ToldRows), each to be restated over the tables for its former's case.
  flat-rel  : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
            → Full n s → (∀ a → Full n (f a)) → Full n (flatMap op f s)

-- THE CONNECT: the source subscribed under the connect's second label,
-- the body under its first, in the environment the source's hot extends.
-- The elaborated source is annotated, one label deeper.
module Conn {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) where

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
  Src = Rel (Tab n s ρ (p ⊕ [ ix 1 ])) (Tab* n ρι s ρ* (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])

  postulate
    -- THE CONNECT'S HOT: the elaborated source annotated, mapped from the
    -- plain source's rows along the source's map; two readers correspond
    -- wherever they cut it alike.
    conn-hot : Src → HotR (here refl) ρ′ (ext ρι) ρ*′

  env′ : Src → EnvR ρ′ (ext ρι) ρ*′
  hot (env′ Rs) (here refl) = conn-hot Rs
  hot (env′ Rs) (there j)   = hot env j

  postulate
    -- THE BODY CUTS ITS HOT ALIKE: subscribed before its source, each
    -- body sees every row of its source, and in its own instant exactly
    -- the source's subscribe burst.
    conn-cut : (Rs : Src) → ∀ N → Alike (proj₁ (conn-hot Rs) N) (hotOf (σ N)) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])

    -- THE CONNECT'S ROWS: the body's, then the source's own past the
    -- body's subscription, its subscribe burst as pins of the connect
    -- and the rest unsubscribed while the body runs.  The connect makes
    -- pins, so `pin-stable` is first met here.
    conn-tab : Src → Rel (Tab n b ρ′ (p ⊕ [ ix 0 ])) (Tab* n (ext ρι) b ρ*′ (p* ⊕ [ ix 0 ])) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
             → Rel (Tab n (connect s b) ρ p) (Tab* n ρι (connect s b) ρ* p*) p p*

  -- The body's subscriptions cut every hot alike: the source's by
  -- `conn-cut`, the rest as the connect's did.
  al′ : (Rs : Src) → Aligned env p p* → Aligned (env′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
  al′ Rs al (here refl) N = conn-cut Rs N
  al′ Rs al (there j)   N = alike-⊕ (al j N) (ix 0) (ix 0)

conn-rel : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Full n s → Full n b → Full n (connect s b)
conn-rel n s b Fs Fb ρ uρ ρι ρ* uρ* env p p* al =
  C.conn-tab Rs (Fb C.ρ′ C.uρ′ (ext ρι) C.ρ*′ C.uρ*′ (C.env′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (C.al′ Rs al))
  where
    module C = Conn n s b ρ uρ ρι ρ* uρ* env p p*

    Rs : C.Src
    Rs = Fs ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (λ i N → alike-r (alike-r (alike-l (al i N) (ix 1)) (ix 1)) (ix 1))

-- EVERY AUTHOR SUBTERM'S CUTS CORRESPOND.  An author's cold only: a
-- `fresh` cold emits the position it is subscribed at, and its
-- elaboration is subscribed deeper, so no map matches its value to the
-- plain one.
rel : ∀ {Γ A} n (o : SObs Γ A) → Full n (plain o)
rel n (cold (fixedˢ m)) ρ uρ ρι ρ* uρ* env p p* _  = cold-tab m n ρ* uρ* p p*
rel n empty             ρ uρ ρι ρ* uρ* env p p* _  = of-tab [] (λ x → instEmit (value x) root) (λ _ → refl) p p*
rel n (of xs)           ρ uρ ρι ρ* uρ* env p p* _  = of-tab xs (λ x → instEmit (value x) root) (λ _ → refl) p p*
rel n (map f s)         ρ uρ ρι ρ* uρ* env p p* al = map-tab f (rel n s ρ uρ ρι ρ* uρ* env p p* al)
rel n (scan f z s)      ρ uρ ρι ρ* uρ* env p p* al = scan-tab f z (rel n s ρ uρ ρι ρ* uρ* env p p* al)
rel n (takeWhile i q s) ρ uρ ρι ρ* uρ* env p p* al = take-tab i q (rel n s ρ uρ ρι ρ* uρ* env p p* al)
rel n (flatMap op f s)  = flat-rel n op (λ a → plain (f a)) (plain s) (rel n s) (λ a → rel n (f a))
rel n (connect s b)     = conn-rel n (plain s) (plain b) (rel n s) (rel n b)
rel n (connected i)     ρ uρ ρι ρ* uρ* env p p* al = proj₂ (hot env i) n p p* (al i)
rel zero    (defer l)   ρ uρ ρι ρ* uρ* env p p* _  = spin-tab p p*
rel (suc n) (defer l)   ρ uρ ρι ρ* uρ* env p p* al =
  defer-tab p p* (rel n (Later.force l) ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (aligned-⊕ env al (ix 1) (ix 1)))
