{-# OPTIONS --guardedness #-}

-- THE POSITION MAP, PER SUBTERM.  A subterm's plain cuts and its
-- elaborated cuts, subscribed at `s` and `s*`, correspond along a map of
-- positions per cut (`Rel`), read off the cuts' tables and never
-- asserted: the map, the late placement, the correspondence of the two
-- tables at each cut, and the lifting facts that carry agreement between
-- cuts across it.  `rel` builds the record by recursion over the tree,
-- each former's case from its children's, in any environment whose hots
-- are related as the record relates them (`simultaneous.TableEnv`): a
-- `connected` meets its hot through the environment, and a `connect`
-- relates the plain hot to its annotated, read one for its body.
--
-- Each case touches only its own operator: a one-to-one former carries
-- its child's record through its operator's table (`map-tab`,
-- `scan-tab`, `take-tab`, `defer-tab`) and its child's order facts
-- through the rows it keeps; `flatMap` and `connect` take their
-- children's records for every environment, so their cases never unfold
-- a child's elaboration.  The cuts are at least three rows deep, past
-- the elaboration's own leaves.
module simultaneous.TableRel where

open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (¬_; does)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; inside; _⊕_)
open import denotation.Events using (Timeline; From; fresh)
open import denotation.EmissionSet using (Unpinned; pin; _≼_)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl)
open import denotation.Laws.Modulus using (AgreeTo)
open import denotation.Laws.Count using (under-guard)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; Row; properAt; ends; rows; allᵇ; anyᵇ; _≼ᵇ_)
open import quickcheck.Tabled.Exact.Base using (when⁻)
open import simultaneous.SObs using (SObs; fixedˢ; plain; lone; ext; module Elaborate)
open import simultaneous.Listing using (listC-ok; UncutEnv)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.TableCorr using (Rel; Rows; TR; Corr; Cons; Got; keys; in-keys)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv
  using (Ren; Tab; Tab*; got-ok; pin-ok; after-ok; pin-after-ok; up; _⊕ˡ_; Linked; Lvl; Cut; at-frame; at-step; Alike; alike; cut; alike-l; alike-r; linked-l; linked-r;
         Maps; Aligned; aligned-⊕;
         Rest; Out; _⊢_; HotR; EnvR; envR; maps; hot; Full)
open import simultaneous.TableMap using (map-tab)
open import simultaneous.TableTake using (take-tab)
open import simultaneous.TableScan using (scan-tab)
open import simultaneous.TableDefer using (defer-tab)
open import simultaneous.TableSpin using (spin-tab)
open import simultaneous.TableOf using (of-tab)
open import simultaneous.TableCold using (cold-tab)
open import simultaneous.TableLayers using (flat-rel)
open import simultaneous.InstEmit using (instEmit; value)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- The order facts each one-to-one former keeps

postulate
  -- A LEAF FORMER'S ROWS: a cold's, an `of`'s and a spin's rows lie at its
  -- subscription's instant or at steps of timers it created there, each
  -- imaged at the alike step of the elaborated subscription; so each row
  -- inherits its subscription's link and its cuts of the hots in scope.
  cold-order : ∀ {Γ A} (m : From A 0) n {Δ} {ρ : ℕ → All Tb.Listed Γ} (ρ* : ℕ → All Tb.Listed Δ) uρ* (Ψ : Maps Γ) p p*
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (cold-tab m n ρ* uρ* p p*)
  of-order   : ∀ {Γ A} (xs : List A) v vals (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) p p*
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (of-tab xs v vals p p*)
  spin-order : ∀ {Γ A} (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) p p*
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (spin-tab {A} p p*)

  -- A ONE-TO-ONE FORMER'S ROWS: map's and take's rows are the child's
  -- rows at the child's positions, along the child's map; scan's are the
  -- child's renamed in place.  Each order fact is the child's, read
  -- through the inversion of the former's rows.
  map-order  : ∀ {Γ A B} (f : A → B) {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} {P Q s s*} (R : Rel P Q s s*)
            → Rest Ψ ρ R → Rest Ψ ρ (map-tab f R)
  scan-order : ∀ {Γ A B} (f : B → A → B) z {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} {P Q s s*} (R : Rel P Q s s*)
            → Rest Ψ ρ R → Rest Ψ ρ (scan-tab f z R)
  take-order : ∀ {Γ A} i (q : A → Bool) {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} {P Q s s*} (R : Rel P Q s s*)
            → Rest Ψ ρ R → Rest Ψ ρ (take-tab i q R)

  -- THE DEFER'S ROWS: its marker under its first label, then the body's,
  -- subscribed one label down.  A pair before the defer is before the
  -- body, and cuts it alike: the body's subscription is in the defer's
  -- instant, past it, and under neither of the pair.
  defer-order : ∀ {Γ A} {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} p p* {P Q} (R : Rel {A} P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]))
             → Rest Ψ ρ R → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (defer-tab p p* R)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- The connect

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

postulate
  -- THE BODY CUTS ITS SOURCE ALIKE.  Subscribed first, at the first
  -- label, the body is past each creator up its instant exactly as its
  -- image is, and before both sources' subscriptions.  By induction on
  -- the link: each creator lies in an earlier instant than the position
  -- it creates.
  cut-body : ∀ {p p*} → Linked p p* → Cut (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])

  -- A ROW NOT OVER THE CUT STAYS CUT ALIKE ONE LABEL DOWN.  Order
  -- arithmetic: past the cut exactly when its parent is, since nothing
  -- strictly between a position and its child lies outside the position.
  lvl-sub : ∀ {q q* y y*} → Lvl q q* y y* → ¬ (y* ⊑ q*) → ∀ l → Lvl q q* y (y* ⊕ [ l ])

  -- A position at or past `p* ⊕ [ix 1] ⊕ [ix 1]` is not over
  -- `p* ⊕ [ix 0]`: what is over it precedes it, and it precedes the
  -- source.
  past-src : ∀ {p* y*} → (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ]) ≼ y* → ¬ (y* ⊑ (p* ⊕ [ ix 0 ]))

cut-sub : ∀ {q q* y y*} → Cut q q* y y* → ¬ (y* ⊑ q*) → ∀ l → Cut q q* y (y* ⊕ [ l ])
cut-sub {y* = y*} (at-frame v a b)  n l = at-frame (lvl-sub v n l) a (trans (inst-⊕ y* [ l ]) b)
cut-sub {y* = y*} (at-step v a b c) n l = at-step (lvl-sub v n l) a (trans (inst-⊕ y* [ l ]) b) c

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
  Src = Out n s ρ ρι ρ* (maps env) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])

  -- The source's hot maps each row to its annotated image.
  Ψ′ : Src → Maps (A ∷ Γ)
  Ψ′ Rs (here refl) N k = Rel.φ (Out.rel Rs) N k ⊕ [ sub (reader* p*) ]
  Ψ′ Rs (there j)       = maps env j

  -- A source row is a row of the source's table.
  src-row : ∀ N {k e} → Rows (hotOf (σ N)) k e → TR (Tab n s ρ (p ⊕ [ ix 1 ]) N) k e
  src-row N x = σ N , proj₁ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))) , proper⊆ (ends (rows (σ N))) (rows (σ N)) x

  postulate
    -- THE CONNECT'S HOT: the elaborated source annotated, each value at
    -- its source image rejoined under the annotation's reader; two
    -- readers correspond wherever they cut it alike.
    conn-hot : (Rs : Src) → HotR (here refl) ρ′ (ext ρι) ρ*′ (Ψ′ Rs)

    -- AN OLD HOT'S READER CUTS THE NEW HOT ALIKE.  The reader's rows are
    -- the old hot's, which the source's rows cut alike with their images
    -- (the source's `cuts`); seen from the other side, the old rows cut
    -- the source's alike, each creator chain compared at its own levels.
    conn-old-cut : (Rs : Src) → ∀ {X} (j : X ∈ Γ) n′ q q* (al : Aligned (Ψ′ Rs) ρ′ q q*) (lk : Linked q q*)
                 → let R = Out.rel (hot env j n′ q q* (λ i → al (there i)) lk) in
                   ∀ N {k e} → TR (Tab n′ (connected j) ρ q N) k e → Unpinned e
                 → ∀ N′ → Alike (Ψ′ Rs (here refl) N′) (Rows (hotOf (σ N′))) k (Rel.φ R N k)

  -- An old hot is read as before; its rows cut the new hot alike.
  old : (Rs : Src) → ∀ {X} (j : X ∈ Γ) → HotR (there j) ρ′ (ext ρι) ρ*′ (Ψ′ Rs)
  old Rs j n′ q q* al lk = Out.rel O ⊢ record
    { linked = Rest.linked (Out.rest O)
    ; cuts   = cuts′
    ; self   = Rest.self (Out.rest O)
    ; seen   = λ al′ → Rest.seen (Out.rest O) (λ i → al′ (there i))
    }
    where
      O = hot env j n′ q q* (λ i → al (there i)) lk

      cuts′ : ∀ N {k e} → TR (Tab n′ (connected j) ρ q N) k e → Unpinned e → Aligned (Ψ′ Rs) ρ′ k (Rel.φ (Out.rel O) N k)
      cuts′ N x un (here refl) N′ = conn-old-cut Rs j n′ q q* al lk N x un N′
      cuts′ N x un (there i)   N′ = Rest.cuts (Out.rest O) N x un i N′

  env′ : Src → EnvR ρ′ (ext ρι) ρ*′
  env′ Rs = envR (Ψ′ Rs) hots
    where
      hots : ∀ {X} (i : X ∈ A ∷ Γ) → HotR i ρ′ (ext ρι) ρ*′ (Ψ′ Rs)
      hots (here refl) = conn-hot Rs
      hots (there j)   = old Rs j

  -- The body's subscriptions cut the source's hot alike: the source sees
  -- the body's pair, before it and cutting it alike, cutting its rows
  -- alike; its images lie past the source, so under the annotation's
  -- reader they stay cut alike.
  conn-cut : (Rs : Src) → Aligned (maps env) ρ p p* → Linked p p*
           → ∀ N → Alike (Ψ′ Rs (here refl) N) (Rows (hotOf (σ N))) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
  conn-cut Rs al lk N = alike λ x un →
    cut-sub (cut seen (src-row N x) un) (past-src (Rel.after-φ (Out.rel Rs) (src-row N x) un)) (sub (reader* p*))
    where
      seen = Rest.seen (Out.rest Rs) (aligned-⊕ {Ψ = maps env} {ρ = ρ} al (ix 0) (ix 0)) (cut-body lk) (under-guard p (⊑-refl (p ⊕ [ ix 0 ]))) N

  ----------------------------------------------------------------------
  -- The connect's record

  P Q : ℕ → _
  P = Tab n (connect s b) ρ p
  Q = Tab* n ρι (connect s b) ρ* p*

  -- The body's tables.
  Bp : ℕ → Maybe (Tb.Listed B)
  Bp = Tab n b ρ′ (p ⊕ [ ix 0 ])

  isBody : ℕ → Pos → Bool
  isBody N y = anyᵇ (λ k → does (k ≟ᵖ y)) (keys (Bp N))

  -- THE CONNECT'S ROWS: the body's, then the source's own past the
  -- body's subscription, one label down, its subscribe burst as pins of
  -- the connect and the rest unsubscribed while the body runs.  A body
  -- row is imaged along the body's map; a source row at its annotated
  -- image, one label down, as the elaborated connect shows it.  The
  -- connect makes pins, so `pin-stable` is first met here.
  module ConnTab (Rs : Src) (Ob : Out n b ρ′ (ext ρι) ρ*′ (Ψ′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])) where
    Rb : Rel Bp (Tab* n (ext ρι) b ρ*′ (p* ⊕ [ ix 0 ])) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
    Rb = Out.rel Ob

    φ′ : ℕ → Pos → Pos
    φ′ N y = if isBody N y then Rel.φ Rb N y else Ψ′ Rs (here refl) N (up y) ⊕ [ ix 0 ]

    Put′ : ℕ → Pos → Pos → Set
    Put′ N y l = if isBody N y then Rel.Put Rb N y l else (Σ _ λ e → TR (P N) y e) × l ≡ φ′ N y

    -- Few rows put on one image: a body row's through the body's, any
    -- other a plain row.
    ct-pb-few : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
    ct-pb-few N l = proj₁ (Rel.pb-few Rb N l) ++ keys (P N) , λ {k} → go k
      where
        go : ∀ k → Put′ N k l → k ∈ proj₁ (Rel.pb-few Rb N l) ++ keys (P N)
        go k pt with isBody N k
        ... | true  = ∈-++⁺ˡ (proj₂ (Rel.pb-few Rb N l) pt)
        ... | false = ∈-++⁺ʳ (proj₁ (Rel.pb-few Rb N l)) (in-keys (proj₂ (proj₁ pt)))

    bk′ : ℕ → Pos → List Pos
    bk′ N l = Rel.bk Rb N l ++ L.map (λ k → k ⊕ [ ix 0 ]) (Rel.bk (Out.rel Rs) N (up (up l)))

    postulate
      ct-corr        : ∀ N → Corr p p* (φ′ N) (Put′ N) (TR (P N)) (TR (Q N))
      ct-φ-agree     : ∀ {N N′ k e} → TR (P N) k e → Unpinned e → AgreeTo k (TR (P N)) (TR (P N′)) → φ′ N k ≡ φ′ N′ k
      ct-in-bk       : ∀ {N k e} → TR (P N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
      ct-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q N′)) (TR (Q N))
                     → AgreeTo k (TR (P N′)) (TR (P N))
      ct-put-up      : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P N′)) (TR (P N)) → Put′ N k l → Put′ N′ k l
      ct-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q N′)) (TR (Q N)) → Put′ N k l
      ct-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → AgreeTo k (TR (P N′)) (TR (P N))
                     → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N))
      ct-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P N) k e → Unpinned e → TR (Q N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N)) → AgreeTo k (TR (P N′)) (TR (P N))
      ct-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P N′)) (TR (P N)) → TR (Q N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q N′)) (TR (Q N))
      ct-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P N) k e → Unpinned e → TR (Q N) (φ′ N k) e′ → Corr.Leads (ct-corr N) k
                     → TR (Q N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q N′)) (TR (Q N)) → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N))
      ct-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → ∀ {y e} → TR (Q N′) y e → TR (Q N) y e
      ct-func        : ∀ {N y e e′} → TR (P N) y e → TR (P N) y e′ → e ≡ e′
      ct-func*       : ∀ {N y e e′} → TR (Q N) y e → TR (Q N) y e′ → e ≡ e′
      ct-flat        : ∀ {N y e l ys e′} → TR (P N) y e → TR (P N) (y ⊕ (l ∷ ys)) e′ → ⊥
      ct-flat*       : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
      ct-cons        : ∀ {N N′} → Cons (TR (P N)) (TR (P N′))
      ct-cons*       : ∀ {N N′} → Cons (TR (Q N)) (TR (Q N′))
      ct-after-φ     : ∀ {N k e} → TR (P N) k e → Unpinned e → p* ≼ φ′ N k
      ct-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → AgreeTo k (TR (P N′)) (TR (P N))
                     → (∀ {y r} → r ≼ k → TR (P N′) y (pin r) → TR (P N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q N′) y (pin r) → TR (Q N) y (pin r)

    ct-got : ∀ N → Got (P N)
    ct-got N = got-ok (3 + N) n (connect s b) {ρ N} (uρ N) p

    ct-pin-in : ∀ {N l r} → TR (P N) l (pin r) → T (inside r l)
    ct-pin-in {N} = pin-ok (3 + N) n (connect s b) {ρ N} p

    ct-after : ∀ {N k e} → TR (P N) k e → p ≼ k
    ct-after {N} = after-ok (3 + N) n (connect s b) {ρ N} p

    ct-got* : ∀ N → Got (Q N)
    ct-got* N = got-ok (3 + N) n (elab ρι (connect s b)) {ρ* N} (uρ* N) p*

    ct-pin-in* : ∀ {N l r} → TR (Q N) l (pin r) → T (inside r l)
    ct-pin-in* {N} = pin-ok (3 + N) n (elab ρι (connect s b)) {ρ* N} p*

    ct-after* : ∀ {N l e} → TR (Q N) l e → p* ≼ l
    ct-after* {N} = after-ok (3 + N) n (elab ρι (connect s b)) {ρ* N} p*

    ct-pin-after* : ∀ {N l r} → TR (Q N) l (pin r) → p* ≼ r
    ct-pin-after* {N} = pin-after-ok (3 + N) n (elab ρι (connect s b)) {ρ* N} p*

    rel′ : Rel P Q p p*
    rel′ = record
      { φ = φ′ ; Put = Put′ ; corr = ct-corr ; φ-agree = ct-φ-agree ; bk = bk′ ; in-bk = ct-in-bk ; pb-few = ct-pb-few
      ; back = ct-back ; put-up = ct-put-up ; back-put = ct-back-put
      ; elab-causal = ct-elab-causal ; stable← = ct-stable← ; stable-put = ct-stable-put ; stable-lead = ct-stable-lead
      ; elab-all = ct-elab-all ; func = ct-func ; func* = ct-func* ; flat = ct-flat ; flat* = ct-flat*
      ; pin-in = ct-pin-in ; pin-in* = ct-pin-in* ; cons = ct-cons ; cons* = ct-cons* ; got = ct-got ; got* = ct-got*
      ; after = ct-after ; after* = ct-after* ; after-φ = ct-after-φ ; pin-after* = ct-pin-after* ; pin-stable = ct-pin-stable }

  conn-tab : (Rs : Src) → Out n b ρ′ (ext ρι) ρ*′ (Ψ′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) → Rel P Q p p*
  conn-tab = ConnTab.rel′

  postulate
    -- The connect's rows are the body's and the source's, each carrying
    -- its own order facts; the source's pins are its subscribe burst.
    conn-order : (Rs : Src) (Ob : Out n b ρ′ (ext ρι) ρ*′ (Ψ′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]))
              → Aligned (maps env) ρ p p* → Linked p p* → Rest (maps env) ρ (conn-tab Rs Ob)

  -- The body's subscriptions cut every hot alike: the source's by
  -- `conn-cut`, the rest as the connect's did.
  al′ : (Rs : Src) → Aligned (maps env) ρ p p* → Linked p p* → Aligned (Ψ′ Rs) ρ′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
  al′ Rs al lk (here refl) N = conn-cut Rs al lk N
  al′ Rs al lk (there j)   N = aligned-⊕ {Ψ = maps env} {ρ = ρ} al (ix 0) (ix 0) j N

conn-rel : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Full n s → Full n b → Full n (connect s b)
conn-rel n s b Fs Fb ρ uρ ρι ρ* uρ* env p p* al lk = C.conn-tab Rs Ob ⊢ C.conn-order Rs Ob al lk
  where
    module C = Conn n s b ρ uρ ρι ρ* uρ* env p p*

    Rs : C.Src
    Rs = Fs ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])
           (λ i N → alike-r (alike-r (alike-l (al i N) (ix 1)) (ix 1)) (ix 1))
           (linked-r (linked-r (linked-l lk (ix 1)) (ix 1)) (ix 1))

    Ob : Out n b C.ρ′ (ext ρι) C.ρ*′ (C.Ψ′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
    Ob = Fb C.ρ′ C.uρ′ (ext ρι) C.ρ*′ C.uρ*′ (C.env′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (C.al′ Rs al lk)
           (linked-r (linked-l lk (ix 0)) (ix 0))

------------------------------------------------------------------------
-- Every author subterm

-- EVERY AUTHOR SUBTERM'S CUTS CORRESPOND.  An author's cold only: a
-- `fresh` cold emits the position it is subscribed at, and its
-- elaboration is subscribed deeper, so no map matches its value to the
-- plain one.
rel : ∀ {Γ A} n (o : SObs Γ A) → Full n (plain o)
rel n (cold (fixedˢ m)) ρ uρ ρι ρ* uρ* env p p* al lk = cold-tab m n ρ* uρ* p p* ⊢ cold-order m n ρ* uρ* (maps env) p p* al lk
rel n empty             ρ uρ ρι ρ* uρ* env p p* al lk =
  of-tab [] (λ x → instEmit (value x) root) (λ _ → refl) p p* ⊢ of-order [] _ _ (maps env) ρ p p* al lk
rel n (of xs)           ρ uρ ρι ρ* uρ* env p p* al lk =
  of-tab xs (λ x → instEmit (value x) root) (λ _ → refl) p p* ⊢ of-order xs _ _ (maps env) ρ p p* al lk
rel n (map f s)         ρ uρ ρι ρ* uρ* env p p* al lk =
  let O = rel n s ρ uρ ρι ρ* uρ* env p p* al lk in map-tab f (Out.rel O) ⊢ map-order f (Out.rel O) (Out.rest O)
rel n (scan f z s)      ρ uρ ρι ρ* uρ* env p p* al lk =
  let O = rel n s ρ uρ ρι ρ* uρ* env p p* al lk in scan-tab f z (Out.rel O) ⊢ scan-order f z (Out.rel O) (Out.rest O)
rel n (takeWhile i q s) ρ uρ ρι ρ* uρ* env p p* al lk =
  let O = rel n s ρ uρ ρι ρ* uρ* env p p* al lk in take-tab i q (Out.rel O) ⊢ take-order i q (Out.rel O) (Out.rest O)
rel n (flatMap op f s)  = flat-rel n op (λ a → plain (f a)) (plain s) (rel n s) (λ a → rel n (f a))
rel n (connect s b)     = conn-rel n (plain s) (plain b) (rel n s) (rel n b)
rel n (connected i)     ρ uρ ρι ρ* uρ* env p p* al lk = hot env i n p p* al lk
rel zero    (defer l)   ρ uρ ρι ρ* uρ* env p p* al lk = spin-tab p p* ⊢ spin-order (maps env) ρ p p* al lk
rel (suc n) (defer l)   ρ uρ ρι ρ* uρ* env p p* al lk =
  let O = rel n (Later.force l) ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (aligned-⊕ {Ψ = maps env} {ρ = ρ} al (ix 1) (ix 1)) (linked-r (linked-l lk (ix 1)) (ix 1))
  in defer-tab p p* (Out.rel O) ⊢ defer-order p p* (Out.rel O) (Out.rest O) al lk
