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
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_; does)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; inside; _⊕_)
open import denotation.Events using (Timeline; From; fresh)
open import denotation.EmissionSet using (Unpinned; pin; _≼_)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl)
open import denotation.Laws.Modulus using (AgreeTo)
open import denotation.Laws.Count using (under-guard)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; anyᵇ)
open import simultaneous.SObs using (SObs; fixedˢ; plain; lone; ext; module Elaborate)
open import simultaneous.Listing using (UncutEnv)
open import simultaneous.TableCorr using (Rel; module Rel; Same; same; φ≡; nl→; Corr; keys; in-keys)
open import simultaneous.TableKit using (cons-≤; Rows; TR; Cons; Got)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv
  using (Ren; ψ; π; scopeOf; Tab; Tab*; got-ok; pin-ok; after-ok; pin-after-ok; up; Linked; Cut; cut-sub; shownᵇ;
  Alike; alike; cut; cut-put; alike-l; alike-r; linked-l; linked-r; Maps;
  Aligned; aligned-⊕; Rest; Out; _⊢_; HotR; EnvR; envR; EnvEq; maps; lw; lw*; hot; hot-coh;
  Full; Coh; Admits; admits-step; admits-wk; admits-body; listHot-u; unended; tab-func;
  tab-flat)
open import simultaneous.ElabUndone using (env-ext)
open import simultaneous.TableMap using (map-tab)
open import simultaneous.TableTake using (take-tab; take-cong)
open import simultaneous.TableScan using (scan-tab)
open import simultaneous.TableDefer using (defer-tab; defer-cong)
open import simultaneous.TableSpin using (spin-tab)
open import simultaneous.TableOf using (of-tab)
open import simultaneous.TableCold using (cold-tab)
open import simultaneous.TableLayers using (flat-rel; flat-coh)
open import simultaneous.TableFlat using (if-≡)
open import simultaneous.TableHot using (reader*; module ConnEnv; conn-hot; conn-hot-coh)
open import simultaneous.InstEmit using (instEmit; value)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- The order facts each one-to-one former keeps

postulate
  -- A LEAF FORMER'S ROWS: a cold's, an `of`'s and a spin's rows lie at its
  -- subscription's instant or at steps of timers it created there, each
  -- imaged at the alike step of the elaborated subscription; so each row
  -- inherits its subscription's link and its cuts of the hots in scope.
  cold-order : ∀ {Γ A} (m : From A 0) n {Δ} {ρ : ℕ → All Tb.Listed Γ} (ρ* : ℕ → All Tb.Listed Δ) uρ* (Ψ : Maps Γ) p p* {S}
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (cold-tab m n ρ* uρ* p p* {S})
  of-order   : ∀ {Γ A} (xs : List A) v vals (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) p p* {S}
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (of-tab xs v vals p p* {S})
  spin-order : ∀ {Γ A} (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) p p* {S}
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (spin-tab {A} p p* {S})

  -- A ONE-TO-ONE FORMER'S ROWS: map's and take's rows are the child's
  -- rows at the child's positions, along the child's map; scan's are the
  -- child's renamed in place.  Each order fact is the child's, read
  -- through the inversion of the former's rows.
  map-order  : ∀ {Γ A B} (f : A → B) {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} {P Q s s* S} (R : Rel P Q s s* S)
            → Rest Ψ ρ R → Rest Ψ ρ (map-tab f R)
  scan-order : ∀ {Γ A B} (f : B → A → B) z {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} {P Q s s* S} (R : Rel P Q s s* S)
            → Rest Ψ ρ R → Rest Ψ ρ (scan-tab f z R)
  take-order : ∀ {Γ A} i (q : A → Bool) {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} {P Q s s* S} (R : Rel P Q s s* S)
            → Rest Ψ ρ R → Rest Ψ ρ (take-tab i q R)

  -- THE DEFER'S ROWS: its marker under its first label, then the body's,
  -- subscribed one label down.  A pair before the defer is before the
  -- body, and cuts it alike: the body's subscription is in the defer's
  -- instant, past it, and under neither of the pair.
  defer-order : ∀ {Γ A} {Ψ : Maps Γ} {ρ : ℕ → All Tb.Listed Γ} p p* {P Q S} (R : Rel {A} P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) S)
             → Rest Ψ ρ R → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (defer-tab p p* R)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- The connect

postulate
  -- THE BODY CUTS ITS SOURCE ALIKE.  Subscribed first, at the first
  -- label, the body is past each creator up its instant exactly as its
  -- image is, and before both sources' subscriptions.  By induction on
  -- the link: each creator lies in an earlier instant than the position
  -- it creates.
  cut-body : ∀ {p p*} → Linked p p* → Cut true (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])

  -- A position at or past `p* ⊕ [ix 1] ⊕ [ix 1]` is not over
  -- `p* ⊕ [ix 0]`: what is over it precedes it, and it precedes the
  -- source.
  past-src : ∀ {p* y*} → (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ]) ≼ y* → ¬ (y* ⊑ (p* ⊕ [ ix 0 ]))

-- A record holds under any guard no weaker than its own.
rel-≤ : ∀ {A} {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {s s*} {S S′ : Scope}
      → (∀ {N N′ y} → Scope.G S′ N N′ y → Scope.G S N N′ y) → (∀ {N N′ y} → Scope.G* S′ N N′ y → Scope.G* S N N′ y)
      → Rel P Q s s* S → Rel P Q s s* S′
rel-≤ g g* R = record
  { φ = φ ; Put = Put ; Late = Late ; corr = corr
  ; φ-agree     = λ x un nl a b → φ-agree x un nl (g a) (g* b)
  ; late-agree  = λ x un nl a b → late-agree x un nl (g a) (g* b)
  ; bk = bk ; in-bk = in-bk ; pb-few = pb-few
  ; back        = λ le x un nl a b → back le x un nl (g a) (g* b)
  ; put-up      = λ le a b → put-up le (g a) (g* b)
  ; back-put    = λ le a b → back-put le (g a) (g* b)
  ; elab-causal = λ le x un nl a b → elab-causal le x un nl (g a) (g* b)
  ; stable←     = λ le x un nl a b → stable← le x un nl (g a) (g* b)
  ; stable-put  = λ le a b → stable-put le (g a) (g* b)
  ; stable-lead = λ le x un nl a b te ld tm gm → stable-lead le x un nl (g a) (g* b) te ld tm (g* gm)
  ; elab-all    = λ le ga gb → elab-all le (λ q → g (ga q)) (λ q → g* (gb q))
  ; func = func ; func* = func* ; flat = flat ; flat* = flat* ; pin-in = pin-in ; pin-in* = pin-in*
  ; cons = cons-≤ g cons ; cons* = cons-≤ g* cons*
  ; got = got ; got* = got* ; after = after ; after* = after* ; after-φ = after-φ ; pin-after* = pin-after*
  ; pin-stable  = λ le x un nl a b → pin-stable le x un nl (g a) (g* b)
  }
  where open Rel R

-- THE CONNECT: the body subscribed under the connect's first label, in
-- the environment the source's hot extends.
module Conn {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (a : Admits (lw env) p) (a* : Admits (lw* env) p*) where
  open ConnEnv n s ρ uρ ρι ρ* uρ* env p p* a a*

  postulate
    -- AN OLD HOT'S READER CUTS THE NEW HOT ALIKE.  The reader's rows are
    -- the old hot's, which the source's rows cut alike with their images
    -- (the source's `cuts`); seen from the other side, the old rows cut
    -- the source's alike, each creator chain compared at its own levels.
    conn-old-cut : (Rs : Src) → ∀ {X} (j : X ∈ Γ) n′ q q* (ad : Admits D′ q) (ad* : Admits D*′ q*) (al : Aligned (Ψ′ Rs) ρ′ q q*) (lk : Linked q q*)
                 → let R = Out.rel (hot env j n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD* (lw* env) ad*) (λ i → al (there i)) lk) in
                   ∀ N {k e} → TR (Tab n′ (connected j) ρ q N) k e → T (shownᵇ e)
                 → ∀ N′ → Alike (Ψ′ Rs (here refl) N′) (Rows (hotOf (σ N′))) k (Rel.φ R N k)

  -- An old hot is read as before; its rows cut the new hot alike.
  old : (Rs : Src) → ∀ {X} (j : X ∈ Γ) → HotR (there j) ρ′ (ext ρι) ρ*′ (Ψ′ Rs) D′ D*′
  old Rs j n′ q q* ad ad* al lk = rel-≤ proj₂ proj₂ (Out.rel O) ⊢ record
    { linked    = Rest.linked (Out.rest O)
    ; cuts      = cuts′
    ; self      = Rest.self (Out.rest O)
    ; self-at   = Rest.self-at (Out.rest O)
    ; self-flat = Rest.self-flat (Out.rest O)
    ; seen      = λ al′ → Rest.seen (Out.rest O) (λ i → al′ (there i))
    }
    where
      O = hot env j n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD* (lw* env) ad*) (λ i → al (there i)) lk

      cuts′ : ∀ N {k e} → TR (Tab n′ (connected j) ρ q N) k e → T (shownᵇ e)
            → Aligned (Ψ′ Rs) ρ′ k (Rel.φ (Out.rel O) N k)
      cuts′ N x sh (here refl) N′ = conn-old-cut Rs j n′ q q* ad ad* al lk N x sh N′
      cuts′ N x sh (there i)   N′ = Rest.cuts (Out.rest O) N x sh i N′

  env′ : Src → EnvR ρ′ (ext ρι) ρ*′
  env′ Rs = envR (Ψ′ Rs) D′ D*′ hots hots-coh λ N → env-ext (listHot-u n s uρ* (lw* env) p* a* (unended env) N) (unended env N)
    where
      hots : ∀ {X} (i : X ∈ A ∷ Γ) → HotR i ρ′ (ext ρι) ρ*′ (Ψ′ Rs) D′ D*′
      hots (here refl) = conn-hot n s ρ uρ ρι ρ* uρ* env p p* a a* Rs
      hots (there j)   = old Rs j

      hots-coh : ∀ {X} (i : X ∈ A ∷ Γ) n′ q q* (ad ad′ : Admits D′ q) (ad* ad*′ : Admits D*′ q*) (al al′ : Aligned (Ψ′ Rs) ρ′ q q*) (lk lk′ : Linked q q*) N y
               → Same (Out.rel (hots i n′ q q* ad ad* al lk)) (Out.rel (hots i n′ q q* ad′ ad*′ al′ lk′)) N y
      hots-coh (here refl) = conn-hot-coh n s ρ uρ ρι ρ* uρ* env env p p* a a a* a* Rs Rs (λ _ _ → same refl (λ nl → nl))
      hots-coh (there j) n′ q q* ad ad′ ad* ad*′ al al′ lk lk′ N y =
        let x = hot-coh env j n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD (lw env) ad′) (admits-wk hD* (lw* env) ad*) (admits-wk hD* (lw* env) ad*′)
                  (λ i → al (there i)) (λ i → al′ (there i)) lk lk′ N y
        in same (φ≡ x) (nl→ x)

  -- The body's subscriptions cut the source's hot alike: the source sees
  -- the body's pair, before it and cutting it alike, cutting its rows
  -- alike; its images lie past the source, so under the annotation's
  -- reader they stay cut alike.
  conn-cut : (Rs : Src) → Aligned (maps env) ρ p p* → Linked p p*
           → ∀ N → Alike (Ψ′ Rs (here refl) N) (Rows (hotOf (σ N))) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
  conn-cut Rs al lk N = alike
    (λ x un nl → cut-sub (cut seen (src-row N x) un nl) (past-src (Rel.after-φ (Out.rel Rs) (src-row N x) un nl)) (sub (reader* p*)))
    (λ { x (l , (pt , e′ , y) , refl) → cut-sub (cut-put seen (src-row N x) (pt , e′ , y)) (past-src (Rel.after* (Out.rel Rs) y)) (sub (reader* p*)) })
    where
      seen = Rest.seen (Out.rest Rs) (aligned-⊕ {Ψ = maps env} {ρ = ρ} al (ix 0) (ix 0)) (cut-body lk) (under-guard p (⊑-refl (p ⊕ [ ix 0 ]))) N

  ----------------------------------------------------------------------
  -- The connect's record

  P Q : ℕ → _
  P = Tab n (connect s b) ρ p
  Q = Tab* n ρι (connect s b) ρ* p*

  -- The hots in scope guarding the connect's record.
  Sc : Scope
  Sc = scopeOf ρ ρι ρ*

  G G* : ℕ → ℕ → Pos → Set
  G  = Scope.G Sc
  G* = Scope.G* Sc

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
    Rb : Rel Bp (Tab* n (ext ρι) b ρ*′ (p* ⊕ [ ix 0 ])) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (scopeOf ρ′ (ext ρι) ρ*′)
    Rb = Out.rel Ob

    φ′ : ℕ → Pos → Pos
    φ′ N y = if isBody N y then Rel.φ Rb N y else ψ (srcMap Rs N) (up y) ⊕ [ ix 0 ]

    -- A source row's skip, past the body's subscription, put at its image
    -- or where the hot's map puts the source's row.
    Put′ : ℕ → Pos → Pos → Set
    Put′ N y l = if isBody N y then Rel.Put Rb N y l
                 else (Σ _ λ e → TR (P N) y e) × (l ≡ φ′ N y ⊎ Σ Pos λ l′ → π (srcMap Rs N) (up y) l′ × l ≡ l′ ⊕ [ ix 0 ])

    -- A body row is late as the body says; a source row's skip is late
    -- where the source's row is late or a pin, whose image the source
    -- never placed.
    Late′ : ℕ → Pos → Set
    Late′ N y = if isBody N y then Rel.Late Rb N y
                else (Rel.Late (Out.rel Rs) N (up y) ⊎ Σ Pos λ r → TR (Tab n s ρ (p ⊕ [ ix 1 ]) N) (up y) (pin r))

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
      ct-corr        : ∀ N → Corr p p* (φ′ N) (Put′ N) (Late′ N) (TR (P N)) (TR (Q N))
      ct-φ-agree     : ∀ {N N′ k e} → TR (P N) k e → Unpinned e → ¬ Late′ N k → G N N′ k → G* N N′ (φ′ N k) → AgreeTo k (TR (P N)) (TR (P N′)) → φ′ N k ≡ φ′ N′ k
      ct-late-agree  : ∀ {N N′ k e} → TR (P N) k e → Unpinned e → ¬ Late′ N k → G N N′ k → G* N N′ (φ′ N k) → AgreeTo k (TR (P N)) (TR (P N′)) → ¬ Late′ N′ k
      ct-in-bk       : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
      ct-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P N′) k e → Unpinned e → ¬ Late′ N′ k → G N′ N k → G* N′ N (φ′ N′ k) → AgreeTo (φ′ N′ k) (TR (Q N′)) (TR (Q N))
                     → AgreeTo k (TR (P N′)) (TR (P N))
      ct-put-up      : ∀ {N N′ k l} → N ≤ N′ → G N′ N k → G* N′ N l → AgreeTo k (TR (P N′)) (TR (P N)) → Put′ N k l → Put′ N′ k l
      ct-back-put    : ∀ {N N′ k l} → N ≤ N′ → G N′ N k → G* N′ N l → Put′ N′ k l → AgreeTo l (TR (Q N′)) (TR (Q N)) → Put′ N k l
      ct-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Late′ N k → G N′ N k → G* N′ N (φ′ N k) → AgreeTo k (TR (P N′)) (TR (P N))
                     → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N))
      ct-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Late′ N k → G N′ N k → G* N′ N (φ′ N k) → TR (Q N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N)) → AgreeTo k (TR (P N′)) (TR (P N))
      ct-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → G N′ N k → G* N′ N l → AgreeTo k (TR (P N′)) (TR (P N)) → TR (Q N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q N′)) (TR (Q N))
      ct-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Late′ N k → G N′ N k → G* N′ N (φ′ N k) → TR (Q N) (φ′ N k) e′ → Corr.Leads (ct-corr N) k
                     → TR (Q N) m e* → G* N′ N m → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q N′)) (TR (Q N)) → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N))
      ct-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → G N′ N q) → (∀ q → G* N′ N q) → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → ∀ {y e} → TR (Q N′) y e → TR (Q N) y e
      ct-cons        : ∀ {N N′} → Cons (G N N′) (TR (P N)) (TR (P N′))
      ct-cons*       : ∀ {N N′} → Cons (G* N N′) (TR (Q N)) (TR (Q N′))
      ct-after-φ     : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Late′ N k → p* ≼ φ′ N k
      ct-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → ¬ Late′ N k → G N′ N k → G* N′ N (φ′ N k) → AgreeTo k (TR (P N′)) (TR (P N))
                     → (∀ {y r} → r ≼ k → TR (P N′) y (pin r) → TR (P N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q N′) y (pin r) → TR (Q N) y (pin r)

    -- One event at a position, none under another: each table is listed
    -- off its lawful emission set.
    ct-func : ∀ {N y e e′} → TR (P N) y e → TR (P N) y e′ → e ≡ e′
    ct-func = tab-func n (connect s b) uρ (lw env) a

    ct-func* : ∀ {N y e e′} → TR (Q N) y e → TR (Q N) y e′ → e ≡ e′
    ct-func* = tab-func n (elab ρι (connect s b)) uρ* (lw* env) a*

    ct-flat : ∀ {N y e l ys e′} → TR (P N) y e → TR (P N) (y ⊕ (l ∷ ys)) e′ → ⊥
    ct-flat = tab-flat n (connect s b) uρ (lw env) a

    ct-flat* : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
    ct-flat* = tab-flat n (elab ρι (connect s b)) uρ* (lw* env) a*

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

    rel′ : Rel P Q p p* Sc
    rel′ = record
      { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = ct-corr ; φ-agree = ct-φ-agree ; late-agree = ct-late-agree ; bk = bk′ ; in-bk = ct-in-bk ; pb-few = ct-pb-few
      ; back = ct-back ; put-up = ct-put-up ; back-put = ct-back-put
      ; elab-causal = ct-elab-causal ; stable← = ct-stable← ; stable-put = ct-stable-put ; stable-lead = ct-stable-lead
      ; elab-all = ct-elab-all ; func = ct-func ; func* = ct-func* ; flat = ct-flat ; flat* = ct-flat*
      ; pin-in = ct-pin-in ; pin-in* = ct-pin-in* ; cons = ct-cons ; cons* = ct-cons* ; got = ct-got ; got* = ct-got*
      ; after = ct-after ; after* = ct-after* ; after-φ = ct-after-φ ; pin-after* = ct-pin-after* ; pin-stable = ct-pin-stable }

  conn-tab : (Rs : Src) → Out n b ρ′ (ext ρι) ρ*′ (Ψ′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) → Rel P Q p p* Sc
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

-- THE CONNECT'S CHILDREN: the source's record, two labels down, and the
-- body's, in the scope the source's hot extends.
module ConnRel {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (Fs : Full n s) (Fb : Full n b)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (a : Admits (lw env) p) (a* : Admits (lw* env) p*) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
  module CE = ConnEnv n s ρ uρ ρι ρ* uρ* env p p* a a*
  module C  = Conn n s b ρ uρ ρι ρ* uρ* env p p* a a*

  Rs : CE.Src
  Rs = Fs ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])
         (admits-step (lw env) a) (admits-step (lw* env) (admits-step (lw* env) a*))
         (λ i N → alike-r (alike-r (alike-l (al i N) (ix 1)) (ix 1)) (ix 1))
         (linked-r (linked-r (linked-l lk (ix 1)) (ix 1)) (ix 1))

  Ob : Out n b CE.ρ′ (ext ρι) CE.ρ*′ (CE.Ψ′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
  Ob = Fb CE.ρ′ CE.uρ′ (ext ρι) CE.ρ*′ CE.uρ*′ (C.env′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
         (admits-body n s uρ (lw env) p a) (admits-body n (annotate (elab ρι s)) uρ* (lw* env) p* a*) (C.al′ Rs al lk)
         (linked-r (linked-l lk (ix 0)) (ix 0))

conn-rel : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Full n s → Full n b → Full n (connect s b)
conn-rel n s b Fs Fb ρ uρ ρι ρ* uρ* env p p* a a* al lk = C.conn-tab Rs Ob ⊢ C.conn-order Rs Ob al lk
  where open ConnRel n s b Fs Fb ρ uρ ρι ρ* uρ* env p p* a a* al lk

-- Rows late alike on each branch of a test are late alike under it.
late-if : ∀ (c : Bool) {A A′ B B′ : Set} → (c ≡ true → ¬ A → ¬ A′) → (c ≡ false → ¬ B → ¬ B′)
        → ¬ (if c then A else B) → ¬ (if c then A′ else B′)
late-if true  t _ = t refl
late-if false _ f = f refl

-- A connect's map and late rows are its body's on the body's rows and
-- its source's one label down on the rest: coherent where both children are, the body's
-- scopes related by the hot's coherence and the outer environments'.
conn-coh : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (Fs : Full n s) (Fb : Full n b)
         → Coh n s Fs → Coh n b Fb → Coh n (connect s b) (conn-rel n s b Fs Fb)
conn-coh n s b Fs Fb cs cb ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y =
  same (if-≡ refl (λ _ → φ≡ (bφ N y)) (λ _ → cong (λ u → (u ⊕ [ sub (reader* p*) ]) ⊕ [ ix 0 ]) (φ≡ (sφ N (up y)))))
       (late-if (X.C.isBody N y) (λ _ → nl→ (bφ N y))
                (λ _ nl → λ { (inj₁ lt) → nl→ (sφ N (up y)) (λ lt₀ → nl (inj₁ lt₀)) lt ; (inj₂ pn) → nl (inj₂ pn) }))
  where
    module X  = ConnRel n s b Fs Fb ρ uρ ρι ρ* uρ* E  p p* a  a*  al  lk
    module X′ = ConnRel n s b Fs Fb ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′

    sφ : ∀ N y → Same (Out.rel X.Rs) (Out.rel X′.Rs) N y
    sφ = cs ρ uρ ρι ρ* uρ* E E′ ee (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])
           (admits-step (lw E) a) (admits-step (lw E′) a′)
           (admits-step (lw* E) (admits-step (lw* E) a*)) (admits-step (lw* E′) (admits-step (lw* E′) a*′)) _ _ _ _

    ee′ : EnvEq (X.C.env′ X.Rs) (X′.C.env′ X′.Rs)
    ee′ (here refl) = conn-hot-coh n s ρ uρ ρι ρ* uρ* E E′ p p* a a′ a* a*′ X.Rs X′.Rs sφ
    ee′ (there j) n′ q q* ad ad′ ad* ad*′ al₁ al₁′ lk₁ lk₁′ N′ y′ =
      let x = ee j n′ q q* (admits-wk X.CE.hD (lw E) ad) (admits-wk X′.CE.hD (lw E′) ad′)
                 (admits-wk X.CE.hD* (lw* E) ad*) (admits-wk X′.CE.hD* (lw* E′) ad*′) (λ i → al₁ (there i)) (λ i → al₁′ (there i)) lk₁ lk₁′ N′ y′
      in same (φ≡ x) (nl→ x)

    bφ : ∀ N y → Same (Out.rel X.Ob) (Out.rel X′.Ob) N y
    bφ = cb X.CE.ρ′ X.CE.uρ′ (ext ρι) X.CE.ρ*′ X.CE.uρ*′ (X.C.env′ X.Rs) (X′.C.env′ X′.Rs) ee′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) _ _ _ _ _ _ _ _

------------------------------------------------------------------------
-- Every author subterm

-- EVERY AUTHOR SUBTERM'S CUTS CORRESPOND.  An author's cold only: a
-- `fresh` cold emits the position it is subscribed at, and its
-- elaboration is subscribed deeper, so no map matches its value to the
-- plain one.
rel : ∀ {Γ A} n (o : SObs Γ A) → Full n (plain o)

-- EVERY AUTHOR SUBTERM'S MAP AND LATE ROWS ARE ITS SUBSCRIPTIONS' (`Coh`): a leaf's map
-- reads no environment, a one-to-one former's is its child's through its
-- table, a `connected`'s is its hot's, and a `flatMap`'s and a
-- `connect`'s are their children's.
rel-coh : ∀ {Γ A} n (o : SObs Γ A) → Coh n (plain o) (rel n o)

rel n (cold (fixedˢ m)) ρ uρ ρι ρ* uρ* env p p* a a* al lk = cold-tab m n ρ* uρ* p p* ⊢ cold-order m n ρ* uρ* (maps env) p p* al lk
rel n empty             ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  of-tab [] (λ x → instEmit (value x) root) (λ _ → refl) p p* ⊢ of-order [] _ _ (maps env) ρ p p* al lk
rel n (of xs)           ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  of-tab xs (λ x → instEmit (value x) root) (λ _ → refl) p p* ⊢ of-order xs _ _ (maps env) ρ p p* al lk
rel n (map f s)         ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = rel n s ρ uρ ρι ρ* uρ* env p p* a a* al lk in map-tab f (Out.rel O) ⊢ map-order f (Out.rel O) (Out.rest O)
rel n (scan f z s)      ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = rel n s ρ uρ ρι ρ* uρ* env p p* a a* al lk in scan-tab f z (Out.rel O) ⊢ scan-order f z (Out.rel O) (Out.rest O)
rel n (takeWhile i q s) ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = rel n s ρ uρ ρι ρ* uρ* env p p* a a* al lk in take-tab i q (Out.rel O) ⊢ take-order i q (Out.rel O) (Out.rest O)
rel n (flatMap op f s)  = flat-rel n op (λ a → plain (f a)) (plain s) (rel n s) (λ a → rel n (f a)) (λ a → rel-coh n (f a))
rel n (connect s b)     = conn-rel n (plain s) (plain b) (rel n s) (rel n b)
rel n (connected i)     ρ uρ ρι ρ* uρ* env p p* a a* al lk = hot env i n p p* a a* al lk
rel zero    (defer l)   ρ uρ ρι ρ* uρ* env p p* a a* al lk = spin-tab p p* ⊢ spin-order (maps env) ρ p p* al lk
rel (suc n) (defer l)   ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = rel n (Later.force l) ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (admits-step (lw env) a) (admits-step (lw* env) a*) (aligned-⊕ {Ψ = maps env} {ρ = ρ} al (ix 1) (ix 1)) (linked-r (linked-l lk (ix 1)) (ix 1))
  in defer-tab p p* (Out.rel O) ⊢ defer-order p p* (Out.rel O) (Out.rest O) al lk

rel-coh n (cold (fixedˢ m)) ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh n empty             ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh n (of xs)           ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh n (map f s)         ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y =
  let c = rel-coh n s ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y in same (φ≡ c) (nl→ c)
rel-coh n (scan f z s)      ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y =
  let c = rel-coh n s ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y in same (φ≡ c) (nl→ c)
rel-coh n (takeWhile i q s) ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ =
  take-cong i q (Out.rel (rel n s ρ uρ ρι ρ* uρ* E p p* a a* al lk)) (Out.rel (rel n s ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′))
    (rel-coh n s ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′)
rel-coh n (flatMap op f s)  =
  flat-coh n op (λ a → plain (f a)) (plain s) (rel n s) (λ a → rel n (f a)) (λ a → rel-coh n (f a)) (rel-coh n s)
rel-coh n (connect s b)     = conn-coh n (plain s) (plain b) (rel n s) (rel n b) (rel-coh n s) (rel-coh n b)
rel-coh n (connected i)     ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ = ee i n p p* a a′ a* a*′ al al′ lk lk′
rel-coh zero    (defer l)   ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh (suc n) (defer l)   ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ =
  defer-cong p p* (Out.rel (rel n (Later.force l) ρ uρ ρι ρ* uρ* E (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (admits-step (lw E) a) (admits-step (lw* E) a*) al₁ lk₁))
                  (Out.rel (rel n (Later.force l) ρ uρ ρι ρ* uρ* E′ (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (admits-step (lw E′) a′) (admits-step (lw* E′) a*′) al₁′ lk₁′))
    (rel-coh n (Later.force l) ρ uρ ρι ρ* uρ* E E′ ee (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ])
      (admits-step (lw E) a) (admits-step (lw E′) a′) (admits-step (lw* E) a*) (admits-step (lw* E′) a*′) al₁ al₁′ lk₁ lk₁′)
  where
    al₁  = aligned-⊕ {Ψ = maps E}  {ρ = ρ} al  (ix 1) (ix 1)
    al₁′ = aligned-⊕ {Ψ = maps E′} {ρ = ρ} al′ (ix 1) (ix 1)
    lk₁  = linked-r (linked-l lk  (ix 1)) (ix 1)
    lk₁′ = linked-r (linked-l lk′ (ix 1)) (ix 1)
