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
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary using (¬_; does)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; inside; _⊕_)
open import denotation.Events using (Timeline; From; fresh)
open import denotation.EmissionSet using (Ev; end; skip; EmissionSet; Unpinned; pin; _≺_; _≼_; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl)
open import denotation.Laws.Count using (under-guard)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; anyᵇ)
open import simultaneous.SObs using (SObs; fixedˢ; plain; plainˡ; lone; ext; module Elaborate)
open import simultaneous.Listing using (UncutEnv; listC)
open import simultaneous.TableCorr using (Rel; module Rel; Across; Same; same; φ≡; nl→; Corr; keys; in-keys)
open import simultaneous.TableKit using (Rows; TR; Got)
open import simultaneous.Horizon using (Tag; held; module Cuts; module ConnB; module ConnBd; module TakeBd; bounded-≃)
open import simultaneous.TreeBounded using (conn-tr→; conn-tr←; tree-bounded; src-out; src-held)
open import simultaneous.HorizonTree using (bd; BdEnv)
open import simultaneous.HorizonConn using (Mark; module ConnPair)
open import simultaneous.HorizonCorr using (module Inter; module Sub; Own; OwnPut; Btw; PB)
open import simultaneous.TableEnv
  using (Ren; ψ; π; Tab; Tab*; got-ok; pin-ok; after-ok; pin-after-ok; up; Linked; Cut; cut-sub;
  shownᵇ; Alike; alike; cut; cut-put; alike-l; alike-r; linked-l; linked-r; Maps; Aligned;
  aligned-⊕; Rest; Out; out; SameBd; sameBd; same-bd; HotR; EnvR; envR; EnvEq; maps; lw; lw*;
  hot; hot-coh; EnvCut; Full; Coh; Admits; DenOf; dbd; admits-step; admits-wk; tab-func;
  tab-flat)
open import simultaneous.TableMap using (map-tab)
open import simultaneous.TableTake using (take-tab; take-bd; take-bd*; take-cong)
open import simultaneous.TableScan using (scan-tab)
open import simultaneous.TableDefer using (defer-tab; defer-cong)
open import simultaneous.TableSpin using (spin-tab)
open import simultaneous.TableOf using (of-tab)
open import simultaneous.TableCold using (cold-tab)
open import simultaneous.TableLayers using (flat-rel; flat-coh)
open import simultaneous.TableFlat using (if-≡)
open import simultaneous.TableHot using (reader*; module ConnEnv; conn-hot; conn-hot-coh)
open import simultaneous.InstEmit using (instEmit; value)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate; passes)

------------------------------------------------------------------------
-- The order facts each one-to-one former keeps

postulate
  -- A LEAF FORMER'S ROWS: a cold's, an `of`'s and a spin's rows lie at its
  -- subscription's instant or at steps of timers it created there, each
  -- imaged at the alike step of the elaborated subscription; so each row
  -- inherits its subscription's link and its cuts of the hots in scope.
  cold-order : ∀ {Γ A} (m : From A 0) n {Δ} {ρ : ℕ → All Tb.Listed Γ} (ρ* : ℕ → All Tb.Listed Δ) uρ* (D* : DenOf ρ*) (Ψ : Maps Γ) p p* (a* : Admits D* p*)
            → Aligned Ψ ρ p p* → Linked p p* → Rest Ψ ρ (cold-tab m n ρ* uρ* D* p p* a*)
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
-- Boundaries moved along their parts' pins

-- A take keeps a boundary by its rows alone, whichever names it.
keep-map : ∀ {A i q} {c : ℕ → EmissionSet A} {Bd Bd′ Bd₀ : ℕ → Pos → Tag → Set}
         → Bd₀ ≡ TakeBd.Bd′ i q c Bd → SameBd Bd Bd′ → SameBd Bd₀ (TakeBd.Bd′ i q c Bd′)
keep-map refl sb = sameBd (λ { (x , k) → SameBd.to sb x , k }) (λ { (x , k) → SameBd.from sb x , k })

-- A connect's boundaries are its parts', each kept by the rows alone.
cbd-map : ∀ {A B p} {σ : ℕ → EmissionSet A} {β : ℕ → EmissionSet B} {Bdσ Bdσ′ Bdβ Bdβ′ : ℕ → Pos → Tag → Set}
        → SameBd Bdσ Bdσ′ → SameBd Bdβ Bdβ′ → SameBd (ConnBd.CBd p σ β Bdσ Bdβ) (ConnBd.CBd p σ β Bdσ′ Bdβ′)
cbd-map {p = p} {σ} {β} sσ sβ = sameBd (go (SameBd.to sσ) (SameBd.to sβ)) (go (SameBd.from sσ) (SameBd.from sβ))
  where
    go : ∀ {X X′ Y Y′ : ℕ → Pos → Tag → Set} → (∀ {N b g} → X N b g → X′ N b g) → (∀ {N b g} → Y N b g → Y′ N b g)
       → ∀ {N b g} → ConnBd.CBd p σ β X Y N b g → ConnBd.CBd p σ β X′ Y′ N b g
    go f h (ConnBd.bodyB x)      = ConnBd.bodyB (h x)
    go f h (ConnBd.burstB x i)   = ConnBd.burstB (f x) i
    go f h (ConnBd.echoB x i a)  = ConnBd.echoB (f x) i a
    go f h (ConnBd.keptB x i a)  = ConnBd.keptB (f x) i a

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
                 → let R = Out.rel (hot env j uρ uρ* n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD* (lw* env) ad*) (λ i → al (there i)) lk) in
                   ∀ N {k e} → TR (Tab n′ (connected j) ρ q N) k e → T (shownᵇ e)
                 → ∀ N′ → Alike (Ψ′ Rs (here refl) N′) (Rows (hotOf (σ N′))) k (Rel.φ R N k)

    -- An old hot's reader's partners cut the new hot alike, with the old.
    conn-old-bcorr : (Rs : Src) → ∀ {X} (j : X ∈ Γ) n′ q q* (ad : Admits D′ q) (ad* : Admits D*′ q*) (al : Aligned (Ψ′ Rs) ρ′ q q*) (lk : Linked q q*)
                   → let R = Out.rel (hot env j uρ uρ* n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD* (lw* env) ad*) (λ i → al (there i)) lk) in
                     ∀ N → Inter.BCorrX (Own (TR (Tab n′ (connected j) ρ q N)) (Rel.Late R N)) (Rel.φ R N)
                                        (OwnPut (TR (Tab n′ (connected j) ρ q N)) (Rel.Put R N)) (Rel.Bd R N) (Rel.Bd* R N) (EnvCut (Ψ′ Rs) ρ′ N)

  -- An old hot is read as before; its rows cut the new hot alike.
  old : (Rs : Src) → ∀ {X} (j : X ∈ Γ) → HotR (there j) ρ′ (ext ρι) ρ*′ (Ψ′ Rs) D′ D*′
  old Rs j _ _ n′ q q* ad ad* al lk = out (Out.rel O) (record
    { linked    = Rest.linked (Out.rest O)
    ; cuts      = cuts′
    ; self      = Rest.self (Out.rest O)
    ; self-at   = Rest.self-at (Out.rest O)
    ; self-flat = Rest.self-flat (Out.rest O)
    ; seen      = λ al′ → Rest.seen (Out.rest O) (λ i → al′ (there i))
    ; bcorr-env = conn-old-bcorr Rs j n′ q q* ad ad* al lk
    }) (Out.bd-pin O) (Out.bd-pin* O)
    where
      O = hot env j uρ uρ* n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD* (lw* env) ad*) (λ i → al (there i)) lk

      cuts′ : ∀ N {k e} → TR (Tab n′ (connected j) ρ q N) k e → T (shownᵇ e)
            → Aligned (Ψ′ Rs) ρ′ k (Rel.φ (Out.rel O) N k)
      cuts′ N x sh (here refl) N′ = conn-old-cut Rs j n′ q q* ad ad* al lk N x sh N′
      cuts′ N x sh (there i)   N′ = Rest.cuts (Out.rest O) N x sh i N′

  env′ : Src → EnvR ρ′ (ext ρι) ρ*′
  env′ Rs = envR (Ψ′ Rs) D′ D*′ hots hots-coh unended′
    where
      hots : ∀ {X} (i : X ∈ A ∷ Γ) → HotR i ρ′ (ext ρι) ρ*′ (Ψ′ Rs) D′ D*′
      hots (here refl) = conn-hot n s ρ uρ ρι ρ* uρ* env p p* a a* Rs
      hots (there j)   = old Rs j

      hots-coh : ∀ {X} (i : X ∈ A ∷ Γ) u u* n′ q q* (ad ad′ : Admits D′ q) (ad* ad*′ : Admits D*′ q*) (al al′ : Aligned (Ψ′ Rs) ρ′ q q*) (lk lk′ : Linked q q*) N y
               → Same (Out.rel (hots i u u* n′ q q* ad ad* al lk)) (Out.rel (hots i u u* n′ q q* ad′ ad*′ al′ lk′)) N y
      hots-coh (here refl) = conn-hot-coh n s ρ uρ ρι ρ* uρ* env env p p* a a a* a* Rs Rs (λ _ _ → same refl (λ nl → nl))
      hots-coh (there j) _ _ n′ q q* ad ad′ ad* ad*′ al al′ lk lk′ N y =
        let x = hot-coh env j uρ uρ* n′ q q* (admits-wk hD (lw env) ad) (admits-wk hD (lw env) ad′) (admits-wk hD* (lw* env) ad*) (admits-wk hD* (lw* env) ad*′)
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

  -- The body's tables.
  Bp : ℕ → Maybe (Tb.Listed B)
  Bp = Tab n b ρ′ (p ⊕ [ ix 0 ])

  isBody : ℕ → Pos → Bool
  isBody N y = anyᵇ (λ k → does (k ≟ᵖ y)) (keys (Bp N))

  -- THE CONNECT'S ROWS: the body's, then the source's own past the
  -- body's subscription, one label down, its subscribe burst as pins of
  -- the connect and the rest unsubscribed while the body runs.  A body
  -- row is imaged along the body's map; a source row at its annotated
  -- image, one label down, as the elaborated connect shows it.
  module ConnTab (Rs : Src) (Ob : Out n b ρ′ uρ′ (ext ρι) ρ*′ uρ*′ (Ψ′ Rs) D′ D*′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])) where
    Rb : Rel Bp (Tab* n (ext ρι) b ρ*′ (p* ⊕ [ ix 0 ])) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
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
      ct-in-bk       : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
      ct-after-φ     : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Late′ N k → p* ≼ φ′ N k

    -- THE CONNECT'S HANGS: the body's boundaries, the source's subscribe
    -- burst, and the source's own kept past the body's (`ConnB`); each
    -- partnered with its image's (`ConnPair`).  Each table is a connect
    -- of its parts, the elaborated over the annotated source.
    RS : Rel (Tab n s ρ (p ⊕ [ ix 1 ])) (Tab* n ρι s ρ* (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])) (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ])
    RS = Out.rel Rs

    σc : ℕ → EmissionSet A
    σc N = TR (Tab n s ρ (p ⊕ [ ix 1 ]) N)

    βc : ℕ → EmissionSet B
    βc N = TR (Bp N)

    σc* : ℕ → EmissionSet (AIE A)
    σc* N = TR (listC (3 + N) n (annotate (elab ρι s)) (ρ* N) (p* ⊕ [ ix 1 ]))

    βc* : ℕ → EmissionSet (IE B)
    βc* N = TR (Tab* n (ext ρι) b ρ*′ (p* ⊕ [ ix 0 ]) N)

    -- A source row's image: the hot's, under the annotation's reader;
    -- a late one placed where the hot puts it, or at that image.
    φσ : ℕ → Pos → Pos
    φσ N = ψ (srcMap Rs N)

    Pσ : ℕ → Pos → Pos → Set
    Pσ N k l = l ≡ ψ (srcMap Rs N) k ⊎ π (srcMap Rs N) k l

    -- The annotated source's hangs: its tree's.
    ct-ann-bd* : ℕ → Pos → Tag → Set
    ct-ann-bd* = bd n (annotate (elab ρι s)) ρ* uρ* (dbd (lw* env)) (p* ⊕ [ ix 1 ])

    ct-ann-bounded* : Cuts.Bounded σc* ct-ann-bd*
    ct-ann-bounded* = tree-bounded n (annotate (elab ρι s)) ρ* uρ* (lw* env) (p* ⊕ [ ix 1 ]) (admits-step (lw* env) a*)

    ct-ann-out* : ∀ {N b g} → ct-ann-bd* N b g → b ≺ p* ⊎ (p* ⊕ [ ix 1 ]) ≺ b
    ct-ann-out* {N} {b} {g} = src-out ρ* uρ* (lw* env) n (annotate (elab ρι s)) p* a* {N} {b} {g}

    ct-ann-held* : ∀ {N b q} → ct-ann-bd* N b (held q) → T (inside (p* ⊕ [ ix 1 ]) b) → (p* ⊕ [ ix 1 ]) ≼ q
    ct-ann-held* {N} {b} {q} = src-held ρ* uρ* (lw* env) n (annotate (elab ρι s)) p* a* {N} {b} {q}

    ct-conn→  : ∀ {N y e} → TR (P N) y e → Connecting.ConnT p (σc N) (βc N) y e
    ct-conn→ {N} {y} {e} = conn-tr→ n s b uρ p {N} {y} {e}

    ct-conn←  : ∀ {N y e} → Connecting.ConnT p (σc N) (βc N) y e → TR (P N) y e
    ct-conn← {N} {y} {e} = conn-tr← n s b uρ p {N} {y} {e}

    ct-conn*→ : ∀ {N y e} → TR (Q N) y e → Connecting.ConnT p* (σc* N) (βc* N) y e
    ct-conn*→ {N} {y} {e} = conn-tr→ n (annotate (elab ρι s)) (elab (ext ρι) b) uρ* p* {N} {y} {e}

    ct-conn*← : ∀ {N y e} → Connecting.ConnT p* (σc* N) (βc* N) y e → TR (Q N) y e
    ct-conn*← {N} {y} {e} = conn-tr← n (annotate (elab ρι s)) (elab (ext ρι) b) uρ* p* {N} {y} {e}

    postulate
      ct-src-out  : ∀ {N b g} → Rel.Bd RS N b g → b ≺ p ⊎ (p ⊕ [ ix 1 ]) ≺ b
      ct-src-held : ∀ {N b q} → Rel.Bd RS N b (held q) → T (inside (p ⊕ [ ix 1 ]) b) → (p ⊕ [ ix 1 ]) ≼ q

    -- The body's rows lie past the connect.
    ct-body-after : ∀ {N c} → βc N c end → p ≺ c
    ct-body-after {N} {c} x = ≺-≼-≺ {p} {p ⊕ [ ix 0 ]} {c} (≺-ext p []) (Rel.after Rb x)

    ct-body-after* : ∀ {N c} → βc* N c end → p* ≺ c
    ct-body-after* {N} {c} x = ≺-≼-≺ {p*} {p* ⊕ [ ix 0 ]} {c} (≺-ext p* []) (Rel.after* Rb x)

    module CB  = ConnB p σc βc (Rel.Bd RS) (Rel.Bd Rb) (Rel.bounded RS) (Rel.bounded Rb)
      (λ {N} {b} {g} → ct-src-out {N} {b} {g}) (λ {N} {b} {q} → ct-src-held {N} {b} {q}) (λ {N} {c} → ct-body-after {N} {c})
    module CB* = ConnB p* σc* βc* ct-ann-bd* (Rel.Bd* Rb) ct-ann-bounded* (Rel.bounded* Rb)
      (λ {N} {b} {g} → ct-ann-out* {N} {b} {g}) (λ {N} {b} {q} → ct-ann-held* {N} {b} {q}) (λ {N} {c} → ct-body-after* {N} {c})
    module CP (N : ℕ) = ConnPair N p p* σc βc (Rel.Bd RS) (Rel.Bd Rb) (Rel.bounded RS) (Rel.bounded Rb)
      (λ {N} {b} {g} → ct-src-out {N} {b} {g}) (λ {N} {b} {q} → ct-src-held {N} {b} {q}) (λ {N} {c} → ct-body-after {N} {c})
      σc* βc* ct-ann-bd* (Rel.Bd* Rb) ct-ann-bounded* (Rel.bounded* Rb)
      (λ {N} {b} {g} → ct-ann-out* {N} {b} {g}) (λ {N} {b} {q} → ct-ann-held* {N} {b} {q}) (λ {N} {c} → ct-body-after* {N} {c})
      (λ _ → ⊥) (λ _ _ → ⊥) (φσ N) (Rel.φ Rb N) (φ′ N) (Rel.Late RS N) (Rel.Late Rb N) (Late′ N) (Pσ N) (Rel.Put Rb N) (Put′ N)

    -- WHAT THE PARTS OWE THE PAIR: the source's pair against the annotated
    -- source; one map and the parts' late rows and placements; the gaps; the
    -- body cutting each source mark pair alike; the burst holding
    -- partners together; the body's ends each other's images.
    postulate
      ct-src-bcorr  : ∀ N → CP.IS.BCorr N
      ct-φc-body : ∀ {N k e} → βc N k e → φ′ N k ≡ Rel.φ Rb N k
      ct-φc-echo : ∀ {N k e} → σc N k e → φ′ N (k ⊕ [ ix 0 ]) ≡ φσ N k ⊕ [ ix 0 ]
      ct-late-body : ∀ {N k} → Rel.Late Rb N k → Late′ N k
      ct-late-echo : ∀ {N k} → Rel.Late RS N k → Late′ N (k ⊕ [ ix 0 ])
      ct-put-split : ∀ {N k e l} → CB.Cc N k e → Put′ N k l
                   → (Σ (Ev B) λ e′ → βc N k e′ × Rel.Put Rb N k l)
                   ⊎ (Σ Pos λ j → Σ (Ev A) λ e′ → Σ Pos λ l₀ → σc N j e′ × k ≡ j ⊕ [ ix 0 ] × Pσ N j l₀ × l ≡ l₀ ⊕ [ ix 0 ])
      ct-img     : ∀ {N k} → Own (CB.Cc N) (Late′ N) k → Σ (Ev (IE B)) (CB*.Cc N (φ′ N k))
      ct-put-row : ∀ {N k e l} → CB.Cc N k e → Put′ N k l → Σ (Ev (IE B)) (CB*.Cc N l)
      ct-gap-src   : ∀ {N b g y e} → Rel.Bd RS N b g → CB.Cc N y e → ¬ y ⊑ b
      ct-gap-src*  : ∀ {N b g y e} → ct-ann-bd* N b g → CB*.Cc N y e → ¬ y ⊑ b
      ct-held-src  : ∀ {N b q y e} → Rel.Bd RS N b (held q) → CB.Cc N y e → ¬ y ⊑ q
      ct-held-src* : ∀ {N b q y e} → ct-ann-bd* N b (held q) → CB*.Cc N y e → ¬ y ⊑ q
      ct-held-body  : ∀ {N b q y e} → Rel.Bd Rb N b (held q) → CB.Cc N y e → ¬ y ⊑ q
      ct-held-body* : ∀ {N b q y e} → Rel.Bd* Rb N b (held q) → CB*.Cc N y e → ¬ y ⊑ q
      ct-body-src : ∀ {N z z*} → Mark (Rel.Bd RS N) z → Mark (ct-ann-bd* N) z* → CP.IS.Between N z z*
                  → Btw (Own (βc N) (Rel.Late Rb N)) (Rel.φ Rb N) z z*
      ct-body-src-put : ∀ {N z z*} → Mark (Rel.Bd RS N) z → Mark (ct-ann-bd* N) z* → CP.IS.PutBefore N z z*
                      → PB (OwnPut (βc N) (Rel.Put Rb N)) z z*
      ct-home→ : ∀ {N b b* g g*} → Rel.Bd RS N b g → ct-ann-bd* N b* g* → CP.IS.Between N b b*
               → T (inside (p ⊕ [ ix 1 ]) b) → T (inside (p* ⊕ [ ix 1 ]) b*)
      ct-home← : ∀ {N b b* g g*} → Rel.Bd RS N b g → ct-ann-bd* N b* g* → CP.IS.Between N b b*
               → T (inside (p* ⊕ [ ix 1 ]) b*) → T (inside (p ⊕ [ ix 1 ]) b)
      ct-end→ : ∀ {N c} → βc N c end → ¬ Rel.Late Rb N c × βc* N (Rel.φ Rb N c) end
      ct-end← : ∀ {N c*} → βc* N c* end → Σ Pos λ c → βc N c end × ¬ Rel.Late Rb N c × c* ≡ Rel.φ Rb N c
      ct-rows-after  : ∀ {N k e} → CB.Cc N k e → p ≺ k
      ct-rows-after* : ∀ {N k e} → CB*.Cc N k e → p* ≺ k

    -- THE BODY'S PAIR CUTS ITS SOURCE ALIKE: the source is the first hot
    -- of the body's scope, so the body's partners cut it alike
    -- (`Rest.bcorr-env`).  Its rows are the source's table's, its images
    -- the annotated rows under the reader, its placements the source's.
    postulate
      -- No source row lies past the source's end.
      ct-src-hot : ∀ {N k e} → σc N k e → Rows (hotOf (σ N)) k e
      -- A source row that is pinned or late is placed at its image.
      ct-src-img : ∀ {N k e} → σc N k e → (Unpinned e × ¬ Rel.Late RS N k) ⊎ π (srcMap Rs N) k (φσ N k)

    src-cut : ∀ {N z z*} → EnvCut (Ψ′ Rs) ρ′ N z z* → CP.SrcCut N z z*
    src-cut {N} {z} {z*} ((bs , pbs) , _) = btw , pb
      where
        btw : Btw (CP.SrcRow N) (φσ N) z z*
        btw (inj₁ (e , x , un , nl)) = bs (e , ct-src-hot x , un , nl)
        btw (inj₂ ())

        pb : PB (CP.SrcPut N) z z*
        pb (inj₁ ((e , x) , inj₂ pl)) kz = pbs ((e , ct-src-hot x) , pl) kz
        pb (inj₁ ((e , x) , inj₁ refl)) kz with ct-src-img x
        ... | inj₁ (un , nl) = proj₁ (bs (e , ct-src-hot x , un , nl)) kz
        ... | inj₂ pl        = pbs ((e , ct-src-hot x) , pl) kz
        pb (inj₂ ()) _

    ct-body-bcorr : ∀ N → CP.IB.BCorrX N (CP.SrcCut N)
    ct-body-bcorr N = Inter.weakenX _ _ _ _ _ (λ {z} {z*} → src-cut {N} {z} {z*}) (Rest.bcorr-env (Out.rest Ob) N)

    ct-bd ct-bd* : ℕ → Pos → Tag → Set
    ct-bd  = CB.CBd
    ct-bd* = CB*.CBd

    ct-bounded : Cuts.Bounded (λ N → TR (P N)) ct-bd
    ct-bounded = bounded-≃ (λ {N} {y} {e} → ct-conn← {N} {y} {e}) (λ {N} {y} {e} → ct-conn→ {N} {y} {e}) CB.bounded

    ct-bounded* : Cuts.Bounded (λ N → TR (Q N)) ct-bd*
    ct-bounded* = bounded-≃ (λ {N} {y} {e} → ct-conn*← {N} {y} {e}) (λ {N} {y} {e} → ct-conn*→ {N} {y} {e}) CB*.bounded

    postulate
      -- THE CONNECT'S HANGS ACROSS CUTS: its body's and its source's, as
      -- at one cut.
      ct-across : Across (λ N → TR (P N)) (λ N → TR (Q N)) φ′ Put′ Late′ ct-bd ct-bd*

    -- A put skip is imaged as any row is, at a row of the elaborated
    -- connect, so over no boundary.
    ct-put-off* : ∀ {N k l b g} → TR (P N) k skip → ¬ Late′ N k → Put′ N k l → ct-bd* N b g → ¬ φ′ N k ⊑ b
    ct-put-off* x nl _ b₀ = proj₂ (Cuts.Bounded.gap CB*.bounded b₀ (proj₂ (ct-img (skip , ct-conn→ x , tt , nl))))

    ct-bcorr : ∀ N → Inter.BCorr (Own (TR (P N)) (Late′ N)) (φ′ N) (OwnPut (TR (P N)) (Put′ N)) (ct-bd N) (ct-bd* N)
    ct-bcorr N = Sub.restrict
      (λ { (e , x , un , nl) → inj₁ (e , ct-conn→ x , un , nl) })
      (λ { ((e , x) , pl) → inj₁ ((e , ct-conn→ x) , pl) })
      (CP.Pair.corr N (ct-src-bcorr N) (ct-body-bcorr N)
        (λ {k} {e} → ct-φc-body {N} {k} {e}) (λ {k} {e} → ct-φc-echo {N} {k} {e}) (λ ())
        (λ {k} → ct-late-body {N} {k}) (λ {k} → ct-late-echo {N} {k})
        (λ {k} {e} {l} → ct-put-split {N} {k} {e} {l}) (λ {k} → ct-img {N} {k}) (λ {k} {e} {l} → ct-put-row {N} {k} {e} {l})
        (λ {b} {g} {y} {e} → ct-gap-src {N} {b} {g} {y} {e}) (λ {b} {g} {y} {e} → ct-gap-src* {N} {b} {g} {y} {e})
        (λ {b} {q} {y} {e} → ct-held-src {N} {b} {q} {y} {e}) (λ {b} {q} {y} {e} → ct-held-src* {N} {b} {q} {y} {e})
        (λ {b} {q} {y} {e} → ct-held-body {N} {b} {q} {y} {e}) (λ {b} {q} {y} {e} → ct-held-body* {N} {b} {q} {y} {e})
        (λ {z} {z*} → ct-body-src {N} {z} {z*}) (λ {z} {z*} → ct-body-src-put {N} {z} {z*})
        (λ {b} {b*} {g} {g*} → ct-home→ {N} {b} {b*} {g} {g*}) (λ {b} {b*} {g} {g*} → ct-home← {N} {b} {b*} {g} {g*})
        (λ {c} → ct-end→ {N} {c}) (λ {c*} → ct-end← {N} {c*})
        (λ {k} {e} → ct-rows-after {N} {k} {e}) (λ {k} {e} → ct-rows-after* {N} {k} {e}) (λ ()))

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

    rel′ : Rel P Q p p*
    rel′ = record
      { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = ct-corr ; bk = bk′ ; in-bk = ct-in-bk ; pb-few = ct-pb-few
      ; func = ct-func ; func* = ct-func* ; flat = ct-flat ; flat* = ct-flat*
      ; pin-in = ct-pin-in ; pin-in* = ct-pin-in* ; got = ct-got ; got* = ct-got*
      ; after = ct-after ; after* = ct-after* ; after-φ = ct-after-φ ; pin-after* = ct-pin-after*
      ; Bd = ct-bd ; Bd* = ct-bd* ; bounded = ct-bounded ; bounded* = ct-bounded* ; bcorr = ct-bcorr ; across = ct-across ; skip-off* = ct-put-off* }

  conn-tab : (Rs : Src) → Out n b ρ′ uρ′ (ext ρι) ρ*′ uρ*′ (Ψ′ Rs) D′ D*′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) → Rel P Q p p*
  conn-tab = ConnTab.rel′

  postulate
    -- The connect's rows are the body's and the source's, each carrying
    -- its own order facts; the source's pins are its subscribe burst.
    conn-order : (Rs : Src) (Ob : Out n b ρ′ uρ′ (ext ρι) ρ*′ uρ*′ (Ψ′ Rs) D′ D*′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]))
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

  Ob : Out n b CE.ρ′ CE.uρ′ (ext ρι) CE.ρ*′ CE.uρ*′ (CE.Ψ′ Rs) CE.D′ CE.D*′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
  Ob = Fb CE.ρ′ CE.uρ′ (ext ρι) CE.ρ*′ CE.uρ*′ (C.env′ Rs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ])
         CE.body-ad CE.body-ad* (C.al′ Rs al lk)
         (linked-r (linked-l lk (ix 0)) (ix 0))

conn-rel : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Full n s → Full n b → Full n (connect s b)
conn-rel {Γ} {A} n s b Fs Fb ρ uρ {Δ} ρι ρ* uρ* env p p* a a* al lk =
  out (C.conn-tab Rs Ob) (C.conn-order Rs Ob al lk) (cbd-map (Out.bd-pin Rs) (subst (λ (β : BdEnv (A ∷ Γ)) → SameBd (Rel.Bd (Out.rel Ob)) (bd n b CE.ρ′ CE.uρ′ β (p ⊕ [ ix 0 ]))) CE.D′-bd (Out.bd-pin Ob)))
      (cbd-map same-bd (subst (λ (β : BdEnv (AIE A ∷ Δ)) → SameBd (Rel.Bd* (Out.rel Ob)) (bd n (elab (ext ρι) b) CE.ρ*′ CE.uρ*′ β (p* ⊕ [ ix 0 ]))) CE.D*′-bd (Out.bd-pin* Ob)))
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
    ee′ (there j) _ _ n′ q q* ad ad′ ad* ad*′ al₁ al₁′ lk₁ lk₁′ N′ y′ =
      let x = ee j uρ uρ* n′ q q* (admits-wk X.CE.hD (lw E) ad) (admits-wk X′.CE.hD (lw E′) ad′)
                 (admits-wk X.CE.hD* (lw* E) ad*) (admits-wk X′.CE.hD* (lw* E′) ad*′) (λ i → al₁ (there i)) (λ i → al₁′ (there i)) lk₁ lk₁′ N′ y′
      in same (φ≡ x) (nl→ x)

    bφ : ∀ N y → Same (Out.rel X.Ob) (Out.rel X′.Ob) N y
    bφ = cb X.CE.ρ′ X.CE.uρ′ (ext ρι) X.CE.ρ*′ X.CE.uρ*′ (X.C.env′ X.Rs) (X′.C.env′ X′.Rs) ee′ (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) _ _ _ _ _ _ _ _

------------------------------------------------------------------------
-- The one-to-one formers and `defer`, over any child

map-rel : ∀ {Γ A B} n (f : A → B) (s : Obs Timeline Γ A) → Full n s → Full n (map f s)
map-rel n f s Fs ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = Fs ρ uρ ρι ρ* uρ* env p p* a a* al lk in out (map-tab f (Out.rel O)) (map-order f (Out.rel O) (Out.rest O)) (Out.bd-pin O) (Out.bd-pin* O)

map-coh : ∀ {Γ A B} n (f : A → B) (s : Obs Timeline Γ A) (Fs : Full n s) → Coh n s Fs → Coh n (map f s) (map-rel n f s Fs)
map-coh n f s Fs cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y =
  let c = cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y in same (φ≡ c) (nl→ c)

scan-rel : ∀ {Γ A B} n (f : B → A → B) (z : B) (s : Obs Timeline Γ A) → Full n s → Full n (scan f z s)
scan-rel n f z s Fs ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = Fs ρ uρ ρι ρ* uρ* env p p* a a* al lk in out (scan-tab f z (Out.rel O)) (scan-order f z (Out.rel O) (Out.rest O)) (Out.bd-pin O) (Out.bd-pin* O)

scan-coh : ∀ {Γ A B} n (f : B → A → B) (z : B) (s : Obs Timeline Γ A) (Fs : Full n s) → Coh n s Fs → Coh n (scan f z s) (scan-rel n f z s Fs)
scan-coh n f z s Fs cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y =
  let c = cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y in same (φ≡ c) (nl→ c)

take-rel : ∀ {Γ A} n i (q : A → Bool) (s : Obs Timeline Γ A) → Full n s → Full n (takeWhile i q s)
take-rel n i q s Fs ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = Fs ρ uρ ρι ρ* uρ* env p p* a a* al lk in out (take-tab i q (Out.rel O)) (take-order i q (Out.rel O) (Out.rest O)) (keep-map {i = i} {q = q} {c = λ N → TR (Tab n s ρ p N)} {Bd = Rel.Bd (Out.rel O)} (take-bd i q (Out.rel O)) (Out.bd-pin O))
      (keep-map {i = i} {q = passes q} {c = λ N → TR (Tab* n ρι s ρ* p* N)} {Bd = Rel.Bd* (Out.rel O)} (take-bd* i q (Out.rel O)) (Out.bd-pin* O))

take-coh : ∀ {Γ A} n i (q : A → Bool) (s : Obs Timeline Γ A) (Fs : Full n s) → Coh n s Fs → Coh n (takeWhile i q s) (take-rel n i q s Fs)
take-coh n i q s Fs cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ =
  take-cong i q (Out.rel (Fs ρ uρ ρι ρ* uρ* E p p* a a* al lk)) (Out.rel (Fs ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′))
    (cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′)

defer-rel : ∀ {Γ A} n (l : Later Timeline Γ A) → Full n (Later.force l) → Full (suc n) (defer l)
defer-rel n l Fl ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  let O = Fl ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (admits-step (lw env) a) (admits-step (lw* env) a*) (aligned-⊕ {Ψ = maps env} {ρ = ρ} al (ix 1) (ix 1)) (linked-r (linked-l lk (ix 1)) (ix 1))
  in out (defer-tab p p* (Out.rel O)) (defer-order p p* (Out.rel O) (Out.rest O) al lk) (Out.bd-pin O) (Out.bd-pin* O)

defer-coh : ∀ {Γ A} n (l : Later Timeline Γ A) (Fl : Full n (Later.force l)) → Coh n (Later.force l) Fl → Coh (suc n) (defer l) (defer-rel n l Fl)
defer-coh n l Fl cl ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ =
  defer-cong p p* (Out.rel (Fl ρ uρ ρι ρ* uρ* E (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (admits-step (lw E) a) (admits-step (lw* E) a*) al₁ lk₁))
                  (Out.rel (Fl ρ uρ ρι ρ* uρ* E′ (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (admits-step (lw E′) a′) (admits-step (lw* E′) a*′) al₁′ lk₁′))
    (cl ρ uρ ρι ρ* uρ* E E′ ee (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ])
      (admits-step (lw E) a) (admits-step (lw E′) a′) (admits-step (lw* E) a*) (admits-step (lw* E′) a*′) al₁ al₁′ lk₁ lk₁′)
  where
    al₁  = aligned-⊕ {Ψ = maps E}  {ρ = ρ} al  (ix 1) (ix 1)
    al₁′ = aligned-⊕ {Ψ = maps E′} {ρ = ρ} al′ (ix 1) (ix 1)
    lk₁  = linked-r (linked-l lk  (ix 1)) (ix 1)
    lk₁′ = linked-r (linked-l lk′ (ix 1)) (ix 1)

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

rel n (cold (fixedˢ m)) ρ uρ ρι ρ* uρ* env p p* a a* al lk = out (cold-tab m n ρ* uρ* (lw* env) p p* a*) (cold-order m n ρ* uρ* (lw* env) (maps env) p p* a* al lk) same-bd same-bd
rel n empty             ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  out (of-tab [] (λ x → instEmit (value x) root) (λ _ → refl) p p*) (of-order [] _ _ (maps env) ρ p p* al lk) same-bd same-bd
rel n (of xs)           ρ uρ ρι ρ* uρ* env p p* a a* al lk =
  out (of-tab xs (λ x → instEmit (value x) root) (λ _ → refl) p p*) (of-order xs _ _ (maps env) ρ p p* al lk) same-bd same-bd
rel n (map f s)         = map-rel n f (plain s) (rel n s)
rel n (scan f z s)      = scan-rel n f z (plain s) (rel n s)
rel n (takeWhile i q s) = take-rel n i q (plain s) (rel n s)
rel n (flatMap op f s)  = flat-rel n op (λ a → plain (f a)) (plain s) (rel n s) (λ a → rel n (f a)) (λ a → rel-coh n (f a))
rel n (connect s b)     = conn-rel n (plain s) (plain b) (rel n s) (rel n b)
rel n (connected i)     ρ uρ ρι ρ* uρ* env p p* a a* al lk = hot env i uρ uρ* n p p* a a* al lk
rel zero    (defer l)   ρ uρ ρι ρ* uρ* env p p* a a* al lk = out (spin-tab p p*) (spin-order (maps env) ρ p p* al lk) same-bd same-bd
rel (suc n) (defer l)   = defer-rel n (plainˡ l) (rel n (Later.force l))

rel-coh n (cold (fixedˢ m)) ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh n empty             ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh n (of xs)           ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh n (map f s)         = map-coh n f (plain s) (rel n s) (rel-coh n s)
rel-coh n (scan f z s)      = scan-coh n f z (plain s) (rel n s) (rel-coh n s)
rel-coh n (takeWhile i q s) = take-coh n i q (plain s) (rel n s) (rel-coh n s)
rel-coh n (flatMap op f s)  =
  flat-coh n op (λ a → plain (f a)) (plain s) (rel n s) (λ a → rel n (f a)) (λ a → rel-coh n (f a)) (rel-coh n s)
rel-coh n (connect s b)     = conn-coh n (plain s) (plain b) (rel n s) (rel n b) (rel-coh n s) (rel-coh n b)
rel-coh n (connected i)     ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ = ee i uρ uρ* n p p* a a′ a* a*′ al al′ lk lk′
rel-coh zero    (defer l)   ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y = same refl (λ nl → nl)
rel-coh (suc n) (defer l)   = defer-coh n (plainˡ l) (rel n (Later.force l)) (rel-coh n (Later.force l))
