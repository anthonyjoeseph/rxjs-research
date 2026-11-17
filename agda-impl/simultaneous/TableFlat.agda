{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S CASE (`flat-rel`): the plain flatMap's record against its
-- elaboration, one layer at a time.  The plain side stays the flatMap's
-- own table; the elaborated side grows outward from the lanes' flatMap
-- (`core`) through the combined scan, the closer and the share.
--
-- The source is related once, at the share's subscription, in the
-- environment the share's trigger extends; its hot is the shared table
-- the lanes' flatMap reads.  The lanes are related wherever they are
-- subscribed alike, each in the environment the flatMap's four binders
-- extend, which no lane reads.
--
-- A lane is subscribed past its creator, so its pair is aligned from its
-- creator's.  `flat-core` owes that alignment, one story per operator:
-- merge, switch and exhaust subscribe each lane under its value's row, so
-- the source's `cuts` and `linked` at the row align it; only the bounded
-- merge queues a lane under an earlier lane's end, a run-dependent row.
module simultaneous.TableFlat where

open import Data.Bool using (Bool; T; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe as M
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does; yes; no)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; of; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; _<ᵖ_; ix; sub; last; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Unpinned; out; end; pin; _≼_)
open import denotation.Laws.Modulus using (AgreeTo)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; Row; rows; ends; anyᵇ; values; afterL; module BoundedL; module Order)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.TableCorr using (Rel; TR; Corr; Cons; Got)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv using (Ren; wk; Tab; Tab*; up; _⊕ˡ_; Linked; linked-l; linked-r; linked-r*; Aligned; aligned-⊕; aligned-r*; Rest; Out; _⊢_; EnvR; maps; env-wk; Holds; Full)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

module Flat {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) where

  ----------------------------------------------------------------------
  -- The elaborated parts

  ρι⁴ : Ren Γ (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρι⁴ = wk (wk (wk (wk ρι)))

  s* : Obs Timeline (⊤ ∷ Δ) (IE A)
  s* = elab (wk ρι) s

  core : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  core op = flatMap op (λ a → laneˢ (elab ρι⁴ (f a))) (each valuesOf (connected (there (here refl))))

  inner : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner op = connect (core op) (combined op (trackers Γ 0 (wk (wk (wk (wk ρι))))))

  body : FlatOp → Obs Timeline (IE A ∷ ⊤ ∷ Δ) (IE B)
  body op = connect closer (inner op)

  shared : Obs Timeline (⊤ ∷ Δ) (IE A)
  shared = flatMap (mergeᶠ nothing) (λ _ → s*) (connected (here refl))

  ----------------------------------------------------------------------
  -- Their subscriptions and hots

  -- The share's body, the closer's body, the combined connect, and the
  -- lanes' flatMap.
  c₃ c₂ c₁ c₀ : Pos
  c₃ = p* ⊕ [ ix 0 ] ⊕ [ ix 0 ]
  c₂ = c₃ ⊕ [ ix 0 ]
  c₁ = c₂ ⊕ [ ix 1 ]
  c₀ = c₂ ⊕ [ ix 0 ]

  -- The source's elaborated subscription: the lane of the trigger's value,
  -- read by the shared flatMap.
  sp* : Pos
  sp* = p* ⊕ˡ (ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ [])

  tt-tab : ℕ → Tb.Listed ⊤
  tt-tab N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ])))

  ρ*s : ℕ → All Tb.Listed (⊤ ∷ Δ)
  ρ*s N = tt-tab N ∷ ρ* N

  uρ*s : ∀ N → UncutEnv (ρ*s N)
  uρ*s N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ]))) , uρ* N

  sh-tab : ℕ → Tb.Listed (IE A)
  sh-tab N = hotOf (proj₁ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ])))

  ρ*h : ℕ → All Tb.Listed (IE A ∷ ⊤ ∷ Δ)
  ρ*h N = sh-tab N ∷ ρ*s N

  uρ*h : ∀ N → UncutEnv (ρ*h N)
  uρ*h N = proj₂ (proj₂ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]))) , uρ*s N

  cl-tab : ℕ → Tb.Listed (IE B)
  cl-tab N = hotOf (proj₁ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ])))

  ρ*c : ℕ → All Tb.Listed (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρ*c N = cl-tab N ∷ ρ*h N

  ----------------------------------------------------------------------
  -- The children's records

  -- The source, at the share's subscription.
  Src : Set₁
  Src = Out n s ρ (wk ρι) ρ*s (maps env) p sp*

  -- Each lane, wherever subscribed alike, whatever the four binders hold.
  Lanes : Set₁
  Lanes = ∀ a (t₁ : ℕ → Tb.Listed ⊤) (t₂ : ℕ → Tb.Listed (IE B)) (t₃ : ℕ → Tb.Listed (IE A)) (t₄ : ℕ → Tb.Listed ⊤)
        → (∀ N → UncutEnv (t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N))
        → Holds n (f a) ρ ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) (env-wk t₁ (env-wk t₂ (env-wk t₃ (env-wk t₄ env))))

  -- The plain flatMap's tables.
  P : FlatOp → ℕ → _
  P op = Tab n (flatMap op f s) ρ p

  -- The lanes' flatMap related to the plain flatMap.
  Core : FlatOp → Set₁
  Core op = Src → Lanes → Aligned (maps env) ρ p p* → Linked p p*
          → Rel (P op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁

  ----------------------------------------------------------------------
  -- The layers

  -- THE LANES' FLATMAP: the shared hot is the source's elaborated rows,
  -- each value read off by `each valuesOf` under its image; each value's
  -- elaborated lane is the plain lane's, run through `laneˢ`.  Its rows
  -- are the plain flatMap's values and ends, along the source's map for
  -- the source's rows and each lane's for its own.
  --
  -- A lane's record is had only from a cut: `Lanes` wants the lane's
  -- value and its pair's alignment, and both are read off the source's
  -- row `TR (Ps N) q (out a)` and `Rest.cuts` at it.  So `φ`, `Put` and
  -- the preimage lists are written per cut, each lane row through its own
  -- lane's record at that cut; `back` is what lets the erasure read them
  -- at the cut settling the image.

  ----------------------------------------------------------------------
  -- The lanes

  -- What the source's and lanes' records give, for every operator.
  module Parts (Os : Src) (Ls : Lanes) where

    -- `laneˢ` under an elaborated lane's subscription: its trigger, its
    -- shared run, the lane itself, and the reader its rows are read by.
    laneL laneX readerR : Pos → Pos
    laneL st = st ⊕ˡ (ix 0 ∷ ix 1 ∷ [])
    laneX st = laneL st ⊕ˡ (ix 1 ∷ ix 0 ∷ sub (laneL st ⊕ˡ (ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])
    readerR st = laneL st ⊕ˡ (ix 0 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])

    -- Where `counted` emits what the reader at `r` reads.
    emitAt : Pos → Pos
    emitAt r = r ⊕ˡ (ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ [])

    uρ*c : ∀ N → UncutEnv (ρ*c N)
    uρ*c N = proj₂ (proj₂ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ]))) , uρ*h N

    -- A lane's trigger, under its subscription.
    trig : Pos → ℕ → Tb.Listed ⊤
    trig st N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ])))

    utrig : ∀ st N → UncutEnv (trig st N ∷ ρ*c N)
    utrig st N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ]))) , uρ*c N

    -- A table's ends.
    endsOf : ∀ {X : Set} → Maybe (Tb.Listed X) → List Pos
    endsOf nothing   = []
    endsOf (just Lx) = ends (rows Lx)

    endAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
    endAt m y = anyᵇ (λ k → does (k ≟ᵖ y)) (endsOf m)

    -- The source's tables.
    S : ℕ → Maybe (Tb.Listed A)
    S = Tab n s ρ p

    -- A value of the source at a cut, with its row.
    record ValAt (N : ℕ) : Set where
      constructor valAt
      field
        q   : Pos
        a   : A
        row : TR (S N) q (out a)

    -- The values among some rows, each with its membership.
    valsIn : (rs : List (Row A)) → List (Σ Pos λ q → Σ A λ a → (q , out a) ∈ rs)
    valsIn []                 = []
    valsIn ((q , out a) ∷ rs) = (q , a , here refl) ∷ L.map (λ { (q′ , a′ , m) → q′ , a′ , there m }) (valsIn rs)
    valsIn (_ ∷ rs)           = L.map (λ { (q′ , a′ , m) → q′ , a′ , there m }) (valsIn rs)

    -- The source's values at a cut.
    valsAt : ∀ N → List (ValAt N)
    valsAt N with S N in eq
    ... | nothing = []
    ... | just Lo = L.map (λ { (q , a , m) → valAt q a (Lo , eq , m) }) (valsIn (rows Lo))

    -- A value's elaborated row: the shared hot's row of its image, read by
    -- the lanes' flatMap, and the value `each` lists from it.
    val* : ℕ → Pos → Pos
    val* N q = Rel.φ (Out.rel Os) N q ⊕ˡ (sub c₁ ∷ ix 1 ∷ ix 0 ∷ [])

    -- And its lane's subscription.
    st* : ℕ → Pos → Pos
    st* N q = val* N q ⊕ [ ix 1 ]

    -- `laneˢ`'s path from an elaborated lane's subscription to the lane.
    laneXs : Pos → List Label
    laneXs st = ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ sub (laneL st ⊕ˡ (ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ []

    -- A lane related at a cut: its value, its two subscriptions, its
    -- record.
    record LaneRec (N : ℕ) : Set₁ where
      constructor laneRec
      field
        a   : A
        st  : Pos
        stE : Pos
        lane : Out n (f a) ρ ρι⁴ (λ N′ → trig stE N′ ∷ ρ*c N′) (maps env) st (laneX stE)

      -- The lane's plain tables.
      tab : Maybe (Tb.Listed B)
      tab = Tab n (f a) ρ st N

      -- Its row's image as the lanes' flatMap shows it: read by
      -- `laneˢ`'s reader and emitted by `counted`; an end at its
      -- `laneDone`'s.
      outImage endImage : Pos → Pos
      outImage y = emitAt (Rel.φ (Out.rel lane) N y ⊕ [ sub (readerR stE) ])
      endImage y = emitAt (Rel.φ (Out.rel lane) N y ⊕ˡ (sub (readerR stE) ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ last ]

    -- A value's lane, subscribed under its row: the source's facts at the
    -- row align the lane's pair.
    valRec : ∀ N → ValAt N → LaneRec N
    valRec N (valAt q a x) = laneRec a (q ⊕ [ ix 1 ]) st (
      Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (q ⊕ [ ix 1 ]) (laneX st)
         (aligned-r* {Ψ = maps env} {ρ = ρ} (aligned-⊕ {Ψ = maps env} {ρ = ρ} (Rest.cuts (Out.rest Os) N x tt) (ix 1) (sub c₁)) ys)
         (linked-r* (linked-r (linked-l (Rest.linked (Out.rest Os) N x tt) (ix 1)) (sub c₁)) ys))
      where
        st = st* N q
        ys = ix 1 ∷ ix 0 ∷ ix 1 ∷ laneXs st

    -- A value's lane, queued under the end of the lane it waited on: that
    -- lane's facts at its end align the pair, the elaborated lane queued
    -- under the end's image.
    queuedRec : ∀ N (R : LaneRec N) {c} → TR (LaneRec.tab R) c end → A → LaneRec N
    queuedRec N R {c} cx a = laneRec a (c ⊕ [ ix 1 ]) st (
      Ls a (trig st) cl-tab sh-tab tt-tab (utrig st) (c ⊕ [ ix 1 ]) (laneX st)
         (aligned-r* {Ψ = maps env} {ρ = ρ} (aligned-⊕ {Ψ = maps env} {ρ = ρ} (Rest.cuts (Out.rest O) N cx tt) (ix 1) (sub r)) ys)
         (linked-r* (linked-r (linked-l (Rest.linked (Out.rest O) N cx tt) (ix 1)) (sub r)) ys))
      where
        O  = LaneRec.lane R
        r  = readerR (LaneRec.stE R)
        st = LaneRec.endImage R c ⊕ [ ix 1 ]
        ys = ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ last ∷ ix 1 ∷ laneXs st

    -- The deepest of some lanes holding `y`: a queued lane lies inside the
    -- lane it waited on.
    deepest : ∀ {N} → List (LaneRec N) → Pos → Maybe (LaneRec N)
    deepest []       y = nothing
    deepest (R ∷ Rs) y with deepest Rs y
    ... | just R′ = just R′
    ... | nothing = if inside (LaneRec.st R) y then just R else nothing

    -- The source's value at a row.
    valAtPos : ∀ N → Pos → Maybe (ValAt N)
    valAtPos N q = first (valsAt N)
      where
        first : List (ValAt N) → Maybe (ValAt N)
        first []       = nothing
        first (v ∷ vs) = if does (ValAt.q v ≟ᵖ q) then just v else first vs

    -- An end among some rows.
    endIn : ∀ {X : Set} (rs : List (Row X)) c → Maybe ((c , end) ∈ rs)
    endIn []               c = nothing
    endIn ((k , end) ∷ rs) c with k ≟ᵖ c
    ... | yes refl = just (here refl)
    ... | no _     = M.map there (endIn rs c)
    endIn (_ ∷ rs)         c = M.map there (endIn rs c)

    -- The lane among some that ends at `c`.
    waitedOn : ∀ {N} → List (LaneRec N) → ∀ c → Maybe (Σ (LaneRec N) λ R → TR (LaneRec.tab R) c end)
    waitedOn []       c = nothing
    waitedOn (R ∷ Rs) c with LaneRec.tab R in eq
    ... | nothing = waitedOn Rs c
    ... | just Lx with endIn (rows Lx) c
    ...   | just m  = just (R , Lx , eq , m)
    ...   | nothing = waitedOn Rs c

    -- The trigger's end, read by the share.
    ttEnd : Pos
    ttEnd = p* ⊕ˡ (ix 1 ∷ last ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ [])

    -- A source row's image, read through the shared hot.
    srcφ : ℕ → Pos → Pos
    srcφ N k = Rel.φ (Out.rel Os) N k ⊕ [ sub c₁ ]

    isMarker : ℕ → Pos → Bool
    isMarker N y = anyᵇ (λ v → does ((ValAt.q v ⊕ [ ix 0 ]) ≟ᵖ y)) (valsAt N)

    ups : ℕ → Pos → Pos
    ups zero    y = y
    ups (suc i) y = ups i (up y)

    -- THE MERGES' MAP, given each cut's lanes.  A lane row is imaged
    -- through its lane's record at the cut, the skip a queue leaves past a
    -- lane's end at its end image's; a value's marker at the marker of its
    -- elaborated value; the source's end at the later of its own and the
    -- trigger's, as the share ends; any other source row through the
    -- shared hot.
    module Tabs (lanes : ∀ N → List (LaneRec N)) where
      φ′ : ℕ → Pos → Pos
      φ′ N y with deepest (lanes N) y
      ... | just R  = if endAt (LaneRec.tab R) y then LaneRec.endImage R y
                      else if endAt (LaneRec.tab R) (up y) then LaneRec.endImage R (up y) ⊕ [ ix 0 ]
                      else LaneRec.outImage R y
      ... | nothing = if isMarker N y then val* N (up y) ⊕ [ ix 0 ]
                      else if endAt (S N) y then (if Rel.φ (Out.rel Os) N y <ᵖ ttEnd then ttEnd else Rel.φ (Out.rel Os) N y) ⊕ [ sub c₁ ]
                      else srcφ N y

      Put′ : ℕ → Pos → Pos → Set
      Put′ N y l with deepest (lanes N) y
      ... | just R  = Σ Pos λ l′ → Rel.Put (Out.rel (LaneRec.lane R)) N y l′ × l ≡ emitAt (l′ ⊕ [ sub (readerR (LaneRec.stE R)) ])
      ... | nothing = (Σ Pos λ l′ → Rel.Put (Out.rel Os) N y l′ × l ≡ l′ ⊕ [ sub c₁ ]) ⊎ l ≡ φ′ N y

      -- Generous: every lane's preimages of the image stripped each way,
      -- the source's of it stripped, the markers', and the source's ends.
      bk′ : ℕ → Pos → List Pos
      bk′ N l = L.concatMap (λ R → let Rl = Out.rel (LaneRec.lane R) in
                                     Rel.bk Rl N (ups 5 l) ++ Rel.bk Rl N (ups 8 l) ++ L.map (λ k → k ⊕ [ ix 0 ]) (Rel.bk Rl N (ups 9 l))) (lanes N)
             ++ Rel.bk (Out.rel Os) N (up l)
             ++ L.map (λ k → k ⊕ [ ix 0 ]) (Rel.bk (Out.rel Os) N (ups 5 l))
             ++ endsOf (S N)

    ----------------------------------------------------------------------
    -- THE PLAIN MERGE: every value's lane subscribed under its row, every
    -- lane row shown.
    module MergeTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = P (mergeᶠ nothing)
      Q′ = λ N → listC (3 + N) n (core (mergeᶠ nothing)) (ρ*c N) c₁

      open Tabs (λ N → L.map (valRec N) (valsAt N))

      postulate
        mg-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        mg-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
        mg-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
        mg-pb-few      : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
        mg-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        mg-put-up      : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
        mg-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
        mg-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        mg-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        mg-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                       → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
        mg-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (mg-corr N) k
                       → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        mg-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
        mg-func        : ∀ {N y e e′} → TR (P′ N) y e → TR (P′ N) y e′ → e ≡ e′
        mg-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
        mg-flat        : ∀ {N y e l ys e′} → TR (P′ N) y e → TR (P′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        mg-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        mg-pin-in      : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
        mg-pin-in*     : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
        mg-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        mg-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        mg-got         : ∀ N → Got (P′ N)
        mg-got*        : ∀ N → Got (Q′ N)
        mg-after       : ∀ {N k e} → TR (P′ N) k e → p ≼ k
        mg-after*      : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
        mg-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        mg-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
        mg-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = mg-corr ; φ-agree = mg-φ-agree ; bk = bk′ ; in-bk = mg-in-bk ; pb-few = mg-pb-few
        ; back = mg-back ; put-up = mg-put-up ; back-put = mg-back-put
        ; elab-causal = mg-elab-causal ; stable← = mg-stable← ; stable-put = mg-stable-put ; stable-lead = mg-stable-lead
        ; elab-all = mg-elab-all ; func = mg-func ; func* = mg-func* ; flat = mg-flat ; flat* = mg-flat*
        ; pin-in = mg-pin-in ; pin-in* = mg-pin-in* ; cons = mg-cons ; cons* = mg-cons* ; got = mg-got ; got* = mg-got*
        ; after = mg-after ; after* = mg-after* ; after-φ = mg-after-φ ; pin-after* = mg-pin-after* ; pin-stable = mg-pin-stable }

    ----------------------------------------------------------------------
    -- THE BOUNDED MERGE: a value's lane subscribed under its row when
    -- fewer than `k` lanes are live there, else queued under the end of
    -- the lane whose end frees its slot.  The queue's state is a run's,
    -- so the lanes are enumerated level by level as the listing
    -- subscribes them; a queued lane's record is had from the lane it
    -- waited on, at its end.
    module ConcatTab (k : ℕ) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = P (mergeᶠ (just k))
      Q′ = λ N → listC (3 + N) n (core (mergeᶠ (just k))) (ρ*c N) c₁

      -- The listing's entries at a cut: each value with its subscriptions.
      entriesAt : ∀ N → List (ℕ × Pos × A × List (Pos × Tb.Listed B))
      entriesAt N with S N
      ... | nothing = []
      ... | just o with BoundedL.levels k (afterL (λ a → listC (3 + N) n (f a) (ρ N))) o
                          (L.length (values (rows o))) 0 [] (Order.nths (values (rows o)) 0)
      ...   | nothing = []
      ...   | just gs = gs

      -- Each entry's lanes, after those of the levels before.
      recs : ∀ N → List (ℕ × Pos × A × List (Pos × Tb.Listed B)) → List (LaneRec N) → List (LaneRec N)
      recs N []                       acc = acc
      recs N ((_ , q , a , ss) ∷ es) acc = recs N es (acc ++ L.concatMap one ss)
        where
          one : Pos × Tb.Listed B → List (LaneRec N)
          one (st , _) = if does (st ≟ᵖ (q ⊕ [ ix 1 ]))
                         then maybe (λ v → [ valRec N v ]) [] (valAtPos N q)
                         else maybe (λ { (R , cx) → [ queuedRec N R cx a ] }) [] (waitedOn acc (up st))

      open Tabs (λ N → recs N (entriesAt N) [])

      postulate
        cc-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        cc-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
        cc-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
        cc-pb-few      : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
        cc-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        cc-put-up      : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
        cc-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
        cc-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        cc-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        cc-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                       → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
        cc-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (cc-corr N) k
                       → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        cc-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
        cc-func        : ∀ {N y e e′} → TR (P′ N) y e → TR (P′ N) y e′ → e ≡ e′
        cc-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
        cc-flat        : ∀ {N y e l ys e′} → TR (P′ N) y e → TR (P′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        cc-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        cc-pin-in      : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
        cc-pin-in*     : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
        cc-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        cc-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        cc-got         : ∀ N → Got (P′ N)
        cc-got*        : ∀ N → Got (Q′ N)
        cc-after       : ∀ {N k e} → TR (P′ N) k e → p ≼ k
        cc-after*      : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
        cc-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        cc-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
        cc-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = cc-corr ; φ-agree = cc-φ-agree ; bk = bk′ ; in-bk = cc-in-bk ; pb-few = cc-pb-few
        ; back = cc-back ; put-up = cc-put-up ; back-put = cc-back-put
        ; elab-causal = cc-elab-causal ; stable← = cc-stable← ; stable-put = cc-stable-put ; stable-lead = cc-stable-lead
        ; elab-all = cc-elab-all ; func = cc-func ; func* = cc-func* ; flat = cc-flat ; flat* = cc-flat*
        ; pin-in = cc-pin-in ; pin-in* = cc-pin-in* ; cons = cc-cons ; cons* = cc-cons* ; got = cc-got ; got* = cc-got*
        ; after = cc-after ; after* = cc-after* ; after-φ = cc-after-φ ; pin-after* = cc-pin-after* ; pin-stable = cc-pin-stable }

  postulate
    -- Every value's lane is subscribed under its row, and a lane's rows
    -- are shown only before the next value's row: the cut is the source's
    -- row, aligned by the source's facts at both rows.
    flat-switch : Core switchᶠ

    -- Every value's lane is subscribed under its row and shown only when
    -- no earlier shown lane is live at that row: whether one is live is
    -- read off the lanes' ends, aligned by the lanes' own records.
    flat-exhaust : Core exhaustᶠ

  flat-core : ∀ op → Core op
  flat-core (mergeᶠ nothing)  = λ Os Ls al lk → Parts.MergeTab.rel′ Os Ls al lk
  flat-core (mergeᶠ (just k)) = λ Os Ls al lk → Parts.ConcatTab.rel′ Os Ls k al lk
  flat-core switchᶠ           = flat-switch
  flat-core exhaustᶠ          = flat-exhaust

  postulate
    -- THE COMBINED SCAN: the lanes' flatMap read through its hot by the
    -- scan over its routes and the trackers', each value re-emitted in
    -- place with its marks.
    flat-comb : ∀ op → Rel (P op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁
              → Rel (P op) (λ N → listC (3 + N) n (inner op) (ρ*c N) c₂) p c₂

    -- THE CLOSER: the combined run past the closer's subscription, the
    -- closer's marks unshown and in the instants of the source's ends.
    flat-close : ∀ op → Rel (P op) (λ N → listC (3 + N) n (inner op) (ρ*c N) c₂) p c₂
               → Rel (P op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃

    -- THE SHARE: the body read past the share's two connects; the
    -- trigger's and the shared hot's own rows are never shown.
    flat-share : ∀ op → Rel (P op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃
               → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*

  flat-tab : ∀ op → Src → Lanes → Aligned (maps env) ρ p p* → Linked p p* → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*
  flat-tab op Os Ls al lk = flat-share op (flat-close op (flat-comb op (flat-core op Os Ls al lk)))

  postulate
    -- THE FLATMAP'S ORDER FACTS: each row is a source row or a lane row
    -- at its own position, imaged along its stream's map, so each fact is
    -- the source's or the lane's; a lane's subscription is past every
    -- earlier pair that cuts the flatMap alike.
    flatmap-order : ∀ op (Os : Src) (Ls : Lanes) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) → Rest (maps env) ρ (flat-tab op Os Ls al lk)

flat-rel : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
         → Full n s → (∀ a → Full n (f a)) → Full n (flatMap op f s)
flat-rel n op f s Fs Ff ρ uρ ρι ρ* uρ* env p p* al lk = F.flat-tab op Os Ls al lk ⊢ F.flatmap-order op Os Ls al lk
  where
    module F = Flat n f s ρ uρ ρι ρ* uρ* env p p*

    path : List Label
    path = ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ []

    Os : F.Src
    Os = Fs ρ uρ (wk ρι) F.ρ*s F.uρ*s (env-wk F.tt-tab env) p F.sp*
           (aligned-r* {Ψ = maps env} {ρ = ρ} al path) (linked-r* lk path)

    Ls : F.Lanes
    Ls a t₁ t₂ t₃ t₄ u = Ff a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk t₁ (env-wk t₂ (env-wk t₃ (env-wk t₄ env))))
