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

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe as M
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does; yes; no)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; of; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; _<ᵖ_; ix; sub; last; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Unpinned; out; end; pin; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ≼-refl; ≼-trans; ≺→≼; ≺-ext)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled.Exact.Base using (any⁻)
open import quickcheck.Tabled using (hotOf; Row; rows; ends; anyᵇ; values; afterL; module BoundedL; module ExhaustL; module Order)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.TableCorr using (Rel; TR; Corr; Cons; Got)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv using (Ren; wk; got-ok; pin-ok; after-ok; Tab; Tab*; up; up-⊕; _⊕ˡ_; Linked; linked-l; linked-r; linked-r*; Aligned; aligned-⊕; aligned-r*; Rest; Out; _⊢_; EnvR; maps; env-wk; Holds; Full)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

private
  ≟-true : ∀ x y → does (x ≟ᵖ y) ≡ true → x ≡ y
  ≟-true x y with x ≟ᵖ y
  ... | yes e = λ _ → e
  ... | no _  = λ ()

  -- A position some row of a list equals is in it.
  any-≟ : ∀ {xs k} → anyᵇ (λ k′ → does (k′ ≟ᵖ k)) xs ≡ true → k ∈ xs
  any-≟ {k = k} h with any⁻ h
  ... | k′ , k′∈ , hk with ≟-true k′ k hk
  ...   | refl = k′∈

  in-if : ∀ (b : Bool) {X : Set} (Q : X → Set) {x y} → (b ≡ true → Q x) → (b ≡ false → Q y) → Q (if b then x else y)
  in-if true  Q t e = t refl
  in-if false Q t e = e refl

  ≼-ˡ : ∀ x ys → x ≼ (x ⊕ˡ ys)
  ≼-ˡ x []       = ≼-refl {x}
  ≼-ˡ x (l ∷ ls) = ≼-trans {x} {x ⊕ [ l ]} {(x ⊕ [ l ]) ⊕ˡ ls} (≺→≼ {x} {x ⊕ [ l ]} (≺-ext x [])) (≼-ˡ (x ⊕ [ l ]) ls)

  -- The latest of some positions and a floor lies past the floor.
  max-ge : ∀ b xs → b ≼ L.foldr (λ x y → if x <ᵖ y then y else x) b xs
  max-ge b []       = ≼-refl {b}
  max-ge b (x ∷ xs) = in-if (x <ᵖ r) (λ v → b ≼ v) (λ _ → max-ge b xs)
                        (λ eq → ≼-trans {b} {r} {x} (max-ge b xs) (λ h → subst T eq h))
    where r = L.foldr (λ x y → if x <ᵖ y then y else x) b xs

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

  uρ*c : ∀ N → UncutEnv (ρ*c N)
  uρ*c N = proj₂ (proj₂ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ]))) , uρ*h N

  -- A table's ends.
  endsOf : ∀ {X : Set} → Maybe (Tb.Listed X) → List Pos
  endsOf nothing   = []
  endsOf (just Lx) = ends (rows Lx)

  endAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
  endAt m y = anyᵇ (λ k → does (k ≟ᵖ y)) (endsOf m)

  rowAt : ∀ {X : Set} → Maybe (Tb.Listed X) → Pos → Bool
  rowAt nothing   y = false
  rowAt (just Lx) y = anyᵇ (λ r → does (proj₁ r ≟ᵖ y)) (rows Lx)

  ups : ℕ → Pos → Pos
  ups zero    y = y
  ups (suc i) y = ups i (up y)

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

    -- A lane's trigger, under its subscription.
    trig : Pos → ℕ → Tb.Listed ⊤
    trig st N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ])))

    utrig : ∀ st N → UncutEnv (trig st N ∷ ρ*c N)
    utrig st N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) {ρ*c N} (uρ*c N) (laneL st ⊕ [ ix 1 ]))) , uρ*c N

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

    -- The last of some lanes that `h` picks: a queued lane is listed after
    -- the lane it waited on.
    lastWith : ∀ {N} → (LaneRec N → Bool) → List (LaneRec N) → Maybe (LaneRec N)
    lastWith h []       = nothing
    lastWith h (R ∷ Rs) with lastWith h Rs
    ... | just R′ = just R′
    ... | nothing = if h R then just R else nothing

    -- The lane whose table holds a row at `y`: a lane's row need not lie
    -- under its subscription, read off a hot or in a cascade its timer
    -- made.
    holder : ∀ {N} → List (LaneRec N) → Pos → Maybe (LaneRec N)
    holder Rs y = lastWith (λ R → rowAt (LaneRec.tab R) y) Rs

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

    -- THE MERGES' MAP, given each cut's lanes.  A lane row is imaged
    -- through its lane's record at the cut, the skip a queue leaves past a
    -- lane's end at its end image's; a value's marker at the marker of its
    -- elaborated value; the source's end at the later of its own and the
    -- trigger's, as the share ends; any other source row through the
    -- shared hot.
    module Tabs (lanes : ∀ N → List (LaneRec N)) where
      φ′ : ℕ → Pos → Pos
      φ′ N y = rowφ (holder (lanes N) y) (lastWith (λ R → endAt (LaneRec.tab R) (up y)) (lanes N))
        where
          rowφ : Maybe (LaneRec N) → Maybe (LaneRec N) → Pos
          rowφ (just R) _        = if endAt (LaneRec.tab R) y then LaneRec.endImage R y else LaneRec.outImage R y
          rowφ nothing  (just R) = LaneRec.endImage R (up y) ⊕ [ ix 0 ]
          rowφ nothing  nothing  = if isMarker N y then val* N (up y) ⊕ [ ix 0 ]
                                   else if endAt (S N) y then (if Rel.φ (Out.rel Os) N y <ᵖ ttEnd then ttEnd else Rel.φ (Out.rel Os) N y) ⊕ [ sub c₁ ]
                                   else srcφ N y

      Put′ : ℕ → Pos → Pos → Set
      Put′ N y l with holder (lanes N) y
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
        mg-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        mg-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        mg-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        mg-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
        mg-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      mg-got : ∀ N → Got (P′ N)
      mg-got N = got-ok (3 + N) n (flatMap (mergeᶠ nothing) f s) {ρ N} (uρ N) p

      mg-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      mg-pin-in {N} = pin-ok (3 + N) n (flatMap (mergeᶠ nothing) f s) {ρ N} p

      mg-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      mg-after {N} = after-ok (3 + N) n (flatMap (mergeᶠ nothing) f s) {ρ N} p

      mg-got* : ∀ N → Got (Q′ N)
      mg-got* N = got-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} (uρ*c N) c₁

      mg-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      mg-pin-in* {N} = pin-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} c₁

      mg-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      mg-after* {N} = after-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} c₁

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
        cc-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        cc-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        cc-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        cc-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
        cc-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      cc-got : ∀ N → Got (P′ N)
      cc-got N = got-ok (3 + N) n (flatMap (mergeᶠ (just k)) f s) {ρ N} (uρ N) p

      cc-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      cc-pin-in {N} = pin-ok (3 + N) n (flatMap (mergeᶠ (just k)) f s) {ρ N} p

      cc-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      cc-after {N} = after-ok (3 + N) n (flatMap (mergeᶠ (just k)) f s) {ρ N} p

      cc-got* : ∀ N → Got (Q′ N)
      cc-got* N = got-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} (uρ*c N) c₁

      cc-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      cc-pin-in* {N} = pin-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} c₁

      cc-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      cc-after* {N} = after-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = cc-corr ; φ-agree = cc-φ-agree ; bk = bk′ ; in-bk = cc-in-bk ; pb-few = cc-pb-few
        ; back = cc-back ; put-up = cc-put-up ; back-put = cc-back-put
        ; elab-causal = cc-elab-causal ; stable← = cc-stable← ; stable-put = cc-stable-put ; stable-lead = cc-stable-lead
        ; elab-all = cc-elab-all ; func = cc-func ; func* = cc-func* ; flat = cc-flat ; flat* = cc-flat*
        ; pin-in = cc-pin-in ; pin-in* = cc-pin-in* ; cons = cc-cons ; cons* = cc-cons* ; got = cc-got ; got* = cc-got*
        ; after = cc-after ; after* = cc-after* ; after-φ = cc-after-φ ; pin-after* = cc-pin-after* ; pin-stable = cc-pin-stable }

    ----------------------------------------------------------------------
    -- THE SWITCH: every value's lane subscribed under its row, its rows
    -- shown only before the next value's row; the map is the merge's.
    module SwitchTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = P (switchᶠ)
      Q′ = λ N → listC (3 + N) n (core (switchᶠ)) (ρ*c N) c₁

      open Tabs (λ N → L.map (valRec N) (valsAt N))

      postulate
        sw-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        sw-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
        sw-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
        sw-pb-few      : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
        sw-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        sw-put-up      : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
        sw-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
        sw-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        sw-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        sw-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                       → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
        sw-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (sw-corr N) k
                       → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        sw-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
        sw-func        : ∀ {N y e e′} → TR (P′ N) y e → TR (P′ N) y e′ → e ≡ e′
        sw-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
        sw-flat        : ∀ {N y e l ys e′} → TR (P′ N) y e → TR (P′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        sw-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        sw-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        sw-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        sw-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        sw-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
        sw-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      sw-got : ∀ N → Got (P′ N)
      sw-got N = got-ok (3 + N) n (flatMap switchᶠ f s) {ρ N} (uρ N) p

      sw-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      sw-pin-in {N} = pin-ok (3 + N) n (flatMap switchᶠ f s) {ρ N} p

      sw-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      sw-after {N} = after-ok (3 + N) n (flatMap switchᶠ f s) {ρ N} p

      sw-got* : ∀ N → Got (Q′ N)
      sw-got* N = got-ok (3 + N) n (core switchᶠ) {ρ*c N} (uρ*c N) c₁

      sw-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      sw-pin-in* {N} = pin-ok (3 + N) n (core switchᶠ) {ρ*c N} c₁

      sw-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      sw-after* {N} = after-ok (3 + N) n (core switchᶠ) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = sw-corr ; φ-agree = sw-φ-agree ; bk = bk′ ; in-bk = sw-in-bk ; pb-few = sw-pb-few
        ; back = sw-back ; put-up = sw-put-up ; back-put = sw-back-put
        ; elab-causal = sw-elab-causal ; stable← = sw-stable← ; stable-put = sw-stable-put ; stable-lead = sw-stable-lead
        ; elab-all = sw-elab-all ; func = sw-func ; func* = sw-func* ; flat = sw-flat ; flat* = sw-flat*
        ; pin-in = sw-pin-in ; pin-in* = sw-pin-in* ; cons = sw-cons ; cons* = sw-cons* ; got = sw-got ; got* = sw-got*
        ; after = sw-after ; after* = sw-after* ; after-φ = sw-after-φ ; pin-after* = sw-pin-after* ; pin-stable = sw-pin-stable }

    ----------------------------------------------------------------------
    -- THE EXHAUST: the lanes the plain exhaust runs, each subscribed under
    -- its value's row; the map is the merge's over those lanes.
    module ExhaustTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = P (exhaustᶠ)
      Q′ = λ N → listC (3 + N) n (core (exhaustᶠ)) (ρ*c N) c₁

      -- The values whose lane the plain exhaust runs.
      ranAt : ℕ → List Pos
      ranAt N with S N
      ... | nothing = []
      ... | just o with Tb.lanes (afterL (λ a → listC (3 + N) n (f a) (ρ N))) (values (rows o))
      ...   | nothing = []
      ...   | just ls = ExhaustL.runs o ls

      open Tabs (λ N → L.concatMap (λ v → if anyᵇ (λ q → does (q ≟ᵖ ValAt.q v)) (ranAt N) then [ valRec N v ] else []) (valsAt N))

      postulate
        ex-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        ex-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
        ex-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
        ex-pb-few      : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
        ex-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        ex-put-up      : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
        ex-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
        ex-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        ex-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                       → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
        ex-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                       → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
        ex-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (ex-corr N) k
                       → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
        ex-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
        ex-func        : ∀ {N y e e′} → TR (P′ N) y e → TR (P′ N) y e′ → e ≡ e′
        ex-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
        ex-flat        : ∀ {N y e l ys e′} → TR (P′ N) y e → TR (P′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        ex-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
        ex-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        ex-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        ex-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        ex-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
        ex-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      ex-got : ∀ N → Got (P′ N)
      ex-got N = got-ok (3 + N) n (flatMap exhaustᶠ f s) {ρ N} (uρ N) p

      ex-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      ex-pin-in {N} = pin-ok (3 + N) n (flatMap exhaustᶠ f s) {ρ N} p

      ex-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      ex-after {N} = after-ok (3 + N) n (flatMap exhaustᶠ f s) {ρ N} p

      ex-got* : ∀ N → Got (Q′ N)
      ex-got* N = got-ok (3 + N) n (core exhaustᶠ) {ρ*c N} (uρ*c N) c₁

      ex-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      ex-pin-in* {N} = pin-ok (3 + N) n (core exhaustᶠ) {ρ*c N} c₁

      ex-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      ex-after* {N} = after-ok (3 + N) n (core exhaustᶠ) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = ex-corr ; φ-agree = ex-φ-agree ; bk = bk′ ; in-bk = ex-in-bk ; pb-few = ex-pb-few
        ; back = ex-back ; put-up = ex-put-up ; back-put = ex-back-put
        ; elab-causal = ex-elab-causal ; stable← = ex-stable← ; stable-put = ex-stable-put ; stable-lead = ex-stable-lead
        ; elab-all = ex-elab-all ; func = ex-func ; func* = ex-func* ; flat = ex-flat ; flat* = ex-flat*
        ; pin-in = ex-pin-in ; pin-in* = ex-pin-in* ; cons = ex-cons ; cons* = ex-cons* ; got = ex-got ; got* = ex-got*
        ; after = ex-after ; after* = ex-after* ; after-φ = ex-after-φ ; pin-after* = ex-pin-after* ; pin-stable = ex-pin-stable }

  flat-core : ∀ op → Core op
  flat-core (mergeᶠ nothing)  = λ Os Ls al lk → Parts.MergeTab.rel′ Os Ls al lk
  flat-core (mergeᶠ (just k)) = λ Os Ls al lk → Parts.ConcatTab.rel′ Os Ls k al lk
  flat-core switchᶠ           = λ Os Ls al lk → Parts.SwitchTab.rel′ Os Ls al lk
  flat-core exhaustᶠ          = λ Os Ls al lk → Parts.ExhaustTab.rel′ Os Ls al lk

  ----------------------------------------------------------------------
  -- THE COMBINED SCAN: each row of the lanes' flatMap read by the scan's
  -- lane branch and re-emitted by `each` as it is, the scan's other emits
  -- all marks; the flatMap's end at the `nothing` the scan's concat sends
  -- past the last of its three branches' ends.
  module CombTab (op : FlatOp) (R : Rel (P op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁) where
    P′ Q′ : ℕ → _
    P′ = P op
    Q′ = λ N → listC (3 + N) n (inner op) (ρ*c N) c₂

    -- The scan's three branches, under its concat's first lane: the
    -- outer, the lanes and the closer, each read at `rB`.
    cA : Pos
    cA = c₂ ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

    rB : ℕ → Pos
    rB i = cA ⊕ˡ (ix i ∷ ix 1 ∷ [])

    readEnd : Pos → List Pos → List Pos
    readEnd r = L.map (λ e → if r <ᵖ e then e ⊕ [ sub r ] else r ⊕ [ last ])

    core-hot : ℕ → Tb.Listed (IE B)
    core-hot N = hotOf (proj₁ (listC-ok (3 + N) n (core op) {ρ*c N} (uρ*c N) c₁))

    -- The last of the branches' ends, as the merge over them ends.
    aEnds : ℕ → List Pos
    aEnds N = readEnd (rB 0) (ends (rows (sh-tab N))) ++ readEnd (rB 1) (ends (rows (core-hot N)))
              ++ readEnd (rB 2) (ends (rows (cl-tab N)))

    aEnd : ℕ → Pos
    aEnd N = L.foldr (λ x y → if x <ᵖ y then y else x) (cA ⊕ [ last ]) (aEnds N)

    reEmit : Pos → Pos
    reEmit l = l ⊕ˡ (sub (rB 1) ∷ ix 1 ∷ ix 0 ∷ [])

    φ′ : ℕ → Pos → Pos
    φ′ N k = if endAt (P′ N) k then aEnd N ⊕ˡ (ix 1 ∷ ix 0 ∷ last ∷ []) else reEmit (Rel.φ R N k)

    Put′ : ℕ → Pos → Pos → Set
    Put′ N k l = Σ Pos λ l′ → Rel.Put R N k l′ × l ≡ reEmit l′

    bk′ : ℕ → Pos → List Pos
    bk′ N l = Rel.bk R N (ups 3 l) ++ endsOf (P′ N)

    postulate
      cb-corr        : ∀ N → Corr p c₂ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
      cb-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
      cb-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                     → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cb-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
      cb-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cb-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cb-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      cb-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (cb-corr N) k
                     → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cb-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      cb-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
      cb-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
      cb-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
      cb-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₂ ≼ r
      cb-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

    -- Three labels up undo the re-emit.
    ups-re : ∀ l → ups 3 (reEmit l) ≡ l
    ups-re l = trans (cong (ups 2) (up-⊕ _ _)) (trans (cong (ups 1) (up-⊕ _ _)) (up-⊕ _ _))

    -- A put's preimages are the lanes' flatMap's at the image re-emitted.
    cb-pb-few : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
    cb-pb-few N l = proj₁ (Rel.pb-few R N (ups 3 l))
                  , λ P → proj₂ (Rel.pb-few R N (ups 3 l))
                            (subst (Rel.Put R N _) (trans (sym (ups-re (proj₁ P))) (cong (ups 3) (sym (proj₂ (proj₂ P))))) (proj₁ (proj₂ P)))

    -- A value's preimage is listed at its re-emit, an end among the ends.
    cb-in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
    cb-in-bk {N} {k} x u = in-if (endAt (P′ N) k) (λ l → k ∈ bk′ N l)
      (λ eq → ∈-++⁺ʳ (Rel.bk R N _) (any-≟ eq))
      (λ _ → ∈-++⁺ˡ (subst (λ y → k ∈ Rel.bk R N y) (sym (ups-re (Rel.φ R N k))) (Rel.in-bk R x u)))

    -- A put is the lanes' flatMap's, re-emitted.
    cb-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₂ ≼ φ′ N k
    cb-after-φ {N} {k} x u = in-if (endAt (P′ N) k) (λ l → c₂ ≼ l)
      (λ _ → ≼-trans {c₂} {aEnd N} {aEnd N ⊕ˡ (ix 1 ∷ ix 0 ∷ last ∷ [])}
               (≼-trans {c₂} {cA ⊕ [ last ]} {aEnd N} (≼-ˡ c₂ (ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])) (max-ge (cA ⊕ [ last ]) (aEnds N)))
               (≼-ˡ (aEnd N) (ix 1 ∷ ix 0 ∷ last ∷ [])))
      (λ _ → ≼-trans {c₂} {c₁} {reEmit (Rel.φ R N k)} (≺→≼ {c₂} {c₁} (≺-ext c₂ []))
               (≼-trans {c₁} {Rel.φ R N k} {reEmit (Rel.φ R N k)} (Rel.after-φ R x u) (≼-ˡ (Rel.φ R N k) (sub (rB 1) ∷ ix 1 ∷ ix 0 ∷ []))))

    cb-put-up : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
    cb-put-up le ag (l′ , pt , eq) = l′ , Rel.put-up R le ag pt , eq

    cb-got* : ∀ N → Got (Q′ N)
    cb-got* N = got-ok (3 + N) n (inner op) {ρ*c N} (uρ*c N) c₂

    cb-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    cb-pin-in* {N} = pin-ok (3 + N) n (inner op) {ρ*c N} c₂

    cb-after* : ∀ {N l e} → TR (Q′ N) l e → c₂ ≼ l
    cb-after* {N} = after-ok (3 + N) n (inner op) {ρ*c N} c₂

    rel′ : Rel P′ Q′ p c₂
    rel′ = record
      { φ = φ′ ; Put = Put′ ; corr = cb-corr ; φ-agree = cb-φ-agree ; bk = bk′ ; in-bk = cb-in-bk ; pb-few = cb-pb-few
      ; back = cb-back ; put-up = cb-put-up ; back-put = cb-back-put
      ; elab-causal = cb-elab-causal ; stable← = cb-stable← ; stable-put = cb-stable-put ; stable-lead = cb-stable-lead
      ; elab-all = cb-elab-all ; func = Rel.func R ; func* = cb-func* ; flat = Rel.flat R ; flat* = cb-flat*
      ; pin-in = Rel.pin-in R ; pin-in* = cb-pin-in* ; cons = Rel.cons R ; cons* = cb-cons* ; got = Rel.got R ; got* = cb-got*
      ; after = Rel.after R ; after* = cb-after* ; after-φ = cb-after-φ ; pin-after* = cb-pin-after* ; pin-stable = cb-pin-stable }

  ----------------------------------------------------------------------
  -- THE CLOSER: the combined run is the closer's connect's body, its rows
  -- shown as they are; the closer, that connect's source, shows only
  -- pins and skips.
  module CloseTab (op : FlatOp) (R : Rel (P op) (λ N → listC (3 + N) n (inner op) (ρ*c N) c₂) p c₂) where
    P′ Q′ : ℕ → _
    P′ = P op
    Q′ = λ N → listC (3 + N) n (body op) (ρ*h N) c₃

    φ′ : ℕ → Pos → Pos
    φ′ = Rel.φ R

    Put′ : ℕ → Pos → Pos → Set
    Put′ = Rel.Put R

    bk′ : ℕ → Pos → List Pos
    bk′ = Rel.bk R

    postulate
      cz-corr        : ∀ N → Corr p c₃ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
      cz-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                     → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cz-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
      cz-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cz-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cz-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      cz-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (cz-corr N) k
                     → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cz-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      cz-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
      cz-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
      cz-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
      cz-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → c₃ ≼ r
      cz-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

    cz-got* : ∀ N → Got (Q′ N)
    cz-got* N = got-ok (3 + N) n (body op) {ρ*h N} (uρ*h N) c₃

    cz-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    cz-pin-in* {N} = pin-ok (3 + N) n (body op) {ρ*h N} c₃

    -- The body's images lie past the closer's body, one label up.
    cz-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₃ ≼ φ′ N k
    cz-after-φ {N} {k} x u = ≼-trans {c₃} {c₂} {φ′ N k} (≼-ˡ c₃ (ix 0 ∷ [])) (Rel.after-φ R x u)

    cz-after* : ∀ {N l e} → TR (Q′ N) l e → c₃ ≼ l
    cz-after* {N} = after-ok (3 + N) n (body op) {ρ*h N} c₃

    rel′ : Rel P′ Q′ p c₃
    rel′ = record
      { φ = φ′ ; Put = Put′ ; corr = cz-corr ; φ-agree = Rel.φ-agree R ; bk = bk′ ; in-bk = Rel.in-bk R ; pb-few = Rel.pb-few R
      ; back = cz-back ; put-up = Rel.put-up R ; back-put = cz-back-put
      ; elab-causal = cz-elab-causal ; stable← = cz-stable← ; stable-put = cz-stable-put ; stable-lead = cz-stable-lead
      ; elab-all = cz-elab-all ; func = Rel.func R ; func* = cz-func* ; flat = Rel.flat R ; flat* = cz-flat*
      ; pin-in = Rel.pin-in R ; pin-in* = cz-pin-in* ; cons = Rel.cons R ; cons* = cz-cons* ; got = Rel.got R ; got* = cz-got*
      ; after = Rel.after R ; after* = cz-after* ; after-φ = cz-after-φ ; pin-after* = cz-pin-after* ; pin-stable = cz-pin-stable }

  ----------------------------------------------------------------------
  -- THE SHARE: the body is the share's two connects' body, its rows shown
  -- as they are; the trigger's and the shared hot's are pins.
  module ShareTab (op : FlatOp) (R : Rel (P op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃) where
    P′ Q′ : ℕ → _
    P′ = P op
    Q′ = Tab* n ρι (flatMap op f s) ρ* p*

    φ′ : ℕ → Pos → Pos
    φ′ = Rel.φ R

    Put′ : ℕ → Pos → Pos → Set
    Put′ = Rel.Put R

    bk′ : ℕ → Pos → List Pos
    bk′ = Rel.bk R

    postulate
      sr-corr        : ∀ N → Corr p p* (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
      sr-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                     → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      sr-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
      sr-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      sr-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      sr-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      sr-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (sr-corr N) k
                     → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      sr-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      sr-func*       : ∀ {N y e e′} → TR (Q′ N) y e → TR (Q′ N) y e′ → e ≡ e′
      sr-flat*       : ∀ {N y e l ys e′} → TR (Q′ N) y e → TR (Q′ N) (y ⊕ (l ∷ ys)) e′ → ⊥
      sr-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
      sr-pin-after*  : ∀ {N l r} → TR (Q′ N) l (pin r) → p* ≼ r
      sr-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

    sr-got* : ∀ N → Got (Q′ N)
    sr-got* N = got-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} (uρ* N) p*

    sr-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    sr-pin-in* {N} = pin-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} p*

    -- The closer's images lie past the share, two labels up.
    sr-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → p* ≼ φ′ N k
    sr-after-φ {N} {k} x u = ≼-trans {p*} {c₃} {φ′ N k} (≼-ˡ p* (ix 0 ∷ ix 0 ∷ [])) (Rel.after-φ R x u)

    sr-after* : ∀ {N l e} → TR (Q′ N) l e → p* ≼ l
    sr-after* {N} = after-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} p*

    rel′ : Rel P′ Q′ p p*
    rel′ = record
      { φ = φ′ ; Put = Put′ ; corr = sr-corr ; φ-agree = Rel.φ-agree R ; bk = bk′ ; in-bk = Rel.in-bk R ; pb-few = Rel.pb-few R
      ; back = sr-back ; put-up = Rel.put-up R ; back-put = sr-back-put
      ; elab-causal = sr-elab-causal ; stable← = sr-stable← ; stable-put = sr-stable-put ; stable-lead = sr-stable-lead
      ; elab-all = sr-elab-all ; func = Rel.func R ; func* = sr-func* ; flat = Rel.flat R ; flat* = sr-flat*
      ; pin-in = Rel.pin-in R ; pin-in* = sr-pin-in* ; cons = Rel.cons R ; cons* = sr-cons* ; got = Rel.got R ; got* = sr-got*
      ; after = Rel.after R ; after* = sr-after* ; after-φ = sr-after-φ ; pin-after* = sr-pin-after* ; pin-stable = sr-pin-stable }

  flat-tab : ∀ op → Src → Lanes → Aligned (maps env) ρ p p* → Linked p p* → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*
  flat-tab op Os Ls al lk = ShareTab.rel′ op (CloseTab.rel′ op (CombTab.rel′ op (flat-core op Os Ls al lk)))

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
