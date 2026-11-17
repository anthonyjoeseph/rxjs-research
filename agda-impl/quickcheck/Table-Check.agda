{-# OPTIONS --guardedness #-}

-- THE TABLES, PROBED: does the plain program's table correspond to its
-- elaboration's, subterm by subterm, as `simultaneous.TableRel.rel`
-- relates them?  Each generated program is walked down its tree, each
-- subterm listed twice (`listC`): plain, and elaborated at the position
-- and in the environment the relation pairs it with.
--
-- The map is read off the tables: the plain visible rows (values and
-- ends), in position order, onto the elaborated rows that show a value
-- and the ends, in position order.  A hot's map onto its elaborated hot
-- is its source's map rejoined under the annotation's reader, as the
-- connect's record states it.
--
-- Checked at every subterm, over its visible rows: the counts agree;
-- the map keeps order, instants and the subscription's instant (`Corr`'s
-- `mono`, `inst`, `home`); every row is linked to its image (`Rest`'s
-- `linked`); every hot's rows cut the subscriptions alike along its map
-- (`Aligned`, `Rest`'s `cuts`); the rows cut alike just under each row
-- and its image (`Rest`'s `self`).  At a connect, every hot row's image
-- is a row of the annotated hot.  Skip rows have no map read off the
-- tables, so the alike cuts are checked on visible rows only; `seen` is
-- not checked.
--
-- A flatMap's lanes are walked at every value, the plain lane under its
-- start and the elaborated lane where `laneˢ` subscribes it under the
-- lanes' flatMap's start; a bounded merge's starts are its levels'.
-- The lanes' flatMap's own table (`flat-core`'s) is checked against the
-- map written out: a lane row under `laneˢ`'s reader and `counted`'s
-- emit, a lane's end at its `laneDone`'s, a source row under the shared
-- hot's reader.
-- A probe for `make table-check`: no proof reads it.
module quickcheck.Table-Check where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using () renaming (⊤ to Unit)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; upTo; length; null) renaming (map to mapL)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _+++_)
open import Data.String.Properties using (_==_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (_>>=_; return)
open import IO.Primitive.Finite using (putStrLn)
open import IO.Primitive.Handle using (hSetBuffering; stdout; lineBuffering)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (does)

open import Tree using (Obs; Later; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected;
  defer)
open import denotation.Position using (Pos; Instant; frame; cascade; root; ix; sub; last; _⊕_; _≟ᵖ_; _≟ⁱ_; _≟ˡ_; _<ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.Readings using (instantOf)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; ext; module Elaborate)
open import simultaneous.Listing using (listC)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Ty using (natᵗ; showPos)
open import quickcheck.Tabled using (Row; Listed; _⊣_; rows; short; sort; hotOf; values; afterL; module BoundedL; module Order;
  concatMap; when; anyᵇ)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate; each; laneˢ; closer)

------------------------------------------------------------------------
-- Visible rows, and the map read off them

data Vis : Set where
  vout vend : Vis

private
  isOut : Vis → Bool
  isOut vout = true
  isOut vend = false

  visP : ∀ {A} → Row A → List (Pos × Vis)
  visP (q , out _) = [ q , vout ]
  visP (q , end)   = [ q , vend ]
  visP _           = []

  visE : ∀ {A} → Row (IE A) → List (Pos × Vis)
  visE (q , out x) = if null (valuesOf x) then [] else [ q , vout ]
  visE (q , end)   = [ q , vend ]
  visE _           = []

  -- A table's visible rows, nothing when cut short.
  plainV : ∀ {A} → Maybe (Listed A) → Maybe (List (Pos × Vis))
  plainV nothing  = nothing
  plainV (just l) = if short l then nothing else just (concatMap visP (sort (rows l)))

  elabV : ∀ {A} → Maybe (Listed (IE A)) → Maybe (List (Pos × Vis))
  elabV nothing  = nothing
  elabV (just l) = if short l then nothing else just (concatMap visE (sort (rows l)))

  ofKind : Bool → List (Pos × Vis) → List Pos
  ofKind b = concatMap λ { (q , v) → when (isOut v ∧ b ∨ not (isOut v) ∧ not b) q }

  pairUp : List Pos → List Pos → Maybe (List (Pos × Pos))
  pairUp []       []         = just []
  pairUp (a ∷ as) (b ∷ bs) with pairUp as bs
  ... | nothing = nothing
  ... | just r  = just ((a , b) ∷ r)
  pairUp _        _          = nothing

  pairing : List (Pos × Vis) → List (Pos × Vis) → Maybe (List (Pos × Pos))
  pairing ks ks* with pairUp (ofKind true ks) (ofKind true ks*) | pairUp (ofKind false ks) (ofKind false ks*)
  ... | just m | just m′ = just (m ++ m′)
  ... | _      | _       = nothing

  phi : List (Pos × Pos) → Pos → Pos
  phi []            k = k
  phi ((a , b) ∷ m) k = if does (a ≟ᵖ k) then b else phi m k

------------------------------------------------------------------------
-- Linked instants, alike cuts

private
  eqᵇ : Bool → Bool → Bool
  eqᵇ a b = (a ∧ b) ∨ (not a ∧ not b)

  _==ⁱ_ : Instant → Instant → Bool
  i ==ⁱ j = does (i ≟ⁱ j)

  inst : Pos → Instant
  inst = instantOf

  lvl : Pos → Pos → Pos → Pos → Bool
  lvl q q* y y* = eqᵇ (q <ᵖ y) (q* <ᵖ y*) ∧ eqᵇ (inst y ==ⁱ inst q) (inst y* ==ⁱ inst q*)
                ∧ not (inside q y) ∧ not (inside q* y*)

  cutᵇ : ℕ → Pos → Pos → Pos → Pos → Bool
  cutᵇ zero    q q* y y* = false
  cutᵇ (suc f) q q* y y* with inst y | inst y*
  ... | frame         | frame            = lvl q q* y y*
  ... | cascade t c l | cascade t* c* l* = lvl q q* y y* ∧ (t ≡ᵇ t*) ∧ does (l ≟ˡ l*) ∧ cutᵇ f q q* c c*
  ... | _             | _                = false

  linkedᵇ : ℕ → Pos → Pos → Bool
  linkedᵇ zero    y y* = false
  linkedᵇ (suc f) y y* with inst y | inst y*
  ... | frame         | frame            = true
  ... | cascade t c l | cascade t* c* l* =
    (t ≡ᵇ t*) ∧ does (l ≟ˡ l*) ∧ (c <ᵖ y) ∧ (c* <ᵖ y*) ∧ not (inst c ==ⁱ inst y) ∧ not (inst c* ==ⁱ inst y*) ∧ linkedᵇ f c c*
  ... | _             | _                = false

  fuel : ℕ
  fuel = 64

------------------------------------------------------------------------
-- One subterm's checks

-- A hot in scope: its visible rows and its map.
Hots : Set
Hots = List (List (Pos × Vis) × (Pos → Pos))

-- Findings (kind, where), subterms checked, subterms skipped.
Res : Set
Res = List (String × String) × ℕ × ℕ

private
  _⊹_ : Res → Res → Res
  (a , b , c) ⊹ (a′ , b′ , c′) = a ++ a′ , b + b′ , c + c′

  none : Res
  none = [] , 0 , 0

  allPairs : ∀ {X : Set} → List X → List (X × X)
  allPairs xs = concatMap (λ a → mapL (a ,_) xs) xs

  fail : String → String → Pos → Pos → List (String × String)
  fail kind nm a a* = [ kind , nm +++ " " +++ showPos a +++ " ~ " +++ showPos a* ]

  checks : String → Pos → Pos → Hots → List (Pos × Pos) → List (String × String)
  checks nm p p* hs m =
       concatMap (λ { ((a , a*) , (b , b*)) → if (a <ᵖ b) ∧ not (a* <ᵖ b*) then fail "order" nm a a* else [] }) (allPairs m)
    ++ concatMap (λ { ((a , a*) , (b , b*)) → if eqᵇ (inst a ==ⁱ inst b) (inst a* ==ⁱ inst b*) then [] else fail "instant" nm a b }) (allPairs m)
    ++ concatMap (λ { (a , a*) → if eqᵇ (inst a* ==ⁱ inst p*) (inst a ==ⁱ inst p) then [] else fail "home" nm a a* }) m
    ++ concatMap (λ { (a , a*) → if linkedᵇ fuel a a* then [] else fail "linked" nm a a* }) m
    ++ concatMap (λ { (ys , ψ) → concatMap (λ { (y , _) → if cutᵇ fuel p p* y (ψ y) then [] else fail "cuts" nm y (ψ y) }) ys }) hs
    ++ concatMap (λ { ((a , a*) , (b , b*)) → if cutᵇ fuel (a ⊕ [ ix 0 ]) (a* ⊕ [ ix 0 ]) b b* then [] else fail "self" nm a b }) (allPairs m)

  -- A subterm's two tables: its map, and its findings.
  node : ∀ {A} → String → Pos → Pos → Hots → Maybe (Listed A) → Maybe (Listed (IE A)) → Maybe (List (Pos × Pos)) × Res
  node {A} nm p p* hs t t* with plainV t | elabV {A} t*
  ... | just ks | just ks* with pairing ks ks*
  ...   | nothing = nothing , ([ "count" , nm +++ " " +++ showℕ (length ks) +++ " ~ " +++ showℕ (length ks*) ] , 1 , 0)
  ...   | just m  = just m , (checks nm p p* hs m , 1 , 0)
  node nm p p* hs t t* | _ | _ = nothing , ([] , 0 , 1)

------------------------------------------------------------------------
-- The walk

Ren : List Set → List Set → Set₁
Ren Γ Δ = ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ

private
  hotV : ∀ {A} → Maybe (Listed A) → List (Pos × Vis)
  hotV nothing  = []
  hotV (just l) = concatMap visP (rows (hotOf l))

  hotL : ∀ {A} → Maybe (Listed A) → Listed A
  hotL nothing  = [] ⊣ true
  hotL (just l) = hotOf l

  -- The annotated hot's rows.
  annRows : ∀ {A} → Maybe (Listed (AIE A)) → List Pos
  annRows nothing  = []
  annRows (just l) = mapL proj₁ (rows l)

  memᵖ : Pos → List Pos → Bool
  memᵖ q = anyᵇ λ r → does (q ≟ᵖ r)

  -- Where `laneˢ` subscribes its program, under a start `s*` of the
  -- lanes' flatMap: its lane part, the share's trigger, and the lane.
  laneL laneM : Pos → Pos
  laneL s* = s* ⊕ [ ix 0 ] ⊕ [ ix 1 ]
  laneM s* = laneL s* ⊕ [ ix 1 ] ⊕ [ ix 0 ] ⊕ [ sub (laneL s* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ] ⊕ [ ix 1 ]

  laneX : Pos → Pos
  laneX s* = laneM s* ⊕ [ ix 0 ] ⊕ [ ix 1 ]

  pairStarts : ∀ {A : Set} → List (A × Pos) → List Pos → Maybe (List (A × Pos × Pos))
  pairStarts []             []         = just []
  pairStarts ((a , s) ∷ xs) (s* ∷ ss*) with pairStarts xs ss*
  ... | nothing = nothing
  ... | just r  = just ((a , s , s*) ∷ r)
  pairStarts _              _          = nothing

  entryStarts : ∀ {A B : Set} → Maybe (List (ℕ × Pos × A × List (Pos × Listed B))) → List (A × Pos)
  entryStarts nothing   = []
  entryStarts (just gs) = concatMap (λ { (_ , _ , a , ss) → mapL (λ { (s , _) → a , s }) ss }) gs

mutual
  -- A subterm's map, and the findings at and below it.
  walkM : ∀ {Γ Δ A} → ℕ → ℕ → Obs Timeline Γ A → Ren Γ Δ → All Listed Γ → All Listed Δ → Hots → Pos → Pos → String → Maybe (List (Pos × Pos)) × Res
  walkM N n o ρι ρ ρ* hs p p* nm with node nm p p* hs (listC N n o ρ p) (listC N n (elab ρι o) ρ* p*)
  ... | m , r = m , (r ⊹ below N n o ρι ρ ρ* hs p p* nm)

  walk : ∀ {Γ Δ A} → ℕ → ℕ → Obs Timeline Γ A → Ren Γ Δ → All Listed Γ → All Listed Δ → Hots → Pos → Pos → String → Res
  walk N n o ρι ρ ρ* hs p p* nm = proj₂ (walkM N n o ρι ρ ρ* hs p p* nm)

  below : ∀ {Γ Δ A} → ℕ → ℕ → Obs Timeline Γ A → Ren Γ Δ → All Listed Γ → All Listed Δ → Hots → Pos → Pos → String → Res
  below N n       (cold _)          ρι ρ ρ* hs p p* nm = none
  below N n       empty             ρι ρ ρ* hs p p* nm = none
  below N n       (of _)            ρι ρ ρ* hs p p* nm = none
  below N n       (connected _)     ρι ρ ρ* hs p p* nm = none
  below N n       (map _ s)         ρι ρ ρ* hs p p* nm = walk N n s ρι ρ ρ* hs p p* (nm +++ "/map")
  below N n       (scan _ _ s)      ρι ρ ρ* hs p p* nm = walk N n s ρι ρ ρ* hs p p* (nm +++ "/scan")
  below N n       (takeWhile _ _ s) ρι ρ ρ* hs p p* nm = walk N n s ρι ρ ρ* hs p p* (nm +++ "/take")
  below N zero    (defer _)         ρι ρ ρ* hs p p* nm = none
  below N (suc n) (defer l)         ρι ρ ρ* hs p p* nm =
    walk N n (Later.force l) ρι ρ ρ* hs (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) (nm +++ "/defer")
  below {Γ} {Δ} {A} N n (connect {A = S} s b) ρι ρ ρ* hs p p* nm =
    proj₂ src ⊹ (hot-image ⊹ walk N n b (ext ρι) (hotL σ ∷ ρ) (hotL σ* ∷ ρ*) ((hotV σ , ψ) ∷ hs) (p ⊕ [ ix 0 ]) (p* ⊕ [ ix 0 ]) (nm +++ "/body"))
    where
      σ  = listC N n s ρ (p ⊕ [ ix 1 ])
      σ* = listC N n (annotate (elab ρι s)) ρ* (p* ⊕ [ ix 1 ])
      src = walkM N n s ρι ρ ρ* hs (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (nm +++ "/src")
      m : List (Pos × Pos)
      m with proj₁ src
      ... | nothing = []
      ... | just m′ = m′
      reader* : Pos
      reader* = p* ⊕ [ ix 1 ] ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 1 ]
      ψ : Pos → Pos
      ψ k = phi m k ⊕ [ sub reader* ]
      hot-image : Res
      -- The annotated hot lists each source row at its image; a reader
      -- rejoins it under its own subscription (`ψ`).
      hot-image = concatMap (λ { (y , _) → if memᵖ (phi m y) (annRows σ*) then []
                    else [ "hot-image" , nm +++ " " +++ showPos y +++ " ~ " +++ showPos (phi m y) +++ " among "
                                          +++ L.foldr (λ r acc → showPos r +++ " " +++ acc) "" (L.take 6 (annRows σ*)) ] }) (hotV σ) , 0 , 0
  below {Γ} {Δ} {B} N n (flatMap {A = A} op f s) ρι ρ ρ* hs p p* nm =
    proj₂ src ⊹ (lanesRes ⊹ coreRes)
    where
      tt-tab : Listed ⊤
      tt-tab = hotL (listC N n (of (tt ∷ [])) ρ* (p* ⊕ [ ix 1 ]))
      sp* : Pos
      sp* = p* ⊕ [ ix 1 ] ⊕ [ ix 0 ] ⊕ [ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ] ⊕ [ ix 1 ]
      src = walkM N n s (λ i → there (ρι i)) ρ (tt-tab ∷ ρ*) hs p sp* (nm +++ "/src")
      s* : Obs Timeline (⊤ ∷ Δ) (IE A)
      s* = elab (λ i → there (ρι i)) s
      sh-tab : Listed (IE A)
      sh-tab = hotL (listC N n (flatMap (mergeᶠ nothing) (λ _ → s*) (connected (here refl))) (tt-tab ∷ ρ*) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]))
      c₃ c₂ c₁ : Pos
      c₃ = p* ⊕ [ ix 0 ] ⊕ [ ix 0 ]
      c₂ = c₃ ⊕ [ ix 0 ]
      c₁ = c₂ ⊕ [ ix 1 ]
      cl-tab : Listed (IE B)
      cl-tab = hotL (listC N n (closer {A = A} {B = B}) (sh-tab ∷ tt-tab ∷ ρ*) (c₃ ⊕ [ ix 1 ]))
      ρ*c : All Listed (IE B ∷ IE A ∷ ⊤ ∷ Δ)
      ρ*c = cl-tab ∷ sh-tab ∷ tt-tab ∷ ρ*
      ρι⁴ : Ren Γ (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
      ρι⁴ i = there (there (there (there (ρι i))))
      core-src : Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) A
      core-src = each valuesOf (connected (there (here refl)))
      o  = listC N n s ρ p
      o* = listC N n core-src ρ*c c₁
      vs vs* : List (Pos × A)
      vs with o
      ... | nothing = []
      ... | just l  = values (rows l)
      vs* with o*
      ... | nothing = []
      ... | just l  = values (rows l)

      -- Each value's lanes, at their plain starts and the lanes' flatMap's.
      starts : _ → Maybe (List (A × Pos × Pos))
      starts (mergeᶠ (just k)) with o | o*
      ... | just l | just l* = pairStarts
            (entryStarts (BoundedL.levels k (afterL (λ a → listC N n (f a) ρ)) l (length vs) 0 [] (Order.nths vs 0)))
            (mapL proj₂ (entryStarts (BoundedL.levels k (afterL (λ a → listC N n (laneˢ (elab ρι⁴ (f a))) ρ*c)) l* (length vs*) 0 [] (Order.nths vs* 0))))
      ... | _ | _ = just []
      starts _ = pairStarts (mapL (λ { (q , a) → a , q ⊕ [ ix 1 ] }) vs) (mapL (λ { (q* , _) → q* ⊕ [ ix 1 ] }) vs*)

      -- One lane, at its plain start and its lanes' flatMap's: the two
      -- starts, the lane's map, its findings.
      lane : A × Pos × Pos → Pos × Pos × Maybe (List (Pos × Pos)) × Res
      lane (a , st , st*) with walkM N n (f a) ρι⁴ ρ (hotL (listC N n (of (tt ∷ [])) ρ*c (laneL st* ⊕ [ ix 1 ])) ∷ ρ*c) hs st (laneX st*) (nm +++ "/lane")
      ... | m , r = st , st* , m , r

      walked : List (Pos × Pos × Maybe (List (Pos × Pos)) × Res)
      walked with starts op
      ... | nothing = []
      ... | just ls = mapL lane ls

      lanesRes : Res
      lanesRes with starts op
      ... | nothing = fail "lanes" nm p p* , 0 , 0
      ... | just _  = L.foldr (λ { (_ , _ , _ , r) acc → r ⊹ acc }) none walked

      -- The lanes' flatMap's table against the plain flatMap's, along the
      -- map written out: a lane row through `laneˢ`'s reader and
      -- `counted`'s emit, its end at its `laneDone`'s; a source row
      -- through the shared hot's reader.
      readerR : Pos → Pos
      readerR st* = laneL st* ⊕ [ ix 0 ] ⊕ [ ix 0 ] ⊕ [ ix 1 ] ⊕ [ ix 1 ]

      emitAt : Pos → Pos
      emitAt r = r ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]

      laneOf : Pos → List (Pos × Pos × Maybe (List (Pos × Pos)) × Res) → Maybe (Pos × List (Pos × Pos))
      laneOf k [] = nothing
      laneOf k ((st , st* , just m , _) ∷ ws) = if inside st k then just (st* , m) else laneOf k ws
      laneOf k (_ ∷ ws) = laneOf k ws

      srcMap : List (Pos × Pos)
      srcMap with proj₁ src
      ... | nothing = []
      ... | just m  = m

      formula : Pos × Vis → Pos
      -- The source's end is the shared flatMap's own, read through the
      -- share's reader.
      formula (k , v) with laneOf k walked | v
      ... | nothing | vout = phi srcMap k ⊕ [ sub c₁ ]
      ... | nothing | vend = p* ⊕ [ ix 1 ] ⊕ [ last ] ⊕ [ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ] ⊕ [ sub c₁ ]
      ... | just (st* , m) | vout = emitAt (phi m k ⊕ [ sub (readerR st*) ])
      ... | just (st* , m) | vend = emitAt (phi m k ⊕ [ sub (readerR st*) ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]) ⊕ [ last ]

      coreRes : Res
      coreRes with plainV (listC N n (flatMap op f s) ρ p) | elabV {B} (listC N n (flatMap op (λ a → laneˢ (elab ρι⁴ (f a))) core-src) ρ*c c₁)
      ... | just ks | just ks* with pairing ks ks*
      ...   | nothing = fail "core-count" nm p c₁ , 0 , 0
      ...   | just m  = concatMap (λ { (k , k*) → let w = formula (k , kindOf k) in if does (w ≟ᵖ k*) then []
                                    else [ "core" , nm +++ " " +++ showPos k +++ " ~ " +++ showPos k* +++ " written " +++ showPos w ] }) m , 0 , 0
        where
          kindOf : Pos → Vis
          kindOf k = if memᵖ k (ofKind false ks) then vend else vout
      coreRes | _ | _ = none

------------------------------------------------------------------------
-- The run

private
  N₀ n₀ : ℕ
  N₀ = 8
  n₀ = 3

  root* : Pos
  root* = root ⊕ [ ix 0 ] ⊕ [ ix 1 ] ⊕ [ ix 1 ]

  probe : ℕ → Res
  probe seed = walk N₀ n₀ (toObs timeline 3 (program seed) [] [] []) (λ i → i) [] [] [] root root* ""

  -- A row's position and its event's former.
  tagOf : ∀ {A} → Ev A → ℕ
  tagOf (out _) = 0
  tagOf end     = 1
  tagOf (pin _) = 2
  tagOf skip    = 3

  upToᵖ : ∀ {A} → Pos → Maybe (Listed A) → List (Pos × ℕ)
  upToᵖ q nothing  = []
  upToᵖ q (just l) = concatMap (λ { (r , e) → when ((r <ᵖ q) ∨ does (r ≟ᵖ q)) (r , tagOf e) }) (sort (rows l))

  sameRows : List (Pos × ℕ) → List (Pos × ℕ) → Bool
  sameRows []             []             = true
  sameRows ((r , a) ∷ xs) ((r′ , a′) ∷ ys) = does (r ≟ᵖ r′) ∧ (a ≡ᵇ a′) ∧ sameRows xs ys
  sameRows _              _              = false

  -- The back fact a cut-indexed `bk` needs: a cut whose elaborated table
  -- agrees with the whole up to a row's image agrees with the plain
  -- whole up to the row.
  backRes : ℕ → Res
  backRes seed with toObs timeline 3 (program seed) [] [] []
  ... | o with listC N₀ n₀ o [] root | listC N₀ n₀ (elab (λ i → i) o) [] root*
  ...   | t | t* with plainV t | elabV t*
  ...     | just ks | just ks* with pairing ks ks*
  ...       | just m = concatMap at (upTo N₀) , 1 , 0
    where
      at : ℕ → List (String × String)
      at N′ with listC N′ n₀ o [] root | listC N′ n₀ (elab (λ i → i) o) [] root*
      ... | c | c* = concatMap (λ { (k , l) →
              if sameRows (upToᵖ l c*) (upToᵖ l t*) ∧ not (sameRows (upToᵖ k c) (upToᵖ k t))
              then fail "back" (showℕ N′) k l else [] }) m
  ...       | nothing = none
  backRes seed | o | t | t* | _ | _ = none

  kinds : List String
  kinds = "count" ∷ "order" ∷ "instant" ∷ "home" ∷ "linked" ∷ "cuts" ∷ "self" ∷ "hot-image" ∷ "lanes" ∷ "core-count" ∷ "core" ∷ "back" ∷ []

  has : String → List (String × String) → Bool
  has k = anyᵇ λ f → proj₁ f == k

  firstOf : String → List (String × String) → List String
  firstOf k []            = []
  firstOf k ((k′ , w) ∷ fs) = if k′ == k then [ w ] else firstOf k fs

  -- Per kind, the seeds it fails.
  Tally : Set
  Tally = List (String × ℕ)

  bump : List (String × String) → Tally → Tally
  bump fs = mapL λ { (k , c) → k , (if has k fs then suc c else c) }

  showTally : Tally → String
  showTally []            = ""
  showTally ((k , c) ∷ t) = k +++ "=" +++ showℕ c +++ " " +++ showTally t

  say : List String → IO Unit
  say []       = return _
  say (l ∷ ls) = putStrLn l >>= λ _ → say ls

  report : List ℕ → ℕ → ℕ → ℕ → Tally → IO Unit
  report [] bad nodes skipped t =
    putStrLn ("table-check: done " +++ showℕ bad +++ " failing seeds, " +++ showℕ nodes +++ " subterms checked, "
              +++ showℕ skipped +++ " cut short; failing seeds by kind: " +++ showTally t)
  report (seed ∷ seeds) bad nodes skipped t with probe seed ⊹ backRes seed
  ... | [] , c , s = report seeds bad (nodes + c) (skipped + s) t
  ... | fs , c , s =
    putStrLn ("table-check: program " +++ showℕ seed +++ " " +++ showCode natᵗ (program seed)) >>= λ _ →
    say (concatMap (λ k → mapL (λ w → "table-check: FAIL seed " +++ showℕ seed +++ " " +++ k +++ " " +++ w) (firstOf k fs)) kinds) >>= λ _ →
    report seeds (suc bad) (nodes + c) (skipped + s) (bump fs t)

main : IO Unit
main = hSetBuffering stdout lineBuffering >>= λ _ → report (upTo 300) 0 0 0 (mapL (_, 0) kinds)
