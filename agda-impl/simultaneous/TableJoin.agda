{-# OPTIONS --guardedness #-}

-- THE JOINERS' CORES (`flat-core`): each joiner's lanes' flatMap related
-- to the plain flatMap along `simultaneous.TableFlat`'s shared map.
--
-- A JOINER'S CUTS BACK ARE ITS DENOTATION'S (`mg-back`, `sw-back`).  A
-- table is its cut program's, so two cuts of the plain joiner agree up
-- to a row once their outers do and every lane the joiner reads there
-- does (`denotation.Laws.Join`, one policy over all four joiners).  The
-- policy carries the switch's negative condition: a lane is read only
-- uncut, and past its cut only the pins of its uncut connects.  So the
-- switch owes what the merge owes, its lanes up to their cuts, and a pin
-- leaf besides; what each owes is the elaborated side, the core agreeing
-- up to a row's image putting the outer and the lanes read in agreement.
module simultaneous.TableJoin where

open import Data.Bool using (T; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Maybe using (just; nothing; maybe)
import Data.Maybe as M
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (does)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; flatMap)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; Unpinned; out; pin; _≼_; _≺_)
open import denotation.Laws.Modulus using (AgreeTo; ≼-refl)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; anyᵇ; values; afterL; lanes; module BoundedL; module ExhaustL; module Order)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.TableCorr using (Rel; TR; Corr; Cons; Got)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv using (Ren; got-ok; pin-ok; after-ok; pin-after-ok; Tab; up; Linked; Aligned; EnvR; maps; lw; lw*;
  den; den-ex; Admits)

open import simultaneous.LaneEndSched using (tr-in)

open import Relation.Nullary using (¬_)
open import denotation.EmissionSet using (enter; DenEnv; Den)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (⟨_⟩; upto; trunc-to)
open import denotation.Laws.Join using (module Join)
open import denotation.Laws.Cut using (capprox)
open import quickcheck.Tabled.Exact.Base using (complete)
open import simultaneous.Listing using (listC-exact)
open import simultaneous.TableFlat using (module Flat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

module Joiners {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (ad : Admits (lw env) p) (ad* : Admits (lw* env) p*) where

  open Flat n f s ρ uρ ρι ρ* uρ* env p p* ad ad*

  ----------------------------------------------------------------------
  -- The cut programs

  ρD : ℕ → DenEnv Γ
  ρD N = den (lw env) N

  sD : ℕ → Den A
  sD N = capprox (3 + N) n s (ρD N)

  fD : ℕ → A → Den B
  fD N a = capprox (3 + N) n (f a) (ρD N)

  -- A table's rows are its cut program's.
  tr-den : ∀ {X} (o : Obs Timeline Γ X) q {N y e} → TR (Tab n o ρ q N) y e → enter (capprox (3 + N) n o (ρD N)) q y e
  tr-den o q {N} = tr-in (3 + N) n o (den-ex (lw env) N) (uρ N) q

  den-tr : ∀ {X} (o : Obs Timeline Γ X) q {N y e} → enter (capprox (3 + N) n o (ρD N)) q y e → TR (Tab n o ρ q N) y e
  den-tr o q {N} x with listC-ok (3 + N) n o (uρ N) q
  ... | L , eq , uL = L , eq , complete (listC-exact (3 + N) n o (den-ex (lw env) N) q eq uL) x

  -- Agreement crosses between two cuts' tables and their cut programs.
  ag-den : ∀ {X} (o : Obs Timeline Γ X) q {N N′ k} → AgreeTo k (TR (Tab n o ρ q N)) (TR (Tab n o ρ q N′))
         → AgreeTo k (enter (capprox (3 + N) n o (ρD N)) q) (enter (capprox (3 + N′) n o (ρD N′)) q)
  ag-den o q {N} {N′} a = ⟨ (λ yk → (λ x → tr-den o q {N′} (proj₁ (upto a yk) (den-tr o q {N} x)))
                                  , (λ x → tr-den o q {N} (proj₂ (upto a yk) (den-tr o q {N′} x)))) ⟩

  den-ag : ∀ {X} (o : Obs Timeline Γ X) q {N N′ k} → AgreeTo k (enter (capprox (3 + N) n o (ρD N)) q) (enter (capprox (3 + N′) n o (ρD N′)) q)
         → AgreeTo k (TR (Tab n o ρ q N)) (TR (Tab n o ρ q N′))
  den-ag o q {N} {N′} a = ⟨ (λ yk → (λ x → den-tr o q {N′} (proj₁ (upto a yk) (tr-den o q {N} x)))
                                  , (λ x → den-tr o q {N} (proj₂ (upto a yk) (tr-den o q {N′} x)))) ⟩

  ----------------------------------------------------------------------
  -- The joiners

  module Joins (Os : Src) (Ls : Lanes) (Lc : LanesCoh Ls) where
    open Parts Os Ls Lc

    ----------------------------------------------------------------------
    -- THE PLAIN MERGE: every value's lane subscribed under its row, every
    -- lane row shown.
    module MergeTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = Pd (mergeᶠ nothing)
      Q′ = λ N → listC (3 + N) n (core (mergeᶠ nothing)) (ρ*c N) c₁

      open Tabs (mergeᶠ nothing) (λ N → L.map (valRec N) (valsAt N))

      postulate
        mg-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        -- THE MERGE'S MAP ACROSS CUTS: each value's lane runs uncut, so two
        -- cuts agreeing up to a row hold its values alike below it, each
        -- lane listing alike; a value past the row has a lane quiet up to it.
        mg-vals-eq     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → ValsEq k (valsAt N) (valsAt N′)
        mg-lane-un     : ∀ {N k e} → TR (P′ N) k e → Unpinned e
                       → ∀ {R} → holder (L.map (valRec N) (valsAt N)) k ≡ just R → Σ (Ev B) λ ev → TR (LaneRec.tab R) k ev × Unpinned ev
        mg-src-at      : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′))
                       → holder (L.map (valRec N) (valsAt N)) k ≡ nothing → ends-above k (L.map (valRec N) (valsAt N)) ≡ nothing → SrcAt N N′ k
        mg-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
        -- THE MERGE'S CUTS BACK, ITS OUTER AND ITS LANES: the core agreeing
        -- up to a row's image puts the source, and every lane subscribed at
        -- or before the row, in agreement up to it.
        mg-src-back    : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → AgreeTo k (TR (S N′)) (TR (S N))
        mg-lane-back   : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → ∀ {q a k₀} → TR (S N′) q (out a) → q ≼ k → k₀ ≼ k
                       → AgreeTo k₀ (TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N′)) (TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N))
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
        mg-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        mg-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        mg-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        mg-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      -- A cut agreeing up to a row's image agrees up to the row: the
      -- plain merge is its cut program's, which agrees once its outer and
      -- every lane it reads do.
      mg-back : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
              → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      mg-back {N} {N′} {k} le x un ag* =
        pd-agree {mergeᶠ nothing} {N′} {N} {k} (den-ag (flatMap (mergeᶠ nothing) f s) p (trunc-to (MJ.agree (ag-den s p (mg-src-back le x un ag*)) L)))
        where
          module MJ = Join.MergeJ {A} {B} k
          L : MJ.Lanes (enter (sD N′) p) (fD N′) (fD N)
          L = MJ.lanes
                (λ {q} {a} xq _ qk k₀k _ → ag-den (f a) (q ⊕ [ ix 1 ]) (mg-lane-back le x un ag* (den-tr s p xq) qk k₀k))
                (λ {q} {a} {k₀} xq _ qk k₀k _ _ → upto (ag-den (f a) (q ⊕ [ ix 1 ]) (mg-lane-back le x un ag* (den-tr s p xq) qk k₀k)) (≼-refl {k₀}))

      mg-φ-agree : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
      mg-φ-agree x un ag = tabs-φ-agree (vals-lanes (mg-vals-eq x un ag)) (mg-lane-un x un) (mg-src-at x un ag)

      mg-got : ∀ N → Got (P′ N)
      mg-got N = pd-got (mergeᶠ nothing) N

      mg-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      mg-pin-in {N} = pd-pin-in {mergeᶠ nothing} {N}

      mg-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      mg-after {N} = pd-after {mergeᶠ nothing} {N}

      mg-got* : ∀ N → Got (Q′ N)
      mg-got* N = got-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} (uρ*c N) c₁

      mg-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      mg-pin-in* {N} = pin-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} c₁

      mg-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      mg-after* {N} = after-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} c₁

      mg-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
      mg-pin-after* {N} = pin-after-ok (3 + N) n (core (mergeᶠ nothing)) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = mg-corr ; φ-agree = mg-φ-agree ; bk = bk′ ; in-bk = mg-in-bk ; pb-few = pb-few′
        ; back = mg-back ; put-up = mg-put-up ; back-put = mg-back-put
        ; elab-causal = mg-elab-causal ; stable← = mg-stable← ; stable-put = mg-stable-put ; stable-lead = mg-stable-lead
        ; elab-all = mg-elab-all ; func = pd-func {(mergeᶠ nothing)} ; func* = core-func {(mergeᶠ nothing)} ; flat = pd-flat {(mergeᶠ nothing)} ; flat* = core-flat {(mergeᶠ nothing)}
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
      P′ = Pd (mergeᶠ (just k))
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

      open Tabs (mergeᶠ (just k)) (λ N → recs N (entriesAt N) [])

      postulate
        cc-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        -- THE QUEUE'S MAP ACROSS CUTS: two cuts agreeing up to a row run
        -- the same queue below it, so each level's lanes are alike, a
        -- queued lane waiting on alike lanes; a lane subscribed past the row
        -- is quiet up to it.
        cc-lanes-eq    : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′))
                       → LanesEq k (recs N (entriesAt N) []) (recs N′ (entriesAt N′) [])
        cc-lane-un     : ∀ {N k e} → TR (P′ N) k e → Unpinned e
                       → ∀ {R} → holder (recs N (entriesAt N) []) k ≡ just R → Σ (Ev B) λ ev → TR (LaneRec.tab R) k ev × Unpinned ev
        cc-src-at      : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′))
                       → holder (recs N (entriesAt N) []) k ≡ nothing → ends-above k (recs N (entriesAt N) []) ≡ nothing → SrcAt N N′ k
        cc-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
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
        cc-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        cc-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        cc-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        cc-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      cc-φ-agree : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
      cc-φ-agree x un ag = tabs-φ-agree (cc-lanes-eq x un ag) (cc-lane-un x un) (cc-src-at x un ag)

      cc-got : ∀ N → Got (P′ N)
      cc-got N = pd-got (mergeᶠ (just k)) N

      cc-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      cc-pin-in {N} = pd-pin-in {mergeᶠ (just k)} {N}

      cc-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      cc-after {N} = pd-after {mergeᶠ (just k)} {N}

      cc-got* : ∀ N → Got (Q′ N)
      cc-got* N = got-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} (uρ*c N) c₁

      cc-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      cc-pin-in* {N} = pin-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} c₁

      cc-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      cc-after* {N} = after-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} c₁

      cc-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
      cc-pin-after* {N} = pin-after-ok (3 + N) n (core (mergeᶠ (just k))) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = cc-corr ; φ-agree = cc-φ-agree ; bk = bk′ ; in-bk = cc-in-bk ; pb-few = pb-few′
        ; back = cc-back ; put-up = cc-put-up ; back-put = cc-back-put
        ; elab-causal = cc-elab-causal ; stable← = cc-stable← ; stable-put = cc-stable-put ; stable-lead = cc-stable-lead
        ; elab-all = cc-elab-all ; func = pd-func {(mergeᶠ (just k))} ; func* = core-func {(mergeᶠ (just k))} ; flat = pd-flat {(mergeᶠ (just k))} ; flat* = core-flat {(mergeᶠ (just k))}
        ; pin-in = cc-pin-in ; pin-in* = cc-pin-in* ; cons = cc-cons ; cons* = cc-cons* ; got = cc-got ; got* = cc-got*
        ; after = cc-after ; after* = cc-after* ; after-φ = cc-after-φ ; pin-after* = cc-pin-after* ; pin-stable = cc-pin-stable }

    ----------------------------------------------------------------------
    -- THE SWITCH: every value's lane subscribed under its row, its rows
    -- shown only before the next value's row; the map is the merge's.
    module SwitchTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = Pd (switchᶠ)
      Q′ = λ N → listC (3 + N) n (core (switchᶠ)) (ρ*c N) c₁

      open Tabs switchᶠ (λ N → L.map (valRec N) (valsAt N))

      postulate
        sw-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        -- THE SWITCH'S MAP ACROSS CUTS: the plain switch's rows agreeing up
        -- to a row say nothing of a cut lane's rows past its cut, which the
        -- switch never shows, yet the holder and the ends above read every
        -- lane's whole table.
        -- DEAD ROUTE: `tabs-φ-agree` as the merge's body: its `LanesEq`
        --   needs every lane's table agreeing up to the row, a cut lane's
        --   included, and the switch's agreement reaches a cut lane's table
        --   only up to the next value's row.
        sw-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
        sw-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)

        -- THE SWITCH'S CUTS BACK, ITS OUTER AND ITS LANES: as the merge's,
        -- each lane read only up to its cut, and past it only the pins its
        -- uncut connects keep.
        sw-src-back    : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → AgreeTo k (TR (S N′)) (TR (S N))
        sw-lane-back   : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → ∀ {q a k₀} → TR (S N′) q (out a) → q ≼ k → k₀ ≼ k
                       → (∀ {q′ a′} → TR (S N′) q′ (out a′) → q ≺ q′ → q′ ≺ k₀ → ⊥)
                       → AgreeTo k₀ (TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N′)) (TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N))
        sw-lane-left   : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                       → ∀ {q a k₀ r} → TR (S N′) q (out a) → q ≼ k → k₀ ≼ k
                       → (∀ {q′ a′} → TR (S N′) q′ (out a′) → q ≺ q′ → q′ ≺ r → ⊥) → T (inside r k₀)
                       → (TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N′) k₀ (pin r) → TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N) k₀ (pin r))
                       × (TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N) k₀ (pin r) → TR (Tab n (f a) ρ (q ⊕ [ ix 1 ]) N′) k₀ (pin r))
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
        sw-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        sw-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        sw-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        sw-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      -- As the merge's, the switch's policy reading a lane only uncut.
      sw-back : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
              → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      sw-back {N} {N′} {k} le x un ag* =
        pd-agree {switchᶠ} {N′} {N} {k} (den-ag (flatMap switchᶠ f s) p (trunc-to (SJ.agree (ag-den s p (sw-src-back le x un ag*)) L)))
        where
          module SJ = Join.SwitchJ {A} {B} k
          uncut : ∀ {q r} → ¬ ES.Switch.Cut (fD N′) (enter (sD N′) p) q r → ∀ {q′ a′} → TR (S N′) q′ (out a′) → q ≺ q′ → q′ ≺ r → ⊥
          uncut nc {q′} {a′} x′ qq′ q′r = nc (q′ , a′ , tr-den s p x′ , qq′ , q′r)
          L : SJ.Lanes (enter (sD N′) p) (fD N′) (fD N)
          L = SJ.lanes
                (λ {q} {a} {k₀} xq _ qk k₀k nc → ag-den (f a) (q ⊕ [ ix 1 ]) (sw-lane-back le x un ag* (den-tr s p xq) qk k₀k (uncut {q} {k₀} nc)))
                (λ {q} {a} {k₀} {r} xq _ qk k₀k nc i →
                   let (to , fr) = sw-lane-left le x un ag* (den-tr s p xq) qk k₀k (uncut {q} {r} nc) i
                   in (λ y → tr-den (f a) (q ⊕ [ ix 1 ]) (to (den-tr (f a) (q ⊕ [ ix 1 ]) y)))
                    , (λ y → tr-den (f a) (q ⊕ [ ix 1 ]) (fr (den-tr (f a) (q ⊕ [ ix 1 ]) y))))

      sw-got : ∀ N → Got (P′ N)
      sw-got N = pd-got (switchᶠ) N

      sw-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      sw-pin-in {N} = pd-pin-in {switchᶠ} {N}

      sw-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      sw-after {N} = pd-after {switchᶠ} {N}

      sw-got* : ∀ N → Got (Q′ N)
      sw-got* N = got-ok (3 + N) n (core switchᶠ) {ρ*c N} (uρ*c N) c₁

      sw-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      sw-pin-in* {N} = pin-ok (3 + N) n (core switchᶠ) {ρ*c N} c₁

      sw-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      sw-after* {N} = after-ok (3 + N) n (core switchᶠ) {ρ*c N} c₁

      sw-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
      sw-pin-after* {N} = pin-after-ok (3 + N) n (core switchᶠ) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = sw-corr ; φ-agree = sw-φ-agree ; bk = bk′ ; in-bk = sw-in-bk ; pb-few = pb-few′
        ; back = sw-back ; put-up = sw-put-up ; back-put = sw-back-put
        ; elab-causal = sw-elab-causal ; stable← = sw-stable← ; stable-put = sw-stable-put ; stable-lead = sw-stable-lead
        ; elab-all = sw-elab-all ; func = pd-func {switchᶠ} ; func* = core-func {switchᶠ} ; flat = pd-flat {switchᶠ} ; flat* = core-flat {switchᶠ}
        ; pin-in = sw-pin-in ; pin-in* = sw-pin-in* ; cons = sw-cons ; cons* = sw-cons* ; got = sw-got ; got* = sw-got*
        ; after = sw-after ; after* = sw-after* ; after-φ = sw-after-φ ; pin-after* = sw-pin-after* ; pin-stable = sw-pin-stable }

    ----------------------------------------------------------------------
    -- THE EXHAUST: the lanes the plain exhaust runs, each subscribed under
    -- its value's row; the map is the merge's over those lanes.
    module ExhaustTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = Pd (exhaustᶠ)
      Q′ = λ N → listC (3 + N) n (core (exhaustᶠ)) (ρ*c N) c₁

      -- The values whose lane the plain exhaust runs.
      ranAt : ℕ → List Pos
      ranAt N with S N
      ... | nothing = []
      ... | just o with Tb.lanes (afterL (λ a → listC (3 + N) n (f a) (ρ N))) (values (rows o))
      ...   | nothing = []
      ...   | just ls = ExhaustL.runs o ls

      open Tabs exhaustᶠ (λ N → L.concatMap (λ v → if anyᵇ (λ q → does (q ≟ᵖ ValAt.q v)) (ranAt N) then [ valRec N v ] else []) (valsAt N))

      postulate
        ex-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
        ex-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
        ex-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
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
        ex-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
        ex-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
        ex-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₁ ≼ φ′ N k
        ex-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                       → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                       → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

      ex-got : ∀ N → Got (P′ N)
      ex-got N = pd-got (exhaustᶠ) N

      ex-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
      ex-pin-in {N} = pd-pin-in {exhaustᶠ} {N}

      ex-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
      ex-after {N} = pd-after {exhaustᶠ} {N}

      ex-got* : ∀ N → Got (Q′ N)
      ex-got* N = got-ok (3 + N) n (core exhaustᶠ) {ρ*c N} (uρ*c N) c₁

      ex-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
      ex-pin-in* {N} = pin-ok (3 + N) n (core exhaustᶠ) {ρ*c N} c₁

      ex-after* : ∀ {N l e} → TR (Q′ N) l e → c₁ ≼ l
      ex-after* {N} = after-ok (3 + N) n (core exhaustᶠ) {ρ*c N} c₁

      ex-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₁ ≼ r
      ex-pin-after* {N} = pin-after-ok (3 + N) n (core exhaustᶠ) {ρ*c N} c₁

      rel′ : Rel P′ Q′ p c₁
      rel′ = record
        { φ = φ′ ; Put = Put′ ; corr = ex-corr ; φ-agree = ex-φ-agree ; bk = bk′ ; in-bk = ex-in-bk ; pb-few = pb-few′
        ; back = ex-back ; put-up = ex-put-up ; back-put = ex-back-put
        ; elab-causal = ex-elab-causal ; stable← = ex-stable← ; stable-put = ex-stable-put ; stable-lead = ex-stable-lead
        ; elab-all = ex-elab-all ; func = pd-func {exhaustᶠ} ; func* = core-func {exhaustᶠ} ; flat = pd-flat {exhaustᶠ} ; flat* = core-flat {exhaustᶠ}
        ; pin-in = ex-pin-in ; pin-in* = ex-pin-in* ; cons = ex-cons ; cons* = ex-cons* ; got = ex-got ; got* = ex-got*
        ; after = ex-after ; after* = ex-after* ; after-φ = ex-after-φ ; pin-after* = ex-pin-after* ; pin-stable = ex-pin-stable }

  flat-core : ∀ op → Core op
  flat-core (mergeᶠ nothing)  = λ Os Ls Lc al lk → Joins.MergeTab.rel′ Os Ls Lc al lk
  flat-core (mergeᶠ (just k)) = λ Os Ls Lc al lk → Joins.ConcatTab.rel′ Os Ls Lc k al lk
  flat-core switchᶠ           = λ Os Ls Lc al lk → Joins.SwitchTab.rel′ Os Ls Lc al lk
  flat-core exhaustᶠ          = λ Os Ls Lc al lk → Joins.ExhaustTab.rel′ Os Ls Lc al lk
