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
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Maybe using (just; nothing; maybe)
import Data.Maybe as M
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Unpinned; pin; _≼_)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; anyᵇ; values; afterL; lanes; module BoundedL; module ExhaustL; module Order)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.TableCorr using (Rel; Corr)
open import simultaneous.TableKit using (TR; Got)
open import simultaneous.HorizonCorr using (module Inter; Own; OwnPut)
open import simultaneous.TableEnv using (Ren; got-ok; pin-ok; after-ok; pin-after-ok; up; Linked; Aligned; EnvR; maps; lw; lw*; den;
  Admits)


open import Relation.Nullary using (¬_)
open import denotation.EmissionSet using (DenEnv; Den)
import denotation.EmissionSet as ES
open import denotation.Laws.Cut using (capprox)
open import simultaneous.TableFlat using (module Flat; module Vals)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

-- What the plain joiners run, the same in every environment.
module Runs {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (p : Pos) where
  open Vals n s ρ p using (S)

  -- The bounded merge's entries at a cut: each value with its
  -- subscriptions.
  entriesAt : ℕ → ∀ N → List (ℕ × Pos × A × List (Pos × Tb.Listed B))
  entriesAt k N with S N
  ... | nothing = []
  ... | just o with BoundedL.levels k (afterL (λ a → listC (3 + N) n (f a) (ρ N))) o
                      (L.length (values (rows o))) 0 [] (Order.nths (values (rows o)) 0)
  ...   | nothing = []
  ...   | just gs = gs

  -- The values whose lane the plain exhaust runs.
  ranAt : ℕ → List Pos
  ranAt N with S N
  ... | nothing = []
  ... | just o with Tb.lanes (afterL (λ a → listC (3 + N) n (f a) (ρ N))) (values (rows o))
  ...   | nothing = []
  ...   | just ls = ExhaustL.runs o ls

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
        mg-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))
        mg-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
        mg-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₁ ≼ φ′ N k

      -- THE MERGE'S HANGS: its outer's boundaries, and each running
      -- lane's before the lane's cut; each partnered with its image's.
      --
      -- RECOVERY: git show 252f560:agda-impl/simultaneous/HorizonJoin.agda restores `JoinPair`, a join's pair over its parts' pairs; git show 252f560:agda-impl/simultaneous/TableJoin.agda restores `tr-den` and `den-tr`, a table read as its cut program.
      postulate
        mg-bcorr    : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (jbd (mergeᶠ nothing) N) (jbd* (mergeᶠ nothing) N)

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
        { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = mg-corr ; bk = bk′ ; in-bk = mg-in-bk ; pb-few = pb-few′
        ; func = pd-func {(mergeᶠ nothing)} ; func* = core-func {(mergeᶠ nothing)} ; flat = pd-flat {(mergeᶠ nothing)} ; flat* = core-flat {(mergeᶠ nothing)}
        ; pin-in = mg-pin-in ; pin-in* = mg-pin-in* ; got = mg-got ; got* = mg-got*
        ; after = mg-after ; after* = mg-after* ; after-φ = mg-after-φ ; pin-after* = mg-pin-after*
        ; Bd = jbd (mergeᶠ nothing) ; Bd* = jbd* (mergeᶠ nothing) ; bounded = jbounded (mergeᶠ nothing) ; bounded* = jbounded* (mergeᶠ nothing) ; bcorr = mg-bcorr }

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

      entriesAt : ∀ N → List (ℕ × Pos × A × List (Pos × Tb.Listed B))
      entriesAt = Runs.entriesAt n f s ρ p k

      -- A subscription's lane: its value's, under the value's row, or a
      -- queued one, under the end of the lane it waited on.
      one : ∀ N → Pos → A → List (LaneRec N) → Pos × Tb.Listed B → List (LaneRec N)
      one N q a acc (st , _) = if does (st ≟ᵖ (q ⊕ [ ix 1 ]))
                               then maybe (λ v → [ valRec N v ]) [] (valAtPos N q)
                               else maybe (λ { (R , cx) → [ queuedRec N R cx a ] }) [] (waitedOn acc (up st))

      -- Each entry's lanes, after those of the levels before.
      recs : ∀ N → List (ℕ × Pos × A × List (Pos × Tb.Listed B)) → List (LaneRec N) → List (LaneRec N)
      recs N []                       acc = acc
      recs N ((_ , q , a , ss) ∷ es) acc = recs N es (acc ++ L.concatMap (one N q a acc) ss)

      open Tabs (mergeᶠ (just k)) (λ N → recs N (entriesAt N) [])

      postulate
        cc-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))
        cc-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
        cc-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₁ ≼ φ′ N k

      -- THE BOUNDED MERGE'S HANGS: its outer's boundaries, and each running
      -- lane's before the lane's cut; each partnered with its image's.
      postulate
        cc-bcorr    : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (jbd (mergeᶠ (just k)) N) (jbd* (mergeᶠ (just k)) N)

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
        { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = cc-corr ; bk = bk′ ; in-bk = cc-in-bk ; pb-few = pb-few′
        ; func = pd-func {(mergeᶠ (just k))} ; func* = core-func {(mergeᶠ (just k))} ; flat = pd-flat {(mergeᶠ (just k))} ; flat* = core-flat {(mergeᶠ (just k))}
        ; pin-in = cc-pin-in ; pin-in* = cc-pin-in* ; got = cc-got ; got* = cc-got*
        ; after = cc-after ; after* = cc-after* ; after-φ = cc-after-φ ; pin-after* = cc-pin-after*
        ; Bd = jbd (mergeᶠ (just k)) ; Bd* = jbd* (mergeᶠ (just k)) ; bounded = jbounded (mergeᶠ (just k)) ; bounded* = jbounded* (mergeᶠ (just k)) ; bcorr = cc-bcorr }

    ----------------------------------------------------------------------
    -- THE SWITCH: every value's lane subscribed under its row, its rows
    -- shown only before the next value's row; the map is the merge's.
    module SwitchTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = Pd (switchᶠ)
      Q′ = λ N → listC (3 + N) n (core (switchᶠ)) (ρ*c N) c₁

      open Tabs switchᶠ (λ N → L.map (valRec N) (valsAt N))

      postulate
        sw-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))
        sw-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)

        sw-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₁ ≼ φ′ N k

      -- THE SWITCH'S HANGS: its outer's boundaries, and each running
      -- lane's before the lane's cut; each partnered with its image's.
      postulate
        sw-bcorr    : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (jbd switchᶠ N) (jbd* switchᶠ N)

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
        { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = sw-corr ; bk = bk′ ; in-bk = sw-in-bk ; pb-few = pb-few′
        ; func = pd-func {switchᶠ} ; func* = core-func {switchᶠ} ; flat = pd-flat {switchᶠ} ; flat* = core-flat {switchᶠ}
        ; pin-in = sw-pin-in ; pin-in* = sw-pin-in* ; got = sw-got ; got* = sw-got*
        ; after = sw-after ; after* = sw-after* ; after-φ = sw-after-φ ; pin-after* = sw-pin-after*
        ; Bd = jbd switchᶠ ; Bd* = jbd* switchᶠ ; bounded = jbounded switchᶠ ; bounded* = jbounded* switchᶠ ; bcorr = sw-bcorr }

    ----------------------------------------------------------------------
    -- THE EXHAUST: the lanes the plain exhaust runs, each subscribed under
    -- its value's row; the map is the merge's over those lanes.
    module ExhaustTab (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
      P′ Q′ : ℕ → _
      P′ = Pd (exhaustᶠ)
      Q′ = λ N → listC (3 + N) n (core (exhaustᶠ)) (ρ*c N) c₁

      ranAt : ℕ → List Pos
      ranAt = Runs.ranAt n f s ρ p

      open Tabs exhaustᶠ (λ N → L.concatMap (λ v → if anyᵇ (λ q → does (q ≟ᵖ ValAt.q v)) (ranAt N) then [ valRec N v ] else []) (valsAt N))

      postulate
        ex-corr        : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))
        ex-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
        ex-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₁ ≼ φ′ N k

      -- THE EXHAUST'S HANGS: its outer's boundaries, and each running
      -- lane's before the lane's cut; each partnered with its image's.
      postulate
        ex-bcorr    : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (jbd exhaustᶠ N) (jbd* exhaustᶠ N)

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
        { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = ex-corr ; bk = bk′ ; in-bk = ex-in-bk ; pb-few = pb-few′
        ; func = pd-func {exhaustᶠ} ; func* = core-func {exhaustᶠ} ; flat = pd-flat {exhaustᶠ} ; flat* = core-flat {exhaustᶠ}
        ; pin-in = ex-pin-in ; pin-in* = ex-pin-in* ; got = ex-got ; got* = ex-got*
        ; after = ex-after ; after* = ex-after* ; after-φ = ex-after-φ ; pin-after* = ex-pin-after*
        ; Bd = jbd exhaustᶠ ; Bd* = jbd* exhaustᶠ ; bounded = jbounded exhaustᶠ ; bounded* = jbounded* exhaustᶠ ; bcorr = ex-bcorr }

  flat-core : ∀ op → Core op
  flat-core (mergeᶠ nothing)  = λ Os Ls Lc al lk → Joins.MergeTab.rel′ Os Ls Lc al lk
  flat-core (mergeᶠ (just k)) = λ Os Ls Lc al lk → Joins.ConcatTab.rel′ Os Ls Lc k al lk
  flat-core switchᶠ           = λ Os Ls Lc al lk → Joins.SwitchTab.rel′ Os Ls Lc al lk
  flat-core exhaustᶠ          = λ Os Ls Lc al lk → Joins.ExhaustTab.rel′ Os Ls Lc al lk
