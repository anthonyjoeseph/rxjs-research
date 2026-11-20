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

open import Data.Bool using (T; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Maybe using (just; nothing; maybe)
import Data.Maybe as M
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (does)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Unpinned; pin; _≼_; _≺_; Ev; out; skip; end; EmissionSet; Ended)
open import simultaneous.Readings using (instantOf)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊑-snoc⁺)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import simultaneous.Horizon using (Tag; free; held; module Cuts; past-child)
open import simultaneous.HorizonTree using (Cut; bd)
open import simultaneous.HorizonJoin using (module MergeJ; module JoinBd)
open JoinBd using (outerB; laneB; laneH)
open import simultaneous.HorizonJoinPair using (module JoinPair)
open import simultaneous.HorizonConn using (Mark; mark; mark-q; retarget)
open import simultaneous.TreeBounded using (tree-bounded; admits-trig)
open import simultaneous.CutParts using (merge-tr→; merge-tr←)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; anyᵇ; values; afterL; lanes; module BoundedL; module ExhaustL; module Order)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.TableCorr using (Rel; Corr; Across; Stable; LeadClear; across-of; off*-mark)
open import simultaneous.TableKit using (TR; Got) renaming (M to Matches)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.InstEmit using (valuesOf)
open import Function using (_⇔_)
open import simultaneous.HorizonCorr using (module Inter; Own; OwnPut; Btw; PB; module Sub)
open import simultaneous.TableEnv using (Ren; got-ok; pin-ok; after-ok; pin-after-ok; up; Linked; Aligned; EnvR; maps; lw; lw*; den;
  Admits; tab-func; admits-row; dbd; SameBd; same-bd; Out; wk; _⊕ˡ_)
open JoinBd using (outerB; laneB; laneH)


open import Relation.Nullary using (¬_)
open import denotation.EmissionSet using (DenEnv; Den)
import denotation.EmissionSet as ES
open import denotation.Laws.Cut using (capprox)
open import simultaneous.TableFlat using (module Flat; module Vals)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; laneSrc; closer; combined; trackers)

-- Apart from a position, a row and its descendants order alike against
-- it.
past-ext : ∀ {o b} l ls → ¬ o ⊑ b → (o ≺ b → (o ⊕ˡ (l ∷ ls)) ≺ b) × ((o ⊕ˡ (l ∷ ls)) ≺ b → o ≺ b)
past-ext {o} {b} l []         no = (λ lt → past-child l lt no) , λ lt → ≺-trans {o} {o ⊕ [ l ]} {b} (≺-ext o []) lt
past-ext {o} {b} l (l′ ∷ ls) no =
  let (fw , bw) = past-ext {o ⊕ [ l ]} {b} l′ ls (λ h → no (⊑-trans (⊑-snoc⁺ o) h))
  in (λ lt → fw (past-child l lt no)) , (λ lt → ≺-trans {o} {o ⊕ [ l ]} {b} (≺-ext o []) (bw lt))

-- Two orderings chained.
chain : ∀ {k z w w′ z*} → (k ≺ z → w ≺ z*) × (w ≺ z* → k ≺ z) → (w ≺ z* → w′ ≺ z*) × (w′ ≺ z* → w ≺ z*)
      → (k ≺ z → w′ ≺ z*) × (w′ ≺ z* → k ≺ z)
chain (f , g) (f′ , g′) = (λ lt → f′ (f lt)) , (λ lt → g (g′ lt))

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

      -- WHAT THE MERGE'S CORRESPONDENCE OWES, field by field.
      MImaged : ℕ → Pos → Ev B → Set
      MImaged N k e = Σ (Ev (IE B)) λ e′ → TR (Q′ N) (φ′ N k) e′ × Matches e e′

      MHomed : ℕ → Pos → Set
      MHomed N k = instantOf k ≡ instantOf p
                 ⊎ Σ Pos λ k₀ → Σ (Ev B) λ e₀ → TR (P′ N) k₀ e₀ × Unpinned e₀ × ¬ Late′ N k₀ × MImaged N k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

      MPutAt : ℕ → Pos → Set
      MPutAt N k = (Σ Pos λ l → Σ (Ev (IE B)) λ e′ → TR (Q′ N) l e′ × Put′ N k l) × MHomed N k

      MLeads : ℕ → Pos → Set
      MLeads N k = ∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

      MPinAt : ℕ → Pos → Pos → Set
      MPinAt N k r = (Σ Pos λ l → Σ Pos λ p′ → TR (Q′ N) l (pin p′) × Put′ N k l
                       × (∀ {k₀ a} → TR (P′ N) k₀ (out a) → φ′ N k₀ ≺ p′ → k₀ ≺ r)) × MHomed N k

      postulate
        mg-row→       : ∀ N {k e} → TR (P′ N) k e → Unpinned e → (MImaged N k e × ¬ Late′ N k) ⊎ (e ≡ skip × MPutAt N k)
        mg-late-put   : ∀ N {k e} → Late′ N k → TR (P′ N) k e → e ≡ skip × MPutAt N k
        mg-pin→       : ∀ N {k r} → TR (P′ N) k (pin r) → Live (TR (P′ N)) k → MPinAt N k r
        mg-put-before : ∀ N {k l k′ e′} → TR (P′ N) k skip → Put′ N k l → TR (P′ N) k′ e′ → Unpinned e′ → ¬ Late′ N k′ → k ≺ k′ → l ≼ φ′ N k′
        mg-pin-before : ∀ N {k r l k′ e′} → TR (P′ N) k (pin r) → Put′ N k l → TR (P′ N) k′ e′ → Unpinned e′ → ¬ Late′ N k′ → k ≺ k′ → l ≼ φ′ N k′
        mg-shown←     : ∀ N {l e′} → TR (Q′ N) l e′ → Shown (One valuesOf) e′
                      → Σ Pos λ k → Σ (Ev B) λ e → l ≡ φ′ N k × TR (P′ N) k e × Unpinned e × ¬ Late′ N k × Matches e e′
        mg-place      : ∀ N {m e′} → TR (Q′ N) m e′ → Live (TR (Q′ N)) m
                      → instantOf m ≡ instantOf c₁
                      ⊎ Σ Pos λ k → Σ (Ev B) λ e → TR (P′ N) k e × Unpinned e × ¬ Late′ N k × MImaged N k e × (φ′ N k ≼ m ⊎ MLeads N k) × instantOf (φ′ N k) ≡ instantOf m
        mg-mono       : ∀ N {k k′ e e′} → TR (P′ N) k e → TR (P′ N) k′ e′ → Unpinned e → Unpinned e′ → ¬ Late′ N k → ¬ Late′ N k′ → k ≺ k′ → φ′ N k ≺ φ′ N k′
        mg-inst       : ∀ N {k k′ e e′} → TR (P′ N) k e → TR (P′ N) k′ e′ → Unpinned e → Unpinned e′ → ¬ Late′ N k → ¬ Late′ N k′
                      → (instantOf (φ′ N k) ≡ instantOf (φ′ N k′) ⇔ instantOf k ≡ instantOf k′)
        mg-home       : ∀ N {k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → (instantOf (φ′ N k) ≡ instantOf c₁ ⇔ instantOf k ≡ instantOf p)

      mg-corr : ∀ N → Corr p c₁ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))
      mg-corr N = record
        { row→ = mg-row→ N ; late-put = mg-late-put N ; pin→ = mg-pin→ N ; put-before = mg-put-before N ; pin-before = mg-pin-before N
        ; shown← = mg-shown← N ; place = mg-place N ; mono = mg-mono N ; inst = mg-inst N ; home = mg-home N }

      postulate
        mg-in-bk       : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
        mg-after-φ     : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₁ ≼ φ′ N k

      -- THE MERGE'S HANGS: its outer's boundaries, and each running
      -- lane's; each partnered with its image's.  The merge is the join of
      -- its parts on both sides (`merge-tr→`), its boundaries the tree's,
      -- so its pair is `JoinPair`'s over the parts' pairs at the tree's
      -- boundaries, restricted to the rows the listing shows.
      oM oM* : ℕ → EmissionSet A
      oM  = Cut n s ρ p
      oM* = Cut n eachS ρ*c c₁

      LM : A → Pos → ℕ → EmissionSet B
      LM a q = Cut n (f a) ρ q

      LM* : A → Pos → ℕ → EmissionSet (IE B)
      LM* a q = Cut n (laneˢ (λ k′ c′ → laneSrc ρι⁴ (f a) k′ c′)) ρ*c q

      BdoM BdoM* : ℕ → Pos → Tag → Set
      BdoM  N = bd n s ρ uρ (dbd (lw env)) p N
      BdoM* N = bd n eachS ρ*c uρ*c (dbd Dc) c₁ N

      BdLM BdLM* : ℕ → Pos → A → Pos → Tag → Set
      BdLM  N q a = bd n (f a) ρ uρ (dbd (lw env)) (q ⊕ [ ix 1 ]) N
      BdLM* N q a = bd n (laneˢ (λ k′ c′ → laneSrc ρι⁴ (f a) k′ c′)) ρ*c uρ*c (dbd Dc) (q ⊕ [ ix 1 ]) N

      -- THE OUTER'S MAP: a value at its elaborated value, `each`'s row
      -- under the shared hot's; any other row where the merge puts it.
      φo : ℕ → Pos → Pos
      φo N k = if isVal N k then val* N k else φ′ N k

      -- The source's elaborated boundaries, at the share's subscription.
      BdS* : ℕ → Pos → Tag → Set
      BdS* N = bd n (elab (wk ρι) s) ρ*s uρ*s (dbd Ds) sp* N

      -- THE SHARE HANGS WHERE ITS CHILD DOES, at the child's queued
      -- subscription: the concat's outer and blocker hang nowhere.
      postulate
        share-bd→ : ∀ N {b g} → bd n shared ρ*s uρ*s (dbd Ds) shp N b g → BdS* N b g
        share-bd← : ∀ N {b g} → BdS* N b g → bd n shared ρ*s uρ*s (dbd Ds) shp N b g

      -- `each` hangs as its shared hot does.
      mg-each-bd→ : ∀ N {b g} → BdoM* N b g → BdS* N b g
      mg-each-bd→ N (outerB x)      = share-bd→ N x
      mg-each-bd→ N (laneB _ _ () _)
      mg-each-bd→ N (laneH _ _ () _)

      mg-each-bd← : ∀ N {b g} → BdS* N b g → BdoM* N b g
      mg-each-bd← N y = outerB (share-bd← N y)

      module JP (N : ℕ) = JoinPair (MergeJ.Lane oM LM N) (oM N) (Ended (oM N)) (λ _ → ⊤) (λ _ _ → ⊥)
        (MergeJ.Lane oM* LM* N) (oM* N) (Ended (oM* N)) (λ _ → ⊤) (λ _ _ → ⊥)
        (BdoM N) (BdLM N) (BdoM* N) (BdLM* N) (λ _ → ⊥) (λ _ _ → ⊥)
        (φo N) (φ′ N) (λ _ _ → φ′ N) (Late′ N) (Late′ N) (λ _ _ → Late′ N) (Put′ N) (Put′ N) (λ _ _ → Put′ N)

      postulate
        -- a value lies where the source has one, and only there
        mg-is-val  : ∀ N {q a} → oM N q (out a) → isVal N q ≡ true
        mg-not-val : ∀ N {k e} → oM N k e → (∀ {a} → ¬ e ≡ out a) → isVal N k ≡ false
        -- an outer row late for the source is late for the merge
        mg-late-src : ∀ N {k e} → oM N k e → Rel.Late (Out.rel Os) N k → Late′ N k
        -- an outer skip or end read through the shared hot
        mg-φ-src : ∀ N {k e} → oM N k e → (∀ {a} → ¬ e ≡ out a) → Unpinned e → φ′ N k ≡ srcφ N k
        mg-o-pb  : ∀ N {z z*} → Mark (BdoM N) z → Mark (BdS* N) z*
                 → Btw (Own (oM N) (Rel.Late (Out.rel Os) N)) (Rel.φ (Out.rel Os) N) z z*
                 → PB (OwnPut (oM N) (Rel.Put (Out.rel Os) N)) z z* → JP.IO.PutBefore N z z*
        -- the lane's pair at the tree's boundaries
        mg-lane-bcorr  : ∀ N {q a a*} → oM N q (out a) → oM* N (φo N q) (out a*) → JP.IL.BCorr N q a (φo N q) a*
        -- every value of the elaborated outer is a value's image
        mg-val←  : ∀ N {q* a*} → oM* N q* (out a*) → Σ Pos λ q → Σ A λ a → oM N q (out a) × q* ≡ φo N q
        -- a value's marker under its image
        mg-φ-val : ∀ N {q a} → oM N q (out a) → φ′ N (q ⊕ [ ix 0 ]) ≡ φo N q ⊕ [ ix 0 ]
        mg-nl-out : ∀ N {q a} → oM N q (out a) → ¬ Late′ N q
        mg-put-split : ∀ N {k e l} → JP.J.JoinT N k e → Put′ N k l
                     → (Σ (Ev A) λ e′ → oM N k e′ × Put′ N k l)
                     ⊎ (Σ Pos λ q → Σ A λ a → Σ (Ev B) λ e′ → oM N q (out a) × MergeJ.Lane oM LM N q a k e′ × Put′ N k l)
        mg-img : ∀ N {k} → Own (JP.J.JoinT N) (Late′ N) k → Σ (Ev (IE B)) (JP.J*.JoinT N (φ′ N k))
        -- each part's rows cut the other parts' marks alike
        mg-outer-lane : ∀ N {z z*} → Mark (BdoM N) z → Mark (BdoM* N) z* → JP.IO.Between N z z* → JP.Lanes N z z*
        mg-outer-lane-put : ∀ N {z z*} → Mark (BdoM N) z → Mark (BdoM* N) z* → JP.IO.PutBefore N z z* → JP.LanesP N z z*
        mg-lane-outer : ∀ N {q a a* z z*} → oM N q (out a) → oM* N (φo N q) (out a*) → Mark (BdLM N q a) z → Mark (BdLM* N (φo N q) a*) z*
                      → JP.IL.Between N q a (φo N q) a* z z* → Btw (Own (oM N) (Late′ N)) (φo N) z z*
        mg-lane-outer-put : ∀ N {q a a* z z*} → oM N q (out a) → oM* N (φo N q) (out a*) → Mark (BdLM N q a) z → Mark (BdLM* N (φo N q) a*) z*
                          → JP.IL.PutBefore N q a (φo N q) a* z z* → PB (OwnPut (oM N) (Put′ N)) z z*
        mg-lane-lane : ∀ N {q a a* z z*} → oM N q (out a) → oM* N (φo N q) (out a*) → Mark (BdLM N q a) z → Mark (BdLM* N (φo N q) a*) z*
                     → JP.IL.Between N q a (φo N q) a* z z*
                     → ∀ {q′ a′} → oM N q′ (out a′) → ¬ q′ ≡ q → Btw (Own (MergeJ.Lane oM LM N q′ a′) (Late′ N)) (φ′ N) z z*
        mg-lane-lane-put : ∀ N {q a a* z z*} → oM N q (out a) → oM* N (φo N q) (out a*) → Mark (BdLM N q a) z → Mark (BdLM* N (φo N q) a*) z*
                         → JP.IL.PutBefore N q a (φo N q) a* z z*
                         → ∀ {q′ a′} → oM N q′ (out a′) → ¬ q′ ≡ q → PB (OwnPut (MergeJ.Lane oM LM N q′ a′) (Put′ N)) z z*

      -- A value's image is its value's row in the elaborated outer.
      φo-val : ∀ N {q a} → oM N q (out a) → φo N q ≡ val* N q
      φo-val N {q} x = cong (λ c → if c then val* N q else φ′ N q) (mg-is-val N x)

      mg-val→ : ∀ N {q a} → oM N q (out a) → Σ A λ a* → oM* N (φo N q) (out a*)
      mg-val→ N {a = a} x = a , subst (λ z → oM* N z (out a)) (sym (φo-val N x)) (each-row x)

      -- The merge reads its outer's other rows where the outer's map does.
      mg-φ-outer : ∀ N {k e} → oM N k e → (∀ {a} → ¬ e ≡ out a) → φ′ N k ≡ φo N k
      mg-φ-outer N {k} x nv = cong (λ c → if c then val* N k else φ′ N k) (sym (mg-not-val N x nv))

      -- An image of the source's values lies over no mark of its
      -- elaborated boundaries.
      module TBs = Cuts.Bounded (tree-bounded n s* ρ*s uρ*s Ds sp* (admits-trig n uρ* (lw* env) p* ad*))

      src-off* : ∀ N {z* y e} → Mark (BdS* N) z* → Cut n s* ρ*s sp* N y e → ¬ y ⊑ z*
      src-off* N (_ , _ , bd , inj₁ refl) y = TBs.gap bd y
      src-off* N (_ , _ , bd , inj₂ refl) y yr = TBs.gap bd y (⊑-trans yr (TBs.held-under bd))

      -- Nor does a skip of the source's.
      mg-skip-off* : ∀ N {z* k} → Mark (BdS* N) z* → oM N k skip → ¬ Rel.Late (Out.rel Os) N k → ¬ Rel.φ (Out.rel Os) N k ⊑ z*
      mg-skip-off* N (b , g , bd , eq) x nlo = off*-mark (Out.rel Os) (skip , x , tt , nlo) (b , g , SameBd.from (Out.bd-pin* Os) bd , eq)

      val-img : ∀ N {k a} → oM N k (out a) → Σ (Ev (IE A)) (Cut n s* ρ*s sp* N (Rel.φ (Out.rel Os) N k))
      val-img N x = [ (λ { ((e′ , y , _) , _) → e′ , y }) , (λ { (() , _) }) ]′ (Corr.row→ (Rel.corr (Out.rel Os) N) x tt)

      -- THE SOURCE'S END, read through the shared hot, which ends where the
      -- source does: below the image of an end, which lies over no mark.
      mg-o-end : ∀ N {z z* k} → Mark (BdoM N) z → Mark (BdS* N) z*
               → Btw (Own (oM N) (Rel.Late (Out.rel Os) N)) (Rel.φ (Out.rel Os) N) z z*
               → oM N k end → ¬ Late′ N k → (k ≺ z → φ′ N k ≺ z*) × (φ′ N k ≺ z* → k ≺ z)
      mg-o-end N {z} {z*} {k} mz (b , g , bd , eq) btw x nl =
        retarget {k} {z} {z*} {srcφ N k} {φ′ N k} (mg-φ-src N x (λ ()) tt)
          (chain {k} {z} {RO.φ N k} {srcφ N k} {z*} (btw (end , x , tt , nlo))
            (past-ext {RO.φ N k} {z*} (sub c₁) [] (off*-mark (Out.rel Os) (end , x , tt , nlo) (b , g , SameBd.from (Out.bd-pin* Os) bd , eq))))
        where
          module RO = Rel (Out.rel Os)
          nlo = λ l → nl (mg-late-src N x l)

      -- THE MERGE'S OUTER ROWS cut a pair of the source's boundaries alike
      -- where the source's rows do: a value at its elaborated value, a
      -- skip through the shared hot, each a descendant of the source's
      -- image, which lies over no mark.
      mg-o-btw : ∀ N {z z*} → Mark (BdoM N) z → Mark (BdS* N) z*
               → Btw (Own (oM N) (Rel.Late (Out.rel Os) N)) (Rel.φ (Out.rel Os) N) z z* → JP.IO.Between N z z*
      mg-o-btw N mz mz* btw (inj₂ ())
      mg-o-btw N mz mz* btw (inj₁ (pin _ , _ , () , _))
      mg-o-btw N {z} {z*} mz mz* btw {k} (inj₁ (out a , x , _ , nl)) =
        retarget {k} {z} {z*} {val* N k} {φo N k} (φo-val N x)
          (chain {k} {z} {RO.φ N k} {val* N k} {z*} (btw (out a , x , tt , λ l → nl (mg-late-src N x l)))
            (past-ext {RO.φ N k} {z*} (sub c₁) (ix 1 ∷ ix 0 ∷ []) (src-off* N mz* (proj₂ (val-img N x)))))
        where module RO = Rel (Out.rel Os)
      mg-o-btw N {z} {z*} mz mz* btw {k} (inj₁ (skip , x , _ , nl)) =
        retarget {k} {z} {z*} {srcφ N k} {φo N k} (trans (sym (mg-φ-outer N x (λ ()))) (mg-φ-src N x (λ ()) tt))
          (chain {k} {z} {RO.φ N k} {srcφ N k} {z*} (btw (skip , x , tt , nlo))
            (past-ext {RO.φ N k} {z*} (sub c₁) [] (mg-skip-off* N mz* x nlo)))
        where
          module RO = Rel (Out.rel Os)
          nlo = λ l → nl (mg-late-src N x l)
      mg-o-btw N {z} {z*} mz mz* btw {k} (inj₁ (end , x , _ , nl)) =
        retarget {k} {z} {z*} {φ′ N k} {φo N k} (sym (mg-φ-outer N x (λ ()))) (mg-o-end N mz mz* btw x nl)

      -- THE OUTER'S PAIR: the source's, at the tree's boundaries on both
      -- sides, the elaborated one's through `each`.
      mg-outer-bcorr : ∀ N → JP.IO.BCorr N
      mg-outer-bcorr N = record { to = to′ ; from = from′ }
        where
          RO = Out.rel Os
          C  = Rel.bcorr RO N
          module C = Inter.BCorr C

          tagTo : ∀ {b b* g g*} → BdoM N b g → BdS* N b* g*
                → Inter.TagTo (Own (oM N) (Rel.Late RO N)) (Rel.φ RO N) (OwnPut (oM N) (Rel.Put RO N)) (Rel.Bd RO N) (Rel.Bd* RO N) g g*
                → JP.IO.TagTo N g g*
          tagTo _ _ Inter.plain-free         = Inter.plain-free
          tagTo x y (Inter.both-held btw)    = Inter.both-held (mg-o-btw N (mark-q x) (mark-q y) btw)

          tagFrom : ∀ {b b* g g*} → BdoM N b g → BdS* N b* g*
                  → Inter.TagFrom (Own (oM N) (Rel.Late RO N)) (Rel.φ RO N) (OwnPut (oM N) (Rel.Put RO N)) (Rel.Bd RO N) (Rel.Bd* RO N) g g*
                  → JP.IO.TagFrom N g g*
          tagFrom _ _ Inter.elab-free        = Inter.elab-free
          tagFrom x y (Inter.both-held btw)  = Inter.both-held (mg-o-btw N (mark-q x) (mark-q y) btw)

          to′ : ∀ {b g} → BdoM N b g → Σ Pos λ b* → Σ Tag λ g* → BdoM* N b* g* × JP.IO.Between N b b* × JP.IO.TagTo N g g*
          to′ x =
            let (b* , g* , y , btw , tg) = C.to (SameBd.from (Out.bd-pin Os) x)
                y′ = SameBd.to (Out.bd-pin* Os) y
            in b* , g* , mg-each-bd← N y′ , mg-o-btw N (mark x) (mark y′) btw , tagTo x y′ tg

          from′ : ∀ {b* g*} → BdoM* N b* g* → Σ Pos λ b → Σ Tag λ g → BdoM N b g × JP.IO.Between N b b* × JP.IO.PutBefore N b b* × JP.IO.TagFrom N g g*
          from′ y =
            let y′ = mg-each-bd→ N y
                (b , g , x , btw , pb , tg) = C.from (SameBd.from (Out.bd-pin* Os) y′)
                x′ = SameBd.to (Out.bd-pin Os) x
            in b , g , x′ , mg-o-btw N (mark x′) (mark y′) btw , mg-o-pb N (mark x′) (mark y′) btw pb , tagFrom x′ y′ tg

      -- A value's row carries one value.
      mg-o-func : ∀ N {q a a′} → oM N q (out a) → oM N q (out a′) → a ≡ a′
      mg-o-func N x x′ with tab-func n s uρ (lw env) ad x x′
      ... | refl = refl

      -- A boundary of a running lane is the merge's.
      mg-laneB : ∀ {N q a b g} → oM N q (out a) → BdLM N q a b g → jbd (mergeᶠ nothing) N b g
      mg-laneB {g = free}   x b₀ = laneB x tt b₀ (λ ())
      mg-laneB {g = held r} x b₀ = laneH x tt b₀ (λ ())

      mg-laneB* : ∀ {N q a b g} → oM* N q (out a) → BdLM* N q a b g → jbd* (mergeᶠ nothing) N b g
      mg-laneB* {g = free}   x b₀ = laneB x tt b₀ (λ ())
      mg-laneB* {g = held r} x b₀ = laneH x tt b₀ (λ ())

      -- No merge row lies over the merge's boundaries.
      mg-gap : ∀ {N b g y e} → jbd (mergeᶠ nothing) N b g → JP.J.JoinT N y e → ¬ y ⊑ b
      mg-gap {N} b₀ y = Cuts.Bounded.gap (jtree (mergeᶠ nothing)) b₀ (merge-tr← n f s uρ p {N} y)

      mg-gap* : ∀ {N b g y e} → jbd* (mergeᶠ nothing) N b g → JP.J*.JoinT N y e → ¬ y ⊑ b
      mg-gap* {N} b₀ y = Cuts.Bounded.gap (jbounded* (mergeᶠ nothing)) b₀ (merge-tr← n (λ a → laneˢ (λ k′ c′ → laneSrc ρι⁴ (f a) k′ c′)) eachS {ρ*c} uρ*c c₁ {N} y)

      -- No merge row lies over a connect a boundary waits on: the
      -- boundary lies under it, and no row over the boundary.
      -- A put skip is imaged as any row is, at a row of the elaborated
      -- merge, so over no boundary.
      mg-put-off* : ∀ {N y l b g} → TR (P′ N) y skip → ¬ Late′ N y → Put′ N y l → jbd* (mergeᶠ nothing) N b g → ¬ φ′ N y ⊑ b
      mg-put-off* {N} x nl _ b₀ = mg-gap* b₀ (proj₂ (mg-img N (skip , merge-tr→ n f s uρ p (pd-sub {mergeᶠ nothing} {N} x) , tt , nl)))

      mg-held : ∀ {N b r y e} → jbd (mergeᶠ nothing) N b (held r) → JP.J.JoinT N y e → ¬ y ⊑ r
      mg-held {N} b₀ y yr = mg-gap b₀ y (⊑-trans yr (Cuts.Bounded.held-under (jtree (mergeᶠ nothing)) b₀))

      mg-held* : ∀ {N b r y e} → jbd* (mergeᶠ nothing) N b (held r) → JP.J*.JoinT N y e → ¬ y ⊑ r
      mg-held* {N} b₀ y yr = mg-gap* b₀ y (⊑-trans yr (Cuts.Bounded.held-under (jbounded* (mergeᶠ nothing)) b₀))

      mg-bcorr : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (jbd (mergeᶠ nothing) N) (jbd* (mergeᶠ nothing) N)
      mg-bcorr N = Sub.restrict {Row = Own (TR (P′ N)) (Late′ N)} {Row′ = JP.JRow N} {φ = φ′ N} {Puts = OwnPut (TR (P′ N)) (Put′ N)} {Puts′ = JP.JPut N}
                     {Bd = jbd (mergeᶠ nothing) N} {Bd* = jbd* (mergeᶠ nothing) N} row put
        (JP.Pair.corr N (mg-outer-bcorr N) (mg-val→ N) (mg-val← N) (λ _ _ → tt) (λ _ _ → tt) (mg-o-func N) (mg-lane-bcorr N)
          (mg-φ-outer N) (mg-φ-val N) (λ _ _ → refl) (λ ()) (λ ()) (mg-nl-out N) (λ l → l) (λ _ _ l → l)
          (mg-put-split N) (mg-img N)
          (λ b₀ → mg-gap (outerB b₀)) (λ b₀ → mg-gap* (outerB b₀)) (λ b₀ → mg-held (outerB b₀)) (λ b₀ → mg-held* (outerB b₀))
          (λ x b₀ → mg-gap (mg-laneB x b₀)) (λ x b₀ → mg-gap* (mg-laneB* x b₀))
          (λ x b₀ → mg-held (laneH x tt b₀ (λ ()))) (λ x b₀ → mg-held* (laneH x tt b₀ (λ ())))
          (λ {q} {a} x b₀ → Cuts.Bounded.held-in (tree-bounded n (f a) ρ uρ (lw env) (q ⊕ [ ix 1 ]) (admits-row n s uρ (lw env) ad x)) b₀)
          (λ {q} {a} x b₀ → Cuts.Bounded.held-in (tree-bounded n (laneˢ (λ k′ c′ → laneSrc ρι⁴ (f a) k′ c′)) ρ*c uρ*c Dc (q ⊕ [ ix 1 ]) (admits-row n eachS uρ*c Dc ad₁ x)) b₀)
          (λ _ _ _ ()) (λ _ _ _ ()) (λ ()) (λ ())
          (mg-outer-lane N) (mg-outer-lane-put N) (mg-lane-outer N) (mg-lane-outer-put N) (mg-lane-lane N) (mg-lane-lane-put N))
        where
          row : ∀ {k} → Own (TR (P′ N)) (Late′ N) k → JP.JRow N k
          row (e , x , un , nl) = inj₁ (e , merge-tr→ n f s uρ p (pd-sub {mergeᶠ nothing} {N} x) , un , nl)

          put : ∀ {k l} → OwnPut (TR (P′ N)) (Put′ N) k l → JP.JPut N k l
          put ((e , x) , pl) = inj₁ ((e , merge-tr→ n f s uρ p (pd-sub {mergeᶠ nothing} {N} x)) , pl)

      -- THE MERGE CLEARS ACROSS CUTS AS ITS PARTS DO: a boundary of the
      -- merge is its outer's or a running lane's, and the image's clearance
      -- restricts to the image's outer and to the image value's lane.
      ClearO ClearO* : ℕ → Pos → Set
      ClearO  N k = ∀ {b g} → BdoM N b g → k ≺ b
      ClearO* N k = ∀ {b g} → BdoM* N b g → k ≺ b

      ClearL : ℕ → Pos → A → Pos → Set
      ClearL N q a k = ∀ {b g} → BdLM N q a b g → k ≺ b

      ClearL* : ℕ → Pos → A → Pos → Set
      ClearL* N q a k = ∀ {b g} → BdLM* N q a b g → k ≺ b

      postulate
        mg-outer-back : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → ¬ Late′ N′ k → ClearO* N (φ′ N′ k) → ClearO N k
        mg-lane-back  : ∀ {N N′ k e q a a*} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → ¬ Late′ N′ k
                      → oM N q (out a) → oM* N (val* N q) (out a*) → ClearL* N (val* N q) a* (φ′ N′ k) → ClearL N q a k
        mg-outer-put  : ∀ {N N′ k e l} → N ≤ N′ → TR (P′ N′) k e → Put′ N′ k l → ClearO* N l → ClearO N k
        mg-lane-put   : ∀ {N N′ k e l q a a*} → N ≤ N′ → TR (P′ N′) k e → Put′ N′ k l
                      → oM N q (out a) → oM* N (val* N q) (out a*) → ClearL* N (val* N q) a* l → ClearL N q a k
        mg-outer-lead : ∀ {N k e m e*} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k
                      → (∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
                      → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → ClearO* N m → ClearO N k
        mg-lane-lead  : ∀ {N k e m e* q a a*} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k
                      → (∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
                      → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k)
                      → oM N q (out a) → oM* N (val* N q) (out a*) → ClearL* N (val* N q) a* m → ClearL N q a k

      mg-clear : ∀ {N k} → ClearO N k → (∀ {q a a*} → oM N q (out a) → oM* N (val* N q) (out a*) → ClearL N q a k)
               → Cuts.Clear (λ M → TR (P′ M)) (jbd (mergeᶠ nothing)) N k
      mg-clear     co cl (outerB b₀)      = co b₀
      mg-clear co cl (laneB x _ b₀ _) = cl x (each-row x) b₀
      mg-clear co cl (laneH x _ b₀ _) = cl x (each-row x) b₀

      mg-across : Across (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Put′ Late′ (jbd (mergeᶠ nothing)) (jbd* (mergeᶠ nothing))
      mg-across = record
        { back-clear = λ {N} {N′} {k} {e} le x un nl cl* → mg-clear {N} {k}
            (mg-outer-back {N} {N′} {k} {e} le x un nl (λ b₀ → cl* (outerB b₀)))
            (λ {q} {a} {a*} x₀ x₀* → mg-lane-back {N} {N′} {k} {e} {q} {a} {a*} le x un nl x₀ x₀* (λ b₀ → cl* (mg-laneB* x₀* b₀)))
        ; put-clear  = λ {N} {N′} {k} {e} {l} le x pl cl* → mg-clear {N} {k}
            (mg-outer-put {N} {N′} {k} {e} {l} le x pl (λ b₀ → cl* (outerB b₀)))
            (λ {q} {a} {a*} x₀ x₀* → mg-lane-put {N} {N′} {k} {e} {l} {q} {a} {a*} le x pl x₀ x₀* (λ b₀ → cl* (mg-laneB* x₀* b₀)))
        ; lead-clear = λ {N} {k} {e} {m} {e*} x un nl ld mq ie cl* → mg-clear {N} {k}
            (mg-outer-lead {N} {k} {e} {m} {e*} x un nl ld mq ie (λ b₀ → cl* (outerB b₀)))
            (λ {q} {a} {a*} x₀ x₀* → mg-lane-lead {N} {k} {e} {m} {e*} {q} {a} {a*} x un nl ld mq ie x₀ x₀* (λ b₀ → cl* (mg-laneB* x₀* b₀))) }

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
        ; Bd = jbd (mergeᶠ nothing) ; Bd* = jbd* (mergeᶠ nothing) ; bounded = jbounded (mergeᶠ nothing) ; bounded* = jbounded* (mergeᶠ nothing) ; bcorr = mg-bcorr ; across = mg-across ; skip-off* = mg-put-off* }

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
        cc-stable : Stable (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Put′ Late′ (jbd (mergeᶠ (just k))) (jbd* (mergeᶠ (just k)))
        cc-lead   : LeadClear (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Late′ (jbd (mergeᶠ (just k))) (jbd* (mergeᶠ (just k)))
        -- every row not late imaged at a row of the elaborated join
        cc-img : ∀ N {y} → Own (TR (P′ N)) (Late′ N) y → Σ (Ev (IE B)) (TR (Q′ N) (φ′ N y))

      -- A put skip is imaged as any row is, so over no boundary.
      cc-put-off* : ∀ {N y l b g} → TR (P′ N) y skip → ¬ Late′ N y → Put′ N y l → jbd* (mergeᶠ (just k)) N b g → ¬ φ′ N y ⊑ b
      cc-put-off* x nl _ b₀ = Cuts.Bounded.gap (jbounded* (mergeᶠ (just k))) b₀ (proj₂ (cc-img _ (skip , x , tt , nl)))

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
        ; Bd = jbd (mergeᶠ (just k)) ; Bd* = jbd* (mergeᶠ (just k)) ; bounded = jbounded (mergeᶠ (just k)) ; bounded* = jbounded* (mergeᶠ (just k)) ; bcorr = cc-bcorr ; across = across-of (λ N → cc-bcorr N) (cc-stable) (λ {N} → cc-lead {N}) ; skip-off* = cc-put-off* }

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
        sw-stable : Stable (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Put′ Late′ (jbd switchᶠ) (jbd* switchᶠ)
        sw-lead   : LeadClear (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Late′ (jbd switchᶠ) (jbd* switchᶠ)
        -- every row not late imaged at a row of the elaborated join
        sw-img : ∀ N {y} → Own (TR (P′ N)) (Late′ N) y → Σ (Ev (IE B)) (TR (Q′ N) (φ′ N y))

      -- A put skip is imaged as any row is, so over no boundary.
      sw-put-off* : ∀ {N y l b g} → TR (P′ N) y skip → ¬ Late′ N y → Put′ N y l → jbd* switchᶠ N b g → ¬ φ′ N y ⊑ b
      sw-put-off* x nl _ b₀ = Cuts.Bounded.gap (jbounded* switchᶠ) b₀ (proj₂ (sw-img _ (skip , x , tt , nl)))

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
        ; Bd = jbd switchᶠ ; Bd* = jbd* switchᶠ ; bounded = jbounded switchᶠ ; bounded* = jbounded* switchᶠ ; bcorr = sw-bcorr ; across = across-of (λ N → sw-bcorr N) (sw-stable) (λ {N} → sw-lead {N}) ; skip-off* = sw-put-off* }

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
        ex-stable : Stable (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Put′ Late′ (jbd exhaustᶠ) (jbd* exhaustᶠ)
        ex-lead   : LeadClear (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Late′ (jbd exhaustᶠ) (jbd* exhaustᶠ)
        -- every row not late imaged at a row of the elaborated join
        ex-img : ∀ N {y} → Own (TR (P′ N)) (Late′ N) y → Σ (Ev (IE B)) (TR (Q′ N) (φ′ N y))

      -- A put skip is imaged as any row is, so over no boundary.
      ex-put-off* : ∀ {N y l b g} → TR (P′ N) y skip → ¬ Late′ N y → Put′ N y l → jbd* exhaustᶠ N b g → ¬ φ′ N y ⊑ b
      ex-put-off* x nl _ b₀ = Cuts.Bounded.gap (jbounded* exhaustᶠ) b₀ (proj₂ (ex-img _ (skip , x , tt , nl)))

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
        ; Bd = jbd exhaustᶠ ; Bd* = jbd* exhaustᶠ ; bounded = jbounded exhaustᶠ ; bounded* = jbounded* exhaustᶠ ; bcorr = ex-bcorr ; across = across-of (λ N → ex-bcorr N) (ex-stable) (λ {N} → ex-lead {N}) ; skip-off* = ex-put-off* }

  flat-core : ∀ op → Core op
  flat-core (mergeᶠ nothing)  = λ Os Ls Lc al lk → Joins.MergeTab.rel′ Os Ls Lc al lk
  flat-core (mergeᶠ (just k)) = λ Os Ls Lc al lk → Joins.ConcatTab.rel′ Os Ls Lc k al lk
  flat-core switchᶠ           = λ Os Ls Lc al lk → Joins.SwitchTab.rel′ Os Ls Lc al lk
  flat-core exhaustᶠ          = λ Os Ls Lc al lk → Joins.ExhaustTab.rel′ Os Ls Lc al lk

  -- Every joiner's core hangs as its tree does.
  flat-core-pin : ∀ op Os Ls Lc (al : Aligned (maps env) ρ p p*) lk → SameBd (Rel.Bd (flat-core op Os Ls Lc al lk)) (jbd op)
  flat-core-pin (mergeᶠ nothing)  _ _ _ _ _ = same-bd
  flat-core-pin (mergeᶠ (just k)) _ _ _ _ _ = same-bd
  flat-core-pin switchᶠ           _ _ _ _ _ = same-bd
  flat-core-pin exhaustᶠ          _ _ _ _ _ = same-bd
