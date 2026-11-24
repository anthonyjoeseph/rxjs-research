{-# OPTIONS --guardedness #-}

-- A COMPLETION STEP OF THE COLD CLOSES WITH ITS END (`cold-cdclose`).
-- The completion's begin is rendered under the tag the cold's end hands
-- its place to, one step under that end; the tag's own end, a label
-- later, ends the concat there, so the merge, the scan and the whole.
-- Every part has ended by then: the outers under the subscription, the
-- cold at its end, the tick under the subscription, and every render, of
-- an earlier tick or under the subscription, or the completion's own,
-- whose name's step lies before the tag's end.  The instant makes few
-- rows at every layer, so each end is reached as the completion is.
module simultaneous.ColdEnd where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (T?)

open import Tree using (mergeᶠ; cold; of; map)
open import denotation.Position using (Pos; ix; last; cascade; _∙_; _⊕_; _≟ᵖ_; _<ᵖ_; root; instant; path)
open import denotation.Events using (Timeline; fresh; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; enter; Ev; out; end; at-end; on-out; on-skip; _≺_; _≼_; Reach; Dep;
  Ended; LaneOf; MapT; map-out; map-skip; map-pin; map-end; Truncate; module Op;
  module Joining; module Merge; module Scan; module Bounded; module Values)
open import denotation.Laws.Modulus using (≺-ext; ≼-split; ≼-refl; ≺→≼)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊑-refl; ⊕-assoc)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end-row)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.Truth using (instant-⊑)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; Tag; val; cdone; tick; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over)
open import simultaneous.Instants using (≺-instant; instant-≺; btw)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.ColdFew using (Fresh; fresh-⊑; fresh-self; fresh-past; ⊑₂; Place; f-end; Leaf; module Pair; Ticks; Tickless;
  Rendered; RZ; Mint; mint-in; rv-raw; O; o-row; module Core)
import simultaneous.ColdFew as CF
open import simultaneous.ColdShape using (module Shape; ROut; IsVal; lf-rows; lf-vals; lf-uniqs; lf-bes; fc-outs; fc-ends; fm-ticks; r-outs)
open import simultaneous.ColdBegin using (same-≺; rz; fm-backs)
open import simultaneous.ColdRuns using (B⁰)
open import simultaneous.ColdOrder using (⊕1-inj)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render; concatˢ; phase)

-- Before a position or at it.
aft? : ∀ c y → c ≺ y ⊎ y ≼ c
aft? c y with T? (c <ᵖ y)
... | yes h = inj₁ h
... | no h  = inj₂ h

-- A row past a reached row of its instant is reached, the instant making
-- few rows.
reach-on : ∀ {X} {t : EmissionSet X} {q y} {v : X} {e : Ev X} → Reach t q (out v)
         → Σ (List Pos) (λ ks → ∀ {k e′} → t k e′ → instant k ≡ instant q → k ∈ ks)
         → q ≺ y → instant q ≡ instant y → Reach t y e
reach-on {t = t} {q = q} {y} {e = e} (ks₁ , h) (ks₂ , g) qy iq = ks₁ ++ ks₂ , go
  where
    go : ∀ {k e′} → t k e′ → k ≺ y → Dep y e k e′ → k ∈ ks₁ ++ ks₂
    go {k} r ky _ with aft? k q
    ... | inj₁ kq = ∈-++⁺ˡ (h r kq tt)
    ... | inj₂ qk with ≼-split {q} {k} qk
    ...   | inj₁ qk′ = ∈-++⁺ʳ ks₁ (g r (btw q k y qk′ ky iq))
    ...   | inj₂ refl = ∈-++⁺ʳ ks₁ (g r refl)

-- A fired instant holds few rows of a part placed at few paths.
few-at : ∀ {Zs s I} → Fresh s I → ∀ {X} {t : EmissionSet X} → (∀ {y e} → t y e → Place Zs s y)
       → Σ (List Pos) λ ks → ∀ {k e′} → t k e′ → instant k ≡ I → k ∈ ks
few-at {Zs} {s} {I} f {t = t} pl = L.map (I ∙_) Zs , go
  where
    at : ∀ {y} → instant y ≡ I → path y ∈ Zs → y ∈ L.map (I ∙_) Zs
    at {y = _ ∙ _} refl m = ∈-map⁺ (_ ∙_) m

    go : ∀ {k e′} → t k e′ → instant k ≡ I → k ∈ L.map (I ∙_) Zs
    go r eq with pl r
    ... | inj₁ u       = ⊥-elim (fresh-self {s} (subst (Fresh s) (trans (sym eq) (instant-⊑ u)) f))
    ... | inj₂ (m , _) = at eq m

------------------------------------------------------------------------
-- The end, from the cold's parts

module Ends {A : Set} (Fc Fm : Bool → Den (Tag A)) (R : Bool × Tag A → Den (IE A))
  (fc-true  : ∀ s {y e} → enter (Fc true) s y e → CF.Place CF.One s y × Tickless e)
  (fc-false : ∀ s {y e} → enter (Fc false) s y e → (y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ]) × Tickless e)
  (fm-true  : ∀ s {y e} → enter (Fm true) s y e → enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) s y e)
  (fm-false : ∀ s {y e} → enter (Fm false) s y e → s ⊑ y × Ticks e)
  (r-in     : ∀ x s {y e} → enter (R x) s y e → Rendered s y)
  (r-begin  : ∀ x s {y n} → enter (R x) s y (out (instEmit (mark begin) n)) → CF.Late x)
  (lf-row   : ∀ s {y e} → enter (Fc true) s y e → Leaf s y e)
  (lf-val   : ∀ s {y v} → enter (Fc true) s y (out v) → IsVal v)
  (lf-uniq  : ∀ s {c c′} → enter (Fc true) s c end → enter (Fc true) s c′ end → c ≡ c′)
  (lf-be    : ∀ s {y e c} → enter (Fc true) s y e → enter (Fc true) s c end → y ≼ c)
  (fc-out   : ∀ s {y v} → enter (Fc false) s y (out v) → y ≡ s ⊕ [ ix 0 ] × v ≡ cdone)
  (fc-end   : ∀ s {y} → enter (Fc false) s y end → y ≡ s ⊕ [ last ])
  (fm-tick  : ∀ s → enter (Fm false) s (s ⊕ [ ix 0 ]) (out tick))
  (r-out    : ∀ x s {y v} → enter (R x) s y (out v) → ROut x s y v)
  (fm-back  : ∀ s {y e} → enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) s y e → enter (Fm true) s y e)
  (fc-fin   : ∀ s → enter (Fc false) s (s ⊕ [ last ]) end)
  (fm-fin   : ∀ s → enter (Fm false) s (s ⊕ [ last ]) end)
  (r-end    : ∀ x s → enter (R x) s (s ⊕ [ last ]) end) where

  open Core Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin using (S₁; Acc; Sc; Mg; acc-tag; read-late; step-few; mg-pl;
    module Cat)
  open Shape Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin lf-row lf-val lf-uniq lf-be fc-out fc-end fm-tick r-out
    using (L1; module Mgs; module Cat′)

  module At (p : Pos) where
    open Mgs p using (val-row; cd-row; not-under; pS; read-early; early-r; tick-r; step-before)
    open Bounded 1 Fc (O (S₁ p)) using (Starts; room; freed; queued; Sched; Indexed)
      renaming (Lane to CLane; Queued to CQueued; Done to CDone; JoinT to CJoinT)
    open Values (O (S₁ p)) using (Nth)
    open Pair (S₁ p) using (nth₀; nth₁)
    open Nths (O (S₁ p)) using (nth-val; nth-inj)
    open Cat (S₁ p) using (first-end; cat-pl)
    open Cat′ (S₁ p) using (lane₀)

    -- The whole, entered at `p`.
    Top : EmissionSet (IE A)
    Top = Truncate (Merge.JoinT R (Sc p))

    -- The scan's rows, placed.
    sc-pl′ : ∀ {y e} → Scan.ScanT phase (false , tick) (Mg p) y e → Place CF.Zc p y
    sc-pl′ (Scan.sval a)  = mg-pl p (proj₁ (acc-tag a))
    sc-pl′ (Scan.sstep x) = mg-pl p (proj₁ x)
    sc-pl′ (Scan.spin x)  = mg-pl p (proj₁ x)
    sc-pl′ (Scan.send x)  = mg-pl p (proj₁ x)

    -- The end at `c`, the cold having ended at `K ∙ []`.
    module Fin (T : ℕ) (e : Pos) (fK : Fresh (S₁ (S₁ p)) (cascade T e last)) (rc : L1 (S₁ p) (cascade T e last ∙ []) end) where

      fP : Fresh p (cascade T e last)
      fP = fresh-⊑ pS fK

      f1 : Fresh (S₁ p) (cascade T e last)
      f1 = fresh-⊑ (⊑₂ (S₁ p) (ix 0) (ix 1)) fK

      -- Under a position the instant is fresh for: before the end.
      past : ∀ {s x} → s ⊑ x → Fresh s (cascade T e last) → x ≼ (cascade T e last ∙ (ix 1 ∷ last ∷ []))
      past {s} {x} u f = ≺→≼ {x} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} (fresh-past {s} {x} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} u f)

      lt₀ : (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) ≺ (cascade T e last ∙ (ix 1 ∷ last ∷ []))
      lt₀ = same-≺ (cascade T e last) (ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ last ∷ []) tt

      -- The tag's lane, ended.
      tag-lane : ∀ {i} → Nth i (S₁ p ⊕ [ ix 1 ]) false → Starts i (S₁ p ⊕ [ ix 1 ]) (Sched i) (cascade T e last ∙ [ ix 1 ])
               → CLane (S₁ p ⊕ [ ix 1 ]) false (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
      tag-lane {i} nd st = i , _ , (nd , st) , (fc-fin (cascade T e last ∙ [ ix 1 ]) , same-≺ (cascade T e last) [ ix 1 ] (ix 1 ∷ last ∷ []) tt)

      -- The cold's lane, ended.
      cold-lane : CLane (S₁ p ⊕ [ ix 0 ]) true (cascade T e last ∙ []) end
      cold-lane = 0 , _ , (nth₀ , room (s≤s z≤n))
                , (rc , fresh-past {S₁ (S₁ p)} {S₁ (S₁ p)} {cascade T e last ∙ []} (⊑-refl (S₁ (S₁ p))) fK)

      -- No lane is subscribed past the end.
      q0 : ∀ {s″} → Starts 0 (S₁ p ⊕ [ ix 0 ]) [] s″ → s″ ≡ (cascade T e last ∙ (ix 1 ∷ last ∷ [])) ⊕ [ ix 1 ] → ⊥
      q0 (room _) eq = not-under (⊑-trans (⊑₂ p (ix 0) (ix 1)) (subst (S₁ p ⊑_) (⊕1-inj {S₁ p ⊕ [ ix 0 ]} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} {ix 1} eq) ([ ix 0 ] , refl))) fP
      q0 (freed () _) _
      q0 (queued () _ _ _ _) _

      q1 : ∀ {s″} → Starts 1 (S₁ p ⊕ [ ix 1 ]) (Sched 1) s″ → s″ ≡ (cascade T e last ∙ (ix 1 ∷ last ∷ [])) ⊕ [ ix 1 ] → ⊥
      q1 (room (s≤s ())) _
      q1 (freed _ _) eq = not-under (⊑-trans (⊑₂ p (ix 0) (ix 1)) (subst (S₁ p ⊑_) (⊕1-inj {S₁ p ⊕ [ ix 1 ]} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} {ix 1} eq) ([ ix 1 ] , refl))) fP
      q1 (queued {c₃} _ _ kc _ _) eq with lf-uniq _ rc (subst (λ z → L1 (S₁ p) z end) (⊕1-inj {c₃} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} {ix 1} eq) (first-end kc))
      ... | ()

      no-queue : CQueued (cascade T e last ∙ (ix 1 ∷ last ∷ [])) → ⊥
      no-queue (j , q , a , nq , st) with o-row (S₁ p) (nth-val nq)
      ... | inj₁ (refl , refl) with nth-inj nq nth₀
      ...   | refl = q0 st refl
      no-queue (j , q , a , nq , st) | inj₂ (refl , refl) with nth-inj nq nth₁
      ...   | refl = q1 st refl

      cat-done : ∀ {i} → Nth i (S₁ p ⊕ [ ix 1 ]) false → Starts i (S₁ p ⊕ [ ix 1 ]) (Sched i) (cascade T e last ∙ [ ix 1 ])
               → CDone (cascade T e last ∙ (ix 1 ∷ last ∷ []))
      cat-done nd st =
        ( _ , (of-end-row (S₁ p) 0 (true ∷ false ∷ []) , of-reach (S₁ p) 0 (true ∷ false ∷ []) {S₁ p ⊕ [ last ]} {end})
        , past (⊑-trans (⊑₂ p (ix 0) (ix 1)) ([ last ] , refl)) fP)
        , λ x _ _ _ → cl (o-row (S₁ p) x)
        where
          cl : ∀ {q a} → (q ≡ S₁ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ S₁ p ⊕ [ ix 1 ] × a ≡ false)
             → Ended (CLane q a) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
          cl (inj₁ (refl , refl)) = _ , cold-lane
            , ≺→≼ {cascade T e last ∙ []} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} (same-≺ (cascade T e last) [] (ix 1 ∷ last ∷ []) tt)
          cl (inj₂ (refl , refl)) = _ , tag-lane nd st , ≼-refl {cascade T e last ∙ (ix 1 ∷ last ∷ [])}

      mg-done : enter (Fm true) (S₁ p) (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
              → Merge.Done Fm (O p) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
      mg-done ct =
        ( _ , (of-end-row p 0 (true ∷ false ∷ []) , of-reach p 0 (true ∷ false ∷ []) {p ⊕ [ last ]} {end}) , past ([ last ] , refl) fP)
        , λ x _ _ _ → ml (o-row p x)
        where
          ml : ∀ {q a} → (q ≡ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ p ⊕ [ ix 1 ] × a ≡ false)
             → Ended (LaneOf Fm q a) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
          ml (inj₁ (refl , refl)) = _ , (ct , fresh-past {S₁ p} {S₁ p} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} (⊑-refl (S₁ p)) f1)
                                  , ≼-refl {cascade T e last ∙ (ix 1 ∷ last ∷ [])}
          ml (inj₂ (refl , refl)) = _ , (fm-fin ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) , ≺-ext ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) {last} [])
                                  , past (⊑-trans (⊑₂ p (ix 1) (ix 1)) ([ last ] , refl)) fP

      -- Every render has ended by the end.
      lc : ∀ x {q} → Acc p q x → ((q ⊕ [ ix 1 ]) ⊕ [ last ]) ≼ (cascade T e last ∙ (ix 1 ∷ last ∷ []))
      lc (false , val a) {q} ac = past (early-r {q} {[ last ]} (read-early ac (λ ()) tt)) fP
      lc (false , cdone) {q} ac = past (early-r {q} {[ last ]} (read-early ac (λ ()) tt)) fP
      lc (false , tick)  {q} ac = past (tick-r {q} {false} {[ last ]} ac) fP
      lc (true , tick)   {q} ac = past (tick-r {q} {true} {[ last ]} ac) fP
      lc (true , val a) ac with val-row ac
      ... | T′ , e′ , i′ , refl , r₁ , _ =
        ≺→≼ {cascade T′ e′ (ix i′) ∙ (ix 1 ∷ last ∷ [])} {cascade T e last ∙ (ix 1 ∷ last ∷ [])}
          (instant-≺ (cascade T′ e′ (ix i′) ∙ (ix 1 ∷ last ∷ [])) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
            (≺-instant (cascade T′ e′ (ix i′) ∙ []) (cascade T e last ∙ []) (step-before r₁ rc) (λ ())))
      lc (true , cdone) ac with cd-row ac
      ... | _ , rc″ , f-end _ , refl with lf-uniq _ rc rc″
      ...   | refl = ≺→≼ {cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])} {cascade T e last ∙ (ix 1 ∷ last ∷ [])}
                       (same-≺ (cascade T e last) (ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ []) (ix 1 ∷ last ∷ []) tt)

      fin : ∀ {i} → O p (p ⊕ [ ix 0 ]) (out true) → O (S₁ p) (S₁ p ⊕ [ ix 1 ]) (out false) → Indexed (S₁ p ⊕ [ ix 1 ])
          → Nth i (S₁ p ⊕ [ ix 1 ]) false → Starts i (S₁ p ⊕ [ ix 1 ]) (Sched i) (cascade T e last ∙ [ ix 1 ])
          → Reach CJoinT (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (out cdone)
          → Reach (Merge.JoinT Fm (O p)) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (out cdone)
          → Reach (Scan.ScanT phase (false , tick) (Mg p)) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (out (true , cdone))
          → Merge.JoinT R (Sc p) (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
          → Reach (Merge.JoinT R (Sc p)) (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
          → Top (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
      fin ox ox′ ix′ nd st rCat rMg rSc r h = Joining.oend sc-end top-done , top-reach
        where
          ct : enter (Fm true) (S₁ p) (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
          ct = fm-back (S₁ p)
            ( Joining.lend ox′ ix′ (tag-lane nd st) (λ ()) no-queue (cat-done nd st)
            , reach-on {t = CJoinT} {q = cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])} {y = cascade T e last ∙ (ix 1 ∷ last ∷ [])} {v = cdone} {e = end}
                rCat (few-at f1 (λ r′ → proj₁ (cat-pl r′))) lt₀ refl)

          mg-end : Mg p (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
          mg-end = Joining.lend ox tt (ct , fresh-past {S₁ p} {S₁ p} {cascade T e last ∙ (ix 1 ∷ last ∷ [])} (⊑-refl (S₁ p)) f1)
                     (λ ()) (λ ()) (mg-done ct)
                 , reach-on {t = Merge.JoinT Fm (O p)} {q = cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])} {y = cascade T e last ∙ (ix 1 ∷ last ∷ [])}
                     {v = cdone} {e = end} rMg (few-at fP (mg-pl p)) lt₀ refl

          sc-end : Sc p (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
          sc-end = Scan.send mg-end
                 , reach-on {t = Scan.ScanT phase (false , tick) (Mg p)} {q = cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])}
                     {y = cascade T e last ∙ (ix 1 ∷ last ∷ [])} {v = true , cdone} {e = end} rSc (few-at fP sc-pl′) lt₀ refl

          tl : ∀ x {q} → Sc p q (out x) → Ended (LaneOf R q x) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
          tl x {q} (Scan.sval ac , _) = _ , (r-end x (q ⊕ [ ix 1 ]) , ≺-ext (q ⊕ [ ix 1 ]) {last} []) , lc x ac

          top-done : Merge.Done R (Sc p) (cascade T e last ∙ (ix 1 ∷ last ∷ []))
          top-done = (_ , sc-end , ≼-refl {cascade T e last ∙ (ix 1 ∷ last ∷ [])}) , λ {q} {x} sx _ _ _ → tl x sx

          top-reach : Reach (Merge.JoinT R (Sc p)) (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
          top-reach = reach-on {t = Merge.JoinT R (Sc p)} {q = B⁰ (cascade T e last)} {y = cascade T e last ∙ (ix 1 ∷ last ∷ [])}
                        {v = instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))} {e = end}
                        h (step-few p r) (same-≺ (cascade T e last) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ last ∷ []) tt) refl

    -- The completion's begin, traced to the tag's lane.
    Beg BegR : ℕ → Pos → Set
    Beg T e = Merge.JoinT R (Sc p) (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
    BegR T e = Reach (Merge.JoinT R (Sc p)) (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))

    EndT : ℕ → Pos → Set
    EndT T e = Top (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end

    ct₃ : ∀ {q₀ T e s′} → Sc p q₀ (out (true , cdone)) → Acc p q₀ (true , cdone) → B⁰ (cascade T e last) ≡ (q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
        → Beg T e → BegR T e → Reach (Merge.JoinT Fm (O p)) q₀ (out cdone)
        → O p (p ⊕ [ ix 0 ]) (out true) → O (S₁ p) (S₁ p ⊕ [ ix 1 ]) (out false) → Indexed (S₁ p ⊕ [ ix 1 ])
        → Nth 1 (S₁ p ⊕ [ ix 1 ]) false → Starts 1 (S₁ p ⊕ [ ix 1 ]) (Sched 1) s′ → enter (Fc false) s′ q₀ (out cdone)
        → Reach CJoinT q₀ (out cdone) → EndT T e
    ct₃ sx ac eq r h rMg ox ox′ ix′ nd (room (s≤s ())) rt rCat
    ct₃ sx ac eq r h rMg ox ox′ ix′ nd (freed _ _) rt rCat with fc-out _ rt
    ... | refl , _ = ⊥-elim (not-under (⊑-trans (⊑₂ p (ix 0) (ix 1)) (⊑-trans (⊑₂ (S₁ p) (ix 1) (ix 1)) ([ ix 0 ] , refl))) (read-late p ac tt))
    ct₃ sx ac eq r h rMg ox ox′ ix′ nd st@(queued {c₂} _ _ kc _ _) rt rCat with fc-out _ rt | lf-row _ (first-end kc)
    ... | refl , _ | inj₁ u = ⊥-elim (not-under (⊑-trans pS (⊑-trans u ((ix 1 ∷ ix 0 ∷ []) , ⊕-assoc c₂ [ ix 1 ] [ ix 0 ]))) (read-late p ac tt))
    ... | refl , _ | inj₂ (f-end fK) with eq
    ...   | refl = Fin.fin _ _ fK (first-end kc) ox ox′ ix′ nd st rCat rMg (proj₂ sx) r h

    ct₂ : ∀ {q₀ T e q a} → Sc p q₀ (out (true , cdone)) → Acc p q₀ (true , cdone) → B⁰ (cascade T e last) ≡ (q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
        → Beg T e → BegR T e → Reach (Merge.JoinT Fm (O p)) q₀ (out cdone)
        → O p (p ⊕ [ ix 0 ]) (out true) → O (S₁ p) q (out a) → Indexed q
        → (q ≡ S₁ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ S₁ p ⊕ [ ix 1 ] × a ≡ false)
        → CLane q a q₀ (out cdone) → Reach CJoinT q₀ (out cdone) → EndT T e
    ct₂ sx ac eq r h rMg ox ox′ ix′ (inj₁ (refl , refl)) ln rCat with () ← lf-val _ (lane₀ ln)
    ct₂ sx ac eq r h rMg ox ox′ ix′ (inj₂ (refl , refl)) (i , s′ , (nd , st) , (rt , _)) rCat with nth-inj nd nth₁
    ... | refl = ct₃ sx ac eq r h rMg ox ox′ ix′ nd st rt rCat

    ct₁ : ∀ {q₀ T e} → Sc p q₀ (out (true , cdone)) → Acc p q₀ (true , cdone) → B⁰ (cascade T e last) ≡ (q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
        → Beg T e → BegR T e → Reach (Merge.JoinT Fm (O p)) q₀ (out cdone)
        → O p (p ⊕ [ ix 0 ]) (out true) → enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) (S₁ p) q₀ (out cdone) → EndT T e
    ct₁ sx ac eq r h rMg ox (Joining.run () _ , _)
    ct₁ sx ac eq r h rMg ox (Joining.lane ox′ ix′ ln _ _ , rCat) = ct₂ sx ac eq r h rMg ox ox′ ix′ (o-row (S₁ p) ox′) ln rCat

    mg₂ : ∀ {q₀ T e q a} → Sc p q₀ (out (true , cdone)) → Acc p q₀ (true , cdone) → B⁰ (cascade T e last) ≡ (q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
        → Beg T e → BegR T e → Reach (Merge.JoinT Fm (O p)) q₀ (out cdone)
        → O p q (out a) → (q ≡ p ⊕ [ ix 0 ] × a ≡ true) ⊎ (q ≡ p ⊕ [ ix 1 ] × a ≡ false) → enter (Fm a) (q ⊕ [ ix 1 ]) q₀ (out cdone) → EndT T e
    mg₂ sx ac eq r h rMg ox (inj₂ (refl , refl)) l₀ = ⊥-elim (proj₂ (fm-false _ l₀))
    mg₂ sx ac eq r h rMg ox (inj₁ (refl , refl)) l₀ = ct₁ sx ac eq r h rMg ox (fm-true _ l₀)

    mg₁ : ∀ {q₀ T e} → Sc p q₀ (out (true , cdone)) → Acc p q₀ (true , cdone) → B⁰ (cascade T e last) ≡ (q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
        → Beg T e → BegR T e → Mg p q₀ (out cdone) → EndT T e
    mg₁ sx ac eq r h (Joining.run () _ , _)
    mg₁ sx ac eq r h (Joining.lane ox _ (l₀ , _) _ _ , rMg) = mg₂ sx ac eq r h rMg ox (o-row p ox) l₀

    cd₀ : ∀ x₀ {q₀ T e} → Sc p q₀ (out x₀) → Acc p q₀ x₀
        → ROut x₀ (q₀ ⊕ [ ix 1 ]) (B⁰ (cascade T e last)) (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ [])))
        → Merge.JoinT R (Sc p) (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
        → Reach (Merge.JoinT R (Sc p)) (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
        → Top (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
    cd₀ (true , val a) sx ac vr r h with val-row ac
    ... | _ , _ , _ , refl , _ with vr
    ...   | ()
    cd₀ (true , cdone)  sx ac (eq , _) r h = mg₁ sx ac eq r h (acc-tag ac)
    cd₀ (false , val a) sx ac (_ , ()) r h
    cd₀ (false , cdone) sx ac () r h
    cd₀ (false , tick)  sx ac () r h
    cd₀ (true , tick)   sx ac () r h

    -- A completion step begun ends the whole.
    cdclose : ∀ {T e} → Top (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
            → Top (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
    cdclose (r@(Joining.lane {a = x₀} sx@(Scan.sval ac , _) _ (l , _) _ _) , h) = cd₀ x₀ sx ac (r-out x₀ _ l) r h
    cdclose (Joining.run () _ , _)

------------------------------------------------------------------------
-- The elaborated cold's ends

-- The minted name's cold, ended.
mint-end : ∀ s → enter (Op.cold Mint) s (s ⊕ [ last ]) end
mint-end s = on-out (on-skip at-end) , L.map (s ⊕_) RZ , λ r _ _ → rz s (mint-in s r)

-- A value's step, ended with its name's cold.
rv-end : ∀ {X : Set} (a : X) s
       → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s
           (s ⊕ [ last ]) end
rv-end a s = Joining.oend (mint-end s) ((_ , mint-end s , ≼-refl {s ⊕ [ last ]}) , λ x _ _ _ → ln x)
           , L.map (s ⊕_) RZ , λ r _ _ → rz s (rv-raw a s r)
  where
    ln : ∀ {q n} → enter (Op.cold Mint) s q (out n)
       → Ended (LaneOf (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) q n) (s ⊕ [ last ])
    ln (x , _) with CF.mint-out s x
    ... | refl = _ , ((of-end-row ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 _ , of-reach ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 _ {_} {end})
                     , ≺-ext ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) {last} [])
               , ≺→≼ {((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {s ⊕ [ last ]}
                   (subst (_≺ (s ⊕ [ last ])) (sym (assoc³ s (ix 0) (ix 1) last))
                     (Equivalence.from T-≡ (<ᵖ-part s {ix 0} {last} (ix 1 ∷ last ∷ []) [] refl)))

-- A completion's step, ended with its name's cold.
cd-end : ∀ {X : Set} s → enter (Op.map (λ n → instEmit {A = X} (mark begin) n) (Op.cold Mint)) s (s ⊕ [ last ]) end
cd-end {X} s = map-end (mint-end s) , L.map (s ⊕_) RZ , go
  where
    go : ∀ {k e′} → MapT (λ n → instEmit {A = X} (mark begin) n) (enter (Op.cold Mint) s) k e′ → k ≺ (s ⊕ [ last ]) → Dep (s ⊕ [ last ]) end k e′
       → k ∈ L.map (s ⊕_) RZ
    go (map-out (x , _))  _ _ = rz s (mint-in s x)
    go (map-skip (x , _)) _ _ = rz s (mint-in s x)
    go (map-pin (x , _))  _ _ = rz s (mint-in s x)
    go (map-end (x , _))  _ _ = rz s (mint-in s x)

em-end : ∀ {X : Set} s → enter (Op.empty {X}) s (s ⊕ [ last ]) end
em-end s = at-end , (s ⊕ [ last ]) ∷ [] , λ { at-end _ _ → here refl }

module _ {Δ : List Set} (env : DenEnv Δ) where

  fc-fins : ∀ m {A} s → enter (ev m (of (cdone {A} ∷ [])) env) s (s ⊕ [ last ]) end
  fc-fins nothing  s = of-end-row s 0 (cdone ∷ []) , of-reach s 0 (cdone ∷ []) {s ⊕ [ last ]} {end}
  fc-fins (just _) s = of-end-row s 0 (cdone ∷ []) , of-reach s 0 (cdone ∷ []) {s ⊕ [ last ]} {end}

  fm-fins : ∀ m {A} s → enter (ev m (of (tick {A} ∷ [])) env) s (s ⊕ [ last ]) end
  fm-fins nothing  s = of-end-row s 0 (tick ∷ []) , of-reach s 0 (tick ∷ []) {s ⊕ [ last ]} {end}
  fm-fins (just _) s = of-end-row s 0 (tick ∷ []) , of-reach s 0 (tick ∷ []) {s ⊕ [ last ]} {end}

  r-ends : ∀ m {A} (x : Bool × Tag A) s → enter (ev m (render x) env) s (s ⊕ [ last ]) end
  r-ends nothing  (false , val a) s = of-end-row s 0 (_ ∷ []) , of-reach s 0 (_ ∷ []) {s ⊕ [ last ]} {end}
  r-ends nothing  (true , val a)  s = rv-end a s
  r-ends nothing  (true , cdone)  s = cd-end s
  r-ends nothing  (false , cdone) s = em-end s
  r-ends nothing  (false , tick)  s = em-end s
  r-ends nothing  (true , tick)   s = em-end s
  r-ends (just _) (false , val a) s = of-end-row s 0 (_ ∷ []) , of-reach s 0 (_ ∷ []) {s ⊕ [ last ]} {end}
  r-ends (just _) (true , val a)  s = rv-end a s
  r-ends (just _) (true , cdone)  s = cd-end s
  r-ends (just _) (false , cdone) s = em-end s
  r-ends (just _) (false , tick)  s = em-end s
  r-ends (just _) (true , tick)   s = em-end s

  module EndsOf (m : Maybe ℕ) {A : Set} (c : Timeline A) =
    Ends (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env)
         (λ b → ev m (if b then concatˢ (map val (cold c)) (of (cdone ∷ [])) else of (tick ∷ [])) env)
         (λ x → ev m (render x) env)
         (CF.fc-true env m c) (CF.fc-false env m) (CF.fm-true env m c) (CF.fm-false env m) (CF.render-in env m) (CF.render-begin env m)
         (lf-rows env m c) (lf-vals env m c) (lf-uniqs env m c) (lf-bes env m c) (fc-outs env m) (fc-ends env m) (fm-ticks env m) (r-outs env m)
         (fm-backs env m c) (fc-fins m) (fm-fins m) (r-ends m)

------------------------------------------------------------------------
-- The cold's

-- A completion step begun closes with the cold's end: every lane the
-- whole runs has ended there.
cold-cdclose : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e}
             → enter (ev m (coldˢ c) env) p (B⁰ (cascade T e last)) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
             → enter (ev m (coldˢ c) env) p (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
cold-cdclose nothing  c env p x = EndsOf.At.cdclose env nothing c p x
cold-cdclose (just n) c env p x = EndsOf.At.cdclose env (just n) c p x
