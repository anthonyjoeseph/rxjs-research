{-# OPTIONS --guardedness #-}

-- EVERY STEP OF THE COLD SHOWS ITS BEGIN.  A value step's value and over
-- lie in the render that sends its begin first (`vb`, `ob`).  A
-- completion step's end at `J ∙ [ ix 1 , last ]` is the concat's second
-- lane ending; that lane's `cdone`, read past the tick, renders the begin
-- (`eb`).  The scan's fold of it is found classically, so that begin is
-- shown under a double negation.
module simultaneous.ColdBegin where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Tree using (mergeᶠ; cold; of; map)
open import denotation.Position using (Pos; ix; last; cascade; _∙_; _⊕_; _≟ᵖ_; root; isLt; cmpPath; lexi)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; enter; Ev; out; end; InE; at-out; on-out; on-skip; _≺_; _≼_; Reach;
  Truncate; Few; map-out; map-skip; map-pin; map-end; module Op; module Joining;
  module Bounded; module Merge; module Scan)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ticks)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans; ⊕-assoc)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.Fold using (fold)
open import denotation.Simultaneity using (reflⁱ)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; Tag; val; cdone; tick; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.ColdFew using (Fresh; fresh-past; ⊑₂; f-end; Leaf; module Pair; Ticks; Tickless; Rendered; RZ; Mint;
  mint-in; module Core; O; o-row; o-under)
import simultaneous.ColdFew as CF
open import simultaneous.ColdShape using (module Shape; lead-⊑; ROut; v-value; v-over; IsVal; lf-rows; lf-vals; lf-uniqs; lf-bes; fc-outs;
  fc-ends; fm-ticks; r-outs)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render; concatˢ; phase)

-- Within one instant, by path.
same-≺ : ∀ i x y → T (isLt (cmpPath x y)) → (i ∙ x) ≺ (i ∙ y)
same-≺ i x y h rewrite reflⁱ i = h

same-≺⁻ : ∀ i x y → (i ∙ x) ≺ (i ∙ y) → T (isLt (cmpPath x y))
same-≺⁻ i x y h = subst (λ c → T (isLt (lexi c (cmpPath x y)))) (reflⁱ i) h

-- A row's reach serves every earlier row: none of them waits on a pin.
inh : ∀ {X} {t : EmissionSet X} {q y} {v : X} {e : Ev X} → Reach t y (out v) → q ≺ y → Reach t q e
inh {q = q} {y} (ks , h) lt = ks , λ {k} r kl _ → h r (≺-trans {k} {q} {y} kl lt) tt

inh-end : ∀ {X} {t : EmissionSet X} {q y} {e : Ev X} → Reach t y end → q ≺ y → Reach t q e
inh-end {q = q} {y} (ks , h) lt = ks , λ {k} r kl _ → h r (≺-trans {k} {q} {y} kl lt) tt

------------------------------------------------------------------------
-- The begins, from the cold's parts

module Begins {A : Set} (Fc Fm : Bool → Den (Tag A)) (R : Bool × Tag A → Den (IE A))
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
  (fc-cd    : ∀ s → enter (Fc false) s (s ⊕ [ ix 0 ]) (out cdone))
  (r-vb     : ∀ a s {y v} → enter (R (true , val a)) s y (out v)
            → enter (R (true , val a)) s (((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (instEmit (mark begin) s)))
  (r-cd     : ∀ s → enter (R (true , cdone)) s (s ⊕ [ ix 0 ]) (out (instEmit (mark begin) s))) where

  open Core Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin using (S₁; Mg; Acc; Sc; acc-tag; module Cat)
  open Shape Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin lf-row lf-val lf-uniq lf-be fc-out fc-end fm-tick r-out
    using (module Mgs; module Cat′)

  module At (p : Pos) where
    open Mgs p using (val-row; late-past; tick-at; T₀; T₀-under; lane-end; not-under; pS)
    open Cat′ (S₁ p) using (lane₀)
    open Cat (S₁ p) using (first-end)
    open Pair (S₁ p) using (nth₁)
    open Nths (O (S₁ p)) using (nth-inj)

    -- The whole, entered at `p`.
    Top : EmissionSet (IE A)
    Top = Truncate (Merge.JoinT R (Sc p))

    sx-acc : ∀ {q b} → Sc p q (out b) → Acc p q b
    sx-acc (Scan.sval ac , _) = ac

    -- A value step's render sends its begin first.
    beg-row : ∀ {q₀ a k v} → Sc p q₀ (out (true , val a)) → enter (R (true , val a)) (q₀ ⊕ [ ix 1 ]) k (out v)
            → Reach (Merge.JoinT R (Sc p)) k (out v) → ((((q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ≺ k
            → Top ((((q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (instEmit (mark begin) (q₀ ⊕ [ ix 1 ])))
    beg-row {q₀} {a} {k} {v} sx l h bk =
      Joining.lane sx tt (r-vb a (q₀ ⊕ [ ix 1 ]) l
        , subst ((q₀ ⊕ [ ix 1 ]) ≺_) (sym (assoc³ (q₀ ⊕ [ ix 1 ]) (ix 0) (ix 1) (ix 0))) (≺-ext (q₀ ⊕ [ ix 1 ]) {ix 0} (ix 1 ∷ ix 0 ∷ [])))
        (λ ()) tt
      , inh {t = Merge.JoinT R (Sc p)} {q = (((q₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} {y = k} {v = v} {e = out (instEmit (mark begin) (q₀ ⊕ [ ix 1 ]))} h bk

    vb′ : ∀ x₀ {q₀ T e i a} → Sc p q₀ (out x₀)
        → enter (R x₀) (q₀ ⊕ [ ix 1 ]) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (out (instEmit (value a) (cascade T e (ix i) ∙ [ ix 1 ])))
        → Reach (Merge.JoinT R (Sc p)) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (out (instEmit (value a) (cascade T e (ix i) ∙ [ ix 1 ])))
        → ROut x₀ (q₀ ⊕ [ ix 1 ]) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (instEmit (value a) (cascade T e (ix i) ∙ [ ix 1 ]))
        → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
    vb′ (true , val _) {T = T} {e} {i} sx l h vr with val-row (sx-acc sx)
    ... | _ , _ , _ , refl , _ , _ with vr
    ...   | v-value = beg-row sx l h (same-≺ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ []) tt)
    vb′ (false , val _) sx l h (_ , ())
    vb′ (true , cdone)  sx l h (_ , ())
    vb′ (false , cdone) sx l h ()
    vb′ (false , tick)  sx l h ()
    vb′ (true , tick)   sx l h ()

    vb : ∀ {T e i a} → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (out (instEmit (value a) (cascade T e (ix i) ∙ [ ix 1 ])))
       → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
    vb (Joining.lane {a = x₀} sx _ (l , _) _ _ , h) = vb′ x₀ sx l h (r-out x₀ _ l)
    vb (Joining.run () _ , _)

    ob′ : ∀ x₀ {q₀ T e i} → Sc p q₀ (out x₀)
        → enter (R x₀) (q₀ ⊕ [ ix 1 ]) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
        → Reach (Merge.JoinT R (Sc p)) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
        → ROut x₀ (q₀ ⊕ [ ix 1 ]) (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ]))
        → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
    ob′ (true , val _) {T = T} {e} {i} sx l h vr with val-row (sx-acc sx)
    ... | _ , _ , _ , refl , _ , _ with vr
    ...   | v-over = beg-row sx l h (same-≺ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt)
    ob′ (false , val _) sx l h (_ , ())
    ob′ (true , cdone)  sx l h (_ , ())
    ob′ (false , cdone) sx l h ()
    ob′ (false , tick)  sx l h ()
    ob′ (true , tick)   sx l h ()

    ob : ∀ {T e i} → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
       → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
    ob (Joining.lane {a = x₀} sx _ (l , _) _ _ , h) = ob′ x₀ sx l h (r-out x₀ _ l)
    ob (Joining.run () _ , _)

    -- A completion step: the concat's second lane, queued at the cold's
    -- end, sends its `cdone` before its end; read late, it renders the
    -- begin.
    sc-mg : ∀ {k e} → Scan.ScanT phase (false , tick) (Mg p) k e → Σ (Ev (Tag A)) (Mg p k)
    sc-mg (Scan.sval a)  = _ , acc-tag a
    sc-mg (Scan.sstep x) = _ , x
    sc-mg (Scan.spin x)  = _ , x
    sc-mg (Scan.send x)  = _ , x

    Bᵖ Eᵖ : ∀ T e → Pos
    Bᵖ T e = cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])
    Eᵖ T e = cascade T e last ∙ (ix 1 ∷ last ∷ [])

    Beg : ∀ T e → Set
    Beg T e = Top (Bᵖ T e) (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))

    -- The cold's end hands the concat to its second lane; that lane's
    -- `cdone`, merged and read past the tick, renders the begin.
    eb-l : ∀ {T e} → Fresh p (cascade T e last) → O p (p ⊕ [ ix 0 ]) (out true)
         → Reach (Merge.JoinT Fm (O p)) (Eᵖ T e) end → Reach (Merge.JoinT R (Sc p)) (Eᵖ T e) end
         → O (S₁ p) (S₁ p ⊕ [ ix 1 ]) (out false) → Bounded.Indexed 1 Fc (O (S₁ p)) (S₁ p ⊕ [ ix 1 ])
         → Reach (Bounded.JoinT 1 Fc (O (S₁ p))) (Eᵖ T e) end
         → Bounded.Lane 1 Fc (O (S₁ p)) (S₁ p ⊕ [ ix 1 ]) false (Eᵖ T e) end → ¬ ¬ Beg T e
    eb-l {T} {e} f o mh h o′ rn ch (i , _ , (nd , st) , (r , _)) with nth-inj nd nth₁
    ... | refl with st
    ...   | Bounded.room (s≤s ())
    ...   | Bounded.freed _ _ =
      ⊥-elim (not-under (subst (p ⊑_) (sym (fc-end _ r)) (⊑-trans (⊑₂ p (ix 0) (ix 1)) (⊑-trans (⊑₂ (S₁ p) (ix 1) (ix 1)) ([ last ] , refl)))) f)
    ...   | Bounded.queued n≤ lq kc ka nk with lf-row (S₁ (S₁ p)) (first-end kc) | fc-end _ r
    ...     | inj₁ u | eq =
      ⊥-elim (not-under (subst (p ⊑_) (sym eq) (⊑-trans pS (⊑-trans u ((ix 1 ∷ last ∷ []) , ⊕-assoc _ [ ix 1 ] [ last ])))) f)
    ...     | inj₂ (f-end _) | refl = λ ¬b → fold phase (false , tick) (Mg p) few mx λ (b , ac) → ¬b (top b ac)
      where
        cr : enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) (S₁ p) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (out cdone)
        cr = Joining.lane o′ rn (1 , _ , (nd , Bounded.queued n≤ lq kc ka nk)
                 , (fc-cd (cascade T e last ∙ [ ix 1 ]) , ≺-ext (cascade T e last ∙ [ ix 1 ]) {ix 0} [])) (λ ()) tt
           , inh-end {e = out cdone} ch (same-≺ (cascade T e last) (ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ last ∷ []) tt)

        mx : Mg p (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (out cdone)
        mx = Joining.lane o tt (fm-back (S₁ p) cr , fresh-past {p} {S₁ p} {cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])} (⊑₂ p (ix 0) (ix 1)) f)
               (λ ()) tt
           , inh-end {e = out cdone} mh (same-≺ (cascade T e last) (ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ last ∷ []) tt)

        few : Few (Mg p) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ []))
        few = proj₁ (proj₂ mx) , λ (x , _) kl → proj₂ (proj₂ mx) x kl tt

        lt₀ : T₀ ≺ (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ []))
        lt₀ = fresh-past {p} {T₀} {cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])} T₀-under f

        top : ∀ b → Acc p (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (phase b cdone) → Beg T e
        top b ac =
          Joining.lane (Scan.sval ac′ , proj₁ few , λ r kl _ → proj₂ few (proj₂ (sc-mg r)) kl) tt
            (r-cd (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) , ≺-ext (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) {ix 0} []) (λ ()) tt
          , inh-end {t = Merge.JoinT R (Sc p)} {e = out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ [])))} h (same-≺ (cascade T e last) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ last ∷ []) tt)
          where
            ac′ : Acc p (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (true , cdone)
            ac′ = subst (λ z → Acc p (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ [])) (z , cdone))
                    (Equivalence.to (T-≡ {proj₁ (phase b cdone)}) (late-past ac (tick-at mx lt₀) lt₀)) ac

    eb-0 : ∀ {T e} → Fresh p (cascade T e last) → Bounded.Lane 1 Fc (O (S₁ p)) (S₁ p ⊕ [ ix 0 ]) true (Eᵖ T e) end → ⊥
    eb-0 f l with lf-row (S₁ (S₁ p)) (lane₀ l)
    ... | inj₁ u = not-under (⊑-trans pS u) f
    ... | inj₂ ()

    eb-c : ∀ {T e} → Fresh p (cascade T e last) → O p (p ⊕ [ ix 0 ]) (out true)
         → Reach (Merge.JoinT Fm (O p)) (Eᵖ T e) end → Reach (Merge.JoinT R (Sc p)) (Eᵖ T e) end
         → enter (Op.flatMap (mergeᶠ (just 1)) Fc (Op.of (true ∷ false ∷ []))) (S₁ p) (Eᵖ T e) end → ¬ ¬ Beg T e
    eb-c f o mh h (Joining.oend o′ _ , _) = ⊥-elim (not-under (⊑-trans (⊑₂ p (ix 0) (ix 1)) (o-under (S₁ p) o′)) f)
    eb-c f o mh h (Joining.lend o′ rn L _ _ _ , ch) with o-row (S₁ p) o′
    ... | inj₁ (refl , refl) = ⊥-elim (eb-0 f L)
    ... | inj₂ (refl , refl) = eb-l f o mh h o′ rn ch L
    eb-c f o mh h (Joining.lane _ _ _ _ () , _)
    eb-c f o mh h (Joining.run () _ , _)
    eb-c f o mh h (Joining.rend () _ _ , _)

    eb-m : ∀ {T e} → Fresh p (cascade T e last) → Mg p (Eᵖ T e) end → Reach (Merge.JoinT R (Sc p)) (Eᵖ T e) end → ¬ ¬ Beg T e
    eb-m f (Joining.oend o _ , _) h = ⊥-elim (not-under (o-under p o) f)
    eb-m f (Joining.lend o _ (l , _) _ _ _ , mh) h with o-row p o
    ... | inj₁ (refl , refl) = eb-c f o mh h (fm-true _ l)
    ... | inj₂ (refl , refl) = ⊥-elim (not-under (⊑-trans (⊑₂ p (ix 1) (ix 1)) (proj₁ (fm-false _ l))) f)
    eb-m f (Joining.lane _ _ _ _ () , _) h
    eb-m f (Joining.run () _ , _) h
    eb-m f (Joining.rend () _ _ , _) h

    eb : ∀ {T e} → Fresh p (cascade T e last) → Top (Eᵖ T e) end → ¬ ¬ Beg T e
    eb f (Joining.oend (Scan.send xm , _) _ , h)                = eb-m f xm h
    eb f (Joining.lend (Scan.sval ac , _) _ (l , _) _ _ dn , _) = ⊥-elim (not-under (lead-⊑ (lane-end ac l dn)) f)
    eb f (Joining.lane _ _ _ _ () , _)
    eb f (Joining.run () _ , _)
    eb f (Joining.rend () _ _ , _)

------------------------------------------------------------------------
-- The elaborated cold's renders

-- A value step's render: begin, value and over of the name minted.
rv-reach : ∀ {Y : Set} {t : EmissionSet Y} s′ (b v o : Y) {y w} → InE (ofᴱ s′ 0 (b ∷ v ∷ o ∷ [])) y (out w)
         → Reach t y (out w) → Reach t (s′ ⊕ [ ix 0 ]) (out b)
rv-reach s′ b v o at-out                   h = h
rv-reach {t = t} s′ b v o (on-out at-out)          h = inh {t = t} {q = s′ ⊕ [ ix 0 ]} {y = s′ ⊕ [ ix 1 ]} {v = v} {e = out b} h (ticks s′ 0)
rv-reach {t = t} s′ b v o (on-out (on-out at-out)) h = inh {t = t} {q = s′ ⊕ [ ix 0 ]} {y = s′ ⊕ [ ix 2 ]} {v = o} {e = out b} h (ticks s′ 1)
rv-reach s′ b v o (on-out (on-out (on-out ()))) h

rv-beg : ∀ {X : Set} (a : X) s {y v}
       → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s y (out v)
       → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s
           (((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (instEmit (mark begin) s))
rv-beg a s (Joining.lane x@(at-out , _) _ ((l , _) , _) _ _ , h) =
  Joining.lane x tt ((at-out , of-reach ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (instEmit (mark begin) s ∷ instEmit (value a) s ∷ instEmit (mark over) s ∷ [])
      {e = out (instEmit (mark begin) s)}) , ≺-ext ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) {ix 0} []) (λ ()) tt
  , rv-reach {t = Merge.JoinT (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (enter (Op.cold Mint) s)}
      ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) (instEmit (mark begin) s) (instEmit (value a) s) (instEmit (mark over) s) l h
rv-beg a s (Joining.lane (on-out (on-skip ()) , _) _ _ _ _ , _)
rv-beg a s (Joining.run () _ , _)

-- A completion step's render: the begin of the name minted.
rz : ∀ s {y} → Rendered s y → y ∈ L.map (s ⊕_) RZ
rz s (_ , m , refl) = ∈-map⁺ (s ⊕_) m

cd-beg : ∀ {X : Set} s → enter (Op.map (λ n → instEmit {A = X} (mark begin) n) (Op.cold Mint)) s (s ⊕ [ ix 0 ]) (out (instEmit (mark begin) s))
cd-beg s = map-out (at-out , L.map (s ⊕_) RZ , λ x _ _ → rz s (mint-in s x))
         , L.map (s ⊕_) RZ
         , λ { (map-out (x , _)) _ _ → rz s (mint-in s x) ; (map-skip (x , _)) _ _ → rz s (mint-in s x)
             ; (map-pin (x , _)) _ _ → rz s (mint-in s x) ; (map-end (x , _)) _ _ → rz s (mint-in s x) }

module _ {Δ : List Set} (env : DenEnv Δ) where

  fm-backs : ∀ m {A} (c : Timeline A) s {y e}
           → enter (Op.flatMap (mergeᶠ (just 1)) (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env) (Op.of (true ∷ false ∷ []))) s y e
           → enter (ev m (concatˢ (map val (cold c)) (of (cdone ∷ []))) env) s y e
  fm-backs nothing  c s r = r
  fm-backs (just _) c s r = r

  fc-cds : ∀ m {A} s → enter (ev m (of (cdone {A} ∷ [])) env) s (s ⊕ [ ix 0 ]) (out cdone)
  fc-cds nothing  s = at-out , of-reach s 0 (cdone ∷ []) {s ⊕ [ ix 0 ]} {out cdone}
  fc-cds (just _) s = at-out , of-reach s 0 (cdone ∷ []) {s ⊕ [ ix 0 ]} {out cdone}

  r-vbs : ∀ m {A} (a : A) s {y v} → enter (ev m (render (true , val a)) env) s y (out v)
        → enter (ev m (render (true , val a)) env) s (((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (instEmit (mark begin) s))
  r-vbs nothing  a s r = rv-beg a s r
  r-vbs (just _) a s r = rv-beg a s r

  r-cds : ∀ m {A} s → enter (ev m (render (true , cdone {A})) env) s (s ⊕ [ ix 0 ]) (out (instEmit (mark begin) s))
  r-cds nothing  s = cd-beg s
  r-cds (just _) s = cd-beg s

  module BeginsOf (m : Maybe ℕ) {A : Set} (c : Timeline A) =
    Begins (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env)
           (λ b → ev m (if b then concatˢ (map val (cold c)) (of (cdone ∷ [])) else of (tick ∷ [])) env)
           (λ x → ev m (render x) env)
           (CF.fc-true env m c) (CF.fc-false env m) (CF.fm-true env m c) (CF.fm-false env m) (CF.render-in env m) (CF.render-begin env m)
           (lf-rows env m c) (lf-vals env m c) (lf-uniqs env m c) (lf-bes env m c) (fc-outs env m) (fc-ends env m) (fm-ticks env m) (r-outs env m)
           (fm-backs m c) (fc-cds m) (r-vbs m) (r-cds m)

------------------------------------------------------------------------
-- The cold's begins

cold-vb : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e i a}
        → enter (ev m (coldˢ c) env) p (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (out (instEmit (value a) (cascade T e (ix i) ∙ [ ix 1 ])))
        → enter (ev m (coldˢ c) env) p (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
cold-vb nothing  c env p x = BeginsOf.At.vb env nothing c p x
cold-vb (just n) c env p x = BeginsOf.At.vb env (just n) c p x

cold-ob : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e i}
        → enter (ev m (coldˢ c) env) p (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
        → enter (ev m (coldˢ c) env) p (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
cold-ob nothing  c env p x = BeginsOf.At.ob env nothing c p x
cold-ob (just n) c env p x = BeginsOf.At.ob env (just n) c p x

cold-eb : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e} → Fresh p (cascade T e last)
        → enter (ev m (coldˢ c) env) p (cascade T e last ∙ (ix 1 ∷ last ∷ [])) end
        → ¬ ¬ enter (ev m (coldˢ c) env) p (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []))
                (out (instEmit (mark begin) (cascade T e last ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ []))))
cold-eb nothing  c env p f x = BeginsOf.At.eb env nothing c p f x
cold-eb (just n) c env p f x = BeginsOf.At.eb env (just n) c p f x
