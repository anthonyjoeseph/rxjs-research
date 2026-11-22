{-# OPTIONS --guardedness #-}

-- A STEP OF THE COLD BEGUN CLOSES IN ITS INSTANT.  The begin's render
-- says which step it is (`label`): a value read past the tick lies at an
-- indexed label, a completion at the last.  A value step's render sends
-- its over after the begin, in the same lane (`vclose`); the instant
-- makes few rows, so the over is reached as the begin is.  A completion
-- step closes with the cold's end (`simultaneous.ColdEnd.cold-cdclose`).
module simultaneous.ColdClose where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (mergeᶠ; cold; of; map)
open import denotation.Position using (Pos; ix; last; cascade; _∙_; _⊕_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; enter; out; end; at-out; on-out; on-skip; _≺_; _≼_; Reach;
  Truncate; module Op; module Joining; module Merge; module Scan)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import denotation.Laws.Worlds using (_⊑_)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; Tag; val; cdone; tick; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over)
open import simultaneous.Routed using (nm)
open import simultaneous.ColdFew using (f-end; Leaf; Ticks; Tickless; Rendered; RZ; Mint; rv-raw; module Core)
import simultaneous.ColdFew as CF
open import simultaneous.ColdShape using (module Shape; ROut; v-begin; IsVal; lf-rows; lf-vals; lf-uniqs; lf-bes; fc-outs;
  fc-ends; fm-ticks; r-outs)
open import simultaneous.ColdBegin using (same-≺; rz)
open import simultaneous.ColdRuns using (B⁰)
open import simultaneous.ColdEnd using (reach-on; cold-cdclose)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render; concatˢ)

------------------------------------------------------------------------
-- The closes, from the cold's parts

module Closes {A : Set} (Fc Fm : Bool → Den (Tag A)) (R : Bool × Tag A → Den (IE A))
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
  (r-vo     : ∀ a s {y v} → enter (R (true , val a)) s y (out v)
            → enter (R (true , val a)) s (((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 2 ]) (out (instEmit (mark over) s))) where

  open Core Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin using (Acc; Sc; step-few)
  open Shape Fc Fm R fc-true fc-false fm-true fm-false r-in r-begin lf-row lf-val lf-uniq lf-be fc-out fc-end fm-tick r-out
    using (module Mgs)

  module At (p : Pos) where
    open Mgs p using (val-row; cd-row)

    -- The whole, entered at `p`.
    Top : EmissionSet (IE A)
    Top = Truncate (Merge.JoinT R (Sc p))

    lab : ∀ x₀ {q₀ T e l n} → Acc p q₀ x₀ → ROut x₀ (q₀ ⊕ [ ix 1 ]) (B⁰ (cascade T e l)) (instEmit (mark begin) n)
        → (Σ ℕ λ i → l ≡ ix i) ⊎ l ≡ last
    lab (true , val a) ac vr with val-row ac
    ... | _ , _ , i , refl , _ with vr
    ...   | v-begin = inj₁ (i , refl)
    lab (true , cdone) ac (eq , refl) with cd-row ac
    ... | _ , _ , f-end _ , refl with eq
    ...   | refl = inj₂ refl
    lab (false , val a) ac (_ , ())
    lab (false , cdone) ac ()
    lab (false , tick)  ac ()
    lab (true , tick)   ac ()

    -- Which step a begin opens.
    label : ∀ {T e l} → Top (B⁰ (cascade T e l)) (out (instEmit (mark begin) (nm (cascade T e l ∙ []))))
          → (Σ ℕ λ i → l ≡ ix i) ⊎ l ≡ last
    label (Joining.lane {a = x₀} (Scan.sval ac , _) _ (l , _) _ _ , _) = lab x₀ ac (r-out x₀ _ l)
    label (Joining.run () _ , _)

    vc : ∀ x₀ {q₀ T e i} → Sc p q₀ (out x₀) → Acc p q₀ x₀
       → enter (R x₀) (q₀ ⊕ [ ix 1 ]) (B⁰ (cascade T e (ix i))) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
       → (q₀ ⊕ [ ix 1 ]) ≺ B⁰ (cascade T e (ix i))
       → Merge.JoinT R (Sc p) (B⁰ (cascade T e (ix i))) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
       → Reach (Merge.JoinT R (Sc p)) (B⁰ (cascade T e (ix i))) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
       → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
    vc (true , val a) {T = T} {e} {i} sx ac l lt r h with val-row ac
    ... | _ , _ , _ , refl , _ with r-out (true , val a) _ l
    ...   | v-begin =
      Joining.lane sx tt
        (r-vo a (cascade T e (ix i) ∙ [ ix 1 ]) l
        , ≺-trans {cascade T e (ix i) ∙ [ ix 1 ]} {B⁰ (cascade T e (ix i))} {cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])} lt
            (same-≺ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt))
        (λ ()) tt
      , reach-on {t = Merge.JoinT R (Sc p)} {q = B⁰ (cascade T e (ix i))} {y = cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])}
          {v = instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])} {e = out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ]))} h (step-few p r)
          (same-≺ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt) refl
    vc (true , cdone) sx ac l lt r h with cd-row ac
    ... | _ , _ , f-end _ , refl with r-out (true , cdone) _ l
    ...   | () , _
    vc (false , val a) sx ac l lt r h with r-out (false , val a) _ l
    ... | _ , ()
    vc (false , cdone) sx ac l lt r h with r-out (false , cdone) _ l
    ... | ()
    vc (false , tick) sx ac l lt r h with r-out (false , tick) _ l
    ... | ()
    vc (true , tick) sx ac l lt r h with r-out (true , tick) _ l
    ... | ()

    -- A value step begun sends its over.
    vclose : ∀ {T e i} → Top (B⁰ (cascade T e (ix i))) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
           → Top (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
    vclose (r@(Joining.lane {a = x₀} sx@(Scan.sval ac , _) _ (l , lt) _ _) , h) = vc x₀ sx ac l lt r h
    vclose (Joining.run () _ , _)

------------------------------------------------------------------------
-- The elaborated cold's renders

-- A value step's render sends its over.
rv-over : ∀ {X : Set} (a : X) s {y v}
        → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s y (out v)
        → enter (Op.flatMap (mergeᶠ nothing) (λ n → Op.of (instEmit (mark begin) n ∷ instEmit (value a) n ∷ instEmit (mark over) n ∷ [])) (Op.cold Mint)) s
            (((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 2 ]) (out (instEmit (mark over) s))
rv-over a s (Joining.lane x@(at-out , _) _ _ _ _ , _) =
  Joining.lane x tt ((on-out (on-out at-out) , of-reach ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (instEmit (mark begin) s ∷ instEmit (value a) s ∷ instEmit (mark over) s ∷ [])
      {e = out (instEmit (mark over) s)}) , ≺-ext ((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) {ix 2} []) (λ ()) tt
  , L.map (s ⊕_) RZ , λ r _ _ → rz s (rv-raw a s r)
rv-over a s (Joining.lane (on-out (on-skip ()) , _) _ _ _ _ , _)
rv-over a s (Joining.run () _ , _)

module _ {Δ : List Set} (env : DenEnv Δ) where

  r-vos : ∀ m {A} (a : A) s {y v} → enter (ev m (render (true , val a)) env) s y (out v)
        → enter (ev m (render (true , val a)) env) s (((s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 2 ]) (out (instEmit (mark over) s))
  r-vos nothing  a s r = rv-over a s r
  r-vos (just _) a s r = rv-over a s r

  module ClosesOf (m : Maybe ℕ) {A : Set} (c : Timeline A) =
    Closes (λ b → ev m (if b then map val (cold c) else of (cdone ∷ [])) env)
           (λ b → ev m (if b then concatˢ (map val (cold c)) (of (cdone ∷ [])) else of (tick ∷ [])) env)
           (λ x → ev m (render x) env)
           (CF.fc-true env m c) (CF.fc-false env m) (CF.fm-true env m c) (CF.fm-false env m) (CF.render-in env m) (CF.render-begin env m)
           (lf-rows env m c) (lf-vals env m c) (lf-uniqs env m c) (lf-bes env m c) (fc-outs env m) (fc-ends env m) (fm-ticks env m) (r-outs env m)
           (r-vos m)

------------------------------------------------------------------------
-- The cold's closes

cold-label : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e l}
           → enter (ev m (coldˢ c) env) p (B⁰ (cascade T e l)) (out (instEmit (mark begin) (nm (cascade T e l ∙ []))))
           → (Σ ℕ λ i → l ≡ ix i) ⊎ l ≡ last
cold-label nothing  c env p x = ClosesOf.At.label env nothing c p x
cold-label (just n) c env p x = ClosesOf.At.label env (just n) c p x

cold-vclose : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e i}
            → enter (ev m (coldˢ c) env) p (B⁰ (cascade T e (ix i))) (out (instEmit (mark begin) (cascade T e (ix i) ∙ [ ix 1 ])))
            → enter (ev m (coldˢ c) env) p (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (cascade T e (ix i) ∙ [ ix 1 ])))
cold-vclose nothing  c env p x = ClosesOf.At.vclose env nothing c p x
cold-vclose (just n) c env p x = ClosesOf.At.vclose env (just n) c p x

-- A step begun closes in its instant: a value step with its over, a
-- completion with the cold's end.
cold-close : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p {T e l}
           → enter (ev m (coldˢ c) env) p (B⁰ (cascade T e l)) (out (instEmit (mark begin) (nm (cascade T e l ∙ []))))
           → (Σ ℕ λ i → l ≡ ix i × enter (ev m (coldˢ c) env) p (cascade T e l ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []))
                                       (out (instEmit (mark over) (nm (cascade T e l ∙ [])))))
             ⊎ (l ≡ last × enter (ev m (coldˢ c) env) p (cascade T e l ∙ (ix 1 ∷ last ∷ [])) end)
cold-close m c env p x with cold-label m c env p x
... | inj₁ (i , refl) = inj₁ (i , refl , cold-vclose m c env p x)
... | inj₂ refl       = inj₂ (refl , cold-cdclose m c env p x)
