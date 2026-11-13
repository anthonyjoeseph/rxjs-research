{-# OPTIONS --guardedness #-}

-- THE WRAPPER CARRIES THE CORE.  `elaborate` takes the core, told and
-- merged beside the subscribe mark, to the completion mark
-- (`simultaneous.WrapTake`), and restamps and projects the whole.  Each
-- stage carries the plain run on its own: a mark shows nothing, so only
-- the end moves, and the stage's carry has an embedding of its own.
module simultaneous.CarryWrap where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Bool using (true)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (takeWhile)
open import denotation.Position using (_≟ᵖ_; Pos; Path; ix; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; enter; approx)
open import denotation.Laws.Worlds using (Ok; Hots; ⊕-identityʳ)
open import denotation.Laws using (inv-approx)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; valuesOf; value; mark; begin; over; stop; outerOpen; outerClose; laneStart;
  laneDone; burstEnd; outerDone; subscribed; completed)
import simultaneous.InstEmit as Marks
open import simultaneous.Relations using (stamp₀; sourced)
open import simultaneous.CarryBase using (PMap; Emb; CarryAt)
open import simultaneous.CarryLeaves using (coreAt)
open import simultaneous.CarryTold using (module Folded)
open import simultaneous.WrapTake using (module Wrap)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; elaborate; restamp; completing; unfinished; marked)

-- A stage of the wrapper over `u`, subscribed at `s′`: the plain run
-- carried along an embedding of the stage's own, the plain subscription
-- put at or under the stage's.
Wrapped : ∀ {A} → ℕ → SObs [] A → EmissionSet (IE A) → Pos → Set₁
Wrapped n o u s′ = Σ PMap λ M → Emb M × Σ Path λ δ → M root (s′ ⊕ δ)
                 × CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root) u root s′

------------------------------------------------------------------------
-- The restamp

-- A restamp keeps the event, so the values.
restamp-vals : ∀ {X : Set} (st : Pos × IE X) x → valuesOf (proj₂ (restamp st x)) ≡ valuesOf x
restamp-vals (_ , _) (instEmit (value _) _)            = refl
restamp-vals (_ , _) (instEmit (mark begin) _)         = refl
restamp-vals (_ , _) (instEmit (mark over) _)          = refl
restamp-vals (_ , _) (instEmit (mark stop) _)          = refl
restamp-vals (_ , _) (instEmit (mark outerOpen) _)     = refl
restamp-vals (_ , _) (instEmit (mark outerClose) _)    = refl
restamp-vals (_ , _) (instEmit (mark laneStart) _)     = refl
restamp-vals (_ , _) (instEmit (mark Marks.carry) _)   = refl
restamp-vals (_ , _) (instEmit (mark laneDone) _)      = refl
restamp-vals (_ , _) (instEmit (mark burstEnd) _)      = refl
restamp-vals (_ , _) (instEmit (mark outerDone) _)     = refl
restamp-vals (_ , _) (instEmit (mark subscribed) _)    = refl
restamp-vals (_ , _) (instEmit (mark completed) _)     = refl

------------------------------------------------------------------------
-- The stages

-- THE TAKE CARRIES THE CORE, through the told run and the merge.
wrap-take : ∀ n {A} (o : SObs [] A) → Wrapped n o (enter (approx n (elab (λ i → i) (plain o)) []) coreAt) coreAt
          → Wrapped n o (enter (approx n (takeWhile true unfinished (sourced o)) []) root) root
wrap-take n o (M , hm , δ , at , c) = M , hm , ix 0 ∷ ix 1 ∷ ix 1 ∷ δ , at , Wrap.carried n o hm c

-- The restamp and projection, over the takeWhile.
wrap-restamp : ∀ n {A} (o : SObs [] A) → Wrapped n o (enter (approx n (takeWhile true unfinished (sourced o)) []) root) root
             → Wrapped n o (enter (approx n (elaborate (plain o)) []) root) root
wrap-restamp n o (M , hm , δ , at , c) =
  M , hm , δ , at , Folded.carried restamp stamp₀ proj₂ restamp-vals (approx n (takeWhile true unfinished (sourced o)) []) root
                      (inv-approx n (takeWhile true unfinished (sourced o)) [] (λ ()) root ok₀) c
  where
    ok₀ : Ok (Hots []) root
    ok₀ = tt , λ ()

-- THE WRAPPER CARRIES THE CORE, at each approximant, stage by stage.
carry-wrap : ∀ n {A} (o : SObs [] A) {M} → Emb M → M root coreAt
           → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root)
               (enter (approx n (elab (λ i → i) (plain o)) []) coreAt) root coreAt
           → Wrapped n o (enter (approx n (elaborate (plain o)) []) root) root
carry-wrap n o {M} hm m c =
  wrap-restamp n o (wrap-take n o (M , hm , [] , subst (M root) (sym (⊕-identityʳ coreAt)) m , c))
