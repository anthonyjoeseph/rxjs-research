{-# OPTIONS --guardedness #-}

-- A DEFER IS ITS BODY, subscribed one label down, behind a guard no
-- reader meets: each row met of it is the body's row, so it holds what
-- the body holds, the body's own burst lying in the defer's.
module simultaneous.HeldDefer where

open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl; trans)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; enter; module Op; Reach; DeferT; guard; body; out; end)
open import denotation.Read using (Run; []; _∷_)
open import denotation.Laws.Modulus using (entered-reach)
open import denotation.Laws.Worlds using (⊑-trans; ⊑-inside; inside-⊑)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Sync; Ex; Rest; Placed)
open import simultaneous.Relabel using (held-same; Same; Rows≈)
open import simultaneous.HeldConnect using (rootOf-ext; held-ex; same-refl; rows-refl)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- The body's burst lies in the defer's.
sync-up : ∀ {p y} zs → Sync (p ⊕ zs) y → Sync p y
sync-up {p} {y} zs (ins , rt) =
  ⊑-inside {p} {y} (⊑-trans {p} {p ⊕ zs} {y} (zs , refl) (inside-⊑ (p ⊕ zs) y ins)) , trans rt (rootOf-ext p zs)

module DeferRun {A : Set} (s : Den A) (p : Pos) where

  B : EmissionSet A
  B = enter s (p ⊕ [ ix 1 ])

  D : EmissionSet A
  D = enter (Op.defer s) p

  -- A body row waits on what it waits on in the body, and the guard.
  lift : ∀ {y e} → B y e → D y e
  lift x = body x , reach (entered-reach s (p ⊕ [ ix 1 ]) x)
    where
      reach : ∀ {y e} → Reach B y e → Reach (DeferT s p) y e
      reach (ks , h) = (p ⊕ [ ix 0 ]) ∷ ks , λ { guard _ _ → here refl ; (body x′) ky d → there (h x′ ky d) }

  back : ∀ {c rs} → Run D c rs → Run B c rs
  back [] = []
  back (((((body x , _) , pr) , ks , few) , vi , ac , lf) ∷ run) =
    (((x , λ x′ → pr (lift x′)) , ks , λ x′ k≺ → few (lift x′) k≺) , vi , ac , (λ x′ v a → lf (lift x′) v a)) ∷ back run
  back (((((guard , _) , _) , _) , () , _) ∷ _)

held-defer : ∀ {X : Set} (s : Den (IE X)) p cs → Held (enter s (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs) → Held (enter (Op.defer s) p) (p ∷ cs)
held-defer {X} s p cs H = held-ex ex (held-same row end-row back′ (λ _ x _ k → k (_ , lift x , λ v → v)) rest′ H)
  where
    open DeferRun s p

    ex : ∀ {y} → Ex ((p ⊕ [ ix 1 ]) ∷ cs) y → Ex (p ∷ cs) y
    ex {y} (here sy) = here (sync-up {p} {y} [ ix 1 ] sy)
    ex (there x) = there x

    row : ∀ {y x′} → D y (out x′) → Σ (IE X) λ x → B y (out x) × Same x′ x
    row (body x , _) = _ , x , same-refl _

    end-row : ∀ {y} → D y end → B y end
    end-row (body x , _) = x

    back′ : ∀ {rs′} → Met D rs′ → Σ _ λ rs → Met B rs × Rows≈ rs′ rs
    back′ m = _ , back m , rows-refl m

    rest′ : Rest B → Rest D
    rest′ R m z bq with R (back m) z bq
    ... | ks , h = (p ⊕ [ ix 0 ]) ∷ ks , λ { (guard , _) _ _ → here refl ; (body x , _) ay rt → there (h x ay rt) }

-- A defer hangs a lane only where its body does: the guard shows nothing.
placed-defer : ∀ {X : Set} {F : Pos → Set} (s : Den (IE X)) p → Placed F (enter s (p ⊕ [ ix 1 ])) → Placed F (enter (Op.defer s) p)
placed-defer s p pl (body x , _) sh = pl x sh
placed-defer s p pl (guard , _) ()
