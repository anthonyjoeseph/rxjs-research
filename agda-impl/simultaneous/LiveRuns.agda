{-# OPTIONS --guardedness #-}

-- A RUN BEFORE ITS END: what tracks a body's runs that have not ended
-- tracks all of them, for an end is met last and nothing it bounds lies
-- past it that does not lie past the run before it.
module simultaneous.LiveRuns where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-∃++)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin)
open import denotation.Read using (Run; []; _∷_; After; cursor)
open import denotation.Laws.Modulus using (≺-trans)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (cnt)
open import simultaneous.InstEmit using (instEmit; mark; begin)
open import simultaneous.Readings using (rootOf)
open import simultaneous.HeldIn using (Upto)
open import simultaneous.HeldJoin using (cnt-++)
open import simultaneous.HeldConnect using (Tracks)
open import simultaneous.Layers using (snoc-view; run-row; run-tail; cursor-snoc; run-past-end)
open import simultaneous.Project using (run-prefix)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- No end is met before a run's last row.
pre-noend : ∀ {A} {t : EmissionSet A} pre {w e c} → Run t nothing (pre ++ [ (w , e) ]) → (c , end) ∈ pre → ⊥
pre-noend {t = t} pre {w} {e} {c} run i with ∈-∃++ i
... | as , bs , refl with run-tail as (subst (Run t nothing) (++-assoc as ((c , end) ∷ bs) [ (w , e) ]) run)
...   | (((ce , _) , _) , _) ∷ rest = nonempty bs (run-past-end ce rest)
  where nonempty : ∀ (zs : List (Pos × Ev _)) → zs ++ [ (w , e) ] ≡ [] → ⊥
        nonempty []      ()
        nonempty (_ ∷ _) ()

-- A row before a value meets an end only before it.
last-out : ∀ {A} {ys : List (Pos × Ev A)} {c c′} {a : A} → (∀ {c″} → (c″ , end) ∈ ys → ⊥)
         → (c′ , end) ∈ ys ⊎ (c′ , end) ∈ [ (c , out a) ] → ⊥
last-out ne (inj₁ i)          = ne i
last-out ne (inj₂ (here ()))
last-out ne (inj₂ (there ()))

-- A run met meets no end, or meets one last after a run that meets none.
end-view : ∀ {A} {t : EmissionSet A} {rs} → Met t rs
         → (∀ {c} → (c , end) ∈ rs → ⊥)
         ⊎ Σ (List (Pos × Ev A)) λ ys → Σ Pos λ c → rs ≡ ys ++ [ (c , end) ] × (∀ {c′} → (c′ , end) ∈ ys → ⊥)
end-view {rs = rs} m with snoc-view rs
... | inj₁ refl = inj₁ λ ()
... | inj₂ (ys , (c , end) , refl) = inj₂ (ys , c , refl , pre-noend ys m)
... | inj₂ (ys , (c , out a) , refl) = inj₁ λ i → last-out {ys = ys} (pre-noend ys m) (∈-++⁻ ys i)
... | inj₂ (ys , (c , skip) , refl) with run-row m (∈-++⁺ʳ ys (here refl))
...   | _ , ()
end-view {rs = rs} m | inj₂ (ys , (c , pin _) , refl) with run-row m (∈-++⁺ʳ ys (here refl))
...   | _ , ()

-- Past the end, past the run before it.
past-end : ∀ {A} {t : EmissionSet A} ys {c} → Met t (ys ++ [ (c , end) ]) → ∀ {y} → After (cursor nothing (ys ++ [ (c , end) ])) y
         → After (cursor nothing ys) y
past-end {t = t} ys {c} m {y} a with run-tail ys m
... | (_ , _ , ac , _) ∷ _ = go (cursor nothing ys) ac (subst (λ w → After w y) (cursor-snoc nothing ys) a)
  where
    go : ∀ w → After w c → After (just c) y → After w y
    go nothing    _  _  = tt
    go (just c₀) c₀c cy = ≺-trans {c₀} {c} {y} c₀c cy

-- A value met before the end is met before it.
before-end : ∀ {A} (ys : List (Pos × Ev A)) {c q a} → (q , out a) ∈ ys ++ [ (c , end) ] → (q , out a) ∈ ys
before-end ys i with ∈-++⁻ ys i
... | inj₁ i′ = i′
... | inj₂ (here ())
... | inj₂ (there ())

-- WHAT TRACKS THE RUNS NOT ENDED TRACKS THEM ALL.
tracks-live : ∀ {A B} {D : Pos → Set} {σ : EmissionSet A} {β : EmissionSet (IE B)}
            → (∀ {rs} → Met β rs → (∀ {c} → (c , end) ∈ rs → ⊥) → Upto D rs → proj₂ (cnt rs) ≡ 0
               → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs)))) ∈ rs
               → Σ (List Pos) λ ks → ∀ {k e} → σ k e → After (cursor nothing rs) k → rootOf k ≡ rootOf q → k ∈ ks)
            → Tracks D σ β
tracks-live h m up z bq with end-view m
... | inj₁ ne = h m ne up z bq
... | inj₂ (ys , c , refl , ne) =
  let eq = cnt-++ ys [ (c , end) ]
      (ks , hk) = h (run-prefix ys m) ne (λ i → up (∈-++⁺ˡ i)) (trans (cong proj₂ (sym eq)) z)
                    (before-end ys (subst (λ r → (_ , out (instEmit (mark begin) (proj₁ r))) ∈ (ys ++ [ (c , end) ])) eq bq))
  in ks , λ x a r → hk x (past-end ys m a) r
