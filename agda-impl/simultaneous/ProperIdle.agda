{-# OPTIONS --guardedness #-}

-- A STREAM'S PROPER ROWS ARE IDLE WHERE THE STREAM IS: past an end only
-- silent rows lie, so every row told of is proper, every row before a
-- proper row is, and a run of the proper rows is a run of the stream.
module simultaneous.ProperIdle where

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import denotation.Events using (Timeline; fresh)
open import denotation.Position using (root; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; end; EmissionSet; Proper; Few; Silent; _≺_)
open import denotation.Read using (Run; Visible; cursor; loud)
import denotation.Read as R
open import denotation.Laws.Modulus using (≺-trans; ≼-or-≻; ≼-split)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Routed using (Idle)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

module _ {A : Set} {S : EmissionSet (IE A)}
         (quiet : ∀ {c y e} → S c end → S y e → c ≺ y → Silent e)
         (func : ∀ {y e e′} → S y e → S y e′ → e ≡ e′) where

  private
    vis : ∀ {y e} → S y e → Visible e → Proper S y e
    vis r v = r , λ sc cy → loud v (quiet sc r cy)

    below : ∀ {q e k e′} → Proper S q e → S k e′ → k ≺ q → Proper S k e′
    below {q} {k = k} pq rk kq = rk , λ {c} sc ck → proj₂ pq sc (≺-trans {c} {k} {q} ck kq)

    few-up : ∀ {q e} → Proper S q e → Few (Proper S) q → Few S q
    few-up pq (ks , h) = ks , λ rk kq → h (below pq rk kq) kq

  -- A run of the proper rows is a run of the stream.
  run-up : ∀ {c rs} → Run (Proper S) c rs → Run S c rs
  run-up R.[] = R.[]
  run-up ((((pq , _) , fw) , v , a , l) R.∷ rest) = ((pq , few-up pq fw) , v , a , λ rk v′ ak → l (vis rk v′) v′ ak) R.∷ run-up rest

  private
    -- The cursor is the last row met.
    last : ∀ {c rs z} → Run S c rs → cursor c rs ≡ just z → c ≡ just z ⊎ Σ (Ev (IE A)) λ e → (z , e) ∈ rs × Proper S z e
    last R.[] eq = inj₁ eq
    last {rs = (q , e) ∷ _} ((sn , _) R.∷ rest) eq with last rest eq
    ... | inj₁ refl         = inj₂ (e , here refl , proj₁ sn)
    ... | inj₂ (e′ , i , p) = inj₂ (e′ , there i , p)

  proper-idle : Idle S → Idle (Proper S)
  proper-idle idle {rs} mt ne {w} fw aw lst = idle (run-up mt) ne (few-w fw) aw (λ r v a → lst (vis r v) v a)
    where
      -- No end lies before `w`: past the cursor the next row lies past `w`,
      -- and at or before it the run met an end, or a row past one.
      no-end : ∀ {c} → S c end → c ≺ w → ⊥
      no-end {c} sc cw with cursor nothing rs in eq
      ... | nothing = lst (vis sc tt) tt tt cw
      ... | just z with last (run-up mt) eq
      ...   | inj₁ ()
      ...   | inj₂ (e , i , pz) with ≼-or-≻ c z
      ...     | inj₂ zc = lst (vis sc tt) tt zc cw
      ...     | inj₁ cz with ≼-split {c} {z} cz
      ...       | inj₁ cz′ = proj₂ pz sc cz′
      ...       | inj₂ refl = ne (subst (λ x → (c , x) ∈ rs) (func (proj₁ pz) sc) i)

      few-w : Few (Proper S) w → Few S w
      few-w (ks , h) = ks , λ {k} rk kw → h (rk , λ {c} sc ck → no-end sc (≺-trans {c} {k} {w} ck kw)) kw
