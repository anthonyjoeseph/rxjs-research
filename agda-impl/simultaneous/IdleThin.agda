{-# OPTIONS --guardedness #-}

-- A STREAM SHOWING ITS PROGRAM'S ROWS IS IDLE LIKE IT, UP TO ITS CUT
-- (`Thin.idle`).  Every visible row of the stream is the program's, or a
-- value moving no route at a place the program holds nothing; every row
-- of the program sits at a row of the stream, its visible ones shown as
-- they are but its end.  A run met of the stream, thinned of its silent
-- values, is then a run of the program with the same count.
--
-- Past the program's end the program waits on nothing, so a reader there
-- reads the program's count at that end, which names its instant: a
-- reader past the end with few rows before it and no cut before it is
-- in that instant.
module simultaneous.IdleThin where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (decidable-stable; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; instant; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; Few; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺→≼; ≺-≼-≺; ≼-or-≻; ≼-split)
open import denotation.Laws.Worlds using (InvAt)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Idle; cnt; nameOf; nm)
open import simultaneous.HeldTo using (Unfailed; IdleTo)
open import simultaneous.Layers using (after-≺)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; count)

module Thin {X : Set} (keep : IE X → Bool) (t u : EmissionSet (IE X)) {H : Pos → Set} {q₀ : Pos} (Iu : InvAt H q₀ u) (iu : Idle u)
            (vis : ∀ {q v} → t q (out v) → u q (out v) ⊎ ((∀ r → count r v ≡ r) × (∀ {e′} → u q e′ → ⊥)))
            (lift : ∀ {q e} → u q e → Σ (Ev (IE X)) (t q))
            (lift-vis : ∀ {q v} → u q (out v) → t q (out v))
            (late : ∀ {c} → u c end → ∀ {w} → c ≺ w → Few t w → Unfailed keep t w → ¬ ¬ (instant w ≡ instant c)) where

  Row : Set
  Row = Pos × Ev (IE X)

  -- A run's rows, its silent values dropped.
  data Thin : List Row → List Row → Set where
    []  : Thin [] []
    kp  : ∀ {q e rs rs′} → u q e → Thin rs rs′ → Thin ((q , e) ∷ rs) ((q , e) ∷ rs′)
    dp  : ∀ {q v rs rs′} → (∀ r → count r v ≡ r) → (∀ {e′} → u q e′ → ⊥) → Thin rs rs′ → Thin ((q , out v) ∷ rs) rs′

  thin : ∀ {c rs} → Run t c rs → (∀ {k} → (k , end) ∈ rs → ⊥) → Σ (List Row) (Thin rs)
  thin [] _ = [] , []
  thin {rs = (q , out v) ∷ _} ((((x , _) , _) , _) ∷ r) ne with vis x | thin r (λ i → ne (there i))
  ... | inj₁ y          | rs′ , th = (q , out v) ∷ rs′ , kp y th
  ... | inj₂ (mu , nu) | rs′ , th = rs′ , dp mu nu th
  thin {rs = (_ , end) ∷ _}   _ ne = ⊥-elim (ne (here refl))
  thin {rs = (_ , skip) ∷ _}  ((_ , () , _) ∷ _) _
  thin {rs = (_ , pin _) ∷ _} ((_ , () , _) ∷ _) _

  fold : ∀ {rs rs′} → Thin rs rs′ → ∀ r → L.foldl count r (values rs) ≡ L.foldl count r (values rs′)
  fold []                     r = refl
  fold (kp {e = out v} _ th)  r = fold th (count r v)
  fold (kp {e = skip} _ th)   r = fold th r
  fold (kp {e = pin _} _ th)  r = fold th r
  fold (kp {e = end} _ th)    r = fold th r
  fold (dp {rs = rs} mu _ th) r = trans (cong (λ z → L.foldl count z (values rs)) (mu r)) (fold th r)

  ends : ∀ {rs rs′} → Thin rs rs′ → ∀ {c} → (c , end) ∈ rs′ → (c , end) ∈ rs
  ends (kp _ th)   (here refl) = here refl
  ends (kp _ th)   (there i)   = there (ends th i)
  ends (dp _ _ th) i           = there (ends th i)

  few : ∀ {w} → Few t w → Few u w
  few (ks , h) = ks , λ x lt → h (proj₂ (lift x)) lt

  -- Nothing the program shows lies past its end.
  proper-vis : ∀ {c y e} → u c end → u y e → Visible e → y ≼ c
  proper-vis uc uy vi cy with InvAt.quiet Iu uc uy cy
  ... | _ , refl , _ = vi

  -- READ ALONG A RUN: the thinned rows are a run of the program, and past
  -- the stream's cursor is past the program's, and a row of the program's
  -- but its end past its cursor is past the stream's.
  run : ∀ {c c′ rs rs′} → Run t c rs → Thin rs rs′
      → (∀ {y} → After c y → After c′ y) → (∀ {k v} → u k (out v) → After c′ k → After c k)
      → Run u c′ rs′ × (∀ {y} → After (cursor c rs) y → After (cursor c′ rs′) y)
                     × (∀ {k v} → u k (out v) → After (cursor c′ rs′) k → After (cursor c rs) k)
  run [] [] i2 i1 = [] , i2 , i1
  run {c} {c′} ((((x , _) , fw) , vi , ac , lst) ∷ r) (kp {q} y th) i2 i1 =
    let (r′ , j2 , j1) = run r th (λ a → a) (λ _ a → a)
    in (((y , λ ce → proper-vis ce y vi) , few fw) , vi , i2 ac , lu) ∷ r′ , j2 , j1
    where
      lu : ∀ {k e′} → u k e′ → Visible e′ → After c′ k → q ≼ k
      lu {e′ = out _} uk vk ak = lst (lift-vis uk) vk (i1 uk ak)
      lu {e′ = end}   uk _  _  = proper-vis uk y vi
      lu {e′ = skip}  _  () _
      lu {e′ = pin _} _  () _
  run {c} {c′} ((((x , _) , _) , vi , ac , lst) ∷ r) (dp {q} _ nu th) i2 i1 = run r th i2′ i1′
    where
      i2′ : ∀ {y} → q ≺ y → After c′ y
      i2′ qy = after-≺ c′ (i2 ac) qy

      i1′ : ∀ {k v} → u k (out v) → After c′ k → q ≺ k
      i1′ {k} uk ak with ≼-split {q} {k} (lst (lift-vis uk) tt (i1 uk ak))
      ... | inj₁ lt   = lt
      ... | inj₂ refl = ⊥-elim (nu uk)

  Goal : List Row → Pos → Set
  Goal rs w = proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

  module Main {rs rs′} (mt : Met t rs) (th : Thin rs rs′) (ne : ∀ {c} → (c , end) ∈ rs → ⊥) {w : Pos} (unf : Unfailed keep t w)
              (fw : Few t w) (aw : After (cursor nothing rs) w) (lw : ∀ {y e} → t y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              (ng : Goal rs w → ⊥) where

    R : Run u nothing rs′ × (∀ {y} → After (cursor nothing rs) y → After (cursor nothing rs′) y)
                          × (∀ {k v} → u k (out v) → After (cursor nothing rs′) k → After (cursor nothing rs) k)
    R = run {nothing} {nothing} mt th (λ _ → tt) (λ _ _ → tt)

    mu : Met u rs′
    mu = proj₁ R

    j1 : ∀ {k v} → u k (out v) → After (cursor nothing rs′) k → After (cursor nothing rs) k
    j1 = proj₂ (proj₂ R)

    ne′ : ∀ {c} → (c , end) ∈ rs′ → ⊥
    ne′ i = ne (ends th i)

    E : cnt rs ≡ cnt rs′
    E = fold th r₀

    back : ∀ {z} → Goal rs′ z → nameOf z ≡ nameOf w → Goal rs w
    back (inj₁ e) _  = inj₁ (trans (cong proj₂ E) e)
    back (inj₂ e) nz = inj₂ (trans (cong proj₁ E) (trans e nz))

    -- Past the program's end: its count there, of its instant.
    from-late : ∀ {c} → u c end → c ≺ w → After (cursor nothing rs′) c → instant w ≡ instant c → Goal rs w
    from-late {c} uc cw ac ic =
      back {c} (iu mu ne′ (few (proj₁ fw , λ {k} x lt → proj₂ fw x (≺-trans {k} {c} {w} lt cw))) ac lc) (cong (λ j → nm (j ∙ [])) (sym ic))
      where
        lc : ∀ {y e} → u y e → Visible e → After (cursor nothing rs′) y → c ≼ y
        lc {y} {e = out _} uy vy ay = ≺→≼ {c} {y} (≺-≼-≺ {c} {w} {y} cw (lw (lift-vis uy) vy (j1 uy ay)))
        lc {e = end}   uy _  _  = proper-vis uy uc tt
        lc {e = skip}  _  () _
        lc {e = pin _} _  () _

    lu : ∀ {y e} → u y e → Visible e → After (cursor nothing rs′) y → w ≼ y
    lu {e = out _} uy vy ay = lw (lift-vis uy) vy (j1 uy ay)
    lu {y} {e = end} uy _ ay with ≼-or-≻ w y
    ... | inj₁ le = le
    ... | inj₂ yw = ⊥-elim (late uy yw fw unf λ ic → ng (from-late uy yw ay ic))
    lu {e = skip}  _  () _
    lu {e = pin _} _  () _

    absurd : ⊥
    absurd = ng (back {w} (iu mu ne′ (few fw) (proj₁ (proj₂ R) aw) lu) refl)

  idle : IdleTo keep t
  idle {rs} mt ne {w} unf fw aw lw with thin mt ne
  ... | rs′ , th = decidable-stable ((proj₂ (cnt rs) ≟ⁿ 0) ⊎-dec (proj₁ (cnt rs) ≟ᵖ nameOf w)) λ ng → Main.absurd mt th ne unf fw aw lw ng
