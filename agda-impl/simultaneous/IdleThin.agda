{-# OPTIONS --guardedness #-}

-- A STREAM SHOWING ITS PROGRAM'S ROWS IS IDLE LIKE IT, UP TO ITS CUT
-- (`Thin.idle`).  Every visible row of the stream is the program's, or a
-- value moving no route at a place the program holds nothing; the program
-- has few rows wherever the stream does, and its values are the stream's.  A run met of the stream, thinned of its silent
-- values, is then a run of the program with the same count.
--
-- Past the program's end the program waits on nothing, so a reader there
-- reads the program's count at that end, which names its instant: a
-- reader past the end with few rows before it, no cut before it and the
-- stream's own end not before it is in that instant.
module simultaneous.IdleThin where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
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
open import simultaneous.Layers using (after-≺; Last; last-met)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; count)

module Thin {X : Set} (keep : IE X → Bool) (t u : EmissionSet (IE X)) {H : Pos → Set} {q₁ : Pos} (It : InvAt H q₁ t)
            (proper-vis : ∀ {c y e} → u c end → u y e → Visible e → y ≼ c) (iu : Idle u)
            (vis : ∀ {q v} → t q (out v) → u q (out v) ⊎ ((∀ r → count r v ≡ r) × (∀ {e′} → u q e′ → ⊥)))
            (few-to : ∀ {w} → Few t w → ¬ ¬ Few u w) (u-few : ∀ {q e} → u q e → Visible e → Few u q)
            (lift-vis : ∀ {q v} → u q (out v) → t q (out v))
            (late : ∀ {c} → u c end → ∀ {w} → c ≺ w → Few t w → Unfailed keep t w → (∀ {c′} → t c′ end → w ≼ c′) → ¬ ¬ (instant w ≡ instant c)) where

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

  -- READ ALONG A RUN: the thinned rows are a run of the program, and past
  -- the stream's cursor is past the program's, and a row of the program's
  -- but its end past its cursor is past the stream's.
  run : ∀ {c c′ rs rs′} → Run t c rs → Thin rs rs′
      → (∀ {y} → After c y → After c′ y) → (∀ {k v} → u k (out v) → After c′ k → After c k)
      → Run u c′ rs′ × (∀ {y} → After (cursor c rs) y → After (cursor c′ rs′) y)
                     × (∀ {k v} → u k (out v) → After (cursor c′ rs′) k → After (cursor c rs) k)
  run [] [] i2 i1 = [] , i2 , i1
  run {c} {c′} ((((x , _) , _) , vi , ac , lst) ∷ r) (kp {q} y th) i2 i1 =
    let (r′ , j2 , j1) = run r th (λ a → a) (λ _ a → a)
    in (((y , λ ce → proper-vis ce y vi) , u-few y vi) , vi , i2 ac , lu) ∷ r′ , j2 , j1
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
    from-late : ∀ {c} → u c end → c ≺ w → After (cursor nothing rs′) c → instant w ≡ instant c → ⊥
    from-late {c} uc cw ac ic =
      few-to (proj₁ fw , λ {k} x lt → proj₂ fw x (≺-trans {k} {c} {w} lt cw)) λ fu →
      ng (back {c} (iu mu ne′ fu ac lc) (cong (λ j → nm (j ∙ [])) (sym ic)))
      where
        lc : ∀ {y e} → u y e → Visible e → After (cursor nothing rs′) y → c ≼ y
        lc {y} {e = out _} uy vy ay = ≺→≼ {c} {y} (≺-≼-≺ {c} {w} {y} cw (lw (lift-vis uy) vy (j1 uy ay)))
        lc {e = end}   uy _  _  = proper-vis uy uc tt
        lc {e = skip}  _  () _
        lc {e = pin _} _  () _

    -- The stream's end lies past the run's cursor: nothing but a pin follows it.
    tend : ∀ {c′} → t c′ end → w ≼ c′
    tend {c′} tc = lw tc tt (aft (cursor nothing rs) (last-met mt))
      where
        aft : ∀ c → Last t c rs → After c c′
        aft nothing  _ = tt
        aft (just y) (e , i , ty , vy) with ≼-or-≻ c′ y
        ... | inj₂ yc = yc
        ... | inj₁ cy with ≼-split {c′} {y} cy
        ...   | inj₁ lt with InvAt.quiet It tc ty lt
        ...     | _ , refl , _ = ⊥-elim vy
        aft (just y) (e , i , ty , vy) | inj₁ cy | inj₂ refl with InvAt.func It tc ty
        ... | refl = ⊥-elim (ne i)

    lu : ∀ {y e} → u y e → Visible e → After (cursor nothing rs′) y → w ≼ y
    lu {e = out _} uy vy ay = lw (lift-vis uy) vy (j1 uy ay)
    lu {y} {e = end} uy _ ay with ≼-or-≻ w y
    ... | inj₁ le = le
    ... | inj₂ yw = ⊥-elim (late uy yw fw unf tend λ ic → from-late uy yw ay ic)
    lu {e = skip}  _  () _
    lu {e = pin _} _  () _

    absurd : ⊥
    absurd = few-to fw λ fu → ng (back {w} (iu mu ne′ fu (proj₁ (proj₂ R) aw) lu) refl)

  idle : IdleTo keep t
  idle {rs} mt ne {w} unf fw aw lw with thin mt ne
  ... | rs′ , th = decidable-stable ((proj₂ (cnt rs) ≟ⁿ 0) ⊎-dec (proj₁ (cnt rs) ≟ᵖ nameOf w)) λ ng → Main.absurd mt th ne unf fw aw lw ng
