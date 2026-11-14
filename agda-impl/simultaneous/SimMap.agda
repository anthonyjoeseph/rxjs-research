{-# OPTIONS --guardedness #-}

-- A MAP SIMULATES ITS MAP: both keep their source's positions and kinds,
-- so the source's simulation carries row for row, along the same map,
-- up to the same bound.  A mark mapped is a mark, a value shown mapped is
-- its value mapped.
module simultaneous.SimMap where

import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; map)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; Truncate; MapT; map-out; map-skip; map-pin; map-end; enter; approx)
open import denotation.Laws.Modulus using (entered-reach)
open import denotation.Laws.Worlds using (_⊑_)
open import adequacy.SubOne using (map-reach)
open import simultaneous.InstEmit using (instEmit; value; mark; valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (PMap; Sim; Mt; m-out; m-skip; m-mark; m-end; m-pin; Upto; Under; ListedB; BoundOk; Shows; Shown; SimIH; sih)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; mapIE)

------------------------------------------------------------------------
-- Values through the map

values-map : ∀ {A B} (f : A → B) (b : IE A) → valuesOf (mapIE f b) ≡ L.map f (valuesOf b)
values-map f (instEmit (value _) _) = refl
values-map f (instEmit (mark _) _)  = refl

shows-map : ∀ {A B} (f : A → B) {a} {b : IE A} → Shows a b → Shows (f a) (mapIE f b)
shows-map f {b = b} sh = trans (values-map f b) (cong (L.map f) sh)

shown← : ∀ {A B} (f : A → B) {b : IE A} → Shown (mapIE f b) → Shown b
shown← f {instEmit (value _) _} _  ()
shown← f {instEmit (mark _) _}  sh _ = sh refl

unshown→ : ∀ {A B} (f : A → B) {b : IE A} → ¬ Shown b → ¬ Shown (mapIE f b)
unshown→ f {instEmit (value _) _} ¬sh _ = ¬sh λ ()
unshown→ f {instEmit (mark _) _}  _  sh = sh refl

------------------------------------------------------------------------
-- The simulation, carried

module Mapped {A B : Set} (f : A → B) (d : Den A) (d′ : Den (IE A)) (p p′ : Pos) where

  t₀ : EmissionSet A
  t₀ = enter d p

  u₀ : EmissionSet (IE A)
  u₀ = enter d′ p′

  T : EmissionSet B
  T = Truncate (MapT f t₀)

  U : EmissionSet (IE B)
  U = Truncate (MapT (mapIE f) u₀)

  -- A source row, mapped, entered.
  up : ∀ {k e} → t₀ k e → Σ (Ev B) (T k)
  up {e = out _} x = _ , map-out x , map-reach (entered-reach d p) (map-out x)
  up {e = skip}  x = _ , map-skip x , map-reach (entered-reach d p) (map-skip x)
  up {e = end}   x = _ , map-end x , map-reach (entered-reach d p) (map-end x)
  up {e = pin _} x = _ , map-pin x , map-reach (entered-reach d p) (map-pin x)

  down : ∀ {k e} → T k e → Σ (Ev A) (t₀ k)
  down (map-out x , _)  = _ , x
  down (map-skip x , _) = _ , x
  down (map-pin x , _)  = _ , x
  down (map-end x , _)  = _ , x

  listed : ∀ {c} → ListedB T c → ListedB t₀ c
  listed (ks , cov , back) = ks , (λ x u → cov (proj₂ (up x)) u) , λ m → down (proj₂ (back m))

  bound : ∀ {Amb c} → BoundOk Amb T c → BoundOk Amb t₀ c
  bound {c = nothing} _              = tt
  bound {c = just _}  (inj₁ a)       = inj₁ a
  bound {c = just _}  (inj₂ (_ , x)) = inj₂ (down x)

  module _ {M : PMap} {c : Maybe Pos} (S : Sim Shows Shown M p c t₀ u₀) where
    open Sim S

    mapped : Sim Shows Shown M p c T U
    mapped = record
      { bnd = bnd
      ; fwd = fw
      ; val← = λ { (map-out x , _) sh un → bv x sh un }
      ; end← = λ { (map-end x , _) un → be x un }
      ; pin← = λ { (map-pin x , _) m un → bp x m un }
      ; upto = proj₁ upto , λ { (map-out x , _) un → proj₂ upto x un ; (map-skip x , _) un → proj₂ upto x un
                                ; (map-pin x , _) un → proj₂ upto x un ; (map-end x , _) un → proj₂ upto x un } }
      where
      ent : ∀ {l e} → MapT (mapIE f) u₀ l e → U l e
      ent m = m , map-reach (entered-reach d′ p′) m

      fw : ∀ {k e} → T k e → Upto c k → Σ Pos λ y → M k y × Σ Pos λ l → y ⊑ l × Σ (Ev (IE B)) λ e′ → U l e′ × Mt Shows Shown M e e′
      fw (map-out x , _) u with fwd x u
      ... | y , m , l , yl , _ , ux , m-out sh   = y , m , l , yl , _ , ent (map-out ux) , m-out (shows-map f sh)
      fw (map-skip x , _) u with fwd x u
      ... | y , m , l , yl , _ , ux , m-skip     = y , m , l , yl , _ , ent (map-skip ux) , m-skip
      ... | y , m , l , yl , _ , ux , m-mark ¬sh = y , m , l , yl , _ , ent (map-out ux) , m-mark (unshown→ f ¬sh)
      fw (map-pin x , _) u with fwd x u
      ... | y , m , l , yl , _ , ux , m-pin mr   = y , m , l , yl , _ , ent (map-pin ux) , m-pin mr
      fw (map-end x , _) u with fwd x u
      ... | y , m , l , yl , _ , ux , m-end      = y , m , l , yl , _ , ent (map-end ux) , m-end

      bv : ∀ {l b} → u₀ l (out b) → Shown (mapIE f b) → Under M c l
         → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × Σ B λ a → T k (out a) × Shows a (mapIE f b)
      bv x sh un with val← x (shown← f sh) un
      ... | k , y , m , yl , a , tx , v = k , y , m , yl , f a , proj₂ (up tx) , shows-map f v

      be : ∀ {l} → u₀ l end → Under M c l → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × T k end
      be x un with end← x un
      ... | k , y , m , yl , tx = k , y , m , yl , proj₂ (up tx)

      bp : ∀ {l r r′} → u₀ l (pin r′) → M r r′ → Under M c l → Σ Pos λ k → Σ Pos λ y → M k y × y ⊑ l × T k (pin r)
      bp x mr un with pin← x mr un
      ... | k , y , m , yl , tx = k , y , m , yl , proj₂ (up tx)

-- THE FORMER: the source's simulation, mapped.
sim-map : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) (s : Obs Timeline Γ A)
        → SimIH n ρ s → SimIH n ρ (map f s)
sim-map n ρ f s (sih ih) = sih λ env env′ Amb c ge ge′ es em p p′ ap fr ok ok′ L B →
  let open Mapped f (approx n s env) (approx n (elab ρ s) env′) p p′
      (M , lc , eb , S) = ih env env′ Amb c ge ge′ es em p p′ ap fr ok ok′ (listed L) (bound B)
  in M , lc , eb , mapped S
