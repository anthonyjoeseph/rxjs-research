{-# OPTIONS --guardedness #-}

-- A MAP SIMULATES ITS MAP: both keep their source's positions and kinds,
-- so the source's simulation carries row for row, along the same map,
-- up to the same bound.  A value shown mapped shows its value mapped.
module simultaneous.SimMap where

import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Tree using (Obs; map)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; Truncate; MapT; map-out; map-skip; map-pin; map-end; enter; approx)
open import denotation.Laws.Modulus using (entered-reach)
open import adequacy.SubOne using (map-reach)
open import simultaneous.InstEmit using (instEmit; value; mark; valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (PMap; Sim; Run; Late; LateL; LateU; lateU-pin; Mt; m-out; m-end; Carried; c-out; c-end; Upto; Under; ListedB; Live; env-live; NoneUnder; Shows; Shown; SimIH; sih)

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

  -- A source row, mapped, entered.
  ent : ∀ {l e} → MapT (mapIE f) u₀ l e → U l e
  ent m = m , map-reach (entered-reach d′ p′) m

  ent′ : ∀ {l e} → u₀ l e → Σ (Ev (IE B)) (U l)
  ent′ {e = out _} x = _ , ent (map-out x)
  ent′ {e = skip}  x = _ , ent (map-skip x)
  ent′ {e = pin _} x = _ , ent (map-pin x)
  ent′ {e = end}   x = _ , ent (map-end x)

  -- A late source pin, mapped: late.
  late-up : ∀ {b k e} (x : t₀ k e) → Late b e → Late b (proj₁ (up x))
  late-up {nothing} x ()
  late-up {just _} {e = pin _} x (y , refl , lt) = y , refl , lt
  late-up {just _} {e = out _} x (_ , () , _)
  late-up {just _} {e = skip}  x (_ , () , _)
  late-up {just _} {e = end}   x (_ , () , _)

  late-listed : ∀ {b c} → LateL T b c → LateL t₀ b c
  late-listed (ks , cov , back) = ks , (λ x l u → cov (proj₂ (up x)) (late-up x l) u) , λ m → down (proj₂ (back m))

  -- A late mapped pin: its source's.
  late-row : ∀ {M b c ls} → (∀ {l e′} → u₀ l e′ → LateU M b e′ → Under M c l → l ∈ ls)
           → ∀ {l e′} → U l e′ → LateU M b e′ → Under M c l → l ∈ ls
  late-row {b = nothing} cov (map-pin x , _) () un
  late-row {b = just _}  cov (map-pin x , _) (y , my , x′ , refl , lt) un = cov x (y , my , x′ , refl , lt) un
  late-row cov (map-out x , _) lu un with lateU-pin lu
  ... | _ , ()
  late-row cov (map-skip x , _) lu un with lateU-pin lu
  ... | _ , ()
  late-row cov (map-end x , _) lu un with lateU-pin lu
  ... | _ , ()

  -- Live in the source: live in the map, which ends where it does.
  live : ∀ {j} → Live t₀ j → Live T j
  live {j} l (map-end x , _) = l x

  -- A carried row: its source's, carried.
  carried : ∀ {k e} → T k e → Carried e → Σ (Ev A) λ e₀ → t₀ k e₀ × Carried e₀
  carried (map-out x , _) c-out = _ , x , c-out
  carried (map-end x , _) c-end = _ , x , c-end

  -- Nothing under a mapped row but under its source's.
  none : ∀ {M} → NoneUnder M t₀ → NoneUnder M T
  none nu x m kx = nu (proj₂ (down x)) m kx

  module _ {M : PMap} {Img : Pos → Pos → Set} {c : Maybe Pos} (S : Sim Shows Shown M Img c t₀ u₀) where
    open Sim S

    mapped : Sim Shows Shown M Img c T U
    mapped = record
      { fwd     = fw
      ; val←    = λ { (map-out x , _) sh un → bv x sh un }
      ; end←    = λ { (map-end x , _) un → be x un }
      ; upto    = proj₁ upto , (λ { (map-out x , _) un → cov x un ; (map-skip x , _) un → cov x un
                                    ; (map-pin x , _) un → cov x un ; (map-end x , _) un → cov x un })
                  , λ m → ent′ (proj₂ (back m)) }
      where
      cov = proj₁ (proj₂ upto)
      back = proj₂ (proj₂ upto)

      fw : ∀ {k e} → T k e → Carried e → Upto c k → Σ Pos λ l → Img k l × Σ (Ev (IE B)) λ e′ → U l e′ × Mt Shows e e′
      fw (map-out x , _) _ u with fwd x c-out u
      ... | l , i , _ , ux , m-out sh = l , i , _ , ent (map-out ux) , m-out (shows-map f sh)
      fw (map-end x , _) _ u with fwd x c-end u
      ... | l , i , _ , ux , m-end    = l , i , _ , ent (map-end ux) , m-end

      bv : ∀ {l b} → u₀ l (out b) → Shown (mapIE f b) → Under M c l
         → Σ Pos λ k → Img k l × Σ B λ a → T k (out a) × Shows a (mapIE f b)
      bv x sh un with val← x (shown← f sh) un
      ... | k , i , a , tx , v = k , i , f a , proj₂ (up tx) , shows-map f v

      be : ∀ {l} → u₀ l end → Under M c l → Σ Pos λ k → Img k l × T k end
      be x un with end← x un
      ... | k , i , tx = k , i , proj₂ (up tx)

-- THE FORMER: the source's simulation, mapped.
sim-map : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) (s : Obs Timeline Γ A)
        → SimIH n ρ s → SimIH n ρ (map f s)
sim-map n ρ f s (sih ih) = sih λ env env′ Amb ge ge′ ap es ns em p p′ pp fr ok ok′ nh →
  let open Mapped f (approx n s env) (approx n (elab ρ s) env′) p p′
      (M , lc , eb , nu , ej , R) = ih env env′ Amb ge ge′ ap es ns em p p′ pp fr ok ok′ nh
      open Run R
  in M , lc , eb , none {M} (λ {k} {e} {x} {y} → nu {k} {e} {x} {y}) , ej
     , record { Img = Img ; img-fun = img-fun ; ext = ext
              ; sim = λ A′ inc ea c mp L lst → mapped (sim A′ inc ea c mp (env-live {ρ = ρ} {Amb = Amb} {env = env} {env′ = env′} es {T = T} {T′ = t₀} (λ {j} → live {j}) {A′} {c} L) (listed lst))
              ; late = λ A′ inc ea b c mp L lst ll →
                  let (ls , cov , back) = late A′ inc ea b c mp (env-live {ρ = ρ} {Amb = Amb} {env = env} {env′ = env′} es {T = T} {T′ = t₀} (λ {j} → live {j}) {A′} {b} L) (listed lst) (late-listed ll)
                  in ls , late-row cov , λ m → ent′ (proj₂ (back m))
              ; anchor = λ A′ inc ea x ce L lst → let (_ , x₀ , ce₀) = carried x ce in anchor A′ inc ea x₀ ce₀ (env-live {ρ = ρ} {Amb = Amb} {env = env} {env′ = env′} es {T = T} {T′ = t₀} (λ {j} → live {j}) {A′} L) (listed lst) }
