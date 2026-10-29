{-# OPTIONS --guardedness #-}

-- WHERE A SUBSCRIPTION'S ROWS LIE: the invariant every reading of a lawful
-- observable keeps, and the positions a run can reach.
--
-- A subscription at `p` places its rows in its WORLD: below `p` a plain
-- label at a time; at a timer's root `ix t ∷ sub e ∷ []`, for a timer
-- created at `e` in the world; and where a hot row `h` is joined at `e` in
-- the world, at `h ++ [ sub e ]`.  The world is what lets a connect's
-- source and body be told apart: neither's rows lie in the other's world.
--
-- A REACHABLE position is led by a tick, and every `sub e` in it names an
-- earlier, reachable position.  A subscription is ADMISSIBLE under hot rows
-- `H` when it is reachable and no hot row lies in its world: the hot was
-- made elsewhere.
module denotation.EmissionSet.Laws.Worlds where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; inside)
open import denotation.EmissionSet using (Ev; end; EmissionSet; _≺_; _≼_; Den; hot; cold; enter; DenEnv)
open import denotation.EmissionSet.Laws.Modulus using (≺-trans; ≺→≼; ≼-refl; ≼-≺-≺; ≺-ext)

-- A label that opens no subscription.
data Plain : Label → Set where
  plain-ix   : ∀ {i} → Plain (ix i)
  plain-last : Plain last

mutual
  -- The world of a subscription at `p` under hot rows `H`, `p` excluded.
  data W (H : Pos → Set) (p : Pos) : Pos → Set where
    step  : ∀ {x l} → W⁼ H p x → Plain l → W H p (x ++ [ l ])
    timer : ∀ {e} t → W⁼ H p e → W H p (ix t ∷ sub e ∷ [])
    join  : ∀ {h e} → H h ⊎ W H p h → W⁼ H p e → e ≺ h → W H p (h ++ [ sub e ])

  -- The world with `p` itself.
  data W⁼ (H : Pos → Set) (p : Pos) : Pos → Set where
    here  : W⁼ H p p
    inW   : ∀ {x} → W H p x → W⁼ H p x

mutual
  -- Led by a tick, every `sub` naming an earlier reachable position.
  Real : Pos → Set
  Real (ix i ∷ p) = Back (ix i ∷ []) p
  Real _          = ⊥

  Back : Pos → Pos → Set
  Back acc []          = ⊤
  Back acc (sub e ∷ p) = Real e × e ≺ (acc ++ [ sub e ]) × Back (acc ++ [ sub e ]) p
  Back acc (ix i ∷ p)  = Back (acc ++ [ ix i ]) p
  Back acc (last ∷ p)  = Back (acc ++ [ last ]) p

-- No hot row lies in the world.
Disj : (Pos → Set) → Pos → Set
Disj H p = ∀ {h w} → H h → W H p w → T (inside w h) → ⊥

-- ADMISSIBLE: reachable, and no hot row in its world.
Ok : (Pos → Set) → Pos → Set
Ok H p = Real p × Disj H p

-- The hot rows `H` and a hot's.
_⊕_ : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
_⊕_ {A} H t q = Σ (Ev A) (t q) ⊎ H q

-- A LAWFUL HOT: reachable rows, none below another, none past an end.
record Lawful {A} (t : EmissionSet A) : Set where
  field
    real   : ∀ {y e} → t y e → Real y
    flat   : ∀ {y e l ys e′} → t y e → t (y ++ l ∷ ys) e′ → ⊥
    proper : ∀ {c y e} → t c end → t y e → y ≼ c

-- THE INVARIANT of a reading at `p`: its rows lie in the world and are
-- reachable; none lies below another; and what follows an end lies with
-- it below one position of the world — the rest of the burst it ended in.
record InvAt {A} (H : Pos → Set) (p : Pos) (X : EmissionSet A) : Set where
  field
    world : ∀ {y e} → X y e → W H p y
    real  : ∀ {y e} → X y e → Real y
    flat  : ∀ {y e l ys e′} → X y e → X (y ++ l ∷ ys) e′ → ⊥
    burst : ∀ {c y e} → X c end → X y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)

-- At every admissible subscription.
InvD : ∀ {A} → (Pos → Set) → Den A → Set
InvD H d = ∀ p → Ok H p → InvAt H p (enter d p)

-- The rows of an environment's hots.
Hots : ∀ {Γ} → DenEnv Γ → Pos → Set
Hots []           = λ _ → ⊥
Hots (hot t ∷ ρ)  = Hots ρ ⊕ t
Hots (cold _ ∷ ρ) = Hots ρ

-- A LAWFUL ENVIRONMENT: every handle keeps the invariant.
GoodEnv : ∀ {Γ} → DenEnv Γ → Set₁
GoodEnv {Γ} ρ = ∀ {A} (i : A ∈ Γ) → InvD (Hots ρ) (lookup ρ i)

------------------------------------------------------------------------
-- Reachability

private
  back-init : ∀ acc x ys → Back acc (x ++ ys) → Back acc x
  back-init acc []          ys b              = tt
  back-init acc (sub e ∷ x) ys (r , lt , b)   = r , lt , back-init (acc ++ [ sub e ]) x ys b
  back-init acc (ix i ∷ x)  ys b              = back-init (acc ++ [ ix i ]) x ys b
  back-init acc (last ∷ x)  ys b              = back-init (acc ++ [ last ]) x ys b

  -- A reachable position's prefix is empty or reachable.
  real-init : ∀ x ys → Real (x ++ ys) → x ≡ [] ⊎ Real x
  real-init []          ys r = inj₁ refl
  real-init (ix i ∷ x)  ys r = inj₂ (back-init (ix i ∷ []) x ys r)
  real-init (sub _ ∷ _) ys ()
  real-init (last ∷ _)  ys ()

  back-real : ∀ acc x {e} → Back acc (x ++ [ sub e ]) → Real e
  back-real acc []           (r , _ , _) = r
  back-real acc (sub e′ ∷ x) (_ , _ , b) = back-real (acc ++ [ sub e′ ]) x b
  back-real acc (ix i ∷ x)   b           = back-real (acc ++ [ ix i ]) x b
  back-real acc (last ∷ x)   b           = back-real (acc ++ [ last ]) x b

  -- What a reachable position's last `sub` names is reachable.
  real-last : ∀ x {e} → Real (x ++ [ sub e ]) → Real e
  real-last []          ()
  real-last (ix i ∷ x)  r = back-real (ix i ∷ []) x r
  real-last (sub _ ∷ _) ()
  real-last (last ∷ _)  ()

  back-snoc : ∀ acc x {i} → Back acc x → Back acc (x ++ [ ix i ])
  back-snoc acc []           b            = tt
  back-snoc acc (sub e ∷ x)  (r , lt , b) = r , lt , back-snoc (acc ++ [ sub e ]) x b
  back-snoc acc (ix j ∷ x)   b            = back-snoc (acc ++ [ ix j ]) x b
  back-snoc acc (last ∷ x)   b            = back-snoc (acc ++ [ last ]) x b

  real-snoc : ∀ x {i} → Real x → Real (x ++ [ ix i ])
  real-snoc []          ()
  real-snoc (ix j ∷ x)  r = back-snoc (ix j ∷ []) x r
  real-snoc (sub _ ∷ _) ()
  real-snoc (last ∷ _)  ()

  snoc≢[] : ∀ (x : Pos) {l : Label} → x ++ [ l ] ≡ [] → ⊥
  snoc≢[] []      ()
  snoc≢[] (_ ∷ _) ()

  w-nonempty : ∀ {H p y} → W H p y → y ≡ [] → ⊥
  w-nonempty (step {x} _ _)   eq = snoc≢[] x eq
  w-nonempty (timer _ _)      ()
  w-nonempty (join {h} _ _ _) eq = snoc≢[] h eq

------------------------------------------------------------------------
-- The world

-- THE WORLD LIES AFTER THE SUBSCRIPTION: each world row extends, joins
-- after, or times from a row at or after it.
mutual
  world-after : ∀ {H p y} → W H p y → Real y → p ≺ y
  world-after {p = p} (step here _) r = ≺-ext p []
  world-after {p = p} (step {x} {l} (inW w) _) r with real-init x [ l ] r
  ... | inj₁ eq = ⊥-elim (w-nonempty w eq)
  ... | inj₂ rx = ≺-trans {p} {x} {x ++ [ l ]} (world-after w rx) (≺-ext x [])
  world-after {p = p} (timer {e} t w) (re , lt , _) = ≼-≺-≺ {p} {e} {ix t ∷ sub e ∷ []} (world-after⁼ w re) lt
  world-after {p = p} (join {h} {e} _ w eh) r =
    ≼-≺-≺ {p} {e} {h ++ [ sub e ]} (world-after⁼ w (real-last h r)) (≺-trans {e} {h} {h ++ [ sub e ]} eh (≺-ext h []))

  world-after⁼ : ∀ {H p y} → W⁼ H p y → Real y → p ≼ y
  world-after⁼ {p = p} here    r = ≼-refl {p}
  world-after⁼ {p = p} {y} (inW w) r = ≺→≼ {p} {y} (world-after w r)

private
  -- The world one tick down lies in the world.
  mutual
    shrink : ∀ {H p i w} → W H (p ++ [ ix i ]) w → W H p w
    shrink (step w l)           = step (inW (shrink⁼ w)) l
    shrink (timer t w)          = timer t (inW (shrink⁼ w))
    shrink (join (inj₁ h) w eh) = join (inj₁ h) (inW (shrink⁼ w)) eh
    shrink (join (inj₂ v) w eh) = join (inj₂ (shrink v)) (inW (shrink⁼ w)) eh

    shrink⁼ : ∀ {H p i w} → W⁼ H (p ++ [ ix i ]) w → W H p w
    shrink⁼ here    = step here plain-ix
    shrink⁼ (inW w) = shrink w

-- A `defer`'s body is subscribed admissibly.
ok-step : ∀ {H} p → Ok H p → Ok H (p ++ [ ix 1 ])
ok-step p (r , d) = real-snoc p r , λ hh w ins → d hh (shrink w) ins

private
  -- More hot rows, the same world.
  mutual
    widen : ∀ {B H p w} (t : EmissionSet B) → W H p w → W (H ⊕ t) p w
    widen t (step w l)           = step (widen⁼ t w) l
    widen t (timer i w)          = timer i (widen⁼ t w)
    widen t (join (inj₁ h) w eh) = join (inj₁ (inj₂ h)) (widen⁼ t w) eh
    widen t (join (inj₂ v) w eh) = join (inj₂ (widen t v)) (widen⁼ t w) eh

    widen⁼ : ∀ {B H p w} (t : EmissionSet B) → W⁼ H p w → W⁼ (H ⊕ t) p w
    widen⁼ t here    = here
    widen⁼ t (inW w) = inW (widen t w)

-- A HANDLE KEEPS THE INVARIANT under more hot rows: admissible under more
-- is admissible under fewer, and the world only grows.
inv-widen : ∀ {A B H} {t : EmissionSet B} {d : Den A} → InvD H d → InvD (H ⊕ t) d
inv-widen {H = H} {t} {d} inv p (r , dj) = record
  { world = λ x → widen t (wo x)
  ; real  = re
  ; flat  = fl
  ; burst = λ ce ye cy → bump (bu ce ye cy)
  }
  where
    bump : ∀ {c y} → Σ Pos (λ w → W⁼ H p w × T (inside w c) × T (inside w y)) → Σ Pos (λ w → W⁼ (H ⊕ t) p w × T (inside w c) × T (inside w y))
    bump (w , w⁼ , i) = w , widen⁼ t w⁼ , i

    open InvAt (inv p (r , λ hh w ins → dj (inj₂ hh) (widen t w) ins)) renaming (world to wo; real to re; flat to fl; burst to bu)
