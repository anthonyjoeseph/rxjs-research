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
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-cancelˡ)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n; m≤n⊔m)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; inside; inside-++; inside-self; <ᵖ-part; <ᵖ-ix)
open import denotation.MonotonicList using (ofᴱ)
open import denotation.EmissionSet using (Ev; end; skip; EmissionSet; _≺_; _≼_; Den; hot; cold; enter; DenEnv; Truncate; InE; at-out;
  at-end; on-out; emptyᵀ; ofᵀ; spin; ⊥ᵀ; MapT; map-out; map-skip; map-end; mapᵀ; module Scan;
  scanᵀ; DeferT; guard; body; deferᵀ; from)
open import denotation.EmissionSet.Laws.Modulus using (≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-≺-≺; ≺-ext; LimD)

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

  back-snoc : ∀ acc x {l} → Plain l → Back acc x → Back acc (x ++ [ l ])
  back-snoc acc []           plain-ix   b            = tt
  back-snoc acc []           plain-last b            = tt
  back-snoc acc (sub e ∷ x)  pl         (r , lt , b) = r , lt , back-snoc (acc ++ [ sub e ]) x pl b
  back-snoc acc (ix j ∷ x)   pl         b            = back-snoc (acc ++ [ ix j ]) x pl b
  back-snoc acc (last ∷ x)   pl         b            = back-snoc (acc ++ [ last ]) x pl b

  real-snoc : ∀ x {l} → Plain l → Real x → Real (x ++ [ l ])
  real-snoc []          _  ()
  real-snoc (ix j ∷ x)  pl r = back-snoc (ix j ∷ []) x pl r
  real-snoc (sub _ ∷ _) _  ()
  real-snoc (last ∷ _)  _  ()

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
ok-step p (r , d) = real-snoc p plain-ix r , λ hh w ins → d hh (shrink w) ins

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

------------------------------------------------------------------------
-- The leaves keep it

private
  ≺-absurd : ∀ {x y} → x ≺ y → y ≺ x → ⊥
  ≺-absurd {x} {y} a b = ≺-irrefl {x} (≺-trans {x} {y} {x} a b)

  -- No position is its own extension.
  ext≢ : ∀ x {l} ys → x ++ l ∷ ys ≡ x → ⊥
  ext≢ x ys eq = ≺-irrefl {x} (subst (x ≺_) eq (≺-ext x ys))

  -- One plain label below `p`.
  Below : Pos → Pos → Set
  Below p y = Σ Label λ l → Plain l × y ≡ p ++ [ l ]

  -- A READING ONE LABEL DEEP keeps the invariant: its rows are siblings,
  -- under `p` together.
  shallow-inv : ∀ {A H p} {X : EmissionSet A} → Ok H p → (∀ {y e} → X y e → Below p y) → InvAt H p X
  shallow-inv {H = H} {p} (r , _) sh = record
    { world = λ x → wo (sh x)
    ; real  = λ x → re (sh x)
    ; flat  = λ x x′ → fl (sh x) (sh x′)
    ; burst = λ c y _ → p , here , ins (sh c) , ins (sh y)
    }
    where
      wo : ∀ {y} → Below p y → W H p y
      wo (_ , pl , refl) = step here pl

      re : ∀ {y} → Below p y → Real y
      re (_ , pl , refl) = real-snoc p pl r

      ins : ∀ {y} → Below p y → T (inside p y)
      ins (l , _ , refl) = Equivalence.from T-≡ (inside-++ p p [ l ] (inside-self p))

      fl : ∀ {y l ys} → Below p y → Below p (y ++ l ∷ ys) → ⊥
      fl {l = l} {ys} (l₀ , _ , refl) (l′ , _ , eq) with ++-cancelˡ p (l₀ ∷ l ∷ ys) [ l′ ] (trans (sym (++-assoc p [ l₀ ] (l ∷ ys))) eq)
      ... | ()

  -- A reading whose rows are another's, ends kept, keeps its invariant.
  inv-via : ∀ {A B H p} {X : EmissionSet A} {Y : EmissionSet B}
          → (∀ {y e} → X y e → Σ (Ev B) (Y y)) → (∀ {y} → X y end → Y y end)
          → InvAt H p Y → InvAt H p X
  inv-via bk be I = record
    { world = λ x → InvAt.world I (proj₂ (bk x))
    ; real  = λ x → InvAt.real I (proj₂ (bk x))
    ; flat  = λ x x′ → InvAt.flat I (proj₂ (bk x)) (proj₂ (bk x′))
    ; burst = λ c y cy → InvAt.burst I (be c) (proj₂ (bk y)) cy
    }

  of-below : ∀ {A} p i (xs : List A) {y e} → InE (ofᴱ p i xs) y e → Below p y
  of-below p i []       at-end     = last , plain-last , refl
  of-below p i (x ∷ xs) at-out     = ix i , plain-ix , refl
  of-below p i (x ∷ xs) (on-out r) = of-below p (suc i) xs r

  acc-row : ∀ {A B} {f : B → A → B} {z} {t : EmissionSet A} {q b} → Scan.Acc f z t q b → Σ (Ev A) (t q)
  acc-row (Scan.acc₀ x _)     = _ , x
  acc-row (Scan.acc _ x _ _)  = _ , x

empty-inv : ∀ {A H} → InvD H (emptyᵀ {A})
empty-inv p ok = shallow-inv ok λ { (at-end , _) → last , plain-last , refl }

of-inv : ∀ {A H} (xs : List A) → InvD H (ofᵀ xs)
of-inv xs p ok = shallow-inv ok λ x → of-below p 0 xs (proj₁ x)

spin-inv : ∀ {A H} → InvD H (⊥ᵀ {A})
spin-inv p ok = shallow-inv ok λ { (spin i , _) → ix i , plain-ix , refl }

map-inv : ∀ {A B H} (f : A → B) {s : Den A} → InvD H s → InvD H (mapᵀ f s)
map-inv f {s} inv p ok = inv-via bk be (inv p ok)
  where
    bk : ∀ {y e} → Truncate (MapT f (enter s p)) y e → Σ _ (enter s p y)
    bk (map-out x , _)  = _ , x
    bk (map-skip x , _) = _ , x
    bk (map-end x , _)  = _ , x

    be : ∀ {y} → Truncate (MapT f (enter s p)) y end → enter s p y end
    be (map-end x , _) = x

scan-inv : ∀ {A B H} (f : B → A → B) z {s : Den A} → InvD H s → InvD H (scanᵀ f z s)
scan-inv f z {s} inv p ok = inv-via bk be (inv p ok)
  where
    bk : ∀ {y e} → Truncate (Scan.ScanT f z (enter s p)) y e → Σ _ (enter s p y)
    bk (Scan.sval a , _)  = acc-row a
    bk (Scan.sstep x , _) = _ , x
    bk (Scan.send x , _)  = _ , x

    be : ∀ {y} → Truncate (Scan.ScanT f z (enter s p)) y end → enter s p y end
    be (Scan.send x , _) = x

-- A DEFER keeps it: its guard lies before the body's subscription, and
-- the body's world lies in its own.
defer-inv : ∀ {A H} {s : Den A} → InvD H s → InvD H (deferᵀ s)
defer-inv {A} {H} {s} inv p ok = record { world = wo ; real = re ; flat = λ x x′ → fl (view x) (view x′) ; burst = λ c y cy → bu (view c) (view y) cy }
  where
    I = inv (p ++ [ ix 1 ]) (ok-step p ok)
    B = enter s (p ++ [ ix 1 ])

    View : Pos → Ev A → Set
    View y e = (y ≡ p ++ [ ix 0 ] × e ≡ skip) ⊎ B y e

    view : ∀ {y e} → Truncate (DeferT s p) y e → View y e
    view (guard , _)  = inj₁ (refl , refl)
    view (body x , _) = inj₂ x

    after : ∀ {y e} → B y e → (p ++ [ ix 1 ]) ≺ y
    after x = world-after (InvAt.world I x) (InvAt.real I x)

    -- The guard and what lies under it come before the body's subscription.
    early : ∀ ys → (p ++ ix 0 ∷ ys) ≺ (p ++ [ ix 1 ])
    early ys = Equivalence.from T-≡ (<ᵖ-part p ys [] (<ᵖ-ix 0))

    wo : ∀ {y e} → Truncate (DeferT s p) y e → W H p y
    wo (guard , _)  = step here plain-ix
    wo (body x , _) = shrink (InvAt.world I x)

    re : ∀ {y e} → Truncate (DeferT s p) y e → Real y
    re (guard , _)  = real-snoc p plain-ix (proj₁ ok)
    re (body x , _) = InvAt.real I x

    fl : ∀ {y e l ys e′} → View y e → View (y ++ l ∷ ys) e′ → ⊥
    fl {ys = ys} (inj₁ (refl , _)) (inj₁ (eq , _)) = ext≢ (p ++ [ ix 0 ]) ys eq
    fl {l = l} {ys} (inj₁ (refl , _)) (inj₂ b) =
      ≺-absurd {p ++ [ ix 1 ]} {(p ++ [ ix 0 ]) ++ l ∷ ys} (after b) (subst (_≺ (p ++ [ ix 1 ])) (sym (++-assoc p [ ix 0 ] (l ∷ ys))) (early (l ∷ ys)))
    fl {y} {l = l} {ys} (inj₂ b) (inj₁ (eq , _)) =
      ≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (≺-trans {p ++ [ ix 1 ]} {y} {p ++ [ ix 0 ]} (after b) (subst (y ≺_) eq (≺-ext y ys))) (early [])
    fl (inj₂ b) (inj₂ b′) = InvAt.flat I b b′

    bu : ∀ {c y e} → View c end → View y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    bu (inj₁ (_ , ())) _ _
    bu {c} (inj₂ b) (inj₁ (refl , _)) cy =
      ⊥-elim (≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (≺-trans {p ++ [ ix 1 ]} {c} {p ++ [ ix 0 ]} (after b) cy) (early []))
    bu (inj₂ b) (inj₂ b′) cy with InvAt.burst I b b′ cy
    ... | w , w⁼ , i = w , inW (shrink⁼ w⁼) , i

-- A LIMIT keeps it: any finitely many of its rows are one member's.
lim-inv : ∀ {A H} {c : ℕ → Den A} → (∀ n → InvD H (c n)) → InvD H (LimD c)
lim-inv inv p ok = record
  { world = λ { (from N l , _) → InvAt.world (I N) (l N ≤-refl) }
  ; real  = λ { (from N l , _) → InvAt.real (I N) (l N ≤-refl) }
  ; flat  = λ { (from N l , _) (from M m , _) → InvAt.flat (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) }
  ; burst = λ { (from N l , _) (from M m , _) cy → InvAt.burst (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) cy }
  }
  where
    I = λ n → inv n p ok
