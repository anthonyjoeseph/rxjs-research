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
open import Data.List.Properties using (++-assoc; ++-cancelˡ; ++-identityʳ; ++-conicalˡ; ∷-injective; ∷-injectiveˡ; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; 1+n≰n; m≤m⊔n; m≤n⊔m)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; inside; inside-++; inside-self; inside-cons; <ᵖ-part; <ᵖ-ix; <ᵖ-split; <ᵖ-between)
open import denotation.MonotonicList using (ofᴱ)
open import denotation.EmissionSet using (Ev; out; end; skip; EmissionSet; _≺_; _≼_; Den; hot; cold; enter; DenEnv; Truncate; InE; at-out;
  at-end; on-out; emptyᵀ; ofᵀ; spin; ⊥ᵀ; MapT; map-out; map-skip; map-end; mapᵀ; Spin; module Scan;
  scanᵀ; DeferT; guard; body; deferᵀ; from)
open import denotation.EmissionSet.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺→≼; ≼-refl; ≼-trans; ≼-antisym; ≼-≺-≺; ≺-ext; ≼-false; LimD)

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
    func   : ∀ {y e e′} → t y e → t y e′ → e ≡ e′
    flat   : ∀ {y e l ys e′} → t y e → t (y ++ l ∷ ys) e′ → ⊥
    proper : ∀ {c y e} → t c end → t y e → y ≼ c

-- `x` LEADS `y`: `y` is `x` or lies under it.
_⊑_ : Pos → Pos → Set
x ⊑ y = Σ Pos λ zs → y ≡ x ++ zs

-- THE INVARIANT of a reading at `p`: its rows lie in the world and are
-- reachable; one event at a position; none lies below another; and what
-- follows an end lies with it below one position of the world — the rest
-- of the burst it ended in.
--
-- One event at a position, because an operator that reads a value's
-- content would otherwise place rows from two events at one position one
-- below the other: a takeWhile passing one and failing the other there.
--
-- No row lies under the world of a row's plain child: that is where a
-- joiner subscribes the row's lane, and an outer row there would meet the
-- lane's.  And only skips follow an end: a value after it would start a
-- lane past the joiner's end, outside its burst.
--
-- REFUTED: 67919a90 flatMap-inv without `under`, by an outer row under a timer rooted below its own value's first child
record InvAt {A} (H : Pos → Set) (p : Pos) (X : EmissionSet A) : Set where
  field
    world : ∀ {y e} → X y e → W H p y
    real  : ∀ {y e} → X y e → Real y
    func  : ∀ {y e e′} → X y e → X y e′ → e ≡ e′
    flat  : ∀ {y e l ys e′} → X y e → X (y ++ l ∷ ys) e′ → ⊥
    burst : ∀ {c y e} → X c end → X y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    under : ∀ {q y w l e e′} → X q e → X y e′ → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
    quiet : ∀ {c y e} → X c end → X y e → c ≺ y → e ≡ skip

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

-- A reachable position's prefix is empty or reachable.
real-init : ∀ x ys → Real (x ++ ys) → x ≡ [] ⊎ Real x
real-init []          ys r = inj₁ refl
real-init (ix i ∷ x)  ys r = inj₂ (back-init (ix i ∷ []) x ys r)
real-init (sub _ ∷ _) ys ()
real-init (last ∷ _)  ys ()

-- A reachable position one plain label down is reachable.
real-snoc : ∀ x {l} → Plain l → Real x → Real (x ++ [ l ])
real-snoc []          _  ()
real-snoc (ix j ∷ x)  pl r = back-snoc (ix j ∷ []) x pl r
real-snoc (sub _ ∷ _) _  ()
real-snoc (last ∷ _)  _  ()

private
  back-sub : ∀ acc x {e} → Back acc x → Real e → e ≺ ((acc ++ x) ++ [ sub e ]) → Back acc (x ++ [ sub e ])
  back-sub acc []           {e} b            re lt = re , subst (λ z → e ≺ (z ++ [ sub e ])) (++-identityʳ acc) lt , tt
  back-sub acc (sub e′ ∷ x) {e} (r , l , b)  re lt = r , l , back-sub (acc ++ [ sub e′ ]) x b re (subst (λ z → e ≺ (z ++ [ sub e ])) (sym (++-assoc acc [ sub e′ ] x)) lt)
  back-sub acc (ix j ∷ x)   {e} b            re lt = back-sub (acc ++ [ ix j ]) x b re (subst (λ z → e ≺ (z ++ [ sub e ])) (sym (++-assoc acc [ ix j ] x)) lt)
  back-sub acc (last ∷ x)   {e} b            re lt = back-sub (acc ++ [ last ]) x b re (subst (λ z → e ≺ (z ++ [ sub e ])) (sym (++-assoc acc [ last ] x)) lt)

-- A reachable position naming an earlier reachable one is reachable.
real-sub : ∀ x {e} → Real x → Real e → e ≺ (x ++ [ sub e ]) → Real (x ++ [ sub e ])
real-sub []          ()
real-sub (ix j ∷ x)  r re lt = back-sub (ix j ∷ []) x r re lt
real-sub (sub _ ∷ _) ()
real-sub (last ∷ _)  ()

snoc≢[] : ∀ (x : Pos) {l : Label} → x ++ [ l ] ≡ [] → ⊥
snoc≢[] []      ()
snoc≢[] (_ ∷ _) ()

private
  w-nonempty : ∀ {H p y} → W H p y → y ≡ [] → ⊥
  w-nonempty (step {x} _ _)   eq = snoc≢[] x eq
  w-nonempty (timer _ _)      ()
  w-nonempty (join {h} _ _ _) eq = snoc≢[] h eq

-- The empty position is in a world only as its subscription.
nonempty⁼ : ∀ {H a} → (a ≡ [] → ⊥) → W⁼ H a [] → ⊥
nonempty⁼ ne here    = ne refl
nonempty⁼ ne (inW u) = w-nonempty u refl

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

-- A world inside the world lies in it.
mutual
  nest : ∀ {H p a w} → W⁼ H p a → W H a w → W H p w
  nest pa (step w l)           = step (nest⁼ pa w) l
  nest pa (timer t w)          = timer t (nest⁼ pa w)
  nest pa (join (inj₁ h) w eh) = join (inj₁ h) (nest⁼ pa w) eh
  nest pa (join (inj₂ v) w eh) = join (inj₂ (nest pa v)) (nest⁼ pa w) eh

  nest⁼ : ∀ {H p a w} → W⁼ H p a → W⁼ H a w → W⁼ H p w
  nest⁼ pa here    = pa
  nest⁼ pa (inW w) = inW (nest pa w)

nest-in : ∀ {H p a w} → W H p a → W⁼ H a w → W H p w
nest-in pa here    = pa
nest-in pa (inW v) = nest (inW pa) v

-- A world one tick down whose own hots lie in the world lies in it.
mutual
  narrow : ∀ {B H p i w} {t : EmissionSet B} → (∀ {h e} → t h e → W H p h) → W (H ⊕ t) (p ++ [ ix i ]) w → W H p w
  narrow tw (step w l)                     = step (inW (narrow⁼ tw w)) l
  narrow tw (timer k w)                    = timer k (inW (narrow⁼ tw w))
  narrow tw (join (inj₁ (inj₁ (_ , x))) w eh) = join (inj₂ (tw x)) (inW (narrow⁼ tw w)) eh
  narrow tw (join (inj₁ (inj₂ h)) w eh)    = join (inj₁ h) (inW (narrow⁼ tw w)) eh
  narrow tw (join (inj₂ v) w eh)           = join (inj₂ (narrow tw v)) (inW (narrow⁼ tw w)) eh

  narrow⁼ : ∀ {B H p i w} {t : EmissionSet B} → (∀ {h e} → t h e → W H p h) → W⁼ (H ⊕ t) (p ++ [ ix i ]) w → W H p w
  narrow⁼ tw here    = step here plain-ix
  narrow⁼ tw (inW w) = narrow tw w

-- A `defer`'s body is subscribed admissibly.
ok-step : ∀ {H} p → Ok H p → Ok H (p ++ [ ix 1 ])
ok-step p (r , d) = real-snoc p plain-ix r , λ hh w ins → d hh (shrink w) ins

------------------------------------------------------------------------
-- Ancestry

-- No position is its own extension.
ext≢ : ∀ x {l} ys → x ++ l ∷ ys ≡ x → ⊥
ext≢ x ys eq = ≺-irrefl {x} (subst (x ≺_) eq (≺-ext x ys))

⊑-refl : ∀ x → x ⊑ x
⊑-refl x = [] , sym (++-identityʳ x)

⊑-snoc⁺ : ∀ x {l} → x ⊑ (x ++ [ l ])
⊑-snoc⁺ x {l} = [ l ] , refl

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans {x} (zs , refl) (ws , refl) = zs ++ ws , ++-assoc x zs ws

⊑-≼ : ∀ {x y} → x ⊑ y → x ≼ y
⊑-≼ {x} ([] , refl)     = subst (x ≼_) (sym (++-identityʳ x)) (≼-refl {x})
⊑-≼ {x} (z ∷ zs , refl) = ≺→≼ {x} {x ++ z ∷ zs} (≺-ext x zs)

⊑-inside : ∀ {x y} → x ⊑ y → T (inside x y)
⊑-inside {x} (zs , refl) = Equivalence.from T-≡ (inside-++ x x zs (inside-self x))

inside-⊑ : ∀ x y → T (inside x y) → x ⊑ y
inside-⊑ []      y       _ = y , refl
inside-⊑ (a ∷ x) []      ()
inside-⊑ (a ∷ x) (b ∷ y) i with inside-cons a x b y (Equivalence.to T-≡ i)
... | refl , i′ with inside-⊑ x y (Equivalence.from T-≡ i′)
...   | zs , eq = zs , cong (a ∷_) eq

-- What lies under `w` is an interval.
conv : ∀ {w a b y} → w ⊑ a → a ≼ b → b ≺ y → w ⊑ y → w ⊑ b
conv {w} {a} {b} wa ab by (ys , refl) with <ᵖ-split w b (≼-false {w} {b} (≼-trans {w} {a} {b} (⊑-≼ wa) ab))
... | inj₁ lt   = <ᵖ-between w b ys lt (Equivalence.to T-≡ by)
... | inj₂ refl = [] , sym (++-identityʳ w)

-- A row before a row under the subscription is under it.
in-world : ∀ {C H p} {X : EmissionSet C} → InvAt H p X → ∀ {k y e} → X k e → k ≺ y → T (inside p y) → T (inside p k)
in-world {p = p} I {k} {y} x lt i =
  ⊑-inside (conv (⊑-refl p) (≺→≼ {p} {k} (world-after (InvAt.world I x) (InvAt.real I x))) lt (inside-⊑ p y i))

-- Leading `y ++ [ l ]`: leading `y`, or it.
⊑-snoc : ∀ {w} y {l} → w ⊑ (y ++ [ l ]) → w ⊑ y ⊎ w ≡ y ++ [ l ]
⊑-snoc {w} y (zs , eq) = go w y zs eq
  where
    go : ∀ w y {l} zs → y ++ [ l ] ≡ w ++ zs → w ⊑ y ⊎ w ≡ y ++ [ l ]
    go []      y       zs eq = inj₁ (y , refl)
    go (a ∷ w) []      zs eq with ∷-injective eq
    ... | refl , eq′ with ++-conicalˡ w zs (sym eq′)
    ...   | refl = inj₂ refl
    go (a ∷ w) (b ∷ y) zs eq with ∷-injective eq
    ... | refl , eq′ with go w y zs eq′
    ...   | inj₁ (vs , e) = inj₁ (vs , cong (a ∷_) e)
    ...   | inj₂ e        = inj₂ (cong (a ∷_) e)

-- Two leaders of one position: one leads the other.
⊑-cmp : ∀ w k {b} → w ⊑ b → k ⊑ b → w ⊑ k ⊎ k ⊑ w
⊑-cmp []      k       _           _          = inj₁ (k , refl)
⊑-cmp (a ∷ w) []      _           _          = inj₂ (a ∷ w , refl)
⊑-cmp (a ∷ w) (c ∷ k) (zs , refl) (zs′ , eq) with ∷-injective eq
... | refl , eq′ with ⊑-cmp w k (zs , refl) (zs′ , eq′)
...   | inj₁ (vs , e) = inj₁ (vs , cong (a ∷_) e)
...   | inj₂ (vs , e) = inj₂ (vs , cong (a ∷_) e)

-- Positions apart past a common prefix.
diverge : ∀ k {a b : Label} ys ms → (a ≡ b → ⊥) → (k ++ [ a ]) ++ ys ≡ (k ++ [ b ]) ++ ms → ⊥
diverge k {a} {b} ys ms ne eq =
  ne (∷-injectiveˡ (++-cancelˡ k (a ∷ ys) (b ∷ ms) (trans (sym (++-assoc k [ a ] ys)) (trans eq (++-assoc k [ b ] ms)))))

-- A row leading another of a flat reading is it.
same-lead : ∀ {C H q} {X : EmissionSet C} → InvAt H q X → ∀ {k k′ e e′} → X k e → X k′ e′ → k ⊑ k′ → k ≡ k′
same-lead I {k} x x′ ([] , eq)      = trans (sym (++-identityʳ k)) (sym eq)
same-lead I     x x′ (z ∷ zs , refl) = ⊥-elim (InvAt.flat I x x′)

-- No row of a flat reading lies under another's child.
flat-under : ∀ {C H q} {X : EmissionSet C} → InvAt H q X → ∀ {k k′ a e e′} → X k e → X k′ e′ → (k ++ [ a ]) ⊑ k′ → ⊥
flat-under {X = X} I {k} {a = a} {e′ = e′} x x′ (zs , refl) = InvAt.flat I x (subst (λ z → X z e′) (++-assoc k [ a ] zs) x′)

-- `a` is `c`'s PARENT: `c` steps a plain label from it, or names it in a
-- closing `sub`.
data Parent (a c : Pos) : Set where
  plain : ∀ {l} → Plain l → c ≡ a ++ [ l ] → Parent a c
  named : ∀ h → c ≡ h ++ [ sub a ] → Parent a c

step-parent : ∀ x {l} → Plain l → Parent x (x ++ [ l ])
step-parent x pl = plain pl refl

plain-sub : ∀ {l e} → Plain l → l ≡ sub e → ⊥
plain-sub plain-ix   ()
plain-sub plain-last ()

-- A position has one parent.
parent-fun : ∀ {a b c} → Parent a c → Parent b c → a ≡ b
parent-fun {a} {b} (plain _ e)  (plain _ e′)  = ∷ʳ-injectiveˡ a b (trans (sym e) e′)
parent-fun {a}     (plain pl e) (named h e′)  = ⊥-elim (plain-sub pl (∷ʳ-injectiveʳ a h (trans (sym e) e′)))
parent-fun {b = b} (named h e)  (plain pl e′) = ⊥-elim (plain-sub pl (sym (∷ʳ-injectiveʳ h b (trans (sym e) e′))))
parent-fun         (named h e)  (named h′ e′) with ∷ʳ-injectiveʳ h h′ (trans (sym e) e′)
... | refl = refl

-- `a` is an ANCESTOR of `c`.
data Anc (a : Pos) : Pos → Set where
  self : Anc a a
  up   : ∀ {b c} → Anc a b → Parent b c → Anc a c

anc-view : ∀ {a c} → Anc a c → a ≡ c ⊎ Σ Pos λ b → Anc a b × Parent b c
anc-view self      = inj₁ refl
anc-view (up x pb) = inj₂ (_ , x , pb)

-- Two ancestors of one position: one is the other's.
anc-lin : ∀ {a b w} → Anc a w → Anc b w → Anc a b ⊎ Anc b a
anc-lin self       y         = inj₂ y
anc-lin (up x pa)  self      = inj₁ (up x pa)
anc-lin (up x pa)  (up y pb) with parent-fun pa pb
... | refl = anc-lin x y

anc-trans : ∀ {a b c} → Anc a b → Anc b c → Anc a c
anc-trans x self      = x
anc-trans x (up y pb) = up (anc-trans x y) pb

anc-nil : ∀ {a} → Anc a [] → a ≡ []
anc-nil self                    = refl
anc-nil (up {b} _ (plain _ e))  = ⊥-elim (snoc≢[] b (sym e))
anc-nil (up _ (named h e))      = ⊥-elim (snoc≢[] h (sym e))

private
  back-lt : ∀ acc x {e} → Back acc (x ++ [ sub e ]) → e ≺ ((acc ++ x) ++ [ sub e ])
  back-lt acc []           {e} (_ , lt , _) = subst (λ z → e ≺ (z ++ [ sub e ])) (sym (++-identityʳ acc)) lt
  back-lt acc (sub e′ ∷ x) {e} (_ , _ , b)  = subst (λ z → e ≺ (z ++ [ sub e ])) (++-assoc acc [ sub e′ ] x) (back-lt (acc ++ [ sub e′ ]) x b)
  back-lt acc (ix i ∷ x)   {e} b            = subst (λ z → e ≺ (z ++ [ sub e ])) (++-assoc acc [ ix i ] x) (back-lt (acc ++ [ ix i ]) x b)
  back-lt acc (last ∷ x)   {e} b            = subst (λ z → e ≺ (z ++ [ sub e ])) (++-assoc acc [ last ] x) (back-lt (acc ++ [ last ]) x b)

  real-lt : ∀ x {e} → Real (x ++ [ sub e ]) → e ≺ (x ++ [ sub e ])
  real-lt []          ()
  real-lt (ix i ∷ x)  r = back-lt (ix i ∷ []) x r
  real-lt (sub _ ∷ _) ()
  real-lt (last ∷ _)  ()

  -- A reachable position's parent is empty or reachable, and before it.
  parent-real : ∀ {b c} → Parent b c → Real c → (b ≡ [] ⊎ Real b) × b ≺ c
  parent-real {b} (plain {l} _ refl) r = real-init b [ l ] r , ≺-ext b []
  parent-real {b} (named h refl)     r = inj₂ (real-last h r) , real-lt h r

-- AN ANCESTOR comes no later.
anc-≼ : ∀ {a c} → Anc a c → Real c → a ≼ c
anc-≼ {a} self r = ≼-refl {a}
anc-≼ {a} {c} (up {b} x pb) r with parent-real pb r
... | inj₂ rb , bc = ≺→≼ {a} {c} (≼-≺-≺ {a} {b} {c} (anc-≼ x rb) bc)
... | inj₁ refl , bc with anc-nil x
...   | refl = ≺→≼ {[]} {c} bc

-- The world descends from its subscription.
mutual
  world-anc : ∀ {H p w} → W H p w → Anc p w
  world-anc (step w pl)       = up (world-anc⁼ w) (plain pl refl)
  world-anc (timer t w)       = up (world-anc⁼ w) (named (ix t ∷ []) refl)
  world-anc (join {h} _ w _)  = up (world-anc⁼ w) (named h refl)

  world-anc⁼ : ∀ {H p w} → W⁼ H p w → Anc p w
  world-anc⁼ here    = self
  world-anc⁼ (inW w) = world-anc w

private
  ≺-[] : ∀ q → q ≺ [] → ⊥
  ≺-[] []      ()
  ≺-[] (_ ∷ _) ()

  not-under : ∀ {p i j} → (i ≡ j → ⊥) → Real p → Anc (p ++ [ ix i ]) (p ++ [ ix j ]) → ⊥
  not-under {p} {i} {j} ne rp a with anc-view a
  ... | inj₁ eq = ne (ix-inj (∷ʳ-injectiveʳ p p eq))
    where ix-inj : ix i ≡ ix j → i ≡ j
          ix-inj refl = refl
  ... | inj₂ (b , x , pb) with parent-fun pb (step-parent p {ix j} plain-ix)
  ...   | refl = anc-≼ x rp (≺-ext p [])

-- SIBLING WORLDS ARE APART: nothing descends from both `p ++ [ ix 0 ]` and
-- `p ++ [ ix 1 ]`; each is the other's only through `p`, before both.
apart : ∀ {p w} → Real p → Anc (p ++ [ ix 0 ]) w → Anc (p ++ [ ix 1 ]) w → ⊥
apart rp x y with anc-lin x y
... | inj₁ a = not-under (λ ()) rp a
... | inj₂ a = not-under (λ ()) rp a

-- A descendant of `a` leads nothing reachable before `a`.
anc-lead : ∀ {a w q} → Anc a w → w ⊑ q → Real q → q ≺ a → ⊥
anc-lead {a} {w} x (zs , refl) rq qa with real-init w zs rq
... | inj₂ rw = ≼-trans {a} {w} {w ++ zs} (anc-≼ x rw) (⊑-≼ {w} {w ++ zs} (zs , refl)) qa
... | inj₁ refl with anc-nil x
...   | refl = ≺-[] zs qa

-- A descendant of a subscription leads no lone tick.
tick-lead : ∀ {p i w t} → Real p → Anc (p ++ [ ix i ]) w → w ⊑ (ix t ∷ []) → ⊥
tick-lead {p} {i} {w} {t} rp x le with ⊑-snoc {w} [] {ix t} le
... | inj₁ le′ = snoc≢[] p (nil-lead x le′)
  where
    nil-lead : ∀ {a v} → Anc a v → v ⊑ [] → a ≡ []
    nil-lead {v = v} y (zs , eq) with ++-conicalˡ v zs (sym eq)
    ... | refl = anc-nil y
... | inj₂ refl = unit rp x
  where
    unit : ∀ {p i t} → Real p → Anc (p ++ [ ix i ]) (ix t ∷ []) → ⊥
    unit {p} {t = t} rp x with anc-view x
    ... | inj₁ eq with ∷ʳ-injectiveˡ p [] eq
    ...   | refl = rp
    unit {p} {t = t} rp x | inj₂ (b , y , pb) with parent-fun pb (step-parent [] {ix t} plain-ix)
    ... | refl = snoc≢[] p (anc-nil y)

------------------------------------------------------------------------
-- What leads a world position

-- No world position is a lone tick.
lone : ∀ {H p w t} → Real p → W H p w → w ⊑ (ix t ∷ []) → ⊥
lone {p = p} {w} {t} rp ww le with ⊑-snoc {w} [] {ix t} le
... | inj₁ (zs , eq) = w-nonempty ww (++-conicalˡ w zs (sym eq))
... | inj₂ refl with anc-view (world-anc ww)
...   | inj₁ refl = ≺-irrefl {p} (world-after ww rp)
...   | inj₂ (b , y , pb) with parent-fun pb (step-parent [] {ix t} plain-ix)
...     | refl with anc-nil y
...       | refl = rp

-- What leads a world position: what leads the subscription, a position
-- of the world, what leads a joined hot row, or a lone tick.
data Lead (H : Pos → Set) (b w : Pos) : Set where
  l-root : w ⊑ b → Lead H b w
  l-in   : W H b w → Lead H b w
  l-hot  : ∀ {h} → H h → w ⊑ h → Lead H b w
  l-tick : ∀ {t} → w ⊑ (ix t ∷ []) → Lead H b w

mutual
  lead : ∀ {H b x w} → W⁼ H b x → w ⊑ x → Lead H b w
  lead here    le = l-root le
  lead (inW v) le = lead′ v le

  lead′ : ∀ {H b x w} → W H b x → w ⊑ x → Lead H b w
  lead′ (step {x′} v pl) le with ⊑-snoc x′ le
  ... | inj₁ le′  = lead v le′
  ... | inj₂ refl = l-in (step v pl)
  lead′ (timer t v) le with ⊑-snoc (ix t ∷ []) le
  ... | inj₁ le′  = l-tick le′
  ... | inj₂ refl = l-in (timer t v)
  lead′ (join {h} (inj₁ hh) v eh) le with ⊑-snoc h le
  ... | inj₁ le′  = l-hot hh le′
  ... | inj₂ refl = l-in (join (inj₁ hh) v eh)
  lead′ (join {h} (inj₂ u) v eh) le with ⊑-snoc h le
  ... | inj₁ le′  = lead′ u le′
  ... | inj₂ refl = l-in (join (inj₂ u) v eh)

-- A WORLD POSITION LEADS NO POSITION OF A WORLD it is not in, unless it
-- leads that world's subscription.
leads : ∀ {H p b w x} → Real p → Disj H p → W H p w → (W⁼ H b w → ⊥) → (w ⊑ b → ⊥) → W⁼ H b x → w ⊑ x → ⊥
leads rp dj ww nb nr bx le with lead bx le
... | l-root r  = nr r
... | l-in v    = nb (inW v)
... | l-hot h r = dj h ww (⊑-inside r)
... | l-tick r  = lone rp ww r

-- How a world position is reached: it is the subscription, one plain
-- label below a world position, or names one in a closing `sub`.
data Shape (H : Pos → Set) (a w : Pos) : Set where
  sh-root  : w ≡ a → Shape H a w
  sh-plain : ∀ {x l} → W⁼ H a x → Plain l → w ≡ x ++ [ l ] → Shape H a w
  sh-sub   : ∀ {x e} → W⁼ H a e → w ≡ x ++ [ sub e ] → Shape H a w

shape : ∀ {H a w} → W⁼ H a w → Shape H a w
shape here                    = sh-root refl
shape (inW (step v pl))       = sh-plain v pl refl
shape (inW (timer t v))       = sh-sub {x = ix t ∷ []} v refl
shape (inW (join v e eh))     = sh-sub e refl

-- One plain label below a world position: the subscription, or its parent
-- is one.
w-up : ∀ {H a x l} → Plain l → W⁼ H a (x ++ [ l ]) → a ≡ x ++ [ l ] ⊎ W⁼ H a x
w-up {x = x} pl v with shape v
... | sh-root eq            = inj₁ (sym eq)
... | sh-plain {x′} u _ eq  = inj₂ (subst (W⁼ _ _) (sym (∷ʳ-injectiveˡ x x′ eq)) u)
... | sh-sub {x′} _ eq      = ⊥-elim (plain-sub pl (∷ʳ-injectiveʳ x x′ eq))

private
  sub-inj : ∀ {a b} → sub a ≡ sub b → a ≡ b
  sub-inj refl = refl

  -- Where two shapes name a closing `sub`, they name one position.
  same-sub : ∀ {x x′ e e′} → x ++ [ sub e ] ≡ x′ ++ [ sub e′ ] → e ≡ e′
  same-sub {x} {x′} eq = sub-inj (∷ʳ-injectiveʳ x x′ eq)

-- THE WORLDS OF TWO CHILDREN ARE APART when they are two, and neither
-- child's parent lies in the other's world.
apart-w : ∀ {H q₁ q₂ l₁ l₂ w} → Plain l₁ → Plain l₂ → (q₁ ++ [ l₁ ] ≡ q₂ ++ [ l₂ ] → ⊥)
        → (W⁼ H (q₂ ++ [ l₂ ]) q₁ → ⊥) → (W⁼ H (q₁ ++ [ l₁ ]) q₂ → ⊥)
        → W⁼ H (q₁ ++ [ l₁ ]) w → W⁼ H (q₂ ++ [ l₂ ]) w → ⊥
apart-w {H} {q₁} {q₂} {l₁} {l₂} p₁ p₂ ne n₁ n₂ = go
  where
    a b : Pos
    a = q₁ ++ [ l₁ ]
    b = q₂ ++ [ l₂ ]

    go : ∀ {w} → W⁼ H a w → W⁼ H b w → ⊥
    go u here with shape u
    ... | sh-root eq              = ne (sym eq)
    ... | sh-plain {x} v _ eq     = n₂ (subst (W⁼ H a) (∷ʳ-injectiveˡ x q₂ (sym eq)) v)
    ... | sh-sub {x} _ eq         = plain-sub p₂ (∷ʳ-injectiveʳ q₂ x eq)
    go u (inW (step {x} v pl)) with shape u
    ... | sh-root eq              = n₁ (subst (W⁼ H b) (∷ʳ-injectiveˡ x q₁ eq) v)
    ... | sh-plain {x′} v′ _ eq   = go (subst (W⁼ H a) (∷ʳ-injectiveˡ x′ x (sym eq)) v′) v
    ... | sh-sub {x′} _ eq        = plain-sub pl (∷ʳ-injectiveʳ x x′ eq)
    go u (inW (timer {e} t v)) with shape u
    ... | sh-root eq              = plain-sub p₁ (sym (∷ʳ-injectiveʳ (ix t ∷ []) q₁ eq))
    ... | sh-plain {x′} _ pl eq   = plain-sub pl (sym (∷ʳ-injectiveʳ (ix t ∷ []) x′ eq))
    ... | sh-sub {x′} v′ eq       = go (subst (W⁼ H a) (sym (same-sub {ix t ∷ []} {x′} eq)) v′) v
    go u (inW (join {h} {e} _ v _)) with shape u
    ... | sh-root eq              = plain-sub p₁ (sym (∷ʳ-injectiveʳ h q₁ eq))
    ... | sh-plain {x′} _ pl eq   = plain-sub pl (sym (∷ʳ-injectiveʳ h x′ eq))
    ... | sh-sub {x′} v′ eq       = go (subst (W⁼ H a) (sym (same-sub {h} {x′} eq)) v′) v

-- A lane subscribed in the world is subscribed admissibly.
ok-in : ∀ {H p s} → Ok H p → W H p s → Real s → Ok H s
ok-in (_ , dj) ws rs = rs , λ hh w ins → dj hh (nest (inW ws) w) ins

-- Nothing in the world of a position's child leads the position.
not-up : ∀ {H q l w} → Real q → W⁼ H (q ++ [ l ]) w → w ⊑ q → ⊥
not-up {l = l} {w} rq v (zs , refl) with real-init w zs rq
... | inj₁ refl = nonempty⁼ (snoc≢[] zs) v
... | inj₂ rw = world-after⁼ v rw (≼-≺-≺ {w} {w ++ zs} {(w ++ zs) ++ [ l ]} (⊑-≼ {w} {w ++ zs} (zs , refl)) (≺-ext (w ++ zs) []))

-- Nothing in the world of a row's child leads a sibling of what leads it.
sib : ∀ {H q l x l′ w} → Real q → Plain l′ → x ⊑ q → (x ++ [ l′ ] ≡ q ++ [ l ] → ⊥) → W⁼ H (q ++ [ l ]) w → w ⊑ (x ++ [ l′ ]) → ⊥
sib {x = x} rq pl xq ne v le with ⊑-snoc x le
... | inj₁ wx = not-up rq v (⊑-trans wx xq)
... | inj₂ refl with w-up pl v
...   | inj₁ eq = ne (sym eq)
...   | inj₂ v′ = not-up rq v′ xq

-- No world position comes back to what it lies in.
cyc : ∀ {H₁ H₂ a w} → Real a → Real w → W⁼ H₁ w a → W H₂ a w → ⊥
cyc {a = a} {w} ra rw wa aw = ≺-irrefl {w} (≼-≺-≺ {w} {a} {w} (world-after⁼ wa ra) (world-after aw rw))

-- How a world position closing in `sub e` is reached.
data Named (H : Pos → Set) (p h e : Pos) : Set where
  n-root  : h ++ [ sub e ] ≡ p → Named H p h e
  n-timer : ∀ {t} → h ≡ ix t ∷ [] → W⁼ H p e → Named H p h e
  n-join  : H h ⊎ W H p h → W⁼ H p e → e ≺ h → Named H p h e

named-view : ∀ {H p h e} → W⁼ H p (h ++ [ sub e ]) → Named H p h e
named-view {H} {p} {h} {e} u = go u refl
  where
    go : ∀ {w} → W⁼ H p w → w ≡ h ++ [ sub e ] → Named H p h e
    go here eq = n-root (sym eq)
    go (inW (step {x} _ pl)) eq = ⊥-elim (plain-sub pl (∷ʳ-injectiveʳ x h eq))
    go (inW (timer t v)) eq with ∷ʳ-injectiveˡ (ix t ∷ []) h eq | same-sub {ix t ∷ []} {h} eq
    ... | hq | refl = n-timer (sym hq) v
    go (inW (join {h′} j v eh)) eq with ∷ʳ-injectiveˡ h′ h eq | same-sub {h′} {h} eq
    ... | refl | refl = n-join j v eh

named-e : ∀ {H p h e} → Named H p h e → (h ++ [ sub e ] ≡ p → ⊥) → W⁼ H p e
named-e (n-root eq)     nr = ⊥-elim (nr eq)
named-e (n-timer _ v)   _  = v
named-e (n-join _ v _)  _  = v

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

private

  -- A WORLD POSITION UNDER FEWER HOT ROWS lies in a sub-world under them,
  -- when the hot's rows lie in no world.
  mutual
    unwiden⁼ : ∀ {B H p a w} {t : EmissionSet B} → Disj (H ⊕ t) p → Real a → W⁼ H p a → Real w → W⁼ (H ⊕ t) a w → W⁼ H p w → W⁼ H a w
    unwiden⁼ dj ra pa rw here    _       = here
    unwiden⁼ dj ra pa rw (inW v) here    = ⊥-elim (cyc ra rw pa v)
    unwiden⁼ dj ra pa rw (inW v) (inW u) = inW (unwiden dj ra pa rw v u)

    unwiden : ∀ {B H p a w} {t : EmissionSet B} → Disj (H ⊕ t) p → Real a → W⁼ H p a → Real w → W (H ⊕ t) a w → W H p w → W H a w
    unwiden {H = H} {p} dj ra pa rw (step {x} v pl) u with real-init x _ rw | w-up pl (inW u)
    ... | inj₁ refl | _       = ⊥-elim (nonempty⁼ (λ { refl → ra }) v)
    ... | inj₂ _    | inj₁ eq = ⊥-elim (cyc ra rw (subst (λ z → W⁼ H z _) eq pa) (step v pl))
    ... | inj₂ rx   | inj₂ u′ = step (unwiden⁼ dj ra pa rx v u′) pl
    unwiden {H = H} dj ra pa rw (timer {e} t v) u =
      timer t (unwiden⁼ dj ra pa (proj₁ rw) v (named-e (named-view {h = ix t ∷ []} (inW u)) λ eq → cyc ra rw (subst (λ z → W⁼ H z _) (sym eq) pa) (timer t v)))
    unwiden {H = H} {t = t′} dj ra pa rw (join {h} {e} hj v eh) u with named-view {h = h} (inW u) | real-init h _ rw
    ... | n-root eq       | _      = ⊥-elim (cyc ra rw (subst (λ z → W⁼ H z _) (sym eq) pa) (join hj v eh))
    ... | _               | inj₁ refl = ⊥-elim rw
    ... | n-timer {t} refl u′ | _  = timer t (unwiden⁼ dj ra pa (proj₁ rw) v u′)
    ... | n-join (inj₁ hh) u′ _ | _ = join (inj₁ hh) (unwiden⁼ dj ra pa (real-last h rw) v u′) eh
    ... | n-join (inj₂ uh) u′ _ | inj₂ rh with hj
    ...   | inj₁ (inj₁ (_ , th)) = ⊥-elim (dj (inj₁ (_ , th)) (widen t′ uh) (⊑-inside (⊑-refl h)))
    ...   | inj₁ (inj₂ hh)       = join (inj₁ hh) (unwiden⁼ dj ra pa (real-last h rw) v u′) eh
    ...   | inj₂ vh              = join (inj₂ (unwiden dj ra pa rh vh uh)) (unwiden⁼ dj ra pa (real-last h rw) v u′) eh

-- A HANDLE KEEPS THE INVARIANT under more hot rows: admissible under more
-- is admissible under fewer, and the world only grows.
inv-widen : ∀ {A B H} {t : EmissionSet B} {d : Den A} → InvD H d → InvD (H ⊕ t) d
inv-widen {H = H} {t} {d} inv p (r , dj) = record
  { world = λ x → widen t (wo x)
  ; real  = re
  ; func  = fu
  ; flat  = fl
  ; burst = λ ce ye cy → bump (bu ce ye cy)
  ; under = un
  ; quiet = qu
  }
  where
    bump : ∀ {c y} → Σ Pos (λ w → W⁼ H p w × T (inside w c) × T (inside w y)) → Σ Pos (λ w → W⁼ (H ⊕ t) p w × T (inside w c) × T (inside w y))
    bump (w , w⁼ , i) = w , widen⁼ t w⁼ , i

    open InvAt (inv p (r , λ hh w ins → dj (inj₂ hh) (widen t w) ins)) renaming (world to wo; real to re; func to fu; flat to fl; burst to bu; under to ud; quiet to qu)

    un : ∀ {q y w l e e′} → enter d p q e → enter d p y e′ → Plain l → W⁼ (H ⊕ t) (q ++ [ l ]) w → w ⊑ y → ⊥
    un {q} {w = w} {l} x x′ pl v (zs , refl) with real-init w zs (re x′)
    ... | inj₁ refl = nonempty⁼ (snoc≢[] q) v
    ... | inj₂ rw with lead (inW (wo x′)) (zs , refl)
    ...   | l-root le = ⊑-≼ le (world-after wp rw)
      where wp = nest-in (widen t (step (inW (wo x)) pl)) v
    ...   | l-in u    = ud x x′ pl (unwiden⁼ dj (real-snoc q pl (re x)) (inW (step (inW (wo x)) pl)) rw v (inW u)) (zs , refl)
    ...   | l-hot hh le = dj (inj₂ hh) (nest-in (widen t (step (inW (wo x)) pl)) v) (⊑-inside le)
    ...   | l-tick le = lone r (nest-in (widen t (step (inW (wo x)) pl)) v) le

------------------------------------------------------------------------
-- The leaves keep it

out-inj : ∀ {A} {a b : A} → out a ≡ out b → a ≡ b
out-inj refl = refl

private
  -- One plain label below `p`.
  Below : Pos → Pos → Set
  Below p y = Σ Label λ l → Plain l × y ≡ p ++ [ l ]

  -- A READING ONE LABEL DEEP keeps the invariant: its rows are siblings,
  -- under `p` together.
  shallow-inv : ∀ {A H p} {X : EmissionSet A} → Ok H p → (∀ {y e} → X y e → Below p y)
              → (∀ {y e e′} → X y e → X y e′ → e ≡ e′) → (∀ {c y e} → X c end → X y e → c ≺ y → e ≡ skip) → InvAt H p X
  shallow-inv {H = H} {p} (r , _) sh fu qu = record
    { world = λ x → wo (sh x)
    ; real  = λ x → re (sh x)
    ; func  = fu
    ; flat  = λ x x′ → fl (sh x) (sh x′)
    ; burst = λ c y _ → p , here , ins (sh c) , ins (sh y)
    ; under = λ x y pl v le → un (sh x) (sh y) pl v le
    ; quiet = qu
    }
    where
      ne : ∀ {l₁ l₂ l} → p ++ [ l₂ ] ≡ (p ++ [ l₁ ]) ++ [ l ] → ⊥
      ne {l₁} {l₂} {l} eq with ++-cancelˡ p [ l₂ ] (l₁ ∷ l ∷ []) (trans eq (++-assoc p [ l₁ ] [ l ]))
      ... | ()

      un : ∀ {q y w l} → Below p q → Below p y → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
      un (_ , pl₁ , refl) (_ , pl₂ , refl) pl v le = sib (real-snoc p pl₁ r) pl₂ (⊑-snoc⁺ p) ne v le

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
          → (bk : ∀ {y e} → X y e → Σ (Ev B) (Y y)) → (∀ {y} → X y end → Y y end)
          → (∀ {y e} (x : X y e) → proj₁ (bk x) ≡ skip → e ≡ skip)
          → (∀ {y e e′} → X y e → X y e′ → e ≡ e′) → InvAt H p Y → InvAt H p X
  inv-via bk be bs fu I = record
    { world = λ x → InvAt.world I (proj₂ (bk x))
    ; real  = λ x → InvAt.real I (proj₂ (bk x))
    ; func  = fu
    ; flat  = λ x x′ → InvAt.flat I (proj₂ (bk x)) (proj₂ (bk x′))
    ; burst = λ c y cy → InvAt.burst I (be c) (proj₂ (bk y)) cy
    ; under = λ x y pl v le → InvAt.under I (proj₂ (bk x)) (proj₂ (bk y)) pl v le
    ; quiet = λ c y cy → bs y (InvAt.quiet I (be c) (proj₂ (bk y)) cy)
    }

  of-end : ∀ {A} p i (xs : List A) {y} → InE (ofᴱ p i xs) y end → y ≡ p ++ [ last ]
  of-end p i []       at-end     = refl
  of-end p i (x ∷ xs) (on-out r) = of-end p (suc i) xs r

  of-below : ∀ {A} p i (xs : List A) {y e} → InE (ofᴱ p i xs) y e → Below p y
  of-below p i []       at-end     = last , plain-last , refl
  of-below p i (x ∷ xs) at-out     = ix i , plain-ix , refl
  of-below p i (x ∷ xs) (on-out r) = of-below p (suc i) xs r

  acc-row : ∀ {A B} {f : B → A → B} {z} {t : EmissionSet A} {q b} → Scan.Acc f z t q b → Σ (Ev A) (t q)
  acc-row (Scan.acc₀ x _)     = _ , x
  acc-row (Scan.acc _ x _ _)  = _ , x

  spin-skip : ∀ {A p y} {e : Ev A} → Spin p y e → e ≡ skip
  spin-skip (spin _) = refl

  -- The rows of `of`, past the index it is at.
  of-idx : ∀ {A} p i (xs : List A) {y e} → InE (ofᴱ p i xs) y e → (Σ ℕ λ j → i ≤ j × y ≡ p ++ [ ix j ]) ⊎ y ≡ p ++ [ last ]
  of-idx p i []       at-end     = inj₂ refl
  of-idx p i (x ∷ xs) at-out     = inj₁ (i , ≤-refl , refl)
  of-idx p i (x ∷ xs) (on-out r) with of-idx p (suc i) xs r
  ... | inj₁ (j , le , eq) = inj₁ (j , ≤-trans (n≤1+n i) le , eq)
  ... | inj₂ eq            = inj₂ eq

  of-fresh : ∀ {A} p i (xs : List A) {e} → InE (ofᴱ p (suc i) xs) (p ++ [ ix i ]) e → ⊥
  of-fresh p i xs r with of-idx p (suc i) xs r
  ... | inj₁ (j , le , eq) with ∷ʳ-injectiveʳ p p eq
  ...   | refl = 1+n≰n le
  of-fresh p i xs r | inj₂ eq with ∷ʳ-injectiveʳ p p eq
  ... | ()

  of-func : ∀ {A} p i (xs : List A) {y e e′} → InE (ofᴱ p i xs) y e → InE (ofᴱ p i xs) y e′ → e ≡ e′
  of-func p i []       at-end     at-end      = refl
  of-func p i (x ∷ xs) at-out     at-out      = refl
  of-func p i (x ∷ xs) at-out     (on-out r′) = ⊥-elim (of-fresh p i xs r′)
  of-func p i (x ∷ xs) (on-out r) at-out      = ⊥-elim (of-fresh p i xs r)
  of-func p i (x ∷ xs) (on-out r) (on-out r′) = of-func p (suc i) xs r r′

  -- A fold has one value at a position.
  module AccF {A B : Set} (f : B → A → B) (z : B) {t : EmissionSet A} (fu : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) where
    open Scan f z t using (Acc; acc₀; acc)

    acc-val : ∀ {q b} → Acc q b → Σ A λ a → t q (out a)
    acc-val (acc₀ x _)    = _ , x
    acc-val (acc _ x _ _) = _ , x

    acc-func : ∀ {q q′ b b′} → q ≡ q′ → Acc q b → Acc q′ b′ → b ≡ b′
    acc-func refl (acc₀ x _)       (acc₀ x′ _)      = cong (f z) (out-inj (fu x x′))
    acc-func refl (acc₀ _ mn)      (acc a _ lt _)   = ⊥-elim (mn (proj₂ (acc-val a)) lt)
    acc-func refl (acc a _ lt _)   (acc₀ _ mn)      = ⊥-elim (mn (proj₂ (acc-val a)) lt)
    acc-func refl (acc {q₀} a x lt nx) (acc {q₁} a′ x′ lt′ nx′) =
      cong₂ f (acc-func (≼-antisym {q₀} {q₁} (λ h → nx′ (proj₂ (acc-val a)) h lt) (λ h → nx (proj₂ (acc-val a′)) h lt′)) a a′)
              (out-inj (fu x x′))

empty-inv : ∀ {A H} → InvD H (emptyᵀ {A})
empty-inv p ok = shallow-inv ok (λ { (at-end , _) → last , plain-last , refl }) (λ { (at-end , _) (at-end , _) → refl })
  λ { (at-end , _) (at-end , _) cy → ⊥-elim (≺-irrefl {p ++ [ last ]} cy) }

of-inv : ∀ {A H} (xs : List A) → InvD H (ofᵀ xs)
of-inv xs p ok = shallow-inv ok (λ x → of-below p 0 xs (proj₁ x)) (λ x x′ → of-func p 0 xs (proj₁ x) (proj₁ x′)) qu
  where
    qu : ∀ {c y e} → Truncate (InE (ofᴱ p 0 xs)) c end → Truncate (InE (ofᴱ p 0 xs)) y e → c ≺ y → _
    qu (c , _) (y , _) cy with of-end p 0 xs c | of-idx p 0 xs y
    ... | refl | inj₁ (j , _ , refl) = ⊥-elim (≺-absurd {p ++ [ last ]} {p ++ [ ix j ]} cy (Equivalence.from T-≡ (<ᵖ-part p {ix j} {last} [] [] refl)))
    ... | refl | inj₂ refl           = ⊥-elim (≺-irrefl {p ++ [ last ]} cy)

spin-inv : ∀ {A H} → InvD H (⊥ᵀ {A})
spin-inv p ok = shallow-inv ok (λ { (spin i , _) → ix i , plain-ix , refl }) (λ x x′ → trans (spin-skip (proj₁ x)) (sym (spin-skip (proj₁ x′))))
  λ _ y _ → spin-skip (proj₁ y)

map-inv : ∀ {A B H} (f : A → B) {s : Den A} → InvD H s → InvD H (mapᵀ f s)
map-inv f {s} inv p ok = inv-via bk be bs fu (inv p ok)
  where
    fu : ∀ {y e e′} → Truncate (MapT f (enter s p)) y e → Truncate (MapT f (enter s p)) y e′ → e ≡ e′
    fu (map-out x , _)  (map-out x′ , _)  = cong (out ∘ f) (out-inj (InvAt.func (inv p ok) x x′))
    fu (map-out x , _)  (map-skip x′ , _) with InvAt.func (inv p ok) x x′
    ... | ()
    fu (map-out x , _)  (map-end x′ , _)  with InvAt.func (inv p ok) x x′
    ... | ()
    fu (map-skip x , _) (map-out x′ , _)  with InvAt.func (inv p ok) x x′
    ... | ()
    fu (map-skip x , _) (map-skip x′ , _) = refl
    fu (map-skip x , _) (map-end x′ , _)  with InvAt.func (inv p ok) x x′
    ... | ()
    fu (map-end x , _)  (map-out x′ , _)  with InvAt.func (inv p ok) x x′
    ... | ()
    fu (map-end x , _)  (map-skip x′ , _) with InvAt.func (inv p ok) x x′
    ... | ()
    fu (map-end x , _)  (map-end x′ , _)  = refl

    bk : ∀ {y e} → Truncate (MapT f (enter s p)) y e → Σ _ (enter s p y)
    bk (map-out x , _)  = _ , x
    bk (map-skip x , _) = _ , x
    bk (map-end x , _)  = _ , x

    be : ∀ {y} → Truncate (MapT f (enter s p)) y end → enter s p y end
    be (map-end x , _) = x

    bs : ∀ {y e} (x : Truncate (MapT f (enter s p)) y e) → proj₁ (bk x) ≡ skip → e ≡ skip
    bs (map-out x , _)  ()
    bs (map-skip x , _) _ = refl
    bs (map-end x , _)  ()

scan-inv : ∀ {A B H} (f : B → A → B) z {s : Den A} → InvD H s → InvD H (scanᵀ f z s)
scan-inv f z {s} inv p ok = inv-via bk be bs fu (inv p ok)
  where
    I = inv p ok
    open AccF f z (InvAt.func I)

    fu : ∀ {y e e′} → Truncate (Scan.ScanT f z (enter s p)) y e → Truncate (Scan.ScanT f z (enter s p)) y e′ → e ≡ e′
    fu (Scan.sval a , _)  (Scan.sval a′ , _)  = cong out (acc-func refl a a′)
    fu (Scan.sval a , _)  (Scan.sstep x′ , _) with InvAt.func I (proj₂ (acc-val a)) x′
    ... | ()
    fu (Scan.sval a , _)  (Scan.send x′ , _)  with InvAt.func I (proj₂ (acc-val a)) x′
    ... | ()
    fu (Scan.sstep x , _) (Scan.sval a′ , _)  with InvAt.func I (proj₂ (acc-val a′)) x
    ... | ()
    fu (Scan.sstep x , _) (Scan.sstep x′ , _) = refl
    fu (Scan.sstep x , _) (Scan.send x′ , _)  with InvAt.func I x x′
    ... | ()
    fu (Scan.send x , _)  (Scan.sval a′ , _)  with InvAt.func I (proj₂ (acc-val a′)) x
    ... | ()
    fu (Scan.send x , _)  (Scan.sstep x′ , _) with InvAt.func I x x′
    ... | ()
    fu (Scan.send x , _)  (Scan.send x′ , _)  = refl

    bk : ∀ {y e} → Truncate (Scan.ScanT f z (enter s p)) y e → Σ _ (enter s p y)
    bk (Scan.sval a , _)  = acc-row a
    bk (Scan.sstep x , _) = _ , x
    bk (Scan.send x , _)  = _ , x

    be : ∀ {y} → Truncate (Scan.ScanT f z (enter s p)) y end → enter s p y end
    be (Scan.send x , _) = x

    bs : ∀ {y e} (x : Truncate (Scan.ScanT f z (enter s p)) y e) → proj₁ (bk x) ≡ skip → e ≡ skip
    bs (Scan.sval (Scan.acc₀ _ _) , _)    ()
    bs (Scan.sval (Scan.acc _ _ _ _) , _) ()
    bs (Scan.sstep x , _) _ = refl
    bs (Scan.send x , _)  ()

-- A DEFER keeps it: its guard lies before the body's subscription, and
-- the body's world lies in its own.
defer-inv : ∀ {A H} {s : Den A} → InvD H s → InvD H (deferᵀ s)
defer-inv {A} {H} {s} inv p ok = record { world = wo ; real = re ; func = λ x x′ → fu (view x) (view x′) ; flat = λ x x′ → fl (view x) (view x′)
  ; burst = λ c y cy → bu (view c) (view y) cy ; under = λ x y → un (view x) (view y) ; quiet = λ c y cy → qu (view c) (view y) cy }
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

    fu : ∀ {y e e′} → View y e → View y e′ → e ≡ e′
    fu (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
    fu (inj₁ (refl , _)) (inj₂ b) = ⊥-elim (≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (after b) (early []))
    fu (inj₂ b) (inj₁ (refl , _)) = ⊥-elim (≺-absurd {p ++ [ ix 1 ]} {p ++ [ ix 0 ]} (after b) (early []))
    fu (inj₂ b) (inj₂ b′) = InvAt.func I b b′

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

    g0 : W H p (p ++ [ ix 0 ])
    g0 = step here plain-ix

    rg : Real (p ++ [ ix 0 ])
    rg = real-snoc p plain-ix (proj₁ ok)

    -- What lies in the guard's child's world is not in the body's.
    off : ∀ {l w} → Plain l → W⁼ H ((p ++ [ ix 0 ]) ++ [ l ]) w → W⁼ H (p ++ [ ix 1 ]) w → ⊥
    off pl v v′ = apart (proj₁ ok) (world-anc⁼ (nest⁼ (inW (step here pl)) v)) (world-anc⁼ v′)

    un : ∀ {q y w l e e′} → View q e → View y e′ → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
    un (inj₁ (refl , _)) (inj₁ (refl , _)) pl v le = not-up rg v le
    un (inj₁ (refl , _)) (inj₂ b) pl v le =
      leads (proj₁ ok) (proj₂ ok) (nest-in (step (inW g0) pl) v) (off pl v) nr (inW (InvAt.world I b)) le
      where nr : _ ⊑ (p ++ [ ix 1 ]) → ⊥
            nr le′ with ⊑-snoc p le′
            ... | inj₁ wp   = not-up rg v (⊑-trans wp (⊑-snoc⁺ p))
            ... | inj₂ refl = off pl v here
    un (inj₂ b) (inj₁ (refl , _)) pl v le =
      anc-lead (world-anc⁼ (nest⁼ (inW (step (inW (InvAt.world I b)) pl)) v)) le rg (early [])
    un (inj₂ b) (inj₂ b′) pl v le = InvAt.under I b b′ pl v le

    qu : ∀ {c y e} → View c end → View y e → c ≺ y → e ≡ skip
    qu (inj₁ (_ , ())) _ _
    qu _ (inj₁ (_ , refl)) _ = refl
    qu (inj₂ b) (inj₂ b′) cy = InvAt.quiet I b b′ cy

-- A LIMIT keeps it: any finitely many of its rows are one member's.
lim-inv : ∀ {A H} {c : ℕ → Den A} → (∀ n → InvD H (c n)) → InvD H (LimD c)
lim-inv inv p ok = record
  { world = λ { (from N l , _) → InvAt.world (I N) (l N ≤-refl) }
  ; real  = λ { (from N l , _) → InvAt.real (I N) (l N ≤-refl) }
  ; func  = λ { (from N l , _) (from M m , _) → InvAt.func (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) }
  ; flat  = λ { (from N l , _) (from M m , _) → InvAt.flat (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) }
  ; burst = λ { (from N l , _) (from M m , _) cy → InvAt.burst (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) cy }
  ; under = λ { (from N l , _) (from M m , _) pl v le → InvAt.under (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) pl v le }
  ; quiet = λ { (from N l , _) (from M m , _) cy → InvAt.quiet (I (N ⊔ M)) (l (N ⊔ M) (m≤m⊔n N M)) (m (N ⊔ M) (m≤n⊔m N M)) cy }
  }
  where
    I = λ n → inv n p ok
