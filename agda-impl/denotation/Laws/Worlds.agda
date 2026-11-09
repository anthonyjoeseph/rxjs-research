{-# OPTIONS --guardedness #-}

-- WHERE A SUBSCRIPTION'S ROWS LIE: the invariant every reading of a lawful
-- observable keeps, and the positions a run can reach.
--
-- A subscription at `p` places its rows in its WORLD: below `p` a plain
-- label at a time; at a cascade's root `cascadeAt t e`, for a timer
-- created at `e` in the world, firing past `e`'s tick; and where a hot row
-- `h` is joined at `e` in the world, at `h ⊕ [ sub e ]`.  The world is
-- what lets a connect's source and body be told apart: neither's rows lie
-- in the other's world.
--
-- A REACHABLE position's cascades each fire past their creator's tick, and
-- every `sub e` in it names an earlier, reachable position.  A
-- subscription is ADMISSIBLE under hot rows `H` when it is reachable and
-- no hot row lies in its world: the hot was made elsewhere.
module denotation.Laws.Worlds where

open import Data.Bool using (T; true)
open import Data.Bool.Properties using (T-≡)
open import Data.Nat using (_<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-cancelˡ; ++-identityʳ; ++-conicalˡ; ∷-injective; ∷-injectiveˡ; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

import denotation.Position as P
open import denotation.Position using (Pos; Path; Label; ix; sub; last; frame; cascade; _∙_; _⊕_; root; cascadeAt; tick;
  isLt; cmpInstant; insideᵗ; inside)
open import denotation.Events using (inside-++; inside-self; inside-cons; <ᵖ-split; <ᵖ-between)
open import denotation.Simultaneity using (eqⁱ; later-tick; lexi-l; isLt-lt)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Silent; held; Unpinned; Dep; Few; Rejoin; shown; heard; ended; late; EmissionSet; _≺_; _≼_; Den; hot; coldAt; enter; DenEnv; from)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans; ≼-≺-≺; ≺-ext; ≼-false; entered-few)

-- A label that opens no subscription.
data Plain : Label → Set where
  plain-ix   : ∀ {i} → Plain (ix i)
  plain-last : Plain last

mutual
  -- The world of a subscription at `p` under hot rows `H`, `p` excluded.
  data W (H : Pos → Set) (p : Pos) : Pos → Set where
    step  : ∀ {x l} → W⁼ H p x → Plain l → W H p (x ⊕ [ l ])
    timer : ∀ {e} t → W⁼ H p e → tick e < t → W H p (cascadeAt t e)
    join  : ∀ {h e} → H h ⊎ W H p h → W⁼ H p e → e ≺ h → W H p (h ⊕ [ sub e ])

  -- The world with `p` itself.
  data W⁼ (H : Pos → Set) (p : Pos) : Pos → Set where
    here  : W⁼ H p p
    inW   : ∀ {x} → W H p x → W⁼ H p x

mutual
  -- Every cascade past its creator's tick, every `sub` naming an earlier
  -- reachable position.
  Real : Pos → Set
  Real (frame ∙ p)       = Back root p
  Real (cascade t e ∙ p) = Real e × tick e < t × Back (cascadeAt t e) p

  Back : Pos → Path → Set
  Back acc []          = ⊤
  Back acc (sub e ∷ p) = Real e × e ≺ (acc ⊕ [ sub e ]) × Back (acc ⊕ [ sub e ]) p
  Back acc (ix i ∷ p)  = Back (acc ⊕ [ ix i ]) p
  Back acc (last ∷ p)  = Back (acc ⊕ [ last ]) p

-- No hot row lies in the world.
Disj : (Pos → Set) → Pos → Set
Disj H p = ∀ {h w} → H h → W H p w → T (inside w h) → ⊥

-- ADMISSIBLE: reachable, and no hot row in its world.
Ok : (Pos → Set) → Pos → Set
Ok H p = Real p × Disj H p

-- The hot rows `H` and a hot's.
_∪ʰ_ : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
_∪ʰ_ {A} H t q = Σ (Ev A) (t q) ⊎ H q

-- A LAWFUL HOT: reachable rows, none below another, none past an end.
record Lawful {A} (t : EmissionSet A) : Set where
  field
    real   : ∀ {y e} → t y e → Real y
    func   : ∀ {y e e′} → t y e → t y e′ → e ≡ e′
    flat   : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥
    proper : ∀ {c y e} → t c end → t y e → y ≼ c

-- `x` LEADS `y`: `y` is `x` or lies under it.
_⊑_ : Pos → Pos → Set
x ⊑ y = Σ Path λ zs → y ≡ x ⊕ zs

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
-- lane's.  And only pins of earlier subscriptions follow an end: a value
-- after it would start a lane past the joiner's end, outside its burst.
--
-- What follows an end: a pin of a subscription made before it.
PinBy : ∀ {A} → Pos → Ev A → Set
PinBy c e = Σ Pos λ r → e ≡ pin r × r ≺ c

pinby-silent : ∀ {A} {c} {e : Ev A} → PinBy c e → Silent e
pinby-silent (_ , refl , _) = held

-- A TIMER'S ROOT: a cascade's root itself, where no row lies; every row
-- is a step of its cascade.
TimerRoot : Pos → Set
TimerRoot (cascade _ _ ∙ []) = ⊤
TimerRoot (frame ∙ [])       = ⊥
TimerRoot (_ ∙ (_ ∷ _))      = ⊥

-- A step under anything is no timer's root.
ext-untimed : ∀ x {l ys} → TimerRoot (x ⊕ (l ∷ ys)) → ⊥
ext-untimed (frame ∙ [])           ()
ext-untimed (frame ∙ (_ ∷ _))      ()
ext-untimed (cascade _ _ ∙ [])      ()
ext-untimed (cascade _ _ ∙ (_ ∷ _)) ()

-- REFUTED: 67919a90 flatMap-inv without `under`, by an outer row under a timer rooted below its own value's first child
record InvAt {A} (H : Pos → Set) (p : Pos) (X : EmissionSet A) : Set where
  field
    world : ∀ {y e} → X y e → W H p y
    real  : ∀ {y e} → X y e → Real y
    func  : ∀ {y e e′} → X y e → X y e′ → e ≡ e′
    flat  : ∀ {y e l ys e′} → X y e → X (y ⊕ (l ∷ ys)) e′ → ⊥
    burst : ∀ {c y e} → X c end → X y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    under : ∀ {q y w l e e′} → X q e → X y e′ → Plain l → W⁼ H (q ⊕ [ l ]) w → w ⊑ y → ⊥
    quiet : ∀ {c y e} → X c end → X y e → c ≺ y → PinBy c e
    pinned : ∀ {y r} → X y (pin r) → W⁼ H p r × T (inside r y)
    untimed : ∀ {y e} → X y e → TimerRoot y → ⊥

-- At every admissible subscription.
InvD : ∀ {A} → (Pos → Set) → Den A → Set
InvD H d = ∀ p → Ok H p → InvAt H p (enter d p)

-- The rows of an environment's hots.
Hots : ∀ {Γ} → DenEnv Γ → Pos → Set
Hots []           = λ _ → ⊥
Hots (hot t ∷ ρ)  = Hots ρ ∪ʰ t
Hots (coldAt _ ∷ ρ) = Hots ρ

-- A HANG SHOWS: past a position, a reader that reaches few rows before it
-- finds few rows of any kind there.  A row with infinitely many rows
-- before it is cut, so only an infinite chain of rows, each cut for the
-- ones below it, could hide a hang from the reader.
Shows : ∀ {A} → EmissionSet A → Set
Shows X = ∀ {v} → (Σ (List Pos) λ ks → ∀ {k e} → X k e → Few X k → k ≺ v → k ∈ ks) → ¬ ¬ Few X v

-- Anything but a pin waits on every row before it.
full : ∀ {X q} {e : Ev X} → Unpinned e → ∀ {k e′} → Dep q e k e′
full {e = out _} _ = tt
full {e = skip}  _ = tt
full {e = end}   _ = tt
full {e = pin _} ()

-- A joined hot pins nothing, so each row it shows has few before it.
hot-shows : ∀ {A} (t : EmissionSet A) p → Shows (enter (hot t) p)
hot-shows t p (ks , h) ¬f = ¬f (ks , λ x lt → h x (entered-few (hot t) p (full (un (proj₁ x))) x) lt)
  where
    un : ∀ {q e} → Rejoin p t q e → Unpinned e
    un (shown {e = out _} _ _ _) = tt
    un (shown {e = skip} _ _ _)  = tt
    un (heard _ _)               = tt
    un (ended _ _)               = tt
    un (late _ _)                = tt

-- A LAWFUL ENVIRONMENT: every handle keeps the invariant, and shows its hangs.
GoodEnv : ∀ {Γ} → DenEnv Γ → Set₁
GoodEnv {Γ} ρ = ∀ {A} (i : A ∈ Γ) → InvD (Hots ρ) (lookup ρ i) × (∀ p → Shows (enter (lookup ρ i) p))

------------------------------------------------------------------------
-- Steps below a position

∙-inj : ∀ {i j p q} → (i ∙ p) ≡ (j ∙ q) → i ≡ j × p ≡ q
∙-inj refl = refl , refl

⊕-assoc : ∀ x ys zs → (x ⊕ ys) ⊕ zs ≡ x ⊕ (ys ++ zs)
⊕-assoc (i ∙ p) ys zs = cong (i ∙_) (++-assoc p ys zs)

⊕-identityʳ : ∀ x → x ⊕ [] ≡ x
⊕-identityʳ (i ∙ p) = cong (i ∙_) (++-identityʳ p)

⊕-cancelˡ : ∀ x ys zs → x ⊕ ys ≡ x ⊕ zs → ys ≡ zs
⊕-cancelˡ (i ∙ p) ys zs e = ++-cancelˡ p ys zs (proj₂ (∙-inj e))

-- One label down, the position and the label are read back.
⊕-injˡ : ∀ x y {a b} → x ⊕ [ a ] ≡ y ⊕ [ b ] → x ≡ y
⊕-injˡ (i ∙ p) (j ∙ q) e with ∙-inj e
... | refl , e′ = cong (i ∙_) (∷ʳ-injectiveˡ p q e′)

⊕-injʳ : ∀ x y {a b} → x ⊕ [ a ] ≡ y ⊕ [ b ] → a ≡ b
⊕-injʳ (i ∙ p) (j ∙ q) e = ∷ʳ-injectiveʳ p q (proj₂ (∙-inj e))

-- A step below a position is no instant's root.
step≢root : ∀ x {l ys} i → x ⊕ (l ∷ ys) ≡ (i ∙ []) → ⊥
step≢root (_ ∙ [])      _ ()
step≢root (_ ∙ (_ ∷ _)) _ ()

-- Only an instant's root leads it.
⊑-unit : ∀ {w} i → w ⊑ (i ∙ []) → w ≡ (i ∙ [])
⊑-unit {_ ∙ []}      _ ([] , refl)    = refl
⊑-unit {_ ∙ []}      _ ((_ ∷ _) , ())
⊑-unit {_ ∙ (_ ∷ _)} _ (_ , ())

-- A timer's creator comes before its cascade.
timer-after : ∀ e {t} → tick e < t → e ≺ cascadeAt t e
timer-after (frame ∙ _)       _ = tt
timer-after (cascade u d ∙ q) h = Equivalence.from T-≡ (cong isLt (lexi-l (isLt-lt (later-tick d (cascade u d ∙ q) h))))

------------------------------------------------------------------------
-- Reachability

private
  back-init : ∀ acc x ys → Back acc (x ++ ys) → Back acc x
  back-init acc []          ys b              = tt
  back-init acc (sub e ∷ x) ys (r , lt , b)   = r , lt , back-init (acc ⊕ [ sub e ]) x ys b
  back-init acc (ix i ∷ x)  ys b              = back-init (acc ⊕ [ ix i ]) x ys b
  back-init acc (last ∷ x)  ys b              = back-init (acc ⊕ [ last ]) x ys b

  back-real : ∀ acc x {e} → Back acc (x ++ [ sub e ]) → Real e
  back-real acc []           (r , _ , _) = r
  back-real acc (sub e′ ∷ x) (_ , _ , b) = back-real (acc ⊕ [ sub e′ ]) x b
  back-real acc (ix i ∷ x)   b           = back-real (acc ⊕ [ ix i ]) x b
  back-real acc (last ∷ x)   b           = back-real (acc ⊕ [ last ]) x b

  -- What a reachable position's last `sub` names is reachable.
  real-last : ∀ x {e} → Real (x ⊕ [ sub e ]) → Real e
  real-last (frame ∙ p)       r           = back-real root p r
  real-last (cascade t e ∙ p) (_ , _ , b) = back-real (cascadeAt t e) p b

  back-snoc : ∀ acc x {l} → Plain l → Back acc x → Back acc (x ++ [ l ])
  back-snoc acc []           plain-ix   b            = tt
  back-snoc acc []           plain-last b            = tt
  back-snoc acc (sub e ∷ x)  pl         (r , lt , b) = r , lt , back-snoc (acc ⊕ [ sub e ]) x pl b
  back-snoc acc (ix j ∷ x)   pl         b            = back-snoc (acc ⊕ [ ix j ]) x pl b
  back-snoc acc (last ∷ x)   pl         b            = back-snoc (acc ⊕ [ last ]) x pl b

-- A reachable position's prefix is reachable.
real-init : ∀ x ys → Real (x ⊕ ys) → Real x
real-init (frame ∙ p)       ys r            = back-init root p ys r
real-init (cascade t e ∙ p) ys (re , h , b) = re , h , back-init (cascadeAt t e) p ys b

-- A reachable position one plain label down is reachable.
real-snoc : ∀ x {l} → Plain l → Real x → Real (x ⊕ [ l ])
real-snoc (frame ∙ p)       pl r            = back-snoc root p pl r
real-snoc (cascade t e ∙ p) pl (re , h , b) = re , h , back-snoc (cascadeAt t e) p pl b

private
  back-sub : ∀ acc x {e} → Back acc x → Real e → e ≺ ((acc ⊕ x) ⊕ [ sub e ]) → Back acc (x ++ [ sub e ])
  back-sub acc []           {e} b            re lt = re , subst (λ z → e ≺ (z ⊕ [ sub e ])) (⊕-identityʳ acc) lt , tt
  back-sub acc (sub e′ ∷ x) {e} (r , l , b)  re lt = r , l , back-sub (acc ⊕ [ sub e′ ]) x b re (subst (λ z → e ≺ (z ⊕ [ sub e ])) (sym (⊕-assoc acc [ sub e′ ] x)) lt)
  back-sub acc (ix j ∷ x)   {e} b            re lt = back-sub (acc ⊕ [ ix j ]) x b re (subst (λ z → e ≺ (z ⊕ [ sub e ])) (sym (⊕-assoc acc [ ix j ] x)) lt)
  back-sub acc (last ∷ x)   {e} b            re lt = back-sub (acc ⊕ [ last ]) x b re (subst (λ z → e ≺ (z ⊕ [ sub e ])) (sym (⊕-assoc acc [ last ] x)) lt)

-- A reachable position naming an earlier reachable one is reachable.
real-sub : ∀ x {e} → Real x → Real e → e ≺ (x ⊕ [ sub e ]) → Real (x ⊕ [ sub e ])
real-sub (frame ∙ p)        r            re lt = back-sub root p r re lt
real-sub (cascade t e′ ∙ p) (r′ , h , b) re lt = r′ , h , back-sub (cascadeAt t e′) p b re lt

------------------------------------------------------------------------
-- The world

-- THE WORLD LIES AFTER THE SUBSCRIPTION: each world row extends, joins
-- after, or times from a row at or after it.
mutual
  world-after : ∀ {H p y} → W H p y → Real y → p ≺ y
  world-after {p = p} (step here _) r = ≺-ext p []
  world-after {p = p} (step {x} {l} (inW w) _) r = ≺-trans {p} {x} {x ⊕ [ l ]} (world-after w (real-init x [ l ] r)) (≺-ext x [])
  world-after {p = p} (timer {e} t w h) (re , _ , _) = ≼-≺-≺ {p} {e} {cascadeAt t e} (world-after⁼ w re) (timer-after e h)
  world-after {p = p} (join {h} {e} _ w eh) r =
    ≼-≺-≺ {p} {e} {h ⊕ [ sub e ]} (world-after⁼ w (real-last h r)) (≺-trans {e} {h} {h ⊕ [ sub e ]} eh (≺-ext h []))

  world-after⁼ : ∀ {H p y} → W⁼ H p y → Real y → p ≼ y
  world-after⁼ {p = p} here    r = ≼-refl {p}
  world-after⁼ {p = p} {y} (inW w) r = ≺→≼ {p} {y} (world-after w r)

-- The world one tick down lies in the world.
mutual
  shrink : ∀ {H p i w} → W H (p ⊕ [ ix i ]) w → W H p w
  shrink (step w l)           = step (inW (shrink⁼ w)) l
  shrink (timer t w lt)       = timer t (inW (shrink⁼ w)) lt
  shrink (join (inj₁ h) w eh) = join (inj₁ h) (inW (shrink⁼ w)) eh
  shrink (join (inj₂ v) w eh) = join (inj₂ (shrink v)) (inW (shrink⁼ w)) eh

  shrink⁼ : ∀ {H p i w} → W⁼ H (p ⊕ [ ix i ]) w → W H p w
  shrink⁼ here    = step here plain-ix
  shrink⁼ (inW w) = shrink w

-- A world inside the world lies in it.
mutual
  nest : ∀ {H p a w} → W⁼ H p a → W H a w → W H p w
  nest pa (step w l)           = step (nest⁼ pa w) l
  nest pa (timer t w lt)       = timer t (nest⁼ pa w) lt
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
  narrow : ∀ {B H p i w} {t : EmissionSet B} → (∀ {h e} → t h e → W H p h) → W (H ∪ʰ t) (p ⊕ [ ix i ]) w → W H p w
  narrow tw (step w l)                     = step (inW (narrow⁼ tw w)) l
  narrow tw (timer k w lt)                 = timer k (inW (narrow⁼ tw w)) lt
  narrow tw (join (inj₁ (inj₁ (_ , x))) w eh) = join (inj₂ (tw x)) (inW (narrow⁼ tw w)) eh
  narrow tw (join (inj₁ (inj₂ h)) w eh)    = join (inj₁ h) (inW (narrow⁼ tw w)) eh
  narrow tw (join (inj₂ v) w eh)           = join (inj₂ (narrow tw v)) (inW (narrow⁼ tw w)) eh

  narrow⁼ : ∀ {B H p i w} {t : EmissionSet B} → (∀ {h e} → t h e → W H p h) → W⁼ (H ∪ʰ t) (p ⊕ [ ix i ]) w → W H p w
  narrow⁼ tw here    = step here plain-ix
  narrow⁼ tw (inW w) = narrow tw w

-- A `defer`'s body is subscribed admissibly.
ok-step : ∀ {H} p → Ok H p → Ok H (p ⊕ [ ix 1 ])
ok-step p (r , d) = real-snoc p plain-ix r , λ hh w ins → d hh (shrink w) ins

------------------------------------------------------------------------
-- Ancestry

-- No position is its own extension.
ext≢ : ∀ x {l} ys → x ⊕ (l ∷ ys) ≡ x → ⊥
ext≢ x ys eq = ≺-irrefl {x} (subst (x ≺_) eq (≺-ext x ys))

⊑-refl : ∀ x → x ⊑ x
⊑-refl x = [] , sym (⊕-identityʳ x)

⊑-snoc⁺ : ∀ x {l} → x ⊑ (x ⊕ [ l ])
⊑-snoc⁺ x {l} = [ l ] , refl

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans {x} (zs , refl) (ws , refl) = zs ++ ws , ⊕-assoc x zs ws

⊑-≼ : ∀ {x y} → x ⊑ y → x ≼ y
⊑-≼ {x} ([] , refl)     = subst (x ≼_) (sym (⊕-identityʳ x)) (≼-refl {x})
⊑-≼ {x} (z ∷ zs , refl) = ≺→≼ {x} {x ⊕ (z ∷ zs)} (≺-ext x zs)

⊑-inside : ∀ {x y} → x ⊑ y → T (inside x y)
⊑-inside {x} (zs , refl) = Equivalence.from T-≡ (inside-++ x x zs (inside-self x))

private
  inside-⊑ᵗ : ∀ x y → insideᵗ x y ≡ true → Σ Path λ zs → y ≡ x ++ zs
  inside-⊑ᵗ []      y       _ = y , refl
  inside-⊑ᵗ (a ∷ x) []      ()
  inside-⊑ᵗ (a ∷ x) (b ∷ y) i with inside-cons a x b y i
  ... | refl , i′ with inside-⊑ᵗ x y i′
  ...   | zs , e = zs , cong (a ∷_) e

inside-⊑ : ∀ x y → T (inside x y) → x ⊑ y
inside-⊑ (i ∙ r) (j ∙ k) h with cmpInstant i j in c
... | P.lt = ⊥-elim h
... | P.gt = ⊥-elim h
... | P.eq with eqⁱ i j c | inside-⊑ᵗ r k (Equivalence.to T-≡ h)
...   | refl | zs , e = zs , cong (i ∙_) e

-- What lies under `w` is an interval.
conv : ∀ {w a b y} → w ⊑ a → a ≼ b → b ≺ y → w ⊑ y → w ⊑ b
conv {w} {a} {b} wa ab by (ys , refl) with <ᵖ-split w b (≼-false {w} {b} (≼-trans {w} {a} {b} (⊑-≼ wa) ab))
... | inj₁ lt   = <ᵖ-between w b ys lt (Equivalence.to T-≡ by)
... | inj₂ refl = [] , sym (⊕-identityʳ w)

-- A row before a row under the subscription is under it.
in-world : ∀ {C H p} {X : EmissionSet C} → InvAt H p X → ∀ {k y e} → X k e → k ≺ y → T (inside p y) → T (inside p k)
in-world {p = p} I {k} {y} x lt i =
  ⊑-inside (conv (⊑-refl p) (≺→≼ {p} {k} (world-after (InvAt.world I x) (InvAt.real I x))) lt (inside-⊑ p y i))

private
  snocᵗ : ∀ w y {l} zs → y ++ [ l ] ≡ w ++ zs → (Σ Path λ vs → y ≡ w ++ vs) ⊎ w ≡ y ++ [ l ]
  snocᵗ []      y       zs eq = inj₁ (y , refl)
  snocᵗ (a ∷ w) []      zs eq with ∷-injective eq
  ... | refl , eq′ with ++-conicalˡ w zs (sym eq′)
  ...   | refl = inj₂ refl
  snocᵗ (a ∷ w) (b ∷ y) zs eq with ∷-injective eq
  ... | refl , eq′ with snocᵗ w y zs eq′
  ...   | inj₁ (vs , e) = inj₁ (vs , cong (a ∷_) e)
  ...   | inj₂ e        = inj₂ (cong (a ∷_) e)

  cmpᵗ : ∀ w k zs zs′ → w ++ zs ≡ k ++ zs′ → (Σ Path λ vs → k ≡ w ++ vs) ⊎ (Σ Path λ vs → w ≡ k ++ vs)
  cmpᵗ []      k       _  _   _  = inj₁ (k , refl)
  cmpᵗ (a ∷ w) []      _  _   _  = inj₂ (a ∷ w , refl)
  cmpᵗ (a ∷ w) (c ∷ k) zs zs′ eq with ∷-injective eq
  ... | refl , eq′ with cmpᵗ w k zs zs′ eq′
  ...   | inj₁ (vs , e) = inj₁ (vs , cong (a ∷_) e)
  ...   | inj₂ (vs , e) = inj₂ (vs , cong (a ∷_) e)

-- Leading `y ⊕ [ l ]`: leading `y`, or it.
⊑-snoc : ∀ {w} y {l} → w ⊑ (y ⊕ [ l ]) → w ⊑ y ⊎ w ≡ y ⊕ [ l ]
⊑-snoc {i ∙ a} (j ∙ b) (zs , e) with ∙-inj e
... | refl , e′ with snocᵗ a b zs e′
...   | inj₁ (vs , e″) = inj₁ (vs , cong (i ∙_) e″)
...   | inj₂ e″        = inj₂ (cong (i ∙_) e″)

-- Two leaders of one position: one leads the other.
⊑-cmp : ∀ w k {b} → w ⊑ b → k ⊑ b → w ⊑ k ⊎ k ⊑ w
⊑-cmp (i ∙ a) (j ∙ c) (zs , refl) (zs′ , e) with ∙-inj e
... | refl , e′ with cmpᵗ a c zs zs′ e′
...   | inj₁ (vs , e″) = inj₁ (vs , cong (i ∙_) e″)
...   | inj₂ (vs , e″) = inj₂ (vs , cong (i ∙_) e″)

-- Positions apart past a common prefix.
diverge : ∀ k {a b : Label} ys ms → (a ≡ b → ⊥) → (k ⊕ [ a ]) ⊕ ys ≡ (k ⊕ [ b ]) ⊕ ms → ⊥
diverge k {a} {b} ys ms ne eq =
  ne (∷-injectiveˡ (⊕-cancelˡ k (a ∷ ys) (b ∷ ms) (trans (sym (⊕-assoc k [ a ] ys)) (trans eq (⊕-assoc k [ b ] ms)))))

-- A row leading another of a flat reading is it.
same-lead : ∀ {C H q} {X : EmissionSet C} → InvAt H q X → ∀ {k k′ e e′} → X k e → X k′ e′ → k ⊑ k′ → k ≡ k′
same-lead I {k} x x′ ([] , eq)      = trans (sym (⊕-identityʳ k)) (sym eq)
same-lead I     x x′ (z ∷ zs , refl) = ⊥-elim (InvAt.flat I x x′)

-- No row of a flat reading lies under another's child.
flat-under : ∀ {C H q} {X : EmissionSet C} → InvAt H q X → ∀ {k k′ a e e′} → X k e → X k′ e′ → (k ⊕ [ a ]) ⊑ k′ → ⊥
flat-under {X = X} I {k} {a = a} {e′ = e′} x x′ (zs , refl) = InvAt.flat I x (subst (λ z → X z e′) (⊕-assoc k [ a ] zs) x′)

-- `a` is `c`'s PARENT: `c` steps a plain label from it, names it in a
-- closing `sub`, or roots a cascade it created.
data Parent (a c : Pos) : Set where
  plain : ∀ {l} → Plain l → c ≡ a ⊕ [ l ] → Parent a c
  named : ∀ h → c ≡ h ⊕ [ sub a ] → Parent a c
  timed : ∀ t → c ≡ cascadeAt t a → Parent a c

step-parent : ∀ x {l} → Plain l → Parent x (x ⊕ [ l ])
step-parent x pl = plain pl refl

plain-sub : ∀ {l e} → Plain l → l ≡ sub e → ⊥
plain-sub plain-ix   ()
plain-sub plain-last ()

-- A position has one parent.
parent-fun : ∀ {a b c} → Parent a c → Parent b c → a ≡ b
parent-fun {a} {b} (plain _ e)  (plain _ e′)  = ⊕-injˡ a b (trans (sym e) e′)
parent-fun {a}     (plain pl e) (named h e′)  = ⊥-elim (plain-sub pl (⊕-injʳ a h (trans (sym e) e′)))
parent-fun {b = b} (named h e)  (plain pl e′) = ⊥-elim (plain-sub pl (sym (⊕-injʳ h b (trans (sym e) e′))))
parent-fun         (named h e)  (named h′ e′) with ⊕-injʳ h h′ (trans (sym e) e′)
... | refl = refl
parent-fun {a}     (plain _ e)  (timed _ e′)  = ⊥-elim (step≢root a _ (trans (sym e) e′))
parent-fun         (named h e)  (timed _ e′)  = ⊥-elim (step≢root h _ (trans (sym e) e′))
parent-fun {b = b} (timed _ e)  (plain _ e′)  = ⊥-elim (step≢root b _ (trans (sym e′) e))
parent-fun         (timed _ e)  (named h e′)  = ⊥-elim (step≢root h _ (trans (sym e′) e))
parent-fun         (timed _ e)  (timed _ e′)  with trans (sym e) e′
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

private
  back-lt : ∀ acc x {e} → Back acc (x ++ [ sub e ]) → e ≺ ((acc ⊕ x) ⊕ [ sub e ])
  back-lt acc []           {e} (_ , lt , _) = subst (λ z → e ≺ (z ⊕ [ sub e ])) (sym (⊕-identityʳ acc)) lt
  back-lt acc (sub e′ ∷ x) {e} (_ , _ , b)  = subst (λ z → e ≺ (z ⊕ [ sub e ])) (⊕-assoc acc [ sub e′ ] x) (back-lt (acc ⊕ [ sub e′ ]) x b)
  back-lt acc (ix i ∷ x)   {e} b            = subst (λ z → e ≺ (z ⊕ [ sub e ])) (⊕-assoc acc [ ix i ] x) (back-lt (acc ⊕ [ ix i ]) x b)
  back-lt acc (last ∷ x)   {e} b            = subst (λ z → e ≺ (z ⊕ [ sub e ])) (⊕-assoc acc [ last ] x) (back-lt (acc ⊕ [ last ]) x b)

  real-lt : ∀ x {e} → Real (x ⊕ [ sub e ]) → e ≺ (x ⊕ [ sub e ])
  real-lt (frame ∙ p)        r           = back-lt root p r
  real-lt (cascade t e′ ∙ p) (_ , _ , b) = back-lt (cascadeAt t e′) p b

  -- A reachable position's parent is reachable, and before it.
  parent-real : ∀ {b c} → Parent b c → Real c → Real b × b ≺ c
  parent-real {b} (plain {l} _ refl) r            = real-init b [ l ] r , ≺-ext b []
  parent-real     (named h refl)     r            = real-last h r , real-lt h r
  parent-real {b} (timed _ refl)     (rb , h , _) = rb , timer-after b h

-- AN ANCESTOR comes no later.
anc-≼ : ∀ {a c} → Anc a c → Real c → a ≼ c
anc-≼ {a} self r = ≼-refl {a}
anc-≼ {a} {c} (up {b} x pb) r with parent-real pb r
... | rb , bc = ≺→≼ {a} {c} (≼-≺-≺ {a} {b} {c} (anc-≼ x rb) bc)

-- The world descends from its subscription.
mutual
  world-anc : ∀ {H p w} → W H p w → Anc p w
  world-anc (step w pl)       = up (world-anc⁼ w) (plain pl refl)
  world-anc (timer t w _)     = up (world-anc⁼ w) (timed t refl)
  world-anc (join {h} _ w _)  = up (world-anc⁼ w) (named h refl)

  world-anc⁼ : ∀ {H p w} → W⁼ H p w → Anc p w
  world-anc⁼ here    = self
  world-anc⁼ (inW w) = world-anc w

private
  not-under : ∀ {p i j} → (i ≡ j → ⊥) → Real p → Anc (p ⊕ [ ix i ]) (p ⊕ [ ix j ]) → ⊥
  not-under {p} {i} {j} ne rp a with anc-view a
  ... | inj₁ eq = ne (ix-inj (⊕-injʳ p p eq))
    where ix-inj : ix i ≡ ix j → i ≡ j
          ix-inj refl = refl
  ... | inj₂ (b , x , pb) with parent-fun pb (step-parent p {ix j} plain-ix)
  ...   | refl = anc-≼ x rp (≺-ext p [])

-- SIBLING WORLDS ARE APART: nothing descends from both `p ⊕ [ ix 0 ]` and
-- `p ⊕ [ ix 1 ]`; each is the other's only through `p`, before both.
apart : ∀ {p w} → Real p → Anc (p ⊕ [ ix 0 ]) w → Anc (p ⊕ [ ix 1 ]) w → ⊥
apart rp x y with anc-lin x y
... | inj₁ a = not-under (λ ()) rp a
... | inj₂ a = not-under (λ ()) rp a

-- A descendant of `a` leads nothing reachable before `a`.
anc-lead : ∀ {a w q} → Anc a w → w ⊑ q → Real q → q ≺ a → ⊥
anc-lead {a} {w} x (zs , refl) rq qa =
  ≼-trans {a} {w} {w ⊕ zs} (anc-≼ x (real-init w zs rq)) (⊑-≼ {w} {w ⊕ zs} (zs , refl)) qa

------------------------------------------------------------------------
-- What leads a world position

-- What leads a world position: what leads the subscription, a position
-- of the world, or what leads a joined hot row.
data Lead (H : Pos → Set) (b w : Pos) : Set where
  l-root : w ⊑ b → Lead H b w
  l-in   : W H b w → Lead H b w
  l-hot  : ∀ {h} → H h → w ⊑ h → Lead H b w

mutual
  lead : ∀ {H b x w} → W⁼ H b x → w ⊑ x → Lead H b w
  lead here    le = l-root le
  lead (inW v) le = lead′ v le

  lead′ : ∀ {H b x w} → W H b x → w ⊑ x → Lead H b w
  lead′ (step {x′} v pl) le with ⊑-snoc x′ le
  ... | inj₁ le′  = lead v le′
  ... | inj₂ refl = l-in (step v pl)
  lead′ (timer t v lt) le with ⊑-unit _ le
  ... | refl = l-in (timer t v lt)
  lead′ (join {h} (inj₁ hh) v eh) le with ⊑-snoc h le
  ... | inj₁ le′  = l-hot hh le′
  ... | inj₂ refl = l-in (join (inj₁ hh) v eh)
  lead′ (join {h} (inj₂ u) v eh) le with ⊑-snoc h le
  ... | inj₁ le′  = lead′ u le′
  ... | inj₂ refl = l-in (join (inj₂ u) v eh)

-- A WORLD POSITION LEADS NO POSITION OF A WORLD it is not in, unless it
-- leads that world's subscription.
leads : ∀ {H p b w x} → Disj H p → W H p w → (W⁼ H b w → ⊥) → (w ⊑ b → ⊥) → W⁼ H b x → w ⊑ x → ⊥
leads dj ww nb nr bx le with lead bx le
... | l-root r  = nr r
... | l-in v    = nb (inW v)
... | l-hot h r = dj h ww (⊑-inside r)

-- How a world position is reached: it is the subscription, one plain
-- label below a world position, names one in a closing `sub`, or roots a
-- cascade one created.
data Shape (H : Pos → Set) (a w : Pos) : Set where
  sh-root  : w ≡ a → Shape H a w
  sh-plain : ∀ {x l} → W⁼ H a x → Plain l → w ≡ x ⊕ [ l ] → Shape H a w
  sh-sub   : ∀ {x e} → W⁼ H a e → w ≡ x ⊕ [ sub e ] → Shape H a w
  sh-timer : ∀ {t e} → W⁼ H a e → w ≡ cascadeAt t e → Shape H a w

shape : ∀ {H a w} → W⁼ H a w → Shape H a w
shape here                    = sh-root refl
shape (inW (step v pl))       = sh-plain v pl refl
shape (inW (timer t v _))     = sh-timer v refl
shape (inW (join v e eh))     = sh-sub e refl

-- One plain label below a world position: the subscription, or its parent
-- is one.
w-up : ∀ {H a x l} → Plain l → W⁼ H a (x ⊕ [ l ]) → a ≡ x ⊕ [ l ] ⊎ W⁼ H a x
w-up {x = x} pl v with shape v
... | sh-root eq            = inj₁ (sym eq)
... | sh-plain {x′} u _ eq  = inj₂ (subst (W⁼ _ _) (sym (⊕-injˡ x x′ eq)) u)
... | sh-sub {x′} _ eq      = ⊥-elim (plain-sub pl (⊕-injʳ x x′ eq))
... | sh-timer _ eq         = ⊥-elim (step≢root x _ eq)

-- A cascade's root in the world: the subscription, or its creator is in
-- the world.
timed-view : ∀ {H p t e} → W⁼ H p (cascadeAt t e) → cascadeAt t e ≡ p ⊎ W⁼ H p e
timed-view u with shape u
... | sh-root eq          = inj₁ eq
... | sh-plain {x} _ _ eq = ⊥-elim (step≢root x _ (sym eq))
... | sh-sub {x} _ eq     = ⊥-elim (step≢root x _ (sym eq))
... | sh-timer v refl     = inj₂ v

private
  sub-inj : ∀ {a b} → sub a ≡ sub b → a ≡ b
  sub-inj refl = refl

  -- Where two shapes name a closing `sub`, they name one position.
  same-sub : ∀ {x x′ e e′} → x ⊕ [ sub e ] ≡ x′ ⊕ [ sub e′ ] → e ≡ e′
  same-sub {x} {x′} eq = sub-inj (⊕-injʳ x x′ eq)

-- THE WORLDS OF TWO CHILDREN ARE APART when they are two, and neither
-- child's parent lies in the other's world.
apart-w : ∀ {H q₁ q₂ l₁ l₂ w} → Plain l₁ → Plain l₂ → (q₁ ⊕ [ l₁ ] ≡ q₂ ⊕ [ l₂ ] → ⊥)
        → (W⁼ H (q₂ ⊕ [ l₂ ]) q₁ → ⊥) → (W⁼ H (q₁ ⊕ [ l₁ ]) q₂ → ⊥)
        → W⁼ H (q₁ ⊕ [ l₁ ]) w → W⁼ H (q₂ ⊕ [ l₂ ]) w → ⊥
apart-w {H} {q₁} {q₂} {l₁} {l₂} p₁ p₂ ne n₁ n₂ = go
  where
    a b : Pos
    a = q₁ ⊕ [ l₁ ]
    b = q₂ ⊕ [ l₂ ]

    go : ∀ {w} → W⁼ H a w → W⁼ H b w → ⊥
    go u here with shape u
    ... | sh-root eq              = ne (sym eq)
    ... | sh-plain {x} v _ eq     = n₂ (subst (W⁼ H a) (⊕-injˡ x q₂ (sym eq)) v)
    ... | sh-sub {x} _ eq         = plain-sub p₂ (⊕-injʳ q₂ x eq)
    ... | sh-timer _ eq           = step≢root q₂ _ eq
    go u (inW (step {x} v pl)) with shape u
    ... | sh-root eq              = n₁ (subst (W⁼ H b) (⊕-injˡ x q₁ eq) v)
    ... | sh-plain {x′} v′ _ eq   = go (subst (W⁼ H a) (⊕-injˡ x′ x (sym eq)) v′) v
    ... | sh-sub {x′} _ eq        = plain-sub pl (⊕-injʳ x x′ eq)
    ... | sh-timer _ eq           = step≢root x _ eq
    go u (inW (timer t v _)) with shape u
    ... | sh-root eq              = step≢root q₁ _ (sym eq)
    ... | sh-plain {x′} _ _ eq    = step≢root x′ _ (sym eq)
    ... | sh-sub {x′} _ eq        = step≢root x′ _ (sym eq)
    ... | sh-timer v′ refl        = go v′ v
    go u (inW (join {h} {e} _ v _)) with shape u
    ... | sh-root eq              = plain-sub p₁ (sym (⊕-injʳ h q₁ eq))
    ... | sh-plain {x′} _ pl eq   = plain-sub pl (sym (⊕-injʳ h x′ eq))
    ... | sh-sub {x′} v′ eq       = go (subst (W⁼ H a) (sym (same-sub {h} {x′} eq)) v′) v
    ... | sh-timer _ eq           = step≢root h _ eq

-- A lane subscribed in the world is subscribed admissibly.
ok-in : ∀ {H p s} → Ok H p → W H p s → Real s → Ok H s
ok-in (_ , dj) ws rs = rs , λ hh w ins → dj hh (nest (inW ws) w) ins

-- Nothing in the world of a position's child leads the position.
not-up : ∀ {H q l w} → Real q → W⁼ H (q ⊕ [ l ]) w → w ⊑ q → ⊥
not-up {l = l} {w} rq v (zs , refl) =
  world-after⁼ v (real-init w zs rq) (≼-≺-≺ {w} {w ⊕ zs} {(w ⊕ zs) ⊕ [ l ]} (⊑-≼ {w} {w ⊕ zs} (zs , refl)) (≺-ext (w ⊕ zs) []))

-- Nothing in the world of a row's child leads a sibling of what leads it.
sib : ∀ {H q l x l′ w} → Real q → Plain l′ → x ⊑ q → (x ⊕ [ l′ ] ≡ q ⊕ [ l ] → ⊥) → W⁼ H (q ⊕ [ l ]) w → w ⊑ (x ⊕ [ l′ ]) → ⊥
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
  n-root  : h ⊕ [ sub e ] ≡ p → Named H p h e
  n-join  : H h ⊎ W H p h → W⁼ H p e → e ≺ h → Named H p h e

named-view : ∀ {H p h e} → W⁼ H p (h ⊕ [ sub e ]) → Named H p h e
named-view {H} {p} {h} {e} u = go u refl
  where
    go : ∀ {w} → W⁼ H p w → w ≡ h ⊕ [ sub e ] → Named H p h e
    go here eq = n-root (sym eq)
    go (inW (step {x} _ pl)) eq = ⊥-elim (plain-sub pl (⊕-injʳ x h eq))
    go (inW (timer _ _ _)) eq = ⊥-elim (step≢root h _ (sym eq))
    go (inW (join {h′} j v eh)) eq with ⊕-injˡ h′ h eq | same-sub {h′} {h} eq
    ... | refl | refl = n-join j v eh

named-e : ∀ {H p h e} → Named H p h e → (h ⊕ [ sub e ] ≡ p → ⊥) → W⁼ H p e
named-e (n-root eq)     nr = ⊥-elim (nr eq)
named-e (n-join _ v _)  _  = v

-- More hot rows, the same world.
mutual
  widen : ∀ {B H p w} (t : EmissionSet B) → W H p w → W (H ∪ʰ t) p w
  widen t (step w l)           = step (widen⁼ t w) l
  widen t (timer i w lt)       = timer i (widen⁼ t w) lt
  widen t (join (inj₁ h) w eh) = join (inj₁ (inj₂ h)) (widen⁼ t w) eh
  widen t (join (inj₂ v) w eh) = join (inj₂ (widen t v)) (widen⁼ t w) eh

  widen⁼ : ∀ {B H p w} (t : EmissionSet B) → W⁼ H p w → W⁼ (H ∪ʰ t) p w
  widen⁼ t here    = here
  widen⁼ t (inW w) = inW (widen t w)

private

  -- A WORLD POSITION UNDER FEWER HOT ROWS lies in a sub-world under them,
  -- when the hot's rows lie in no world.
  mutual
    unwiden⁼ : ∀ {B H p a w} {t : EmissionSet B} → Disj (H ∪ʰ t) p → Real a → W⁼ H p a → Real w → W⁼ (H ∪ʰ t) a w → W⁼ H p w → W⁼ H a w
    unwiden⁼ dj ra pa rw here    _       = here
    unwiden⁼ dj ra pa rw (inW v) here    = ⊥-elim (cyc ra rw pa v)
    unwiden⁼ dj ra pa rw (inW v) (inW u) = inW (unwiden dj ra pa rw v u)

    unwiden : ∀ {B H p a w} {t : EmissionSet B} → Disj (H ∪ʰ t) p → Real a → W⁼ H p a → Real w → W (H ∪ʰ t) a w → W H p w → W H a w
    unwiden {H = H} dj ra pa rw (step {x} v pl) u with w-up pl (inW u)
    ... | inj₁ eq = ⊥-elim (cyc ra rw (subst (λ z → W⁼ H z _) eq pa) (step v pl))
    ... | inj₂ u′ = step (unwiden⁼ dj ra pa (real-init x _ rw) v u′) pl
    unwiden {H = H} dj ra pa rw (timer t v lt) u with timed-view (inW u)
    ... | inj₁ eq = ⊥-elim (cyc ra rw (subst (λ z → W⁼ H z _) (sym eq) pa) (timer t v lt))
    ... | inj₂ u′ = timer t (unwiden⁼ dj ra pa (proj₁ rw) v u′) lt
    unwiden {H = H} {t = t′} dj ra pa rw (join {h} {e} hj v eh) u with named-view {h = h} (inW u)
    ... | n-root eq       = ⊥-elim (cyc ra rw (subst (λ z → W⁼ H z _) (sym eq) pa) (join hj v eh))
    ... | n-join (inj₁ hh) u′ _ = join (inj₁ hh) (unwiden⁼ dj ra pa (real-last h rw) v u′) eh
    ... | n-join (inj₂ uh) u′ _ with hj
    ...   | inj₁ (inj₁ (_ , th)) = ⊥-elim (dj (inj₁ (_ , th)) (widen t′ uh) (⊑-inside (⊑-refl h)))
    ...   | inj₁ (inj₂ hh)       = join (inj₁ hh) (unwiden⁼ dj ra pa (real-last h rw) v u′) eh
    ...   | inj₂ vh              = join (inj₂ (unwiden dj ra pa (real-init h _ rw) vh uh)) (unwiden⁼ dj ra pa (real-last h rw) v u′) eh

-- A HANDLE KEEPS THE INVARIANT under more hot rows: admissible under more
-- is admissible under fewer, and the world only grows.
inv-widen : ∀ {A B H} {t : EmissionSet B} {d : Den A} → InvD H d → InvD (H ∪ʰ t) d
inv-widen {H = H} {t} {d} inv p (r , dj) = record
  { world = λ x → widen t (wo x)
  ; real  = re
  ; func  = fu
  ; flat  = fl
  ; burst = λ ce ye cy → bump (bu ce ye cy)
  ; under = un
  ; quiet = qu
  ; pinned = λ x → let (w⁼ , i) = pn x in widen⁼ t w⁼ , i
  ; untimed = ut
  }
  where
    bump : ∀ {c y} → Σ Pos (λ w → W⁼ H p w × T (inside w c) × T (inside w y)) → Σ Pos (λ w → W⁼ (H ∪ʰ t) p w × T (inside w c) × T (inside w y))
    bump (w , w⁼ , i) = w , widen⁼ t w⁼ , i

    open InvAt (inv p (r , λ hh w ins → dj (inj₂ hh) (widen t w) ins)) renaming (world to wo; real to re; func to fu; flat to fl; burst to bu; under to ud; quiet to qu; pinned to pn; untimed to ut)

    un : ∀ {q y w l e e′} → enter d p q e → enter d p y e′ → Plain l → W⁼ (H ∪ʰ t) (q ⊕ [ l ]) w → w ⊑ y → ⊥
    un {q} {w = w} {l} x x′ pl v (zs , refl) with lead (inW (wo x′)) (zs , refl)
    ... | l-root le = ⊑-≼ le (world-after wp (real-init w zs (re x′)))
      where wp = nest-in (widen t (step (inW (wo x)) pl)) v
    ... | l-in u    = ud x x′ pl (unwiden⁼ dj (real-snoc q pl (re x)) (inW (step (inW (wo x)) pl)) (real-init w zs (re x′)) v (inW u)) (zs , refl)
    ... | l-hot hh le = dj (inj₂ hh) (nest-in (widen t (step (inW (wo x)) pl)) v) (⊑-inside le)
