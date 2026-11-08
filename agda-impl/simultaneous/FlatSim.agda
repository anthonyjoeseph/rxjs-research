{-# OPTIONS --guardedness #-}

-- WHAT FLATMAP'S SCAN COUNTS, AGAINST WHAT IT SENDS.  The scan keeps
-- routes of one instant (`at`) in four counters: through the outer,
-- through the lanes, held for a queued lane or its own completion, and
-- parked on the connects in scope.  Every stop it sends takes one of
-- them, every begin adds one, and its over ends them all: so while the
-- instant is live the routes its output counts are at least the
-- counters', of that instant, and past the over none (`Inv`).  A stop it
-- sends always finds a route.
module simultaneous.FlatSim where

open import Data.Bool using (true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using ([])
import Data.List as L
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (does)
open import simultaneous.Routed using (Routing; r-begin; r-over; r-subscribed; r-completed)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊓_; z≤n; s≤s; _<ᵇ_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; +-suc; n≤1+n; ∸-monoˡ-≤; 0∸n≡0; ⊓-zeroʳ; +-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; flat; outerB; laneB; closeB; isZero; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count; Out; Input; react; onMark; begun; entered; anew; bump;
  share; stopped; overed; cut; unpark; arrive; ended; burstOver; left; stops; anyHolds; setAt)

------------------------------------------------------------------------
-- The invariant

-- The routes the counters hold.
tot : Flat Pos → ℕ
tot s = Flat.outer s + Flat.lanes s + Flat.held s + Flat.parked s

-- The routes past what an output sent.
after : ∀ {B} → Routes → Out B → Routes
after c o = L.foldl count c (proj₂ o)

data Inv : Routes → Flat Pos → Set where
  live : ∀ {k s} → Flat.spent s ≡ false → tot s ≤ k → Inv (Flat.at s , k) s
  dead : ∀ {s} → Flat.spent s ≡ true → tot s ≡ 0 → Inv (Flat.at s , 0) s

-- The scan starts with nothing counted.
inv₀ : Inv (root , 0) (flat root 0 0 false false false false 0 0 0 0 0 [])
inv₀ = live refl z≤n

------------------------------------------------------------------------
-- Arithmetic

private
  ≤-∸ : ∀ a b K → a + b ≤ K → b ≤ K ∸ a
  ≤-∸ zero    b K       le      = le
  ≤-∸ (suc a) b (suc K) (s≤s le) = ≤-∸ a b K le

  ∸-∸ : ∀ k j → k ∸ suc j ≡ (k ∸ 1) ∸ j
  ∸-∸ zero    j = sym (0∸n≡0 j)
  ∸-∸ (suc k) j = refl

  zero₄ : ∀ a b c d → a + b + c + d ≡ 0 → (a ≡ 0 × b ≡ 0) × (c ≡ 0 × d ≡ 0)
  zero₄ zero zero zero zero refl = (refl , refl) , (refl , refl)

  -- What a lane hands on and what stays with the lanes make up the lanes.
  hand : ∀ l a → (l ∸ a) + (a ⊓ l) ≡ l
  hand l       zero    = +-identityʳ l
  hand zero    (suc a) = refl
  hand (suc l) (suc a) = trans (+-suc (l ∸ a) (a ⊓ l)) (cong suc (hand l a))

  -- The counters, one of them moved.
  park : ∀ a b c d k → a + b + c + (d + k) ≡ k + (a + b + c + d)
  park = solve-∀

  holdₖ : ∀ a b c d k → a + b + (c + k) + d ≡ k + (a + b + c + d)
  holdₖ = solve-∀

  hold₀ : ∀ a b c d → c + (a + b + 0 + d) ≡ a + b + c + d
  hold₀ = solve-∀

  cut₀ : ∀ k a b c d → k + c + (a + b + 0 + d) ≡ k + (a + b + c + d)
  cut₀ = solve-∀

  outer₀ : ∀ a b c d → a + (0 + b + c + d) ≡ a + b + c + d
  outer₀ = solve-∀

  lanes₀ : ∀ a b c d → b + (a + 0 + c + d) ≡ a + b + c + d
  lanes₀ = solve-∀

stops-after : ∀ {B} m k j n → L.foldl count (m , k) (stops {B} j n) ≡ (m , k ∸ j)
stops-after m k zero    n = refl
stops-after m k (suc j) n = trans (stops-after m (k ∸ 1) j n) (cong (m ,_) (sym (∸-∸ k j)))

------------------------------------------------------------------------
-- Routes cut

-- `k` routes, beside what the counters hold, within the routes counted;
-- past the over, nothing.
data Fits (k : ℕ) (s : Flat Pos) : ℕ → Set where
  fits-live : ∀ {K} → Flat.spent s ≡ false → k + tot s ≤ K → Fits k s K
  fits-dead : Flat.spent s ≡ true → tot s ≡ 0 → Fits k s 0

cut-inv : ∀ {B} k n s {K} → Fits k s K → Inv (after (Flat.at s , K) (cut {B} k n s)) (proj₁ (cut {B} k n s))
cut-inv k n s (fits-dead sp z) rewrite sp = dead sp z
cut-inv k n s {K} (fits-live sp le) rewrite sp with anyHolds (Flat.at s) (Flat.live s)
... | true  = live sp (subst (_≤ K) (sym (park (Flat.outer s) (Flat.lanes s) (Flat.held s) (Flat.parked s) k)) le)
... | false = subst (λ c → Inv c s) (sym (stops-after (Flat.at s) K k n)) (live sp (≤-∸ k (tot s) K le))

-- A stop on a live instant's route keeps what the rest hold within.
pred-≤ : ∀ {a b} → a ≤ b → a ∸ 1 ≤ b ∸ 1
pred-≤ {a} {b} le = ∸-monoˡ-≤ 1 le

------------------------------------------------------------------------
-- One step

-- A route added through a branch.
bump-suc : ∀ b s {k} → Flat.spent s ≡ false → tot s ≤ k → Inv (Flat.at s , suc k) (bump b suc s)
bump-suc outerB s sp le = live sp (s≤s le)
bump-suc laneB  s {k} sp le = live sp (subst (_≤ suc k) (sym (lane+ (Flat.outer s) (Flat.lanes s) (Flat.held s) (Flat.parked s))) (s≤s le))
  where
    lane+ : ∀ a b c d → a + suc b + c + d ≡ suc (a + b + c + d)
    lane+ = solve-∀
bump-suc closeB s sp le = live sp (≤-trans le (n≤1+n _))

-- A route of a new instant, the first.
bump-new : ∀ b n s → Inv (n , 1) (bump b suc (anew n s))
bump-new outerB n s = live refl ≤-refl
bump-new laneB  n s = live refl ≤-refl
bump-new closeB n s = live refl z≤n

begun-inv : ∀ {B} b n {c} s → Inv c s → Inv (after c (begun {B} b n s)) (proj₁ (begun {B} b n s))
begun-inv b n s (live sp le) with n ≟ᵖ Flat.at s
... | no ne with n ≟ᵖ Flat.at s
...   | yes e = ⊥-elim (ne e)
...   | no _ with n ≟ᵖ Flat.at s
...     | yes e = ⊥-elim (ne e)
...     | no _ = bump-new b n s
begun-inv b n s (live sp le) | yes refl rewrite sp with Flat.at s ≟ᵖ Flat.at s
... | no ne = ⊥-elim (ne refl)
... | yes _ with Flat.at s ≟ᵖ Flat.at s
...   | no ne = ⊥-elim (ne refl)
...   | yes _ = bump-suc b s sp le
begun-inv b n s (dead sp z) with n ≟ᵖ Flat.at s
... | no ne with n ≟ᵖ Flat.at s
...   | yes e = ⊥-elim (ne e)
...   | no _ = bump-new b n s
begun-inv b n s (dead sp z) | yes refl rewrite sp = dead sp z

-- A step that moves no route and no instant.
keep : ∀ {c s s′} → Flat.at s′ ≡ Flat.at s → Flat.spent s′ ≡ Flat.spent s → tot s′ ≡ tot s → Inv c s → Inv c s′
keep {s′ = s′} ea es et (live {k} sp le) =
  subst (λ a → Inv (a , k) s′) ea (live (trans es sp) (subst (_≤ k) (sym et) le))
keep {s′ = s′} ea es et (dead sp z) =
  subst (λ a → Inv (a , 0) s′) ea (dead (trans es sp) (trans et z))

private
  outer-1 : ∀ s {j k} → Flat.outer s ≡ suc j → tot s ≤ k → (Flat.outer s ∸ 1) + Flat.lanes s + Flat.held s + Flat.parked s ≤ k ∸ 1
  outer-1 s eq le rewrite eq = pred-≤ le

  lanes-1 : ∀ s {j k} → Flat.lanes s ≡ suc j → tot s ≤ k → Flat.outer s + (Flat.lanes s ∸ 1) + Flat.held s + Flat.parked s ≤ k ∸ 1
  lanes-1 s {j} {k} eq le rewrite eq =
    pred-≤ (subst (_≤ k) (lane+ (Flat.outer s) j (Flat.held s) (Flat.parked s)) le)
    where
      lane+ : ∀ a b c d → a + suc b + c + d ≡ suc (a + b + c + d)
      lane+ = solve-∀

private
  unO : ∀ s {x k} → Flat.outer s ≡ x → x + Flat.lanes s + Flat.held s + Flat.parked s ≤ k → tot s ≤ k
  unO s refl le = le

  unL : ∀ s {x k} → Flat.lanes s ≡ x → Flat.outer s + x + Flat.held s + Flat.parked s ≤ k → tot s ≤ k
  unL s refl le = le

stopped-inv : ∀ {B} b n s {c} → Inv c s → Inv (after c (stopped {B} b n s (if Flat.spent s then 0 else share b s)))
                                         (proj₁ (stopped {B} b n s (if Flat.spent s then 0 else share b s)))
stopped-inv b n s (dead sp z) rewrite sp = dead sp z
stopped-inv outerB n s (live sp le) rewrite sp with Flat.outer s in eq
... | zero  = live sp (unO s eq le)
... | suc j = live sp (outer-1 s eq (unO s eq le))
stopped-inv laneB n s (live sp le) rewrite sp with Flat.lanes s in eq
... | zero  = live sp (unL s eq le)
... | suc j = live sp (lanes-1 s eq (unL s eq le))
stopped-inv closeB n s (live sp le) rewrite sp = live sp le

overed-inv : ∀ {B} n s {c} → Inv c s → Inv (after c (overed {B} n s)) (proj₁ (overed {B} n s))
overed-inv n s (live sp le) rewrite sp = dead refl refl
overed-inv n s (dead sp z) rewrite sp = dead sp z

arrive-inv : ∀ {B} op n s {c} → Inv c s → Inv (after c (arrive {B} op n s)) (proj₁ (arrive {B} op n s))
arrive-inv (mergeᶠ (just j)) n s i with Flat.active s <ᵇ j
... | true  = i
... | false = keep refl refl refl i
arrive-inv (mergeᶠ nothing) n s i = i
arrive-inv switchᶠ n s (live {k} sp le) =
  cut-inv (Flat.lanes s) n _ (fits-live sp (subst (_≤ k) (sym (lanes₀ (Flat.outer s) (Flat.lanes s) (Flat.held s) (Flat.parked s))) le))
arrive-inv switchᶠ n s (dead sp z) with zero₄ (Flat.outer s) (Flat.lanes s) (Flat.held s) (Flat.parked s) z
... | (o , l) , (h , p) rewrite o | l | h | p = cut-inv 0 n _ (fits-dead sp refl)
arrive-inv exhaustᶠ n s i = i

private
  zero-r : ∀ a b → a + b ≡ 0 → b ≡ 0
  zero-r zero b e = e

-- Routes cut from a state `s′` that agrees with `s` on all but how its
-- routes are split.
cutG : ∀ {B c s} s′ k n → Flat.at s′ ≡ Flat.at s → Flat.spent s′ ≡ Flat.spent s → k + tot s′ ≡ tot s → Inv c s
     → Inv (after c (cut {B} k n s′)) (proj₁ (cut {B} k n s′))
cutG s′ k n ea es et (live {K} sp le) rewrite sym ea =
  cut-inv k n s′ (fits-live (trans es sp) (subst (_≤ K) (sym et) le))
cutG s′ k n ea es et (dead sp z) rewrite sym ea =
  cut-inv k n s′ (fits-dead (trans es sp) (zero-r k _ (trans et z)))

-- The lane's routes, moved to `held`, or cut.
holdL : ∀ {c s} s′ k → Flat.at s′ ≡ Flat.at s → Flat.spent s′ ≡ Flat.spent s → k + tot s′ ≡ tot s
      → Inv c s → Inv c (record s′ { held = Flat.held s′ + k })
holdL s′ k ea es et = keep ea es (trans (holdₖ (Flat.outer s′) (Flat.lanes s′) (Flat.held s′) (Flat.parked s′) k) et)

cutL : ∀ {B c s} s′ k n → Flat.at s′ ≡ Flat.at s → Flat.spent s′ ≡ Flat.spent s → k + tot s′ ≡ tot s → Inv c s
     → Inv (after c (cut {B} (k + Flat.held s′) n (record s′ { held = 0 }))) (proj₁ (cut {B} (k + Flat.held s′) n (record s′ { held = 0 })))
cutL s′ k n ea es et = cutG _ (k + Flat.held s′) n ea es (trans (cut₀ k (Flat.outer s′) (Flat.lanes s′) (Flat.held s′) (Flat.parked s′)) et)

private
  handed′ : ∀ o l a h p → (a ⊓ l) + (o + (l ∸ a) + h + p) ≡ o + l + h + p
  handed′ o l a h p = trans (shuffle o (l ∸ a) (a ⊓ l) h p) (cong (λ x → o + x + h + p) (hand l a))
    where
      shuffle : ∀ o x y h p → y + (o + x + h + p) ≡ o + (x + y) + h + p
      shuffle = solve-∀

  -- Past the over the lanes hold nothing to hand on.
  spent-k : ∀ {c} s → Inv c s → Flat.spent s ≡ true → Flat.acc s ⊓ Flat.lanes s ≡ 0
  spent-k s (live sp _) e with () ← trans (sym e) sp
  spent-k s (dead sp z) e rewrite proj₂ (proj₁ (zero₄ (Flat.outer s) (Flat.lanes s) (Flat.held s) (Flat.parked s) z)) = ⊓-zeroʳ (Flat.acc s)

-- A lane ended holding `k`, from a state that split them off.
ended-hand : ∀ {B c s} s₁ k n → Flat.at s₁ ≡ Flat.at s → Flat.spent s₁ ≡ Flat.spent s → k + tot s₁ ≡ tot s
           → (Flat.spent s ≡ true → k ≡ 0) → Inv c s → Inv (after c (ended {B} k n s₁)) (proj₁ (ended {B} k n s₁))
ended-hand s₁ k n ea es et kz i with Flat.queue s₁
... | suc _ = holdL s₁ k ea es et i
... | zero with Flat.finished s₁ | Flat.active s₁
...   | true  | zero  = holdL s₁ k ea es et i
...   | true  | suc _ = cutL s₁ k n ea es et i
...   | false | _     = cutL s₁ k n ea es et i

laneDone-inv : ∀ {B} op b n s {c} → Inv c s → Inv (after c (onMark {B} op b s laneDone n)) (proj₁ (onMark {B} op b s laneDone n))
laneDone-inv op b n s i =
  ended-hand (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0
                       ; popping = not (isZero (Flat.queue s)) ; dead = true }) _ n refl refl (handed′ (Flat.outer s) (Flat.lanes s) (Flat.acc s) (Flat.held s) (Flat.parked s)) (spent-k s i) i

burstEnd-inv : ∀ {B} op b n s {c} → Inv c s → Inv (after c (onMark {B} op b s burstEnd n)) (proj₁ (onMark {B} op b s burstEnd n))
burstEnd-inv op b n s i with isZero (Flat.held s) ∨ Flat.dead s
... | true  = i
... | false = cutG _ (Flat.held s) n refl refl (hold₀ (Flat.outer s) (Flat.lanes s) (Flat.held s) (Flat.parked s)) i

left-hand : ∀ {B c s} s₁ n → Flat.at s₁ ≡ Flat.at s → Flat.spent s₁ ≡ Flat.spent s → tot s₁ ≡ tot s → Inv c s
          → Inv (after c (left {B} n s₁)) (proj₁ (left {B} n s₁))
left-hand s₁ n ea es et i with isZero (Flat.active s₁) ∧ isZero (Flat.queue s₁)
... | true  = keep ea es et i
... | false = cutG _ (Flat.outer s₁) n ea es (trans (outer₀ (Flat.outer s₁) (Flat.lanes s₁) (Flat.held s₁) (Flat.parked s₁)) et) i

private
  unpark₀ : ∀ a b c d → d + (a + b + c + 0) ≡ a + b + c + d
  unpark₀ = solve-∀

  zero₃ : ∀ a b c d → a + b + c + d ≡ 0 → a + b + c + 0 ≡ 0
  zero₃ zero zero zero zero refl = refl

  unparked : ∀ {B c s} s₁ n → Flat.at s₁ ≡ Flat.at s → Flat.spent s₁ ≡ Flat.spent s → tot s₁ ≡ tot s → Inv c s
           → Inv (L.foldl count c (stops {B} (Flat.parked s₁) n)) (record s₁ { parked = 0 })
  unparked s₁ n ea es et (live {K} sp le) rewrite sym ea =
    subst (λ c → Inv c _) (sym (stops-after (Flat.at s₁) K (Flat.parked s₁) n))
      (live (trans es sp) (≤-∸ (Flat.parked s₁) _ K
        (subst (_≤ K) (sym (trans (unpark₀ (Flat.outer s₁) (Flat.lanes s₁) (Flat.held s₁) (Flat.parked s₁)) et)) le)))
  unparked s₁ n ea es et (dead sp z) rewrite sym ea =
    subst (λ c → Inv c _) (sym (trans (stops-after (Flat.at s₁) 0 (Flat.parked s₁) n) (cong (Flat.at s₁ ,_) (0∸n≡0 (Flat.parked s₁)))))
      (dead (trans es sp) (zero₃ (Flat.outer s₁) (Flat.lanes s₁) (Flat.held s₁) (Flat.parked s₁) (trans et z)))

unpark-hand : ∀ {B c s} s₁ n → Flat.at s₁ ≡ Flat.at s → Flat.spent s₁ ≡ Flat.spent s → tot s₁ ≡ tot s → Inv c s
            → Inv (after c (unpark {B} n s₁)) (proj₁ (unpark {B} n s₁))
unpark-hand s₁ n ea es et i with anyHolds (Flat.at s₁) (Flat.live s₁)
... | true  = keep ea es et i
... | false = unparked s₁ n ea es et i

onMark-inv : ∀ {B} op b m n s {c} → Inv c s → Inv (after c (onMark {B} op b s m n)) (proj₁ (onMark {B} op b s m n))
onMark-inv op b begin      n s i = begun-inv b n s i
onMark-inv op b stop       n s i = stopped-inv b n s i
onMark-inv op b over       n s i = overed-inv n s i
onMark-inv op b carry      n s i = keep refl refl refl i
onMark-inv op b outerOpen  n s i = arrive-inv op n s i
onMark-inv op b outerClose n s i = i
onMark-inv op b laneStart  n s i = keep refl refl refl i
onMark-inv op b laneDone   n s i = laneDone-inv op b n s i
onMark-inv op b burstEnd   n s i = burstEnd-inv op b n s i
onMark-inv op b outerDone  n s i = left-hand (record s { finished = true }) n refl refl refl i
onMark-inv op b subscribed n s (live sp le) = live sp le
onMark-inv op b subscribed n s (dead sp z)  = dead sp z
onMark-inv op b completed  n s (live sp le) = live sp le
onMark-inv op b completed  n s (dead sp z)  = dead sp z

-- THE SCAN'S STEP KEEPS THE INVARIANT.
react-inv : ∀ {B} op (o : Out B) x {c} → Inv c (proj₁ o) → Inv (after c (react op o x)) (proj₁ (react op o x))
react-inv op o (just (inj₁ (b , instEmit (value v) n))) (live sp le) = live sp le
react-inv op o (just (inj₁ (b , instEmit (value v) n))) (dead sp z)  = dead sp z
react-inv op o (just (inj₁ (b , instEmit (mark m) n)))  i = onMark-inv op b m n (proj₁ o) i
react-inv op o (just (inj₂ (j , r)))                    i = unpark-hand (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }) root refl refl refl i
react-inv op o nothing                                  i = i

------------------------------------------------------------------------
-- What the scan sends

-- WHAT THE SCAN SENDS is a stop, or what it read: a value, or a mark read
-- above every flatMap.
data Sent {B} (x : Maybe (Input B)) : IE B → Set where
  passed  : ∀ {b v n} → x ≡ just (inj₁ (b , instEmit (value v) n)) → Sent x (instEmit (value v) n)
  routed  : ∀ {b m n} → Routing m → x ≡ just (inj₁ (b , instEmit (mark m) n)) → Sent x (instEmit (mark m) n)
  minted  : ∀ {n} → Sent x (instEmit (mark stop) n)

private
  none : ∀ {A P : Set} {v : A} → v ∈ [] → P
  none ()

  stops-sent : ∀ {B} {x : Maybe (Input B)} k n {v} → v ∈ stops {B} k n → Sent x v
  stops-sent (suc k) n (here refl) = minted
  stops-sent (suc k) n (there i)   = stops-sent k n i

  cut-sent : ∀ {B} {x : Maybe (Input B)} k n s {v} → v ∈ proj₂ (cut {B} k n s) → Sent x v
  cut-sent k n s i with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = none i
  ... | false | true  = none i
  ... | false | false = stops-sent k n i

  unpark-sent : ∀ {B} {x : Maybe (Input B)} n s {v} → v ∈ proj₂ (unpark {B} n s) → Sent x v
  unpark-sent n s i with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = none i
  ... | false = stops-sent (Flat.parked s) n i

  arrive-sent : ∀ {B} {x : Maybe (Input B)} op n s {v} → v ∈ proj₂ (arrive {B} op n s) → Sent x v
  arrive-sent (mergeᶠ (just k)) n s i with Flat.active s <ᵇ k
  ... | true  = none i
  ... | false = none i
  arrive-sent (mergeᶠ nothing) n s i = none i
  arrive-sent switchᶠ n s i = cut-sent (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }) i
  arrive-sent exhaustᶠ n s i = none i

  ended-sent : ∀ {B} {x : Maybe (Input B)} k n s {v} → v ∈ proj₂ (ended {B} k n s) → Sent x v
  ended-sent k n s i with Flat.queue s
  ... | suc _ = none i
  ... | zero with Flat.finished s | Flat.active s
  ...   | true  | zero  = none i
  ...   | true  | suc _ = cut-sent (k + Flat.held s) n (record s { held = 0 }) i
  ...   | false | _     = cut-sent (k + Flat.held s) n (record s { held = 0 }) i

  burst-sent : ∀ {B} {x : Maybe (Input B)} h n s {v} → v ∈ proj₂ (burstOver {B} h n s) → Sent x v
  burst-sent true  n s i = none i
  burst-sent false n s i = cut-sent (Flat.held s) n (record s { held = 0 }) i

  left-sent : ∀ {B} {x : Maybe (Input B)} n s {v} → v ∈ proj₂ (left {B} n s) → Sent x v
  left-sent n s i with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = none i
  ... | false = cut-sent (Flat.outer s) n (record s { outer = 0 }) i

  begun-sent : ∀ {B b} n s {v} → v ∈ proj₂ (begun {B} b n s) → Sent (just (inj₁ (b , instEmit (mark begin) n))) v
  begun-sent {b = b} n s i with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = none i
  ... | false with i
  ...   | here refl = routed r-begin refl
  ...   | there j   = none j

  stopped-sent : ∀ {B} {x : Maybe (Input B)} b n s k {v} → v ∈ proj₂ (stopped {B} b n s k) → Sent x v
  stopped-sent b n s zero    i         = none i
  stopped-sent b n s (suc k) (here refl) = minted
  stopped-sent b n s (suc k) (there i)   = none i

  overed-sent : ∀ {B b} n s {v} → v ∈ proj₂ (overed {B} n s) → Sent (just (inj₁ (b , instEmit (mark over) n))) v
  overed-sent n s i with Flat.spent s
  ... | true  = none i
  ... | false with i
  ...   | here refl = routed r-over refl
  ...   | there j   = none j

  onMark-sent : ∀ {B} op b m n s {v} → v ∈ proj₂ (onMark {B} op b s m n) → Sent (just (inj₁ (b , instEmit (mark m) n))) v
  onMark-sent op b begin      n s i = begun-sent n s i
  onMark-sent op b stop       n s i = stopped-sent b n s (if Flat.spent s then 0 else share b s) i
  onMark-sent op b over       n s i = overed-sent n s i
  onMark-sent op b carry      n s i = none i
  onMark-sent op b outerOpen  n s i = arrive-sent op n s i
  onMark-sent op b outerClose n s i = none i
  onMark-sent op b laneStart  n s i = none i
  onMark-sent op b laneDone   n s i =
    ended-sent (Flat.acc s ⊓ Flat.lanes s) n
      (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0
                ; popping = not (isZero (Flat.queue s)) ; dead = true }) i
  onMark-sent op b burstEnd   n s i = burst-sent (isZero (Flat.held s) ∨ Flat.dead s) n s i
  onMark-sent op b outerDone  n s i = left-sent n (record s { finished = true }) i
  onMark-sent op b subscribed n s (here refl) = routed r-subscribed refl
  onMark-sent op b subscribed n s (there i)   = none i
  onMark-sent op b completed  n s (here refl) = routed r-completed refl
  onMark-sent op b completed  n s (there i)   = none i

react-sent : ∀ {B} op (o : Out B) x {v} → v ∈ proj₂ (react op o x) → Sent x v
react-sent op o (just (inj₁ (b , instEmit (value v) n))) (here refl) = passed refl
react-sent op o (just (inj₁ (b , instEmit (value v) n))) (there i)   = none i
react-sent op o (just (inj₁ (b , instEmit (mark m) n)))  i = onMark-sent op b m n (proj₁ o) i
react-sent op o (just (inj₂ (j , r)))                    i = unpark-sent root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }) i
react-sent op o nothing                                  i = none i
