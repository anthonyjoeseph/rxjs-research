{-# OPTIONS --guardedness #-}

-- THE OPERATORS READ NO FURTHER THAN THEY SHOW: each one's first k steps,
-- and what it leaves running at each, are fixed by its inputs' first k,
-- at every subscription.  Every output step spends one step of one input
-- or tail, and choosing it looks at most one step ahead in each, so a
-- budget of m steps left is enough for every input still being read.
module denotation.NonExpansive where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import denotation.MonotonicList using (MonotonicList; Events; Events∞; Tail; Tail∞; idle; out; skip; end; hush; Agree; Agreeᵀ;
  stopᵀ; pin⁼; idle⁼; agreeᵀ-refl; agreeᵀ-pred; agree-refl; agree-pred; stop; out⁼; skip⁼;
  end⁼; hush⁼; _≈[_]_; agrees; agree; agreeᵀ; ≈ₖ-pred; enter; mapᴰ; scanᴰ; takeWhileᴰ; mapᴱ;
  scanᴱ; takeWhileᴱ; taking; hot; rejoin; _∪_; first; sooner; burstOn; runOn; inside; tailᴱ;
  onward∞; beside; side; ahead; body; before; connectᴰ; ix; _<ᵖ_; FlatOp; mergeᶠ; switchᶠ;
  exhaustᶠ; head; Earliest; none; found; earliest; admit; cuts; whole; clear; headᴼ; clears;
  ahead-of; go; left; parts; viaOuter; race; outer; lane; flatMapᴰ)
open Events∞
open Tail∞

------------------------------------------------------------------------
-- States agreeing for m steps: next events and tails alike

record Agreeˢ {A : Set} (m : ℕ) (l l′ : Events∞ A) : Set where
  constructor _,ˢ_
  field
    cutˢ : Agreeᵀ m (cut l) (cut l′)
    nowˢ : Agree m (force l) (force l′)
open Agreeˢ

agreeˢ-pred : ∀ {A m} {l l′ : Events∞ A} → Agreeˢ (suc m) l l′ → Agreeˢ m l l′
agreeˢ-pred (t ,ˢ a) = agreeᵀ-pred t ,ˢ agree-pred a

entered : ∀ {A k} {x y : MonotonicList A} → x ≈[ k ] y → ∀ p → Agreeˢ k (enter x p) (enter y p)
entered xy p = agreeᵀ xy p ,ˢ agree xy p

------------------------------------------------------------------------
-- Tails

private
  sooner-agree : ∀ {m k u u′} → Agreeᵀ (suc m) u u′ → sooner k u ≡ sooner k u′
  sooner-agree (pin⁼ _) = refl
  sooner-agree idle⁼    = refl

-- Tails alike merge alike.
mutual
  ∪-ne : ∀ {m t t′ u u′} → Agreeᵀ m t t′ → Agreeᵀ m u u′ → Agreeᵀ m (t ∪ u) (t′ ∪ u′)
  ∪-ne {zero}  _ _ = stopᵀ
  ∪-ne {suc m} idle⁼ b = b
  ∪-ne {suc m} {u = u} {u′} (pin⁼ {p = k} a) b rewrite sooner-agree {k = k} b = first-ne (sooner k u′) a b

  first-ne : ∀ {m k r r′ u u′} f → Agreeᵀ m (later r) (later r′) → Agreeᵀ (suc m) u u′
           → Agreeᵀ (suc m) (first k r u f) (first k r′ u′ f)
  first-ne true  a b        = pin⁼ (∪-ne a (agreeᵀ-pred b))
  first-ne false a idle⁼    = pin⁼ a
  first-ne false a (pin⁼ b) = pin⁼ (∪-ne (agreeᵀ-pred (pin⁼ a)) b)

-- A tail run alike, as events.
tailᴱ-ne : ∀ {A m} {t t′ : Tail} → Agreeᵀ m t t′ → Agree {A} m (tailᴱ t) (tailᴱ t′)
tailᴱ-ne stopᵀ    = stop
tailᴱ-ne (pin⁼ a) = skip⁼ a (tailᴱ-ne a)
tailᴱ-ne idle⁼    = hush⁼

------------------------------------------------------------------------
-- ONE STEP IN, ONE STEP OUT

mapᴱ-ne : ∀ {A B m} (f : A → B) {x y : Events A} → Agree m x y → Agree m (mapᴱ f x) (mapᴱ f y)
mapᴱ-ne f stop        = stop
mapᴱ-ne f (out⁼ t a)  = out⁼ t (mapᴱ-ne f a)
mapᴱ-ne f (skip⁼ t a) = skip⁼ t (mapᴱ-ne f a)
mapᴱ-ne f end⁼        = end⁼
mapᴱ-ne f hush⁼       = hush⁼

scanᴱ-ne : ∀ {A B m} (f : B → A → B) z {x y : Events A} → Agree m x y → Agree m (scanᴱ f z x) (scanᴱ f z y)
scanᴱ-ne f z stop                = stop
scanᴱ-ne f z (out⁼ {a = a} t r)  = out⁼ t (scanᴱ-ne f (f z a) r)
scanᴱ-ne f z (skip⁼ t r)         = skip⁼ t (scanᴱ-ne f z r)
scanᴱ-ne f z end⁼                = end⁼
scanᴱ-ne f z hush⁼               = hush⁼

mutual
  takeWhileᴱ-ne : ∀ {A m} i (p : A → Bool) {x y : Events A} → Agree m x y → Agree m (takeWhileᴱ i p x) (takeWhileᴱ i p y)
  takeWhileᴱ-ne i p stop                 = stop
  takeWhileᴱ-ne i p (out⁼ {a = a} t r)   = taking-ne i p (p a) t r
  takeWhileᴱ-ne i p (skip⁼ t r)          = skip⁼ t (takeWhileᴱ-ne i p r)
  takeWhileᴱ-ne i p end⁼                 = end⁼
  takeWhileᴱ-ne i p hush⁼                = hush⁼

  taking-ne : ∀ {A m k a} i (p : A → Bool) b {l r : Events∞ A} → Agreeᵀ m (cut l) (cut r) → Agree m (force l) (force r)
            → Agree (suc m) (taking i p k a b l) (taking i p k a b r)
  taking-ne i     p true  t a = out⁼ t (takeWhileᴱ-ne i p a)
  taking-ne {m = m} true  p false t a = out⁼ t (agree-refl m _)
  taking-ne false p false t a = end⁼

mapᴰ-ne : ∀ {A B k} (f : A → B) {x y : MonotonicList A} → x ≈[ k ] y → mapᴰ f x ≈[ k ] mapᴰ f y
mapᴰ-ne f xy = agrees (agreeᵀ xy) λ p → mapᴱ-ne f (agree xy p)

scanᴰ-ne : ∀ {A B k} (f : B → A → B) z {x y : MonotonicList A} → x ≈[ k ] y → scanᴰ f z x ≈[ k ] scanᴰ f z y
scanᴰ-ne f z xy = agrees (agreeᵀ xy) λ p → scanᴱ-ne f z (agree xy p)

takeWhileᴰ-ne : ∀ {A k} i (p : A → Bool) {x y : MonotonicList A} → x ≈[ k ] y → takeWhileᴰ i p x ≈[ k ] takeWhileᴰ i p y
takeWhileᴰ-ne i p xy = agrees (agreeᵀ xy) λ q → takeWhileᴱ-ne i p (agree xy q)

------------------------------------------------------------------------
-- CONNECT: the hot handle shows a joiner's skipped past as one skip per
-- source step, all at one position, and the body and the source
-- interleave, each read one step ahead.  What is left running is the
-- source's subscribe burst, read as far as the source is.

rejoin-ne : ∀ {A m} p {x y : Events A} → Agree m x y → Agree m (rejoin p x) (rejoin p y)
rejoin-ne p stop = stop
rejoin-ne p (out⁼ {p = q} _ a) with p <ᵖ q
... | true  = out⁼ (agreeᵀ-refl _ idle) (rejoin-ne p a)
... | false = skip⁼ (agreeᵀ-refl _ idle) (rejoin-ne p a)
rejoin-ne p (skip⁼ {p = q} _ a) with p <ᵖ q
... | true  = skip⁼ (agreeᵀ-refl _ idle) (rejoin-ne p a)
... | false = skip⁼ (agreeᵀ-refl _ idle) (rejoin-ne p a)
rejoin-ne {m = suc m} p (end⁼ {p = c}) = agree-refl (suc m) _
rejoin-ne p hush⁼ = hush⁼

hot-ne : ∀ {A k} {e e′ : Events A} → Agree k e e′ → hot e ≈[ k ] hot e′
hot-ne a = agrees (λ p → agreeᵀ-refl _ idle) λ p → rejoin-ne p a

-- The burst run on, read as far as the source agrees.
runOn-ne : ∀ {A m} r {e e′ : Events A} {t t′} → Agree m e e′ → Agreeᵀ m t t′ → Agreeᵀ m (runOn r e t) (runOn r e′ t′)
runOn-ne r stop t = stopᵀ
runOn-ne r (out⁼ {p = k} u a) t with inside r k
... | true  = pin⁼ (runOn-ne r a u)
... | false = t
runOn-ne r (skip⁼ {p = k} u a) t with inside r k
... | true  = pin⁼ (runOn-ne r a u)
... | false = t
runOn-ne r end⁼  t = t
runOn-ne r hush⁼ t = t

burstOn-ne : ∀ {A m} r {s s′ : Events∞ A} → Agreeˢ m s s′ → Agreeᵀ m (burstOn r s) (burstOn r s′)
burstOn-ne r (t ,ˢ a) = runOn-ne r a t

onward-ne : ∀ {A m} {σ σ′ : Events∞ A} {e e′} → Agreeˢ (suc m) σ σ′ → Agree (suc m) e e′
          → Agreeˢ m (onward∞ σ e) (onward∞ σ′ e′)
onward-ne s       (out⁼ t a)  = t ,ˢ a
onward-ne s       (skip⁼ t a) = t ,ˢ a
onward-ne (t ,ˢ _) end⁼        = agreeᵀ-pred t ,ˢ tailᴱ-ne (agreeᵀ-pred t)
onward-ne s       hush⁼       = agreeˢ-pred s

before-agree : ∀ {B m} q {x y : Events B} → Agree (suc m) x y → before q x ≡ before q y
before-agree q (out⁼ _ _)  = refl
before-agree q (skip⁼ _ _) = refl
before-agree q end⁼        = refl
before-agree q hush⁼       = refl

mutual
  beside-ne : ∀ {A B m} r {β β′ : Events∞ B} {σ σ′ : Events∞ A} → Agreeˢ m β β′ → Agreeˢ m σ σ′
            → Agree m (beside r β σ) (beside r β′ σ′)
  beside-ne {m = zero}  r _ _ = stop
  beside-ne {m = suc m} r b s = side-ne r b s (nowˢ s)

  side-ne : ∀ {A B m} r {β β′ : Events∞ B} {σ σ′ : Events∞ A} {e e′} → Agreeˢ (suc m) β β′ → Agreeˢ (suc m) σ σ′
          → Agree (suc m) e e′ → Agree (suc m) (side r β σ e) (side r β′ σ′ e′)
  side-ne r b s (out⁼ {p = q} _ _)  = ahead-ne r _ _ (before-agree (q ++ [ ix 0 ]) (nowˢ b)) b s
  side-ne r b s (skip⁼ {p = q} _ _) = ahead-ne r _ _ (before-agree (q ++ [ ix 0 ]) (nowˢ b)) b s
  side-ne r b s (end⁼ {p = c})      = ahead-ne r _ _ (before-agree (c ++ [ ix 0 ]) (nowˢ b)) b s
  side-ne r b s hush⁼               = nowˢ b

  -- The flag is `before` of each side, equal because the bodies agree.
  ahead-ne : ∀ {A B m q} r {β β′ : Events∞ B} {σ σ′ : Events∞ A} f f′ → f ≡ f′ → Agreeˢ (suc m) β β′ → Agreeˢ (suc m) σ σ′
           → Agree (suc m) (ahead r β σ q f) (ahead r β′ σ′ q f′)
  ahead-ne r {σ = σ} {σ′} true _ refl b s =
    skip⁼ (∪-ne (burstOn-ne r {onward∞ σ (force σ)} {onward∞ σ′ (force σ′)} o) (agreeᵀ-pred (cutˢ b))) (beside-ne r (agreeˢ-pred b) o)
    where o = onward-ne {σ = σ} {σ′} s (nowˢ s)
  ahead-ne r false _ refl b s = body-ne r s (nowˢ b)

  body-ne : ∀ {A B m q} r {σ σ′ : Events∞ A} {b b′ : Events B} → Agreeˢ (suc m) σ σ′ → Agree (suc m) b b′
          → Agree (suc m) (body r σ q b) (body r σ′ q b′)
  body-ne {m = zero}  r s (out⁼ _ _)  = out⁼ stopᵀ stop
  body-ne {m = zero}  r s (skip⁼ _ _) = skip⁼ stopᵀ stop
  body-ne {m = suc m} {q = q} r {σ} {σ′} s (out⁼ t a) =
    out⁼ (∪-ne (burstOn-ne r {σ} {σ′} (agreeˢ-pred s)) t) (ahead-ne r _ _ (before-agree q a) (t ,ˢ a) (agreeˢ-pred s))
  body-ne {m = suc m} {q = q} r {σ} {σ′} s (skip⁼ t a) =
    skip⁼ (∪-ne (burstOn-ne r {σ} {σ′} (agreeˢ-pred s)) t) (ahead-ne r _ _ (before-agree q a) (t ,ˢ a) (agreeˢ-pred s))
  body-ne r s end⁼  = end⁼
  body-ne r s hush⁼ = hush⁼

connectᴰ-ne : ∀ {A B k} {x y : MonotonicList A} {f g : MonotonicList A → MonotonicList B}
            → x ≈[ k ] y → (∀ {r r′} → r ≈[ k ] r′ → f r ≈[ k ] g r′) → connectᴰ x f ≈[ k ] connectᴰ y g
connectᴰ-ne {x = x} {y} xy H = agrees
  (λ p → ∪-ne (burstOn-ne (p ++ [ ix 1 ]) {enter x (p ++ [ ix 1 ])} {enter y (p ++ [ ix 1 ])} (entered xy (p ++ [ ix 1 ])))
              (cutˢ (bodies p)))
  (λ p → beside-ne (p ++ [ ix 1 ]) (bodies p) (entered xy (p ++ [ ix 1 ])))
  where bodies = λ p → entered (H (hot-ne (agree xy (p ++ [ ix 1 ])))) (p ++ [ ix 0 ])

------------------------------------------------------------------------
-- FLATMAP

infixr 5 _∷ᴸ_ _∷ᑫ_

-- Lanes and queues agreeing for m steps, pairwise.
data Lanes {B : Set} (m : ℕ) : List (Events∞ B) → List (Events∞ B) → Set where
  []ᴸ  : Lanes m [] []
  _∷ᴸ_ : ∀ {l l′ ls ls′} → Agreeˢ m l l′ → Lanes m ls ls′ → Lanes m (l ∷ ls) (l′ ∷ ls′)

data Queue {B : Set} (m : ℕ) : List (MonotonicList B) → List (MonotonicList B) → Set where
  []ᑫ  : Queue m [] []
  _∷ᑫ_ : ∀ {q q′ qs qs′} → q ≈[ m ] q′ → Queue m qs qs′ → Queue m (q ∷ qs) (q′ ∷ qs′)

-- Outer runs agreeing for m steps, each element alike its counterpart
-- for the steps that remain.
data Agreeᴹ {B : Set} : ℕ → Events (MonotonicList B) → Events (MonotonicList B) → Set where
  stopᴹ : ∀ {x y} → Agreeᴹ zero x y
  outᴹ  : ∀ {k p x x′ l r} → x ≈[ k ] x′ → Agreeᵀ k (cut l) (cut r) → Agreeᴹ k (force l) (force r)
        → Agreeᴹ (suc k) (out p x l) (out p x′ r)
  skipᴹ : ∀ {k p l r} → Agreeᵀ k (cut l) (cut r) → Agreeᴹ k (force l) (force r) → Agreeᴹ (suc k) (skip p l) (skip p r)
  endᴹ  : ∀ {k p} → Agreeᴹ (suc k) (end p) (end p)
  hushᴹ : ∀ {k} → Agreeᴹ (suc k) hush hush

-- The outer: done on both sides, or alike.
data Outerᴿ {B : Set} (m : ℕ) : Maybe (Events∞ (MonotonicList B)) → Maybe (Events∞ (MonotonicList B)) → Set where
  doneᴼ : Outerᴿ m nothing nothing
  liveᴼ : ∀ {e e′} → Agreeᵀ m (cut e) (cut e′) → Agreeᴹ m (force e) (force e′) → Outerᴿ m (just e) (just e′)

data Earliestᴿ {B : Set} (m : ℕ) : Earliest B → Earliest B → Set where
  noneᴿ  : Earliestᴿ m none none
  foundᴿ : ∀ {k bs bs′ l l′ as as′} → Lanes m bs bs′ → Agreeˢ m l l′ → Lanes m as as′
         → Earliestᴿ m (found k bs l as) (found k bs′ l′ as′)

-- Mapped alike, an outer run's elements are alike.
mapᴱ-neᴹ : ∀ {A B m} {f g : A → MonotonicList B} → (∀ a → f a ≈[ m ] g a) → {x y : Events A} → Agree m x y
         → Agreeᴹ m (mapᴱ f x) (mapᴱ g y)
mapᴱ-neᴹ F stop                = stopᴹ
mapᴱ-neᴹ F (out⁼ {a = a} t r)  = outᴹ (≈ₖ-pred (F a)) t (mapᴱ-neᴹ (λ a → ≈ₖ-pred (F a)) r)
mapᴱ-neᴹ F (skip⁼ t r)         = skipᴹ t (mapᴱ-neᴹ (λ a → ≈ₖ-pred (F a)) r)
mapᴱ-neᴹ F end⁼                = endᴹ
mapᴱ-neᴹ F hush⁼               = hushᴹ

-- Every part's tail, alike.
cuts-ne : ∀ {B m} {ls ls′ : List (Events∞ B)} → Lanes m ls ls′ → Agreeᵀ m (cuts ls) (cuts ls′)
cuts-ne []ᴸ           = agreeᵀ-refl _ idle
cuts-ne ((t ,ˢ _) ∷ᴸ l) = ∪-ne t (cuts-ne l)

whole-ne : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ t t′} → Outerᴿ m o o′ → Lanes m ls ls′ → Agreeᵀ m t t′
         → Agreeᵀ m (whole o ls t) (whole o′ ls′ t′)
whole-ne doneᴼ       l t = ∪-ne (agreeᵀ-refl _ idle) (∪-ne (cuts-ne l) t)
whole-ne (liveᴼ u _) l t = ∪-ne u (∪-ne (cuts-ne l) t)

private
  agreeᴹ-pred : ∀ {B m} {x y : Events (MonotonicList B)} → Agreeᴹ (suc m) x y → Agreeᴹ m x y
  agreeᴹ-pred {m = zero}  _            = stopᴹ
  agreeᴹ-pred {m = suc m} (outᴹ x t a) = outᴹ (≈ₖ-pred x) (agreeᵀ-pred t) (agreeᴹ-pred a)
  agreeᴹ-pred {m = suc m} (skipᴹ t a)  = skipᴹ (agreeᵀ-pred t) (agreeᴹ-pred a)
  agreeᴹ-pred {m = suc m} endᴹ         = endᴹ
  agreeᴹ-pred {m = suc m} hushᴹ        = hushᴹ

  outer-pred : ∀ {B m} {o o′ : Maybe (Events∞ (MonotonicList B))} → Outerᴿ (suc m) o o′ → Outerᴿ m o o′
  outer-pred doneᴼ       = doneᴼ
  outer-pred (liveᴼ t a) = liveᴼ (agreeᵀ-pred t) (agreeᴹ-pred a)

  lanes-pred : ∀ {B m} {ls ls′ : List (Events∞ B)} → Lanes (suc m) ls ls′ → Lanes m ls ls′
  lanes-pred []ᴸ      = []ᴸ
  lanes-pred (a ∷ᴸ l) = agreeˢ-pred a ∷ᴸ lanes-pred l

  lanes-++ : ∀ {B m} {as as′ bs bs′ : List (Events∞ B)} → Lanes m as as′ → Lanes m bs bs′ → Lanes m (as ++ bs) (as′ ++ bs′)
  lanes-++ []ᴸ      b = b
  lanes-++ (a ∷ᴸ l) b = a ∷ᴸ lanes-++ l b

  lanes-length : ∀ {B m} {ls ls′ : List (Events∞ B)} → Lanes m ls ls′ → length ls ≡ length ls′
  lanes-length []ᴸ      = refl
  lanes-length (_ ∷ᴸ l) = cong suc (lanes-length l)

  queue-pred : ∀ {B m} {qs qs′ : List (MonotonicList B)} → Queue (suc m) qs qs′ → Queue m qs qs′
  queue-pred []ᑫ      = []ᑫ
  queue-pred (a ∷ᑫ q) = ≈ₖ-pred a ∷ᑫ queue-pred q

  queue-++ : ∀ {B m} {as as′ bs bs′ : List (MonotonicList B)} → Queue m as as′ → Queue m bs bs′ → Queue m (as ++ bs) (as′ ++ bs′)
  queue-++ []ᑫ      b = b
  queue-++ (a ∷ᑫ q) b = a ∷ᑫ queue-++ q b

  -- Agreeing for a step, they agree where they go next.
  head-agree : ∀ {B m} {x y : Events B} → Agree (suc m) x y → head x ≡ head y
  head-agree (out⁼ _ _)  = refl
  head-agree (skip⁼ _ _) = refl
  head-agree end⁼        = refl
  head-agree hush⁼       = refl

  headᴹ : ∀ {B m} {x y : Events (MonotonicList B)} → Agreeᴹ (suc m) x y → head x ≡ head y
  headᴹ (outᴹ _ _ _) = refl
  headᴹ (skipᴹ _ _)  = refl
  headᴹ endᴹ         = refl
  headᴹ hushᴹ        = refl

  -- What the ended left is ahead of the parts alike.
  ahead-of-agree : ∀ {B m k} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′} → Outerᴿ (suc m) o o′ → Lanes (suc m) ls ls′
                 → ahead-of k o ls ≡ ahead-of k o′ ls′
  ahead-of-agree {k = k} r l = cong₂ _∧_ (cong (clear k) (heads r)) (lanes l)
    where
      heads : ∀ {o o′} → Outerᴿ _ o o′ → headᴼ o ≡ headᴼ o′
      heads doneᴼ       = refl
      heads (liveᴼ _ a) = headᴹ a
      lanes : ∀ {ls ls′} → Lanes _ ls ls′ → clears k ls ≡ clears k ls′
      lanes []ᴸ      = refl
      lanes (a ∷ᴸ l) = cong₂ _∧_ (cong (clear k) (head-agree (nowˢ a))) (lanes l)

  -- Agreeing lanes race alike: the winner is read off their heads.
  earliest-agree : ∀ {B m} {ls ls′ : List (Events∞ B)} → Lanes (suc m) ls ls′ → Earliestᴿ (suc m) (earliest ls) (earliest ls′)
  earliest-agree []ᴸ = noneᴿ
  earliest-agree {ls = l ∷ ls} {l′ ∷ ls′} (a ∷ᴸ as)
    with head (force l) | head (force l′) | head-agree (nowˢ a) | earliest ls | earliest ls′ | earliest-agree as
  ... | nothing | _ | refl | none            | _ | noneᴿ          = noneᴿ
  ... | nothing | _ | refl | found _ _ _ _   | _ | foundᴿ b c d   = foundᴿ (a ∷ᴸ b) c d
  ... | just k  | _ | refl | none            | _ | noneᴿ          = foundᴿ []ᴸ a as
  ... | just k  | _ | refl | found k′ _ _ _  | _ | foundᴿ b c d with k <ᵖ k′
  ...   | true  = foundᴿ []ᴸ a as
  ...   | false = foundᴿ (a ∷ᴸ b) c d

  -- Agreeing lanes and queue admit an agreeing lane alike, and drop alike.
  admit-agree : ∀ {B m} op q {x y : MonotonicList B} {ls ls′ qs qs′} → x ≈[ m ] y → Lanes m ls ls′ → Queue m qs qs′
              → Lanes m (proj₁ (admit op q x ls qs)) (proj₁ (admit op q y ls′ qs′))
              × Queue m (proj₁ (proj₂ (admit op q x ls qs))) (proj₁ (proj₂ (admit op q y ls′ qs′)))
              × Agreeᵀ m (proj₂ (proj₂ (admit op q x ls qs))) (proj₂ (proj₂ (admit op q y ls′ qs′)))
  admit-agree (mergeᶠ nothing)  q xy l w = entered xy q ∷ᴸ l , w , agreeᵀ-refl _ idle
  admit-agree (mergeᶠ (just n)) q {ls = ls} {ls′} xy l w rewrite lanes-length l with length ls′ <ᵇ n
  ... | true  = entered xy q ∷ᴸ l , w , agreeᵀ-refl _ idle
  ... | false = l , queue-++ w (xy ∷ᑫ []ᑫ) , agreeᵀ-refl _ idle
  admit-agree switchᶠ           q xy l w = entered xy q ∷ᴸ []ᴸ , w , cuts-ne l
  admit-agree exhaustᶠ          q xy []ᴸ w = entered xy q ∷ᴸ []ᴸ , w , agreeᵀ-refl _ idle
  admit-agree exhaustᶠ          q xy (a ∷ᴸ l) w = a ∷ᴸ l , w , agreeᵀ-refl _ idle

module _ {B : Set} (op : FlatOp) where

  mutual
    go-ne : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ qs qs′ t t′} → Outerᴿ m o o′ → Lanes m ls ls′ → Queue m qs qs′
          → Agreeᵀ m t t′ → Agree m (go op o ls qs t) (go op o′ ls′ qs′ t′)
    go-ne {zero}  _ _ _ _        = stop
    go-ne {suc m} r l w idle⁼    = parts-ne r l w idle⁼
    go-ne {suc m} r l w (pin⁼ u) = left-ne r l w u _ _ (ahead-of-agree r l)

    left-ne : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ qs qs′ k u u′} → Outerᴿ (suc m) o o′ → Lanes (suc m) ls ls′
            → Queue (suc m) qs qs′ → Agreeᵀ m (later u) (later u′) → ∀ f f′ → f ≡ f′
            → Agree (suc m) (left op o ls qs k u f) (left op o′ ls′ qs′ k u′ f′)
    left-ne r l w u true  _ refl =
      skip⁼ (whole-ne (outer-pred r) (lanes-pred l) u) (go-ne (outer-pred r) (lanes-pred l) (queue-pred w) u)
    left-ne r l w u false _ refl = parts-ne r l w (pin⁼ u)

    parts-ne : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ qs qs′ t t′} → Outerᴿ (suc m) o o′ → Lanes (suc m) ls ls′
             → Queue (suc m) qs qs′ → Agreeᵀ (suc m) t t′ → Agree (suc m) (parts op o ls qs t) (parts op o′ ls′ qs′ t′)
    parts-ne {ls = ls} {ls′} r l w t with earliest ls | earliest ls′ | earliest-agree l
    ... | none          | _ | noneᴿ        = viaOuter-ne r l w t
    ... | found k _ _ _ | _ | foundᴿ b c d = race-ne r b c d w t

    viaOuter-ne : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {ls ls′ qs qs′ t t′} → Outerᴿ (suc m) o o′ → Lanes (suc m) ls ls′
                → Queue (suc m) qs qs′ → Agreeᵀ (suc m) t t′ → Agree (suc m) (viaOuter op o ls qs t) (viaOuter op o′ ls′ qs′ t′)
    viaOuter-ne doneᴼ       l w t = hush⁼
    viaOuter-ne (liveᴼ u a) l w t = outer-ne u l w t a

    race-ne : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {k bs bs′ c c′ as as′ qs qs′ t t′} → Outerᴿ (suc m) o o′
            → Lanes (suc m) bs bs′ → Agreeˢ (suc m) c c′ → Lanes (suc m) as as′ → Queue (suc m) qs qs′ → Agreeᵀ (suc m) t t′
            → Agree (suc m) (race op o k bs c as qs t) (race op o′ k bs′ c′ as′ qs′ t′)
    race-ne doneᴼ b c d w t = lane-ne doneᴼ b c d w t (nowˢ c)
    race-ne {k = k} o@(liveᴼ {e} {e′} u a) b c d w t with head (force e) | head (force e′) | headᴹ a
    ... | nothing | _ | refl = lane-ne o b c d w t (nowˢ c)
    ... | just k′ | _ | refl with k′ <ᵖ k
    ...   | true  = outer-ne u (lanes-++ b (c ∷ᴸ d)) w t a
    ...   | false = lane-ne o b c d w t (nowˢ c)

    outer-ne : ∀ {m} {e e′ : Events∞ (MonotonicList B)} {ls ls′ qs qs′ t t′ ev ev′} → Agreeᵀ (suc m) (cut e) (cut e′)
             → Lanes (suc m) ls ls′ → Queue (suc m) qs qs′ → Agreeᵀ (suc m) t t′ → Agreeᴹ (suc m) ev ev′
             → Agree (suc m) (outer op e ls qs t ev) (outer op e′ ls′ qs′ t′ ev′)
    outer-ne {ls = ls} {ls′} {qs} {qs′} u l w t (outᴹ {p = q} {x = x} {x′} {e₁} {e₁′} xx v a)
      with admit op (q ++ [ ix 1 ]) x ls qs | admit op (q ++ [ ix 1 ]) x′ ls′ qs′
         | admit-agree op (q ++ [ ix 1 ]) xx (lanes-pred l) (queue-pred w)
    ... | _ , _ , _ | _ , _ , _ | l′ , w′ , d =
      skip⁼ (whole-ne (liveᴼ {e = e₁} {e₁′} v a) l′ (∪-ne (agreeᵀ-pred t) d)) (go-ne (liveᴼ {e = e₁} {e₁′} v a) l′ w′ (∪-ne (agreeᵀ-pred t) d))
    outer-ne u l w t (skipᴹ {l = e₁} {e₁′} v a) =
      skip⁼ (whole-ne (liveᴼ {e = e₁} {e₁′} v a) (lanes-pred l) (agreeᵀ-pred t))
            (go-ne (liveᴼ {e = e₁} {e₁′} v a) (lanes-pred l) (queue-pred w) (agreeᵀ-pred t))
    outer-ne u []ᴸ       []ᑫ      t endᴹ = end⁼
    outer-ne u []ᴸ       (x ∷ᑫ w) t endᴹ =
      skip⁼ (whole-ne {B} doneᴼ []ᴸ (∪-ne (agreeᵀ-pred t) (agreeᵀ-pred u)))
            (go-ne doneᴼ []ᴸ (queue-pred (x ∷ᑫ w)) (∪-ne (agreeᵀ-pred t) (agreeᵀ-pred u)))
    outer-ne u (y ∷ᴸ l)  w        t endᴹ =
      skip⁼ (whole-ne doneᴼ (lanes-pred (y ∷ᴸ l)) (∪-ne (agreeᵀ-pred t) (agreeᵀ-pred u)))
            (go-ne doneᴼ (lanes-pred (y ∷ᴸ l)) (queue-pred w) (∪-ne (agreeᵀ-pred t) (agreeᵀ-pred u)))
    outer-ne u l w t hushᴹ = hush⁼

    lane-ne : ∀ {m} {o o′ : Maybe (Events∞ (MonotonicList B))} {bs bs′ c c′ as as′ qs qs′ t t′ ev ev′} → Outerᴿ (suc m) o o′
            → Lanes (suc m) bs bs′ → Agreeˢ (suc m) c c′ → Lanes (suc m) as as′ → Queue (suc m) qs qs′ → Agreeᵀ (suc m) t t′
            → Agree (suc m) ev ev′ → Agree (suc m) (lane op o bs c as qs t ev) (lane op o′ bs′ c′ as′ qs′ t′ ev′)
    lane-ne r b c d w t (out⁼ v a) =
      out⁼ (whole-ne (outer-pred r) L (agreeᵀ-pred t)) (go-ne (outer-pred r) L (queue-pred w) (agreeᵀ-pred t))
      where L = lanes-++ (lanes-pred b) ((v ,ˢ a) ∷ᴸ lanes-pred d)
    lane-ne r b c d w t (skip⁼ v a) =
      skip⁼ (whole-ne (outer-pred r) L (agreeᵀ-pred t)) (go-ne (outer-pred r) L (queue-pred w) (agreeᵀ-pred t))
      where L = lanes-++ (lanes-pred b) ((v ,ˢ a) ∷ᴸ lanes-pred d)
    lane-ne r b c d (x ∷ᑫ w) t (end⁼ {p = q}) =
      skip⁼ (whole-ne (outer-pred r) L T) (go-ne (outer-pred r) L (queue-pred w) T)
      where L = entered (≈ₖ-pred x) (q ++ [ ix 1 ]) ∷ᴸ lanes-pred (lanes-++ b d)
            T = ∪-ne (agreeᵀ-pred t) (agreeᵀ-pred (cutˢ c))
    lane-ne doneᴼ []ᴸ c []ᴸ []ᑫ t end⁼ = end⁼
    lane-ne doneᴼ []ᴸ c (x ∷ᴸ d) []ᑫ t end⁼ =
      skip⁼ (whole-ne doneᴼ L T) (go-ne doneᴼ L []ᑫ T)
      where L = lanes-pred (x ∷ᴸ d)
            T = ∪-ne (agreeᵀ-pred t) (agreeᵀ-pred (cutˢ c))
    lane-ne doneᴼ (x ∷ᴸ b) c d []ᑫ t end⁼ =
      skip⁼ (whole-ne doneᴼ L T) (go-ne doneᴼ L []ᑫ T)
      where L = lanes-pred (lanes-++ (x ∷ᴸ b) d)
            T = ∪-ne (agreeᵀ-pred t) (agreeᵀ-pred (cutˢ c))
    lane-ne r@(liveᴼ _ _) b c d []ᑫ t end⁼ =
      skip⁼ (whole-ne (outer-pred r) L T) (go-ne (outer-pred r) L []ᑫ T)
      where L = lanes-pred (lanes-++ b d)
            T = ∪-ne (agreeᵀ-pred t) (agreeᵀ-pred (cutˢ c))
    lane-ne r b c d w t hush⁼ = hush⁼

flatMapᴰ-ne : ∀ {A B k} op {f g : A → MonotonicList B} {x y : MonotonicList A}
            → x ≈[ k ] y → (∀ a → f a ≈[ k ] g a) → flatMapᴰ op f x ≈[ k ] flatMapᴰ op g y
flatMapᴰ-ne op {f} {g} {x} {y} xy F = agrees
  (λ p → whole-ne (live p) []ᴸ (agreeᵀ-refl _ idle))
  (λ p → go-ne op (live p) []ᴸ []ᑫ (agreeᵀ-refl _ idle))
  where live = λ p → liveᴼ {e = enter (mapᴰ f x) p} {enter (mapᴰ g y) p} (agreeᵀ xy p) (mapᴱ-neᴹ F (agree xy p))
