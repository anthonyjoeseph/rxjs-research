{-# OPTIONS --guardedness #-}

-- A RUN WITH SKIPS ERASED (`Erase`), and its tail with pins erased
-- (`Eraseᵀ`): each one erased comes no later than the other's next, so
-- the other's next is never earlier than the run's (`nb-erase`,
-- `after-erase`), and tails so erased merge so erased (`∪-erase`).
module adequacy.Engine.Erase where

open import Data.Bool using (true; false)
open import Data.List using ([]; _++_; [_])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; Tail∞; pin; out; skip; end; hush; idle; _∪_; first; sooner; _<ᵖ_;
  <ᵖ-split; <ᵖ-asym; <ᵖ-trans; <ᵖ-below; ≮-trans)
open import denotation.MonotonicList using (head; mapᴱ; Agree; Agreeᵀ; stop; stopᵀ; pin⁼; idle⁼; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agreeᵀ-refl)
open import adequacy.Placed.Order using (still)
open import adequacy.Engine.Race using (After; NotBefore; TailNotBefore)
open Events∞
open Tail∞

------------------------------------------------------------------------
-- Runs with skips erased

-- A tail with none or more of its pins erased, each no later than the
-- other's next: a merge of tails reads each by its next.
--
-- REFUTED: 5a5d1bd0 any pin erased, by an outer's tail `[5, 1]` erased of
--   its `5` beside a pool pinned at `[3]`: the merge's tails are `[3, 5, 1]`
--   and `[1, 3]`.
data Eraseᵀ : ℕ → Tail → Tail → Set where
  stopᵉ : ∀ {x y} → Eraseᵀ zero x y
  pinᵉ  : ∀ {k p l r} → Eraseᵀ k (later l) (later r) → Eraseᵀ (suc k) (pin p l) (pin p r)
  unpin : ∀ {k p l r} → TailNotBefore p r → Eraseᵀ k (later l) r → Eraseᵀ (suc k) (pin p l) r
  idleᵉ : ∀ {k} → Eraseᵀ (suc k) idle idle

-- A run with none or more of its skips erased, `t` what the other leaves
-- running where it stands: each event kept alike, each tail beside one
-- erased alike, the tail past an erased skip beside the other's.  An
-- erased skip comes no later than the other's next: a merge reads its
-- parts by their next, so a skip erased out of order moves a sibling
-- across the outer's next.
--
-- REFUTED: 01726160 any skip erased, by an outer's `skip [5]` erased
--   before its `skip [1]`: a lane at `[3]` merges before the outer's next
--   on the one side, after it on the other.
data Erase {A : Set} : ℕ → Events A → Tail → Events A → Set where
  stopᵉ  : ∀ {x t y} → Erase zero x t y
  outᵉ   : ∀ {k p a l r t} → Eraseᵀ k (cut l) (cut r) → Erase k (force l) (cut r) (force r) → Erase (suc k) (out p a l) t (out p a r)
  skipᵉ  : ∀ {k p l r t} → Eraseᵀ k (cut l) (cut r) → Erase k (force l) (cut r) (force r) → Erase (suc k) (skip p l) t (skip p r)
  erased : ∀ {k p l t e} → NotBefore p (head e) → Eraseᵀ k (cut l) t → Erase k (force l) t e → Erase (suc k) (skip p l) t e
  endᵉ   : ∀ {k p t} → Erase (suc k) (end p) t (end p)
  hushᵉ  : ∀ {k t} → Erase (suc k) hush t hush

-- Two runs with the same next.
data Lead⁼ {A : Set} : Events A → Events A → Set where
  outᴸ  : ∀ {p a l r} → Lead⁼ (out p a l) (out p a r)
  skipᴸ : ∀ {p l r} → Lead⁼ (skip p l) (skip p r)
  endᴸ  : ∀ {p} → Lead⁼ (end p) (end p)
  hushᴸ : Lead⁼ hush hush

record Eraseˢ {A : Set} (m : ℕ) (l l′ : Events∞ A) : Set where
  constructor _,ᵉ_
  field
    cutᵉ : Eraseᵀ m (cut l) (cut l′)
    nowᵉ : Erase m (force l) (cut l′) (force l′)
open Eraseˢ public

-- THE REST, ERASED: `h′` is `h` with skips erased, its next kept, and,
-- hushed, leaving the same running.
_⊒_ : ∀ {A} → Events∞ A → Events∞ A → Set
h ⊒ h′ = Lead⁼ (force h) (force h′) × (force h ≡ hush → ∀ d → Agreeᵀ d (cut h) (cut h′)) × (∀ n → Eraseˢ n h h′)

-- Alike, erased of nothing.
eraseᵀ-agree : ∀ {k} {x y : Tail} → Agreeᵀ k x y → Eraseᵀ k x y
eraseᵀ-agree stopᵀ    = stopᵉ
eraseᵀ-agree (pin⁼ a) = pinᵉ (eraseᵀ-agree a)
eraseᵀ-agree idle⁼    = idleᵉ

erase-agree : ∀ {A k} {x y : Events A} {t} → Agree k x y → Erase k x t y
erase-agree stop        = stopᵉ
erase-agree (out⁼ t a)  = outᵉ (eraseᵀ-agree t) (erase-agree a)
erase-agree (skip⁼ t a) = skipᵉ (eraseᵀ-agree t) (erase-agree a)
erase-agree end⁼        = endᵉ
erase-agree hush⁼       = hushᵉ

lead-agree : ∀ {A} {x y : Events A} → Agree 1 x y → Lead⁼ x y
lead-agree (out⁼ _ _)  = outᴸ
lead-agree (skip⁼ _ _) = skipᴸ
lead-agree end⁼        = endᴸ
lead-agree hush⁼       = hushᴸ

eraseˢ-refl : ∀ {A} m (l : Events∞ A) → Eraseˢ m l l
eraseˢ-refl m l = eraseᵀ-agree (agreeᵀ-refl m (cut l)) ,ᵉ erase-agree (agree-refl m (force l))

-- Erased for a step more, erased.
eraseᵀ-pred : ∀ {k} {x y : Tail} → Eraseᵀ (suc k) x y → Eraseᵀ k x y
eraseᵀ-pred {zero}  _           = stopᵉ
eraseᵀ-pred {suc k} (pinᵉ a)    = pinᵉ (eraseᵀ-pred a)
eraseᵀ-pred {suc k} (unpin o a) = unpin o (eraseᵀ-pred a)
eraseᵀ-pred {suc k} idleᵉ       = idleᵉ

erase-pred : ∀ {A k} {x y : Events A} {t} → Erase (suc k) x t y → Erase k x t y
erase-pred {k = zero}  _              = stopᵉ
erase-pred {k = suc k} (outᵉ e x)     = outᵉ (eraseᵀ-pred e) (erase-pred x)
erase-pred {k = suc k} (skipᵉ e x)    = skipᵉ (eraseᵀ-pred e) (erase-pred x)
erase-pred {k = suc k} (erased o e x) = erased o (eraseᵀ-pred e) (erase-pred x)
erase-pred {k = suc k} endᵉ           = endᵉ
erase-pred {k = suc k} hushᵉ          = hushᵉ

eraseˢ-pred : ∀ {A m} {l l′ : Events∞ A} → Eraseˢ (suc m) l l′ → Eraseˢ m l l′
eraseˢ-pred (t ,ᵉ x) = eraseᵀ-pred t ,ᵉ erase-pred x

-- The next of a run erased is the next of the run.
lead-head : ∀ {A} {x y : Events A} → Lead⁼ x y → head x ≡ head y
lead-head outᴸ  = refl
lead-head skipᴸ = refl
lead-head endᴸ  = refl
lead-head hushᴸ = refl

------------------------------------------------------------------------
-- Positions in order

nb-le : ∀ {p q} h → q <ᵖ p ≡ false → NotBefore q h → NotBefore p h
nb-le nothing   _ _ = tt
nb-le {p} {q} (just h) x y = ≮-trans p q h x y

after-le : ∀ {p q} h → p <ᵖ q ≡ true → NotBefore q h → After p h
after-le nothing   _ _ = tt
after-le {p} {q} (just h) x y = still p q h x y

after-nb : ∀ {p} h → After p h → NotBefore p h
after-nb nothing  _ = tt
after-nb {p} (just h) x = <ᵖ-asym p h x

tnb-le : ∀ {p q} t → q <ᵖ p ≡ false → TailNotBefore q t → TailNotBefore p t
tnb-le idle      _ _ = tt
tnb-le {p} {q} (pin k _) x y = ≮-trans p q k x y

-- Past a position, its subtree too.
below-on : ∀ {p} k x → NotBefore p (just k) → NotBefore p (just (k ++ [ x ]))
below-on {p} k x o with <ᵖ-split p k o
... | inj₁ lt   = <ᵖ-asym p (k ++ [ x ]) (<ᵖ-trans p k (k ++ [ x ]) lt (<ᵖ-below k []))
... | inj₂ refl = <ᵖ-asym k (k ++ [ x ]) (<ᵖ-below k [])

------------------------------------------------------------------------
-- What erasure keeps of a next

-- The other's next is no earlier than the run's.
nb-erase : ∀ {A k p} {x y : Events A} {t} → Erase (suc k) x t y → NotBefore p (head x) → NotBefore p (head y)
nb-erase (outᵉ _ _)         n = n
nb-erase (skipᵉ _ _)        n = n
nb-erase {y = y} (erased o _ _) n = nb-le (head y) n o
nb-erase endᵉ               n = n
nb-erase hushᵉ              n = n

after-erase : ∀ {A k p} {x y : Events A} {t} → Erase (suc k) x t y → After p (head x) → After p (head y)
after-erase (outᵉ _ _)         a = a
after-erase (skipᵉ _ _)        a = a
after-erase {y = y} (erased o _ _) a = after-le (head y) a o
after-erase endᵉ               a = a
after-erase hushᵉ              a = a

hushed-erase : ∀ {A k} {x y : Events A} {t} → Erase (suc k) x t y → head x ≡ nothing → head y ≡ nothing
hushed-erase hushᵉ refl = refl

tnb-erase : ∀ {k p} {t t′ : Tail} → Eraseᵀ (suc k) t t′ → TailNotBefore p t → TailNotBefore p t′
tnb-erase (pinᵉ _)            n = n
tnb-erase {t′ = t′} (unpin o _) n = tnb-le t′ n o
tnb-erase idleᵉ               n = n

------------------------------------------------------------------------
-- Tails erased, merged

tnb-∪ : ∀ {p} {x y : Tail} → TailNotBefore p x → TailNotBefore p y → TailNotBefore p (x ∪ y)
tnb-∪ {x = idle}    _ b = b
tnb-∪ {x = pin k r} {idle}     a b = a
tnb-∪ {x = pin k r} {pin k′ u} a b with k <ᵖ k′
... | true  = a
... | false = b

private
  sooner-on : ∀ {k q} (y : Tail) → k <ᵖ q ≡ true → TailNotBefore q y → sooner k y ≡ true
  sooner-on idle      _ _ = refl
  sooner-on {k} {q} (pin k′ _) a b = still k q k′ a b

  tnb-lt : ∀ {p q} (y : Tail) → p <ᵖ q ≡ true → TailNotBefore q y → TailNotBefore p y
  tnb-lt {p} {q} y a b = tnb-le y (<ᵖ-asym p q a) b

-- Tails erased merge erased: each merge reads its parts by their next,
-- and an erased pin is no later than the other's.
mutual
  ∪-erase : ∀ {n} {x x′ y y′ : Tail} → Eraseᵀ n x x′ → Eraseᵀ n y y′ → Eraseᵀ n (x ∪ y) (x′ ∪ y′)
  ∪-erase {zero}  _ _ = stopᵉ
  ∪-erase {suc n} idleᵉ b = b
  ∪-erase {suc n} {y = y} (pinᵉ {p = k} a)    b = first-kept {s = sooner k y} refl a b
  ∪-erase {suc n} {y = y} (unpin {p = k} o a) b = first-gone {s = sooner k y} refl o a b

  first-kept : ∀ {n k l r} {y y′ : Tail} {s} → sooner k y ≡ s → Eraseᵀ n (later l) (later r) → Eraseᵀ (suc n) y y′
             → Eraseᵀ (suc n) (first k l y s) (pin k r ∪ y′)
  first-kept {s = true}  ss a idleᵉ = pinᵉ (∪-erase a (eraseᵀ-pred idleᵉ))
  first-kept {s = true}  ss a (pinᵉ b) rewrite ss = pinᵉ (∪-erase a (eraseᵀ-pred (pinᵉ b)))
  first-kept {k = k} {y′ = y′} {s = true} ss a (unpin {p = q} o b) rewrite sooner-on {k} {q} y′ ss o = pinᵉ (∪-erase a (eraseᵀ-pred (unpin o b)))
  first-kept {s = false} () a idleᵉ
  first-kept {s = false} ss a (pinᵉ b) rewrite ss = pinᵉ (∪-erase (eraseᵀ-pred (pinᵉ a)) b)
  first-kept {s = false} ss a (unpin o b) = unpin (tnb-∪ ss o) (∪-erase (eraseᵀ-pred (pinᵉ a)) b)

  first-gone : ∀ {n k l} {x′ y y′ : Tail} {s} → sooner k y ≡ s → TailNotBefore k x′ → Eraseᵀ n (later l) x′ → Eraseᵀ (suc n) y y′
             → Eraseᵀ (suc n) (first k l y s) (x′ ∪ y′)
  first-gone {s = true} ss o a idleᵉ = unpin (tnb-∪ o tt) (∪-erase a (eraseᵀ-pred idleᵉ))
  first-gone {k = k} {s = true} ss o a (pinᵉ {p = q} b) = unpin (tnb-∪ o (<ᵖ-asym k q ss)) (∪-erase a (eraseᵀ-pred (pinᵉ b)))
  first-gone {y′ = y′} {s = true} ss o a (unpin o′ b) = unpin (tnb-∪ o (tnb-lt y′ ss o′)) (∪-erase a (eraseᵀ-pred (unpin o′ b)))
  first-gone {s = false} () o a idleᵉ
  first-gone {x′ = idle} {s = false} ss o a (pinᵉ b) = pinᵉ (∪-erase (eraseᵀ-pred (unpin o a)) b)
  first-gone {k = k} {x′ = pin k′ r′} {s = false} ss o a (pinᵉ {p = q} b) rewrite ≮-trans q k k′ ss o =
    pinᵉ (∪-erase (eraseᵀ-pred (unpin o a)) b)
  first-gone {x′ = x′} {s = false} ss o a (unpin o′ b) = unpin (tnb-∪ (tnb-le x′ ss o) o′) (∪-erase (eraseᵀ-pred (unpin o a)) b)

------------------------------------------------------------------------
-- Mapped, erased alike

private
  map-on : ∀ {A B} (g : A → B) {p} x → NotBefore p (head x) → NotBefore p (head (mapᴱ g x))
  map-on g (out _ _ _) o = o
  map-on g (skip _ _)  o = o
  map-on g (end _)     o = o
  map-on g hush        o = o

map-erase : ∀ {A B} (g : A → B) {k x t y} → Erase k x t y → Erase k (mapᴱ g x) t (mapᴱ g y)
map-erase g stopᵉ          = stopᵉ
map-erase g (outᵉ e x)     = outᵉ e (map-erase g x)
map-erase g (skipᵉ e x)    = skipᵉ e (map-erase g x)
map-erase g (erased o e x) = erased (map-on g _ o) e (map-erase g x)
map-erase g endᵉ           = endᵉ
map-erase g hushᵉ          = hushᵉ

map-lead : ∀ {A B} (g : A → B) {x y} → Lead⁼ x y → Lead⁼ (mapᴱ g x) (mapᴱ g y)
map-lead g outᴸ  = outᴸ
map-lead g skipᴸ = skipᴸ
map-lead g endᴸ  = endᴸ
map-lead g hushᴸ = hushᴸ
