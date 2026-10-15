{-# OPTIONS --guardedness #-}

-- THE OPERATORS READ NO FURTHER THAN THEY SHOW: each one's first k steps
-- are fixed by its inputs' first k, at every subscription.  Every output
-- step spends one step of one input, and choosing it looks at most one
-- step ahead in each, so a budget of m steps left is enough for every
-- input still being read.
module denotation.NonExpansive where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import denotation.MonotonicList using (MonotonicList; Events; Events∞; Agree; agree-refl; mapᴰ; scanᴰ; takeWhileᴰ; scanᴱ;
  takeWhileᴱ; taking; connectᴰ; hot; rejoin; beside; ahead; before; stop; out⁼; skip⁼; end⁼;
  hush⁼; agree-pred; _≈[_]_; agrees; agree; ≈ₖ-pred; ix; _<ᵖ_; mapᴱ; FlatOp; mergeᶠ; switchᶠ;
  exhaustᶠ; head; Earliest; none; found; earliest; admit; go; viaOuter; race; outer; lane;
  flatMapᴰ)

------------------------------------------------------------------------
-- Lanes and queues agreeing for m steps, pairwise

infixr 5 _∷ᴸ_ _∷ᑫ_

data Lanes {B : Set} (m : ℕ) : List (Events B) → List (Events B) → Set where
  []ᴸ  : Lanes m [] []
  _∷ᴸ_ : ∀ {l l′ ls ls′} → Agree m l l′ → Lanes m ls ls′ → Lanes m (l ∷ ls) (l′ ∷ ls′)

data Queue {B : Set} (m : ℕ) : List (MonotonicList B) → List (MonotonicList B) → Set where
  []ᑫ  : Queue m [] []
  _∷ᑫ_ : ∀ {q q′ qs qs′} → q ≈[ m ] q′ → Queue m qs qs′ → Queue m (q ∷ qs) (q′ ∷ qs′)

private
  lanes-pred : ∀ {B m} {ls ls′ : List (Events B)} → Lanes (suc m) ls ls′ → Lanes m ls ls′
  lanes-pred []ᴸ      = []ᴸ
  lanes-pred (a ∷ᴸ l) = agree-pred a ∷ᴸ lanes-pred l

  lanes-++ : ∀ {B m} {as as′ bs bs′ : List (Events B)} → Lanes m as as′ → Lanes m bs bs′ → Lanes m (as ++ bs) (as′ ++ bs′)
  lanes-++ []ᴸ      b = b
  lanes-++ (a ∷ᴸ l) b = a ∷ᴸ lanes-++ l b

  lanes-length : ∀ {B m} {ls ls′ : List (Events B)} → Lanes m ls ls′ → length ls ≡ length ls′
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
  head-agree (out⁼ _)  = refl
  head-agree (skip⁼ _) = refl
  head-agree end⁼      = refl
  head-agree hush⁼     = refl

------------------------------------------------------------------------
-- ONE STEP IN, ONE STEP OUT

private
  mapᴱ-ne : ∀ {A B m} (f : A → B) {x y : Events A} → Agree m x y → Agree m (mapᴱ f x) (mapᴱ f y)
  mapᴱ-ne f stop      = stop
  mapᴱ-ne f (out⁼ a)  = out⁼ (mapᴱ-ne f a)
  mapᴱ-ne f (skip⁼ a) = skip⁼ (mapᴱ-ne f a)
  mapᴱ-ne f end⁼      = end⁼
  mapᴱ-ne f hush⁼     = hush⁼

  scanᴱ-ne : ∀ {A B m} (f : B → A → B) z {x y : Events A} → Agree m x y → Agree m (scanᴱ f z x) (scanᴱ f z y)
  scanᴱ-ne f z stop                = stop
  scanᴱ-ne f z (out⁼ {a = a} r)    = out⁼ (scanᴱ-ne f (f z a) r)
  scanᴱ-ne f z (skip⁼ r)           = skip⁼ (scanᴱ-ne f z r)
  scanᴱ-ne f z end⁼                = end⁼
  scanᴱ-ne f z hush⁼               = hush⁼

  mutual
    takeWhileᴱ-ne : ∀ {A m} i (p : A → Bool) {x y : Events A} → Agree m x y → Agree m (takeWhileᴱ i p x) (takeWhileᴱ i p y)
    takeWhileᴱ-ne i p stop                 = stop
    takeWhileᴱ-ne i p (out⁼ {a = a} r)     = taking-ne i p (p a) r
    takeWhileᴱ-ne i p (skip⁼ r)            = skip⁼ (takeWhileᴱ-ne i p r)
    takeWhileᴱ-ne i p end⁼                 = end⁼
    takeWhileᴱ-ne i p hush⁼                = hush⁼

    taking-ne : ∀ {A m k a} i (p : A → Bool) t {l r : Events∞ A} → Agree m (Events∞.force l) (Events∞.force r)
              → Agree (suc m) (taking i p k a t l) (taking i p k a t r)
    taking-ne i     p true  a = out⁼ (takeWhileᴱ-ne i p a)
    taking-ne {m = m} true  p false a = out⁼ (agree-refl m _)
    taking-ne false p false a = end⁼

mapᴰ-ne : ∀ {A B k} (f : A → B) {x y : MonotonicList A} → x ≈[ k ] y → mapᴰ f x ≈[ k ] mapᴰ f y
mapᴰ-ne f xy = agrees λ p → mapᴱ-ne f (agree xy p)

scanᴰ-ne : ∀ {A B k} (f : B → A → B) z {x y : MonotonicList A} → x ≈[ k ] y → scanᴰ f z x ≈[ k ] scanᴰ f z y
scanᴰ-ne f z xy = agrees λ p → scanᴱ-ne f z (agree xy p)

takeWhileᴰ-ne : ∀ {A k} i (p : A → Bool) {x y : MonotonicList A} → x ≈[ k ] y → takeWhileᴰ i p x ≈[ k ] takeWhileᴰ i p y
takeWhileᴰ-ne i p xy = agrees λ q → takeWhileᴱ-ne i p (agree xy q)

------------------------------------------------------------------------
-- CONNECT: the hot handle shows a joiner's skipped past as one skip per
-- source step, and the body and the source interleave, each read one
-- step ahead.

private
  rejoin-ne : ∀ {A m} p i {x y : Events A} → Agree m x y → Agree m (rejoin p i x) (rejoin p i y)
  rejoin-ne p i stop = stop
  rejoin-ne p i (out⁼ {p = q} a) with p <ᵖ q
  ... | true  = out⁼ (rejoin-ne p i a)
  ... | false = skip⁼ (rejoin-ne p (suc i) a)
  rejoin-ne p i (skip⁼ {p = q} a) with p <ᵖ q
  ... | true  = skip⁼ (rejoin-ne p i a)
  ... | false = skip⁼ (rejoin-ne p (suc i) a)
  rejoin-ne {m = suc m} p i (end⁼ {p = c}) = agree-refl (suc m) _
  rejoin-ne p i hush⁼ = hush⁼

  before-agree : ∀ {B m} q {x y : Events B} → Agree (suc m) x y → before q x ≡ before q y
  before-agree q (out⁼ _)  = refl
  before-agree q (skip⁼ _) = refl
  before-agree q end⁼      = refl
  before-agree q hush⁼     = refl

  mutual
    beside-ne : ∀ {A B m} {b b′ : Events B} {e e′ : Events A} → Agree m b b′ → Agree m e e′ → Agree m (beside b e) (beside b′ e′)
    beside-ne {m = zero} _ _ = stop
    beside-ne {m = suc m} {b} {b′} bb (out⁼ {p = q} a) =
      ahead-ne (before (q ++ [ ix 0 ]) b) (before (q ++ [ ix 0 ]) b′) (before-agree (q ++ [ ix 0 ]) bb) bb a
    beside-ne {m = suc m} {b} {b′} bb (skip⁼ {p = q} a) =
      ahead-ne (before (q ++ [ ix 0 ]) b) (before (q ++ [ ix 0 ]) b′) (before-agree (q ++ [ ix 0 ]) bb) bb a
    beside-ne {m = suc m} bb end⁼  = bb
    beside-ne {m = suc m} bb hush⁼ = bb

    -- The flag is `before` of each side, equal because the bodies agree.
    ahead-ne : ∀ {A B m q} {b b′ : Events B} {s s′ : Events∞ A} t t′ → t ≡ t′ → Agree (suc m) b b′
             → Agree m (Events∞.force s) (Events∞.force s′) → Agree (suc m) (ahead b q s t) (ahead b′ q s′ t′)
    ahead-ne true  _ refl bb a = skip⁼ (beside-ne (agree-pred bb) a)
    ahead-ne {m = zero}  false _ refl (out⁼ _)  a = out⁼ stop
    ahead-ne {m = zero}  false _ refl (skip⁼ _) a = skip⁼ stop
    ahead-ne {m = suc m} {q = q} false _ refl (out⁼ {l = r} {r = r′} bb) a =
      out⁼ (ahead-ne (before q (Events∞.force r)) (before q (Events∞.force r′)) (before-agree q bb) bb (agree-pred a))
    ahead-ne {m = suc m} {q = q} false _ refl (skip⁼ {l = r} {r = r′} bb) a =
      skip⁼ (ahead-ne (before q (Events∞.force r)) (before q (Events∞.force r′)) (before-agree q bb) bb (agree-pred a))
    ahead-ne false _ refl end⁼  a = end⁼
    ahead-ne false _ refl hush⁼ a = hush⁼

  hot-ne : ∀ {A k} {e e′ : Events A} → Agree k e e′ → hot e ≈[ k ] hot e′
  hot-ne a = agrees λ p → rejoin-ne p 0 a

connectᴰ-ne : ∀ {A B k} {x y : MonotonicList A} {f g : MonotonicList A → MonotonicList B}
            → x ≈[ k ] y → (∀ {r r′} → r ≈[ k ] r′ → f r ≈[ k ] g r′) → connectᴰ x f ≈[ k ] connectᴰ y g
connectᴰ-ne xy H = agrees λ p →
  beside-ne (agree (H (hot-ne (agree xy (p ++ [ ix 1 ])))) (p ++ [ ix 0 ])) (agree xy (p ++ [ ix 1 ]))

------------------------------------------------------------------------
-- FLATMAP

data Earliestᴿ {B : Set} (m : ℕ) : Earliest B → Earliest B → Set where
  noneᴿ  : Earliestᴿ m none none
  foundᴿ : ∀ {k bs bs′ l l′ as as′} → Lanes m bs bs′ → Agree m l l′ → Lanes m as as′
         → Earliestᴿ m (found k bs l as) (found k bs′ l′ as′)

private
  -- Agreeing lanes race alike: the winner is read off their heads.
  earliest-agree : ∀ {B m} {ls ls′ : List (Events B)} → Lanes (suc m) ls ls′ → Earliestᴿ (suc m) (earliest ls) (earliest ls′)
  earliest-agree []ᴸ = noneᴿ
  earliest-agree {ls = l ∷ ls} {l′ ∷ ls′} (a ∷ᴸ as)
    with head l | head l′ | head-agree a | earliest ls | earliest ls′ | earliest-agree as
  ... | nothing | _ | refl | none            | _ | noneᴿ          = noneᴿ
  ... | nothing | _ | refl | found _ _ _ _   | _ | foundᴿ b c d   = foundᴿ (a ∷ᴸ b) c d
  ... | just k  | _ | refl | none            | _ | noneᴿ          = foundᴿ []ᴸ a as
  ... | just k  | _ | refl | found k′ _ _ _  | _ | foundᴿ b c d with k <ᵖ k′
  ...   | true  = foundᴿ []ᴸ a as
  ...   | false = foundᴿ (a ∷ᴸ b) c d

  -- Agreeing lanes and queue admit an agreeing lane alike.
  admit-agree : ∀ {B m} op q {x y : MonotonicList B} {ls ls′ qs qs′} → x ≈[ m ] y → Lanes m ls ls′ → Queue m qs qs′
              → Lanes m (proj₁ (admit op q x ls qs)) (proj₁ (admit op q y ls′ qs′))
              × Queue m (proj₂ (admit op q x ls qs)) (proj₂ (admit op q y ls′ qs′))
  admit-agree (mergeᶠ nothing)  q xy l w = agree xy q ∷ᴸ l , w
  admit-agree (mergeᶠ (just n)) q {ls = ls} {ls′} xy l w rewrite lanes-length l with length ls′ <ᵇ n
  ... | true  = agree xy q ∷ᴸ l , w
  ... | false = l , queue-++ w (xy ∷ᑫ []ᑫ)
  admit-agree switchᶠ           q xy l w = agree xy q ∷ᴸ []ᴸ , w
  admit-agree exhaustᶠ          q xy []ᴸ w = agree xy q ∷ᴸ []ᴸ , w
  admit-agree exhaustᶠ          q xy (a ∷ᴸ l) w = a ∷ᴸ l , w

  head-map : ∀ {A B m} {f g : A → B} {x y : Events A} → Agree (suc m) x y → head (mapᴱ f x) ≡ head (mapᴱ g y)
  head-map (out⁼ _)  = refl
  head-map (skip⁼ _) = refl
  head-map end⁼      = refl
  head-map hush⁼     = refl

module _ {A B : Set} (op : FlatOp) (f g : A → MonotonicList B) where

  -- The outer: done on both sides, or the elements' runs agreeing, each
  -- side's element the function's lane.
  data Outerᴿ (m : ℕ) : Maybe (Events (MonotonicList B)) → Maybe (Events (MonotonicList B)) → Set where
    doneᴼ : Outerᴿ m nothing nothing
    liveᴼ : ∀ {e e′} → Agree m e e′ → Outerᴿ m (just (mapᴱ f e)) (just (mapᴱ g e′))

  private
    outer-pred : ∀ {m o o′} → Outerᴿ (suc m) o o′ → Outerᴿ m o o′
    outer-pred doneᴼ     = doneᴼ
    outer-pred (liveᴼ a) = liveᴼ (agree-pred a)

  mutual
    go-ne : ∀ {m o o′ ls ls′ qs qs′} → (∀ a → f a ≈[ m ] g a) → Outerᴿ m o o′ → Lanes m ls ls′ → Queue m qs qs′
          → Agree m (go op o ls qs) (go op o′ ls′ qs′)
    go-ne {zero} _ _ _ _ = stop
    go-ne {suc m} {ls = ls} {ls′} F r l w with earliest ls | earliest ls′ | earliest-agree l
    ... | none          | _ | noneᴿ        = viaOuter-ne F r l w
    ... | found k _ _ _ | _ | foundᴿ b c d = race-ne F r b c d w

    viaOuter-ne : ∀ {m o o′ ls ls′ qs qs′} → (∀ a → f a ≈[ suc m ] g a) → Outerᴿ (suc m) o o′ → Lanes (suc m) ls ls′ → Queue (suc m) qs qs′
                → Agree (suc m) (viaOuter op o ls qs) (viaOuter op o′ ls′ qs′)
    viaOuter-ne F doneᴼ     l w = hush⁼
    viaOuter-ne F (liveᴼ a) l w = outer-ne F a l w

    race-ne : ∀ {m o o′ k bs bs′ c c′ as as′ qs qs′} → (∀ a → f a ≈[ suc m ] g a) → Outerᴿ (suc m) o o′
            → Lanes (suc m) bs bs′ → Agree (suc m) c c′ → Lanes (suc m) as as′ → Queue (suc m) qs qs′
            → Agree (suc m) (race op o k bs c as qs) (race op o′ k bs′ c′ as′ qs′)
    race-ne F doneᴼ b c d w = lane-ne F doneᴼ b c d w
    race-ne {k = k} F (liveᴼ {e} {e′} a) b c d w
      with head (mapᴱ f e) | head (mapᴱ g e′) | head-map {f = f} {g} a
    ... | nothing | _ | refl = lane-ne F (liveᴼ a) b c d w
    ... | just k′ | _ | refl with k′ <ᵖ k
    ...   | true  = outer-ne F a (lanes-++ b (c ∷ᴸ d)) w
    ...   | false = lane-ne F (liveᴼ a) b c d w

    outer-ne : ∀ {m e e′ ls ls′ qs qs′} → (∀ a → f a ≈[ suc m ] g a) → Agree (suc m) e e′ → Lanes (suc m) ls ls′ → Queue (suc m) qs qs′
             → Agree (suc m) (outer op (mapᴱ f e) ls qs) (outer op (mapᴱ g e′) ls′ qs′)
    outer-ne {ls = ls} {ls′} {qs} {qs′} F (out⁼ {p = q} {a = x} a) l w
      with admit op (q ++ [ ix 1 ]) (f x) ls qs | admit op (q ++ [ ix 1 ]) (g x) ls′ qs′
         | admit-agree op (q ++ [ ix 1 ]) (F x) l w
    ... | _ , _ | _ , _ | l′ , w′ = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) (liveᴼ a) (lanes-pred l′) (queue-pred w′))
    outer-ne F (skip⁼ a) l w = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) (liveᴼ a) (lanes-pred l) (queue-pred w))
    outer-ne F end⁼ []ᴸ       []ᑫ       = end⁼
    outer-ne F end⁼ []ᴸ       (x ∷ᑫ w)  = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) doneᴼ []ᴸ (queue-pred (x ∷ᑫ w)))
    outer-ne F end⁼ (x ∷ᴸ l)  w         = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) doneᴼ (lanes-pred (x ∷ᴸ l)) (queue-pred w))
    outer-ne F hush⁼ l w = hush⁼

    lane-ne : ∀ {m o o′ bs bs′ c c′ as as′ qs qs′} → (∀ a → f a ≈[ suc m ] g a) → Outerᴿ (suc m) o o′
            → Lanes (suc m) bs bs′ → Agree (suc m) c c′ → Lanes (suc m) as as′ → Queue (suc m) qs qs′
            → Agree (suc m) (lane op o bs c as qs) (lane op o′ bs′ c′ as′ qs′)
    lane-ne F r b (out⁼ a)  d w = out⁼ (go-ne (λ a → ≈ₖ-pred (F a)) (outer-pred r) (lanes-++ (lanes-pred b) (a ∷ᴸ lanes-pred d)) (queue-pred w))
    lane-ne F r b (skip⁼ a) d w = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) (outer-pred r) (lanes-++ (lanes-pred b) (a ∷ᴸ lanes-pred d)) (queue-pred w))
    lane-ne F r b (end⁼ {p = c}) d (x ∷ᑫ w) =
      skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) (outer-pred r) (agree (≈ₖ-pred x) (c ++ [ ix 1 ]) ∷ᴸ lanes-pred (lanes-++ b d)) (queue-pred w))
    lane-ne F doneᴼ     []ᴸ      end⁼ []ᴸ      []ᑫ = end⁼
    lane-ne F doneᴼ     []ᴸ      end⁼ (x ∷ᴸ d) []ᑫ = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) doneᴼ (lanes-pred (x ∷ᴸ d)) []ᑫ)
    lane-ne F doneᴼ     (x ∷ᴸ b) end⁼ d        []ᑫ = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) doneᴼ (lanes-pred (lanes-++ (x ∷ᴸ b) d)) []ᑫ)
    lane-ne F (liveᴼ a) b        end⁼ d        []ᑫ = skip⁼ (go-ne (λ a → ≈ₖ-pred (F a)) (liveᴼ (agree-pred a)) (lanes-pred (lanes-++ b d)) []ᑫ)
    lane-ne F r b hush⁼ d w = hush⁼

flatMapᴰ-ne : ∀ {A B k} op {f g : A → MonotonicList B} {x y : MonotonicList A}
            → x ≈[ k ] y → (∀ a → f a ≈[ k ] g a) → flatMapᴰ op f x ≈[ k ] flatMapᴰ op g y
flatMapᴰ-ne op {f} {g} xy F = agrees λ p → go-ne op f g F (liveᴼ (agree xy p)) []ᴸ []ᑫ
