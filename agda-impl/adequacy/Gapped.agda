{-# OPTIONS --guardedness #-}

-- A STEPPED NODE AGAINST THE TREE'S PART: alike, but for gaps.  A step
-- a connect's source took feeds its body; what the body's joiners and
-- deferred nodes are fed of a step they postdate, or of a skip, a part
-- read off the heap does not hold.  Every such entry is a gap: the
-- stepped node's meaning is the part's with skips more.
--
-- Gaps up to `κ`, the latest step fed: a factory's lane and a deferred
-- node's subscription may differ at a step no later than `κ` only once
-- they are reached past it.
module adequacy.Gapped where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList using (Pos; _<ᵖ_; ix; end)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sorted using (_≤ᵖ_)
open import adequacy.Sane using (Sane; allLive)
open import adequacy.Placed using (Placed; Ordered; Reaches; Headed; Sorted; Alienᴱ)
open import adequacy.Strong using (module Strongly)
open import adequacy.Ghost using (module Ghosting)

module Gapping (R : Set) where
  open Strongly R using (Heads)
  open Ghosting R using (Past; residual)

  -- A joiner's entries, skips dropped.
  data Thin {A : Set} : List (Pos × Maybe A) → List (Pos × Maybe A) → Set where
    []ᵗ   : Thin [] []
    keepᵗ : ∀ {x xs ys} → Thin xs ys → Thin (x ∷ xs) (x ∷ ys)
    dropᵗ : ∀ {p xs ys} → Thin xs ys → Thin ((p , nothing) ∷ xs) ys

  -- A deferred node's notices at `p`, a skip's dropped, and a step's no
  -- later than `κ` dropped once `p` is past `κ`.
  data ThinN {Γ} (κ p : Pos) : List (U.Notice Γ) → List (U.Notice Γ) → Set₁ where
    []ⁿ   : ThinN κ p [] []
    keepⁿ : ∀ {n ns ms} → ThinN κ p ns ms → ThinN κ p (n ∷ ns) (n ∷ ms)
    gapⁿ  : ∀ {A} {i : A ∈ Γ} {q ns ms} → ThinN κ p ns ms → ThinN κ p (U.notice i q nothing ∷ ns) ms
    lateⁿ : ∀ {A} {i : A ∈ Γ} {q a ns ms} → q ≤ᵖ κ → κ ≤ᵖ p → ThinN κ p ns ms → ThinN κ p (U.notice i q a ∷ ns) ms

  -- An outer whose next value comes no sooner than `κ`.
  Upcoming : ∀ {Δ A} → Pos → Maybe (U.Node Δ A) → Set
  Upcoming κ nothing  = ⊤
  Upcoming κ (just o) = Heads κ o

  mutual
    data Gapped (κ : Pos) : ∀ {Δ A} → U.Node Δ A → U.Node Δ A → Set₁ where
      alike        : ∀ {Δ A} {c : U.Node Δ A} → Gapped κ c c
      gap-map      : ∀ {Δ A B} {f : A → B} {c c′ : U.Node Δ A} → Gapped κ c c′ → Gapped κ (U.mapᶜ f c) (U.mapᶜ f c′)
      gap-scan     : ∀ {Δ A B} {f : B → A → B} {z} {c c′ : U.Node Δ A} → Gapped κ c c′ → Gapped κ (U.scanᶜ f z c) (U.scanᶜ f z c′)
      gap-take     : ∀ {Δ A} {i p} {c c′ : U.Node Δ A} → Gapped κ c c′ → Gapped κ (U.takeWhileᶜ i p c) (U.takeWhileᶜ i p c′)
      -- Every lane the factory makes, gapped.
      gap-flat     : ∀ {Δ A B} {op} {g g′ : A → Pos → U.Node Δ B} {o o′ ls ls′ qs pl pl′}
                   → (∀ x r → Gapped κ (g x r) (g′ x r)) → GappedM κ o o′ → GappedL κ ls ls′ → Gapped κ pl pl′
                   → Gapped κ (U.flatMapᶜ op g o ls qs pl) (U.flatMapᶜ op g′ o′ ls′ qs pl′)
      -- Only the lanes the outer has still to make, past `κ`.
      gap-late     : ∀ {Δ A B} {op} {g g′ : A → Pos → U.Node Δ B} {o o′ ls ls′ qs pl pl′}
                   → Upcoming κ o → (∀ x r → κ ≤ᵖ r → Gapped κ (g x r) (g′ x r)) → (∀ x r → Sane (allLive Δ) (g′ x r))
                   → GappedM κ o o′ → GappedL κ ls ls′ → Gapped κ pl pl′
                   → Gapped κ (U.flatMapᶜ op g o ls qs pl) (U.flatMapᶜ op g′ o′ ls′ qs pl′)
      gap-join     : ∀ {Δ A} {i : A ∈ Δ} {p xs xs′ e} → Thin xs xs′ → Gapped κ (U.joinᶜ i p xs e) (U.joinᶜ i p xs′ e)
      gap-connect  : ∀ {Δ A B} {r} {b b′ : U.Node (A ∷ Δ) B} {s s′ : U.Source Δ A} → Gapped κ b b′ → GappedS κ s s′
                   → Gapped κ (U.connectᶜ r b s) (U.connectᶜ r b′ s′)
      gap-shut     : ∀ {Δ A B} {i : A ∈ Δ} {c} {b b′ : U.Node Δ B} → Gapped κ b b′ → Gapped κ (U.shut i c b) (U.shut i c b′)
      gap-defer    : ∀ {Δ A} {l} {p} {ns ns′ : List (U.Notice Δ)} → ThinN κ p ns ns′ → Gapped κ (U.deferᶜ {A = A} l p ns) (U.deferᶜ l p ns′)
      gap-ending   : ∀ {Δ A} {p} {c c′ : U.Node Δ A} → Gapped κ c c′ → Gapped κ (U.endingᶜ p c) (U.endingᶜ p c′)
      gap-rest     : ∀ {Δ A B} {c c′ : U.Node Δ A} → Gapped κ c c′ → Gapped κ (U.restᶜ {B = B} c) (U.restᶜ c′)
      gap-union    : ∀ {Δ B} {x x′ y y′ : U.Node Δ B} → Gapped κ x x′ → Gapped κ y y′ → Gapped κ (U.unionᶜ x y) (U.unionᶜ x′ y′)
      gap-bursting : ∀ {Δ A B} {r} {t t′ : U.Node Δ A} → Gapped κ t t′ → Gapped κ (U.burstingᶜ {B = B} r t) (U.burstingᶜ r t′)
      gap-under    : ∀ {Δ A C B} {s s′ : U.Source Δ A} {b b′ : U.Node (A ∷ Δ) C} → GappedS κ s s′ → Gapped κ b b′
                   → Gapped κ (U.underᶜ {B = B} s b) (U.underᶜ s′ b′)

    data GappedM (κ : Pos) {Δ A} : Maybe (U.Node Δ A) → Maybe (U.Node Δ A) → Set₁ where
      gap-nothing : GappedM κ nothing nothing
      gap-just    : ∀ {c c′} → Gapped κ c c′ → GappedM κ (just c) (just c′)

    data GappedL (κ : Pos) {Δ A} : List (U.Node Δ A) → List (U.Node Δ A) → Set₁ where
      gap-[] : GappedL κ [] []
      gap-∷  : ∀ {c c′ cs cs′} → Gapped κ c c′ → GappedL κ cs cs′ → GappedL κ (c ∷ cs) (c′ ∷ cs′)

    data GappedS (κ : Pos) {Δ A} : U.Source Δ A → U.Source Δ A → Set₁ where
      gap-live  : ∀ {s s′} → Gapped κ s s′ → GappedS κ (U.live s) (U.live s′)
      gap-ended : ∀ {c t t′} → Gapped κ t t′ → GappedS κ (U.ended c t) (U.ended c t′)

  gapM-refl : ∀ {κ Δ A} (o : Maybe (U.Node Δ A)) → GappedM κ o o
  gapM-refl nothing  = gap-nothing
  gapM-refl (just _) = gap-just alike

  gapL-refl : ∀ {κ Δ A} (ls : List (U.Node Δ A)) → GappedL κ ls ls
  gapL-refl []       = gap-[]
  gapL-refl (_ ∷ ls) = gap-∷ alike (gapL-refl ls)

  -- One lane gapped, the rest alike.
  gapL-mid : ∀ {κ Δ A} (bs : List (U.Node Δ A)) {c c′} as → Gapped κ c c′ → GappedL κ (bs ++ c ∷ as) (bs ++ c′ ∷ as)
  gapL-mid []       as gp = gap-∷ gp (gapL-refl as)
  gapL-mid (_ ∷ bs) as gp = gap-∷ alike (gapL-mid bs as gp)

  ----------------------------------------------------------------------
  -- A skip fed is a gap

  thin-refl : ∀ {A} (xs : List (Pos × Maybe A)) → Thin xs xs
  thin-refl []       = []ᵗ
  thin-refl (_ ∷ xs) = keepᵗ (thin-refl xs)

  thin-snoc : ∀ {A} (xs : List (Pos × Maybe A)) p → Thin (xs ++ [ p , nothing ]) xs
  thin-snoc []       p = dropᵗ []ᵗ
  thin-snoc (_ ∷ xs) p = keepᵗ (thin-snoc xs p)

  thinN-snoc : ∀ {κ p Γ A} (ns : List (U.Notice Γ)) {i : A ∈ Γ} {q} → ThinN κ p (ns ++ [ U.notice i q nothing ]) ns
  thinN-snoc []       = gapⁿ []ⁿ
  thinN-snoc (_ ∷ ns) = keepⁿ (thinN-snoc ns)

  fed-thin : ∀ {Γ A B} (i : A ∈ Γ) q (j : B ∈ Γ) p xs s → Thin (U.fed i q nothing j p xs s) xs
  fed-thin i q j p xs nothing = thin-refl xs
  fed-thin i q j p xs (just refl) with p <ᵖ q
  ... | true  = thin-snoc xs _
  ... | false = thin-snoc xs _

  mutual
    feed-gapped : ∀ {κ Γ A B} (i : A ∈ Γ) q (c : U.Node Γ B) → Gapped κ (U.feed i q nothing c) c
    feed-gapped i q (U.framesᶜ _ _ _)            = alike
    feed-gapped i q (U.burstᶜ _ _ _ _)           = alike
    feed-gapped i q (U.ofᶜ _ _ _)                = alike
    feed-gapped i q (U.mapᶜ f c)                 = gap-map (feed-gapped i q c)
    feed-gapped i q (U.scanᶜ f z c)              = gap-scan (feed-gapped i q c)
    feed-gapped i q (U.takeWhileᶜ b p c)         = gap-take (feed-gapped i q c)
    feed-gapped i q (U.flatMapᶜ op g o ls qs pl) =
      gap-flat (λ x r → feed-gapped i q (g x r)) (feedᴹ-gapped i q o) (feedᴸ-gapped i q ls) (feed-gapped i q pl)
    feed-gapped i q (U.joinᶜ j p xs e)           = gap-join (fed-thin i q j p xs (U.same? i j))
    feed-gapped i q (U.connectᶜ r b s)           = gap-connect (feed-gapped (there i) q b) (feedˢ-gapped i q s)
    feed-gapped i q (U.deferᶜ l p ns)            = gap-defer (thinN-snoc ns)
    feed-gapped i q (U.endingᶜ p n)              = gap-ending (feed-gapped i q n)
    feed-gapped i q (U.restᶜ n)                  = gap-rest (feed-gapped i q n)
    feed-gapped i q U.idleᶜ                      = alike
    feed-gapped i q (U.unionᶜ x y)               = gap-union (feed-gapped i q x) (feed-gapped i q y)
    feed-gapped i q (U.burstingᶜ r t)            = gap-bursting (feed-gapped i q t)
    feed-gapped i q (U.underᶜ s b)               = gap-under (feedˢ-gapped i q s) (feed-gapped (there i) q b)

    feedᴹ-gapped : ∀ {κ Γ A B} (i : A ∈ Γ) q (o : Maybe (U.Node Γ B)) → GappedM κ (U.feedᴹ i q nothing o) o
    feedᴹ-gapped i q nothing  = gap-nothing
    feedᴹ-gapped i q (just c) = gap-just (feed-gapped i q c)

    feedᴸ-gapped : ∀ {κ Γ A B} (i : A ∈ Γ) q (ls : List (U.Node Γ B)) → GappedL κ (U.feedᴸ i q nothing ls) ls
    feedᴸ-gapped i q []       = gap-[]
    feedᴸ-gapped i q (c ∷ ls) = gap-∷ (feed-gapped i q c) (feedᴸ-gapped i q ls)

    feedˢ-gapped : ∀ {κ Γ A B} (i : A ∈ Γ) q (s : U.Source Γ B) → GappedS κ (U.feedˢ i q nothing s) s
    feedˢ-gapped i q (U.live s)    = gap-live (feed-gapped i q s)
    feedˢ-gapped i q (U.ended c t) = gap-ended (feed-gapped i q t)

  -- Every node in order, rests and their sources included: `Placed`
  -- looks at no node under a rest, a union, a burst or an ended source.
  mutual
    Deep : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
    Deep c ρ = Ordered (U.meaning c ρ) × Deeps c ρ

    Deeps : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
    Deeps (U.mapᶜ f c)                    ρ = Deep c ρ
    Deeps (U.scanᶜ f z c)                 ρ = Deep c ρ
    Deeps (U.takeWhileᶜ i p c)            ρ = Deep c ρ
    Deeps (U.flatMapᶜ op g o ls qs pl)    ρ = Deepᴹ o ρ × Deepᴸ ls ρ × Deep pl ρ
      × (∀ a x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.flatMapᶜ op g o ls qs pl) ρ) → Deep (g a (x ++ [ ix 1 ])) ρ)
    Deeps (U.connectᶜ r b (U.live s))    ρ = Deep b (U.meaning s ρ ∷ ρ) × Deep s ρ
    Deeps (U.connectᶜ r b (U.ended c t)) ρ = Deep b (end c ∷ ρ) × Deep t ρ
    Deeps (U.deferᶜ l p ns)               ρ = Headed p × Sorted (U.replay ns ρ) × Alienᴱ p (U.replay ns ρ)
    Deeps (U.endingᶜ p n)                 ρ = Deep n ρ
    Deeps (U.restᶜ n)                     ρ = Deep n ρ
    Deeps (U.unionᶜ x y)                  ρ = Deep x ρ × Deep y ρ
    Deeps (U.burstingᶜ r t)               ρ = Deep t ρ
    Deeps (U.underᶜ (U.live s) b)         ρ = Deep s ρ × Deep b (U.meaning s ρ ∷ ρ)
    Deeps (U.underᶜ (U.ended c t) b)      ρ = Deep t ρ × Deep b (end c ∷ ρ)
    Deeps _                               ρ = ⊤

    Deepᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
    Deepᴹ nothing  ρ = ⊤
    Deepᴹ (just c) ρ = Deep c ρ

    Deepᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
    Deepᴸ []       ρ = ⊤
    Deepᴸ (c ∷ cs) ρ = Deep c ρ × Deepᴸ cs ρ

  -- A gap holds nothing: the stepped node's meaning is the part's with
  -- skips more.  Over an outer whose events run out of order a factory's
  -- lane before `κ` would be reached, and a guarded factory's gap not
  -- hold: the meaning in order, under every rest too.  A joiner's skip
  -- ahead of its rejoined source, under a burst, stops the burst the part
  -- runs on.
  --
  -- REFUTED: 190d13be of the meaning merely `Placed`, by a joiner holding a skip before its source's value, under a burst
  postulate
    gapped-past   : ∀ {κ} {g′ g″ : U.Node [] R} → Gapped κ g′ g″ → Deep g′ [] → Past (residual g′) (residual g″)

  -- A gap is no joiner's end, nor any position's.
  postulate
    gapped-sane   : ∀ {κ} {g′ g″ : U.Node [] R} → Gapped κ g′ g″ → Sane [] g′ → Sane [] g″
    gapped-placed : ∀ {κ} {g′ g″ : U.Node [] R} → Gapped κ g′ g″ → Placed g′ [] → Placed g″ []

  -- What a skip steps to, in order under every rest.  `Placed` and
  -- `Sane` say nothing under a rest, so this reads what neither holds:
  -- the order a run's rests keep belongs in the invariant the machine
  -- carries, beside `Placed`.
  postulate
    stepped-deep : ∀ {g : U.Node [] R} {k g′} → Sane [] g → Placed g [] → U.step g ≡ U.skipˢ k g′ → Deep g′ []
