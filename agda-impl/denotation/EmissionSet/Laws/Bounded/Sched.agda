{-# OPTIONS --guardedness #-}

-- A BOUNDED MERGE'S SCHEDULE, read off its definition alone.  The i-th
-- value lies at one position and later values later; a lane starts at one
-- position; and the lanes before one, counted by their ends, give up a
-- count only to a lane with no end where it is counted.
--
-- Two lanes ending at one position count twice there (`Two`): whether
-- that can happen is a question about where lanes lie, not about the
-- schedule.
module denotation.EmissionSet.Laws.Bounded.Sched where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _∸_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; <⇒≱; <-cmp; m<n⇒m<1+n; n<1+n; m≤n⇒m<n∨m≡n; +-∸-assoc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import denotation.MonotonicList.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; _≺_; _≼_; Den; module Values; module Bounded)
open import denotation.EmissionSet.Laws.Modulus using (≺-irrefl; ≺-trans; ≼-antisym; ≼-or-≻; ≼-≺-≺)
open import denotation.EmissionSet.Laws.Worlds using (InvAt; out-inj)

-- At or before: before, or there.
≼-split : ∀ {x c} → x ≼ c → x ≺ c ⊎ x ≡ c
≼-split {x} {c} le with ≼-or-≻ c x
... | inj₁ cx = inj₂ (≼-antisym {x} {c} le cx)
... | inj₂ xc = inj₁ xc

module Sched {A B : Set} {H : Pos → Set} {p : Pos} (n : ℕ) (f : A → Den B) {O : EmissionSet A} (Io : InvAt H p O) where
  open Bounded n f O
  open Values O using (Nth; first; next)

  ----------------------------------------------------------------------
  -- The values in order

  nth-row : ∀ {i q a} → Nth i q a → O q (out a)
  nth-row (first x _)    = x
  nth-row (next _ x _ _) = x

  -- The i-th value lies at one position ...
  nth-fun : ∀ {i q q′ a a′} → Nth i q a → Nth i q′ a′ → q ≡ q′
  nth-fun {q = q} {q′} (first x m) (first x′ m′) = ≼-antisym {q} {q′} (m x′) (m′ x)
  nth-fun (next nq x lt nx) (next nq′ x′ lt′ nx′) with nth-fun nq nq′
  ... | refl = ≼-antisym (nx x′ lt′) (nx′ x lt)

  -- ... with one value there ...
  nth-val : ∀ {i q a a′} → Nth i q a → Nth i q a′ → a ≡ a′
  nth-val nq nq′ = out-inj (InvAt.func Io (nth-row nq) (nth-row nq′))

  -- ... and later values lie later.
  nth-lt : ∀ {i i′ q q′ a a′} → Nth i q a → Nth i′ q′ a′ → i < i′ → q ≺ q′
  nth-lt nq (first _ _) ()
  nth-lt {q = q} nq (next {q = q₀} n₀ x lt nx) (s≤s le) with m≤n⇒m<n∨m≡n le
  ... | inj₁ lt′ = ≺-trans {q} {q₀} (nth-lt nq n₀ lt′) lt
  ... | inj₂ refl with nth-fun nq n₀
  ...   | refl = lt

  nth-inj : ∀ {i i′ q a a′} → Nth i q a → Nth i′ q a′ → i ≡ i′
  nth-inj {i} {i′} {q} nq nq′ with <-cmp i i′
  ... | tri< lt _ _ = ⊥-elim (≺-irrefl {q} (nth-lt nq nq′ lt))
  ... | tri≈ _ eq _ = eq
  ... | tri> _ _ gt = ⊥-elim (≺-irrefl {q} (nth-lt nq′ nq gt))

  ----------------------------------------------------------------------
  -- Counting ends

  kth-map : ∀ {P P′ : Pos → Set} → (∀ {c} → P c → P′ c) → ∀ ls k → Kth P ls k → Kth P′ ls k
  kth-map g []       k       ()
  kth-map g (l ∷ ls) zero    (inj₁ (c , lc , pc))        = inj₁ (c , lc , g pc)
  kth-map g (l ∷ ls) zero    (inj₂ kk)                   = inj₂ (kth-map g ls zero kk)
  kth-map g (l ∷ ls) (suc k) (inj₁ ((c , lc , pc) , kk)) = inj₁ ((c , lc , g pc) , kth-map g ls k kk)
  kth-map g (l ∷ ls) (suc k) (inj₂ kk)                   = inj₂ (kth-map g ls (suc k) kk)

  kth-down : ∀ {P} ls k → Kth P ls (suc k) → Kth P ls k
  kth-down []       k       ()
  kth-down (l ∷ ls) zero    (inj₁ (h , _))  = inj₁ h
  kth-down (l ∷ ls) zero    (inj₂ kk)       = inj₂ (kth-down ls zero kk)
  kth-down (l ∷ ls) (suc k) (inj₁ (h , kk)) = inj₁ (h , kth-down ls k kk)
  kth-down (l ∷ ls) (suc k) (inj₂ kk)       = inj₂ (kth-down ls (suc k) kk)

  kth-under : ∀ {P} l ls k → Kth P ls k → Kth P (l ∷ ls) k
  kth-under l ls zero    kk = inj₂ kk
  kth-under l ls (suc k) kk = inj₂ kk

  -- A lane gives up at most one of the count.
  kth-pred : ∀ {P} l ls k → Kth P (l ∷ ls) (suc k) → Kth P ls k
  kth-pred l ls k (inj₁ (_ , kk)) = kk
  kth-pred l ls k (inj₂ kk)       = kth-down ls k kk

  -- A lane with no end where `P` holds gives up none.
  kth-skip : ∀ {P} l ls k → ((Σ Pos λ c → l c × P c) → ⊥) → Kth P (l ∷ ls) k → Kth P ls k
  kth-skip l ls zero    no (inj₁ h)       = ⊥-elim (no h)
  kth-skip l ls zero    no (inj₂ kk)      = kk
  kth-skip l ls (suc k) no (inj₁ (h , _)) = ⊥-elim (no h)
  kth-skip l ls (suc k) no (inj₂ kk)      = kk

  -- Two of the lanes end where `P` holds.
  Two : (Pos → Set) → List (Pos → Set) → Set
  Two P []       = ⊥
  Two P (l ∷ ls) = ((Σ Pos λ c → l c × P c) × Kth P ls 0) ⊎ Two P ls

  -- At or before `c`: before it, or one there.
  kth-one : ∀ {c} ls k → Kth (_≼ c) ls k → Kth (_≺ c) ls k ⊎ Kth (_≡ c) ls 0
  kth-one []       k ()
  kth-one (l ∷ ls) zero (inj₁ (x , lx , le)) with ≼-split le
  ... | inj₁ lt = inj₁ (inj₁ (x , lx , lt))
  ... | inj₂ eq = inj₂ (inj₁ (x , lx , eq))
  kth-one (l ∷ ls) zero (inj₂ kk) with kth-one ls zero kk
  ... | inj₁ k′ = inj₁ (inj₂ k′)
  ... | inj₂ e  = inj₂ (inj₂ e)
  kth-one (l ∷ ls) (suc k) (inj₁ ((x , lx , le) , kk)) with ≼-split le
  ... | inj₂ eq = inj₂ (inj₁ (x , lx , eq))
  ... | inj₁ lt with kth-one ls k kk
  ...   | inj₁ k′ = inj₁ (inj₁ ((x , lx , lt) , k′))
  ...   | inj₂ e  = inj₂ (inj₂ e)
  kth-one (l ∷ ls) (suc k) (inj₂ kk) with kth-one ls (suc k) kk
  ... | inj₁ k′ = inj₁ (inj₂ k′)
  ... | inj₂ e  = inj₂ (inj₂ e)

  -- One more at or before `c` than before it: two there.
  kth-split : ∀ {c} ls k → Kth (_≼ c) ls (suc k) → Kth (_≺ c) ls k ⊎ Two (_≡ c) ls
  kth-split []       k ()
  kth-split {c} (l ∷ ls) k (inj₁ ((x , lx , le) , kk)) = go k (≼-split le) kk
    where
      go : ∀ k → x ≺ c ⊎ x ≡ c → Kth (_≼ c) ls k → Kth (_≺ c) (l ∷ ls) k ⊎ Two (_≡ c) (l ∷ ls)
      go k (inj₂ eq) kk with kth-one ls k kk
      ... | inj₁ k′ = inj₁ (kth-under l ls k k′)
      ... | inj₂ e  = inj₂ (inj₁ ((x , lx , eq) , e))
      go zero    (inj₁ lt) kk = inj₁ (inj₁ (x , lx , lt))
      go (suc k) (inj₁ lt) kk with kth-split ls k kk
      ... | inj₁ k′ = inj₁ (inj₁ ((x , lx , lt) , k′))
      ... | inj₂ t  = inj₂ (inj₂ t)
  kth-split (l ∷ ls) k (inj₂ kk) with kth-split ls k kk
  ... | inj₁ k′ = inj₁ (kth-under l ls k k′)
  ... | inj₂ t  = inj₂ (inj₂ t)

  ----------------------------------------------------------------------
  -- The lanes before lane i

  -- A count among the lanes before lane i names one of them.
  sched-lane : ∀ {P} i k → Kth P (Sched i) k → Σ ℕ λ j → j < i × Σ Pos λ c → Ends j (Sched j) c × P c
  sched-lane zero    k       ()
  sched-lane (suc i) zero    (inj₁ (c , e , pc))       = i , n<1+n i , c , e , pc
  sched-lane (suc i) zero    (inj₂ kk) with sched-lane i zero kk
  ... | j , lt , h = j , m<n⇒m<1+n lt , h
  sched-lane (suc i) (suc k) (inj₁ ((c , e , pc) , _)) = i , n<1+n i , c , e , pc
  sched-lane (suc i) (suc k) (inj₂ kk) with sched-lane i (suc k) kk
  ... | j , lt , h = j , m<n⇒m<1+n lt , h

  -- Two of them, the later first.
  sched-two : ∀ {P} i → Two P (Sched i)
            → Σ ℕ λ j → Σ ℕ λ j′ → j′ < j × j < i × (Σ Pos λ c → Ends j (Sched j) c × P c) × (Σ Pos λ c → Ends j′ (Sched j′) c × P c)
  sched-two zero    ()
  sched-two (suc i) (inj₁ (h , kk)) with sched-lane i zero kk
  ... | j′ , lt , h′ = i , j′ , lt , n<1+n i , h , h′
  sched-two (suc i) (inj₂ t) with sched-two i t
  ... | j , j′ , lt , lt′ , h , h′ = j , j′ , lt , m<n⇒m<1+n lt′ , h , h′

  -- A later lane's count, past the lanes between, is lane `suc i`'s.
  peel-to : ∀ {P i} i′ → n ≤ i → i < i′ → Kth P (Sched i′) (i′ ∸ n) → Kth P (Sched (suc i)) (suc i ∸ n)
  peel-to zero ni () kk
  peel-to {P} {i} (suc i′) ni (s≤s le) kk with m≤n⇒m<n∨m≡n le
  ... | inj₂ refl = kk
  ... | inj₁ lt   = peel-to i′ ni lt (kth-pred _ (Sched i′) (i′ ∸ n)
                      (subst (Kth P (Sched (suc i′))) (+-∸-assoc 1 (≤-trans ni (<⇒≤ lt))) kk))

  ----------------------------------------------------------------------
  -- Where a lane starts

  -- A lane starts at one position.
  st-fun : ∀ {i q ls s s′} → Starts i q ls s → Starts i q ls s′ → s ≡ s′
  st-fun (room _)             (room _)             = refl
  st-fun (room lt)            (freed le _)         = ⊥-elim (<⇒≱ lt le)
  st-fun (room lt)            (queued le _ _ _ _)  = ⊥-elim (<⇒≱ lt le)
  st-fun (freed le _)         (room lt)            = ⊥-elim (<⇒≱ lt le)
  st-fun (freed _ _)          (freed _ _)          = refl
  st-fun {ls = ls} (freed _ k) (queued {c} _ qc _ _ nk) = ⊥-elim (nk (kth-map (λ {x} xq → ≺-trans {x} xq qc) ls _ k))
  st-fun (queued le _ _ _ _)  (room lt)            = ⊥-elim (<⇒≱ lt le)
  st-fun {ls = ls} (queued {c} _ qc _ _ nk) (freed _ k) = ⊥-elim (nk (kth-map (λ {x} xq → ≺-trans {x} xq qc) ls _ k))
  st-fun {ls = ls} (queued {c} _ _ _ kc nk) (queued {c′} _ _ _ kc′ nk′) with ≼-or-≻ c′ c
  ... | inj₂ cc′ = ⊥-elim (nk′ (kth-map (λ {x} xc → ≼-≺-≺ {x} {c} {c′} xc cc′) ls _ kc))
  ... | inj₁ c′c with ≼-or-≻ c c′
  ...   | inj₂ c′≺c = ⊥-elim (nk (kth-map (λ {x} xc′ → ≼-≺-≺ {x} {c′} {c} xc′ c′≺c) ls _ kc′))
  ...   | inj₁ cc′ with ≼-antisym {c} {c′} cc′ c′c
  ...     | refl = refl
