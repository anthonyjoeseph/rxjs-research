{-# OPTIONS --guardedness #-}

-- A BOUNDED MERGE KEEPS THE INVARIANT.  A lane starts at its value's
-- second child, or, queued, at the second child of the end that frees it,
-- that end shown silent at its first child.  Following the queue back, a
-- lane's subscription lies in the world of some value's second child, its
-- root, so every lane is subscribed admissibly (`seat`) and its rows keep
-- the lane's invariant.
--
-- Two lanes' subscriptions lie under distinct roots, or the later lies
-- under the second child of an end of the earlier (`rel`).  Either way
-- their rows never meet: apart worlds, or a world under an end the
-- earlier lane's rows stay clear of.
--
-- Lanes start in value order, so a lane never lies under an end a later
-- lane was queued behind (`noback`): two lanes queued at one end would
-- need two earlier lanes ending there, and no two lanes end at one
-- position (`one-end`).
module denotation.Laws.BoundedInv where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (<-cmp; <⇒≱; <⇒≤; ≤-refl; ≤-trans; n≤1+n; n<1+n; m<n⇒m<1+n; ≤-<-trans; <-trans; <-irrefl;
  +-∸-assoc; m∸n+n≡m; m≤n+m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import denotation.Events using (Pos; ix; inside; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Silent; hush; EmissionSet; _≺_; _≼_; Work; Den; enter; After; Truncate; module Values;
  module Bounded)
open import denotation.Laws.Modulus using (≺-trans; ≼-antisym; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (Plain; plain-ix; W; W⁼; step; here; inW; Real; Ok; InvAt; InvD; _⊑_; real-snoc; ok-in; nest;
  nest⁼; nest-in; leads; w-up; not-up; sib; same-lead; flat-under; conv; ⊑-refl; ⊑-snoc; ⊑-snoc⁺; ⊑-inside; inside-⊑; ext≢; out-inj)
open import denotation.Laws.JoinInv using (ix01; ix10; below; module Kids; module Join)
open import denotation.Laws.Nth using (module Nths)

end≢skip : ∀ {C} → Silent {C} end → ⊥
end≢skip ()

-- One end to a reading.
end-uniq : ∀ {C H s} {X : EmissionSet C} → InvAt H s X → ∀ {c c′} → X c end → X c′ end → c ≡ c′
end-uniq I {c} {c′} x x′ with ≼-or-≻ c c′ | ≼-or-≻ c′ c
... | _       | inj₂ lt  = ⊥-elim (end≢skip (InvAt.quiet I x x′ lt))
... | inj₂ lt | _        = ⊥-elim (end≢skip (InvAt.quiet I x′ x lt))
... | inj₁ le | inj₁ le′ = ≼-antisym {c} {c′} le le′

-- A bounded merge of the outer `O` read at `p`.
module BoundedI {A B H p} (ok : Ok H p) (n : ℕ) (f : A → Den B) (fi : ∀ a → InvD H (f a)) {O : EmissionSet A} (Io : InvAt H p O) where
  open Bounded n f O
  open Values O using (Nth; first; next)
  open InvAt Io renaming (world to wo; real to re; func to fu; flat to fl; burst to bu; under to U; quiet to qu)
  open Join ok f fi Io using (sw; kids; kid-root; kid-lane; o-lane; val-lane; o-lead; o-lane-lead; end-before; val-after; module View)
  open View Done (λ _ _ _ → ⊤) using (OEv; o-skip; o-pin; o-end; o-pass; o-nout; o-func; o-skipped)
  open Nths O using (nth-val; nth-fun; nth-lt; nth-inj)

  ------------------------------------------------------------------------
  -- Counting ends

  kth-cons : ∀ {P l ls k} → Kth P ls k → Kth P (l ∷ ls) k
  kth-cons {k = zero}  K = inj₂ K
  kth-cons {k = suc k} K = inj₂ K

  kth-down : ∀ {P} ls {k} → Kth P ls (suc k) → Kth P ls k
  kth-down []       ()
  kth-down (l ∷ ls) {zero}  (inj₁ (h , _)) = inj₁ h
  kth-down (l ∷ ls) {zero}  (inj₂ K)       = inj₂ (kth-down ls K)
  kth-down (l ∷ ls) {suc k} (inj₁ (h , K)) = inj₁ (h , kth-down ls K)
  kth-down (l ∷ ls) {suc k} (inj₂ K)       = inj₂ (kth-down ls K)

  kth-tail : ∀ {P l} ls {k} → Kth P (l ∷ ls) (suc k) → Kth P ls k
  kth-tail ls (inj₁ (_ , K)) = K
  kth-tail ls (inj₂ K)       = kth-down ls K

  kth-mono : ∀ {P Q : Pos → Set} → (∀ {c} → P c → Q c) → ∀ ls {k} → Kth P ls k → Kth Q ls k
  kth-mono g []       ()
  kth-mono g (l ∷ ls) {zero}  (inj₁ (c , lc , pc))       = inj₁ (c , lc , g pc)
  kth-mono g (l ∷ ls) {zero}  (inj₂ K)                   = inj₂ (kth-mono g ls K)
  kth-mono g (l ∷ ls) {suc k} (inj₁ ((c , lc , pc) , K)) = inj₁ ((c , lc , g pc) , kth-mono g ls K)
  kth-mono g (l ∷ ls) {suc k} (inj₂ K)                   = inj₂ (kth-mono g ls K)

  -- A lane before lane i ending where `P` holds.
  data Ending (P : Pos → Set) (i : ℕ) : Set where
    ending : ∀ {j c} → j < i → Ends j (Sched j) c → P c → Ending P i

  ending-up : ∀ {P i} → Ending P i → Ending P (suc i)
  ending-up (ending lt e pc) = ending (m<n⇒m<1+n lt) e pc

  kth-lane : ∀ {P} i {k} → Kth P (Sched i) k → Ending P i
  kth-lane zero    ()
  kth-lane (suc i) {zero}  (inj₁ (c , e , pc))       = ending (n<1+n i) e pc
  kth-lane (suc i) {zero}  (inj₂ K)                  = ending-up (kth-lane i K)
  kth-lane (suc i) {suc k} (inj₁ ((c , e , pc) , _)) = ending (n<1+n i) e pc
  kth-lane (suc i) {suc k} (inj₂ K)                  = ending-up (kth-lane i K)

  split≼ : ∀ {c′ c} → c′ ≼ c → c′ ≺ c ⊎ c′ ≡ c
  split≼ {c′} {c} le with ≼-or-≻ c c′
  ... | inj₁ le′ = inj₂ (≼-antisym {c′} {c} le le′)
  ... | inj₂ lt  = inj₁ lt

  -- With k + 1 ends at or before `c` and not before it, one is at it.
  at-c : ∀ {c} ls k → Kth (_≼ c) ls k → ¬ Kth (_≺ c) ls k → Kth (_≡ c) ls 0
  at-c []       _       ()
  at-c {c} (l ∷ ls) zero    (inj₁ (c′ , lc , le)) nk with split≼ {c′} {c} le
  ... | inj₁ lt = ⊥-elim (nk (inj₁ (c′ , lc , lt)))
  ... | inj₂ eq = inj₁ (c′ , lc , eq)
  at-c (l ∷ ls) zero    (inj₂ K) nk = inj₂ (at-c ls zero K (λ K′ → nk (inj₂ K′)))
  at-c {c} (l ∷ ls) (suc k) (inj₁ ((c′ , lc , le) , K)) nk with split≼ {c′} {c} le
  ... | inj₁ lt = inj₂ (at-c ls k K (λ K′ → nk (inj₁ ((c′ , lc , lt) , K′))))
  ... | inj₂ eq = inj₁ (c′ , lc , eq)
  at-c (l ∷ ls) (suc k) (inj₂ K) nk = inj₂ (at-c ls (suc k) K (λ K′ → nk (inj₂ K′)))

  -- Two lanes before lane i ending at `c`.
  data Two (i : ℕ) (c : Pos) : Set where
    two : ∀ {j₁ j₂} → j₁ < j₂ → j₂ < i → Ends j₁ (Sched j₁) c → Ends j₂ (Sched j₂) c → Two i c

  two-up : ∀ {i c} → Two i c → Two (suc i) c
  two-up (two lt lt′ e e′) = two lt (m<n⇒m<1+n lt′) e e′

  -- With k + 2 ends at or before `c` and not k + 1 before it, two are at it.
  two-at : ∀ i {c} k → Kth (_≼ c) (Sched i) (suc k) → ¬ Kth (_≺ c) (Sched i) k → Two i c
  two-at zero    k ()
  two-at (suc i) k (inj₂ K) nk = two-up (two-at i k K (λ K′ → nk (kth-cons K′)))
  two-at (suc i) {c} zero (inj₁ ((c′ , e′ , le) , K)) nk with split≼ {c′} {c} le
  ... | inj₁ lt = ⊥-elim (nk (inj₁ (c′ , e′ , lt)))
  ... | inj₂ refl with kth-lane i (at-c (Sched i) zero K (λ K′ → nk (kth-cons K′)))
  ...   | ending j<i e refl = two j<i (n<1+n i) e e′
  two-at (suc i) {c} (suc k) (inj₁ ((c′ , e′ , le) , K)) nk with split≼ {c′} {c} le
  ... | inj₁ lt = two-up (two-at i k K (λ K′ → nk (inj₁ ((c′ , e′ , lt) , K′))))
  ... | inj₂ refl with kth-lane i (at-c (Sched i) (suc k) K (λ K′ → nk (kth-cons K′)))
  ...   | ending j<i e refl = two j<i (n<1+n i) e e′

  -- Dropping d lanes drops at most d ends.
  strip : ∀ {P} d i → n ≤ i → Kth P (Sched (d + i)) ((d + i) ∸ n) → Kth P (Sched i) (i ∸ n)
  strip zero        i n≤i K = K
  strip {P} (suc d) i n≤i K =
    strip d i n≤i (kth-tail (Sched (d + i)) (subst (Kth P (Sched (suc (d + i)))) (+-∸-assoc 1 (≤-trans n≤i (m≤n+m i d))) K))

  ------------------------------------------------------------------------
  -- One lane to a value

  starts-fun : ∀ {i q ls s s′} → Starts i q ls s → Starts i q ls s′ → s ≡ s′
  starts-fun (room _)    (room _)    = refl
  starts-fun (room _)    (freed _ _) = refl
  starts-fun (freed _ _) (room _)    = refl
  starts-fun (freed _ _) (freed _ _) = refl
  starts-fun (room i<n) (queued n≤i _ _ _ _) = ⊥-elim (<⇒≱ i<n n≤i)
  starts-fun (queued n≤i _ _ _ _) (room i<n) = ⊥-elim (<⇒≱ i<n n≤i)
  starts-fun {q = q} {ls} (freed _ K) (queued {c} _ qc _ _ nK) = ⊥-elim (nK (kth-mono (λ {c′} lt → ≺-trans {c′} {q} {c} lt qc) ls K))
  starts-fun {q = q} {ls} (queued {c} _ qc _ _ nK) (freed _ K) = ⊥-elim (nK (kth-mono (λ {c′} lt → ≺-trans {c′} {q} {c} lt qc) ls K))
  starts-fun {ls = ls} (queued {c} _ _ _ K nK) (queued {c′} _ _ _ K′ nK′) with ≼-or-≻ c c′ | ≼-or-≻ c′ c
  ... | _       | inj₂ lt  = ⊥-elim (nK′ (kth-mono (λ {x} le → ≼-≺-≺ {x} {c} {c′} le lt) ls K))
  ... | inj₂ lt | _        = ⊥-elim (nK (kth-mono (λ {x} le → ≼-≺-≺ {x} {c′} {c} le lt) ls K′))
  ... | inj₁ le | inj₁ le′ = cong (_++ [ ix 1 ]) (≼-antisym {c} {c′} le le′)

  sub-fun : ∀ {i q q′ s s′ a a′} → Sub i q s a → Sub i q′ s′ a′ → q ≡ q′ × a ≡ a′ × s ≡ s′
  sub-fun (nq , st) (nq′ , st′) with nth-fun nq nq′
  ... | refl = refl , out-inj (fu (nth-val nq) (nth-val nq′)) , starts-fun st st′

  ------------------------------------------------------------------------
  -- Where a lane sits

  -- In the world, reachable, and in the world of the second child of a
  -- value no later than its own.
  data Seat (i : ℕ) (s : Pos) : Set where
    seat′ : ∀ {k r b} → W H p s → Real s → k ≤ i → Nth k r b → W⁼ H (r ++ [ ix 1 ]) s → Seat i s

  LIat : ∀ {s} a → W H p s → Real s → InvAt H s (enter (f a) s)
  LIat {s} a w r = fi a s (ok-in ok w r)

  seat-end : ∀ {i j c a s} → j < i → Seat j s → After (f a) s c end → Seat i (c ++ [ ix 1 ])
  seat-end {c = c} {a} {s} j<i (seat′ w r k≤j nr rw) ac =
    seat′ (nest-in w (inW cw)) (real-snoc c plain-ix (InvAt.real (LIat a w r) (proj₁ ac))) (≤-trans k≤j (<⇒≤ j<i)) nr (nest⁼ rw (inW cw))
    where
      cw : W H s (c ++ [ ix 1 ])
      cw = step (inW (InvAt.world (LIat a w r) (proj₁ ac))) plain-ix

  seat : ∀ {i q s a} → Acc _<_ i → Sub i q s a → Seat i s
  seat {q = q} _ (nq , room _)    = seat′ (sw (nth-val nq)) (real-snoc q plain-ix (re (nth-val nq))) ≤-refl nq here
  seat {q = q} _ (nq , freed _ _) = seat′ (sw (nth-val nq)) (real-snoc q plain-ix (re (nth-val nq))) ≤-refl nq here
  seat {i} (acc rs) (nq , queued _ _ kc _ _) with kth-lane i kc
  ... | ending j<i (_ , _ , _ , nj , stj , ac) refl = seat-end j<i (seat (rs j<i) (nj , stj)) ac

  seat* : ∀ {i q s a} → Sub i q s a → Seat i s
  seat* sb = seat (<-wellFounded _) sb

  okS : ∀ {i q s a} → Sub i q s a → Ok H s
  okS sb with seat* sb
  ... | seat′ w r _ _ _ = ok-in ok w r

  s-w : ∀ {i q s a} → Sub i q s a → W H p s
  s-w sb with seat* sb
  ... | seat′ w _ _ _ _ = w

  LI : ∀ {i q s a} → Sub i q s a → InvAt H s (enter (f a) s)
  LI {s = s} {a} sb = fi a s (okS sb)

  module LK {i q s a} (sb : Sub i q s a) = Kids (okS sb) (LI sb)

  row-w : ∀ {i q s a y e} → Sub i q s a → After (f a) s y e → W H s y
  row-w sb x = InvAt.world (LI sb) (proj₁ x)

  -- An end's second child lies in its lane's world.
  end-w : ∀ {i q s a c e} → Sub i q s a → After (f a) s c e → W H s (c ++ [ ix 1 ])
  end-w sb x = step (inW (row-w sb x)) plain-ix

  lane-end : ∀ {i q s a c c′} → Sub i q s a → After (f a) s c end → After (f a) s c′ end → c ≡ c′
  lane-end sb x x′ = end-uniq (LI sb) (proj₁ x) (proj₁ x′)

  ------------------------------------------------------------------------
  -- Two lanes

  -- Lane at `s` before lane at `s′`: under distinct roots, or `s′` under
  -- an end of the first, queued at.
  data Rel (a : A) (s s′ : Pos) : Set where
    apart : ∀ {r r′ b b′} → O r (out b) → O r′ (out b′) → (r ≡ r′ → ⊥) → W⁼ H (r ++ [ ix 1 ]) s → W⁼ H (r′ ++ [ ix 1 ]) s′ → Rel a s s′
    queued-in : ∀ {c} → After (f a) s c end → Queued c → W⁼ H (c ++ [ ix 1 ]) s′ → Rel a s s′

  RelAt : ℕ → Set
  RelAt i′ = ∀ {i q s a q′ s′ a′} → i < i′ → Sub i q s a → Sub i′ q′ s′ a′ → Rel a s s′

  apart-ww : ∀ {r r′ b b′ w} → O r (out b) → O r′ (out b′) → (r ≡ r′ → ⊥) → W⁼ H (r ++ [ ix 1 ]) w → W⁼ H (r′ ++ [ ix 1 ]) w → ⊥
  apart-ww {r} {r′} xr xr′ ne = kids xr xr′ plain-ix plain-ix (λ eq → ne (∷ʳ-injectiveˡ r r′ eq))

  apart-lead : ∀ {r r′ b b′ w y} → O r (out b) → O r′ (out b′) → (r ≡ r′ → ⊥) → W⁼ H (r ++ [ ix 1 ]) w → W H (r′ ++ [ ix 1 ]) y → w ⊑ y → ⊥
  apart-lead {r} {r′} xr xr′ ne v yw = kid-lane xr plain-ix v xr′ yw (λ eq → ne (∷ʳ-injectiveˡ r r′ eq))

  -- No two lanes end at one position.
  one-end : ∀ {j₁ j₂ c} → RelAt j₂ → j₁ < j₂ → Ends j₁ (Sched j₁) c → Ends j₂ (Sched j₂) c → ⊥
  one-end R lt (_ , _ , _ , n₁ , st₁ , e₁) (_ , _ , _ , n₂ , st₂ , e₂) with R lt (n₁ , st₁) (n₂ , st₂)
  ... | apart xr xr′ ne rw rw′ = apart-ww xr xr′ ne (nest⁼ rw (inW (row-w (n₁ , st₁) e₁))) (nest⁼ rw′ (inW (row-w (n₂ , st₂) e₂)))
  ... | queued-in e _ v with lane-end (n₁ , st₁) e e₁
  ...   | refl = not-up (InvAt.real (LI (n₂ , st₂)) (proj₁ e₂)) (nest⁼ v (inW (row-w (n₂ , st₂) e₂))) (⊑-refl _)

  -- Two lanes queued at one end need two earlier lanes ending there.
  same-c : ∀ {i i′ q a c} → (∀ {m} → m < i′ → RelAt m) → i < i′ → Kth (_≼ c) (Sched i′) (i′ ∸ n)
         → Sub i q (c ++ [ ix 1 ]) a → n ≤ i → ¬ Kth (_≺ c) (Sched i) (i ∸ n) → ⊥
  same-c {i} {i′} {c = c} rec i<i′ Kc sb n≤i nK
    with subst (Kth (_≼ c) (Sched (suc i))) (+-∸-assoc 1 n≤i)
           (strip (i′ ∸ suc i) (suc i) (≤-trans n≤i (n≤1+n i)) (subst (λ m → Kth (_≼ c) (Sched m) (m ∸ n)) (sym (m∸n+n≡m i<i′)) Kc))
  ... | inj₁ ((c′ , (_ , _ , _ , n₁ , st₁ , ac₁) , le) , _) with sub-fun (n₁ , st₁) sb
  ...   | refl , refl , refl = le (≺-trans {c} {c ++ [ ix 1 ]} {c′} (≺-ext c []) (proj₂ ac₁))
  same-c {i} {i′} {c = c} rec i<i′ Kc sb n≤i nK | inj₂ K with two-at i (i ∸ n) K nK
  ... | two j₁<j₂ j₂<i e₁ e₂ = one-end (rec (<-trans j₂<i i<i′)) j₁<j₂ e₁ e₂

  -- A value's second child under a lane's end.
  nb-root : ∀ {j qj sj aj c q a} → Sub j qj sj aj → After (f aj) sj c end → O q (out a) → W⁼ H (c ++ [ ix 1 ]) (q ++ [ ix 1 ]) → ⊥
  nb-root {c = c} {q} {a} sbj ac xq v with seat* sbj
  ... | seat′ _ _ _ nr rw with w-up plain-ix v
  ...   | inj₁ eq = o-lane (subst (λ z → O z (out a)) (sym (∷ʳ-injectiveˡ c q eq)) xq) (nth-val nr) (nest rw (row-w sbj ac))
  ...   | inj₂ v′ = U (nth-val nr) xq plain-ix (nest⁼ rw (inW (nest-in (end-w sbj ac) v′))) (⊑-refl q)

  -- NO LANE BEFORE LANE i′ LIES UNDER THE END i′ IS QUEUED AT.
  noback : ∀ {i′ c j qj sj aj} → (∀ {m} → m < i′ → RelAt m) → Kth (_≼ c) (Sched i′) (i′ ∸ n) → j < i′ → Sub j qj sj aj
         → After (f aj) sj c end → ∀ i → Acc _<_ i → ∀ {q s a} → i < i′ → Sub i q s a → W⁼ H (c ++ [ ix 1 ]) s → ⊥
  noback rec Kc j<i′ sbj ac i _ i<i′ (nq , room _)    v = nb-root sbj ac (nth-val nq) v
  noback rec Kc j<i′ sbj ac i _ i<i′ (nq , freed _ _) v = nb-root sbj ac (nth-val nq) v
  noback {c = c} {j} rec Kc j<i′ sbj ac i (acc rs) i<i′ sb@(nq , queued {ck} n≤i _ kck _ nK) v with w-up plain-ix v
  ... | inj₁ eq with ∷ʳ-injectiveˡ c ck eq
  ...   | refl = same-c rec i<i′ Kc sb n≤i nK
  noback {c = c} {j} rec Kc j<i′ sbj ac i (acc rs) i<i′ sb@(nq , queued {ck} n≤i _ kck _ nK) v | inj₂ v′ with kth-lane i kck
  ... | ending {k} k<i (_ , _ , _ , nk , stk , ack) refl with <-cmp k j
  ...   | tri≈ _ refl _ with sub-fun (nk , stk) sbj
  ...     | refl , refl , refl with lane-end sbj ack ac
  ...       | refl = not-up (InvAt.real (LI sbj) (proj₁ ac)) v′ (⊑-refl _)
  noback {c = c} {j} rec Kc j<i′ sbj ac i (acc rs) i<i′ sb@(nq , queued {ck} n≤i _ kck _ nK) v | inj₂ v′
    | ending {k} k<i (_ , _ , _ , nk , stk , ack) refl | tri< k<j _ _ with rec j<i′ k<j (nk , stk) sbj
  ... | apart xr xr′ ne rwk rwj = apart-ww xr xr′ ne (nest⁼ rwk (inW (row-w (nk , stk) ack))) (nest⁼ rwj (inW (nest-in (end-w sbj ac) v′)))
  ... | queued-in e _ vj = InvAt.under (LI (nk , stk)) (proj₁ e) (proj₁ ack) plain-ix (nest⁼ vj (inW (nest-in (end-w sbj ac) v′))) (⊑-refl _)
  noback {c = c} {j} rec Kc j<i′ sbj ac i (acc rs) i<i′ sb@(nq , queued {ck} n≤i _ kck _ nK) v | inj₂ v′
    | ending {k} k<i (_ , _ , _ , nk , stk , ack) refl | tri> _ _ j<k with rec (<-trans k<i i<i′) j<k sbj (nk , stk)
  ... | apart xr xr′ ne rwj rwk = apart-ww xr xr′ ne (nest⁼ rwj (inW (nest-in (end-w sbj ac) v′))) (nest⁼ rwk (inW (row-w (nk , stk) ack)))
  ... | queued-in e _ vk with lane-end sbj e ac
  ...   | refl = noback rec Kc j<i′ sbj ac k (rs k<i) (<-trans k<i i<i′) (nk , stk) vk

  rel-root : ∀ {i i′ q s a q′ a′} → i < i′ → Sub i q s a → Nth i′ q′ a′ → Rel a s (q′ ++ [ ix 1 ])
  rel-root {q′ = q′} i<i′ sb nq′ with seat* sb
  ... | seat′ {r = r} _ _ k≤i nr rw with r ≟ᵖ q′
  ...   | no ne    = apart (nth-val nr) (nth-val nq′) ne rw here
  ...   | yes refl = ⊥-elim (<-irrefl (nth-inj nr nq′) (≤-<-trans k≤i i<i′))

  lift : ∀ {a s s₁ s₂} → W⁼ H s₁ s₂ → Rel a s s₁ → Rel a s s₂
  lift u (apart xr xr′ ne rw rw′) = apart xr xr′ ne rw (nest⁼ rw′ u)
  lift u (queued-in e Q v)        = queued-in e Q (nest⁼ v u)

  rel′ : ∀ i′ → Acc _<_ i′ → RelAt i′
  rel′ i′ _ i<i′ sb (nq′ , room _)    = rel-root i<i′ sb nq′
  rel′ i′ _ i<i′ sb (nq′ , freed _ _) = rel-root i<i′ sb nq′
  rel′ i′ (acc rs) {i} {q′ = q′} {a′ = a′} i<i′ sb sb′@(nq′ , queued {c} _ _ kc Kc _) with kth-lane i′ kc
  ... | ending {j} j<i′ (_ , _ , _ , nj , stj , ac) refl with <-cmp i j
  ...   | tri< i<j _ _ = lift (inW (end-w (nj , stj) ac)) (rel′ j (rs j<i′) i<j sb (nj , stj))
  ...   | tri≈ _ refl _ with sub-fun sb (nj , stj)
  ...     | refl , refl , refl = queued-in ac (i′ , q′ , a′ , sb′) here
  rel′ i′ (acc rs) {i} {q′ = q′} {a′ = a′} i<i′ sb sb′@(nq′ , queued {c} _ _ kc Kc _) | ending {j} j<i′ (_ , _ , _ , nj , stj , ac) refl
    | tri> _ _ j<i with rel′ i (rs i<i′) j<i (nj , stj) sb
  ... | apart xr xr′ ne rwj rw = apart xr′ xr (λ eq → ne (sym eq)) rw (nest⁼ rwj (inW (end-w (nj , stj) ac)))
  ... | queued-in e _ v with lane-end (nj , stj) e ac
  ...   | refl = ⊥-elim (noback (λ {m} lt → rel′ m (rs lt)) Kc j<i′ (nj , stj) ac i (rs i<i′) i<i′ sb v)

  rel : ∀ {i i′ q s a q′ s′ a′} → i < i′ → Sub i q s a → Sub i′ q′ s′ a′ → Rel a s s′
  rel {i′ = i′} lt sb sb′ = rel′ i′ (<-wellFounded i′) lt sb sb′

  ------------------------------------------------------------------------
  -- A lane's rows the merge shows

  -- Its own, not a queued end; or its queued end's first child.
  data Lr (a : A) (s y : Pos) : Set where
    lr-row  : ∀ {e} → After (f a) s y e → (After (f a) s y end → Queued y → ⊥) → Lr a s y
    lr-hand : ∀ {c} → After (f a) s c end → Queued c → y ≡ c ++ [ ix 0 ] → Lr a s y

  lr-w : ∀ {i q s a y} → Sub i q s a → Lr a s y → W H s y
  lr-w sb (lr-row x _)       = row-w sb x
  lr-w sb (lr-hand x _ refl) = step (inW (row-w sb x)) plain-ix

  lr-real : ∀ {i q s a y} → Sub i q s a → Lr a s y → Real y
  lr-real sb (lr-row x _)            = InvAt.real (LI sb) (proj₁ x)
  lr-real sb (lr-hand {c} x _ refl) = real-snoc c plain-ix (InvAt.real (LI sb) (proj₁ x))

  -- In the world of a value's second child.
  data InRoot (y : Pos) : Set where
    in-root : ∀ {r b} → O r (out b) → W H (r ++ [ ix 1 ]) y → InRoot y

  lr-root : ∀ {i q s a y} → Sub i q s a → Lr a s y → InRoot y
  lr-root sb l with seat* sb
  ... | seat′ _ _ _ nr rw = in-root (nth-val nr) (nest rw (lr-w sb l))

  child-in : ∀ {r i q s a x l w} → W⁼ H r s → Sub i q s a → Lr a s x → Plain l → W⁼ H (x ++ [ l ]) w → W⁼ H r w
  child-in rw sb lx pl v = nest⁼ (nest⁼ rw (inW (step (inW (lr-w sb lx)) pl))) v

  -- One lane's rows.
  same-flat : ∀ {i q s a y l ys} → Sub i q s a → Lr a s y → Lr a s (y ++ l ∷ ys) → ⊥
  same-flat sb (lr-row x _) (lr-row x′ _) = InvAt.flat (LI sb) (proj₁ x) (proj₁ x′)
  same-flat {y = y} {ys = ys} sb (lr-row x nq) (lr-hand x′ Q eq) with same-lead (LI sb) (proj₁ x) (proj₁ x′) (below y ys _ eq)
  ... | refl = nq x′ Q
  same-flat {l = l} {ys} sb (lr-hand x _ refl) (lr-row x′ _) = flat-under (LI sb) (proj₁ x) (proj₁ x′) (l ∷ ys , refl)
  same-flat {ys = ys} sb (lr-hand x _ refl) (lr-hand x′ _ eq) with lane-end sb x x′
  ... | refl = ext≢ _ ys eq

  same-under : ∀ {i q s a x y l w} → Sub i q s a → Lr a s x → Lr a s y → Plain l → W⁼ H (x ++ [ l ]) w → w ⊑ y → ⊥
  same-under sb (lr-row x _) (lr-row y _) pl v le = InvAt.under (LI sb) (proj₁ x) (proj₁ y) pl v le
  same-under {x = x} sb (lr-row x′ nq) (lr-hand {c} y Q refl) pl v le with ⊑-snoc c le
  ... | inj₁ wc = InvAt.under (LI sb) (proj₁ x′) (proj₁ y) pl v wc
  ... | inj₂ refl with w-up plain-ix v
  ...   | inj₂ v′ = InvAt.under (LI sb) (proj₁ x′) (proj₁ y) pl v′ (⊑-refl c)
  ...   | inj₁ eq with ∷ʳ-injectiveˡ x c eq
  ...     | refl = nq y Q
  same-under sb (lr-hand x _ refl) (lr-row y _) pl v le = InvAt.under (LI sb) (proj₁ x) (proj₁ y) plain-ix (nest⁼ (inW (step here pl)) v) le
  same-under sb (lr-hand {c} x _ refl) (lr-hand x′ _ refl) pl v le with lane-end sb x x′
  ... | refl = not-up (real-snoc c plain-ix (InvAt.real (LI sb) (proj₁ x))) v le

  -- A lane's own row, not a queued end, leads no second child of its
  -- queued end.
  row-not-c : ∀ {i q s a c y e} → Sub i q s a → After (f a) s c end → Queued c → After (f a) s y e
            → (After (f a) s y end → Queued y → ⊥) → y ⊑ (c ++ [ ix 1 ]) → ⊥
  row-not-c {c = c} sb ac Q x nq le with ⊑-snoc c le
  ... | inj₂ refl = InvAt.flat (LI sb) (proj₁ ac) (proj₁ x)
  ... | inj₁ yc with same-lead (LI sb) (proj₁ x) (proj₁ ac) yc
  ...   | refl = nq ac Q

  -- Under an end a later lane is queued at, against the end's lane.
  nest-back : ∀ {i q s a c w y} → Sub i q s a → After (f a) s c end → W⁼ H (c ++ [ ix 1 ]) w → Lr a s y → w ⊑ y → ⊥
  nest-back sb ac v (lr-row x _) le = InvAt.under (LI sb) (proj₁ ac) (proj₁ x) plain-ix v le
  nest-back {c = c} sb ac v (lr-hand x _ refl) le with lane-end sb ac x
  ... | refl = sib (InvAt.real (LI sb) (proj₁ ac)) plain-ix (⊑-refl c) (λ eq → ix01 (∷ʳ-injectiveʳ c c eq)) v le

  nest-lead : ∀ {i q s a c y y′} → Sub i q s a → After (f a) s c end → Queued c → Lr a s y → W H (c ++ [ ix 1 ]) y′ → y ⊑ y′ → ⊥
  nest-lead {y = y} sb ac Q (lr-row x nq) yw le =
    leads (proj₁ (okS sb)) (proj₂ (okS sb)) (row-w sb x) (λ u → InvAt.under (LI sb) (proj₁ ac) (proj₁ x) plain-ix u (⊑-refl y))
          (row-not-c sb ac Q x nq) (inW yw) le
  nest-lead {c = c} sb ac Q (lr-hand x _ refl) yw le with lane-end sb ac x
  ... | refl = LK.kid-lane sb (proj₁ ac) plain-ix here (proj₁ ac) yw (λ eq → ix01 (∷ʳ-injectiveʳ c c eq)) le

  nest-under : ∀ {i q s a c x l w y′} → Sub i q s a → After (f a) s c end → Queued c → Lr a s x → Plain l → W⁼ H (x ++ [ l ]) w
             → W H (c ++ [ ix 1 ]) y′ → w ⊑ y′ → ⊥
  nest-under {c = c} {x} sb ac Q (lr-row x′ nq) pl v yw le =
    LK.kid-lane sb (proj₁ x′) pl v (proj₁ ac) yw
      (λ eq → row-not-c sb ac Q x′ nq (subst (_⊑ (c ++ [ ix 1 ])) (sym (∷ʳ-injectiveˡ x c eq)) (⊑-snoc⁺ c))) le
  nest-under {c = c} sb ac Q (lr-hand x _ refl) pl v yw le with lane-end sb ac x
  ... | refl = LK.kid-lane sb (proj₁ ac) plain-ix (nest⁼ (inW (step here pl)) v) (proj₁ ac) yw (λ eq → ix01 (∷ʳ-injectiveʳ c c eq)) le

  -- Two lanes, the first before the second.
  x-lead : ∀ {i q s a i′ q′ s′ a′ y y′} → Sub i q s a → Sub i′ q′ s′ a′ → Rel a s s′ → Lr a s y → Lr a′ s′ y′ → y ⊑ y′ → ⊥
  x-lead sb sb′ (apart xr xr′ ne rw rw′) l l′ = apart-lead xr xr′ ne (inW (nest rw (lr-w sb l))) (nest rw′ (lr-w sb′ l′))
  x-lead sb sb′ (queued-in ac Q v)       l l′ = nest-lead sb ac Q l (nest v (lr-w sb′ l′))

  x-back : ∀ {i q s a i′ q′ s′ a′ y y′} → Sub i q s a → Sub i′ q′ s′ a′ → Rel a s s′ → Lr a s y → Lr a′ s′ y′ → y′ ⊑ y → ⊥
  x-back sb sb′ (apart xr xr′ ne rw rw′) l l′ = apart-lead xr′ xr (λ eq → ne (sym eq)) (inW (nest rw′ (lr-w sb′ l′))) (nest rw (lr-w sb l))
  x-back sb sb′ (queued-in ac Q v)       l l′ = nest-back sb ac (inW (nest v (lr-w sb′ l′))) l

  x-under : ∀ {i q s a i′ q′ s′ a′ x y′ l w} → Sub i q s a → Sub i′ q′ s′ a′ → Rel a s s′ → Lr a s x → Lr a′ s′ y′
          → Plain l → W⁼ H (x ++ [ l ]) w → w ⊑ y′ → ⊥
  x-under sb sb′ (apart xr xr′ ne rw rw′) lx l′ pl v = apart-lead xr xr′ ne (child-in rw sb lx pl v) (nest rw′ (lr-w sb′ l′))
  x-under sb sb′ (queued-in ac Q v₁)      lx l′ pl v = nest-under sb ac Q lx pl v (nest v₁ (lr-w sb′ l′))

  x-under′ : ∀ {i q s a i′ q′ s′ a′ x y l w} → Sub i q s a → Sub i′ q′ s′ a′ → Rel a s s′ → Lr a′ s′ x → Lr a s y
           → Plain l → W⁼ H (x ++ [ l ]) w → w ⊑ y → ⊥
  x-under′ sb sb′ (apart xr xr′ ne rw rw′) lx ly pl v = apart-lead xr′ xr (λ eq → ne (sym eq)) (child-in rw′ sb′ lx pl v) (nest rw (lr-w sb ly))
  x-under′ sb sb′ (queued-in ac Q v₁)      lx ly pl v = nest-back sb ac (child-in v₁ sb′ lx pl v) ly

  ------------------------------------------------------------------------
  -- The view

  -- What a lane's row shows.
  data LEv (a : A) (s y : Pos) : Ev B → Set where
    l-work : ∀ {e} → After (f a) s y e → Work e → LEv a s y e
    l-end  : After (f a) s y end → ¬ Queued y → Done y → LEv a s y end
    l-pass : After (f a) s y end → ¬ Queued y → ¬ Done y → LEv a s y skip
    l-hand : ∀ {c} → After (f a) s c end → Queued c → y ≡ c ++ [ ix 0 ] → LEv a s y skip

  data V (y : Pos) : Ev B → Set where
    v-o   : ∀ {e₀ e} → O y e₀ → OEv y e₀ e → V y e
    v-val : ∀ {q a} → O q (out a) → y ≡ q ++ [ ix 0 ] → V y skip
    v-l   : ∀ {i q s a e} → Sub i q s a → LEv a s y e → V y e

  vw : ∀ {y e} → JoinT y e → V y e
  vw (val x)                           = v-val x refl
  vw (step x)                          = v-o x o-skip
  vw (opin x)                          = v-o x o-pin
  vw (oend x d)                        = v-o x (o-end d)
  vw (opass x nd)                      = v-o x (o-pass nd)
  vw (lane _ _ (_ , _ , sb , l) _ w)     = v-l sb (l-work l w)
  vw (hand _ _ (_ , _ , sb , l) _ Q)     = v-l sb (l-hand l Q refl)
  vw (lend _ _ (_ , _ , sb , l) _ nQ d)  = v-l sb (l-end l nQ d)
  vw (lpass _ _ (_ , _ , sb , l) _ nQ nd) = v-l sb (l-pass l nQ nd)
  vw (left _ _ (_ , _ , sb , l) _ _)   = v-l sb (l-work l tt)
  vw (run () _)
  vw (rend () _ _)
  vw (rpass () _ _)
  vw (rhand () _)

  work-end : ∀ {e : Ev B} → Work e → e ≡ end → ⊥
  work-end w refl = w

  lr : ∀ {i q s a y e} → Sub i q s a → LEv a s y e → Lr a s y
  lr sb (l-work x w)     = lr-row x (λ x′ _ → work-end w (InvAt.func (LI sb) (proj₁ x) (proj₁ x′)))
  lr sb (l-end x nQ _)   = lr-row x (λ _ Q → nQ Q)
  lr sb (l-pass x nQ _)  = lr-row x (λ _ Q → nQ Q)
  lr sb (l-hand x Q eq)  = lr-hand x Q eq

  l-func : ∀ {i q s a y e e′} → Sub i q s a → LEv a s y e → LEv a s y e′ → e ≡ e′
  l-func sb (l-work x _)       (l-work x′ _)      = InvAt.func (LI sb) (proj₁ x) (proj₁ x′)
  l-func sb (l-work x _)       (l-end x′ _ _)     = InvAt.func (LI sb) (proj₁ x) (proj₁ x′)
  l-func sb (l-work x w)       (l-pass x′ _ _)    = ⊥-elim (work-end w (InvAt.func (LI sb) (proj₁ x) (proj₁ x′)))
  l-func sb (l-work x _)       (l-hand x′ _ refl) = ⊥-elim (flat-under (LI sb) (proj₁ x′) (proj₁ x) (⊑-refl _))
  l-func sb (l-end x _ _)      (l-work x′ _)      = InvAt.func (LI sb) (proj₁ x) (proj₁ x′)
  l-func sb (l-end _ _ _)      (l-end _ _ _)      = refl
  l-func sb (l-end _ _ d)      (l-pass _ _ nd)    = ⊥-elim (nd d)
  l-func sb (l-end x _ _)      (l-hand x′ _ refl) = ⊥-elim (flat-under (LI sb) (proj₁ x′) (proj₁ x) (⊑-refl _))
  l-func sb (l-pass x _ _)     (l-work x′ w)      = ⊥-elim (work-end w (sym (InvAt.func (LI sb) (proj₁ x) (proj₁ x′))))
  l-func sb (l-pass _ _ nd)    (l-end _ _ d)      = ⊥-elim (nd d)
  l-func sb (l-pass _ _ _)     (l-pass _ _ _)     = refl
  l-func sb (l-pass _ _ _)     (l-hand _ _ _)     = refl
  l-func sb (l-hand x _ refl)  (l-work x′ _)      = ⊥-elim (flat-under (LI sb) (proj₁ x) (proj₁ x′) (⊑-refl _))
  l-func sb (l-hand x _ refl)  (l-end x′ _ _)     = ⊥-elim (flat-under (LI sb) (proj₁ x) (proj₁ x′) (⊑-refl _))
  l-func sb (l-hand _ _ _)     (l-pass _ _ _)     = refl
  l-func sb (l-hand _ _ _)     (l-hand _ _ _)     = refl

  func-ll : ∀ {i q s a i′ q′ s′ a′ y e e′} → Sub i q s a → LEv a s y e → Sub i′ q′ s′ a′ → LEv a′ s′ y e′ → e ≡ e′
  func-ll {i} {i′ = i′} {y = y} sb lv sb′ lv′ with <-cmp i i′
  ... | tri< lt _ _ = ⊥-elim (x-lead sb sb′ (rel lt sb sb′) (lr sb lv) (lr sb′ lv′) (⊑-refl y))
  ... | tri> _ _ gt = ⊥-elim (x-lead sb′ sb (rel gt sb′ sb) (lr sb′ lv′) (lr sb lv) (⊑-refl y))
  ... | tri≈ _ refl _ with sub-fun sb sb′
  ...   | refl , refl , refl = l-func sb lv lv′

  flat-ll : ∀ {i q s a i′ q′ s′ a′ y l ys e e′} → Sub i q s a → LEv a s y e → Sub i′ q′ s′ a′ → LEv a′ s′ (y ++ l ∷ ys) e′ → ⊥
  flat-ll {i} {i′ = i′} {l = l} {ys} sb lv sb′ lv′ with <-cmp i i′
  ... | tri< lt _ _ = x-lead sb sb′ (rel lt sb sb′) (lr sb lv) (lr sb′ lv′) (l ∷ ys , refl)
  ... | tri> _ _ gt = x-back sb′ sb (rel gt sb′ sb) (lr sb′ lv′) (lr sb lv) (l ∷ ys , refl)
  ... | tri≈ _ refl _ with sub-fun sb sb′
  ...   | refl , refl , refl = same-flat sb (lr sb lv) (lr sb lv′)

  under-ll : ∀ {i q s a i′ q′ s′ a′ x y l w e e′} → Sub i q s a → LEv a s x e → Sub i′ q′ s′ a′ → LEv a′ s′ y e′
           → Plain l → W⁼ H (x ++ [ l ]) w → w ⊑ y → ⊥
  under-ll {i} {i′ = i′} sb lv sb′ lv′ pl v le with <-cmp i i′
  ... | tri< lt _ _ = x-under sb sb′ (rel lt sb sb′) (lr sb lv) (lr sb′ lv′) pl v le
  ... | tri> _ _ gt = x-under′ sb′ sb (rel gt sb′ sb) (lr sb lv) (lr sb′ lv′) pl v le
  ... | tri≈ _ refl _ with sub-fun sb sb′
  ...   | refl , refl , refl = same-under sb (lr sb lv) (lr sb lv′) pl v le

  world-v : ∀ {y e} → V y e → W H p y
  world-v (v-o x _)      = wo x
  world-v (v-val x refl) = step (inW (wo x)) plain-ix
  world-v (v-l sb lv)    = nest-in (s-w sb) (inW (lr-w sb (lr sb lv)))

  real-v : ∀ {y e} → V y e → Real y
  real-v (v-o x _)          = re x
  real-v (v-val {q} x refl) = real-snoc q plain-ix (re x)
  real-v (v-l sb lv)        = lr-real sb (lr sb lv)

  func-v : ∀ {y e e′} → V y e → V y e′ → e ≡ e′
  func-v (v-o x ev)     (v-o x′ ev′) with fu x x′
  ... | refl = o-func ev ev′
  func-v (v-o x _)      (v-val x′ refl) = ⊥-elim (fl x′ x)
  func-v (v-o x _)      (v-l sb lv) with lr-root sb (lr sb lv)
  ... | in-root xr yw = ⊥-elim (o-lane x xr yw)
  func-v (v-val x refl) (v-o x′ _)      = ⊥-elim (fl x x′)
  func-v (v-val _ _)    (v-val _ _)     = refl
  func-v (v-val x refl) (v-l sb lv) with lr-root sb (lr sb lv)
  ... | in-root xr yw = ⊥-elim (val-lane x xr yw)
  func-v (v-l sb lv)    (v-o x′ _) with lr-root sb (lr sb lv)
  ... | in-root xr yw = ⊥-elim (o-lane x′ xr yw)
  func-v (v-l sb lv)    (v-val x′ refl) with lr-root sb (lr sb lv)
  ... | in-root xr yw = ⊥-elim (val-lane x′ xr yw)
  func-v (v-l sb lv)    (v-l sb′ lv′)   = func-ll sb lv sb′ lv′

  flat-v : ∀ {y e l ys e′} → V y e → V (y ++ l ∷ ys) e′ → ⊥
  flat-v (v-o x _) (v-o x′ _) = fl x x′
  flat-v {y} {ys = ys} (v-o x ev) (v-val x′ eq) = o-lead x (o-nout ev x) x′ (below y ys _ eq)
  flat-v {l = l} {ys} (v-o x ev) (v-l sb lv) with lr-root sb (lr sb lv)
  ... | in-root xr yw = o-lane-lead x (o-nout ev x) xr yw (l ∷ ys , refl)
  flat-v {l = l} {ys} (v-val x refl) (v-o x′ _) = flat-under Io {a = ix 0} x x′ (l ∷ ys , refl)
  flat-v {ys = ys} (v-val {q} x refl) (v-val x′ eq) = flat-under Io {a = ix 0} x x′ (below (q ++ [ ix 0 ]) ys _ eq)
  flat-v {l = l} {ys} (v-val x refl) (v-l sb lv) with lr-root sb (lr sb lv)
  ... | in-root xr yw = kid-lane x plain-ix here xr yw (λ eq → ix01 (∷ʳ-injectiveʳ _ _ eq)) (l ∷ ys , refl)
  flat-v {l = l} {ys} (v-l sb lv) (v-o x′ _) with lr-root sb (lr sb lv)
  ... | in-root xr yw = U xr x′ plain-ix (inW yw) (l ∷ ys , refl)
  flat-v {y} {ys = ys} (v-l sb lv) (v-val x′ eq) with lr-root sb (lr sb lv)
  ... | in-root xr yw = U xr x′ plain-ix (inW yw) (below y ys _ eq)
  flat-v (v-l sb lv) (v-l sb′ lv′) = flat-ll sb lv sb′ lv′

  -- Under a value's first child.
  val-under : ∀ {q a w l y e′} → O q (out a) → W⁼ H ((q ++ [ ix 0 ]) ++ [ l ]) w → W⁼ H (q ++ [ ix 0 ]) w → V y e′ → w ⊑ y → ⊥
  val-under xq v v₀ (v-o oy _) le = U xq oy plain-ix v₀ le
  val-under {q} xq v v₀ (v-val {q′} xq′ refl) le with ⊑-snoc q′ le
  ... | inj₁ wq = U xq xq′ plain-ix v₀ wq
  ... | inj₂ refl with w-up plain-ix v₀
  ...   | inj₁ eq = not-up (real-snoc q plain-ix (re xq)) v (subst (λ z → (q′ ++ [ ix 0 ]) ⊑ z) (sym eq) (⊑-refl _))
  ...   | inj₂ v′ = U xq xq′ plain-ix v′ (⊑-refl q′)
  val-under xq v v₀ (v-l sb lv) le with lr-root sb (lr sb lv)
  ... | in-root xr yw = kid-lane xq plain-ix v₀ xr yw (λ eq → ix01 (∷ʳ-injectiveʳ _ _ eq)) le

  under-v : ∀ {x y w l e e′} → V x e → V y e′ → Plain l → W⁼ H (x ++ [ l ]) w → w ⊑ y → ⊥
  under-v (v-o ox _) (v-o oy _) pl v le = U ox oy pl v le
  under-v {x} (v-o ox ev) (v-val xq refl) pl v le =
    kid-root ox pl v xq plain-ix (λ eq → o-nout ev ox (subst (λ z → O z (out _)) (sym (∷ʳ-injectiveˡ x _ eq)) xq)) le
  under-v {x} (v-o ox ev) (v-l sb lv) pl v le with lr-root sb (lr sb lv)
  ... | in-root xr yw = kid-lane ox pl v xr yw (λ eq → o-nout ev ox (subst (λ z → O z (out _)) (sym (∷ʳ-injectiveˡ x _ eq)) xr)) le
  under-v (v-val xq refl) vy pl v le = val-under xq v (nest⁼ (inW (step here pl)) v) vy le
  under-v (v-l sb lv) (v-o oy _) pl v le with lr-root sb (lr sb lv)
  ... | in-root xr xw = U xr oy plain-ix (nest⁼ (inW (step (inW xw) pl)) v) le
  under-v (v-l sb lv) (v-val xq′ refl) pl v le with lr-root sb (lr sb lv)
  ... | in-root xr xw = kid-root xr plain-ix (nest⁼ (inW (step (inW xw) pl)) v) xq′ plain-ix (λ eq → ix10 (∷ʳ-injectiveʳ _ _ eq)) le
  under-v (v-l sb lv) (v-l sb′ lv′) pl v le = under-ll sb lv sb′ lv′ pl v le

  ------------------------------------------------------------------------
  -- After an end

  done-v : ∀ {c} → V c end → Done c
  done-v (v-o _ (o-end d))     = d
  done-v (v-l _ (l-end _ _ d)) = d
  done-v (v-l _ (l-work _ ()))

  -- A lane begun before the merge's end has ended by it.
  lane-done : ∀ {c i q s a} → Done c → Sub i q s a → Σ Pos λ c′ → After (f a) s c′ end × c′ ≼ c
  lane-done {c} {i} {q} {a = a} ((c₀ , oc , le) , ln) sb
    with ln (nth-val (proj₁ sb)) (i , a , proj₁ sb) (≺-≼-≺ {q} {c₀} {c} (end-before oc (nth-val (proj₁ sb))) le) (λ ())
  ... | c′ , (_ , _ , sb₁ , x) , le′ with nth-inj (proj₁ sb₁) (proj₁ sb)
  ...   | refl with sub-fun sb₁ sb
  ...     | refl , refl , refl = c′ , x , le′

  row-burst : ∀ {i q s a c c′ y e} → Sub i q s a → After (f a) s c′ end → c′ ≼ c → After (f a) s y e → c ≺ y
            → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
  row-burst {c = c} {c′} {y} sb ac le x cy with InvAt.burst (LI sb) (proj₁ ac) (proj₁ x) (≼-≺-≺ {c′} {c} {y} le cy)
  ... | w , w⁼ , i₁ , i₂ = w , nest⁼ (inW (s-w sb)) w⁼ , ⊑-inside (conv {w} {c′} {c} {y} (inside-⊑ w c′ i₁) le cy (inside-⊑ w y i₂)) , i₂

  lane-burst : ∀ {i q s a c c′ y e} → Sub i q s a → After (f a) s c′ end → c′ ≼ c → LEv a s y e → c ≺ y
             → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
  lane-burst sb ac le (l-work x _)   cy = row-burst sb ac le x cy
  lane-burst sb ac le (l-end x _ _)  cy = row-burst sb ac le x cy
  lane-burst sb ac le (l-pass x _ _) cy = row-burst sb ac le x cy
  lane-burst {c = c} {c′} sb ac le (l-hand x _ refl) cy with lane-end sb ac x
  ... | refl = c′ , inW (nest-in (s-w sb) (inW (row-w sb ac))) ,
               ⊑-inside (conv {c′} {c′} {c} {c′ ++ [ ix 0 ]} (⊑-refl c′) le cy (⊑-snoc⁺ c′)) , ⊑-inside (⊑-snoc⁺ c′)

  burst-v : ∀ {c y e} → V c end → V y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
  burst-v vc vy = go (done-v vc) vy
    where
      go : ∀ {c y e} → Done c → V y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
      go {c} {y} ((c₀ , oc , le) , _) (v-o oy _) cy with bu oc oy (≼-≺-≺ {c₀} {c} {y} le cy)
      ... | w , w⁼ , i₁ , i₂ = w , w⁼ , ⊑-inside (conv {w} {c₀} {c} {y} (inside-⊑ w c₀ i₁) le cy (inside-⊑ w y i₂)) , i₂
      go {c} {y} ((c₀ , oc , le) , _) (v-val xq eq) cy = ⊥-elim (val-after oc xq (subst (c₀ ≺_) eq (≼-≺-≺ {c₀} {c} {y} le cy)))
      go d (v-l sb lv) cy with lane-done d sb
      ... | c′ , ac , le = lane-burst sb ac le lv cy

  quiet-v : ∀ {c y e} → V c end → V y e → c ≺ y → Silent e
  quiet-v vc vy = go (done-v vc) vy
    where
      go : ∀ {c y e} → Done c → V y e → c ≺ y → Silent e
      go {c} {y} ((c₀ , oc , le) , _) (v-o oy ev) cy = o-skipped (qu oc oy (≼-≺-≺ {c₀} {c} {y} le cy)) ev
      go _ (v-val _ _) _ = hush
      go {c} {y} d (v-l sb (l-work x _)) cy with lane-done d sb
      ... | c′ , ac , le = InvAt.quiet (LI sb) (proj₁ ac) (proj₁ x) (≼-≺-≺ {c′} {c} {y} le cy)
      go {c} {y} d (v-l sb (l-end x _ _)) cy with lane-done d sb
      ... | c′ , ac , le = ⊥-elim (end≢skip (InvAt.quiet (LI sb) (proj₁ ac) (proj₁ x) (≼-≺-≺ {c′} {c} {y} le cy)))
      go _ (v-l _ (l-pass _ _ _)) _ = hush
      go _ (v-l _ (l-hand _ _ _)) _ = hush

  pinned-v : ∀ {y r} → V y (pin r) → W⁼ H p r × T (inside r y)
  pinned-v (v-o x o-pin)            = InvAt.pinned Io x
  pinned-v (v-l sb (l-work x _)) with InvAt.pinned (LI sb) (proj₁ x)
  ... | w⁼ , i = nest⁼ (inW (s-w sb)) w⁼ , i

  inv : InvAt H p (Truncate JoinT)
  inv = record
    { world = λ x → world-v (vw (proj₁ x))
    ; real  = λ x → real-v (vw (proj₁ x))
    ; func  = λ x x′ → func-v (vw (proj₁ x)) (vw (proj₁ x′))
    ; flat  = λ x x′ → flat-v (vw (proj₁ x)) (vw (proj₁ x′))
    ; burst = λ c y cy → burst-v (vw (proj₁ c)) (vw (proj₁ y)) cy
    ; under = λ x y pl v le → under-v (vw (proj₁ x)) (vw (proj₁ y)) pl v le
    ; quiet = λ c y cy → quiet-v (vw (proj₁ c)) (vw (proj₁ y)) cy
    ; pinned = λ x → pinned-v (vw (proj₁ x))
    }
