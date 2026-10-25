{-# OPTIONS --guardedness #-}

-- TAILS JOINED: a merge's pool joins the tails its parts leave in the
-- order they ended, the engine's in the order its lanes sit.  Joined
-- tails regroup freely (`∪-assocᵀ`); two tails each in position order
-- join the same either way round (`∪-commᵀ`).  Out of order they need
-- not: a tie takes the right-hand tail's step first, so `2 2` joined
-- with `2 1` is not `2 1` joined with `2 2`.
module adequacy.Engine.Union where

open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import denotation.MonotonicList.Events using (Tail; Tail∞; pin; idle; _∪_; first; sooner; _<ᵖ_; <ᵖ-trans; <ᵖ-asym; <ᵖ-irrefl; <ᵖ-split;
  ≮-trans)
open import denotation.MonotonicList using (Agreeᵀ; stopᵀ; pin⁼; idle⁼; agreeᵀ-refl; agreeᵀ-sym; agreeᵀ-trans)
open import denotation.NonExpansive using (∪-ne)
open import adequacy.Placed.Trail using (SortedT; sortedᵀ)
open import adequacy.Placed.Rising using (AtopT)
open Tail∞

-- A tail joined to none.
∪-idleᵀ : ∀ n (t : Tail) → Agreeᵀ n (t ∪ idle) t
∪-idleᵀ zero    t         = stopᵀ
∪-idleᵀ (suc n) idle      = idle⁼
∪-idleᵀ (suc n) (pin k r) = pin⁼ (∪-idleᵀ n (later r))

private
  conv : ∀ {n x x′ y y′} → x ≡ x′ → y ≡ y′ → Agreeᵀ n x y → Agreeᵀ n x′ y′
  conv refl refl a = a

  -- A join headed by a pin, at the race its head runs.
  st : ∀ {m} k {r} u {β} → sooner k u ≡ β → Agreeᵀ m (pin k r ∪ u) (first k r u β)
  st k {r} u e = conv (sym (cong (first k r u) e)) refl (agreeᵀ-refl _ _)

  st′ : ∀ {m k r u β} → sooner k u ≡ β → Agreeᵀ m (pin k r ∪ u) (first k r u β)
  st′ {k = k} {r} {u} e = st k {r} u e

  clash : ∀ {A : Set} {b} → b ≡ true → b ≡ false → A
  clash refl ()

  soon-first : ∀ a b s v β → a <ᵖ b ≡ true → sooner a v ≡ true → sooner a (first b s v β) ≡ true
  soon-first a b s v         true  e₁ e₂ = e₁
  soon-first a b s idle      false e₁ e₂ = e₁
  soon-first a b s (pin c w) false e₁ e₂ = e₂

  soon-∪ : ∀ a u v → sooner a u ≡ true → sooner a v ≡ true → sooner a (u ∪ v) ≡ true
  soon-∪ a idle      v e₁ e₂ = e₂
  soon-∪ a (pin b s) v e₁ e₂ = soon-first a b s v (sooner b v) e₁ e₂

-- Joined tails regroup: whichever order the joins run in, each step is
-- the latest-joined of the soonest heads.
mutual
  ∪-assocᵀ : ∀ n t u v → Agreeᵀ n ((t ∪ u) ∪ v) (t ∪ (u ∪ v))
  ∪-assocᵀ zero    t         u         v         = stopᵀ
  ∪-assocᵀ (suc n) idle      u         v         = agreeᵀ-refl (suc n) (u ∪ v)
  ∪-assocᵀ (suc n) (pin a r) idle      v         = ∪-ne (∪-idleᵀ (suc n) (pin a r)) (agreeᵀ-refl (suc n) v)
  ∪-assocᵀ (suc n) (pin a r) (pin b s) idle      =
    agreeᵀ-trans (∪-idleᵀ (suc n) (pin a r ∪ pin b s)) (∪-ne (agreeᵀ-refl (suc n) (pin a r)) (agreeᵀ-sym (∪-idleᵀ (suc n) (pin b s))))
  ∪-assocᵀ (suc n) (pin a r) (pin b s) (pin c w) = assoc-pin n a r b s c w (a <ᵖ b) (b <ᵖ c) (a <ᵖ c) refl refl refl

  assoc-pin : ∀ n a r b s c w x y z → a <ᵖ b ≡ x → b <ᵖ c ≡ y → a <ᵖ c ≡ z
            → Agreeᵀ (suc n) ((pin a r ∪ pin b s) ∪ pin c w) (pin a r ∪ (pin b s ∪ pin c w))
  assoc-pin n a r b s c w true y true ex ey ez =
    agreeᵀ-trans (∪-ne (st a (pin b s) ex) (agreeᵀ-refl _ (pin c w)))
      (agreeᵀ-trans (st a (pin c w) ez)
        (agreeᵀ-trans (pin⁼ (∪-assocᵀ n (later r) (pin b s) (pin c w)))
          (agreeᵀ-sym (st a (pin b s ∪ pin c w) (soon-∪ a (pin b s) (pin c w) ex ez)))))
  assoc-pin n a r b s c w true true false ex ey ez = clash (<ᵖ-trans a b c ex ey) ez
  assoc-pin n a r b s c w true false false ex ey ez =
    agreeᵀ-trans (∪-ne (st a (pin b s) ex) (agreeᵀ-refl _ (pin c w)))
      (agreeᵀ-trans (st a (pin c w) ez)
        (agreeᵀ-trans (pin⁼ (agreeᵀ-trans (∪-ne (agreeᵀ-sym (st a (pin b s) ex)) (agreeᵀ-refl _ (later w)))
                                           (∪-assocᵀ n (pin a r) (pin b s) (later w))))
          (agreeᵀ-sym (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ (pin a r)) (st b (pin c w) ey)) (st′ ez)))))
  assoc-pin n a r b s c w false true z ex ey ez =
    agreeᵀ-trans (∪-ne (st a (pin b s) ex) (agreeᵀ-refl _ (pin c w)))
      (agreeᵀ-trans (st′ ey)
        (agreeᵀ-trans (pin⁼ (∪-assocᵀ n (pin a r) (later s) (pin c w)))
          (agreeᵀ-sym (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ (pin a r)) (st b (pin c w) ey)) (st′ ex)))))
  assoc-pin n a r b s c w false false true ex ey ez = clash ez (≮-trans c b a ey ex)
  assoc-pin n a r b s c w false false false ex ey ez =
    agreeᵀ-trans (∪-ne (st a (pin b s) ex) (agreeᵀ-refl _ (pin c w)))
      (agreeᵀ-trans (st′ ey)
        (agreeᵀ-trans (pin⁼ (agreeᵀ-trans (∪-ne (agreeᵀ-sym (st a (pin b s) ex)) (agreeᵀ-refl _ (later w)))
                                           (∪-assocᵀ n (pin a r) (pin b s) (later w))))
          (agreeᵀ-sym (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ (pin a r)) (st b (pin c w) ey)) (st′ ez)))))

-- Two tails in position order join the same either way round: on a tie
-- each side's head leads its own rest and the other side (`front`), so
-- either head goes first.
mutual
  ∪-commᵀ : ∀ n t u → SortedT t → SortedT u → Agreeᵀ n (t ∪ u) (u ∪ t)
  ∪-commᵀ zero    t         u         st su = stopᵀ
  ∪-commᵀ (suc n) idle      u         st su = agreeᵀ-sym (∪-idleᵀ (suc n) u)
  ∪-commᵀ (suc n) (pin a r) idle      st su = ∪-idleᵀ (suc n) (pin a r)
  ∪-commᵀ (suc n) (pin a r) (pin b s) st su = comm-pin n a r b s st su (a <ᵖ b) (b <ᵖ a) refl refl

  comm-pin : ∀ n a r b s → SortedT (pin a r) → SortedT (pin b s) → ∀ x y → a <ᵖ b ≡ x → b <ᵖ a ≡ y
           → Agreeᵀ (suc n) (pin a r ∪ pin b s) (pin b s ∪ pin a r)
  comm-pin n a r b s sr ss true  true  ex ey = clash ey (<ᵖ-asym a b ex)
  comm-pin n a r b s sr ss true  false ex ey =
    agreeᵀ-trans (st a (pin b s) ex)
      (agreeᵀ-trans (pin⁼ (∪-commᵀ n (later r) (pin b s) (proj₂ (sortedᵀ sr)) ss)) (agreeᵀ-sym (st b (pin a r) ey)))
  comm-pin n a r b s sr ss false true  ex ey =
    agreeᵀ-trans (st a (pin b s) ex)
      (agreeᵀ-trans (pin⁼ (∪-commᵀ n (pin a r) (later s) sr (proj₂ (sortedᵀ ss)))) (agreeᵀ-sym (st b (pin a r) ey)))
  comm-pin n a r b s sr ss false false ex ey with <ᵖ-split a b ey
  ... | inj₁ lt   = clash lt ex
  ... | inj₂ refl =
    agreeᵀ-trans (st a (pin a s) ex)
      (agreeᵀ-trans (pin⁼ (agreeᵀ-trans (front n a r (later s) sr (proj₂ (sortedᵀ ss)) (proj₁ (sortedᵀ ss)))
                            (agreeᵀ-trans (pin-c n a r s (proj₂ (sortedᵀ sr)) (proj₂ (sortedᵀ ss)))
                              (agreeᵀ-sym (front n a s (later r) ss (proj₂ (sortedᵀ sr)) (proj₁ (sortedᵀ sr)))))))
        (agreeᵀ-sym (st a (pin a r) ey)))

  -- A head no later than a tail's goes first, ahead of its own rest.
  front : ∀ n a r u → SortedT (pin a r) → SortedT u → AtopT a u → Agreeᵀ n (pin a r ∪ u) (first a r u true)
  front zero    a r u         sr su au = stopᵀ
  front (suc n) a r idle      sr su au = agreeᵀ-refl (suc n) (pin a r ∪ idle)
  front (suc n) a r (pin b s) sr su au with <ᵖ-split a b au
  ... | inj₁ lt   = st a (pin b s) lt
  ... | inj₂ refl =
    agreeᵀ-trans (st a (pin a s) (<ᵖ-irrefl a))
      (pin⁼ (agreeᵀ-trans (front n a r (later s) sr (proj₂ (sortedᵀ su)) (proj₁ (sortedᵀ su)))
              (agreeᵀ-trans (pin-c n a r s (proj₂ (sortedᵀ sr)) (proj₂ (sortedᵀ su)))
                (agreeᵀ-sym (agreeᵀ-trans (∪-commᵀ n (later r) (pin a s) (proj₂ (sortedᵀ sr)) su)
                  (front n a s (later r) su (proj₂ (sortedᵀ sr)) (proj₁ (sortedᵀ sr))))))))

  pin-c : ∀ n a r s → SortedT (later r) → SortedT (later s) → Agreeᵀ n (first a r (later s) true) (first a s (later r) true)
  pin-c zero    a r s sr ss = stopᵀ
  pin-c (suc n) a r s sr ss = pin⁼ (∪-commᵀ n (later r) (later s) sr ss)
