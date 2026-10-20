{-# OPTIONS --guardedness #-}

-- UNIONS REGROUPED: a tail is positions alone, so three in order merge
-- alike however they are grouped, and three nodes' rests leave alike
-- regrouped or swapped.
module adequacy.Leaves.Union where

open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import denotation.MonotonicList.Events using (Pos; Tail; Tail∞; pin; idle; _<ᵖ_; _∪_; <ᵖ-asym; <ᵖ-split; <ᵖ-trans; ≮-trans)
open import denotation.MonotonicList using (Agreeᵀ; agreeᵀ-refl; agreeᵀ-sym; agreeᵀ-trans; stopᵀ; pin⁼)
open import denotation.NonExpansive using (tailᴱ-ne; ∪-ne)
import denotation.Unfold as U
open import adequacy.Placed.Rising using (AtopT)
open import adequacy.Placed.Trail using (SortedT; sortedᵀ; sortedT-∪; atopT-∪)
open import adequacy.Deep using (deepR-rest; deep-cutR)
open import adequacy.Leaves using (Pinned; pinned; unpinned; rest-pinned; Leaves; leaves; Twin; lv-swap; lv-refl; ∪-unit; ∪-tie; ∪-comm)

open Tail∞

private
  contra : ∀ {ℓ} {X : Set ℓ} → true ≡ false → X
  contra ()

  after : Tail → Tail∞
  later (after t) = t

  sortedT-pin : ∀ a (r : Tail∞) → AtopT a (later r) → SortedT (later r) → SortedT (pin a r)
  sortedᵀ (sortedT-pin a r at sr) = at , sr

  -- A pin no later than a tail's first, merged in front of it.
  ∪-head : ∀ m a (r : Tail∞) u → SortedT (pin a r) → AtopT a u → SortedT u → Agreeᵀ m (pin a r ∪ u) (pin a (after (later r ∪ u)))
  ∪-head zero    a r u         st au su = stopᵀ
  ∪-head (suc m) a r idle      st au su = pin⁼ (agreeᵀ-refl m _)
  ∪-head (suc m) a r (pin b s) st au su with a <ᵖ b in e
  ... | true  = pin⁼ (agreeᵀ-refl m _)
  ... | false with <ᵖ-split a b au
  ...   | inj₁ lt   = contra (trans (sym lt) e)
  ...   | inj₂ refl = pin⁼ (∪-tie m a r s (proj₁ (sortedᵀ st)) (proj₁ (sortedᵀ su)) (proj₂ (sortedᵀ su)))

mutual
  ∪-assoc : ∀ m t u w → SortedT t → SortedT u → SortedT w → Agreeᵀ m ((t ∪ u) ∪ w) (t ∪ (u ∪ w))
  ∪-assoc zero    t         u         w         st su sw = stopᵀ
  ∪-assoc (suc m) idle      u         w         st su sw = agreeᵀ-refl _ _
  ∪-assoc (suc m) (pin a r) idle      w         st su sw = ∪-ne (agreeᵀ-sym (∪-unit (suc m) (pin a r))) (agreeᵀ-refl _ w)
  ∪-assoc (suc m) (pin a r) (pin b s) idle      st su sw =
    agreeᵀ-trans (agreeᵀ-sym (∪-unit (suc m) (pin a r ∪ pin b s))) (∪-ne (agreeᵀ-refl _ (pin a r)) (∪-unit (suc m) (pin b s)))
  ∪-assoc (suc m) (pin a r) (pin b s) (pin c z) st su sw with b <ᵖ a in eba | c <ᵖ a in eca
  ... | false | false = least-t m a r b s c z eba eca st su sw
  ... | false | true  = least-w m a r b s c z (<ᵖ-asym c a eca) (≮-trans c a b (<ᵖ-asym c a eca) eba) st su sw
  ... | true  | _ with c <ᵖ b in ecb
  ...   | false = least-u m a r b s c z (<ᵖ-asym b a eba) ecb st su sw
  ...   | true  = least-w m a r b s c z (<ᵖ-asym c a (<ᵖ-trans c b a ecb eba)) (<ᵖ-asym c b ecb) st su sw

  private
    least-t : ∀ m a r b s c z → b <ᵖ a ≡ false → c <ᵖ a ≡ false → SortedT (pin a r) → SortedT (pin b s) → SortedT (pin c z)
            → Agreeᵀ (suc m) ((pin a r ∪ pin b s) ∪ pin c z) (pin a r ∪ (pin b s ∪ pin c z))
    least-t m a r b s c z au aw st su sw =
      agreeᵀ-trans (∪-ne (∪-head (suc m) a r u st au su) (agreeᵀ-refl _ w))
        (agreeᵀ-trans (∪-head (suc m) a (after (later r ∪ u)) w (sortedT-pin a _ (atopT-∪ a (later r) u ar au) (sortedT-∪ _ _ sr su)) aw sw)
          (agreeᵀ-trans (pin⁼ (∪-assoc m (later r) u w sr su sw))
            (agreeᵀ-sym (∪-head (suc m) a r (u ∪ w) st (atopT-∪ a u w au aw) (sortedT-∪ u w su sw)))))
      where u = pin b s
            w = pin c z
            ar = proj₁ (sortedᵀ st)
            sr = proj₂ (sortedᵀ st)

    least-u : ∀ m a r b s c z → a <ᵖ b ≡ false → c <ᵖ b ≡ false → SortedT (pin a r) → SortedT (pin b s) → SortedT (pin c z)
            → Agreeᵀ (suc m) ((pin a r ∪ pin b s) ∪ pin c z) (pin a r ∪ (pin b s ∪ pin c z))
    least-u m a r b s c z bt bw st su sw =
      agreeᵀ-trans (∪-ne (agreeᵀ-trans (∪-comm (suc m) t u st su) (∪-head (suc m) b s t su bt st)) (agreeᵀ-refl _ w))
        (agreeᵀ-trans (∪-head (suc m) b (after (later s ∪ t)) w (sortedT-pin b _ (atopT-∪ b (later s) t bs bt) (sortedT-∪ _ _ ss st)) bw sw)
          (agreeᵀ-trans (pin⁼ (agreeᵀ-trans (∪-assoc m (later s) t w ss st sw)
                                (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ (later s)) (∪-comm m t w st sw))
                                              (agreeᵀ-sym (∪-assoc m (later s) w t ss sw st)))))
            (agreeᵀ-sym
              (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ t) (∪-head (suc m) b s w su bw sw))
                (agreeᵀ-trans (∪-comm (suc m) t _ st sw′)
                  (∪-head (suc m) b (after (later s ∪ w)) t sw′ bt st))))))
      where t = pin a r
            u = pin b s
            w = pin c z
            bs = proj₁ (sortedᵀ su)
            ss = proj₂ (sortedᵀ su)
            sw′ = sortedT-pin b (after (later s ∪ w)) (atopT-∪ b (later s) w bs bw) (sortedT-∪ _ _ ss sw)

    least-w : ∀ m a r b s c z → a <ᵖ c ≡ false → b <ᵖ c ≡ false → SortedT (pin a r) → SortedT (pin b s) → SortedT (pin c z)
            → Agreeᵀ (suc m) ((pin a r ∪ pin b s) ∪ pin c z) (pin a r ∪ (pin b s ∪ pin c z))
    least-w m a r b s c z ct cu st su sw =
      agreeᵀ-trans (∪-comm (suc m) (t ∪ u) w (sortedT-∪ t u st su) sw)
        (agreeᵀ-trans (∪-head (suc m) c z (t ∪ u) sw (atopT-∪ c t u ct cu) (sortedT-∪ t u st su))
          (agreeᵀ-trans (pin⁼ (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ (later z)) (∪-comm m t u st su))
                                            (agreeᵀ-sym (∪-assoc m (later z) u t sz su st))))
            (agreeᵀ-sym
              (agreeᵀ-trans (∪-ne (agreeᵀ-refl _ t) (agreeᵀ-trans (∪-comm (suc m) u w su sw) (∪-head (suc m) c z u sw cu su)))
                (agreeᵀ-trans (∪-comm (suc m) t _ st sw′)
                  (∪-head (suc m) c (after (later z ∪ u)) t sw′ ct st))))))
      where t = pin a r
            u = pin b s
            w = pin c z
            sz = proj₂ (sortedᵀ sw)
            sw′ = sortedT-pin c (after (later z ∪ u)) (atopT-∪ c (later z) u (proj₁ (sortedᵀ sw)) cu) (sortedT-∪ _ _ sz su)

private
  pins3 : ∀ {Γ B C} a b c {X x y z : U.Node Γ B} {x₁ y₁ z₁} {x′ Y y′ z′ : U.Node Γ C} {x₂ y₂ z₂}
        → Pinned (U.unionˢ X (U.unionˢ x (U.skipˢ a x₁) y (U.skipˢ b y₁)) z (U.skipˢ c z₁))
                 (U.unionˢ x′ (U.skipˢ a x₂) Y (U.unionˢ y′ (U.skipˢ b y₂) z′ (U.skipˢ c z₂)))
  pins3 a b c with b <ᵖ c in ebc
  ... | true with a <ᵖ b in eab
  ...   | true with a <ᵖ c in eac
  ...     | true  = pinned
  ...     | false = contra (trans (sym (<ᵖ-trans a b c eab ebc)) eac)
  pins3 a b c | true | false with b <ᵖ c in ebc′
  ...   | true  = pinned
  ...   | false = contra (sym ebc)
  pins3 a b c | false with a <ᵖ b in eab
  ...   | true with a <ᵖ c
  ...     | true  = pinned
  ...     | false = pinned
  pins3 a b c | false | false with b <ᵖ c in ebc′ | a <ᵖ c in eac
  ...   | true  | _     = contra ebc
  ...   | false | true  = contra (trans (sym eac) (≮-trans c b a ebc′ eab))
  ...   | false | false = pinned

-- A union's next step pins as its halves regrouped.
union-assoc-pinned : ∀ {Γ B C} {X x y z : U.Node Γ B} {sx sy sz} {x′ Y y′ z′ : U.Node Γ C} {sx′ sy′ sz′}
                   → Pinned sx sx′ → Pinned sy sy′ → Pinned sz sz′
                   → Pinned (U.unionˢ X (U.unionˢ x sx y sy) z sz) (U.unionˢ x′ sx′ Y (U.unionˢ y′ sy′ z′ sz′))
union-assoc-pinned (pinned {a}) (pinned {b}) (pinned {c}) = pins3 a b c
union-assoc-pinned (pinned {a}) (pinned {b}) unpinned with a <ᵖ b
... | true  = pinned
... | false = pinned
union-assoc-pinned (pinned {a}) unpinned (pinned {c}) with a <ᵖ c
... | true  = pinned
... | false = pinned
union-assoc-pinned pinned unpinned unpinned = pinned
union-assoc-pinned unpinned (pinned {b}) (pinned {c}) with b <ᵖ c
... | true  = pinned
... | false = pinned
union-assoc-pinned unpinned pinned   unpinned = pinned
union-assoc-pinned unpinned unpinned pinned   = pinned
union-assoc-pinned unpinned unpinned unpinned = unpinned

-- Three nodes' rests leave alike however they are grouped.
lv-assoc : ∀ {Γ A} (x y z : U.Node Γ A) → Leaves (U.unionᶜ (U.unionᶜ x y) z) (U.unionᶜ x (U.unionᶜ y z))
lv-assoc x y z = leaves
  (λ ρ e n → tailᴱ-ne (∪-assoc n (U.cutᴺ x ρ) (U.cutᴺ y ρ) (U.cutᴺ z ρ)
                         (deep-cutR x (proj₁ (proj₁ (proj₂ e)))) (deep-cutR y (proj₂ (proj₁ (proj₂ e)))) (deep-cutR z (proj₂ (proj₂ e)))))
  (λ ρ e → deepR-rest {c = U.unionᶜ x (U.unionᶜ y z)} (proj₁ (proj₁ (proj₂ e)) , (proj₂ (proj₁ (proj₂ e)) , proj₂ (proj₂ e))))
  (union-assoc-pinned (rest-pinned x) (rest-pinned y) (rest-pinned z))

tw-assoc : ∀ {Γ A} (x y z : U.Node Γ A) → Twin (U.unionᶜ (U.unionᶜ x y) z) (U.unionᶜ x (U.unionᶜ y z))
tw-assoc x y z = lv-assoc x y z
               , λ ρ d → deepR-rest {c = U.unionᶜ (U.unionᶜ x y) z} ((proj₁ (proj₂ d) , proj₁ (proj₂ (proj₂ d))) , proj₂ (proj₂ (proj₂ d)))

tw-swap : ∀ {Γ A} (x y : U.Node Γ A) → Twin (U.unionᶜ x y) (U.unionᶜ y x)
tw-swap x y = lv-swap (lv-refl x) (lv-refl y) , λ ρ d → deepR-rest {c = U.unionᶜ x y} (proj₂ (proj₂ d) , proj₁ (proj₂ d))
