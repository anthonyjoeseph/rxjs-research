{-# OPTIONS --guardedness #-}

-- WHERE A SUBSCRIPTION OPENS: a program subscribed heads at a position,
-- never the empty one; each head is something appended to, or a
-- timer's cascade; so at the root, no earlier than the root.
module adequacy.Opens where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; From; Frame; Timeline; timelineAt; at; done; quiet; emit; stall; close; ix; last; tick; root)
  renaming (sub to subᴾ)
import denotation.Unfold as U
open import adequacy.Sorted using (_≤ᵖ_)

Opens : Maybe Pos → Set
Opens nothing        = ⊤
Opens (just [])      = ⊥
Opens (just (_ ∷ _)) = ⊤

opens-++ : ∀ k x → Opens (just (k ++ [ x ]))
opens-++ []      x = tt
opens-++ (_ ∷ _) x = tt

opens-map : ∀ {Γ A B} (f : A → B) (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.mapˢ f s))
opens-map f (U.outˢ k a c) o = o
opens-map f (U.skipˢ k c)  o = o
opens-map f (U.endˢ k)     o = o
opens-map f U.hushˢ        o = tt

opens-scan : ∀ {Γ A B} (f : B → A → B) z (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.scanˢ f z s))
opens-scan f z (U.outˢ k a c) o = o
opens-scan f z (U.skipˢ k c)  o = o
opens-scan f z (U.endˢ k)     o = o
opens-scan f z U.hushˢ        o = tt

opens-taking : ∀ {Γ A} i (p : A → Bool) k a (c : U.Node Γ A) b → Opens (just k) → Opens (U.headˢ (U.taking i p k a c b))
opens-taking i     p k a c true  o = o
opens-taking true  p k a c false o = opens-++ k (ix 0)
opens-taking false p k a c false o = opens-++ k last

opens-take : ∀ {Γ A} i (p : A → Bool) (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.takeWhileˢ i p s))
opens-take i p (U.outˢ k a c) o = opens-taking i p k a c (p a) o
opens-take i p (U.skipˢ k c)  o = o
opens-take i p (U.endˢ k)     o = o
opens-take i p U.hushˢ        o = tt

opens-outer : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (so : U.Step Γ A) → Opens (U.headˢ so)
            → Opens (U.headˢ (U.outerˢ op g o so [] [] U.idleᶜ))
opens-outer op g o (U.outˢ q a o′) h = opens-++ q (ix 0)
opens-outer op g o (U.skipˢ q o′)  h = h
opens-outer op g o (U.endˢ c)      h = h
opens-outer op g o U.hushˢ         h = tt

opens-body : ∀ {Γ A B} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → Opens (U.headˢ sb) → Opens (U.headˢ (U.bodyˢ r s sb))
opens-body r s (U.outˢ k a b) h = h
opens-body r s (U.skipˢ k b)  h = h
opens-body r s (U.endˢ c)     h = h
opens-body r s U.hushˢ        h = tt

opens-source : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) ss → Opens (U.headˢ sb)
             → Opens (U.headˢ (U.sourceˢ r b sb s ss))
opens-source r b sb s (U.outˢ q a s′) h with U.beforeˢ (q ++ [ ix 0 ]) sb
... | true  = opens-++ q (ix 0)
... | false = opens-body r (U.live s) sb h
opens-source r b sb s (U.skipˢ q s′) h with U.beforeˢ (q ++ [ ix 0 ]) sb
... | true  = opens-++ q (ix 0)
... | false = opens-body r (U.live s) sb h
opens-source r b sb s (U.endˢ c) h with U.beforeˢ (c ++ [ ix 0 ]) sb
... | true  = opens-++ c (ix 0)
... | false = opens-body r (U.live s) sb h
opens-source r b sb s U.hushˢ h = opens-body r (U.live s) sb h

opens-burst : ∀ {Γ A t} τ r i (f : Frame A t) → Opens (U.headˢ (U.burstˢ {Γ} τ r i f))
opens-burst τ r i (emit a k) = opens-++ r (ix i)
opens-burst τ r i (stall k)  = opens-++ r (ix i)
opens-burst τ r i (close k)  = opens-++ r (ix i)

opens-start : ∀ {Γ A} p (m : From A 0) → Opens (U.headˢ (U.step (U.startᶜ {Γ} p m)))
opens-start p (at zero _ b)    = opens-burst (tick p) p 0 b
opens-start p (at (suc t) _ b) = opens-burst (tick p) _ 0 b
opens-start p done             = opens-++ p last
opens-start p quiet            = tt

opens-of : ∀ {Γ A} p i (xs : List A) → Opens (U.headˢ (U.ofˢ {Γ} p i xs))
opens-of p i []       = opens-++ p last
opens-of p i (x ∷ xs) = opens-++ p (ix i)

opens-subscribe : ∀ {Γ A} (o : Obs Timeline Γ A) p → Opens (U.headˢ (U.step (U.subscribe o p)))
opens-subscribe (cold c)          p = opens-start p (timelineAt c p)
opens-subscribe empty             p = opens-++ p last
opens-subscribe (of xs)           p = opens-of p 0 xs
opens-subscribe (map f s)         p = opens-map f _ (opens-subscribe s p)
opens-subscribe (scan f z s)      p = opens-scan f z _ (opens-subscribe s p)
opens-subscribe (takeWhile i q s) p = opens-take i q _ (opens-subscribe s p)
opens-subscribe (flatMap op f s)  p = opens-outer op (λ a q → U.subscribe (f a) q) (U.subscribe s p) _ (opens-subscribe s p)
opens-subscribe (connect s b)     p =
  opens-source (p ++ [ ix 1 ]) (U.subscribe b (p ++ [ ix 0 ])) _ (U.subscribe s (p ++ [ ix 1 ])) (U.step (U.subscribe s (p ++ [ ix 1 ]))) (opens-subscribe b (p ++ [ ix 0 ]))
opens-subscribe (connected i)     p = tt
opens-subscribe (defer l)         p = opens-++ p (ix 0)

-- The root comes before every position but the empty one.
root-least : ∀ a q → root ≤ᵖ (a ∷ q)
root-least (ix zero)    []      = inj₁ refl
root-least (ix zero)    (_ ∷ _) = inj₂ refl
root-least (ix (suc n)) q       = inj₂ refl
root-least (subᴾ x)     q       = inj₂ refl
root-least last         q       = inj₂ refl

heads-open : ∀ {k} (h : Maybe Pos) → Opens h → h ≡ just k → root ≤ᵖ k
heads-open (just (a ∷ q)) _ refl = root-least a q
