{-# OPTIONS --guardedness #-}

module adequacy.Placed.Heads where

open import Data.Bool using (true; false)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (zero; suc; _+_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (timelineAt; Pos; From; Timeline; ix; sub; last; tick)
import denotation.MonotonicList.Events as M
import denotation.Unfold as U
open import adequacy.Placed.Order using (Headed; Owned; Prefix; Sided; SidedFed; SidedNext; Sides; fed; onward; prefix-++; sides)
open import adequacy.Placed.Keys using (Mark; ix-mark; last-mark; owned-trans; prefix-refl; sibling)
open import adequacy.Placed.Rising using (Disjoint; apart-mark)

-- A burst steps first at its next index.
head-burst : ∀ {Γ A t} τ r i (b : M.Frame A t) → U.headˢ (U.burstˢ {Γ} τ r i b) ≡ just (r ++ [ ix i ])
head-burst τ r i (M.emit a k) = refl
head-burst τ r i (M.stall k)  = refl
head-burst τ r i (M.close k)  = refl

-- A cold steps first one mark under where it started, or at a frame
-- tagged with its end.
heads-start : ∀ (P : Pos → Set) → (∀ k l → Mark l → P k → P (k ++ [ l ])) → (∀ t r → P r → P (ix t ∷ sub r ∷ []))
            → ∀ {Γ A} q (m : From A 0) k → P q → U.headˢ (U.step (U.startᶜ {Γ} q m)) ≡ just k → P k
heads-start P mk fr q (M.at zero _ b) k pq h with trans (sym (head-burst (tick q) q 0 b)) h
... | refl = mk q (ix 0) (ix-mark 0) pq
heads-start P mk fr q (M.at (suc t) _ b) k pq h with trans (sym (head-burst (tick q) (ix (tick q + suc t) ∷ sub (q ++ [ last ]) ∷ []) 0 b)) h
... | refl = mk _ (ix 0) (ix-mark 0) (fr (tick q + suc t) (q ++ [ last ]) (mk q last last-mark pq))
heads-start P mk fr q M.done  _ pq refl = mk q last last-mark pq
heads-start P mk fr q M.quiet _ pq ()

heads-of : ∀ (P : Pos → Set) → (∀ k l → Mark l → P k → P (k ++ [ l ]))
         → ∀ {Γ A} q (xs : List A) k → P q → U.headˢ (U.ofˢ {Γ} q 0 xs) ≡ just k → P k
heads-of P mk q []       _ pq refl = mk q last last-mark pq
heads-of P mk q (x ∷ xs) _ pq refl = mk q (ix 0) (ix-mark 0) pq

heads-map : ∀ (P : Pos → Set) {Γ A B} (f : A → B) (t : U.Step Γ A)
          → (∀ k → U.headˢ t ≡ just k → P k) → ∀ k → U.headˢ (U.mapˢ f t) ≡ just k → P k
heads-map P f (U.outˢ k a c) hs = hs
heads-map P f (U.skipˢ k c)  hs = hs
heads-map P f (U.endˢ k)     hs = hs
heads-map P f U.hushˢ        hs = hs

heads-scan : ∀ (P : Pos → Set) {Γ A B} (f : B → A → B) z (t : U.Step Γ A)
           → (∀ k → U.headˢ t ≡ just k → P k) → ∀ k → U.headˢ (U.scanˢ f z t) ≡ just k → P k
heads-scan P f z (U.outˢ k a c) hs = hs
heads-scan P f z (U.skipˢ k c)  hs = hs
heads-scan P f z (U.endˢ k)     hs = hs
heads-scan P f z U.hushˢ        hs = hs

heads-take : ∀ (P : Pos → Set) → (∀ k l → Mark l → P k → P (k ++ [ l ]))
           → ∀ {Γ A} i f (t : U.Step Γ A) → (∀ k → U.headˢ t ≡ just k → P k) → ∀ k → U.headˢ (U.takeWhileˢ i f t) ≡ just k → P k
heads-take P mk true  f (U.outˢ k a c) hs k′ h with f a
heads-take P mk true  f (U.outˢ k a c) hs k′ h    | true  = hs k′ h
heads-take P mk true  f (U.outˢ k a c) hs _  refl | false = mk k (ix 0) (ix-mark 0) (hs k refl)
heads-take P mk false f (U.outˢ k a c) hs k′ h with f a
heads-take P mk false f (U.outˢ k a c) hs k′ h    | true  = hs k′ h
heads-take P mk false f (U.outˢ k a c) hs _  refl | false = mk k last last-mark (hs k refl)
heads-take P mk i f (U.skipˢ k c) hs = hs
heads-take P mk i f (U.endˢ k)    hs = hs
heads-take P mk i f U.hushˢ       hs _ ()

heads-outer : ∀ (P : Pos → Set) → (∀ k l → Mark l → P k → P (k ++ [ l ]))
            → ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (so : U.Step Γ A)
            → (∀ k → U.headˢ so ≡ just k → P k) → ∀ k → U.headˢ (U.outerˢ op g o so [] [] U.idleᶜ) ≡ just k → P k
heads-outer P mk op g o (U.outˢ q a o′) hs _ refl = mk q (ix 0) (ix-mark 0) (hs q refl)
heads-outer P mk op g o (U.skipˢ q o′)  hs = hs
heads-outer P mk op g o (U.endˢ c)      hs = hs
heads-outer P mk op g o U.hushˢ         hs _ ()

heads-body : ∀ (P : Pos → Set) {Γ A B} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B)
           → (∀ k → U.headˢ sb ≡ just k → P k) → ∀ k → U.headˢ (U.bodyˢ r s sb) ≡ just k → P k
heads-body P r s (U.outˢ k a b) hb = hb
heads-body P r s (U.skipˢ k b)  hb = hb
heads-body P r s (U.endˢ c)     hb = hb
heads-body P r s U.hushˢ        hb = hb

heads-source : ∀ (P : Pos → Set) → (∀ k l → Mark l → P k → P (k ++ [ l ]))
             → ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (sb : U.Step (A ∷ Γ) B) (s : U.Node Γ A) (ss : U.Step Γ A)
             → (∀ k → U.headˢ sb ≡ just k → P k) → (∀ k → U.headˢ ss ≡ just k → P k)
             → ∀ k → U.headˢ (U.sourceˢ r b sb s ss) ≡ just k → P k
heads-source P mk r b sb s (U.outˢ q a s′) hb hs k h with U.beforeˢ (q ++ [ ix 0 ]) sb
heads-source P mk r b sb s (U.outˢ q a s′) hb hs _ refl | true  = mk q (ix 0) (ix-mark 0) (hs q refl)
heads-source P mk r b sb s (U.outˢ q a s′) hb hs k h    | false = heads-body P r (U.live s) sb hb k h
heads-source P mk r b sb s (U.skipˢ q s′) hb hs k h with U.beforeˢ (q ++ [ ix 0 ]) sb
heads-source P mk r b sb s (U.skipˢ q s′) hb hs _ refl | true  = mk q (ix 0) (ix-mark 0) (hs q refl)
heads-source P mk r b sb s (U.skipˢ q s′) hb hs k h    | false = heads-body P r (U.live s) sb hb k h
heads-source P mk r b sb s (U.endˢ c) hb hs k h with U.beforeˢ (c ++ [ ix 0 ]) sb
heads-source P mk r b sb s (U.endˢ c) hb hs _ refl | true  = mk c (ix 0) (ix-mark 0) (hs c refl)
heads-source P mk r b sb s (U.endˢ c) hb hs k h    | false = heads-body P r (U.live s) sb hb k h
heads-source P mk r b sb s U.hushˢ hb hs = heads-body P r (U.live s) sb hb

-- What holds where a program subscribes, and is kept one mark further on
-- and at a frame tagged with it, holds where the program first steps.
heads-sub : ∀ (P : Pos → Set) → (∀ k l → Mark l → P k → P (k ++ [ l ])) → (∀ t r → P r → P (ix t ∷ sub r ∷ []))
          → ∀ {Γ A} (o : Obs Timeline Γ A) q k → P q → U.headˢ (U.step (U.subscribe o q)) ≡ just k → P k
heads-sub P mk fr (cold c) q k pq h = heads-start P mk fr q (timelineAt c q) k pq h
heads-sub P mk fr {Γ} {A} empty q k pq h = heads-of P mk {Γ} {A} q [] k pq h
heads-sub P mk fr (of xs) q k pq h = heads-of P mk q xs k pq h
heads-sub P mk fr (map f s) q k pq h = heads-map P f (U.step (U.subscribe s q)) (λ k′ → heads-sub P mk fr s q k′ pq) k h
heads-sub P mk fr (scan f z s) q k pq h = heads-scan P f z (U.step (U.subscribe s q)) (λ k′ → heads-sub P mk fr s q k′ pq) k h
heads-sub P mk fr (takeWhile i f s) q k pq h =
  heads-take P mk i f (U.step (U.subscribe s q)) (λ k′ → heads-sub P mk fr s q k′ pq) k h
heads-sub P mk fr (flatMap op f s) q k pq h =
  heads-outer P mk op (λ a r → U.subscribe (f a) r) (U.subscribe s q) (U.step (U.subscribe s q)) (λ k′ → heads-sub P mk fr s q k′ pq) k h
heads-sub P mk fr (connect s b) q k pq h =
  heads-source P mk (q ++ [ ix 1 ]) (U.subscribe b (q ++ [ ix 0 ])) (U.step (U.subscribe b (q ++ [ ix 0 ])))
    (U.subscribe s (q ++ [ ix 1 ])) (U.step (U.subscribe s (q ++ [ ix 1 ])))
    (λ k′ → heads-sub P mk fr b (q ++ [ ix 0 ]) k′ (mk q (ix 0) (ix-mark 0) pq))
    (λ k′ → heads-sub P mk fr s (q ++ [ ix 1 ]) k′ (mk q (ix 1) (ix-mark 1) pq)) k h
heads-sub P mk fr (connected i) q k pq ()
heads-sub P mk fr (defer l) q _ pq refl = mk q (ix 0) (ix-mark 0) pq

-- A program just subscribed steps first under where it subscribed.
head-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p k → U.headˢ (U.step (U.subscribe o p)) ≡ just k → Owned p k
head-sub o p k =
  heads-sub (Owned p) (λ j l _ o′ → owned-trans p j (j ++ [ l ]) o′ (inj₁ (prefix-++ j [ l ]))) (λ t r o′ → inj₂ (inj₁ o′))
            o p k (inj₁ (prefix-refl p))

-- A first child of a position a tick heads is no prefix of a frame.
frame-prefix : ∀ p → Headed p → ∀ t r → ¬ Prefix (p ++ [ ix 0 ]) (ix t ∷ sub r ∷ [])
frame-prefix (ix _ ∷ [])        _ t r (_ , () , _)
frame-prefix (ix _ ∷ _ ∷ [])    _ t r (_ , _ , ())
frame-prefix (ix _ ∷ _ ∷ _ ∷ _) _ t r (_ , _ , ())

-- A frame tagged with what lies apart from a first child lies apart from
-- it too.
frame-apart : ∀ p → Headed p → ∀ t r → Disjoint (p ++ [ ix 0 ]) r → Disjoint (p ++ [ ix 0 ]) (ix t ∷ sub r ∷ [])
frame-apart p hp t r d =
    (λ { (inj₁ q) → frame-prefix p hp t r q ; (inj₂ (inj₁ o)) → proj₁ d o ; (inj₂ (inj₂ ())) })
  , (λ o → proj₂ d (owned-trans r (ix t ∷ sub r ∷ []) (p ++ [ ix 0 ]) (inj₂ (inj₁ (inj₁ (prefix-refl r)))) o))

-- A connect's source, just subscribed, steps first apart from where its
-- body subscribed.
head-sub-apart : ∀ {Γ A} (o : Obs Timeline Γ A) p k → Headed p → U.headˢ (U.step (U.subscribe o (p ++ [ ix 1 ]))) ≡ just k
               → Disjoint (p ++ [ ix 0 ]) k
head-sub-apart o p k hp =
  heads-sub (Disjoint (p ++ [ ix 0 ])) (apart-mark (p ++ [ ix 0 ])) (frame-apart p hp)
            o (p ++ [ ix 1 ]) k (sibling p (ix-mark 1) (λ ()) , sibling p (ix-mark 0) (λ ()))

-- Under a region, apart from what lies apart from it and from just past
-- that.
sides-of : ∀ P k q → Owned P k → Disjoint P q → k ≢ q × k ≢ q ++ [ ix 0 ]
sides-of P k q o d = (λ { refl → proj₁ d o }) , (λ { refl → proj₁ (apart-mark P q (ix 0) (ix-mark 0) d) o })

-- A connect's body and source, just subscribed, step apart.
sides-sub : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p → Headed p
          → Sides (U.step (U.subscribe b (p ++ [ ix 0 ]))) (U.step (U.subscribe s (p ++ [ ix 1 ])))
sides-sub s b p hp k q hk hq = sides-of (p ++ [ ix 0 ]) k q (head-sub b (p ++ [ ix 0 ]) k hk) (head-sub-apart s p q hp hq)

postulate
  -- A connect's body, just subscribed, steps alone apart from its
  -- source for good.
  --
  -- Unwritten route: a key on nodes, every position a body holds owned
  -- by where it subscribed and every one its source holds disjoint from
  -- it, kept by a step and a feed; `Sided` then follows by coinduction.
  sub-onward : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p → Headed p
             → SidedNext (U.step (U.subscribe b (p ++ [ ix 0 ]))) (U.subscribe s (p ++ [ ix 1 ]))

  -- And fed its source's first step, apart from it for good.
  sub-fed : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p → Headed p
          → SidedFed (U.subscribe b (p ++ [ ix 0 ])) (U.step (U.subscribe s (p ++ [ ix 1 ])))

-- A connect's body and source, just subscribed, kept apart.
sided-sub : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p → Headed p
          → Sided (U.subscribe b (p ++ [ ix 0 ])) (U.subscribe s (p ++ [ ix 1 ]))
sides  (sided-sub s b p hp) = sides-sub s b p hp
onward (sided-sub s b p hp) = sub-onward s b p hp
fed    (sided-sub s b p hp) = sub-fed s b p hp
