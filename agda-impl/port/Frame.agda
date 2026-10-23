{-# OPTIONS --guardedness #-}

-- THE FRAME: heads lemmas and shut/down machinery, heap-free.
-- Heap-dependent parts of old adequacy/Frame.agda (scan-part, gates,
-- defined-alike, seen-gates, gates-apart, scan-apart, store-alike,
-- scan-defined, scan-sees, merged-eq) are not ported.
module port.Frame where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ) renaming (++⁺ to all-++⁺)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import port.Sorted using (_≤ᵖ_; ≤ᵖ-child; ≤ᵖ-trans)
open import port.Told using (untoldᴶ; untold; untoldʳ; untoldʳᴹ; untoldʳᴸ; untoldᵇ; untoldᴹ; untoldᴸ; untoldˢ; Tells)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₂)

open import denotation.MonotonicList.Events using (Events∞; Pos; ix; last; _<ᵖ_; <ᵖ-trans; <ᵖ-split; <ᵖ-asym; <ᵖ-below; inside)
import Data.Maybe.Relation.Binary.Pointwise as MP
import Data.List.Relation.Binary.Pointwise as LP
open import denotation.MonotonicList.Events using () renaming (done to doneᶠ; quiet to quietᶠ; at to atᶠ; emit to emitᶠ; stall to stallᶠ; close to closeᶠ)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import port.Stepper.Past using (head-map; head-scan)
import Tree as T
open import port.Strong using (module Strongly)
open Events∞


module Framing (R : Set) where
  open Strongly R using (Heads)

  heads-map : ∀ {Γ A B q} (g : A → B) {c : U.Node Γ A} → Heads q c → Heads q (U.mapᶜ g c)
  heads-map g {c} hd e = hd (trans (sym (head-map g (U.step c))) e)

  heads-scan : ∀ {Γ A B q} (g : B → A → B) z {c : U.Node Γ A} → Heads q c → Heads q (U.scanᶜ g z c)
  heads-scan g z {c} hd e = hd (trans (sym (head-scan g z (U.step c))) e)

  -- A take's head is its source's, or under it.
  taking-head : ∀ {Γ A q} i (p : A → Bool) k a (c : U.Node Γ A) b → (∀ {k′} → just k ≡ just k′ → q ≤ᵖ k′)
              → ∀ {k′} → U.headˢ (U.taking i p k a c b) ≡ just k′ → q ≤ᵖ k′
  taking-head i     p k a c true  hd refl = hd refl
  taking-head true  p k a c false hd refl = ≤ᵖ-child k (hd refl)
  taking-head false p k a c false hd refl = ≤ᵖ-child k (hd refl)

  take-head : ∀ {Γ A q} i (p : A → Bool) (s : U.Step Γ A) → (∀ {k} → U.headˢ s ≡ just k → q ≤ᵖ k)
            → ∀ {k} → U.headˢ (U.takeWhileˢ i p s) ≡ just k → q ≤ᵖ k
  take-head i p (U.outˢ k a c) hd = taking-head i p k a c (p a) hd
  take-head i p (U.skipˢ k c)  hd = hd
  take-head i p (U.endˢ k)     hd = hd
  take-head i p U.hushˢ        hd ()

  heads-take : ∀ {Γ A q} i (p : A → Bool) {c : U.Node Γ A} → Heads q c → Heads q (U.takeWhileᶜ i p c)
  heads-take i p {c} hd = take-head i p (U.step c) hd

  HeadsS : ∀ {Γ A} → Pos → U.Step Γ A → Set
  HeadsS q s = ∀ {k} → U.headˢ s ≡ just k → q ≤ᵖ k

  if-head : ∀ {Γ A q} b (s₁ s₂ : U.Step Γ A) → HeadsS q s₁ → HeadsS q s₂ → HeadsS q (if b then s₁ else s₂)
  if-head true  s₁ s₂ h₁ h₂ = h₁
  if-head false s₁ s₂ h₁ h₂ = h₂

  child-skip : ∀ {Γ A q} k l (c : U.Node Γ A) → (∀ {k′} → just k ≡ just k′ → q ≤ᵖ k′) → HeadsS q (U.skipˢ (k ++ [ l ]) c)
  child-skip k l c hd refl = ≤ᵖ-child k (hd refl)

  body-head : ∀ {Γ A B q} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → HeadsS q sb → HeadsS q (U.bodyˢ r s sb)
  body-head r s (U.outˢ k a b) hd = hd
  body-head r s (U.skipˢ k b)  hd = hd
  body-head r s (U.endˢ c)     hd = hd
  body-head r s U.hushˢ        hd ()

  -- A live connect's head is its body's, or under its source's.
  source-head : ∀ {Γ A B q} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) (ss : U.Step Γ A) → HeadsS q sb → HeadsS q ss
              → HeadsS q (U.sourceˢ r b sb s ss)
  source-head r b sb s (U.outˢ k a s′) hb hs =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) n) (U.bodyˢ r (U.live s) sb) (child-skip k (ix 0) n hs) (body-head r (U.live s) sb hb)
    where n = U.connectᶜ r (U.feed (here refl) k (just a) b) (U.live s′)
  source-head r b sb s (U.skipˢ k s′)  hb hs =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) n) (U.bodyˢ r (U.live s) sb) (child-skip k (ix 0) n hs) (body-head r (U.live s) sb hb)
    where n = U.connectᶜ r (U.feed (here refl) k nothing b) (U.live s′)
  source-head r b sb s (U.endˢ c)      hb hs =
    if-head (U.beforeˢ (c ++ [ ix 0 ]) sb) (U.skipˢ (c ++ [ ix 0 ]) n) (U.bodyˢ r (U.live s) sb) (child-skip c (ix 0) n hs) (body-head r (U.live s) sb hb)
    where n = U.connectᶜ r (U.shut (here refl) c b) (U.ended c (U.restᶜ s))
  source-head r b sb s U.hushˢ         hb hs = body-head r (U.live s) sb hb

  heads-source : ∀ {Γ A B q} r {b : U.Node (A ∷ Γ) B} {s : U.Node Γ A} → Heads q s → Heads q b → Heads q (U.connectᶜ r b (U.live s))
  heads-source r {b} {s} hs hb = source-head r b (U.step b) s (U.step s) hb hs

  data Apart : ∀ {Γ : List Set} {A C : Set} → A ∈ᴸ Γ → C ∈ᴸ Γ → Set₁ where
    here-there  : ∀ {Γ A C} {i : C ∈ᴸ Γ} → Apart {A ∷ Γ} (here refl) (there i)
    there-here  : ∀ {Γ A C} {k : A ∈ᴸ Γ} → Apart {C ∷ Γ} (there k) (here refl)
    there-there : ∀ {Γ X A C} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → Apart {X ∷ Γ} (there k) (there i)

  untoldᴶ-none : ∀ {A B : Set} p e → untoldᴶ {A} {B} p e nothing ≡ []
  untoldᴶ-none p nothing  = refl
  untoldᴶ-none p (just _) = refl

  untold-told : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (j : B ∈ᴸ Γ) p e
              → untoldᴶ p (U.told k c j p e (U.same? k j)) (U.same? i j) ≡ untoldᴶ p e (U.same? i j)
  untold-told here-there      c (here refl) p e        = trans (untoldᴶ-none p _) (sym (untoldᴶ-none p e))
  untold-told here-there      c (there j)   p nothing  = refl
  untold-told here-there      c (there j)   p (just _) = refl
  untold-told there-here      c (here refl) p nothing  = refl
  untold-told there-here      c (here refl) p (just _) = refl
  untold-told there-here      c (there j)   p e        = trans (untoldᴶ-none p _) (sym (untoldᴶ-none p e))
  untold-told (there-there a) c (here refl) p e        = trans (untoldᴶ-none p _) (sym (untoldᴶ-none p e))
  untold-told (there-there a) c (there j)   p e        = untold-told a c j p e

  -- A shut tells only the joiners of the connect it ends.
  mutual
    untold-apart : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (n : U.Node Γ B) → untold i (U.shut k c n) ≡ untold i n
    untold-apart a c (U.mapᶜ f n)                 = untold-apart a c n
    untold-apart a c (U.scanᶜ f z n)              = untold-apart a c n
    untold-apart a c (U.takeWhileᶜ b p n)         = untold-apart a c n
    untold-apart a c (U.flatMapᶜ op g o ls qs pl) =
      cong₂ _++_ (untold-apartᴹ a c o) (cong₂ _++_ (untold-apartᴸ a c ls) (untold-apart a c pl))
    untold-apart a c (U.joinᶜ j p xs e)           = untold-told a c j p e
    untold-apart a c (U.connectᶜ r b s)           = cong₂ _++_ (untold-apart (there-there a) c b) (untold-apartˢ a c s)
    untold-apart a c (U.endingᶜ p n)              = untold-apart a c n
    untold-apart a c (U.restᶜ n)                  = rested-apart a c n
    untold-apart a c (U.unionᶜ x y)               = cong₂ _++_ (rested-apart a c x) (rested-apart a c y)
    untold-apart a c (U.burstingᶜ r t)            = cong₂ _++_ (untold-apart a c t) (rested-apart a c t)
    untold-apart a c (U.underᶜ s b)               = rested-apart (there-there a) c b
    untold-apart a c (U.framesᶜ _ _ _)            = refl
    untold-apart a c (U.burstᶜ _ _ _ _)           = refl
    untold-apart a c (U.ofᶜ _ _ _)                = refl
    untold-apart a c (U.deferᶜ _ _ _)             = refl
    untold-apart a c U.idleᶜ                      = refl

    untold-apartᴹ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (m : Maybe (U.Node Γ B)) → untoldᴹ i (U.shutᴹ k c m) ≡ untoldᴹ i m
    untold-apartᴹ a c nothing  = refl
    untold-apartᴹ a c (just n) = untold-apart a c n

    untold-apartᴸ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (ns : List (U.Node Γ B)) → untoldᴸ i (U.shutᴸ k c ns) ≡ untoldᴸ i ns
    untold-apartᴸ a c []       = refl
    untold-apartᴸ a c (n ∷ ns) = cong₂ _++_ (untold-apart a c n) (untold-apartᴸ a c ns)

    untold-apartˢ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (s : U.Source Γ B) → untoldˢ i (U.shutˢ k c s) ≡ untoldˢ i s
    untold-apartˢ a c (U.live s)    = untold-apart a c s
    untold-apartˢ a c (U.ended e t) = untold-apart a c t

    rested-apart : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (n : U.Node Γ B) → untoldʳ i (U.shut k c n) ≡ untoldʳ i n
    rested-apart a c (U.mapᶜ f n)                 = rested-apart a c n
    rested-apart a c (U.scanᶜ f z n)              = rested-apart a c n
    rested-apart a c (U.takeWhileᶜ b p n)         = rested-apart a c n
    rested-apart a c (U.flatMapᶜ op g o ls qs pl) =
      cong₂ _++_ (rested-apartᴹ a c o) (cong₂ _++_ (rested-apartᴸ a c ls) (rested-apart a c pl))
    rested-apart a c (U.joinᶜ j p xs e)           = refl
    rested-apart a c (U.connectᶜ r b s)           = cong₂ _++_ (rested-apart (there-there a) c b) (rested-apartᵇ a c s)
    rested-apart a c (U.endingᶜ p n)              = rested-apart a c n
    rested-apart a c (U.restᶜ n)                  = rested-apart a c n
    rested-apart a c (U.unionᶜ x y)               = cong₂ _++_ (rested-apart a c x) (rested-apart a c y)
    rested-apart a c (U.burstingᶜ r t)            = cong₂ _++_ (untold-apart a c t) (rested-apart a c t)
    rested-apart a c (U.underᶜ s b)               = rested-apart (there-there a) c b
    rested-apart a c (U.framesᶜ _ _ _)            = refl
    rested-apart a c (U.burstᶜ _ _ _ _)           = refl
    rested-apart a c (U.ofᶜ _ _ _)                = refl
    rested-apart a c (U.deferᶜ _ _ _)             = refl
    rested-apart a c U.idleᶜ                      = refl

    rested-apartᴹ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (m : Maybe (U.Node Γ B)) → untoldʳᴹ i (U.shutᴹ k c m) ≡ untoldʳᴹ i m
    rested-apartᴹ a c nothing  = refl
    rested-apartᴹ a c (just n) = rested-apart a c n

    rested-apartᴸ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (ns : List (U.Node Γ B)) → untoldʳᴸ i (U.shutᴸ k c ns) ≡ untoldʳᴸ i ns
    rested-apartᴸ a c []       = refl
    rested-apartᴸ a c (n ∷ ns) = cong₂ _++_ (rested-apart a c n) (rested-apartᴸ a c ns)

    rested-apartᵇ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (s : U.Source Γ B) → untoldᵇ i (U.shutˢ k c s) ≡ untoldᵇ i s
    rested-apartᵇ a c (U.live s)    = cong₂ _++_ (untold-apart a c s) (rested-apart a c s)
    rested-apartᵇ a c (U.ended e t) = cong₂ _++_ (untold-apart a c t) (rested-apart a c t)

  untold-shut : ∀ {Γ A B C} (i : C ∈ᴸ Γ) c (b : U.Node (A ∷ Γ) B) → untold (there i) (U.shut (here refl) c b) ≡ untold (there i) b
  untold-shut i c b = untold-apart here-there c b


  shut-heads-step : ∀ {Γ A B q} r c (t : U.Node Γ A) (S : U.Step (A ∷ Γ) B) → HeadsS q S → HeadsS q (U.shutˢᵗ r c t S)
  shut-heads-step r c t (U.outˢ _ _ _) hs = hs
  shut-heads-step r c t (U.skipˢ _ _)  hs = hs
  shut-heads-step r c t (U.endˢ _)     hs = hs
  shut-heads-step r c t U.hushˢ        hs = hs

  private
    ≤ᵖ-after : ∀ {i lo p} → i <ᵖ lo ≡ true → lo ≤ᵖ p → i <ᵖ p ≡ true
    ≤ᵖ-after         h (inj₁ refl) = h
    ≤ᵖ-after {i} {lo} {p} h (inj₂ g) = <ᵖ-trans i lo p h g

  -- Two steps alike but for their continuations.
  data Twin {Γ : List Set} {A : Set} : U.Step Γ A → U.Step Γ A → Set₁ where
    outᵗ  : ∀ {k a c c′} → Twin (U.outˢ k a c) (U.outˢ k a c′)
    skipᵗ : ∀ {k c c′}   → Twin (U.skipˢ k c) (U.skipˢ k c′)
    endᵗ  : ∀ {k}        → Twin (U.endˢ k) (U.endˢ k)
    hushᵗ :                Twin U.hushˢ U.hushˢ

  twin-refl : ∀ {Γ A} (s : U.Step Γ A) → Twin s s
  twin-refl (U.outˢ k a c) = outᵗ
  twin-refl (U.skipˢ k c)  = skipᵗ
  twin-refl (U.endˢ k)     = endᵗ
  twin-refl U.hushˢ        = hushᵗ

  twin-head : ∀ {Γ A} {s s′ : U.Step Γ A} → Twin s s′ → U.headˢ s ≡ U.headˢ s′
  twin-head outᵗ  = refl
  twin-head skipᵗ = refl
  twin-head endᵗ  = refl
  twin-head hushᵗ = refl

  -- A shut steps as its node did, or neither heads before `q`: an end it
  -- tells came first, so what that end beat came no sooner either.
  Down : ∀ {Γ A} → Pos → U.Step Γ A → U.Step Γ A → Set₁
  Down q s s′ = Twin s s′ ⊎ (HeadsS q s × HeadsS q s′)

  -- A rest's step: a skip, or nothing.
  data Hushed {Γ : List Set} {A : Set} : U.Step Γ A → Set₁ where
    skipʰ : ∀ {k c} → Hushed (U.skipˢ k c)
    hushʰ : Hushed U.hushˢ

  if-hushed : ∀ {Γ A} b {s₁ s₂ : U.Step Γ A} → Hushed s₁ → Hushed s₂ → Hushed (if b then s₁ else s₂)
  if-hushed true  h₁ h₂ = h₁
  if-hushed false h₁ h₂ = h₂

  union-hushed : ∀ {Γ B} (x : U.Node Γ B) sx y sy → Hushed sy → Hushed (U.unionˢ x sx y sy)
  union-hushed x (U.skipˢ k x′) y (U.skipˢ k′ y′) h = if-hushed (k <ᵖ k′) skipʰ skipʰ
  union-hushed x (U.skipˢ k x′) y (U.outˢ _ _ _)  h = skipʰ
  union-hushed x (U.skipˢ k x′) y (U.endˢ _)      h = skipʰ
  union-hushed x (U.skipˢ k x′) y U.hushˢ         h = skipʰ
  union-hushed x (U.outˢ _ _ _) y sy              h = h
  union-hushed x (U.endˢ _)     y sy              h = h
  union-hushed x U.hushˢ        y sy              h = h

  under-hushed : ∀ {Γ A B C} (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) C) → Hushed {Γ} {B} (U.underˢ s sb)
  under-hushed s (U.skipˢ k b)  = skipʰ
  under-hushed s (U.outˢ _ _ _) = hushʰ
  under-hushed s (U.endˢ _)     = hushʰ
  under-hushed s U.hushˢ        = hushʰ

  bursts-hushed : ∀ {Γ A B} r (t : U.Node Γ A) (st : U.Step Γ A) → Hushed (U.restˢ {B = B} t) → Hushed {Γ} {B} (U.burstsˢ r t st)
  bursts-hushed r t (U.outˢ k _ _) h = if-hushed (inside r k) skipʰ h
  bursts-hushed r t (U.skipˢ k _)  h = if-hushed (inside r k) skipʰ h
  bursts-hushed r t (U.endˢ _)     h = h
  bursts-hushed r t U.hushˢ        h = h

  mutual
    rest-hushed : ∀ {Γ A B} (n : U.Node Γ A) → Hushed (U.restˢ {B = B} n)
    rest-hushed (U.framesᶜ τ e m)           = hushʰ
    rest-hushed (U.burstᶜ τ r k b)          = hushʰ
    rest-hushed (U.ofᶜ p k xs)              = hushʰ
    rest-hushed (U.mapᶜ f c)                = rest-hushed c
    rest-hushed (U.scanᶜ f z c)             = rest-hushed c
    rest-hushed (U.takeWhileᶜ i p c)        = rest-hushed c
    rest-hushed (U.flatMapᶜ op g o ls qs p) =
      union-hushed (U.outerᶜ o) (U.restᴹ o) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ p)) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p))
        (union-hushed (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p) (rest-hushed p))
    rest-hushed (U.joinᶜ i p xs e)          = hushʰ
    rest-hushed (U.connectᶜ {B = C} r b (U.live s)) =
      union-hushed (U.burstingᶜ r s) (U.burstsˢ r s (U.step s)) (U.underᶜ (U.live s) b) (U.underˢ (U.live s) (U.restˢ {B = C} b))
        (under-hushed (U.live s) (U.restˢ {B = C} b))
    rest-hushed (U.connectᶜ {B = C} r b (U.ended c t)) =
      union-hushed (U.burstingᶜ r t) (U.burstsˢ r t (U.step t)) (U.underᶜ (U.ended c t) b) (U.underˢ (U.ended c t) (U.restˢ {B = C} b))
        (under-hushed (U.ended c t) (U.restˢ {B = C} b))
    rest-hushed (U.deferᶜ l p ns)           = hushʰ
    rest-hushed (U.endingᶜ p n)             = rest-hushed n
    rest-hushed (U.restᶜ n)                 = rest-hushed n
    rest-hushed U.idleᶜ                     = hushʰ
    rest-hushed (U.unionᶜ x y)              = union-hushed (U.restᶜ x) (U.restˢ x) (U.restᶜ y) (U.restˢ y) (rest-hushed y)
    rest-hushed (U.burstingᶜ r t)           = bursts-hushed r t (U.step t) (rest-hushed t)
    rest-hushed (U.underᶜ {C = C} s b)      = under-hushed s (U.restˢ {B = C} b)

  rests-hushed : ∀ {Γ A B} (ls : List (U.Node Γ A)) → Hushed (U.restsˢ {B = B} ls)
  rests-hushed []       = hushʰ
  rests-hushed (l ∷ ls) = union-hushed (U.restᶜ l) (U.restˢ l) (U.restsᶜ ls) (U.restsˢ ls) (rests-hushed ls)

  map-down : ∀ {Γ A B q} (f : A → B) (s s′ : U.Step Γ A) → Down q s s′ → Down q (U.mapˢ f s) (U.mapˢ f s′)
  map-down f _ _ (inj₁ outᵗ)  = inj₁ outᵗ
  map-down f _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  map-down f _ _ (inj₁ endᵗ)  = inj₁ endᵗ
  map-down f _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  map-down f s s′ (inj₂ (h , h′)) = inj₂ ((λ e → h (trans (sym (head-map f s)) e)) , (λ e → h′ (trans (sym (head-map f s′)) e)))

  scan-down : ∀ {Γ A B q} (f : B → A → B) z (s s′ : U.Step Γ A) → Down q s s′ → Down q (U.scanˢ f z s) (U.scanˢ f z s′)
  scan-down f z _ _ (inj₁ outᵗ)  = inj₁ outᵗ
  scan-down f z _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  scan-down f z _ _ (inj₁ endᵗ)  = inj₁ endᵗ
  scan-down f z _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  scan-down f z s s′ (inj₂ (h , h′)) = inj₂ ((λ e → h (trans (sym (head-scan f z s)) e)) , (λ e → h′ (trans (sym (head-scan f z s′)) e)))

  taking-twin : ∀ {Γ A} i (p : A → Bool) k a (c c′ : U.Node Γ A) b → Twin (U.taking i p k a c b) (U.taking i p k a c′ b)
  taking-twin i     p k a c c′ true  = outᵗ
  taking-twin true  p k a c c′ false = outᵗ
  taking-twin false p k a c c′ false = endᵗ

  take-down : ∀ {Γ A q} i (p : A → Bool) (s s′ : U.Step Γ A) → Down q s s′ → Down q (U.takeWhileˢ i p s) (U.takeWhileˢ i p s′)
  take-down i p _ _ (inj₁ (outᵗ {k} {a} {c} {c′})) = inj₁ (taking-twin i p k a c c′ (p a))
  take-down i p _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  take-down i p _ _ (inj₁ endᵗ)  = inj₁ endᵗ
  take-down i p _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  take-down i p s s′ (inj₂ (h , h′)) = inj₂ (take-head i p s h , take-head i p s′ h′)

  under-heads : ∀ {Γ A B C q} (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) C) → HeadsS q sb → HeadsS {Γ} {B} q (U.underˢ s sb)
  under-heads s (U.skipˢ k b)  h = h
  under-heads s (U.outˢ _ _ _) h ()
  under-heads s (U.endˢ _)     h ()
  under-heads s U.hushˢ        h ()

  under-down : ∀ {Γ A B C q} (s s′ : U.Source Γ A) (sb sb′ : U.Step (A ∷ Γ) C) → Down q sb sb′ → Down {Γ} {B} q (U.underˢ s sb) (U.underˢ s′ sb′)
  under-down s s′ _ _ (inj₁ outᵗ)  = inj₁ hushᵗ
  under-down s s′ _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  under-down s s′ _ _ (inj₁ endᵗ)  = inj₁ hushᵗ
  under-down s s′ _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  under-down s s′ sb sb′ (inj₂ (h , h′)) = inj₂ (under-heads s sb h , under-heads s′ sb′ h′)

  told-end : ∀ {Γ A q c p} → Tells q c [ p ] → Down {Γ} {A} q U.hushˢ (U.endˢ (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ]))
  told-end (h ∷ []) = inj₂ ((λ ()) , λ { refl → h })

  DownN : ∀ {Γ A} → Pos → U.Node Γ A → U.Node Γ A → Set₁
  DownN q n n′ = Down q (U.step n) (U.step n′)

  -- THE STEP FUNCTIONS KEEP `Down`: each picks among its parts' steps by
  -- position, so a part shut to a told end leads only where that end
  -- comes first, and what it displaced came no sooner.

  -- Each picks by comparing positions: a part heading before `q` leads
  -- both sides alike, or is passed over on both; past `q`, so is the pick.
  not-< : ∀ {a b} → a <ᵖ b ≡ false → b ≤ᵖ a
  not-< {a} {b} h with <ᵖ-split b a h
  ... | inj₁ lt = inj₂ lt
  ... | inj₂ eq = inj₁ eq

  true≢false : ∀ {ℓ} {X : Set ℓ} → true ≡ false → X
  true≢false ()

  nothing≢just : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} {k : X} → nothing ≡ just k → Y
  nothing≢just ()

  if-true : ∀ {ℓ} {X : Set ℓ} {b} {u v : X} → b ≡ true → (if b then u else v) ≡ u
  if-true refl = refl

  if-false : ∀ {ℓ} {X : Set ℓ} {b} {u v : X} → b ≡ false → (if b then u else v) ≡ v
  if-false refl = refl

  if-twin : ∀ {Γ A} {b b′} {s₁ s₂ s₁′ s₂′ : U.Step Γ A} → b ≡ b′ → Twin s₁ s₁′ → Twin s₂ s₂′ → Twin (if b then s₁ else s₂) (if b′ then s₁′ else s₂′)
  if-twin {b = true}  refl t₁ t₂ = t₁
  if-twin {b = false} refl t₁ t₂ = t₂

  twin-via : ∀ {Γ A} {s₁ s₂ u u′ : U.Step Γ A} → s₁ ≡ u → s₂ ≡ u′ → Twin u u′ → Twin s₁ s₂
  twin-via refl refl t = t

  at-heads : ∀ {Γ A q} (s : U.Step Γ A) {k} → U.headˢ s ≡ just k → q ≤ᵖ k → HeadsS q s
  at-heads s e le e′ with trans (sym e) e′
  ... | refl = le

  before-head : ∀ {Γ A} X (s : U.Step Γ A) {h} → U.headˢ s ≡ just h → U.beforeˢ X s ≡ X <ᵖ h
  before-head X (U.outˢ k _ _) refl = refl
  before-head X (U.skipˢ k _)  refl = refl
  before-head X (U.endˢ k)     refl = refl
  before-head X U.hushˢ        ()

  before-low : ∀ {Γ A q X} (s : U.Step Γ A) → X <ᵖ q ≡ true → HeadsS q s → U.beforeˢ X s ≡ true
  before-low {X = X} (U.outˢ k _ _) lt hs = ≤ᵖ-after {i = X} lt (hs refl)
  before-low {X = X} (U.skipˢ k _)  lt hs = ≤ᵖ-after {i = X} lt (hs refl)
  before-low {X = X} (U.endˢ k)     lt hs = ≤ᵖ-after {i = X} lt (hs refl)
  before-low U.hushˢ        lt hs = refl

  before-twin : ∀ {Γ A} X {s s′ : U.Step Γ A} → Twin s s′ → U.beforeˢ X s ≡ U.beforeˢ X s′
  before-twin X outᵗ  = refl
  before-twin X skipᵗ = refl
  before-twin X endᵗ  = refl
  before-twin X hushᵗ = refl

  -- A child of a position past `q`, against a head before `q`.
  past-ix : ∀ {q k h} → q ≤ᵖ k → h <ᵖ q ≡ true → (k ++ [ ix 0 ]) <ᵖ h ≡ false
  past-ix {q} {k} {h} le lt = <ᵖ-asym h (k ++ [ ix 0 ]) (≤ᵖ-after {i = h} lt (≤ᵖ-trans le (inj₂ (<ᵖ-below k []))))

  -- A twin pair either heads past `q`, or both at one head before it.
  low-or-high : ∀ {Γ A} q {s s′ : U.Step Γ A} → Twin s s′
              → (HeadsS q s × HeadsS q s′) ⊎ Σ Pos λ h → h <ᵖ q ≡ true × U.headˢ s ≡ just h × U.headˢ s′ ≡ just h
  low-or-high q {s} {s′} t = go (U.headˢ s) refl
    where
      go : (m : Maybe Pos) → U.headˢ s ≡ m → (HeadsS q s × HeadsS q s′) ⊎ Σ Pos λ h → h <ᵖ q ≡ true × U.headˢ s ≡ just h × U.headˢ s′ ≡ just h
      go nothing  e = inj₁ ((λ e″ → nothing≢just (trans (sym e) e″)) , (λ e″ → nothing≢just (trans (sym e) (trans (twin-head t) e″))))
      go (just k) e with k <ᵖ q in lt
      ... | true  = inj₂ (k , lt , e , trans (sym (twin-head t)) e)
      ... | false = inj₁ (at-heads s e (not-< lt) , at-heads s′ (trans (sym (twin-head t)) e) (not-< lt))

  union-heads : ∀ {Γ B q} (x : U.Node Γ B) sx y sy → HeadsS q sx → HeadsS q sy → HeadsS q (U.unionˢ x sx y sy)
  union-heads x (U.skipˢ k x₁) y (U.skipˢ k′ y₁) hx hy = if-head (k <ᵖ k′) (U.skipˢ k (U.unionᶜ x₁ y)) (U.skipˢ k′ (U.unionᶜ x y₁)) hx hy
  union-heads x (U.skipˢ k x₁) y (U.outˢ _ _ _)  hx hy = hx
  union-heads x (U.skipˢ k x₁) y (U.endˢ _)      hx hy = hx
  union-heads x (U.skipˢ k x₁) y U.hushˢ         hx hy = hx
  union-heads x (U.outˢ _ _ _) y sy hx hy = hy
  union-heads x (U.endˢ _)     y sy hx hy = hy
  union-heads x U.hushˢ        y sy hx hy = hy

  union-low-y : ∀ {Γ B q k′} (x : U.Node Γ B) sx y y₁ → k′ <ᵖ q ≡ true → HeadsS q sx
              → Σ (U.Node Γ B) λ c → U.unionˢ x sx y (U.skipˢ k′ y₁) ≡ U.skipˢ k′ c
  union-low-y {k′ = k′} x (U.skipˢ k x₁) y y₁ lt hx with k <ᵖ k′ in e
  ... | true  = true≢false (trans (sym e) (<ᵖ-asym k′ k (≤ᵖ-after {i = k′} lt (hx refl))))
  ... | false = _ , refl
  union-low-y x (U.outˢ _ _ _) y y₁ lt hx = _ , refl
  union-low-y x (U.endˢ _)     y y₁ lt hx = _ , refl
  union-low-y x U.hushˢ        y y₁ lt hx = _ , refl

  union-low-x : ∀ {Γ B q k} (x x₁ y : U.Node Γ B) {sy} → k <ᵖ q ≡ true → HeadsS q sy → Hushed sy
              → Σ (U.Node Γ B) λ c → U.unionˢ x (U.skipˢ k x₁) y sy ≡ U.skipˢ k c
  union-low-x {k = k} x x₁ y lt hy (skipʰ {k′}) with k <ᵖ k′ in e
  ... | true  = _ , refl
  ... | false = true≢false (trans (sym (≤ᵖ-after {i = k} lt (hy refl))) e)
  union-low-x x x₁ y lt hy hushʰ = _ , refl

  skips-down : ∀ {Γ A q k} {s s′ : U.Step Γ A} {c c′} → s ≡ U.skipˢ k c → s′ ≡ U.skipˢ k c′ → Down q s s′
  skips-down refl refl = inj₁ skipᵗ

  -- A union's right side must be a rest's step: a non-skip there is
  -- dropped whole, so an end before `q` would vanish under a new left skip.
  union-down : ∀ {Γ B q} (x x′ y y′ : U.Node Γ B) sx sx′ sy sy′ → Hushed sy → Hushed sy′ → Down q sx sx′ → Down q sy sy′
             → Down q (U.unionˢ x sx y sy) (U.unionˢ x′ sx′ y′ sy′)
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ outᵗ)  dy = dy
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ endᵗ)  dy = dy
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ hushᵗ) dy = dy
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ (skipᵗ {k})) (inj₁ (skipᵗ {k′})) with k <ᵖ k′
  ... | true  = inj₁ skipᵗ
  ... | false = inj₁ skipᵗ
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ skipᵗ) (inj₁ outᵗ)  = inj₁ skipᵗ
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ skipᵗ) (inj₁ endᵗ)  = inj₁ skipᵗ
  union-down x x′ y y′ _ _ _ _ hy hy′ (inj₁ skipᵗ) (inj₁ hushᵗ) = inj₁ skipᵗ
  union-down {q = q} x x′ y y′ _ _ sy sy′ hy hy′ (inj₁ (skipᵗ {k} {a} {a′})) (inj₂ (h , h′)) with k <ᵖ q in e
  ... | true  = skips-down (proj₂ (union-low-x x a y e h hy)) (proj₂ (union-low-x x′ a′ y′ e h′ hy′))
  ... | false = inj₂ (union-heads x (U.skipˢ k a) y sy (at-heads (U.skipˢ k a) refl (not-< e)) h
                    , union-heads x′ (U.skipˢ k a′) y′ sy′ (at-heads (U.skipˢ k a′) refl (not-< e)) h′)
  union-down x x′ y y′ sx sx′ sy sy′ hy hy′ (inj₂ (hx , hx′)) (inj₂ (h , h′)) = inj₂ (union-heads x sx y sy hx h , union-heads x′ sx′ y′ sy′ hx′ h′)
  union-down {q = q} x x′ y y′ sx sx′ _ _ hy hy′ (inj₂ (hx , hx′)) (inj₁ (skipᵗ {k′} {b₁} {b₁′})) with k′ <ᵖ q in e
  ... | true  = skips-down (proj₂ (union-low-y x sx y b₁ e hx)) (proj₂ (union-low-y x′ sx′ y′ b₁′ e hx′))
  ... | false = inj₂ (union-heads x sx y (U.skipˢ k′ b₁) hx (at-heads (U.skipˢ k′ b₁) refl (not-< e))
                    , union-heads x′ sx′ y′ (U.skipˢ k′ b₁′) hx′ (at-heads (U.skipˢ k′ b₁′) refl (not-< e)))
  union-down x x′ y y′ sx sx′ _ _ hy hy′ (inj₂ (hx , hx′)) (inj₁ hushᵗ) = inj₂ (union-heads x sx y U.hushˢ hx (λ ()) , union-heads x′ sx′ y′ U.hushˢ hx′ (λ ()))
  union-down x x′ y y′ sx sx′ _ _ () hy′ (inj₂ _) (inj₁ outᵗ)
  union-down x x′ y y′ sx sx′ _ _ () hy′ (inj₂ _) (inj₁ endᵗ)

  postulate
    -- A burst steps as before, or past `q`, when its source's step and
    -- rest do.  False: a source's rest can head before its own step, so
    -- a step moved out of the burst's range falls back onto a rest
    -- twinned below `q`.
    bursts-down : ∀ {Γ A B q} r (t t′ : U.Node Γ A) (st st′ : U.Step Γ A) → Down q st st′ → Down q (U.restˢ {B = B} t) (U.restˢ {B = B} t′)
                → Down {Γ} {B} q (U.burstsˢ r t st) (U.burstsˢ r t′ st′)

  body-twin : ∀ {Γ A B} r (s s′ : U.Source Γ A) {sb sb′ : U.Step (A ∷ Γ) B} → Twin sb sb′ → Twin (U.bodyˢ r s sb) (U.bodyˢ r s′ sb′)
  body-twin r s s′ outᵗ  = outᵗ
  body-twin r s s′ skipᵗ = skipᵗ
  body-twin r s s′ endᵗ  = endᵗ
  body-twin r s s′ hushᵗ = hushᵗ

  shut-twin : ∀ {Γ A B} r c (t t′ : U.Node Γ A) {sb sb′ : U.Step (A ∷ Γ) B} → Twin sb sb′ → Twin (U.shutˢᵗ r c t sb) (U.shutˢᵗ r c t′ sb′)
  shut-twin r c t t′ outᵗ  = outᵗ
  shut-twin r c t t′ skipᵗ = skipᵗ
  shut-twin r c t t′ endᵗ  = endᵗ
  shut-twin r c t t′ hushᵗ = hushᵗ

  -- A body heading before `q`, against a source heading past it: the body leads.
  source-low : ∀ {Γ A B q h} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) ss → h <ᵖ q ≡ true → U.headˢ sb ≡ just h → HeadsS q ss
             → U.sourceˢ r b sb s ss ≡ U.bodyˢ r (U.live s) sb
  source-low r b sb s (U.outˢ k a s′) lt hd hs = if-false (trans (before-head (k ++ [ ix 0 ]) sb hd) (past-ix (hs refl) lt))
  source-low r b sb s (U.skipˢ k s′)  lt hd hs = if-false (trans (before-head (k ++ [ ix 0 ]) sb hd) (past-ix (hs refl) lt))
  source-low r b sb s (U.endˢ c)      lt hd hs = if-false (trans (before-head (c ++ [ ix 0 ]) sb hd) (past-ix (hs refl) lt))
  source-low r b sb s U.hushˢ         lt hd hs = refl

  source-down : ∀ {Γ A B q} r (b b′ : U.Node (A ∷ Γ) B) (s s′ : U.Node Γ A) sb sb′ ss ss′ → Down q sb sb′ → Down q ss ss′
              → Down q (U.sourceˢ r b sb s ss) (U.sourceˢ r b′ sb′ s′ ss′)
  source-down r b b′ s s′ sb sb′ _ _ (inj₁ tb) (inj₁ (outᵗ {k}))  = inj₁ (if-twin (before-twin (k ++ [ ix 0 ]) tb) skipᵗ (body-twin r (U.live s) (U.live s′) tb))
  source-down r b b′ s s′ sb sb′ _ _ (inj₁ tb) (inj₁ (skipᵗ {k})) = inj₁ (if-twin (before-twin (k ++ [ ix 0 ]) tb) skipᵗ (body-twin r (U.live s) (U.live s′) tb))
  source-down r b b′ s s′ sb sb′ _ _ (inj₁ tb) (inj₁ (endᵗ {k}))  = inj₁ (if-twin (before-twin (k ++ [ ix 0 ]) tb) skipᵗ (body-twin r (U.live s) (U.live s′) tb))
  source-down r b b′ s s′ sb sb′ _ _ (inj₁ tb) (inj₁ hushᵗ)       = inj₁ (body-twin r (U.live s) (U.live s′) tb)
  source-down {q = q} r b b′ s s′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ (outᵗ {k} {a} {c} {c′})) with (k ++ [ ix 0 ]) <ᵖ q in e
  ... | true  = inj₁ (twin-via (if-true (before-low sb e hb)) (if-true (before-low sb′ e hb′)) skipᵗ)
  ... | false = inj₂ ( if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k (just a) b) (U.live c))) (U.bodyˢ r (U.live s) sb) (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k (just a) b) (U.live c))) refl (not-< e)) (body-head r (U.live s) sb hb)
                     , if-head (U.beforeˢ (k ++ [ ix 0 ]) sb′) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k (just a) b′) (U.live c′))) (U.bodyˢ r (U.live s′) sb′) (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k (just a) b′) (U.live c′))) refl (not-< e)) (body-head r (U.live s′) sb′ hb′))
  source-down {q = q} r b b′ s s′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ (skipᵗ {k} {c} {c′})) with (k ++ [ ix 0 ]) <ᵖ q in e
  ... | true  = inj₁ (twin-via (if-true (before-low sb e hb)) (if-true (before-low sb′ e hb′)) skipᵗ)
  ... | false = inj₂ ( if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k nothing b) (U.live c))) (U.bodyˢ r (U.live s) sb) (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k nothing b) (U.live c))) refl (not-< e)) (body-head r (U.live s) sb hb)
                     , if-head (U.beforeˢ (k ++ [ ix 0 ]) sb′) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k nothing b′) (U.live c′))) (U.bodyˢ r (U.live s′) sb′) (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.feed (here refl) k nothing b′) (U.live c′))) refl (not-< e)) (body-head r (U.live s′) sb′ hb′))
  source-down {q = q} r b b′ s s′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ (endᵗ {k})) with (k ++ [ ix 0 ]) <ᵖ q in e
  ... | true  = inj₁ (twin-via (if-true (before-low sb e hb)) (if-true (before-low sb′ e hb′)) skipᵗ)
  ... | false = inj₂ ( if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.shut (here refl) k b) (U.ended k (U.restᶜ s)))) (U.bodyˢ r (U.live s) sb) (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.shut (here refl) k b) (U.ended k (U.restᶜ s)))) refl (not-< e)) (body-head r (U.live s) sb hb)
                     , if-head (U.beforeˢ (k ++ [ ix 0 ]) sb′) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.shut (here refl) k b′) (U.ended k (U.restᶜ s′)))) (U.bodyˢ r (U.live s′) sb′) (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r (U.shut (here refl) k b′) (U.ended k (U.restᶜ s′)))) refl (not-< e)) (body-head r (U.live s′) sb′ hb′))
  source-down r b b′ s s′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ hushᵗ) = inj₂ (body-head r (U.live s) sb hb , body-head r (U.live s′) sb′ hb′)
  source-down r b b′ s s′ sb sb′ ss ss′ (inj₂ (hb , hb′)) (inj₂ (hs , hs′)) = inj₂ (source-head r b sb s ss hb hs , source-head r b′ sb′ s′ ss′ hb′ hs′)
  source-down {q = q} r b b′ s s′ sb sb′ ss ss′ (inj₁ tb) (inj₂ (hs , hs′)) with low-or-high q tb
  ... | inj₁ (hb , hb′) = inj₂ (source-head r b sb s ss hb hs , source-head r b′ sb′ s′ ss′ hb′ hs′)
  ... | inj₂ (h , lt , e , e′) = inj₁ (twin-via (source-low r b sb s ss lt e hs) (source-low r b′ sb′ s′ ss′ lt e′ hs′) (body-twin r (U.live s) (U.live s′) tb))

  ended-heads : ∀ {Γ A B q} r c (b : U.Node (A ∷ Γ) B) sb (t : U.Node Γ A) st → HeadsS q sb → HeadsS q st → HeadsS q (U.endedˢ r b sb c t st)
  ended-heads r c b sb t (U.skipˢ k t′) hb hs =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b (U.ended c t′))) (U.shutˢᵗ r c t sb)
      (child-skip k (ix 0) (U.connectᶜ r b (U.ended c t′)) hs) (shut-heads-step r c t sb hb)
  ended-heads r c b sb t (U.outˢ _ _ _) hb hs = shut-heads-step r c t sb hb
  ended-heads r c b sb t (U.endˢ _)     hb hs = shut-heads-step r c t sb hb
  ended-heads r c b sb t U.hushˢ        hb hs = shut-heads-step r c t sb hb

  ended-low : ∀ {Γ A B q h} r c (b : U.Node (A ∷ Γ) B) sb (t : U.Node Γ A) st → h <ᵖ q ≡ true → U.headˢ sb ≡ just h → HeadsS q st
            → U.endedˢ r b sb c t st ≡ U.shutˢᵗ r c t sb
  ended-low r c b sb t (U.skipˢ k t′) lt hd hs = if-false (trans (before-head (k ++ [ ix 0 ]) sb hd) (past-ix (hs refl) lt))
  ended-low r c b sb t (U.outˢ _ _ _) lt hd hs = refl
  ended-low r c b sb t (U.endˢ _)     lt hd hs = refl
  ended-low r c b sb t U.hushˢ        lt hd hs = refl

  ended-down : ∀ {Γ A B q} r c (b b′ : U.Node (A ∷ Γ) B) (t t′ : U.Node Γ A) sb sb′ st st′ → Down q sb sb′ → Down q st st′
             → Down q (U.endedˢ r b sb c t st) (U.endedˢ r b′ sb′ c t′ st′)
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₁ tb) (inj₁ (skipᵗ {k})) = inj₁ (if-twin (before-twin (k ++ [ ix 0 ]) tb) skipᵗ (shut-twin r c t t′ tb))
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₁ tb) (inj₁ outᵗ)  = inj₁ (shut-twin r c t t′ tb)
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₁ tb) (inj₁ endᵗ)  = inj₁ (shut-twin r c t t′ tb)
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₁ tb) (inj₁ hushᵗ) = inj₁ (shut-twin r c t t′ tb)
  ended-down {q = q} r c b b′ t t′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ (skipᵗ {k} {t₁} {t₁′})) with (k ++ [ ix 0 ]) <ᵖ q in e
  ... | true  = inj₁ (twin-via (if-true (before-low sb e hb)) (if-true (before-low sb′ e hb′)) skipᵗ)
  ... | false = inj₂ ( if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b (U.ended c t₁))) (U.shutˢᵗ r c t sb)
                         (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b (U.ended c t₁))) refl (not-< e)) (shut-heads-step r c t sb hb)
                     , if-head (U.beforeˢ (k ++ [ ix 0 ]) sb′) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b′ (U.ended c t₁′))) (U.shutˢᵗ r c t′ sb′)
                         (at-heads (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b′ (U.ended c t₁′))) refl (not-< e)) (shut-heads-step r c t′ sb′ hb′))
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ outᵗ)  = inj₂ (shut-heads-step r c t sb hb , shut-heads-step r c t′ sb′ hb′)
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ endᵗ)  = inj₂ (shut-heads-step r c t sb hb , shut-heads-step r c t′ sb′ hb′)
  ended-down r c b b′ t t′ sb sb′ _ _ (inj₂ (hb , hb′)) (inj₁ hushᵗ) = inj₂ (shut-heads-step r c t sb hb , shut-heads-step r c t′ sb′ hb′)
  ended-down r c b b′ t t′ sb sb′ st st′ (inj₂ (hb , hb′)) (inj₂ (hs , hs′)) = inj₂ (ended-heads r c b sb t st hb hs , ended-heads r c b′ sb′ t′ st′ hb′ hs′)
  ended-down {q = q} r c b b′ t t′ sb sb′ st st′ (inj₁ tb) (inj₂ (hs , hs′)) with low-or-high q tb
  ... | inj₁ (hb , hb′) = inj₂ (ended-heads r c b sb t st hb hs , ended-heads r c b′ sb′ t′ st′ hb′ hs′)
  ... | inj₂ (h , lt , e , e′) = inj₁ (twin-via (ended-low r c b sb t st lt e hs) (ended-low r c b′ sb′ t′ st′ lt e′ hs′) (shut-twin r c t t′ tb))

  postulate
    -- A flatMap steps as before, or past `q`, when its outer, lanes and
    -- pool do: the lists keep their lengths and the outer its presence,
    -- so the outer's and lanes' ends with nothing left read alike.
    flat-down : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (ls ls′ : List (U.Node Δ B)) qs (pl pl′ : U.Node Δ B)
              → MP.Pointwise (DownN q) o o′ → LP.Pointwise (DownN q) ls ls′ → DownN q pl pl′
              → DownN q (U.flatMapᶜ op g o ls qs pl) (U.flatMapᶜ op g o′ ls′ qs pl′)

  mutual
    shut-down : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) → Tells q c (untold i b) → DownN q b (U.shut i c b)
    shut-down i c (U.framesᶜ τ e m)            tl = inj₁ (twin-refl _)
    shut-down i c (U.burstᶜ τ r k b)           tl = inj₁ (twin-refl _)
    shut-down i c (U.ofᶜ p k xs)               tl = inj₁ (twin-refl _)
    shut-down i c (U.mapᶜ f n)                 tl = map-down f (U.step n) (U.step (U.shut i c n)) (shut-down i c n tl)
    shut-down i c (U.scanᶜ f z n)              tl = scan-down f z (U.step n) (U.step (U.shut i c n)) (shut-down i c n tl)
    shut-down i c (U.takeWhileᶜ t p n)         tl = take-down t p (U.step n) (U.step (U.shut i c n)) (shut-down i c n tl)
    shut-down i c (U.flatMapᶜ op g o ls qs pl) tl =
      flat-down op g o (U.shutᴹ i c o) ls (U.shutᴸ i c ls) qs pl (U.shut i c pl)
        (shut-downᴹ i c o (++⁻ˡ (untoldᴹ i o) tl))
        (shut-downᴸ i c ls (++⁻ˡ (untoldᴸ i ls) (++⁻ʳ (untoldᴹ i o) tl)))
        (shut-down i c pl (++⁻ʳ (untoldᴸ i ls) (++⁻ʳ (untoldᴹ i o) tl)))
    shut-down i c (U.joinᶜ j p ((_ , just a) ∷ xs) e)  tl = inj₁ outᵗ
    shut-down i c (U.joinᶜ j p ((_ , nothing) ∷ xs) e) tl = inj₁ skipᵗ
    shut-down i c (U.joinᶜ j p [] (just e))            tl = inj₁ endᵗ
    shut-down i c (U.joinᶜ j p [] nothing)             tl with U.same? i j
    ... | nothing   = inj₁ hushᵗ
    ... | just refl = told-end tl
    shut-down i c (U.connectᶜ r b (U.live s))  tl =
      source-down r b (U.shut (there i) c b) s (U.shut i c s) (U.step b) (U.step (U.shut (there i) c b)) (U.step s) (U.step (U.shut i c s))
        (shut-down (there i) c b (++⁻ˡ (untold (there i) b) tl)) (shut-down i c s (++⁻ʳ (untold (there i) b) tl))
    shut-down i c (U.connectᶜ r b (U.ended e t)) tl =
      ended-down r e b (U.shut (there i) c b) t (U.shut i c t) (U.step b) (U.step (U.shut (there i) c b)) (U.step t) (U.step (U.shut i c t))
        (shut-down (there i) c b (++⁻ˡ (untold (there i) b) tl)) (shut-down i c t (++⁻ʳ (untold (there i) b) tl))
    shut-down i c (U.deferᶜ l p ns)            tl = inj₁ (twin-refl _)
    shut-down i c (U.endingᶜ p n)              tl = inj₁ endᵗ
    shut-down i c (U.restᶜ n)                  tl = rest-down i c n tl
    shut-down i c U.idleᶜ                      tl = inj₁ hushᵗ
    shut-down i c (U.unionᶜ x y)               tl =
      union-down x (U.shut i c x) y (U.shut i c y) (U.restˢ x) (U.restˢ (U.shut i c x)) (U.restˢ y) (U.restˢ (U.shut i c y))
        (rest-hushed y) (rest-hushed (U.shut i c y)) (rest-down i c x (++⁻ˡ (untoldʳ i x) tl)) (rest-down i c y (++⁻ʳ (untoldʳ i x) tl))
    shut-down i c (U.burstingᶜ r t)            tl =
      bursts-down r t (U.shut i c t) (U.step t) (U.step (U.shut i c t)) (shut-down i c t (++⁻ˡ (untold i t) tl)) (rest-down i c t (++⁻ʳ (untold i t) tl))
    shut-down i c (U.underᶜ {C = C} s b)       tl =
      under-down s (U.shutˢ i c s) (U.restˢ {B = C} b) (U.restˢ {B = C} (U.shut (there i) c b)) (rest-down (there i) c b tl)

    shut-downᴹ : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (o : Maybe (U.Node Γ B)) → Tells q c (untoldᴹ i o) → MP.Pointwise (DownN q) o (U.shutᴹ i c o)
    shut-downᴹ i c nothing  tl = MP.nothing
    shut-downᴹ i c (just n) tl = MP.just (shut-down i c n tl)

    shut-downᴸ : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (ls : List (U.Node Γ B)) → Tells q c (untoldᴸ i ls) → LP.Pointwise (DownN q) ls (U.shutᴸ i c ls)
    shut-downᴸ i c []       tl = LP.[]
    shut-downᴸ i c (n ∷ ns) tl = shut-down i c n (++⁻ˡ (untold i n) tl) LP.∷ shut-downᴸ i c ns (++⁻ʳ (untold i n) tl)

    rest-down : ∀ {Γ A B C q} (i : A ∈ᴸ Γ) c (n : U.Node Γ B) → Tells q c (untoldʳ i n) → Down q (U.restˢ {B = C} n) (U.restˢ {B = C} (U.shut i c n))
    rest-down i c (U.framesᶜ τ e m)            tl = inj₁ hushᵗ
    rest-down i c (U.burstᶜ τ r k b)           tl = inj₁ hushᵗ
    rest-down i c (U.ofᶜ p k xs)               tl = inj₁ hushᵗ
    rest-down i c (U.mapᶜ f n)                 tl = rest-down i c n tl
    rest-down i c (U.scanᶜ f z n)              tl = rest-down i c n tl
    rest-down i c (U.takeWhileᶜ t p n)         tl = rest-down i c n tl
    rest-down i c (U.flatMapᶜ op g o ls qs pl) tl =
      union-down (U.outerᶜ o) (U.outerᶜ o′) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ pl)) (U.unionᶜ (U.restsᶜ ls′) (U.restᶜ pl′))
        (U.restᴹ o) (U.restᴹ o′) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ pl) (U.restˢ pl)) (U.unionˢ (U.restsᶜ ls′) (U.restsˢ ls′) (U.restᶜ pl′) (U.restˢ pl′))
        (union-hushed (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ pl) (U.restˢ pl) (rest-hushed pl))
        (union-hushed (U.restsᶜ ls′) (U.restsˢ ls′) (U.restᶜ pl′) (U.restˢ pl′) (rest-hushed pl′))
        (rest-downᴹ i c o (++⁻ˡ (untoldʳᴹ i o) tl))
        (union-down (U.restsᶜ ls) (U.restsᶜ ls′) (U.restᶜ pl) (U.restᶜ pl′) (U.restsˢ ls) (U.restsˢ ls′) (U.restˢ pl) (U.restˢ pl′)
          (rest-hushed pl) (rest-hushed pl′)
          (rests-down i c ls (++⁻ˡ (untoldʳᴸ i ls) (++⁻ʳ (untoldʳᴹ i o) tl)))
          (rest-down i c pl (++⁻ʳ (untoldʳᴸ i ls) (++⁻ʳ (untoldʳᴹ i o) tl))))
      where o′ = U.shutᴹ i c o
            ls′ = U.shutᴸ i c ls
            pl′ = U.shut i c pl
    rest-down i c (U.joinᶜ j p xs e)           tl = inj₁ hushᵗ
    rest-down i c (U.connectᶜ {B = C} r b (U.live s)) tl =
      union-down (U.burstingᶜ r s) (U.burstingᶜ r s′) (U.underᶜ (U.live s) b) (U.underᶜ (U.live s′) b′)
        (U.burstsˢ r s (U.step s)) (U.burstsˢ r s′ (U.step s′)) (U.underˢ (U.live s) (U.restˢ {B = C} b)) (U.underˢ (U.live s′) (U.restˢ {B = C} b′))
        (under-hushed (U.live s) (U.restˢ {B = C} b)) (under-hushed (U.live s′) (U.restˢ {B = C} b′))
        (bursts-down r s s′ (U.step s) (U.step s′) (shut-down i c s (++⁻ˡ (untold i s) tlₛ)) (rest-down i c s (++⁻ʳ (untold i s) tlₛ)))
        (under-down (U.live s) (U.live s′) (U.restˢ {B = C} b) (U.restˢ {B = C} b′) (rest-down (there i) c b (++⁻ˡ (untoldʳ (there i) b) tl)))
      where s′ = U.shut i c s
            b′ = U.shut (there i) c b
            tlₛ = ++⁻ʳ (untoldʳ (there i) b) tl
    rest-down i c (U.connectᶜ {B = C} r b (U.ended e t)) tl =
      union-down (U.burstingᶜ r t) (U.burstingᶜ r t′) (U.underᶜ (U.ended e t) b) (U.underᶜ (U.ended e t′) b′)
        (U.burstsˢ r t (U.step t)) (U.burstsˢ r t′ (U.step t′)) (U.underˢ (U.ended e t) (U.restˢ {B = C} b)) (U.underˢ (U.ended e t′) (U.restˢ {B = C} b′))
        (under-hushed (U.ended e t) (U.restˢ {B = C} b)) (under-hushed (U.ended e t′) (U.restˢ {B = C} b′))
        (bursts-down r t t′ (U.step t) (U.step t′) (shut-down i c t (++⁻ˡ (untold i t) tlₜ)) (rest-down i c t (++⁻ʳ (untold i t) tlₜ)))
        (under-down (U.ended e t) (U.ended e t′) (U.restˢ {B = C} b) (U.restˢ {B = C} b′) (rest-down (there i) c b (++⁻ˡ (untoldʳ (there i) b) tl)))
      where t′ = U.shut i c t
            b′ = U.shut (there i) c b
            tlₜ = ++⁻ʳ (untoldʳ (there i) b) tl
    rest-down i c (U.deferᶜ l p ns)            tl = inj₁ hushᵗ
    rest-down i c (U.endingᶜ p n)              tl = rest-down i c n tl
    rest-down i c (U.restᶜ n)                  tl = rest-down i c n tl
    rest-down i c U.idleᶜ                      tl = inj₁ hushᵗ
    rest-down i c (U.unionᶜ x y)               tl =
      union-down (U.restᶜ x) (U.restᶜ (U.shut i c x)) (U.restᶜ y) (U.restᶜ (U.shut i c y))
        (U.restˢ x) (U.restˢ (U.shut i c x)) (U.restˢ y) (U.restˢ (U.shut i c y))
        (rest-hushed y) (rest-hushed (U.shut i c y)) (rest-down i c x (++⁻ˡ (untoldʳ i x) tl)) (rest-down i c y (++⁻ʳ (untoldʳ i x) tl))
    rest-down i c (U.burstingᶜ r t)            tl =
      bursts-down r t (U.shut i c t) (U.step t) (U.step (U.shut i c t)) (shut-down i c t (++⁻ˡ (untold i t) tl)) (rest-down i c t (++⁻ʳ (untold i t) tl))
    rest-down i c (U.underᶜ {C = C} s b)       tl =
      under-down s (U.shutˢ i c s) (U.restˢ {B = C} b) (U.restˢ {B = C} (U.shut (there i) c b)) (rest-down (there i) c b tl)

    rest-downᴹ : ∀ {Γ A B C q} (i : A ∈ᴸ Γ) c (o : Maybe (U.Node Γ B)) → Tells q c (untoldʳᴹ i o) → Down q (U.restᴹ {B = C} o) (U.restᴹ {B = C} (U.shutᴹ i c o))
    rest-downᴹ i c nothing  tl = inj₁ hushᵗ
    rest-downᴹ i c (just n) tl = rest-down i c n tl

    rests-down : ∀ {Γ A B C q} (i : A ∈ᴸ Γ) c (ls : List (U.Node Γ B)) → Tells q c (untoldʳᴸ i ls) → Down q (U.restsˢ {B = C} ls) (U.restsˢ {B = C} (U.shutᴸ i c ls))
    rests-down i c []       tl = inj₁ hushᵗ
    rests-down i c (l ∷ ls) tl =
      union-down (U.restᶜ l) (U.restᶜ (U.shut i c l)) (U.restsᶜ ls) (U.restsᶜ (U.shutᴸ i c ls))
        (U.restˢ l) (U.restˢ (U.shut i c l)) (U.restsˢ ls) (U.restsˢ (U.shutᴸ i c ls))
        (rests-hushed ls) (rests-hushed (U.shutᴸ i c ls)) (rest-down i c l (++⁻ˡ (untoldʳ i l) tl)) (rests-down i c ls (++⁻ʳ (untoldʳ i l) tl))


  -- An ended connect heads where its body and its source's rest do.
  ended-head : ∀ {Γ A B q} r c (b : U.Node (A ∷ Γ) B) (t : U.Node Γ A) (st : U.Step Γ A)
             → Heads q b → HeadsS q st → HeadsS q (U.endedˢ r b (U.step b) c t st)
  ended-head r c b t st hb ht = ended-heads r c b (U.step b) t st hb ht

  -- A shut heads where the node did, or at an end it tells.
  shut-heads : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) → Heads q b → Tells q c (untold i b) → Heads q (U.shut i c b)
  shut-heads i c b hb tl e with shut-down i c b tl
  ... | inj₁ tw       = hb (trans (twin-head tw) e)
  ... | inj₂ (_ , h′) = h′ e

  -- A FLATMAP'S HEAD: its pool's skip, its outer's step or its
  -- earliest lane's, each moved at most a child down.  So it heads no
  -- sooner than `q` whenever its pool, its outer and its lanes do.
  outerˢ-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Node Δ A) (so : U.Step Δ A) ls qs p → HeadsS q so
               → HeadsS q (U.outerˢ op g o so ls qs p)
  outerˢ-heads op g o (U.outˢ k a o′) ls      qs      p hs refl = ≤ᵖ-child k (hs refl)
  outerˢ-heads op g o (U.skipˢ k o′)  ls      qs      p hs refl = hs refl
  outerˢ-heads op g o (U.endˢ c)      []      []      p hs refl = hs refl
  outerˢ-heads op g o (U.endˢ c)      []      (_ ∷ _) p hs refl = hs refl
  outerˢ-heads op g o (U.endˢ c)      (_ ∷ _) qs      p hs refl = hs refl
  outerˢ-heads op g o U.hushˢ         ls      qs      p hs ()

  laneˢ-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) bs l (s : U.Step Δ B) as qs p → HeadsS q s
              → HeadsS q (U.laneˢ op g o bs l s as qs p)
  laneˢ-heads op g o bs l (U.outˢ k b c) as qs p hs refl = hs refl
  laneˢ-heads op g o bs l (U.skipˢ k c)  as qs p hs refl = hs refl
  laneˢ-heads op g nothing  []      l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  []      l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g nothing  []      l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  []      l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g (just o) []      l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) []      l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g (just o) []      l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) []      l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g o bs l U.hushˢ        as qs p hs ()

  OuterHeads : ∀ {Δ A} → Pos → U.Outer Δ A → Set
  OuterHeads q U.doneᵒ      = ⊤
  OuterHeads q (U.runᵒ o s) = HeadsS q s

  EarliestHeads : ∀ {Δ B} → Pos → U.Earliest Δ B → Set
  EarliestHeads q U.none                = ⊤
  EarliestHeads q (U.found k bs l s as) = HeadsS q s

  pick-heads : ∀ {Δ B q} (l : U.Node Δ B) (s : U.Step Δ B) ls m (E : U.Earliest Δ B) → HeadsS q s → EarliestHeads q E
             → EarliestHeads q (U.pick l s ls m E)
  pick-heads l s ls nothing  U.none                  hs he = tt
  pick-heads l s ls nothing  (U.found k bs c sc as)  hs he = he
  pick-heads l s ls (just k) U.none                  hs he = hs
  pick-heads l s ls (just k) (U.found k′ bs c sc as) hs he with k <ᵖ k′
  ... | true  = hs
  ... | false = he

  earliest-heads : ∀ {Δ B q} (ls : List (U.Node Δ B)) → All (Heads q) ls → EarliestHeads q (U.earliest ls)
  earliest-heads []       []        = tt
  earliest-heads (l ∷ ls) (hl ∷ hL) = pick-heads l (U.step l) ls (U.headˢ (U.step l)) (U.earliest ls) hl (earliest-heads ls hL)

  race-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) o (so : U.Step Δ A) mk k bs l (s : U.Step Δ B) as qs p → HeadsS q so → HeadsS q s
             → HeadsS q (U.raceˢ op g o so mk k bs l s as qs p)
  race-heads op g o so nothing   k bs l s as qs p ho hs = laneˢ-heads op g (just o) bs l s as qs p hs
  race-heads op g o so (just k′) k bs l s as qs p ho hs =
    if-head (k′ <ᵖ k) (U.outerˢ op g o so (bs ++ l ∷ as) qs p) (U.laneˢ op g (just o) bs l s as qs p)
      (outerˢ-heads op g o so (bs ++ l ∷ as) qs p ho) (laneˢ-heads op g (just o) bs l s as qs p hs)

  go-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Outer Δ A) ls qs p (E : U.Earliest Δ B) → OuterHeads q o → EarliestHeads q E
           → HeadsS q (U.goˢ op g o ls qs p E)
  go-heads op g U.doneᵒ       ls qs p U.none                ho he ()
  go-heads op g (U.runᵒ o so) ls qs p U.none                ho he = outerˢ-heads op g o so ls qs p ho
  go-heads op g U.doneᵒ       ls qs p (U.found k bs l s as) ho he = laneˢ-heads op g nothing bs l s as qs p he
  go-heads op g (U.runᵒ o so) ls qs p (U.found k bs l s as) ho he = race-heads op g o so (U.headˢ so) k bs l s as qs p ho he

  flatˢ-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Outer Δ A) ls qs p (sp : U.Step Δ B) (E : U.Earliest Δ B)
              → HeadsS q sp → OuterHeads q o → EarliestHeads q E → HeadsS q (U.flatˢ op g o ls qs p sp E)
  flatˢ-heads op g o ls qs p (U.skipˢ k p′) E hp ho he =
    if-head (U.aheadˢ k o E) (U.skipˢ k (U.flatMapᶜ op g (U.nodeᵒ o) ls qs p′)) (U.goˢ op g o ls qs p E) hp (go-heads op g o ls qs p E ho he)
  flatˢ-heads op g o ls qs p (U.outˢ k b p′) E hp ho he = go-heads op g o ls qs p E ho he
  flatˢ-heads op g o ls qs p (U.endˢ k)      E hp ho he = go-heads op g o ls qs p E ho he
  flatˢ-heads op g o ls qs p U.hushˢ         E hp ho he = go-heads op g o ls qs p E ho he

  outer-of : ∀ {Δ A q} (o : Maybe (U.Node Δ A)) → (∀ {c} → o ≡ just c → Heads q c) → OuterHeads q (U.outerOf o)
  outer-of nothing  ho = tt
  outer-of (just c) ho = ho refl

  -- DEAD ROUTE: the flatMap's old head in place of its pool's.  A pool
  --   skip at the outer's out position, the flatMap a child under it,
  --   is first once the outer is done.
  heads-flat : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) (L : List (U.Node Δ B)) Q pl
             → Heads q pl → (∀ {c} → o ≡ just c → Heads q c) → All (Heads q) L → Heads q (U.flatMapᶜ op g o L Q pl)
  heads-flat op g o L Q pl hp ho hL = flatˢ-heads op g (U.outerOf o) L Q pl (U.step pl) (U.earliest L) hp (outer-of o ho) (earliest-heads L hL)

