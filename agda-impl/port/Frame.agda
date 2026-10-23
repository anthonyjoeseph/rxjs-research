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
open import port.Sorted using (_≤ᵖ_; ≤ᵖ-child)
open import port.Told using (untoldᴶ; untold; untoldʳ; untoldʳᴹ; untoldʳᴸ; untoldᵇ; untoldᴹ; untoldᴸ; untoldˢ; Tells)
open import Data.Unit using (⊤; tt)

open import denotation.MonotonicList.Events using (Events∞; Pos; ix; _<ᵖ_)
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

  -- An ended connect heads where its body and its source's rest do.
  ended-head : ∀ {Γ A B q} r c (b : U.Node (A ∷ Γ) B) (t : U.Node Γ A) (st : U.Step Γ A)
             → Heads q b → HeadsS q st → HeadsS q (U.endedˢ r b (U.step b) c t st)
  ended-head r c b t (U.skipˢ k t′) hb ht =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) (U.step b)) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b (U.ended c t′))) (U.shutˢᵗ r c t (U.step b))
      (child-skip k (ix 0) (U.connectᶜ r b (U.ended c t′)) ht) (shut-heads-step r c t (U.step b) hb)
  ended-head r c b t (U.outˢ _ _ _) hb ht = shut-heads-step r c t (U.step b) hb
  ended-head r c b t (U.endˢ _)     hb ht = shut-heads-step r c t (U.step b) hb
  ended-head r c b t U.hushˢ        hb ht = shut-heads-step r c t (U.step b) hb

  postulate
    -- A shut heads where the node did, or at an end it tells.
    --
    -- SUSPECT: `Heads` reads a node's step alone.  A burst whose step
    -- skips inside its range heads where the skip is, and its rest, which
    -- the shut leaves alone, need not; a shut that moves the step out of
    -- the range falls back to that rest.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Frame.agda
    --
    -- DEAD ROUTE: by steps kept `Down` through every step function. A burst's step falls back to its rest, and no `Down` of its step bounds its rest, so the burst case takes a premise that names neither node it is about.
    shut-heads : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) → Heads q b → Tells q c (untold i b) → Heads q (U.shut i c b)

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

