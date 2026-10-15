{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; out; skip; end; hush; _<ᵖ_; root)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)

open Events∞

-- Nothing in `e` comes before `k`.
Atop : ∀ {A} → Pos → Events A → Set
Atop k (out h _ _) = h <ᵖ k ≡ false
Atop k (skip h _)  = h <ᵖ k ≡ false
Atop k (end h)     = h <ᵖ k ≡ false
Atop k hush        = ⊤

-- Each event at or before the one after it.
mutual
  Orders : ∀ {A} → Events A → Set
  Orders (out k _ r) = Atop k (force r) × Ordered (force r)
  Orders (skip k r)  = Atop k (force r) × Ordered (force r)
  Orders (end _)     = ⊤
  Orders hush        = ⊤

  record Ordered {A} (e : Events A) : Set where
    coinductive
    field ordered : Orders e

open Ordered public

-- Every node's meaning in order, read in its own environment: a
-- connect's body reading its source's, a flatMap's lanes yet to
-- subscribe, wherever they will be, reading its own.
mutual
  Placed : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Placed c ρ = Ordered (U.meaning c ρ) × Within c ρ

  Within : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Within (U.mapᶜ f c)               ρ = Placed c ρ
  Within (U.scanᶜ f z c)            ρ = Placed c ρ
  Within (U.takeWhileᶜ i p c)       ρ = Placed c ρ
  Within (U.flatMapᶜ op g o ls qs)  ρ = Placedᴹ o ρ × Placedᴸ ls ρ × (∀ a q → Placed (g a q) ρ)
  Within (U.connectᶜ b (U.live s))  ρ = Placed b (U.meaning s ρ ∷ᴬ ρ) × Placed s ρ
  Within (U.connectᶜ b (U.ended c)) ρ = Placed b (end c ∷ᴬ ρ)
  Within _                          ρ = ⊤

  Placedᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  Placedᴹ nothing  ρ = ⊤
  Placedᴹ (just c) ρ = Placed c ρ

  Placedᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  Placedᴸ []       ρ = ⊤
  Placedᴸ (c ∷ cs) ρ = Placed c ρ × Placedᴸ cs ρ

-- Each connect's source in order.
Sorted : ∀ {Γ} → NEnv Γ → Set
Sorted []ᴬ      = ⊤
Sorted (e ∷ᴬ ρ) = Ordered e × Sorted ρ

sorted-lookup : ∀ {Γ A} (ρ : NEnv Γ) → Sorted ρ → (i : A ∈ Γ) → Ordered (lookup ρ i)
sorted-lookup (e ∷ᴬ ρ) (o , so) (here refl) = o
sorted-lookup (e ∷ᴬ ρ) (o , so) (there i)   = sorted-lookup ρ so i

-- A value changed, or a running total, keeps its position.
atop-map : ∀ {A B} (f : A → B) k (e : Events A) → Atop k e → Atop k (M.mapᴱ f e)
atop-map f k (out _ _ _) at = at
atop-map f k (skip _ _)  at = at
atop-map f k (end _)     at = at
atop-map f k hush        at = at

ordered-map : ∀ {A B} (f : A → B) (e : Events A) → Ordered e → Ordered (M.mapᴱ f e)
ordered (ordered-map f (out k a r) o) = atop-map f k (force r) (proj₁ (ordered o)) , ordered-map f (force r) (proj₂ (ordered o))
ordered (ordered-map f (skip k r)  o) = atop-map f k (force r) (proj₁ (ordered o)) , ordered-map f (force r) (proj₂ (ordered o))
ordered (ordered-map f (end k)     o) = tt
ordered (ordered-map f hush        o) = tt

atop-scan : ∀ {A B} (f : B → A → B) z k (e : Events A) → Atop k e → Atop k (M.scanᴱ f z e)
atop-scan f z k (out _ _ _) at = at
atop-scan f z k (skip _ _)  at = at
atop-scan f z k (end _)     at = at
atop-scan f z k hush        at = at

ordered-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Ordered e → Ordered (M.scanᴱ f z e)
ordered (ordered-scan f z (out k a r) o) = atop-scan f (f z a) k (force r) (proj₁ (ordered o)) , ordered-scan f (f z a) (force r) (proj₂ (ordered o))
ordered (ordered-scan f z (skip k r)  o) = atop-scan f z k (force r) (proj₁ (ordered o)) , ordered-scan f z (force r) (proj₂ (ordered o))
ordered (ordered-scan f z (end k)     o) = tt
ordered (ordered-scan f z hush        o) = tt

start-within : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Within (U.startᶜ p m) ρ
start-within p (M.at zero _ _)    ρ = tt
start-within p (M.at (suc _) _ _) ρ = tt
start-within p M.done             ρ = tt
start-within p M.quiet            ρ = tt

postulate
  -- A COLD'S RUN IS IN ORDER: a burst, or its frames, from the start.
  ordered-start : ∀ {A} p (m : From A 0) → Ordered (M.start p m)

  -- A LIST'S RUN IS IN ORDER: its values at rising indices, then its end.
  ordered-of : ∀ {A} p i (xs : List A) → Ordered (M.ofᴱ p i xs)

  -- A CUT KEEPS THE ORDER: the run up to the first value failing, then
  -- its end.
  ordered-take : ∀ {A} i (p : A → Bool) (e : Events A) → Ordered e → Ordered (M.takeWhileᴱ i p e)

  -- A JOIN KEEPS ITS SOURCE'S ORDER: what it missed as skips just past
  -- the join, the rest rekeyed under it.
  ordered-rejoin : ∀ {A} p (e : Events A) → Ordered e → Ordered (M.rejoin p e)

  -- A CONNECT'S SOURCE MERGES INTO ITS BODY IN ORDER: each source step a
  -- skip just past it, ahead of the body's later events.
  ordered-beside : ∀ {A B} (b : Events B) (s : Events A) → Ordered b → Ordered s → Ordered (M.beside b s)

  -- A FLATMAP MERGES IN ORDER: its outer's run, and each lane's, each
  -- in order and atop where it subscribes.
  --
  -- The risk is a tie: an outer value at `q` shows as a skip just past
  -- `q`, so an outer skip at that same `q` after it would show before it.
  -- `Ordered` allows ties, and a connect's body event at its source's
  -- skip position shows ahead of that skip.
  ordered-flat : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (ρ : NEnv Γ) → Ordered (U.meaning o ρ)
               → (∀ a q → Ordered (U.meaning (g a q) ρ) × Atop q (U.meaning (g a q) ρ))
               → Ordered (U.meaning (U.flatMapᶜ op g (just o) [] []) ρ)

  -- A DEFER'S RUN IS IN ORDER: its program, reached, over sources in
  -- order.
  ordered-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Ordered (U.meaning (U.deferᶜ l p []) ρ)

  -- A SUBSCRIPTION SHOWS NOTHING BEFORE WHERE IT IS MADE.
  atop-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Atop p (U.meaning (U.subscribe o p) ρ)

-- A program subscribed anywhere, over sources in order, is placed.
placed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Placed (U.subscribe o p) ρ
placed-sub (cold c) p ρ so =
  subst Ordered (sym (U.start-meaning p (lower c) ρ)) (ordered-start p (lower c)) , start-within p (lower c) ρ
placed-sub empty p ρ so = record { ordered = tt } , tt
placed-sub (of xs) p ρ so = ordered-of p 0 xs , tt
placed-sub (map f s) p ρ so = ordered-map f _ (proj₁ ps) , ps
  where ps = placed-sub s p ρ so
placed-sub (scan f z s) p ρ so = ordered-scan f z _ (proj₁ ps) , ps
  where ps = placed-sub s p ρ so
placed-sub (takeWhile i q s) p ρ so = ordered-take i q _ (proj₁ ps) , ps
  where ps = placed-sub s p ρ so
placed-sub (flatMap op f s) p ρ so =
  ordered-flat op (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ (proj₁ ps) (λ a q → proj₁ (placed-sub (f a) q ρ so) , atop-sub (f a) q ρ)
  , ps , tt , λ a q → placed-sub (f a) q ρ so
  where ps = placed-sub s p ρ so
placed-sub (connect s b) p ρ so = ordered-beside _ _ (proj₁ pb) (proj₁ ps) , pb , ps
  where ps = placed-sub s (p ++ [ M.ix 1 ]) ρ so
        pb = placed-sub b (p ++ [ M.ix 0 ]) (U.meaning (U.subscribe s (p ++ [ M.ix 1 ])) ρ ∷ᴬ ρ) (proj₁ ps , so)
placed-sub (connected i) p ρ so = ordered-rejoin p _ (sorted-lookup ρ so i) , tt
placed-sub (defer l) p ρ so = ordered-defer l p ρ so , tt

-- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root is
-- placed.
placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
placed-subscribe o = placed-sub o root []ᴬ tt
