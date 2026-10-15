{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; out; skip; end; hush; ix; _<ᵖ_; root)
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

-- `h` lies strictly inside `k`'s subtree.
data Ext (k : Pos) : Pos → Set where
  ext : ∀ l ls → Ext k (k ++ l ∷ ls)

-- `e`'s first is no proper extension of `k`.
Apart : ∀ {A} → Pos → Events A → Set
Apart k (out h _ _) = ¬ Ext k h
Apart k (skip h _)  = ¬ Ext k h
Apart k (end h)     = ¬ Ext k h
Apart k hush        = ⊤

-- `e`'s first is strictly past `k`, and no proper extension of it.
Past : ∀ {A} → Pos → Events A → Set
Past k (out h _ _) = k <ᵖ h ≡ true × ¬ Ext k h
Past k (skip h _)  = k <ᵖ h ≡ true × ¬ Ext k h
Past k (end h)     = k <ᵖ h ≡ true × ¬ Ext k h
Past k hush        = ⊤

-- Never a step inside the position just left, and never one tied with
-- a value.  A rejoin keys a source's event at `q` under `q`, so a
-- source stepping inside `q` sorts first, and a flatMap shows a value
-- at `q` just past `q`, so a source stepping to `q` again sorts first.
mutual
  Steadies : ∀ {A} → Events A → Set
  Steadies (out k _ r) = Past k (force r) × Steady (force r)
  Steadies (skip k r)  = Apart k (force r) × Steady (force r)
  Steadies (end _)     = ⊤
  Steadies hush        = ⊤

  record Steady {A} (e : Events A) : Set where
    coinductive
    field steady : Steadies e

open Steady public

-- No event of `e` lies inside `p`'s subtree.
mutual
  Clears : ∀ {A} → Pos → Events A → Set
  Clears p (out h _ r) = ¬ Ext p h × Clear p (force r)
  Clears p (skip h r)  = ¬ Ext p h × Clear p (force r)
  Clears p (end h)     = ¬ Ext p h
  Clears p hush        = ⊤

  record Clear {A} (p : Pos) (e : Events A) : Set where
    coinductive
    field clear : Clears p e

open Clear public

-- Every source clear of `p`: the subtree a subscription at `p` keys.
Clearᴱ : ∀ {Γ} → Pos → NEnv Γ → Set
Clearᴱ p []ᴬ      = ⊤
Clearᴱ p (e ∷ᴬ ρ) = Clear p e × Clearᴱ p ρ

-- `e` shows an event at `k`.
data Reaches {A} (k : Pos) : Events A → Set where
  out-here   : ∀ {a r} → Reaches k (out k a r)
  skip-here  : ∀ {r} → Reaches k (skip k r)
  out-there  : ∀ {h a r} → Reaches k (force r) → Reaches k (out h a r)
  skip-there : ∀ {h r} → Reaches k (force r) → Reaches k (skip h r)

-- Every node's meaning in order, read in its own environment: a
-- connect's body reading its source's, a flatMap's lanes yet to
-- subscribe reading its own, each where the flatMap shows a skip just
-- before it, as it does when it admits one.
mutual
  Placed : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Placed c ρ = Ordered (U.meaning c ρ) × Within c ρ

  Within : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Within (U.mapᶜ f c)               ρ = Placed c ρ
  Within (U.scanᶜ f z c)            ρ = Placed c ρ
  Within (U.takeWhileᶜ i p c)       ρ = Placed c ρ
  Within (U.flatMapᶜ op g o ls qs)  ρ = Placedᴹ o ρ × Placedᴸ ls ρ
    × (∀ a x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.flatMapᶜ op g o ls qs) ρ) → Placed (g a (x ++ [ ix 1 ])) ρ)
  Within (U.connectᶜ b (U.live s))  ρ = Placed b (U.meaning s ρ ∷ᴬ ρ) × Placed s ρ
  Within (U.connectᶜ b (U.ended c)) ρ = Placed b (end c ∷ᴬ ρ)
  Within _                          ρ = ⊤

  Placedᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  Placedᴹ nothing  ρ = ⊤
  Placedᴹ (just c) ρ = Placed c ρ

  Placedᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  Placedᴸ []       ρ = ⊤
  Placedᴸ (c ∷ cs) ρ = Placed c ρ × Placedᴸ cs ρ

-- Each connect's source in order, and steady.
Sorted : ∀ {Γ} → NEnv Γ → Set
Sorted []ᴬ      = ⊤
Sorted (e ∷ᴬ ρ) = (Ordered e × Steady e) × Sorted ρ

sorted-lookup : ∀ {Γ A} (ρ : NEnv Γ) → Sorted ρ → (i : A ∈ Γ) → Ordered (lookup ρ i) × Steady (lookup ρ i)
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

-- Inside `p ++ [ l ]` is inside `p`.
under-ext : ∀ p l {h} → Ext (p ++ [ l ]) h → Ext p h
under-ext p l (ext m ms) = subst (Ext p) (sym (++-assoc p [ l ] (m ∷ ms))) (ext l (m ∷ ms))

clear-under : ∀ {A} p l (e : Events A) → Clear p e → Clear (p ++ [ l ]) e
clear (clear-under p l (out h _ r) c) = (λ x → proj₁ (clear c) (under-ext p l x)) , clear-under p l (force r) (proj₂ (clear c))
clear (clear-under p l (skip h r)  c) = (λ x → proj₁ (clear c) (under-ext p l x)) , clear-under p l (force r) (proj₂ (clear c))
clear (clear-under p l (end h)     c) = λ x → clear c (under-ext p l x)
clear (clear-under p l hush        c) = tt

clearᴱ-under : ∀ {Γ} p l (ρ : NEnv Γ) → Clearᴱ p ρ → Clearᴱ (p ++ [ l ]) ρ
clearᴱ-under p l []ᴬ      c        = tt
clearᴱ-under p l (e ∷ᴬ ρ) (ce , c) = clear-under p l e ce , clearᴱ-under p l ρ c

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

  -- A JOIN KEEPS ITS STEADY SOURCE'S ORDER: what it missed as skips
  -- just past the join, the rest rekeyed under it.
  --
  -- REFUTED: 37b70651 of a source merely in order, stepping inside its last position
  ordered-rejoin : ∀ {A} p (e : Events A) → Ordered e → Steady e → Ordered (M.rejoin p e)

  -- A CONNECT'S SOURCE MERGES INTO ITS BODY IN ORDER: each source step a
  -- skip just past it, ahead of the body's later events.
  ordered-beside : ∀ {A B} (b : Events B) (s : Events A) → Ordered b → Ordered s → Ordered (M.beside b s)

  -- A FLATMAP SUBSCRIBED MERGES IN ORDER: over sorted sources clear of
  -- where it subscribes.
  --
  -- The risk is a tie: an outer value at `q` shows as a skip just past
  -- `q`, so an outer event at that same `q` after it would show before
  -- it.  `Steady` sources leave none to rekey; the operators must make
  -- none.
  --
  -- REFUTED: 37b70651 of any outer node in order, by a joiner told a value and a skip at one position
  ordered-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Clearᴱ p ρ
               → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ)

  -- A DEFER'S RUN IS IN ORDER: its program, reached, over sorted sources
  -- clear of where it subscribes.
  ordered-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Clearᴱ p ρ → Ordered (U.meaning (U.deferᶜ l p []) ρ)

  -- A SUBSCRIPTION OVER STEADY SOURCES IS STEADY: a joiner's skips for
  -- what it missed sit just past the join, which nothing it rekeys
  -- lies inside, its sources being clear of it.
  steady-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Clearᴱ p ρ → Steady (U.meaning (U.subscribe o p) ρ)

  -- A CONNECT'S SOURCE STAYS OUT OF ITS BODY'S SUBTREE.
  clear-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Clearᴱ p ρ
            → Clear (p ++ [ ix 0 ]) (U.meaning (U.subscribe o (p ++ [ ix 1 ])) ρ)

  -- A FLATMAP'S SOURCES STAY OUT OF EVERY LANE IT CAN ADMIT: wherever it
  -- shows a skip at `x ++ [ ix 0 ]`, they are clear of `x ++ [ ix 1 ]`.
  -- The risk is a position the flatMap shows that is keyed under a
  -- source's, a joiner's rekey, rather than under where it subscribes.
  clear-shown : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Clearᴱ p ρ
              → ∀ x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.subscribe (flatMap op f s) p) ρ) → Clearᴱ (x ++ [ ix 1 ]) ρ

-- A program subscribed anywhere, over sorted sources clear of where it
-- subscribes, is placed.
placed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Clearᴱ p ρ → Placed (U.subscribe o p) ρ
placed-sub (cold c) p ρ so cl =
  subst Ordered (sym (U.start-meaning p (lower c) ρ)) (ordered-start p (lower c)) , start-within p (lower c) ρ
placed-sub empty p ρ so cl = record { ordered = tt } , tt
placed-sub (of xs) p ρ so cl = ordered-of p 0 xs , tt
placed-sub (map f s) p ρ so cl = ordered-map f _ (proj₁ ps) , ps
  where ps = placed-sub s p ρ so cl
placed-sub (scan f z s) p ρ so cl = ordered-scan f z _ (proj₁ ps) , ps
  where ps = placed-sub s p ρ so cl
placed-sub (takeWhile i q s) p ρ so cl = ordered-take i q _ (proj₁ ps) , ps
  where ps = placed-sub s p ρ so cl
placed-sub (flatMap op f s) p ρ so cl =
  ordered-flat op f s p ρ so cl , placed-sub s p ρ so cl , tt
  , λ a x r → placed-sub (f a) (x ++ [ ix 1 ]) ρ so (clear-shown op f s p ρ so cl x r)
placed-sub (connect s b) p ρ so cl = ordered-beside _ _ (proj₁ pb) (proj₁ ps) , pb , ps
  where cs = clearᴱ-under p (ix 1) ρ cl
        ps = placed-sub s (p ++ [ ix 1 ]) ρ so cs
        pb = placed-sub b (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ)
               ((proj₁ ps , steady-sub s (p ++ [ ix 1 ]) ρ so cs) , so) (clear-sub s p ρ cl , clearᴱ-under p (ix 0) ρ cl)
placed-sub (connected i) p ρ so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl) , tt
  where sl = sorted-lookup ρ so i
placed-sub (defer l) p ρ so cl = ordered-defer l p ρ so cl , tt

-- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root is
-- placed.
placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
placed-subscribe o = placed-sub o root []ᴬ tt tt
