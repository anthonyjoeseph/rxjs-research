{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-monoʳ-≤; <⇒≤; <-≤-trans; ≤-trans; m≤n+m; m≤m+n; <-irrefl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; agree; Earliest; none; found; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root; <ᵖ-asym; <ᵖ-down; <ᵖ-next; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-part)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp)
open import denotation.Compositional using (env-refl)

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

-- `e`'s first is strictly past `k`, and no proper extension of it.
Past : ∀ {A} → Pos → Events A → Set
Past k (out h _ _) = k <ᵖ h ≡ true × ¬ Ext k h
Past k (skip h _)  = k <ᵖ h ≡ true × ¬ Ext k h
Past k (end h)     = k <ᵖ h ≡ true × ¬ Ext k h
Past k hush        = ⊤

-- `e`'s first no proper extension of `k`, and strictly past it if a value.
Clear : ∀ {A} → Pos → Events A → Set
Clear k (out h _ _) = k <ᵖ h ≡ true × ¬ Ext k h
Clear k (skip h _)  = ¬ Ext k h
Clear k (end h)     = ¬ Ext k h
Clear k hush        = ⊤

-- Never a step inside the position just left, and never one tied with
-- a value.  A rejoin keys a source's event at `q` under `q`, so a
-- source stepping inside `q` sorts first, and a flatMap shows a value
-- at `q` just past `q`, so a source stepping to `q` again sorts first.
mutual
  Steadies : ∀ {A} → Events A → Set
  Steadies (out k _ r) = Past k (force r) × Steady (force r)
  Steadies (skip k r)  = Clear k (force r) × Steady (force r)
  Steadies (end _)     = ⊤
  Steadies hush        = ⊤

  record Steady {A} (e : Events A) : Set where
    coinductive
    field steady : Steadies e

open Steady public

-- `k` a prefix of `h`, and a proper one.
Prefix : Pos → Pos → Set
Prefix []      h       = ⊤
Prefix (_ ∷ _) []      = ⊥
Prefix (a ∷ k) (b ∷ h) = a ≡ b × Prefix k h

Prefix⁺ : Pos → Pos → Set
Prefix⁺ []      []      = ⊥
Prefix⁺ []      (_ ∷ _) = ⊤
Prefix⁺ (_ ∷ _) []      = ⊥
Prefix⁺ (a ∷ k) (b ∷ h) = a ≡ b × Prefix⁺ k h

-- `h` keyed under `k`: inside its subtree, or tagged by a join or a
-- timer keyed under it.  A rejoin at `p` keys a source's `q` as
-- `q ++ [ sub p ]`, and a frame of a cold at `p` sits at
-- `ix t ∷ sub e ∷ []` for an `e` under `p`: neither inside `p`.
mutual
  Owned : Pos → Pos → Set
  Owned k h = Prefix k h ⊎ Tagged k h

  Tagged : Pos → Pos → Set
  Tagged k []          = ⊥
  Tagged k (ix _ ∷ h)  = Tagged k h
  Tagged k (sub j ∷ h) = Owned k j ⊎ Tagged k h
  Tagged k (last ∷ h)  = Tagged k h

-- Strictly keyed under `k`: anywhere but `k` itself.
Beneath : Pos → Pos → Set
Beneath k h = Prefix⁺ k h ⊎ Tagged k h

-- Every position `e` shows, its end's included, satisfies `P`.
mutual
  Everys : ∀ {A} → (Pos → Set) → Events A → Set
  Everys P (out h _ r) = P h × Every P (force r)
  Everys P (skip h r)  = P h × Every P (force r)
  Everys P (end h)     = P h
  Everys P hush        = ⊤

  record Every {A} (P : Pos → Set) (e : Events A) : Set where
    coinductive
    field every : Everys P e

open Every public

-- Every source's positions satisfying `P`.
Everyᴱ : ∀ {Γ} → (Pos → Set) → NEnv Γ → Set
Everyᴱ P []ᴬ      = ⊤
Everyᴱ P (e ∷ᴬ ρ) = Every P e × Everyᴱ P ρ

every-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (e : Events A) → Every P e → Every Q e
every (every-mono f (out h _ r) pe) = f h (proj₁ (every pe)) , every-mono f (force r) (proj₂ (every pe))
every (every-mono f (skip h r)  pe) = f h (proj₁ (every pe)) , every-mono f (force r) (proj₂ (every pe))
every (every-mono f (end h)     pe) = f h (every pe)
every (every-mono f hush        pe) = tt

every-monoᴱ : ∀ {Γ} {P Q : Pos → Set} → (∀ h → P h → Q h) → (ρ : NEnv Γ) → Everyᴱ P ρ → Everyᴱ Q ρ
every-monoᴱ f []ᴬ      _         = tt
every-monoᴱ f (e ∷ᴬ ρ) (pe , pρ) = every-mono f e pe , every-monoᴱ f ρ pρ

every-lookup : ∀ {Γ A} P (ρ : NEnv Γ) → Everyᴱ P ρ → (i : A ∈ Γ) → Every P (lookup ρ i)
every-lookup P (e ∷ᴬ ρ) (pe , pρ) (here refl) = pe
every-lookup P (e ∷ᴬ ρ) (pe , pρ) (there i)   = every-lookup P ρ pρ i

-- No event of `e` keyed under `p`.
Alien : ∀ {A} → Pos → Events A → Set
Alien p = Every (λ h → ¬ Owned p h)

-- Every source alien to `p`: what a subscription at `p` keys.
Alienᴱ : ∀ {Γ} → Pos → NEnv Γ → Set
Alienᴱ p = Everyᴱ (λ h → ¬ Owned p h)

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

-- A value changed, or a running total, keeps a run steady.
clear-map : ∀ {A B} (f : A → B) k (e : Events A) → Clear k e → Clear k (M.mapᴱ f e)
clear-map f k (out _ _ _) c = c
clear-map f k (skip _ _)  c = c
clear-map f k (end _)     c = c
clear-map f k hush        c = c

past-map : ∀ {A B} (f : A → B) k (e : Events A) → Past k e → Past k (M.mapᴱ f e)
past-map f k (out _ _ _) c = c
past-map f k (skip _ _)  c = c
past-map f k (end _)     c = c
past-map f k hush        c = c

steady-map : ∀ {A B} (f : A → B) (e : Events A) → Steady e → Steady (M.mapᴱ f e)
steady (steady-map f (out k a r) st) = past-map f k (force r) (proj₁ (steady st)) , steady-map f (force r) (proj₂ (steady st))
steady (steady-map f (skip k r)  st) = clear-map f k (force r) (proj₁ (steady st)) , steady-map f (force r) (proj₂ (steady st))
steady (steady-map f (end k)     st) = tt
steady (steady-map f hush        st) = tt

clear-scan : ∀ {A B} (f : B → A → B) z k (e : Events A) → Clear k e → Clear k (M.scanᴱ f z e)
clear-scan f z k (out _ _ _) c = c
clear-scan f z k (skip _ _)  c = c
clear-scan f z k (end _)     c = c
clear-scan f z k hush        c = c

past-scan : ∀ {A B} (f : B → A → B) z k (e : Events A) → Past k e → Past k (M.scanᴱ f z e)
past-scan f z k (out _ _ _) c = c
past-scan f z k (skip _ _)  c = c
past-scan f z k (end _)     c = c
past-scan f z k hush        c = c

steady-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Steady e → Steady (M.scanᴱ f z e)
steady (steady-scan f z (out k a r) st) = past-scan f (f z a) k (force r) (proj₁ (steady st)) , steady-scan f (f z a) (force r) (proj₂ (steady st))
steady (steady-scan f z (skip k r)  st) = clear-scan f z k (force r) (proj₁ (steady st)) , steady-scan f z (force r) (proj₂ (steady st))
steady (steady-scan f z (end k)     st) = tt
steady (steady-scan f z hush        st) = tt

-- `e`'s first, if any, no proper extension of `k`.
Away : ∀ {A} → Pos → Events A → Set
Away k (out h _ _) = ¬ Ext k h
Away k (skip h _)  = ¬ Ext k h
Away k (end h)     = ¬ Ext k h
Away k hush        = ⊤

past-away : ∀ {A} k (e : Events A) → Past k e → Away k e
past-away k (out _ _ _) c = proj₂ c
past-away k (skip _ _)  c = proj₂ c
past-away k (end _)     c = proj₂ c
past-away k hush        c = tt

clear-away : ∀ {A} k (e : Events A) → Clear k e → Away k e
clear-away k (out _ _ _) c = proj₂ c
clear-away k (skip _ _)  c = c
clear-away k (end _)     c = c
clear-away k hush        c = tt

off : ∀ {k h} → ¬ Ext k h → ∀ l ls → h ≡ k ++ l ∷ ls → ⊥
off ne l ls refl = ne (ext l ls)

-- Rekeyed under one label, what was no earlier and not below stays so.
under : ∀ q h x → h <ᵖ q ≡ false → ¬ Ext q h → (h ++ [ x ]) <ᵖ (q ++ [ x ]) ≡ false
under q h x a ne with <ᵖ-split q h a
... | inj₁ qh   = <ᵖ-asym (q ++ [ x ]) (h ++ [ x ]) (<ᵖ-down q h x x qh (off ne))
... | inj₂ refl = <ᵖ-irrefl (q ++ [ x ])

still : ∀ p q h → p <ᵖ q ≡ true → h <ᵖ q ≡ false → p <ᵖ h ≡ true
still p q h pq a with <ᵖ-split q h a
... | inj₁ qh   = <ᵖ-trans p q h pq qh
... | inj₂ refl = pq

-- After a source event the join shows, the next it shows is no earlier.
atop-in : ∀ {A} p q (e : Events A) → p <ᵖ q ≡ true → Atop q e → Away q e → Atop (q ++ [ sub p ]) (M.rejoin p e)
atop-in p q (out h _ _) pq a ne with p <ᵖ h in ph
... | true  = under q h (sub p) a ne
... | false with () ← trans (sym ph) (still p q h pq a)
atop-in p q (skip h _)  pq a ne with p <ᵖ h in ph
... | true  = under q h (sub p) a ne
... | false with () ← trans (sym ph) (still p q h pq a)
atop-in p q (end c)     pq a ne with p <ᵖ c in pc
... | true  = under q c (sub p) a ne
... | false with () ← trans (sym pc) (still p q c pq a)
atop-in p q hush        pq a ne = tt

-- After a missed event, anything the join shows is no earlier.
atop-pre : ∀ {A} p (e : Events A) → Atop (p ++ [ ix 0 ]) (M.rejoin p e)
atop-pre p (out h _ _) with p <ᵖ h in ph
... | true  = <ᵖ-asym (p ++ [ ix 0 ]) (h ++ [ sub p ]) (<ᵖ-next p h (sub p) ph)
... | false = <ᵖ-irrefl (p ++ [ ix 0 ])
atop-pre p (skip h _)  with p <ᵖ h in ph
... | true  = <ᵖ-asym (p ++ [ ix 0 ]) (h ++ [ sub p ]) (<ᵖ-next p h (sub p) ph)
... | false = <ᵖ-irrefl (p ++ [ ix 0 ])
atop-pre p (end c)     with p <ᵖ c in pc
... | true  = <ᵖ-asym (p ++ [ ix 0 ]) (c ++ [ sub p ]) (<ᵖ-next p c (sub p) pc)
... | false = <ᵖ-asym (p ++ [ ix 0 ]) (p ++ [ last ]) (<ᵖ-part p {ix 0} {last} [] [] refl)
atop-pre p hush        = tt

-- A JOIN KEEPS ITS STEADY SOURCE'S ORDER: what it missed as skips
-- just past the join, the rest rekeyed under it.
--
-- REFUTED: 37b70651 of a source merely in order, stepping inside its last position
ordered-rejoin : ∀ {A} p (e : Events A) → Ordered e → Steady e → Ordered (M.rejoin p e)
ordered (ordered-rejoin p (out q a k) o st) with p <ᵖ q in pq
... | true  = atop-in p q (force k) pq (proj₁ (ordered o)) (past-away q (force k) (proj₁ (steady st)))
            , ordered-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st))
... | false = atop-pre p (force k) , ordered-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st))
ordered (ordered-rejoin p (skip q k) o st) with p <ᵖ q in pq
... | true  = atop-in p q (force k) pq (proj₁ (ordered o)) (clear-away q (force k) (proj₁ (steady st)))
            , ordered-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st))
... | false = atop-pre p (force k) , ordered-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st))
ordered (ordered-rejoin p (end c) o st) with p <ᵖ c
... | true  = tt
... | false = tt
ordered (ordered-rejoin p hush o st) = tt

prefix-++ : ∀ k w → Prefix k (k ++ w)
prefix-++ []      w = tt
prefix-++ (a ∷ k) w = refl , prefix-++ k w

prefix-trans : ∀ k j h → Prefix k j → Prefix j h → Prefix k h
prefix-trans []      j       h       _          _          = tt
prefix-trans (_ ∷ _) []      _       ()         _
prefix-trans (_ ∷ _) (_ ∷ _) []      _          ()
prefix-trans (a ∷ k) (b ∷ j) (c ∷ h) (refl , p) (refl , q) = refl , prefix-trans k j h p q

ext-eq : ∀ {k h} → Ext k h → ∃₂ λ l ls → h ≡ k ++ l ∷ ls
ext-eq (ext l ls) = l , ls , refl

cons-ext : ∀ {k h} a → Ext k h → Ext (a ∷ k) (a ∷ h)
cons-ext a (ext l ls) = ext l ls

ext-irrefl : ∀ k → ¬ Ext k k
ext-irrefl k x with ext-eq x
... | l , ls , e = go k l ls e
  where go : ∀ k l ls → k ≡ k ++ l ∷ ls → ⊥
        go []      l ls ()
        go (a ∷ k) l ls e = go k l ls (∷-injectiveʳ e)

owned-ext : ∀ {k h} → Ext k h → Owned k h
owned-ext (ext l ls) = inj₁ (prefix-++ _ (l ∷ ls))

-- One position below another a label down was below it already.
under-ext : ∀ q h {x y} → Ext (q ++ [ x ]) (h ++ [ y ]) → Ext q h
under-ext q h {x} x′ with ext-eq x′
... | l , ls , e = go q h e
  where nil : ∀ q l ls → [] ≡ (q ++ [ x ]) ++ l ∷ ls → ⊥
        nil []      l ls ()
        nil (_ ∷ _) l ls ()
        go : ∀ q h {y l ls} → h ++ [ y ] ≡ (q ++ [ x ]) ++ l ∷ ls → Ext q h
        go []      []      e with () ← ∷-injectiveʳ e
        go []      (b ∷ h) e = ext b h
        go (a ∷ q) []      {l = l} {ls} e = ⊥-elim (nil q l ls (∷-injectiveʳ e))
        go (a ∷ q) (b ∷ h) e with ∷-injective e
        ... | refl , e′ = cons-ext a (go q h e′)

-- After a missed event, nothing the join shows lies inside its skips:
-- an alien source has nothing under the join.
clear-pre : ∀ {A} p (e : Events A) → Alien p e → Clear (p ++ [ ix 0 ]) (M.rejoin p e)
clear-pre p (out h _ _) al with p <ᵖ h in ph
... | true  = <ᵖ-next p h (sub p) ph , λ x → proj₁ (every al) (owned-ext (under-ext p h x))
... | false = ext-irrefl (p ++ [ ix 0 ])
clear-pre p (skip h _)  al with p <ᵖ h in ph
... | true  = λ x → proj₁ (every al) (owned-ext (under-ext p h x))
... | false = ext-irrefl (p ++ [ ix 0 ])
clear-pre p (end c)     al with p <ᵖ c in pc
... | true  = λ x → every al (owned-ext (under-ext p c x))
... | false = λ x → ext-irrefl p (under-ext p p x)
clear-pre p hush        al = tt

-- After a source event the join shows, the next it shows is not inside
-- it, and past it as the source's next is.
apart-in : ∀ q h x → q <ᵖ h ≡ true → ¬ Ext q h → (q ++ [ x ]) <ᵖ (h ++ [ x ]) ≡ true × ¬ Ext (q ++ [ x ]) (h ++ [ x ])
apart-in q h x qh ne = <ᵖ-down q h x x qh (off ne) , λ y → ne (under-ext q h y)

past-in : ∀ {A} p q (e : Events A) → p <ᵖ q ≡ true → Past q e → Past (q ++ [ sub p ]) (M.rejoin p e)
past-in p q (out h _ _) pq (qh , ne) with p <ᵖ h in ph
... | true  = apart-in q h (sub p) qh ne
... | false with () ← trans (sym ph) (<ᵖ-trans p q h pq qh)
past-in p q (skip h _)  pq (qh , ne) with p <ᵖ h in ph
... | true  = apart-in q h (sub p) qh ne
... | false with () ← trans (sym ph) (<ᵖ-trans p q h pq qh)
past-in p q (end c)     pq (qc , ne) with p <ᵖ c in pc
... | true  = apart-in q c (sub p) qc ne
... | false with () ← trans (sym pc) (<ᵖ-trans p q c pq qc)
past-in p q hush        pq _ = tt

clear-in : ∀ {A} p q (e : Events A) → p <ᵖ q ≡ true → Atop q e → Clear q e → Clear (q ++ [ sub p ]) (M.rejoin p e)
clear-in p q (out h _ _) pq a (qh , ne) with p <ᵖ h in ph
... | true  = apart-in q h (sub p) qh ne
... | false with () ← trans (sym ph) (still p q h pq a)
clear-in p q (skip h _)  pq a ne with p <ᵖ h in ph
... | true  = λ y → ne (under-ext q h y)
... | false with () ← trans (sym ph) (still p q h pq a)
clear-in p q (end c)     pq a ne with p <ᵖ c in pc
... | true  = λ y → ne (under-ext q c y)
... | false with () ← trans (sym pc) (still p q c pq a)
clear-in p q hush        pq a _ = tt

-- A JOIN KEEPS AN ALIEN STEADY RUN STEADY: what it missed as skips
-- just past the join, nothing it shows later inside them.  Not of any
-- steady run: one emitting inside `p ++ [ ix 0 ]` after a missed step
-- shows it inside those skips.
steady-rejoin : ∀ {A} p (e : Events A) → Ordered e → Steady e → Alien p e → Steady (M.rejoin p e)
steady (steady-rejoin p (out q a k) o st al) with p <ᵖ q in pq
... | true  = past-in p q (force k) pq (proj₁ (steady st))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (every al))
... | false = clear-pre p (force k) (proj₂ (every al))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (every al))
steady (steady-rejoin p (skip q k) o st al) with p <ᵖ q in pq
... | true  = clear-in p q (force k) pq (proj₁ (ordered o)) (proj₁ (steady st))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (every al))
... | false = clear-pre p (force k) (proj₂ (every al))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (every al))
steady (steady-rejoin p (end c) o st al) with p <ᵖ c
... | true  = tt
... | false = tt
steady (steady-rejoin p hush o st al) = tt

-- A tag inside `j` is inside what `j` prefixes.
tagged-prefix : ∀ k j h → Tagged k j → Prefix j h → Tagged k h
tagged-prefix k []          h       ()         _
tagged-prefix k (_ ∷ _)     []      _          ()
tagged-prefix k (ix _ ∷ j)  (_ ∷ h) t          (refl , p) = tagged-prefix k j h t p
tagged-prefix k (last ∷ j)  (_ ∷ h) t          (refl , p) = tagged-prefix k j h t p
tagged-prefix k (sub _ ∷ j) (_ ∷ h) (inj₁ o)   (refl , p) = inj₁ o
tagged-prefix k (sub _ ∷ j) (_ ∷ h) (inj₂ t)   (refl , p) = inj₂ (tagged-prefix k j h t p)

-- Keyed under what is keyed under `k` is keyed under `k`.
mutual
  owned-trans : ∀ k j h → Owned k j → Owned j h → Owned k h
  owned-trans k j h (inj₁ p) (inj₁ q) = inj₁ (prefix-trans k j h p q)
  owned-trans k j h (inj₂ t) (inj₁ q) = inj₂ (tagged-prefix k j h t q)
  owned-trans k j h o        (inj₂ t) = inj₂ (owned-tagged k j h o t)

  owned-tagged : ∀ k j h → Owned k j → Tagged j h → Tagged k h
  owned-tagged k j []          o ()
  owned-tagged k j (ix _ ∷ h)  o t        = owned-tagged k j h o t
  owned-tagged k j (last ∷ h)  o t        = owned-tagged k j h o t
  owned-tagged k j (sub i ∷ h) o (inj₁ q) = inj₁ (owned-trans k j i o q)
  owned-tagged k j (sub i ∷ h) o (inj₂ t) = inj₂ (owned-tagged k j h o t)

-- What a flatMap shows just before a lane, strictly under `p`, puts the
-- lane under `p`.
prefix-lane : ∀ k x l → Prefix⁺ k (x ++ [ l ]) → Prefix k x
prefix-lane []          x       l _          = tt
prefix-lane (_ ∷ [])    []      l (refl , ())
prefix-lane (_ ∷ _ ∷ _) []      l (refl , ())
prefix-lane (a ∷ k)     (b ∷ x) l (refl , p) = refl , prefix-lane k x l p

tagged-lane : ∀ k x n → Tagged k (x ++ [ ix n ]) → Tagged k x
tagged-lane k []          n ()
tagged-lane k (ix _ ∷ x)  n t        = tagged-lane k x n t
tagged-lane k (last ∷ x)  n t        = tagged-lane k x n t
tagged-lane k (sub _ ∷ x) n (inj₁ o) = inj₁ o
tagged-lane k (sub _ ∷ x) n (inj₂ t) = inj₂ (tagged-lane k x n t)

tagged-++ : ∀ k h w → Tagged k h → Tagged k (h ++ w)
tagged-++ k []          w ()
tagged-++ k (ix _ ∷ h)  w t        = tagged-++ k h w t
tagged-++ k (last ∷ h)  w t        = tagged-++ k h w t
tagged-++ k (sub _ ∷ h) w (inj₁ o) = inj₁ o
tagged-++ k (sub _ ∷ h) w (inj₂ t) = inj₂ (tagged-++ k h w t)

owned-lane : ∀ p x → Beneath p (x ++ [ ix 0 ]) → Owned p (x ++ [ ix 1 ])
owned-lane p x (inj₁ q) = inj₁ (prefix-trans p x (x ++ [ ix 1 ]) (prefix-lane p x (ix 0) q) (prefix-++ x [ ix 1 ]))
owned-lane p x (inj₂ t) = inj₂ (tagged-++ p x [ ix 1 ] (tagged-lane p x 0 t))

-- Alien to `p` is alien to whatever `p` keys.
alienᴱ-owned : ∀ {Γ} p k → Owned p k → (ρ : NEnv Γ) → Alienᴱ p ρ → Alienᴱ k ρ
alienᴱ-owned p k o = every-monoᴱ (λ h na x → na (owned-trans p k h o x))

-- A position's size, a tag counting what it holds.
mutual
  weigh : Pos → ℕ
  weigh []      = 0
  weigh (l ∷ h) = weighˡ l + weigh h

  weighˡ : M.Label → ℕ
  weighˡ (ix _)  = 1
  weighˡ (sub j) = suc (weigh j)
  weighˡ last    = 1

prefix-weigh : ∀ k h → Prefix k h → weigh k ≤ weigh h
prefix-weigh []      h       _          = z≤n
prefix-weigh (_ ∷ _) []      ()
prefix-weigh (a ∷ k) (_ ∷ h) (refl , p) = +-monoʳ-≤ (weighˡ a) (prefix-weigh k h p)

-- What keys `h` is no larger than it, and a tag strictly smaller.
mutual
  owned-weigh : ∀ k h → Owned k h → weigh k ≤ weigh h
  owned-weigh k h (inj₁ p) = prefix-weigh k h p
  owned-weigh k h (inj₂ t) = <⇒≤ (tagged-weigh k h t)

  tagged-weigh : ∀ k h → Tagged k h → weigh k < weigh h
  tagged-weigh k []          ()
  tagged-weigh k (ix _ ∷ h)  t        = <-≤-trans (tagged-weigh k h t) (m≤n+m (weigh h) 1)
  tagged-weigh k (last ∷ h)  t        = <-≤-trans (tagged-weigh k h t) (m≤n+m (weigh h) 1)
  tagged-weigh k (sub j ∷ h) (inj₁ o) = s≤s (≤-trans (owned-weigh k j o) (m≤m+n (weigh j) (weigh h)))
  tagged-weigh k (sub j ∷ h) (inj₂ t) = <-≤-trans (tagged-weigh k h t) (m≤n+m (weigh h) (suc (weigh j)))

-- A label marking a step, not a tag.
data Mark : M.Label → Set where
  ix-mark   : ∀ i → Mark (ix i)
  last-mark : Mark last

tagged-mark : ∀ k h l → Mark l → Tagged k (h ++ [ l ]) → Tagged k h
tagged-mark k []          l (ix-mark _) ()
tagged-mark k []          l last-mark   ()
tagged-mark k (ix _ ∷ h)  l m t        = tagged-mark k h l m t
tagged-mark k (last ∷ h)  l m t        = tagged-mark k h l m t
tagged-mark k (sub _ ∷ h) l m (inj₁ o) = inj₁ o
tagged-mark k (sub _ ∷ h) l m (inj₂ t) = inj₂ (tagged-mark k h l m t)

sibling-prefix : ∀ p {i j} → i ≢ j → ¬ Prefix (p ++ [ ix i ]) (p ++ [ ix j ])
sibling-prefix []      ne (refl , _) = ne refl
sibling-prefix (_ ∷ p) ne (_ , q)    = sibling-prefix p ne q

-- Two children of one position key nothing of each other.
sibling : ∀ p {i j} → i ≢ j → ¬ Owned (p ++ [ ix i ]) (p ++ [ ix j ])
sibling p     ne (inj₁ q) = sibling-prefix p ne q
sibling p {i} {j} ne (inj₂ t) =
  <-irrefl refl (<-≤-trans (tagged-weigh (p ++ [ ix i ]) p (tagged-mark _ p _ (ix-mark j) t)) (prefix-weigh p (p ++ [ ix i ]) (prefix-++ p [ ix i ])))

-- A child is somewhere.
snoc-there : ∀ p {l : M.Label} → p ++ [ l ] ≢ []
snoc-there []      ()
snoc-there (_ ∷ _) ()

-- A first child is never a timer's tick.
no-tick : ∀ p m → p ++ [ ix 0 ] ≢ ix (suc m) ∷ []
no-tick []          m ()
no-tick (_ ∷ [])    m ()
no-tick (_ ∷ _ ∷ _) m ()

every-reach : ∀ {A} {P : Pos → Set} (e : Events A) h → Every P e → Reaches h e → P h
every-reach (out h _ r) _ pe out-here       = proj₁ (every pe)
every-reach (out _ _ r) h pe (out-there x)  = every-reach (force r) h (proj₂ (every pe)) x
every-reach (skip h r)  _ pe skip-here      = proj₁ (every pe)
every-reach (skip _ r)  h pe (skip-there x) = every-reach (force r) h (proj₂ (every pe)) x

prefix-refl : ∀ k → Prefix k k
prefix-refl []      = tt
prefix-refl (a ∷ k) = refl , prefix-refl k

prefix-snoc : ∀ k r l → Prefix k r → Prefix⁺ k (r ++ [ l ])
prefix-snoc []      []      l _          = tt
prefix-snoc []      (_ ∷ _) l _          = tt
prefix-snoc (_ ∷ _) []      l ()
prefix-snoc (a ∷ k) (b ∷ r) l (refl , q) = refl , prefix-snoc k r l q

prefix⁺-++ : ∀ k h w → Prefix⁺ k h → Prefix⁺ k (h ++ w)
prefix⁺-++ []      []      w ()
prefix⁺-++ []      (_ ∷ _) w _          = tt
prefix⁺-++ (_ ∷ _) []      w ()
prefix⁺-++ (a ∷ k) (b ∷ h) w (refl , q) = refl , prefix⁺-++ k h w q

prefix⁺-prefix : ∀ k h → Prefix⁺ k h → Prefix k h
prefix⁺-prefix []      h       _          = tt
prefix⁺-prefix (_ ∷ _) []      ()
prefix⁺-prefix (a ∷ k) (b ∷ h) (refl , q) = refl , prefix⁺-prefix k h q

owned-snoc : ∀ p r l → Owned p r → Beneath p (r ++ [ l ])
owned-snoc p r l (inj₁ q) = inj₁ (prefix-snoc p r l q)
owned-snoc p r l (inj₂ t) = inj₂ (tagged-++ p r [ l ] t)

beneath-snoc : ∀ p k l → Beneath p k → Beneath p (k ++ [ l ])
beneath-snoc p k l (inj₁ q) = inj₁ (prefix⁺-++ p k [ l ] q)
beneath-snoc p k l (inj₂ t) = inj₂ (tagged-++ p k [ l ] t)

beneath-owned : ∀ p k → Beneath p k → Owned p k
beneath-owned p k (inj₁ q) = inj₁ (prefix⁺-prefix p k q)
beneath-owned p k (inj₂ t) = inj₂ t

-- A join at `p` tags what it rekeys with `p` itself.
tagged-sub : ∀ q p → Tagged p (q ++ [ sub p ])
tagged-sub []          p = inj₁ (inj₁ (prefix-refl p))
tagged-sub (ix _ ∷ q)  p = tagged-sub q p
tagged-sub (last ∷ q)  p = tagged-sub q p
tagged-sub (sub _ ∷ q) p = inj₂ (tagged-sub q p)

-- The lane `earliest` picks, and those around it, are lanes it was given.
Picked : ∀ {B} → (Events B → Set) → Earliest B → Set
Picked P none              = ⊤
Picked P (found k bs l as) = All P bs × P l × All P as

earliest-all : ∀ {B} (P : Events B → Set) (ls : List (Events B)) → All P ls → Picked P (M.earliest ls)
earliest-all P []       []ᴬ        = tt
earliest-all P (l ∷ ls) (pl ∷ᴬ al) with M.head l | M.earliest ls | earliest-all P ls al
... | nothing | none             | _                 = tt
... | nothing | found k bs c as  | (pb , pc , pa)    = pl ∷ᴬ pb , pc , pa
... | just k  | none             | _                 = []ᴬ , pl , al
... | just k  | found k′ bs c as | (pb , pc , pa) with k <ᵖ k′
...   | true  = []ᴬ , pl , al
...   | false = pl ∷ᴬ pb , pc , pa

-- What agrees at every depth shows the same positions.
out-tail : ∀ {A k h h′ a b} {l r : Events∞ A} → Agree (suc k) (out h a l) (out h′ b r) → Agree k (force l) (force r)
out-tail (out⁼ t) = t

skip-tail : ∀ {A k h h′} {l r : Events∞ A} → Agree (suc k) (skip h l) (skip h′ r) → Agree k (force l) (force r)
skip-tail (skip⁼ t) = t

mutual
  every-≈ : ∀ {A} {P : Pos → Set} (x y : Events A) → (∀ k → Agree k x y) → Every P x → Every P y
  every (every-≈ x y a px) = everys-≈ x y a (a 1) px

  everys-≈ : ∀ {A} {P : Pos → Set} (x y : Events A) → (∀ k → Agree k x y) → Agree 1 x y → Every P x → Everys P y
  everys-≈ (out h _ l) (out h _ r) a (out⁼ _)  px =
    proj₁ (every px) , every-≈ (force l) (force r) (λ k → out-tail (a (suc k))) (proj₂ (every px))
  everys-≈ (skip h l)  (skip h r)  a (skip⁼ _) px =
    proj₁ (every px) , every-≈ (force l) (force r) (λ k → skip-tail (a (suc k))) (proj₂ (every px))
  everys-≈ (end h)     (end h)     a end⁼      px = every px
  everys-≈ hush        hush        a hush⁼     px = tt

-- What a subscription is held to: `S` where it subscribes, `P` what it
-- shows, `Src` what its sources show.  Each field is one way an
-- operator makes a position: a step or an end under where it
-- subscribes, a mark just past what it shows, a timer's frame tagged
-- with the burst before it, a source's position tagged with a join.
record Rules : Set₁ where
  field
    S P Src : Pos → Set
    child   : ∀ j l → Mark l → S j → P (j ++ [ l ])
    deeper  : ∀ h l → Mark l → P h → P (h ++ [ l ])
    held    : ∀ h → P h → S h
    frame   : ∀ n e → P e → S (ix (suc n) ∷ sub e ∷ [])
    join    : ∀ q j → Src q → S j → P (q ++ [ sub j ])
    source  : ∀ h → P h → Src h

module Reach (R : Rules) where
  open Rules R

  -- A cold shows its subscribe burst under where it subscribes, and
  -- each later frame at a tick past it, tagged with the burst before.
  mutual
    every-frames : ∀ {A t} τ e (m : M.From A (suc t)) → P e → Every P (M.frames τ e m)
    every (every-frames τ e M.done                    pe) = pe
    every (every-frames τ e M.quiet                   pe) = tt
    every (every-frames τ e (M.at (suc t′) (s≤s _) b) pe) =
      every (every-burst τ _ 0 b (subst (λ x → S (ix x ∷ sub e ∷ [])) (sym (+-suc τ t′)) (frame (τ + t′) e pe)))

    every-burst : ∀ {A t} τ r i (b : M.Frame A t) → S r → Every P (M.burst τ r i b)
    every (every-burst τ r i (M.emit a k) sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) sr
    every (every-burst τ r i (M.stall k)  sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) sr
    every (every-burst τ r i (M.close k)  sr) =
      child r (ix i) (ix-mark i) sr , every-frames τ (r ++ [ last ]) (M.From∞.force k) (child r last last-mark sr)

  every-start : ∀ {A} p (m : From A 0) → S p → Every P (M.start p m)
  every-start p (M.at zero _ b)    sp = every-burst (tick p) p 0 b sp
  every-start p (M.at (suc n) _ b) sp =
    every-burst (tick p) _ 0 b
      (subst (λ x → S (ix x ∷ sub (p ++ [ last ]) ∷ [])) (sym (+-suc (tick p) n)) (frame (tick p + n) _ (child p last last-mark sp)))
  every-start p M.done             sp = record { every = child p last last-mark sp }
  every-start p M.quiet            sp = record { every = tt }

  every-of : ∀ {A} p i (xs : List A) → S p → Every P (M.ofᴱ p i xs)
  every (every-of p i []       sp) = child p last last-mark sp
  every (every-of p i (x ∷ xs) sp) = child p (ix i) (ix-mark i) sp , every-of p (suc i) xs sp

  every-map : ∀ {A B} (f : A → B) (e : Events A) → Every P e → Every P (M.mapᴱ f e)
  every (every-map f (out k a r) pe) = proj₁ (every pe) , every-map f (force r) (proj₂ (every pe))
  every (every-map f (skip k r)  pe) = proj₁ (every pe) , every-map f (force r) (proj₂ (every pe))
  every (every-map f (end k)     pe) = every pe
  every (every-map f hush        pe) = tt

  every-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Every P e → Every P (M.scanᴱ f z e)
  every (every-scan f z (out k a r) pe) = proj₁ (every pe) , every-scan f (f z a) (force r) (proj₂ (every pe))
  every (every-scan f z (skip k r)  pe) = proj₁ (every pe) , every-scan f z (force r) (proj₂ (every pe))
  every (every-scan f z (end k)     pe) = every pe
  every (every-scan f z hush        pe) = tt

  -- A cut shows its failing value, if at all, just past where it was,
  -- and ends just past it.
  mutual
    every-take : ∀ {A} i (q : A → Bool) (e : Events A) → Every P e → Every P (M.takeWhileᴱ i q e)
    every (every-take i q (out k a r) pe) = every (every-taking i q k a (q a) r pe)
    every (every-take i q (skip k r)  pe) = proj₁ (every pe) , every-take i q (force r) (proj₂ (every pe))
    every (every-take i q (end k)     pe) = every pe
    every (every-take i q hush        pe) = tt

    every-taking : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) → Every P (out k a r) → Every P (M.taking i q k a b r)
    every (every-taking i     q k a true  r pe) = proj₁ (every pe) , every-take i q (force r) (proj₂ (every pe))
    every (every-taking true  q k a false r pe) =
      deeper k (ix 0) (ix-mark 0) (proj₁ (every pe)) , record { every = deeper k last last-mark (proj₁ (every pe)) }
    every (every-taking false q k a false r pe) = deeper k last last-mark (proj₁ (every pe))

  -- A join at `p` shows what it missed just past `p`, the rest tagged.
  mutual
    every-rejoin : ∀ {A} p (e : Events A) → S p → Every Src e → Every P (M.rejoin p e)
    every (every-rejoin p (out q a k) sp se) = every (every-shown p q (just a) k (p <ᵖ q) sp (proj₁ (every se)) (proj₂ (every se)))
    every (every-rejoin p (skip q k)  sp se) = every (every-shown p q nothing k (p <ᵖ q) sp (proj₁ (every se)) (proj₂ (every se)))
    every (every-rejoin p (end c)     sp se) with p <ᵖ c
    ... | true  = join c p (every se) sp
    ... | false = child p last last-mark sp
    every (every-rejoin p hush        sp se) = tt

    every-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → S p → Src q → Every Src (force k) → Every P (M.shown p q a k b)
    every (every-shown p q (just a) k true  sp sq sk) = join q p sq sp , every-rejoin p (force k) sp sk
    every (every-shown p q nothing  k true  sp sq sk) = join q p sq sp , every-rejoin p (force k) sp sk
    every (every-shown p q (just a) k false sp sq sk) = child p (ix 0) (ix-mark 0) sp , every-rejoin p (force k) sp sk
    every (every-shown p q nothing  k false sp sq sk) = child p (ix 0) (ix-mark 0) sp , every-rejoin p (force k) sp sk

  -- A connect shows each of its source's steps, and its end, just past it.
  mutual
    every-beside : ∀ {A B} (b : Events B) (s : Events A) → Every P b → Every P s → Every P (M.beside b s)
    every (every-beside b (out q _ r) pb ps) =
      every (every-ahead b (q ++ [ ix 0 ]) r (M.before (q ++ [ ix 0 ]) b) pb (deeper q (ix 0) (ix-mark 0) (proj₁ (every ps))) (proj₂ (every ps)))
    every (every-beside b (skip q r)  pb ps) =
      every (every-ahead b (q ++ [ ix 0 ]) r (M.before (q ++ [ ix 0 ]) b) pb (deeper q (ix 0) (ix-mark 0) (proj₁ (every ps))) (proj₂ (every ps)))
    every (every-beside b (end c)     pb ps) =
      every (every-ahead b (c ++ [ ix 0 ]) M.hushed (M.before (c ++ [ ix 0 ]) b) pb (deeper c (ix 0) (ix-mark 0) (every ps)) (record { every = tt }))
    every (every-beside b hush        pb ps) = every pb

    every-ahead : ∀ {A B} (b : Events B) q (s : Events∞ A) t → Every P b → P q → Every P (force s) → Every P (M.ahead b q s t)
    every (every-ahead b           q s true  pb pq ps) = pq , every-beside b (force s) pb ps
    every (every-ahead (out k a r) q s false pb pq ps) = proj₁ (every pb) , every-ahead (force r) q s _ (proj₂ (every pb)) pq ps
    every (every-ahead (skip k r)  q s false pb pq ps) = proj₁ (every pb) , every-ahead (force r) q s _ (proj₂ (every pb)) pq ps
    every (every-ahead (end c)     q s false pb pq ps) = every pb
    every (every-ahead hush        q s false pb pq ps) = tt

  -- A lane held to the rules wherever it may subscribe.
  Lane : ∀ {B} → MonotonicList B → Set
  Lane m = ∀ k → S k → Every P (M.observe m k)

  -- An outer held to the rules, each value a lane.
  mutual
    Outers : ∀ {B} → Events (MonotonicList B) → Set
    Outers (out h m r) = P h × Lane m × Outer (force r)
    Outers (skip h r)  = P h × Outer (force r)
    Outers (end h)     = P h
    Outers hush        = ⊤

    record Outer {B} (e : Events (MonotonicList B)) : Set where
      coinductive
      field outerly : Outers e

  open Outer public

  outer-map : ∀ {A B} (F : A → MonotonicList B) (e : Events A) → (∀ a → Lane (F a)) → Every P e → Outer (M.mapᴱ F e)
  outerly (outer-map F (out h a r) lf pe) = proj₁ (every pe) , lf a , outer-map F (force r) lf (proj₂ (every pe))
  outerly (outer-map F (skip h r)  lf pe) = proj₁ (every pe) , outer-map F (force r) lf (proj₂ (every pe))
  outerly (outer-map F (end h)     lf pe) = every pe
  outerly (outer-map F hush        lf pe) = tt

  Outerᴹ : ∀ {B} → Maybe (Events (MonotonicList B)) → Set
  Outerᴹ nothing  = ⊤
  Outerᴹ (just e) = Outer e

  -- An admitted lane subscribes held, and a queued one stays a lane.
  Admitted : ∀ {B} → List (Events B) × List (MonotonicList B) → Set
  Admitted (ls , qs) = All (Every P) ls × All Lane qs

  admit-all : ∀ {B} op q (m : MonotonicList B) ls qs → S q → Lane m → All (Every P) ls → All Lane qs
            → Admitted (M.admit op q m ls qs)
  admit-all (M.mergeᶠ nothing)  q m ls       qs sq lm pl pq = lm q sq ∷ᴬ pl , pq
  admit-all (M.mergeᶠ (just n)) q m ls       qs sq lm pl pq with length ls <ᵇ n
  ... | true  = lm q sq ∷ᴬ pl , pq
  ... | false = pl , All++⁺ pq (lm ∷ᴬ []ᴬ)
  admit-all M.switchᶠ           q m ls       qs sq lm pl pq = lm q sq ∷ᴬ []ᴬ , pq
  admit-all M.exhaustᶠ          q m []       qs sq lm pl pq = lm q sq ∷ᴬ []ᴬ , pq
  admit-all M.exhaustᶠ          q m (l ∷ ls) qs sq lm pl pq = pl , pq

  -- A flatMap's merge shows its outer's skips and ends where they were,
  -- each value just past where it was, and its lanes' events where they
  -- were, each lane's end just past it when another is queued.
  mutual
    every-go : ∀ {B} op (o : Maybe (Events (MonotonicList B))) ls qs → Outerᴹ o → All (Every P) ls → All Lane qs
             → Every P (M.go op o ls qs)
    every-go op o ls qs po pl pq with M.earliest ls | earliest-all (Every P) ls pl
    ... | none            | _                = every-via op o ls qs po pl pq
    ... | found k bs l as | (pb , pl₁ , pa)  = every-race op o k bs l as qs po pb pl₁ pa pq

    every-via : ∀ {B} op (o : Maybe (Events (MonotonicList B))) ls qs → Outerᴹ o → All (Every P) ls → All Lane qs
              → Every P (M.viaOuter op o ls qs)
    every-via op nothing  ls qs po pl pq = record { every = tt }
    every-via op (just e) ls qs po pl pq = every-outer op e ls qs po pl pq

    every-race : ∀ {B} op (o : Maybe (Events (MonotonicList B))) k bs (l : Events B) as qs → Outerᴹ o
               → All (Every P) bs → Every P l → All (Every P) as → All Lane qs → Every P (M.race op o k bs l as qs)
    every-race op nothing  k bs l as qs po pb pl pa pq = every-lane op nothing bs l as qs po pb pl pa pq
    every-race op (just e) k bs l as qs po pb pl pa pq with M.head e
    ... | nothing = every-lane op (just e) bs l as qs po pb pl pa pq
    ... | just k′ with k′ <ᵖ k
    ...   | true  = every-outer op e (bs ++ l ∷ as) qs po (All++⁺ pb (pl ∷ᴬ pa)) pq
    ...   | false = every-lane op (just e) bs l as qs po pb pl pa pq

    every-outer : ∀ {B} op (e : Events (MonotonicList B)) ls qs → Outer e → All (Every P) ls → All Lane qs
                → Every P (M.outer op e ls qs)
    every (every-outer op (out q m r) ls qs po pl pq)
      with M.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-all op (q ++ [ ix 1 ]) m ls qs
             (held _ (deeper q (ix 1) (ix-mark 1) (proj₁ (outerly po)))) (proj₁ (proj₂ (outerly po))) pl pq
    ... | ls′ , qs′ | (pl′ , pq′) =
      deeper q (ix 0) (ix-mark 0) (proj₁ (outerly po)) , every-go op (just (force r)) ls′ qs′ (proj₂ (proj₂ (outerly po))) pl′ pq′
    every (every-outer op (skip q r) ls qs po pl pq) =
      proj₁ (outerly po) , every-go op (just (force r)) ls qs (proj₂ (outerly po)) pl pq
    every (every-outer op (end c) []       []       po pl pq) = outerly po
    every (every-outer op (end c) []       (m ∷ qs) po pl pq) = outerly po , every-go op nothing [] (m ∷ qs) tt pl pq
    every (every-outer op (end c) (l ∷ ls) qs       po pl pq) = outerly po , every-go op nothing (l ∷ ls) qs tt pl pq
    every (every-outer op hush    ls       qs       po pl pq) = tt

    every-lane : ∀ {B} op (o : Maybe (Events (MonotonicList B))) bs (l : Events B) as qs → Outerᴹ o
               → All (Every P) bs → Every P l → All (Every P) as → All Lane qs → Every P (M.lane op o bs l as qs)
    every (every-lane op o bs (out k b r) as qs po pb pl pa pq) =
      proj₁ (every pl) , every-go op o (bs ++ force r ∷ as) qs po (All++⁺ pb (proj₂ (every pl) ∷ᴬ pa)) pq
    every (every-lane op o bs (skip k r) as qs po pb pl pa pq) =
      proj₁ (every pl) , every-go op o (bs ++ force r ∷ as) qs po (All++⁺ pb (proj₂ (every pl) ∷ᴬ pa)) pq
    every (every-lane op o bs (end c) as (m ∷ qs) po pb pl pa (lm ∷ᴬ pq)) =
      deeper c (ix 0) (ix-mark 0) (every pl)
      , every-go op o (M.observe m (c ++ [ ix 1 ]) ∷ bs ++ as) qs po
          (lm (c ++ [ ix 1 ]) (held _ (deeper c (ix 1) (ix-mark 1) (every pl))) ∷ᴬ All++⁺ pb pa) pq
    every (every-lane op nothing  []       (end c) []       [] po pb pl pa pq) = every pl
    every (every-lane op nothing  []       (end c) (a ∷ as) [] po pb pl pa pq) =
      every pl , every-go op nothing (a ∷ as) [] po pa pq
    every (every-lane op nothing  (b ∷ bs) (end c) as       [] po pb pl pa pq) =
      every pl , every-go op nothing (b ∷ bs ++ as) [] po (All++⁺ pb pa) pq
    every (every-lane op (just e) bs       (end c) as       [] po pb pl pa pq) =
      every pl , every-go op (just e) (bs ++ as) [] po (All++⁺ pb pa) pq
    every (every-lane op o bs hush as qs po pb pl pa pq) = tt

  postulate
    -- A DEFERRED PROGRAM SUBSCRIBED IS HELD TO THE RULES: `reach` at the
    -- program a defer holds.
    --
    -- DEAD ROUTE: `reach` calling itself at `Later.force l`, which is
    --   not structurally smaller, under `every-≈`, so not guarded either;
    --   with the structural calls of the other operators no argument
    --   decreases on every cycle.  An `Every` indexed by depth, by
    --   induction on depth then program, would carry it.
    reach-later : ∀ {Γ A} (l : Later Timeline Γ A) k (ρ : NEnv Γ) → S k → Everyᴱ Src ρ
                → Every P (U.meaning (U.subscribe (Later.force l) k) ρ)

  -- A SUBSCRIPTION IS HELD TO THE RULES: subscribed where they allow,
  -- over sources showing what they allow.
  reach : ∀ {Γ A} (o : Obs Timeline Γ A) k (ρ : NEnv Γ) → S k → Everyᴱ Src ρ → Every P (U.meaning (U.subscribe o k) ρ)
  reach (cold c)          k ρ sk sρ = subst (Every P) (sym (U.start-meaning k (lower c) ρ)) (every-start k (lower c) sk)
  reach empty             k ρ sk sρ = record { every = child k last last-mark sk }
  reach (of xs)           k ρ sk sρ = every-of k 0 xs sk
  reach (map f s)         k ρ sk sρ = every-map f _ (reach s k ρ sk sρ)
  reach (scan f z s)      k ρ sk sρ = every-scan f z _ (reach s k ρ sk sρ)
  reach (takeWhile i q s) k ρ sk sρ = every-take i q _ (reach s k ρ sk sρ)
  reach (flatMap op f s)  k ρ sk sρ =
    every-go (flatOp op) (just (M.mapᴱ F (U.meaning (U.subscribe s k) ρ))) [] []
      (outer-map F _ (λ a j sj → reach (f a) j ρ sj sρ) (reach s k ρ sk sρ)) []ᴬ []ᴬ
    where F = λ a → M.cold λ q → U.meaning (U.subscribe (f a) q) ρ
  reach (connect s b)     k ρ sk sρ =
    every-beside _ _
      (reach b (k ++ [ ix 0 ]) (U.meaning (U.subscribe s (k ++ [ ix 1 ])) ρ ∷ᴬ ρ) (held _ (child k (ix 0) (ix-mark 0) sk))
        (every-mono source _ (reach s (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ) , sρ))
      (reach s (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ)
  reach (connected i)     k ρ sk sρ = every-rejoin k (lookup ρ i) sk (every-lookup Src ρ sρ i)
  reach (defer l)         k ρ sk sρ = record { every =
    child k (ix 0) (ix-mark 0) sk
    , every-≈ _ _ (λ n → agree (U.subscribed (Later.force l) (env-refl (U.hots ρ))) (k ++ [ ix 1 ]))
        (reach-later l (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ) }

-- Keyed under `p`: subscribing where `p` keys, showing strictly under it.
keyedRules : Pos → Rules
keyedRules p = record
  { S      = Owned p
  ; P      = Beneath p
  ; Src    = λ _ → ⊤
  ; child  = λ j l _ o → owned-snoc p j l o
  ; deeper = λ h l _ b → beneath-snoc p h l b
  ; held   = beneath-owned p
  ; frame  = λ n e b → inj₂ (inj₁ (beneath-owned p e b))
  ; join   = λ q j _ o → inj₂ (owned-tagged p j (q ++ [ sub j ]) o (tagged-sub q j))
  ; source = λ _ _ → tt
  }

prefix-split : ∀ a j l → Prefix a (j ++ [ l ]) → Prefix a j ⊎ a ≡ j ++ [ l ]
prefix-split []          j       l _          = inj₁ tt
prefix-split (_ ∷ [])    []      l (refl , _) = inj₂ refl
prefix-split (_ ∷ _ ∷ _) []      l (refl , ())
prefix-split (x ∷ a)     (_ ∷ j) l (refl , q) with prefix-split a j l q
... | inj₁ p  = inj₁ (refl , p)
... | inj₂ eq = inj₂ (cong (x ∷_) eq)

tagged-split : ∀ k q j → Tagged k (q ++ [ sub j ]) → Tagged k q ⊎ Owned k j
tagged-split k []          j (inj₁ o) = inj₂ o
tagged-split k []          j (inj₂ ())
tagged-split k (ix _ ∷ q)  j t        = tagged-split k q j t
tagged-split k (last ∷ q)  j t        = tagged-split k q j t
tagged-split k (sub _ ∷ q) j (inj₁ o) = inj₁ (inj₁ o)
tagged-split k (sub _ ∷ q) j (inj₂ t) with tagged-split k q j t
... | inj₁ t′ = inj₁ (inj₂ t′)
... | inj₂ o  = inj₂ o

-- Neither a prefix of the other.
Unrelated : Pos → Pos → Set
Unrelated k h = ¬ Prefix k h × ¬ Prefix h k

ext-prefix : ∀ {k h} → Ext k h → Prefix k h
ext-prefix (ext l ls) = prefix-++ _ (l ∷ ls)

-- No later and no prefix is earlier.
strict : ∀ k q → q <ᵖ k ≡ false → ¬ Prefix k q → k <ᵖ q ≡ true
strict k q a np with <ᵖ-split k q a
... | inj₁ kq   = kq
... | inj₂ refl = ⊥-elim (np (prefix-refl k))

-- `e`'s first, if any, shows its step outside `q`.
Next : ∀ {A} → Pos → Events A → Set
Next q (out h _ _) = ¬ Ext q (h ++ [ ix 0 ])
Next q (skip h _)  = ¬ Ext q (h ++ [ ix 0 ])
Next q (end h)     = ¬ Ext q (h ++ [ ix 0 ])
Next q hush        = ⊤

away-next : ∀ {A} q (e : Events A) → Away q e → Next (q ++ [ ix 0 ]) e
away-next q (out h _ _) ne = λ x → ne (under-ext q h x)
away-next q (skip h _)  ne = λ x → ne (under-ext q h x)
away-next q (end h)     ne = λ x → ne (under-ext q h x)
away-next q hush        ne = tt

-- The body's next, kept or behind a step.
past-ahead : ∀ {A B} k (b : Events B) q (s : Events∞ A) → Past k b → k <ᵖ q ≡ true → ¬ Ext k q → Past k (M.ahead b q s (M.before q b))
past-ahead k b q s pb kq ne with M.before q b
past-ahead k b           q s pb kq ne | true  = kq , ne
past-ahead k (out _ _ _) q s pb kq ne | false = pb
past-ahead k (skip _ _)  q s pb kq ne | false = pb
past-ahead k (end _)     q s pb kq ne | false = pb
past-ahead k hush        q s pb kq ne | false = tt

clear-ahead : ∀ {A B} k (b : Events B) q (s : Events∞ A) → Clear k b → ¬ Ext k q → Clear k (M.ahead b q s (M.before q b))
clear-ahead k b q s cb ne with M.before q b
clear-ahead k b           q s cb ne | true  = ne
clear-ahead k (out _ _ _) q s cb ne | false = cb
clear-ahead k (skip _ _)  q s cb ne | false = cb
clear-ahead k (end _)     q s cb ne | false = cb
clear-ahead k hush        q s cb ne | false = tt

-- After a step at `q`, the body's next is past it, and so is the next step.
clear-head : ∀ {B} q (b : Events B) → M.before q b ≡ true → Every (λ k → Unrelated k q) b → Clear q b
clear-head q (out k _ _) qk ub = qk , λ x → proj₂ (proj₁ (every ub)) (ext-prefix x)
clear-head q (skip k _)  qk ub = λ x → proj₂ (proj₁ (every ub)) (ext-prefix x)
clear-head q (end k)     qk ub = λ x → proj₂ (every ub) (ext-prefix x)
clear-head q hush        qk ub = tt

clear-step : ∀ {A B} q (b : Events B) q′ (r : Events∞ A) → M.before q b ≡ true → Every (λ k → Unrelated k q) b → ¬ Ext q q′
           → Clear q (M.ahead b q′ r (M.before q′ b))
clear-step q b q′ r qb ub nx with M.before q′ b
clear-step q b           q′ r qb ub nx | true  = nx
clear-step q (out k a r′) q′ r qb ub nx | false = clear-head q (out k a r′) qb ub
clear-step q (skip k r′)  q′ r qb ub nx | false = clear-head q (skip k r′) qb ub
clear-step q (end k)      q′ r qb ub nx | false = clear-head q (end k) qb ub
clear-step q hush         q′ r qb ub nx | false = tt

clear-beside : ∀ {A B} q (b : Events B) (s : Events A) → M.before q b ≡ true → Every (λ k → Unrelated k q) b → Next q s → Clear q (M.beside b s)
clear-beside q b (out h _ r) qb ub nx = clear-step q b (h ++ [ ix 0 ]) r qb ub nx
clear-beside q b (skip h r)  qb ub nx = clear-step q b (h ++ [ ix 0 ]) r qb ub nx
clear-beside q b (end c)     qb ub nx = clear-step q b (c ++ [ ix 0 ]) M.hushed qb ub nx
clear-beside q b hush        qb ub nx = clear-head q b qb ub

-- A SOURCE'S STEPS MERGE INTO A STEADY BODY STEADILY when nothing the
-- body shows lies above or below where a step shows.
mutual
  steady-beside : ∀ {A B} (b : Events B) (s : Events A) → Steady b → Steady s
                → Every (λ k → Every (λ q → Unrelated k (q ++ [ ix 0 ])) s) b → Steady (M.beside b s)
  steady (steady-beside b (out q _ s) sb ss u) =
    steady (steady-ahead b (q ++ [ ix 0 ]) s _ refl sb (proj₂ (steady ss)) (every-mono (λ k x → proj₁ (every x)) b u)
                         (every-mono (λ k x → proj₂ (every x)) b u) (away-next q (force s) (past-away q (force s) (proj₁ (steady ss)))))
  steady (steady-beside b (skip q s) sb ss u) =
    steady (steady-ahead b (q ++ [ ix 0 ]) s _ refl sb (proj₂ (steady ss)) (every-mono (λ k x → proj₁ (every x)) b u)
                         (every-mono (λ k x → proj₂ (every x)) b u) (away-next q (force s) (clear-away q (force s) (proj₁ (steady ss)))))
  steady (steady-beside b (end c) sb ss u) =
    steady (steady-ahead b (c ++ [ ix 0 ]) M.hushed _ refl sb (record { steady = tt }) (every-mono (λ k x → every x) b u)
                         (every-mono (λ k x → record { every = tt }) b u) tt)
  steady (steady-beside b hush sb ss u) = steady sb

  steady-ahead : ∀ {A B} (b : Events B) q (s : Events∞ A) t → t ≡ M.before q b → Steady b → Steady (force s)
               → Every (λ k → Unrelated k q) b → Every (λ k → Every (λ q′ → Unrelated k (q′ ++ [ ix 0 ])) (force s)) b → Next q (force s)
               → Steady (M.ahead b q s t)
  steady (steady-ahead b q s true e sb ss ub us nx) = clear-beside q b (force s) (sym e) ub nx , steady-beside b (force s) sb ss us
  steady (steady-ahead (out k a r) q s false e sb ss ub us nx) =
    past-ahead k (force r) q s (proj₁ (steady sb)) (strict k q (sym e) (proj₁ (proj₁ (every ub)))) (λ x → proj₁ (proj₁ (every ub)) (ext-prefix x))
    , steady-ahead (force r) q s _ refl (proj₂ (steady sb)) ss (proj₂ (every ub)) (proj₂ (every us)) nx
  steady (steady-ahead (skip k r) q s false e sb ss ub us nx) =
    clear-ahead k (force r) q s (proj₁ (steady sb)) (λ x → proj₁ (proj₁ (every ub)) (ext-prefix x))
    , steady-ahead (force r) q s _ refl (proj₂ (steady sb)) ss (proj₂ (every ub)) (proj₂ (every us)) nx
  steady (steady-ahead (end c) q s false e sb ss ub us nx) = tt
  steady (steady-ahead hush q s false e sb ss ub us nx) = tt

-- Neither keys the other.
Disjoint : Pos → Pos → Set
Disjoint a h = ¬ Owned a h × ¬ Owned h a

apart-mark : ∀ a j l → Mark l → Disjoint a j → Disjoint a (j ++ [ l ])
apart-mark a j l m (na , nb) = fwd , λ o → nb (owned-trans j (j ++ [ l ]) a (inj₁ (prefix-++ j [ l ])) o)
  where
    fwd : ¬ Owned a (j ++ [ l ])
    fwd (inj₁ q) with prefix-split a j l q
    ... | inj₁ q′ = na (inj₁ q′)
    ... | inj₂ eq = nb (subst (Owned j) (sym eq) (inj₁ (prefix-++ j [ l ])))
    fwd (inj₂ t) = na (inj₂ (tagged-mark a j l m t))

-- A frame's root holds its burst's tag, so whatever it keys, or keys
-- it, the tag does too.
frame-fwd : ∀ a n e → (∀ m → a ≢ ix (suc m) ∷ []) → ¬ Owned a e → ¬ Owned e a → ¬ Owned a (ix (suc n) ∷ sub e ∷ [])
frame-fwd []              n e nt na nb (inj₁ _)                 = na (inj₁ tt)
frame-fwd (_ ∷ [])        n e nt na nb (inj₁ (refl , _))        = nt n refl
frame-fwd (_ ∷ _ ∷ [])    n e nt na nb (inj₁ (refl , refl , _)) = nb (inj₂ (inj₁ (inj₁ (prefix-refl e))))
frame-fwd (_ ∷ _ ∷ _ ∷ _) n e nt na nb (inj₁ (_ , _ , ()))
frame-fwd a               n e nt na nb (inj₂ (inj₁ o))          = na o
frame-fwd a               n e nt na nb (inj₂ (inj₂ ()))

frame-bwd : ∀ a n e → ¬ Owned e a → ¬ Owned (ix (suc n) ∷ sub e ∷ []) a
frame-bwd []          n e nb (inj₁ ())
frame-bwd (_ ∷ [])    n e nb (inj₁ (_ , ()))
frame-bwd (_ ∷ _ ∷ _) n e nb (inj₁ (refl , refl , _)) = nb (inj₂ (inj₁ (inj₁ (prefix-refl e))))
frame-bwd a           n e nb (inj₂ t)                 = nb (inj₂ (owned-tagged e _ a (inj₂ (inj₁ (inj₁ (prefix-refl e)))) t))

apart-join : ∀ a q j → ¬ Owned a q → Disjoint a j → Disjoint a (q ++ [ sub j ])
apart-join a q j sq (na , nb) = fwd , λ o → nb (owned-trans j (q ++ [ sub j ]) a (inj₂ (tagged-sub q j)) o)
  where
    fwd : ¬ Owned a (q ++ [ sub j ])
    fwd (inj₁ p) with prefix-split a q (sub j) p
    ... | inj₁ p′ = sq (inj₁ p′)
    ... | inj₂ eq = nb (subst (Owned j) (sym eq) (inj₂ (tagged-sub q j)))
    fwd (inj₂ t) with tagged-split a q j t
    ... | inj₁ t′ = sq (inj₂ t′)
    ... | inj₂ o  = na o

-- Apart from `a`, over sources alien to it.
apartRules : ∀ a → (∀ m → a ≢ ix (suc m) ∷ []) → Rules
apartRules a nt = record
  { S      = Disjoint a
  ; P      = Disjoint a
  ; Src    = λ h → ¬ Owned a h
  ; child  = apart-mark a
  ; deeper = apart-mark a
  ; held   = λ _ x → x
  ; frame  = λ n e (na , nb) → frame-fwd a n e nt na nb , frame-bwd a n e nb
  ; join   = apart-join a
  ; source = λ _ → proj₁
  }

-- A SUBSCRIPTION KEYS NOTHING UNDER A POSITION APART FROM IT: over
-- sources alien to `a`, where neither keys the other and `a` is no
-- timer's tick.  `keyedRules` does not carry it: a tag under the join
-- says nothing of the source position it tags.
alien-apart : ∀ {Γ A} (o : Obs Timeline Γ A) a k (ρ : NEnv Γ) → Alienᴱ a ρ → ¬ Owned a k → ¬ Owned k a
            → (∀ m → a ≢ ix (suc m) ∷ []) → Alien a (U.meaning (U.subscribe o k) ρ)
alien-apart o a k ρ al na nb nt = every-mono (λ _ → proj₁) _ (Reach.reach (apartRules a nt) o k ρ (na , nb) al)

-- A flatMap's sources stay out of every lane it can admit: the skip
-- before the lane is keyed under the flatMap, so the lane is.
--
-- REFUTED: f5faeaf6 of sources merely clear of the flatMap's subtree, by one tagged under its join
alien-shown : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
            → ∀ x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.subscribe (flatMap op f s) p) ρ) → Alienᴱ (x ++ [ ix 1 ]) ρ
alien-shown op f s p ρ al x r =
  alienᴱ-owned p (x ++ [ ix 1 ])
    (owned-lane p x (every-reach _ (x ++ [ ix 0 ])
      (Reach.reach (keyedRules p) (flatMap op f s) p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ al)) r)) ρ al

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

  -- A CONNECT'S SOURCE MERGES INTO ITS BODY IN ORDER: each source step a
  -- skip just past it, ahead of the body's later events.
  ordered-beside : ∀ {A B} (b : Events B) (s : Events A) → Ordered b → Ordered s → Ordered (M.beside b s)

  -- A FLATMAP SUBSCRIBED MERGES IN ORDER: over sorted sources alien to
  -- where it subscribes.
  --
  -- The risk is a tie: an outer value at `q` shows as a skip just past
  -- `q`, so an outer event at that same `q` after it would show before
  -- it.  `Steady` sources leave none to rekey; the operators must make
  -- none.
  --
  -- REFUTED: 37b70651 of any outer node in order, by a joiner told a value and a skip at one position
  ordered-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ
               → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ)

  -- A DEFER'S RUN IS IN ORDER: its program, reached, over sorted sources
  -- alien to where it subscribes.
  ordered-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ → Ordered (U.meaning (U.deferᶜ l p []) ρ)

  -- A COLD'S RUN IS STEADY somewhere: its frames step at its ticks.
  steady-start : ∀ {A} p (m : From A 0) → p ≢ [] → Steady (M.start p m)

  -- A LIST'S RUN IS STEADY: each value at the next index.
  steady-of : ∀ {A} p i (xs : List A) → Steady (M.ofᴱ p i xs)

  -- A CUT KEEPS A RUN STEADY: the failing value just inside its own
  -- position, its completion just past that.
  steady-take : ∀ {A} i (p : A → Bool) (e : Events A) → Steady e → Steady (M.takeWhileᴱ i p e)

  -- A FLATMAP SUBSCRIBED SOMEWHERE IS STEADY, over sources sorted and
  -- alien to it: no lane steps inside its outer's last position.
  steady-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
              → Steady (U.meaning (U.subscribe (flatMap op f s) p) ρ)

  -- A SUBSCRIPTION OWNS NOTHING JUST PAST ITS OWN EVENTS, somewhere,
  -- over sources sorted and alien to it: nothing it shows lies under, or
  -- is tagged under, the position just past one of its events.
  alien-steps : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
              → Every (λ q → Alien (q ++ [ ix 0 ]) (U.meaning (U.subscribe o p) ρ)) (U.meaning (U.subscribe o p) ρ)


  -- A DEFER'S RUN IS STEADY somewhere, over sources sorted and alien to it.
  steady-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
               → Steady (U.meaning (U.deferᶜ l p []) ρ)


-- A CONNECT'S SOURCE KEYS NOTHING UNDER ITS BODY: the two are siblings.
alien-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
          → Alien (p ++ [ ix 0 ]) (U.meaning (U.subscribe o (p ++ [ ix 1 ])) ρ)
alien-sub o p ρ al =
  alien-apart o (p ++ [ ix 0 ]) (p ++ [ ix 1 ]) ρ (alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ al)
    (sibling p (λ ())) (sibling p (λ ())) (no-tick p)

every-zip : ∀ {A} {P Q : Pos → Set} (e : Events A) → Every P e → Every Q e → Every (λ h → P h × Q h) e
every (every-zip (out h _ r) pe qe) = (proj₁ (every pe) , proj₁ (every qe)) , every-zip (force r) (proj₂ (every pe)) (proj₂ (every qe))
every (every-zip (skip h r)  pe qe) = (proj₁ (every pe) , proj₁ (every qe)) , every-zip (force r) (proj₂ (every pe)) (proj₂ (every qe))
every (every-zip (end h)     pe qe) = every pe , every qe
every (every-zip hush        pe qe) = tt

-- Of every `q` in `s`, every `k` in `b`: so of every `k`, every `q`.
every-swap : ∀ {A B} {R : Pos → Pos → Set} (b : Events B) (s : Events A) → Every (λ q → Every (R q) b) s → Every (λ k → Every (λ q → R q k) s) b
every (every-swap (out k _ r) s h) = every-mono (λ q x → proj₁ (every x)) s h , every-swap (force r) s (every-mono (λ q x → proj₂ (every x)) s h)
every (every-swap (skip k r)  s h) = every-mono (λ q x → proj₁ (every x)) s h , every-swap (force r) s (every-mono (λ q x → proj₂ (every x)) s h)
every (every-swap (end k)     s h) = every-mono (λ q x → every x) s h
every (every-swap hush        s h) = tt

-- A CONNECT'S BODY STAYS CLEAR OF ITS SOURCE'S STEPS, over sources
-- sorted and alien to it: nothing the body shows lies above or below
-- the position just past any source event, where the step shows.
unrelated-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
                  → Every (λ k → Every (λ q → Unrelated k (q ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ))
                          (U.meaning (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
unrelated-connect s b p ρ np so cl =
  every-swap _ S (every-mono per S (every-zip S keyed (every-zip S (alien-sub s p ρ cl) (alien-steps s (p ++ [ ix 1 ]) ρ (snoc-there p) so cs))))
  where
    S  = U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ
    cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    keyed : Every (Beneath (p ++ [ ix 1 ])) S
    keyed = Reach.reach (keyedRules (p ++ [ ix 1 ])) s (p ++ [ ix 1 ]) ρ (inj₁ (prefix-refl _)) (every-monoᴱ (λ _ _ → tt) ρ cs)
    per : ∀ q → Beneath (p ++ [ ix 1 ]) q × ¬ Owned (p ++ [ ix 0 ]) q × Alien (q ++ [ ix 0 ]) S
        → Every (λ k → Unrelated k (q ++ [ ix 0 ])) (U.meaning (U.subscribe b (p ++ [ ix 0 ])) (S ∷ᴬ ρ))
    per q (bq , nq , aq) =
      every-mono (λ k d → (λ x → proj₂ d (inj₁ x)) , (λ x → proj₁ d (inj₁ x))) _
        (Reach.reach (apartRules (q ++ [ ix 0 ]) (no-tick q)) b (p ++ [ ix 0 ]) (S ∷ᴬ ρ) (proj₂ dq , proj₁ dq)
          (aq , alienᴱ-owned p (q ++ [ ix 0 ]) (beneath-owned p (q ++ [ ix 0 ]) (owned-snoc p q (ix 0) oq)) ρ cl))
      where
        oq : Owned p q
        oq = owned-trans p (p ++ [ ix 1 ]) q (inj₁ (prefix-++ p [ ix 1 ])) (beneath-owned (p ++ [ ix 1 ]) q bq)
        dq : Disjoint (p ++ [ ix 0 ]) (q ++ [ ix 0 ])
        dq = apart-mark (p ++ [ ix 0 ]) q (ix 0) (ix-mark 0)
               (nq , λ o → sibling p {1} {0} (λ ()) (owned-trans (p ++ [ ix 1 ]) q (p ++ [ ix 0 ]) (beneath-owned (p ++ [ ix 1 ]) q bq) o))

-- A program subscribed anywhere, over sorted sources alien to where it
-- subscribes, is placed.
placed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ → Placed (U.subscribe o p) ρ

-- A SUBSCRIPTION OVER STEADY SOURCES IS STEADY: a joiner's skips for
-- what it missed sit just past the join, which nothing it rekeys
-- lies inside, its sources being alien to it.  Somewhere, not at the
-- empty position, where its own steps would sit at bare ticks.
--
-- REFUTED: 91953190 at the empty position, a lane's timer frame shown just inside the outer's step at its tick
-- REFUTED: 42e70878 over sources stepping and then emitting at one position, a takeWhile showing the value inside the step
steady-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
           → Steady (U.meaning (U.subscribe o p) ρ)
steady-sub (cold c) p ρ np so cl = subst Steady (sym (U.start-meaning p (lower c) ρ)) (steady-start p (lower c) np)
steady-sub empty p ρ np so cl = record { steady = tt }
steady-sub (of xs) p ρ np so cl = steady-of p 0 xs
steady-sub (map f s) p ρ np so cl = steady-map f _ (steady-sub s p ρ np so cl)
steady-sub (scan f z s) p ρ np so cl = steady-scan f z _ (steady-sub s p ρ np so cl)
steady-sub (takeWhile i q s) p ρ np so cl = steady-take i q _ (steady-sub s p ρ np so cl)
steady-sub (flatMap op f s) p ρ np so cl = steady-flat op f s p ρ np so cl
steady-sub (connect s b) p ρ np so cl =
  steady-beside _ _ (steady-sub b (p ++ [ ix 0 ]) (S ∷ᴬ ρ) (snoc-there p) ((proj₁ (placed-sub s (p ++ [ ix 1 ]) ρ so cs) , ss) , so)
                                (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl))
                    ss (unrelated-connect s b p ρ np so cl)
  where S  = U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ
        cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
        ss = steady-sub s (p ++ [ ix 1 ]) ρ (snoc-there p) so cs
steady-sub (connected i) p ρ np so cl =
  steady-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
steady-sub (defer l) p ρ np so cl = steady-defer l p ρ np so cl

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
  , λ a x r → placed-sub (f a) (x ++ [ ix 1 ]) ρ so (alien-shown op f s p ρ cl x r)
placed-sub (connect s b) p ρ so cl = ordered-beside _ _ (proj₁ pb) (proj₁ ps) , pb , ps
  where cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
        ps = placed-sub s (p ++ [ ix 1 ]) ρ so cs
        pb = placed-sub b (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ)
               ((proj₁ ps , steady-sub s (p ++ [ ix 1 ]) ρ (snoc-there p) so cs) , so) (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl)
placed-sub (connected i) p ρ so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl) , tt
  where sl = sorted-lookup ρ so i
placed-sub (defer l) p ρ so cl = ordered-defer l p ρ so cl , tt

-- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root is
-- placed.
placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
placed-subscribe o = placed-sub o root []ᴬ tt tt
