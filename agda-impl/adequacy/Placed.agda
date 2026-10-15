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
open import Data.Nat.Properties using (+-suc; +-monoʳ-≤; +-monoʳ-<; <⇒≤; <-≤-trans; ≤-trans; ≤-reflexive; m≤n+m; m≤m+n; <-irrefl; ≤-refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; agree; Earliest; none; found; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root; <ᵖ-asym; <ᵖ-down; <ᵖ-next; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-part; ≮-trans; <ᵖ-below; <ᵖ-step; <ᵖ-tick)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (env-refl)
open import adequacy.Finite using (Finite; cold-f; empty-f; of-f; map-f; scan-f; takeWhile-f; flatMap-f; connect-f; connected-f; defer-f; trunc; finite-trunc; trunc-agree)

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

-- Nothing a run shows lies under, or is tagged under, the position just
-- past one of its own events, where a step there would show.
Fresh : ∀ {A} → Events A → Set
Fresh e = Every (λ q → Alien (q ++ [ ix 0 ]) e) e

-- Every source alien to `p`: what a subscription at `p` keys.
Alienᴱ : ∀ {Γ} → Pos → NEnv Γ → Set
Alienᴱ p = Everyᴱ (λ h → ¬ Owned p h)

-- `e` shows an event at `k`.
data Reaches {A} (k : Pos) : Events A → Set where
  out-here   : ∀ {a r} → Reaches k (out k a r)
  skip-here  : ∀ {r} → Reaches k (skip k r)
  out-there  : ∀ {h a r} → Reaches k (force r) → Reaches k (out h a r)
  skip-there : ∀ {h r} → Reaches k (force r) → Reaches k (skip h r)

-- A tick heads it, as it heads every position under the root: a
-- timer's frame sits at a bare tick, so only there does it sort after
-- the steps before it.
Headed : Pos → Set
Headed (ix _ ∷ _) = ⊤
Headed _          = ⊥

-- Each connect's source in order, steady, and headed.
Sorted : ∀ {Γ} → NEnv Γ → Set
Sorted []ᴬ      = ⊤
Sorted (e ∷ᴬ ρ) = (Ordered e × Steady e) × Every Headed e × Sorted ρ

-- Every node's meaning in order, read in its own environment: a
-- connect's body reading its source's, a flatMap's lanes yet to
-- subscribe reading its own, each where the flatMap shows a skip just
-- before it, as it does when it admits one; a defer's sources, its
-- notices put back, as they stood when it subscribed, headed and
-- sorted and alien to it, as its program subscribed needs them.
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
  Within (U.deferᶜ l p ns)          ρ = Headed p × Sorted (U.replay ns ρ) × Alienᴱ p (U.replay ns ρ)
  Within _                          ρ = ⊤

  Placedᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  Placedᴹ nothing  ρ = ⊤
  Placedᴹ (just c) ρ = Placed c ρ

  Placedᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  Placedᴸ []       ρ = ⊤
  Placedᴸ (c ∷ cs) ρ = Placed c ρ × Placedᴸ cs ρ

headed-snoc : ∀ p {l : M.Label} → Headed p → Headed (p ++ [ l ])
headed-snoc (ix _ ∷ _) h = tt
headed-snoc []         ()
headed-snoc (sub _ ∷ _) ()
headed-snoc (last ∷ _) ()

headed-there : ∀ p → Headed p → p ≢ []
headed-there (ix _ ∷ _) h ()

sorted-lookup : ∀ {Γ A} (ρ : NEnv Γ) → Sorted ρ → (i : A ∈ Γ) → Ordered (lookup ρ i) × Steady (lookup ρ i)
sorted-lookup (e ∷ᴬ ρ) (o , _ , so) (here refl) = o
sorted-lookup (e ∷ᴬ ρ) (o , _ , so) (there i)   = sorted-lookup ρ so i

sorted-headed : ∀ {Γ} (ρ : NEnv Γ) → Sorted ρ → Everyᴱ Headed ρ
sorted-headed []ᴬ      _            = tt
sorted-headed (e ∷ᴬ ρ) (_ , h , so) = h , sorted-headed ρ so

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

snoc-inj : ∀ x q {l l′ : M.Label} → x ++ [ l ] ≡ q ++ [ l′ ] → x ≡ q × l ≡ l′
snoc-inj []      []      e = refl , proj₁ (∷-injective e)
snoc-inj []      (_ ∷ q) e = ⊥-elim (snoc-there q (sym (∷-injectiveʳ e)))
snoc-inj (_ ∷ x) []      e = ⊥-elim (snoc-there x (∷-injectiveʳ e))
snoc-inj (a ∷ x) (_ ∷ q) e with ∷-injective e
... | refl , e′ = cong (a ∷_) (proj₁ (snoc-inj x q e′)) , proj₂ (snoc-inj x q e′)

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

-- A mark weighs one.
weigh-mark : ∀ h l → Mark l → weigh (h ++ [ l ]) ≡ suc (weigh h)
weigh-mark []      _ (ix-mark _) = refl
weigh-mark []      _ last-mark   = refl
weigh-mark (a ∷ h) l m           = trans (cong (weighˡ a +_) (weigh-mark h l m)) (+-suc (weighˡ a) (weigh h))

prefix⁺-weigh : ∀ k h → Prefix⁺ k h → weigh k < weigh h
prefix⁺-weigh []      (ix _ ∷ h)  _          = s≤s z≤n
prefix⁺-weigh []      (sub _ ∷ h) _          = s≤s z≤n
prefix⁺-weigh []      (last ∷ h)  _          = s≤s z≤n
prefix⁺-weigh (_ ∷ _) []          ()
prefix⁺-weigh (a ∷ k) (_ ∷ h)     (refl , p) = +-monoʳ-< (weighˡ a) (prefix⁺-weigh k h p)

-- Strictly keyed under `p` is heavier than `p`.
beneath-weigh : ∀ p h → Beneath p h → weigh p < weigh h
beneath-weigh p h (inj₁ q) = prefix⁺-weigh p h q
beneath-weigh p h (inj₂ t) = tagged-weigh p h t

-- Just past a position keys nothing as heavy as it.
past-weigh : ∀ x h → weigh h ≤ weigh x → ¬ Owned (x ++ [ ix 0 ]) h
past-weigh x h le o = <-irrefl refl (<-≤-trans (s≤s le) (subst (_≤ weigh h) (weigh-mark x (ix 0) (ix-mark 0)) (owned-weigh _ _ o)))

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

-- What follows a run's first event; nothing after its end.
rest : ∀ {A} → Events A → Events A
rest (out _ _ r) = force r
rest (skip _ r)  = force r
rest (end _)     = hush
rest hush        = hush

rest-agree : ∀ {A k} {x y : Events A} → Agree (suc k) x y → Agree k (rest x) (rest y)
rest-agree         (out⁼ a)  = a
rest-agree         (skip⁼ a) = a
rest-agree {k = k} end⁼      = M.agree-refl k hush
rest-agree {k = k} hush⁼     = M.agree-refl k hush

rest-every : ∀ {A} {P : Pos → Set} (x : Events A) → Every P x → Every P (rest x)
rest-every (out _ _ r) px = proj₂ (every px)
rest-every (skip _ r)  px = proj₂ (every px)
rest-every (end _)     px = record { every = tt }
rest-every hush        px = px

-- A LIMIT SHOWS WHAT ITS APPROXIMANTS SHOW: what agrees with the `n`th
-- of a sequence for `n` steps, each showing only positions satisfying
-- `P`, does too.
mutual
  every-lim : ∀ {A} {P : Pos → Set} (xs : ℕ → Events A) (y : Events A) → (∀ n → Every P (xs n)) → (∀ n → Agree n (xs n) y)
            → Every P y
  every (every-lim xs y px ag) = everys-lim xs y px ag (xs 1) (px 1) (ag 1)

  everys-lim : ∀ {A} {P : Pos → Set} (xs : ℕ → Events A) (y : Events A) → (∀ n → Every P (xs n)) → (∀ n → Agree n (xs n) y)
             → (x : Events A) → Every P x → Agree 1 x y → Everys P y
  everys-lim xs (out h _ r) px ag (out h _ _) ex (out⁼ _) =
    proj₁ (every ex) , every-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-every (xs (suc n)) (px (suc n))) (λ n → rest-agree (ag (suc n)))
  everys-lim xs (skip h r)  px ag (skip h _)  ex (skip⁼ _) =
    proj₁ (every ex) , every-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-every (xs (suc n)) (px (suc n))) (λ n → rest-agree (ag (suc n)))
  everys-lim xs (end h)     px ag (end h)     ex end⁼      = every ex
  everys-lim xs hush        px ag hush        ex hush⁼     = tt

-- What agrees at every depth shows the same positions.
every-≈ : ∀ {A} {P : Pos → Set} (x y : Events A) → (∀ k → Agree k x y) → Every P x → Every P y
every-≈ x y a px = every-lim (λ _ → x) y (λ _ → px) a

-- What agrees for a step starts alike.
atop-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Atop k x → Atop k y
atop-agree (out⁼ _)  a = a
atop-agree (skip⁼ _) a = a
atop-agree end⁼      a = a
atop-agree hush⁼     a = a

past-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Past k x → Past k y
past-agree (out⁼ _)  a = a
past-agree (skip⁼ _) a = a
past-agree end⁼      a = a
past-agree hush⁼     a = a

clear-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Clear k x → Clear k y
clear-agree (out⁼ _)  a = a
clear-agree (skip⁼ _) a = a
clear-agree end⁼      a = a
clear-agree hush⁼     a = a

rest-ordered : ∀ {A} (x : Events A) → Ordered x → Ordered (rest x)
rest-ordered (out _ _ _) o = proj₂ (ordered o)
rest-ordered (skip _ _)  o = proj₂ (ordered o)
rest-ordered (end _)     o = record { ordered = tt }
rest-ordered hush        o = o

rest-steady : ∀ {A} (x : Events A) → Steady x → Steady (rest x)
rest-steady (out _ _ _) o = proj₂ (steady o)
rest-steady (skip _ _)  o = proj₂ (steady o)
rest-steady (end _)     o = record { steady = tt }
rest-steady hush        o = o

-- A LIMIT OF RUNS IN ORDER IS IN ORDER, and of steady runs steady: each
-- reads an event and the next, which the second approximant shows.
mutual
  ordered-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Ordered (xs n)) → (∀ n → Agree n (xs n) y) → Ordered y
  ordered (ordered-lim xs y po ag) = orders-lim xs y po ag (xs 2) (po 2) (ag 2)

  orders-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Ordered (xs n)) → (∀ n → Agree n (xs n) y)
             → (x : Events A) → Ordered x → Agree 2 x y → Orders y
  orders-lim xs (out h _ r) po ag (out h _ _) ox (out⁼ a) =
    atop-agree a (proj₁ (ordered ox))
    , ordered-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-ordered (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  orders-lim xs (skip h r)  po ag (skip h _)  ox (skip⁼ a) =
    atop-agree a (proj₁ (ordered ox))
    , ordered-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-ordered (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  orders-lim xs (end h)     po ag (end h)     ox end⁼      = tt
  orders-lim xs hush        po ag hush        ox hush⁼     = tt

mutual
  steady-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Steady (xs n)) → (∀ n → Agree n (xs n) y) → Steady y
  steady (steady-lim xs y po ag) = steadies-lim xs y po ag (xs 2) (po 2) (ag 2)

  steadies-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Steady (xs n)) → (∀ n → Agree n (xs n) y)
               → (x : Events A) → Steady x → Agree 2 x y → Steadies y
  steadies-lim xs (out h _ r) po ag (out h _ _) ox (out⁼ a) =
    past-agree a (proj₁ (steady ox))
    , steady-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-steady (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  steadies-lim xs (skip h r)  po ag (skip h _)  ox (skip⁼ a) =
    clear-agree a (proj₁ (steady ox))
    , steady-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-steady (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  steadies-lim xs (end h)     po ag (end h)     ox end⁼      = tt
  steadies-lim xs hush        po ag hush        ox hush⁼     = tt

ordered-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Ordered x → Ordered y
ordered-≈ x y a o = ordered-lim (λ _ → x) y (λ _ → o) a

steady-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Steady x → Steady y
steady-≈ x y a o = steady-lim (λ _ → x) y (λ _ → o) a

fresh-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Fresh x → Fresh y
fresh-≈ x y a fx = every-≈ x y a (every-mono (λ q → every-≈ x y a) x fx)

every-map : ∀ {A B} {P : Pos → Set} (f : A → B) (e : Events A) → Every P e → Every P (M.mapᴱ f e)
every (every-map f (out k a r) pe) = proj₁ (every pe) , every-map f (force r) (proj₂ (every pe))
every (every-map f (skip k r)  pe) = proj₁ (every pe) , every-map f (force r) (proj₂ (every pe))
every (every-map f (end k)     pe) = every pe
every (every-map f hush        pe) = tt

every-scan : ∀ {A B} {P : Pos → Set} (f : B → A → B) z (e : Events A) → Every P e → Every P (M.scanᴱ f z e)
every (every-scan f z (out k a r) pe) = proj₁ (every pe) , every-scan f (f z a) (force r) (proj₂ (every pe))
every (every-scan f z (skip k r)  pe) = proj₁ (every pe) , every-scan f z (force r) (proj₂ (every pe))
every (every-scan f z (end k)     pe) = every pe
every (every-scan f z hush        pe) = tt

-- A connect shows each of its source's steps, and its end, just past it.
mutual
  every-beside : ∀ {A B} {P : Pos → Set} (b : Events B) (s : Events A) → Every P b → Every (λ q → P (q ++ [ ix 0 ])) s → Every P (M.beside b s)
  every (every-beside b (out q _ r) pb ps) =
    every (every-ahead b (q ++ [ ix 0 ]) r (M.before (q ++ [ ix 0 ]) b) pb (proj₁ (every ps)) (proj₂ (every ps)))
  every (every-beside b (skip q r)  pb ps) =
    every (every-ahead b (q ++ [ ix 0 ]) r (M.before (q ++ [ ix 0 ]) b) pb (proj₁ (every ps)) (proj₂ (every ps)))
  every (every-beside b (end c)     pb ps) =
    every (every-ahead b (c ++ [ ix 0 ]) M.hushed (M.before (c ++ [ ix 0 ]) b) pb (every ps) (record { every = tt }))
  every (every-beside b hush        pb ps) = every pb

  every-ahead : ∀ {A B} {P : Pos → Set} (b : Events B) q (s : Events∞ A) t → Every P b → P q → Every (λ q → P (q ++ [ ix 0 ])) (force s)
              → Every P (M.ahead b q s t)
  every (every-ahead b           q s true  pb pq ps) = pq , every-beside b (force s) pb ps
  every (every-ahead (out k a r) q s false pb pq ps) = proj₁ (every pb) , every-ahead (force r) q s _ (proj₂ (every pb)) pq ps
  every (every-ahead (skip k r)  q s false pb pq ps) = proj₁ (every pb) , every-ahead (force r) q s _ (proj₂ (every pb)) pq ps
  every (every-ahead (end c)     q s false pb pq ps) = every pb
  every (every-ahead hush        q s false pb pq ps) = tt

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

  -- A SUBSCRIPTION IS HELD TO THE RULES: subscribed where they allow,
  -- over sources showing what they allow.
  reachᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ k (ρ : NEnv Γ) → S k → Everyᴱ Src ρ → Every P (U.meaning (U.subscribe o k) ρ)
  reachᶠ (cold c) (cold-f _)          k ρ sk sρ = subst (Every P) (sym (U.start-meaning k (lower c) ρ)) (every-start k (lower c) sk)
  reachᶠ empty empty-f             k ρ sk sρ = record { every = child k last last-mark sk }
  reachᶠ (of xs) (of-f _)           k ρ sk sρ = every-of k 0 xs sk
  reachᶠ (map f s) (map-f fs)         k ρ sk sρ = every-map f _ (reachᶠ s fs k ρ sk sρ)
  reachᶠ (scan f z s) (scan-f fs)      k ρ sk sρ = every-scan f z _ (reachᶠ s fs k ρ sk sρ)
  reachᶠ (takeWhile i q s) (takeWhile-f fs) k ρ sk sρ = every-take i q _ (reachᶠ s fs k ρ sk sρ)
  reachᶠ (flatMap op f s) (flatMap-f ff fs)  k ρ sk sρ =
    every-go (flatOp op) (just (M.mapᴱ F (U.meaning (U.subscribe s k) ρ))) [] []
      (outer-map F _ (λ a j sj → reachᶠ (f a) (ff a) j ρ sj sρ) (reachᶠ s fs k ρ sk sρ)) []ᴬ []ᴬ
    where F = λ a → M.cold λ q → U.meaning (U.subscribe (f a) q) ρ
  reachᶠ (connect s b) (connect-f fs fb)     k ρ sk sρ =
    every-beside _ _
      (reachᶠ b fb (k ++ [ ix 0 ]) (U.meaning (U.subscribe s (k ++ [ ix 1 ])) ρ ∷ᴬ ρ) (held _ (child k (ix 0) (ix-mark 0) sk))
        (every-mono source _ (reachᶠ s fs (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ) , sρ))
      (every-mono (λ q → deeper q (ix 0) (ix-mark 0)) _ (reachᶠ s fs (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ))
  reachᶠ (connected i) (connected-f _)     k ρ sk sρ = every-rejoin k (lookup ρ i) sk (every-lookup Src ρ sρ i)
  reachᶠ (defer l) (defer-f fl)         k ρ sk sρ = record { every =
    child k (ix 0) (ix-mark 0) sk
    , every-≈ _ _ (λ n → agree (U.subscribed (Later.force l) (env-refl (U.hots ρ))) (k ++ [ ix 1 ]))
        (reachᶠ (Later.force l) fl (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ) }

  -- A SUBSCRIPTION IS HELD TO THE RULES: its truncations are, and it
  -- agrees with each for as many steps as it is deep.
  reach : ∀ {Γ A} (o : Obs Timeline Γ A) k (ρ : NEnv Γ) → S k → Everyᴱ Src ρ → Every P (U.meaning (U.subscribe o k) ρ)
  reach o k ρ sk sρ =
    every-lim (λ n → U.meaning (U.subscribe (trunc n o) k) ρ) _ (λ n → reachᶠ (trunc n o) (finite-trunc n o) k ρ sk sρ) (λ n → trunc-agree n o k ρ)

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

-- Headed: subscribing where a tick heads, over sources so headed.
headedRules : Rules
headedRules = record
  { S      = Headed
  ; P      = Headed
  ; Src    = Headed
  ; child  = λ j _ _ h → headed-snoc j h
  ; deeper = λ h _ _ x → headed-snoc h x
  ; held   = λ _ x → x
  ; frame  = λ _ _ _ → tt
  ; join   = λ q _ hq _ → headed-snoc q hq
  ; source = λ _ x → x
  }

-- A SUBSCRIPTION WHERE A TICK HEADS SHOWS ONLY WHERE ONE HEADS.
headed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Every Headed (U.meaning (U.subscribe o p) ρ)
headed-sub o p ρ hp so = Reach.reach headedRules o p ρ hp (sorted-headed ρ so)

-- A lane subscribes headed just past where the step admitting it shows.
headed-lane : ∀ x → Headed (x ++ [ ix 0 ]) → Headed (x ++ [ ix 1 ])
headed-lane []          h = tt
headed-lane (ix _ ∷ _)  h = tt
headed-lane (sub _ ∷ _) ()
headed-lane (last ∷ _)  ()

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

-- After each value at `x`, nothing later lies where a lane admitted
-- after it would key, or is keyed by where `x`'s lane subscribes.
mutual
  Spreads : ∀ {A} → Events A → Set
  Spreads (out x _ r) = Every (λ y → Disjoint (y ++ [ ix 1 ]) (x ++ [ ix 1 ])) (force r) × Spread (force r)
  Spreads (skip _ r)  = Spread (force r)
  Spreads (end _)     = ⊤
  Spreads hush        = ⊤

  record Spread {A} (e : Events A) : Set where
    coinductive
    field spread : Spreads e

open Spread public

spread-map : ∀ {A B} (f : A → B) (e : Events A) → Spread e → Spread (M.mapᴱ f e)
spread (spread-map f (out x a r) s) = every-map f (force r) (proj₁ (spread s)) , spread-map f (force r) (proj₂ (spread s))
spread (spread-map f (skip x r)  s) = spread-map f (force r) (spread s)
spread (spread-map f (end x)     s) = tt
spread (spread-map f hush        s) = tt

spread-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Spread e → Spread (M.scanᴱ f z e)
spread (spread-scan f z (out x a r) s) = every-scan f (f z a) (force r) (proj₁ (spread s)) , spread-scan f (f z a) (force r) (proj₂ (spread s))
spread (spread-scan f z (skip x r)  s) = spread-scan f z (force r) (spread s)
spread (spread-scan f z (end x)     s) = tt
spread (spread-scan f z hush        s) = tt

rest-spread : ∀ {A} (x : Events A) → Spread x → Spread (rest x)
rest-spread (out _ _ _) s = proj₂ (spread s)
rest-spread (skip _ _)  s = spread s
rest-spread (end _)     s = record { spread = tt }
rest-spread hush        s = s

spread-head : ∀ {A n} {x : Events A} {h a r} → Agree (suc n) x (out h a r) → Spread x
            → Every (λ y → Disjoint (y ++ [ ix 1 ]) (h ++ [ ix 1 ])) (rest x)
spread-head (out⁼ _) s = proj₁ (spread s)

-- A LIMIT OF SPREAD RUNS IS SPREAD: each value's later positions are
-- read by every approximant past it.
mutual
  spread-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Spread (xs n)) → (∀ n → Agree n (xs n) y) → Spread y
  spread (spread-lim xs y ps ag) = spreads-lim xs y ps ag

  spreads-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Spread (xs n)) → (∀ n → Agree n (xs n) y) → Spreads y
  spreads-lim xs (out h a r) ps ag =
    every-lim (λ n → rest (xs (suc n))) (force r) (λ n → spread-head (ag (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
    , spread-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-spread (xs (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
  spreads-lim xs (skip h r)  ps ag =
    spread-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-spread (xs (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
  spreads-lim xs (end h)     ps ag = tt
  spreads-lim xs hush        ps ag = tt

spread-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Spread x → Spread y
spread-≈ x y a sp = spread-lim (λ _ → x) y (λ _ → sp) a

-- `e`'s first, if any, strictly past `k`.
Beyond : ∀ {A} → Pos → Events A → Set
Beyond k (out h _ _) = k <ᵖ h ≡ true
Beyond k (skip h _)  = k <ᵖ h ≡ true
Beyond k (end h)     = k <ᵖ h ≡ true
Beyond k hush        = ⊤

-- Shown just past one no earlier is no earlier.
snoc-atop : ∀ q l k → q <ᵖ k ≡ false → (q ++ [ l ]) <ᵖ k ≡ false
snoc-atop q l k a = ≮-trans k q (q ++ [ l ]) a (<ᵖ-asym q (q ++ [ l ]) (<ᵖ-below q []))

atop-weaken : ∀ {A} k k′ (e : Events A) → k <ᵖ k′ ≡ false → Atop k e → Atop k′ e
atop-weaken k k′ (out h _ _) kk a = ≮-trans k′ k h kk a
atop-weaken k k′ (skip h _)  kk a = ≮-trans k′ k h kk a
atop-weaken k k′ (end h)     kk a = ≮-trans k′ k h kk a
atop-weaken k k′ hush        kk a = tt

beyond-atop : ∀ {A} k (e : Events A) → Beyond k e → Atop k e
beyond-atop k (out h _ _) b = <ᵖ-asym k h b
beyond-atop k (skip h _)  b = <ᵖ-asym k h b
beyond-atop k (end h)     b = <ᵖ-asym k h b
beyond-atop k hush        b = tt

beyond-step : ∀ {A} k (e : Events A) → Beyond k e → Atop (k ++ [ ix 0 ]) e
beyond-step k (out h _ _) b = <ᵖ-step k h b
beyond-step k (skip h _)  b = <ᵖ-step k h b
beyond-step k (end h)     b = <ᵖ-step k h b
beyond-step k hush        b = tt

beyond-still : ∀ {A} k′ k (e : Events A) → k′ <ᵖ k ≡ true → Atop k e → Beyond k′ e
beyond-still k′ k (out h _ _) kk a = still k′ k h kk a
beyond-still k′ k (skip h _)  kk a = still k′ k h kk a
beyond-still k′ k (end h)     kk a = still k′ k h kk a
beyond-still k′ k hush        kk a = tt

past-beyond : ∀ {A} k (e : Events A) → Past k e → Beyond k e
past-beyond k (out _ _ _) c = proj₁ c
past-beyond k (skip _ _)  c = proj₁ c
past-beyond k (end _)     c = proj₁ c
past-beyond k hush        c = tt

-- No earlier than `c`, and keying nothing `c`'s keeper keys: past it.
atop-clear : ∀ {A} r c (e : Events A) → Owned r c → Atop c e → Every (λ h → ¬ Owned r h) e → Beyond c e
atop-clear r c (out h _ _) oc a al with <ᵖ-split c h a
... | inj₁ ch   = ch
... | inj₂ refl = ⊥-elim (proj₁ (every al) oc)
atop-clear r c (skip h _)  oc a al with <ᵖ-split c h a
... | inj₁ ch   = ch
... | inj₂ refl = ⊥-elim (proj₁ (every al) oc)
atop-clear r c (end h)     oc a al with <ᵖ-split c h a
... | inj₁ ch   = ch
... | inj₂ refl = ⊥-elim (every al oc)
atop-clear r c hush        oc a al = tt

-- A run past `k` keying nothing under it is clear of it.
beyond-clear : ∀ {A} k (e : Events A) → Beyond k e → Alien k e → Clear k e
beyond-clear k (out h _ _) b al = b , λ { (ext l ls) → proj₁ (every al) (inj₁ (prefix-++ k (l ∷ ls))) }
beyond-clear k (skip h _)  b al = λ { (ext l ls) → proj₁ (every al) (inj₁ (prefix-++ k (l ∷ ls))) }
beyond-clear k (end h)     b al = λ { (ext l ls) → every al (inj₁ (prefix-++ k (l ∷ ls))) }
beyond-clear k hush        b al = tt

-- Read off the first's position.
Hush : ∀ {A} → Events A → Set
Hush e = M.head e ≡ nothing

atop-nothing : ∀ {A} k (e : Events A) → Hush e → Atop k e
atop-nothing k (out _ _ _) ()
atop-nothing k (skip _ _)  ()
atop-nothing k (end _)     ()
atop-nothing k hush        h = tt

atop-just : ∀ {A} (e : Events A) {k k′} → M.head e ≡ just k → k <ᵖ k′ ≡ false → Atop k′ e
atop-just (out _ _ _) refl a = a
atop-just (skip _ _)  refl a = a
atop-just (end _)     refl a = a
atop-just hush        ()   a

beyond-nothing : ∀ {A} k (e : Events A) → Hush e → Beyond k e
beyond-nothing k (out _ _ _) ()
beyond-nothing k (skip _ _)  ()
beyond-nothing k (end _)     ()
beyond-nothing k hush        h = tt

beyond-just : ∀ {A} k′ (e : Events A) {k} → M.head e ≡ just k → k′ <ᵖ k ≡ true → Beyond k′ e
beyond-just k′ (out _ _ _) refl b = b
beyond-just k′ (skip _ _)  refl b = b
beyond-just k′ (end _)     refl b = b
beyond-just k′ hush        ()   b

Atopᴹ : ∀ {A} → Pos → Maybe (Events A) → Set
Atopᴹ k nothing  = ⊤
Atopᴹ k (just e) = Atop k e

-- The merge's first is no earlier than `k` when no lane's and not the
-- outer's is: each step it shows sits just past an event of theirs.
atop-lane : ∀ {B} op (o : Maybe (Events (MonotonicList B))) bs (l : Events B) as qs k → Atop k l → Atop k (M.lane op o bs l as qs)
atop-lane op o        bs      (out _ _ _) as      qs       k a = a
atop-lane op o        bs      (skip _ _)  as      qs       k a = a
atop-lane op o        bs      (end c)     as      (m ∷ qs) k a = snoc-atop c (ix 0) k a
atop-lane op nothing  []      (end c)     []      []       k a = a
atop-lane op nothing  []      (end c)     (_ ∷ _) []       k a = a
atop-lane op nothing  (_ ∷ _) (end c)     as      []       k a = a
atop-lane op (just _) bs      (end c)     as      []       k a = a
atop-lane op o        bs      hush        as      qs       k a = tt

atop-outer : ∀ {B} op (e : Events (MonotonicList B)) ls qs k → Atop k e → Atop k (M.outer op e ls qs)
atop-outer op (out q m r) ls qs k a with M.admit op (q ++ [ ix 1 ]) m ls qs
... | ls′ , qs′ = snoc-atop q (ix 0) k a
atop-outer op (skip q r) ls       qs       k a = a
atop-outer op (end c)    []       []       k a = a
atop-outer op (end c)    []       (m ∷ qs) k a = a
atop-outer op (end c)    (l ∷ ls) qs       k a = a
atop-outer op hush       ls       qs       k a = tt

atop-race : ∀ {B} op (o : Maybe (Events (MonotonicList B))) k′ bs (l : Events B) as qs k → Atop k l → Atopᴹ k o
          → Atop k (M.race op o k′ bs l as qs)
atop-race op nothing  k′ bs l as qs k al ao = atop-lane op nothing bs l as qs k al
atop-race op (just e) k′ bs l as qs k al ao with M.head e
... | nothing = atop-lane op (just e) bs l as qs k al
... | just k″ with k″ <ᵖ k′
...   | true  = atop-outer op e (bs ++ l ∷ as) qs k ao
...   | false = atop-lane op (just e) bs l as qs k al

atop-via : ∀ {B} op (o : Maybe (Events (MonotonicList B))) ls qs k → Atopᴹ k o → Atop k (M.viaOuter op o ls qs)
atop-via op nothing  ls qs k ao = tt
atop-via op (just e) ls qs k ao = atop-outer op e ls qs k ao

atop-go : ∀ {B} op (o : Maybe (Events (MonotonicList B))) ls qs k → All (Atop k) ls → Atopᴹ k o → Atop k (M.go op o ls qs)
atop-go op o ls qs k al ao with M.earliest ls | earliest-all (Atop k) ls al
... | none             | _             = atop-via op o ls qs k ao
... | found k′ bs l as | (_ , al′ , _) = atop-race op o k′ bs l as qs k al′ ao

-- A cut, a merge with a source's steps, a join: each first no earlier
-- than what it reads, or than where it subscribes.
atop-take : ∀ {A} i (q : A → Bool) k (e : Events A) → Atop k e → Atop k (M.takeWhileᴱ i q e)
atop-take i q k (out h a r) at with q a
atop-take i     q k (out h a r) at | true  = at
atop-take true  q k (out h a r) at | false = snoc-atop h (ix 0) k at
atop-take false q k (out h a r) at | false = snoc-atop h last k at
atop-take i q k (skip _ _) at = at
atop-take i q k (end _)    at = at
atop-take i q k hush       at = tt

atop-ahead : ∀ {A B} (b : Events B) q (s : Events∞ A) t k → Atop k b → q <ᵖ k ≡ false → Atop k (M.ahead b q s t)
atop-ahead b           q s true  k ab aq = aq
atop-ahead (out _ _ _) q s false k ab aq = ab
atop-ahead (skip _ _)  q s false k ab aq = ab
atop-ahead (end _)     q s false k ab aq = ab
atop-ahead hush        q s false k ab aq = tt

atop-beside : ∀ {A B} (b : Events B) (s : Events A) k → Atop k b → Atop k s → Atop k (M.beside b s)
atop-beside b (out q _ s) k ab as = atop-ahead b (q ++ [ ix 0 ]) s _ k ab (snoc-atop q (ix 0) k as)
atop-beside b (skip q s)  k ab as = atop-ahead b (q ++ [ ix 0 ]) s _ k ab (snoc-atop q (ix 0) k as)
atop-beside b (end c)     k ab as = atop-ahead b (c ++ [ ix 0 ]) _ _ k ab (snoc-atop c (ix 0) k as)
atop-beside b hush        k ab as = ab

atop-rejoin : ∀ {A} p (e : Events A) → Atop p (M.rejoin p e)
atop-rejoin p (out q a k) with p <ᵖ q in pq
... | true  = snoc-atop q (sub p) p (<ᵖ-asym p q pq)
... | false = <ᵖ-asym p (p ++ [ ix 0 ]) (<ᵖ-below p [])
atop-rejoin p (skip q k)  with p <ᵖ q in pq
... | true  = snoc-atop q (sub p) p (<ᵖ-asym p q pq)
... | false = <ᵖ-asym p (p ++ [ ix 0 ]) (<ᵖ-below p [])
atop-rejoin p (end c)     with p <ᵖ c in pc
... | true  = snoc-atop c (sub p) p (<ᵖ-asym p c pc)
... | false = <ᵖ-asym p (p ++ [ last ]) (<ᵖ-below p [])
atop-rejoin p hush        = tt

-- A cold's first: its subscribe burst under where it subscribes, or a
-- frame at a later tick than the one heading it.
rise-burst : ∀ {A t} τ r i (b : M.Frame A t) k → (r ++ [ ix i ]) <ᵖ k ≡ false → Atop k (M.burst τ r i b)
rise-burst τ r i (M.emit _ _) k h = h
rise-burst τ r i (M.stall _)  k h = h
rise-burst τ r i (M.close _)  k h = h

rise-tick : ∀ τ n x j′ → (ix (τ + suc n) ∷ x) <ᵖ (ix τ ∷ j′) ≡ false
rise-tick τ n x j′ with (ix (τ + suc n) ∷ x) <ᵖ (ix τ ∷ j′) in h
... | false = refl
... | true  = ⊥-elim (<-irrefl refl (≤-trans (subst (_≤ τ) (+-suc τ n) (<ᵖ-tick (τ + suc n) τ x j′ h)) (m≤m+n τ n)))

rise-start : ∀ {A} τ j′ (m : From A 0) → Atop (ix τ ∷ j′) (M.start (ix τ ∷ j′) m)
rise-start τ j′ (M.at zero _ b)    = rise-burst τ (ix τ ∷ j′) 0 b (ix τ ∷ j′) (<ᵖ-asym (ix τ ∷ j′) ((ix τ ∷ j′) ++ [ ix 0 ]) (<ᵖ-below (ix τ ∷ j′) []))
rise-start τ j′ (M.at (suc n) _ b) = rise-burst τ _ 0 b _ (rise-tick τ n (sub ((ix τ ∷ j′) ++ [ last ]) ∷ ix 0 ∷ []) j′)
rise-start τ j′ M.done             = <ᵖ-asym (ix τ ∷ j′) ((ix τ ∷ j′) ++ [ last ]) (<ᵖ-below (ix τ ∷ j′) [])
rise-start τ j′ M.quiet            = tt

-- A SUBSCRIPTION SHOWS NOTHING BEFORE WHERE IT SUBSCRIBES, where a tick
-- heads it.
rise-sub : ∀ {Γ A} (o : Obs Timeline Γ A) j (ρ : NEnv Γ) → Headed j → Atop j (U.meaning (U.subscribe o j) ρ)
rise-sub (cold c) (ix τ ∷ j′) ρ hj =
  subst (Atop (ix τ ∷ j′)) (sym (U.start-meaning (ix τ ∷ j′) (lower c) ρ)) (rise-start τ j′ (lower c))
rise-sub (cold c) []          ρ ()
rise-sub (cold c) (sub _ ∷ _) ρ ()
rise-sub (cold c) (last ∷ _)  ρ ()
rise-sub empty             j ρ hj = <ᵖ-asym j (j ++ [ last ]) (<ᵖ-below j [])
rise-sub (of [])           j ρ hj = <ᵖ-asym j (j ++ [ last ]) (<ᵖ-below j [])
rise-sub (of (_ ∷ _))      j ρ hj = <ᵖ-asym j (j ++ [ ix 0 ]) (<ᵖ-below j [])
rise-sub (map f s)         j ρ hj = atop-map f j _ (rise-sub s j ρ hj)
rise-sub (scan f z s)      j ρ hj = atop-scan f z j _ (rise-sub s j ρ hj)
rise-sub (takeWhile i q s) j ρ hj = atop-take i q j _ (rise-sub s j ρ hj)
rise-sub (flatMap op f s)  j ρ hj =
  atop-go (flatOp op) (just (M.mapᴱ F S)) [] [] j []ᴬ (atop-map F j S (rise-sub s j ρ hj))
  where S = U.meaning (U.subscribe s j) ρ
        F = λ a → M.cold λ q → U.meaning (U.subscribe (f a) q) ρ
rise-sub (connect s b)     j ρ hj =
  atop-beside _ _ j
    (atop-weaken (j ++ [ ix 0 ]) j _ (<ᵖ-asym j _ (<ᵖ-below j [])) (rise-sub b (j ++ [ ix 0 ]) (S ∷ᴬ ρ) (headed-snoc j hj)))
    (atop-weaken (j ++ [ ix 1 ]) j _ (<ᵖ-asym j _ (<ᵖ-below j [])) (rise-sub s (j ++ [ ix 1 ]) ρ (headed-snoc j hj)))
  where S = U.meaning (U.subscribe s (j ++ [ ix 1 ])) ρ
rise-sub (connected i)     j ρ hj = atop-rejoin j (lookup ρ i)
rise-sub (defer l)         j ρ hj = <ᵖ-asym j (j ++ [ ix 0 ]) (<ᵖ-below j [])

-- Strictly under a position a tick heads is no timer's bare tick.
tick-beneath : ∀ p R → Headed p → Beneath p R → ∀ m → R ≢ ix (suc m) ∷ []
tick-beneath (ix _ ∷ [])    _ _  (inj₁ (_ , ())) m refl
tick-beneath (ix _ ∷ _ ∷ _) _ _  (inj₁ (_ , ())) m refl
tick-beneath p              _ _  (inj₂ ())       m refl
tick-beneath []             _ () (inj₁ _)        m refl
tick-beneath (sub _ ∷ _)    _ () (inj₁ _)        m refl
tick-beneath (last ∷ _)     _ () (inj₁ _)        m refl

-- The lane `earliest` picks, where it sat, and no lane's first before it.
Picks : ∀ {B} → List (Events B) → Earliest B → Set
Picks ls none              = All Hush ls
Picks ls (found k bs l as) = ls ≡ bs ++ l ∷ as × M.head l ≡ just k × All (Atop k) bs × All (Atop k) as

earliest-picks : ∀ {B} (ls : List (Events B)) → Picks ls (M.earliest ls)
earliest-picks []       = []ᴬ
earliest-picks (l ∷ ls) with M.head l in hl | M.earliest ls | earliest-picks ls
... | nothing | none             | hs                  = hl ∷ᴬ hs
... | nothing | found k bs c as  | (eq , hc , ab , aa) = cong (l ∷_) eq , hc , atop-nothing k l hl ∷ᴬ ab , aa
... | just k  | none             | hs                  = refl , hl , []ᴬ , mapᴬ (λ {x} → atop-nothing k x) hs
... | just k  | found k′ bs c as | (eq , hc , ab , aa) with k <ᵖ k′ in kk
...   | true  = refl , hl , []ᴬ
              , subst (All (Atop k)) (sym eq)
                  (All++⁺ (mapᴬ (λ {x} → atop-weaken k′ k x (<ᵖ-asym k k′ kk)) ab)
                          (atop-just c hc (<ᵖ-asym k k′ kk) ∷ᴬ mapᴬ (λ {x} → atop-weaken k′ k x (<ᵖ-asym k k′ kk)) aa))
...   | false = cong (l ∷_) eq , hc , atop-just l hl kk ∷ᴬ ab , aa

all-pick : ∀ {A : Set} {P : A → Set} xs {y} ys → All P (xs ++ y ∷ ys) → P y × All P (xs ++ ys)
all-pick []       ys (py ∷ᴬ pys) = py , pys
all-pick (x ∷ xs) ys (px ∷ᴬ pxs) = proj₁ (all-pick xs ys pxs) , px ∷ᴬ proj₂ (all-pick xs ys pxs)

disjoint-swap : ∀ a h → Disjoint a h → Disjoint h a
disjoint-swap a h (na , nb) = nb , na

-- Pairwise apart.
Parted : List Pos → Set
Parted []       = ⊤
Parted (r ∷ rs) = All (Disjoint r) rs × Parted rs

parted-pick : ∀ rbs r ras → Parted (rbs ++ r ∷ ras) → All (Disjoint r) (rbs ++ ras) × Parted (rbs ++ ras)
parted-pick []        r ras pt        = pt
parted-pick (b ∷ rbs) r ras (db , pt) =
  disjoint-swap b r (proj₁ (all-pick rbs ras db)) ∷ᴬ proj₁ (parted-pick rbs r ras pt)
  , proj₂ (all-pick rbs ras db) , proj₂ (parted-pick rbs r ras pt)

-- Each later outer event apart from the root, a step past it: no lane
-- the outer admits keys it or is keyed under it.
Aside : ∀ {B} → Maybe (Events (MonotonicList B)) → Pos → Set
Aside nothing  r = ⊤
Aside (just e) r = Every (λ y → Disjoint (y ++ [ ix 1 ]) r) e

aside-none : ∀ {B} rs → All (Aside {B} nothing) rs
aside-none     []       = []ᴬ
aside-none {B} (r ∷ rs) = tt ∷ᴬ aside-none {B} rs

aside-out : ∀ {B} q m (t : Events∞ (MonotonicList B)) {rs} → All (Aside (just (out q m t))) rs
          → All (Disjoint (q ++ [ ix 1 ])) rs × All (Aside (just (force t))) rs
aside-out q m t []ᴬ       = []ᴬ , []ᴬ
aside-out q m t (a ∷ᴬ as) = proj₁ (every a) ∷ᴬ proj₁ (aside-out q m t as) , proj₂ (every a) ∷ᴬ proj₂ (aside-out q m t as)

aside-skip : ∀ {B} q (t : Events∞ (MonotonicList B)) {rs} → All (Aside (just (skip q t))) rs → All (Aside (just (force t))) rs
aside-skip q t []ᴬ       = []ᴬ
aside-skip q t (a ∷ᴬ as) = proj₂ (every a) ∷ᴬ aside-skip q t as

-- An outer's first, if any, strictly before every lane's.
Lead : ∀ {A B} → Events A → List (Events B) → Set
Lead (out h _ _) ls = All (Beyond h) ls
Lead (skip h _)  ls = All (Beyond h) ls
Lead (end h)     ls = All (Beyond h) ls
Lead hush        ls = ⊤

lead-of : ∀ {A B} (e : Events A) {k} {ls : List (Events B)} → M.head e ≡ just k → All (Beyond k) ls → Lead e ls
lead-of (out _ _ _) refl b = b
lead-of (skip _ _)  refl b = b
lead-of (end _)     refl b = b
lead-of hush        ()   b

lead-hush : ∀ {A B} (e : Events A) {ls : List (Events B)} → All Hush ls → Lead e ls
lead-hush (out h _ _) hs = mapᴬ (λ {x} → beyond-nothing h x) hs
lead-hush (skip h _)  hs = mapᴬ (λ {x} → beyond-nothing h x) hs
lead-hush (end h)     hs = mapᴬ (λ {x} → beyond-nothing h x) hs
lead-hush hush        hs = tt

-- A FLATMAP'S MERGE IN ORDER, under `p`.  Each lane carries a ghost
-- root: where the outer value admitting it showed its lane, or, for a
-- queued lane, the root of the lane whose end subscribed it.  Roots are
-- pairwise apart, each lane keyed under its own and alien to whatever
-- is apart from it, and the outer's later events apart from each root a
-- step past them.  So no lane's first, and not the outer's, ties with a
-- lane's end: whatever the merge shows just past that end is no earlier
-- than the rest.
module FlatOrder (p : Pos) where

  -- Where a lane may subscribe: strictly under `p`, a tick heading it.
  Ok : Pos → Set
  Ok j = Beneath p j × Headed j

  -- Alien to whatever is apart from `j`.
  Shy : ∀ {B} → Pos → Events B → Set
  Shy j l = ∀ R → Ok R → Disjoint R j → Alien R l

  -- A lane subscribed at `j`.
  Fit : ∀ {B} → Pos → Events B → Set
  Fit j l = Ordered l × Atop j l × Every (λ h → Owned j h × Headed h) l × Shy j l

  Gen : ∀ {B} → MonotonicList B → Set
  Gen m = ∀ j → Ok j → Fit j (M.observe m j)

  -- Each outer value a lane fit wherever it may subscribe.
  mutual
    Spawns : ∀ {B} → Events (MonotonicList B) → Set
    Spawns (out _ m r) = Gen m × Spawn (force r)
    Spawns (skip _ r)  = Spawn (force r)
    Spawns (end _)     = ⊤
    Spawns hush        = ⊤

    record Spawn {B} (e : Events (MonotonicList B)) : Set where
      coinductive
      field spawned : Spawns e

  open Spawn public

  spawn-map : ∀ {A B} (F : A → MonotonicList B) (e : Events A) → (∀ a → Gen (F a)) → Spawn (M.mapᴱ F e)
  spawned (spawn-map F (out h a r) g) = g a , spawn-map F (force r) g
  spawned (spawn-map F (skip h r)  g) = spawn-map F (force r) g
  spawned (spawn-map F (end h)     g) = tt
  spawned (spawn-map F hush        g) = tt

  -- A lane in flight under its root.
  record Static {B} (r : Pos) (l : Events B) : Set where
    constructor static
    field
      sorted : Ordered l
      keyed  : Every (λ h → Owned r h × Headed h) l
      shy    : Shy r l
      ok     : Ok r

  static-out : ∀ {B r k b} {t : Events∞ B} → Static r (out k b t) → Static r (force t)
  static-out st = static (proj₂ (ordered (Static.sorted st))) (proj₂ (every (Static.keyed st)))
                         (λ R o d → proj₂ (every (Static.shy st R o d))) (Static.ok st)

  static-skip : ∀ {B r k} {t : Events∞ B} → Static r (skip k t) → Static r (force t)
  static-skip st = static (proj₂ (ordered (Static.sorted st))) (proj₂ (every (Static.keyed st)))
                          (λ R o d → proj₂ (every (Static.shy st R o d))) (Static.ok st)

  data Roots {B} : List (Events B) → List Pos → Set where
    []ᴿ  : Roots [] []
    _∷ᴿ_ : ∀ {r l ls rs} → Static r l → Roots ls rs → Roots (l ∷ ls) (r ∷ rs)

  roots-++ : ∀ {B} {xs ys : List (Events B)} {rs ss} → Roots xs rs → Roots ys ss → Roots (xs ++ ys) (rs ++ ss)
  roots-++ []ᴿ       S = S
  roots-++ (st ∷ᴿ R) S = st ∷ᴿ roots-++ R S

  data Split {B} (bs : List (Events B)) (l : Events B) (as : List (Events B)) : List Pos → Set where
    split : ∀ {rbs r ras} → Roots bs rbs → Static r l → Roots as ras → Split bs l as (rbs ++ r ∷ ras)

  roots-split : ∀ {B} (bs : List (Events B)) {l as rs} → Roots (bs ++ l ∷ as) rs → Split bs l as rs
  roots-split []       (st ∷ᴿ R) = split []ᴿ st R
  roots-split (b ∷ bs) (sb ∷ᴿ R) with roots-split bs R
  ... | split rb st ra = split (sb ∷ᴿ rb) st ra

  roots-at : ∀ {B} bs (l : Events B) as {ls rs} → ls ≡ bs ++ l ∷ as → Roots ls rs → Split bs l as rs
  roots-at bs l as refl R = roots-split bs R

  -- The outer: in order and steady, spread, under `p`, its values lanes.
  Held : ∀ {B} → Events (MonotonicList B) → Set
  Held e = (Ordered e × Steady e) × Spread e × Every (λ y → Owned p y × Headed y) e × Spawn e

  Heldᴹ : ∀ {B} → Maybe (Events (MonotonicList B)) → Set
  Heldᴹ nothing  = ⊤
  Heldᴹ (just e) = Held e

  -- Where a lane ending under its root subscribes the next.
  hand-ok : ∀ r c → Ok r → Owned r c → Headed c → Ok (c ++ [ ix 1 ])
  hand-ok r c (br , _) oc hc = owned-snoc p c (ix 1) (owned-trans p r c (beneath-owned p r br) oc) , headed-snoc c hc

  -- A queued lane takes the root of the lane whose end subscribes it.
  handed : ∀ {B} r c (m : MonotonicList B) → Gen m → Static {B} r (end c) → Static r (M.observe m (c ++ [ ix 1 ]))
  handed r c m gm st =
    static (proj₁ fit)
           (every-mono (λ h x → owned-trans r (c ++ [ ix 1 ]) h orj (proj₁ x) , proj₂ x) _ (proj₁ (proj₂ (proj₂ fit))))
           (λ R okR d → proj₂ (proj₂ (proj₂ fit)) R okR
                          (apart-mark R c (ix 1) (ix-mark 1) (every (Static.shy st R okR d) , λ o → proj₂ d (owned-trans r c R oc o))))
           (Static.ok st)
    where
      oc  = proj₁ (every (Static.keyed st))
      orj = owned-trans r c (c ++ [ ix 1 ]) oc (inj₁ (prefix-++ c [ ix 1 ]))
      fit = gm (c ++ [ ix 1 ]) (hand-ok r c (Static.ok st) oc (proj₂ (every (Static.keyed st))))

  fresh-static : ∀ {B} j (m : MonotonicList B) → Gen m → Ok j → Static j (M.observe m j)
  fresh-static j m gm okj = static (proj₁ fit) (proj₁ (proj₂ (proj₂ fit))) (proj₂ (proj₂ (proj₂ fit))) okj
    where fit = gm j okj

  fresh-top : ∀ {B} q (m : MonotonicList B) → Gen m → Ok (q ++ [ ix 1 ]) → Atop (q ++ [ ix 0 ]) (M.observe m (q ++ [ ix 1 ]))
  fresh-top q m gm okq =
    atop-weaken (q ++ [ ix 1 ]) (q ++ [ ix 0 ]) _ (<ᵖ-asym (q ++ [ ix 0 ]) (q ++ [ ix 1 ]) (<ᵖ-part q {ix 0} {ix 1} [] [] refl))
      (proj₁ (proj₂ (gm (q ++ [ ix 1 ]) okq)))

  -- What the merge holds after an outer value's step.
  data Taken {B} (k : Pos) (e : Events (MonotonicList B)) : List (Events B) × List (MonotonicList B) → Set where
    taken : ∀ {ls qs rs} → Roots ls rs → Parted rs → All (Aside (just e)) rs → All (Atop k) ls → All Gen qs → Taken k e (ls , qs)

  admit-new : ∀ {B} q (m : MonotonicList B) t ls qs {rs} → Roots ls rs → Parted rs → All (Aside (just (out q m t))) rs → All Gen qs
            → Gen m → Ok (q ++ [ ix 1 ]) → Aside (just (force t)) (q ++ [ ix 1 ]) → All (Beyond q) ls
            → Taken (q ++ [ ix 0 ]) (force t) (M.observe m (q ++ [ ix 1 ]) ∷ ls , qs)
  admit-new q m t ls qs R pt asd gq gm okq sp bl =
    taken (fresh-static (q ++ [ ix 1 ]) m gm okq ∷ᴿ R) (proj₁ (aside-out q m t asd) , pt) (sp ∷ᴬ proj₂ (aside-out q m t asd))
          (fresh-top q m gm okq ∷ᴬ mapᴬ (λ {x} → beyond-step q x) bl) gq

  admit-keep : ∀ {B} q (m : MonotonicList B) t ls qs {rs} → Roots ls rs → Parted rs → All (Aside (just (out q m t))) rs
             → All (Beyond q) ls → All Gen qs → Taken (q ++ [ ix 0 ]) (force t) (ls , qs)
  admit-keep q m t ls qs R pt asd bl gq = taken R pt (proj₂ (aside-out q m t asd)) (mapᴬ (λ {x} → beyond-step q x) bl) gq

  admit-ok : ∀ {B} op q (m : MonotonicList B) t ls qs {rs} → Roots ls rs → Parted rs → All (Aside (just (out q m t))) rs → All Gen qs
           → Gen m → Ok (q ++ [ ix 1 ]) → Aside (just (force t)) (q ++ [ ix 1 ]) → All (Beyond q) ls
           → Taken (q ++ [ ix 0 ]) (force t) (M.admit op (q ++ [ ix 1 ]) m ls qs)
  admit-ok (M.mergeᶠ nothing)  q m t ls       qs R pt asd gq gm okq sp bl = admit-new q m t ls qs R pt asd gq gm okq sp bl
  admit-ok (M.mergeᶠ (just n)) q m t ls       qs R pt asd gq gm okq sp bl with length ls <ᵇ n
  ... | true  = admit-new q m t ls qs R pt asd gq gm okq sp bl
  ... | false = admit-keep q m t ls (qs ++ [ m ]) R pt asd bl (All++⁺ gq (gm ∷ᴬ []ᴬ))
  admit-ok M.switchᶠ           q m t ls       qs R pt asd gq gm okq sp bl = admit-new q m t [] qs []ᴿ tt []ᴬ gq gm okq sp []ᴬ
  admit-ok M.exhaustᶠ          q m t []       qs R pt asd gq gm okq sp bl = admit-new q m t [] qs R pt asd gq gm okq sp bl
  admit-ok M.exhaustᶠ          q m t (l ∷ ls) qs R pt asd gq gm okq sp bl = admit-keep q m t (l ∷ ls) qs R pt asd bl gq

  -- The lanes other than one ending at `c` under `r` are all past `c`.
  clear-lanes : ∀ {B} r c {ls : List (Events B)} {rs} → Ok r → Owned r c → Roots ls rs → All (Disjoint r) rs → All (Atop c) ls
              → All (Atop (c ++ [ ix 0 ])) ls
  clear-lanes r c okr oc []ᴿ                     []ᴬ       []ᴬ       = []ᴬ
  clear-lanes r c okr oc (_∷ᴿ_ {l = l} st R) (d ∷ᴬ ds) (a ∷ᴬ as) =
    beyond-step c l (atop-clear r c l oc a (Static.shy st r okr d)) ∷ᴬ clear-lanes r c okr oc R ds as

  -- And so is the outer.
  atop-hand : ∀ {B} r c (o : Maybe (Events (MonotonicList B))) → Owned r c → Atopᴹ c o → Aside o r → Atopᴹ (c ++ [ ix 0 ]) o
  atop-hand r c nothing  oc ao asr = tt
  atop-hand r c (just e) oc ao asr =
    beyond-step c e (atop-clear r c e oc ao (every-mono (λ y d o → proj₂ d (owned-trans r y (y ++ [ ix 1 ]) o (inj₁ (prefix-++ y [ ix 1 ])))) e asr))

  mutual
    ordered-go : ∀ {B} op (o : Maybe (Events (MonotonicList B))) ls qs {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Ordered (M.go op o ls qs)
    ordered-go op o ls qs R pt asd gq h with M.earliest ls | earliest-picks ls
    ... | none            | hs                  = ordered-via op o ls qs R pt asd gq h hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = ordered-race op o k bs l as qs rb st ra pt asd gq h hk ab aa

    ordered-via : ∀ {B} op (o : Maybe (Events (MonotonicList B))) ls qs {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                → Heldᴹ o → All Hush ls → Ordered (M.viaOuter op o ls qs)
    ordered-via op nothing  ls qs R pt asd gq h hs = record { ordered = tt }
    ordered-via op (just e) ls qs R pt asd gq h hs = ordered-outer op e ls qs R pt asd gq h (lead-hush e hs)

    ordered-race : ∀ {B} op (o : Maybe (Events (MonotonicList B))) k bs (l : Events B) as qs {rbs r ras}
                 → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → M.head l ≡ just k → All (Atop k) bs → All (Atop k) as → Ordered (M.race op o k bs l as qs)
    ordered-race op nothing  k bs l as qs rb st ra pt asd gq h hk ab aa = ordered-lane op nothing bs l as qs rb st ra pt asd gq h hk ab aa tt
    ordered-race op (just e) k bs l as qs rb st ra pt asd gq h hk ab aa with M.head e in he
    ... | nothing = ordered-lane op (just e) bs l as qs rb st ra pt asd gq h hk ab aa (atop-nothing k e he)
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = ordered-outer op e (bs ++ l ∷ as) qs (roots-++ rb (st ∷ᴿ ra)) pt asd gq h
                      (lead-of e he (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k x kk) ab)
                                            (beyond-just k′ l hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k x kk) aa)))
    ...   | false = ordered-lane op (just e) bs l as qs rb st ra pt asd gq h hk ab aa (atop-just e he kk)

    ordered-outer : ∀ {B} op (e : Events (MonotonicList B)) ls qs {rs} → Roots ls rs → Parted rs → All (Aside (just e)) rs → All Gen qs
                  → Held e → Lead e ls → Ordered (M.outer op e ls qs)
    ordered (ordered-outer op (out q m t) ls qs R pt asd gq ((od , sd) , sp , ev , sw) ld)
      with M.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-ok op q m t ls qs R pt asd gq (proj₁ (spawned sw))
             (owned-snoc p q (ix 1) (proj₁ (proj₁ (every ev))) , headed-snoc q (proj₂ (proj₁ (every ev)))) (proj₁ (spread sp)) ld
    ... | ls′ , qs′ | taken R′ pt′ asd′ at′ gq′ =
      atop-go op (just (force t)) ls′ qs′ (q ++ [ ix 0 ]) at′ (beyond-step q (force t) (past-beyond q (force t) (proj₁ (steady sd))))
      , ordered-go op (just (force t)) ls′ qs′ R′ pt′ asd′ gq′
          ((proj₂ (ordered od) , proj₂ (steady sd)) , proj₂ (spread sp) , proj₂ (every ev) , proj₂ (spawned sw))
    ordered (ordered-outer op (skip q t) ls qs R pt asd gq ((od , sd) , sp , ev , sw) ld) =
      atop-go op (just (force t)) ls qs q (mapᴬ (λ {x} → beyond-atop q x) ld) (proj₁ (ordered od))
      , ordered-go op (just (force t)) ls qs R pt (aside-skip q t asd) gq
          ((proj₂ (ordered od) , proj₂ (steady sd)) , spread sp , proj₂ (every ev) , spawned sw)
    ordered (ordered-outer op (end c) [] [] R pt asd gq h ld) = tt
    ordered (ordered-outer {B} op (end c) [] (m ∷ qs) R pt asd gq h ld) =
      atop-go op nothing [] (m ∷ qs) c []ᴬ tt , ordered-go op nothing [] (m ∷ qs) R pt (aside-none {B} _) gq tt
    ordered (ordered-outer {B} op (end c) (l ∷ ls) qs R pt asd gq h ld) =
      atop-go op nothing (l ∷ ls) qs c (mapᴬ (λ {x} → beyond-atop c x) ld) tt
      , ordered-go op nothing (l ∷ ls) qs R pt (aside-none {B} _) gq tt
    ordered (ordered-outer op hush ls qs R pt asd gq h ld) = tt

    ordered-lane : ∀ {B} op (o : Maybe (Events (MonotonicList B))) bs (l : Events B) as qs {rbs r ras}
                 → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → ∀ {k} → M.head l ≡ just k → All (Atop k) bs → All (Atop k) as → Atopᴹ k o → Ordered (M.lane op o bs l as qs)
    ordered (ordered-lane op o bs (out k b t) as qs rb st ra pt asd gq h refl ab aa ao) =
      atop-go op o (bs ++ force t ∷ as) qs k (All++⁺ ab (proj₁ (ordered (Static.sorted st)) ∷ᴬ aa)) ao
      , ordered-go op o (bs ++ force t ∷ as) qs (roots-++ rb (static-out st ∷ᴿ ra)) pt asd gq h
    ordered (ordered-lane op o bs (skip k t) as qs rb st ra pt asd gq h refl ab aa ao) =
      atop-go op o (bs ++ force t ∷ as) qs k (All++⁺ ab (proj₁ (ordered (Static.sorted st)) ∷ᴬ aa)) ao
      , ordered-go op o (bs ++ force t ∷ as) qs (roots-++ rb (static-skip st ∷ᴿ ra)) pt asd gq h
    ordered (ordered-lane op o bs (end c) as (m ∷ qs) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h refl ab aa ao) =
      atop-go op o (M.observe m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (c ++ [ ix 0 ])
        (fresh-top c m gm (hand-ok r c (Static.ok st) oc (proj₂ (every (Static.keyed st))))
         ∷ᴬ clear-lanes r c (Static.ok st) oc (roots-++ rb ra) (proj₁ (parted-pick rbs r ras pt)) (All++⁺ ab aa))
        (atop-hand r c o oc ao (proj₁ (all-pick rbs ras asd)))
      , ordered-go op o (M.observe m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (handed r c m gm st ∷ᴿ roots-++ rb ra)
          (parted-pick rbs r ras pt) (proj₁ (all-pick rbs ras asd) ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
      where oc = proj₁ (every (Static.keyed st))
    ordered (ordered-lane op nothing [] (end c) [] [] rb st ra pt asd gq h refl ab aa ao) = tt
    ordered (ordered-lane op nothing [] (end c) (a ∷ as) [] {rbs} {r} {ras} rb st ra pt asd gq h refl ab aa ao) =
      atop-go op nothing (a ∷ as) [] c aa tt
      , ordered-go op nothing (a ∷ as) [] (roots-++ rb ra) (proj₂ (parted-pick rbs r ras pt)) (proj₂ (all-pick rbs ras asd)) gq h
    ordered (ordered-lane op nothing (b ∷ bs) (end c) as [] {rbs} {r} {ras} rb st ra pt asd gq h refl ab aa ao) =
      atop-go op nothing (b ∷ bs ++ as) [] c (All++⁺ ab aa) tt
      , ordered-go op nothing (b ∷ bs ++ as) [] (roots-++ rb ra) (proj₂ (parted-pick rbs r ras pt)) (proj₂ (all-pick rbs ras asd)) gq h
    ordered (ordered-lane op (just e) bs (end c) as [] {rbs} {r} {ras} rb st ra pt asd gq h refl ab aa ao) =
      atop-go op (just e) (bs ++ as) [] c (All++⁺ ab aa) ao
      , ordered-go op (just e) (bs ++ as) [] (roots-++ rb ra) (proj₂ (parted-pick rbs r ras pt)) (proj₂ (all-pick rbs ras asd)) gq h
    ordered (ordered-lane op o bs hush as qs rb st ra pt asd gq h () ab aa ao)

start-within : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Within (U.startᶜ p m) ρ
start-within p (M.at zero _ _)    ρ = tt
start-within p (M.at (suc _) _ _) ρ = tt
start-within p M.done             ρ = tt
start-within p M.quiet            ρ = tt

postulate
  -- A COLD'S RUN IS IN ORDER where a tick heads it: a burst, or its
  -- frames, from the start.
  --
  -- REFUTED: 6f6818f6 wherever no tick heads the position, a timer's frame at a bare tick sorting before the burst behind it
  ordered-start : ∀ {A} p (m : From A 0) → Headed p → Ordered (M.start p m)

  -- A LIST'S RUN IS IN ORDER: its values at rising indices, then its end.
  ordered-of : ∀ {A} p i (xs : List A) → Ordered (M.ofᴱ p i xs)

  -- A CUT KEEPS THE ORDER: the run up to the first value failing, then
  -- its end.
  ordered-take : ∀ {A} i (p : A → Bool) (e : Events A) → Ordered e → Ordered (M.takeWhileᴱ i p e)

  -- A CONNECT'S SOURCE MERGES INTO ITS BODY IN ORDER: each source step a
  -- skip just past it, ahead of the body's later events.
  ordered-beside : ∀ {A B} (b : Events B) (s : Events A) → Ordered b → Ordered s → Ordered (M.beside b s)

  -- A COLD'S RUN IS SPREAD: no later burst or frame keyed under where a
  -- value's lane would subscribe, a burst's root holding no frame's.
  spread-start : ∀ {A} p (m : From A 0) → Spread (M.start p m)

  -- A LIST'S RUN IS SPREAD: its values at sibling indices.
  spread-of : ∀ {A} p i (xs : List A) → Spread (M.ofᴱ p i xs)

  -- A CUT KEEPS A RUN SPREAD: the failing value and the completion just
  -- inside and past a position later than every value kept.
  spread-take : ∀ {A} i (p : A → Bool) (e : Events A) → Ordered e → Steady e → Spread e → Spread (M.takeWhileᴱ i p e)

  -- A REJOIN KEEPS A SOURCE'S RUN SPREAD, alien to the join: each value
  -- rekeyed under the join, which no position of the source's is keyed
  -- under, its pre-join skips and end beside the join.
  spread-rejoin : ∀ {A} p (e : Events A) → Ordered e → Steady e → Alien p e → Spread (M.rejoin p e)

  -- A FLATMAP SUBSCRIBED IS SPREAD: a lane's value is keyed under the
  -- lane's root, apart from every later lane's and the outer's later
  -- steps, its outer being spread.
  spread-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Spread (U.meaning (U.subscribe (flatMap op f s) p) ρ)

  -- A CONNECT SUBSCRIBED IS SPREAD: its body's values, rekeyed under
  -- joins or its own, apart from its source's later steps shown just
  -- past them.
  spread-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                 → Spread (U.meaning (U.subscribe (connect s b) p) ρ)

  -- A COLD'S RUN IS STEADY where a tick heads it: its frames step at its
  -- ticks.
  --
  -- REFUTED: 6f6818f6 wherever no tick heads the position, a timer's frame at a bare tick sorting before the burst behind it
  steady-start : ∀ {A} p (m : From A 0) → Headed p → Steady (M.start p m)

  -- A LIST'S RUN IS STEADY: each value at the next index.
  steady-of : ∀ {A} p i (xs : List A) → Steady (M.ofᴱ p i xs)

  -- A CUT KEEPS A RUN STEADY: the failing value just inside its own
  -- position, its completion just past that.
  steady-take : ∀ {A} i (p : A → Bool) (e : Events A) → Steady e → Steady (M.takeWhileᴱ i p e)

  -- A FLATMAP SUBSCRIBED WHERE A TICK HEADS IS STEADY, over sources
  -- sorted and alien to it: no lane steps inside its outer's last
  -- position.
  --
  -- REFUTED: 0d0df253 wherever no tick heads the position, a lane's timer frame sorting before the step admitting it
  steady-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Steady (U.meaning (U.subscribe (flatMap op f s) p) ρ)

  -- A COLD'S RUN IS FRESH: each burst under its root, each frame tagged
  -- with the burst before it.
  fresh-start : ∀ {A} p (m : From A 0) → Fresh (M.start p m)

  -- A CUT KEEPS A RUN FRESH: the failing value just inside its own
  -- position, its completion just past that, over a run in order and
  -- steady, which never shows a value where it stepped before.
  fresh-take : ∀ {A} i (q : A → Bool) (e : Events A) → Ordered e → Steady e → Fresh e → Fresh (M.takeWhileᴱ i q e)

  -- A FLATMAP SUBSCRIBED SOMEWHERE IS FRESH, over sources sorted and
  -- alien to it.
  fresh-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → p ≢ [] → Sorted ρ → Alienᴱ p ρ
             → Fresh (U.meaning (U.subscribe (flatMap op f s) p) ρ)


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

-- A DEFER SHOWS A SKIP, THEN ITS PROGRAM SUBSCRIBED JUST PAST IT: the
-- fold's meaning there agrees with the program's at every depth, and
-- nothing the program shows sorts before where it subscribes, nor keys
-- under the skip, its sibling.
module Deferred {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) (hp : Headed p) (cl : Alienᴱ p ρ) where
  P₁ = p ++ [ ix 1 ]
  S  = U.meaning (U.subscribe (Later.force l) P₁) ρ
  X  = M.observe (⟦ Later.force l ⟧ᴰ (U.hots ρ)) P₁

  alike : ∀ k → Agree k S X
  alike k = agree (U.subscribed (Later.force l) (env-refl (U.hots ρ))) P₁

  atop : Atop (p ++ [ ix 0 ]) S
  atop = atop-weaken P₁ (p ++ [ ix 0 ]) S (<ᵖ-asym (p ++ [ ix 0 ]) P₁ (<ᵖ-part p [] [] refl)) (rise-sub (Later.force l) P₁ ρ (headed-snoc p hp))

  alien : Alien (p ++ [ ix 0 ]) S
  alien = alien-sub (Later.force l) p ρ cl

  keyed : Every (Beneath P₁) S
  keyed = Reach.reach (keyedRules P₁) (Later.force l) P₁ ρ (inj₁ (prefix-refl P₁))
            (every-monoᴱ (λ _ _ → tt) ρ (alienᴱ-owned p P₁ (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

-- A DEFER'S RUN IS IN ORDER where a tick heads it, its program's being.
--
-- REFUTED: 6f6818f6 wherever no tick heads the position, a timer's frame at a bare tick sorting before the burst behind it
ordered-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
              → Ordered (U.meaning (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Ordered (U.meaning (U.deferᶜ l p []) ρ)
ordered (ordered-defer l p ρ hp cl o) = atop-agree (alike 1) atop , ordered-≈ S X alike o
  where open Deferred l p ρ hp cl

-- A DEFER'S RUN IS STEADY where a tick heads it, its program's being:
-- the program's first is past the skip, and nothing it shows extends it.
--
-- REFUTED: 6f6818f6 wherever no tick heads the position, a timer's frame at a bare tick sorting before the burst behind it
steady-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
             → Steady (U.meaning (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Steady (U.meaning (U.deferᶜ l p []) ρ)
steady (steady-defer l p ρ hp cl st) =
  clear-agree (alike 1) (beyond-clear (p ++ [ ix 0 ]) S (atop-clear (p ++ [ ix 0 ]) (p ++ [ ix 0 ]) S (inj₁ (prefix-refl _)) atop alien) alien)
  , steady-≈ S X alike st
  where open Deferred l p ρ hp cl

-- A DEFER'S RUN IS FRESH, its program's being: nothing under the skip's
-- step, its sibling's, and the skip under no step of the program's, each
-- keyed under the sibling past it.
fresh-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
            → Fresh (U.meaning (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Fresh (U.meaning (U.deferᶜ l p []) ρ)
every (fresh-defer l p ρ hp cl fr) =
  record { every = past-weigh (p ++ [ ix 0 ]) (p ++ [ ix 0 ]) ≤-refl
                 , every-≈ S X alike (every-mono (λ h nh o → nh (owned-trans (p ++ [ ix 0 ]) _ h (inj₁ (prefix-++ _ [ ix 0 ])) o)) S alien) }
  , every-mono (λ q bf → record { every = shy q (proj₁ bf) , proj₂ bf }) X (every-zip X (every-≈ S X alike keyed) (fresh-≈ S X alike fr))
  where
    open Deferred l p ρ hp cl
    shy : ∀ q → Beneath P₁ q → ¬ Owned (q ++ [ ix 0 ]) (p ++ [ ix 0 ])
    shy q b = past-weigh q (p ++ [ ix 0 ])
      (subst (_≤ weigh q) (sym (weigh-mark p (ix 0) (ix-mark 0)))
        (<⇒≤ (subst (_< weigh q) (weigh-mark p (ix 1) (ix-mark 1)) (beneath-weigh P₁ q b))))

-- A DEFER'S RUN IS SPREAD, its program's being: the skip shows no value.
spread-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
             → Spread (U.meaning (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Spread (U.meaning (U.deferᶜ l p []) ρ)
spread (spread-defer l p ρ hp cl sp) = spread-≈ S X alike sp
  where open Deferred l p ρ hp cl

-- Of every `q` in `s`, every `k` in `b`: so of every `k`, every `q`.
every-swap : ∀ {A B} {R : Pos → Pos → Set} (b : Events B) (s : Events A) → Every (λ q → Every (R q) b) s → Every (λ k → Every (λ q → R q k) s) b
every (every-swap (out k _ r) s h) = every-mono (λ q x → proj₁ (every x)) s h , every-swap (force r) s (every-mono (λ q x → proj₂ (every x)) s h)
every (every-swap (skip k r)  s h) = every-mono (λ q x → proj₁ (every x)) s h , every-swap (force r) s (every-mono (λ q x → proj₂ (every x)) s h)
every (every-swap (end k)     s h) = every-mono (λ q x → every x) s h
every (every-swap hush        s h) = tt

-- A run all at one weight is fresh.
fresh-even : ∀ {A} n (e : Events A) → Every (λ h → weigh h ≡ n) e → Fresh e
fresh-even n e ev = every-mono (λ x wx → every-mono (λ h wh → past-weigh x h (≤-reflexive (trans wh (sym wx)))) e ev) e ev

even-of : ∀ {A} p i (xs : List A) → Every (λ h → weigh h ≡ suc (weigh p)) (M.ofᴱ p i xs)
every (even-of p i [])       = weigh-mark p last last-mark
every (even-of p i (x ∷ xs)) = weigh-mark p (ix i) (ix-mark i) , even-of p (suc i) xs

fresh-map : ∀ {A B} (f : A → B) (e : Events A) → Fresh e → Fresh (M.mapᴱ f e)
fresh-map f e fr = every-map f e (every-mono (λ q → every-map f e) e fr)

fresh-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Fresh e → Fresh (M.scanᴱ f z e)
fresh-scan f z e fr = every-scan f z e (every-mono (λ q → every-scan f z e) e fr)

-- A label past `a` keys nothing a mark past what `a` does not key.
drop-snoc : ∀ a h x y → Mark y → ¬ Owned a h → ¬ Owned (a ++ [ x ]) (h ++ [ y ])
drop-snoc a h x y m na (inj₁ q) with prefix-split (a ++ [ x ]) h y q
... | inj₁ q′ = na (owned-trans a (a ++ [ x ]) h (inj₁ (prefix-++ a [ x ])) (inj₁ q′))
... | inj₂ eq = na (inj₁ (subst (Prefix a) (proj₁ (snoc-inj a h eq)) (prefix-refl a)))
drop-snoc a h x y m na (inj₂ t) = na (inj₂ (owned-tagged a (a ++ [ x ]) h (inj₁ (prefix-++ a [ x ])) (tagged-mark _ h y m t)))

-- Just past what a join shows lies nothing it shows: what it rekeys is
-- tagged with the join, which nothing under the join keys; its skips
-- and end are lighter than anything under it.
under-tag : ∀ p x q → Beneath p x → ¬ Owned p q → ¬ Owned (x ++ [ ix 0 ]) (q ++ [ sub p ])
under-tag p x q b nq (inj₁ pr) with prefix-split (x ++ [ ix 0 ]) q (sub p) pr
... | inj₁ pr′ = nq (owned-trans p (x ++ [ ix 0 ]) q (beneath-owned p _ (beneath-snoc p x (ix 0) b)) (inj₁ pr′))
... | inj₂ eq with () ← proj₂ (snoc-inj x q eq)
under-tag p x q b nq (inj₂ t) with tagged-split (x ++ [ ix 0 ]) q p t
... | inj₁ t′ = nq (owned-trans p (x ++ [ ix 0 ]) q (beneath-owned p _ (beneath-snoc p x (ix 0) b)) (inj₂ t′))
... | inj₂ o  = past-weigh x p (<⇒≤ (beneath-weigh p x b)) o

under-mark : ∀ p x l → Mark l → Beneath p x → ¬ Owned (x ++ [ ix 0 ]) (p ++ [ l ])
under-mark p x l m b = past-weigh x (p ++ [ l ]) (subst (_≤ weigh x) (sym (weigh-mark p l m)) (beneath-weigh p x b))

mutual
  alien-rejoin : ∀ {A} p x (e : Events A) → Beneath p x → Alien p e → Alien (x ++ [ ix 0 ]) (M.rejoin p e)
  every (alien-rejoin p x (out q a k) b al) = every (alien-showing p x q (just a) k (p <ᵖ q) b (proj₁ (every al)) (proj₂ (every al)))
  every (alien-rejoin p x (skip q k)  b al) = every (alien-showing p x q nothing k (p <ᵖ q) b (proj₁ (every al)) (proj₂ (every al)))
  every (alien-rejoin p x (end c)     b al) with p <ᵖ c
  ... | true  = under-tag p x c b (every al)
  ... | false = under-mark p x last last-mark b
  every (alien-rejoin p x hush        b al) = tt

  alien-showing : ∀ {A} p x q (a : Maybe A) (k : Events∞ A) t → Beneath p x → ¬ Owned p q → Alien p (force k)
                → Alien (x ++ [ ix 0 ]) (M.shown p q a k t)
  every (alien-showing p x q (just a) k true  b nq al) = under-tag p x q b nq , alien-rejoin p x (force k) b al
  every (alien-showing p x q nothing  k true  b nq al) = under-tag p x q b nq , alien-rejoin p x (force k) b al
  every (alien-showing p x q (just a) k false b nq al) = under-mark p x (ix 0) (ix-mark 0) b , alien-rejoin p x (force k) b al
  every (alien-showing p x q nothing  k false b nq al) = under-mark p x (ix 0) (ix-mark 0) b , alien-rejoin p x (force k) b al

-- A JOIN OF AN ALIEN RUN IS FRESH: everything it shows is under it.
fresh-rejoin : ∀ {A} p (e : Events A) → Alien p e → Fresh (M.rejoin p e)
fresh-rejoin p e al =
  every-mono (λ x b → alien-rejoin p x e b al) _
    (Reach.every-rejoin (keyedRules p) p e (inj₁ (prefix-refl p)) (every-mono (λ _ _ → tt) e al))

-- A MERGE IS FRESH when both runs are and each of the body's events is
-- apart from the position just past each source event.
fresh-beside : ∀ {A B} (b : Events B) (s : Events A) → Fresh b → Fresh s
             → Every (λ k → Every (λ q → Disjoint (q ++ [ ix 0 ]) k) s) b → Fresh (M.beside b s)
fresh-beside b s fb fs ap =
  every-beside b s
    (every-mono (λ k fk → every-beside b s (proj₁ fk)
                  (every-mono (λ q d → drop-snoc k q (ix 0) (ix 0) (ix-mark 0)
                                         (λ o → proj₂ d (owned-trans k q (q ++ [ ix 0 ]) o (inj₁ (prefix-++ q [ ix 0 ]))))) s (proj₂ fk)))
       b (every-zip b fb ap))
    (every-mono (λ q fq → every-beside b s
                  (every-mono (λ k d o → proj₁ d (owned-trans (q ++ [ ix 0 ]) ((q ++ [ ix 0 ]) ++ [ ix 0 ]) k (inj₁ (prefix-++ _ [ ix 0 ])) o)) b (proj₂ fq))
                  (every-mono (λ q′ → drop-snoc (q ++ [ ix 0 ]) q′ (ix 0) (ix 0) (ix-mark 0)) s (proj₁ fq)))
       s (every-zip s fs (every-swap {R = λ k q → Disjoint (q ++ [ ix 0 ]) k} s b ap)))

-- A SUBSCRIPTION IS FRESH somewhere, over sources sorted and alien to
-- it: nothing it shows lies under, or is tagged under, the position
-- just past one of its events.
alien-steps : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Fresh (U.meaning (U.subscribe o p) ρ)

-- A CONNECT'S BODY STAYS APART FROM ITS SOURCE'S STEPS, over sources
-- sorted and alien to it: nothing the body shows keys, or is keyed
-- under, the position just past any source event, where the step shows.
apart-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) → Finite s → (b : Obs Timeline (A ∷ Γ) B) → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Every (λ q → Every (Disjoint (q ++ [ ix 0 ])) (U.meaning (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ)))
                      (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ)
apart-connect s fs b p ρ hp so cl =
  every-mono per S (every-zip S keyed (every-zip S (alien-sub s p ρ cl) (alien-steps s fs (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so cs)))
  where
    S  = U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ
    cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    keyed : Every (Beneath (p ++ [ ix 1 ])) S
    keyed = Reach.reach (keyedRules (p ++ [ ix 1 ])) s (p ++ [ ix 1 ]) ρ (inj₁ (prefix-refl _)) (every-monoᴱ (λ _ _ → tt) ρ cs)
    per : ∀ q → Beneath (p ++ [ ix 1 ]) q × ¬ Owned (p ++ [ ix 0 ]) q × Alien (q ++ [ ix 0 ]) S
        → Every (Disjoint (q ++ [ ix 0 ])) (U.meaning (U.subscribe b (p ++ [ ix 0 ])) (S ∷ᴬ ρ))
    per q (bq , nq , aq) =
      Reach.reach (apartRules (q ++ [ ix 0 ]) (no-tick q)) b (p ++ [ ix 0 ]) (S ∷ᴬ ρ) (proj₂ dq , proj₁ dq)
        (aq , alienᴱ-owned p (q ++ [ ix 0 ]) (beneath-owned p (q ++ [ ix 0 ]) (owned-snoc p q (ix 0) oq)) ρ cl)
      where
        oq : Owned p q
        oq = owned-trans p (p ++ [ ix 1 ]) q (inj₁ (prefix-++ p [ ix 1 ])) (beneath-owned (p ++ [ ix 1 ]) q bq)
        dq : Disjoint (p ++ [ ix 0 ]) (q ++ [ ix 0 ])
        dq = apart-mark (p ++ [ ix 0 ]) q (ix 0) (ix-mark 0)
               (nq , λ o → sibling p {1} {0} (λ ()) (owned-trans (p ++ [ ix 1 ]) q (p ++ [ ix 0 ]) (beneath-owned (p ++ [ ix 1 ]) q bq) o))

-- A CONNECT'S BODY STAYS CLEAR OF ITS SOURCE'S STEPS: nothing it shows
-- lies above or below the position just past any source event.
unrelated-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) → Finite s → (b : Obs Timeline (A ∷ Γ) B) → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                  → Every (λ k → Every (λ q → Unrelated k (q ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ))
                          (U.meaning (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
unrelated-connect s fs b p ρ hp so cl =
  every-swap _ S (every-mono (λ q → every-mono (λ k d → (λ x → proj₂ d (inj₁ x)) , (λ x → proj₁ d (inj₁ x))) _) S (apart-connect s fs b p ρ hp so cl))
  where S = U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ

-- A FLATMAP SUBSCRIBED MERGES IN ORDER: over sorted sources alien to
-- where it subscribes.  An outer value at `q` shows as a skip just past
-- `q`, its outer steady so nothing ties there; a lane's end at `c` with
-- one queued shows a skip just past `c`, and no other lane, nor the
-- outer, ties at `c`, by `FlatOrder`'s roots.
--
-- REFUTED: 37b70651 of any outer node in order, by a joiner told a value and a skip at one position
-- REFUTED: 0d0df253 wherever no tick heads the position, a lane's timer frame sorting before the step admitting it
ordered-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s → ∀ p (ρ : NEnv Γ)
             → Headed p → Sorted ρ → Alienᴱ p ρ
             → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ)

-- A FINITE PROGRAM SUBSCRIBED IS IN ORDER, where a tick heads, over
-- sorted sources alien to where it subscribes.
ordered-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
             → Ordered (U.meaning (U.subscribe o p) ρ)

-- A FINITE PROGRAM SUBSCRIBED SPREADS ITS VALUES: nothing after a
-- value lies where a lane admitted after it would key, nor is keyed by
-- where the value's own lane subscribes.  The ordering half is Ordered
-- and Steady; the rest is causal, no event tagged with a join made later.
spread-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Spread (U.meaning (U.subscribe o p) ρ)

-- A SUBSCRIPTION OVER STEADY SOURCES IS STEADY: a joiner's skips for
-- what it missed sit just past the join, which nothing it rekeys
-- lies inside, its sources being alien to it.  Where a tick heads it,
-- as one heads every real subscription: elsewhere its frames sit at
-- bare ticks, ahead of its own steps.
--
-- REFUTED: 91953190 at the empty position, a lane's timer frame shown just inside the outer's step at its tick
-- REFUTED: 0d0df253 off the empty position where no tick heads it, that frame sorting before the step
-- REFUTED: 42e70878 over sources stepping and then emitting at one position, a takeWhile showing the value inside the step
steady-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Steady (U.meaning (U.subscribe o p) ρ)
steady-subᶠ (cold c) _ p ρ hp so cl = subst Steady (sym (U.start-meaning p (lower c) ρ)) (steady-start p (lower c) hp)
steady-subᶠ empty _ p ρ hp so cl = record { steady = tt }
steady-subᶠ (of xs) _ p ρ hp so cl = steady-of p 0 xs
steady-subᶠ (map f s) (map-f fs) p ρ hp so cl = steady-map f _ (steady-subᶠ s fs p ρ hp so cl)
steady-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = steady-scan f z _ (steady-subᶠ s fs p ρ hp so cl)
steady-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl = steady-take i q _ (steady-subᶠ s fs p ρ hp so cl)
steady-subᶠ (flatMap op f s) _ p ρ hp so cl = steady-flat op f s p ρ hp so cl
steady-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl =
  steady-beside _ _ (steady-subᶠ b fb (p ++ [ ix 0 ]) (S ∷ᴬ ρ) (headed-snoc p hp)
                                 ((ordered-subᶠ s fs (p ++ [ ix 1 ]) ρ hs so cs , ss) , headed-sub s (p ++ [ ix 1 ]) ρ hs so , so)
                                 (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl))
                    ss (unrelated-connect s fs b p ρ hp so cl)
  where S  = U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ
        hs = headed-snoc p hp
        cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
        ss = steady-subᶠ s fs (p ++ [ ix 1 ]) ρ hs so cs
steady-subᶠ (connected i) _ p ρ hp so cl =
  steady-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
steady-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  steady-defer l p ρ hp cl (steady-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                              (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

ordered-subᶠ (cold c) _ p ρ hp so cl = subst Ordered (sym (U.start-meaning p (lower c) ρ)) (ordered-start p (lower c) hp)
ordered-subᶠ empty _ p ρ hp so cl = record { ordered = tt }
ordered-subᶠ (of xs) _ p ρ hp so cl = ordered-of p 0 xs
ordered-subᶠ (map f s) (map-f fs) p ρ hp so cl = ordered-map f _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = ordered-scan f z _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl = ordered-take i q _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = ordered-flat op f s ff fs p ρ hp so cl
ordered-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl =
  ordered-beside _ _
    (ordered-subᶠ b fb (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ) (headed-snoc p hp)
       ((os , steady-subᶠ s fs (p ++ [ ix 1 ]) ρ hs so cs) , headed-sub s (p ++ [ ix 1 ]) ρ hs so , so)
       (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl))
    os
  where hs = headed-snoc p hp
        cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
        os = ordered-subᶠ s fs (p ++ [ ix 1 ]) ρ hs so cs
ordered-subᶠ (connected i) _ p ρ hp so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl)
  where sl = sorted-lookup ρ so i
ordered-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  ordered-defer l p ρ hp cl (ordered-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                               (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

spread-subᶠ (cold c) _ p ρ hp so cl = subst Spread (sym (U.start-meaning p (lower c) ρ)) (spread-start p (lower c))
spread-subᶠ empty _ p ρ hp so cl = record { spread = tt }
spread-subᶠ (of xs) _ p ρ hp so cl = spread-of p 0 xs
spread-subᶠ (map f s) (map-f fs) p ρ hp so cl = spread-map f _ (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = spread-scan f z _ (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  spread-take i q _ (ordered-subᶠ s fs p ρ hp so cl) (steady-subᶠ s fs p ρ hp so cl) (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (flatMap op f s) _ p ρ hp so cl = spread-flat op f s p ρ hp so cl
spread-subᶠ (connect s b) _ p ρ hp so cl = spread-connect s b p ρ hp so cl
spread-subᶠ (connected i) _ p ρ hp so cl =
  spread-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
spread-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  spread-defer l p ρ hp cl (spread-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                              (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

alien-steps (cold c) _ p ρ hp so cl = subst Fresh (sym (U.start-meaning p (lower c) ρ)) (fresh-start p (lower c))
alien-steps empty _ p ρ hp so cl = fresh-even _ (end (p ++ [ last ])) (record { every = weigh-mark p last last-mark })
alien-steps (of xs) _ p ρ hp so cl = fresh-even _ _ (even-of p 0 xs)
alien-steps (map f s) (map-f fs) p ρ hp so cl = fresh-map f _ (alien-steps s fs p ρ hp so cl)
alien-steps (scan f z s) (scan-f fs) p ρ hp so cl = fresh-scan f z _ (alien-steps s fs p ρ hp so cl)
alien-steps (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  fresh-take i q _ (ordered-subᶠ s fs p ρ hp so cl) (steady-subᶠ s fs p ρ hp so cl) (alien-steps s fs p ρ hp so cl)
alien-steps (flatMap op f s) _ p ρ hp so cl = fresh-flat op f s p ρ (headed-there p hp) so cl
alien-steps (connect s b) (connect-f fs fb) p ρ hp so cl =
  fresh-beside _ S (alien-steps b fb (p ++ [ ix 0 ]) (S ∷ᴬ ρ) (headed-snoc p hp)
                                 ((ordered-subᶠ s fs (p ++ [ ix 1 ]) ρ hs so cs , steady-subᶠ s fs (p ++ [ ix 1 ]) ρ hs so cs) , headed-sub s (p ++ [ ix 1 ]) ρ hs so , so)
                                 (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl))
                   (alien-steps s fs (p ++ [ ix 1 ]) ρ hs so cs)
                   (every-swap {R = λ q k → Disjoint (q ++ [ ix 0 ]) k} _ S (apart-connect s fs b p ρ hp so cl))
  where S  = U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ
        hs = headed-snoc p hp
        cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
alien-steps (connected i) _ p ρ hp so cl = fresh-rejoin p _ (every-lookup (λ h → ¬ Owned p h) ρ cl i)
alien-steps (defer l) (defer-f fl) p ρ hp so cl =
  fresh-defer l p ρ hp cl (alien-steps (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                             (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

ordered-flat op f s ff fs p ρ hp so cl =
  O.ordered-go (flatOp op) (just (M.mapᴱ F S)) [] [] O.[]ᴿ tt []ᴬ []ᴬ
    ( (ordered-map F S (ordered-subᶠ s fs p ρ hp so cl) , steady-map F S (steady-subᶠ s fs p ρ hp so cl))
    , spread-map F S (spread-subᶠ s fs p ρ hp so cl)
    , every-map F S (every-zip S (every-mono (beneath-owned p) S keyed) (headed-sub s p ρ hp so))
    , O.spawn-map F S gen )
  where
    module O = FlatOrder p
    S = U.meaning (U.subscribe s p) ρ
    F = λ a → M.cold λ q → U.meaning (U.subscribe (f a) q) ρ
    keyed : Every (Beneath p) S
    keyed = Reach.reach (keyedRules p) s p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ cl)
    gen : ∀ a → O.Gen (F a)
    gen a j (bj , hj) =
      ordered-subᶠ (f a) (ff a) j ρ hj so cj
      , rise-sub (f a) j ρ hj
      , every-zip _ (every-mono (beneath-owned j) _ (Reach.reach (keyedRules j) (f a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj)))
                    (headed-sub (f a) j ρ hj so)
      , λ R okR d → alien-apart (f a) R j ρ (alienᴱ-owned p R (beneath-owned p R (proj₁ okR)) ρ cl) (proj₁ d) (proj₂ d)
                      (tick-beneath p R hp (proj₁ okR))
      where cj = alienᴱ-owned p j (beneath-owned p j bj) ρ cl

-- A PROGRAM SUBSCRIBED IS IN ORDER AND STEADY: its truncations are, and
-- it agrees with each for as many steps as it is deep.
ordered-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Ordered (U.meaning (U.subscribe o p) ρ)
ordered-sub o p ρ hp so cl =
  ordered-lim (λ n → U.meaning (U.subscribe (trunc n o) p) ρ) _ (λ n → ordered-subᶠ (trunc n o) (finite-trunc n o) p ρ hp so cl)
    (λ n → trunc-agree n o p ρ)

steady-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Steady (U.meaning (U.subscribe o p) ρ)
steady-sub o p ρ hp so cl =
  steady-lim (λ n → U.meaning (U.subscribe (trunc n o) p) ρ) _ (λ n → steady-subᶠ (trunc n o) (finite-trunc n o) p ρ hp so cl)
    (λ n → trunc-agree n o p ρ)

-- A program subscribed where a tick heads, over sorted sources alien to
-- where it subscribes, is placed.
placed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Placed (U.subscribe o p) ρ
placed-sub (cold c) p ρ hp so cl = ordered-sub (cold c) p ρ hp so cl , start-within p (lower c) ρ
placed-sub empty p ρ hp so cl = ordered-sub empty p ρ hp so cl , tt
placed-sub (of xs) p ρ hp so cl = ordered-sub (of xs) p ρ hp so cl , tt
placed-sub (map f s) p ρ hp so cl = ordered-sub (map f s) p ρ hp so cl , placed-sub s p ρ hp so cl
placed-sub (scan f z s) p ρ hp so cl = ordered-sub (scan f z s) p ρ hp so cl , placed-sub s p ρ hp so cl
placed-sub (takeWhile i q s) p ρ hp so cl = ordered-sub (takeWhile i q s) p ρ hp so cl , placed-sub s p ρ hp so cl
placed-sub (flatMap op f s) p ρ hp so cl =
  ordered-sub (flatMap op f s) p ρ hp so cl , placed-sub s p ρ hp so cl , tt
  , λ a x r → placed-sub (f a) (x ++ [ ix 1 ]) ρ (headed-lane x (every-reach _ (x ++ [ ix 0 ]) (headed-sub (flatMap op f s) p ρ hp so) r))
                so (alien-shown op f s p ρ cl x r)
placed-sub (connect s b) p ρ hp so cl = ordered-sub (connect s b) p ρ hp so cl , pb , ps
  where hs = headed-snoc p hp
        cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
        ps = placed-sub s (p ++ [ ix 1 ]) ρ hs so cs
        pb = placed-sub b (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ) (headed-snoc p hp)
               ((proj₁ ps , steady-sub s (p ++ [ ix 1 ]) ρ hs so cs) , headed-sub s (p ++ [ ix 1 ]) ρ hs so , so)
               (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl)
placed-sub (connected i) p ρ hp so cl = ordered-sub (connected i) p ρ hp so cl , tt
placed-sub (defer l) p ρ hp so cl = ordered-sub (defer l) p ρ hp so cl , hp , so , cl

-- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root is
-- placed.
placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
placed-subscribe o = placed-sub o root []ᴬ tt tt tt
