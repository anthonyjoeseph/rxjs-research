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
open import Data.Nat.Properties using (+-identityʳ; +-monoʳ-<; ≤-pred; m≤n⇒m<n∨m≡n; <⇒≢; +-suc; +-monoʳ-≤; <⇒≤; <-≤-trans; ≤-trans; m≤n+m; m≤m+n; <-irrefl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; agree;
  agreeᵀ; Earliest; none; found; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root;
  <ᵖ-asym; <ᵖ-down; <ᵖ-next; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-part; ≮-trans; <ᵖ-below;
  <ᵖ-tick; <ᵖ-ix; <ᵖ-step; Tail; Tail∞; pin; idle; _∪_; tailᴱ; Agreeᵀ; pin⁼; idle⁼)
import denotation.MonotonicList as M
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (env-refl)
open import adequacy.Finite using (Finite; cold-f; empty-f; of-f; map-f; scan-f; takeWhile-f; flatMap-f; connect-f; connected-f; defer-f; trunc; finite-trunc; trunc-agree)

open Events∞
open Tail∞

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

-- Every position a tail would step at satisfies `P`.
mutual
  EveryTs : (Pos → Set) → Tail → Set
  EveryTs P (pin k u) = P k × EveryT P (later u)
  EveryTs P idle      = ⊤

  record EveryT (P : Pos → Set) (t : Tail) : Set where
    coinductive
    field everyᵀ : EveryTs P t

open EveryT public

-- Every position `e` shows, its end's included, and every position
-- what it leaves running at each step would show, satisfies `P`.
mutual
  Everys : ∀ {A} → (Pos → Set) → Events A → Set
  Everys P (out h _ r) = P h × Every∞ P r
  Everys P (skip h r)  = P h × Every∞ P r
  Everys P (end h)     = P h
  Everys P hush        = ⊤

  -- A state: its run, and what it leaves running were it cut now.
  Every∞ : ∀ {A} → (Pos → Set) → Events∞ A → Set
  Every∞ P r = Every P (force r) × EveryT P (cut r)

  record Every {A} (P : Pos → Set) (e : Events A) : Set where
    coinductive
    field every : Everys P e

open Every public

-- Every source's positions satisfying `P`.
Everyᴱ : ∀ {Γ} → (Pos → Set) → NEnv Γ → Set
Everyᴱ P []ᴬ      = ⊤
Everyᴱ P (e ∷ᴬ ρ) = Every P e × Everyᴱ P ρ

everyT-idle : ∀ {P : Pos → Set} → EveryT P idle
everyᵀ everyT-idle = tt

everyT-mono : ∀ {P Q : Pos → Set} → (∀ h → P h → Q h) → (t : Tail) → EveryT P t → EveryT Q t
everyᵀ (everyT-mono f (pin k u) pt) = f k (proj₁ (everyᵀ pt)) , everyT-mono f (later u) (proj₂ (everyᵀ pt))
everyᵀ (everyT-mono f idle      pt) = tt

mutual
  every-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (e : Events A) → Every P e → Every Q e
  every (every-mono f (out h _ r) pe) = f h (proj₁ (every pe)) , every∞-mono f r (proj₂ (every pe))
  every (every-mono f (skip h r)  pe) = f h (proj₁ (every pe)) , every∞-mono f r (proj₂ (every pe))
  every (every-mono f (end h)     pe) = f h (every pe)
  every (every-mono f hush        pe) = tt

  every∞-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (r : Events∞ A) → Every∞ P r → Every∞ Q r
  every∞-mono f r (pr , tr) = every-mono f (force r) pr , everyT-mono f (cut r) tr

-- Two tails side by side step only where either would.
mutual
  everyT-∪ : ∀ {P : Pos → Set} (t u : Tail) → EveryT P t → EveryT P u → EveryT P (t ∪ u)
  everyT-∪ idle      u pt pu = pu
  everyT-∪ (pin k r) u pt pu = everyT-first k r u (M.sooner k u) (proj₁ (everyᵀ pt)) (proj₂ (everyᵀ pt)) pu

  everyT-first : ∀ {P : Pos → Set} k (r : Tail∞) u b → P k → EveryT P (later r) → EveryT P u → EveryT P (M.first k r u b)
  everyᵀ (everyT-first k r u          true  pk pr pu) = pk , everyT-∪ (later r) u pr pu
  everyᵀ (everyT-first k r idle       false pk pr pu) = pk , pr
  everyᵀ (everyT-first k r (pin k′ u) false pk pr pu) =
    proj₁ (everyᵀ pu) , everyT-∪ (pin k r) (later u) (record { everyᵀ = pk , pr }) (proj₂ (everyᵀ pu))

-- A tail run shows only where it steps.
every-tail : ∀ {A} {P : Pos → Set} (t : Tail) → EveryT P t → Every {A} P (tailᴱ t)
every (every-tail (pin k r) pt) = proj₁ (everyᵀ pt) , every-tail (later r) (proj₂ (everyᵀ pt)) , proj₂ (everyᵀ pt)
every (every-tail idle      pt) = tt

-- What a run leaves running once its first is taken.
every-tailOf : ∀ {A} {P : Pos → Set} (e : Events A) → Every P e → EveryT P (M.tailOf e)
every-tailOf (out _ _ r) pe = proj₂ (proj₂ (every pe))
every-tailOf (skip _ r)  pe = proj₂ (proj₂ (every pe))
every-tailOf (end _)     pe = everyT-idle
every-tailOf hush        pe = everyT-idle

-- A source's burst run on steps only where the source does.
mutual
  everyT-burstOn : ∀ {A} {P : Pos → Set} r (s : Events∞ A) → Every∞ P s → EveryT P (M.burstOn r s)
  everyT-burstOn r s (ps , ts) = everyT-runOn r (force s) (cut s) ps ts

  everyT-runOn : ∀ {A} {P : Pos → Set} r (e : Events A) t → Every P e → EveryT P t → EveryT P (M.runOn r e t)
  everyT-runOn r (out k _ s) t pe pt = everyT-pinned r k s t (M.inside r k) (proj₁ (every pe)) (proj₂ (every pe)) pt
  everyT-runOn r (skip k s)  t pe pt = everyT-pinned r k s t (M.inside r k) (proj₁ (every pe)) (proj₂ (every pe)) pt
  everyT-runOn r (end _)     t pe pt = pt
  everyT-runOn r hush        t pe pt = pt

  everyT-pinned : ∀ {A} {P : Pos → Set} r k (s : Events∞ A) t b → P k → Every∞ P s → EveryT P t → EveryT P (M.pinned r k s t b)
  everyᵀ (everyT-pinned r k s t true  pk ps pt) = pk , everyT-burstOn r s ps
  everyᵀ (everyT-pinned r k s t false pk ps pt) = everyᵀ pt

-- A source past its next step: past its end, what it left running.
every-onward : ∀ {A} {P : Pos → Set} (σ : Events∞ A) e → Every P e → EveryT P (cut σ) → Every P (force σ) → Every∞ P (M.onward∞ σ e)
every-onward σ (out _ _ s) pe ts ps = proj₂ (every pe)
every-onward σ (skip _ s)  pe ts ps = proj₂ (every pe)
every-onward σ (end _)     pe ts ps = every-tail (cut σ) ts , ts
every-onward σ hush        pe ts ps = ps , ts

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
  Within (U.flatMapᶜ op g o ls qs pl)  ρ = Placedᴹ o ρ × Placedᴸ ls ρ
    × (∀ a x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.flatMapᶜ op g o ls qs pl) ρ) → Placed (g a (x ++ [ ix 1 ])) ρ)
  Within (U.connectᶜ r b (U.live s))    ρ = Placed b (U.meaning s ρ ∷ᴬ ρ) × Placed s ρ
  Within (U.connectᶜ r b (U.ended c t)) ρ = Placed b (end c ∷ᴬ ρ)
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
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
... | false = clear-pre p (force k) (proj₁ (proj₂ (every al)))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
steady (steady-rejoin p (skip q k) o st al) with p <ᵖ q in pq
... | true  = clear-in p q (force k) pq (proj₁ (ordered o)) (proj₁ (steady st))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
... | false = clear-pre p (force k) (proj₁ (proj₂ (every al)))
            , steady-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
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
every-reach (out _ _ r) h pe (out-there x)  = every-reach (force r) h (proj₁ (proj₂ (every pe))) x
every-reach (skip h r)  _ pe skip-here      = proj₁ (every pe)
every-reach (skip _ r)  h pe (skip-there x) = every-reach (force r) h (proj₁ (proj₂ (every pe))) x

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
Picked : ∀ {B} → (Events∞ B → Set) → Earliest B → Set
Picked P none              = ⊤
Picked P (found k bs l as) = All P bs × P l × All P as

earliest-all : ∀ {B} (P : Events∞ B → Set) (ls : List (Events∞ B)) → All P ls → Picked P (M.earliest ls)
earliest-all P []       []ᴬ        = tt
earliest-all P (l ∷ ls) (pl ∷ᴬ al) with M.head (force l) | M.earliest ls | earliest-all P ls al
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
rest-agree         (out⁼ _ a)  = a
rest-agree         (skip⁼ _ a) = a
rest-agree {k = k} end⁼      = M.agree-refl k hush
rest-agree {k = k} hush⁼     = M.agree-refl k hush

rest-every : ∀ {A} {P : Pos → Set} (x : Events A) → Every P x → Every P (rest x)
rest-every (out _ _ r) px = proj₁ (proj₂ (every px))
rest-every (skip _ r)  px = proj₁ (proj₂ (every px))
rest-every (end _)     px = record { every = tt }
rest-every hush        px = px

-- What follows a tail's first step.
restᵀ : Tail → Tail
restᵀ (pin _ u) = later u
restᵀ idle      = idle

restᵀ-agree : ∀ {k} {x y : Tail} → Agreeᵀ (suc k) x y → Agreeᵀ k (restᵀ x) (restᵀ y)
restᵀ-agree         (pin⁼ a) = a
restᵀ-agree {k = k} idle⁼    = M.agreeᵀ-refl k idle

everyT-restᵀ : ∀ {P : Pos → Set} (x : Tail) → EveryT P x → EveryT P (restᵀ x)
everyT-restᵀ (pin _ u) px = proj₂ (everyᵀ px)
everyT-restᵀ idle      px = px

-- A LIMIT OF TAILS STEPS WHERE ITS APPROXIMANTS DO.
mutual
  everyT-lim : ∀ {P : Pos → Set} (ts : ℕ → Tail) (t : Tail) → (∀ n → EveryT P (ts n)) → (∀ n → Agreeᵀ n (ts n) t) → EveryT P t
  everyᵀ (everyT-lim ts t pt ag) = everyTs-lim ts t pt ag (ts 1) (pt 1) (ag 1)

  everyTs-lim : ∀ {P : Pos → Set} (ts : ℕ → Tail) (t : Tail) → (∀ n → EveryT P (ts n)) → (∀ n → Agreeᵀ n (ts n) t)
              → (x : Tail) → EveryT P x → Agreeᵀ 1 x t → EveryTs P t
  everyTs-lim ts (pin k u) pt ag (pin k _) px (pin⁼ _) =
    proj₁ (everyᵀ px) , everyT-lim (λ n → restᵀ (ts (suc n))) (later u) (λ n → everyT-restᵀ (ts (suc n)) (pt (suc n))) (λ n → restᵀ-agree (ag (suc n)))
  everyTs-lim ts idle      pt ag idle      px idle⁼    = tt

everyT-≈ : ∀ {P : Pos → Set} (t u : Tail) → (∀ k → Agreeᵀ k t u) → EveryT P t → EveryT P u
everyT-≈ t u a pt = everyT-lim (λ _ → t) u (λ _ → pt) a

-- A LIMIT SHOWS WHAT ITS APPROXIMANTS SHOW: what agrees with the `n`th
-- of a sequence for `n` steps, each showing only positions satisfying
-- `P`, does too.
mutual
  every-lim : ∀ {A} {P : Pos → Set} (xs : ℕ → Events A) (y : Events A) → (∀ n → Every P (xs n)) → (∀ n → Agree n (xs n) y)
            → Every P y
  every (every-lim xs y px ag) = everys-lim xs y px ag (xs 1) (px 1) (ag 1)

  everys-lim : ∀ {A} {P : Pos → Set} (xs : ℕ → Events A) (y : Events A) → (∀ n → Every P (xs n)) → (∀ n → Agree n (xs n) y)
             → (x : Events A) → Every P x → Agree 1 x y → Everys P y
  everys-lim xs (out h _ r) px ag (out h _ _) ex (out⁼ _ _) =
    proj₁ (every ex)
    , every-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-every (xs (suc n)) (px (suc n))) (λ n → rest-agree (ag (suc n)))
    , everyT-lim (λ n → M.tailOf (xs (suc n))) (cut r) (λ n → every-tailOf (xs (suc n)) (px (suc n))) (λ n → M.agree-tail (ag (suc n)))
  everys-lim xs (skip h r)  px ag (skip h _)  ex (skip⁼ _ _) =
    proj₁ (every ex)
    , every-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-every (xs (suc n)) (px (suc n))) (λ n → rest-agree (ag (suc n)))
    , everyT-lim (λ n → M.tailOf (xs (suc n))) (cut r) (λ n → every-tailOf (xs (suc n)) (px (suc n))) (λ n → M.agree-tail (ag (suc n)))
  everys-lim xs (end h)     px ag (end h)     ex end⁼      = every ex
  everys-lim xs hush        px ag hush        ex hush⁼     = tt

-- What agrees at every depth shows the same positions.
every-≈ : ∀ {A} {P : Pos → Set} (x y : Events A) → (∀ k → Agree k x y) → Every P x → Every P y
every-≈ x y a px = every-lim (λ _ → x) y (λ _ → px) a

-- What agrees for a step starts alike.
atop-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Atop k x → Atop k y
atop-agree (out⁼ _ _)  a = a
atop-agree (skip⁼ _ _) a = a
atop-agree end⁼      a = a
atop-agree hush⁼     a = a

past-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Past k x → Past k y
past-agree (out⁼ _ _)  a = a
past-agree (skip⁼ _ _) a = a
past-agree end⁼      a = a
past-agree hush⁼     a = a

clear-agree : ∀ {A k} {x y : Events A} → Agree 1 x y → Clear k x → Clear k y
clear-agree (out⁼ _ _)  a = a
clear-agree (skip⁼ _ _) a = a
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
  orders-lim xs (out h _ r) po ag (out h _ _) ox (out⁼ _ a) =
    atop-agree a (proj₁ (ordered ox))
    , ordered-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-ordered (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  orders-lim xs (skip h r)  po ag (skip h _)  ox (skip⁼ _ a) =
    atop-agree a (proj₁ (ordered ox))
    , ordered-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-ordered (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  orders-lim xs (end h)     po ag (end h)     ox end⁼      = tt
  orders-lim xs hush        po ag hush        ox hush⁼     = tt

mutual
  steady-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Steady (xs n)) → (∀ n → Agree n (xs n) y) → Steady y
  steady (steady-lim xs y po ag) = steadies-lim xs y po ag (xs 2) (po 2) (ag 2)

  steadies-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Steady (xs n)) → (∀ n → Agree n (xs n) y)
               → (x : Events A) → Steady x → Agree 2 x y → Steadies y
  steadies-lim xs (out h _ r) po ag (out h _ _) ox (out⁼ _ a) =
    past-agree a (proj₁ (steady ox))
    , steady-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-steady (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  steadies-lim xs (skip h r)  po ag (skip h _)  ox (skip⁼ _ a) =
    clear-agree a (proj₁ (steady ox))
    , steady-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-steady (xs (suc n)) (po (suc n))) (λ n → rest-agree (ag (suc n)))
  steadies-lim xs (end h)     po ag (end h)     ox end⁼      = tt
  steadies-lim xs hush        po ag hush        ox hush⁼     = tt

ordered-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Ordered x → Ordered y
ordered-≈ x y a o = ordered-lim (λ _ → x) y (λ _ → o) a

steady-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Steady x → Steady y
steady-≈ x y a o = steady-lim (λ _ → x) y (λ _ → o) a

every-map : ∀ {A B} {P : Pos → Set} (f : A → B) (e : Events A) → Every P e → Every P (M.mapᴱ f e)
every (every-map f (out k a r) pe) = proj₁ (every pe) , every-map f (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-map f (skip k r)  pe) = proj₁ (every pe) , every-map f (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-map f (end k)     pe) = every pe
every (every-map f hush        pe) = tt

every-scan : ∀ {A B} {P : Pos → Set} (f : B → A → B) z (e : Events A) → Every P e → Every P (M.scanᴱ f z e)
every (every-scan f z (out k a r) pe) = proj₁ (every pe) , every-scan f (f z a) (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-scan f z (skip k r)  pe) = proj₁ (every pe) , every-scan f z (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-scan f z (end k)     pe) = every pe
every (every-scan f z hush        pe) = tt

-- A connect shows its body's positions and each of its source's steps,
-- and its end, just past it; it leaves running its body's tail and its
-- source's, each step where it was.
mutual
  every-beside : ∀ {A B} {P : Pos → Set} r (β : Events∞ B) (σ : Events∞ A) → Every∞ P β
               → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → Every P (M.beside r β σ)
  every (every-beside r β σ pb ps) = every (every-side r β σ (force σ) pb ps (proj₁ ps))

  every-side : ∀ {A B} {P : Pos → Set} r (β : Events∞ B) (σ : Events∞ A) e → Every∞ P β
             → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → Every (λ q → P q × P (q ++ [ ix 0 ])) e → Every P (M.side r β σ e)
  every (every-side r β σ (out q _ _) pb ps pe) = every (every-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) pb ps (proj₂ (proj₁ (every pe))))
  every (every-side r β σ (skip q _)  pb ps pe) = every (every-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) pb ps (proj₂ (proj₁ (every pe))))
  every (every-side r β σ (end c)     pb ps pe) = every (every-ahead r β σ (c ++ [ ix 0 ]) (M.before (c ++ [ ix 0 ]) (force β)) pb ps (proj₂ (every pe)))
  every (every-side r β σ hush        pb ps pe) = every (proj₁ pb)

  every-ahead : ∀ {A B} {P : Pos → Set} r (β : Events∞ B) (σ : Events∞ A) q t → Every∞ P β
              → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → P q → Every P (M.ahead r β σ q t)
  every (every-ahead r β σ q true  pb ps pq) =
    pq , every-beside r β σ′ pb on , everyT-∪ (M.burstOn r σ′) (cut β) (everyT-burstOn r σ′ (every∞-mono (λ _ → proj₁) σ′ on)) (proj₂ pb)
    where σ′ = M.onward∞ σ (force σ)
          on = every-onward σ (force σ) (proj₁ ps) (proj₂ ps) (proj₁ ps)
  every (every-ahead r β σ q false pb ps pq) = every (every-body r σ q (force β) ps pq (proj₁ pb))

  every-body : ∀ {A B} {P : Pos → Set} r (σ : Events∞ A) q (e : Events B)
             → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → P q → Every P e → Every P (M.body r σ q e)
  every (every-body r σ q (out k a β) ps pq pe) =
    proj₁ (every pe) , every-ahead r β σ q (M.before q (force β)) (proj₂ (every pe)) ps pq
    , everyT-∪ (M.burstOn r σ) (cut β) (everyT-burstOn r σ (every∞-mono (λ _ → proj₁) σ ps)) (proj₂ (proj₂ (every pe)))
  every (every-body r σ q (skip k β)  ps pq pe) =
    proj₁ (every pe) , every-ahead r β σ q (M.before q (force β)) (proj₂ (every pe)) ps pq
    , everyT-∪ (M.burstOn r σ) (cut β) (everyT-burstOn r σ (every∞-mono (λ _ → proj₁) σ ps)) (proj₂ (proj₂ (every pe)))
  every (every-body r σ q (end c)     ps pq pe) = every pe
  every (every-body r σ q hush        ps pq pe) = tt

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
    every (every-burst τ r i (M.emit a k) sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) sr , everyT-idle
    every (every-burst τ r i (M.stall k)  sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) sr , everyT-idle
    every (every-burst τ r i (M.close k)  sr) =
      child r (ix i) (ix-mark i) sr , every-frames τ (r ++ [ last ]) (M.From∞.force k) (child r last last-mark sr) , everyT-idle

  every-start : ∀ {A} p (m : From A 0) → S p → Every P (M.start p m)
  every-start p (M.at zero _ b)    sp = every-burst (tick p) p 0 b sp
  every-start p (M.at (suc n) _ b) sp =
    every-burst (tick p) _ 0 b
      (subst (λ x → S (ix x ∷ sub (p ++ [ last ]) ∷ [])) (sym (+-suc (tick p) n)) (frame (tick p + n) _ (child p last last-mark sp)))
  every-start p M.done             sp = record { every = child p last last-mark sp }
  every-start p M.quiet            sp = record { every = tt }

  every-of : ∀ {A} p i (xs : List A) → S p → Every P (M.ofᴱ p i xs)
  every (every-of p i []       sp) = child p last last-mark sp
  every (every-of p i (x ∷ xs) sp) = child p (ix i) (ix-mark i) sp , every-of p (suc i) xs sp , everyT-idle

  -- A cut shows its failing value, if at all, just past where it was,
  -- and ends just past it, leaving running what the source left.
  mutual
    every-take : ∀ {A} i (q : A → Bool) (e : Events A) → Every P e → Every P (M.takeWhileᴱ i q e)
    every (every-take i q (out k a r) pe) = every (every-taking i q k a (q a) r pe)
    every (every-take i q (skip k r)  pe) = proj₁ (every pe) , every-take i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-take i q (end k)     pe) = every pe
    every (every-take i q hush        pe) = tt

    every-taking : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) → Every P (out k a r) → Every P (M.taking i q k a b r)
    every (every-taking i     q k a true  r pe) = proj₁ (every pe) , every-take i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-taking true  q k a false r pe) =
      deeper k (ix 0) (ix-mark 0) (proj₁ (every pe)) , record { every = deeper k last last-mark (proj₁ (every pe)) } , proj₂ (proj₂ (every pe))
    every (every-taking false q k a false r pe) = deeper k last last-mark (proj₁ (every pe))

  -- A join at `p` shows what it missed just past `p`, the rest tagged.
  mutual
    every-rejoin : ∀ {A} p (e : Events A) → S p → Every Src e → Every P (M.rejoin p e)
    every (every-rejoin p (out q a k) sp se) = every (every-shown p q (just a) k (p <ᵖ q) sp (proj₁ (every se)) (proj₁ (proj₂ (every se))))
    every (every-rejoin p (skip q k)  sp se) = every (every-shown p q nothing k (p <ᵖ q) sp (proj₁ (every se)) (proj₁ (proj₂ (every se))))
    every (every-rejoin p (end c)     sp se) with p <ᵖ c
    ... | true  = join c p (every se) sp
    ... | false = child p last last-mark sp
    every (every-rejoin p hush        sp se) = tt

    every-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → S p → Src q → Every Src (force k) → Every P (M.shown p q a k b)
    every (every-shown p q (just a) k true  sp sq sk) = join q p sq sp , every-rejoin p (force k) sp sk , everyT-idle
    every (every-shown p q nothing  k true  sp sq sk) = join q p sq sp , every-rejoin p (force k) sp sk , everyT-idle
    every (every-shown p q (just a) k false sp sq sk) = child p (ix 0) (ix-mark 0) sp , every-rejoin p (force k) sp sk , everyT-idle
    every (every-shown p q nothing  k false sp sq sk) = child p (ix 0) (ix-mark 0) sp , every-rejoin p (force k) sp sk , everyT-idle

  -- A lane held to the rules wherever it may subscribe.
  Lane : ∀ {B} → MonotonicList B → Set
  Lane m = ∀ k → S k → Every∞ P (M.enter m k)

  -- An outer held to the rules, each value a lane.
  mutual
    Outers : ∀ {B} → Events (MonotonicList B) → Set
    Outers (out h m r) = P h × Lane m × Outer∞ r
    Outers (skip h r)  = P h × Outer∞ r
    Outers (end h)     = P h
    Outers hush        = ⊤

    Outer∞ : ∀ {B} → Events∞ (MonotonicList B) → Set
    Outer∞ r = Outer (force r) × EveryT P (cut r)

    record Outer {B} (e : Events (MonotonicList B)) : Set where
      coinductive
      field outerly : Outers e

  open Outer public

  outer-map : ∀ {A B} (F : A → MonotonicList B) (e : Events A) → (∀ a → Lane (F a)) → Every P e → Outer (M.mapᴱ F e)
  outerly (outer-map F (out h a r) lf pe) =
    proj₁ (every pe) , lf a , outer-map F (force r) lf (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
  outerly (outer-map F (skip h r)  lf pe) = proj₁ (every pe) , outer-map F (force r) lf (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
  outerly (outer-map F (end h)     lf pe) = every pe
  outerly (outer-map F hush        lf pe) = tt

  Outerᴹ : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Set
  Outerᴹ nothing  = ⊤
  Outerᴹ (just e) = Outer∞ e

  -- Every lane's tail, and the whole's.
  everyT-cuts : ∀ {B} (ls : List (Events∞ B)) → All (Every∞ P) ls → EveryT P (M.cuts ls)
  everyT-cuts []       []ᴬ        = everyT-idle
  everyT-cuts (l ∷ ls) (pl ∷ᴬ al) = everyT-∪ (cut l) (M.cuts ls) (proj₂ pl) (everyT-cuts ls al)

  everyT-whole : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t → Outerᴹ o → All (Every∞ P) ls → EveryT P t → EveryT P (M.whole o ls t)
  everyT-whole nothing  ls t po pl pt = everyT-∪ idle (M.cuts ls ∪ t) everyT-idle (everyT-∪ (M.cuts ls) t (everyT-cuts ls pl) pt)
  everyT-whole (just e) ls t po pl pt = everyT-∪ (cut e) (M.cuts ls ∪ t) (proj₂ po) (everyT-∪ (M.cuts ls) t (everyT-cuts ls pl) pt)

  -- An admitted lane subscribes held, a queued one stays a lane, and a
  -- dropped one leaves its tail.
  Admitted : ∀ {B} → List (Events∞ B) × List (MonotonicList B) × Tail → Set
  Admitted (ls , qs , d) = All (Every∞ P) ls × All Lane qs × EveryT P d

  admit-all : ∀ {B} op q (m : MonotonicList B) ls qs → S q → Lane m → All (Every∞ P) ls → All Lane qs
            → Admitted (M.admit op q m ls qs)
  admit-all (M.mergeᶠ nothing)  q m ls       qs sq lm pl pq = lm q sq ∷ᴬ pl , pq , everyT-idle
  admit-all (M.mergeᶠ (just n)) q m ls       qs sq lm pl pq with length ls <ᵇ n
  ... | true  = lm q sq ∷ᴬ pl , pq , everyT-idle
  ... | false = pl , All++⁺ pq (lm ∷ᴬ []ᴬ) , everyT-idle
  admit-all M.switchᶠ           q m ls       qs sq lm pl pq = lm q sq ∷ᴬ []ᴬ , pq , everyT-cuts ls pl
  admit-all M.exhaustᶠ          q m []       qs sq lm pl pq = lm q sq ∷ᴬ []ᴬ , pq , everyT-idle
  admit-all M.exhaustᶠ          q m (l ∷ ls) qs sq lm pl pq = pl , pq , everyT-idle

  -- A flatMap's merge shows its outer's skips and ends where they were,
  -- each value just past where it was, its lanes' events where they
  -- were, each lane's end just past it when another is queued, and
  -- what ended parts left running where it steps.
  mutual
    every-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → Outerᴹ o → All (Every∞ P) ls → All Lane qs → EveryT P t
             → Every P (M.go op o ls qs t)
    every (every-go op o ls qs idle      po pl pq pt) = every (every-parts op o ls qs idle po pl pq pt)
    every (every-go op o ls qs (pin k u) po pl pq pt) = every (every-left op o ls qs k u (M.ahead-of k o ls) po pl pq pt)

    every-left : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u b → Outerᴹ o → All (Every∞ P) ls → All Lane qs
               → EveryT P (pin k u) → Every P (M.left op o ls qs k u b)
    every (every-left op o ls qs k u true  po pl pq pt) =
      proj₁ (everyᵀ pt) , every-go op o ls qs (later u) po pl pq (proj₂ (everyᵀ pt)) , everyT-whole o ls (later u) po pl (proj₂ (everyᵀ pt))
    every (every-left op o ls qs k u false po pl pq pt) = every (every-parts op o ls qs (pin k u) po pl pq pt)

    every-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → Outerᴹ o → All (Every∞ P) ls → All Lane qs → EveryT P t
                → Every P (M.parts op o ls qs t)
    every-parts op o ls qs t po pl pq pt with M.earliest ls | earliest-all (Every∞ P) ls pl
    ... | none            | _                = every-via op o ls qs t po pl pq pt
    ... | found k bs l as | (pb , pl₁ , pa)  = every-race op o k bs l as qs t po pb pl₁ pa pq pt

    every-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → Outerᴹ o → All (Every∞ P) ls → All Lane qs → EveryT P t
              → Every P (M.viaOuter op o ls qs t)
    every-via op nothing  ls qs t po pl pq pt = record { every = tt }
    every-via op (just e) ls qs t po pl pq pt = every-outer op e ls qs t (force e) (proj₁ po) (proj₂ po) pl pq pt

    every-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t → Outerᴹ o
               → All (Every∞ P) bs → Every∞ P l → All (Every∞ P) as → All Lane qs → EveryT P t → Every P (M.race op o k bs l as qs t)
    every-race op nothing  k bs l as qs t po pb pl pa pq pt = every-lane op nothing bs l as qs t (force l) po pb (proj₁ pl) (proj₂ pl) pa pq pt
    every-race op (just e) k bs l as qs t po pb pl pa pq pt with M.head (force e)
    ... | nothing = every-lane op (just e) bs l as qs t (force l) po pb (proj₁ pl) (proj₂ pl) pa pq pt
    ... | just k′ with k′ <ᵖ k
    ...   | true  = every-outer op e (bs ++ l ∷ as) qs t (force e) (proj₁ po) (proj₂ po) (All++⁺ pb (pl ∷ᴬ pa)) pq pt
    ...   | false = every-lane op (just e) bs l as qs t (force l) po pb (proj₁ pl) (proj₂ pl) pa pq pt

    every-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) → Outer x → EveryT P (cut e)
                → All (Every∞ P) ls → All Lane qs → EveryT P t → Every P (M.outer op e ls qs t x)
    every (every-outer op e ls qs t (out q m r) po pe pl pq pt)
      with M.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-all op (q ++ [ ix 1 ]) m ls qs
             (held _ (deeper q (ix 1) (ix-mark 1) (proj₁ (outerly po)))) (proj₁ (proj₂ (outerly po))) pl pq
    ... | ls′ , qs′ , d | (pl′ , pq′ , pd) =
      deeper q (ix 0) (ix-mark 0) (proj₁ (outerly po))
      , every-go op (just r) ls′ qs′ (t ∪ d) (proj₂ (proj₂ (outerly po))) pl′ pq′ (everyT-∪ t d pt pd)
      , everyT-whole (just r) ls′ (t ∪ d) (proj₂ (proj₂ (outerly po))) pl′ (everyT-∪ t d pt pd)
    every (every-outer op e ls qs t (skip q r) po pe pl pq pt) =
      proj₁ (outerly po) , every-go op (just r) ls qs t (proj₂ (outerly po)) pl pq pt , everyT-whole (just r) ls t (proj₂ (outerly po)) pl pt
    every (every-outer op e []       []       t (end c) po pe pl pq pt) = outerly po
    every (every-outer op e []       (m ∷ qs) t (end c) po pe pl pq pt) =
      outerly po , every-go op nothing [] (m ∷ qs) (t ∪ cut e) tt pl pq (everyT-∪ t (cut e) pt pe)
      , everyT-whole nothing [] (t ∪ cut e) tt pl (everyT-∪ t (cut e) pt pe)
    every (every-outer op e (l ∷ ls) qs       t (end c) po pe pl pq pt) =
      outerly po , every-go op nothing (l ∷ ls) qs (t ∪ cut e) tt pl pq (everyT-∪ t (cut e) pt pe)
      , everyT-whole nothing (l ∷ ls) (t ∪ cut e) tt pl (everyT-∪ t (cut e) pt pe)
    every (every-outer op e ls       qs       t hush    po pe pl pq pt) = tt

    every-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) → Outerᴹ o
               → All (Every∞ P) bs → Every P x → EveryT P (cut l) → All (Every∞ P) as → All Lane qs → EveryT P t
               → Every P (M.lane op o bs l as qs t x)
    every (every-lane op o bs l as qs t (out k b r) po pb px pl pa pq pt) =
      proj₁ (every px)
      , every-go op o (bs ++ r ∷ as) qs t po (All++⁺ pb (proj₂ (every px) ∷ᴬ pa)) pq pt
      , everyT-whole o (bs ++ r ∷ as) t po (All++⁺ pb (proj₂ (every px) ∷ᴬ pa)) pt
    every (every-lane op o bs l as qs t (skip k r) po pb px pl pa pq pt) =
      proj₁ (every px)
      , every-go op o (bs ++ r ∷ as) qs t po (All++⁺ pb (proj₂ (every px) ∷ᴬ pa)) pq pt
      , everyT-whole o (bs ++ r ∷ as) t po (All++⁺ pb (proj₂ (every px) ∷ᴬ pa)) pt
    every (every-lane op o bs l as (m ∷ qs) t (end c) po pb px pl pa (lm ∷ᴬ pq) pt) =
      deeper c (ix 0) (ix-mark 0) (every px)
      , every-go op o (M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ cut l) po (ln ∷ᴬ All++⁺ pb pa) pq (everyT-∪ t (cut l) pt pl)
      , everyT-whole o (M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) (t ∪ cut l) po (ln ∷ᴬ All++⁺ pb pa) (everyT-∪ t (cut l) pt pl)
      where ln = lm (c ++ [ ix 1 ]) (held _ (deeper c (ix 1) (ix-mark 1) (every px)))
    every (every-lane op nothing  []       l []       [] t (end c) po pb px pl pa pq pt) = every px
    every (every-lane op nothing  []       l (a ∷ as) [] t (end c) po pb px pl pa pq pt) =
      every px , every-go op nothing (a ∷ as) [] (t ∪ cut l) po pa pq (everyT-∪ t (cut l) pt pl)
      , everyT-whole nothing (a ∷ as) (t ∪ cut l) po pa (everyT-∪ t (cut l) pt pl)
    every (every-lane op nothing  (b ∷ bs) l as       [] t (end c) po pb px pl pa pq pt) =
      every px , every-go op nothing (b ∷ bs ++ as) [] (t ∪ cut l) po (All++⁺ pb pa) pq (everyT-∪ t (cut l) pt pl)
      , everyT-whole nothing (b ∷ bs ++ as) (t ∪ cut l) po (All++⁺ pb pa) (everyT-∪ t (cut l) pt pl)
    every (every-lane op (just e) bs       l as       [] t (end c) po pb px pl pa pq pt) =
      every px , every-go op (just e) (bs ++ as) [] (t ∪ cut l) po (All++⁺ pb pa) pq (everyT-∪ t (cut l) pt pl)
      , everyT-whole (just e) (bs ++ as) (t ∪ cut l) po (All++⁺ pb pa) (everyT-∪ t (cut l) pt pl)
    every (every-lane op o bs l as qs t hush po pb px pl pa pq pt) = tt

  -- A SUBSCRIPTION IS HELD TO THE RULES: subscribed where they allow,
  -- over sources showing what they allow, it shows and leaves running
  -- only what they allow.
  reachᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ k (ρ : NEnv Γ) → S k → Everyᴱ Src ρ
         → Every∞ P (U.stateᴺ (U.subscribe o k) ρ)
  reachᶠ (cold c) (cold-f _)          k ρ sk sρ =
    subst (Every P) (sym (U.start-meaning k (lower c) ρ)) (every-start k (lower c) sk)
    , subst (EveryT P) (sym (U.start-cut k (lower c) ρ)) everyT-idle
  reachᶠ empty empty-f             k ρ sk sρ = record { every = child k last last-mark sk } , everyT-idle
  reachᶠ (of xs) (of-f _)           k ρ sk sρ = every-of k 0 xs sk , everyT-idle
  reachᶠ (map f s) (map-f fs)         k ρ sk sρ = every-map f _ (proj₁ ih) , proj₂ ih
    where ih = reachᶠ s fs k ρ sk sρ
  reachᶠ (scan f z s) (scan-f fs)      k ρ sk sρ = every-scan f z _ (proj₁ ih) , proj₂ ih
    where ih = reachᶠ s fs k ρ sk sρ
  reachᶠ (takeWhile i q s) (takeWhile-f fs) k ρ sk sρ = every-take i q _ (proj₁ ih) , proj₂ ih
    where ih = reachᶠ s fs k ρ sk sρ
  reachᶠ (flatMap op f s) (flatMap-f ff fs)  k ρ sk sρ =
    every-go (flatOp op) (just O) [] [] idle po []ᴬ []ᴬ everyT-idle , everyT-whole (just O) [] idle po []ᴬ everyT-idle
    where
      O  = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s k) ρ
      ih = reachᶠ s fs k ρ sk sρ
      po : Outer∞ O
      po = outer-map _ _ (λ a j sj → reachᶠ (f a) (ff a) j ρ sj sρ) (proj₁ ih) , proj₂ ih
  reachᶠ (connect s b) (connect-f fs fb)     k ρ sk sρ =
    every-beside (k ++ [ ix 1 ]) Bᶜ Sᶜ ib (every∞-mono (λ q pq → pq , deeper q (ix 0) (ix-mark 0) pq) Sᶜ is)
    , everyT-∪ (M.burstOn (k ++ [ ix 1 ]) Sᶜ) (cut Bᶜ) (everyT-burstOn (k ++ [ ix 1 ]) Sᶜ is) (proj₂ ib)
    where
      Sᶜ  = U.stateᴺ (U.subscribe s (k ++ [ ix 1 ])) ρ
      Bᶜ  = U.stateᴺ (U.subscribe b (k ++ [ ix 0 ])) (U.meaning (U.subscribe s (k ++ [ ix 1 ])) ρ ∷ᴬ ρ)
      is = reachᶠ s fs (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ
      ib = reachᶠ b fb (k ++ [ ix 0 ]) (U.meaning (U.subscribe s (k ++ [ ix 1 ])) ρ ∷ᴬ ρ) (held _ (child k (ix 0) (ix-mark 0) sk))
             (every-mono source _ (proj₁ is) , sρ)
  reachᶠ (connected i) (connected-f _)     k ρ sk sρ = every-rejoin k (lookup ρ i) sk (every-lookup Src ρ sρ i) , everyT-idle
  reachᶠ (defer l) (defer-f fl)         k ρ sk sρ = record { every =
    child k (ix 0) (ix-mark 0) sk
    , every-≈ _ _ (λ n → agree (U.subscribed (Later.force l) (env-refl (U.hots ρ))) (k ++ [ ix 1 ])) (proj₁ ih)
    , everyT-≈ _ _ (λ n → agreeᵀ (U.subscribed (Later.force l) (env-refl (U.hots ρ))) (k ++ [ ix 1 ])) (proj₂ ih) }
    , everyT-idle
    where ih = reachᶠ (Later.force l) fl (k ++ [ ix 1 ]) ρ (held _ (child k (ix 1) (ix-mark 1) sk)) sρ

  -- A SUBSCRIPTION IS HELD TO THE RULES: its truncations are, and it
  -- agrees with each for as many steps as it is deep.
  reach : ∀ {Γ A} (o : Obs Timeline Γ A) k (ρ : NEnv Γ) → S k → Everyᴱ Src ρ → Every P (U.meaning (U.subscribe o k) ρ)
  reach o k ρ sk sρ =
    every-lim (λ n → U.meaning (U.subscribe (trunc n o) k) ρ) _ (λ n → proj₁ (reachᶠ (trunc n o) (finite-trunc n o) k ρ sk sρ))
      (λ n → trunc-agree n o k ρ)

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

Atopᴹ : ∀ {A} → Pos → Maybe (Events∞ A) → Set
Atopᴹ k nothing  = ⊤
Atopᴹ k (just e) = Atop k (force e)

-- A tail's next pin no earlier than `k`.
AtopT : Pos → Tail → Set
AtopT k (pin h _) = h <ᵖ k ≡ false
AtopT k idle      = ⊤

-- The merge's first is no earlier than `k` when no lane's, not the
-- outer's, and not the pool's is: each step it shows sits just past an
-- event of theirs.
atop-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) k → Atop k x
          → Atop k (M.lane op o bs l as qs t x)
atop-lane op o        bs      l as      qs       t (out _ _ _) k a = a
atop-lane op o        bs      l as      qs       t (skip _ _)  k a = a
atop-lane op o        bs      l as      (m ∷ qs) t (end c) k a = snoc-atop c (ix 0) k a
atop-lane op nothing  []      l []      []       t (end c) k a = a
atop-lane op nothing  []      l (_ ∷ _) []       t (end c) k a = a
atop-lane op nothing  (_ ∷ _) l as      []       t (end c) k a = a
atop-lane op (just _) bs      l as      []       t (end c) k a = a
atop-lane op o        bs      l as      qs       t hush    k a = tt

atop-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) k → Atop k x
           → Atop k (M.outer op e ls qs t x)
atop-outer op e ls qs t (out q m r) k a with M.admit op (q ++ [ ix 1 ]) m ls qs
... | ls′ , qs′ , d = snoc-atop q (ix 0) k a
atop-outer op e ls       qs       t (skip q r) k a = a
atop-outer op e []       []       t (end c)    k a = a
atop-outer op e []       (m ∷ qs) t (end c)    k a = a
atop-outer op e (l ∷ ls) qs       t (end c)    k a = a
atop-outer op e ls       qs       t hush       k a = tt

atop-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k′ bs (l : Events∞ B) as qs t k → Atop k (force l) → Atopᴹ k o
          → Atop k (M.race op o k′ bs l as qs t)
atop-race op nothing  k′ bs l as qs t k al ao = atop-lane op nothing bs l as qs t (force l) k al
atop-race op (just e) k′ bs l as qs t k al ao with M.head (force e)
... | nothing = atop-lane op (just e) bs l as qs t (force l) k al
... | just k″ with k″ <ᵖ k′
...   | true  = atop-outer op e (bs ++ l ∷ as) qs t (force e) k ao
...   | false = atop-lane op (just e) bs l as qs t (force l) k al

atop-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t k → Atopᴹ k o → Atop k (M.viaOuter op o ls qs t)
atop-via op nothing  ls qs t k ao = tt
atop-via op (just e) ls qs t k ao = atop-outer op e ls qs t (force e) k ao

atop-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t k → All (λ l → Atop k (force l)) ls → Atopᴹ k o
           → Atop k (M.parts op o ls qs t)
atop-parts op o ls qs t k al ao with M.earliest ls | earliest-all (λ l → Atop k (force l)) ls al
... | none             | _             = atop-via op o ls qs t k ao
... | found k′ bs l as | (_ , al′ , _) = atop-race op o k′ bs l as qs t k al′ ao

atop-left : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k′ u b k → All (λ l → Atop k (force l)) ls → Atopᴹ k o
          → k′ <ᵖ k ≡ false → Atop k (M.left op o ls qs k′ u b)
atop-left op o ls qs k′ u true  k al ao at = at
atop-left op o ls qs k′ u false k al ao at = atop-parts op o ls qs (pin k′ u) k al ao

atop-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t k → All (λ l → Atop k (force l)) ls → Atopᴹ k o → AtopT k t
        → Atop k (M.go op o ls qs t)
atop-go op o ls qs idle       k al ao at = atop-parts op o ls qs idle k al ao
atop-go op o ls qs (pin k′ u) k al ao at = atop-left op o ls qs k′ u (M.ahead-of k′ o ls) k al ao at

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

atop-body : ∀ {A B} r (σ : Events∞ A) q (e : Events B) k → Atop k e → Atop k (M.body r σ q e)
atop-body r σ q (out _ _ _) k a = a
atop-body r σ q (skip _ _)  k a = a
atop-body r σ q (end _)     k a = a
atop-body r σ q hush        k a = tt

atop-ahead : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) q t k → Atop k (force β) → q <ᵖ k ≡ false → Atop k (M.ahead r β σ q t)
atop-ahead r β σ q true  k ab aq = aq
atop-ahead r β σ q false k ab aq = atop-body r σ q (force β) k ab

atop-side : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) (e : Events A) k → Atop k (force β) → Atop k e → Atop k (M.side r β σ e)
atop-side r β σ (out q _ _) k ab as = atop-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) k ab (snoc-atop q (ix 0) k as)
atop-side r β σ (skip q _)  k ab as = atop-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) k ab (snoc-atop q (ix 0) k as)
atop-side r β σ (end c)     k ab as = atop-ahead r β σ (c ++ [ ix 0 ]) (M.before (c ++ [ ix 0 ]) (force β)) k ab (snoc-atop c (ix 0) k as)
atop-side r β σ hush        k ab as = ab

atop-beside : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) k → Atop k (force β) → Atop k (force σ) → Atop k (M.beside r β σ)
atop-beside r β σ k ab as = atop-side r β σ (force σ) k ab as

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
  atop-go (flatOp op) (just (U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s j) ρ)) [] [] idle j []ᴬ
    (atop-map _ j (U.meaning (U.subscribe s j) ρ) (rise-sub s j ρ hj)) tt
rise-sub (connect s b)     j ρ hj =
  atop-beside (j ++ [ ix 1 ]) (U.stateᴺ (U.subscribe b (j ++ [ ix 0 ])) (S ∷ᴬ ρ)) (U.stateᴺ (U.subscribe s (j ++ [ ix 1 ])) ρ) j
    (atop-weaken (j ++ [ ix 0 ]) j _ (<ᵖ-asym j _ (<ᵖ-below j [])) (rise-sub b (j ++ [ ix 0 ]) (S ∷ᴬ ρ) (headed-snoc j hj)))
    (atop-weaken (j ++ [ ix 1 ]) j _ (<ᵖ-asym j _ (<ᵖ-below j [])) (rise-sub s (j ++ [ ix 1 ]) ρ (headed-snoc j hj)))
  where S = U.meaning (U.subscribe s (j ++ [ ix 1 ])) ρ
rise-sub (connected i)     j ρ hj = atop-rejoin j (lookup ρ i)
rise-sub (defer l)         j ρ hj = <ᵖ-asym j (j ++ [ ix 0 ]) (<ᵖ-below j [])

start-within : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Within (U.startᶜ p m) ρ
start-within p (M.at zero _ _)    ρ = tt
start-within p (M.at (suc _) _ _) ρ = tt
start-within p M.done             ρ = tt
start-within p M.quiet            ρ = tt

-- A RUN RISING: each event strictly before the next and not around
-- it, so both in order and steady.
mutual
  Rises : ∀ {A} → Events A → Set
  Rises (out k _ r) = Past k (force r) × Rising (force r)
  Rises (skip k r)  = Past k (force r) × Rising (force r)
  Rises (end _)     = ⊤
  Rises hush        = ⊤

  record Rising {A} (e : Events A) : Set where
    coinductive
    field rises : Rises e

open Rising public

past-atop : ∀ {A} k (e : Events A) → Past k e → Atop k e
past-atop k (out h _ _) (l , _) = <ᵖ-asym k h l
past-atop k (skip h _)  (l , _) = <ᵖ-asym k h l
past-atop k (end h)     (l , _) = <ᵖ-asym k h l
past-atop k hush        _       = tt

past-clear : ∀ {A} k (e : Events A) → Past k e → Clear k e
past-clear k (out h _ _) p       = p
past-clear k (skip h _)  (_ , n) = n
past-clear k (end h)     (_ , n) = n
past-clear k hush        _       = tt

rising-ordered : ∀ {A} (e : Events A) → Rising e → Ordered e
ordered (rising-ordered (out k _ r) ri) = past-atop k _ (proj₁ (rises ri)) , rising-ordered _ (proj₂ (rises ri))
ordered (rising-ordered (skip k r)  ri) = past-atop k _ (proj₁ (rises ri)) , rising-ordered _ (proj₂ (rises ri))
ordered (rising-ordered (end _)     ri) = tt
ordered (rising-ordered hush        ri) = tt

rising-steady : ∀ {A} (e : Events A) → Rising e → Steady e
steady (rising-steady (out k _ r) ri) = proj₁ (rises ri) , rising-steady _ (proj₂ (rises ri))
steady (rising-steady (skip k r)  ri) = past-clear k _ (proj₁ (rises ri)) , rising-steady _ (proj₂ (rises ri))
steady (rising-steady (end _)     ri) = tt
steady (rising-steady hush        ri) = tt

-- One label on from the same position: strictly past it, not inside it.
next-ix : ∀ r i → (r ++ [ ix i ]) <ᵖ (r ++ [ ix (suc i) ]) ≡ true × ¬ Ext (r ++ [ ix i ]) (r ++ [ ix (suc i) ])
next-ix r i = <ᵖ-part r [] [] (<ᵖ-ix i) , λ x → ext-irrefl r (under-ext r r x)

ix-last : ∀ r i → (r ++ [ ix i ]) <ᵖ (r ++ [ last ]) ≡ true × ¬ Ext (r ++ [ ix i ]) (r ++ [ last ])
ix-last r i = <ᵖ-part r [] [] refl , λ x → ext-irrefl r (under-ext r r x)

ix-< : ∀ {m n} → m < n → (ix m ∷ []) <ᵖ (ix n ∷ []) ≡ true
ix-< {m} {suc n} l with m≤n⇒m<n∨m≡n (≤-pred l)
... | inj₁ l′   = <ᵖ-trans (ix m ∷ []) (ix n ∷ []) (ix (suc n) ∷ []) (ix-< l′) (<ᵖ-ix n)
... | inj₂ refl = <ᵖ-ix n

-- A later tick: strictly past, and not inside.
tick-past : ∀ {m n} p q → m < n → (ix m ∷ p) <ᵖ (ix n ∷ q) ≡ true × ¬ Ext (ix m ∷ p) (ix n ∷ q)
tick-past {m} {n} p q l = <ᵖ-part [] {ix m} {ix n} p q (ix-< l) , apart
  where apart : ¬ Ext (ix m ∷ p) (ix n ∷ q)
        apart x with ext-eq x
        ... | _ , _ , e with ∷-injective e
        ...   | refl , _ = <⇒≢ l refl

-- A burst's first event is at its next index.
burst-past : ∀ {A t} τ r i (b : M.Frame A t) {k} → k <ᵖ (r ++ [ ix i ]) ≡ true × ¬ Ext k (r ++ [ ix i ]) → Past k (M.burst τ r i b)
burst-past τ r i (M.emit _ _) h = h
burst-past τ r i (M.stall _)  h = h
burst-past τ r i (M.close _)  h = h

-- A burst at its frame's tick rises, and so does every frame after it:
-- each frame's tick past the last.
mutual
  rising-burst : ∀ {A t} τ n q i (b : M.Frame A t) → n ≡ τ + t → Rising (M.burst τ (ix n ∷ q) i b)
  rises (rising-burst τ n q i (M.emit a f) e) = burst-past τ _ (suc i) (M.Frame∞.force f) (next-ix (ix n ∷ q) i) , rising-burst τ n q (suc i) _ e
  rises (rising-burst τ n q i (M.stall f)  e) = burst-past τ _ (suc i) (M.Frame∞.force f) (next-ix (ix n ∷ q) i) , rising-burst τ n q (suc i) _ e
  rises (rising-burst τ n q i (M.close f)  e) = frames-past τ q i (M.From∞.force f) e , rising-frames τ _ (M.From∞.force f)

  rising-frames : ∀ {A t} τ e (m : From A t) → Rising (M.frames τ e m)
  rises (rising-frames τ e M.done)         = tt
  rises (rising-frames τ e M.quiet)        = tt
  rises (rising-frames τ e (M.at t′ _ b)) = rises (rising-burst τ (τ + t′) (sub e ∷ []) 0 b refl)

  frames-past : ∀ {A t n} τ q i (m : From A (suc t)) → n ≡ τ + t → Past (ix n ∷ q ++ [ ix i ]) (M.frames τ (ix n ∷ q ++ [ last ]) m)
  frames-past τ q i M.done        e    = ix-last (ix _ ∷ q) i
  frames-past τ q i M.quiet       e    = tt
  frames-past τ q i (M.at t′ l b) refl = burst-past τ _ 0 b (tick-past (q ++ [ ix i ]) _ (+-monoʳ-< τ l))

-- A COLD'S RUN RISES where a tick heads it: its subscribe burst at the
-- tick's own label, every later frame at a later tick.
--
-- REFUTED: 6f6818f6 wherever no tick heads the position, a timer's frame at a bare tick sorting before the burst behind it
rising-start : ∀ {A} p (m : From A 0) → Headed p → Rising (M.start p m)
rising-start (ix τ ∷ q)  (M.at zero _ b)    hp = rising-burst τ τ q 0 b (sym (+-identityʳ τ))
rising-start []          (M.at zero _ b)    ()
rising-start (sub _ ∷ _) (M.at zero _ b)    ()
rising-start (last ∷ _)  (M.at zero _ b)    ()
rising-start p           (M.at (suc t) l b) hp = rising-frames (tick p) (p ++ [ last ]) (M.at (suc t) l b)
rising-start p           M.done             hp = rising-frames {t = 0} (tick p) (p ++ [ last ]) M.done
rising-start p           M.quiet            hp = rising-frames {t = 0} (tick p) (p ++ [ last ]) M.quiet

ordered-start : ∀ {A} p (m : From A 0) → Headed p → Ordered (M.start p m)
ordered-start p m hp = rising-ordered _ (rising-start p m hp)

steady-start : ∀ {A} p (m : From A 0) → Headed p → Steady (M.start p m)
steady-start p m hp = rising-steady _ (rising-start p m hp)

-- A LIST'S RUN RISES: its values at rising indices, then its end.
rising-of : ∀ {A} p i (xs : List A) → Rising (M.ofᴱ p i xs)
rises (rising-of p i [])           = tt
rises (rising-of p i (x ∷ []))     = ix-last p i , rising-of p (suc i) []
rises (rising-of p i (x ∷ y ∷ xs)) = next-ix p i , rising-of p (suc i) (y ∷ xs)

ordered-of : ∀ {A} p i (xs : List A) → Ordered (M.ofᴱ p i xs)
ordered-of p i xs = rising-ordered _ (rising-of p i xs)

steady-of : ∀ {A} p i (xs : List A) → Steady (M.ofᴱ p i xs)
steady-of p i xs = rising-steady _ (rising-of p i xs)

-- A position one label down from another is inside only what that one
-- is inside or is.
ext-snoc : ∀ k h x → Ext k (h ++ [ x ]) → Ext k h ⊎ k ≡ h
ext-snoc k h x e with ext-eq e
... | _ , _ , eq = go k h eq
  where go : ∀ k h {l ls} → h ++ [ x ] ≡ k ++ l ∷ ls → Ext k h ⊎ k ≡ h
        go []          []      e = inj₂ refl
        go []          (b ∷ h) e = inj₁ (ext b h)
        go (a ∷ [])    []      e with () ← ∷-injectiveʳ e
        go (a ∷ _ ∷ _) []      e with () ← ∷-injectiveʳ e
        go (a ∷ k)     (b ∷ h) e with ∷-injective e
        ... | refl , e′ with go k h e′
        ...   | inj₁ x′   = inj₁ (cons-ext a x′)
        ...   | inj₂ refl = inj₂ refl

past-snoc : ∀ k h x → k <ᵖ h ≡ true × ¬ Ext k h → k <ᵖ (h ++ [ x ]) ≡ true × ¬ Ext k (h ++ [ x ])
past-snoc k h x (l , n) = <ᵖ-trans k h (h ++ [ x ]) l (<ᵖ-below h []) , away
  where away : ¬ Ext k (h ++ [ x ])
        away e with ext-snoc k h x e
        ... | inj₁ e′   = n e′
        ... | inj₂ refl with () ← trans (sym l) (<ᵖ-irrefl k)

-- A cut shows a run's first event, or that event's own completion just
-- below it: whatever the run's first was past or clear of, the cut's is.
past-take : ∀ {A} i (p : A → Bool) k (e : Events A) → Past k e → Past k (M.takeWhileᴱ i p e)
past-take i p k (out h a r) pk with p a | i
... | true  | _     = pk
... | false | true  = past-snoc k h (ix 0) pk
... | false | false = past-snoc k h last pk
past-take i p k (skip h r)  pk = pk
past-take i p k (end h)     pk = pk
past-take i p k hush        pk = tt

clear-take : ∀ {A} i (p : A → Bool) k (e : Events A) → Clear k e → Clear k (M.takeWhileᴱ i p e)
clear-take i p k (out h a r) ck with p a | i
... | true  | _     = ck
... | false | true  = past-snoc k h (ix 0) ck
... | false | false = proj₂ (past-snoc k h last ck)
clear-take i p k (skip h r)  ck = ck
clear-take i p k (end h)     ck = ck
clear-take i p k hush        ck = tt

-- A CUT KEEPS THE ORDER: the run up to the first value failing, then
-- its end.
mutual
  ordered-take : ∀ {A} i (p : A → Bool) (e : Events A) → Ordered e → Ordered (M.takeWhileᴱ i p e)
  ordered (ordered-take i p (out h a r) o) = ordered (ordered-taking i p h a (p a) r (ordered o))
  ordered (ordered-take i p (skip h r)  o) = atop-take i p h _ (proj₁ (ordered o)) , ordered-take i p _ (proj₂ (ordered o))
  ordered (ordered-take i p (end h)     o) = tt
  ordered (ordered-take i p hush        o) = tt

  ordered-taking : ∀ {A} i (p : A → Bool) h a b (r : Events∞ A) → Atop h (force r) × Ordered (force r) → Ordered (M.taking i p h a b r)
  ordered (ordered-taking i     p h a true  r (at , o)) = atop-take i p h _ at , ordered-take i p _ o
  ordered (ordered-taking true  p h a false r _)        = <ᵖ-asym (h ++ [ ix 0 ]) (h ++ [ last ]) (proj₁ (ix-last h 0)) , record { ordered = tt }
  ordered (ordered-taking false p h a false r _)        = tt

-- A CUT KEEPS A RUN STEADY: the failing value just inside its own
-- position, its completion just past that.
mutual
  steady-take : ∀ {A} i (p : A → Bool) (e : Events A) → Steady e → Steady (M.takeWhileᴱ i p e)
  steady (steady-take i p (out h a r) s) = steady (steady-taking i p h a (p a) r (steady s))
  steady (steady-take i p (skip h r)  s) = clear-take i p h _ (proj₁ (steady s)) , steady-take i p _ (proj₂ (steady s))
  steady (steady-take i p (end h)     s) = tt
  steady (steady-take i p hush        s) = tt

  steady-taking : ∀ {A} i (p : A → Bool) h a b (r : Events∞ A) → Past h (force r) × Steady (force r) → Steady (M.taking i p h a b r)
  steady (steady-taking i     p h a true  r (pk , s)) = past-take i p h _ pk , steady-take i p _ s
  steady (steady-taking true  p h a false r _)        = ix-last h 0 , record { steady = tt }
  steady (steady-taking false p h a false r _)        = tt

postulate
  -- A CONNECT SUBSCRIBED IS IN ORDER: each source step a skip just past
  -- it, ahead of the body's later events, and what the source runs on
  -- with past the body's end left as the tail.
  ordered-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                  → Ordered (U.meaning (U.subscribe (connect s b) p) ρ)

  -- A CONNECT SUBSCRIBED WHERE A TICK HEADS IS STEADY, over sources
  -- sorted and alien to it: nothing the body shows lies above or below
  -- where a source step shows, and the source's run past the body's end
  -- steps where it would have.
  --
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `steady-beside`, the proof over a merge without tails
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `alien-steps`, a subscription keying nothing just past its own events, which `steady-beside` read
  steady-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                 → Steady (U.meaning (U.subscribe (connect s b) p) ρ)


-- A CONNECT'S SOURCE KEYS NOTHING UNDER ITS BODY: the two are siblings.
alien-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
          → Alien (p ++ [ ix 0 ]) (U.meaning (U.subscribe o (p ++ [ ix 1 ])) ρ)
alien-sub o p ρ al =
  alien-apart o (p ++ [ ix 0 ]) (p ++ [ ix 1 ]) ρ (alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ al)
    (sibling p (λ ())) (sibling p (λ ())) (no-tick p)

everyT-zip : ∀ {P Q : Pos → Set} (t : Tail) → EveryT P t → EveryT Q t → EveryT (λ h → P h × Q h) t
everyᵀ (everyT-zip (pin k u) pt qt) = (proj₁ (everyᵀ pt) , proj₁ (everyᵀ qt)) , everyT-zip (later u) (proj₂ (everyᵀ pt)) (proj₂ (everyᵀ qt))
everyᵀ (everyT-zip idle      pt qt) = tt

every-zip : ∀ {A} {P Q : Pos → Set} (e : Events A) → Every P e → Every Q e → Every (λ h → P h × Q h) e
every (every-zip (out h _ r) pe qe) = (proj₁ (every pe) , proj₁ (every qe)) , every-zip (force r) (proj₁ (proj₂ (every pe))) (proj₁ (proj₂ (every qe)))
                                      , everyT-zip (cut r) (proj₂ (proj₂ (every pe))) (proj₂ (proj₂ (every qe)))
every (every-zip (skip h r)  pe qe) = (proj₁ (every pe) , proj₁ (every qe)) , every-zip (force r) (proj₁ (proj₂ (every pe))) (proj₁ (proj₂ (every qe)))
                                      , everyT-zip (cut r) (proj₂ (proj₂ (every pe))) (proj₂ (proj₂ (every qe)))
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

------------------------------------------------------------------------
-- What a cut leaves running, against the run.

-- A tail's steps in order.
mutual
  SortedTs : Tail → Set
  SortedTs (pin k u) = AtopT k (later u) × SortedT (later u)
  SortedTs idle      = ⊤

  record SortedT (t : Tail) : Set where
    coinductive
    field sortedᵀ : SortedTs t

open SortedT public

sortedT-idle : SortedT idle
sortedᵀ sortedT-idle = tt

-- Two tails side by side: first whichever's first is.
atopT-∪ : ∀ h t u → AtopT h t → AtopT h u → AtopT h (t ∪ u)
atopT-∪ h idle      u at au = au
atopT-∪ h (pin k r) u at au = fst (M.sooner k u) u au
  where fst : ∀ b u → AtopT h u → AtopT h (M.first k r u b)
        fst true  u          au = at
        fst false idle       au = at
        fst false (pin k′ u) au = au

sooner-atop : ∀ k u → M.sooner k u ≡ true → AtopT k u
sooner-atop k idle       e = tt
sooner-atop k (pin k′ u) e = <ᵖ-asym k k′ e

mutual
  sortedT-∪ : ∀ t u → SortedT t → SortedT u → SortedT (t ∪ u)
  sortedT-∪ idle      u st su = su
  sortedT-∪ (pin k r) u st su = sortedT-first k r u (M.sooner k u) refl st su

  sortedT-first : ∀ k r u b → M.sooner k u ≡ b → SortedT (pin k r) → SortedT u → SortedT (M.first k r u b)
  sortedᵀ (sortedT-first k r u          true  e st su) =
    atopT-∪ k (later r) u (proj₁ (sortedᵀ st)) (sooner-atop k u e) , sortedT-∪ (later r) u (proj₂ (sortedᵀ st)) su
  sortedᵀ (sortedT-first k r idle       false e st su) = sortedᵀ st
  sortedᵀ (sortedT-first k r (pin k′ u) false e st su) =
    atopT-∪ k′ (pin k r) (later u) e (proj₁ (sortedᵀ su)) , sortedT-∪ (pin k r) (later u) st (proj₂ (sortedᵀ su))

-- A tail's first, from what every step of it satisfies.
atopT-every : ∀ h {P : Pos → Set} t → (∀ k → P k → k <ᵖ h ≡ false) → EveryT P t → AtopT h t
atopT-every h (pin k u) f pt = f k (proj₁ (everyᵀ pt))
atopT-every h idle      f pt = tt

-- What a cut leaves running trails the run's next event: no step before
-- a value, nor before a skip but the one showing that very step just
-- past it; every step past an end, and none keyed where that end would
-- subscribe a lane; nothing left behind silence.
TrailE : ∀ {A} → Events A → Pos → Set
TrailE (out n _ _) k = k <ᵖ n ≡ false
TrailE (skip n _)  k = k <ᵖ n ≡ false ⊎ n ≡ k ++ [ ix 0 ]
TrailE (end n)     k = n <ᵖ k ≡ true × ¬ Owned (n ++ [ ix 1 ]) k
TrailE hush        k = ⊥

mutual
  Trailings : ∀ {A} → Events A → Set
  Trailings (out _ _ r) = Trail (force r) (cut r)
  Trailings (skip _ r)  = Trail (force r) (cut r)
  Trailings (end _)     = ⊤
  Trailings hush        = ⊤

  -- A run `x`, leaving `c` running were it cut now, and every later
  -- state, each cut trailing its run.
  record Trail {A} (x : Events A) (c : Tail) : Set where
    coinductive
    field trail : SortedT c × EveryT (TrailE x) c × Trailings x

open Trail public

Trailing : ∀ {A} → Events∞ A → Set
Trailing r = Trail (force r) (cut r)

trailE-map : ∀ {A B} (f : A → B) (x : Events A) k → TrailE x k → TrailE (M.mapᴱ f x) k
trailE-map f (out _ _ _) k t = t
trailE-map f (skip _ _)  k t = t
trailE-map f (end _)     k t = t
trailE-map f hush        k ()

mutual
  trailings-map : ∀ {A B} (f : A → B) (x : Events A) → Trailings x → Trailings (M.mapᴱ f x)
  trailings-map f (out _ _ r) t = trail-map f (force r) (cut r) t
  trailings-map f (skip _ r)  t = trail-map f (force r) (cut r) t
  trailings-map f (end _)     t = tt
  trailings-map f hush        t = tt

  trail-map : ∀ {A B} (f : A → B) (x : Events A) c → Trail x c → Trail (M.mapᴱ f x) c
  trail (trail-map f x c t) =
    proj₁ (trail t) , everyT-mono (trailE-map f x) c (proj₁ (proj₂ (trail t))) , trailings-map f x (proj₂ (proj₂ (trail t)))

-- After a value at `x`, nothing later, shown or left running, lies
-- where a lane admitted then would key, nor keys where `x`'s does.
mutual
  Spreads : ∀ {A} → Events A → Set
  Spreads (out x _ r) = Every∞ (λ y → Disjoint (y ++ [ ix 1 ]) (x ++ [ ix 1 ])) r × Spread (force r)
  Spreads (skip _ r)  = Spread (force r)
  Spreads (end _)     = ⊤
  Spreads hush        = ⊤

  record Spread {A} (e : Events A) : Set where
    coinductive
    field spread : Spreads e

open Spread public

spread-map : ∀ {A B} (f : A → B) (e : Events A) → Spread e → Spread (M.mapᴱ f e)
spread (spread-map f (out h a r) s) =
  (every-map f (force r) (proj₁ (proj₁ (spread s))) , proj₂ (proj₁ (spread s))) , spread-map f (force r) (proj₂ (spread s))
spread (spread-map f (skip h r)  s) = spread-map f (force r) (spread s)
spread (spread-map f (end h)     s) = tt
spread (spread-map f hush        s) = tt

-- One fact for every index, step by step.
mutual
  everyT-∀ : ∀ {I : Set} {P : I → Pos → Set} (t : Tail) → (∀ i → EveryT (P i) t) → EveryT (λ h → ∀ i → P i h) t
  everyᵀ (everyT-∀ (pin k u) f) = (λ i → proj₁ (everyᵀ (f i))) , everyT-∀ (later u) (λ i → proj₂ (everyᵀ (f i)))
  everyᵀ (everyT-∀ idle      f) = tt

mutual
  every-∀ : ∀ {A} {I : Set} {P : I → Pos → Set} (e : Events A) → (∀ i → Every (P i) e) → Every (λ h → ∀ i → P i h) e
  every (every-∀ (out h _ r) f) = (λ i → proj₁ (every (f i))) , every-∀ (force r) (λ i → proj₁ (proj₂ (every (f i))))
                                  , everyT-∀ (cut r) (λ i → proj₂ (proj₂ (every (f i))))
  every (every-∀ (skip h r)  f) = (λ i → proj₁ (every (f i))) , every-∀ (force r) (λ i → proj₁ (proj₂ (every (f i))))
                                  , everyT-∀ (cut r) (λ i → proj₂ (proj₂ (every (f i))))
  every (every-∀ (end h)     f) = λ i → every (f i)
  every (every-∀ hush        f) = tt

-- Strictly under a position a tick heads is no timer's bare tick.
tick-beneath : ∀ p R → Headed p → Beneath p R → ∀ m → R ≢ ix (suc m) ∷ []
tick-beneath (ix _ ∷ [])    _ _  (inj₁ (_ , ())) m refl
tick-beneath (ix _ ∷ _ ∷ _) _ _  (inj₁ (_ , ())) m refl
tick-beneath p              _ _  (inj₂ ())       m refl
tick-beneath []             _ () (inj₁ _)        m refl
tick-beneath (sub _ ∷ _)    _ () (inj₁ _)        m refl
tick-beneath (last ∷ _)     _ () (inj₁ _)        m refl

-- Reading off a run's first position.
atop-nothing : ∀ {A} k (e : Events A) → M.head e ≡ nothing → Atop k e
atop-nothing k (out _ _ _) ()
atop-nothing k (skip _ _)  ()
atop-nothing k (end _)     ()
atop-nothing k hush        h = tt

atop-just : ∀ {A} (e : Events A) {k k′} → M.head e ≡ just k → k <ᵖ k′ ≡ false → Atop k′ e
atop-just (out _ _ _) refl a = a
atop-just (skip _ _)  refl a = a
atop-just (end _)     refl a = a
atop-just hush        ()   a

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

beyond-nothing : ∀ {A} k (e : Events A) → M.head e ≡ nothing → Beyond k e
beyond-nothing k (out _ _ _) ()
beyond-nothing k (skip _ _)  ()
beyond-nothing k (end _)     ()
beyond-nothing k hush        h = tt

beyond-just : ∀ {A} k′ (e : Events A) {k} → M.head e ≡ just k → k′ <ᵖ k ≡ true → Beyond k′ e
beyond-just k′ (out _ _ _) refl b = b
beyond-just k′ (skip _ _)  refl b = b
beyond-just k′ (end _)     refl b = b
beyond-just k′ hush        ()   b

past-beyond : ∀ {A} k (e : Events A) → Past k e → Beyond k e
past-beyond k (out _ _ _) c = proj₁ c
past-beyond k (skip _ _)  c = proj₁ c
past-beyond k (end _)     c = proj₁ c
past-beyond k hush        c = tt

-- Past `q` and not `q` itself: no earlier than just past it.
step-apart : ∀ q k → k <ᵖ q ≡ false → q ≢ k → k <ᵖ (q ++ [ ix 0 ]) ≡ false
step-apart q k a ne with <ᵖ-split q k a
... | inj₁ qk   = <ᵖ-step q k qk
... | inj₂ refl = ⊥-elim (ne refl)

-- No pool step left ahead of every part is before what the parts show
-- first.
clear-atop : ∀ {B} h k (x : Events B) → Atop h x → M.clear k (M.head x) ≡ false → k <ᵖ h ≡ false
clear-atop h k (out k′ _ _) a c = ≮-trans h k′ k a c
clear-atop h k (skip k′ _)  a c = ≮-trans h k′ k a c
clear-atop h k (end k′)     a c = ≮-trans h k′ k a c
clear-atop h k hush         a ()

clears-atop : ∀ {B} h k (ls : List (Events∞ B)) → All (λ l → Atop h (force l)) ls → M.clears k ls ≡ false → k <ᵖ h ≡ false
clears-atop h k []       _          ()
clears-atop h k (l ∷ ls) (a ∷ᴬ as) c with M.clear k (M.head (force l)) in e
... | true  = clears-atop h k ls as c
... | false = clear-atop h k (force l) a e

-- What the pool holds back, with the parts it is held behind.
Behind : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → Tail → Set
Behind o ls idle      = ⊤
Behind o ls (pin k u) = M.ahead-of k o ls ≡ false

behind-atop : ∀ {B} h (o : Maybe (Events∞ (MonotonicList B))) ls t → Behind o ls t → All (λ l → Atop h (force l)) ls → Atopᴹ h o
            → AtopT h t
behind-atop h o        ls idle      _ _  _  = tt
behind-atop h nothing  ls (pin k u) b al ao = clears-atop h k ls al b
behind-atop h (just e) ls (pin k u) b al ao with M.clear k (M.head (force e)) in c
... | true  = clears-atop h k ls al b
... | false = clear-atop h k (force e) ao c

-- A pool ahead of every part: each part's first is past its step.
ahead-atop : ∀ {B} k (o : Maybe (Events∞ (MonotonicList B))) ls → M.ahead-of k o ls ≡ true
           → All (λ l → Atop k (force l)) ls × Atopᴹ k o
ahead-atop k o ls e = lanes ls (clears-of o e) , outer o e
  where
    one : ∀ {B} (x : Events B) → M.clear k (M.head x) ≡ true → Atop k x
    one (out h _ _) c = <ᵖ-asym k h c
    one (skip h _)  c = <ᵖ-asym k h c
    one (end h)     c = <ᵖ-asym k h c
    one hush        c = tt
    clears-of : ∀ o → M.ahead-of k o ls ≡ true → M.clears k ls ≡ true
    clears-of nothing  e = e
    clears-of (just x) e with M.clear k (M.head (force x))
    ... | true = e
    lanes : ∀ ls → M.clears k ls ≡ true → All (λ l → Atop k (force l)) ls
    lanes []       c = []ᴬ
    lanes (l ∷ ls) c with M.clear k (M.head (force l)) in d
    ... | true  = one (force l) d ∷ᴬ lanes ls c
    outer : ∀ o → M.ahead-of k o ls ≡ true → Atopᴹ k o
    outer nothing  e = tt
    outer (just x) e with M.clear k (M.head (force x)) in d
    ... | true = one (force x) d

-- The lane `earliest` picks, where it sat, and no lane's first before it.
Picks : ∀ {B} → List (Events∞ B) → Earliest B → Set
Picks ls none              = All (λ l → M.head (force l) ≡ nothing) ls
Picks ls (found k bs l as) = ls ≡ bs ++ l ∷ as × M.head (force l) ≡ just k × All (λ x → Atop k (force x)) bs × All (λ x → Atop k (force x)) as

earliest-picks : ∀ {B} (ls : List (Events∞ B)) → Picks ls (M.earliest ls)
earliest-picks []       = []ᴬ
earliest-picks (l ∷ ls) with M.head (force l) in hl | M.earliest ls | earliest-picks ls
... | nothing | none             | hs                  = hl ∷ᴬ hs
... | nothing | found k bs c as  | (eq , hc , ab , aa) = cong (l ∷_) eq , hc , atop-nothing k (force l) hl ∷ᴬ ab , aa
... | just k  | none             | hs                  = refl , hl , []ᴬ , mapᴬ (λ {x} → atop-nothing k (force x)) hs
... | just k  | found k′ bs c as | (eq , hc , ab , aa) with k <ᵖ k′ in kk
...   | true  = refl , hl , []ᴬ
              , subst (All (λ x → Atop k (force x))) (sym eq)
                  (All++⁺ (mapᴬ (λ {x} → atop-weaken k′ k (force x) (<ᵖ-asym k k′ kk)) ab)
                          (atop-just (force c) hc (<ᵖ-asym k k′ kk) ∷ᴬ mapᴬ (λ {x} → atop-weaken k′ k (force x) (<ᵖ-asym k k′ kk)) aa))
...   | false = cong (l ∷_) eq , hc , atop-just (force l) hl kk ∷ᴬ ab , aa

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

all-zip : ∀ {A : Set} {P Q : A → Set} {xs} → All P xs → All Q xs → All (λ x → P x × Q x) xs
all-zip []ᴬ       []ᴬ       = []ᴬ
all-zip (p ∷ᴬ ps) (q ∷ᴬ qs) = (p , q) ∷ᴬ all-zip ps qs

t≢f : true ≡ false → ⊥
t≢f ()

behind-at : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) {ls ls′ : List (Events∞ B)} t → ls ≡ ls′ → Behind o ls t → Behind o ls′ t
behind-at o t refl b = b

-- Past `q` and not `q`: nothing a tail holds is before just past it.
pool-step : ∀ q t → AtopT q t → EveryT (λ k → q ≢ k) t → AtopT (q ++ [ ix 0 ]) t
pool-step q idle      a e = tt
pool-step q (pin k u) a e = step-apart q k a (proj₁ (everyᵀ e))

-- Each lane's tail, together.
cuts-every : ∀ {B} {P : Pos → Set} (ls : List (Events∞ B)) → All (λ l → EveryT P (cut l)) ls → EveryT P (M.cuts ls)
cuts-every []       []ᴬ       = everyT-idle
cuts-every (l ∷ ls) (a ∷ᴬ as) = everyT-∪ (cut l) (M.cuts ls) a (cuts-every ls as)

-- One fact per root, at every step, as every step's fact for each root.
everyT-all : ∀ {Q : Pos → Pos → Set} (rs : List Pos) (t : Tail) → All (λ r → EveryT (Q r) t) rs → EveryT (λ k → All (λ r → Q r k) rs) t
everyᵀ (everyT-all rs (pin k u) a) = mapᴬ (λ e → proj₁ (everyᵀ e)) a , everyT-all rs (later u) (mapᴬ (λ e → proj₂ (everyᵀ e)) a)
everyᵀ (everyT-all rs idle      a) = tt

self-atop : ∀ {A} (x : Events A) {k} → M.head x ≡ just k → Atop k x
self-atop x {k} h = atop-just x h (<ᵖ-irrefl k)

-- A run's first, read off a tail.
Atopᴴ : ∀ {A} → Events A → Tail → Set
Atopᴴ (out h _ _) t = AtopT h t
Atopᴴ (skip h _)  t = AtopT h t
Atopᴴ (end h)     t = AtopT h t
Atopᴴ hush        t = ⊤

atopᴴ : ∀ {A} (x : Events A) {k} t → M.head x ≡ just k → AtopT k t → Atopᴴ x t
atopᴴ (out _ _ _) t refl a = a
atopᴴ (skip _ _)  t refl a = a
atopᴴ (end _)     t refl a = a
atopᴴ hush        t ()   a

atopᴴ-nothing : ∀ {A} (x : Events A) t → M.head x ≡ nothing → Atopᴴ x t
atopᴴ-nothing (out _ _ _) t ()
atopᴴ-nothing (skip _ _)  t ()
atopᴴ-nothing (end _)     t ()
atopᴴ-nothing hush        t h = tt

-- Every lane's first strictly past the outer's.
Lead : ∀ {A B} → Events A → List (Events∞ B) → Set
Lead (out h _ _) ls = All (λ l → Beyond h (force l)) ls
Lead (skip h _)  ls = All (λ l → Beyond h (force l)) ls
Lead (end h)     ls = All (λ l → Beyond h (force l)) ls
Lead hush        ls = ⊤

lead-of : ∀ {A B} (x : Events A) (ls : List (Events∞ B)) {k} → M.head x ≡ just k → All (λ l → Beyond k (force l)) ls → Lead x ls
lead-of (out _ _ _) ls refl b = b
lead-of (skip _ _)  ls refl b = b
lead-of (end _)     ls refl b = b
lead-of hush        ls ()   b

lead-hush : ∀ {A B} (x : Events A) (ls : List (Events∞ B)) → All (λ l → M.head (force l) ≡ nothing) ls → Lead x ls
lead-hush (out h _ _) ls hs = mapᴬ (λ {l} → beyond-nothing h (force l)) hs
lead-hush (skip h _)  ls hs = mapᴬ (λ {l} → beyond-nothing h (force l)) hs
lead-hush (end h)     ls hs = mapᴬ (λ {l} → beyond-nothing h (force l)) hs
lead-hush hush        ls hs = tt

------------------------------------------------------------------------
-- An event's first, by whether it is a value and where.
At : ∀ {A} → (Bool → Pos → Set) → Events A → Set
At P (out h _ _) = P true h
At P (skip h _)  = P false h
At P (end h)     = P false h
At P hush        = ⊤

-- What a lane, the outer and the pool would show first in the merge.
LaneAt : ∀ {A B : Set} → (Bool → Pos → Set) → List A → Events B → Set
LaneAt P qs      (out h _ _) = P true h
LaneAt P qs      (skip h _)  = P false h
LaneAt P []      (end c)     = P false c
LaneAt P (_ ∷ _) (end c)     = P false (c ++ [ ix 0 ])
LaneAt P qs      hush        = ⊤

OuterAt : ∀ {A} → (Bool → Pos → Set) → Events A → Set
OuterAt P (out q _ _) = P false (q ++ [ ix 0 ])
OuterAt P (skip q _)  = P false q
OuterAt P (end c)     = P false c
OuterAt P hush        = ⊤

OuterAtᴹ : ∀ {A} → (Bool → Pos → Set) → Maybe (Events∞ A) → Set
OuterAtᴹ P nothing  = ⊤
OuterAtᴹ P (just e) = OuterAt P (force e)

PoolAt : (Bool → Pos → Set) → Tail → Set
PoolAt P (pin k _) = P false k
PoolAt P idle      = ⊤

first-lane : ∀ {B} P op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) → LaneAt P qs x
           → At P (M.lane op o bs l as qs t x)
first-lane P op o        bs      l as      qs       t (out _ _ _) a = a
first-lane P op o        bs      l as      qs       t (skip _ _)  a = a
first-lane P op o        bs      l as      (m ∷ qs) t (end c)     a = a
first-lane P op nothing  []      l []      []       t (end c)     a = a
first-lane P op nothing  []      l (_ ∷ _) []       t (end c)     a = a
first-lane P op nothing  (_ ∷ _) l as      []       t (end c)     a = a
first-lane P op (just _) bs      l as      []       t (end c)     a = a
first-lane P op o        bs      l as      qs       t hush        a = tt

first-outer : ∀ {B} P op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) → OuterAt P x
            → At P (M.outer op e ls qs t x)
first-outer P op e ls qs t (out q m r) a with M.admit op (q ++ [ ix 1 ]) m ls qs
... | ls′ , qs′ , d = a
first-outer P op e ls       qs       t (skip q r) a = a
first-outer P op e []       []       t (end c)    a = a
first-outer P op e []       (m ∷ qs) t (end c)    a = a
first-outer P op e (l ∷ ls) qs       t (end c)    a = a
first-outer P op e ls       qs       t hush       a = tt

first-race : ∀ {B} P op (o : Maybe (Events∞ (MonotonicList B))) k′ bs (l : Events∞ B) as qs t → LaneAt P qs (force l) → OuterAtᴹ P o
           → At P (M.race op o k′ bs l as qs t)
first-race P op nothing  k′ bs l as qs t al ao = first-lane P op nothing bs l as qs t (force l) al
first-race P op (just e) k′ bs l as qs t al ao with M.head (force e)
... | nothing = first-lane P op (just e) bs l as qs t (force l) al
... | just k″ with k″ <ᵖ k′
...   | true  = first-outer P op e (bs ++ l ∷ as) qs t (force e) ao
...   | false = first-lane P op (just e) bs l as qs t (force l) al

first-via : ∀ {B} P op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → OuterAtᴹ P o → At P (M.viaOuter op o ls qs t)
first-via P op nothing  ls qs t ao = tt
first-via P op (just e) ls qs t ao = first-outer P op e ls qs t (force e) ao

first-parts : ∀ {B} P op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → LaneAt P qs (force l)) ls → OuterAtᴹ P o
            → At P (M.parts op o ls qs t)
first-parts P op o ls qs t al ao with M.earliest ls | earliest-all (λ l → LaneAt P qs (force l)) ls al
... | none             | _             = first-via P op o ls qs t ao
... | found k′ bs l as | (_ , al′ , _) = first-race P op o k′ bs l as qs t al′ ao

first-go : ∀ {B} P op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → LaneAt P qs (force l)) ls → OuterAtᴹ P o → PoolAt P t
         → At P (M.go op o ls qs t)
first-go P op o ls qs idle      al ao at = first-parts P op o ls qs idle al ao
first-go P op o ls qs (pin k u) al ao at with M.ahead-of k o ls
... | true  = at
... | false = first-parts P op o ls qs (pin k u) al ao

-- After an event at `k`, a value or not, the next: no earlier, past it
-- if either is a value, and never inside it.
Strict : Bool → Bool → Pos → Pos → Set
Strict true  _     k h = k <ᵖ h ≡ true
Strict false true  k h = k <ᵖ h ≡ true
Strict false false k h = ⊤

Clean : Bool → Pos → Bool → Pos → Set
Clean v k v′ h = Strict v v′ k h × ¬ Ext k h

Next : Bool → Pos → Bool → Pos → Set
Next v k v′ h = h <ᵖ k ≡ false × Clean v k v′ h

mutual
  Calms : ∀ {A} → Events A → Set
  Calms (out k _ r) = At (Next true k) (force r) × Calm (force r)
  Calms (skip k r)  = At (Next false k) (force r) × Calm (force r)
  Calms (end _)     = ⊤
  Calms hush        = ⊤

  record Calm {A} (e : Events A) : Set where
    coinductive
    field calms : Calms e

open Calm public

next-atop : ∀ {A} v k (e : Events A) → At (Next v k) e → Atop k e
next-atop v k (out h _ _) n = proj₁ n
next-atop v k (skip h _)  n = proj₁ n
next-atop v k (end h)     n = proj₁ n
next-atop v k hush        n = tt

next-past : ∀ {A} k (e : Events A) → At (Next true k) e → Past k e
next-past k (out h _ _) n = proj₂ n
next-past k (skip h _)  n = proj₂ n
next-past k (end h)     n = proj₂ n
next-past k hush        n = tt

next-clear : ∀ {A} k (e : Events A) → At (Next false k) e → Clear k e
next-clear k (out h _ _) n = proj₂ n
next-clear k (skip h _)  n = proj₂ (proj₂ n)
next-clear k (end h)     n = proj₂ (proj₂ n)
next-clear k hush        n = tt

calm-ordered : ∀ {A} (e : Events A) → Calm e → Ordered e
ordered (calm-ordered (out k _ r) c) = next-atop true k _ (proj₁ (calms c)) , calm-ordered _ (proj₂ (calms c))
ordered (calm-ordered (skip k r)  c) = next-atop false k _ (proj₁ (calms c)) , calm-ordered _ (proj₂ (calms c))
ordered (calm-ordered (end _)     c) = tt
ordered (calm-ordered hush        c) = tt

calm-steady : ∀ {A} (e : Events A) → Calm e → Steady e
steady (calm-steady (out k _ r) c) = next-past k _ (proj₁ (calms c)) , calm-steady _ (proj₂ (calms c))
steady (calm-steady (skip k r)  c) = next-clear k _ (proj₁ (calms c)) , calm-steady _ (proj₂ (calms c))
steady (calm-steady (end _)     c) = tt
steady (calm-steady hush        c) = tt

-- What the merge's parts would show next, against an event at `k`.
Obl : ∀ {B} → Bool → Pos → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → List (MonotonicList B) → Tail → Set
Obl v k o ls qs t = All (λ l → LaneAt (Clean v k) qs (force l)) ls × OuterAtᴹ (Clean v k) o × PoolAt (Clean v k) t

atop-laneAt : ∀ {A B : Set} k (qs : List A) (x : Events B) → Atop k x → LaneAt (λ _ h → h <ᵖ k ≡ false) qs x
atop-laneAt k qs      (out _ _ _) a = a
atop-laneAt k qs      (skip _ _)  a = a
atop-laneAt k []      (end c)     a = a
atop-laneAt k (_ ∷ _) (end c)     a = snoc-atop c (ix 0) k a
atop-laneAt k qs      hush        a = tt

laneAt-zip : ∀ {A B : Set} {P Q : Bool → Pos → Set} (qs : List A) (x : Events B) → LaneAt P qs x → LaneAt Q qs x
           → LaneAt (λ v h → P v h × Q v h) qs x
laneAt-zip qs      (out _ _ _) a b = a , b
laneAt-zip qs      (skip _ _)  a b = a , b
laneAt-zip []      (end c)     a b = a , b
laneAt-zip (_ ∷ _) (end c)     a b = a , b
laneAt-zip qs      hush        a b = tt

outerAt-next : ∀ {A} v k (x : Events A) → Atop k x → OuterAt (Clean v k) x → OuterAt (Next v k) x
outerAt-next v k (out q _ _) a n = snoc-atop q (ix 0) k a , n
outerAt-next v k (skip q _)  a n = a , n
outerAt-next v k (end c)     a n = a , n
outerAt-next v k hush        a n = tt

lanes-next : ∀ {A B : Set} v k (qs : List A) (ls : List (Events∞ B)) → All (λ l → Atop k (force l)) ls → All (λ l → LaneAt (Clean v k) qs (force l)) ls
           → All (λ l → LaneAt (Next v k) qs (force l)) ls
lanes-next v k qs []       []ᴬ       []ᴬ       = []ᴬ
lanes-next v k qs (l ∷ ls) (a ∷ᴬ as) (n ∷ᴬ ns) = laneAt-zip qs (force l) (atop-laneAt k qs (force l) a) n ∷ᴬ lanes-next v k qs ls as ns

outerᴹ-next : ∀ {B} v k (o : Maybe (Events∞ (MonotonicList B))) → Atopᴹ k o → OuterAtᴹ (Clean v k) o → OuterAtᴹ (Next v k) o
outerᴹ-next v k nothing  a n = tt
outerᴹ-next v k (just e) a n = outerAt-next v k (force e) a n

pool-next : ∀ v k t → AtopT k t → PoolAt (Clean v k) t → PoolAt (Next v k) t
pool-next v k (pin _ _) a n = a , n
pool-next v k idle      a n = tt

next-go : ∀ {B} v k op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → Atop k (force l)) ls → Atopᴹ k o → AtopT k t
        → Obl v k o ls qs t → At (Next v k) (M.go op o ls qs t)
next-go v k op o ls qs t al ao at (nl , no , np) =
  first-go (Next v k) op o ls qs t (lanes-next v k qs ls al nl) (outerᴹ-next v k o ao no) (pool-next v k t at np)

-- A FLATMAP'S MERGE IN ORDER, under `p`.  Each lane carries a ghost
-- root, where it subscribed; roots are pairwise apart, each lane keyed
-- under its own and by nothing apart from it a lane may subscribe at,
-- and the outer's events apart from each root a step past them.  What
-- ended parts left running is keyed under no root, nor where a later
-- outer value subscribes its lane, nor at that value: so no lane, nor
-- the outer, nor the pool ties with a step the merge shows just past a
-- lane's end or an outer value.
module FlatOrder (p : Pos) where

  -- Where a lane may subscribe: strictly under `p`, a tick heading it.
  Ok : Pos → Set
  Ok j = Beneath p j × Headed j

  -- Keyed under `j`, a tick heading it, keyed by nothing apart from `j`
  -- a lane may subscribe at.
  Under : Pos → Pos → Set
  Under j h = Owned j h × Headed h × (∀ R → Ok R → Disjoint R j → ¬ Owned R h)

  -- A lane subscribed at `j`.
  Fit : ∀ {B} → Pos → Events∞ B → Set
  Fit j l = Ordered (force l) × Atop j (force l) × Steady (force l) × Trailing l × Every∞ (Under j) l

  Gen : ∀ {B} → MonotonicList B → Set
  Gen m = ∀ j → Ok j → Fit j (M.enter m j)

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

  -- A lane in flight under its root: its run, and what it leaves running.
  record Lane {B} (r : Pos) (x : Events B) (c : Tail) : Set where
    constructor lane
    field
      ord : Ordered x
      std : Steady x
      trl : Trail x c
      kx  : Every (Under r) x
      kc  : EveryT (Under r) c
      ok  : Ok r

  Static : ∀ {B} → Pos → Events∞ B → Set
  Static r l = Lane r (force l) (cut l)

  fresh : ∀ {B} j (l : Events∞ B) → Fit j l → Ok j → Static j l
  fresh j l (o , _ , sd , t , kx , kc) okj = lane o sd t kx kc okj

  lane-out : ∀ {B r k b c} {w : Events∞ B} → Lane r (out k b w) c → Static r w
  lane-out st = lane (proj₂ (ordered (Lane.ord st))) (proj₂ (steady (Lane.std st))) (proj₂ (proj₂ (trail (Lane.trl st))))
                     (proj₁ (proj₂ (every (Lane.kx st)))) (proj₂ (proj₂ (every (Lane.kx st)))) (Lane.ok st)

  lane-skip : ∀ {B r k c} {w : Events∞ B} → Lane r (skip k w) c → Static r w
  lane-skip st = lane (proj₂ (ordered (Lane.ord st))) (proj₂ (steady (Lane.std st))) (proj₂ (proj₂ (trail (Lane.trl st))))
                      (proj₁ (proj₂ (every (Lane.kx st)))) (proj₂ (proj₂ (every (Lane.kx st)))) (Lane.ok st)

  data Roots {B} : List (Events∞ B) → List Pos → Set where
    []ᴿ  : Roots [] []
    _∷ᴿ_ : ∀ {r l ls rs} → Static r l → Roots ls rs → Roots (l ∷ ls) (r ∷ rs)

  roots-++ : ∀ {B} {xs ys : List (Events∞ B)} {rs ss} → Roots xs rs → Roots ys ss → Roots (xs ++ ys) (rs ++ ss)
  roots-++ []ᴿ       S = S
  roots-++ (st ∷ᴿ R) S = st ∷ᴿ roots-++ R S

  roots-ok : ∀ {B} {ls : List (Events∞ B)} {rs} → Roots ls rs → All Ok rs
  roots-ok []ᴿ       = []ᴬ
  roots-ok (st ∷ᴿ R) = Lane.ok st ∷ᴬ roots-ok R

  data Split {B} (bs : List (Events∞ B)) (l : Events∞ B) (as : List (Events∞ B)) : List Pos → Set where
    split : ∀ {rbs r ras} → Roots bs rbs → Static r l → Roots as ras → Split bs l as (rbs ++ r ∷ ras)

  roots-split : ∀ {B} (bs : List (Events∞ B)) {l as rs} → Roots (bs ++ l ∷ as) rs → Split bs l as rs
  roots-split []       (st ∷ᴿ R) = split []ᴿ st R
  roots-split (b ∷ bs) (sb ∷ᴿ R) with roots-split bs R
  ... | split rb st ra = split (sb ∷ᴿ rb) st ra

  roots-at : ∀ {B} bs (l : Events∞ B) as {ls rs} → ls ≡ bs ++ l ∷ as → Roots ls rs → Split bs l as rs
  roots-at bs l as refl R = roots-split bs R

  -- An outer position: under `p`, a tick heading it.
  K : Pos → Set
  K y = Owned p y × Headed y

  -- The outer: in order and steady, its cuts trailing it, spread, under
  -- `p`, its values lanes.
  record Outer {B} (x : Events (MonotonicList B)) (c : Tail) : Set where
    constructor outer
    field
      ord : Ordered x
      std : Steady x
      trl : Trail x c
      spr : Spread x
      kx  : Every K x
      kc  : EveryT K c
      spn : Spawn x

  Heldᴹ : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Set
  Heldᴹ nothing  = ⊤
  Heldᴹ (just e) = Outer (force e) (cut e)

  outer-out : ∀ {B q m c} {w : Events∞ (MonotonicList B)} → Outer (out q m w) c → Outer (force w) (cut w)
  outer-out h = outer (proj₂ (ordered (Outer.ord h))) (proj₂ (steady (Outer.std h))) (proj₂ (proj₂ (trail (Outer.trl h))))
                      (proj₂ (spread (Outer.spr h))) (proj₁ (proj₂ (every (Outer.kx h)))) (proj₂ (proj₂ (every (Outer.kx h))))
                      (proj₂ (spawned (Outer.spn h)))

  outer-skip : ∀ {B q c} {w : Events∞ (MonotonicList B)} → Outer (skip q w) c → Outer (force w) (cut w)
  outer-skip h = outer (proj₂ (ordered (Outer.ord h))) (proj₂ (steady (Outer.std h))) (proj₂ (proj₂ (trail (Outer.trl h))))
                       (spread (Outer.spr h)) (proj₁ (proj₂ (every (Outer.kx h)))) (proj₂ (proj₂ (every (Outer.kx h))))
                       (spawned (Outer.spn h))

  -- Where a value at `y` subscribes its lane, apart from root `r`.
  D : Pos → Pos → Set
  D r y = Disjoint (y ++ [ ix 1 ]) r

  Aside : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Pos → Set
  Aside nothing  r = ⊤
  Aside (just e) r = Every∞ (D r) e

  aside-none : ∀ {B} rs → All (Aside {B} nothing) rs
  aside-none []       = []ᴬ
  aside-none {B} (r ∷ rs) = tt ∷ᴬ aside-none {B} rs

  -- No outer value at `k`, nor subscribing its lane over it.
  Free : ∀ {A} → Events A → Pos → Set
  Free x k = Every (λ y → ¬ Owned (y ++ [ ix 1 ]) k × y ≢ k) x

  FreeO : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Pos → Set
  FreeO nothing  k = ⊤
  FreeO (just e) k = Free (force e) k

  -- What ended parts left running: in order, under no root, free of the
  -- outer.
  Pool : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List Pos → Tail → Set
  Pool o rs t = SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × FreeO o k) t

  own-lane : ∀ r y → Owned r y → Owned r (y ++ [ ix 1 ])
  own-lane r y o = owned-trans r y (y ++ [ ix 1 ]) o (inj₁ (prefix-++ y [ ix 1 ]))

  aside-not : ∀ r y → D r y → ¬ Owned r y
  aside-not r y d o = proj₂ d (own-lane r y o)

  lane-ok : ∀ y → K y → Ok (y ++ [ ix 1 ])
  lane-ok y (o , h) = owned-snoc p y (ix 1) o , headed-snoc y h

  -- A step under a root is free of an outer value apart from it.
  q-pin : ∀ r k y → Under r k → D r y → K y → ¬ Owned (y ++ [ ix 1 ]) k × y ≢ k
  q-pin r k y (ork , _ , shy) d ky = shy (y ++ [ ix 1 ]) (lane-ok y ky) d , λ { refl → aside-not r y d ork }

  free : ∀ {A} r k (x : Events A) → Under r k → Every (D r) x → Every K x → Free x k
  free r k x u dx kx = every-mono (λ y dk → q-pin r k y u (proj₁ dk) (proj₂ dk)) x (every-zip x dx kx)

  freeO : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) r k → Under r k → Aside o r → Heldᴹ o → FreeO o k
  freeO nothing  r k u a h = tt
  freeO (just e) r k u a h = free r k (force e) u (proj₁ a) (Outer.kx h)

  -- A step an ended lane left: under no other root, free of the outer.
  ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) r k rs → Under r k → All (λ r′ → Ok r′ × Disjoint r r′) rs → Aside o r → Heldᴹ o
        → All (λ r′ → ¬ Owned r′ k) rs × FreeO o k
  ended o r k rs u oks a h = mapᴬ (λ {r′} od → proj₂ (proj₂ u) r′ (proj₁ od) (disjoint-swap r r′ (proj₂ od))) oks , freeO o r k u a h

  -- A lane dropped past an outer value at `q` leaves nothing before the
  -- step the value shows.
  drop-atop : ∀ {B} r q (x : Events B) c → Lane r x c → Beyond q x → D r q → AtopT (q ++ [ ix 0 ]) c
  drop-atop r q x idle      st b d = tt
  drop-atop r q x (pin k u) st b d = go x b (proj₁ (everyᵀ (proj₁ (proj₂ (trail (Lane.trl st)))))) (proj₁ (everyᵀ (Lane.kc st)))
    where
      go : ∀ x → Beyond q x → TrailE x k → Under r k → k <ᵖ (q ++ [ ix 0 ]) ≡ false
      go (out n _ _) b tr          u = <ᵖ-step q k (still q n k b tr)
      go (skip n _)  b (inj₁ tr)   u = <ᵖ-step q k (still q n k b tr)
      go (skip n _)  b (inj₂ refl) u with k <ᵖ q in kq
      ... | true  = ⊥-elim (t≢f (trans (sym b) (<ᵖ-step k q kq)))
      ... | false with <ᵖ-split q k kq
      ...   | inj₁ qk   = <ᵖ-step q k qk
      ...   | inj₂ refl = ⊥-elim (aside-not r q d (proj₁ u))
      go (end n)     b tr          u = <ᵖ-step q k (<ᵖ-trans q n k b (proj₁ tr))
      go hush        b ()          u

  drops-atop : ∀ {B} q (ls : List (Events∞ B)) {rs} → Roots ls rs → All (λ l → Beyond q (force l)) ls → All (λ r → D r q) rs
             → AtopT (q ++ [ ix 0 ]) (M.cuts ls)
  drops-atop q []       []ᴿ       []ᴬ       []ᴬ       = tt
  drops-atop q (l ∷ ls) (st ∷ᴿ R) (b ∷ᴬ bs) (d ∷ᴬ ds) =
    atopT-∪ (q ++ [ ix 0 ]) (cut l) (M.cuts ls) (drop-atop _ q (force l) (cut l) st b d) (drops-atop q ls R bs ds)

  drops-sorted : ∀ {B} (ls : List (Events∞ B)) {rs} → Roots ls rs → SortedT (M.cuts ls)
  drops-sorted []       []ᴿ       = sortedT-idle
  drops-sorted (l ∷ ls) (st ∷ᴿ R) = sortedT-∪ (cut l) (M.cuts ls) (proj₁ (trail (Lane.trl st))) (drops-sorted ls R)

  drops-free : ∀ {B} q (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) {rs} → Roots ls rs
             → All (λ r → Every (D r) (out q m w)) rs → Ok (q ++ [ ix 1 ]) → Every K (force w)
             → All (λ l → EveryT (λ k → All (λ r → ¬ Owned r k) [ q ++ [ ix 1 ] ] × Free (force w) k) (cut l)) ls
  drops-free q m w []       []ᴿ       []ᴬ       okq kw = []ᴬ
  drops-free q m w (l ∷ ls) (_∷ᴿ_ {r = r} st R) (a ∷ᴬ as) okq kw =
    everyT-mono (λ k u → proj₂ (proj₂ u) (q ++ [ ix 1 ]) okq (proj₁ (every a)) ∷ᴬ []ᴬ , free r k (force w) u (proj₁ (proj₂ (every a))) kw)
      (cut l) (Lane.kc st)
    ∷ᴬ drops-free q m w ls R as okq kw

  -- What the merge holds after an outer value's step.
  data Taken {B} (q : Pos) (w : Events∞ (MonotonicList B)) (t : Tail) : List (Events∞ B) × List (MonotonicList B) × Tail → Set where
    taken : ∀ {ls qs d rs} → Roots ls rs → Parted rs → All (Aside (just w)) rs → All (λ l → Atop (q ++ [ ix 0 ]) (force l)) ls
          → All Gen qs → Pool (just w) rs (t ∪ d) → AtopT (q ++ [ ix 0 ]) d → Taken q w t (ls , qs , d)

  module Admit {B} (q : Pos) (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (t : Tail) {rs : List Pos}
               (asd : All (λ r → Every (D r) (out q m w)) rs) (gm : Gen m) (okq : Ok (q ++ [ ix 1 ]))
               (sp : Aside (just w) (q ++ [ ix 1 ])) (kw : Every K (force w))
               (pl : SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free (out q m w) k) t) where

    q₁ = q ++ [ ix 1 ]
    q₀ = q ++ [ ix 0 ]
    fit = gm q₁ okq

    top : Atop q₀ (force (M.enter m q₁))
    top = atop-weaken q₁ q₀ _ (<ᵖ-asym q₀ q₁ (<ᵖ-part q {ix 0} {ix 1} [] [] refl)) (proj₁ (proj₂ fit))

    rest′ : All (Aside (just w)) rs
    rest′ = mapᴬ (λ a → proj₂ (every a)) asd

    keep : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned r k) rs → Free (out q m w) k → All (λ r → ¬ Owned r k) rs′) → Pool (just w) rs′ (t ∪ idle)
    keep f = sortedT-∪ t idle (proj₁ pl) sortedT-idle
           , everyT-∪ t idle (everyT-mono (λ k af → f k (proj₁ af) (proj₂ af) , proj₁ (proj₂ (every (proj₂ af)))) t (proj₂ pl)) everyT-idle

    admit-new : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls
              → Taken q w t (M.enter m q₁ ∷ ls , qs , idle)
    admit-new ls qs R pt gq bl =
      taken (fresh q₁ (M.enter m q₁) fit okq ∷ᴿ R) (mapᴬ (λ a → proj₁ (every a)) asd , pt) (sp ∷ᴬ rest′)
            (top ∷ᴬ mapᴬ (λ {l} → beyond-step q (force l)) bl) gq (keep (λ k a f → proj₁ (proj₁ (every f)) ∷ᴬ a)) tt

    admit-keep : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls → Taken q w t (ls , qs , idle)
    admit-keep ls qs R pt gq bl = taken R pt rest′ (mapᴬ (λ {l} → beyond-step q (force l)) bl) gq (keep (λ k a f → a)) tt

    admit-switch : ∀ ls qs → Roots ls rs → All Gen qs → All (λ l → Beyond q (force l)) ls → Taken q w t ([ M.enter m q₁ ] , qs , M.cuts ls)
    admit-switch ls qs R gq bl =
      taken (fresh q₁ (M.enter m q₁) fit okq ∷ᴿ []ᴿ) ([]ᴬ , tt) (sp ∷ᴬ []ᴬ) (top ∷ᴬ []ᴬ) gq
            ( sortedT-∪ t (M.cuts ls) (proj₁ pl) (drops-sorted ls R)
            , everyT-∪ t (M.cuts ls)
                (everyT-mono (λ k af → proj₁ (proj₁ (every (proj₂ af))) ∷ᴬ []ᴬ , proj₁ (proj₂ (every (proj₂ af)))) t (proj₂ pl))
                (cuts-every ls (drops-free q m w ls R asd okq kw)))
            (drops-atop q ls R bl (mapᴬ (λ a → proj₁ (every a)) asd))

  admit-ok : ∀ {B} op q (m : MonotonicList B) w t ls qs {rs} → Roots ls rs → Parted rs → All (λ r → Every (D r) (out q m w)) rs
           → All Gen qs → Gen m → Ok (q ++ [ ix 1 ]) → Aside (just w) (q ++ [ ix 1 ]) → All (λ l → Beyond q (force l)) ls
           → Every K (force w) → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free (out q m w) k) t
           → Taken q w t (M.admit op (q ++ [ ix 1 ]) m ls qs)
  admit-ok (M.mergeᶠ nothing)  q m w t ls       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-new q m w t asd gm okq sp kw pl ls qs R pt gq bl
  admit-ok (M.mergeᶠ (just n)) q m w t ls       qs R pt asd gq gm okq sp bl kw pl with length ls <ᵇ n
  ... | true  = Admit.admit-new q m w t asd gm okq sp kw pl ls qs R pt gq bl
  ... | false = Admit.admit-keep q m w t asd gm okq sp kw pl ls (qs ++ [ m ]) R pt (All++⁺ gq (gm ∷ᴬ []ᴬ)) bl
  admit-ok M.switchᶠ           q m w t ls       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-switch q m w t asd gm okq sp kw pl ls qs R gq bl
  admit-ok M.exhaustᶠ          q m w t []       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-new q m w t asd gm okq sp kw pl [] qs R pt gq bl
  admit-ok M.exhaustᶠ          q m w t (l ∷ ls) qs R pt asd gq gm okq sp bl kw pl = Admit.admit-keep q m w t asd gm okq sp kw pl (l ∷ ls) qs R pt gq bl

  -- The lanes other than one ending at `c` under `r` are all past `c`.
  clear-lanes : ∀ {B} r c {ls : List (Events∞ B)} {rs} → Ok r → Owned r c → Roots ls rs → All (Disjoint r) rs
              → All (λ l → Atop c (force l)) ls → All (λ l → Atop (c ++ [ ix 0 ]) (force l)) ls
  clear-lanes r c okr oc []ᴿ                 []ᴬ       []ᴬ       = []ᴬ
  clear-lanes r c okr oc (_∷ᴿ_ {l = l} st R) (d ∷ᴬ ds) (a ∷ᴬ as) =
    beyond-step c (force l) (atop-clear r c (force l) oc a (every-mono (λ h u → proj₂ (proj₂ u) r okr d) (force l) (Lane.kx st)))
    ∷ᴬ clear-lanes r c okr oc R ds as

  -- And so is the outer.
  atop-hand : ∀ {B} r c (o : Maybe (Events∞ (MonotonicList B))) → Owned r c → Atopᴹ c o → Aside o r → Atopᴹ (c ++ [ ix 0 ]) o
  atop-hand r c nothing  oc ao a = tt
  atop-hand r c (just e) oc ao a = beyond-step c (force e) (atop-clear r c (force e) oc ao (every-mono (aside-not r) (force e) (proj₁ a)))

  -- Where a lane's end at `c` subscribes the next, apart from every
  -- other root and from where the outer subscribes its lanes.
  hand-ok : ∀ r c → Ok r → Under r c → Ok (c ++ [ ix 1 ])
  hand-ok r c (br , _) (orc , hc , _) = owned-snoc p c (ix 1) (owned-trans p r c (beneath-owned p r br) orc) , headed-snoc c hc

  hand-apart : ∀ r c r′ → Under r c → Ok r′ → Disjoint r r′ → Disjoint (c ++ [ ix 1 ]) r′
  hand-apart r c r′ (orc , _ , shy) ok′ d =
    disjoint-swap r′ (c ++ [ ix 1 ])
      (apart-mark r′ c (ix 1) (ix-mark 1) (shy r′ ok′ (disjoint-swap r r′ d) , λ o → proj₁ d (owned-trans r c r′ orc o)))

  hand-aside : ∀ {B} r c (o : Maybe (Events∞ (MonotonicList B))) → Under r c → Aside o r → Heldᴹ o → Aside o (c ++ [ ix 1 ])
  hand-aside r c nothing  u a h = tt
  hand-aside r c (just e) u a h =
    every-mono one (force e) (every-zip (force e) (proj₁ a) (Outer.kx h)) , everyT-mono one (cut e) (everyT-zip (cut e) (proj₂ a) (Outer.kc h))
    where
      one : ∀ y → D r y × K y → D (c ++ [ ix 1 ]) y
      one y (d , ky) = apart-mark (y ++ [ ix 1 ]) c (ix 1) (ix-mark 1)
                         (proj₂ (proj₂ u) (y ++ [ ix 1 ]) (lane-ok y ky) d , λ o → proj₂ d (owned-trans r c (y ++ [ ix 1 ]) (proj₁ u) o))

  mutual
    ordered-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Ordered (M.go op o ls qs t)
    ordered-go op o ls qs idle      R pt asd gq h pl = ordered-parts op o ls qs idle R pt asd gq h pl tt
    ordered-go op o ls qs (pin k u) R pt asd gq h pl with M.ahead-of k o ls in e
    ... | true  = ordered-pool op o ls qs k u e R pt asd gq h pl
    ... | false = ordered-parts op o ls qs (pin k u) R pt asd gq h pl e

    ordered-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                 → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Ordered (M.left op o ls qs k u true)
    ordered (ordered-pool op o ls qs k u e R pt asd gq h (st , et)) =
      atop-go op o ls qs (later u) k (proj₁ (ahead-atop k o ls e)) (proj₂ (ahead-atop k o ls e)) (proj₁ (sortedᵀ st))
      , ordered-go op o ls qs (later u) R pt asd gq h (proj₂ (sortedᵀ st) , proj₂ (everyᵀ et))

    ordered-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                  → Heldᴹ o → Pool o rs t → Behind o ls t → Ordered (M.parts op o ls qs t)
    ordered-parts op o ls qs t R pt asd gq h pl bh with M.earliest ls | earliest-picks ls
    ... | none            | hs                  = ordered-via op o ls qs t R pt asd gq h pl bh hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = ordered-race op o k bs l as qs t rb st ra pt asd gq h pl (behind-at o t eq bh) hk ab aa

    ordered-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                → Heldᴹ o → Pool o rs t → Behind o ls t → All (λ l → M.head (force l) ≡ nothing) ls → Ordered (M.viaOuter op o ls qs t)
    ordered-via op nothing  ls qs t R pt asd gq h pl bh hs = record { ordered = tt }
    ordered-via op (just e) ls qs t R pt asd gq h pl bh hs with M.head (force e) in he
    ... | nothing = ordered-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs) (atopᴴ-nothing (force e) t he)
    ... | just k  = ordered-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs)
                      (atopᴴ (force e) t he (behind-atop k (just e) ls t bh (mapᴬ (λ {l} → atop-nothing k (force l)) hs) (self-atop (force e) he)))

    ordered-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
                 → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Behind o (bs ++ l ∷ as) t → M.head (force l) ≡ just k
                 → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as → Ordered (M.race op o k bs l as qs t)
    ordered-race op nothing  k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa =
      ordered-lane op nothing bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa tt
        (behind-atop k nothing (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) tt)
    ordered-race op (just e) k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa with M.head (force e) in he
    ... | nothing = ordered-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-nothing k (force e) he)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-nothing k (force e) he))
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = ordered-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) pt asd gq h pl
                      (lead-of (force e) (bs ++ l ∷ as) he
                        (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                                (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
                      (atopᴴ (force e) t he
                        (behind-atop k′ (just e) (bs ++ l ∷ as) t bh
                          (mapᴬ (λ {x} → atop-weaken k k′ (force x) (<ᵖ-asym k′ k kk)) (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)))
                          (self-atop (force e) he)))
    ...   | false = ordered-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-just (force e) he kk)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-just (force e) he kk))

    ordered-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs → Parted rs
                  → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → All Gen qs → Outer x (cut e)
                  → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free x k) t → Lead x ls → Atopᴴ x t
                  → Ordered (M.outer op e ls qs t x)
    ordered (ordered-outer op e ls qs t (out q m w) R pt asd gq h (st , et) ld at)
      with M.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (spawned (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₁ (proj₂ (every (Outer.kx h)))) (st , et)
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad =
      atop-go op (just w) ls′ qs′ (t ∪ d) (q ++ [ ix 0 ]) at′ (beyond-step q (force w) (past-beyond q (force w) (proj₁ (steady (Outer.std h)))))
        (atopT-∪ (q ++ [ ix 0 ]) t d (pool-step q t at (everyT-mono (λ k af → proj₂ (proj₁ (every (proj₂ af)))) t et)) ad)
      , ordered-go op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    ordered (ordered-outer op e ls qs t (skip q w) R pt asd gq h (st , et) ld at) =
      atop-go op (just w) ls qs t q (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (proj₁ (ordered (Outer.ord h))) at
      , ordered-go op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h)
          (st , everyT-mono (λ k af → proj₁ af , proj₁ (proj₂ (every (proj₂ af)))) t et)
    ordered (ordered-outer op e [] [] t (end c) R pt asd gq h pl ld at) = tt
    ordered (ordered-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h (st , et) ld at) =
      atop-go op nothing [] (m ∷ qs) (t ∪ cut e) c []ᴬ tt (outer-end-atop c e t h at)
      , ordered-go op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd (st , et))
    ordered (ordered-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h (st , et) ld at) =
      atop-go op nothing (l ∷ ls) qs (t ∪ cut e) c (mapᴬ (λ {x} → beyond-atop c (force x)) ld) tt (outer-end-atop c e t h at)
      , ordered-go op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd (st , et))
    ordered (ordered-outer op e ls qs t hush R pt asd gq h pl ld at) = tt

    ordered-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                 → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M.head x ≡ just k → All (λ y → Atop k (force y)) bs
                 → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t → Ordered (M.lane op o bs l as qs t x)
    ordered (ordered-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl ab aa ao at) =
      atop-go op o (bs ++ w ∷ as) qs t k (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at
      , ordered-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
    ordered (ordered-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl ab aa ao at) =
      atop-go op o (bs ++ w ∷ as) qs t k (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at
      , ordered-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    ordered (ordered-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h (sp , ep) refl ab aa ao at) =
      atop-go op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) c₀
        (top ∷ᴬ clear-lanes r c (Lane.ok st) orc (roots-++ rb ra) (proj₁ pp) (All++⁺ ab aa))
        (atop-hand r c o orc ao ar)
        (atopT-∪ c₀ t (cut l)
           (pool-step c t at (everyT-mono (λ k af eq → proj₁ (all-pick rbs ras (proj₁ af)) (subst (Owned r) eq orc)) t ep))
           (atopT-every c₀ (cut l) (λ k tr → <ᵖ-step c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
      , ordered-go op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M.enter m c₁) fit okc ∷ᴿ roots-++ rb ra)
          (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
          (hand-aside r c o uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
          ( sortedT-∪ t (cut l) sp (proj₁ (trail (Lane.trl st)))
          , everyT-∪ t (cut l)
              (everyT-mono (λ k af → (λ o₁ → proj₁ (all-pick rbs ras (proj₁ af)) (owned-trans r c₁ k (own-lane r c orc) o₁))
                                     ∷ᴬ proj₂ (all-pick rbs ras (proj₁ af)) , proj₂ af) t ep)
              (everyT-mono (λ k ut → proj₂ (proj₂ ut) ∷ᴬ proj₁ (ended o r k (rbs ++ ras) (proj₁ ut) oks ar h)
                                     , proj₂ (ended o r k (rbs ++ ras) (proj₁ ut) oks ar h))
                 (cut l) (everyT-zip (cut l) (Lane.kc st) (proj₁ (proj₂ (trail (Lane.trl st)))))))
      where
        c₀  = c ++ [ ix 0 ]
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        orc = proj₁ uc
        okc = hand-ok r c (Lane.ok st) uc
        fit = gm c₁ okc
        top = atop-weaken c₁ c₀ _ (<ᵖ-asym c₀ c₁ (<ᵖ-part c {ix 0} {ix 1} [] [] refl)) (proj₁ (proj₂ fit))
        pp  = parted-pick rbs r ras pt
        ar  = proj₁ (all-pick rbs ras asd)
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)
    ordered (ordered-lane op nothing [] l [] [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) = tt
    ordered (ordered-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      lane-ended op nothing [] l (a ∷ as) t c rb st ra pt asd h pl ab aa ao at
    ordered (ordered-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      lane-ended op nothing (b ∷ bs) l as t c rb st ra pt asd h pl ab aa ao at
    ordered (ordered-lane op (just e) bs l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      lane-ended op (just e) bs l as t c rb st ra pt asd h pl ab aa ao at
    ordered (ordered-lane op o bs l as qs t hush rb st ra pt asd gq h pl () ab aa ao at)

    lane-ended : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
               → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
               → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
               → Atop c (M.go op o (bs ++ as) [] (t ∪ cut l)) × Ordered (M.go op o (bs ++ as) [] (t ∪ cut l))
    lane-ended op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h (sp , ep) ab aa ao at =
      atop-go op o (bs ++ as) [] (t ∪ cut l) c (All++⁺ ab aa) ao
        (atopT-∪ c t (cut l) at (atopT-every c (cut l) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
      , ordered-go op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
          ( sortedT-∪ t (cut l) sp (proj₁ (trail (Lane.trl st)))
          , everyT-∪ t (cut l) (everyT-mono (λ k af → proj₂ (all-pick rbs ras (proj₁ af)) , proj₂ af) t ep)
              (everyT-mono (λ k u → ended o r k (rbs ++ ras) u oks (proj₁ (all-pick rbs ras asd)) h) (cut l) (Lane.kc st)))
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

    outer-end-atop : ∀ {B} c (e : Events∞ (MonotonicList B)) t → Outer (end c) (cut e) → AtopT c t → AtopT c (t ∪ cut e)
    outer-end-atop c e t h at = atopT-∪ c t (cut e) at (atopT-every c (cut e) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Outer.trl h)))))

    outer-end-pool : ∀ {B} c (e : Events∞ (MonotonicList B)) t rs → Outer (end c) (cut e) → All (λ r → Every (D r) (end c) × EveryT (D r) (cut e)) rs
                   → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free (end c) k) t → Pool {B} nothing rs (t ∪ cut e)
    outer-end-pool c e t rs h asd (st , et) =
      sortedT-∪ t (cut e) st (proj₁ (trail (Outer.trl h)))
      , everyT-∪ t (cut e) (everyT-mono (λ k af → proj₁ af , tt) t et)
          (everyT-mono (λ k a → mapᴬ (λ {r} → aside-not r k) a , tt) (cut e) (everyT-all rs (cut e) (mapᴬ proj₂ asd)))

  postulate
    -- AFTER A POOL STEP AT `k`, NOTHING SHOWS INSIDE IT: no lane, nor
    -- the outer, nor the pool's next keys under a step an ended part left.
    calm-pool-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                → All (Aside o) rs → Heldᴹ o → Pool o rs (pin k u) → Obl false k o ls qs (later u)

    -- AFTER A LANE'S VALUE AT `k`, EVERY PART'S NEXT IS PAST IT AND NOT
    -- INSIDE IT: the lane's own by its steadiness, the others keyed apart
    -- from its root.
    calm-out-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t k b w {rbs r ras}
               → Roots bs rbs → Lane r (out k b w) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
               → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
               → Obl true k o (bs ++ w ∷ as) qs t

    -- AFTER A LANE'S SKIP AT `k`, NOTHING SHOWS INSIDE IT, AND A VALUE
    -- PAST IT: the lane's own end, with one queued, not at `k` itself.
    calm-skip-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t k w {rbs r ras}
                → Roots bs rbs → Lane r (skip k w) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
                → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
                → Obl false k o (bs ++ w ∷ as) qs t

    -- AFTER A LANE'S END AT `c` HANDS ITS QUEUE ON, NOTHING SHOWS INSIDE
    -- THE STEP JUST PAST `c`: not the lane it subscribes, not another, not
    -- what it left running.
    calm-queue-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as m qs t c {rbs r ras}
                 → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
                 → Gen m → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
                 → Obl false (c ++ [ ix 0 ]) o (M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ cut l)

    -- AFTER A LANE'S END AT `c`, NOTHING SHOWS INSIDE IT: what it left
    -- running trailing it, the other parts keyed apart from its root.
    calm-end-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
               → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
               → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
               → Obl false c o (bs ++ as) [] (t ∪ cut l)

    -- AFTER AN OUTER VALUE'S STEP JUST PAST `q`, NOTHING SHOWS INSIDE
    -- THAT STEP: not the lane it admits, the lanes it keeps, what it drops.
    calm-admit-n : ∀ {B} op (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t q m (w : Events∞ (MonotonicList B)) {rs ls′ qs′ d} → M.admit op (q ++ [ ix 1 ]) m ls qs ≡ (ls′ , qs′ , d)
                 → Roots ls rs → Parted rs → All (λ r → Every (D r) (out q m w) × EveryT (D r) (cut e)) rs → All Gen qs
                 → Outer (out q m w) (cut e) → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free (out q m w) k) t
                 → Lead (out q m w) ls → Atopᴴ (out q m w) t
                 → Obl false (q ++ [ ix 0 ]) (just w) ls′ qs′ (t ∪ d)

    -- AFTER AN OUTER SKIP AT `q`, NOTHING SHOWS INSIDE IT.
    calm-oskip-n : ∀ {B} (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t q (w : Events∞ (MonotonicList B)) {rs}
                 → Roots ls rs → Parted rs → All (λ r → Every (D r) (skip q w) × EveryT (D r) (cut e)) rs
                 → Outer (skip q w) (cut e) → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free (skip q w) k) t
                 → Lead (skip q w) ls → Atopᴴ (skip q w) t
                 → Obl false q (just w) ls qs t

    -- AFTER THE OUTER'S END AT `c`, NOTHING SHOWS INSIDE IT.
    calm-oend-n : ∀ {B} (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t c {rs}
                → Roots ls rs → Parted rs → All (λ r → Every {MonotonicList B} (D r) (end c) × EveryT (D r) (cut e)) rs
                → Outer {B} (end c) (cut e) → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free {MonotonicList B} (end c) k) t
                → Lead {MonotonicList B} (end c) ls → Atopᴴ {MonotonicList B} (end c) t
                → Obl {B} false c nothing ls qs (t ∪ cut e)
  mutual
    calm-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Calm (M.go op o ls qs t)
    calm-go op o ls qs idle      R pt asd gq h pl = calm-parts op o ls qs idle R pt asd gq h pl tt
    calm-go op o ls qs (pin k u) R pt asd gq h pl with M.ahead-of k o ls in e
    ... | true  = calm-pool op o ls qs k u e R pt asd gq h pl
    ... | false = calm-parts op o ls qs (pin k u) R pt asd gq h pl e

    calm-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                 → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Calm (M.left op o ls qs k u true)
    calms (calm-pool op o ls qs k u e R pt asd gq h (st , et)) =
      next-go false k op o ls qs (later u) (proj₁ (ahead-atop k o ls e)) (proj₂ (ahead-atop k o ls e)) (proj₁ (sortedᵀ st))
        (calm-pool-n o ls qs k u e R pt asd h (st , et))
      , calm-go op o ls qs (later u) R pt asd gq h (proj₂ (sortedᵀ st) , proj₂ (everyᵀ et))

    calm-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                  → Heldᴹ o → Pool o rs t → Behind o ls t → Calm (M.parts op o ls qs t)
    calm-parts op o ls qs t R pt asd gq h pl bh with M.earliest ls | earliest-picks ls
    ... | none            | hs                  = calm-via op o ls qs t R pt asd gq h pl bh hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = calm-race op o k bs l as qs t rb st ra pt asd gq h pl (behind-at o t eq bh) hk ab aa

    calm-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                → Heldᴹ o → Pool o rs t → Behind o ls t → All (λ l → M.head (force l) ≡ nothing) ls → Calm (M.viaOuter op o ls qs t)
    calm-via op nothing  ls qs t R pt asd gq h pl bh hs = record { calms = tt }
    calm-via op (just e) ls qs t R pt asd gq h pl bh hs with M.head (force e) in he
    ... | nothing = calm-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs) (atopᴴ-nothing (force e) t he)
    ... | just k  = calm-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs)
                      (atopᴴ (force e) t he (behind-atop k (just e) ls t bh (mapᴬ (λ {l} → atop-nothing k (force l)) hs) (self-atop (force e) he)))

    calm-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
                 → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Behind o (bs ++ l ∷ as) t → M.head (force l) ≡ just k
                 → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as → Calm (M.race op o k bs l as qs t)
    calm-race op nothing  k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa =
      calm-lane op nothing bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa tt
        (behind-atop k nothing (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) tt)
    calm-race op (just e) k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa with M.head (force e) in he
    ... | nothing = calm-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-nothing k (force e) he)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-nothing k (force e) he))
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = calm-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) pt asd gq h pl
                      (lead-of (force e) (bs ++ l ∷ as) he
                        (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                                (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
                      (atopᴴ (force e) t he
                        (behind-atop k′ (just e) (bs ++ l ∷ as) t bh
                          (mapᴬ (λ {x} → atop-weaken k k′ (force x) (<ᵖ-asym k′ k kk)) (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)))
                          (self-atop (force e) he)))
    ...   | false = calm-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-just (force e) he kk)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-just (force e) he kk))

    calm-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs → Parted rs
                  → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → All Gen qs → Outer x (cut e)
                  → SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × Free x k) t → Lead x ls → Atopᴴ x t
                  → Calm (M.outer op e ls qs t x)
    calms (calm-outer op e ls qs t (out q m w) R pt asd gq h (st , et) ld at)
      with M.admit op (q ++ [ ix 1 ]) m ls qs in eq
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (spawned (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₁ (proj₂ (every (Outer.kx h)))) (st , et)
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad =
      next-go false (q ++ [ ix 0 ]) op (just w) ls′ qs′ (t ∪ d) at′ (beyond-step q (force w) (past-beyond q (force w) (proj₁ (steady (Outer.std h)))))
        (atopT-∪ (q ++ [ ix 0 ]) t d (pool-step q t at (everyT-mono (λ k af → proj₂ (proj₁ (every (proj₂ af)))) t et)) ad)
        (calm-admit-n op e ls qs t q m w eq R pt asd gq h (st , et) ld at)
      , calm-go op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    calms (calm-outer op e ls qs t (skip q w) R pt asd gq h (st , et) ld at) =
      next-go false q op (just w) ls qs t (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (proj₁ (ordered (Outer.ord h))) at
        (calm-oskip-n e ls qs t q w R pt asd h (st , et) ld at)
      , calm-go op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h)
          (st , everyT-mono (λ k af → proj₁ af , proj₁ (proj₂ (every (proj₂ af)))) t et)
    calms (calm-outer op e [] [] t (end c) R pt asd gq h pl ld at) = tt
    calms (calm-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h (st , et) ld at) =
      next-go false c op nothing [] (m ∷ qs) (t ∪ cut e) []ᴬ tt (outer-end-atop c e t h at) (calm-oend-n e [] (m ∷ qs) t c []ᴿ pt asd h (st , et) ld at)
      , calm-go op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd (st , et))
    calms (calm-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h (st , et) ld at) =
      next-go false c op nothing (l ∷ ls) qs (t ∪ cut e) (mapᴬ (λ {x} → beyond-atop c (force x)) ld) tt (outer-end-atop c e t h at)
        (calm-oend-n e (l ∷ ls) qs t c R pt asd h (st , et) ld at)
      , calm-go op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd (st , et))
    calms (calm-outer op e ls qs t hush R pt asd gq h pl ld at) = tt

    calm-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                 → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M.head x ≡ just k → All (λ y → Atop k (force y)) bs
                 → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t → Calm (M.lane op o bs l as qs t x)
    calms (calm-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl ab aa ao at) =
      next-go true k op o (bs ++ w ∷ as) qs t (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at (calm-out-n o bs l as qs t k b w rb st ra pt asd h pl ab aa ao at)
      , calm-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
    calms (calm-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl ab aa ao at) =
      next-go false k op o (bs ++ w ∷ as) qs t (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at (calm-skip-n o bs l as qs t k w rb st ra pt asd h pl ab aa ao at)
      , calm-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    calms (calm-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h (sp , ep) refl ab aa ao at) =
      next-go false c₀ op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l)
        (top ∷ᴬ clear-lanes r c (Lane.ok st) orc (roots-++ rb ra) (proj₁ pp) (All++⁺ ab aa))
        (atop-hand r c o orc ao ar)
        (atopT-∪ c₀ t (cut l)
           (pool-step c t at (everyT-mono (λ k af eq → proj₁ (all-pick rbs ras (proj₁ af)) (subst (Owned r) eq orc)) t ep))
           (atopT-every c₀ (cut l) (λ k tr → <ᵖ-step c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
        (calm-queue-n o bs l as m qs t c rb st ra pt asd gm h (sp , ep) ab aa ao at)
      , calm-go op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M.enter m c₁) fit okc ∷ᴿ roots-++ rb ra)
          (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
          (hand-aside r c o uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
          ( sortedT-∪ t (cut l) sp (proj₁ (trail (Lane.trl st)))
          , everyT-∪ t (cut l)
              (everyT-mono (λ k af → (λ o₁ → proj₁ (all-pick rbs ras (proj₁ af)) (owned-trans r c₁ k (own-lane r c orc) o₁))
                                     ∷ᴬ proj₂ (all-pick rbs ras (proj₁ af)) , proj₂ af) t ep)
              (everyT-mono (λ k ut → proj₂ (proj₂ ut) ∷ᴬ proj₁ (ended o r k (rbs ++ ras) (proj₁ ut) oks ar h)
                                     , proj₂ (ended o r k (rbs ++ ras) (proj₁ ut) oks ar h))
                 (cut l) (everyT-zip (cut l) (Lane.kc st) (proj₁ (proj₂ (trail (Lane.trl st)))))))
      where
        c₀  = c ++ [ ix 0 ]
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        orc = proj₁ uc
        okc = hand-ok r c (Lane.ok st) uc
        fit = gm c₁ okc
        top = atop-weaken c₁ c₀ _ (<ᵖ-asym c₀ c₁ (<ᵖ-part c {ix 0} {ix 1} [] [] refl)) (proj₁ (proj₂ fit))
        pp  = parted-pick rbs r ras pt
        ar  = proj₁ (all-pick rbs ras asd)
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)
    calms (calm-lane op nothing [] l [] [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) = tt
    calms (calm-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      calm-ended op nothing [] l (a ∷ as) t c rb st ra pt asd h pl ab aa ao at
    calms (calm-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      calm-ended op nothing (b ∷ bs) l as t c rb st ra pt asd h pl ab aa ao at
    calms (calm-lane op (just e) bs l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      calm-ended op (just e) bs l as t c rb st ra pt asd h pl ab aa ao at
    calms (calm-lane op o bs l as qs t hush rb st ra pt asd gq h pl () ab aa ao at)

    calm-ended : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
               → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
               → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
               → At (Next false c) (M.go op o (bs ++ as) [] (t ∪ cut l)) × Calm (M.go op o (bs ++ as) [] (t ∪ cut l))
    calm-ended op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h (sp , ep) ab aa ao at =
      next-go false c op o (bs ++ as) [] (t ∪ cut l) (All++⁺ ab aa) ao
        (atopT-∪ c t (cut l) at (atopT-every c (cut l) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
        (calm-end-n o bs l as t c rb st ra pt asd h (sp , ep) ab aa ao at)
      , calm-go op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
          ( sortedT-∪ t (cut l) sp (proj₁ (trail (Lane.trl st)))
          , everyT-∪ t (cut l) (everyT-mono (λ k af → proj₂ (all-pick rbs ras (proj₁ af)) , proj₂ af) t ep)
              (everyT-mono (λ k u → ended o r k (rbs ++ ras) u oks (proj₁ (all-pick rbs ras asd)) h) (cut l) (Lane.kc st)))
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

  -- Every step of a lane subscribed at `j`, keyed under it, headed, and
  -- keyed by nothing apart from it a lane may subscribe at.
  under∞ : ∀ {A} j (r : Events∞ A) → Every∞ (Owned j) r → Every∞ Headed r → (∀ R → Ok R → Disjoint R j → Every∞ (λ h → ¬ Owned R h) r)
         → Every∞ (Under j) r
  under∞ j r ow hh ap =
    every-mono pack (force r) (every-zip (force r) (every-zip (force r) (proj₁ ow) (proj₁ hh))
                                 (every-∀ {P = λ i h → ¬ Owned (proj₁ i) h} (force r) (λ i → proj₁ (ap (proj₁ i) (proj₁ (proj₂ i)) (proj₂ (proj₂ i))))))
    , everyT-mono pack (cut r) (everyT-zip (cut r) (everyT-zip (cut r) (proj₂ ow) (proj₂ hh))
                                  (everyT-∀ {P = λ i h → ¬ Owned (proj₁ i) h} (cut r) (λ i → proj₂ (ap (proj₁ i) (proj₁ (proj₂ i)) (proj₂ (proj₂ i))))))
    where
      pack : ∀ h → (Owned j h × Headed h) × (∀ (i : Σ Pos (λ R → Ok R × Disjoint R j)) → ¬ Owned (proj₁ i) h) → Under j h
      pack h ((o , hd) , f) = o , hd , λ R ok d → f (R , ok , d)

-- A SUBSCRIPTION'S CUTS TRAIL ITS RUN, where a tick heads it, over
-- sorted sources alien to it: at every state, what a cut would leave
-- running is sorted, none of it before a value coming next, nor before a
-- skip but the step that skip shows just past it; all of it past an end,
-- none keyed where that end would subscribe a lane.
postulate
  trailing-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Trailing (U.stateᴺ (U.subscribe o p) ρ)

-- A SUBSCRIPTION'S VALUES SPREAD, where a tick heads it, over sorted
-- sources alien to it: after a value at `x`, nothing later, shown or
-- left running, keys where a lane admitted at `x` would, nor where a
-- later value's lane would key under it.
postulate
  spread-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
             → Spread (U.meaning (U.subscribe o p) ρ)

-- A FINITE PROGRAM SUBSCRIBED IS IN ORDER, where a tick heads, over
-- sorted sources alien to where it subscribes.
ordered-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
             → Ordered (U.meaning (U.subscribe o p) ρ)

-- A FLATMAP SUBSCRIBED MERGES IN ORDER AND STEADY: over sorted sources
-- alien to where it subscribes.  An outer value at `q` shows as a skip
-- just past `q`, its outer steady so nothing ties there; a lane's end
-- at `c` with one queued shows a skip just past `c`, and no other lane,
-- nor the outer, ties at `c`; what an ended part left shows when it is
-- ahead of every part still running.  And no part's next lies inside
-- the event just shown.
--
-- REFUTED: 37b70651 of any outer node in order, by a joiner told a value and a skip at one position
-- REFUTED: 0d0df253 wherever no tick heads the position, a lane's timer frame sorting before the step admitting it
flat-calm : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
          → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
          → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ) × Steady (U.meaning (U.subscribe (flatMap op f s) p) ρ)

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
steady-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₂ (flat-calm op f s ff fs p ρ hp so cl)
steady-subᶠ (connect s b) _ p ρ hp so cl = steady-connect s b p ρ hp so cl
steady-subᶠ (connected i) _ p ρ hp so cl =
  steady-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
steady-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  steady-defer l p ρ hp cl (steady-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                              (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

flat-calm {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  O.ordered-go (flatOp op) (just E) [] [] idle O.[]ᴿ tt []ᴬ []ᴬ held (sortedT-idle , everyT-idle)
  , calm-steady _ (O.calm-go (flatOp op) (just E) [] [] idle O.[]ᴿ tt []ᴬ []ᴬ held (sortedT-idle , everyT-idle))
  where
    module O = FlatOrder p
    S = U.stateᴺ (U.subscribe s p) ρ
    F : A → MonotonicList B
    F a = M.cold λ q → U.stateᴺ (U.subscribe (f a) q) ρ
    E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ
    kp = Reach.reachᶠ (keyedRules p) s fs p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ cl)
    hd = Reach.reachᶠ headedRules s fs p ρ hp (sorted-headed ρ so)
    ko : Every∞ O.K S
    ko = every∞-mono (λ h bh → beneath-owned p h (proj₁ bh) , proj₂ bh) S
           (every-zip (force S) (proj₁ kp) (proj₁ hd) , everyT-zip (cut S) (proj₂ kp) (proj₂ hd))
    gen : ∀ a → O.Gen (F a)
    gen a j (bj , hj) =
      ordered-subᶠ (f a) (ff a) j ρ hj so cj , rise-sub (f a) j ρ hj , steady-subᶠ (f a) (ff a) j ρ hj so cj , trailing-sub (f a) j ρ hj so cj
      , O.under∞ j L
          (every∞-mono (beneath-owned j) L (Reach.reachᶠ (keyedRules j) (f a) (ff a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj)))
          (Reach.reachᶠ headedRules (f a) (ff a) j ρ hj (sorted-headed ρ so))
          (λ R okR d → every∞-mono (λ _ → proj₁) L
             (Reach.reachᶠ (apartRules R (tick-beneath p R hp (proj₁ okR))) (f a) (ff a) j ρ d
                (alienᴱ-owned p R (beneath-owned p R (proj₁ okR)) ρ cl)))
      where
        L  = U.stateᴺ (U.subscribe (f a) j) ρ
        cj = alienᴱ-owned p j (beneath-owned p j bj) ρ cl
    held : O.Outer (force E) (cut E)
    held = O.outer (ordered-map F _ (ordered-subᶠ s fs p ρ hp so cl)) (steady-map F _ (steady-subᶠ s fs p ρ hp so cl))
             (trail-map F (force S) (cut S) (trailing-sub s p ρ hp so cl)) (spread-map F _ (spread-sub s p ρ hp so cl))
             (every-map F _ (proj₁ ko)) (proj₂ ko) (O.spawn-map F _ gen)

ordered-subᶠ (cold c) _ p ρ hp so cl = subst Ordered (sym (U.start-meaning p (lower c) ρ)) (ordered-start p (lower c) hp)
ordered-subᶠ empty _ p ρ hp so cl = record { ordered = tt }
ordered-subᶠ (of xs) _ p ρ hp so cl = ordered-of p 0 xs
ordered-subᶠ (map f s) (map-f fs) p ρ hp so cl = ordered-map f _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = ordered-scan f z _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl = ordered-take i q _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₁ (flat-calm op f s ff fs p ρ hp so cl)
ordered-subᶠ (connect s b) _ p ρ hp so cl = ordered-connect s b p ρ hp so cl
ordered-subᶠ (connected i) _ p ρ hp so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl)
  where sl = sorted-lookup ρ so i
ordered-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  ordered-defer l p ρ hp cl (ordered-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                               (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

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
