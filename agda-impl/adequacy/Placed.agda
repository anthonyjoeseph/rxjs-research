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
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; agree;
  agreeᵀ; Earliest; none; found; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root;
  <ᵖ-asym; <ᵖ-down; <ᵖ-next; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-part; ≮-trans; <ᵖ-below;
  <ᵖ-tick; Tail; Tail∞; pin; idle; _∪_; tailᴱ; Agreeᵀ; pin⁼; idle⁼)
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

  -- A CONNECT SUBSCRIBED IS IN ORDER: each source step a skip just past
  -- it, ahead of the body's later events, and what the source runs on
  -- with past the body's end left as the tail.
  ordered-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                  → Ordered (U.meaning (U.subscribe (connect s b) p) ρ)

  -- A FLATMAP SUBSCRIBED MERGES IN ORDER: over sorted sources alien to
  -- where it subscribes.  An outer value at `q` shows as a skip just
  -- past `q`, its outer steady so nothing ties there; a lane's end at
  -- `c` with one queued shows a skip just past `c`, and no other lane,
  -- nor the outer, ties at `c`; what an ended part left shows when it
  -- is ahead of every part still running.
  --
  -- REFUTED: 37b70651 of any outer node in order, by a joiner told a value and a skip at one position
  -- REFUTED: 0d0df253 wherever no tick heads the position, a lane's timer frame sorting before the step admitting it
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `FlatOrder`, the proof over pool-free lanes, ghost roots pairwise apart
  ordered-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ)

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

-- A FINITE PROGRAM SUBSCRIBED IS IN ORDER, where a tick heads, over
-- sorted sources alien to where it subscribes.
ordered-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
             → Ordered (U.meaning (U.subscribe o p) ρ)

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
steady-subᶠ (connect s b) _ p ρ hp so cl = steady-connect s b p ρ hp so cl
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
ordered-subᶠ (flatMap op f s) _ p ρ hp so cl = ordered-flat op f s p ρ hp so cl
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
