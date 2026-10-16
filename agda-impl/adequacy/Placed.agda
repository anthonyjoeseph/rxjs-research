{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ; ++-assoc; ++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; +-identityʳ; +-monoʳ-<; ≤-pred; m≤n⇒m<n∨m≡n; <⇒≢; +-suc; +-monoʳ-≤; +-monoˡ-≤; +-assoc; n≤1+n; <⇒≤; <-≤-trans; ≤-trans; m≤n+m; m≤m+n; <-irrefl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
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

-- `e`'s first no proper extension of `k`, and strictly past it if a value
-- or an end.
Clear : ∀ {A} → Pos → Events A → Set
Clear k (out h _ _) = k <ᵖ h ≡ true × ¬ Ext k h
Clear k (skip h _)  = ¬ Ext k h
Clear k (end h)     = k <ᵖ h ≡ true × ¬ Ext k h
Clear k hush        = ⊤

-- Never a step inside the position just left, and never one tied with
-- a value or an end: a flatMap lane ending where it just stepped, one
-- queued, would subscribe it inside that step.  A rejoin keys a source's event at `q` under `q`, so a
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
clear-away k (end _)     c = proj₂ c
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
... | true  = <ᵖ-next p c (sub p) pc , λ x → every al (owned-ext (under-ext p c x))
... | false = <ᵖ-part p {ix 0} {last} [] [] refl , λ x → ext-irrefl p (under-ext p p x)
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
clear-in p q (end c)     pq a (qc , ne) with p <ᵖ c in pc
... | true  = apart-in q c (sub p) qc ne
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

sibling-prefix : ∀ p {l l′} → l ≢ l′ → ¬ Prefix (p ++ [ l ]) (p ++ [ l′ ])
sibling-prefix []      ne (refl , _) = ne refl
sibling-prefix (_ ∷ p) ne (_ , q)    = sibling-prefix p ne q

-- Two children of one position key nothing of each other.
sibling : ∀ p {l l′} → Mark l′ → l ≢ l′ → ¬ Owned (p ++ [ l ]) (p ++ [ l′ ])
sibling p     m ne (inj₁ q) = sibling-prefix p ne q
sibling p {l} m ne (inj₂ t) =
  <-irrefl refl (<-≤-trans (tagged-weigh (p ++ [ l ]) p (tagged-mark _ p _ m t)) (prefix-weigh p (p ++ [ l ]) (prefix-++ p [ l ])))

-- A bare tick keyed under no position a tick heads.
owned-tick : ∀ p t → Headed p → ¬ Owned (p ++ [ ix 1 ]) (ix t ∷ [])
owned-tick (ix _ ∷ [])    t _ (inj₁ (_ , ()))
owned-tick (ix _ ∷ _ ∷ _) t _ (inj₁ (_ , ()))
owned-tick (ix _ ∷ _)     t _ (inj₂ ())
owned-tick []             t () _
owned-tick (sub _ ∷ _)    t () _
owned-tick (last ∷ _)     t () _

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

-- A prefix is the position itself or a proper one.
prefix-plus : ∀ k h → Prefix k h → k ≡ h ⊎ Prefix⁺ k h
prefix-plus []      []      tt         = inj₁ refl
prefix-plus []      (_ ∷ _) tt         = inj₂ tt
prefix-plus (a ∷ k) (b ∷ h) (refl , q) with prefix-plus k h q
... | inj₁ refl = inj₁ refl
... | inj₂ q⁺   = inj₂ (refl , q⁺)

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
-- A burst's end keeps its root's tick.
tick-last : ∀ r → tick (r ++ [ last ]) ≡ tick r
tick-last []          = refl
tick-last (ix _ ∷ _)  = refl
tick-last (sub _ ∷ _) = refl
tick-last (last ∷ _)  = refl

-- Each value a run shows satisfies `G`.
mutual
  Valuess : ∀ {A} → (A → Set) → Events A → Set
  Valuess G (out _ a r) = G a × Values G (force r)
  Valuess G (skip _ r)  = Values G (force r)
  Valuess G (end _)     = ⊤
  Valuess G hush        = ⊤

  record Values {A} (G : A → Set) (e : Events A) : Set where
    coinductive
    field values : Valuess G e

open Values public

values-map : ∀ {A B} {G : B → Set} (f : A → B) (e : Events A) → (∀ a → G (f a)) → Values G (M.mapᴱ f e)
values (values-map f (out h a r) g) = g a , values-map f (force r) g
values (values-map f (skip h r)  g) = values-map f (force r) g
values (values-map f (end h)     g) = tt
values (values-map f hush        g) = tt

values-mono : ∀ {A} {G H : A → Set} → (∀ a → G a → H a) → (e : Events A) → Values G e → Values H e
values (values-mono g (out h a r) v) = g a (proj₁ (values v)) , values-mono g (force r) (proj₂ (values v))
values (values-mono g (skip h r)  v) = values-mono g (force r) (values v)
values (values-mono g (end h)     v) = tt
values (values-mono g hush        v) = tt

-- A flatMap's merge over parts holding `P`: the outer's values show a
-- step just past them, holding `P` there, and a lane's end with one
-- queued too; a lane subscribes where `S` lets it, just past either.
module Merge (P S : Pos → Set) (step : ∀ h → P h → P (h ++ [ ix 0 ])) (held : ∀ h → P h → S (h ++ [ ix 1 ])) where

  -- A lane holding `P` wherever `S` lets it subscribe.
  Lane : ∀ {B} → MonotonicList B → Set
  Lane m = ∀ k → S k → Every∞ P (M.enter m k)

  -- An outer holding `P`, each value a lane.
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

  outer-of : ∀ {B} (e : Events (MonotonicList B)) → Every P e → Values (Lane {B}) e → Outer e
  outerly (outer-of (out h m r) pe ve) =
    proj₁ (every pe) , proj₁ (values ve) , outer-of (force r) (proj₁ (proj₂ (every pe))) (proj₂ (values ve)) , proj₂ (proj₂ (every pe))
  outerly (outer-of (skip h r)  pe ve) = proj₁ (every pe) , outer-of (force r) (proj₁ (proj₂ (every pe))) (values ve) , proj₂ (proj₂ (every pe))
  outerly (outer-of (end h)     pe ve) = every pe
  outerly (outer-of hush        pe ve) = tt

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
             (held q (proj₁ (outerly po))) (proj₁ (proj₂ (outerly po))) pl pq
    ... | ls′ , qs′ , d | (pl′ , pq′ , pd) =
      step q (proj₁ (outerly po))
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
      step c (every px)
      , every-go op o (M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ cut l) po (ln ∷ᴬ All++⁺ pb pa) pq (everyT-∪ t (cut l) pt pl)
      , everyT-whole o (M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) (t ∪ cut l) po (ln ∷ᴬ All++⁺ pb pa) (everyT-∪ t (cut l) pt pl)
      where ln = lm (c ++ [ ix 1 ]) (held c (every px))
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

record Rules : Set₁ where
  field
    S P Src : Pos → Set
    child   : ∀ j l → Mark l → S j → P (j ++ [ l ])
    deeper  : ∀ h l → Mark l → P h → P (h ++ [ l ])
    held    : ∀ h → P h → S h
    frame   : ∀ n e → P e → tick e ≤ n → S (ix (suc n) ∷ sub e ∷ [])
    join    : ∀ q j → Src q → S j → j <ᵖ q ≡ true → P (q ++ [ sub j ])
    source  : ∀ h → P h → Src h

module Reach (R : Rules) where
  open Rules R
  open Merge P S (λ h → deeper h (ix 0) (ix-mark 0)) (λ h ph → held _ (deeper h (ix 1) (ix-mark 1) ph))

  -- A cold shows its subscribe burst under where it subscribes, and
  -- each later frame at a tick past it, tagged with the burst before.
  mutual
    every-frames : ∀ {A t} τ e (m : M.From A (suc t)) → tick e ≡ τ + t → P e → Every P (M.frames τ e m)
    every (every-frames τ e M.done                     te pe) = pe
    every (every-frames τ e M.quiet                    te pe) = tt
    every (every-frames τ e (M.at (suc t′) (s≤s le) b) te pe) =
      every (every-burst τ _ 0 b refl (subst (λ x → S (ix x ∷ sub e ∷ [])) (sym (+-suc τ t′))
        (frame (τ + t′) e pe (subst (_≤ τ + t′) (sym te) (+-monoʳ-≤ τ le)))))

    every-burst : ∀ {A t} τ r i (b : M.Frame A t) → tick r ≡ τ + t → S r → Every P (M.burst τ r i b)
    every (every-burst τ r i (M.emit a k) tr sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) tr sr , everyT-idle
    every (every-burst τ r i (M.stall k)  tr sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) tr sr , everyT-idle
    every (every-burst τ r i (M.close k)  tr sr) =
      child r (ix i) (ix-mark i) sr , every-frames τ (r ++ [ last ]) (M.From∞.force k) (trans (tick-last r) tr) (child r last last-mark sr) , everyT-idle

  every-start : ∀ {A} p (m : From A 0) → S p → Every P (M.start p m)
  every-start p (M.at zero _ b)    sp = every-burst (tick p) p 0 b (sym (+-identityʳ (tick p))) sp
  every-start p (M.at (suc n) _ b) sp =
    every-burst (tick p) _ 0 b refl
      (subst (λ x → S (ix x ∷ sub (p ++ [ last ]) ∷ [])) (sym (+-suc (tick p) n))
        (frame (tick p + n) _ (child p last last-mark sp) (subst (_≤ tick p + n) (sym (tick-last p)) (m≤m+n (tick p) n))))
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
    every (every-rejoin p (out q a k) sp se) = every (every-shown p q (just a) k (p <ᵖ q) refl sp (proj₁ (every se)) (proj₁ (proj₂ (every se))))
    every (every-rejoin p (skip q k)  sp se) = every (every-shown p q nothing k (p <ᵖ q) refl sp (proj₁ (every se)) (proj₁ (proj₂ (every se))))
    every (every-rejoin p (end c)     sp se) with p <ᵖ c in pc
    ... | true  = join c p (every se) sp pc
    ... | false = child p last last-mark sp
    every (every-rejoin p hush        sp se) = tt

    every-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → p <ᵖ q ≡ b → S p → Src q → Every Src (force k) → Every P (M.shown p q a k b)
    every (every-shown p q (just a) k true  pq sp sq sk) = join q p sq sp pq , every-rejoin p (force k) sp sk , everyT-idle
    every (every-shown p q nothing  k true  pq sp sq sk) = join q p sq sp pq , every-rejoin p (force k) sp sk , everyT-idle
    every (every-shown p q (just a) k false pq sp sq sk) = child p (ix 0) (ix-mark 0) sp , every-rejoin p (force k) sp sk , everyT-idle
    every (every-shown p q nothing  k false pq sp sq sk) = child p (ix 0) (ix-mark 0) sp , every-rejoin p (force k) sp sk , everyT-idle

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
      po = outer-of _ (every-map _ _ (proj₁ ih)) (values-map _ _ (λ a j sj → reachᶠ (f a) (ff a) j ρ sj sρ)) , proj₂ ih
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
  ; frame  = λ n e b _ → inj₂ (inj₁ (beneath-owned p e b))
  ; join   = λ q j _ o _ → inj₂ (owned-tagged p j (q ++ [ sub j ]) o (tagged-sub q j))
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
  ; frame  = λ _ _ _ _ → tt
  ; join   = λ q _ hq _ _ → headed-snoc q hq
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
  ; frame  = λ n e (na , nb) _ → frame-fwd a n e nt na nb , frame-bwd a n e nb
  ; join   = λ q j nq dj _ → apart-join a q j nq dj
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

-- Before the next step, atop it.
before-atop : ∀ {B} q (x : Events B) → M.before q x ≡ true → Atop q x
before-atop q (out k _ _) b = <ᵖ-asym q k b
before-atop q (skip k _)  b = <ᵖ-asym q k b
before-atop q (end k)     b = <ᵖ-asym q k b
before-atop q hush        b = tt

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
beyond-clear k (end h)     b al = b , λ { (ext l ls) → every al (inj₁ (prefix-++ k (l ∷ ls))) }
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
past-clear k (end h)     p       = p
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

prefix-rest : ∀ k h → Prefix k h → Σ Pos (λ ys → h ≡ k ++ ys)
prefix-rest []      h       _          = h , refl
prefix-rest (_ ∷ _) []      ()
prefix-rest (a ∷ k) (b ∷ h) (refl , p) with prefix-rest k h p
... | ys , refl = ys , refl

prefix-lt : ∀ j n → Prefix j n → j ≡ n ⊎ j <ᵖ n ≡ true
prefix-lt j n pr with prefix-rest j n pr
... | []     , refl = inj₁ (sym (++-identityʳ j))
... | l ∷ ls , refl = inj₂ (<ᵖ-below j ls)

-- What comes before a position under `p`, outside `p`, comes before `p`.
below-under : ∀ p k ys → ¬ Prefix p k → k <ᵖ (p ++ ys) ≡ true → k <ᵖ p ≡ true
below-under p k ys np h with k <ᵖ p in e
... | true  = refl
... | false with <ᵖ-split p k e
...   | inj₂ refl = ⊥-elim (np (prefix-refl p))
...   | inj₁ pk with () ← trans (sym (<ᵖ-asym (p ++ ys) k (M.<ᵖ-apart p k ys pk (λ zs q → np (subst (Prefix p) (sym q) (prefix-++ p zs)))))) h

-- What comes before a lane under `p`, outside `p`, comes before every
-- lane under it.
below-lane : ∀ p k i j → ¬ Prefix p k → k <ᵖ (p ++ [ ix i ]) ≡ true → k <ᵖ (p ++ [ ix j ]) ≡ true
below-lane p k i j np h = <ᵖ-trans k p (p ++ [ ix j ]) (below-under p k [ ix i ] np h) (<ᵖ-below p [])

-- RISING: whatever under `p` tags a position came before it.  A join
-- keys a source's event after where it joined, and a timer's frame
-- sits at a tick past its burst's.
Rise : Pos → Pos → Set
Rise p h = Headed h × (∀ k → Headed k → Owned p k → Tagged k h → k <ᵖ h ≡ true)

rise-owned : ∀ p k h → Rise p h → Headed k → Owned p k → Owned k h → k ≡ h ⊎ k <ᵖ h ≡ true
rise-owned p k h r hk ok (inj₁ pr) = prefix-lt k h pr
rise-owned p k h r hk ok (inj₂ t)  = inj₂ (proj₂ r k hk ok t)

tick-mono : ∀ k h → Headed k → Headed h → k ≡ h ⊎ k <ᵖ h ≡ true → tick k ≤ tick h
tick-mono (ix t ∷ ks) (ix u ∷ hs) _ _ (inj₁ refl) = ≤-refl
tick-mono (ix t ∷ ks) (ix u ∷ hs) _ _ (inj₂ lt)   = <ᵖ-tick t u ks hs lt
tick-mono []          _           () _
tick-mono (sub _ ∷ _) _           () _
tick-mono (last ∷ _)  _           () _
tick-mono (ix _ ∷ _)  []          _ ()
tick-mono (ix _ ∷ _)  (sub _ ∷ _) _ ()
tick-mono (ix _ ∷ _)  (last ∷ _)  _ ()

rise-mark : ∀ p j l → Mark l → Rise p j → Rise p (j ++ [ l ])
rise-mark p j l m (hj , rj) =
  headed-snoc j hj , λ k hk ok t → <ᵖ-trans k j (j ++ [ l ]) (rj k hk ok (tagged-mark k j l m t)) (<ᵖ-below j [])

rise-frame : ∀ p n e → Rise p e → tick e ≤ n → Rise p (ix (suc n) ∷ sub e ∷ [])
rise-frame p n e re te = tt , tg
  where tg : ∀ k → Headed k → Owned p k → Tagged k (ix (suc n) ∷ sub e ∷ []) → k <ᵖ (ix (suc n) ∷ sub e ∷ []) ≡ true
        tg (ix t ∷ ks) hk ok (inj₁ o) =
          proj₁ (tick-past ks (sub e ∷ []) (s≤s (≤-trans (tick-mono (ix t ∷ ks) e hk (proj₁ re) (rise-owned p _ e re hk ok o)) te)))
        tg []          () ok _
        tg (sub _ ∷ _) () ok _
        tg (last ∷ _)  () ok _

rise-join : ∀ p q j → Rise p q → Rise p j → j <ᵖ q ≡ true → Rise p (q ++ [ sub j ])
rise-join p q j rq rj jq = headed-snoc q (proj₁ rq) , tg
  where tg : ∀ k → Headed k → Owned p k → Tagged k (q ++ [ sub j ]) → k <ᵖ (q ++ [ sub j ]) ≡ true
        tg k hk ok t with tagged-split k q j t
        ... | inj₁ tq = <ᵖ-trans k q (q ++ [ sub j ]) (proj₂ rq k hk ok tq) (<ᵖ-below q [])
        ... | inj₂ oj with rise-owned p k j rj hk ok oj
        ...   | inj₁ refl = <ᵖ-trans k q (q ++ [ sub j ]) jq (<ᵖ-below q [])
        ...   | inj₂ kj   = <ᵖ-trans k q (q ++ [ sub j ]) (<ᵖ-trans k j q kj jq) (<ᵖ-below q [])

risingRules : Pos → Rules
risingRules p = record
  { S      = Rise p
  ; P      = Rise p
  ; Src    = Rise p
  ; child  = λ j l m r → rise-mark p j l m r
  ; deeper = λ h l m r → rise-mark p h l m r
  ; held   = λ _ r → r
  ; frame  = rise-frame p
  ; join   = rise-join p
  ; source = λ _ r → r
  }

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
... | false | false = past-snoc k h last ck
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



-- A CONNECT'S SOURCE KEYS NOTHING UNDER ITS BODY: the two are siblings.
alien-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
          → Alien (p ++ [ ix 0 ]) (U.meaning (U.subscribe o (p ++ [ ix 1 ])) ρ)
alien-sub o p ρ al =
  alien-apart o (p ++ [ ix 0 ]) (p ++ [ ix 1 ]) ρ (alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ al)
    (sibling p (ix-mark _) (λ ())) (sibling p (ix-mark _) (λ ())) (no-tick p)

everyT-zip : ∀ {P Q : Pos → Set} (t : Tail) → EveryT P t → EveryT Q t → EveryT (λ h → P h × Q h) t
everyᵀ (everyT-zip (pin k u) pt qt) = (proj₁ (everyᵀ pt) , proj₁ (everyᵀ qt)) , everyT-zip (later u) (proj₂ (everyᵀ pt)) (proj₂ (everyᵀ qt))
everyᵀ (everyT-zip idle      pt qt) = tt

-- Each of `t`'s steps with each of `u`'s, read from `u`'s side.
everyT-flip : ∀ {P : Pos → Pos → Set} (t u : Tail) → EveryT (λ a → EveryT (P a) u) t → EveryT (λ b → EveryT (λ a → P a b) t) u
everyᵀ (everyT-flip t (pin k v) x) = everyT-mono (λ a e → proj₁ (everyᵀ e)) t x , everyT-flip t (later v) (everyT-mono (λ a e → proj₂ (everyᵀ e)) t x)
everyᵀ (everyT-flip t idle      x) = tt

every-zip : ∀ {A} {P Q : Pos → Set} (e : Events A) → Every P e → Every Q e → Every (λ h → P h × Q h) e
every (every-zip (out h _ r) pe qe) = (proj₁ (every pe) , proj₁ (every qe)) , every-zip (force r) (proj₁ (proj₂ (every pe))) (proj₁ (proj₂ (every qe)))
                                      , everyT-zip (cut r) (proj₂ (proj₂ (every pe))) (proj₂ (proj₂ (every qe)))
every (every-zip (skip h r)  pe qe) = (proj₁ (every pe) , proj₁ (every qe)) , every-zip (force r) (proj₁ (proj₂ (every pe))) (proj₁ (proj₂ (every qe)))
                                      , everyT-zip (cut r) (proj₂ (proj₂ (every pe))) (proj₂ (proj₂ (every qe)))
every (every-zip (end h)     pe qe) = every pe , every qe
every (every-zip hush        pe qe) = tt

every∞-zip : ∀ {A} {P Q : Pos → Set} (r : Events∞ A) → Every∞ P r → Every∞ Q r → Every∞ (λ h → P h × Q h) r
every∞-zip r (pe , pt) (qe , qt) = every-zip (force r) pe qe , everyT-zip (cut r) pt qt

-- Sources alien to `p` rise under anything `p` owns: nothing there tags them.
rise-env : ∀ {Γ} p r → Owned p r → (ρ : NEnv Γ) → Everyᴱ Headed ρ → Alienᴱ p ρ → Everyᴱ (Rise r) ρ
rise-env p r pr []ᴬ      _         _         = tt
rise-env p r pr (e ∷ᴬ ρ) (he , hρ) (ae , aρ) =
  every-mono (λ h z → proj₁ z , λ k hk ok t → ⊥-elim (proj₂ z (owned-trans p r h pr (inj₂ (owned-tagged r k h ok t))))) e (every-zip e he ae)
  , rise-env p r pr ρ hρ aρ

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

-- A tail's steps never inside one before them.
mutual
  FlatTs : Tail → Set
  FlatTs (pin k u) = EveryT (λ h → ¬ Ext k h) (later u) × FlatT (later u)
  FlatTs idle      = ⊤

  record FlatT (t : Tail) : Set where
    coinductive
    field flatᵀ : FlatTs t

open FlatT public

flatT-idle : FlatT idle
flatᵀ flatT-idle = tt

-- Neither strictly inside the other.
Apart : Pos → Pos → Set
Apart a b = ¬ Ext a b × ¬ Ext b a

apart-of : ∀ {a b} → Disjoint a b → Apart a b
apart-of d = (λ x → proj₁ d (owned-ext x)) , (λ x → proj₂ d (owned-ext x))

-- Two flat tails side by side, no step of one inside a step of the other.
mutual
  flatT-∪ : ∀ t u → FlatT t → FlatT u → EveryT (λ a → EveryT (Apart a) u) t → FlatT (t ∪ u)
  flatT-∪ idle      u ft fu x = fu
  flatT-∪ (pin k r) u ft fu x = flatT-first k r u (M.sooner k u) ft fu x

  flatT-first : ∀ k r u b → FlatT (pin k r) → FlatT u → EveryT (λ a → EveryT (Apart a) u) (pin k r) → FlatT (M.first k r u b)
  flatᵀ (flatT-first k r u          true  ft fu x) =
    everyT-∪ (later r) u (proj₁ (flatᵀ ft)) (everyT-mono (λ h ap → proj₁ ap) u (proj₁ (everyᵀ x)))
    , flatT-∪ (later r) u (proj₂ (flatᵀ ft)) fu (proj₂ (everyᵀ x))
  flatᵀ (flatT-first k r idle       false ft fu x) = flatᵀ ft
  flatᵀ (flatT-first k r (pin k′ u) false ft fu x) =
    everyT-∪ (pin k r) (later u) (everyT-mono (λ a ap → proj₂ (proj₁ (everyᵀ ap))) (pin k r) x) (proj₁ (flatᵀ fu))
    , flatT-∪ (pin k r) (later u) ft (proj₂ (flatᵀ fu)) (everyT-mono (λ a ap → proj₂ (everyᵀ ap)) (pin k r) x)

-- A tail's first, from what every step of it satisfies.
atopT-every : ∀ h {P : Pos → Set} t → (∀ k → P k → k <ᵖ h ≡ false) → EveryT P t → AtopT h t
atopT-every h (pin k u) f pt = f k (proj₁ (everyᵀ pt))
atopT-every h idle      f pt = tt

-- `n` marks the step at `k`: just past it, or just past a mark of it, as
-- a connect re-shows a skip it did not take.
--
-- REFUTED: e295322c by a connect re-showing its lane's skip at `k ++ [ ix 0 , ix 0 ]`, `k` still pinned, while a mark was only `k ++ [ ix 0 ]`
data Marks (k : Pos) : Pos → Set where
  shown  : Marks k (k ++ [ ix 0 ])
  reshown : ∀ {n} → Marks k n → Marks k (n ++ [ ix 0 ])

marks-eq : ∀ {k n} → Marks k n → Σ Pos (λ zs → n ≡ k ++ ix 0 ∷ zs)
marks-eq         shown      = [] , refl
marks-eq {k = k} (reshown m) with marks-eq m
... | zs , refl = zs ++ [ ix 0 ] , ++-assoc k (ix 0 ∷ zs) [ ix 0 ]

-- Past `k`, and no proper extension of it: no extension of it at all.
past-apart : ∀ k h → k <ᵖ h ≡ true → ¬ Ext k h → ∀ ys → h ≡ k ++ ys → ⊥
past-apart k h kh nx []       e with () ← trans (sym (subst (λ z → k <ᵖ z ≡ true) (trans e (++-identityʳ k)) kh)) (<ᵖ-irrefl k)
past-apart k h kh nx (l ∷ ls) e = nx (subst (Ext k) (sym e) (ext l ls))

-- Past `k`'s subtree, and so is all that comes no earlier.
past-noext : ∀ k n h → k <ᵖ n ≡ true → ¬ Ext k n → h <ᵖ n ≡ false → ¬ Ext k h
past-noext k n .(k ++ l ∷ ls) kn nx hn (ext l ls) with () ← trans (sym hn) (M.<ᵖ-apart k n (l ∷ ls) kn (past-apart k n kn nx))

inside-prefix : ∀ r k h → M.inside r k ≡ true → Prefix k h → M.inside r h ≡ true
inside-prefix r k h i pr with prefix-rest k h pr
... | ys , refl = M.inside-++ r k ys i

-- Inside `r` is under it.
inside-under : ∀ r k → M.inside r k ≡ true → Prefix r k
inside-under []      k       i = tt
inside-under (a ∷ r) []      ()
inside-under (a ∷ r) (b ∷ k) i with M.inside-cons a r b k i
... | e , i′ = e , inside-under r k i′

ext-prefix : ∀ {k j n} → Ext k j → Prefix j n → Ext k n
ext-prefix {k} {n = n} (ext l ls) pr with prefix-rest (k ++ l ∷ ls) n pr
... | ys , refl = subst (Ext k) (sym (++-assoc k (l ∷ ls) ys)) (ext l (ls ++ ys))

marks-prefix : ∀ {k n} → Marks k n → Prefix k n
marks-prefix {k} shown             = prefix-++ k [ ix 0 ]
marks-prefix {k} (reshown {n} m)   = prefix-trans k n (n ++ [ ix 0 ]) (marks-prefix m) (prefix-++ n [ ix 0 ])

-- Between a step and its mark, its mark too.
marks-mid : ∀ {j n} k → Marks j n → j <ᵖ k ≡ true → n <ᵖ k ≡ false → Marks j k
marks-mid {j} k shown jk nk with <ᵖ-split (j ++ [ ix 0 ]) k (<ᵖ-step j k jk)
... | inj₁ lt with () ← trans (sym lt) nk
... | inj₂ refl = shown
marks-mid {j} k (reshown {n} m) jk nk with n <ᵖ k in e
... | false = marks-mid k m jk e
... | true with <ᵖ-split (n ++ [ ix 0 ]) k (<ᵖ-step n k e)
...   | inj₁ lt with () ← trans (sym lt) nk
...   | inj₂ refl = reshown m

-- Between a step and its mark, under the mark.
marks-under : ∀ {j n} k → Marks j n → j <ᵖ k ≡ true → n <ᵖ k ≡ false → Prefix k n
marks-under {j} k shown jk nk with <ᵖ-split (j ++ [ ix 0 ]) k (<ᵖ-step j k jk)
... | inj₁ lt with () ← trans (sym lt) nk
... | inj₂ refl = prefix-refl k
marks-under {j} k (reshown {n} m) jk nk with n <ᵖ k in e
... | false = prefix-trans k n (n ++ [ ix 0 ]) (marks-under k m jk e) (prefix-++ n [ ix 0 ])
... | true with <ᵖ-split (n ++ [ ix 0 ]) k (<ᵖ-step n k e)
...   | inj₁ lt with () ← trans (sym lt) nk
...   | inj₂ refl = prefix-refl k

-- A mark of a step keyed with none of `a` is not keyed under `a`.
marks-alien : ∀ {a k n} → Marks k n → Owned a n → Disjoint a k → ⊥
marks-alien {a} {k} shown (inj₁ pr) d with prefix-split a k (ix 0) pr
... | inj₁ q  = proj₁ d (inj₁ q)
... | inj₂ eq = proj₂ d (subst (Owned k) (sym eq) (inj₁ (prefix-++ k [ ix 0 ])))
marks-alien {a} {k} shown (inj₂ t) d = proj₁ d (inj₂ (tagged-lane a k 0 t))
marks-alien {a} {k} (reshown {n} m) (inj₁ pr) d with prefix-split a n (ix 0) pr
... | inj₁ q  = marks-alien m (inj₁ q) d
... | inj₂ eq = proj₂ d (subst (Owned k) (sym eq) (inj₁ (prefix-trans k n (n ++ [ ix 0 ]) (marks-prefix m) (prefix-++ n [ ix 0 ]))))
marks-alien {a} {k} (reshown {n} m) (inj₂ t) d = marks-alien m (inj₂ (tagged-lane a n 0 t)) d

-- Past a step and not under it: past its marks.
marks-past : ∀ {k n} h → Marks k n → k <ᵖ h ≡ true → ¬ Ext k h → n <ᵖ h ≡ true
marks-past {k} h m kh nx with marks-eq m
... | zs , refl = M.<ᵖ-apart k h (ix 0 ∷ zs) kh (past-apart k h kh nx)

-- Between a step and its mark: under the step.
marks-between : ∀ {k n} q → Marks k n → k <ᵖ q ≡ true → q <ᵖ n ≡ true → Prefix k q
marks-between {k} q m kq qn with marks-eq m
... | zs , refl with M.<ᵖ-between k q (ix 0 ∷ zs) kq qn
...   | ys , refl = prefix-++ k ys

-- What a skip at `n` lets run on: no step before it but one it marks.
Marked : Pos → Pos → Set
Marked n k = k <ᵖ n ≡ false ⊎ Marks k n

marked-cue : ∀ {j n} m → Marks j n → n <ᵖ m ≡ false → Marked m j
marked-cue {j} m mk nm with j <ᵖ m in e
... | true  = inj₂ (marks-mid m mk e nm)
... | false = inj₁ refl

-- What a cut leaves running trails the run's next event: no step before
-- a value nor keyed with it, nor before a skip but a step it marks; every step past an end, and none keyed where that end would
-- subscribe a lane, nor over it; nothing left behind silence.
TrailE : ∀ {A} → Events A → Pos → Set
TrailE (out n _ _) k = k <ᵖ n ≡ false × Disjoint n k
TrailE (skip n _)  k = Marked n k
TrailE (end n)     k = n <ᵖ k ≡ true × Disjoint (n ++ [ ix 1 ]) k × ¬ Ext n k
TrailE hush        k = ⊥

mutual
  Trailings : ∀ {A} → Events A → Set
  Trailings (out n _ r) = Trail (force r) (cut r) × EveryT (Disjoint n) (cut r)
  Trailings (skip _ r)  = Trail (force r) (cut r)
  Trailings (end _)     = ⊤
  Trailings hush        = ⊤

  -- A run `x`, leaving `c` running were it cut now, and every later
  -- state, each cut trailing its run.
  record Trail {A} (x : Events A) (c : Tail) : Set where
    coinductive
    field trail : SortedT c × EveryT (TrailE x) c × Trailings x
          trailᶠ : FlatT c

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
  trailings-map f (out _ _ r) t = trail-map f (force r) (cut r) (proj₁ t) , proj₂ t
  trailings-map f (skip _ r)  t = trail-map f (force r) (cut r) t
  trailings-map f (end _)     t = tt
  trailings-map f hush        t = tt

  trail-map : ∀ {A B} (f : A → B) (x : Events A) c → Trail x c → Trail (M.mapᴱ f x) c
  trail (trail-map f x c t) =
    proj₁ (trail t) , everyT-mono (trailE-map f x) c (proj₁ (proj₂ (trail t))) , trailings-map f x (proj₂ (proj₂ (trail t)))
  trailᶠ (trail-map f x c t) = trailᶠ t

trailE-scan : ∀ {A B} (f : B → A → B) z (x : Events A) k → TrailE x k → TrailE (M.scanᴱ f z x) k
trailE-scan f z (out _ _ _) k t = t
trailE-scan f z (skip _ _)  k t = t
trailE-scan f z (end _)     k t = t
trailE-scan f z hush        k ()

mutual
  trailings-scan : ∀ {A B} (f : B → A → B) z (x : Events A) → Trailings x → Trailings (M.scanᴱ f z x)
  trailings-scan f z (out _ a r) t = trail-scan f (f z a) (force r) (cut r) (proj₁ t) , proj₂ t
  trailings-scan f z (skip _ r)  t = trail-scan f z (force r) (cut r) t
  trailings-scan f z (end _)     t = tt
  trailings-scan f z hush        t = tt

  trail-scan : ∀ {A B} (f : B → A → B) z (x : Events A) c → Trail x c → Trail (M.scanᴱ f z x) c
  trail (trail-scan f z x c t) =
    proj₁ (trail t) , everyT-mono (trailE-scan f z x) c (proj₁ (proj₂ (trail t))) , trailings-scan f z x (proj₂ (proj₂ (trail t)))
  trailᶠ (trail-scan f z x c t) = trailᶠ t

-- A run leaving nothing running, at its last state, trails it.
trail-idle : ∀ {A} (x : Events A) → Trailings x → Trail x idle
trail (trail-idle x t) = sortedT-idle , everyT-idle , t
trailᶠ (trail-idle x t) = flatT-idle

-- A TRAIL HOLDS OF WHAT AGREES WITH IT at every depth: its run and what
-- it leaves running alike.
atopT-≈ : ∀ h t u → Agreeᵀ 1 t u → AtopT h t → AtopT h u
atopT-≈ h (pin k _) (pin k _) (pin⁼ _) a = a
atopT-≈ h idle      idle      idle⁼    a = a

mutual
  sortedT-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → SortedT t → SortedT u
  sortedᵀ (sortedT-≈ t u ag st) = sortedTs-≈ t u ag (ag 1) st

  sortedTs-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → Agreeᵀ 1 t u → SortedT t → SortedTs u
  sortedTs-≈ (pin k l) (pin k r) ag (pin⁼ _) st =
    atopT-≈ k (later l) (later r) (restᵀ-agree (ag 2)) (proj₁ (sortedᵀ st))
    , sortedT-≈ (later l) (later r) (λ n → restᵀ-agree (ag (suc n))) (proj₂ (sortedᵀ st))
  sortedTs-≈ idle      idle      ag idle⁼    st = tt

mutual
  flatT-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → FlatT t → FlatT u
  flatᵀ (flatT-≈ t u ag ft) = flatTs-≈ t u ag (ag 1) ft

  flatTs-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → Agreeᵀ 1 t u → FlatT t → FlatTs u
  flatTs-≈ (pin k l) (pin k r) ag (pin⁼ _) ft =
    everyT-≈ (later l) (later r) (λ n → restᵀ-agree (ag (suc n))) (proj₁ (flatᵀ ft))
    , flatT-≈ (later l) (later r) (λ n → restᵀ-agree (ag (suc n))) (proj₂ (flatᵀ ft))
  flatTs-≈ idle      idle      ag idle⁼    ft = tt

trailE-≈ : ∀ {A} (x y : Events A) → Agree 1 x y → ∀ k → TrailE x k → TrailE y k
trailE-≈ (out _ _ _) (out _ _ _) (out⁼ _ _)  k t = t
trailE-≈ (skip _ _)  (skip _ _)  (skip⁼ _ _) k t = t
trailE-≈ (end _)     (end _)     end⁼        k t = t
trailE-≈ hush        hush        hush⁼       k t = t

mutual
  trail-≈ : ∀ {A} (x y : Events A) c d → (∀ k → Agree k x y) → (∀ k → Agreeᵀ k c d) → Trail x c → Trail y d
  trail (trail-≈ x y c d ag at tr) =
    sortedT-≈ c d at (proj₁ (trail tr))
    , everyT-≈ c d at (everyT-mono (trailE-≈ x y (ag 1)) c (proj₁ (proj₂ (trail tr))))
    , trailings-≈ x y ag (ag 1) (proj₂ (proj₂ (trail tr)))
  trailᶠ (trail-≈ x y c d ag at tr) = flatT-≈ c d at (trailᶠ tr)

  trailings-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Agree 1 x y → Trailings x → Trailings y
  trailings-≈ (out _ _ l) (out _ _ r) ag (out⁼ _ _) (t , e) =
    trail-≈ (force l) (force r) (cut l) (cut r) (λ k → rest-agree (ag (suc k))) (λ k → M.agree-tail (ag (suc k))) t
    , everyT-≈ (cut l) (cut r) (λ k → M.agree-tail (ag (suc k))) e
  trailings-≈ (skip _ l)  (skip _ r)  ag (skip⁼ _ _) t =
    trail-≈ (force l) (force r) (cut l) (cut r) (λ k → rest-agree (ag (suc k))) (λ k → M.agree-tail (ag (suc k))) t
  trailings-≈ (end _)     (end _)     ag end⁼        t = tt
  trailings-≈ hush        hush        ag hush⁼       t = tt

-- A cold leaf's run leaves nothing running at any state.
mutual
  trail-frames : ∀ {A t} τ e (m : From A t) → Trail (M.frames τ e m) idle
  trail-frames τ e M.done        = trail-idle _ tt
  trail-frames τ e M.quiet       = trail-idle _ tt
  trail-frames τ e (M.at t _ b)  = trail-burst τ (ix (τ + t) ∷ sub e ∷ []) 0 b

  trail-burst : ∀ {A t} τ r i (b : M.Frame A t) → Trail (M.burst τ r i b) idle
  trail (trail-burst τ r i (M.emit a k)) = sortedT-idle , everyT-idle , trail-burst τ r (suc i) (M.Frame∞.force k) , everyT-idle
  trail (trail-burst τ r i (M.stall k))  = sortedT-idle , everyT-idle , trail-burst τ r (suc i) (M.Frame∞.force k)
  trail (trail-burst τ r i (M.close k))  = sortedT-idle , everyT-idle , trail-frames τ (r ++ [ last ]) (M.From∞.force k)
  trailᶠ (trail-burst τ r i b) = flatT-idle

trailing-start : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Trailing (U.stateᴺ (U.startᶜ p m) ρ)
trailing-start p (M.at zero _ b)    ρ = trail-burst (tick p) p 0 b
trailing-start p (M.at (suc t) le b) ρ = trail-frames (tick p) (p ++ [ last ]) (M.at (suc t) le b)
trailing-start p M.done             ρ = trail-idle _ tt
trailing-start p M.quiet            ρ = trail-idle _ tt

-- A list's run leaves nothing running.
trail-of : ∀ {A} p i (xs : List A) → Trail (M.ofᴱ p i xs) idle
trail-of p i []       = trail-idle _ tt
trail-of p i (x ∷ xs) = trail-idle _ (trail-of p (suc i) xs , everyT-idle)

-- A joiner's run leaves nothing running, whatever its source left.
mutual
  trail-rejoin : ∀ {A} p (e : Events A) → Trail (M.rejoin p e) idle
  trail-rejoin p (out q a k) = trail-shown p q (just a) k (p <ᵖ q)
  trail-rejoin p (skip q k)  = trail-shown p q nothing k (p <ᵖ q)
  trail-rejoin p (end c) with p <ᵖ c
  ... | true  = trail-idle _ tt
  ... | false = trail-idle _ tt
  trail-rejoin p hush        = trail-idle _ tt

  trail-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → Trail (M.shown p q a k b) idle
  trail (trail-shown p q (just a) k true)  = sortedT-idle , everyT-idle , trail-rejoin p (force k) , everyT-idle
  trail (trail-shown p q nothing  k true)  = sortedT-idle , everyT-idle , trail-rejoin p (force k)
  trail (trail-shown p q (just a) k false) = sortedT-idle , everyT-idle , trail-rejoin p (force k)
  trail (trail-shown p q nothing  k false) = sortedT-idle , everyT-idle , trail-rejoin p (force k)
  trailᶠ (trail-shown p q a k b) = flatT-idle

-- Keyed apart from where a lane admitted at `x` would key, and `y`'s
-- lane too.
Sp : Pos → Pos → Set
Sp x y = Disjoint (y ++ [ ix 1 ]) (x ++ [ ix 1 ]) × ¬ Owned y (x ++ [ ix 1 ])

-- After a value at `x`, nothing later, shown or left running, lies
-- where a lane admitted then would key, nor keys where `x`'s does.
mutual
  Spreads : ∀ {A} → Events A → Set
  Spreads (out x _ r) = Every∞ (Sp x) r × Spread (force r)
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

spread-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Spread e → Spread (M.scanᴱ f z e)
spread (spread-scan f z (out h a r) s) =
  (every-scan f (f z a) (force r) (proj₁ (proj₁ (spread s))) , proj₂ (proj₁ (spread s))) , spread-scan f (f z a) (force r) (proj₂ (spread s))
spread (spread-scan f z (skip h r)  s) = spread-scan f z (force r) (spread s)
spread (spread-scan f z (end h)     s) = tt
spread (spread-scan f z hush        s) = tt

rest-spread : ∀ {A} (x : Events A) → Spread x → Spread (rest x)
rest-spread (out _ _ _) s = proj₂ (spread s)
rest-spread (skip _ _)  s = spread s
rest-spread (end _)     s = record { spread = tt }
rest-spread hush        s = s

-- What follows a value at `x`, in whatever agrees with a run there.
spread-rest : ∀ {A k} x a (r : Events∞ A) (e : Events A) → Agree (suc k) e (out x a r) → Spread e
            → Every∞ (Sp x) (record { force = rest e ; cut = M.tailOf e })
spread-rest x a r (out _ _ _) (out⁼ _ _) s = proj₁ (spread s)

-- A LIMIT SPREADS WHERE ITS APPROXIMANTS DO.
mutual
  spread-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Spread (xs n)) → (∀ n → Agree n (xs n) y) → Spread y
  spread (spread-lim xs y ps ag) = spreads-lim xs y ps ag (xs 1) (ag 1)

  spreads-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Spread (xs n)) → (∀ n → Agree n (xs n) y)
              → (x : Events A) → Agree 1 x y → Spreads y
  spreads-lim xs (out h a r) ps ag (out h _ _) (out⁼ _ _) =
    ( every-lim (λ n → rest (xs (suc n))) (force r) (λ n → proj₁ (spread-rest h a r (xs (suc n)) (ag (suc n)) (ps (suc n))))
        (λ n → rest-agree (ag (suc n)))
    , everyT-lim (λ n → M.tailOf (xs (suc n))) (cut r) (λ n → proj₂ (spread-rest h a r (xs (suc n)) (ag (suc n)) (ps (suc n))))
        (λ n → M.agree-tail (ag (suc n))) )
    , spread-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-spread (xs (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
  spreads-lim xs (skip h r)  ps ag (skip h _)  (skip⁼ _ _) =
    spread-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-spread (xs (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
  spreads-lim xs (end h)     ps ag (end h)     end⁼        = tt
  spreads-lim xs hush        ps ag hush        hush⁼       = tt

spread-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Spread x → Spread y
spread-≈ x y a s = spread-lim (λ _ → x) y (λ _ → s) a

-- A DEFER SPREADS, its program's being.
spread-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
             → Spread (U.meaning (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Spread (U.meaning (U.deferᶜ l p []) ρ)
spread (spread-defer l p ρ hp cl sp) = spread-≈ S X alike sp
  where open Deferred l p ρ hp cl

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

clear-beyond : ∀ {A} k (e : Events A) → M.clear k (M.head e) ≡ true → Beyond k e
clear-beyond k (out _ _ _) c = c
clear-beyond k (skip _ _)  c = c
clear-beyond k (end _)     c = c
clear-beyond k hush        c = tt

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
At P (end h)     = P true h
At P hush        = ⊤

-- What a lane, the outer and the pool would show first in the merge.
LaneAt : ∀ {A B : Set} → (Bool → Pos → Set) → List A → Events B → Set
LaneAt P qs      (out h _ _) = P true h
LaneAt P qs      (skip h _)  = P false h
LaneAt P []      (end c)     = P true c
LaneAt P (_ ∷ _) (end c)     = P false (c ++ [ ix 0 ])
LaneAt P qs      hush        = ⊤

OuterAt : ∀ {A} → (Bool → Pos → Set) → Events A → Set
OuterAt P (out q _ _) = P false (q ++ [ ix 0 ])
OuterAt P (skip q _)  = P false q
OuterAt P (end c)     = P true c
OuterAt P hush        = ⊤

OuterAtᴹ : ∀ {A} → (Bool → Pos → Set) → Maybe (Events∞ A) → Set
OuterAtᴹ P nothing  = ⊤
OuterAtᴹ P (just e) = OuterAt P (force e)

PoolAt : (Bool → Pos → Set) → Tail → Set
PoolAt P (pin k _) = P false k
PoolAt P idle      = ⊤

-- An end shown as a step where other parts run on.
Down : (Bool → Pos → Set) → Set
Down P = ∀ h → P true h → P false h

first-lane : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) → LaneAt P qs x
           → At P (M.lane op o bs l as qs t x)
first-lane P dn op o        bs      l as      qs       t (out _ _ _) a = a
first-lane P dn op o        bs      l as      qs       t (skip _ _)  a = a
first-lane P dn op o        bs      l as      (m ∷ qs) t (end c)     a = a
first-lane P dn op nothing  []      l []      []       t (end c)     a = a
first-lane P dn op nothing  []      l (_ ∷ _) []       t (end c)     a = dn c a
first-lane P dn op nothing  (_ ∷ _) l as      []       t (end c)     a = dn c a
first-lane P dn op (just _) bs      l as      []       t (end c)     a = dn c a
first-lane P dn op o        bs      l as      qs       t hush        a = tt

first-outer : ∀ {B} P → Down P → ∀ op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) → OuterAt P x
            → At P (M.outer op e ls qs t x)
first-outer P dn op e ls qs t (out q m r) a with M.admit op (q ++ [ ix 1 ]) m ls qs
... | ls′ , qs′ , d = a
first-outer P dn op e ls       qs       t (skip q r) a = a
first-outer P dn op e []       []       t (end c)    a = a
first-outer P dn op e []       (m ∷ qs) t (end c)    a = dn c a
first-outer P dn op e (l ∷ ls) qs       t (end c)    a = dn c a
first-outer P dn op e ls       qs       t hush       a = tt

first-race : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) k′ bs (l : Events∞ B) as qs t → LaneAt P qs (force l) → OuterAtᴹ P o
           → At P (M.race op o k′ bs l as qs t)
first-race P dn op nothing  k′ bs l as qs t al ao = first-lane P dn op nothing bs l as qs t (force l) al
first-race P dn op (just e) k′ bs l as qs t al ao with M.head (force e)
... | nothing = first-lane P dn op (just e) bs l as qs t (force l) al
... | just k″ with k″ <ᵖ k′
...   | true  = first-outer P dn op e (bs ++ l ∷ as) qs t (force e) ao
...   | false = first-lane P dn op (just e) bs l as qs t (force l) al

first-via : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → OuterAtᴹ P o → At P (M.viaOuter op o ls qs t)
first-via P dn op nothing  ls qs t ao = tt
first-via P dn op (just e) ls qs t ao = first-outer P dn op e ls qs t (force e) ao

first-parts : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → LaneAt P qs (force l)) ls → OuterAtᴹ P o
            → At P (M.parts op o ls qs t)
first-parts P dn op o ls qs t al ao with M.earliest ls | earliest-all (λ l → LaneAt P qs (force l)) ls al
... | none             | _             = first-via P dn op o ls qs t ao
... | found k′ bs l as | (_ , al′ , _) = first-race P dn op o k′ bs l as qs t al′ ao

first-go : ∀ {B} P → Down P → ∀ op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → All (λ l → LaneAt P qs (force l)) ls → OuterAtᴹ P o → PoolAt P t
         → At P (M.go op o ls qs t)
first-go P dn op o ls qs idle      al ao at = first-parts P dn op o ls qs idle al ao
first-go P dn op o ls qs (pin k u) al ao at with M.ahead-of k o ls
... | true  = at
... | false = first-parts P dn op o ls qs (pin k u) al ao

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

-- What a state would leave running, sorted, flat and trailing it.
Here : ∀ {A} → Events A → Tail → Set
Here x c = SortedT c × EveryT (TrailE x) c × FlatT c

mutual
  Calms : ∀ {A} → Events A → Set
  Calms (out k _ r) = EveryT (Disjoint k) (cut r) × At (Next true k) (force r) × Here (force r) (cut r) × Calm (force r)
  Calms (skip k r)  = At (Next false k) (force r) × Here (force r) (cut r) × Calm (force r)
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
next-clear k (end h)     n = proj₂ n
next-clear k hush        n = tt

calm-ordered : ∀ {A} (e : Events A) → Calm e → Ordered e
ordered (calm-ordered (out k _ r) c) = next-atop true k _ (proj₁ (proj₂ (calms c))) , calm-ordered _ (proj₂ (proj₂ (proj₂ (calms c))))
ordered (calm-ordered (skip k r)  c) = next-atop false k _ (proj₁ (calms c)) , calm-ordered _ (proj₂ (proj₂ (calms c)))
ordered (calm-ordered (end _)     c) = tt
ordered (calm-ordered hush        c) = tt

calm-steady : ∀ {A} (e : Events A) → Calm e → Steady e
steady (calm-steady (out k _ r) c) = next-past k _ (proj₁ (proj₂ (calms c))) , calm-steady _ (proj₂ (proj₂ (proj₂ (calms c))))
steady (calm-steady (skip k r)  c) = next-clear k _ (proj₁ (calms c)) , calm-steady _ (proj₂ (proj₂ (calms c)))
steady (calm-steady (end _)     c) = tt
steady (calm-steady hush        c) = tt

-- A calm run, each state leaving what trails it, trails from where it
-- does.
calm-trail : ∀ {A} (e : Events A) c → Here e c → Calm e → Trail e c
trail (calm-trail (out k _ r) c (st , et , ft) cm) = st , et , calm-trail (force r) (cut r) (proj₁ (proj₂ (proj₂ (calms cm)))) (proj₂ (proj₂ (proj₂ (calms cm)))) , proj₁ (calms cm)
trail (calm-trail (skip k r)  c (st , et , ft) cm) = st , et , calm-trail (force r) (cut r) (proj₁ (proj₂ (calms cm))) (proj₂ (proj₂ (calms cm)))
trail (calm-trail (end _)     c (st , et , ft) cm) = st , et , tt
trail (calm-trail hush        c (st , et , ft) cm) = st , et , tt
trailᶠ (calm-trail e c (st , et , ft) cm) = ft

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
  first-go (Next v k) dn op o ls qs t (lanes-next v k qs ls al nl) (outerᴹ-next v k o ao no) (pool-next v k t at np)
  where strict-down : ∀ v {h} → Strict v true k h → Strict v false k h
        strict-down true  s = s
        strict-down false s = tt
        dn : Down (Next v k)
        dn h (a , s , x) = a , strict-down v s , x

-- Strictly past `k`, and not inside it.
Aloof : Pos → Pos → Set
Aloof k h = k <ᵖ h ≡ true × ¬ Ext k h

clean-of : ∀ v v′ {k h} → Aloof k h → Clean v k v′ h
clean-of true  v′    a = a
clean-of false true  a = a
clean-of false false a = tt , proj₂ a

-- Keyed apart from what keys `k`, and no earlier: away from `k`.
apart-clean : ∀ r k h → Owned r k → ¬ Owned r h → h <ᵖ k ≡ false → Aloof k h
apart-clean r k h ok nh a with <ᵖ-split k h a
... | inj₁ kh   = kh , λ x → nh (owned-trans r k h ok (owned-ext x))
... | inj₂ refl = ⊥-elim (nh ok)

-- Aloof from `k`, so is the step just past `c`.
past-step : ∀ k c → Aloof k c → Aloof k (c ++ [ ix 0 ])
past-step k c (kc , nx) = <ᵖ-trans k c (c ++ [ ix 0 ]) kc (<ᵖ-below c []) , λ x → go (ext-snoc k c (ix 0) x)
  where go : Ext k c ⊎ k ≡ c → ⊥
        go (inj₁ e)    = nx e
        go (inj₂ refl) = t≢f (trans (sym kc) (<ᵖ-irrefl k))

-- Aloof from `c`, so from the step just past it.
ext-up : ∀ c x h → Ext (c ++ [ x ]) h → Ext c h
ext-up c x h e = subst (Ext c) (sym (trans (proj₂ (proj₂ (ext-eq e))) (++-assoc c [ x ] _))) (ext x _)

step-past : ∀ c h → Aloof c h → Aloof (c ++ [ ix 0 ]) h
step-past c h (ch , nx) with <ᵖ-split (c ++ [ ix 0 ]) h (<ᵖ-step c h ch)
... | inj₁ sh   = sh , λ e → nx (ext-up c (ix 0) h e)
... | inj₂ refl = ⊥-elim (nx (ext (ix 0) []))

-- What a lane or the outer shows first, read off its own first.
away-lane : ∀ {A B : Set} k (qs : List A) (x : Events B) → At (λ _ → Aloof k) x → LaneAt (λ _ → Aloof k) qs x
away-lane k qs      (out h _ _) a = a
away-lane k qs      (skip h _)  a = a
away-lane k []      (end c)     a = a
away-lane k (_ ∷ _) (end c)     a = past-step k c a
away-lane k qs      hush        a = tt

away-outer : ∀ {A} k (x : Events A) → At (λ _ → Aloof k) x → OuterAt (λ _ → Aloof k) x
away-outer k (out q _ _) a = past-step k q a
away-outer k (skip q _)  a = a
away-outer k (end c)     a = a
away-outer k hush        a = tt

at-apart : ∀ {A} r k (x : Events A) → Owned r k → Atop k x → Every (λ h → ¬ Owned r h) x → At (λ _ → Aloof k) x
at-apart r k (out h _ _) ok a al = apart-clean r k h ok (proj₁ (every al)) a
at-apart r k (skip h _)  ok a al = apart-clean r k h ok (proj₁ (every al)) a
at-apart r k (end c)     ok a al = apart-clean r k c ok (every al) a
at-apart r k hush        ok a al = tt

past-at : ∀ {A} k (x : Events A) → Past k x → At (λ _ → Aloof k) x
past-at k (out h _ _) pk = pk
past-at k (skip h _)  pk = pk
past-at k (end c)     pk = pk
past-at k hush        pk = tt

pool-apart : ∀ r k t → Owned r k → AtopT k t → EveryT (λ h → ¬ Owned r h) t → PoolAt (λ _ → Aloof k) t
pool-apart r k (pin h _) ok a al = apart-clean r k h ok (proj₁ (everyᵀ al)) a
pool-apart r k idle      ok a al = tt

laneAt-map : ∀ {A B : Set} {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (qs : List A) (x : Events B) → LaneAt P qs x → LaneAt Q qs x
laneAt-map f qs      (out h _ _) a = f true h a
laneAt-map f qs      (skip h _)  a = f false h a
laneAt-map f []      (end c)     a = f true c a
laneAt-map f (_ ∷ _) (end c)     a = f false (c ++ [ ix 0 ]) a
laneAt-map f qs      hush        a = tt

outerAt-map : ∀ {A} {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (x : Events A) → OuterAt P x → OuterAt Q x
outerAt-map f (out q _ _) a = f false (q ++ [ ix 0 ]) a
outerAt-map f (skip q _)  a = f false q a
outerAt-map f (end c)     a = f true c a
outerAt-map f hush        a = tt

poolAt-map : ∀ {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (t : Tail) → PoolAt P t → PoolAt Q t
poolAt-map f (pin k _) a = f false k a
poolAt-map f idle      a = tt

poolAt-∪ : ∀ (P : Bool → Pos → Set) t u → PoolAt P t → PoolAt P u → PoolAt P (t ∪ u)
poolAt-∪ P idle      u at au = au
poolAt-∪ P (pin k r) u at au = fst (M.sooner k u) u au
  where fst : ∀ b u → PoolAt P u → PoolAt P (M.first k r u b)
        fst true  u          au = at
        fst false idle       au = at
        fst false (pin k′ u) au = au

outerᴹ-map : ∀ {A} {P Q : Bool → Pos → Set} → (∀ v h → P v h → Q v h) → (o : Maybe (Events∞ A)) → OuterAtᴹ P o → OuterAtᴹ Q o
outerᴹ-map f nothing  a = tt
outerᴹ-map f (just e) a = outerAt-map f (force e) a

-- Past `k`, keying nothing under it: aloof from it.
at-beyond : ∀ {A} k (x : Events A) → Beyond k x → Every (λ h → ¬ Owned k h) x → At (λ _ → Aloof k) x
at-beyond k (out h _ _) b al = b , λ e → proj₁ (every al) (owned-ext e)
at-beyond k (skip h _)  b al = b , λ e → proj₁ (every al) (owned-ext e)
at-beyond k (end c)     b al = b , λ e → every al (owned-ext e)
at-beyond k hush        b al = tt

-- Apart from where a lane admitted at `x` keys, a position is spread
-- from `x`; and so is one apart from `x`.
sp-of : ∀ x y → Disjoint y (x ++ [ ix 1 ]) → Sp x y
sp-of x y d = disjoint-swap _ _ (apart-mark (x ++ [ ix 1 ]) y (ix 1) (ix-mark 1) (disjoint-swap _ _ d)) , proj₁ d

sp-apart : ∀ x y → Disjoint y x → Sp x y
sp-apart x y d = sp-of x y (apart-mark y x (ix 1) (ix-mark 1) d)

-- Keyed under a root apart from where `x`'s lane keys, and over
-- nothing of it.
sp-under : ∀ x j y → Owned j y → Disjoint j (x ++ [ ix 1 ]) → ¬ Owned (x ++ [ ix 1 ]) y → Sp x y
sp-under x j y o d n = sp-of x y ((λ o′ → proj₁ d (owned-trans j y _ o o′)) , n)

-- The step just past a position spread from `x` is.
sp-step : ∀ x h → Sp x h → Sp x (h ++ [ ix 0 ])
sp-step x h (d , n) = sp-of x (h ++ [ ix 0 ]) (fwd , bwd)
  where
    X = x ++ [ ix 1 ]
    fwd : ¬ Owned (h ++ [ ix 0 ]) X
    fwd o = n (owned-trans h (h ++ [ ix 0 ]) X (inj₁ (prefix-++ h [ ix 0 ])) o)
    bwd : ¬ Owned X (h ++ [ ix 0 ])
    bwd (inj₁ q) with prefix-split X h (ix 0) q
    ... | inj₁ q′ = proj₂ d (inj₁ (prefix-trans X h (h ++ [ ix 1 ]) q′ (prefix-++ h [ ix 1 ])))
    ... | inj₂ eq with snoc-inj x h eq
    ...   | _ , ()
    bwd (inj₂ t) = proj₂ d (inj₂ (tagged-++ X h [ ix 1 ] (tagged-mark X h (ix 0) (ix-mark 0) t)))

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
  Fit j l = Ordered (force l) × Atop j (force l) × Steady (force l) × Trailing l × Every∞ (Under j) l × Spread (force l)

  Gen : ∀ {B} → MonotonicList B → Set
  Gen m = ∀ j → Ok j → Fit j (M.enter m j)

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
      spr : Spread x

  Static : ∀ {B} → Pos → Events∞ B → Set
  Static r l = Lane r (force l) (cut l)

  fresh : ∀ {B} j (l : Events∞ B) → Fit j l → Ok j → Static j l
  fresh j l (o , _ , sd , t , (kx , kc) , sp) okj = lane o sd t kx kc okj sp

  lane-out : ∀ {B r k b c} {w : Events∞ B} → Lane r (out k b w) c → Static r w
  lane-out st = lane (proj₂ (ordered (Lane.ord st))) (proj₂ (steady (Lane.std st))) (proj₁ (proj₂ (proj₂ (trail (Lane.trl st)))))
                     (proj₁ (proj₂ (every (Lane.kx st)))) (proj₂ (proj₂ (every (Lane.kx st)))) (Lane.ok st) (proj₂ (spread (Lane.spr st)))

  lane-skip : ∀ {B r k c} {w : Events∞ B} → Lane r (skip k w) c → Static r w
  lane-skip st = lane (proj₂ (ordered (Lane.ord st))) (proj₂ (steady (Lane.std st))) (proj₂ (proj₂ (trail (Lane.trl st))))
                      (proj₁ (proj₂ (every (Lane.kx st)))) (proj₂ (proj₂ (every (Lane.kx st)))) (Lane.ok st) (spread (Lane.spr st))

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
      spn : Values Gen x

  Heldᴹ : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Set
  Heldᴹ nothing  = ⊤
  Heldᴹ (just e) = Outer (force e) (cut e)

  outer-out : ∀ {B q m c} {w : Events∞ (MonotonicList B)} → Outer (out q m w) c → Outer (force w) (cut w)
  outer-out h = outer (proj₂ (ordered (Outer.ord h))) (proj₂ (steady (Outer.std h))) (proj₁ (proj₂ (proj₂ (trail (Outer.trl h)))))
                      (proj₂ (spread (Outer.spr h))) (proj₁ (proj₂ (every (Outer.kx h)))) (proj₂ (proj₂ (every (Outer.kx h))))
                      (proj₂ (values (Outer.spn h)))

  outer-skip : ∀ {B q c} {w : Events∞ (MonotonicList B)} → Outer (skip q w) c → Outer (force w) (cut w)
  outer-skip h = outer (proj₂ (ordered (Outer.ord h))) (proj₂ (steady (Outer.std h))) (proj₂ (proj₂ (trail (Outer.trl h))))
                       (spread (Outer.spr h)) (proj₁ (proj₂ (every (Outer.kx h)))) (proj₂ (proj₂ (every (Outer.kx h))))
                       (values (Outer.spn h))

  -- Where a value at `y` subscribes its lane, apart from root `r`; and
  -- `y` itself over no root.
  D : Pos → Pos → Set
  D r y = Disjoint (y ++ [ ix 1 ]) r × ¬ Owned y r

  Aside : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Pos → Set
  Aside nothing  r = ⊤
  Aside (just e) r = Every∞ (D r) e

  aside-none : ∀ {B} rs → All (Aside {B} nothing) rs
  aside-none []       = []ᴬ
  aside-none {B} (r ∷ rs) = tt ∷ᴬ aside-none {B} rs

  -- No outer value at `k`, over it or under it, nor subscribing its
  -- lane over it.
  Free : ∀ {A} → Events A → Pos → Set
  Free x k = Every (λ y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k) x

  -- And none an outer at `x`, leaving `c` running, would show.
  FreeC : ∀ {A} → Events A → Tail → Pos → Set
  FreeC x c k = Free x k × EveryT (λ y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k) c

  FreeO : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Pos → Set
  FreeO nothing  k = ⊤
  FreeO (just e) k = FreeC (force e) (cut e) k

  -- Outer positions over no root, no one inside one before it.
  Wide : List Pos → Tail → Set
  Wide rs t = EveryT (λ k → All (λ r → ¬ Owned k r) rs × K k) t × FlatT t

  -- What ended parts left running: in order, under no root, `F` of it.
  PoolF : (Pos → Set) → List Pos → Tail → Set
  PoolF F rs t = SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × F k) t × Wide rs t

  -- And free of the outer.
  Pool : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List Pos → Tail → Set
  Pool o rs t = PoolF (FreeO o) rs t

  own-lane : ∀ r y → Owned r y → Owned r (y ++ [ ix 1 ])
  own-lane r y o = owned-trans r y (y ++ [ ix 1 ]) o (inj₁ (prefix-++ y [ ix 1 ]))

  aside-not : ∀ r y → D r y → ¬ Owned r y
  aside-not r y d o = proj₂ (proj₁ d) (own-lane r y o)

  lane-ok : ∀ y → K y → Ok (y ++ [ ix 1 ])
  lane-ok y (o , h) = owned-snoc p y (ix 1) o , headed-snoc y h

  -- An outer position over no root a lane may subscribe at is one.
  ok-apart : ∀ y r → K y → Ok r → ¬ Owned y r → Ok y
  ok-apart y r (inj₂ t , hy) okr ny = inj₂ t , hy
  ok-apart y r (inj₁ q , hy) okr ny with prefix-plus p y q
  ... | inj₁ refl = ⊥-elim (ny (beneath-owned p r (proj₁ okr)))
  ... | inj₂ q⁺   = inj₁ q⁺ , hy

  -- A step under a root is free of an outer value apart from it.
  q-pin : ∀ r k y → Ok r → Under r k → D r y → K y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k
  q-pin r k y okr (ork , _ , shy) d ky =
    shy (y ++ [ ix 1 ]) (lane-ok y ky) (proj₁ d)
    , shy y (ok-apart y r ky okr (proj₂ d)) (proj₂ d , aside-not r y d)
    , λ o → aside-not r y d (owned-trans r k y ork o)

  free : ∀ {A} r k (x : Events A) → Ok r → Under r k → Every (D r) x → Every K x → Free x k
  free r k x okr u dx kx = every-mono (λ y dk → q-pin r k y okr u (proj₁ dk) (proj₂ dk)) x (every-zip x dx kx)

  free∞ : ∀ {A} r k (e : Events∞ A) → Ok r → Under r k → Every∞ (D r) e → Every∞ K e → FreeC (force e) (cut e) k
  free∞ r k e okr u (dx , dc) (kx , kc) =
    free r k (force e) okr u dx kx , everyT-mono (λ y dk → q-pin r k y okr u (proj₁ dk) (proj₂ dk)) (cut e) (everyT-zip (cut e) dc kc)

  freeO : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) r k → Ok r → Under r k → Aside o r → Heldᴹ o → FreeO o k
  freeO nothing  r k okr u a h = tt
  freeO (just e) r k okr u a h = free∞ r k e okr u a (Outer.kx h , Outer.kc h)

  -- A step an ended lane left: under no other root, free of the outer.
  ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) r k rs → Ok r → Under r k → All (λ r′ → Ok r′ × Disjoint r r′) rs → Aside o r → Heldᴹ o
        → All (λ r′ → ¬ Owned r′ k) rs × FreeO o k
  ended o r k rs okr u oks a h = mapᴬ (λ {r′} od → proj₂ (proj₂ u) r′ (proj₁ od) (disjoint-swap r r′ (proj₂ od))) oks , freeO o r k okr u a h

  -- A step under root `r`: an outer position, over no root apart from `r`.
  under-k : ∀ r k → Ok r → Under r k → K k
  under-k r k okr u = owned-trans p r k (beneath-owned p r (proj₁ okr)) (proj₁ u) , proj₁ (proj₂ u)

  under-over : ∀ r k r′ → Under r k → Disjoint r r′ → ¬ Owned k r′
  under-over r k r′ u d o = proj₁ d (owned-trans r k r′ (proj₁ u) o)

  -- An outer position apart from root `r`: keyed with no step under it.
  disjoint-under : ∀ r a b → Ok r → K a → ¬ Owned r a → ¬ Owned a r → Under r b → Disjoint a b
  disjoint-under r a b okr ka nra nar u =
    (λ o → proj₂ (proj₂ u) a (ok-apart a r ka okr nar) (nar , nra) o)
    , (λ o → nra (owned-trans r b a (proj₁ u) o))

  apart-under : ∀ r a b → Ok r → K a → ¬ Owned r a → ¬ Owned a r → Under r b → Apart a b
  apart-under r a b okr ka nra nar u = apart-of (disjoint-under r a b okr ka nra nar u)

  -- Steps under roots apart are apart.
  disjoint-roots : ∀ {B} r a → Ok r → Under r a → {ls : List (Events∞ B)} {rs : List Pos} → Roots ls rs → All (Disjoint r) rs
                 → All (λ l → EveryT (Disjoint a) (cut l)) ls
  disjoint-roots r a okr ua []ᴿ                          []ᴬ       = []ᴬ
  disjoint-roots r a okr ua (_∷ᴿ_ {r = r′} {l = l} st R) (d ∷ᴬ ds) =
    everyT-mono (λ b ub → (λ o → proj₂ (proj₂ ub) r okr d (owned-trans r a b (proj₁ ua) o))
                         , (λ o → proj₂ (proj₂ ua) r′ (Lane.ok st) (disjoint-swap r r′ d) (owned-trans r′ b a (proj₁ ub) o)))
      (cut l) (Lane.kc st)
    ∷ᴬ disjoint-roots r a okr ua R ds

  apart-roots : ∀ {B} r a → Ok r → Under r a → {ls : List (Events∞ B)} {rs : List Pos} → Roots ls rs → All (Disjoint r) rs
              → All (λ l → EveryT (Apart a) (cut l)) ls
  apart-roots r a okr ua R ds = mapᴬ (λ {l} → everyT-mono (λ b → apart-of) (cut l)) (disjoint-roots r a okr ua R ds)

  -- A pool's next steps.
  pool-later : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rs k u → Pool o rs (pin k u) → Pool o rs (later u)
  pool-later o rs k u (st , et , ew , ef) = proj₂ (sortedᵀ st) , proj₂ (everyᵀ et) , proj₂ (everyᵀ ew) , proj₂ (flatᵀ ef)

  -- Past an outer skip.
  pool-oskip : ∀ {B} q (w : Events∞ (MonotonicList B)) c t rs → PoolF (FreeC (skip q w) c) rs t → Pool (just w) rs t
  pool-oskip q w c t rs (st , et , wd) = st , everyT-mono (λ k af → proj₁ af , proj₂ (every (proj₁ (proj₂ af)))) t et , wd

  -- A lane ending under root `r` leaves its cut to the pool.
  pool-ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rbs r ras t {x : Events B} c → Lane r x c
             → All (λ r′ → Ok r′ × Disjoint r r′) (rbs ++ ras) → Aside o r → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Pool o (rbs ++ ras) (t ∪ c)
  pool-ended o rbs r ras t c st oks a h (sp , ep , ew , ef) =
    sortedT-∪ t c sp (proj₁ (trail (Lane.trl st)))
    , everyT-∪ t c (everyT-mono (λ k af → proj₂ (all-pick rbs ras (proj₁ af)) , proj₂ af) t ep)
        (everyT-mono (λ k u → ended o r k (rbs ++ ras) (Lane.ok st) u oks a h) c (Lane.kc st))
    , everyT-∪ t c (everyT-mono (λ k w → proj₂ (all-pick rbs ras (proj₁ w)) , proj₂ w) t ew)
        (everyT-mono (λ k u → mapᴬ (λ {r′} od → under-over r k r′ u (proj₂ od)) oks , under-k r k (Lane.ok st) u) c (Lane.kc st))
    , flatT-∪ t c ef (trailᶠ (Lane.trl st))
        (everyT-mono (λ a ia → everyT-mono (λ b u → apart-under r a b (Lane.ok st) (proj₂ (proj₁ ia))
                                                      (proj₁ (all-pick rbs ras (proj₁ (proj₂ ia)))) (proj₁ (all-pick rbs ras (proj₁ (proj₁ ia)))) u)
                                    c (Lane.kc st))
          t (everyT-zip t ew ep))

  -- And with one queued, subscribes it just past its end.
  pool-hand : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rbs r ras t c (l : Events∞ B) → Lane r (end c) (cut l)
            → All (λ r′ → Ok r′ × Disjoint r r′) (rbs ++ ras) → Aside o r → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t
            → Pool o ((c ++ [ ix 1 ]) ∷ rbs ++ ras) (t ∪ cut l)
  pool-hand o rbs r ras t c l st oks a h pl with pool-ended o rbs r ras t (cut l) st oks a h pl
  ... | sp , ep , ew , ef =
    sp , everyT-mono (λ k z → proj₁ (proj₁ z) ∷ᴬ proj₁ (proj₂ z) , proj₂ (proj₂ z)) (t ∪ cut l) (everyT-zip (t ∪ cut l) c1 ep)
    , everyT-mono (λ k z → proj₂ (proj₁ z) ∷ᴬ proj₁ (proj₂ z) , proj₂ (proj₂ z)) (t ∪ cut l) (everyT-zip (t ∪ cut l) c1 ew) , ef
    where
      c₁  = c ++ [ ix 1 ]
      uc  = every (Lane.kx st)
      orc = proj₁ uc
      old : ∀ k → (All (λ r′ → ¬ Owned k r′) (rbs ++ r ∷ ras) × K k) × (All (λ r′ → ¬ Owned r′ k) (rbs ++ r ∷ ras) × FreeO o k)
          → ¬ Owned c₁ k × ¬ Owned k c₁
      old k ((nk , kk) , (nr , _)) =
        (λ o₁ → nrk (owned-trans r c₁ k (own-lane r c orc) o₁))
        , proj₁ (apart-mark k c (ix 1) (ix-mark 1) (proj₂ (proj₂ uc) k (ok-apart k r kk (Lane.ok st) nkr) (nkr , nrk) , λ o₁ → nrk (owned-trans r c k orc o₁)))
        where nrk = proj₁ (all-pick rbs ras nr)
              nkr = proj₁ (all-pick rbs ras nk)
      c1 : EveryT (λ k → ¬ Owned c₁ k × ¬ Owned k c₁) (t ∪ cut l)
      c1 = everyT-∪ t (cut l) (everyT-mono old t (everyT-zip t (proj₁ (proj₂ (proj₂ pl))) (proj₁ (proj₂ pl))))
             (everyT-mono (λ k tr → proj₁ (proj₂ tr)) (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))))

  -- A lane dropped past an outer value at `q` leaves nothing before the
  -- step the value shows.
  drop-atop : ∀ {B} r q (x : Events B) c → Lane r x c → Beyond q x → D r q → AtopT (q ++ [ ix 0 ]) c
  drop-atop r q x idle      st b d = tt
  drop-atop r q x (pin k u) st b d = go x b (proj₁ (everyᵀ (proj₁ (proj₂ (trail (Lane.trl st)))))) (proj₁ (everyᵀ (Lane.kc st)))
    where
      go : ∀ x → Beyond q x → TrailE x k → Under r k → k <ᵖ (q ++ [ ix 0 ]) ≡ false
      go (out n _ _) b tr          u = <ᵖ-step q k (still q n k b (proj₁ tr))
      go (skip n _)  b (inj₁ tr)   u = <ᵖ-step q k (still q n k b tr)
      go (skip n _)  b (inj₂ m) u with k <ᵖ q in kq
      ... | true  = ⊥-elim (aside-not r q d (owned-trans r k q (proj₁ u) (inj₁ (marks-between q m kq b))))
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
             → All (λ r → Every (D r) (out q m w)) rs → Ok (q ++ [ ix 1 ]) → Every∞ K w
             → All (λ l → EveryT (λ k → All (λ r → ¬ Owned r k) [ q ++ [ ix 1 ] ] × FreeC (force w) (cut w) k) (cut l)) ls
  drops-free q m w []       []ᴿ       []ᴬ       okq kw = []ᴬ
  drops-free q m w (l ∷ ls) (_∷ᴿ_ {r = r} st R) (a ∷ᴬ as) okq kw =
    everyT-mono (λ k u → proj₂ (proj₂ u) (q ++ [ ix 1 ]) okq (proj₁ (proj₁ (every a))) ∷ᴬ []ᴬ , free∞ r k w (Lane.ok st) u (proj₂ (every a)) kw)
      (cut l) (Lane.kc st)
    ∷ᴬ drops-free q m w ls R as okq kw

  -- And over no root where the value subscribes its lane, outer positions.
  drops-wide : ∀ {B} q (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) {rs} → Roots ls rs
             → All (λ r → Every (D r) (out q m w)) rs
             → All (λ l → EveryT (λ k → All (λ r → ¬ Owned k r) [ q ++ [ ix 1 ] ] × K k) (cut l)) ls
  drops-wide q m w []       []ᴿ       []ᴬ       = []ᴬ
  drops-wide q m w (l ∷ ls) (_∷ᴿ_ {r = r} st R) (a ∷ᴬ as) =
    everyT-mono (λ k u → (λ o → proj₂ (proj₁ (proj₁ (every a))) (owned-trans r k (q ++ [ ix 1 ]) (proj₁ u) o)) ∷ᴬ []ᴬ , under-k r k (Lane.ok st) u)
      (cut l) (Lane.kc st)
    ∷ᴬ drops-wide q m w ls R as

  -- No step a dropped lane leaves inside another's.
  drops-flat : ∀ {B} (ls : List (Events∞ B)) {rs} → Roots ls rs → Parted rs → FlatT (M.cuts ls)
  drops-flat []       []ᴿ       pt        = flatT-idle
  drops-flat (l ∷ ls) (_∷ᴿ_ {r = r} st R) (ds , pt) =
    flatT-∪ (cut l) (M.cuts ls) (trailᶠ (Lane.trl st)) (drops-flat ls R pt)
      (everyT-mono (λ a u → cuts-every ls (apart-roots r a (Lane.ok st) u R ds)) (cut l) (Lane.kc st))

  -- An outer position apart from every dropped root: keyed with nothing they leave.
  drops-disjoint : ∀ {B} a (ls : List (Events∞ B)) {rs} → Roots ls rs → K a → All (λ r → ¬ Owned r a) rs → All (λ r → ¬ Owned a r) rs
                 → All (λ l → EveryT (Disjoint a) (cut l)) ls
  drops-disjoint a []       []ᴿ       ka []ᴬ       []ᴬ       = []ᴬ
  drops-disjoint a (l ∷ ls) (_∷ᴿ_ {r = r} st R) ka (n ∷ᴬ ns) (o ∷ᴬ os) =
    everyT-mono (λ b u → disjoint-under r a b (Lane.ok st) ka n o u) (cut l) (Lane.kc st) ∷ᴬ drops-disjoint a ls R ka ns os

  drops-apart : ∀ {B} a (ls : List (Events∞ B)) {rs} → Roots ls rs → K a → All (λ r → ¬ Owned r a) rs → All (λ r → ¬ Owned a r) rs
              → All (λ l → EveryT (Apart a) (cut l)) ls
  drops-apart a ls R ka ns os = mapᴬ (λ {l} → everyT-mono (λ b → apart-of) (cut l)) (drops-disjoint a ls R ka ns os)

  -- What the merge holds after an outer value's step.
  data Taken {B} (q : Pos) (w : Events∞ (MonotonicList B)) (t : Tail) : List (Events∞ B) × List (MonotonicList B) × Tail → Set where
    taken : ∀ {ls qs d rs} → Roots ls rs → Parted rs → All (Aside (just w)) rs → All (λ l → Atop (q ++ [ ix 0 ]) (force l)) ls
          → All Gen qs → Pool (just w) rs (t ∪ d) → AtopT (q ++ [ ix 0 ]) d → Taken q w t (ls , qs , d)

  module Admit {B} (q : Pos) (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (t : Tail) {c : Tail} {rs : List Pos}
               (asd : All (λ r → Every (D r) (out q m w)) rs) (gm : Gen m) (okq : Ok (q ++ [ ix 1 ]))
               (sp : Aside (just w) (q ++ [ ix 1 ])) (kw : Every∞ K w)
               (pl : PoolF (FreeC (out q m w) c) rs t) where

    q₁ = q ++ [ ix 1 ]
    q₀ = q ++ [ ix 0 ]
    fit = gm q₁ okq

    top : Atop q₀ (force (M.enter m q₁))
    top = atop-weaken q₁ q₀ _ (<ᵖ-asym q₀ q₁ (<ᵖ-part q {ix 0} {ix 1} [] [] refl)) (proj₁ (proj₂ fit))

    rest′ : All (Aside (just w)) rs
    rest′ = mapᴬ (λ a → proj₂ (every a)) asd

    -- What the pool held, each step's facts side by side.
    items : EveryT (λ k → (All (λ r → ¬ Owned k r) rs × K k) × (All (λ r → ¬ Owned r k) rs × FreeC (out q m w) c k)) t
    items = everyT-zip t (proj₁ (proj₂ (proj₂ pl))) (proj₁ (proj₂ pl))

    -- A step free of the value at `q`: over none where it subscribes its lane.
    new-over : ∀ k → Free (out q m w) k → ¬ Owned k q₁
    new-over k f = proj₁ (apart-mark k q (ix 1) (ix-mark 1) (disjoint-swap q k (proj₂ (proj₁ (every f)))))

    held : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned r k) rs → Free (out q m w) k → All (λ r → ¬ Owned r k) rs′)
         → EveryT (λ k → All (λ r → ¬ Owned r k) rs′ × FreeO (just w) k) t
    held f = everyT-mono (λ k af → f k (proj₁ af) (proj₁ (proj₂ af)) , proj₂ (every (proj₁ (proj₂ af)))) t (proj₁ (proj₂ pl))

    wide : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned k r) rs → Free (out q m w) k → All (λ r → ¬ Owned k r) rs′)
         → EveryT (λ k → All (λ r → ¬ Owned k r) rs′ × K k) t
    wide g = everyT-mono (λ k z → g k (proj₁ (proj₁ z)) (proj₁ (proj₂ (proj₂ z))) , proj₂ (proj₁ z)) t items

    keep : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned r k) rs → Free (out q m w) k → All (λ r → ¬ Owned r k) rs′)
         → (∀ k → All (λ r → ¬ Owned k r) rs → Free (out q m w) k → All (λ r → ¬ Owned k r) rs′) → Pool (just w) rs′ (t ∪ idle)
    keep f g = sortedT-∪ t idle (proj₁ pl) sortedT-idle
             , everyT-∪ t idle (held f) everyT-idle
             , everyT-∪ t idle (wide g) everyT-idle
             , flatT-∪ t idle (proj₂ (proj₂ (proj₂ pl))) flatT-idle (everyT-mono (λ _ _ → everyT-idle) t items)

    admit-new : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls
              → Taken q w t (M.enter m q₁ ∷ ls , qs , idle)
    admit-new ls qs R pt gq bl =
      taken (fresh q₁ (M.enter m q₁) fit okq ∷ᴿ R) (mapᴬ (λ a → proj₁ (proj₁ (every a))) asd , pt) (sp ∷ᴬ rest′)
            (top ∷ᴬ mapᴬ (λ {l} → beyond-step q (force l)) bl) gq (keep (λ k a f → proj₁ (proj₁ (every f)) ∷ᴬ a) (λ k a f → new-over k f ∷ᴬ a)) tt

    admit-keep : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls → Taken q w t (ls , qs , idle)
    admit-keep ls qs R pt gq bl = taken R pt rest′ (mapᴬ (λ {l} → beyond-step q (force l)) bl) gq (keep (λ k a f → a) (λ k a f → a)) tt

    admit-switch : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls → Taken q w t ([ M.enter m q₁ ] , qs , M.cuts ls)
    admit-switch ls qs R pt gq bl =
      taken (fresh q₁ (M.enter m q₁) fit okq ∷ᴿ []ᴿ) ([]ᴬ , tt) (sp ∷ᴬ []ᴬ) (top ∷ᴬ []ᴬ) gq
            ( sortedT-∪ t (M.cuts ls) (proj₁ pl) (drops-sorted ls R)
            , everyT-∪ t (M.cuts ls) (held (λ k a f → proj₁ (proj₁ (every f)) ∷ᴬ []ᴬ)) (cuts-every ls (drops-free q m w ls R asd okq kw))
            , everyT-∪ t (M.cuts ls) (wide (λ k a f → new-over k f ∷ᴬ []ᴬ)) (cuts-every ls (drops-wide q m w ls R asd))
            , flatT-∪ t (M.cuts ls) (proj₂ (proj₂ (proj₂ pl))) (drops-flat ls R pt)
                (everyT-mono (λ a z → cuts-every ls (drops-apart a ls R (proj₂ (proj₁ z)) (proj₁ (proj₂ z)) (proj₁ (proj₁ z)))) t items))
            (drops-atop q ls R bl (mapᴬ (λ a → proj₁ (every a)) asd))

  admit-ok : ∀ {B} op q (m : MonotonicList B) w t ls qs {c rs} → Roots ls rs → Parted rs → All (λ r → Every (D r) (out q m w)) rs
           → All Gen qs → Gen m → Ok (q ++ [ ix 1 ]) → Aside (just w) (q ++ [ ix 1 ]) → All (λ l → Beyond q (force l)) ls
           → Every∞ K w → PoolF (FreeC (out q m w) c) rs t
           → Taken q w t (M.admit op (q ++ [ ix 1 ]) m ls qs)
  admit-ok (M.mergeᶠ nothing)  q m w t ls       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-new q m w t asd gm okq sp kw pl ls qs R pt gq bl
  admit-ok (M.mergeᶠ (just n)) q m w t ls       qs R pt asd gq gm okq sp bl kw pl with length ls <ᵇ n
  ... | true  = Admit.admit-new q m w t asd gm okq sp kw pl ls qs R pt gq bl
  ... | false = Admit.admit-keep q m w t asd gm okq sp kw pl ls (qs ++ [ m ]) R pt (All++⁺ gq (gm ∷ᴬ []ᴬ)) bl
  admit-ok M.switchᶠ           q m w t ls       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-switch q m w t asd gm okq sp kw pl ls qs R pt gq bl
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
  hand-ok : ∀ r c l → Ok r → Under r c → Ok (c ++ [ l ])
  hand-ok r c l (br , _) (orc , hc , _) = owned-snoc p c l (owned-trans p r c (beneath-owned p r br) orc) , headed-snoc c hc

  hand-apart : ∀ r c r′ → Under r c → Ok r′ → Disjoint r r′ → Disjoint (c ++ [ ix 1 ]) r′
  hand-apart r c r′ (orc , _ , shy) ok′ d =
    disjoint-swap r′ (c ++ [ ix 1 ])
      (apart-mark r′ c (ix 1) (ix-mark 1) (shy r′ ok′ (disjoint-swap r r′ d) , λ o → proj₁ d (owned-trans r c r′ orc o)))

  hand-aside : ∀ {B} r c (o : Maybe (Events∞ (MonotonicList B))) → Ok r → Under r c → Aside o r → Heldᴹ o → Aside o (c ++ [ ix 1 ])
  hand-aside r c nothing  okr u a h = tt
  hand-aside r c (just e) okr u a h =
    every-mono one (force e) (every-zip (force e) (proj₁ a) (Outer.kx h)) , everyT-mono one (cut e) (everyT-zip (cut e) (proj₂ a) (Outer.kc h))
    where
      one : ∀ y → D r y × K y → D (c ++ [ ix 1 ]) y
      one y (d , ky) = apart-mark (y ++ [ ix 1 ]) c (ix 1) (ix-mark 1)
                         (proj₂ (proj₂ u) (y ++ [ ix 1 ]) (lane-ok y ky) (proj₁ d) , λ o → proj₂ (proj₁ d) (owned-trans r c (y ++ [ ix 1 ]) (proj₁ u) o))
                       , proj₁ (apart-mark y c (ix 1) (ix-mark 1)
                           (proj₂ (proj₂ u) y (ok-apart y r ky okr (proj₂ d)) (proj₂ d , aside-not r y d) , λ o → aside-not r y d (owned-trans r c y (proj₁ u) o)))

  mutual
    ordered-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Ordered (M.go op o ls qs t)
    ordered-go op o ls qs idle      R pt asd gq h pl = ordered-parts op o ls qs idle R pt asd gq h pl tt
    ordered-go op o ls qs (pin k u) R pt asd gq h pl with M.ahead-of k o ls in e
    ... | true  = ordered-pool op o ls qs k u e R pt asd gq h pl
    ... | false = ordered-parts op o ls qs (pin k u) R pt asd gq h pl e

    ordered-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                 → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Ordered (M.left op o ls qs k u true)
    ordered (ordered-pool op o ls qs k u {rs} e R pt asd gq h pl) =
      atop-go op o ls qs (later u) k (proj₁ (ahead-atop k o ls e)) (proj₂ (ahead-atop k o ls e)) (proj₁ (sortedᵀ (proj₁ pl)))
      , ordered-go op o ls qs (later u) R pt asd gq h (pool-later o rs k u pl)

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
                  → PoolF (FreeC x (cut e)) rs t → Lead x ls → Atopᴴ x t
                  → Ordered (M.outer op e ls qs t x)
    ordered (ordered-outer op e ls qs t (out q m w) R pt asd gq h pl ld at)
      with M.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (values (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₂ (every (Outer.kx h))) pl
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad =
      atop-go op (just w) ls′ qs′ (t ∪ d) (q ++ [ ix 0 ]) at′ (beyond-step q (force w) (past-beyond q (force w) (proj₁ (steady (Outer.std h)))))
        (atopT-∪ (q ++ [ ix 0 ]) t d (pool-step q t at (everyT-mono (λ k af eq → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af))))) (subst (Owned q) eq (inj₁ (prefix-refl q)))) t (proj₁ (proj₂ pl)))) ad)
      , ordered-go op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    ordered (ordered-outer op e ls qs t (skip q w) {rs} R pt asd gq h pl ld at) =
      atop-go op (just w) ls qs t q (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (proj₁ (ordered (Outer.ord h))) at
      , ordered-go op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h)
          (pool-oskip q w (cut e) t rs pl)
    ordered (ordered-outer op e [] [] t (end c) R pt asd gq h pl ld at) = tt
    ordered (ordered-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h pl ld at) =
      atop-go op nothing [] (m ∷ qs) (t ∪ cut e) c []ᴬ tt (outer-end-atop c e t h at)
      , ordered-go op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd pl)
    ordered (ordered-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h pl ld at) =
      atop-go op nothing (l ∷ ls) qs (t ∪ cut e) c (mapᴬ (λ {x} → beyond-atop c (force x)) ld) tt (outer-end-atop c e t h at)
      , ordered-go op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd pl)
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
    ordered (ordered-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h pl refl ab aa ao at) =
      atop-go op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) c₀
        (top ∷ᴬ clear-lanes r c (Lane.ok st) orc (roots-++ rb ra) (proj₁ pp) (All++⁺ ab aa))
        (atop-hand r c o orc ao ar)
        (atopT-∪ c₀ t (cut l)
           (pool-step c t at (everyT-mono (λ k af eq → proj₁ (all-pick rbs ras (proj₁ af)) (subst (Owned r) eq orc)) t (proj₁ (proj₂ pl))))
           (atopT-every c₀ (cut l) (λ k tr → <ᵖ-step c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
      , ordered-go op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M.enter m c₁) fit okc ∷ᴿ roots-++ rb ra)
          (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
          (hand-aside r c o (Lane.ok st) uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
          (pool-hand o rbs r ras t c l st oks ar h pl)
      where
        c₀  = c ++ [ ix 0 ]
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        orc = proj₁ uc
        okc = hand-ok r c (ix 1) (Lane.ok st) uc
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
    lane-ended op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
      atop-go op o (bs ++ as) [] (t ∪ cut l) c (All++⁺ ab aa) ao
        (atopT-∪ c t (cut l) at (atopT-every c (cut l) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
      , ordered-go op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
          (pool-ended o rbs r ras t (cut l) st oks (proj₁ (all-pick rbs ras asd)) h pl)
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

    outer-end-atop : ∀ {B} c (e : Events∞ (MonotonicList B)) t → Outer (end c) (cut e) → AtopT c t → AtopT c (t ∪ cut e)
    outer-end-atop c e t h at = atopT-∪ c t (cut e) at (atopT-every c (cut e) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Outer.trl h)))))

    outer-end-pool : ∀ {B} c (e : Events∞ (MonotonicList B)) t rs → Outer (end c) (cut e) → All (λ r → Every (D r) (end c) × EveryT (D r) (cut e)) rs
                   → PoolF (FreeC (end c) (cut e)) rs t → Pool {B} nothing rs (t ∪ cut e)
    outer-end-pool c e t rs h asd (st , et , ew , ef) =
      sortedT-∪ t (cut e) st (proj₁ (trail (Outer.trl h)))
      , everyT-∪ t (cut e) (everyT-mono (λ k af → proj₁ af , tt) t et)
          (everyT-mono (λ k a → mapᴬ (λ {r} → aside-not r k) a , tt) (cut e) ds)
      , everyT-∪ t (cut e) ew (everyT-mono (λ k z → mapᴬ proj₂ (proj₁ z) , proj₂ z) (cut e) (everyT-zip (cut e) ds (Outer.kc h)))
      , flatT-∪ t (cut e) ef (trailᶠ (Outer.trl h))
          (everyT-mono (λ a af → everyT-mono (λ y fy → (λ x → proj₂ (proj₂ fy) (owned-ext x)) , (λ x → proj₁ (proj₂ fy) (owned-ext x))) (cut e) (proj₂ (proj₂ af))) t et)
      where ds = everyT-all rs (cut e) (mapᴬ proj₂ asd)

  -- After a pool step at `k`, nothing shows inside it: each lane's first
  -- is past it and keyed apart from it by its root, the outer's keyed
  -- clear of it, and the pool's next is not inside it, the pool flat.
  calm-pool-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
              → All (Aside o) rs → Heldᴹ o → Pool o rs (pin k u) → Obl false k o ls qs (later u)
  calm-pool-n o ls qs k u e R pt asd h (st , et , ew , ef) =
    by-lanes ls R (proj₁ (proj₁ (everyᵀ ew))) (proj₁ (proj₁ (everyᵀ et))) (clears-of o e)
    , by-outer o e (proj₂ (proj₁ (everyᵀ et)))
    , by-pool (later u) (proj₁ (flatᵀ ef))
    where
      kk = proj₂ (proj₁ (everyᵀ ew))
      clears-of : ∀ o → M.ahead-of k o ls ≡ true → M.clears k ls ≡ true
      clears-of nothing  e = e
      clears-of (just x) e with M.clear k (M.head (force x))
      ... | true = e
      by-lanes : ∀ ls {rs} → Roots ls rs → All (λ r → ¬ Owned k r) rs → All (λ r → ¬ Owned r k) rs → M.clears k ls ≡ true
            → All (λ y → LaneAt (Clean false k) qs (force y)) ls
      by-lanes [] []ᴿ []ᴬ []ᴬ c = []ᴬ
      by-lanes (y ∷ ls) (_∷ᴿ_ {r = r} sb R) (a ∷ᴬ as) (b ∷ᴬ bs) c with M.clear k (M.head (force y)) in d
      ... | true =
        laneAt-map (λ v h → clean-of false v) qs (force y)
          (away-lane k qs (force y) (at-beyond k (force y) (clear-beyond k (force y) d)
            (every-mono (λ h u → proj₂ (proj₂ u) k (ok-apart k r kk (Lane.ok sb) a) (a , b)) (force y) (Lane.kx sb))))
        ∷ᴬ by-lanes ls R as bs c
      by-apart : ∀ q → ¬ Owned k q → ¬ Ext k (q ++ [ ix 0 ])
      by-apart q nk x with ext-snoc k q (ix 0) x
      ... | inj₁ x′   = nk (owned-ext x′)
      ... | inj₂ refl = nk (inj₁ (prefix-refl k))
      by-first : ∀ {A} (x : Events A) → Beyond k x → Free x k → OuterAt (Clean false k) x
      by-first (out q _ _) b f = tt , by-apart q (proj₂ (proj₂ (proj₁ (every f))))
      by-first (skip q _)  b f = tt , λ x → proj₂ (proj₂ (proj₁ (every f))) (owned-ext x)
      by-first (end c)     b f = b , λ x → proj₂ (proj₂ (every f)) (owned-ext x)
      by-first hush        b f = tt
      by-outer : ∀ o → M.ahead-of k o ls ≡ true → FreeO o k → OuterAtᴹ (Clean false k) o
      by-outer nothing  e f = tt
      by-outer (just x) e f with M.clear k (M.head (force x)) in d
      ... | true = by-first (force x) (clear-beyond k (force x) d) (proj₁ f)
      by-pool : ∀ t → EveryT (λ h → ¬ Ext k h) t → PoolAt (Clean false k) t
      by-pool (pin _ _) a = tt , proj₁ (everyᵀ a)
      by-pool idle      a = tt

  -- Every other lane's first, keyed apart from `r` and no earlier than
  -- `k` it keys: away from `k`.
  calm-apart : ∀ {B A} r k (qs : List A) {ls : List (Events∞ B)} {rs} → Ok r → Owned r k → Roots ls rs → All (Disjoint r) rs
             → All (λ y → Atop k (force y)) ls → All (λ y → LaneAt (λ _ → Aloof k) qs (force y)) ls
  calm-apart r k qs okr ok []ᴿ                  []ᴬ       []ᴬ       = []ᴬ
  calm-apart r k qs okr ok (_∷ᴿ_ {l = y} sb R) (d ∷ᴬ ds) (a ∷ᴬ as) =
    away-lane k qs (force y) (at-apart r k (force y) ok a (every-mono (λ h u → proj₂ (proj₂ u) r okr d) (force y) (Lane.kx sb)))
    ∷ᴬ calm-apart r k qs okr ok R ds as

  -- The outer's first, keyed apart from root `r`, no earlier than `k` it keys.
  outer-apart : ∀ {B} r k (o : Maybe (Events∞ (MonotonicList B))) → Owned r k → Aside o r → Atopᴹ k o → OuterAtᴹ (λ _ → Aloof k) o
  outer-apart r k nothing  ok _ _ = tt
  outer-apart r k (just e) ok a x = away-outer k (force e) (at-apart r k (force e) ok x
    (every-mono (aside-not r) (force e) (proj₁ a)))

  -- After a lane's value at `k`, every part's next is past it and not
  -- inside it: the lane's own by its steadiness, the others keyed apart
  -- from its root.
  calm-out : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t k b w {rbs r ras}
           → Roots bs rbs → Lane r (out k b w) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
           → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
           → Obl true k o (bs ++ w ∷ as) qs t
  calm-out {B} o bs l as qs t k b w {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
    mapᴬ (λ {y} → laneAt-map cl qs (force y))
      (All++⁺ (calm-apart r k qs okr ok rb (All++⁻ˡ rbs ds) ab)
        (away-lane k qs (force w) (past-at k (force w) (proj₁ (steady (Lane.std st)))) ∷ᴬ calm-apart r k qs okr ok ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r k o ok (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-map cl t (pool-apart r k t ok at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl))))
    where
      okr = Lane.ok st
      ok  = proj₁ (proj₁ (every (Lane.kx st)))
      ds  = proj₁ (parted-pick rbs r ras pt)
      cl : ∀ v h → Aloof k h → Clean true k v h
      cl v h = clean-of true v

  -- After a lane's skip at `k`, nothing shows inside it, and a value or
  -- an end past it: the lane's own by its steadiness, an end strictly
  -- past so a queued lane's step is not inside it either; the others
  -- keyed apart from its root.
  calm-skip : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t k w {rbs r ras}
            → Roots bs rbs → Lane r (skip k w) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
            → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
            → Obl false k o (bs ++ w ∷ as) qs t
  calm-skip {B} o bs l as qs t k w {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
    All++⁺ (mapᴬ (λ {y} → laneAt-map cl qs (force y)) (calm-apart r k qs okr ok rb (All++⁻ˡ rbs ds) ab))
      (own qs (force w) (proj₁ (steady (Lane.std st)))
       ∷ᴬ mapᴬ (λ {y} → laneAt-map cl qs (force y)) (calm-apart r k qs okr ok ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r k o ok (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-map cl t (pool-apart r k t ok at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl))))
    where
      okr = Lane.ok st
      ok  = proj₁ (proj₁ (every (Lane.kx st)))
      ds  = proj₁ (parted-pick rbs r ras pt)
      cl : ∀ v h → Aloof k h → Clean false k v h
      cl v h = clean-of false v
      own : ∀ {A} (qs : List A) (x : Events B) → Clear k x → LaneAt (Clean false k) qs x
      own qs      (out h _ _) c = c
      own qs      (skip h _)  c = tt , c
      own []      (end c)     a = a
      own (_ ∷ _) (end c)     a = tt , proj₂ (past-step k c a)
      own qs      hush        c = tt

  -- After a lane's end at `c`, nothing shows inside it: what it left
  -- running trails it, the other parts keyed apart from its root.
  calm-end : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
           → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
           → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
           → Obl false c o (bs ++ as) [] (t ∪ cut l)
  calm-end {B} o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
    mapᴬ (λ {y} → laneAt-map cl [] (force y)) (All++⁺ (calm-apart r c [] okr oc rb (All++⁻ˡ rbs ds) ab) (calm-apart r c [] okr oc ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r c o oc (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-∪ (Clean false c) t (cut l)
        (poolAt-map cl t (pool-apart r c t oc at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl)))))
        (left (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))))
    where
      okr = Lane.ok st
      oc  = proj₁ (every (Lane.kx st))
      ds  = proj₁ (parted-pick rbs r ras pt)
      cl : ∀ v h → Aloof c h → Clean false c v h
      cl v h = clean-of false v
      left : ∀ u → EveryT (TrailE {B} (end c)) u → PoolAt (Clean false c) u
      left (pin k _) e = tt , proj₂ (proj₂ (proj₁ (everyᵀ e)))
      left idle      e = tt

  -- After a lane's end at `c` hands its queue on, nothing shows inside
  -- the step just past `c`: not the lane it subscribes, keyed apart from
  -- that step, not another, not what it left running.
  calm-queue : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as m qs t c {rbs r ras}
             → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
             → Gen m → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
             → Obl false (c ++ [ ix 0 ]) o (M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ cut l)
  calm-queue {B} o bs l as m qs t c {rbs} {r} {ras} rb st ra pt asd gm h pl ab aa ao at =
    laneAt-map (λ v h → clean-of false v) qs (force n) (away-lane c₀ qs (force n) first)
    ∷ᴬ mapᴬ (λ {y} → laneAt-map cl qs (force y)) (All++⁺ (calm-apart r c qs okr oc rb (All++⁻ˡ rbs ds) ab) (calm-apart r c qs okr oc ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r c o oc (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-∪ (Clean false c₀) t (cut l)
        (poolAt-map cl t (pool-apart r c t oc at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl)))))
        (left (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))))
    where
      c₀  = c ++ [ ix 0 ]
      c₁  = c ++ [ ix 1 ]
      n   = M.enter m c₁
      okr = Lane.ok st
      uc  = every (Lane.kx st)
      oc  = proj₁ uc
      ds  = proj₁ (parted-pick rbs r ras pt)
      fit = gm c₁ (hand-ok r c (ix 1) okr uc)
      d01 : Disjoint c₀ c₁
      d01 = sibling c (ix-mark _) (λ ()) , sibling c (ix-mark _) (λ ())
      first : At (λ _ → Aloof c₀) (force n)
      first = at-beyond c₀ (force n) (beyond-still c₀ c₁ (force n) (<ᵖ-part c {ix 0} {ix 1} [] [] refl) (proj₁ (proj₂ fit)))
                (every-mono (λ h u → proj₂ (proj₂ u) c₀ (hand-ok r c (ix 0) okr uc) d01) (force n) (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ fit)))))))
      cl : ∀ v h → Aloof c h → Clean false c₀ v h
      cl v h a = clean-of false v (step-past c h a)
      left : ∀ u → EveryT (TrailE {B} (end c)) u → PoolAt (Clean false c₀) u
      left (pin k _) e = clean-of false false (step-past c k (proj₁ (proj₁ (everyᵀ e)) , proj₂ (proj₂ (proj₁ (everyᵀ e)))))
      left idle      e = tt

  -- The lanes past an outer step at `q`, each keyed apart from it.
  lead-aloof : ∀ {B A} q (qs : List A) {ls : List (Events∞ B)} {rs} → K q → Roots ls rs → All (λ r → D r q) rs
             → All (λ l → Beyond q (force l)) ls → All (λ l → LaneAt (λ _ → Aloof q) qs (force l)) ls
  lead-aloof q qs kq []ᴿ                         []ᴬ       []ᴬ       = []ᴬ
  lead-aloof q qs kq (_∷ᴿ_ {r = r} {l = l} st R) (d ∷ᴬ ds) (b ∷ᴬ bs) =
    away-lane q qs (force l) (at-beyond q (force l) b
      (every-mono (λ h u → proj₂ (proj₂ u) q (ok-apart q r kq (Lane.ok st) (proj₂ d)) (proj₂ d , aside-not r q d)) (force l) (Lane.kx st)))
    ∷ᴬ lead-aloof q qs kq R ds bs

  -- Steady past a skip at `q`, the outer's next shows nothing inside it.
  outer-clear : ∀ {A} q (x : Events A) → Clear q x → OuterAt (Clean false q) x
  outer-clear q (out h _ _) c = clean-of false false (past-step q h c)
  outer-clear q (skip h _)  c = tt , c
  outer-clear q (end h)     c = c
  outer-clear q hush        c = tt

  -- The lane an outer value at `q` subscribes: away from the step it shows.
  admitted : ∀ {B A} q (m : MonotonicList B) (qs : List A) → K q → Gen m
           → LaneAt (Clean false (q ++ [ ix 0 ])) qs (force (M.enter m (q ++ [ ix 1 ])))
  admitted q m qs kq gm =
    laneAt-map (λ v h → clean-of false v) qs (force n) (away-lane q₀ qs (force n)
      (at-beyond q₀ (force n) (beyond-still q₀ q₁ (force n) (<ᵖ-part q {ix 0} {ix 1} [] [] refl) (proj₁ (proj₂ fit)))
        (every-mono (λ h u → proj₂ (proj₂ u) q₀ ok₀ d01) (force n) (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ fit)))))))))
    where
      q₀  = q ++ [ ix 0 ]
      q₁  = q ++ [ ix 1 ]
      n   = M.enter m q₁
      fit = gm q₁ (lane-ok q kq)
      ok₀ : Ok q₀
      ok₀ = owned-snoc p q (ix 0) (proj₁ kq) , headed-snoc q (proj₂ kq)
      d01 : Disjoint q₀ q₁
      d01 = sibling q (ix-mark _) (λ ()) , sibling q (ix-mark _) (λ ())

  -- The lanes an outer value at `q` keeps, past the step it shows.
  kept-lanes : ∀ {B A} q (qs : List A) {ls : List (Events∞ B)} {rs} → K q → Roots ls rs → All (λ r → D r q) rs
             → All (λ l → Beyond q (force l)) ls → All (λ l → LaneAt (Clean false (q ++ [ ix 0 ])) qs (force l)) ls
  kept-lanes q qs kq R ds bs = mapᴬ (λ {l} → laneAt-map (λ v h a → clean-of false v (step-past q h a)) qs (force l)) (lead-aloof q qs kq R ds bs)

  -- What a lane dropped past an outer value at `q` leaves: under its
  -- root, so away from the step the value shows.
  drops-clean : ∀ {B} q (ls : List (Events∞ B)) {rs} → K q → Roots ls rs → All (λ r → D r q) rs
              → All (λ l → Beyond q (force l)) ls → PoolAt (Clean false (q ++ [ ix 0 ])) (M.cuts ls)
  drops-clean q ls kq R ds bs =
    poolAt-map (λ v h → clean-of false v) (M.cuts ls)
      (pool-apart q (q ++ [ ix 0 ]) (M.cuts ls) (inj₁ (prefix-++ q [ ix 0 ])) (drops-atop q ls R bs ds) (cuts-every ls (go ls R ds)))
    where
      go : ∀ ls {rs} → Roots ls rs → All (λ r → D r q) rs → All (λ l → EveryT (λ h → ¬ Owned q h) (cut l)) ls
      go []       []ᴿ                  []ᴬ       = []ᴬ
      go (l ∷ ls) (_∷ᴿ_ {r = r} st R) (d ∷ᴬ ds) =
        everyT-mono (λ h u → proj₂ (proj₂ u) q (ok-apart q r kq (Lane.ok st) (proj₂ d)) (proj₂ d , aside-not r q d)) (cut l) (Lane.kc st)
        ∷ᴬ go ls R ds

  -- An outer value at `q`'s next, and what ended parts left, past the
  -- step it shows.
  step-outer : ∀ {B q m c} {w : Events∞ (MonotonicList B)} → Outer (out q m w) c → OuterAt (Clean false (q ++ [ ix 0 ])) (force w)
  step-outer {q = q} {w = w} h =
    outerAt-map (λ v h′ a → clean-of false v (step-past q h′ a)) (force w) (away-outer q (force w) (past-at q (force w) (proj₁ (steady (Outer.std h)))))

  step-pool : ∀ {B} q m (w : Events∞ (MonotonicList B)) t {c rs} → AtopT q t → EveryT (λ k → All (λ r → ¬ Owned r k) rs × FreeC (out q m w) c k) t
            → PoolAt (Clean false (q ++ [ ix 0 ])) t
  step-pool q m w t at et =
    poolAt-map (λ v h a → clean-of false v (step-past q h a)) t
      (pool-apart q q t (inj₁ (prefix-refl q)) at (everyT-mono (λ k af → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af)))))) t et))

  -- AFTER AN OUTER VALUE'S STEP JUST PAST `q`, NOTHING SHOWS INSIDE
  -- THAT STEP: not the lane it admits, the lanes it keeps, what it drops.
  calm-admit : ∀ {B} op (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t q m (w : Events∞ (MonotonicList B)) {rs ls′ qs′ d} → M.admit op (q ++ [ ix 1 ]) m ls qs ≡ (ls′ , qs′ , d)
             → Roots ls rs → Parted rs → All (λ r → Every (D r) (out q m w) × EveryT (D r) (cut e)) rs → All Gen qs
             → Outer (out q m w) (cut e) → PoolF (FreeC (out q m w) (cut e)) rs t
             → Lead (out q m w) ls → Atopᴴ (out q m w) t
             → Obl false (q ++ [ ix 0 ]) (just w) ls′ qs′ (t ∪ d)
  calm-admit (M.mergeᶠ nothing) e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ kept-lanes q qs (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit (M.mergeᶠ (just n)) e ls qs t q m w eq R pt asd gq h (st , et , wd) ld at with length ls <ᵇ n
  calm-admit (M.mergeᶠ (just n)) e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at | true =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ kept-lanes q qs (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit (M.mergeᶠ (just n)) e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at | false =
    kept-lanes q (qs ++ [ m ]) (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit M.switchᶠ e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ []ᴬ , step-outer h
    , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t (M.cuts ls) (step-pool q m w t at et) (drops-clean q ls (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld)
  calm-admit M.exhaustᶠ e [] qs t q m w refl []ᴿ pt asd gq h (st , et , wd) ld at =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ []ᴬ , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit M.exhaustᶠ e (l ∷ ls) qs t q m w refl R pt asd gq h (st , et , wd) ld at =
    kept-lanes q qs (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt

  -- AFTER AN OUTER SKIP AT `q`, NOTHING SHOWS INSIDE IT.
  calm-oskip : ∀ {B} (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t q (w : Events∞ (MonotonicList B)) {rs}
             → Roots ls rs → Parted rs → All (λ r → Every (D r) (skip q w) × EveryT (D r) (cut e)) rs
             → Outer (skip q w) (cut e) → PoolF (FreeC (skip q w) (cut e)) rs t
             → Lead (skip q w) ls → Atopᴴ (skip q w) t
             → Obl false q (just w) ls qs t
  calm-oskip e ls qs t q w R pt asd h (st , et , wd) ld at =
    mapᴬ (λ {l} → laneAt-map (λ v h′ → clean-of false v) qs (force l)) (lead-aloof q qs kq R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld)
    , outer-clear q (force w) (proj₁ (steady (Outer.std h)))
    , poolAt-map (λ v h′ → clean-of false v) t
        (pool-apart q q t (inj₁ (prefix-refl q)) at (everyT-mono (λ k af → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af)))))) t et))
    where kq = proj₁ (every (Outer.kx h))

  -- AFTER THE OUTER'S END AT `c`, NOTHING SHOWS INSIDE IT.
  calm-oend : ∀ {B} (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t c {rs}
            → Roots ls rs → Parted rs → All (λ r → Every {MonotonicList B} (D r) (end c) × EveryT (D r) (cut e)) rs
            → Outer {B} (end c) (cut e) → PoolF (FreeC {MonotonicList B} (end c) (cut e)) rs t
            → Lead {MonotonicList B} (end c) ls → Atopᴴ {MonotonicList B} (end c) t
            → Obl {B} false c nothing ls qs (t ∪ cut e)
  calm-oend {B} e ls qs t c R pt asd h (st , et , wd) ld at =
    mapᴬ (λ {l} → laneAt-map (λ v h′ → clean-of false v) qs (force l)) (lead-aloof c qs (every (Outer.kx h)) R (mapᴬ (λ a → every (proj₁ a)) asd) ld)
    , tt
    , poolAt-∪ (Clean false c) t (cut e)
        (poolAt-map (λ v h′ → clean-of false v) t
          (pool-apart c c t (inj₁ (prefix-refl c)) at (everyT-mono (λ k af → proj₁ (proj₂ (every (proj₁ (proj₂ af))))) t et)))
        (left (cut e) (proj₁ (proj₂ (trail (Outer.trl h)))))
    where
      left : ∀ u → EveryT (TrailE {MonotonicList B} (end c)) u → PoolAt (Clean false c) u
      left (pin k _) e = tt , proj₂ (proj₂ (proj₁ (everyᵀ e)))
      left idle      e = tt

  -- What the merge would leave running, sorted.
  sorted-whole : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t {rs} → Roots ls rs → Heldᴹ o → Pool o rs t → SortedT (M.whole o ls t)
  sorted-whole nothing  ls t R h pl = sortedT-∪ (M.cuts ls) t (drops-sorted ls R) (proj₁ pl)
  sorted-whole (just e) ls t R h pl =
    sortedT-∪ (cut e) (M.cuts ls ∪ t) (proj₁ (trail (Outer.trl h))) (sortedT-∪ (M.cuts ls) t (drops-sorted ls R) (proj₁ pl))

  -- No earlier than `k`.
  Lag : Pos → Pos → Set
  Lag k h = h <ᵖ k ≡ false

  -- A pin trailing a run whose first is no earlier than `k`, and not
  -- over `k`, is no earlier than `k`.
  lags : ∀ {A} (x : Events A) k h → TrailE x h → Atop k x → ¬ Ext h k → Lag k h
  lags (out n _ _) k h tr        at nx = ≮-trans k n h at (proj₁ tr)
  lags (skip n _)  k h (inj₁ tr) at nx = ≮-trans k n h at tr
  lags (skip n _)  k h (inj₂ m) at nx with h <ᵖ k in hk
  ... | false = refl
  ... | true  with () ← trans (sym (marks-past k m hk nx)) at
  lags (end n)     k h tr        at nx with h <ᵖ k in hk
  ... | false = refl
  ... | true  with () ← trans (sym (<ᵖ-trans n h k (proj₁ tr) hk)) at
  lags hush        k h ()        at nx

  lags-on : ∀ {A} (x : Events A) c k → EveryT (TrailE x) c → Atop k x → EveryT (λ h → ¬ Ext h k) c → EveryT (Lag k) c
  lags-on x c k tr at nx = everyT-mono (λ h a → lags x k h (proj₁ a) at (proj₂ a)) c (everyT-zip c tr nx)

  atopT-lag : ∀ k h u → AtopT h u → Lag k h → AtopT k u
  atopT-lag k h idle       a l = tt
  atopT-lag k h (pin h′ _) a l = ≮-trans k h h′ l a

  -- A sorted tail, its first no earlier than `k`: all of it.
  sorted-lag : ∀ k t → SortedT t → AtopT k t → EveryT (Lag k) t
  everyᵀ (sorted-lag k (pin h u) st a) = a , sorted-lag k (later u) (proj₂ (sortedᵀ st)) (atopT-lag k h (later u) (proj₁ (sortedᵀ st)) a)
  everyᵀ (sorted-lag k idle      st a) = tt

  lag-pin : ∀ k u → SortedT (pin k u) → EveryT (Lag k) (pin k u)
  everyᵀ (lag-pin k u st) = <ᵖ-irrefl k , sorted-lag k (later u) (proj₂ (sortedᵀ st)) (proj₁ (sortedᵀ st))

  -- No earlier than `c`: past the step just under it, or that step's own.
  lag-step : ∀ c h → Lag c h → Lag (c ++ [ ix 0 ]) h ⊎ Marks h (c ++ [ ix 0 ])
  lag-step c h l with <ᵖ-split c h l
  ... | inj₁ ch   = inj₁ (<ᵖ-step c h ch)
  ... | inj₂ refl = inj₂ shown

  owned-ix : ∀ h c i → Owned h (c ++ [ ix i ]) → Owned h c ⊎ h ≡ c ++ [ ix i ]
  owned-ix h c i (inj₁ pr) with prefix-split h c (ix i) pr
  ... | inj₁ q  = inj₁ (inj₁ q)
  ... | inj₂ eq = inj₂ eq
  owned-ix h c i (inj₂ tg) = inj₁ (inj₂ (tagged-lane h c i tg))

  -- A pin no earlier than an end at `c`, apart from `c`, trails it.
  end-trail : ∀ c h → Lag c h → ¬ Owned c h → ¬ Owned h c → c <ᵖ h ≡ true × Disjoint (c ++ [ ix 1 ]) h × ¬ Ext c h
  end-trail c h l nc nh with <ᵖ-split c h l
  ... | inj₂ refl = ⊥-elim (nc (inj₁ (prefix-refl c)))
  ... | inj₁ ch   = ch , ((λ o → nc (owned-trans c (c ++ [ ix 1 ]) h (inj₁ (prefix-++ c [ ix 1 ])) o)) , no) , λ x → nc (owned-ext x)
    where no : ¬ Owned h (c ++ [ ix 1 ])
          no o with owned-ix h c 1 o
          ... | inj₁ hc = nh hc
          ... | inj₂ eq = nc (subst (Owned c) (sym eq) (inj₁ (prefix-++ c [ ix 1 ])))

  apart-ext : ∀ r k → ¬ Owned r k → ∀ h → Owned r h → ¬ Ext h k
  apart-ext r k nr h o x = nr (owned-trans r h k o (owned-ext x))

  aside-ext : ∀ r q → D r q → ∀ h → Owned r h → ¬ Ext h q
  aside-ext r q d h o x = aside-not r q d (owned-trans r h q o (owned-ext x))

  -- Each lane's cut no earlier than `k`, its first being none, and its
  -- root keying nothing over `k`.
  lag-lanes : ∀ {B} k {ls : List (Events∞ B)} {rs} → Roots ls rs → All (λ l → Atop k (force l)) ls
            → All (λ r → ∀ h → Owned r h → ¬ Ext h k) rs → All (λ l → EveryT (Lag k) (cut l)) ls
  lag-lanes k []ᴿ []ᴬ []ᴬ = []ᴬ
  lag-lanes k {l ∷ ls} (st ∷ᴿ R) (a ∷ᴬ as) (n ∷ᴬ ns) =
    lags-on (force l) (cut l) k (proj₁ (proj₂ (trail (Lane.trl st)))) a (everyT-mono (λ h u → n h (proj₁ u)) (cut l) (Lane.kc st))
    ∷ᴬ lag-lanes k R as ns

  lag-whole : ∀ {B} {P : Pos → Set} (o : Maybe (Events∞ (MonotonicList B))) ls t → EveryT P (M.cutᴼ o) → All (λ l → EveryT P (cut l)) ls
            → EveryT P t → EveryT P (M.whole o ls t)
  lag-whole o ls t a b c = everyT-∪ (M.cutᴼ o) (M.cuts ls ∪ t) a (everyT-∪ (M.cuts ls) t (cuts-every ls b) c)

  lift-skip : ∀ k c → EveryT (Lag k) c → EveryT (λ h → h <ᵖ k ≡ false ⊎ Marks h k) c
  lift-skip k c = everyT-mono (λ _ → inj₁) c

  -- What a lane's event at `k` leaves aside: the other lanes, the outer
  -- and the pool, each no earlier than `k`.
  lag-rest : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) (bs as : List (Events∞ B)) t k {rbs r ras}
           → Roots bs rbs → Ok r → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → Heldᴹ o
           → Pool o (rbs ++ r ∷ ras) t → Under r k → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as
           → Atopᴹ k o → AtopT k t
           → All (λ l → EveryT (Lag k) (cut l)) bs × All (λ l → EveryT (Lag k) (cut l)) as × EveryT (Lag k) (M.cutᴼ o) × EveryT (Lag k) t
  lag-rest o bs as t k {rbs} {r} {ras} rb okr ra pt asd h pl u ab aa ao at =
    lag-lanes k rb ab (mapᴬ (λ {r′} n → apart-ext r′ k n) (All++⁻ˡ rbs nos))
    , lag-lanes k ra aa (mapᴬ (λ {r′} n → apart-ext r′ k n) (All++⁻ʳ rbs nos))
    , by-outer o h ao (proj₁ (all-pick rbs ras asd))
    , sorted-lag k t (proj₁ pl) at
    where
      oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ (parted-pick rbs r ras pt))
      nos : All (λ r′ → ¬ Owned r′ k) (rbs ++ ras)
      nos = mapᴬ (λ {r′} od → proj₂ (proj₂ u) r′ (proj₁ od) (disjoint-swap r r′ (proj₂ od))) oks
      by-outer : ∀ o → Heldᴹ o → Atopᴹ k o → Aside o r → EveryT (Lag k) (M.cutᴼ o)
      by-outer nothing  h ao ar = everyT-idle
      by-outer (just e) h ao ar =
        lags-on (force e) (cut e) k (proj₁ (proj₂ (trail (Outer.trl h)))) ao
          (everyT-mono (λ y a x → proj₁ (proj₂ (q-pin r k y okr u (proj₁ a) (proj₂ a))) (owned-ext x)) (cut e) (everyT-zip (cut e) (proj₂ ar) (Outer.kc h)))

  -- What a lane's value at `k` leaves aside, the other lanes, the outer
  -- and the pool, keyed with none of it.
  keyed-rest : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) (bs as : List (Events∞ B)) t k {rbs r ras}
             → Roots bs rbs → Ok r → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → Heldᴹ o
             → Pool o (rbs ++ r ∷ ras) t → Under r k
             → All (λ l → EveryT (Disjoint k) (cut l)) bs × All (λ l → EveryT (Disjoint k) (cut l)) as × EveryT (Disjoint k) (M.cutᴼ o) × EveryT (Disjoint k) t
  keyed-rest o bs as t k {rbs} {r} {ras} rb okr ra pt asd h pl u =
    disjoint-roots r k okr u rb (All++⁻ˡ rbs ds)
    , disjoint-roots r k okr u ra (All++⁻ʳ rbs ds)
    , by-outer o h (proj₁ (all-pick rbs ras asd))
    , everyT-mono (λ b z → disjoint-swap b k (disjoint-under r b k okr (proj₂ (proj₂ z)) (proj₁ (all-pick rbs ras (proj₁ (proj₁ z)))) (proj₁ (all-pick rbs ras (proj₁ (proj₂ z)))) u))
        t (everyT-zip t (proj₁ (proj₂ pl)) (proj₁ (proj₂ (proj₂ pl))))
    where
      ds = proj₁ (parted-pick rbs r ras pt)
      by-outer : ∀ o → Heldᴹ o → Aside o r → EveryT (Disjoint k) (M.cutᴼ o)
      by-outer nothing  h ar = everyT-idle
      by-outer (just e) h ar =
        everyT-mono (λ y z → disjoint-swap y k (disjoint-under r y k okr (proj₂ z) (aside-not r y (proj₁ z)) (proj₂ (proj₁ z)) u))
          (cut e) (everyT-zip (cut e) (proj₂ ar) (Outer.kc h))

  -- The pool's skip at `k`, ahead of every part.
  lag-pool : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs
           → Heldᴹ o → Pool o rs (pin k u) → EveryT (Lag k) (M.whole o ls (pin k u))
  lag-pool o ls k u e R h (st , et , wd) =
    lag-whole o ls (pin k u) (by-outer o h (proj₂ aa) (proj₂ (proj₁ (everyᵀ et))))
      (lag-lanes k R (proj₁ aa) (mapᴬ (λ {r} n → apart-ext r k n) (proj₁ (proj₁ (everyᵀ et))))) (lag-pin k u st)
    where
      aa = ahead-atop k o ls e
      by-outer : ∀ o → Heldᴹ o → Atopᴹ k o → FreeO o k → EveryT (Lag k) (M.cutᴼ o)
      by-outer nothing  h ao f = everyT-idle
      by-outer (just e) h ao f =
        lags-on (force e) (cut e) k (proj₁ (proj₂ (trail (Outer.trl h)))) ao (everyT-mono (λ y d x → proj₁ (proj₂ d) (owned-ext x)) (cut e) (proj₂ f))

  -- Nothing showing anywhere, nothing left running.
  quiet-one : ∀ {B} (x : Events B) c → M.head x ≡ nothing → EveryT (TrailE x) c → EveryT (λ _ → ⊥) c
  quiet-one (out _ _ _) c () e
  quiet-one (skip _ _)  c () e
  quiet-one (end _)     c () e
  quiet-one hush        c n  e = e

  quiet-lanes : ∀ {B} {ls : List (Events∞ B)} {rs} → Roots ls rs → All (λ l → M.head (force l) ≡ nothing) ls → All (λ l → EveryT (λ _ → ⊥) (cut l)) ls
  quiet-lanes []ᴿ []ᴬ = []ᴬ
  quiet-lanes {ls = l ∷ ls} (st ∷ᴿ R) (hl ∷ᴬ hs) = quiet-one (force l) (cut l) hl (proj₁ (proj₂ (trail (Lane.trl st)))) ∷ᴬ quiet-lanes R hs

  clears-quiet : ∀ {B} k (ls : List (Events∞ B)) → All (λ l → M.head (force l) ≡ nothing) ls → M.clears k ls ≡ true
  clears-quiet k []       []ᴬ        = refl
  clears-quiet k (l ∷ ls) (hl ∷ᴬ hs) rewrite hl = clears-quiet k ls hs

  ahead-quiet : ∀ {B} k (o : Maybe (Events∞ (MonotonicList B))) ls → M.headᴼ o ≡ nothing → All (λ l → M.head (force l) ≡ nothing) ls
              → M.ahead-of k o ls ≡ true
  ahead-quiet k o ls ho hs rewrite ho = clears-quiet k ls hs

  quiet-pool : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t → M.headᴼ o ≡ nothing → All (λ l → M.head (force l) ≡ nothing) ls
             → Behind o ls t → EveryT (λ _ → ⊥) t
  quiet-pool o ls idle      ho hs bh = everyT-idle
  quiet-pool o ls (pin k u) ho hs bh with () ← trans (sym (ahead-quiet k o ls ho hs)) bh

  mute : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t {rs} → Roots ls rs → M.headᴼ o ≡ nothing → All (λ l → M.head (force l) ≡ nothing) ls
       → Behind o ls t → EveryT (λ _ → ⊥) (M.cuts ls ∪ t)
  mute o ls t R ho hs bh = everyT-∪ (M.cuts ls) t (cuts-every ls (quiet-lanes R hs)) (quiet-pool o ls t ho hs bh)

  just≢nothing : ∀ {k : Pos} {m : Maybe Pos} → m ≡ just k → m ≡ nothing → ⊥
  just≢nothing refl ()

  -- The outer's event, the earliest: each part's cut lags it.
  trail-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs
              → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → Outer x (cut e) → PoolF (FreeC x (cut e)) rs t
              → Lead x ls → Atopᴴ x t → (M.head x ≡ nothing → EveryT (λ _ → ⊥) (M.cuts ls ∪ t))
              → EveryT (TrailE (M.outer op e ls qs t x)) (M.whole (just e) ls t)
  trail-outer op e ls qs t (out q m w) R asd h pl ld at mt with M.admit op (q ++ [ ix 1 ]) m ls qs
  ... | ls′ , qs′ , d =
    everyT-mono (λ y → lag-step q y) (M.whole (just e) ls t)
      (lag-whole (just e) ls t (everyT-mono (λ _ x → proj₁ x) (cut e) (proj₁ (proj₂ (trail (Outer.trl h)))))
        (lag-lanes q R (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (mapᴬ (λ {r} a → aside-ext r q (proj₁ (every (proj₁ a)))) asd))
        (sorted-lag q t (proj₁ pl) at))
  trail-outer op e ls qs t (skip q w) R asd h pl ld at mt =
    lag-whole (just e) ls t (proj₁ (proj₂ (trail (Outer.trl h))))
      (mapᴬ (λ {l} → lift-skip q (cut l)) (lag-lanes q R (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (mapᴬ (λ {r} a → aside-ext r q (proj₁ (every (proj₁ a)))) asd)))
      (lift-skip q t (sorted-lag q t (proj₁ pl) at))
  trail-outer op e [] [] t (end c) R asd h pl ld at mt =
    lag-whole (just e) [] t (proj₁ (proj₂ (trail (Outer.trl h)))) []ᴬ
      (everyT-mono (λ y a → end-trail c y (proj₁ a) (proj₁ (proj₂ (every (proj₁ (proj₂ (proj₂ a)))))) (proj₂ (proj₂ (every (proj₁ (proj₂ (proj₂ a)))))))
        t (everyT-zip t (sorted-lag c t (proj₁ pl) at) (proj₁ (proj₂ pl))))
  trail-outer op e [] (m ∷ qs) t (end c) R asd h pl ld at mt =
    lag-whole (just e) [] t (everyT-mono (λ y tr → inj₁ (<ᵖ-asym c y (proj₁ tr))) (cut e) (proj₁ (proj₂ (trail (Outer.trl h))))) []ᴬ
      (lift-skip c t (sorted-lag c t (proj₁ pl) at))
  trail-outer op e (l ∷ ls) qs t (end c) R asd h pl ld at mt =
    lag-whole (just e) (l ∷ ls) t (everyT-mono (λ y tr → inj₁ (<ᵖ-asym c y (proj₁ tr))) (cut e) (proj₁ (proj₂ (trail (Outer.trl h)))))
      (mapᴬ (λ {l} → lift-skip c (cut l)) (lag-lanes c R (mapᴬ (λ {l} → beyond-atop c (force l)) ld) (mapᴬ (λ {r} a → aside-ext r c (every (proj₁ a))) asd)))
      (lift-skip c t (sorted-lag c t (proj₁ pl) at))
  trail-outer op e ls qs t hush R asd h pl ld at mt = everyT-∪ (cut e) (M.cuts ls ∪ t) (proj₁ (proj₂ (trail (Outer.trl h)))) (mt refl)

  -- A lane's end at `c`: everything left running no earlier than `c`.
  lag-ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
            → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
            → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
            → EveryT (Lag c) (M.whole o (bs ++ l ∷ as) t)
  lag-ended o bs l as t c rb st ra pt asd h pl ab aa ao at =
    lag-whole o (bs ++ l ∷ as) t (proj₁ (proj₂ (proj₂ g)))
      (All++⁺ (proj₁ g) (everyT-mono (λ y tr → <ᵖ-asym c y (proj₁ tr)) (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))) ∷ᴬ proj₁ (proj₂ g)))
      (proj₂ (proj₂ (proj₂ g)))
    where g = lag-rest o bs as t c rb (Lane.ok st) ra pt asd h pl (every (Lane.kx st)) ab aa ao at

  -- A lane's event, the earliest: its own cut trails it, every other
  -- part's lags it.
  trail-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
             → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
             → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M.head x ≡ just k → All (λ y → Atop k (force y)) bs
             → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
             → EveryT (TrailE (M.lane op o bs l as qs t x)) (M.whole o (bs ++ l ∷ as) t)
  trail-lane op o bs l as qs t (out k b w) rb st ra pt asd h pl refl ab aa ao at =
    everyT-zip (M.whole o (bs ++ l ∷ as) t)
      (lag-whole o (bs ++ l ∷ as) t (proj₁ (proj₂ (proj₂ g))) (All++⁺ (proj₁ g) (everyT-mono (λ _ x → proj₁ x) (cut l) own ∷ᴬ proj₁ (proj₂ g))) (proj₂ (proj₂ (proj₂ g))))
      (lag-whole o (bs ++ l ∷ as) t (proj₁ (proj₂ (proj₂ d))) (All++⁺ (proj₁ d) (everyT-mono (λ _ x → proj₂ x) (cut l) own ∷ᴬ proj₁ (proj₂ d))) (proj₂ (proj₂ (proj₂ d))))
    where g = lag-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st))) ab aa ao at
          d = keyed-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st)))
          own = proj₁ (proj₂ (trail (Lane.trl st)))
  trail-lane op o bs l as qs t (skip k w) rb st ra pt asd h pl refl ab aa ao at =
    lag-whole o (bs ++ l ∷ as) t (lift-skip k _ (proj₁ (proj₂ (proj₂ g))))
      (All++⁺ (mapᴬ (λ {y} → lift-skip k (cut y)) (proj₁ g)) (proj₁ (proj₂ (trail (Lane.trl st))) ∷ᴬ mapᴬ (λ {y} → lift-skip k (cut y)) (proj₁ (proj₂ g))))
      (lift-skip k t (proj₂ (proj₂ (proj₂ g))))
    where g = lag-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st))) ab aa ao at
  trail-lane op o bs l as (m ∷ qs) t (end c) rb st ra pt asd h pl refl ab aa ao at =
    everyT-mono (λ y → lag-step c y) (M.whole o (bs ++ l ∷ as) t) (lag-ended o bs l as t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op nothing [] l [] [] t (end c) {r = r} []ᴿ st []ᴿ pt asd h (sp , ep , wp , fp) refl ab aa ao at =
    lag-whole nothing (l ∷ []) t everyT-idle (proj₁ (proj₂ (trail (Lane.trl st))) ∷ᴬ []ᴬ)
      (everyT-mono (λ y a → end-trail c y (proj₁ (proj₁ a)) (nc y (proj₂ (proj₁ a))) (nh y (proj₂ (proj₁ a)) (proj₂ a))) t
        (everyT-zip t (everyT-zip t (sorted-lag c t sp at) ep) wp))
    where
      u = every (Lane.kx st)
      one : ∀ {P : Pos → Set} {y} → All P (y ∷ []) → P y
      one (a ∷ᴬ []ᴬ) = a
      nc : ∀ y → All (λ r → ¬ Owned r y) (r ∷ []) × ⊤ → ¬ Owned c y
      nc y a o = one (proj₁ a) (owned-trans r c y (proj₁ u) o)
      nh : ∀ y → All (λ r → ¬ Owned r y) (r ∷ []) × ⊤ → All (λ r → ¬ Owned y r) (r ∷ []) × K y → ¬ Owned y c
      nh y a w = proj₂ (proj₂ u) y (ok-apart y r (proj₂ w) (Lane.ok st) (one (proj₁ w))) (one (proj₁ w) , one (proj₁ a))
  trail-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd h pl refl ab aa ao at =
    lift-skip c _ (lag-ended nothing [] l (a ∷ as) t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd h pl refl ab aa ao at =
    lift-skip c _ (lag-ended nothing (b ∷ bs) l as t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op (just e) bs l as [] t (end c) rb st ra pt asd h pl refl ab aa ao at =
    lift-skip c _ (lag-ended (just e) bs l as t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op o bs l as qs t hush rb st ra pt asd h pl () ab aa ao at

  trail-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
             → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
             → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Behind o (bs ++ l ∷ as) t → M.head (force l) ≡ just k
             → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as
             → EveryT (TrailE (M.race op o k bs l as qs t)) (M.whole o (bs ++ l ∷ as) t)
  trail-race op nothing  k bs l as qs t rb st ra pt asd h pl bh hk ab aa =
    trail-lane op nothing bs l as qs t (force l) rb st ra pt asd h pl hk ab aa tt
      (behind-atop k nothing (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) tt)
  trail-race op (just e) k bs l as qs t rb st ra pt asd h pl bh hk ab aa with M.head (force e) in he
  ... | nothing = trail-lane op (just e) bs l as qs t (force l) rb st ra pt asd h pl hk ab aa (atop-nothing k (force e) he)
                    (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-nothing k (force e) he))
  ... | just k′ with k′ <ᵖ k in kk
  ...   | true  = trail-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) asd h pl
                    (lead-of (force e) (bs ++ l ∷ as) he
                      (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                              (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
                    (atopᴴ (force e) t he
                      (behind-atop k′ (just e) (bs ++ l ∷ as) t bh
                        (mapᴬ (λ {x} → atop-weaken k k′ (force x) (<ᵖ-asym k′ k kk)) (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)))
                        (self-atop (force e) he)))
                    (λ n → ⊥-elim (just≢nothing he n))
  ...   | false = trail-lane op (just e) bs l as qs t (force l) rb st ra pt asd h pl hk ab aa (atop-just (force e) he kk)
                    (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-just (force e) he kk))

  trail-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → All (Aside o) rs
            → Heldᴹ o → Pool o rs t → Behind o ls t → All (λ l → M.head (force l) ≡ nothing) ls
            → EveryT (TrailE (M.viaOuter op o ls qs t)) (M.whole o ls t)
  trail-via op nothing  ls qs t R asd h pl bh hs = mute nothing ls t R refl hs bh
  trail-via op (just e) ls qs t R asd h pl bh hs with M.head (force e) in he
  ... | nothing = trail-outer op e ls qs t (force e) R asd h pl (lead-hush (force e) ls hs) (atopᴴ-nothing (force e) t he)
                    (λ _ → mute (just e) ls t R he hs bh)
  ... | just k  = trail-outer op e ls qs t (force e) R asd h pl (lead-hush (force e) ls hs)
                    (atopᴴ (force e) t he (behind-atop k (just e) ls t bh (mapᴬ (λ {l} → atop-nothing k (force l)) hs) (self-atop (force e) he)))
                    (λ n → ⊥-elim (just≢nothing he n))

  trail-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs
              → Heldᴹ o → Pool o rs t → Behind o ls t → EveryT (TrailE (M.parts op o ls qs t)) (M.whole o ls t)
  trail-parts op o ls qs t R pt asd h pl bh with M.earliest ls | earliest-picks ls
  ... | none            | hs                  = trail-via op o ls qs t R asd h pl bh hs
  ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
  ...   | split rb st ra =
    subst (λ ls → EveryT (TrailE (M.race op o k bs l as qs t)) (M.whole o ls t)) (sym eq)
      (trail-race op o k bs l as qs t rb st ra pt asd h pl (behind-at o t eq bh) hk ab aa)

  -- WHAT THE MERGE WOULD LEAVE RUNNING TRAILS WHAT IT SHOWS NEXT: the
  -- outer's cut, every lane's and what ended parts left, against the
  -- earliest part's next or the pool's skip ahead of them all.
  trail-whole : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs
              → Heldᴹ o → Pool o rs t → EveryT (TrailE (M.go op o ls qs t)) (M.whole o ls t)
  trail-whole op o ls qs idle      R pt asd h pl = trail-parts op o ls qs idle R pt asd h pl tt
  trail-whole op o ls qs (pin k u) R pt asd h pl with M.ahead-of k o ls in e
  ... | true  = lift-skip k (M.whole o ls (pin k u)) (lag-pool o ls k u e R h pl)
  ... | false = trail-parts op o ls qs (pin k u) R pt asd h pl e

  -- What the dropped lanes and the pool leave running side by side.
  flat-rest : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) (ls : List (Events∞ B)) t {rs} → Roots ls rs → Parted rs → Pool o rs t → FlatT (M.cuts ls ∪ t)
  flat-rest o ls t R pt pl =
    flatT-∪ (M.cuts ls) t (drops-flat ls R pt) (proj₂ (proj₂ (proj₂ pl)))
      (everyT-mono (λ a z → everyT-mono (λ b ab → proj₂ ab , proj₁ ab) t z) (M.cuts ls)
        (everyT-flip t (M.cuts ls)
          (everyT-mono (λ b z → cuts-every ls (drops-apart b ls R (proj₂ (proj₂ z)) (proj₁ (proj₁ z)) (proj₁ (proj₂ z))))
            t (everyT-zip t (proj₁ (proj₂ pl)) (proj₁ (proj₂ (proj₂ pl)))))))

  -- WHAT THE MERGE WOULD LEAVE RUNNING IS FLAT: no step of the outer's
  -- cut, a lane's or the pool's inside a step of another's.
  flat-whole : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t {rs} → Roots ls rs → Parted rs → All (Aside o) rs
             → Heldᴹ o → Pool o rs t → FlatT (M.whole o ls t)
  flat-whole nothing  ls t R pt asd h pl = flatT-∪ idle (M.cuts ls ∪ t) flatT-idle (flat-rest nothing ls t R pt pl) everyT-idle
  flat-whole (just e) ls t {rs} R pt asd h pl =
    flatT-∪ (cut e) (M.cuts ls ∪ t) (trailᶠ (Outer.trl h)) (flat-rest (just e) ls t R pt pl)
      (everyT-mono (λ y z → everyT-∪ (M.cuts ls) t
                     (cuts-every ls (drops-apart y ls R (proj₁ (proj₁ z)) (mapᴬ (λ {r} d → aside-not r y d) (proj₂ (proj₁ z))) (mapᴬ (λ {r} d → proj₂ d) (proj₂ (proj₁ z)))))
                     (proj₂ z))
        (cut e) (everyT-zip (cut e) (everyT-zip (cut e) (Outer.kc h) (everyT-all rs (cut e) (mapᴬ (λ {r} a → proj₂ a) asd))) op))
    where
      op : EveryT (λ y → EveryT (Apart y) t) (cut e)
      op = everyT-flip t (cut e)
             (everyT-mono (λ b af → everyT-mono (λ y fy → (λ x → proj₁ (proj₂ fy) (owned-ext x)) , (λ x → proj₂ (proj₂ fy) (owned-ext x))) (cut e) (proj₂ (proj₂ af)))
               t (proj₁ (proj₂ pl)))

  mutual
    calm-at : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Here (M.go op o ls qs t) (M.whole o ls t) × Calm (M.go op o ls qs t)
    calm-at op o ls qs t R pt asd gq h pl =
      (sorted-whole o ls t R h pl , trail-whole op o ls qs t R pt asd h pl , flat-whole o ls t R pt asd h pl) , calm-go op o ls qs t R pt asd gq h pl

    calm-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Calm (M.go op o ls qs t)
    calm-go op o ls qs idle      R pt asd gq h pl = calm-parts op o ls qs idle R pt asd gq h pl tt
    calm-go op o ls qs (pin k u) R pt asd gq h pl with M.ahead-of k o ls in e
    ... | true  = calm-pool op o ls qs k u e R pt asd gq h pl
    ... | false = calm-parts op o ls qs (pin k u) R pt asd gq h pl e

    calm-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                 → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Calm (M.left op o ls qs k u true)
    calms (calm-pool op o ls qs k u {rs} e R pt asd gq h pl) =
      next-go false k op o ls qs (later u) (proj₁ (ahead-atop k o ls e)) (proj₂ (ahead-atop k o ls e)) (proj₁ (sortedᵀ (proj₁ pl)))
        (calm-pool-n o ls qs k u e R pt asd h pl)
      , calm-at op o ls qs (later u) R pt asd gq h (pool-later o rs k u pl)

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
                  → PoolF (FreeC x (cut e)) rs t → Lead x ls → Atopᴴ x t
                  → Calm (M.outer op e ls qs t x)
    calms (calm-outer op e ls qs t (out q m w) R pt asd gq h pl ld at)
      with M.admit op (q ++ [ ix 1 ]) m ls qs in eq
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (values (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₂ (every (Outer.kx h))) pl
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad =
      next-go false (q ++ [ ix 0 ]) op (just w) ls′ qs′ (t ∪ d) at′ (beyond-step q (force w) (past-beyond q (force w) (proj₁ (steady (Outer.std h)))))
        (atopT-∪ (q ++ [ ix 0 ]) t d (pool-step q t at (everyT-mono (λ k af eq → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af))))) (subst (Owned q) eq (inj₁ (prefix-refl q)))) t (proj₁ (proj₂ pl)))) ad)
        (calm-admit op e ls qs t q m w eq R pt asd gq h pl ld at)
      , calm-at op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    calms (calm-outer op e ls qs t (skip q w) {rs} R pt asd gq h pl ld at) =
      next-go false q op (just w) ls qs t (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (proj₁ (ordered (Outer.ord h))) at
        (calm-oskip e ls qs t q w R pt asd h pl ld at)
      , calm-at op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h)
          (pool-oskip q w (cut e) t rs pl)
    calms (calm-outer op e [] [] t (end c) R pt asd gq h pl ld at) = tt
    calms (calm-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h pl ld at) =
      next-go false c op nothing [] (m ∷ qs) (t ∪ cut e) []ᴬ tt (outer-end-atop c e t h at) (calm-oend e [] (m ∷ qs) t c []ᴿ pt asd h pl ld at)
      , calm-at op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd pl)
    calms (calm-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h pl ld at) =
      next-go false c op nothing (l ∷ ls) qs (t ∪ cut e) (mapᴬ (λ {x} → beyond-atop c (force x)) ld) tt (outer-end-atop c e t h at)
        (calm-oend e (l ∷ ls) qs t c R pt asd h pl ld at)
      , calm-at op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd pl)
    calms (calm-outer op e ls qs t hush R pt asd gq h pl ld at) = tt

    calm-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                 → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M.head x ≡ just k → All (λ y → Atop k (force y)) bs
                 → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t → Calm (M.lane op o bs l as qs t x)
    calms (calm-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl ab aa ao at) =
      lag-whole o (bs ++ w ∷ as) t (proj₁ (proj₂ (proj₂ d))) (All++⁺ (proj₁ d) (proj₂ (proj₂ (proj₂ (trail (Lane.trl st)))) ∷ᴬ proj₁ (proj₂ d))) (proj₂ (proj₂ (proj₂ d)))
      , next-go true k op o (bs ++ w ∷ as) qs t (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at (calm-out o bs l as qs t k b w rb st ra pt asd h pl ab aa ao at)
      , calm-at op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
      where d = keyed-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st)))
    calms (calm-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl ab aa ao at) =
      next-go false k op o (bs ++ w ∷ as) qs t (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at (calm-skip o bs l as qs t k w rb st ra pt asd h pl ab aa ao at)
      , calm-at op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    calms (calm-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h pl refl ab aa ao at) =
      next-go false c₀ op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l)
        (top ∷ᴬ clear-lanes r c (Lane.ok st) orc (roots-++ rb ra) (proj₁ pp) (All++⁺ ab aa))
        (atop-hand r c o orc ao ar)
        (atopT-∪ c₀ t (cut l)
           (pool-step c t at (everyT-mono (λ k af eq → proj₁ (all-pick rbs ras (proj₁ af)) (subst (Owned r) eq orc)) t (proj₁ (proj₂ pl))))
           (atopT-every c₀ (cut l) (λ k tr → <ᵖ-step c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
        (calm-queue o bs l as m qs t c rb st ra pt asd gm h pl ab aa ao at)
      , calm-at op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M.enter m c₁) fit okc ∷ᴿ roots-++ rb ra)
          (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
          (hand-aside r c o (Lane.ok st) uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
          (pool-hand o rbs r ras t c l st oks ar h pl)
      where
        c₀  = c ++ [ ix 0 ]
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        orc = proj₁ uc
        okc = hand-ok r c (ix 1) (Lane.ok st) uc
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
               → At (Next false c) (M.go op o (bs ++ as) [] (t ∪ cut l)) × Here (M.go op o (bs ++ as) [] (t ∪ cut l)) (M.whole o (bs ++ as) (t ∪ cut l))
                 × Calm (M.go op o (bs ++ as) [] (t ∪ cut l))
    calm-ended op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
      next-go false c op o (bs ++ as) [] (t ∪ cut l) (All++⁺ ab aa) ao
        (atopT-∪ c t (cut l) at (atopT-every c (cut l) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
        (calm-end o bs l as t c rb st ra pt asd h pl ab aa ao at)
      , calm-at op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
          (pool-ended o rbs r ras t (cut l) st oks (proj₁ (all-pick rbs ras asd)) h pl)
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

  -- After a lane's value at `x`: what may follow it, at an outer
  -- position; and where a lane may subscribe apart from `x`'s.
  Pk : Pos → Pos → Set
  Pk x y = Sp x y × K y

  Sk : Pos → Pos → Set
  Sk x j = Ok j × Disjoint j (x ++ [ ix 1 ])

  k-step : ∀ h → K h → K (h ++ [ ix 0 ])
  k-step h (o , hh) = owned-trans p h (h ++ [ ix 0 ]) o (inj₁ (prefix-++ h [ ix 0 ])) , headed-snoc h hh

  module After (x : Pos) = Merge (Pk x) (Sk x) (λ h ph → sp-step x h (proj₁ ph) , k-step h (proj₂ ph)) (λ h ph → lane-ok h (proj₂ ph) , proj₁ (proj₁ ph))

  -- A lane subscribed apart from `x`'s keys nothing of it.
  gen-after : ∀ {B} x (m : MonotonicList B) → K x → Gen m → After.Lane x m
  gen-after x m kx gm j (okj , d) =
    every∞-mono (λ y u → sp-under x j y (proj₁ u) d (proj₂ (proj₂ u) (x ++ [ ix 1 ]) (lane-ok x kx) (disjoint-swap j _ d)) , under-k j y okj u)
      (M.enter m j) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (gm j okj))))))

  -- A step under a root apart from `r` is apart from one under `r`.
  lane-apart : ∀ r r′ x y → Ok r → Ok r′ → Under r x → Disjoint r r′ → Under r′ y → Disjoint y x
  lane-apart r r′ x y okr okr′ ux d uy =
    (λ o → proj₂ (proj₂ ux) r′ okr′ (disjoint-swap r r′ d) (owned-trans r′ y x (proj₁ uy) o))
    , (λ o → proj₂ (proj₂ uy) r okr d (owned-trans r x y (proj₁ ux) o))

  roots-after : ∀ {B} r x → Ok r → Under r x → {ls : List (Events∞ B)} {rs : List Pos} → Roots ls rs → All (Disjoint r) rs
              → All (Every∞ (Pk x)) ls
  roots-after r x okr ux []ᴿ                          []ᴬ       = []ᴬ
  roots-after r x okr ux (_∷ᴿ_ {r = r′} {l = l} st R) (d ∷ᴬ ds) =
    (every-mono one (force l) (Lane.kx st) , everyT-mono one (cut l) (Lane.kc st)) ∷ᴬ roots-after r x okr ux R ds
    where
      one : ∀ y → Under r′ y → Pk x y
      one y uy = sp-apart x y (lane-apart r r′ x y okr (Lane.ok st) ux d uy) , under-k r′ y (Lane.ok st) uy

  -- The lane's own rest, spread past its value.
  own-after : ∀ {B} r x b (w : Events∞ B) c → Lane r (out x b w) c → Every∞ (Pk x) w
  own-after r x b w c st =
    every-mono one (force w) (every-zip (force w) (proj₁ (proj₁ (spread (Lane.spr st)))) (proj₁ (proj₂ (every (Lane.kx st)))))
    , everyT-mono one (cut w) (everyT-zip (cut w) (proj₂ (proj₁ (spread (Lane.spr st)))) (proj₂ (proj₂ (every (Lane.kx st)))))
    where
      one : ∀ y → Sp x y × Under r y → Pk x y
      one y (s , u) = s , under-k r y (Lane.ok st) u

  -- The outer, apart from `x`'s root a step past it.
  outer-after : ∀ {B} r x (o : Maybe (Events∞ (MonotonicList B))) → Ok r → Under r x → Aside o r → Heldᴹ o → After.Outerᴹ x o
  outer-after r x nothing  okr ux a h = tt
  outer-after r x (just e) okr ux a h =
    After.outer-of x (force e) (every-mono one (force e) (every-zip (force e) (proj₁ a) (Outer.kx h)))
      (values-mono (λ m → gen-after x m (under-k r x okr ux)) (force e) (Outer.spn h))
    , everyT-mono one (cut e) (everyT-zip (cut e) (proj₂ a) (Outer.kc h))
    where
      one : ∀ y → D r y × K y → Pk x y
      one y (d , ky) = sp-apart x y (disjoint-under r y x okr ky (aside-not r y d) (proj₂ d) ux) , ky

  -- What ended parts left, under no root.
  pool-after : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rbs r ras t x → Ok r → Under r x → Pool o (rbs ++ r ∷ ras) t → EveryT (Pk x) t
  pool-after o rbs r ras t x okr ux pl =
    everyT-mono one t (everyT-zip t (proj₁ (proj₂ (proj₂ pl))) (proj₁ (proj₂ pl)))
    where
      one : ∀ k → (All (λ r′ → ¬ Owned k r′) (rbs ++ r ∷ ras) × K k) × (All (λ r′ → ¬ Owned r′ k) (rbs ++ r ∷ ras) × FreeO o k) → Pk x k
      one k ((nk , kk) , (nr , _)) = sp-apart x k (disjoint-under r k x okr kk (proj₁ (all-pick rbs ras nr)) (proj₁ (all-pick rbs ras nk)) ux) , kk

  -- After a lane's value at `x` under root `r`, nothing the merge shows
  -- next, nor leaves running, keys where `x`'s lane would.
  after-out : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (w : Events∞ B) as qs t {rbs r ras} x b c
            → Roots bs rbs → Lane r (out x b w) c → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
            → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t
            → Every (Sp x) (M.go op o (bs ++ w ∷ as) qs t) × EveryT (Sp x) (M.whole o (bs ++ w ∷ as) t)
  after-out op o bs w as qs t {rbs} {r} {ras} x b c rb st ra pt asd gq h pl =
    every-mono (λ _ → proj₁) _ (After.every-go x op o (bs ++ w ∷ as) qs t po pls pq pp)
    , everyT-mono (λ _ → proj₁) _ (After.everyT-whole x o (bs ++ w ∷ as) t po pls pp)
    where
      okr = Lane.ok st
      ux  = proj₁ (every (Lane.kx st))
      ds  = proj₁ (parted-pick rbs r ras pt)
      po  = outer-after r x o okr ux (proj₁ (all-pick rbs ras asd)) h
      pls = All++⁺ (roots-after r x okr ux rb (All++⁻ˡ rbs ds)) (own-after r x b w c st ∷ᴬ roots-after r x okr ux ra (All++⁻ʳ rbs ds))
      pq  = mapᴬ (λ {m} → gen-after x m (under-k r x okr ux)) gq
      pp  = pool-after o rbs r ras t x okr ux pl

  -- THE MERGE SPREADS: after each lane's value, the merge's next is
  -- keyed apart from where the value's lane would subscribe.
  mutual
    spread-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
              → Heldᴹ o → Pool o rs t → Spread (M.go op o ls qs t)
    spread-go op o ls qs idle      R pt asd gq h pl = spread-parts op o ls qs idle R pt asd gq h pl
    spread-go op o ls qs (pin k u) R pt asd gq h pl with M.ahead-of k o ls
    ... | true  = spread-pool op o ls qs k u R pt asd gq h pl
    ... | false = spread-parts op o ls qs (pin k u) R pt asd gq h pl

    spread-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → Roots ls rs → Parted rs
                → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Spread (M.left op o ls qs k u true)
    spread (spread-pool op o ls qs k u {rs} R pt asd gq h pl) = spread-go op o ls qs (later u) R pt asd gq h (pool-later o rs k u pl)

    spread-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                 → Heldᴹ o → Pool o rs t → Spread (M.parts op o ls qs t)
    spread-parts op o ls qs t R pt asd gq h pl with M.earliest ls | earliest-picks ls
    ... | none            | hs                  = spread-via op o ls qs t R pt asd gq h pl hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = spread-race op o k bs l as qs t rb st ra pt asd gq h pl hk ab aa

    spread-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → All (λ l → M.head (force l) ≡ nothing) ls → Spread (M.viaOuter op o ls qs t)
    spread-via op nothing  ls qs t R pt asd gq h pl hs = record { spread = tt }
    spread-via op (just e) ls qs t R pt asd gq h pl hs = spread-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs)

    spread-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
                → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → M.head (force l) ≡ just k
                → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as → Spread (M.race op o k bs l as qs t)
    spread-race op nothing  k bs l as qs t rb st ra pt asd gq h pl hk ab aa = spread-lane op nothing bs l as qs t (force l) rb st ra pt asd gq h pl hk
    spread-race op (just e) k bs l as qs t rb st ra pt asd gq h pl hk ab aa with M.head (force e) in he
    ... | nothing = spread-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = spread-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) pt asd gq h pl
                      (lead-of (force e) (bs ++ l ∷ as) he
                        (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                                (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
    ...   | false = spread-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk

    spread-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs → Parted rs
                 → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → All Gen qs → Outer x (cut e)
                 → PoolF (FreeC x (cut e)) rs t → Lead x ls → Spread (M.outer op e ls qs t x)
    spread (spread-outer op e ls qs t (out q m w) R pt asd gq h pl ld)
      with M.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (values (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₂ (every (Outer.kx h))) pl
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad = spread-go op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    spread (spread-outer op e ls qs t (skip q w) {rs} R pt asd gq h pl ld) =
      spread-go op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h) (pool-oskip q w (cut e) t rs pl)
    spread (spread-outer op e [] [] t (end c) R pt asd gq h pl ld) = tt
    spread (spread-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h pl ld) =
      spread-go op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd pl)
    spread (spread-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h pl ld) =
      spread-go op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd pl)
    spread (spread-outer op e ls qs t hush R pt asd gq h pl ld) = tt

    spread-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M.head x ≡ just k → Spread (M.lane op o bs l as qs t x)
    spread (spread-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl) =
      after-out op o bs w as qs t k b (cut l) rb st ra pt asd gq h pl
      , spread-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
    spread (spread-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl) =
      spread-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    spread (spread-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h pl refl) =
      spread-go op o (M.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M.enter m c₁) (gm c₁ okc) okc ∷ᴿ roots-++ rb ra)
        (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
        (hand-aside r c o (Lane.ok st) uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
        (pool-hand o rbs r ras t c l st oks ar h pl)
      where
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        okc = hand-ok r c (ix 1) (Lane.ok st) uc
        pp  = parted-pick rbs r ras pt
        ar  = proj₁ (all-pick rbs ras asd)
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)
    spread (spread-lane op nothing [] l [] [] t (end c) rb st ra pt asd gq h pl refl) = tt
    spread (spread-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd gq h pl refl) =
      lane-gone op nothing [] l (a ∷ as) t c rb st ra pt asd h pl
    spread (spread-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd gq h pl refl) =
      lane-gone op nothing (b ∷ bs) l as t c rb st ra pt asd h pl
    spread (spread-lane op (just e) bs l as [] t (end c) rb st ra pt asd gq h pl refl) =
      lane-gone op (just e) bs l as t c rb st ra pt asd h pl
    spread (spread-lane op o bs l as qs t hush rb st ra pt asd gq h pl ())

    lane-gone : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
              → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
              → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Spread (M.go op o (bs ++ as) [] (t ∪ cut l))
    lane-gone op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl =
      spread-go op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
        (pool-ended o rbs r ras t (cut l) st oks (proj₁ (all-pick rbs ras asd)) h pl)
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

-- Keyed with no step `h` keys, so with none just under it.
disjoint-snoc : ∀ h k l → (∀ x → Tagged k (x ++ [ l ]) → Tagged k x) → Disjoint h k → Disjoint (h ++ [ l ]) k
disjoint-snoc h k l tg (nh , nk) = (λ o → nh (owned-trans h (h ++ [ l ]) k (inj₁ (prefix-++ h [ l ])) o)) , down
  where down : ¬ Owned k (h ++ [ l ])
        down (inj₁ pr) with prefix-split k h l pr
        ... | inj₁ q  = nk (inj₁ q)
        ... | inj₂ eq = nh (inj₁ (subst (Prefix h) (sym eq) (prefix-++ h [ l ])))
        down (inj₂ t) = nk (inj₂ (tg h t))

-- No earlier than `h` and keyed with none of it: strictly past it.
take-ahead : ∀ h k → k <ᵖ h ≡ false → Disjoint h k → h <ᵖ k ≡ true
take-ahead h k l d with <ᵖ-split h k l
... | inj₁ hk   = hk
... | inj₂ refl = ⊥-elim (proj₁ d (inj₁ (prefix-refl h)))

-- Past `h` and keyed with none of it: past its completion under `last`.
take-end : ∀ h k → h <ᵖ k ≡ true → Disjoint h k
         → (h ++ [ last ]) <ᵖ k ≡ true × Disjoint ((h ++ [ last ]) ++ [ ix 1 ]) k × ¬ Ext (h ++ [ last ]) k
take-end h k hk d =
  M.<ᵖ-apart h k [ last ] hk (λ ys eq → proj₁ d (inj₁ (subst (Prefix h) (sym eq) (prefix-++ h ys))))
  , disjoint-snoc (h ++ [ last ]) k (ix 1) (λ x → tagged-lane k x 1) dl
  , λ x → proj₁ dl (owned-ext x)
  where dl = disjoint-snoc h k last (λ x → tagged-mark k x last last-mark) d

-- A pin trailing what comes past a value at `h`, keyed with none of `h`:
-- past `h`.
pin-past : ∀ {A} h (x : Events A) k → Past h x → TrailE x k → Disjoint h k → h <ᵖ k ≡ true
pin-past h (out n _ _) k (hn , _) (l , _)    d = still h n k hn l
pin-past h (skip n _)  k (hn , _) (inj₁ l)   d = still h n k hn l
pin-past h (skip n _)  k (hn , _) (inj₂ m) d with k <ᵖ h in kh
... | true  = ⊥-elim (proj₂ d (inj₁ (marks-between h m kh hn)))
... | false = take-ahead h k kh d
pin-past h (end n)     k (hn , _) (nk , _)   d = <ᵖ-trans h n k hn nk
pin-past h hush        k _        ()         d

-- A TAKEWHILE KEEPS ITS SOURCE'S CUTS TRAILING, its source in order and
-- steady: what was left running before the first failing value trails
-- that value moved under `ix 0`, and the completion under `last`.
mutual
  trail-take : ∀ {A} i (q : A → Bool) (x : Events A) c → Ordered x → Steady x → Trail x c → Trail (M.takeWhileᴱ i q x) c
  trail-take i q (out h a r) c o s tr = trail-taking i q h a (q a) r c o s tr
  trail-take i q (skip h r)  c o s tr = trail-skipping i q h r c o s tr
  trail-take i q (end h)     c o s tr = tr
  trail-take i q hush        c o s tr = tr

  trail-skipping : ∀ {A} i (q : A → Bool) h (r : Events∞ A) c → Ordered (skip h r) → Steady (skip h r) → Trail (skip h r) c
                 → Trail (M.takeWhileᴱ i q (skip h r)) c
  trail (trail-skipping i q h r c o s tr) =
    proj₁ (trail tr) , proj₁ (proj₂ (trail tr)) , trail-take i q (force r) (cut r) (proj₂ (ordered o)) (proj₂ (steady s)) (proj₂ (proj₂ (trail tr)))
  trailᶠ (trail-skipping i q h r c o s tr) = trailᶠ tr

  trail-taking : ∀ {A} i (q : A → Bool) h a b (r : Events∞ A) c → Ordered (out h a r) → Steady (out h a r) → Trail (out h a r) c
               → Trail (M.taking i q h a b r) c
  trail (trail-taking i q h a true r c o s tr) =
    proj₁ (trail tr) , proj₁ (proj₂ (trail tr))
    , trail-take i q (force r) (cut r) (proj₂ (ordered o)) (proj₂ (steady s)) (proj₁ (proj₂ (proj₂ (trail tr)))) , proj₂ (proj₂ (proj₂ (trail tr)))
  trail (trail-taking true q h a false r c o s tr) =
    proj₁ (trail tr)
    , everyT-mono (λ k z → <ᵖ-step h k (take-ahead h k (proj₁ z) (proj₂ z)) , disjoint-snoc h k (ix 0) (λ x → tagged-lane k x 0) (proj₂ z)) c (proj₁ (proj₂ (trail tr)))
    , ended , everyT-mono (λ k d → disjoint-snoc h k (ix 0) (λ x → tagged-lane k x 0) d) (cut r) (proj₂ nx)
    where
      nx = proj₂ (proj₂ (trail tr))
      ended : Trail (end (h ++ [ last ])) (cut r)
      trail ended = proj₁ (trail (proj₁ nx))
                  , everyT-mono (λ k z → take-end h k (pin-past h (force r) k (proj₁ (steady s)) (proj₁ z) (proj₂ z)) (proj₂ z)) (cut r)
                      (everyT-zip (cut r) (proj₁ (proj₂ (trail (proj₁ nx)))) (proj₂ nx))
                  , tt
      trailᶠ ended = trailᶠ (proj₁ nx)
  trail (trail-taking false q h a false r c o s tr) =
    proj₁ (trail tr) , everyT-mono (λ k z → take-end h k (take-ahead h k (proj₁ z) (proj₂ z)) (proj₂ z)) c (proj₁ (proj₂ (trail tr))) , tt
  trailᶠ (trail-taking i q h a b r c o s tr) = trailᶠ tr

-- A DEFER'S CUTS TRAIL ITS RUN where a tick heads it, its program's
-- subscribed just past its skip doing so: the skip leaves nothing
-- running, and past it the program's run is what it shows.
trail-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
            → Trailing (U.stateᴺ (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Trailing (U.stateᴺ (U.deferᶜ l p []) ρ)
trail (trail-defer l p ρ hp cl tr) =
  sortedT-idle , everyT-idle
  , trail-≈ S X _ _ alike (λ k → agreeᵀ (U.subscribed (Later.force l) (env-refl (U.hots ρ))) P₁) tr
  where open Deferred l p ρ hp cl
trailᶠ (trail-defer l p ρ hp cl tr) = flatT-idle

-- `P` of where `e` next shows, if anywhere.
Head : ∀ {A} → (Pos → Set) → Events A → Set
Head P (out n _ _) = P n
Head P (skip n _)  = P n
Head P (end n)     = P n
Head P hush        = ⊤

-- A run that steps.
Going : ∀ {A} → Events A → Set
Going hush = ⊥
Going _    = ⊤

------------------------------------------------------------------------
-- A tail run as events, against itself.

atopT-trans : ∀ k j t → j <ᵖ k ≡ false → AtopT j t → AtopT k t
atopT-trans k j (pin h _) jk a = ≮-trans k j h jk a
atopT-trans k j idle      jk a = tt

sorted-above : ∀ k t → SortedT t → AtopT k t → EveryT (λ j → j <ᵖ k ≡ false) t
everyᵀ (sorted-above k (pin j u) st a) = a , sorted-above k (later u) (proj₂ (sortedᵀ st)) (atopT-trans k j (later u) a (proj₁ (sortedᵀ st)))
everyᵀ (sorted-above k idle      st a) = tt

trail-tail : ∀ {A} t → SortedT t → FlatT t → Trail {A} (tailᴱ t) t
trail (trail-tail (pin k u) st ft) =
  st , record { everyᵀ = inj₁ (<ᵖ-irrefl k) , everyT-mono (λ j a → inj₁ a) (later u) (sorted-above k (later u) (proj₂ (sortedᵀ st)) (proj₁ (sortedᵀ st))) }
  , trail-tail (later u) (proj₂ (sortedᵀ st)) (proj₂ (flatᵀ ft))
trailᶠ (trail-tail (pin k u) st ft) = ft
trail (trail-tail idle st ft) = sortedT-idle , everyT-idle , tt
trailᶠ (trail-tail idle st ft) = flatT-idle

atop-tailᴱ : ∀ {A} k t → AtopT k t → Atop k (tailᴱ {A} t)
atop-tailᴱ k (pin h _) a = a
atop-tailᴱ k idle      a = tt

ordered-tail : ∀ {A} t → SortedT t → Ordered (tailᴱ {A} t)
ordered (ordered-tail (pin k u) st) = atop-tailᴱ k (later u) (proj₁ (sortedᵀ st)) , ordered-tail (later u) (proj₂ (sortedᵀ st))
ordered (ordered-tail idle      st) = tt

clear-tail : ∀ {A} k t → EveryT (λ h → ¬ Ext k h) t → Clear k (tailᴱ {A} t)
clear-tail k (pin h _) e = proj₁ (everyᵀ e)
clear-tail k idle      e = tt

steady-tail : ∀ {A} t → FlatT t → Steady (tailᴱ {A} t)
steady (steady-tail (pin k u) ft) = clear-tail k (later u) (proj₁ (flatᵀ ft)) , steady-tail (later u) (proj₂ (flatᵀ ft))
steady (steady-tail idle      ft) = tt

-- A source past its next step, from what its cut trails.
trailing-onward : ∀ {A} (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Trailing (M.onward∞ σ e)
trailing-onward σ (out _ _ s) _ tr = proj₁ (proj₂ (proj₂ (trail tr)))
trailing-onward σ (skip _ s)  _ tr = proj₂ (proj₂ (trail tr))
trailing-onward σ (end _)     _ tr = trail-tail (cut σ) (proj₁ (trail tr)) (trailᶠ tr)
trailing-onward σ hush        eq tr = subst (λ z → Trail z (cut σ)) (sym eq) tr

ordered-onward : ∀ {A} (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Ordered e → Ordered (force (M.onward∞ σ e))
ordered-onward σ (out _ _ s) _ tr o = proj₂ (ordered o)
ordered-onward σ (skip _ s)  _ tr o = proj₂ (ordered o)
ordered-onward σ (end _)     _ tr o = ordered-tail (cut σ) (proj₁ (trail tr))
ordered-onward σ hush        eq tr o = subst Ordered (sym eq) o

steady-onward : ∀ {A} (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Steady e → Steady (force (M.onward∞ σ e))
steady-onward σ (out _ _ s) _ tr st = proj₂ (steady st)
steady-onward σ (skip _ s)  _ tr st = proj₂ (steady st)
steady-onward σ (end _)     _ tr st = steady-tail (cut σ) (trailᶠ tr)
steady-onward σ hush        eq tr st = subst Steady (sym eq) st

-- Beside nothing running, a trail is its own.
trail-hushed : ∀ {B} t u (x : Events B) → EveryT (λ _ → ⊥) t → Trail x u → Trail x (t ∪ u)
trail-hushed idle      u x e tr = tr
trail-hushed (pin k _) u x e tr = ⊥-elim (proj₁ (everyᵀ e))

------------------------------------------------------------------------
-- No later step inside a pinned one.

past-on : ∀ {A} k n (x : Events A) → k <ᵖ n ≡ true → ¬ Ext k n → Past n x → Past k x
past-on k n (out h _ _) kn nx (nh , _) = <ᵖ-trans k n h kn nh , past-noext k n h kn nx (<ᵖ-asym n h nh)
past-on k n (skip h _)  kn nx (nh , _) = <ᵖ-trans k n h kn nh , past-noext k n h kn nx (<ᵖ-asym n h nh)
past-on k n (end h)     kn nx (nh , _) = <ᵖ-trans k n h kn nh , past-noext k n h kn nx (<ᵖ-asym n h nh)
past-on k n hush        kn nx p        = tt

-- A skip showing again where it stood.
Tie : ∀ {A} → Pos → Events A → Set
Tie k (skip n _) = n ≡ k
Tie k _          = ⊥

-- Past `k`'s subtree, or a skip at `k` again.
Fore : ∀ {A} → Pos → Events A → Set
Fore k e = Past k e ⊎ Tie k e

clear-fore : ∀ {A} n (x : Events A) → Clear n x → Atop n x → Fore n x
clear-fore n (out h _ _) c a = inj₁ c
clear-fore n (skip h _)  c a with <ᵖ-split n h a
... | inj₁ nh   = inj₁ (nh , c)
... | inj₂ refl = inj₂ refl
clear-fore n (end h)     c a = inj₁ c
clear-fore n hush        c a = inj₁ tt

fore-trans : ∀ {A} k n (x : Events A) → (k <ᵖ n ≡ true × ¬ Ext k n) ⊎ n ≡ k → Fore n x → Fore k x
fore-trans k n x          (inj₂ refl)       f           = f
fore-trans k n x          (inj₁ (kn , nx)) (inj₁ p)    = inj₁ (past-on k n x kn nx p)
fore-trans k n (skip h _) (inj₁ (kn , nx)) (inj₂ refl) = inj₁ (kn , nx)
fore-trans k n (out _ _ _) (inj₁ _) (inj₂ ())
fore-trans k n (end _)     (inj₁ _) (inj₂ ())
fore-trans k n hush        (inj₁ _) (inj₂ ())

fore-head : ∀ {A} k (e : Events A) → Fore k e → Head (λ h → ¬ Ext k h) e
fore-head k (out h _ _) (inj₁ p)    = proj₂ p
fore-head k (out h _ _) (inj₂ ())
fore-head k (skip h _)  (inj₁ p)    = proj₂ p
fore-head k (skip h _)  (inj₂ refl) = ext-irrefl k
fore-head k (end h)     (inj₁ p)    = proj₂ p
fore-head k (end h)     (inj₂ ())
fore-head k hush        f           = tt

------------------------------------------------------------------------
-- A SOURCE'S BURST, run on under `r`: in order, flat, and trailing
-- where the source's next step shows.

module Bursting (r : Pos) where

  -- `m` no later than where `e` next shows.
  Cue : ∀ {A} → Pos → Events A → Set
  Cue m = Head (λ h → (h ++ [ ix 0 ]) <ᵖ m ≡ false)

  cue-self : ∀ {A} (e : Events A) → Cue (M.shownAt e) e
  cue-self (out k _ _) = <ᵖ-irrefl (k ++ [ ix 0 ])
  cue-self (skip k _)  = <ᵖ-irrefl (k ++ [ ix 0 ])
  cue-self (end k)     = <ᵖ-irrefl (k ++ [ ix 0 ])
  cue-self hush        = tt

  cue-on : ∀ {A} k m (x : Events A) → (k ++ [ ix 0 ]) <ᵖ m ≡ false → Atop k x → Cue m x
  cue-on k m (out n _ _) c a = ≮-trans m (k ++ [ ix 0 ]) (n ++ [ ix 0 ]) c (M.<ᵖ-shift n k a)
  cue-on k m (skip n _)  c a = ≮-trans m (k ++ [ ix 0 ]) (n ++ [ ix 0 ]) c (M.<ᵖ-shift n k a)
  cue-on k m (end n)     c a = ≮-trans m (k ++ [ ix 0 ]) (n ++ [ ix 0 ]) c (M.<ᵖ-shift n k a)
  cue-on k m hush        c a = tt

  shown-cue : ∀ {A} m (e : Events A) → M.shownAt e <ᵖ m ≡ false → Cue m e
  shown-cue m (out _ _ _) c = c
  shown-cue m (skip _ _)  c = c
  shown-cue m (end _)     c = c
  shown-cue m hush        c = tt

  cue-shown : ∀ {A} m (e : Events A) → Going e → Cue m e → M.shownAt e <ᵖ m ≡ false
  cue-shown m (out _ _ _) g c = c
  cue-shown m (skip _ _)  g c = c
  cue-shown m (end _)     g c = c
  cue-shown m hush        () c

  every-cue : ∀ {A} m (e : Events A) → Every (λ h → (h ++ [ ix 0 ]) <ᵖ m ≡ false) e → Cue m e
  every-cue m (out _ _ _) pe = proj₁ (every pe)
  every-cue m (skip _ _)  pe = proj₁ (every pe)
  every-cue m (end _)     pe = every pe
  every-cue m hush        pe = tt

  cue-down : ∀ {A} m m′ (e : Events A) → m <ᵖ m′ ≡ false → Cue m e → Cue m′ e
  cue-down m m′ (out k _ _) mm c = ≮-trans m′ m (k ++ [ ix 0 ]) mm c
  cue-down m m′ (skip k _)  mm c = ≮-trans m′ m (k ++ [ ix 0 ]) mm c
  cue-down m m′ (end k)     mm c = ≮-trans m′ m (k ++ [ ix 0 ]) mm c
  cue-down m m′ hush        mm c = tt

  -- Past an end, what it left running shows past it.
  cue-tail : ∀ {A} m c t → (c ++ [ ix 0 ]) <ᵖ m ≡ false → EveryT (λ j → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j) t
           → Cue {A} m (tailᴱ t)
  cue-tail m c (pin j u) q e =
    ≮-trans m (c ++ [ ix 0 ]) (j ++ [ ix 0 ]) q
      (<ᵖ-asym (c ++ [ ix 0 ]) (j ++ [ ix 0 ]) (<ᵖ-trans (c ++ [ ix 0 ]) j (j ++ [ ix 0 ]) (marks-past j shown (proj₁ z) (proj₂ (proj₂ z))) (<ᵖ-below j [])))
    where z = proj₁ (everyᵀ e)
  cue-tail m c idle      q e = tt

  -- A source past its next step shows no earlier.
  cue-onward : ∀ {A} m (σ : Events∞ A) e → force σ ≡ e → Trail e (cut σ) → Ordered e → Cue m e → Cue m (force (M.onward∞ σ e))
  cue-onward m σ (out k _ s) _  tr o c = cue-on k m (force s) c (proj₁ (ordered o))
  cue-onward m σ (skip k s)  _  tr o c = cue-on k m (force s) c (proj₁ (ordered o))
  cue-onward m σ (end c)     _  tr o q = cue-tail m c (cut σ) q (proj₁ (proj₂ (trail tr)))
  cue-onward m σ hush        eq tr o c = subst (Cue m) (sym eq) c

  cue-marked : ∀ k m → (k ++ [ ix 0 ]) <ᵖ m ≡ false → Marked m k
  cue-marked k m c = marked-cue m shown c

  out-marked : ∀ k m → (k ++ [ ix 0 ]) <ᵖ m ≡ false → ∀ j → j <ᵖ k ≡ false × Disjoint k j → Marked m j
  out-marked k m c j (jk , d) = inj₁ (≮-trans m (k ++ [ ix 0 ]) j c (<ᵖ-step k j (take-ahead k j jk d)))

  skip-marked : ∀ k m → (k ++ [ ix 0 ]) <ᵖ m ≡ false → ∀ j → Marked k j → Marked m j
  skip-marked k m c j (inj₁ jk) with <ᵖ-split k j jk
  ... | inj₁ kj   = inj₁ (≮-trans m (k ++ [ ix 0 ]) j c (<ᵖ-step k j kj))
  ... | inj₂ refl = cue-marked k m c
  skip-marked k m c j (inj₂ mk) = marked-cue m (reshown mk) c

  end-marked : ∀ c m → (c ++ [ ix 0 ]) <ᵖ m ≡ false → ∀ j → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j → Marked m j
  end-marked c m q j (cj , _ , nx) = inj₁ (≮-trans m (c ++ [ ix 0 ]) j q (<ᵖ-asym (c ++ [ ix 0 ]) j (marks-past j shown cj nx)))

  mutual
    lead-run : ∀ {A} m (e : Events A) t → Trail e t → Ordered e → Cue m e → EveryT (Marked m) (M.runOn r e t)
    lead-run m (out k _ s) t tr o c =
      lead-pinned m k s t (M.inside r k) (cue-marked k m c) (proj₁ (proj₂ (proj₂ (trail tr)))) (proj₂ (ordered o))
        (cue-on k m (force s) c (proj₁ (ordered o))) (everyT-mono (out-marked k m c) t (proj₁ (proj₂ (trail tr))))
    lead-run m (skip k s)  t tr o c =
      lead-pinned m k s t (M.inside r k) (cue-marked k m c) (proj₂ (proj₂ (trail tr))) (proj₂ (ordered o))
        (cue-on k m (force s) c (proj₁ (ordered o))) (everyT-mono (skip-marked k m c) t (proj₁ (proj₂ (trail tr))))
    lead-run m (end k)     t tr o c = everyT-mono (end-marked k m c) t (proj₁ (proj₂ (trail tr)))
    lead-run m hush        t tr o c = everyT-mono (λ _ ()) t (proj₁ (proj₂ (trail tr)))

    lead-pinned : ∀ {A} m k (s : Events∞ A) t b → Marked m k → Trail (force s) (cut s) → Ordered (force s) → Cue m (force s)
                → EveryT (Marked m) t → EveryT (Marked m) (M.pinned r k s t b)
    everyᵀ (lead-pinned m k s t true  mk tr o c et) = mk , lead-run m (force s) (cut s) tr o c
    everyᵀ (lead-pinned m k s t false mk tr o c et) = everyᵀ et

  -- Every step a run has yet to show, and every step any state of it
  -- would leave running, is marked by where it next shows.
  lead-cut : ∀ {A} m (e : Events A) t → Trail e t → Cue m e → EveryT (Marked m) t
  lead-cut m (out k _ s) t tr c = everyT-mono (out-marked k m c) t (proj₁ (proj₂ (trail tr)))
  lead-cut m (skip k s)  t tr c = everyT-mono (skip-marked k m c) t (proj₁ (proj₂ (trail tr)))
  lead-cut m (end k)     t tr c = everyT-mono (end-marked k m c) t (proj₁ (proj₂ (trail tr)))
  lead-cut m hush        t tr c = everyT-mono (λ _ ()) t (proj₁ (proj₂ (trail tr)))

  lead-every : ∀ {A} m (e : Events A) t → Trail e t → Ordered e → Cue m e → Every (Marked m) e
  every (lead-every m (out k _ s) t tr o c) =
    cue-marked k m c , lead-every m (force s) (cut s) tr′ (proj₂ (ordered o)) c′ , lead-cut m (force s) (cut s) tr′ c′
    where tr′ = proj₁ (proj₂ (proj₂ (trail tr)))
          c′  = cue-on k m (force s) c (proj₁ (ordered o))
  every (lead-every m (skip k s)  t tr o c) =
    cue-marked k m c , lead-every m (force s) (cut s) tr′ (proj₂ (ordered o)) c′ , lead-cut m (force s) (cut s) tr′ c′
    where tr′ = proj₂ (proj₂ (trail tr))
          c′  = cue-on k m (force s) c (proj₁ (ordered o))
  every (lead-every m (end k)     t tr o c) = cue-marked k m c
  every (lead-every m hush        t tr o c) = tt

  lead∞ : ∀ {A} m (s : Events∞ A) → Trailing s → Ordered (force s) → Cue m (force s) → Every∞ (Marked m) s
  lead∞ m s tr o c = lead-every m (force s) (cut s) tr o c , lead-cut m (force s) (cut s) tr c

  atopT-pin : ∀ {A} k n (s : Events∞ A) t b → n <ᵖ k ≡ false → (M.inside r n ≡ false → AtopT k t) → M.inside r n ≡ b
            → AtopT k (M.pinned r n s t b)
  atopT-pin k n s t true  a f ib = a
  atopT-pin k n s t false a f ib = f ib

  skip-atop : ∀ k n → n <ᵖ k ≡ false → M.inside r k ≡ true → M.inside r n ≡ false → ∀ j → Marked n j → j <ᵖ k ≡ false
  skip-atop k n a ik nb j (inj₁ jn) = ≮-trans k n j a jn
  skip-atop k n a ik nb j (inj₂ mk) with j <ᵖ k in e
  ... | false = refl
  ... | true with () ← trans (sym (inside-prefix r k n ik (marks-under k mk e a))) nb

  -- What runs on past a pinned step comes no earlier.
  atopT-run : ∀ {A} k (e : Events A) t → Atop k e → Trail e t → M.inside r k ≡ true → AtopT k (M.runOn r e t)
  atopT-run k (out n _ s) t a tr ik =
    atopT-pin k n s t (M.inside r n) a (λ _ → atopT-every k t (λ j tj → ≮-trans k n j a (proj₁ tj)) (proj₁ (proj₂ (trail tr)))) refl
  atopT-run k (skip n s)  t a tr ik =
    atopT-pin k n s t (M.inside r n) a (λ nb → atopT-every k t (skip-atop k n a ik nb) (proj₁ (proj₂ (trail tr)))) refl
  atopT-run k (end c)     t a tr ik = atopT-every k t (λ j tj → ≮-trans k c j a (<ᵖ-asym c j (proj₁ tj))) (proj₁ (proj₂ (trail tr)))
  atopT-run k hush        t a tr ik = atopT-every k t (λ j ()) (proj₁ (proj₂ (trail tr)))

  mutual
    sorted-run : ∀ {A} (e : Events A) t → Ordered e → Trail e t → SortedT (M.runOn r e t)
    sorted-run (out n _ s) t o tr = sorted-pinned n s t (M.inside r n) refl (proj₂ (ordered o)) (proj₁ (ordered o)) (proj₁ (proj₂ (proj₂ (trail tr)))) (proj₁ (trail tr))
    sorted-run (skip n s)  t o tr = sorted-pinned n s t (M.inside r n) refl (proj₂ (ordered o)) (proj₁ (ordered o)) (proj₂ (proj₂ (trail tr))) (proj₁ (trail tr))
    sorted-run (end _)     t o tr = proj₁ (trail tr)
    sorted-run hush        t o tr = proj₁ (trail tr)

    sorted-pinned : ∀ {A} n (s : Events∞ A) t b → M.inside r n ≡ b → Ordered (force s) → Atop n (force s) → Trail (force s) (cut s)
                  → SortedT t → SortedT (M.pinned r n s t b)
    sortedᵀ (sorted-pinned n s t true  ib o a tr st) = atopT-run n (force s) (cut s) a tr ib , sorted-run (force s) (cut s) o tr
    sortedᵀ (sorted-pinned n s t false ib o a tr st) = sortedᵀ st

  out-noext : ∀ {A} k n (a : A) (s : Events∞ A) → Fore k (out n a s) → ∀ j → j <ᵖ n ≡ false × Disjoint n j → ¬ Ext k j
  out-noext k n a s (inj₁ (kn , nx)) j (jn , _) = past-noext k n j kn nx jn
  out-noext k n a s (inj₂ ()) j _

  skip-noext : ∀ {A} k n (s : Events∞ A) → Fore k (skip n s) → M.inside r k ≡ true → M.inside r n ≡ false → ∀ j → Marked n j → ¬ Ext k j
  skip-noext k n s (inj₁ (kn , nx)) ik nb j (inj₁ jn) = past-noext k n j kn nx jn
  skip-noext k n s (inj₁ (kn , nx)) ik nb j (inj₂ mk) = λ x → nx (ext-prefix x (marks-prefix mk))
  skip-noext k n s (inj₂ refl)      ik nb j _ with () ← trans (sym ik) nb

  end-noext : ∀ {A} k c → Fore {A} k (end c) → ∀ j → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j → ¬ Ext k j
  end-noext k c (inj₁ (kc , nx)) j (cj , _) = past-noext k c j kc nx (<ᵖ-asym c j cj)
  end-noext k c (inj₂ ()) j _

  out-fore : ∀ {A} k n (a : A) (s : Events∞ A) → Fore k (out n a s) → (k <ᵖ n ≡ true × ¬ Ext k n) ⊎ n ≡ k
  out-fore k n a s (inj₁ p) = inj₁ p
  out-fore k n a s (inj₂ ())

  mutual
    noext-run : ∀ {A} k (e : Events A) t → Fore k e → M.inside r k ≡ true → Ordered e → Steady e → Trail e t
              → EveryT (λ h → ¬ Ext k h) (M.runOn r e t)
    noext-run k (out n a s) t f ik o st tr =
      noext-pin k n s t (M.inside r n) refl (fore-head k (out n a s) f) (fore-trans k n (force s) (out-fore k n a s f) (inj₁ (proj₁ (steady st))))
        ik (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (proj₂ (trail tr))))
        (λ nb → everyT-mono (out-noext k n a s f) t (proj₁ (proj₂ (trail tr))))
    noext-run k (skip n s)  t f ik o st tr =
      noext-pin k n s t (M.inside r n) refl (fore-head k (skip n s) f)
        (fore-trans k n (force s) f (clear-fore n (force s) (proj₁ (steady st)) (proj₁ (ordered o))))
        ik (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (proj₂ (trail tr)))
        (λ nb → everyT-mono (skip-noext k n s f ik nb) t (proj₁ (proj₂ (trail tr))))
    noext-run {A} k (end c) t f ik o st tr = everyT-mono (end-noext {A} k c f) t (proj₁ (proj₂ (trail tr)))
    noext-run k hush        t f ik o st tr = everyT-mono (λ j ()) t (proj₁ (proj₂ (trail tr)))

    noext-pin : ∀ {A} k n (s : Events∞ A) t b → M.inside r n ≡ b → ¬ Ext k n → Fore k (force s) → M.inside r k ≡ true
              → Ordered (force s) → Steady (force s) → Trail (force s) (cut s) → (M.inside r n ≡ false → EveryT (λ h → ¬ Ext k h) t)
              → EveryT (λ h → ¬ Ext k h) (M.pinned r n s t b)
    everyᵀ (noext-pin k n s t true  ib nn f ik o st tr ft) = nn , noext-run k (force s) (cut s) f ik o st tr
    everyᵀ (noext-pin k n s t false ib nn f ik o st tr ft) = everyᵀ (ft ib)

  mutual
    flat-run : ∀ {A} (e : Events A) t → Ordered e → Steady e → Trail e t → FlatT (M.runOn r e t)
    flat-run (out n _ s) t o st tr =
      flat-pin n s t (M.inside r n) refl (inj₁ (proj₁ (steady st))) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (proj₂ (trail tr)))) (trailᶠ tr)
    flat-run (skip n s)  t o st tr =
      flat-pin n s t (M.inside r n) refl (clear-fore n (force s) (proj₁ (steady st)) (proj₁ (ordered o)))
        (proj₂ (ordered o)) (proj₂ (steady st)) (proj₂ (proj₂ (trail tr))) (trailᶠ tr)
    flat-run (end _)     t o st tr = trailᶠ tr
    flat-run hush        t o st tr = trailᶠ tr

    flat-pin : ∀ {A} n (s : Events∞ A) t b → M.inside r n ≡ b → Fore n (force s) → Ordered (force s) → Steady (force s)
             → Trail (force s) (cut s) → FlatT t → FlatT (M.pinned r n s t b)
    flatᵀ (flat-pin n s t true  ib f o st tr ft) = noext-run n (force s) (cut s) f ib o st tr , flat-run (force s) (cut s) o st tr
    flatᵀ (flat-pin n s t false ib f o st tr ft) = flatᵀ ft

------------------------------------------------------------------------
-- What a run leaves running, against what it last showed.

-- What `c` lies inside, keyed with none of `p`, came before `n`, or is a
-- bare tick.
Fresh : Pos → Pos → Pos → Set
Fresh p n c = ∀ k → Ext k c → ¬ Owned p k → k <ᵖ n ≡ true ⊎ Σ ℕ (λ t → k ≡ ix t ∷ [])

-- After each step a run shows, what it leaves running is fresh against it.
mutual
  Freshes : ∀ {A} → Pos → Events A → Set
  Freshes p (out n _ s) = EveryT (Fresh p n) (cut s) × FreshRun p (force s)
  Freshes p (skip n s)  = EveryT (Fresh p n) (cut s) × FreshRun p (force s)
  Freshes p (end _)     = ⊤
  Freshes p hush        = ⊤

  record FreshRun {A} (p : Pos) (e : Events A) : Set where
    coinductive
    field freshᴿ : Freshes p e

open FreshRun public

-- A state fresh against where it subscribed, and as it runs on.
Fresh∞ : ∀ {A} → Pos → Events∞ A → Set
Fresh∞ p σ = EveryT (Fresh p p) (cut σ) × FreshRun p (force σ)

-- Fresh against a step, fresh against any after it.
fresh-up : ∀ p n m c → n <ᵖ m ≡ true ⊎ n ≡ m → Fresh p n c → Fresh p m c
fresh-up p n m c nm f k x d with f k x d
... | inj₂ t  = inj₂ t
... | inj₁ kn with nm
...   | inj₁ lt   = inj₁ (<ᵖ-trans k n m kn lt)
...   | inj₂ refl = inj₁ kn

fresh-past : ∀ p n m c → m <ᵖ n ≡ false → Fresh p n c → Fresh p m c
fresh-past p n m c h = fresh-up p n m c (<ᵖ-split n m h)

-- Fresh against a step under `p`, fresh against `p`.
fresh-under : ∀ p ys c → Fresh p (p ++ ys) c → Fresh p p c
fresh-under p ys c f k x no with f k x no
... | inj₂ t  = inj₂ t
... | inj₁ kl = inj₁ (below-under p k ys (λ q → no (inj₁ q)) kl)

-- What an end left running, all past `m`, runs on fresh.
fresh-tail : ∀ {A} p m t → EveryT (Fresh p m) t → EveryT (λ k → m <ᵖ k ≡ true) t → FreshRun {A} p (tailᴱ t)
freshᴿ (fresh-tail p m (pin k u) ct mt) =
  everyT-mono (λ h → fresh-up p m k h (inj₁ (proj₁ (everyᵀ mt)))) (later u) (proj₂ (everyᵀ ct)) , fresh-tail p m (later u) (proj₂ (everyᵀ ct)) (proj₂ (everyᵀ mt))
freshᴿ (fresh-tail p m idle ct mt) = tt

mutual
  freshes-map : ∀ {A B} (f : A → B) p (x : Events A) → Freshes p x → Freshes p (M.mapᴱ f x)
  freshes-map f p (out _ _ r) (c , t) = c , fresh-map f p (force r) t
  freshes-map f p (skip _ r)  (c , t) = c , fresh-map f p (force r) t
  freshes-map f p (end _)     t       = tt
  freshes-map f p hush        t       = tt

  fresh-map : ∀ {A B} (f : A → B) p (x : Events A) → FreshRun p x → FreshRun p (M.mapᴱ f x)
  freshᴿ (fresh-map f p x t) = freshes-map f p x (freshᴿ t)

mutual
  freshes-scan : ∀ {A B} (f : B → A → B) z p (x : Events A) → Freshes p x → Freshes p (M.scanᴱ f z x)
  freshes-scan f z p (out _ a r) (c , t) = c , fresh-scan f (f z a) p (force r) t
  freshes-scan f z p (skip _ r)  (c , t) = c , fresh-scan f z p (force r) t
  freshes-scan f z p (end _)     t       = tt
  freshes-scan f z p hush        t       = tt

  fresh-scan : ∀ {A B} (f : B → A → B) z p (x : Events A) → FreshRun p x → FreshRun p (M.scanᴱ f z x)
  freshᴿ (fresh-scan f z p x t) = freshes-scan f z p x (freshᴿ t)

-- A take's last value shows just inside where the source's stood.
mutual
  fresh-take : ∀ {A} i (q : A → Bool) p (x : Events A) → FreshRun p x → FreshRun p (M.takeWhileᴱ i q x)
  freshᴿ (fresh-take i q p (out k a r) t) = fresh-taking i q p k a (q a) r (freshᴿ t)
  freshᴿ (fresh-take i q p (skip k r)  t) = proj₁ (freshᴿ t) , fresh-take i q p (force r) (proj₂ (freshᴿ t))
  freshᴿ (fresh-take i q p (end k)     t) = tt
  freshᴿ (fresh-take i q p hush        t) = tt

  fresh-taking : ∀ {A} i (q : A → Bool) p k (a : A) b (r : Events∞ A) → Freshes p (out k a r) → Freshes p (M.taking i q k a b r)
  fresh-taking i     q p k a true  r (c , t) = c , fresh-take i q p (force r) t
  fresh-taking true  q p k a false r (c , t) =
    everyT-mono (λ h → fresh-up p k (k ++ [ ix 0 ]) h (inj₁ (<ᵖ-below k []))) (cut r) c , record { freshᴿ = tt }
  fresh-taking false q p k a false r _       = tt

-- A cold leaf's run, a list's and a joiner's leave nothing running.
mutual
  fresh-frames : ∀ {A t} p τ e (m : From A t) → FreshRun p (M.frames τ e m)
  fresh-frames p τ e M.done       = record { freshᴿ = tt }
  fresh-frames p τ e M.quiet      = record { freshᴿ = tt }
  fresh-frames p τ e (M.at t _ b) = fresh-burst p τ (ix (τ + t) ∷ sub e ∷ []) 0 b

  fresh-burst : ∀ {A t} p τ r i (b : M.Frame A t) → FreshRun p (M.burst τ r i b)
  freshᴿ (fresh-burst p τ r i (M.emit a k)) = everyT-idle , fresh-burst p τ r (suc i) (M.Frame∞.force k)
  freshᴿ (fresh-burst p τ r i (M.stall k))  = everyT-idle , fresh-burst p τ r (suc i) (M.Frame∞.force k)
  freshᴿ (fresh-burst p τ r i (M.close k))  = everyT-idle , fresh-frames p τ (r ++ [ last ]) (M.From∞.force k)

fresh-start : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Fresh∞ p (U.stateᴺ (U.startᶜ p m) ρ)
fresh-start p (M.at zero _ b)     ρ = everyT-idle , fresh-burst p (tick p) p 0 b
fresh-start p (M.at (suc t) le b) ρ = everyT-idle , fresh-frames p (tick p) (p ++ [ last ]) (M.at (suc t) le b)
fresh-start p M.done              ρ = everyT-idle , record { freshᴿ = tt }
fresh-start p M.quiet             ρ = everyT-idle , record { freshᴿ = tt }

fresh-of : ∀ {A} p q i (xs : List A) → FreshRun q (M.ofᴱ p i xs)
freshᴿ (fresh-of p q i [])       = tt
freshᴿ (fresh-of p q i (x ∷ xs)) = everyT-idle , fresh-of p q (suc i) xs

mutual
  fresh-rejoin : ∀ {A} p q (e : Events A) → FreshRun q (M.rejoin p e)
  fresh-rejoin p q (out j a k) = fresh-shown p q j (just a) k (p <ᵖ j)
  fresh-rejoin p q (skip j k)  = fresh-shown p q j nothing k (p <ᵖ j)
  fresh-rejoin p q (end c) with p <ᵖ c
  ... | true  = record { freshᴿ = tt }
  ... | false = record { freshᴿ = tt }
  fresh-rejoin p q hush        = record { freshᴿ = tt }

  fresh-shown : ∀ {A} p q j (a : Maybe A) (k : Events∞ A) b → FreshRun q (M.shown p j a k b)
  freshᴿ (fresh-shown p q j (just a) k true)  = everyT-idle , fresh-rejoin p q (force k)
  freshᴿ (fresh-shown p q j nothing  k true)  = everyT-idle , fresh-rejoin p q (force k)
  freshᴿ (fresh-shown p q j (just a) k false) = everyT-idle , fresh-rejoin p q (force k)
  freshᴿ (fresh-shown p q j nothing  k false) = everyT-idle , fresh-rejoin p q (force k)

-- Freshness holds of what agrees with it at every depth, and of a
-- position owning less.
mutual
  fresh-≈ : ∀ {A} p (x y : Events A) → (∀ k → Agree k x y) → FreshRun p x → FreshRun p y
  freshᴿ (fresh-≈ p x y ag fr) = freshes-≈ p x y ag (ag 1) (freshᴿ fr)

  freshes-≈ : ∀ {A} p (x y : Events A) → (∀ k → Agree k x y) → Agree 1 x y → Freshes p x → Freshes p y
  freshes-≈ p (out _ _ l) (out _ _ r) ag (out⁼ _ _) (c , t) =
    everyT-≈ (cut l) (cut r) (λ k → M.agree-tail (ag (suc k))) c , fresh-≈ p (force l) (force r) (λ k → rest-agree (ag (suc k))) t
  freshes-≈ p (skip _ l)  (skip _ r)  ag (skip⁼ _ _) (c , t) =
    everyT-≈ (cut l) (cut r) (λ k → M.agree-tail (ag (suc k))) c , fresh-≈ p (force l) (force r) (λ k → rest-agree (ag (suc k))) t
  freshes-≈ p (end _)     (end _)     ag end⁼        t = tt
  freshes-≈ p hush        hush        ag hush⁼       t = tt

mutual
  fresh-widen : ∀ {A} p q → (∀ k → ¬ Owned p k → ¬ Owned q k) → (x : Events A) → FreshRun q x → FreshRun p x
  freshᴿ (fresh-widen p q w x fr) = freshes-widen p q w x (freshᴿ fr)

  freshes-widen : ∀ {A} p q → (∀ k → ¬ Owned p k → ¬ Owned q k) → (x : Events A) → Freshes q x → Freshes p x
  freshes-widen p q w (out _ _ r) (c , t) = everyT-mono (λ h f k x d → f k x (w k d)) (cut r) c , fresh-widen p q w (force r) t
  freshes-widen p q w (skip _ r)  (c , t) = everyT-mono (λ h f k x d → f k x (w k d)) (cut r) c , fresh-widen p q w (force r) t
  freshes-widen p q w (end _)     t       = tt
  freshes-widen p q w hush        t       = tt

owned-drop : ∀ k w h → Owned (k ++ w) h → Owned k h
owned-drop k w h = owned-trans k (k ++ w) h (inj₁ (prefix-++ k w))

-- Keyed under a position tagged with `p`: keyed under `p`.
mutual
  sub-owned : ∀ k p h → Owned (k ++ [ sub p ]) h → Owned p h
  sub-owned k p h (inj₁ pr) = inj₂ (tagged-prefix p (k ++ [ sub p ]) h (tagged-sub k p) pr)
  sub-owned k p h (inj₂ t)  = inj₂ (sub-tagged k p h t)

  sub-tagged : ∀ k p h → Tagged (k ++ [ sub p ]) h → Tagged p h
  sub-tagged k p []          ()
  sub-tagged k p (ix _ ∷ h)  t        = sub-tagged k p h t
  sub-tagged k p (last ∷ h)  t        = sub-tagged k p h t
  sub-tagged k p (sub j ∷ h) (inj₁ o) = inj₁ (sub-owned k p j o)
  sub-tagged k p (sub j ∷ h) (inj₂ t) = inj₂ (sub-tagged k p h t)

-- A position tagged with `p` outweighs it, and a step under `p` too.
heavy : ∀ k p → ¬ Owned (k ++ [ sub p ]) p
heavy k p o = <-irrefl refl (<-≤-trans (tagged-weigh p (k ++ [ sub p ]) (tagged-sub k p)) (owned-weigh _ _ o))

snoc-weigh : ∀ p (l : M.Label) → weigh p < weigh (p ++ [ l ])
snoc-weigh []      (ix _)  = s≤s z≤n
snoc-weigh []      (sub _) = s≤s z≤n
snoc-weigh []      last    = s≤s z≤n
snoc-weigh (a ∷ p) l       = +-monoʳ-< (weighˡ a) (snoc-weigh p l)

longer : ∀ p (l : M.Label) → ¬ Owned (p ++ [ l ]) p
longer p l o = <-irrefl refl (<-≤-trans (snoc-weigh p l) (owned-weigh _ _ o))

mark-sub : ∀ {l} → Mark l → ∀ j → sub j ≢ l
mark-sub (ix-mark _) j ()
mark-sub last-mark   j ()

snoc-ne : ∀ a b {l l′ : M.Label} → l ≢ l′ → a ++ [ l ] ≢ b ++ [ l′ ]
snoc-ne a b ne eq = ne (proj₂ (snoc-inj a b eq))

-- Neither a prefix of the other.
Unrelated : Pos → Pos → Set
Unrelated k h = ¬ Prefix k h × ¬ Prefix h k

ext-prefixed : ∀ {k h} → Ext k h → Prefix k h
ext-prefixed (ext l ls) = prefix-++ _ (l ∷ ls)

-- No later and no prefix is earlier.
strict : ∀ k q → q <ᵖ k ≡ false → ¬ Prefix k q → k <ᵖ q ≡ true
strict k q a np with <ᵖ-split k q a
... | inj₁ kq   = kq
... | inj₂ refl = ⊥-elim (np (prefix-refl k))

------------------------------------------------------------------------
-- THE WALK: a connect's cuts trail its run at every reachable state.

module Walk {A B} (p : Pos) (hp : Headed p) where
  r P₀ : Pos
  r  = p ++ [ ix 1 ]
  P₀ = p ++ [ ix 0 ]

  rt : ∀ t → ¬ Owned r (ix t ∷ [])
  rt t = owned-tick p t hp

  open Bursting r

  record Side (β : Events∞ B) (σ : Events∞ A) : Set where
    field
      tb : Trailing β
      ts : Trailing σ
      os : Ordered (force σ)
      ss : Steady (force σ)
      kb : Every∞ (Owned P₀) β
      ks : Every∞ (Disjoint P₀) σ
      kr : Every∞ (Rise r) β
      hs : Every∞ Headed σ
      rs : Every∞ (Owned r) σ
      lf : Pos
      lo : Owned P₀ lf
      lc : Cue lf (force σ)
      fc : EveryT (Fresh P₀ lf) (cut β)
      fr : FreshRun P₀ (force β)

  -- What the source next shows is keyed with none of the body.
  shown-apart : ∀ (e : Events A) → Going e → Every (Disjoint P₀) e → ¬ Owned P₀ (M.shownAt e)
  shown-apart (out k _ _) g pe = proj₁ (apart-mark P₀ k (ix 0) (ix-mark 0) (proj₁ (every pe)))
  shown-apart (skip k _)  g pe = proj₁ (apart-mark P₀ k (ix 0) (ix-mark 0) (proj₁ (every pe)))
  shown-apart (end k)     g pe = proj₁ (apart-mark P₀ k (ix 0) (ix-mark 0) (every pe))
  shown-apart hush        () pe

  -- Before the body's next, what it leaves running trails a skip.
  body-lead : ∀ q (x : Events B) c → M.before q x ≡ true → Trail x c → EveryT (Marked q) c
  body-lead q (out k _ _) c qk tr = everyT-mono (λ j z → inj₁ (≮-trans q k j (<ᵖ-asym q k qk) (proj₁ z))) c (proj₁ (proj₂ (trail tr)))
  body-lead q (skip k _)  c qk tr = everyT-mono lead c (proj₁ (proj₂ (trail tr)))
    where lead : ∀ j → Marked k j → Marked q j
          lead j (inj₁ jk) = inj₁ (≮-trans q k j (<ᵖ-asym q k qk) jk)
          lead j (inj₂ mk) = marked-cue q mk (<ᵖ-asym q k qk)
  body-lead q (end k)     c qk tr = everyT-mono (λ j z → inj₁ (≮-trans q k j (<ᵖ-asym q k qk) (<ᵖ-asym k j (proj₁ z)))) c (proj₁ (proj₂ (trail tr)))
  body-lead q hush        c qk tr = everyT-mono (λ j ()) c (proj₁ (proj₂ (trail tr)))

  -- A body step `n` no later than the source's `q` comes before it.
  below : ∀ q n → ¬ Owned P₀ q → Owned P₀ n → q <ᵖ n ≡ false → n <ᵖ q ≡ true
  below q n nq on nl with <ᵖ-split n q nl
  ... | inj₁ x  = x
  ... | inj₂ eq = ⊥-elim (nq (subst (Owned P₀) eq on))

  -- A burst step the source has not passed lies nowhere before `n`.
  late : ∀ q n j → ¬ Owned P₀ q → Owned P₀ n → q <ᵖ n ≡ false → Disjoint P₀ j → Marked q j → j <ᵖ n ≡ true → ⊥
  late q n j nq on nl dj (inj₁ jq) jn with () ← trans (sym jq) (<ᵖ-trans j n q jn (below q n nq on nl))
  late q n j nq on nl dj (inj₂ mq) jn = marks-alien (marks-mid n mq jn nl) on dj

  -- A body step `n` before the source's `q`, beside a burst step `j`.
  module Pin q n j (nq : ¬ Owned P₀ q) (on : Owned P₀ n) (nl : q <ᵖ n ≡ false) (rn : Rise r n) (dj : Disjoint P₀ j) (hj : Headed j) (oj : Owned r j) where
    unowned : Marked q j → ¬ Owned j n
    unowned mj (inj₁ pr) with prefix-lt j n pr
    ... | inj₁ eq = proj₁ dj (subst (Owned P₀) (sym eq) on)
    ... | inj₂ jn = late q n j nq on nl dj mj jn
    unowned mj (inj₂ t) = late q n j nq on nl dj mj (proj₂ rn j hj oj t)

    unkeys : ¬ Owned n j
    unkeys o = proj₁ dj (owned-trans P₀ n j on o)

    apart : Marked q j → Disjoint n j
    apart mj = unkeys , unowned mj

    atop : Marked q j → j <ᵖ n ≡ false
    atop (inj₁ jq) = ≮-trans n q j nl jq
    atop (inj₂ mq) with j <ᵖ n in e
    ... | false = refl
    ... | true  = ⊥-elim (marks-alien (marks-mid n mq e nl) on dj)

    past : Marked q j → n <ᵖ j ≡ true
    past mj = take-ahead n j (atop mj) (apart mj)

  out-pin : ∀ q n → ¬ Owned P₀ q → Owned P₀ n → q <ᵖ n ≡ false → Rise r n → ∀ j → (Marked q j × Disjoint P₀ j) × Headed j × Owned r j
          → j <ᵖ n ≡ false × Disjoint n j
  out-pin q n nq on nl rn j ((mj , dj) , hj , oj) = atop mj , apart mj
    where open Pin q n j nq on nl rn dj hj oj

  end-pin : ∀ q c → ¬ Owned P₀ q → Owned P₀ c → q <ᵖ c ≡ false → Rise r c → ∀ j → (Marked q j × Disjoint P₀ j) × Headed j × Owned r j
          → c <ᵖ j ≡ true × Disjoint (c ++ [ ix 1 ]) j × ¬ Ext c j
  end-pin q c nq on nl rc j ((mj , dj) , hj , oj) = past mj , disjoint-snoc c j (ix 1) (λ x → tagged-lane j x 1) (apart mj) , λ x → unkeys (owned-ext x)
    where open Pin q c j nq on nl rc dj hj oj

  module At {β σ} (sd : Side β σ) where
    open Side sd

    burst-sorted : SortedT (M.burstOn r σ ∪ cut β)
    burst-sorted = sortedT-∪ _ _ (sorted-run (force σ) (cut σ) os ts) (proj₁ (trail tb))

    -- Each burst step, against the source's next and the body's.
    pinsAt : ∀ e → force σ ≡ e → EveryT (λ j → Marked (M.shownAt e) j × Disjoint P₀ j) (M.burstOn r σ)
    pinsAt e eq = everyT-zip (M.burstOn r σ) (lead-run (M.shownAt e) (force σ) (cut σ) ts os (subst (Cue (M.shownAt e)) (sym eq) (cue-self e)))
                    (everyT-burstOn r σ ks)

    pinsOn : ∀ e → force σ ≡ e → EveryT (λ j → (Marked (M.shownAt e) j × Disjoint P₀ j) × Headed j × Owned r j) (M.burstOn r σ)
    pinsOn e eq = everyT-zip (M.burstOn r σ) (pinsAt e eq) (everyT-zip (M.burstOn r σ) (everyT-burstOn r σ hs) (everyT-burstOn r σ rs))

    nqAt : ∀ e → force σ ≡ e → Going e → ¬ Owned P₀ (M.shownAt e)
    nqAt e eq g = shown-apart e g (subst (Every (Disjoint P₀)) eq (proj₁ ks))

    -- No body pin lies inside a burst step: the body passed what it lies
    -- inside, and the source has not.
    pins-apart : ∀ e → force σ ≡ e → Going e → EveryT (λ a → EveryT (Apart a) (cut β)) (M.burstOn r σ)
    pins-apart e eq g = everyT-mono pair (M.burstOn r σ) (pinsOn e eq)
      where
        nl = cue-shown lf e g (subst (Cue lf) eq lc)
        pair : ∀ k → (Marked (M.shownAt e) k × Disjoint P₀ k) × Headed k × Owned r k → EveryT (Apart k) (cut β)
        pair k ((mk , dk) , _ , ok) = everyT-mono apart (cut β) (everyT-zip (cut β) fc (proj₂ kb))
          where
            inside : ∀ h → Fresh P₀ lf h → ¬ Ext k h
            inside h fh x with fh k x (proj₁ dk)
            ... | inj₁ kl       = late (M.shownAt e) lf k (nqAt e eq g) lo nl dk mk kl
            ... | inj₂ (t , kt) = rt t (subst (Owned r) kt ok)
            apart : ∀ h → Fresh P₀ lf h × Owned P₀ h → Apart k h
            apart h (fh , oh) = inside h fh , λ x → proj₁ dk (owned-trans P₀ h k oh (owned-ext x))

    burst-flat : ∀ e → force σ ≡ e → Going e → FlatT (M.burstOn r σ ∪ cut β)
    burst-flat e eq g = flatT-∪ _ _ (flat-run (force σ) (cut σ) os ss ts) (trailᶠ tb) (pins-apart e eq g)

    -- The source steps first.
    toSource : ∀ e → force σ ≡ e → Going e → M.before (M.shownAt e) (force β) ≡ true → Side β (M.onward∞ σ (force σ))
    toSource e eq g be = record
      { tb = tb
      ; ts = trailing-onward σ (force σ) refl ts
      ; os = ordered-onward σ (force σ) refl ts os
      ; ss = steady-onward σ (force σ) refl ts ss
      ; kb = kb
      ; ks = every-onward σ (force σ) (proj₁ ks) (proj₂ ks) (proj₁ ks)
      ; kr = kr
      ; hs = every-onward σ (force σ) (proj₁ hs) (proj₂ hs) (proj₁ hs)
      ; rs = every-onward σ (force σ) (proj₁ rs) (proj₂ rs) (proj₁ rs)
      ; lf = lf
      ; lo = lo
      ; lc = cue-onward lf σ (force σ) refl ts os lc
      ; fc = fc
      ; fr = fr
      }

    -- The body steps first.
    toBody : ∀ e → force σ ≡ e → ∀ n → M.shownAt e <ᵖ n ≡ false → Owned P₀ n → ∀ β′
           → Trailing β′ → Every∞ (Owned P₀) β′ → Every∞ (Rise r) β′ → EveryT (Fresh P₀ n) (cut β′) → FreshRun P₀ (force β′) → Side β′ σ
    toBody e eq n be on β′ tb′ kb′ kr′ fc′ fr′ = record
      { tb = tb′
      ; ts = ts
      ; os = os
      ; ss = ss
      ; kb = kb′
      ; ks = ks
      ; kr = kr′
      ; hs = hs
      ; rs = rs
      ; lf = n
      ; lo = on
      ; lc = subst (Cue n) (sym eq) (shown-cue n e be)
      ; fc = fc′
      ; fr = fr′
      }

  open At

  mutual
    tr-beside : ∀ β σ → Side β σ → Trail (M.beside r β σ) (M.burstOn r σ ∪ cut β)
    tr-beside β σ sd = tr-side β σ sd (force σ) refl

    tr-side : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Trail (M.side r β σ e) (M.runOn r e (cut σ) ∪ cut β)
    tr-side β σ sd (out k a s) eq =
      tr-ahead β σ sd (out k a s) eq tt _ refl _ (cong (λ z → M.runOn r z (cut σ) ∪ cut β) eq)
    tr-side β σ sd (skip k s)  eq =
      tr-ahead β σ sd (skip k s) eq tt _ refl _ (cong (λ z → M.runOn r z (cut σ) ∪ cut β) eq)
    tr-side β σ sd (end c)     eq =
      tr-ahead β σ sd (end c) eq tt _ refl _ (cong (λ z → M.runOn r z (cut σ) ∪ cut β) eq)
    tr-side β σ sd hush        eq =
      trail-hushed (cut σ) (cut β) (force β) (proj₁ (proj₂ (trail (subst (λ z → Trail z (cut σ)) eq (Side.ts sd))))) (Side.tb sd)

    tr-ahead : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ b → M.before (M.shownAt e) (force β) ≡ b
             → ∀ c → M.burstOn r σ ∪ cut β ≡ c → Trail (M.ahead r β σ (M.shownAt e) b) c
    tr-ahead β σ sd e eq g true  be c ce = tr-src β σ sd e eq g be c ce
    tr-ahead β σ sd e eq g false be c ce = tr-body β σ sd e eq g (force β) refl be c ce

    tr-src : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → M.before (M.shownAt e) (force β) ≡ true
           → ∀ c → M.burstOn r σ ∪ cut β ≡ c → Trail (M.ahead r β σ (M.shownAt e) true) c
    trail (tr-src β σ sd e eq g be c ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT (Marked (M.shownAt e))) ce (everyT-∪ (M.burstOn r σ) (cut β) (everyT-mono (λ j z → proj₁ z) (M.burstOn r σ) (pinsAt sd e eq))
          (body-lead (M.shownAt e) (force β) (cut β) be (Side.tb sd)))
      , tr-beside β (M.onward∞ σ (force σ)) (toSource sd e eq g be)
    trailᶠ (tr-src β σ sd e eq g be c ce) = subst FlatT ce (burst-flat sd e eq g)

    tr-body : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ x → force β ≡ x → M.before (M.shownAt e) x ≡ false
            → ∀ c → M.burstOn r σ ∪ cut β ≡ c → Trail (M.body r σ (M.shownAt e) x) c
    trail (tr-body β σ sd e eq g (out n a β′) xe be c′ ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT _) ce (everyT-∪ (M.burstOn r σ) (cut β) (everyT-mono (out-pin q n nq on be rn) (M.burstOn r σ) (pinsOn sd e eq)) (proj₁ (proj₂ (trail tbx))))
      , tr-ahead β′ σ (toBody sd e eq n be on β′ (proj₁ (proj₂ (proj₂ (trail tbx)))) (proj₂ (every kbx)) (proj₂ (every krx))
                         (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) e eq g _ refl _ refl
      , everyT-∪ (M.burstOn r σ) (cut β′) (everyT-mono (λ j z → proj₂ (out-pin q n nq on be rn j z)) (M.burstOn r σ) (pinsOn sd e eq))
          (proj₂ (proj₂ (proj₂ (trail tbx))))
      where q = M.shownAt e
            nq = nqAt sd e eq g
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            rn = proj₁ (every krx)
            frx = subst (FreshRun P₀) xe (Side.fr sd)
    trail (tr-body β σ sd e eq g (skip n β′) xe be c′ ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT _) ce (everyT-∪ (M.burstOn r σ) (cut β) (everyT-mono (λ j z → inj₁ (proj₁ (out-pin q n nq on be rn j z))) (M.burstOn r σ) (pinsOn sd e eq))
          (proj₁ (proj₂ (trail tbx))))
      , tr-ahead β′ σ (toBody sd e eq n be on β′ (proj₂ (proj₂ (trail tbx))) (proj₂ (every kbx)) (proj₂ (every krx))
                         (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) e eq g _ refl _ refl
      where q = M.shownAt e
            nq = nqAt sd e eq g
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            rn = proj₁ (every krx)
            frx = subst (FreshRun P₀) xe (Side.fr sd)
    trail (tr-body β σ sd e eq g (end c) xe be c′ ce) =
      subst SortedT ce (burst-sorted sd)
      , subst (EveryT _) ce (everyT-∪ (M.burstOn r σ) (cut β) (everyT-mono (end-pin q c nq on be rc) (M.burstOn r σ) (pinsOn sd e eq)) (proj₁ (proj₂ (trail tbx))))
      , tt
      where q = M.shownAt e
            nq = nqAt sd e eq g
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            on = every (subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd)))
            rc = every (subst (Every (Rise r)) xe (proj₁ (Side.kr sd)))
    trail (tr-body β σ sd e eq g hush xe () c′ ce)
    trailᶠ (tr-body β σ sd e eq g x xe be c′ ce) = subst FlatT ce (burst-flat sd e eq g)

  -- A body step before a source step keys no lane admitted there, nor
  -- does the source step key the body step's.
  sp-late : ∀ n y → Owned P₀ n → Rise r n → Disjoint P₀ y → Headed y → Owned r y → n <ᵖ y ≡ true → Sp n y
  sp-late n y on rn dy hy oy ny = sp-of n y (fwd , bwd)
    where
      on₁ : Owned P₀ (n ++ [ ix 1 ])
      on₁ = beneath-owned P₀ _ (owned-snoc P₀ n (ix 1) on)
      fwd : ¬ Owned y (n ++ [ ix 1 ])
      fwd (inj₁ pr) with prefix-split y n (ix 1) pr
      ... | inj₂ eq  = proj₁ dy (subst (Owned P₀) (sym eq) on₁)
      ... | inj₁ pr′ with prefix-lt y n pr′
      ...   | inj₁ eq = proj₁ dy (subst (Owned P₀) (sym eq) on)
      ...   | inj₂ yn = t≢f (trans (sym yn) (<ᵖ-asym n y ny))
      fwd (inj₂ t) = t≢f (trans (sym (proj₂ rn y hy oy (tagged-mark y n (ix 1) (ix-mark 1) t))) (<ᵖ-asym n y ny))
      bwd : ¬ Owned (n ++ [ ix 1 ]) y
      bwd o = proj₁ dy (owned-trans P₀ (n ++ [ ix 1 ]) y on₁ o)

  every-shown : ∀ {C} {P : Pos → Set} (e : Events C) → Going e → Every (λ y → P y × P (y ++ [ ix 0 ])) e → P (M.shownAt e)
  every-shown (out _ _ _) g pe = proj₂ (proj₁ (every pe))
  every-shown (skip _ _)  g pe = proj₂ (proj₁ (every pe))
  every-shown (end _)     g pe = proj₂ (every pe)
  every-shown hush        () pe

  -- Past a body step no later than where the source next shows, every
  -- step the source has yet to show or leave running keys no lane the
  -- body step admits, shown or not.
  src-sp : ∀ {β σ} → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ n → M.shownAt e <ᵖ n ≡ false → Owned P₀ n → Rise r n
         → Every∞ (λ y → Sp n y × Sp n (y ++ [ ix 0 ])) σ
  src-sp {β} {σ} sd e eq g n be on rn =
    every∞-mono f σ (every∞-zip σ (every∞-zip σ (every∞-zip σ mk (Side.ks sd)) (Side.hs sd)) (Side.rs sd))
    where
      q  = M.shownAt e
      nq = nqAt sd e eq g
      mk = lead∞ q σ (Side.ts sd) (Side.os sd) (subst (Cue q) (sym eq) (cue-self e))
      f : ∀ y → ((Marked q y × Disjoint P₀ y) × Headed y) × Owned r y → Sp n y × Sp n (y ++ [ ix 0 ])
      f y (((my , dy) , hy) , oy) = sy , sp-step n y sy
        where sy = sp-late n y on rn dy hy oy (Pin.past q n y nq on be rn dy hy oy my)

  -- THE SPREAD WALK: after a body value, nothing the connect later shows
  -- or leaves running keys where a lane admitted at it would.
  mutual
    sp-beside : ∀ β σ → Side β σ → Spread (force β) → Spread (M.beside r β σ)
    sp-beside β σ sd sb = sp-side β σ sd sb (force σ) refl

    sp-side : ∀ β σ → Side β σ → Spread (force β) → ∀ e → force σ ≡ e → Spread (M.side r β σ e)
    sp-side β σ sd sb (out k a s) eq = sp-ahead β σ sd sb (out k a s) eq tt _ refl
    sp-side β σ sd sb (skip k s)  eq = sp-ahead β σ sd sb (skip k s) eq tt _ refl
    sp-side β σ sd sb (end c)     eq = sp-ahead β σ sd sb (end c) eq tt _ refl
    sp-side β σ sd sb hush        eq = sb

    sp-ahead : ∀ β σ → Side β σ → Spread (force β) → ∀ e → force σ ≡ e → Going e → ∀ b → M.before (M.shownAt e) (force β) ≡ b
             → Spread (M.ahead r β σ (M.shownAt e) b)
    sp-ahead β σ sd sb e eq g true  be = sp-src β σ sd sb e eq g be
    sp-ahead β σ sd sb e eq g false be = sp-body β σ sd e eq g (force β) refl sb be

    sp-src : ∀ β σ → Side β σ → Spread (force β) → ∀ e → force σ ≡ e → Going e → M.before (M.shownAt e) (force β) ≡ true
           → Spread (M.ahead r β σ (M.shownAt e) true)
    spread (sp-src β σ sd sb e eq g be) = sp-beside β (M.onward∞ σ (force σ)) (toSource sd e eq g be) sb

    sp-body : ∀ β σ → Side β σ → ∀ e → force σ ≡ e → Going e → ∀ x → force β ≡ x → Spread x → M.before (M.shownAt e) x ≡ false
            → Spread (M.body r σ (M.shownAt e) x)
    spread (sp-body β σ sd e eq g (out n a β′) xe sx be) =
      ( every-ahead {P = Sp n} r β′ σ q (M.before q (force β′)) (proj₁ (spread sx)) ss
          (every-shown e g (subst (Every (λ y → Sp n y × Sp n (y ++ [ ix 0 ]))) eq (proj₁ ss)))
      , everyT-∪ (M.burstOn r σ) (cut β′) (everyT-burstOn r σ (every∞-mono (λ _ → proj₁) σ ss)) (proj₂ (proj₁ (spread sx))) )
      , sp-ahead β′ σ (toBody sd e eq n be on β′ (proj₁ (proj₂ (proj₂ (trail tbx)))) (proj₂ (every kbx)) (proj₂ (every krx))
                         (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) (proj₂ (spread sx)) e eq g _ refl
      where q = M.shownAt e
            tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            frx = subst (FreshRun P₀) xe (Side.fr sd)
            ss = src-sp sd e eq g n be on (proj₁ (every krx))
    spread (sp-body β σ sd e eq g (skip n β′) xe sx be) =
      sp-ahead β′ σ (toBody sd e eq n be on β′ (proj₂ (proj₂ (trail tbx))) (proj₂ (every kbx)) (proj₂ (every krx))
                       (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))) (spread sx) e eq g _ refl
      where tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
            kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
            on = proj₁ (every kbx)
            krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
            frx = subst (FreshRun P₀) xe (Side.fr sd)
    spread (sp-body β σ sd e eq g (end c) xe sx be) = tt
    spread (sp-body β σ sd e eq g hush    xe sx be) = tt

  -- THE ORDER WALK: each step the connect shows no earlier than the one
  -- before, the source's past the body's last and the body's past the
  -- source's last.
  atop-cue : ∀ L β (σ : Events∞ A) e → Cue L e → Atop L (force β) → Atop L (M.side r β σ e)
  atop-cue L β σ (out q _ _) c a = atop-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) L a c
  atop-cue L β σ (skip q _)  c a = atop-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) L a c
  atop-cue L β σ (end q)     c a = atop-ahead r β σ (q ++ [ ix 0 ]) (M.before (q ++ [ ix 0 ]) (force β)) L a c
  atop-cue L β σ hush        c a = a

  mutual
    or-beside : ∀ β σ → Trailing σ → Ordered (force σ) → Ordered (force β) → Ordered (M.beside r β σ)
    or-beside β σ ts os ob = or-side β σ ts os ob (force σ) refl

    or-side : ∀ β σ → Trailing σ → Ordered (force σ) → Ordered (force β) → ∀ e → force σ ≡ e → Ordered (M.side r β σ e)
    or-side β σ ts os ob (out k a s) eq = or-ahead β σ ts os ob (out k a s) eq tt _ refl
    or-side β σ ts os ob (skip k s)  eq = or-ahead β σ ts os ob (skip k s) eq tt _ refl
    or-side β σ ts os ob (end c)     eq = or-ahead β σ ts os ob (end c) eq tt _ refl
    or-side β σ ts os ob hush        eq = ob

    or-ahead : ∀ β σ → Trailing σ → Ordered (force σ) → Ordered (force β) → ∀ e → force σ ≡ e → Going e → ∀ b
             → M.before (M.shownAt e) (force β) ≡ b → Ordered (M.ahead r β σ (M.shownAt e) b)
    or-ahead β σ ts os ob e eq g true  be = or-src β σ ts os ob e eq g be
    or-ahead β σ ts os ob e eq g false be = or-body σ ts os e eq g (force β) ob be

    or-src : ∀ β σ → Trailing σ → Ordered (force σ) → Ordered (force β) → ∀ e → force σ ≡ e → Going e
           → M.before (M.shownAt e) (force β) ≡ true → Ordered (M.ahead r β σ (M.shownAt e) true)
    ordered (or-src β σ ts os ob e eq g be) =
      atop-cue q β σ′ (force σ′) (cue-onward q σ (force σ) refl ts os (subst (λ z → Cue (M.shownAt z) (force σ)) eq (cue-self (force σ))))
        (before-atop q (force β) be)
      , or-beside β σ′ (trailing-onward σ (force σ) refl ts) (ordered-onward σ (force σ) refl ts os) ob
      where q  = M.shownAt e
            σ′ = M.onward∞ σ (force σ)

    or-body : ∀ σ → Trailing σ → Ordered (force σ) → ∀ e → force σ ≡ e → Going e → ∀ x → Ordered x
            → M.before (M.shownAt e) x ≡ false → Ordered (M.body r σ (M.shownAt e) x)
    ordered (or-body σ ts os e eq g (out n a β′) ox be) =
      atop-ahead r β′ σ (M.shownAt e) (M.before (M.shownAt e) (force β′)) n (proj₁ (ordered ox)) be , or-ahead β′ σ ts os (proj₂ (ordered ox)) e eq g _ refl
    ordered (or-body σ ts os e eq g (skip n β′) ox be) =
      atop-ahead r β′ σ (M.shownAt e) (M.before (M.shownAt e) (force β′)) n (proj₁ (ordered ox)) be , or-ahead β′ σ ts os (proj₂ (ordered ox)) e eq g _ refl
    ordered (or-body σ ts os e eq g (end c)     ox be) = tt
    ordered (or-body σ ts os e eq g hush        ox be) = tt

  -- THE STEADY WALK: a source step's shown position lies outside the
  -- body's next, and the source's; a body step's outside the source's.
  clear-head : ∀ q (x : Events B) → M.before q x ≡ true → Every (λ k → Unrelated k q) x → Clear q x
  clear-head q (out k _ _) qk ux = qk , λ e → proj₂ (proj₁ (every ux)) (ext-prefixed e)
  clear-head q (skip k _)  qk ux = λ e → proj₂ (proj₁ (every ux)) (ext-prefixed e)
  clear-head q (end k)     qk ux = qk , λ e → proj₂ (every ux) (ext-prefixed e)
  clear-head q hush        qk ux = tt

  clear-body : ∀ q (σ : Events∞ A) q′ (x : Events B) → M.before q x ≡ true → Every (λ k → Unrelated k q) x → Clear q (M.body r σ q′ x)
  clear-body q σ q′ (out k a β) qk ux = clear-head q (out k a β) qk ux
  clear-body q σ q′ (skip k β)  qk ux = clear-head q (skip k β) qk ux
  clear-body q σ q′ (end k)     qk ux = clear-head q (end k) qk ux
  clear-body q σ q′ hush        qk ux = tt

  clear-ahead : ∀ q β (σ : Events∞ A) q′ b → M.before q (force β) ≡ true → Every (λ k → Unrelated k q) (force β) → ¬ Ext q q′
              → Clear q (M.ahead r β σ q′ b)
  clear-ahead q β σ q′ true  qb ub nx = nx
  clear-ahead q β σ q′ false qb ub nx = clear-body q σ q′ (force β) qb ub

  clear-side : ∀ q β (σ : Events∞ A) e → M.before q (force β) ≡ true → Every (λ k → Unrelated k q) (force β)
             → Head (λ h → ¬ Ext q (h ++ [ ix 0 ])) e → Clear q (M.side r β σ e)
  clear-side q β σ (out h _ _) qb ub nx = clear-ahead q β σ (h ++ [ ix 0 ]) (M.before (h ++ [ ix 0 ]) (force β)) qb ub nx
  clear-side q β σ (skip h _)  qb ub nx = clear-ahead q β σ (h ++ [ ix 0 ]) (M.before (h ++ [ ix 0 ]) (force β)) qb ub nx
  clear-side q β σ (end h)     qb ub nx = clear-ahead q β σ (h ++ [ ix 0 ]) (M.before (h ++ [ ix 0 ]) (force β)) qb ub nx
  clear-side q β σ hush        qb ub nx = clear-head q (force β) qb ub

  past-body : ∀ n (σ : Events∞ A) q (x : Events B) → Past n x → Past n (M.body r σ q x)
  past-body n σ q (out _ _ _) pb = pb
  past-body n σ q (skip _ _)  pb = pb
  past-body n σ q (end _)     pb = pb
  past-body n σ q hush        pb = tt

  past-ahead : ∀ n β (σ : Events∞ A) q b → Past n (force β) → n <ᵖ q ≡ true → ¬ Ext n q → Past n (M.ahead r β σ q b)
  past-ahead n β σ q true  pb nq nx = nq , nx
  past-ahead n β σ q false pb nq nx = past-body n σ q (force β) pb

  clear-under : ∀ n (σ : Events∞ A) q (x : Events B) → Clear n x → Clear n (M.body r σ q x)
  clear-under n σ q (out _ _ _) cb = cb
  clear-under n σ q (skip _ _)  cb = cb
  clear-under n σ q (end _)     cb = cb
  clear-under n σ q hush        cb = tt

  clear-next : ∀ n β (σ : Events∞ A) q b → Clear n (force β) → ¬ Ext n q → Clear n (M.ahead r β σ q b)
  clear-next n β σ q true  cb nx = nx
  clear-next n β σ q false cb nx = clear-under n σ q (force β) cb

  -- Where the source next shows, read off what holds just past each step.
  head-shown : ∀ {P : Pos → Set} (σ : Events∞ A) e → force σ ≡ e → Going e → Every∞ (λ q → P (q ++ [ ix 0 ])) σ → P (M.shownAt e)
  head-shown {P} σ e eq g u = go e g (subst (Every (λ q → P (q ++ [ ix 0 ]))) eq (proj₁ u))
    where
      go : ∀ e → Going e → Every (λ q → P (q ++ [ ix 0 ])) e → P (M.shownAt e)
      go (out _ _ _) g pe = proj₁ (every pe)
      go (skip _ _)  g pe = proj₁ (every pe)
      go (end _)     g pe = every pe
      go hush        () pe

  away-head : ∀ k (x : Events A) → Away k x → Head (λ h → ¬ Ext (k ++ [ ix 0 ]) (h ++ [ ix 0 ])) x
  away-head k (out h _ _) aw = λ x → aw (under-ext k h x)
  away-head k (skip h _)  aw = λ x → aw (under-ext k h x)
  away-head k (end h)     aw = λ x → aw (under-ext k h x)
  away-head k hush        aw = tt

  tail-head : ∀ c t → EveryT (TrailE {A} (end c)) t → Head (λ h → ¬ Ext (c ++ [ ix 0 ]) (h ++ [ ix 0 ])) (tailᴱ {A} t)
  tail-head c (pin j u) e = λ x → proj₂ (proj₂ (proj₁ (everyᵀ e))) (under-ext c j x)
  tail-head c idle      e = tt

  -- The source's next shows outside where its step showed.
  next-away : ∀ (σ : Events∞ A) e → Going e → Trail e (cut σ) → Steady e
            → Head (λ h → ¬ Ext (M.shownAt e) (h ++ [ ix 0 ])) (force (M.onward∞ σ e))
  next-away σ (out k _ s) g tr se = away-head k (force s) (past-away k (force s) (proj₁ (steady se)))
  next-away σ (skip k s)  g tr se = away-head k (force s) (clear-away k (force s) (proj₁ (steady se)))
  next-away σ (end c)     g tr se = tail-head c (cut σ) (proj₁ (proj₂ (trail tr)))
  next-away σ hush        () tr se

  UB : Events∞ B → Events∞ A → Set
  UB β σ = Every∞ (λ k → Every∞ (λ q → Unrelated k (q ++ [ ix 0 ])) σ) β

  mutual
    st-beside : ∀ β σ → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → Steady (M.beside r β σ)
    st-beside β σ ts os ss sb u = st-side β σ ts os ss sb u (force σ) refl

    st-side : ∀ β σ → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → ∀ e → force σ ≡ e
            → Steady (M.side r β σ e)
    st-side β σ ts os ss sb u (out k a s) eq = st-ahead β σ ts os ss sb u (out k a s) eq tt _ refl
    st-side β σ ts os ss sb u (skip k s)  eq = st-ahead β σ ts os ss sb u (skip k s) eq tt _ refl
    st-side β σ ts os ss sb u (end c)     eq = st-ahead β σ ts os ss sb u (end c) eq tt _ refl
    st-side β σ ts os ss sb u hush        eq = sb

    st-ahead : ∀ β σ → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → ∀ e → force σ ≡ e → Going e
             → ∀ b → M.before (M.shownAt e) (force β) ≡ b → Steady (M.ahead r β σ (M.shownAt e) b)
    st-ahead β σ ts os ss sb u e eq g true  be = st-src β σ ts os ss sb u e eq g be
    st-ahead β σ ts os ss sb u e eq g false be = st-body σ ts os ss e eq g (force β) sb (proj₁ u) be

    st-src : ∀ β σ → Trailing σ → Ordered (force σ) → Steady (force σ) → Steady (force β) → UB β σ → ∀ e → force σ ≡ e → Going e
           → M.before (M.shownAt e) (force β) ≡ true → Steady (M.ahead r β σ (M.shownAt e) true)
    steady (st-src β σ ts os ss sb u e eq g be) =
      clear-side q β σ′ (force σ′) be (every-mono (λ k w → head-shown {P = Unrelated k} σ e eq g w) (force β) (proj₁ u))
        (subst (λ z → Head (λ h → ¬ Ext q (h ++ [ ix 0 ])) (force (M.onward∞ σ z))) (sym eq)
           (next-away σ e g (subst (λ z → Trail z (cut σ)) eq ts) (subst Steady eq ss)))
      , st-beside β σ′ (trailing-onward σ (force σ) refl ts) (ordered-onward σ (force σ) refl ts os) (steady-onward σ (force σ) refl ts ss) sb
          (every∞-mono (λ k w → every-onward σ (force σ) (proj₁ w) (proj₂ w) (proj₁ w)) β u)
      where q  = M.shownAt e
            σ′ = M.onward∞ σ (force σ)

    st-body : ∀ σ → Trailing σ → Ordered (force σ) → Steady (force σ) → ∀ e → force σ ≡ e → Going e → ∀ x → Steady x
            → Every (λ k → Every∞ (λ q → Unrelated k (q ++ [ ix 0 ])) σ) x → M.before (M.shownAt e) x ≡ false
            → Steady (M.body r σ (M.shownAt e) x)
    steady (st-body σ ts os ss e eq g (out n a β′) sx ux be) =
      past-ahead n β′ σ q (M.before q (force β′)) (proj₁ (steady sx)) (strict n q be (proj₁ un)) (λ x → proj₁ un (ext-prefixed x))
      , st-ahead β′ σ ts os ss (proj₂ (steady sx)) (proj₂ (every ux)) e eq g _ refl
      where q  = M.shownAt e
            un = head-shown {P = Unrelated n} σ e eq g (proj₁ (every ux))
    steady (st-body σ ts os ss e eq g (skip n β′) sx ux be) =
      clear-next n β′ σ q (M.before q (force β′)) (proj₁ (steady sx)) (λ x → proj₁ un (ext-prefixed x))
      , st-ahead β′ σ ts os ss (proj₂ (steady sx)) (proj₂ (every ux)) e eq g _ refl
      where q  = M.shownAt e
            un = head-shown {P = Unrelated n} σ e eq g (proj₁ (every ux))
    steady (st-body σ ts os ss e eq g (end c)     sx ux be) = tt
    steady (st-body σ ts os ss e eq g hush        sx ux be) = tt

  -- A body step keyed under it, a source step apart from it and under
  -- the source's root: the body step no prefix of where the source
  -- step shows.
  easy-pt : ∀ k q → Owned P₀ k → Disjoint P₀ q → Owned r q → ¬ Prefix k (q ++ [ ix 0 ])
  easy-pt k q ok dq oq pr with prefix-split k q (ix 0) pr
  ... | inj₁ pk = proj₁ dq (owned-trans P₀ k q ok (inj₁ pk))
  ... | inj₂ eq = shown₀ (subst (Owned P₀) eq ok)
    where
      shown₀ : ¬ Owned P₀ (q ++ [ ix 0 ])
      shown₀ (inj₂ t) = proj₁ dq (inj₂ (tagged-lane P₀ q 0 t))
      shown₀ (inj₁ pq) with prefix-split P₀ q (ix 0) pq
      ... | inj₁ pq′ = proj₁ dq (inj₁ pq′)
      ... | inj₂ e   = longer p (ix 1) (subst (Owned r) (sym (proj₁ (snoc-inj p q e))) oq)

  -- The body unrelated to the source's shown steps, given that none of
  -- its steps lies under one.
  unrelated : ∀ {β σ} → Side β σ → Every∞ (λ k → Every∞ (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) σ) β → UB β σ
  unrelated {β} {σ} sd hard =
    every∞-mono (λ k x → every∞-mono (λ q y → easy-pt k q (proj₁ x) (proj₁ (proj₁ y)) (proj₂ (proj₁ y)) , proj₂ y) σ
                           (every∞-zip σ (every∞-zip σ (Side.ks sd) (Side.rs sd)) (proj₂ x)))
      β (every∞-zip β (Side.kb sd) hard)

  -- Keyed with none of the connect, keyed with none of its body.
  narrow₀ : ∀ k → ¬ Owned p k → ¬ Owned P₀ k
  narrow₀ k no o = no (owned-trans p P₀ k (inj₁ (prefix-++ p [ ix 0 ])) o)

  pinned-under : ∀ k → M.inside r k ≡ true → Σ Pos (λ ys → k ≡ p ++ ys)
  pinned-under k i = prefix-rest p k (prefix-trans p r k (prefix-++ p [ ix 1 ]) (inside-under r k i))

  -- The source's burst, fresh against any step no earlier than the
  -- connect: what its pins lie inside, outside the connect, lies before it.
  mutual
    fresh-burstOn : ∀ L → L <ᵖ p ≡ false → (σ : Events∞ A) → EveryT (Fresh p L) (cut σ) → FreshRun p (force σ)
                  → EveryT (Fresh p L) (M.burstOn r σ)
    fresh-burstOn L pl σ ct fr = fresh-runOn L pl (force σ) (cut σ) ct fr

    fresh-runOn : ∀ L → L <ᵖ p ≡ false → (e : Events A) → ∀ t → EveryT (Fresh p L) t → FreshRun p e → EveryT (Fresh p L) (M.runOn r e t)
    fresh-runOn L pl (out k _ s) t ct fr = fresh-pinned L pl k s t (M.inside r k) refl ct (proj₁ (freshᴿ fr)) (proj₂ (freshᴿ fr))
    fresh-runOn L pl (skip k s)  t ct fr = fresh-pinned L pl k s t (M.inside r k) refl ct (proj₁ (freshᴿ fr)) (proj₂ (freshᴿ fr))
    fresh-runOn L pl (end _)     t ct fr = ct
    fresh-runOn L pl hush        t ct fr = ct

    fresh-pinned : ∀ L → L <ᵖ p ≡ false → ∀ k (s : Events∞ A) t b → M.inside r k ≡ b → EveryT (Fresh p L) t
                 → EveryT (Fresh p k) (cut s) → FreshRun p (force s) → EveryT (Fresh p L) (M.pinned r k s t b)
    everyᵀ (fresh-pinned L pl k s t true  ib ct cs fs) = at-k , fresh-burstOn L pl s (everyT-mono lift (cut s) cs) fs
      where
        ys = proj₁ (pinned-under k ib)
        ke = proj₂ (pinned-under k ib)
        at-k : Fresh p L k
        at-k k′ x no with ext-eq x
        ... | l , ls , e =
          inj₁ (still k′ p L (below-under p k′ ys (λ q → no (inj₁ q)) (subst (λ z → k′ <ᵖ z ≡ true) (trans (sym e) ke) (<ᵖ-below k′ ls))) pl)
        lift : ∀ h → Fresh p k h → Fresh p L h
        lift h f = fresh-past p p L h pl (fresh-under p ys h (subst (λ z → Fresh p z h) ke f))
    everyᵀ (fresh-pinned L pl k s t false ib ct cs fs) = everyᵀ ct

  -- The source past its next step, fresh against where that step shows.
  fresh-onward : ∀ L (σ : Events∞ A) e → Going e → Trail e (cut σ) → M.shownAt e <ᵖ L ≡ false → EveryT (Fresh p L) (cut σ) → FreshRun p e
               → EveryT (Fresh p (M.shownAt e)) (cut (M.onward∞ σ e)) × FreshRun p (force (M.onward∞ σ e))
  fresh-onward L σ (out k _ s) g tr lq ct fr =
    everyT-mono (λ h → fresh-up p k (k ++ [ ix 0 ]) h (inj₁ (<ᵖ-below k []))) (cut s) (proj₁ (freshᴿ fr)) , proj₂ (freshᴿ fr)
  fresh-onward L σ (skip k s)  g tr lq ct fr =
    everyT-mono (λ h → fresh-up p k (k ++ [ ix 0 ]) h (inj₁ (<ᵖ-below k []))) (cut s) (proj₁ (freshᴿ fr)) , proj₂ (freshᴿ fr)
  fresh-onward L σ (end c)     g tr lq ct fr =
    cq , fresh-tail p (c ++ [ ix 0 ]) (cut σ) cq (everyT-mono (λ j z → marks-past j shown (proj₁ z) (proj₂ (proj₂ z))) (cut σ) (proj₁ (proj₂ (trail tr))))
    where cq = everyT-mono (λ h → fresh-past p L (c ++ [ ix 0 ]) h lq) (cut σ) ct
  fresh-onward L σ hush        () tr lq ct fr

  -- A side the connect last showed at `L`: no earlier than the connect,
  -- nor later than either run's next; both runs' cuts fresh against it.
  record FSide (β : Events∞ B) (σ : Events∞ A) : Set where
    field
      sd : Side β σ
      ob : Ordered (force β)
      L  : Pos
      pL : L <ᵖ p ≡ false
      cL : Cue L (force σ)
      bL : Atop L (force β)
      bc : EveryT (Fresh p L) (cut β)
      sc : EveryT (Fresh p L) (cut σ)
      sr : FreshRun p (force σ)

  -- What a side leaves running is fresh against where it last showed.
  cuts-fresh : ∀ {β σ} (fs : FSide β σ) → EveryT (Fresh p (FSide.L fs)) (M.burstOn r σ ∪ cut β)
  cuts-fresh {β} {σ} fs = everyT-∪ (M.burstOn r σ) (cut β) (fresh-burstOn L pL σ sc sr) bc
    where open FSide fs

  toSourceF : ∀ {β σ} (fs : FSide β σ) e → force σ ≡ e → Going e → M.before (M.shownAt e) (force β) ≡ true → FSide β (M.onward∞ σ (force σ))
  toSourceF {β} {σ} fs e eq g be = record
    { sd = toSource sd e eq g be
    ; ob = ob
    ; L  = M.shownAt e
    ; pL = ≮-trans p L (M.shownAt e) pL qL
    ; cL = cue-onward (M.shownAt e) σ (force σ) refl (Side.ts sd) (Side.os sd) (subst (λ z → Cue (M.shownAt z) (force σ)) eq (cue-self (force σ)))
    ; bL = before-atop (M.shownAt e) (force β) be
    ; bc = everyT-mono (λ h → fresh-past p L (M.shownAt e) h qL) (cut β) bc
    ; sc = proj₁ on
    ; sr = proj₂ on
    }
    where
      open FSide fs
      qL = cue-shown L e g (subst (Cue L) eq cL)
      on = subst (λ z → EveryT (Fresh p (M.shownAt e)) (cut (M.onward∞ σ z)) × FreshRun p (force (M.onward∞ σ z))) (sym eq)
             (fresh-onward L σ e g (subst (λ z → Trail z (cut σ)) eq (Side.ts sd)) qL sc (subst (FreshRun p) eq sr))

  -- THE FRESH WALK: at every state the connect reaches, what it leaves
  -- running is fresh against the step it shows.
  mutual
    fr-beside : ∀ β σ → FSide β σ → FreshRun p (M.beside r β σ)
    fr-beside β σ fs = fr-side β σ fs (force σ) refl

    fr-side : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → FreshRun p (M.side r β σ e)
    fr-side β σ fs (out k a s) eq = fr-ahead β σ fs (out k a s) eq tt _ refl
    fr-side β σ fs (skip k s)  eq = fr-ahead β σ fs (skip k s) eq tt _ refl
    fr-side β σ fs (end c)     eq = fr-ahead β σ fs (end c) eq tt _ refl
    fr-side β σ fs hush        eq = fresh-widen p P₀ narrow₀ (force β) (Side.fr (FSide.sd fs))

    fr-ahead : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → Going e → ∀ b → M.before (M.shownAt e) (force β) ≡ b
             → FreshRun p (M.ahead r β σ (M.shownAt e) b)
    fr-ahead β σ fs e eq g true  be = fr-src β σ fs e eq g be
    fr-ahead β σ fs e eq g false be = fr-body β σ fs e eq g (force β) refl be

    fr-src : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → Going e → M.before (M.shownAt e) (force β) ≡ true
           → FreshRun p (M.ahead r β σ (M.shownAt e) true)
    freshᴿ (fr-src β σ fs e eq g be) = cuts-fresh fs′ , fr-beside β (M.onward∞ σ (force σ)) fs′
      where fs′ = toSourceF fs e eq g be

    fr-body : ∀ β σ → FSide β σ → ∀ e → force σ ≡ e → Going e → ∀ x → force β ≡ x → M.before (M.shownAt e) x ≡ false
            → FreshRun p (M.body r σ (M.shownAt e) x)
    freshᴿ (fr-body β σ fs e eq g (out n a β′) xe be) = cuts-fresh fs′ , fr-ahead β′ σ fs′ e eq g _ refl
      where
        open FSide fs
        tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
        kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
        krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
        frx = subst (FreshRun P₀) xe (Side.fr sd)
        obx = subst Ordered xe ob
        bn  = subst (Atop L) xe bL
        fs′ : FSide β′ σ
        fs′ = record
          { sd = toBody sd e eq n be (proj₁ (every kbx)) β′ (proj₁ (proj₂ (proj₂ (trail tbx)))) (proj₂ (every kbx)) (proj₂ (every krx))
                        (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))
          ; ob = proj₂ (ordered obx)
          ; L  = n
          ; pL = ≮-trans p L n pL bn
          ; cL = subst (Cue n) (sym eq) (shown-cue n e be)
          ; bL = proj₁ (ordered obx)
          ; bc = everyT-mono (λ h f k x no → f k x (narrow₀ k no)) (cut β′) (proj₁ (freshᴿ frx))
          ; sc = everyT-mono (λ h → fresh-past p L n h bn) (cut σ) sc
          ; sr = sr
          }
    freshᴿ (fr-body β σ fs e eq g (skip n β′) xe be) = cuts-fresh fs′ , fr-ahead β′ σ fs′ e eq g _ refl
      where
        open FSide fs
        tbx = subst (λ z → Trail z (cut β)) xe (Side.tb sd)
        kbx = subst (Every (Owned P₀)) xe (proj₁ (Side.kb sd))
        krx = subst (Every (Rise r)) xe (proj₁ (Side.kr sd))
        frx = subst (FreshRun P₀) xe (Side.fr sd)
        obx = subst Ordered xe ob
        bn  = subst (Atop L) xe bL
        fs′ : FSide β′ σ
        fs′ = record
          { sd = toBody sd e eq n be (proj₁ (every kbx)) β′ (proj₂ (proj₂ (trail tbx))) (proj₂ (every kbx)) (proj₂ (every krx))
                        (proj₁ (freshᴿ frx)) (proj₂ (freshᴿ frx))
          ; ob = proj₂ (ordered obx)
          ; L  = n
          ; pL = ≮-trans p L n pL bn
          ; cL = subst (Cue n) (sym eq) (shown-cue n e be)
          ; bL = proj₁ (ordered obx)
          ; bc = everyT-mono (λ h f k x no → f k x (narrow₀ k no)) (cut β′) (proj₁ (freshᴿ frx))
          ; sc = everyT-mono (λ h → fresh-past p L n h bn) (cut σ) sc
          ; sr = sr
          }
    freshᴿ (fr-body β σ fs e eq g (end c) xe be) = tt
    freshᴿ (fr-body β σ fs e eq g hush    xe be) = tt

------------------------------------------------------------------------
-- A flatMap's merge, each part fresh against the last step it showed.

module FlatFresh (p : Pos) where
  K : Pos → Set
  K y = Owned p y × Headed y

  -- A lane in flight: what it leaves running fresh against `L`, its run
  -- fresh, keyed under `p`.
  Lanef : ∀ {B} → Pos → Events∞ B → Set
  Lanef L l = EveryT (Fresh p L) (cut l) × FreshRun p (force l) × Every K (force l)

  -- A lane admitted just past `q` is fresh against the skip the merge
  -- shows at `q`'s left.
  GenF : ∀ {B} → MonotonicList B → Set
  GenF m = ∀ q → K q → Lanef (q ++ [ ix 0 ]) (M.enter m (q ++ [ ix 1 ]))

  Freshᴼ : ∀ {B} → Pos → Maybe (Events∞ (MonotonicList B)) → Set
  Freshᴼ L nothing  = ⊤
  Freshᴼ L (just e) = EveryT (Fresh p L) (cut e) × FreshRun p (force e) × Values GenF (force e) × Every K (force e)

  -- Fresh against a step, fresh against any after it.
  up : ∀ L L′ → L′ <ᵖ L ≡ false → (t : Tail) → EveryT (Fresh p L) t → EveryT (Fresh p L′) t
  up L L′ a = everyT-mono (λ h → fresh-past p L L′ h a)

  lane-up : ∀ {B} L L′ → L′ <ᵖ L ≡ false → (l : Events∞ B) → Lanef L l → Lanef L′ l
  lane-up L L′ a l (c , r , k) = up L L′ a (cut l) c , r , k

  lanes-up : ∀ {B} L L′ → L′ <ᵖ L ≡ false → (ls : List (Events∞ B)) → All (Lanef L) ls → All (Lanef L′) ls
  lanes-up L L′ a ls = mapᴬ (λ {l} → lane-up L L′ a l)

  outer-up : ∀ {B} L L′ → L′ <ᵖ L ≡ false → (o : Maybe (Events∞ (MonotonicList B))) → Freshᴼ L o → Freshᴼ L′ o
  outer-up L L′ a nothing  fo            = tt
  outer-up L L′ a (just e) (c , r , v , k) = up L L′ a (cut e) c , r , v , k

  cuts-fresh : ∀ {B} L (ls : List (Events∞ B)) → All (Lanef L) ls → EveryT (Fresh p L) (M.cuts ls)
  cuts-fresh L []       []ᴬ        = everyT-idle
  cuts-fresh L (l ∷ ls) (fl ∷ᴬ al) = everyT-∪ (cut l) (M.cuts ls) (proj₁ fl) (cuts-fresh L ls al)

  whole-fresh : ∀ {B} L (o : Maybe (Events∞ (MonotonicList B))) ls t → Freshᴼ L o → All (Lanef L) ls → EveryT (Fresh p L) t
              → EveryT (Fresh p L) (M.whole o ls t)
  whole-fresh L nothing  ls t fo fl ft = everyT-∪ idle (M.cuts ls ∪ t) everyT-idle (everyT-∪ (M.cuts ls) t (cuts-fresh L ls fl) ft)
  whole-fresh L (just e) ls t fo fl ft = everyT-∪ (cut e) (M.cuts ls ∪ t) (proj₁ fo) (everyT-∪ (M.cuts ls) t (cuts-fresh L ls fl) ft)

  -- An admitted lane runs fresh, a queued one stays fresh where it would
  -- be admitted, and a dropped one leaves its tail.
  Admittedᶠ : ∀ {B} → Pos → List (Events∞ B) × List (MonotonicList B) × Tail → Set
  Admittedᶠ L (ls , qs , d) = All (Lanef L) ls × All GenF qs × EveryT (Fresh p L) d

  admit-fresh : ∀ {B} op q (m : MonotonicList B) ls qs L → Lanef L (M.enter m q) → GenF m → All (Lanef L) ls → All GenF qs
              → Admittedᶠ L (M.admit op q m ls qs)
  admit-fresh (M.mergeᶠ nothing)  q m ls       qs L lm gm fl fq = lm ∷ᴬ fl , fq , everyT-idle
  admit-fresh (M.mergeᶠ (just n)) q m ls       qs L lm gm fl fq with length ls <ᵇ n
  ... | true  = lm ∷ᴬ fl , fq , everyT-idle
  ... | false = fl , All++⁺ fq (gm ∷ᴬ []ᴬ) , everyT-idle
  admit-fresh M.switchᶠ           q m ls       qs L lm gm fl fq = lm ∷ᴬ []ᴬ , fq , cuts-fresh L ls fl
  admit-fresh M.exhaustᶠ          q m []       qs L lm gm fl fq = lm ∷ᴬ []ᴬ , fq , everyT-idle
  admit-fresh M.exhaustᶠ          q m (l ∷ ls) qs L lm gm fl fq = fl , fq , everyT-idle

  -- Each step the merge shows is no earlier than the last, so every part
  -- fresh against the last is fresh against it; the part that showed it
  -- is fresh against it by its own run.
  mutual
    fr-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
          → EveryT (Fresh p L) t → Atop L (M.go op o ls qs t) → Ordered (M.go op o ls qs t) → FreshRun p (M.go op o ls qs t)
    freshᴿ (fr-go op o ls qs idle      L fo fl fq ft at od) = freshᴿ (fr-parts op o ls qs idle L fo fl fq ft at od)
    freshᴿ (fr-go op o ls qs (pin k u) L fo fl fq ft at od) =
      freshᴿ (fr-left op o ls qs k u (M.ahead-of k o ls) L fo fl fq ft at od)

    fr-left : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u b L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
            → EveryT (Fresh p L) (pin k u) → Atop L (M.left op o ls qs k u b) → Ordered (M.left op o ls qs k u b)
            → FreshRun p (M.left op o ls qs k u b)
    freshᴿ (fr-left op o ls qs k u true  L fo fl fq ft at od) =
      whole-fresh k o ls (later u) fo′ fl′ ft′ , fr-go op o ls qs (later u) k fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L k at o fo
        fl′ = lanes-up L k at ls fl
        ft′ = up L k at (later u) (proj₂ (everyᵀ ft))
    freshᴿ (fr-left op o ls qs k u false L fo fl fq ft at od) = freshᴿ (fr-parts op o ls qs (pin k u) L fo fl fq ft at od)

    fr-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
             → EveryT (Fresh p L) t → Atop L (M.parts op o ls qs t) → Ordered (M.parts op o ls qs t) → FreshRun p (M.parts op o ls qs t)
    fr-parts op o ls qs t L fo fl fq ft at od with M.earliest ls | earliest-all (Lanef L) ls fl
    ... | none            | _               = fr-via op o ls qs t L fo fl fq ft at od
    ... | found k bs l as | (fb , fl₁ , fa) = fr-race op o k bs l as qs t L fo fb fl₁ fa fq ft at od

    fr-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
           → EveryT (Fresh p L) t → Atop L (M.viaOuter op o ls qs t) → Ordered (M.viaOuter op o ls qs t)
           → FreshRun p (M.viaOuter op o ls qs t)
    fr-via op nothing  ls qs t L fo                  fl fq ft at od = record { freshᴿ = tt }
    fr-via op (just e) ls qs t L (ce , re , ve , ke) fl fq ft at od = fr-outer op e ls qs t (force e) L ce re ve ke fl fq ft at od

    fr-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t L → Freshᴼ L o
            → All (Lanef L) bs → Lanef L l → All (Lanef L) as → All GenF qs → EveryT (Fresh p L) t
            → Atop L (M.race op o k bs l as qs t) → Ordered (M.race op o k bs l as qs t) → FreshRun p (M.race op o k bs l as qs t)
    fr-race op nothing  k bs l as qs t L fo fb (cl , rl , kl) fa fq ft at od =
      fr-lane op nothing bs l as qs t (force l) L fo fb cl rl kl fa fq ft at od
    fr-race op (just e) k bs l as qs t L fo fb (cl , rl , kl) fa fq ft at od with M.head (force e)
    ... | nothing = fr-lane op (just e) bs l as qs t (force l) L fo fb cl rl kl fa fq ft at od
    ... | just k′ with k′ <ᵖ k
    ...   | true  = fr-outer op e (bs ++ l ∷ as) qs t (force e) L (proj₁ fo) (proj₁ (proj₂ fo)) (proj₁ (proj₂ (proj₂ fo)))
                      (proj₂ (proj₂ (proj₂ fo))) (All++⁺ fb ((cl , rl , kl) ∷ᴬ fa)) fq ft at od
    ...   | false = fr-lane op (just e) bs l as qs t (force l) L fo fb cl rl kl fa fq ft at od

    fr-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) L → EveryT (Fresh p L) (cut e)
             → FreshRun p x → Values GenF x → Every K x → All (Lanef L) ls → All GenF qs → EveryT (Fresh p L) t
             → Atop L (M.outer op e ls qs t x) → Ordered (M.outer op e ls qs t x) → FreshRun p (M.outer op e ls qs t x)
    freshᴿ (fr-outer op e ls qs t (out q m r) L ce rx vx kx fl fq ft at od) with M.admit op (q ++ [ ix 1 ]) m ls qs in eq
    ... | ls′ , qs′ , d =
      whole-fresh Q (just r) ls′ (t ∪ d) fo′ (proj₁ ad) ft′
      , fr-go op (just r) ls′ qs′ (t ∪ d) Q fo′ (proj₁ ad) (proj₁ (proj₂ ad)) ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        Q = q ++ [ ix 0 ]
        fo′ : Freshᴼ Q (just r)
        fo′ = everyT-mono (λ h → fresh-up p q Q h (inj₁ (<ᵖ-below q []))) (cut r) (proj₁ (freshᴿ rx)) , proj₂ (freshᴿ rx)
              , proj₂ (values vx) , proj₁ (proj₂ (every kx))
        ad : Admittedᶠ Q (ls′ , qs′ , d)
        ad = subst (Admittedᶠ Q) eq
               (admit-fresh op (q ++ [ ix 1 ]) m ls qs Q (proj₁ (values vx) q (proj₁ (every kx))) (proj₁ (values vx))
                  (lanes-up L Q at ls fl) fq)
        ft′ = everyT-∪ t d (up L Q at t ft) (proj₂ (proj₂ ad))
    freshᴿ (fr-outer op e ls qs t (skip q r) L ce rx vx kx fl fq ft at od) =
      whole-fresh q (just r) ls t fo′ fl′ ft′ , fr-go op (just r) ls qs t q fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ : Freshᴼ q (just r)
        fo′ = proj₁ (freshᴿ rx) , proj₂ (freshᴿ rx) , values vx , proj₁ (proj₂ (every kx))
        fl′ = lanes-up L q at ls fl
        ft′ = up L q at t ft
    freshᴿ (fr-outer op e []       []       t (end c) L ce rx vx kx fl fq ft at od) = tt
    freshᴿ (fr-outer {B} op e []       (m ∷ qs) t (end c) L ce rx vx kx fl fq ft at od) =
      whole-fresh {B} c nothing [] (t ∪ cut e) tt []ᴬ ft′ , fr-go op nothing [] (m ∷ qs) (t ∪ cut e) c tt []ᴬ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where ft′ = everyT-∪ t (cut e) (up L c at t ft) (up L c at (cut e) ce)
    freshᴿ (fr-outer op e (l ∷ ls) qs       t (end c) L ce rx vx kx fl fq ft at od) =
      whole-fresh c nothing (l ∷ ls) (t ∪ cut e) tt fl′ ft′
      , fr-go op nothing (l ∷ ls) qs (t ∪ cut e) c tt fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fl′ = lanes-up L c at (l ∷ ls) fl
        ft′ = everyT-∪ t (cut e) (up L c at t ft) (up L c at (cut e) ce)
    freshᴿ (fr-outer op e ls       qs       t hush    L ce rx vx kx fl fq ft at od) = tt

    fr-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) L → Freshᴼ L o
            → All (Lanef L) bs → EveryT (Fresh p L) (cut l) → FreshRun p x → Every K x → All (Lanef L) as → All GenF qs
            → EveryT (Fresh p L) t → Atop L (M.lane op o bs l as qs t x) → Ordered (M.lane op o bs l as qs t x)
            → FreshRun p (M.lane op o bs l as qs t x)
    freshᴿ (fr-lane op o bs l as qs t (out k b r) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh k o (bs ++ r ∷ as) t fo′ fl′ ft′ , fr-go op o (bs ++ r ∷ as) qs t k fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L k at o fo
        fl′ = All++⁺ (lanes-up L k at bs fb) ((proj₁ (freshᴿ rx) , proj₂ (freshᴿ rx) , proj₁ (proj₂ (every kx))) ∷ᴬ lanes-up L k at as fa)
        ft′ = up L k at t ft
    freshᴿ (fr-lane op o bs l as qs t (skip k r) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh k o (bs ++ r ∷ as) t fo′ fl′ ft′ , fr-go op o (bs ++ r ∷ as) qs t k fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L k at o fo
        fl′ = All++⁺ (lanes-up L k at bs fb) ((proj₁ (freshᴿ rx) , proj₂ (freshᴿ rx) , proj₁ (proj₂ (every kx))) ∷ᴬ lanes-up L k at as fa)
        ft′ = up L k at t ft
    freshᴿ (fr-lane op o bs l as (m ∷ qs) t (end c) L fo fb cl rx kx fa (gm ∷ᴬ fq) ft at od) =
      whole-fresh Q o ls′ (t ∪ cut l) fo′ fl′ ft′ , fr-go op o ls′ qs (t ∪ cut l) Q fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        Q = c ++ [ ix 0 ]
        ls′ = M.enter m (c ++ [ ix 1 ]) ∷ bs ++ as
        fo′ = outer-up L Q at o fo
        fl′ = gm c (every kx) ∷ᴬ All++⁺ (lanes-up L Q at bs fb) (lanes-up L Q at as fa)
        ft′ = everyT-∪ t (cut l) (up L Q at t ft) (up L Q at (cut l) cl)
    freshᴿ (fr-lane op nothing  []       l []       [] t (end c) L fo fb cl rx kx fa fq ft at od) = tt
    freshᴿ (fr-lane op nothing  []       l (a ∷ as) [] t (end c) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh c nothing (a ∷ as) (t ∪ cut l) tt fl′ ft′ , fr-go op nothing (a ∷ as) [] (t ∪ cut l) c tt fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fl′ = lanes-up L c at (a ∷ as) fa
        ft′ = everyT-∪ t (cut l) (up L c at t ft) (up L c at (cut l) cl)
    freshᴿ (fr-lane op nothing  (b ∷ bs) l as       [] t (end c) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh c nothing (b ∷ bs ++ as) (t ∪ cut l) tt fl′ ft′
      , fr-go op nothing (b ∷ bs ++ as) [] (t ∪ cut l) c tt fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fl′ = All++⁺ (lanes-up L c at (b ∷ bs) fb) (lanes-up L c at as fa)
        ft′ = everyT-∪ t (cut l) (up L c at t ft) (up L c at (cut l) cl)
    freshᴿ (fr-lane op (just e) bs       l as       [] t (end c) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh c (just e) (bs ++ as) (t ∪ cut l) fo′ fl′ ft′
      , fr-go op (just e) (bs ++ as) [] (t ∪ cut l) c fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L c at (just e) fo
        fl′ = All++⁺ (lanes-up L c at bs fb) (lanes-up L c at as fa)
        ft′ = everyT-∪ t (cut l) (up L c at t ft) (up L c at (cut l) cl)
    freshᴿ (fr-lane op o bs l as qs t hush L fo fb cl rx kx fa fq ft at od) = tt

-- Two marks under one position, neither's lane keyed by the other's,
-- nor its lane by it.
sibling-spread : ∀ p {l l′} → Mark l → Mark l′ → l ≢ l′
               → Disjoint ((p ++ [ l ]) ++ [ ix 1 ]) ((p ++ [ l′ ]) ++ [ ix 1 ]) × ¬ Owned (p ++ [ l ]) ((p ++ [ l′ ]) ++ [ ix 1 ])
sibling-spread p {l} {l′} m m′ ne = disjoint-swap _ _ d₂ , proj₁ d₁
  where
    d₁ = apart-mark (p ++ [ l ]) (p ++ [ l′ ]) (ix 1) (ix-mark 1) (sibling p m′ ne , sibling p m (λ e → ne (sym e)))
    d₂ = apart-mark ((p ++ [ l′ ]) ++ [ ix 1 ]) (p ++ [ l ]) (ix 1) (ix-mark 1) (disjoint-swap _ _ d₁)

weigh-++ : ∀ a b → weigh (a ++ b) ≡ weigh a + weigh b
weigh-++ []      b = refl
weigh-++ (l ∷ a) b = trans (cong (weighˡ l +_) (weigh-++ a b)) (sym (+-assoc (weighˡ l) (weigh a) (weigh b)))

-- A position keyed under a value's lane shares its second label: a tag
-- the value's own root holds, so smaller than it.
second-sub : ∀ r i n e z → Prefix ((r ++ [ ix i ]) ++ [ ix 1 ]) (ix n ∷ sub e ∷ z) → weigh e < weigh r
second-sub []           i n e z (_ , () , _)
second-sub (a ∷ [])     i n e z (_ , () , _)
second-sub (a ∷ b ∷ r′) i n e z (_ , refl , _) = ≤-trans (m≤m+n (suc (weigh e)) (weigh r′)) (m≤n+m _ (weighˡ a))

-- After a value at `r ++ [ ix i ]` of a cold's burst: the burst's later
-- steps its siblings, and every later frame rooted past the close, its
-- root tagging the close before it, so heavier than the value's lane.
module Apart {A : Set} (τ : ℕ) (r : Pos) (i : ℕ) where
  private
    X1 = (r ++ [ ix i ]) ++ [ ix 1 ]

  data Chain : Pos → Set where
    base : Chain (r ++ [ last ])
    step : ∀ {e} n → Chain e → Chain (ix n ∷ sub e ∷ last ∷ [])

  x1≡ : weigh X1 ≡ (weigh r + 1) + 1
  x1≡ = trans (weigh-++ (r ++ [ ix i ]) [ ix 1 ]) (cong (_+ 1) (weigh-++ r [ ix i ]))

  chain-weigh : ∀ {e} → Chain e → weigh r + 1 ≤ weigh e
  chain-weigh base         = subst (_≤ weigh (r ++ [ last ])) (weigh-++ r [ last ]) ≤-refl
  chain-weigh (step {e} n c) = ≤-trans (chain-weigh c) (≤-trans (m≤m+n (weigh e) 1) (≤-trans (n≤1+n _) (n≤1+n _)))

  nested : ∀ {e} → Chain e → weigh e < weigh r → ⊥
  nested c lt = <-irrefl refl (<-≤-trans lt (≤-trans (m≤m+n (weigh r) 1) (chain-weigh c)))

  frame-big : ∀ {e} → Chain e → ∀ n {l} → Mark l → weigh X1 < weigh (ix n ∷ sub e ∷ l ∷ [])
  frame-big {e} c n (ix-mark _) = subst (_< _) (sym x1≡) (s≤s (≤-trans (+-monoˡ-≤ 1 (chain-weigh c)) (n≤1+n (weigh e + 1))))
  frame-big {e} c n last-mark   = subst (_< _) (sym x1≡) (s≤s (≤-trans (+-monoˡ-≤ 1 (chain-weigh c)) (n≤1+n (weigh e + 1))))

  big : ∀ {h} → weigh X1 < weigh h → ¬ Owned h X1
  big lt o = <-irrefl refl (<-≤-trans lt (owned-weigh _ _ o))

  big-ext : ∀ {h} z → weigh X1 < weigh h → ¬ Owned (h ++ z) X1
  big-ext {h} z lt = big (<-≤-trans lt (prefix-weigh h (h ++ z) (prefix-++ h z)))

  no-own : ∀ {e} → Chain e → ¬ Owned X1 e
  no-own base o = sibling r last-mark (λ ()) (owned-trans (r ++ [ ix i ]) X1 (r ++ [ last ]) (inj₁ (prefix-++ (r ++ [ ix i ]) [ ix 1 ])) o)
  no-own (step {e} n c) (inj₁ q)        = nested c (second-sub r i n e _ q)
  no-own (step n c)     (inj₂ (inj₁ o)) = no-own c o
  no-own (step n c)     (inj₂ (inj₂ ()))

  far : ∀ {e} → Chain e → ∀ n {l} → Mark l → ¬ Owned X1 (ix n ∷ sub e ∷ l ∷ ix 1 ∷ [])
  far {e} c n m           (inj₁ q)        = nested c (second-sub r i n e _ q)
  far c n m               (inj₂ (inj₁ o)) = no-own c o
  far c n (ix-mark _)     (inj₂ (inj₂ ()))
  far c n last-mark       (inj₂ (inj₂ ()))

  frame-sp : ∀ {e} → Chain e → ∀ n {l} → Mark l → Sp (r ++ [ ix i ]) (ix n ∷ sub e ∷ l ∷ [])
  frame-sp c n m = (big-ext [ ix 1 ] (frame-big c n m) , far c n m) , big (frame-big c n m)

  mutual
    frames-apart : ∀ {e t} → Chain e → Sp (r ++ [ ix i ]) e → (m : From A t) → Every (Sp (r ++ [ ix i ])) (M.frames τ e m)
    frames-apart c ok M.done       = record { every = ok }
    frames-apart c ok M.quiet      = record { every = tt }
    frames-apart c ok (M.at t _ b) = chain-burst (τ + t) c 0 b

    chain-burst : ∀ {e t} n → Chain e → ∀ j (b : M.Frame A t) → Every (Sp (r ++ [ ix i ])) (M.burst τ (ix n ∷ sub e ∷ []) j b)
    every (chain-burst n c j (M.emit a k)) = frame-sp c n (ix-mark j) , chain-burst n c (suc j) (M.Frame∞.force k) , everyT-idle
    every (chain-burst n c j (M.stall k))  = frame-sp c n (ix-mark j) , chain-burst n c (suc j) (M.Frame∞.force k) , everyT-idle
    every (chain-burst n c j (M.close k))  =
      frame-sp c n (ix-mark j) , frames-apart (step n c) (frame-sp c n last-mark) (M.From∞.force k) , everyT-idle

  burst-apart : ∀ {t} j → i < j → (b : M.Frame A t) → Every (Sp (r ++ [ ix i ])) (M.burst τ r j b)
  every (burst-apart j lt (M.emit a k)) = sib j lt , burst-apart (suc j) (<-≤-trans lt (n≤1+n j)) (M.Frame∞.force k) , everyT-idle
    where sib : ∀ j → i < j → Sp (r ++ [ ix i ]) (r ++ [ ix j ])
          sib j lt = sibling-spread r (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl })
  every (burst-apart j lt (M.stall k))  = sib j lt , burst-apart (suc j) (<-≤-trans lt (n≤1+n j)) (M.Frame∞.force k) , everyT-idle
    where sib : ∀ j → i < j → Sp (r ++ [ ix i ]) (r ++ [ ix j ])
          sib j lt = sibling-spread r (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl })
  every (burst-apart j lt (M.close k))  =
    sibling-spread r (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl })
    , frames-apart base (sibling-spread r last-mark (ix-mark i) (λ ())) (M.From∞.force k) , everyT-idle

-- A COLD LEAF'S RUN SPREADS: each burst's steps siblings, each frame
-- tagged by the close before it.
spread-frames : ∀ {A t} τ e (m : From A t) → Spread (M.frames τ e m)
spread-burst : ∀ {A t} τ r i (b : M.Frame A t) → Spread (M.burst τ r i b)
spread-frames τ e M.done       = record { spread = tt }
spread-frames τ e M.quiet      = record { spread = tt }
spread-frames τ e (M.at t _ b) = spread-burst τ (ix (τ + t) ∷ sub e ∷ []) 0 b

spread (spread-burst τ r i (M.emit a k)) =
  (Apart.burst-apart τ r i (suc i) ≤-refl (M.Frame∞.force k) , everyT-idle) , spread-burst τ r (suc i) (M.Frame∞.force k)
spread (spread-burst τ r i (M.stall k))  = spread-burst τ r (suc i) (M.Frame∞.force k)
spread (spread-burst τ r i (M.close k))  = spread-frames τ (r ++ [ last ]) (M.From∞.force k)

spread-start : ∀ {A} p (m : From A 0) → Headed p → Spread (M.start p m)
spread-start p (M.at zero _ b)    _ = spread-burst (tick p) p 0 b
spread-start p (M.at (suc t) l b) _ = spread-frames (tick p) (p ++ [ last ]) (M.at (suc t) l b)
spread-start p M.done             _ = spread-frames {t = 0} (tick p) (p ++ [ last ]) M.done
spread-start p M.quiet            _ = spread-frames {t = 0} (tick p) (p ++ [ last ]) M.quiet

-- A LIST'S RUN SPREADS: its values siblings, its end beside them.
of-apart : ∀ {A} p i j (xs : List A) → i < j
         → Every (λ y → Disjoint (y ++ [ ix 1 ]) ((p ++ [ ix i ]) ++ [ ix 1 ]) × ¬ Owned y ((p ++ [ ix i ]) ++ [ ix 1 ])) (M.ofᴱ p j xs)
every (of-apart p i j []       lt) = sibling-spread p last-mark (ix-mark i) (λ ())
every (of-apart p i j (x ∷ xs) lt) =
  sibling-spread p (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl }) , of-apart p i (suc j) xs (<-≤-trans lt (m≤n+m j 1)) , everyT-idle

spread-of : ∀ {A} p i (xs : List A) → Spread (M.ofᴱ p i xs)
spread (spread-of p i [])       = tt
spread (spread-of p i (x ∷ xs)) = (of-apart p i (suc i) xs ≤-refl , everyT-idle) , spread-of p (suc i) xs

-- A cut shows its source's positions, or a step just under one.
module _ {P : Pos → Set} (d₀ : ∀ h → P h → P (h ++ [ ix 0 ])) (dₗ : ∀ h → P h → P (h ++ [ last ])) where
  mutual
    every-cut : ∀ {A} i (q : A → Bool) (e : Events A) → Every P e → Every P (M.takeWhileᴱ i q e)
    every (every-cut i q (out k a r) pe) = every (every-cutting i q k a (q a) r pe)
    every (every-cut i q (skip k r)  pe) = proj₁ (every pe) , every-cut i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-cut i q (end k)     pe) = every pe
    every (every-cut i q hush        pe) = tt

    every-cutting : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) → Every P (out k a r) → Every P (M.taking i q k a b r)
    every (every-cutting i     q k a true  r pe) = proj₁ (every pe) , every-cut i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-cutting true  q k a false r pe) = d₀ k (proj₁ (every pe)) , record { every = dₗ k (proj₁ (every pe)) } , proj₂ (proj₂ (every pe))
    every (every-cutting false q k a false r pe) = dₗ k (proj₁ (every pe))

-- Apart from a lane, a step just under it too.
sp-mark : ∀ x k {l} → Mark l → Sp x k → Sp x (k ++ [ l ])
sp-mark x k {l} m ((_ , b) , c) =
  ( (λ o → c (owned-drop k [ l ] _ (owned-drop (k ++ [ l ]) [ ix 1 ] _ o)))
  , proj₁ (apart-mark (x ++ [ ix 1 ]) (k ++ [ l ]) (ix 1) (ix-mark 1) (apart-mark (x ++ [ ix 1 ]) k l m (nk , c))) )
  , (λ o → c (owned-drop k [ l ] _ o))
  where
    nk : ¬ Owned (x ++ [ ix 1 ]) k
    nk o = b (owned-trans (x ++ [ ix 1 ]) k (k ++ [ ix 1 ]) o (inj₁ (prefix-++ k [ ix 1 ])))

-- What a source left running apart from a value: apart from the step
-- kept just inside it.
sp-cut : ∀ k t → Disjoint k t → Sp (k ++ [ ix 0 ]) t
sp-cut k t d =
  ( (λ o → proj₁ d₁ (owned-drop t [ ix 1 ] _ o))
  , (λ o → proj₁ (apart-mark k t (ix 1) (ix-mark 1) d) (owned-drop k [ ix 0 ] _ (owned-drop (k ++ [ ix 0 ]) [ ix 1 ] _ o))) )
  , proj₁ d₁
  where
    d₁ = apart-mark t (k ++ [ ix 0 ]) (ix 1) (ix-mark 1) (apart-mark t k (ix 0) (ix-mark 0) (disjoint-swap k t d))

-- A CUT SPREADS ITS SOURCE'S RUN: a failing value kept just inside its
-- own position, which nothing its source left running keys.
spread-take : ∀ {A} i (q : A → Bool) (e : Events A) c → Trail e c → Spread e → Spread (M.takeWhileᴱ i q e)
spread-taking : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) c → Trail (out k a r) c → Spread (out k a r) → Spread (M.taking i q k a b r)
spread (spread-take i q (out k a r) c t s) = spread (spread-taking i q k a (q a) r c t s)
spread (spread-take i q (skip k r)  c t s) = spread-take i q (force r) (cut r) (proj₂ (proj₂ (trail t))) (spread s)
spread (spread-take i q (end k)     c t s) = tt
spread (spread-take i q hush        c t s) = tt

spread (spread-taking i     q k a true  r c t s) =
  ( every-cut (λ h → sp-mark k h (ix-mark 0)) (λ h → sp-mark k h last-mark) i q (force r) (proj₁ (proj₁ (spread s)))
  , proj₂ (proj₁ (spread s)) )
  , spread-take i q (force r) (cut r) (proj₁ (proj₂ (proj₂ (trail t)))) (proj₂ (spread s))
spread (spread-taking true  q k a false r c t s) =
  ( record { every = sibling-spread k last-mark (ix-mark 0) (λ ()) }
  , everyT-mono (sp-cut k) (cut r) (proj₂ (proj₂ (proj₂ (trail t)))) )
  , record { spread = tt }
spread (spread-taking false q k a false r c t s) = tt

-- Two of a source's positions apart, the second alien to the joiner,
-- both tagged with it: the first keys nothing of the second's lane.
tagged-apart : ∀ p a b → ¬ Owned p b → a ≢ b → ¬ Owned (a ++ [ sub p ]) ((b ++ [ sub p ]) ++ [ ix 1 ])
tagged-apart p a b nb ne (inj₁ pr) with prefix-split (a ++ [ sub p ]) (b ++ [ sub p ]) (ix 1) pr
... | inj₂ eq = snoc-ne a (b ++ [ sub p ]) (λ ()) eq
... | inj₁ pr′ with prefix-split (a ++ [ sub p ]) b (sub p) pr′
...   | inj₁ pb = nb (sub-owned a p b (inj₁ pb))
...   | inj₂ eq = ne (proj₁ (snoc-inj a b eq))
tagged-apart p a b nb ne (inj₂ t) with tagged-split (a ++ [ sub p ]) b p (tagged-lane (a ++ [ sub p ]) (b ++ [ sub p ]) 1 t)
... | inj₁ tb = nb (inj₂ (sub-tagged a p b tb))
... | inj₂ o  = heavy a p o

-- A joiner's own step keys nothing of a tagged lane over a source alien
-- to it, and the tagged position nothing of the step's lane.
pre-apart : ∀ p q l → ¬ Owned p q → ¬ Owned (p ++ [ l ]) ((q ++ [ sub p ]) ++ [ ix 1 ])
pre-apart p q l nq (inj₂ t) with tagged-split (p ++ [ l ]) q p (tagged-lane (p ++ [ l ]) (q ++ [ sub p ]) 1 t)
... | inj₁ tq = nq (owned-drop p [ l ] q (inj₂ tq))
... | inj₂ o  = longer p l o
pre-apart p q l nq (inj₁ pr) with prefix-split p (q ++ [ sub p ]) (ix 1) (prefix-trans p (p ++ [ l ]) ((q ++ [ sub p ]) ++ [ ix 1 ]) (prefix-++ p [ l ]) pr)
... | inj₂ eq = heavy q p (inj₁ (subst (Prefix (q ++ [ sub p ])) (sym eq) (prefix-++ (q ++ [ sub p ]) [ ix 1 ])))
... | inj₁ pr′ with prefix-split p q (sub p) pr′
...   | inj₁ pq = nq (inj₁ pq)
...   | inj₂ eq = heavy q p (inj₁ (subst (Prefix (q ++ [ sub p ])) (sym eq) (prefix-refl (q ++ [ sub p ]))))

pre-apart′ : ∀ p q {l} → Mark l → ¬ Owned (q ++ [ sub p ]) ((p ++ [ l ]) ++ [ ix 1 ])
pre-apart′ p q {l} m (inj₁ pr) with prefix-split (q ++ [ sub p ]) (p ++ [ l ]) (ix 1) pr
... | inj₂ eq = snoc-ne q (p ++ [ l ]) (λ ()) eq
... | inj₁ pr′ with prefix-split (q ++ [ sub p ]) p l pr′
...   | inj₁ pp = heavy q p (inj₁ pp)
...   | inj₂ eq = snoc-ne q p (mark-sub m p) eq
pre-apart′ p q {l} m (inj₂ t) =
  heavy q p (inj₂ (tagged-mark (q ++ [ sub p ]) p l m (tagged-lane (q ++ [ sub p ]) (p ++ [ l ]) 1 t)))

sp-join : ∀ p q h → ¬ Owned p q → ¬ Owned p h → q <ᵖ h ≡ true → Sp (q ++ [ sub p ]) (h ++ [ sub p ])
sp-join p q h nq nh qh =
  ( (λ o → tagged-apart p h q nq hq (owned-drop (h ++ [ sub p ]) [ ix 1 ] _ o))
  , (λ o → tagged-apart p q h nh (λ e → hq (sym e)) (owned-drop (q ++ [ sub p ]) [ ix 1 ] _ o)) )
  , tagged-apart p h q nq hq
  where
    hq : h ≢ q
    hq e with trans (sym (subst (λ x → q <ᵖ x ≡ true) e qh)) (<ᵖ-irrefl q)
    ... | ()

sp-pre : ∀ p q {l} → Mark l → ¬ Owned p q → Sp (q ++ [ sub p ]) (p ++ [ l ])
sp-pre p q {l} m nq =
  ( (λ o → pre-apart p q l nq (owned-drop (p ++ [ l ]) [ ix 1 ] _ o))
  , (λ o → pre-apart′ p q m (owned-drop (q ++ [ sub p ]) [ ix 1 ] _ o)) )
  , pre-apart p q l nq

-- Strictly past `q`, then no earlier than that: strictly past `q`.
beyond-on : ∀ {A} q h (e : Events A) → q <ᵖ h ≡ true → Atop h e → Beyond q e
beyond-on q h (out k _ _) qh a with <ᵖ-split h k a
... | inj₁ hk   = <ᵖ-trans q h k qh hk
... | inj₂ refl = qh
beyond-on q h (skip k _)  qh a with <ᵖ-split h k a
... | inj₁ hk   = <ᵖ-trans q h k qh hk
... | inj₂ refl = qh
beyond-on q h (end k)     qh a with <ᵖ-split h k a
... | inj₁ hk   = <ᵖ-trans q h k qh hk
... | inj₂ refl = qh
beyond-on q h hush        qh a = tt

-- What a joiner shows after a value tagged from `q`, over a source past
-- it: tagged from past `q`, or its own step.
module _ (p q : Pos) (nq : ¬ Owned p q) where
  mutual
    sp-rejoin : ∀ {A} (e : Events A) → Alien p e → Ordered e → Beyond q e → Every (Sp (q ++ [ sub p ])) (M.rejoin p e)
    every (sp-rejoin (out h a k) al o b) =
      every (sp-shown h (just a) k (p <ᵖ h) (proj₁ (every al)) (proj₁ (proj₂ (every al))) (proj₁ (ordered o)) (proj₂ (ordered o)) b)
    every (sp-rejoin (skip h k)  al o b) =
      every (sp-shown h nothing k (p <ᵖ h) (proj₁ (every al)) (proj₁ (proj₂ (every al))) (proj₁ (ordered o)) (proj₂ (ordered o)) b)
    every (sp-rejoin (end c)     al o b) with p <ᵖ c
    ... | true  = sp-join p q c nq (every al) b
    ... | false = sp-pre p q last-mark nq
    every (sp-rejoin hush        al o b) = tt

    sp-shown : ∀ {A} h (a : Maybe A) (k : Events∞ A) c → ¬ Owned p h → Alien p (force k) → Atop h (force k) → Ordered (force k)
             → q <ᵖ h ≡ true → Every (Sp (q ++ [ sub p ])) (M.shown p h a k c)
    every (sp-shown h (just a) k true  nh al at o qh) =
      sp-join p q h nq nh qh , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle
    every (sp-shown h nothing  k true  nh al at o qh) =
      sp-join p q h nq nh qh , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle
    every (sp-shown h (just a) k false nh al at o qh) =
      sp-pre p q (ix-mark 0) nq , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle
    every (sp-shown h nothing  k false nh al at o qh) =
      sp-pre p q (ix-mark 0) nq , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle

-- A JOINER'S RUN SPREADS over a source in order, steady and alien to
-- it: each value its source's, tagged with the joiner.
spread-rejoin : ∀ {A} p (e : Events A) → Ordered e → Steady e → Alien p e → Spread (M.rejoin p e)
spread (spread-rejoin p (out q a k) o st al) with p <ᵖ q
... | true  =
  ( sp-rejoin p q (proj₁ (every al)) (force k) (proj₁ (proj₂ (every al))) (proj₂ (ordered o)) (past-beyond q (force k) (proj₁ (steady st)))
  , everyT-idle )
  , spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
... | false = spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
spread (spread-rejoin p (skip q k) o st al) with p <ᵖ q
... | true  = spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
... | false = spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
spread (spread-rejoin p (end c) o st al) with p <ᵖ c
... | true  = tt
... | false = tt
spread (spread-rejoin p hush o st al) = tt

-- A FLATMAP'S CUTS ARE FRESH, over sorted sources alien to where it
-- subscribes: a lane inside an outer value at `q` is admitted at the skip
-- the flatMap shows just past `q`, and a lane a completion admits at the
-- skip just past that completion.
fresh-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
           → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
           → Fresh∞ p (U.stateᴺ (U.subscribe (flatMap op f s) p) ρ)

-- A CONNECT'S CUTS ARE FRESH, over sorted sources alien to where it
-- subscribes: its source's burst lies inside only its own subscription,
-- and its body shows nothing the connect does not.
fresh-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
              → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Fresh∞ p (U.stateᴺ (U.subscribe (connect s b) p) ρ)

-- A DEFER'S CUTS ARE FRESH, its program's being: what is alien to the
-- defer is alien to its program, and before the program's position only
-- if before the defer's skip.
fresh-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
            → Fresh∞ (p ++ [ ix 1 ]) (U.stateᴺ (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ)
            → Fresh∞ p (U.stateᴺ (U.deferᶜ l p []) ρ)
fresh-defer l p ρ hp cl (fc , fr) =
  everyT-idle
  , record { freshᴿ = everyT-≈ _ _ (λ k → agreeᵀ (U.subscribed (Later.force l) (env-refl (U.hots ρ))) P₁) (everyT-mono first _ fc)
                    , fresh-≈ p S X alike (fresh-widen p P₁ wide S fr) }
  where
    open Deferred l p ρ hp cl
    wide : ∀ k → ¬ Owned p k → ¬ Owned P₁ k
    wide k no o = no (owned-trans p P₁ k (inj₁ (prefix-++ p [ ix 1 ])) o)
    first : ∀ h → Fresh P₁ P₁ h → Fresh p (p ++ [ ix 0 ]) h
    first h f k x d with f k x (wide k d)
    ... | inj₂ t  = inj₂ t
    ... | inj₁ kl = inj₁ (below-lane p k 1 0 (λ q → d (inj₁ q)) kl)

-- A FINITE PROGRAM'S CUTS ARE FRESH, where a tick heads it, over sorted
-- sources alien to it: at every state, what it leaves running lies inside
-- nothing alien to it but a bare tick or a position before the step it
-- last showed.
fresh-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
           → Fresh∞ p (U.stateᴺ (U.subscribe o p) ρ)
-- A FINITE PROGRAM'S CUTS TRAIL ITS RUN, where a tick heads it, over
-- sorted sources alien to it: at every state, what a cut would leave
-- running is sorted and flat, none of it before a value coming next, nor
-- before a skip but the step that skip shows just past it; all of it past
-- an end, none keyed where that end would subscribe a lane, nor over it.
trailing-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Trailing (U.stateᴺ (U.subscribe o p) ρ)


-- A FINITE PROGRAM'S VALUES SPREAD, where a tick heads it, over sorted
-- sources alien to it: after a value at `x`, nothing later, shown or
-- left running, keys where a lane admitted at `x` would, nor where a
-- later value's lane would key under it.
spread-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Spread (U.meaning (U.subscribe o p) ρ)

-- A FLATMAP'S VALUES SPREAD, over sorted sources alien to where it
-- subscribes: each lane keyed apart from every other, as the outer's
-- values are.
spread-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
            → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Spread (U.meaning (U.subscribe (flatMap op f s) p) ρ)

-- A CONNECT'S VALUES SPREAD, over sorted sources alien to where it
-- subscribes: its body's values, its source's steps only skips, each
-- past every body value shown before it.
spread-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
               → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Spread (U.meaning (U.subscribe (connect s b) p) ρ)

-- A CONNECT SUBSCRIBED IS IN ORDER: each source step a skip just past
-- it, ahead of the body's later events, and what the source runs on
-- with past the body's end left as the tail.
ordered-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
                → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                → Ordered (U.meaning (U.subscribe (connect s b) p) ρ)

-- A CONNECT SUBSCRIBED WHERE A TICK HEADS IS STEADY, over sources
-- sorted and alien to it: nothing the body shows lies above or below
-- where a source step shows, and the source's run past the body's end
-- steps where it would have.
steady-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
               → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Steady (U.meaning (U.subscribe (connect s b) p) ρ)

-- A FINITE PROGRAM SUBSCRIBED IS IN ORDER, where a tick heads, over
-- sorted sources alien to where it subscribes.
ordered-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
             → Ordered (U.meaning (U.subscribe o p) ρ)

-- A FLATMAP SUBSCRIBED MERGES IN ORDER AND STEADY, ITS CUTS TRAILING
-- IT: over sorted sources alien to where it subscribes.  An outer value at `q` shows as a skip
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
            × Trailing (U.stateᴺ (U.subscribe (flatMap op f s) p) ρ)

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
steady-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₁ (proj₂ (flat-calm op f s ff fs p ρ hp so cl))
steady-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = steady-connect s b fs fb p ρ hp so cl
steady-subᶠ (connected i) _ p ρ hp so cl =
  steady-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
steady-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  steady-defer l p ρ hp cl (steady-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                              (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

-- Where a connect starts: its body and its source, each just subscribed.
-- A CONNECT'S BODY LIES UNDER NONE OF ITS SOURCE'S STEPS, over sources
-- sorted and alien to it: nothing the body shows or leaves running lies
-- under where a source step shows, its run past an end included.
--
-- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `alien-steps`, a subscription keying nothing just past its own events, from which this was read over a merge without tails
postulate
  under-shown-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
                      → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                      → Every∞ (λ k → Every∞ (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ))
                               (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))

connect-side : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b → ∀ p (ρ : NEnv Γ) (hp : Headed p) → Sorted ρ
             → Alienᴱ p ρ → Walk.Side p hp (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
                                        (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ)
connect-side s b fs fb p ρ hp so cl = record
    { tb = trailing-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′
    ; ts = trailing-subᶠ s fs r ρ hr so cr
    ; os = ordered-subᶠ s fs r ρ hr so cr
    ; ss = steady-subᶠ s fs r ρ hr so cr
    ; kb = every∞-mono (beneath-owned P₀) Bᶜ (Reach.reachᶠ (keyedRules P₀) b fb P₀ ρ′ (inj₁ (prefix-refl P₀)) (every-monoᴱ (λ _ _ → tt) ρ′ cl′))
    ; ks = Reach.reachᶠ (apartRules P₀ (no-tick p)) s fs r ρ (sibling p (ix-mark _) (λ ()) , sibling p (ix-mark _) (λ ())) c₀
    ; kr = Reach.reachᶠ (risingRules r) b fb P₀ ρ′ rP₀ (Reach.reach (risingRules r) s r ρ rr rρ , rρ)
    ; hs = Reach.reachᶠ headedRules s fs r ρ hr (sorted-headed ρ so)
    ; rs = rS
    ; lf = P₀
    ; lo = inj₁ (prefix-refl P₀)
    ; lc = Bursting.every-cue r P₀ (force Sᶜ) (every-mono above (force Sᶜ) (every-zip (force Sᶜ) (proj₁ kS) (proj₁ rS)))
    ; fc = proj₁ fB
    ; fr = proj₂ fB
    }
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ P₀ ρ′
    cl′ = alien-sub s p ρ cl , c₀
    rr : Rise r r
    rr = hr , λ k hk ok t → ⊥-elim (<-irrefl refl (tagged-weigh r r (owned-tagged r k r ok t)))
    rP₀ : Rise r P₀
    rP₀ = headed-snoc p hp , λ k hk ok t → ⊥-elim (sibling p (ix-mark _) (λ ()) (inj₂ (owned-tagged r k P₀ ok t)))
    rρ : Everyᴱ (Rise r) ρ
    rρ = rise-env p r (inj₁ (prefix-++ p [ ix 1 ])) ρ (sorted-headed ρ so) cl
    rS = every∞-mono (beneath-owned r) Sᶜ (Reach.reachᶠ (keyedRules r) s fs r ρ (inj₁ (prefix-refl r)) (every-monoᴱ (λ _ _ → tt) ρ cl))
    kS = Reach.reachᶠ (risingRules r) s fs r ρ rr rρ
    fB = fresh-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′
    up : ∀ h → P₀ <ᵖ h ≡ true → (h ++ [ ix 0 ]) <ᵖ P₀ ≡ false
    up h lt = <ᵖ-asym P₀ (h ++ [ ix 0 ]) (<ᵖ-trans P₀ h (h ++ [ ix 0 ]) lt (<ᵖ-below h []))
    above : ∀ h → Rise r h × Owned r h → (h ++ [ ix 0 ]) <ᵖ P₀ ≡ false
    above h (rh , oh) with rise-owned r r h rh hr (inj₁ (prefix-refl r)) oh
    ... | inj₁ e  = up h (subst (λ z → P₀ <ᵖ z ≡ true) e (proj₁ (next-ix p 0)))
    ... | inj₂ lt = up h (<ᵖ-trans P₀ r h (proj₁ (next-ix p 0)) lt)

-- A CONNECT'S CUTS TRAIL ITS RUN, where a tick heads it, over sorted
-- sources alien to it: its source's burst left running beside what its
-- body would leave trails what the connect shows next, at every state
-- the walk reaches.
trail-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ
              → Alienᴱ p ρ → Trailing (U.stateᴺ (U.subscribe (connect s b) p) ρ)
trail-connect s b fs fb p ρ hp so cl = Walk.tr-beside p hp _ _ (connect-side s b fs fb p ρ hp so cl)

spread-connect {Γ} {A} {B} s b fs fb p ρ hp so cl =
  Walk.sp-beside {A} {B} p hp _ _ (connect-side s b fs fb p ρ hp so cl) (spread-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′)
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ P₀ ρ′
    cl′ = alien-sub s p ρ cl , c₀

steady-connect {Γ} {A} {B} s b fs fb p ρ hp so cl =
  W.st-beside _ _ (W.Side.ts sd) (W.Side.os sd) (W.Side.ss sd) (steady-subᶠ b fb (p ++ [ ix 0 ]) ρ′ (headed-snoc p hp) so′ cl′)
    (W.unrelated sd (under-shown-connect s b fs fb p ρ hp so cl))
  where
    module W = Walk {A} {B} p hp
    r  = p ++ [ ix 1 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ (p ++ [ ix 0 ]) ρ′
    cl′ = alien-sub s p ρ cl , c₀
    sd = connect-side s b fs fb p ρ hp so cl

ordered-connect {Γ} {A} {B} s b fs fb p ρ hp so cl =
  W.or-beside _ _ (W.Side.ts sd) (W.Side.os sd) (ordered-subᶠ b fb (p ++ [ ix 0 ]) ρ′ (headed-snoc p hp) so′ cl′)
  where
    module W = Walk {A} {B} p hp
    r  = p ++ [ ix 1 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ (p ++ [ ix 0 ]) ρ′
    cl′ = alien-sub s p ρ cl , c₀
    sd = connect-side s b fs fb p ρ hp so cl

fresh-connect {Γ} {A} {B} s b fs fb p ρ hp so cl = W.cuts-fresh fs₀ , W.fr-beside Bᶜ Sᶜ fs₀
  where
    module W = Walk {A} {B} p hp
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ P₀ ρ′
    cl′ = alien-sub s p ρ cl , c₀
    sd = connect-side s b fs fb p ρ hp so cl
    fS = fresh-subᶠ s fs r ρ hr so cr
    pP : P₀ <ᵖ p ≡ false
    pP = <ᵖ-asym p P₀ (<ᵖ-below p [])
    wide : ∀ k → ¬ Owned p k → ¬ Owned r k
    wide k no o = no (owned-trans p r k (inj₁ (prefix-++ p [ ix 1 ])) o)
    rPP : Rise P₀ P₀
    rPP = headed-snoc p hp , λ k hk ok t → ⊥-elim (<-irrefl refl (tagged-weigh P₀ P₀ (owned-tagged P₀ k P₀ ok t)))
    rPr : Rise P₀ r
    rPr = hr , λ k hk ok t → ⊥-elim (sibling p (ix-mark _) (λ ()) (inj₂ (owned-tagged P₀ k r ok t)))
    rρ : Everyᴱ (Rise P₀) ρ
    rρ = rise-env p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ (sorted-headed ρ so) cl
    rB = Reach.reachᶠ (risingRules P₀) b fb P₀ ρ′ rPP (Reach.reach (risingRules P₀) s r ρ rPr rρ , rρ)
    past : ∀ h → Owned P₀ h × Rise P₀ h → h <ᵖ p ≡ false
    past h (oh , rh) with rise-owned P₀ P₀ h rh (headed-snoc p hp) (inj₁ (prefix-refl P₀)) oh
    ... | inj₁ e  = <ᵖ-asym p h (subst (λ z → p <ᵖ z ≡ true) e (<ᵖ-below p []))
    ... | inj₂ lt = <ᵖ-asym p h (<ᵖ-trans p P₀ h (<ᵖ-below p []) lt)
    atop : ∀ (x : Events B) → Every (λ h → h <ᵖ p ≡ false) x → Atop p x
    atop (out _ _ _) pe = proj₁ (every pe)
    atop (skip _ _)  pe = proj₁ (every pe)
    atop (end _)     pe = every pe
    atop hush        pe = tt
    fs₀ : W.FSide Bᶜ Sᶜ
    fs₀ = record
      { sd = sd
      ; ob = ordered-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′
      ; L  = p
      ; pL = <ᵖ-irrefl p
      ; cL = Bursting.cue-down r P₀ p (force Sᶜ) pP (W.Side.lc sd)
      ; bL = atop (force Bᶜ) (every-mono past (force Bᶜ) (every-zip (force Bᶜ) (proj₁ (W.Side.kb sd)) (proj₁ rB)))
      ; bc = everyT-mono (λ h f → fresh-under p [ ix 0 ] h (λ k x no → f k x (W.narrow₀ k no))) (cut Bᶜ) (W.Side.fc sd)
      ; sc = everyT-mono (λ h f → fresh-under p [ ix 1 ] h (λ k x no → f k x (wide k no))) (cut Sᶜ) (proj₁ fS)
      ; sr = fresh-widen p r wide (force Sᶜ) (proj₂ fS)
      }

fresh-subᶠ (cold c) _ p ρ hp so cl = fresh-start p (lower c) ρ
fresh-subᶠ empty _ p ρ hp so cl = everyT-idle , record { freshᴿ = tt }
fresh-subᶠ (of xs) _ p ρ hp so cl = everyT-idle , fresh-of p p 0 xs
fresh-subᶠ (map f s) (map-f fs) p ρ hp so cl =
  proj₁ (fresh-subᶠ s fs p ρ hp so cl) , fresh-map f p _ (proj₂ (fresh-subᶠ s fs p ρ hp so cl))
fresh-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl =
  proj₁ (fresh-subᶠ s fs p ρ hp so cl) , fresh-scan f z p _ (proj₂ (fresh-subᶠ s fs p ρ hp so cl))
fresh-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  proj₁ (fresh-subᶠ s fs p ρ hp so cl) , fresh-take i q p _ (proj₂ (fresh-subᶠ s fs p ρ hp so cl))
fresh-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = fresh-flat op f s ff fs p ρ hp so cl
fresh-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = fresh-connect s b fs fb p ρ hp so cl
fresh-subᶠ (connected i) _ p ρ hp so cl = everyT-idle , fresh-rejoin p p (lookup ρ i)
fresh-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  fresh-defer l p ρ hp cl (fresh-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                             (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

trailing-subᶠ (cold c) _ p ρ hp so cl = trailing-start p (lower c) ρ
trailing-subᶠ empty _ p ρ hp so cl = trail-idle _ tt
trailing-subᶠ (of xs) _ p ρ hp so cl = trail-of p 0 xs
trailing-subᶠ (map f s) (map-f fs) p ρ hp so cl = trail-map f _ _ (trailing-subᶠ s fs p ρ hp so cl)
trailing-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = trail-scan f z _ _ (trailing-subᶠ s fs p ρ hp so cl)
trailing-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  trail-take i q _ _ (ordered-subᶠ s fs p ρ hp so cl) (steady-subᶠ s fs p ρ hp so cl) (trailing-subᶠ s fs p ρ hp so cl)
trailing-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₂ (proj₂ (flat-calm op f s ff fs p ρ hp so cl))
trailing-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = trail-connect s b fs fb p ρ hp so cl
trailing-subᶠ (connected i) _ p ρ hp so cl = trail-rejoin p (lookup ρ i)
trailing-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  trail-defer l p ρ hp cl (trailing-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                             (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

-- A flatMap's outer, as its merge holds it.
flat-held : ∀ {Γ A B} (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
          → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
          → FlatOrder.Outer p (force (U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ))
                              (cut (U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ))
flat-held {Γ} {A} {B} f s ff fs p ρ hp so cl =
  O.outer (ordered-map F _ (ordered-subᶠ s fs p ρ hp so cl)) (steady-map F _ (steady-subᶠ s fs p ρ hp so cl))
    (trail-map F (force S) (cut S) (trailing-subᶠ s fs p ρ hp so cl)) (spread-map F _ (spread-subᶠ s fs p ρ hp so cl))
    (every-map F _ (proj₁ ko)) (proj₂ ko) (values-map F _ gen)
  where
    module O = FlatOrder p
    S = U.stateᴺ (U.subscribe s p) ρ
    F : A → MonotonicList B
    F a = M.cold λ q → U.stateᴺ (U.subscribe (f a) q) ρ
    kp = Reach.reachᶠ (keyedRules p) s fs p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ cl)
    hd = Reach.reachᶠ headedRules s fs p ρ hp (sorted-headed ρ so)
    ko : Every∞ O.K S
    ko = every∞-mono (λ h bh → beneath-owned p h (proj₁ bh) , proj₂ bh) S
           (every-zip (force S) (proj₁ kp) (proj₁ hd) , everyT-zip (cut S) (proj₂ kp) (proj₂ hd))
    gen : ∀ a → O.Gen (F a)
    gen a j (bj , hj) =
      ordered-subᶠ (f a) (ff a) j ρ hj so cj , rise-sub (f a) j ρ hj , steady-subᶠ (f a) (ff a) j ρ hj so cj , trailing-subᶠ (f a) (ff a) j ρ hj so cj
      , O.under∞ j L
          (every∞-mono (beneath-owned j) L (Reach.reachᶠ (keyedRules j) (f a) (ff a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj)))
          (Reach.reachᶠ headedRules (f a) (ff a) j ρ hj (sorted-headed ρ so))
          (λ R okR d → every∞-mono (λ _ → proj₁) L
             (Reach.reachᶠ (apartRules R (tick-beneath p R hp (proj₁ okR))) (f a) (ff a) j ρ d
                (alienᴱ-owned p R (beneath-owned p R (proj₁ okR)) ρ cl)))
      , spread-subᶠ (f a) (ff a) j ρ hj so cj
      where
        L  = U.stateᴺ (U.subscribe (f a) j) ρ
        cj = alienᴱ-owned p j (beneath-owned p j bj) ρ cl

flat-calm {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  O.ordered-go (flatOp op) (just E) [] [] idle O.[]ᴿ tt []ᴬ []ᴬ held (sortedT-idle , everyT-idle , everyT-idle , flatT-idle)
  , calm-steady _ (proj₂ c₀) , calm-trail _ _ (proj₁ c₀) (proj₂ c₀)
  where
    module O = FlatOrder p
    E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ
    held = flat-held f s ff fs p ρ hp so cl
    c₀ = O.calm-at (flatOp op) (just E) [] [] idle O.[]ᴿ tt []ᴬ []ᴬ held (sortedT-idle , everyT-idle , everyT-idle , flatT-idle)

spread-flat {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  FlatOrder.spread-go p (flatOp op) (just E) [] [] idle FlatOrder.[]ᴿ tt []ᴬ []ᴬ (flat-held f s ff fs p ρ hp so cl)
    (sortedT-idle , everyT-idle , everyT-idle , flatT-idle)
  where E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ

fresh-flat {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  W.whole-fresh p (just E) [] idle fo []ᴬ everyT-idle
  , W.fr-go (flatOp op) (just E) [] [] idle p fo []ᴬ []ᴬ everyT-idle
      (atop-go (flatOp op) (just E) [] [] idle p []ᴬ (atop-map F p _ (rise-sub s p ρ hp)) tt) (proj₁ (flat-calm op f s ff fs p ρ hp so cl))
  where
    module W = FlatFresh p
    S = U.stateᴺ (U.subscribe s p) ρ
    F : A → MonotonicList B
    F a = M.cold λ q → U.stateᴺ (U.subscribe (f a) q) ρ
    E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ
    kp = Reach.reachᶠ (keyedRules p) s fs p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ cl)
    hd = Reach.reachᶠ headedRules s fs p ρ hp (sorted-headed ρ so)
    ko : Every W.K (force S)
    ko = every-mono (λ h bh → beneath-owned p h (proj₁ bh) , proj₂ bh) (force S) (every-zip (force S) (proj₁ kp) (proj₁ hd))
    gen : ∀ a → W.GenF (F a)
    gen a q (oq , hq) = everyT-mono first (cut L) (proj₁ fL) , fresh-widen p j wide (force L) (proj₂ fL) , kL
      where
        j = q ++ [ ix 1 ]
        L = U.stateᴺ (U.subscribe (f a) j) ρ
        oj : Owned p j
        oj = owned-trans p q j oq (inj₁ (prefix-++ q [ ix 1 ]))
        hj = headed-snoc q hq
        cj = alienᴱ-owned p j oj ρ cl
        fL = fresh-subᶠ (f a) (ff a) j ρ hj so cj
        wide : ∀ k → ¬ Owned p k → ¬ Owned j k
        wide k no o = no (owned-trans p j k oj o)
        first : ∀ h → Fresh j j h → Fresh p (q ++ [ ix 0 ]) h
        first h fh k x no with fh k x (wide k no)
        ... | inj₂ t  = inj₂ t
        ... | inj₁ kj = inj₁ (below-lane q k 1 0 (λ pq → no (owned-trans p q k oq (inj₁ pq))) kj)
        kL : Every W.K (force L)
        kL = every-zip (force L)
               (every-mono (λ h bh → owned-trans p j h oj (beneath-owned j h bh)) (force L)
                  (proj₁ (Reach.reachᶠ (keyedRules j) (f a) (ff a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj))))
               (proj₁ (Reach.reachᶠ headedRules (f a) (ff a) j ρ hj (sorted-headed ρ so)))
    fo : W.Freshᴼ p (just E)
    fo = proj₁ fS , fresh-map F p _ (proj₂ fS) , values-map F _ gen , every-map F _ ko
      where fS = fresh-subᶠ s fs p ρ hp so cl

ordered-subᶠ (cold c) _ p ρ hp so cl = subst Ordered (sym (U.start-meaning p (lower c) ρ)) (ordered-start p (lower c) hp)
ordered-subᶠ empty _ p ρ hp so cl = record { ordered = tt }
ordered-subᶠ (of xs) _ p ρ hp so cl = ordered-of p 0 xs
ordered-subᶠ (map f s) (map-f fs) p ρ hp so cl = ordered-map f _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = ordered-scan f z _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl = ordered-take i q _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₁ (flat-calm op f s ff fs p ρ hp so cl)
ordered-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = ordered-connect s b fs fb p ρ hp so cl
ordered-subᶠ (connected i) _ p ρ hp so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl)
  where sl = sorted-lookup ρ so i
ordered-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  ordered-defer l p ρ hp cl (ordered-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                               (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

spread-subᶠ (cold c) _ p ρ hp so cl = subst Spread (sym (U.start-meaning p (lower c) ρ)) (spread-start p (lower c) hp)
spread-subᶠ empty _ p ρ hp so cl = record { spread = tt }
spread-subᶠ (of xs) _ p ρ hp so cl = spread-of p 0 xs
spread-subᶠ (map f s) (map-f fs) p ρ hp so cl = spread-map f _ (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = spread-scan f z _ (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  spread-take i q _ _ (trailing-subᶠ s fs p ρ hp so cl) (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = spread-flat op f s ff fs p ρ hp so cl
spread-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = spread-connect s b fs fb p ρ hp so cl
spread-subᶠ (connected i) _ p ρ hp so cl =
  spread-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
spread-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  spread-defer l p ρ hp cl (spread-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
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
