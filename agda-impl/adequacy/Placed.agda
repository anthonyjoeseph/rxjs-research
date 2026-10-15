{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (zero; suc; _<ᵇ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import Level using (lower)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; agree; Earliest; none; found; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root)
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

-- No event of `e` keyed under `p`.
mutual
  Aliens : ∀ {A} → Pos → Events A → Set
  Aliens p (out h _ r) = ¬ Owned p h × Alien p (force r)
  Aliens p (skip h r)  = ¬ Owned p h × Alien p (force r)
  Aliens p (end h)     = ¬ Owned p h
  Aliens p hush        = ⊤

  record Alien {A} (p : Pos) (e : Events A) : Set where
    coinductive
    field alien : Aliens p e

open Alien public

-- Every source alien to `p`: what a subscription at `p` keys.
Alienᴱ : ∀ {Γ} → Pos → NEnv Γ → Set
Alienᴱ p []ᴬ      = ⊤
Alienᴱ p (e ∷ᴬ ρ) = Alien p e × Alienᴱ p ρ

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

prefix-++ : ∀ k w → Prefix k (k ++ w)
prefix-++ []      w = tt
prefix-++ (a ∷ k) w = refl , prefix-++ k w

prefix-trans : ∀ k j h → Prefix k j → Prefix j h → Prefix k h
prefix-trans []      j       h       _          _          = tt
prefix-trans (_ ∷ _) []      _       ()         _
prefix-trans (_ ∷ _) (_ ∷ _) []      _          ()
prefix-trans (a ∷ k) (b ∷ j) (c ∷ h) (refl , p) (refl , q) = refl , prefix-trans k j h p q

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
alien-owned : ∀ {A} p k → Owned p k → (e : Events A) → Alien p e → Alien k e
alien (alien-owned p k o (out h _ r) a) = (λ x → proj₁ (alien a) (owned-trans p k h o x)) , alien-owned p k o (force r) (proj₂ (alien a))
alien (alien-owned p k o (skip h r)  a) = (λ x → proj₁ (alien a) (owned-trans p k h o x)) , alien-owned p k o (force r) (proj₂ (alien a))
alien (alien-owned p k o (end h)     a) = λ x → alien a (owned-trans p k h o x)
alien (alien-owned p k o hush        a) = tt

alienᴱ-owned : ∀ {Γ} p k → Owned p k → (ρ : NEnv Γ) → Alienᴱ p ρ → Alienᴱ k ρ
alienᴱ-owned p k o []ᴬ      a        = tt
alienᴱ-owned p k o (e ∷ᴬ ρ) (ae , a) = alien-owned p k o e ae , alienᴱ-owned p k o ρ a

-- Every position `e` shows, its end's included, strictly keyed under `p`.
mutual
  Keys : ∀ {A} → Pos → Events A → Set
  Keys p (out h _ r) = Beneath p h × Keyed p (force r)
  Keys p (skip h r)  = Beneath p h × Keyed p (force r)
  Keys p (end h)     = Beneath p h
  Keys p hush        = ⊤

  record Keyed {A} (p : Pos) (e : Events A) : Set where
    coinductive
    field keyed : Keys p e

open Keyed public

keyed-reach : ∀ {A} p (e : Events A) h → Keyed p e → Reaches h e → Beneath p h
keyed-reach p (out h _ r) _ ke out-here       = proj₁ (keyed ke)
keyed-reach p (out _ _ r) h ke (out-there x)  = keyed-reach p (force r) h (proj₂ (keyed ke)) x
keyed-reach p (skip h r)  _ ke skip-here      = proj₁ (keyed ke)
keyed-reach p (skip _ r)  h ke (skip-there x) = keyed-reach p (force r) h (proj₂ (keyed ke)) x

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

-- A cold keys its subscribe burst under where it subscribes, and every
-- later frame under a timer tagged with a position under it.
mutual
  keyed-frames : ∀ {A t} p τ e (m : M.From A t) → Beneath p e → Keyed p (M.frames τ e m)
  keyed (keyed-frames p τ e M.done       o) = o
  keyed (keyed-frames p τ e M.quiet      o) = tt
  keyed (keyed-frames p τ e (M.at _ _ b) o) = keyed (keyed-burst p τ _ 0 b (inj₂ (inj₁ (beneath-owned p e o))))

  keyed-burst : ∀ {A t} p τ r i (b : M.Frame A t) → Owned p r → Keyed p (M.burst τ r i b)
  keyed (keyed-burst p τ r i (M.emit a k) o) = owned-snoc p r (ix i) o , keyed-burst p τ r (suc i) (M.Frame∞.force k) o
  keyed (keyed-burst p τ r i (M.stall k)  o) = owned-snoc p r (ix i) o , keyed-burst p τ r (suc i) (M.Frame∞.force k) o
  keyed (keyed-burst p τ r i (M.close k)  o) = owned-snoc p r (ix i) o , keyed-frames p τ (r ++ [ last ]) (M.From∞.force k) (owned-snoc p r last o)

keyed-start : ∀ {A} p (m : From A 0) → Keyed p (M.start p m)
keyed-start p (M.at zero _ b)      = keyed-burst p (tick p) p 0 b (inj₁ (prefix-refl p))
keyed-start p m@(M.at (suc _) _ _) = keyed-frames p (tick p) (p ++ [ last ]) m (owned-snoc p p last (inj₁ (prefix-refl p)))
keyed-start p m@M.done             = keyed-frames {t = 0} p (tick p) (p ++ [ last ]) m (owned-snoc p p last (inj₁ (prefix-refl p)))
keyed-start p m@M.quiet            = keyed-frames {t = 0} p (tick p) (p ++ [ last ]) m (owned-snoc p p last (inj₁ (prefix-refl p)))

keyed-of : ∀ {A} p i (xs : List A) → Keyed p (M.ofᴱ p i xs)
keyed (keyed-of p i [])       = owned-snoc p p last (inj₁ (prefix-refl p))
keyed (keyed-of p i (x ∷ xs)) = owned-snoc p p (ix i) (inj₁ (prefix-refl p)) , keyed-of p (suc i) xs

keyed-map : ∀ {A B} p (f : A → B) (e : Events A) → Keyed p e → Keyed p (M.mapᴱ f e)
keyed (keyed-map p f (out k a r) ke) = proj₁ (keyed ke) , keyed-map p f (force r) (proj₂ (keyed ke))
keyed (keyed-map p f (skip k r)  ke) = proj₁ (keyed ke) , keyed-map p f (force r) (proj₂ (keyed ke))
keyed (keyed-map p f (end k)     ke) = keyed ke
keyed (keyed-map p f hush        ke) = tt

keyed-scan : ∀ {A B} p (f : B → A → B) z (e : Events A) → Keyed p e → Keyed p (M.scanᴱ f z e)
keyed (keyed-scan p f z (out k a r) ke) = proj₁ (keyed ke) , keyed-scan p f (f z a) (force r) (proj₂ (keyed ke))
keyed (keyed-scan p f z (skip k r)  ke) = proj₁ (keyed ke) , keyed-scan p f z (force r) (proj₂ (keyed ke))
keyed (keyed-scan p f z (end k)     ke) = keyed ke
keyed (keyed-scan p f z hush        ke) = tt

-- A cut shows its failing value, if at all, just past where it was, and
-- ends just past it.
mutual
  keyed-take : ∀ {A} p i (q : A → Bool) (e : Events A) → Keyed p e → Keyed p (M.takeWhileᴱ i q e)
  keyed (keyed-take p i q (out k a r) ke) = keyed (keyed-taking p i q k a (q a) r ke)
  keyed (keyed-take p i q (skip k r)  ke) = proj₁ (keyed ke) , keyed-take p i q (force r) (proj₂ (keyed ke))
  keyed (keyed-take p i q (end k)     ke) = keyed ke
  keyed (keyed-take p i q hush        ke) = tt

  keyed-taking : ∀ {A} p i (q : A → Bool) k a b (r : Events∞ A) → Keyed p (out k a r) → Keyed p (M.taking i q k a b r)
  keyed (keyed-taking p i     q k a true  r ke) = proj₁ (keyed ke) , keyed-take p i q (force r) (proj₂ (keyed ke))
  keyed (keyed-taking p true  q k a false r ke) =
    beneath-snoc p k (ix 0) (proj₁ (keyed ke)) , record { keyed = beneath-snoc p k last (proj₁ (keyed ke)) }
  keyed (keyed-taking p false q k a false r ke) = beneath-snoc p k last (proj₁ (keyed ke))

-- A join at `p` shows what it missed just past `p`, the rest tagged.
mutual
  keyed-rejoin : ∀ {A} p (e : Events A) → Keyed p (M.rejoin p e)
  keyed (keyed-rejoin p (out q a k)) = keyed (keyed-shown p q (just a) k (p <ᵖ q))
  keyed (keyed-rejoin p (skip q k))  = keyed (keyed-shown p q nothing k (p <ᵖ q))
  keyed (keyed-rejoin p (end c))     with p <ᵖ c
  ... | true  = inj₂ (tagged-sub c p)
  ... | false = owned-snoc p p last (inj₁ (prefix-refl p))
  keyed (keyed-rejoin p hush)        = tt

  keyed-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → Keyed p (M.shown p q a k b)
  keyed (keyed-shown p q (just a) k true)  = inj₂ (tagged-sub q p) , keyed-rejoin p (force k)
  keyed (keyed-shown p q nothing  k true)  = inj₂ (tagged-sub q p) , keyed-rejoin p (force k)
  keyed (keyed-shown p q (just a) k false) = owned-snoc p p (ix 0) (inj₁ (prefix-refl p)) , keyed-rejoin p (force k)
  keyed (keyed-shown p q nothing  k false) = owned-snoc p p (ix 0) (inj₁ (prefix-refl p)) , keyed-rejoin p (force k)

prefix-trans⁺ : ∀ k j h → Prefix k j → Prefix⁺ j h → Prefix⁺ k h
prefix-trans⁺ []      []      h       _          q          = q
prefix-trans⁺ []      (_ ∷ _) []      _          ()
prefix-trans⁺ []      (_ ∷ _) (_ ∷ _) _          _          = tt
prefix-trans⁺ (_ ∷ _) []      _       ()         _
prefix-trans⁺ (_ ∷ _) (_ ∷ _) []      _          ()
prefix-trans⁺ (a ∷ k) (b ∷ j) (c ∷ h) (refl , p) (refl , q) = refl , prefix-trans⁺ k j h p q

-- Strictly keyed under what `p` keys is strictly keyed under `p`.
beneath-trans : ∀ p k h → Owned p k → Beneath k h → Beneath p h
beneath-trans p k h (inj₁ o) (inj₁ q) = inj₁ (prefix-trans⁺ p k h o q)
beneath-trans p k h (inj₂ t) (inj₁ q) = inj₂ (tagged-prefix p k h t (prefix⁺-prefix k h q))
beneath-trans p k h o        (inj₂ t) = inj₂ (owned-tagged p k h o t)

keyed-under : ∀ {A} p k → Owned p k → (e : Events A) → Keyed k e → Keyed p e
keyed (keyed-under p k o (out h _ r) ke) = beneath-trans p k h o (proj₁ (keyed ke)) , keyed-under p k o (force r) (proj₂ (keyed ke))
keyed (keyed-under p k o (skip h r)  ke) = beneath-trans p k h o (proj₁ (keyed ke)) , keyed-under p k o (force r) (proj₂ (keyed ke))
keyed (keyed-under p k o (end h)     ke) = beneath-trans p k h o (keyed ke)
keyed (keyed-under p k o hush        ke) = tt

-- A connect shows each of its source's steps, and its end, just past it.
mutual
  keyed-beside : ∀ {A B} p (b : Events B) (s : Events A) → Keyed p b → Keyed p s → Keyed p (M.beside b s)
  keyed (keyed-beside p b (out q _ r) kb ks) =
    keyed (keyed-ahead p b (q ++ [ ix 0 ]) r _ kb (beneath-snoc p q (ix 0) (proj₁ (keyed ks))) (proj₂ (keyed ks)))
  keyed (keyed-beside p b (skip q r)  kb ks) =
    keyed (keyed-ahead p b (q ++ [ ix 0 ]) r _ kb (beneath-snoc p q (ix 0) (proj₁ (keyed ks))) (proj₂ (keyed ks)))
  keyed (keyed-beside p b (end c)     kb ks) =
    keyed (keyed-ahead p b (c ++ [ ix 0 ]) M.hushed _ kb (beneath-snoc p c (ix 0) (keyed ks)) (record { keyed = tt }))
  keyed (keyed-beside p b hush        kb ks) = keyed kb

  keyed-ahead : ∀ {A B} p (b : Events B) q (s : Events∞ A) t → Keyed p b → Beneath p q → Keyed p (force s) → Keyed p (M.ahead b q s t)
  keyed (keyed-ahead p b           q s true  kb bq ks) = bq , keyed-beside p b (force s) kb ks
  keyed (keyed-ahead p (out k a r) q s false kb bq ks) = proj₁ (keyed kb) , keyed-ahead p (force r) q s _ (proj₂ (keyed kb)) bq ks
  keyed (keyed-ahead p (skip k r)  q s false kb bq ks) = proj₁ (keyed kb) , keyed-ahead p (force r) q s _ (proj₂ (keyed kb)) bq ks
  keyed (keyed-ahead p (end c)     q s false kb bq ks) = keyed kb
  keyed (keyed-ahead p hush        q s false kb bq ks) = tt

-- A lane keyed wherever it subscribes under `p`.
Lane : ∀ {B} → Pos → MonotonicList B → Set
Lane p m = ∀ k → Owned p k → Keyed p (M.observe m k)

-- An outer keyed under `p`, each value a lane keyed under `p`.
mutual
  Outers : ∀ {B} → Pos → Events (MonotonicList B) → Set
  Outers p (out h m r) = Beneath p h × Lane p m × Outer p (force r)
  Outers p (skip h r)  = Beneath p h × Outer p (force r)
  Outers p (end h)     = Beneath p h
  Outers p hush        = ⊤

  record Outer {B} (p : Pos) (e : Events (MonotonicList B)) : Set where
    coinductive
    field outerly : Outers p e

open Outer public

outer-map : ∀ {A B} p (F : A → MonotonicList B) (e : Events A) → (∀ a → Lane p (F a)) → Keyed p e → Outer p (M.mapᴱ F e)
outerly (outer-map p F (out h a r) lf ke) = proj₁ (keyed ke) , lf a , outer-map p F (force r) lf (proj₂ (keyed ke))
outerly (outer-map p F (skip h r)  lf ke) = proj₁ (keyed ke) , outer-map p F (force r) lf (proj₂ (keyed ke))
outerly (outer-map p F (end h)     lf ke) = keyed ke
outerly (outer-map p F hush        lf ke) = tt

Outerᴹ : ∀ {B} → Pos → Maybe (Events (MonotonicList B)) → Set
Outerᴹ p nothing  = ⊤
Outerᴹ p (just e) = Outer p e

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

-- An admitted lane subscribes keyed, and a queued one stays a lane.
Admitted : ∀ {B} → Pos → List (Events B) × List (MonotonicList B) → Set
Admitted p (ls , qs) = All (Keyed p) ls × All (Lane p) qs

admit-all : ∀ {B} p op q (m : MonotonicList B) ls qs → Owned p q → Lane p m → All (Keyed p) ls → All (Lane p) qs
          → Admitted p (M.admit op q m ls qs)
admit-all p (M.mergeᶠ nothing)  q m ls       qs o lm kl kq = lm q o ∷ᴬ kl , kq
admit-all p (M.mergeᶠ (just n)) q m ls       qs o lm kl kq with length ls <ᵇ n
... | true  = lm q o ∷ᴬ kl , kq
... | false = kl , All++⁺ kq (lm ∷ᴬ []ᴬ)
admit-all p M.switchᶠ           q m ls       qs o lm kl kq = lm q o ∷ᴬ []ᴬ , kq
admit-all p M.exhaustᶠ          q m []       qs o lm kl kq = lm q o ∷ᴬ []ᴬ , kq
admit-all p M.exhaustᶠ          q m (l ∷ ls) qs o lm kl kq = kl , kq

-- A flatMap's merge shows its outer's skips and ends where they were,
-- each value just past where it was, and its lanes' events where they
-- were, each lane's end just past it when another is queued.
mutual
  keyed-go : ∀ {B} p op (o : Maybe (Events (MonotonicList B))) ls qs → Outerᴹ p o → All (Keyed p) ls → All (Lane p) qs
           → Keyed p (M.go op o ls qs)
  keyed-go p op o ls qs ko kl kq with M.earliest ls | earliest-all (Keyed p) ls kl
  ... | none            | _                = keyed-via p op o ls qs ko kl kq
  ... | found k bs l as | (kb , kl₁ , ka)  = keyed-race p op o k bs l as qs ko kb kl₁ ka kq

  keyed-via : ∀ {B} p op (o : Maybe (Events (MonotonicList B))) ls qs → Outerᴹ p o → All (Keyed p) ls → All (Lane p) qs
            → Keyed p (M.viaOuter op o ls qs)
  keyed-via p op nothing  ls qs ko kl kq = record { keyed = tt }
  keyed-via p op (just e) ls qs ko kl kq = keyed-outer p op e ls qs ko kl kq

  keyed-race : ∀ {B} p op (o : Maybe (Events (MonotonicList B))) k bs (l : Events B) as qs → Outerᴹ p o
             → All (Keyed p) bs → Keyed p l → All (Keyed p) as → All (Lane p) qs → Keyed p (M.race op o k bs l as qs)
  keyed-race p op nothing  k bs l as qs ko kb kl ka kq = keyed-lane p op nothing bs l as qs ko kb kl ka kq
  keyed-race p op (just e) k bs l as qs ko kb kl ka kq with M.head e
  ... | nothing = keyed-lane p op (just e) bs l as qs ko kb kl ka kq
  ... | just k′ with k′ <ᵖ k
  ...   | true  = keyed-outer p op e (bs ++ l ∷ as) qs ko (All++⁺ kb (kl ∷ᴬ ka)) kq
  ...   | false = keyed-lane p op (just e) bs l as qs ko kb kl ka kq

  keyed-outer : ∀ {B} p op (e : Events (MonotonicList B)) ls qs → Outer p e → All (Keyed p) ls → All (Lane p) qs
              → Keyed p (M.outer op e ls qs)
  keyed (keyed-outer p op (out q m r) ls qs ko kl kq)
    with M.admit op (q ++ [ ix 1 ]) m ls qs
       | admit-all p op (q ++ [ ix 1 ]) m ls qs
           (beneath-owned p _ (beneath-snoc p q (ix 1) (proj₁ (outerly ko)))) (proj₁ (proj₂ (outerly ko))) kl kq
  ... | ls′ , qs′ | (kl′ , kq′) =
    beneath-snoc p q (ix 0) (proj₁ (outerly ko)) , keyed-go p op (just (force r)) ls′ qs′ (proj₂ (proj₂ (outerly ko))) kl′ kq′
  keyed (keyed-outer p op (skip q r) ls qs ko kl kq) =
    proj₁ (outerly ko) , keyed-go p op (just (force r)) ls qs (proj₂ (outerly ko)) kl kq
  keyed (keyed-outer p op (end c) []       []       ko kl kq) = outerly ko
  keyed (keyed-outer p op (end c) []       (m ∷ qs) ko kl kq) = outerly ko , keyed-go p op nothing [] (m ∷ qs) tt kl kq
  keyed (keyed-outer p op (end c) (l ∷ ls) qs       ko kl kq) = outerly ko , keyed-go p op nothing (l ∷ ls) qs tt kl kq
  keyed (keyed-outer p op hush    ls       qs       ko kl kq) = tt

  keyed-lane : ∀ {B} p op (o : Maybe (Events (MonotonicList B))) bs (l : Events B) as qs → Outerᴹ p o
             → All (Keyed p) bs → Keyed p l → All (Keyed p) as → All (Lane p) qs → Keyed p (M.lane op o bs l as qs)
  keyed (keyed-lane p op o bs (out k b r) as qs ko kb kl ka kq) =
    proj₁ (keyed kl) , keyed-go p op o (bs ++ force r ∷ as) qs ko (All++⁺ kb (proj₂ (keyed kl) ∷ᴬ ka)) kq
  keyed (keyed-lane p op o bs (skip k r) as qs ko kb kl ka kq) =
    proj₁ (keyed kl) , keyed-go p op o (bs ++ force r ∷ as) qs ko (All++⁺ kb (proj₂ (keyed kl) ∷ᴬ ka)) kq
  keyed (keyed-lane p op o bs (end c) as (m ∷ qs) ko kb kl ka (lm ∷ᴬ kq)) =
    beneath-snoc p c (ix 0) (keyed kl)
    , keyed-go p op o (M.observe m (c ++ [ ix 1 ]) ∷ bs ++ as) qs ko
        (lm (c ++ [ ix 1 ]) (beneath-owned p _ (beneath-snoc p c (ix 1) (keyed kl))) ∷ᴬ All++⁺ kb ka) kq
  keyed (keyed-lane p op nothing  []       (end c) []       [] ko kb kl ka kq) = keyed kl
  keyed (keyed-lane p op nothing  []       (end c) (a ∷ as) [] ko kb kl ka kq) =
    keyed kl , keyed-go p op nothing (a ∷ as) [] ko ka kq
  keyed (keyed-lane p op nothing  (b ∷ bs) (end c) as       [] ko kb kl ka kq) =
    keyed kl , keyed-go p op nothing (b ∷ bs ++ as) [] ko (All++⁺ kb ka) kq
  keyed (keyed-lane p op (just e) bs       (end c) as       [] ko kb kl ka kq) =
    keyed kl , keyed-go p op (just e) (bs ++ as) [] ko (All++⁺ kb ka) kq
  keyed (keyed-lane p op o bs hush as qs ko kb kl ka kq) = tt

-- What agrees at every depth shows the same positions.
out-tail : ∀ {A k h h′ a b} {l r : Events∞ A} → Agree (suc k) (out h a l) (out h′ b r) → Agree k (force l) (force r)
out-tail (out⁼ t) = t

skip-tail : ∀ {A k h h′} {l r : Events∞ A} → Agree (suc k) (skip h l) (skip h′ r) → Agree k (force l) (force r)
skip-tail (skip⁼ t) = t

mutual
  keyed-≈ : ∀ {A} p (x y : Events A) → (∀ k → Agree k x y) → Keyed p x → Keyed p y
  keyed (keyed-≈ p x y a kx) = keys-≈ p x y a (a 1) kx

  keys-≈ : ∀ {A} p (x y : Events A) → (∀ k → Agree k x y) → Agree 1 x y → Keyed p x → Keys p y
  keys-≈ p (out h _ l) (out h _ r) a (out⁼ _)  kx =
    proj₁ (keyed kx) , keyed-≈ p (force l) (force r) (λ k → out-tail (a (suc k))) (proj₂ (keyed kx))
  keys-≈ p (skip h l)  (skip h r)  a (skip⁼ _) kx =
    proj₁ (keyed kx) , keyed-≈ p (force l) (force r) (λ k → skip-tail (a (suc k))) (proj₂ (keyed kx))
  keys-≈ p (end h)     (end h)     a end⁼      kx = keyed kx
  keys-≈ p hush        hush        a hush⁼     kx = tt

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

  -- A DEFERRED PROGRAM SUBSCRIBED SHOWS ONLY WHAT IT KEYS: `owned-reach`
  -- at the program a defer holds.
  --
  -- DEAD ROUTE: `owned-reach` calling itself at `Later.force l`, which is
  --   not structurally smaller, under `keyed-≈` and `keyed-under`, so not
  --   guarded either; with the structural calls of the other operators no
  --   argument decreases on every cycle.  A `Keyed` indexed by depth, by
  --   induction on depth then program, would carry it.
  owned-later : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Keyed p (U.meaning (U.subscribe (Later.force l) p) ρ)

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

  -- A SUBSCRIPTION OVER STEADY SOURCES IS STEADY: a joiner's skips for
  -- what it missed sit just past the join, which nothing it rekeys
  -- lies inside, its sources being alien to it.
  steady-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ → Steady (U.meaning (U.subscribe o p) ρ)

  -- A CONNECT'S SOURCE KEYS NOTHING UNDER ITS BODY: what it shows is
  -- keyed under its own subscription, or a source's position tagged.
  alien-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
            → Alien (p ++ [ ix 0 ]) (U.meaning (U.subscribe o (p ++ [ ix 1 ])) ρ)


-- A SUBSCRIPTION SHOWS ONLY WHAT IT KEYS: inside where it subscribes, a
-- source's position tagged by one of its joins, or a frame of one of its
-- timers.
owned-reach : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Keyed p (U.meaning (U.subscribe o p) ρ)
owned-reach (cold c)          p ρ = subst (Keyed p) (sym (U.start-meaning p (lower c) ρ)) (keyed-start p (lower c))
owned-reach empty             p ρ = record { keyed = owned-snoc p p last (inj₁ (prefix-refl p)) }
owned-reach (of xs)           p ρ = keyed-of p 0 xs
owned-reach (map f s)         p ρ = keyed-map p f _ (owned-reach s p ρ)
owned-reach (scan f z s)      p ρ = keyed-scan p f z _ (owned-reach s p ρ)
owned-reach (takeWhile i q s) p ρ = keyed-take p i q _ (owned-reach s p ρ)
owned-reach (flatMap op f s)  p ρ =
  keyed-go p (flatOp op) (just (M.mapᴱ F (U.meaning (U.subscribe s p) ρ))) [] []
    (outer-map p F _ (λ a k o → keyed-under p k o _ (owned-reach (f a) k ρ)) (owned-reach s p ρ)) []ᴬ []ᴬ
  where F = λ a → M.cold λ q → U.meaning (U.subscribe (f a) q) ρ
owned-reach (connect s b)     p ρ =
  keyed-beside p _ _
    (keyed-under p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) _ (owned-reach b (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ)))
    (keyed-under p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) _ (owned-reach s (p ++ [ ix 1 ]) ρ))
owned-reach (connected i)     p ρ = keyed-rejoin p (lookup ρ i)
owned-reach (defer l)         p ρ = record { keyed =
  owned-snoc p p (ix 0) (inj₁ (prefix-refl p))
  , keyed-≈ p _ _ (λ k → agree (U.subscribed (Later.force l) (env-refl (U.hots ρ))) (p ++ [ ix 1 ]))
      (keyed-under p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) _ (owned-later l (p ++ [ ix 1 ]) ρ)) }

-- A flatMap's sources stay out of every lane it can admit: the skip
-- before the lane is keyed under the flatMap, so the lane is.
--
-- REFUTED: f5faeaf6 of sources merely clear of the flatMap's subtree, by one tagged under its join
alien-shown : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
            → ∀ x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.subscribe (flatMap op f s) p) ρ) → Alienᴱ (x ++ [ ix 1 ]) ρ
alien-shown op f s p ρ al x r =
  alienᴱ-owned p (x ++ [ ix 1 ]) (owned-lane p x (keyed-reach p _ (x ++ [ ix 0 ]) (owned-reach (flatMap op f s) p ρ) r)) ρ al

-- A program subscribed anywhere, over sorted sources alien to where it
-- subscribes, is placed.
placed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Sorted ρ → Alienᴱ p ρ → Placed (U.subscribe o p) ρ
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
               ((proj₁ ps , steady-sub s (p ++ [ ix 1 ]) ρ so cs) , so) (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl)
placed-sub (connected i) p ρ so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl) , tt
  where sl = sorted-lookup ρ so i
placed-sub (defer l) p ρ so cl = ordered-defer l p ρ so cl , tt

-- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root is
-- placed.
placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
placed-subscribe o = placed-sub o root []ᴬ tt tt
