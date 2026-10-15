{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
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
open import denotation.MonotonicList using (Events; Events∞; Pos; From; Timeline; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root)
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

-- Every position `e` shows strictly keyed under `p`.
Keyed : ∀ {A} → Pos → Events A → Set
Keyed p e = ∀ h → Reaches h e → Beneath p h

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
  keyed-frames : ∀ {A t} p τ e (m : M.From A t) → Owned p e → Keyed p (M.frames τ e m)
  keyed-frames p τ e M.done        o h ()
  keyed-frames p τ e M.quiet       o h ()
  keyed-frames p τ e (M.at _ _ b)  o h x = keyed-burst p τ _ 0 b (inj₂ (inj₁ o)) h x

  keyed-burst : ∀ {A t} p τ r i (b : M.Frame A t) → Owned p r → Keyed p (M.burst τ r i b)
  keyed-burst p τ r i (M.emit a k) o _ out-here        = owned-snoc p r (ix i) o
  keyed-burst p τ r i (M.emit a k) o h (out-there x)   = keyed-burst p τ r (suc i) (M.Frame∞.force k) o h x
  keyed-burst p τ r i (M.stall k)  o _ skip-here       = owned-snoc p r (ix i) o
  keyed-burst p τ r i (M.stall k)  o h (skip-there x)  = keyed-burst p τ r (suc i) (M.Frame∞.force k) o h x
  keyed-burst p τ r i (M.close k)  o _ skip-here       = owned-snoc p r (ix i) o
  keyed-burst p τ r i (M.close k)  o h (skip-there x)  =
    keyed-frames p τ (r ++ [ last ]) (M.From∞.force k) (beneath-owned p _ (owned-snoc p r last o)) h x

keyed-start : ∀ {A} p (m : From A 0) → Keyed p (M.start p m)
keyed-start p (M.at zero _ b)      = keyed-burst p (tick p) p 0 b (inj₁ (prefix-refl p))
keyed-start p m@(M.at (suc _) _ _) = keyed-frames p (tick p) (p ++ [ last ]) m (inj₁ (prefix-++ p [ last ]))
keyed-start p m@M.done             = keyed-frames {t = 0} p (tick p) (p ++ [ last ]) m (inj₁ (prefix-++ p [ last ]))
keyed-start p m@M.quiet            = keyed-frames {t = 0} p (tick p) (p ++ [ last ]) m (inj₁ (prefix-++ p [ last ]))

keyed-of : ∀ {A} p i (xs : List A) → Keyed p (M.ofᴱ p i xs)
keyed-of p i []       h ()
keyed-of p i (x ∷ xs) _ out-here      = owned-snoc p p (ix i) (inj₁ (prefix-refl p))
keyed-of p i (x ∷ xs) h (out-there y) = keyed-of p (suc i) xs h y

keyed-map : ∀ {A B} p (f : A → B) (e : Events A) → Keyed p e → Keyed p (M.mapᴱ f e)
keyed-map p f (out k a r) ke _ out-here       = ke _ out-here
keyed-map p f (out k a r) ke h (out-there x)  = keyed-map p f (force r) (λ h′ y → ke h′ (out-there y)) h x
keyed-map p f (skip k r)  ke _ skip-here      = ke _ skip-here
keyed-map p f (skip k r)  ke h (skip-there x) = keyed-map p f (force r) (λ h′ y → ke h′ (skip-there y)) h x
keyed-map p f (end k)     ke h ()
keyed-map p f hush        ke h ()

keyed-scan : ∀ {A B} p (f : B → A → B) z (e : Events A) → Keyed p e → Keyed p (M.scanᴱ f z e)
keyed-scan p f z (out k a r) ke _ out-here       = ke _ out-here
keyed-scan p f z (out k a r) ke h (out-there x)  = keyed-scan p f (f z a) (force r) (λ h′ y → ke h′ (out-there y)) h x
keyed-scan p f z (skip k r)  ke _ skip-here      = ke _ skip-here
keyed-scan p f z (skip k r)  ke h (skip-there x) = keyed-scan p f z (force r) (λ h′ y → ke h′ (skip-there y)) h x
keyed-scan p f z (end k)     ke h ()
keyed-scan p f z hush        ke h ()

-- A cut shows its failing value, if at all, just past where it was.
mutual
  keyed-take : ∀ {A} p i (q : A → Bool) (e : Events A) → Keyed p e → Keyed p (M.takeWhileᴱ i q e)
  keyed-take p i q (out k a r) ke h x              = keyed-taking p i q k a (q a) r ke h x
  keyed-take p i q (skip k r)  ke _ skip-here      = ke _ skip-here
  keyed-take p i q (skip k r)  ke h (skip-there x) = keyed-take p i q (force r) (λ h′ y → ke h′ (skip-there y)) h x
  keyed-take p i q (end k)     ke h ()
  keyed-take p i q hush        ke h ()

  keyed-taking : ∀ {A} p i (q : A → Bool) k a b (r : Events∞ A) → Keyed p (out k a r) → Keyed p (M.taking i q k a b r)
  keyed-taking p i     q k a true  r ke _ out-here      = ke _ out-here
  keyed-taking p i     q k a true  r ke h (out-there x) = keyed-take p i q (force r) (λ h′ y → ke h′ (out-there y)) h x
  keyed-taking p true  q k a false r ke _ out-here      = beneath-snoc p k (ix 0) (ke _ out-here)
  keyed-taking p true  q k a false r ke h (out-there ())
  keyed-taking p false q k a false r ke h ()

-- A join at `p` shows what it missed just past `p`, the rest tagged.
mutual
  keyed-rejoin : ∀ {A} p (e : Events A) → Keyed p (M.rejoin p e)
  keyed-rejoin p (out q a k) h x = keyed-shown p q (just a) k (p <ᵖ q) h x
  keyed-rejoin p (skip q k)  h x = keyed-shown p q nothing k (p <ᵖ q) h x
  keyed-rejoin p (end c)     h x with p <ᵖ c
  keyed-rejoin p (end c)     h () | true
  keyed-rejoin p (end c)     h () | false
  keyed-rejoin p hush        h ()

  keyed-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → Keyed p (M.shown p q a k b)
  keyed-shown p q (just a) k true  _ out-here       = inj₂ (tagged-sub q p)
  keyed-shown p q (just a) k true  h (out-there x)  = keyed-rejoin p (force k) h x
  keyed-shown p q nothing  k true  _ skip-here      = inj₂ (tagged-sub q p)
  keyed-shown p q nothing  k true  h (skip-there x) = keyed-rejoin p (force k) h x
  keyed-shown p q (just a) k false _ skip-here      = owned-snoc p p (ix 0) (inj₁ (prefix-refl p))
  keyed-shown p q (just a) k false h (skip-there x) = keyed-rejoin p (force k) h x
  keyed-shown p q nothing  k false _ skip-here      = owned-snoc p p (ix 0) (inj₁ (prefix-refl p))
  keyed-shown p q nothing  k false h (skip-there x) = keyed-rejoin p (force k) h x

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

  -- A FLATMAP SHOWS ONLY WHAT IT KEYS: its outer's positions, each value
  -- just past where it was, and its lanes', each keyed under where it
  -- was admitted.  The risk is `go`'s merge showing a position of its
  -- own making.
  owned-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ)
             → Keyed p (U.meaning (U.subscribe (flatMap op f s) p) ρ)

  -- A CONNECT SHOWS ONLY WHAT IT KEYS: its body's positions, and each of
  -- its source's steps and its end just past where it was.
  owned-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ)
                → Keyed p (U.meaning (U.subscribe (connect s b) p) ρ)

  -- A DEFER SHOWS ONLY WHAT IT KEYS: its skip just past where it
  -- subscribes, then its program's run under it, read by the fold's
  -- meaning rather than the unfold's.
  owned-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Keyed p (U.meaning (U.deferᶜ l p []) ρ)

-- A SUBSCRIPTION SHOWS ONLY WHAT IT KEYS: inside where it subscribes, a
-- source's position tagged by one of its joins, or a frame of one of its
-- timers.
owned-reach : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Keyed p (U.meaning (U.subscribe o p) ρ)
owned-reach (cold c)          p ρ = subst (Keyed p) (sym (U.start-meaning p (lower c) ρ)) (keyed-start p (lower c))
owned-reach empty             p ρ h ()
owned-reach (of xs)           p ρ = keyed-of p 0 xs
owned-reach (map f s)         p ρ = keyed-map p f _ (owned-reach s p ρ)
owned-reach (scan f z s)      p ρ = keyed-scan p f z _ (owned-reach s p ρ)
owned-reach (takeWhile i q s) p ρ = keyed-take p i q _ (owned-reach s p ρ)
owned-reach (flatMap op f s)  p ρ = owned-flat op f s p ρ
owned-reach (connect s b)     p ρ = owned-connect s b p ρ
owned-reach (connected i)     p ρ = keyed-rejoin p (lookup ρ i)
owned-reach (defer l)         p ρ = owned-defer l p ρ

-- A flatMap's sources stay out of every lane it can admit: the skip
-- before the lane is keyed under the flatMap, so the lane is.
--
-- REFUTED: f5faeaf6 of sources merely clear of the flatMap's subtree, by one tagged under its join
alien-shown : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p (ρ : NEnv Γ) → Alienᴱ p ρ
            → ∀ x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.subscribe (flatMap op f s) p) ρ) → Alienᴱ (x ++ [ ix 1 ]) ρ
alien-shown op f s p ρ al x r =
  alienᴱ-owned p (x ++ [ ix 1 ]) (owned-lane p x (owned-reach (flatMap op f s) p ρ (x ++ [ ix 0 ]) r)) ρ al

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
