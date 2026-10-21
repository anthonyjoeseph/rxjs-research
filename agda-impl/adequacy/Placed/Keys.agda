{-# OPTIONS --guardedness #-}

module adequacy.Placed.Keys where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (ℕ; suc; _<ᵇ_; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-monoʳ-≤; <⇒≤; <-≤-trans; ≤-trans; m≤n+m; m≤m+n; <-irrefl)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; Tail; Tail∞; pin;
  idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; Earliest; none; found; Agreeᵀ; pin⁼; idle⁼)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import adequacy.Placed.Order using (Alienᴱ; Atop; Beneath; Clear; Every; EveryT; EveryTs; Everys; Every∞; Headed; Ordered; Orders; Owned; Past; Prefix; Prefix⁺; Reaches; Steadies; Steady; Tagged; every; every-monoᴱ; every-onward; every-tailOf; everyT-burstOn; everyT-idle; everyT-∪; everyᵀ; every∞-mono; ordered; out-here; out-there; prefix-++; prefix-trans; skip-here; skip-there; steady)

open Events∞
open Tail∞

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

earliest-all : ∀ {B} (P : Events∞ B → Set) (ls : List (Events∞ B)) → All P ls → Picked P (M′.earliest ls)
earliest-all P []       []ᴬ        = tt
earliest-all P (l ∷ ls) (pl ∷ᴬ al) with M′.head (force l) | M′.earliest ls | earliest-all P ls al
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
rest-agree {k = k} end⁼      = M′.agree-refl k hush
rest-agree {k = k} hush⁼     = M′.agree-refl k hush

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
restᵀ-agree {k = k} idle⁼    = M′.agreeᵀ-refl k idle

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
    , everyT-lim (λ n → M′.tailOf (xs (suc n))) (cut r) (λ n → every-tailOf (xs (suc n)) (px (suc n))) (λ n → M′.agree-tail (ag (suc n)))
  everys-lim xs (skip h r)  px ag (skip h _)  ex (skip⁼ _ _) =
    proj₁ (every ex)
    , every-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-every (xs (suc n)) (px (suc n))) (λ n → rest-agree (ag (suc n)))
    , everyT-lim (λ n → M′.tailOf (xs (suc n))) (cut r) (λ n → every-tailOf (xs (suc n)) (px (suc n))) (λ n → M′.agree-tail (ag (suc n)))
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

every-map : ∀ {A B} {P : Pos → Set} (f : A → B) (e : Events A) → Every P e → Every P (M′.mapᴱ f e)
every (every-map f (out k a r) pe) = proj₁ (every pe) , every-map f (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-map f (skip k r)  pe) = proj₁ (every pe) , every-map f (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-map f (end k)     pe) = every pe
every (every-map f hush        pe) = tt

every-scan : ∀ {A B} {P : Pos → Set} (f : B → A → B) z (e : Events A) → Every P e → Every P (M′.scanᴱ f z e)
every (every-scan f z (out k a r) pe) = proj₁ (every pe) , every-scan f (f z a) (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-scan f z (skip k r)  pe) = proj₁ (every pe) , every-scan f z (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
every (every-scan f z (end k)     pe) = every pe
every (every-scan f z hush        pe) = tt

-- A connect shows its body's positions and each of its source's steps,
-- and its end, just past it; it leaves running its body's tail and its
-- source's, each step where it was.
mutual
  every-beside : ∀ {A B} {P : Pos → Set} r (β : Events∞ B) (σ : Events∞ A) → Every∞ P β
               → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → Every P (M′.beside r β σ)
  every (every-beside r β σ pb ps) = every (every-side r β σ (force σ) pb ps (proj₁ ps))

  every-side : ∀ {A B} {P : Pos → Set} r (β : Events∞ B) (σ : Events∞ A) e → Every∞ P β
             → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → Every (λ q → P q × P (q ++ [ ix 0 ])) e → Every P (M′.side r β σ e)
  every (every-side r β σ (out q _ _) pb ps pe) = every (every-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) pb ps (proj₂ (proj₁ (every pe))))
  every (every-side r β σ (skip q _)  pb ps pe) = every (every-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) pb ps (proj₂ (proj₁ (every pe))))
  every (every-side r β σ (end c)     pb ps pe) = every (every-ahead r β σ (c ++ [ ix 0 ]) (M′.before (c ++ [ ix 0 ]) (force β)) pb ps (proj₂ (every pe)))
  every (every-side r β σ hush        pb ps pe) = every (proj₁ pb)

  every-ahead : ∀ {A B} {P : Pos → Set} r (β : Events∞ B) (σ : Events∞ A) q t → Every∞ P β
              → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → P q → Every P (M′.ahead r β σ q t)
  every (every-ahead r β σ q true  pb ps pq) =
    pq , every-beside r β σ′ pb on , everyT-∪ (M′.burstOn r σ′) (cut β) (everyT-burstOn r σ′ (every∞-mono (λ _ → proj₁) σ′ on)) (proj₂ pb)
    where σ′ = M′.onward∞ σ (force σ)
          on = every-onward σ (force σ) (proj₁ ps) (proj₂ ps) (proj₁ ps)
  every (every-ahead r β σ q false pb ps pq) = every (every-body r σ q (force β) ps pq (proj₁ pb))

  every-body : ∀ {A B} {P : Pos → Set} r (σ : Events∞ A) q (e : Events B)
             → Every∞ (λ q → P q × P (q ++ [ ix 0 ])) σ → P q → Every P e → Every P (M′.body r σ q e)
  every (every-body r σ q (out k a β) ps pq pe) =
    proj₁ (every pe) , every-ahead r β σ q (M′.before q (force β)) (proj₂ (every pe)) ps pq
    , everyT-∪ (M′.burstOn r σ) (cut β) (everyT-burstOn r σ (every∞-mono (λ _ → proj₁) σ ps)) (proj₂ (proj₂ (every pe)))
  every (every-body r σ q (skip k β)  ps pq pe) =
    proj₁ (every pe) , every-ahead r β σ q (M′.before q (force β)) (proj₂ (every pe)) ps pq
    , everyT-∪ (M′.burstOn r σ) (cut β) (everyT-burstOn r σ (every∞-mono (λ _ → proj₁) σ ps)) (proj₂ (proj₂ (every pe)))
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

values-map : ∀ {A B} {G : B → Set} (f : A → B) (e : Events A) → (∀ a → G (f a)) → Values G (M′.mapᴱ f e)
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
  Lane m = ∀ k → S k → Every∞ P (M′.enter m k)

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
  everyT-cuts : ∀ {B} (ls : List (Events∞ B)) → All (Every∞ P) ls → EveryT P (M′.cuts ls)
  everyT-cuts []       []ᴬ        = everyT-idle
  everyT-cuts (l ∷ ls) (pl ∷ᴬ al) = everyT-∪ (cut l) (M′.cuts ls) (proj₂ pl) (everyT-cuts ls al)

  everyT-whole : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t → Outerᴹ o → All (Every∞ P) ls → EveryT P t → EveryT P (M′.whole o ls t)
  everyT-whole nothing  ls t po pl pt = everyT-∪ idle (M′.cuts ls ∪ t) everyT-idle (everyT-∪ (M′.cuts ls) t (everyT-cuts ls pl) pt)
  everyT-whole (just e) ls t po pl pt = everyT-∪ (cut e) (M′.cuts ls ∪ t) (proj₂ po) (everyT-∪ (M′.cuts ls) t (everyT-cuts ls pl) pt)

  -- An admitted lane subscribes held, a queued one stays a lane, and a
  -- dropped one leaves its tail.
  Admitted : ∀ {B} → List (Events∞ B) × List (MonotonicList B) × Tail → Set
  Admitted (ls , qs , d) = All (Every∞ P) ls × All Lane qs × EveryT P d

  admit-all : ∀ {B} op q (m : MonotonicList B) ls qs → S q → Lane m → All (Every∞ P) ls → All Lane qs
            → Admitted (M′.admit op q m ls qs)
  admit-all (M′.mergeᶠ nothing)  q m ls       qs sq lm pl pq = lm q sq ∷ᴬ pl , pq , everyT-idle
  admit-all (M′.mergeᶠ (just n)) q m ls       qs sq lm pl pq with length ls <ᵇ n
  ... | true  = lm q sq ∷ᴬ pl , pq , everyT-idle
  ... | false = pl , All++⁺ pq (lm ∷ᴬ []ᴬ) , everyT-idle
  admit-all M′.switchᶠ           q m ls       qs sq lm pl pq = lm q sq ∷ᴬ []ᴬ , pq , everyT-cuts ls pl
  admit-all M′.exhaustᶠ          q m []       qs sq lm pl pq = lm q sq ∷ᴬ []ᴬ , pq , everyT-idle
  admit-all M′.exhaustᶠ          q m (l ∷ ls) qs sq lm pl pq = pl , pq , everyT-idle

  -- A flatMap's merge shows its outer's skips and ends where they were,
  -- each value just past where it was, its lanes' events where they
  -- were, each lane's end just past it when another is queued, and
  -- what ended parts left running where it steps.
  mutual
    every-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → Outerᴹ o → All (Every∞ P) ls → All Lane qs → EveryT P t
             → Every P (M′.go op o ls qs t)
    every (every-go op o ls qs idle      po pl pq pt) = every (every-parts op o ls qs idle po pl pq pt)
    every (every-go op o ls qs (pin k u) po pl pq pt) = every (every-left op o ls qs k u (M′.ahead-of k o ls) po pl pq pt)

    every-left : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u b → Outerᴹ o → All (Every∞ P) ls → All Lane qs
               → EveryT P (pin k u) → Every P (M′.left op o ls qs k u b)
    every (every-left op o ls qs k u true  po pl pq pt) =
      proj₁ (everyᵀ pt) , every-go op o ls qs (later u) po pl pq (proj₂ (everyᵀ pt)) , everyT-whole o ls (later u) po pl (proj₂ (everyᵀ pt))
    every (every-left op o ls qs k u false po pl pq pt) = every (every-parts op o ls qs (pin k u) po pl pq pt)

    every-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → Outerᴹ o → All (Every∞ P) ls → All Lane qs → EveryT P t
                → Every P (M′.parts op o ls qs t)
    every-parts op o ls qs t po pl pq pt with M′.earliest ls | earliest-all (Every∞ P) ls pl
    ... | none            | _                = every-via op o ls qs t po pl pq pt
    ... | found k bs l as | (pb , pl₁ , pa)  = every-race op o k bs l as qs t po pb pl₁ pa pq pt

    every-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → Outerᴹ o → All (Every∞ P) ls → All Lane qs → EveryT P t
              → Every P (M′.viaOuter op o ls qs t)
    every-via op nothing  ls qs t po pl pq pt = record { every = tt }
    every-via op (just e) ls qs t po pl pq pt = every-outer op e ls qs t (force e) (proj₁ po) (proj₂ po) pl pq pt

    every-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t → Outerᴹ o
               → All (Every∞ P) bs → Every∞ P l → All (Every∞ P) as → All Lane qs → EveryT P t → Every P (M′.race op o k bs l as qs t)
    every-race op nothing  k bs l as qs t po pb pl pa pq pt = every-lane op nothing bs l as qs t (force l) po pb (proj₁ pl) (proj₂ pl) pa pq pt
    every-race op (just e) k bs l as qs t po pb pl pa pq pt with M′.head (force e)
    ... | nothing = every-lane op (just e) bs l as qs t (force l) po pb (proj₁ pl) (proj₂ pl) pa pq pt
    ... | just k′ with k′ <ᵖ k
    ...   | true  = every-outer op e (bs ++ l ∷ as) qs t (force e) (proj₁ po) (proj₂ po) (All++⁺ pb (pl ∷ᴬ pa)) pq pt
    ...   | false = every-lane op (just e) bs l as qs t (force l) po pb (proj₁ pl) (proj₂ pl) pa pq pt

    every-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) → Outer x → EveryT P (cut e)
                → All (Every∞ P) ls → All Lane qs → EveryT P t → Every P (M′.outer op e ls qs t x)
    every (every-outer op e ls qs t (out q m r) po pe pl pq pt)
      with M′.admit op (q ++ [ ix 1 ]) m ls qs
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
               → Every P (M′.lane op o bs l as qs t x)
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
      , every-go op o (M′.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ cut l) po (ln ∷ᴬ All++⁺ pb pa) pq (everyT-∪ t (cut l) pt pl)
      , everyT-whole o (M′.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) (t ∪ cut l) po (ln ∷ᴬ All++⁺ pb pa) (everyT-∪ t (cut l) pt pl)
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

-- Every part silent: whatever the ended left comes ahead of them all.
clears-quiet : ∀ {B} k (ls : List (Events∞ B)) → All (λ l → M′.head (force l) ≡ nothing) ls → M′.clears k ls ≡ true
clears-quiet k []       []ᴬ        = refl
clears-quiet k (l ∷ ls) (hl ∷ᴬ hs) rewrite hl = clears-quiet k ls hs

ahead-quiet : ∀ {B} k (o : Maybe (Events∞ (MonotonicList B))) ls → M′.headᴼ o ≡ nothing → All (λ l → M′.head (force l) ≡ nothing) ls
            → M′.ahead-of k o ls ≡ true
ahead-quiet k o ls ho hs rewrite ho = clears-quiet k ls hs
