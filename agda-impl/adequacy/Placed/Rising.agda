{-# OPTIONS --guardedness #-}

module adequacy.Placed.Rising where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-monoʳ-<; ≤-pred; m≤n⇒m<n∨m≡n; <⇒≢; +-suc; +-monoʳ-≤; ≤-trans; m≤m+n; <-irrefl)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (timelineAt; Events; Events∞; Pos; From; Timeline; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_;
  <ᵖ-asym; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-part; ≮-trans; <ᵖ-below; <ᵖ-tick; <ᵖ-ix; Tail;
  Tail∞; pin; idle)
open import denotation.MonotonicList using (MonotonicList; Agree; agree; agreeᵀ; none; found)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (env-refl)
open import adequacy.Finite using (Finite; cold-f; empty-f; of-f; map-f; scan-f; takeWhile-f; flatMap-f; connect-f; connected-f; defer-f; trunc; finite-trunc; trunc-agree)
open import adequacy.Placed.Order using (Alien; Alienᴱ; Atop; Clear; Disjoint; Every; EveryT; Everyᴱ; Every∞; Ext; Headed; Ordered;
  Owned; Past; Prefix; Steady; Tagged; atop-map; atop-scan; cons-ext; every; every-lookup;
  every-mono; everyT-burstOn; everyT-idle; everyT-mono; everyT-∪; everyᵀ; every∞-mono; ext;
  ext-eq; ext-irrefl; headed-snoc; ordered; prefix-++; steady; under-ext)
open import adequacy.Placed.Keys using (Mark; module Merge; alienᴱ-owned; atop-agree; clear-agree; earliest-all; every-beside;
  every-lim; every-map; every-scan; every-≈; everyT-≈; ix-mark; last-mark; no-tick; ordered-≈;
  owned-tagged; owned-trans; prefix-refl; sibling; steady-≈; tagged-mark; tagged-sub;
  tick-last; values-map)

open Events∞
open Tail∞

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
    every-frames : ∀ {A t} τ e (m : M.From A (suc t)) → tick e ≡ τ + t → P e → Every P (M′.frames τ e m)
    every (every-frames τ e M.done                     te pe) = pe
    every (every-frames τ e M.quiet                    te pe) = tt
    every (every-frames τ e (M.at (suc t′) (s≤s le) b) te pe) =
      every (every-burst τ _ 0 b refl (subst (λ x → S (ix x ∷ sub e ∷ [])) (sym (+-suc τ t′))
        (frame (τ + t′) e pe (subst (_≤ τ + t′) (sym te) (+-monoʳ-≤ τ le)))))

    every-burst : ∀ {A t} τ r i (b : M.Frame A t) → tick r ≡ τ + t → S r → Every P (M′.burst τ r i b)
    every (every-burst τ r i (M.emit a k) tr sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) tr sr , everyT-idle
    every (every-burst τ r i (M.stall k)  tr sr) = child r (ix i) (ix-mark i) sr , every-burst τ r (suc i) (M.Frame∞.force k) tr sr , everyT-idle
    every (every-burst τ r i (M.close k)  tr sr) =
      child r (ix i) (ix-mark i) sr , every-frames τ (r ++ [ last ]) (M.From∞.force k) (trans (tick-last r) tr) (child r last last-mark sr) , everyT-idle

  every-start : ∀ {A} p (m : From A 0) → S p → Every P (M′.start p m)
  every-start p (M.at zero _ b)    sp = every-burst (tick p) p 0 b (sym (+-identityʳ (tick p))) sp
  every-start p (M.at (suc n) _ b) sp =
    every-burst (tick p) _ 0 b refl
      (subst (λ x → S (ix x ∷ sub (p ++ [ last ]) ∷ [])) (sym (+-suc (tick p) n))
        (frame (tick p + n) _ (child p last last-mark sp) (subst (_≤ tick p + n) (sym (tick-last p)) (m≤m+n (tick p) n))))
  every-start p M.done             sp = record { every = child p last last-mark sp }
  every-start p M.quiet            sp = record { every = tt }

  every-of : ∀ {A} p i (xs : List A) → S p → Every P (M′.ofᴱ p i xs)
  every (every-of p i []       sp) = child p last last-mark sp
  every (every-of p i (x ∷ xs) sp) = child p (ix i) (ix-mark i) sp , every-of p (suc i) xs sp , everyT-idle

  -- A cut shows its failing value, if at all, just past where it was,
  -- and ends just past it, leaving running what the source left.
  mutual
    every-take : ∀ {A} i (q : A → Bool) (e : Events A) → Every P e → Every P (M′.takeWhileᴱ i q e)
    every (every-take i q (out k a r) pe) = every (every-taking i q k a (q a) r pe)
    every (every-take i q (skip k r)  pe) = proj₁ (every pe) , every-take i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-take i q (end k)     pe) = every pe
    every (every-take i q hush        pe) = tt

    every-taking : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) → Every P (out k a r) → Every P (M′.taking i q k a b r)
    every (every-taking i     q k a true  r pe) = proj₁ (every pe) , every-take i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-taking true  q k a false r pe) =
      deeper k (ix 0) (ix-mark 0) (proj₁ (every pe)) , record { every = deeper k last last-mark (proj₁ (every pe)) } , proj₂ (proj₂ (every pe))
    every (every-taking false q k a false r pe) = deeper k last last-mark (proj₁ (every pe))

  -- A join at `p` shows what it missed just past `p`, the rest tagged.
  mutual
    every-rejoin : ∀ {A} p (e : Events A) → S p → Every Src e → Every P (M′.rejoin p e)
    every (every-rejoin p (out q a k) sp se) = every (every-shown p q (just a) k (p <ᵖ q) refl sp (proj₁ (every se)) (proj₁ (proj₂ (every se))))
    every (every-rejoin p (skip q k)  sp se) = every (every-shown p q nothing k (p <ᵖ q) refl sp (proj₁ (every se)) (proj₁ (proj₂ (every se))))
    every (every-rejoin p (end c)     sp se) with p <ᵖ c in pc
    ... | true  = join c p (every se) sp pc
    ... | false = child p last last-mark sp
    every (every-rejoin p hush        sp se) = tt

    every-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → p <ᵖ q ≡ b → S p → Src q → Every Src (force k) → Every P (M′.shown p q a k b)
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
    subst (Every P) (sym (U.start-meaning k (timelineAt c k) ρ)) (every-start k (timelineAt c k) sk)
    , subst (EveryT P) (sym (U.start-cut k (timelineAt c k) ρ)) everyT-idle
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
    , everyT-∪ (M′.burstOn (k ++ [ ix 1 ]) Sᶜ) (cut Bᶜ) (everyT-burstOn (k ++ [ ix 1 ]) Sᶜ is) (proj₂ ib)
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
          → Atop k (M′.lane op o bs l as qs t x)
atop-lane op o        bs      l as      qs       t (out _ _ _) k a = a
atop-lane op o        bs      l as      qs       t (skip _ _)  k a = a
atop-lane op o        bs      l as      (m ∷ qs) t (end c) k a = snoc-atop c (ix 0) k a
atop-lane op nothing  []      l []      []       t (end c) k a = a
atop-lane op nothing  []      l (_ ∷ _) []       t (end c) k a = a
atop-lane op nothing  (_ ∷ _) l as      []       t (end c) k a = a
atop-lane op (just _) bs      l as      []       t (end c) k a = a
atop-lane op o        bs      l as      qs       t hush    k a = tt

atop-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) k → Atop k x
           → Atop k (M′.outer op e ls qs t x)
atop-outer op e ls qs t (out q m r) k a with M′.admit op (q ++ [ ix 1 ]) m ls qs
... | ls′ , qs′ , d = snoc-atop q (ix 0) k a
atop-outer op e ls       qs       t (skip q r) k a = a
atop-outer op e []       []       t (end c)    k a = a
atop-outer op e []       (m ∷ qs) t (end c)    k a = a
atop-outer op e (l ∷ ls) qs       t (end c)    k a = a
atop-outer op e ls       qs       t hush       k a = tt

atop-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k′ bs (l : Events∞ B) as qs t k → Atop k (force l) → Atopᴹ k o
          → Atop k (M′.race op o k′ bs l as qs t)
atop-race op nothing  k′ bs l as qs t k al ao = atop-lane op nothing bs l as qs t (force l) k al
atop-race op (just e) k′ bs l as qs t k al ao with M′.head (force e)
... | nothing = atop-lane op (just e) bs l as qs t (force l) k al
... | just k″ with k″ <ᵖ k′
...   | true  = atop-outer op e (bs ++ l ∷ as) qs t (force e) k ao
...   | false = atop-lane op (just e) bs l as qs t (force l) k al

atop-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t k → Atopᴹ k o → Atop k (M′.viaOuter op o ls qs t)
atop-via op nothing  ls qs t k ao = tt
atop-via op (just e) ls qs t k ao = atop-outer op e ls qs t (force e) k ao

atop-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t k → All (λ l → Atop k (force l)) ls → Atopᴹ k o
           → Atop k (M′.parts op o ls qs t)
atop-parts op o ls qs t k al ao with M′.earliest ls | earliest-all (λ l → Atop k (force l)) ls al
... | none             | _             = atop-via op o ls qs t k ao
... | found k′ bs l as | (_ , al′ , _) = atop-race op o k′ bs l as qs t k al′ ao

atop-left : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k′ u b k → All (λ l → Atop k (force l)) ls → Atopᴹ k o
          → k′ <ᵖ k ≡ false → Atop k (M′.left op o ls qs k′ u b)
atop-left op o ls qs k′ u true  k al ao at = at
atop-left op o ls qs k′ u false k al ao at = atop-parts op o ls qs (pin k′ u) k al ao

atop-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t k → All (λ l → Atop k (force l)) ls → Atopᴹ k o → AtopT k t
        → Atop k (M′.go op o ls qs t)
atop-go op o ls qs idle       k al ao at = atop-parts op o ls qs idle k al ao
atop-go op o ls qs (pin k′ u) k al ao at = atop-left op o ls qs k′ u (M′.ahead-of k′ o ls) k al ao at

-- A cut, a merge with a source's steps, a join: each first no earlier
-- than what it reads, or than where it subscribes.
atop-take : ∀ {A} i (q : A → Bool) k (e : Events A) → Atop k e → Atop k (M′.takeWhileᴱ i q e)
atop-take i q k (out h a r) at with q a
atop-take i     q k (out h a r) at | true  = at
atop-take true  q k (out h a r) at | false = snoc-atop h (ix 0) k at
atop-take false q k (out h a r) at | false = snoc-atop h last k at
atop-take i q k (skip _ _) at = at
atop-take i q k (end _)    at = at
atop-take i q k hush       at = tt

atop-body : ∀ {A B} r (σ : Events∞ A) q (e : Events B) k → Atop k e → Atop k (M′.body r σ q e)
atop-body r σ q (out _ _ _) k a = a
atop-body r σ q (skip _ _)  k a = a
atop-body r σ q (end _)     k a = a
atop-body r σ q hush        k a = tt

atop-ahead : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) q t k → Atop k (force β) → q <ᵖ k ≡ false → Atop k (M′.ahead r β σ q t)
atop-ahead r β σ q true  k ab aq = aq
atop-ahead r β σ q false k ab aq = atop-body r σ q (force β) k ab

atop-side : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) (e : Events A) k → Atop k (force β) → Atop k e → Atop k (M′.side r β σ e)
atop-side r β σ (out q _ _) k ab as = atop-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) k ab (snoc-atop q (ix 0) k as)
atop-side r β σ (skip q _)  k ab as = atop-ahead r β σ (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β)) k ab (snoc-atop q (ix 0) k as)
atop-side r β σ (end c)     k ab as = atop-ahead r β σ (c ++ [ ix 0 ]) (M′.before (c ++ [ ix 0 ]) (force β)) k ab (snoc-atop c (ix 0) k as)
atop-side r β σ hush        k ab as = ab

atop-beside : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) k → Atop k (force β) → Atop k (force σ) → Atop k (M′.beside r β σ)
atop-beside r β σ k ab as = atop-side r β σ (force σ) k ab as

atop-rejoin : ∀ {A} p (e : Events A) → Atop p (M′.rejoin p e)
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
rise-burst : ∀ {A t} τ r i (b : M.Frame A t) k → (r ++ [ ix i ]) <ᵖ k ≡ false → Atop k (M′.burst τ r i b)
rise-burst τ r i (M.emit _ _) k h = h
rise-burst τ r i (M.stall _)  k h = h
rise-burst τ r i (M.close _)  k h = h

rise-tick : ∀ τ n x j′ → (ix (τ + suc n) ∷ x) <ᵖ (ix τ ∷ j′) ≡ false
rise-tick τ n x j′ with (ix (τ + suc n) ∷ x) <ᵖ (ix τ ∷ j′) in h
... | false = refl
... | true  = ⊥-elim (<-irrefl refl (≤-trans (subst (_≤ τ) (+-suc τ n) (<ᵖ-tick (τ + suc n) τ x j′ h)) (m≤m+n τ n)))

rise-start : ∀ {A} τ j′ (m : From A 0) → Atop (ix τ ∷ j′) (M′.start (ix τ ∷ j′) m)
rise-start τ j′ (M.at zero _ b)    = rise-burst τ (ix τ ∷ j′) 0 b (ix τ ∷ j′) (<ᵖ-asym (ix τ ∷ j′) ((ix τ ∷ j′) ++ [ ix 0 ]) (<ᵖ-below (ix τ ∷ j′) []))
rise-start τ j′ (M.at (suc n) _ b) = rise-burst τ _ 0 b _ (rise-tick τ n (sub ((ix τ ∷ j′) ++ [ last ]) ∷ ix 0 ∷ []) j′)
rise-start τ j′ M.done             = <ᵖ-asym (ix τ ∷ j′) ((ix τ ∷ j′) ++ [ last ]) (<ᵖ-below (ix τ ∷ j′) [])
rise-start τ j′ M.quiet            = tt

-- A SUBSCRIPTION SHOWS NOTHING BEFORE WHERE IT SUBSCRIBES, where a tick
-- heads it.
rise-sub : ∀ {Γ A} (o : Obs Timeline Γ A) j (ρ : NEnv Γ) → Headed j → Atop j (U.meaning (U.subscribe o j) ρ)
rise-sub (cold c) (ix τ ∷ j′) ρ hj =
  subst (Atop (ix τ ∷ j′)) (sym (U.start-meaning (ix τ ∷ j′) (timelineAt c (ix τ ∷ j′)) ρ)) (rise-start τ j′ (timelineAt c (ix τ ∷ j′)))
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

-- A burst's first event is at its next index.
burst-past : ∀ {A t} τ r i (b : M.Frame A t) {k} → k <ᵖ (r ++ [ ix i ]) ≡ true × ¬ Ext k (r ++ [ ix i ]) → Past k (M′.burst τ r i b)
burst-past τ r i (M.emit _ _) h = h
burst-past τ r i (M.stall _)  h = h
burst-past τ r i (M.close _)  h = h

-- A burst at its frame's tick rises, and so does every frame after it:
-- each frame's tick past the last.
mutual
  rising-burst : ∀ {A t} τ n q i (b : M.Frame A t) → n ≡ τ + t → Rising (M′.burst τ (ix n ∷ q) i b)
  rises (rising-burst τ n q i (M.emit a f) e) = burst-past τ _ (suc i) (M.Frame∞.force f) (next-ix (ix n ∷ q) i) , rising-burst τ n q (suc i) _ e
  rises (rising-burst τ n q i (M.stall f)  e) = burst-past τ _ (suc i) (M.Frame∞.force f) (next-ix (ix n ∷ q) i) , rising-burst τ n q (suc i) _ e
  rises (rising-burst τ n q i (M.close f)  e) = frames-past τ q i (M.From∞.force f) e , rising-frames τ _ (M.From∞.force f)

  rising-frames : ∀ {A t} τ e (m : From A t) → Rising (M′.frames τ e m)
  rises (rising-frames τ e M.done)         = tt
  rises (rising-frames τ e M.quiet)        = tt
  rises (rising-frames τ e (M.at t′ _ b)) = rises (rising-burst τ (τ + t′) (sub e ∷ []) 0 b refl)

  frames-past : ∀ {A t n} τ q i (m : From A (suc t)) → n ≡ τ + t → Past (ix n ∷ q ++ [ ix i ]) (M′.frames τ (ix n ∷ q ++ [ last ]) m)
  frames-past τ q i M.done        e    = ix-last (ix _ ∷ q) i
  frames-past τ q i M.quiet       e    = tt
  frames-past τ q i (M.at t′ l b) refl = burst-past τ _ 0 b (tick-past (q ++ [ ix i ]) _ (+-monoʳ-< τ l))

-- A LIST'S RUN RISES: its values at rising indices, then its end.
rising-of : ∀ {A} p i (xs : List A) → Rising (M′.ofᴱ p i xs)
rises (rising-of p i [])           = tt
rises (rising-of p i (x ∷ []))     = ix-last p i , rising-of p (suc i) []
rises (rising-of p i (x ∷ y ∷ xs)) = next-ix p i , rising-of p (suc i) (y ∷ xs)

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
past-take : ∀ {A} i (p : A → Bool) k (e : Events A) → Past k e → Past k (M′.takeWhileᴱ i p e)
past-take i p k (out h a r) pk with p a | i
... | true  | _     = pk
... | false | true  = past-snoc k h (ix 0) pk
... | false | false = past-snoc k h last pk
past-take i p k (skip h r)  pk = pk
past-take i p k (end h)     pk = pk
past-take i p k hush        pk = tt

clear-take : ∀ {A} i (p : A → Bool) k (e : Events A) → Clear k e → Clear k (M′.takeWhileᴱ i p e)
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
  ordered-take : ∀ {A} i (p : A → Bool) (e : Events A) → Ordered e → Ordered (M′.takeWhileᴱ i p e)
  ordered (ordered-take i p (out h a r) o) = ordered (ordered-taking i p h a (p a) r (ordered o))
  ordered (ordered-take i p (skip h r)  o) = atop-take i p h _ (proj₁ (ordered o)) , ordered-take i p _ (proj₂ (ordered o))
  ordered (ordered-take i p (end h)     o) = tt
  ordered (ordered-take i p hush        o) = tt

  ordered-taking : ∀ {A} i (p : A → Bool) h a b (r : Events∞ A) → Atop h (force r) × Ordered (force r) → Ordered (M′.taking i p h a b r)
  ordered (ordered-taking i     p h a true  r (at , o)) = atop-take i p h _ at , ordered-take i p _ o
  ordered (ordered-taking true  p h a false r _)        = <ᵖ-asym (h ++ [ ix 0 ]) (h ++ [ last ]) (proj₁ (ix-last h 0)) , record { ordered = tt }
  ordered (ordered-taking false p h a false r _)        = tt

-- A CUT KEEPS A RUN STEADY: the failing value just inside its own
-- position, its completion just past that.
mutual
  steady-take : ∀ {A} i (p : A → Bool) (e : Events A) → Steady e → Steady (M′.takeWhileᴱ i p e)
  steady (steady-take i p (out h a r) s) = steady (steady-taking i p h a (p a) r (steady s))
  steady (steady-take i p (skip h r)  s) = clear-take i p h _ (proj₁ (steady s)) , steady-take i p _ (proj₂ (steady s))
  steady (steady-take i p (end h)     s) = tt
  steady (steady-take i p hush        s) = tt

  steady-taking : ∀ {A} i (p : A → Bool) h a b (r : Events∞ A) → Past h (force r) × Steady (force r) → Steady (M′.taking i p h a b r)
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

-- A DEFER SHOWS A SKIP, THEN ITS PROGRAM SUBSCRIBED JUST PAST IT: the
-- fold's meaning there agrees with the program's at every depth, and
-- nothing the program shows sorts before where it subscribes, nor keys
-- under the skip, its sibling.
module Deferred {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) (hp : Headed p) (cl : Alienᴱ p ρ) where
  P₁ = p ++ [ ix 1 ]
  S  = U.meaning (U.subscribe (Later.force l) P₁) ρ
  X  = M′.observe (⟦ Later.force l ⟧ᴰ (U.hots ρ)) P₁

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

