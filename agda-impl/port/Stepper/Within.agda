{-# OPTIONS --guardedness #-}

-- A STEP KEEPS THE GHOST PLACED: what a node's step leaves is placed
-- within, at any scope whose sources are clear of the step, node by
-- node as the step runs each part.
module port.Stepper.Within where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using ([_,_])
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Data.List.Membership.Propositional using (_∈_)
open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events∞; end; Pos; ix; _<ᵖ_; <ᵖ-below; Timeline; From; Frame)
import denotation.MonotonicList.Events as E
open import denotation.NonExpansive using (Agreeˢ)
open import denotation.MonotonicList using (agree-refl)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import port.Sane using (Sane; Mode; over)
open import port.Stepper.Past using (Clear; Placedˢ; Shy; Skips; Withinˢ; _≃_; afterᴱ; alike; clear-lower; head-map; head-scan; placed-step; shows)
open import port.Stepper.Fed using (placed-fed; placed-shut)
open import port.Env using (nagree-refl; same-cons)
open import port.Stepper.Parts using (clear-take; fed-here; head-body; head-shut)
open import port.Stepper using (skips; shy-clear; step-skips)
open import port.Placed.Order using (Placed; Within)
open import port.Placed.Heads using (ApartFed; ApartNext; apart-fed; apart-next; apart-sides)

open _≃_
open Events∞
open Agreeˢ using (nowˢ)

-- A value changed, a running total or a take keeps its source's stepped
-- node placed within it.
map-within : ∀ {Γ A B} (ρ : NEnv Γ) (f : A → B) (s : U.Step Γ A) → Placedˢ ρ s → Withinˢ ρ (U.mapˢ f s)
map-within ρ f (U.outˢ k a c) (_ , p) = p
map-within ρ f (U.skipˢ k c)  (_ , p) = p
map-within ρ f (U.endˢ k)     _       = tt
map-within ρ f U.hushˢ        _       = tt

scan-within : ∀ {Γ A B} (ρ : NEnv Γ) (f : B → A → B) z (s : U.Step Γ A) → Placedˢ ρ s → Withinˢ ρ (U.scanˢ f z s)
scan-within ρ f z (U.outˢ k a c) (_ , p) = p
scan-within ρ f z (U.skipˢ k c)  (_ , p) = p
scan-within ρ f z (U.endˢ k)     _       = tt
scan-within ρ f z U.hushˢ        _       = tt

take-within : ∀ {Γ A} (ρ : NEnv Γ) i (p : A → Bool) (s : U.Step Γ A) → Placedˢ ρ s → Withinˢ ρ (U.takeWhileˢ i p s)
take-within ρ i p (U.outˢ k a c) (_ , pc) = taking i (p a)
  where
    taking : ∀ j b → Withinˢ ρ (U.taking j p k a c b)
    taking j     true  = pc
    taking true  false = tt
    taking false false = tt
take-within ρ i p (U.skipˢ k c)  (_ , pc) = pc
take-within ρ i p (U.endˢ k)     _        = tt
take-within ρ i p U.hushˢ        _        = tt

-- A generator steps to a generator, a joiner to itself.
burst-within : ∀ {Γ A t} (ρ : NEnv Γ) τ r i (b : Frame A t) → Withinˢ ρ (U.burstˢ τ r i b)
burst-within ρ τ r i (E.emit a k) = tt
burst-within ρ τ r i (E.stall k)  = tt
burst-within ρ τ r i (E.close k)  = tt

frames-within : ∀ {Γ A t} (ρ : NEnv Γ) τ e (m : From A t) → Withinˢ ρ (U.framesˢ τ e m)
frames-within ρ τ e E.done     = tt
frames-within ρ τ e E.quiet    = tt
frames-within ρ τ e (E.at t _ b) = burst-within ρ τ _ 0 b

of-within : ∀ {Γ A} (ρ : NEnv Γ) p i (xs : List A) → Withinˢ ρ (U.ofˢ p i xs)
of-within ρ p i []       = tt
of-within ρ p i (x ∷ xs) = tt

join-within : ∀ {Γ A} (ρ : NEnv Γ) (i : A ∈ Γ) p xs e → Within (U.joinᶜ i p xs e) ρ → Withinˢ ρ (U.joinˢ i p xs e)
join-within ρ i p ((q , just a) ∷ xs) e        w = w
join-within ρ i p ((q , nothing) ∷ xs) e       w = w
join-within ρ i p []                   (just c) w = tt
join-within ρ i p []                   nothing  w = tt

postulate
  -- What a sane, placed flatMap's step leaves holds its parts placed,
  -- when its sources are clear of the step.
  --
  -- REFUTED: c8c55884 over a placing with each live joiner joined before its source, by a lane admitted past its source's next event
  flat-within : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} op (g : A → Pos → U.Node Γ B) o ls qs pl (ρ : NEnv Γ)
              → Sane ν (U.flatMapᶜ op g o ls qs pl) → Placed (U.flatMapᶜ op g o ls qs pl) ρ
              → Clear ν (U.headˢ (U.step (U.flatMapᶜ op g o ls qs pl))) ρ → Withinˢ ρ (U.step (U.flatMapᶜ op g o ls qs pl))

  -- A defer's program subscribed, its notices fed, is placed.
  defer-within : ∀ {Γ A} (l : Later Timeline Γ A) p ns (ρ : NEnv Γ) → Placed (U.deferᶜ l p ns) ρ → Withinˢ ρ (U.step (U.deferᶜ l p ns))

-- A rest-like steps to a rest-like.
union-within : ∀ {Γ B} (ρ : NEnv Γ) (x : U.Node Γ B) sx y sy → Withinˢ ρ sy → Withinˢ ρ (U.unionˢ x sx y sy)
union-within ρ x (U.skipˢ k x′) y (U.skipˢ k′ y′) _ with k <ᵖ k′
... | true  = tt
... | false = tt
union-within ρ x (U.skipˢ k x′) y (U.outˢ _ _ _) _ = tt
union-within ρ x (U.skipˢ k x′) y (U.endˢ _)     _ = tt
union-within ρ x (U.skipˢ k x′) y U.hushˢ        _ = tt
union-within ρ x (U.outˢ _ _ _) y sy w = w
union-within ρ x (U.endˢ _)     y sy w = w
union-within ρ x U.hushˢ        y sy w = w

under-within : ∀ {Γ A B C} (ρ : NEnv Γ) (s : U.Source Γ A) (b : U.Step (A ∷ Γ) C) → Withinˢ ρ (U.underˢ {B = B} s b)
under-within ρ s (U.skipˢ k b)  = tt
under-within ρ s (U.outˢ _ _ _) = tt
under-within ρ s (U.endˢ _)     = tt
under-within ρ s U.hushˢ        = tt

mutual
  rest-within : ∀ {Γ A B} (ρ : NEnv Γ) (n : U.Node Γ A) → Withinˢ ρ (U.restˢ {B = B} n)
  rest-within ρ (U.mapᶜ f c)         = rest-within ρ c
  rest-within ρ (U.scanᶜ f z c)      = rest-within ρ c
  rest-within ρ (U.takeWhileᶜ i p c) = rest-within ρ c
  rest-within ρ (U.flatMapᶜ op g o ls qs p) =
    union-within ρ (U.outerᶜ o) (U.restᴹ o) _ _ (union-within ρ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p) (rest-within ρ p))
  rest-within ρ (U.connectᶜ {B = C} r b (U.live s))    = union-within ρ _ (U.burstsˢ r s (U.step s)) _ _ (under-within ρ (U.live s) (U.restˢ {B = C} b))
  rest-within ρ (U.connectᶜ {B = C} r b (U.ended c t)) = union-within ρ _ (U.burstsˢ r t (U.step t)) _ _ (under-within ρ (U.ended c t) (U.restˢ {B = C} b))
  rest-within ρ (U.endingᶜ p n)      = rest-within ρ n
  rest-within ρ (U.restᶜ n)          = rest-within ρ n
  rest-within ρ (U.unionᶜ x y)       = union-within ρ (U.restᶜ x) (U.restˢ x) (U.restᶜ y) (U.restˢ y) (rest-within ρ y)
  rest-within ρ (U.burstingᶜ r t)    = bursts-within ρ r t (U.step t)
  rest-within ρ (U.underᶜ {C = C} s b) = under-within ρ s (U.restˢ {B = C} b)
  rest-within ρ (U.framesᶜ τ e m)    = tt
  rest-within ρ (U.burstᶜ τ r i b)   = tt
  rest-within ρ (U.ofᶜ p i xs)       = tt
  rest-within ρ (U.joinᶜ i p xs e)   = tt
  rest-within ρ (U.deferᶜ l p ns)    = tt
  rest-within ρ U.idleᶜ              = tt

  bursts-within : ∀ {Γ A B} (ρ : NEnv Γ) r (t : U.Node Γ A) st → Withinˢ ρ (U.burstsˢ {B = B} r t st)
  bursts-within ρ r t (U.outˢ k _ t′) with E.inside r k
  ... | true  = tt
  ... | false = rest-within ρ t
  bursts-within ρ r t (U.skipˢ k t′) with E.inside r k
  ... | true  = tt
  ... | false = rest-within ρ t
  bursts-within ρ r t (U.endˢ _) = rest-within ρ t
  bursts-within ρ r t U.hushˢ    = rest-within ρ t

-- A source's step showing `a` at `q`, its next node `s′`.
showsˢ : ∀ {Γ A} → Pos → Maybe A → U.Node Γ A → U.Step Γ A
showsˢ q (just a) s′ = U.outˢ q a s′
showsˢ q nothing  s′ = U.skipˢ q s′

-- The body stepped first, its source carried.
body-within : ∀ {Γ A B} r (s : U.Node Γ A) (ρ : NEnv Γ) (sb : U.Step (A ∷ Γ) B)
            → Placedˢ (U.meaning s ρ ∷ᴬ ρ) sb → Placed s ρ → ApartNext r sb s ρ → Withinˢ ρ (U.bodyˢ r (U.live s) sb)
body-within r s ρ (U.outˢ k a b′) (_ , pb) ps sd = pb , ps , sd
body-within r s ρ (U.skipˢ k b′)  (_ , pb) ps sd = pb , ps , sd
body-within r s ρ (U.endˢ k)      _        ps sd = tt
body-within r s ρ U.hushˢ         _        ps sd = tt

-- A source's step, read off its skips.
forward : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {s : U.Node Γ A} {ρ : NEnv Γ} {t} → U.step s ≡ t → Skips ν s ρ
        → Clear ν (U.headˢ t) ρ → U.meaning s ρ ≃ afterᴱ ρ t
forward refl sk = sk

shown-alike : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (s s′ : U.Node Γ A) (ρ : NEnv Γ) q (a : Maybe A) → Skips ν s ρ
            → U.step s ≡ showsˢ q a s′ → Clear ν (just q) ρ → U.meaning s ρ ≃ shows q a (U.stateᴺ s′ ρ)
shown-alike {ν = ν} s s′ ρ q (just x) sk es cl = forward {ν = ν} {s = s} {ρ = ρ} es sk cl
shown-alike {ν = ν} s s′ ρ q nothing  sk es cl = forward {ν = ν} {s = s} {ρ = ρ} es sk cl

-- A body fed its source's step, shown first, is placed in the source's
-- next meaning.
fed-placed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s s′ : U.Node Γ A) (ρ : NEnv Γ) q (a : Maybe A)
           → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ → U.step s ≡ showsˢ q a s′
           → U.beforeˢ (q ++ [ ix 0 ]) (U.step b) ≡ true → Clear ν (just (q ++ [ ix 0 ])) ρ
           → Placed (U.feed (here refl) q a b) (U.meaning s′ ρ ∷ᴬ ρ)
fed-placed {ν = ν} r b s s′ ρ q a (sb , ss) pl es fb cl =
  placed-fed (here refl) q a b sb refl (fed-here (U.stateᴺ s′ ρ) al (λ m → nagree-refl m ρ)) (proj₁ (proj₂ pl))
  where al = shown-alike {ν = ν} s s′ ρ q a (skips {ν = ν} s ρ ss (proj₁ (proj₂ (proj₂ pl)))) es (clear-lower ν ρ (<ᵖ-below q []) cl)

-- A body told its source's end, shown first, is placed past it.
shut-placed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ) c
            → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ → U.step s ≡ U.endˢ c
            → U.beforeˢ (c ++ [ ix 0 ]) (U.step b) ≡ true → Clear ν (just (c ++ [ ix 0 ])) ρ
            → Placed (U.shut (here refl) c b) (end c ∷ᴬ ρ)
shut-placed {ν = ν} r b s ρ c (sb , ss) pl es fb cl =
  placed-shut (here refl) c b al (same-cons (agreeing al) (λ m → nagree-refl m ρ)) (proj₁ (proj₂ pl))
  where al = forward {ν = ν} {s = s} {ρ = ρ} es (skips {ν = ν} s ρ ss (proj₁ (proj₂ (proj₂ pl)))) (clear-lower ν ρ (<ᵖ-below c []) cl)

-- A body placed past its source's end is placed told it again.
reshut-placed : ∀ {Γ A B} c (b : U.Node (A ∷ Γ) B) (ρ : NEnv Γ) → Placed b (end c ∷ᴬ ρ) → Placed (U.shut (here refl) c b) (end c ∷ᴬ ρ)
reshut-placed c b ρ pb = placed-shut (here refl) c b (alike λ d → agree-refl d _) (λ m → nagree-refl m (end c ∷ᴬ ρ)) pb

-- An ended connect's body stepped first, told its source's end.
shut-within : ∀ {Γ A B} r c (t : U.Node Γ A) (ρ : NEnv Γ) (sb : U.Step (A ∷ Γ) B) → Placedˢ (end c ∷ᴬ ρ) sb → Withinˢ ρ (U.shutˢᵗ r c t sb)
shut-within r c t ρ (U.outˢ k a b′) (_ , pb) = reshut-placed c b′ ρ pb
shut-within r c t ρ (U.skipˢ k b′)  (_ , pb) = reshut-placed c b′ ρ pb
shut-within r c t ρ (U.endˢ k)      _        = tt
shut-within r c t ρ U.hushˢ         _        = tt

-- WHAT A STEP LEAVES IS PLACED WITHIN, when its sources are clear of it.
mutual
  withins : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ
          → Clear ν (U.headˢ (U.step c)) ρ → Withinˢ ρ (U.step c)
  withins (U.framesᶜ τ e m)  ρ _ _ _ = frames-within ρ τ e m
  withins (U.burstᶜ τ r i b) ρ _ _ _ = burst-within ρ τ r i b
  withins (U.ofᶜ p i xs)     ρ _ _ _ = of-within ρ p i xs
  withins {ν = ν} (U.mapᶜ f c) ρ sn (_ , pl) cl =
    map-within ρ f (U.step c) (placeds c ρ sn pl (subst (λ h → Clear ν h ρ) (head-map f (U.step c)) cl))
  withins {ν = ν} (U.scanᶜ f z c) ρ sn (_ , pl) cl =
    scan-within ρ f z (U.step c) (placeds c ρ sn pl (subst (λ h → Clear ν h ρ) (head-scan f z (U.step c)) cl))
  withins {ν = ν} (U.takeWhileᶜ i p c) ρ sn (_ , pl) cl =
    take-within ρ i p (U.step c) (placeds c ρ sn pl (clear-take {ν = ν} {ρ = ρ} i p (U.step c) cl))
  withins (U.flatMapᶜ op g o ls qs pl) ρ sn pd cl = flat-within op g o ls qs pl ρ sn pd cl
  withins (U.joinᶜ i p xs e) ρ _ (_ , w) _ = join-within ρ i p xs e w
  withins (U.connectᶜ r b (U.live s))    ρ sn pd cl = connect-within r b s ρ sn pd cl
  withins (U.connectᶜ r b (U.ended c t)) ρ sn pd cl = ended-within r b c t ρ sn pd cl
  withins (U.deferᶜ l p ns)  ρ _ pd _ = defer-within l p ns ρ pd
  withins (U.endingᶜ p n)    ρ _ _ _  = tt
  withins (U.restᶜ n)        ρ _ _ _  = rest-within ρ n
  withins U.idleᶜ            ρ _ _ _  = tt
  withins (U.unionᶜ x y)     ρ _ _ _  = union-within ρ x (U.restˢ x) y (U.restˢ y) (rest-within ρ y)
  withins (U.burstingᶜ r t)  ρ _ _ _  = bursts-within ρ r t (U.step t)
  withins (U.underᶜ {C = C} s b) ρ _ _ _ = under-within ρ s (U.restˢ {B = C} b)

  -- A connect: the source's step first, the body fed or told it; else
  -- the body's, the source carried.
  connect-within : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
                 → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ
                 → Clear ν (U.headˢ (U.step (U.connectᶜ r b (U.live s)))) ρ → Withinˢ ρ (U.step (U.connectᶜ r b (U.live s)))
  connect-within {ν = ν} r b s ρ sn@(sb , ss) pl cl with U.step s in es
  ... | U.outˢ q a s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
  ...   | true  = fed-placed r b s s′ ρ q (just a) sn pl es fb cl , proj₂ (source-next r b s ρ sn pl es (clear-lower ν ρ (<ᵖ-below q []) cl))
                , subst (λ t → ApartFed r b t ρ) es (apart-fed r b s ρ (proj₂ (proj₂ (proj₂ pl))))
  ...   | false = body-first r b s ρ sn pl (subst (Shy (U.step b)) (sym es) fb) cl
  connect-within {ν = ν} r b s ρ sn@(sb , ss) pl cl | U.skipˢ q s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
  ...   | true  = fed-placed r b s s′ ρ q nothing sn pl es fb cl , proj₂ (source-next r b s ρ sn pl es (clear-lower ν ρ (<ᵖ-below q []) cl))
                , subst (λ t → ApartFed r b t ρ) es (apart-fed r b s ρ (proj₂ (proj₂ (proj₂ pl))))
  ...   | false = body-first r b s ρ sn pl (subst (Shy (U.step b)) (sym es) fb) cl
  connect-within {ν = ν} r b s ρ sn@(sb , ss) pl cl | U.endˢ c with U.beforeˢ (c ++ [ ix 0 ]) (U.step b) in fb
  ...   | true  = shut-placed r b s ρ c sn pl es fb cl
  ...   | false = body-first r b s ρ sn pl (subst (Shy (U.step b)) (sym es) fb) cl
  connect-within {ν = ν} r b s ρ sn@(sb , ss) pl cl | U.hushˢ = body-first r b s ρ sn pl (subst (Shy (U.step b)) (sym es) tt) cl

  -- The source's next node, placed.
  source-next : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
              → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ
              → ∀ {t} → U.step s ≡ t → Clear ν (U.headˢ t) ρ → Placedˢ ρ t
  source-next r b s ρ (_ , ss) (_ , _ , ps , _) refl cl = placeds s ρ ss ps cl

  body-first : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
             → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ
             → Shy (U.step b) (U.step s) → Clear ν (U.headˢ (U.bodyˢ r (U.live s) (U.step b))) ρ
             → Withinˢ ρ (U.bodyˢ r (U.live s) (U.step b))
  body-first {ν = ν} r b s ρ sn@(sb , ss) pl@(_ , pb , ps , sd) shy cl =
    body-within r s ρ (U.step b) (placeds b (U.meaning s ρ ∷ᴬ ρ) sb pb (ce , cl′)) ps (apart-next r b s ρ sd)
    where cl′ = subst (λ h → Clear ν h ρ) (head-body r (U.live s) (U.step b)) cl
          ce  = shy-clear b s ρ ss ps (apart-sides r b s ρ sd) (skips s ρ ss ps) shy cl′

  -- An ended connect: its rest's skip first, else the body's, told the end.
  ended-within : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) c t (ρ : NEnv Γ)
               → Sane ν (U.connectᶜ r b (U.ended c t)) → Placed (U.connectᶜ r b (U.ended c t)) ρ
               → Clear ν (U.headˢ (U.step (U.connectᶜ r b (U.ended c t)))) ρ → Withinˢ ρ (U.step (U.connectᶜ r b (U.ended c t)))
  ended-within r b c t ρ (sb , _) (_ , pb) cl with U.step t
  ... | U.skipˢ k t′ with U.beforeˢ (k ++ [ ix 0 ]) (U.step b)
  ...   | true  = pb
  ...   | false = reshut r b c t ρ sb pb cl
  ended-within r b c t ρ (sb , _) (_ , pb) cl | U.outˢ k a t′ = reshut r b c t ρ sb pb cl
  ended-within r b c t ρ (sb , _) (_ , pb) cl | U.endˢ k      = reshut r b c t ρ sb pb cl
  ended-within r b c t ρ (sb , _) (_ , pb) cl | U.hushˢ       = reshut r b c t ρ sb pb cl

  reshut : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) c (t : U.Node Γ A) (ρ : NEnv Γ)
         → Sane (over ∷ᴬ ν) b → Placed b (end c ∷ᴬ ρ) → Clear ν (U.headˢ (U.shutˢᵗ r c t (U.step b))) ρ
         → Withinˢ ρ (U.shutˢᵗ r c t (U.step b))
  reshut {ν = ν} r b c t ρ sb pb cl =
    shut-within r c t ρ (U.step b) (placeds b (end c ∷ᴬ ρ) sb pb (subst (λ h → Clear ν h ρ) (head-shut r c t (U.step b)) cl))

  placeds : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ
          → Clear ν (U.headˢ (U.step c)) ρ → Placedˢ ρ (U.step c)
  placeds c ρ sn pl cl = placed-step ρ (U.step c) (skips c ρ sn pl cl) (proj₁ pl) (withins c ρ sn pl cl)

-- What a sane, placed ghost's step leaves holds its parts placed: at the
-- root no source is in scope.
within-step : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Withinˢ []ᴬ (U.step g)
within-step g sn pl = withins g []ᴬ sn pl tt

-- A STEP KEEPS THE GHOST PLACED: atop what the step shows.
placed-after : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Placedˢ []ᴬ (U.step g)
placed-after g sn pl = placed-step []ᴬ (U.step g) (step-skips g sn pl) (proj₁ pl) (within-step g sn pl)
