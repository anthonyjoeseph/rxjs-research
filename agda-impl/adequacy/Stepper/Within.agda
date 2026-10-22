{-# OPTIONS --guardedness #-}

-- A STEP KEEPS THE GHOST PLACED: what a node's step leaves is placed
-- within, at any scope whose sources are clear of the step, node by
-- node as the step runs each part.
module adequacy.Stepper.Within where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using ([_,_]; inj₁)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (_<ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (Later)
import Tree as T
open import Data.List.Membership.Propositional using (_∈_)
open import denotation.MonotonicList.Events using (Timeline; From; Frame)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Events; Events∞; end; out; skip; Pos; ix; _<ᵖ_; <ᵖ-below)
open import denotation.NonExpansive using (Agreeˢ)
open import adequacy.Stepper.Past using (Clear; Placedˢ; Shy; Skips; Withinˢ; _≃_; afterᴱ; alike; clear-lower; head-map; head-scan; placed-step; shows)
open import adequacy.Stepper.Fed using (placed-fed; placed-feeds; placed-shut)
open import adequacy.Env using (nagree-refl; reaches-agree; same-cons)
open import adequacy.Stepper.Parts using (clear-take; fed-here; head-body; head-shut)

open Agreeˢ using (nowˢ)
open import adequacy.Stepper using (skips; shy-clear; step-skips)
import denotation.MonotonicList as M′
open import denotation.MonotonicList using (agree-refl; agree-sym)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Saneᴸ; Saneᴹ; Mode; over; running-all; sane-subscribe)
open import adequacy.Placed using (placed-sub)
open import adequacy.Placed.Keys using (alienᴱ-owned)
open import adequacy.Placed.Order using (headed-snoc; prefix-++; Placed; Placedᴸ; Placedᴹ; Reaches; Within; out-there; skip-here; skip-there)
open import adequacy.Placed.Heads using (ApartFed; ApartNext; apart-fed; apart-next; apart-sides)
open import adequacy.Deep using (Deep; Deepˢ)

open _≃_
open Events∞

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

-- What a step past a meaning reaches, the meaning reaches.
skipped : ∀ {C} {M : Events C} {x k} {σ : Events∞ C} → M ≃ skip k σ → Reaches x (force σ) → Reaches x M
skipped H r = reaches-agree (λ m → agree-sym (agreeing H m)) (skip-there r)

outed : ∀ {C} {M : Events C} {x k a} {σ : Events∞ C} → M ≃ out k a σ → Reaches x (force σ) → Reaches x M
outed H r = reaches-agree (λ m → agree-sym (agreeing H m)) (out-there r)

landed : ∀ {C} {M : Events C} {k} {σ : Events∞ C} → M ≃ skip k σ → Reaches k M
landed H = reaches-agree (λ m → agree-sym (agreeing H m)) skip-here

-- A part placed, with what its step leaves placed once its sources are
-- clear of the step.
module _ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) where
  Stepped : ∀ {C} → U.Node Γ C → U.Step Γ C → Set
  Stepped c s = Placed c ρ × (Clear ν (U.headˢ s) ρ → Placedˢ ρ s)

  OuterP : ∀ {C} → U.Outer Γ C → Set
  OuterP U.doneᵒ       = ⊤
  OuterP (U.runᵒ o so) = Stepped o so

  EarliestP : ∀ {C} → U.Earliest Γ C → Set
  EarliestP U.none                 = ⊤
  EarliestP (U.found k bs l s as) = Placedᴸ bs ρ × Stepped l s × Placedᴸ as ρ

  outer-node : ∀ {C} (o : U.Outer Γ C) → OuterP o → Placedᴹ (U.nodeᵒ o) ρ
  outer-node U.doneᵒ       _        = tt
  outer-node (U.runᵒ o so) (po , _) = po

  placedᴸ-++ : ∀ {C} (bs as : List (U.Node Γ C)) → Placedᴸ bs ρ → Placedᴸ as ρ → Placedᴸ (bs ++ as) ρ
  placedᴸ-++ []       as _          pas = pas
  placedᴸ-++ (b ∷ bs) as (pb , pbs) pas = pb , placedᴸ-++ bs as pbs pas

  pick-placed : ∀ {C} (l : U.Node Γ C) s ls → Stepped l s → Placedᴸ ls ρ → ∀ h (e : U.Earliest Γ C) → EarliestP e
              → EarliestP (U.pick l s ls h e)
  pick-placed l s ls sl pls nothing  U.none                _                  = tt
  pick-placed l s ls sl pls nothing  (U.found k bs c sc as) (pbs , sc′ , pas) = (proj₁ sl , pbs) , sc′ , pas
  pick-placed l s ls sl pls (just k) U.none                _                  = tt , sl , pls
  pick-placed l s ls sl pls (just k) (U.found k′ bs c sc as) (pbs , sc′ , pas) with k <ᵖ k′
  ... | true  = tt , sl , pls
  ... | false = (proj₁ sl , pbs) , sc′ , pas

  -- The lanes an arrival leaves, the arrival placed.
  admit-placed : ∀ {A B} op (g : A → Pos → U.Node Γ B) q a ls qs d → Placed (g a q) ρ → Placedᴸ ls ρ
               → Placedᴸ (proj₁ (U.admit op g q a ls qs d)) ρ
  admit-placed (T.mergeᶠ nothing)  g q a ls       qs d pg pls = pg , pls
  admit-placed (T.mergeᶠ (just n)) g q a ls       qs d pg pls with length ls <ᵇ n
  ... | true  = pg , pls
  ... | false = pls
  admit-placed T.switchᶠ           g q a ls       qs d pg pls = pg , tt
  admit-placed T.exhaustᶠ          g q a []       qs d pg pls = pg , tt
  admit-placed T.exhaustᶠ          g q a (l ∷ ls) qs d pg pls = pls

-- A FLATMAP'S STEP, PART BY PART: the part it steps leaves itself
-- placed, the others are as they were, and each lane it admits is one
-- its meaning reaches the admission of.
module _ {Γ A B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (op : T.FlatOp) (g : A → Pos → U.Node Γ B) {M : Events B}
         (G : ∀ a x → Reaches (x ++ [ ix 0 ]) M → Placed (g a (x ++ [ ix 1 ])) ρ) where

  outer-w : ∀ (o : U.Node Γ A) so ls qs p → Stepped ν ρ o so → Placedᴸ ls ρ → M ≃ afterᴱ ρ (U.outerˢ op g o so ls qs p)
          → Clear ν (U.headˢ (U.outerˢ op g o so ls qs p)) ρ → Withinˢ ρ (U.outerˢ op g o so ls qs p)
  outer-w o (U.outˢ q a o′) ls qs p (_ , qo) pls H cl =
    proj₂ (qo (clear-lower ν ρ (<ᵖ-below q []) cl)) , admit-placed ν ρ op g (q ++ [ ix 1 ]) a ls qs (U.restsᶜ ls) (G a q (landed H)) pls , λ a′ x r → G a′ x (skipped H r)
  outer-w o (U.skipˢ q o′) ls       qs       p (_ , qo) pls H cl = proj₂ (qo cl) , pls , λ a x r → G a x (skipped H r)
  outer-w o (U.endˢ c)     []       []       p _ _   H cl = tt
  outer-w o (U.endˢ c)     []       (y ∷ qs) p _ pls H cl = tt , pls , λ a x r → G a x (skipped H r)
  outer-w o (U.endˢ c)     (l ∷ ls) qs       p _ pls H cl = tt , pls , λ a x r → G a x (skipped H r)
  outer-w o U.hushˢ        ls       qs       p _ _   H cl = tt

  lane-w : ∀ (o : Maybe (U.Node Γ A)) bs (l : U.Node Γ B) s as qs p → Placedᴹ o ρ → Placedᴸ bs ρ → Stepped ν ρ l s → Placedᴸ as ρ
         → M ≃ afterᴱ ρ (U.laneˢ op g o bs l s as qs p) → Clear ν (U.headˢ (U.laneˢ op g o bs l s as qs p)) ρ
         → Withinˢ ρ (U.laneˢ op g o bs l s as qs p)
  lane-w o bs l (U.outˢ k b c) as qs p po pbs (_ , ql) pas H cl =
    po , placedᴸ-++ ν ρ bs (c ∷ as) pbs (proj₂ (ql cl) , pas) , λ a x r → G a x (outed H r)
  lane-w o bs l (U.skipˢ k c)  as qs p po pbs (_ , ql) pas H cl =
    po , placedᴸ-++ ν ρ bs (c ∷ as) pbs (proj₂ (ql cl) , pas) , λ a x r → G a x (skipped H r)
  lane-w o bs l (U.endˢ c) as (a ∷ qs) p po pbs _ pas H cl =
    po , (G a c (landed H) , placedᴸ-++ ν ρ bs as pbs pas) , λ a′ x r → G a′ x (skipped H r)
  lane-w nothing  []       l (U.endˢ c) []       [] p _  _   _ _   H cl = tt
  lane-w nothing  []       l (U.endˢ c) (y ∷ as) [] p po pbs _ pas H cl = po , pas , λ a x r → G a x (skipped H r)
  lane-w nothing  (b ∷ bs) l (U.endˢ c) as       [] p po pbs _ pas H cl =
    po , placedᴸ-++ ν ρ (b ∷ bs) as pbs pas , λ a x r → G a x (skipped H r)
  lane-w (just o) bs       l (U.endˢ c) as       [] p po pbs _ pas H cl =
    po , placedᴸ-++ ν ρ bs as pbs pas , λ a x r → G a x (skipped H r)
  lane-w o bs l U.hushˢ as qs p _ _ _ _ H cl = tt

  race-w : ∀ (o : U.Node Γ A) so h k bs l s as qs p → Stepped ν ρ o so → Placedᴸ bs ρ → Stepped ν ρ l s → Placedᴸ as ρ
         → M ≃ afterᴱ ρ (U.raceˢ op g o so h k bs l s as qs p) → Clear ν (U.headˢ (U.raceˢ op g o so h k bs l s as qs p)) ρ
         → Withinˢ ρ (U.raceˢ op g o so h k bs l s as qs p)
  race-w o so nothing   k bs l s as qs p so′ pbs sl pas H cl = lane-w (just o) bs l s as qs p (proj₁ so′) pbs sl pas H cl
  race-w o so (just k′) k bs l s as qs p so′ pbs sl pas H cl with k′ <ᵖ k
  ... | true  = outer-w o so (bs ++ l ∷ as) qs p so′ (placedᴸ-++ ν ρ bs (l ∷ as) pbs (proj₁ sl , pas)) H cl
  ... | false = lane-w (just o) bs l s as qs p (proj₁ so′) pbs sl pas H cl

  go-w : ∀ (o : U.Outer Γ A) ls qs p e → OuterP ν ρ o → Placedᴸ ls ρ → EarliestP ν ρ e
       → M ≃ afterᴱ ρ (U.goˢ op g o ls qs p e) → Clear ν (U.headˢ (U.goˢ op g o ls qs p e)) ρ → Withinˢ ρ (U.goˢ op g o ls qs p e)
  go-w U.doneᵒ       ls qs p U.none                _  _   _                 H cl = tt
  go-w (U.runᵒ o so) ls qs p U.none                po pls _                 H cl = outer-w o so ls qs p po pls H cl
  go-w U.doneᵒ       ls qs p (U.found k bs l s as) _  _   (pbs , sl , pas) H cl = lane-w nothing bs l s as qs p tt pbs sl pas H cl
  go-w (U.runᵒ o so) ls qs p (U.found k bs l s as) po _   (pbs , sl , pas) H cl =
    race-w o so (U.headˢ so) k bs l s as qs p po pbs sl pas H cl

  flat-w : ∀ (o : U.Outer Γ A) ls qs p sp e → OuterP ν ρ o → Placedᴸ ls ρ → EarliestP ν ρ e
         → M ≃ afterᴱ ρ (U.flatˢ op g o ls qs p sp e) → Clear ν (U.headˢ (U.flatˢ op g o ls qs p sp e)) ρ
         → Withinˢ ρ (U.flatˢ op g o ls qs p sp e)
  flat-w o ls qs p (U.skipˢ k p′) e po pls pe H cl with U.aheadˢ k o e
  ... | true  = outer-node ν ρ o po , pls , λ a x r → G a x (skipped H r)
  ... | false = go-w o ls qs p e po pls pe H cl
  flat-w o ls qs p (U.outˢ k b p′) e po pls pe H cl = go-w o ls qs p e po pls pe H cl
  flat-w o ls qs p (U.endˢ k)      e po pls pe H cl = go-w o ls qs p e po pls pe H cl
  flat-w o ls qs p U.hushˢ         e po pls pe H cl = go-w o ls qs p e po pls pe H cl

-- A defer's program subscribed, its notices fed, is placed.
defer-within : ∀ {Γ A} (l : Later Timeline Γ A) p ns (ρ : NEnv Γ) → Placed (U.deferᶜ l p ns) ρ → Withinˢ ρ (U.step (U.deferᶜ l p ns))
defer-within l p ns ρ (_ , hp , so , al) =
  proj₂ (placed-feeds ns (U.subscribe (Later.force l) q) ρ (sane-subscribe (Later.force l) q running-all)
          (placed-sub (Later.force l) q (U.replay ns ρ) (headed-snoc p hp) so (alienᴱ-owned p q (inj₁ (prefix-++ p [ ix 1 ])) (U.replay ns ρ) al)))
  where q = p ++ [ ix 1 ]

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
  withins {ν = ν} (U.flatMapᶜ op g o ls qs pl) ρ sn@(so , sl , _) pd@(_ , po , pls , pg) cl =
    flat-w ν ρ op g pg (U.outerOf o) ls qs pl (U.step pl) (U.earliest ls) (outers o ρ so po) pls (earliests ls ρ sl pls)
      (skips (U.flatMapᶜ op g o ls qs pl) ρ sn pd cl) cl
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

  -- The outer and each lane, placed with what its step leaves.
  outers : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴹ ν o → Placedᴹ o ρ → OuterP ν ρ (U.outerOf o)
  outers nothing  ρ _  _  = tt
  outers (just o) ρ so po = po , placeds o ρ so po

  earliests : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ B)) (ρ : NEnv Γ) → Saneᴸ ν ls → Placedᴸ ls ρ
            → EarliestP ν ρ (U.earliest ls)
  earliests []       ρ _          _          = tt
  earliests {ν = ν} (l ∷ ls) ρ (sl , sls) (pl , pls) =
    pick-placed ν ρ l (U.step l) ls (pl , placeds l ρ sl pl) pls (U.headˢ (U.step l)) (U.earliest ls) (earliests ls ρ sls pls)

  placeds : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ
          → Clear ν (U.headˢ (U.step c)) ρ → Placedˢ ρ (U.step c)
  placeds c ρ sn pl cl = placed-step ρ (U.step c) (skips c ρ sn pl cl) (proj₁ pl) (withins c ρ sn pl cl)

-- What a sane, placed ghost's step leaves holds its parts placed: at the
-- root no source is in scope.
within-step : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Withinˢ []ᴬ (U.step g)
within-step g sn pl = withins g []ᴬ sn pl tt

postulate
  -- What a sane, placed ghost in order to every depth steps to is in
  -- order to every depth: the stepped node runs what the meaning runs
  -- past the step, and a rest the step opens is a part it held.
  step-deep : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Deep g []ᴬ → Deepˢ []ᴬ (U.step g)

-- A STEP KEEPS THE GHOST PLACED: atop what the step shows.
placed-after : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Placedˢ []ᴬ (U.step g)
placed-after g sn pl = placed-step []ᴬ (U.step g) (step-skips g sn pl) (proj₁ pl) (within-step g sn pl)
