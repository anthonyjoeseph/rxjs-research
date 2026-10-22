{-# OPTIONS --guardedness #-}

-- UNDER NO STEP: the rules holding a subscription at `P₀` off every
-- position just past a step of `σ`'s run apart from `P₀`.  A frame
-- keys its burst's root, and a join its source, so both carry the
-- clearance up.
module adequacy.Placed.Under where

open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Tail∞; Timeline; end; hush; idle; ix; out; pin; skip; sub)
open import denotation.MonotonicList using (tailᴱ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Finite using (Finite)
open import adequacy.Placed.Order using (Alienᴱ; Beneath; Disjoint; Every; EveryT; Everyᴱ; Every∞; Headed; Owned; Prefix; Sorted; every; everyT-mono; everyᵀ; every-mono; every-monoᴱ; every∞-mono; headed-snoc; prefix-++)
open import adequacy.Placed.Keys using (Mark; alienᴱ-owned; beneath-owned; beneath-snoc; ix-mark; no-tick; owned-snoc; owned-tagged; owned-trans; prefix-refl; sibling; snoc-inj; tagged-mark; tagged-sub)
open import adequacy.Placed.Rising using (Rules; module Reach; apartRules; everyT-zip; keyedRules; prefix-split; tagged-split)

open Events∞
open Tail∞

-- A source's RUN: every position it shows, and past its end what it
-- leaves running, run on as its steps.  No cut before the end: a pin
-- there is a step it has yet to show.
mutual
  Runsˢ : ∀ {A} → (Pos → Set) → Events A → Tail → Set
  Runsˢ P (out h _ r) t = P h × Run P r
  Runsˢ P (skip h r)  t = P h × Run P r
  Runsˢ P (end h)     t = P h × EveryT P t
  Runsˢ P hush        t = ⊤

  Run : ∀ {A} → (Pos → Set) → Events∞ A → Set
  Run P r = Runs P (force r) (cut r)

  record Runs {A} (P : Pos → Set) (e : Events A) (t : Tail) : Set where
    coinductive
    field runs : Runsˢ P e t

open Runs public

mutual
  runs-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (e : Events A) → ∀ t → Runs P e t → Runs Q e t
  runs (runs-mono f (out h _ r) t pe) = f h (proj₁ (runs pe)) , run-mono f r (proj₂ (runs pe))
  runs (runs-mono f (skip h r)  t pe) = f h (proj₁ (runs pe)) , run-mono f r (proj₂ (runs pe))
  runs (runs-mono f (end h)     t pe) = f h (proj₁ (runs pe)) , everyT-mono f t (proj₂ (runs pe))
  runs (runs-mono f hush        t pe) = tt

  run-mono : ∀ {A} {P Q : Pos → Set} → (∀ h → P h → Q h) → (r : Events∞ A) → Run P r → Run Q r
  run-mono f r = runs-mono f (force r) (cut r)

mutual
  runs-zip : ∀ {A} {P Q : Pos → Set} (e : Events A) t → Runs P e t → Runs Q e t → Runs (λ h → P h × Q h) e t
  runs (runs-zip (out h _ r) t pe qe) = (proj₁ (runs pe) , proj₁ (runs qe)) , run-zip r (proj₂ (runs pe)) (proj₂ (runs qe))
  runs (runs-zip (skip h r)  t pe qe) = (proj₁ (runs pe) , proj₁ (runs qe)) , run-zip r (proj₂ (runs pe)) (proj₂ (runs qe))
  runs (runs-zip (end h)     t pe qe) = (proj₁ (runs pe) , proj₁ (runs qe)) , everyT-zip t (proj₂ (runs pe)) (proj₂ (runs qe))
  runs (runs-zip hush        t pe qe) = tt

  run-zip : ∀ {A} {P Q : Pos → Set} (r : Events∞ A) → Run P r → Run Q r → Run (λ h → P h × Q h) r
  run-zip r = runs-zip (force r) (cut r)

-- A run is no more than the state: every cut, not only the end's.
mutual
  every-runs : ∀ {A} {P : Pos → Set} (e : Events A) t → Every P e → EveryT P t → Runs P e t
  runs (every-runs (out h _ r) t pe pt) = proj₁ (every pe) , every-run r (proj₂ (every pe))
  runs (every-runs (skip h r)  t pe pt) = proj₁ (every pe) , every-run r (proj₂ (every pe))
  runs (every-runs (end h)     t pe pt) = every pe , pt
  runs (every-runs hush        t pe pt) = tt

  every-run : ∀ {A} {P : Pos → Set} (r : Events∞ A) → Every∞ P r → Run P r
  every-run r (pe , pt) = every-runs (force r) (cut r) pe pt

tail-runs : ∀ {A} {P : Pos → Set} t → EveryT P t → Runs {A} P (tailᴱ t) t
runs (tail-runs (pin k u) pt) = proj₁ (everyᵀ pt) , tail-runs (later u) (proj₂ (everyᵀ pt))
runs (tail-runs idle      pt) = tt

-- A source past its next step runs on within its run.
run-onward : ∀ {A} {P : Pos → Set} (σ : Events∞ A) → Run P σ → Run P (M′.onward∞ σ (force σ))
run-onward {P = P} σ u = go (force σ) u
  where
    go : ∀ e → Runs P e (cut σ) → Run P (M′.onward∞ σ e)
    go (out _ _ s) r = proj₂ (runs r)
    go (skip _ s)  r = proj₂ (runs r)
    go (end _)     r = tail-runs (cut σ) (proj₂ (runs r))
    go hush        r = u

-- Nothing at `h` lies just past `q`, when `q` stands apart from `P₀`.
Off : Pos → Pos → Pos → Set
Off P₀ h q = Disjoint P₀ q → ¬ Owned (q ++ [ ix 0 ]) h

off-snoc : ∀ P₀ j l → Mark l → Owned P₀ j → ∀ q → Off P₀ j q → Off P₀ (j ++ [ l ]) q
off-snoc P₀ j l m oj q d dq (inj₁ pr) with prefix-split (q ++ [ ix 0 ]) j l pr
... | inj₁ pr′ = d dq (inj₁ pr′)
... | inj₂ eq  = proj₁ dq (subst (Owned P₀) (sym (proj₁ (snoc-inj q j eq))) oj)
off-snoc P₀ j l m oj q d dq (inj₂ t) = d dq (inj₂ (tagged-mark (q ++ [ ix 0 ]) j l m t))

frame-off : ∀ n e q → Owned (q ++ [ ix 0 ]) (ix (suc n) ∷ sub e ∷ []) → Owned (q ++ [ ix 0 ]) e
frame-off n e q               (inj₂ (inj₁ o))       = o
frame-off n e q               (inj₂ (inj₂ ()))
frame-off n e []              (inj₁ (() , _))
frame-off n e (_ ∷ [])        (inj₁ (_ , () , _))
frame-off n e (_ ∷ _ ∷ [])    (inj₁ (_ , _ , ()))
frame-off n e (_ ∷ _ ∷ _ ∷ _) (inj₁ (_ , _ , ()))

off-join : ∀ P₀ q j q₁ → Off P₀ q q₁ × Off P₀ j q₁ → Off P₀ (q ++ [ sub j ]) q₁
off-join P₀ q j q₁ (sq , dj) dq (inj₁ pr) with prefix-split (q₁ ++ [ ix 0 ]) q (sub j) pr
... | inj₁ pr′ = sq dq (inj₁ pr′)
... | inj₂ eq with snoc-inj q₁ q eq
...   | _ , ()
off-join P₀ q j q₁ (sq , dj) dq (inj₂ t) with tagged-split (q₁ ++ [ ix 0 ]) q j t
... | inj₁ t′ = sq dq (inj₂ t′)
... | inj₂ o  = dj dq o

underRules : ∀ {A} → Pos → Events∞ A → Rules
underRules P₀ σ = record
  { S      = λ j → Owned P₀ j × Off∞ j
  ; P      = λ h → Beneath P₀ h × Off∞ h
  ; Src    = Off∞
  ; child  = λ j l m sj → owned-snoc P₀ j l (proj₁ sj) , run-mono (off-snoc P₀ j l m (proj₁ sj)) σ (proj₂ sj)
  ; deeper = λ h l m ph → beneath-snoc P₀ h l (proj₁ ph) , run-mono (off-snoc P₀ h l m (beneath-owned P₀ h (proj₁ ph))) σ (proj₂ ph)
  ; held   = λ h ph → beneath-owned P₀ h (proj₁ ph) , proj₂ ph
  ; frame  = λ n e pe _ → inj₂ (inj₁ (beneath-owned P₀ e (proj₁ pe))) , run-mono (λ q d dq o → d dq (frame-off n e q o)) σ (proj₂ pe)
  ; join   = λ q j sq sj _ → inj₂ (owned-tagged P₀ j (q ++ [ sub j ]) (proj₁ sj) (tagged-sub q j))
                           , run-mono (off-join P₀ q j) σ (run-zip σ sq (proj₂ sj))
  ; source = λ _ → proj₂
  }
  where
    Off∞ : Pos → Set
    Off∞ h = Run (Off P₀ h) σ

-- A SUBSCRIPTION KEYS NOTHING JUST PAST ITS OWN STEPS, over sources
-- sorted and alien to it: nothing it shows lies under, or is tagged
-- under, the position just past any step of its run, its run past an
-- end included.
--
-- REFUTED: 4c946ba8 over every cut, by a connect's cut pinning its source's next step, which the connect then shows just past it
-- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `alien-steps`, the same over its events alone, as a body over `Fresh`
postulate
  shown-fresh : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Every (λ k → Run (λ q → ¬ Owned (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe o p) ρ)) (U.meaning (U.subscribe o p) ρ)

-- A CONNECT'S BODY LIES UNDER NONE OF ITS SOURCE'S STEPS, over sources
-- sorted and alien to it: nothing the body shows or leaves running lies
-- under where a step of its source's run shows, past an end included.
under-shown-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
                    → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                    → Every∞ (λ k → Run (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ))
                             (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
under-shown-connect s b fs fb p ρ hp so cl =
  every∞-mono (λ k fk → run-mono (λ q d x → proj₂ d (proj₁ d) (inj₁ x)) Sᶜ (run-zip Sᶜ ks (proj₂ fk))) Bᶜ
    (Reach.reachᶠ (underRules P₀ Sᶜ) b fb P₀ ρ′ (inj₁ (prefix-refl P₀) , run-mono start Sᶜ rS) (head , tail))
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    S  = U.meaning (U.subscribe s r) ρ
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = S ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    ks : Run (Disjoint P₀) Sᶜ
    ks = every-run Sᶜ (Reach.reachᶠ (apartRules P₀ (no-tick p)) s fs r ρ (sibling p (ix-mark _) (λ ()) , sibling p (ix-mark _) (λ ()))
                         (alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl))
    rS : Run (Beneath r) Sᶜ
    rS = every-run Sᶜ (Reach.reachᶠ (keyedRules r) s fs r ρ (inj₁ (prefix-refl r)) (every-monoᴱ (λ _ _ → tt) ρ cr))
    start : ∀ q → Beneath r q → Off P₀ P₀ q
    start q _ dq o = proj₂ dq (owned-trans q (q ++ [ ix 0 ]) P₀ (inj₁ (prefix-++ q [ ix 0 ])) o)
    past : ∀ q → Beneath r q → Owned p (q ++ [ ix 0 ])
    past q bq = beneath-owned p _ (owned-snoc p q (ix 0) (owned-trans p r q (inj₁ (prefix-++ p [ ix 1 ])) (beneath-owned r q bq)))
    head : Every (λ k → Run (Off P₀ k) Sᶜ) S
    head = every-mono (λ k nk → run-mono (λ q n _ → n) Sᶜ nk) S (shown-fresh s fs r ρ (headed-snoc p hp) so cr)
    tail : Everyᴱ (λ h → Run (Off P₀ h) Sᶜ) ρ
    tail = every-monoᴱ (λ h nh → run-mono (λ q bq _ o → nh (owned-trans p (q ++ [ ix 0 ]) h (past q bq) o)) Sᶜ rS) ρ cl
