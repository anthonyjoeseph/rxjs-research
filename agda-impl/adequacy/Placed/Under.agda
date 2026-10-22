{-# OPTIONS --guardedness #-}

-- UNDER NO STEP: the rules holding a subscription at `P₀` off every
-- position just past a step of `σ` apart from `P₀`.  A frame keys its
-- burst's root, and a join its source, so both carry the clearance up.
module adequacy.Placed.Under where

open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline; ix; sub)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Finite using (Finite)
open import adequacy.Placed.Order using (Alienᴱ; Beneath; Disjoint; Every; Everyᴱ; Every∞; Headed; Owned; Prefix; Sorted; every-mono; every-monoᴱ; every∞-mono; headed-snoc; prefix-++)
open import adequacy.Placed.Keys using (Mark; alienᴱ-owned; beneath-owned; beneath-snoc; ix-mark; no-tick; owned-snoc; owned-tagged; owned-trans; prefix-refl; sibling; snoc-inj; tagged-mark; tagged-sub)
open import adequacy.Placed.Rising using (Rules; module Reach; apartRules; every∞-zip; keyedRules; prefix-split; tagged-split)

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
  ; child  = λ j l m sj → owned-snoc P₀ j l (proj₁ sj) , every∞-mono (off-snoc P₀ j l m (proj₁ sj)) σ (proj₂ sj)
  ; deeper = λ h l m ph → beneath-snoc P₀ h l (proj₁ ph) , every∞-mono (off-snoc P₀ h l m (beneath-owned P₀ h (proj₁ ph))) σ (proj₂ ph)
  ; held   = λ h ph → beneath-owned P₀ h (proj₁ ph) , proj₂ ph
  ; frame  = λ n e pe _ → inj₂ (inj₁ (beneath-owned P₀ e (proj₁ pe))) , every∞-mono (λ q d dq o → d dq (frame-off n e q o)) σ (proj₂ pe)
  ; join   = λ q j sq sj _ → inj₂ (owned-tagged P₀ j (q ++ [ sub j ]) (proj₁ sj) (tagged-sub q j))
                           , every∞-mono (off-join P₀ q j) σ (every∞-zip σ sq (proj₂ sj))
  ; source = λ _ → proj₂
  }
  where
    Off∞ : Pos → Set
    Off∞ h = Every∞ (Off P₀ h) σ

-- A SUBSCRIPTION KEYS NOTHING JUST PAST ITS OWN STEPS, over sources
-- sorted and alien to it: nothing it shows lies under, or is tagged
-- under, the position just past any of its steps, its run past an end
-- included.
--
-- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `alien-steps`, the same over its events alone, as a body over `Fresh`
postulate
  shown-fresh : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Every (λ k → Every∞ (λ q → ¬ Owned (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe o p) ρ)) (U.meaning (U.subscribe o p) ρ)

-- A CONNECT'S BODY LIES UNDER NONE OF ITS SOURCE'S STEPS, over sources
-- sorted and alien to it: nothing the body shows or leaves running lies
-- under where a source step shows, its run past an end included.
under-shown-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
                    → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                    → Every∞ (λ k → Every∞ (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ))
                             (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
under-shown-connect s b fs fb p ρ hp so cl =
  every∞-mono (λ k fk → every∞-mono (λ q d x → proj₂ d (proj₁ d) (inj₁ x)) Sᶜ (every∞-zip Sᶜ ks (proj₂ fk))) Bᶜ
    (Reach.reachᶠ (underRules P₀ Sᶜ) b fb P₀ ρ′ (inj₁ (prefix-refl P₀) , every∞-mono start Sᶜ rS) (head , tail))
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    S  = U.meaning (U.subscribe s r) ρ
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = S ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    ks : Every∞ (Disjoint P₀) Sᶜ
    ks = Reach.reachᶠ (apartRules P₀ (no-tick p)) s fs r ρ (sibling p (ix-mark _) (λ ()) , sibling p (ix-mark _) (λ ()))
           (alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl)
    rS : Every∞ (Beneath r) Sᶜ
    rS = Reach.reachᶠ (keyedRules r) s fs r ρ (inj₁ (prefix-refl r)) (every-monoᴱ (λ _ _ → tt) ρ cr)
    start : ∀ q → Beneath r q → Off P₀ P₀ q
    start q _ dq o = proj₂ dq (owned-trans q (q ++ [ ix 0 ]) P₀ (inj₁ (prefix-++ q [ ix 0 ])) o)
    past : ∀ q → Beneath r q → Owned p (q ++ [ ix 0 ])
    past q bq = beneath-owned p _ (owned-snoc p q (ix 0) (owned-trans p r q (inj₁ (prefix-++ p [ ix 1 ])) (beneath-owned r q bq)))
    head : Every (λ k → Every∞ (Off P₀ k) Sᶜ) S
    head = every-mono (λ k nk → every∞-mono (λ q n _ → n) Sᶜ nk) S (shown-fresh s fs r ρ (headed-snoc p hp) so cr)
    tail : Everyᴱ (λ h → Every∞ (Off P₀ h) Sᶜ) ρ
    tail = every-monoᴱ (λ h nh → every∞-mono (λ q bq _ o → nh (owned-trans p (q ++ [ ix 0 ]) h (past q bq) o)) Sᶜ rS) ρ cl
