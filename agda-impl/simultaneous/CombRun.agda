{-# OPTIONS --guardedness #-}

-- WHAT THE SCANNED STREAM MEETS, READ BACK AS WHAT ITS SOURCE MEETS, row
-- for row and position for position, for a source read at any
-- subscription: a scan keeps its source's positions, and an each lays a
-- value's list beneath it, lane by lane.
module simultaneous.CombRun where

open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Properties using (++-conicalʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Tree using (Obs; mergeᶠ; scan)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; out; end; skip; pin; enter; ⟦_⟧; Den; module Op; DenEnv; Few; module Scan)
open import denotation.Laws.Modulus using (entered-few)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Worlds using (InvAt; GoodEnv; Ok; Hots; ⊕-assoc)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Layers using (run-row; snoc-view; scanRows; laneRows; eachRows; module ScanLayer; module EachLayer; run-past-end)
open import simultaneous.Prefixes using (prefix-ext)
open import simultaneous.Reach using (module Reached)
open import simultaneous.HeldComb using (ev; init; outRows; lay)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.ScanAcc using (module AccRun)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Out; Input; react; each)

-- AN EACH OF A SOURCE READ ANYWHERE: a run met of it is a prefix of what
-- a run met of the source lays out, the one reaching the source row its
-- last row hangs under, which is found classically.
module EachOpen {X Y : Set} (f : X → List Y) (d : Den X) (P : Pos) {H : Pos → Set} (IS : InvAt H P (enter d P))
               (fuE : ∀ {y e e′} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (f x)) d) P y e
                    → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (f x)) d) P y e′ → e ≡ e′) where
  open EachLayer f d P IS using (E; S; vis; vis-anc; found)
  open Reached d P IS using (reach)

  each-out : ∀ {rs} → Met E rs → ¬ ¬ Σ _ λ sc → Met S sc × Σ _ λ ext → rs ++ ext ≡ eachRows f sc
  each-out {rs} m no with snoc-view rs
  ... | inj₁ refl = no ([] , [] , [] , refl)
  ... | inj₂ (ys , (k , e) , refl) with run-row m (∈-++⁺ʳ ys (here refl))
  ...   | kE , vi with vis kE vi
  ...     | q , v with vis-anc v
  ...       | e₀ , x₀ , vi₀ = reach x₀ vi₀ λ (rs″ , mS) →
    let (_ , _ , longer , _ , eqr) = found fuE m v rs″ mS in
    no (rs″ ++ [ (q , e₀) ] , mS , proj₁ (prefix-ext longer) , trans (sym (proj₂ (prefix-ext longer))) eqr)

------------------------------------------------------------------------
-- The scanned stream

lane-lay : ∀ {B} q i (xs : List (IE B)) → laneRows q i xs ≡ lay q i xs
lane-lay q i []       = refl
lane-lay q i (x ∷ xs) = cong₂ (λ y ys → (y , out x) ∷ ys) (⊕-assoc q [ ix 1 ] [ ix i ]) (lane-lay q (suc i) xs)

-- The each of the scan lays out what the combiner's steps output.
each-scan : ∀ {B} op (o : Out B) rx → eachRows proj₂ (scanRows (react op) o rx) ≡ outRows op o rx
each-scan op o []                  = refl
each-scan op o ((q , out x) ∷ rx)  = cong₂ _++_ (lane-lay q 0 (proj₂ (react op o x))) (each-scan op (react op o x) rx)
each-scan op o ((q , end) ∷ rx)    = refl
each-scan op o ((q , skip) ∷ rx)   = each-scan op o rx
each-scan op o ((q , pin _) ∷ rx)  = each-scan op o rx

-- A SCAN'S ROWS UP TO A VALUE are those before it and the value's fold.
scan-snoc : ∀ {A B} (f : B → A → B) b {t : EmissionSet A} {c} rx {q a} → Run t c (rx ++ [ (q , out a) ])
          → scanRows f b (rx ++ [ (q , out a) ]) ≡ scanRows f b rx ++ [ (q , out (f (L.foldl f b (values rx)) a)) ]
scan-snoc f b []                  _         = refl
scan-snoc f b ((y , out a′) ∷ rx) (_ ∷ run) = cong ((y , out (f b a′)) ∷_) (scan-snoc f (f b a′) rx run)
scan-snoc f b ((y , end) ∷ rx) ((((x , _) , _) , _) ∷ run) with ++-conicalʳ rx _ (run-past-end x run)
... | ()
scan-snoc f b ((y , skip) ∷ rx)   ((_ , () , _) ∷ _)
scan-snoc f b ((y , pin _) ∷ rx)  ((_ , () , _) ∷ _)

-- THE SCANNED STREAM, NOT ENDED, READ BACK CONSTRUCTIVELY: its last row
-- hangs under a value of the scan, whose fold is a chain of the source's
-- values back to its first, and that chain is the run.
module CombLive {B} op (d : Den (Maybe (Input B))) P {H H′ : Pos → Set}
                (IS : InvAt H P (enter d P)) (ISc : InvAt H′ P (enter (Op.scan (react op) init d) P))
                (fuE : ∀ {y e e′} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) init d)) P y e
                                  → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) init d)) P y e′ → e ≡ e′) where
  open EachLayer proj₂ (Op.scan (react op) init d) P ISc using (E; vis; found; vlane; vend)

  few : ∀ {q e} → enter d P q e → Visible e → Few (enter d P) q
  few {e = out _} x _ = entered-few d P tt x
  few {e = end}   x _ = entered-few d P tt x

  open AccRun (react op) init IS few using (acc-run)

  open Scan (react op) init (enter d P) using (Acc; sval)

  acc-of : ∀ {q b} → enter (Op.scan (react op) init d) P q (out b) → Acc q b
  acc-of (sval ac , _) = ac

  comb-live : ∀ {rs} → Met E rs → (∀ {c} → (c , end) ∈ rs → ⊥)
            → Σ _ λ rx → Met (enter d P) rx × Σ _ λ ext → rs ++ ext ≡ outRows op init rx
  comb-live {rs} m ne with snoc-view rs
  ... | inj₁ refl = [] , [] , [] , refl
  ... | inj₂ (ys , (k , e) , refl) with run-row m (∈-++⁺ʳ ys (here refl))
  ...   | kE , vi with vis kE vi
  ...     | _ , vend _ = ⊥-elim (ne (∈-++⁺ʳ ys (here refl)))
  ...     | q , v@(vlane x _) with acc-run (acc-of x)
  ...       | rx , a , _ , run , _ =
    let sc-eq = scan-snoc (react op) init rx run
        (_ , msc , _ , _ , eqsc) = ScanLayer.in-go (react op) init d P (InvAt.func IS) ScanLayer.none run
        (_ , _ , longer , _ , eqr) = found fuE m v (scanRows (react op) init rx) (subst (Met (enter (Op.scan (react op) init d) P)) (trans eqsc sc-eq) msc)
    in rx ++ [ (q , out a) ] , run , proj₁ (prefix-ext longer) ,
       trans (sym (proj₂ (prefix-ext longer)))
         (trans eqr (trans (cong (eachRows proj₂) (sym sc-eq)) (each-scan op init (rx ++ [ (q , out a) ]))))

comb-gen : ∀ {B} op (d : Den (Maybe (Input B))) P {H H′ : Pos → Set}
         → InvAt H P (enter d P) → InvAt H′ P (enter (Op.scan (react op) init d) P)
         → (∀ {y e e′} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) init d)) P y e
                       → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) init d)) P y e′ → e ≡ e′)
         → ∀ {rs} → Met (enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) init d)) P) rs
         → ¬ ¬ Σ _ λ rx → Met (enter d P) rx × Σ _ λ ext → rs ++ ext ≡ outRows op init rx
comb-gen op d P IS ISc fuE mt no = EachOpen.each-out proj₂ (Op.scan (react op) init d) P ISc fuE mt λ (sc , ms , ext , eq) →
  let (rx , mx , _ , _ , eqs) = ScanLayer.out-go (react op) init d P (InvAt.func IS) ScanLayer.none ms in
  no (rx , mx , ext , trans eq (trans (cong (eachRows proj₂) eqs) (each-scan op init rx)))

-- WHAT THE SCANNED STREAM MEETS IS LAID OUT FROM WHAT ITS SOURCE MEETS: a
-- run met of it is a prefix of what a run met of the source lays out.
-- DEAD ROUTE: the run constructed outright, for a run met to its end.  A
--   value's fold chains back through the source's values, but nothing
--   chains the source's values past the last the scan lays a row under to
--   its end; finding them decides a hot's rows, so the run is found only
--   classically, through `simultaneous.Reach`.
comb-run : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P → GoodEnv ρ → Ok (Hots ρ) P
         → ∀ {rs} → Met (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) rs
         → ¬ ¬ Σ _ λ rx → Met (enter (ev m s ρ) P) rx × Σ _ λ ext → rs ++ ext ≡ outRows op init rx
comb-run nothing op s ρ P g ok =
  comb-gen op (⟦ s ⟧ ρ) P (inv-ev nothing s ρ g P ok) (inv-ev nothing (scan (react op) init s) ρ g P ok)
    (InvAt.func (inv-ev nothing (each proj₂ (scan (react op) init s)) ρ g P ok))
comb-run (just n) op s ρ P g ok =
  comb-gen op (ev (just n) s ρ) P (inv-ev (just n) s ρ g P ok) (inv-ev (just n) (scan (react op) init s) ρ g P ok)
    (InvAt.func (inv-ev (just n) (each proj₂ (scan (react op) init s)) ρ g P ok))

-- WHAT THE SCANNED STREAM MEETS BEFORE ITS END is laid out, constructively,
-- from what its source meets.
comb-now : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P → GoodEnv ρ → Ok (Hots ρ) P
         → ∀ {rs} → Met (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) rs → (∀ {c} → (c , end) ∈ rs → ⊥)
         → Σ _ λ rx → Met (enter (ev m s ρ) P) rx × Σ _ λ ext → rs ++ ext ≡ outRows op init rx
comb-now nothing op s ρ P g ok =
  CombLive.comb-live op (⟦ s ⟧ ρ) P (inv-ev nothing s ρ g P ok) (inv-ev nothing (scan (react op) init s) ρ g P ok)
    (InvAt.func (inv-ev nothing (each proj₂ (scan (react op) init s)) ρ g P ok))
comb-now (just n) op s ρ P g ok =
  CombLive.comb-live op (ev (just n) s ρ) P (inv-ev (just n) s ρ g P ok) (inv-ev (just n) (scan (react op) init s) ρ g P ok)
    (InvAt.func (inv-ev (just n) (each proj₂ (scan (react op) init s)) ρ g P ok))
