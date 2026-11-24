{-# OPTIONS --guardedness #-}

-- WHAT A COUNT READS AT A ROW, carried from a source to a stream built on
-- it.  `covered` and `exact` read only the rows met up to the row they
-- judge, so each is a fact about a run met ending at that row
-- (`Counts`), and it moves along any stream whose runs are its source's
-- with rows the count passes over dropped, relabelled, or cut short past
-- a row it never judges.
module simultaneous.Counts where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; Den; out; Few) renaming (enter to enter′)
open import denotation.Read using (Run; []; _∷_)
open import denotation.Laws.Worlds using (InvAt)
open import simultaneous.InstEmit using (instEmit; mark; stop)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Idle; Carried; c-stop; cnt; nameOf; Ex)
open import simultaneous.Relabel using (ev-out; same-mark; RowsAt; cntAt; splitAt; headAt; carried-same)
open import simultaneous.HeldTake using (module TakeBack; ++-split′)
open import simultaneous.Project using (run-prefix)
open import simultaneous.Layers using (run-tail)
open import simultaneous.HeldRead using (pre-noend)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- WHAT THE COUNT READS AT A ROW, from the rows met before it: a carried
-- row not exempt finds a route of its instant, and a stop a route.
record Counts {A : Set} (t : EmissionSet (IE A)) (X : Pos → Set) : Set where
  field
    cov : ∀ r₁ {y v} → Met t (r₁ ++ [ (y , out v) ]) → Carried (out v) → ¬ X y → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    stp : ∀ r₁ {y n} → Met t (r₁ ++ [ (y , out (instEmit (mark stop) n)) ]) → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k

-- A run met up to one of its rows.
pre : ∀ {A} {t : EmissionSet A} r₁ {x} r₂ → Met t (r₁ ++ x ∷ r₂) → Met t (r₁ ++ [ x ])
pre {t = t} r₁ {x} r₂ m = run-prefix (r₁ ++ [ x ]) (subst (Met t) (sym (++-assoc r₁ [ x ] r₂)) m)

counts-held : ∀ {A} {t : EmissionSet (IE A)} {cs} → Held t cs → Counts t (Ex cs)
counts-held H = record
  { cov = λ r₁ m c nx → Held.covered H m r₁ [] refl c nx
  ; stp = λ r₁ m → Held.exact H m r₁ [] refl }

-- IDLENESS AND COUNTS ARE PROPERTIES OF THE ROWS: two sets holding the
-- same rows hold them together.
module Alike {X : Set} {t u : EmissionSet (IE X)} (to : ∀ {y e} → t y e → u y e) (from : ∀ {y e} → u y e → t y e) where

  few : ∀ {w} → Few t w → Few u w
  few (ks , h) = ks , λ x lt → h (from x) lt

  run : ∀ {c rs} → Run t c rs → Run u c rs
  run [] = []
  run ((((x , pe) , fw) , v , ac , lst) ∷ r) = (((to x , λ ce → pe (from ce)) , few fw) , v , ac , λ k v′ a → lst (from k) v′ a) ∷ run r

  idle : Idle u → Idle t
  idle iu mt ne fw aw lw = iu (run mt) ne (few fw) aw λ x v a → lw (from x) v a

  counts : ∀ {Y} → Counts u Y → Counts t Y
  counts C = record { cov = λ r₁ m → Counts.cov C r₁ (run m) ; stp = λ r₁ m → Counts.stp C r₁ (run m) }

-- A STREAM WHOSE ROWS ARE ITS SOURCE'S, MOVED, counts what its source
-- counts: the rows before are the source's, relabelled, and the row the
-- same kind of row.
counts-at : ∀ {A B : Set} {t : EmissionSet (IE A)} {t′ : EmissionSet (IE B)} {Y Y′ : Pos → Set} (R : Pos → Pos → Set)
          → (∀ {y′ y} → R y′ y → nameOf y′ ≡ nameOf y)
          → (∀ {y′ y} → R y′ y → Y y → Y′ y′)
          → (∀ {rs′} → Met t′ rs′ → Σ _ λ rs → Met t rs × RowsAt R rs′ rs)
          → Counts t Y → Counts t′ Y′
counts-at {t = t} {t′} {Y} {Y′} R nmR exR back C = record { cov = cov ; stp = stp }
  where
    cov : ∀ r₁′ {y v} → Met t′ (r₁′ ++ [ (y , out v) ]) → Carried (out v) → ¬ Y′ y → Σ ℕ λ k → cnt r₁′ ≡ (nameOf y , suc k)
    cov r₁′ m c nx with back m
    ... | rs , run , eq with splitAt eq r₁′ _ refl
    ...   | r₁ , r₂ , refl , e₁ , e₂ with headAt e₂
    ...     | _ , _ , r₂₀ , refl , r , s@(ev-out _) =
      subst₂ (λ a b → Σ ℕ λ k → a ≡ (b , suc k)) (sym (cntAt e₁)) (sym (nmR r))
        (Counts.cov C r₁ (pre r₁ r₂₀ run) (carried-same s c) λ ex → nx (exR r ex))

    stp : ∀ r₁′ {y n} → Met t′ (r₁′ ++ [ (y , out (instEmit (mark stop) n)) ]) → Σ ℕ λ k → proj₂ (cnt r₁′) ≡ suc k
    stp r₁′ m with back m
    ... | rs , run , eq with splitAt eq r₁′ _ refl
    ...   | r₁ , r₂ , refl , e₁ , e₂ with headAt e₂
    ...     | _ , _ , r₂₀ , refl , _ , ev-out (same-mark _) =
      subst (λ r → Σ _ λ k → proj₂ r ≡ _) (sym (cntAt e₁)) (Counts.stp C r₁ (pre r₁ r₂₀ run))

-- A TAKE COUNTS WHAT ITS SOURCE COUNTS, where the count carries no row it
-- fails at: its rows before the cut are its source's, and those under
-- the cut are the failing row, carried by nothing, and its end.
module TakeCounts {A : Set} {H : Pos → Set} (incl : Bool) (keep : IE A → Bool) (d : Den (IE A)) (p : Pos) (iv : InvAt H p (enter′ d p))
                  (nc : ∀ {a} → T (not (keep a)) → Carried (out a) → ⊥) where
  open TakeBack {H = H} incl keep d p iv

  -- What a take puts under its cut is never empty.
  filled : ∀ {f a tl} n → Tl f a tl → [] ≡ n ++ tl → ⊥
  filled []      (tl-v _)  ()
  filled []      (tl-ve _) ()
  filled []      tl-e      ()
  filled (_ ∷ _) _         ()

  -- The row judged lies before the cut: past it lie only the failing
  -- row, carried by nothing, and the end.
  before : ∀ r₁ {y v} → Met Tk (r₁ ++ [ (y , out v) ]) → Carried (out v) → Met S (r₁ ++ [ (y , out v) ])
  before r₁ {y} {v} m c with back c-none m
  ... | inj₁ (m′ , _) = m′
  ... | inj₂ (cut {rs₀} {tl} {f} {a} eq run fx nk nF sh _) with ++-split′ rs₀ tl r₁ (y , out v) [] (sym eq)
  ...   | inj₂ (n , _ , e) = ⊥-elim (filled n sh e)
  ...   | inj₁ (n , refl , teq) with tl-val sh (subst ((y , out v) ∈_) (sym teq) (∈-++⁺ʳ n (here refl)))
  ...     | _ , refl = ⊥-elim (nc nk c)

  counts : ∀ {Y} → Counts S Y → Counts Tk Y
  counts C = record
    { cov = λ r₁ m c nx → Counts.cov C r₁ (before r₁ m c) c nx
    ; stp = λ r₁ m → Counts.stp C r₁ (before r₁ m c-stop) }

-- AT A ROW, THE RUN MET BEFORE IT IS IDLE: its count holds no route, or
-- routes of the row's instant.
idle-row : ∀ {A} {t : EmissionSet (IE A)} → Idle t → ∀ r₁ {y v} → Met t (r₁ ++ [ (y , out v) ])
         → proj₂ (cnt r₁) ≡ 0 ⊎ proj₁ (cnt r₁) ≡ nameOf y
idle-row I r₁ m with run-tail r₁ m
... | ((_ , fw) , _ , ac , lst) ∷ [] = I (run-prefix r₁ m) (pre-noend r₁ m) fw ac lst
