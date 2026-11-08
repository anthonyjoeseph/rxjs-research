{-# OPTIONS --guardedness #-}

-- A PROGRAM READ THROUGH THE OPERATOR ON TOP: what a subscriber to a
-- `scan`, or to an `each` (a merge of `of`s), meets, read back as what a
-- subscriber to its source meets.  Generic in the source: nothing here
-- knows the batcher.
module simultaneous.Layers where

open import Data.List using (List; []; _∷_; concatMap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Tree using (Obs; scan)
open import denotation.Events using (Timeline; Pos; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; out; end; skip; pin; _≼_; enter; ⟦_⟧; module Scan)
open import denotation.Read using (Run; []; _∷_; Visible; After)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Worlds using (InvAt)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import denotation.Laws.Modulus using (≼-antisym; entered-reach; entered-few)
open import denotation.Laws.Fold using (fold)
open import adequacy.SubOne using (scan-reach)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met; values; Ends)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (each)

-- A closed program's emission set, subscribed at the root.
at : ∀ {A} → Obs Timeline [] A → EmissionSet A
at s = enter (⟦ s ⟧ []) root

-- The states a fold passes through, one per value.
scans : ∀ {A B : Set} → (B → A → B) → B → List A → List B
scans f z []       = []
scans f z (a ∷ as) = f z a ∷ scans f (f z a) as

-- Nothing is met past an end.
run-past-end : ∀ {A} {t : EmissionSet A} {q rs} → t q end → Run t (just q) rs → rs ≡ []
run-past-end _ []                                    = refl
run-past-end x ((((_ , prop) , _) , _ , aft , _) ∷ _) = ⊥-elim (prop x aft)

-- A SCAN IS ITS SOURCE, ROW FOR ROW: what is met of it is what is met of
-- its source, each value the fold's state, completing when it does.  A
-- value of the source has its fold, so a row least among the scan's is
-- least among the source's; the fold met is the fold of the values met,
-- for the one before a value is the value met before it.
module ScanLayer {A B : Set} (f : B → A → B) (z : B) (s : Obs Timeline [] A) where
  open Scan f z (at s) using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)

  S  = at s
  Sc = at (scan f z s)

  fu : ∀ {y e e′} → S y e → S y e′ → e ≡ e′
  fu = InvAt.func (inv-⟦⟧ s [] (λ ()) root (tt , λ ()))

  open AccF f z {S} fu using (acc-val; acc-func)

  toSc : ∀ {y e} → ScanT y e → Sc y e
  toSc x = x , scan-reach (entered-reach (⟦ s ⟧ []) root) x

  -- The fold so far, at the cursor: none before any value.
  data St : Maybe Pos → B → Set where
    none : St nothing z
    some : ∀ {q b} → Acc q b → St (just q) b

  -- What is least among the scan's rows is least among the source's.
  least-src : ∀ {c q} → (∀ {k e} → Sc k e → Visible e → After c k → q ≼ k)
            → ∀ {k e} → S k e → Visible e → After c k → q ≼ k
  least-src lst {e = out _} y _ ak kq = fold f z S (entered-few (⟦ s ⟧ []) root tt y) y λ { (_ , ac) → lst (toSc (sval ac)) tt ak kq }
  least-src lst {e = end}   y _ ak    = lst (toSc (send y)) tt ak

  least-scan : ∀ {c q} → (∀ {k e} → S k e → Visible e → After c k → q ≼ k)
             → ∀ {k e} → Sc k e → Visible e → After c k → q ≼ k
  least-scan lst (sval ac , _) _ ak = lst (proj₂ (acc-val ac)) tt ak
  least-scan lst (send y , _)  _ ak = lst y tt ak

  -- The fold met at a value is the state's, stepped by it.
  stepped : ∀ {c b q b′} → St c b → (ac : Acc q b′) → After c q → (∀ {k e} → Sc k e → Visible e → After c k → q ≼ k)
          → b′ ≡ f b (proj₁ (acc-val ac))
  stepped none (acc₀ _ _) _ _ = refl
  stepped none (acc ac′ _ lt _) _ lst = ⊥-elim (lst (toSc (sval ac′)) tt tt lt)
  stepped (some acs) (acc₀ _ mn) aft _ = ⊥-elim (mn (proj₂ (acc-val acs)) aft)
  stepped (some {q₀} acs) (acc {q₁} ac′ _ lt nx) aft lst =
    cong (λ w → f w _) (acc-func (≼-antisym {q₁} {q₀} (λ h → lst (toSc (sval ac′)) tt h lt) (λ h → nx (proj₂ (acc-val acs)) h aft)) ac′ acs)

  -- The fold at a value met, from the state.
  next : ∀ {c b q a} → St c b → S q (out a) → After c q → (∀ {k e} → S k e → Visible e → After c k → q ≼ k) → Acc q (f b a)
  next none       x _   lst = acc₀ x λ y → lst y tt tt
  next (some acs) x aft lst = acc acs x aft λ y → lst y tt

  out-go : ∀ {c b sc} → St c b → Run Sc c sc
         → Σ _ λ rx → Run S c rx × values sc ≡ scans f b (values rx) × (Ends sc → Ends rx)
  out-go st [] = [] , [] , refl , λ ()
  out-go {c} {b} st (((((sval ac , _) , prop) , _) , _ , aft , lst) ∷ run) with out-go (some ac) run
  ... | rx , run′ , eq , en =
    let ls = least-src {c} lst in
    (_ , out (proj₁ (acc-val ac))) ∷ rx ,
    (((proj₂ (acc-val ac) , λ y → prop (toSc (send y))) , entered-few (⟦ s ⟧ []) root tt (proj₂ (acc-val ac))) , tt , aft , ls) ∷ run′ ,
    cong₂ _∷_ e (trans eq (cong (λ w → scans f w (values rx)) e)) ,
    λ { (here ()) ; (there h) → there (en h) }
    where e = stepped st ac aft lst
  out-go {c} st (((((send y , r) , prop) , _) , _ , aft , lst) ∷ run) with run-past-end {t = Sc} (send y , r) run
  ... | refl =
    (_ , end) ∷ [] ,
    (((y , λ y′ → prop (toSc (send y′))) , entered-few (⟦ s ⟧ []) root tt y) , tt , aft , least-src {c} lst) ∷ [] ,
    refl , λ _ → here refl
  out-go st (((((sstep _ , _) , _) , _) , () , _) ∷ _)
  out-go st (((((spin _ , _) , _) , _) , () , _) ∷ _)

  in-go : ∀ {c b rx} → St c b → Run S c rx
        → Σ _ λ sc → Run Sc c sc × values sc ≡ scans f b (values rx) × (Ends rx → Ends sc)
  in-go st [] = [] , [] , refl , λ ()
  in-go {c} {b} st (_∷_ {e = out a} (((x , prop) , _) , _ , aft , lst) run) with in-go (some (next st x aft lst)) run
  ... | sc , run′ , eq , en =
    (_ , out (f b a)) ∷ sc ,
    (((toSc (sval ac) , λ { (send y , _) → prop y }) , entered-few (⟦ scan f z s ⟧ []) root tt (toSc (sval ac))) , tt , aft , least-scan {c} lst) ∷ run′ ,
    cong (f b a ∷_) eq ,
    λ { (here ()) ; (there h) → there (en h) }
    where ac = next st x aft lst
  in-go {c} st (_∷_ {e = end} (((x , prop) , _) , _ , aft , lst) run) with run-past-end {t = S} x run
  ... | refl =
    (_ , end) ∷ [] ,
    (((toSc (send x) , λ { (send y , _) → prop y }) , entered-few (⟦ scan f z s ⟧ []) root tt (toSc (send x))) , tt , aft , least-scan {c} lst) ∷ [] ,
    refl , λ _ → here refl
  in-go st (_∷_ {e = skip}  (_ , () , _) _)
  in-go st (_∷_ {e = pin _} (_ , () , _) _)

scan-out : ∀ {A B} (f : B → A → B) z (s : Obs Timeline [] A) {sc} → Met (at (scan f z s)) sc
         → Σ _ λ rx → Met (at s) rx × values sc ≡ scans f z (values rx) × (Ends sc → Ends rx)
scan-out f z s = ScanLayer.out-go f z s (ScanLayer.none)

scan-in : ∀ {A B} (f : B → A → B) z (s : Obs Timeline [] A) {rx} → Met (at s) rx
        → Σ _ λ sc → Met (at (scan f z s)) sc × values sc ≡ scans f z (values rx) × (Ends rx → Ends sc)
scan-in f z s = ScanLayer.in-go f z s (ScanLayer.none)

-- AN EACH IS ITS SOURCE'S LANES IN TURN: what is met of it lies within
-- every lane of what is met of its source, and is all of them once it
-- completes; every lane of what is met of the source is met of it.
postulate
  each-out : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {rs} → Met (at (each f s)) rs
           → Σ _ λ sc → Met (at s) sc × Prefix _≡_ (values rs) (concatMap f (values sc))
                      × (Ends rs → Ends sc × values rs ≡ concatMap f (values sc))
  each-in  : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {sc} → Met (at s) sc
           → Σ _ λ rs → Met (at (each f s)) rs × values rs ≡ concatMap f (values sc) × (Ends sc → Ends rs)
