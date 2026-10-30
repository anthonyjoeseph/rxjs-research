{-# OPTIONS --guardedness #-}

-- WHAT A SUBSCRIPTION ENTERS: a merge entered is the merge part way
-- through with nothing begun, read as entered.
module adequacy.Enter where

open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; [])
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Unit using (⊤; tt)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; map; scan; flatMap)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; Reach; PDep; enter; ⟦_⟧; DenEnv; MapT; map-out;
  map-skip; map-pin; map-end; module Scan; module Switch; module Exhaust; module Bounded;
  LaneOf; At; Ended)
open import denotation.Laws.Modulus using (reach-via; entered-reach)
open import adequacy.Rows using (acc-val; ∅; pendRows; Lane; reads; Kth; sub; _≃_; _⇄_; module Flat; module BoundedF; module SwitchF; module ExhaustF)
open import adequacy.Up using (trunc-≃; join-≃)
open import adequacy.Policy using (Policy; flatP; switchP; exhaustP; boundedP)

open _≃_

-- A merge with no outer rows and no lane begun: no rows.
flat-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d n → Flat.RowT L ∅ d n [] ≃ ∅
flat-∅ L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → Flat.JoinT L ∅ d n [] k e → ⊥
    to′ (Flat.val ())
    to′ (Flat.step ())
    to′ (Flat.opin ())
    to′ (Flat.oend () _)
    to′ (Flat.opass () _)
    to′ (Flat.lane () _ _ _ _)
    to′ (Flat.lend () _ _ _ _ _)
    to′ (Flat.lpass () _ _ _ _ _)
    to′ (Flat.hand () _ _ _ _)
    to′ (Flat.left () _ _ _ _)
    to′ (Flat.run () _)
    to′ (Flat.rend () _ _)
    to′ (Flat.rpass () _ _)
    to′ (Flat.rhand () _)

-- A JOINER WITH NO OUTER ROWS, NOTHING BEGUN AND NOTHING QUEUED: no rows.
switch-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d n → SwitchF.RowT L ∅ d n [] ≃ ∅
switch-∅ L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → SwitchF.JoinT L ∅ d n [] k e → ⊥
    to′ (SwitchF.val ())
    to′ (SwitchF.step ())
    to′ (SwitchF.opin ())
    to′ (SwitchF.oend () _)
    to′ (SwitchF.opass () _)
    to′ (SwitchF.lane () _ _ _ _)
    to′ (SwitchF.lend () _ _ _ _ _)
    to′ (SwitchF.lpass () _ _ _ _ _)
    to′ (SwitchF.hand () _ _ _ _)
    to′ (SwitchF.left () _ _ _ _)
    to′ (SwitchF.run (SwitchF.bg () _) _)
    to′ (SwitchF.rend (SwitchF.bg () _) _ _)
    to′ (SwitchF.rpass (SwitchF.bg () _) _ _)
    to′ (SwitchF.rhand (SwitchF.bg () _) _)
    to′ (SwitchF.run (SwitchF.bpin () _ _) _)

exhaust-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d n → ExhaustF.RowT L ∅ d n [] ≃ ∅
exhaust-∅ L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → ExhaustF.JoinT L ∅ d n [] k e → ⊥
    to′ (ExhaustF.val ())
    to′ (ExhaustF.step ())
    to′ (ExhaustF.opin ())
    to′ (ExhaustF.oend () _)
    to′ (ExhaustF.opass () _)
    to′ (ExhaustF.lane () _ _ _ _)
    to′ (ExhaustF.lend () _ _ _ _ _)
    to′ (ExhaustF.lpass () _ _ _ _ _)
    to′ (ExhaustF.hand () _ _ _ _)
    to′ (ExhaustF.left () _ _ _ _)
    to′ (ExhaustF.run () _)
    to′ (ExhaustF.rend () _ _)
    to′ (ExhaustF.rpass () _ _)
    to′ (ExhaustF.rhand () _)

bounded-∅ : ∀ {A B} m (L : A → Pos → EmissionSet B) d n → BoundedF.RowT m L ∅ d n [] [] ≃ ∅
bounded-∅ m L d n = (λ (r , _) → to′ r) ⇄ λ ()
  where
    to′ : ∀ {k e} → BoundedF.JoinT m L ∅ d n [] [] k e → ⊥
    to′ (BoundedF.val ())
    to′ (BoundedF.step ())
    to′ (BoundedF.opin ())
    to′ (BoundedF.oend () _)
    to′ (BoundedF.opass () _)
    to′ (BoundedF.lane () _ _ _ _)
    to′ (BoundedF.lend () _ _ _ _ _)
    to′ (BoundedF.lpass () _ _ _ _ _)
    to′ (BoundedF.hand () _ _ _ _)
    to′ (BoundedF.left () _ _ _ _)
    to′ (BoundedF.run (BoundedF.begun ()) _)
    to′ (BoundedF.rend (BoundedF.begun ()) _ _)
    to′ (BoundedF.rpass (BoundedF.begun ()) _ _)
    to′ (BoundedF.rhand (BoundedF.begun ()) _)
    to′ (BoundedF.run (BoundedF.waits (BoundedF.queued () , _) _) _)
    to′ (BoundedF.rend (BoundedF.waits (BoundedF.queued () , _) _) _ _)
    to′ (BoundedF.rpass (BoundedF.waits (BoundedF.queued () , _) _) _ _)
    to′ (BoundedF.rhand (BoundedF.waits (BoundedF.queued () , _) _) _)


-- A MAP ENTERED: its source entered, mapped.
enter-map : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → B) (s : Obs Timeline Γ A) p → pendRows ρ (map f s) p ≃ MapT f (pendRows ρ s p)
enter-map ρ f s p = proj₁ ⇄ λ x → x , reach′ x
  where
    t = enter (⟦ s ⟧ ρ) p

    src : ∀ {k e} → MapT f t k e → Σ (Ev _) (t k)
    src (map-out y)  = _ , y
    src (map-skip y) = _ , y
    src (map-pin y)  = _ , y
    src (map-end y)  = _ , y

    -- A pin's source row is the same pin.
    pd : ∀ {k e r} (x : MapT f t k e) → PDep r k e → PDep r k (proj₁ (src x))
    pd x            (inj₁ kr)   = inj₁ kr
    pd (map-pin y)  (inj₂ refl) = inj₂ refl
    pd (map-out y)  (inj₂ ())
    pd (map-skip y) (inj₂ ())
    pd (map-end y)  (inj₂ ())

    reach′ : ∀ {q e} → MapT f t q e → Reach (MapT f t) q e
    reach′ (map-out {a = a} y) = reach-via {e = out (f a)} {out a} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (map-skip y) = reach-via {e = skip} {skip} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (map-end y)  = reach-via {e = end} {end} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (map-pin {r = r} y) = reach-via {e = pin r} {pin r} (λ x _ d → proj₁ (src x) , proj₂ (src x) , λ i → pd x (d i)) (entered-reach (⟦ s ⟧ ρ) p y)

-- The denotation's joiner, freshly subscribed, as a policy.
denP : ∀ {A B : Set} → (Pos → A → EmissionSet B) → EmissionSet A → (Pos → Set) → (Pos → Pos → Set) → Policy A B
denP L o Ru Cu = record { lanes = L ; outer = o ; begun = λ _ _ → ⊥ ; over = Ended o ; runs = Ru ; cut = Cu ; hand = λ _ → ⊥ }

-- A lane read at its value's second child.
lane-at : ∀ {A B} {L : A → Pos → EmissionSet B} {q a} → At L q a ≃ Lane L q a
lane-at = (λ (l , p) → reads l p) ⇄ λ (reads l p) → l , p

-- A MERGE ENTERED: the merge part way through, at its outer entered, not
-- done, nothing begun.
enter-merge : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p
            → pendRows ρ (flatMap (mergeᶠ nothing) f s) p ≃ Flat.RowT (λ a → pendRows ρ (f a)) (pendRows ρ s p) false 0 []
enter-merge ρ f s p =
  trunc-≃ (join-≃ (denP (LaneOf (λ a → ⟦ f a ⟧ ρ)) O (λ _ → ⊤) (λ _ _ → ⊥)) (flatP L O false 0 [])
                  (record { lane≃ = lane-at ; ov→ = λ e → Flat.over-at (inj₂ e) tt ; ov← = λ { (Flat.over-at (inj₁ ()) _) ; (Flat.over-at (inj₂ e) _) → e }
                          ; ru→ = λ x → x ; ru← = λ x → x ; cu→ = λ x → x ; cu← = λ x → x ; ha→ = λ () ; ha← = λ () })
                  ((λ x → x) ⇄ (λ x → x)) ((λ ()) ⇄ (λ ())))
  where
    O = pendRows ρ s p
    L = λ a → pendRows ρ (f a)

-- A SCAN ENTERED: its source entered, scanned.
enter-scan : ∀ {Γ A B} (ρ : DenEnv Γ) (f : B → A → B) z (s : Obs Timeline Γ A) p → pendRows ρ (scan f z s) p ≃ Scan.ScanT f z (pendRows ρ s p)
enter-scan ρ f z s p = proj₁ ⇄ λ x → x , reach′ x
  where
    t = enter (⟦ s ⟧ ρ) p

    src : ∀ {k e} → Scan.ScanT f z t k e → Σ (Ev _) (t k)
    src (Scan.sval a)  = _ , proj₂ (acc-val a)
    src (Scan.sstep y) = _ , y
    src (Scan.spin y)  = _ , y
    src (Scan.send y)  = _ , y

    -- A pin's source row is the same pin.
    pd : ∀ {k e r} (x : Scan.ScanT f z t k e) → PDep r k e → PDep r k (proj₁ (src x))
    pd x             (inj₁ kr)   = inj₁ kr
    pd (Scan.spin y) (inj₂ refl) = inj₂ refl
    pd (Scan.sval y)  (inj₂ ())
    pd (Scan.sstep y) (inj₂ ())
    pd (Scan.send y)  (inj₂ ())

    reach′ : ∀ {q e} → Scan.ScanT f z t q e → Reach (Scan.ScanT f z t) q e
    reach′ (Scan.sval {b = b} a) = reach-via {e = out b} {out (proj₁ (acc-val a))} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p (proj₂ (acc-val a)))
    reach′ (Scan.sstep y) = reach-via {e = skip} {skip} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (Scan.send y)  = reach-via {e = end} {end} (λ x _ _ → proj₁ (src x) , proj₂ (src x) , tt) (entered-reach (⟦ s ⟧ ρ) p y)
    reach′ (Scan.spin {r = r} y) = reach-via {e = pin r} {pin r} (λ x _ d → proj₁ (src x) , proj₂ (src x) , λ i → pd x (d i)) (entered-reach (⟦ s ⟧ ρ) p y)

-- A SWITCH ENTERED: the switch part way through at its outer entered, not
-- done, nothing begun.
enter-switch : ∀ {Γ A B} (ρ : DenEnv Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p
             → pendRows ρ (flatMap switchᶠ f s) p ≃ SwitchF.RowT (λ a → pendRows ρ (f a)) (pendRows ρ s p) false 0 []
enter-switch ρ f s p =
  trunc-≃ (join-≃ (denP (LaneOf (λ a → ⟦ f a ⟧ ρ)) O (λ _ → ⊤) (Switch.Cut (λ a → ⟦ f a ⟧ ρ) O)) (switchP L O false 0 [])
                  (record { lane≃ = lane-at ; ov→ = λ e → inj₂ e , inj₁ tt ; ov← = λ { (inj₁ () , _) ; (inj₂ e , _) → e }
                          ; ru→ = λ x → x ; ru← = λ x → x ; cu→ = λ x → x ; cu← = λ x → x ; ha→ = λ () ; ha← = λ () })
                  ((λ x → x) ⇄ (λ x → x)) ((λ ()) ⇄ λ { (SwitchF.bg () _) ; (SwitchF.bpin () _ _) }))
  where
    O = pendRows ρ s p
    L = λ a → pendRows ρ (f a)

-- AN EXHAUST ENTERED: the exhaust part way through at its outer entered,
-- not done, nothing begun, so a value runs exactly where the
-- denotation's does.
module _ {Γ A B} (ρ : DenEnv Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (p : Pos) where
  private
    O = pendRows ρ s p
    L = λ a → pendRows ρ (f a)
    module D = Exhaust (λ a → ⟦ f a ⟧ ρ) O
    module F = ExhaustF L O false 0 []

    -- No lane begun: none is ever the last run.
    no-bg : ∀ {q} → F.Cur q nothing → ⊥
    no-bg (F.bg₀ _ _ nf)      = nf tt
    no-bg (F.bdrop c _ _ _ _) = no-bg c

    cur→ : ∀ {q₁ q} → D.Cur q₁ q → F.Cur q₁ (just q)
    cur→ (D.cur₀ r mn)                     = F.cur₀ r mn tt
    cur→ (D.run c r (l , lp) lt r₂ lt′ nx) = F.run (cur→ c) r (reads l lp) lt r₂ lt′ nx
    cur→ (D.drop c r h r₂ lt nx)           = F.drop (cur→ c) r (λ (reads l lp) → h (l , lp)) r₂ lt nx

    cur← : ∀ {q₁ q} → F.Cur q₁ (just q) → D.Cur q₁ q
    cur← (F.cur₀ r mn _)                         = D.cur₀ r mn
    cur← (F.run c r (reads l lp) lt r₂ lt′ nx)   = D.run (cur← c) r (l , lp) lt r₂ lt′ nx
    cur← (F.drop c r h r₂ lt nx)                 = D.drop (cur← c) r (λ (l , lp) → h (reads l lp)) r₂ lt nx
    cur← (F.brun c _ _ _ _)                      = ⊥-elim (no-bg c)

  enter-exhaust : pendRows ρ (flatMap exhaustᶠ f s) p ≃ ExhaustF.RowT L O false 0 []
  enter-exhaust =
    trunc-≃ (join-≃ (denP (LaneOf (λ a → ⟦ f a ⟧ ρ)) O D.Run (λ _ _ → ⊥)) (exhaustP L O false 0 [])
                    (record { lane≃ = lane-at ; ov→ = λ e → inj₂ e , tt ; ov← = λ { (inj₁ () , _) ; (inj₂ e , _) → e }
                            ; ru→ = cur→ ; ru← = cur← ; cu→ = λ x → x ; cu← = λ x → x ; ha→ = λ () ; ha← = λ () })
                    ((λ x → x) ⇄ (λ x → x)) ((λ ()) ⇄ (λ ())))

-- Two lists of ends, end for end the same.
SameEnds : List (Pos → Set) → List (Pos → Set) → Set₁
SameEnds = Pointwise (λ l l′ → ∀ c → (l c → l′ c) × (l′ c → l c))

-- A BOUNDED MERGE ENTERED: the joiner part way through at its outer
-- entered, not done, nothing begun or queued, so its schedule is the
-- denotation's lane for lane.
module _ {Γ A B} (ρ : DenEnv Γ) (m : ℕ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (p : Pos) where
  private
    O = pendRows ρ s p
    L = λ a → pendRows ρ (f a)
    module D = Bounded m (λ a → ⟦ f a ⟧ ρ) O
    module F = BoundedF m L O false 0 [] []

    kth→ : ∀ {P ls ls′ k} → SameEnds ls ls′ → D.Kth P ls k → Kth P ls′ k
    kth→ {k = zero}  (r ∷ pw) (inj₁ (c , l , x))       = inj₁ (c , proj₁ (r c) l , x)
    kth→ {k = zero}  (r ∷ pw) (inj₂ y)                 = inj₂ (kth→ pw y)
    kth→ {k = suc k} (r ∷ pw) (inj₁ ((c , l , x) , y)) = inj₁ ((c , proj₁ (r c) l , x) , kth→ pw y)
    kth→ {k = suc k} (r ∷ pw) (inj₂ y)                 = inj₂ (kth→ pw y)

    kth← : ∀ {P ls ls′ k} → SameEnds ls ls′ → Kth P ls′ k → D.Kth P ls k
    kth← {k = zero}  (r ∷ pw) (inj₁ (c , l , x))       = inj₁ (c , proj₂ (r c) l , x)
    kth← {k = zero}  (r ∷ pw) (inj₂ y)                 = inj₂ (kth← pw y)
    kth← {k = suc k} (r ∷ pw) (inj₁ ((c , l , x) , y)) = inj₁ ((c , proj₂ (r c) l , x) , kth← pw y)
    kth← {k = suc k} (r ∷ pw) (inj₂ y)                 = inj₂ (kth← pw y)

    starts→ : ∀ {i q ls ls′ t} → SameEnds ls ls′ → D.Starts i q ls t → F.Starts i ls′ (just q) t
    starts→ pw (D.room lt)                = F.room lt
    starts→ pw (D.freed le k)             = F.freed le (kth→ pw k)
    starts→ pw (D.queued le lt k₀ kl nk)  = F.queued le lt (kth→ pw k₀) (kth→ pw kl) (λ x → nk (kth← pw x))

    starts← : ∀ {i q ls ls′ t} → SameEnds ls ls′ → F.Starts i ls′ (just q) t → D.Starts i q ls t
    starts← pw (F.room lt)                = D.room lt
    starts← pw (F.freed le k)             = D.freed le (kth← pw k)
    starts← pw (F.queued le lt k₀ kl nk)  = D.queued le lt (kth← pw k₀) (kth← pw kl) (λ x → nk (kth→ pw x))

    ends→ : ∀ {i ls ls′ c} → SameEnds ls ls′ → D.Ends i ls c → F.Ends i ls′ c
    ends→ pw (q , a , t , nt , st , (e , lt)) = just q , a , t , F.outer nt , starts→ pw st , sub e lt

    ends← : ∀ {i ls ls′ c} → SameEnds ls ls′ → F.Ends i ls′ c → D.Ends i ls c
    ends← pw (just q , a , t , F.outer nt , st , sub e lt) = q , a , t , nt , starts← pw st , (e , lt)
    ends← pw (nothing , a , t , F.queued () , _)

    sched : ∀ i → SameEnds (D.Sched i) (F.Sched i)
    sched zero    = []
    sched (suc i) = (λ c → ends→ (sched i) , ends← (sched i)) ∷ sched i

    lane→ : ∀ {q a k e} → D.Lane q a k e → F.LaneB q a k e
    lane→ (i , t , (nt , st) , (e , lt)) = i , t , (F.outer nt , starts→ (sched i) st) , sub e lt

    lane← : ∀ {q a k e} → F.LaneB q a k e → D.Lane q a k e
    lane← (i , t , (F.outer nt , st) , sub e lt) = i , t , (nt , starts← (sched i) st) , (e , lt)

    ha→ : ∀ {c} → D.Queued c → F.Queued c
    ha→ (i , q , a , nt , st) = i , just q , a , F.outer nt , starts→ (sched i) st

    ha← : ∀ {c} → F.Queued c → D.Queued c
    ha← (i , just q , a , F.outer nt , st) = i , q , a , nt , starts← (sched i) st
    ha← (i , nothing , a , F.queued () , _)

    bg← : ∀ {k e} → F.Bg k e → ⊥
    bg← (F.begun ())
    bg← (F.waits (F.queued () , _) _)

    dP = record { lanes = D.Lane ; outer = O ; begun = λ _ _ → ⊥ ; over = Ended O ; runs = D.Indexed ; cut = λ _ _ → ⊥ ; hand = D.Queued }

  enter-bounded : pendRows ρ (flatMap (mergeᶠ (just m)) f s) p ≃ BoundedF.RowT m L O false 0 [] []
  enter-bounded =
    trunc-≃ (join-≃ dP (boundedP m L O false 0 [] [])
                    (record { lane≃ = lane→ ⇄ lane← ; ov→ = λ e → inj₂ e , tt ; ov← = λ { (inj₁ () , _) ; (inj₂ e , _) → e }
                            ; ru→ = λ (i , a , nt) → i , a , F.outer nt ; ru← = λ { (i , a , F.outer nt) → i , a , nt }
                            ; cu→ = λ x → x ; cu← = λ x → x ; ha→ = ha→ ; ha← = ha← })
                    ((λ x → x) ⇄ (λ x → x)) ((λ ()) ⇄ λ x → ⊥-elim (bg← x)))
