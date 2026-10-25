{-# OPTIONS --guardedness #-}

-- WHAT THE FRAMES ABOVE ASK OF A SKIP.  A skip dropped at a hole reaches
-- the root only through frames that show the hole's next step (`shows`);
-- each such frame asks the skip to come first among its siblings
-- (`Ahead`), whatever the hole runs.  A flatMap's lane by its siblings
-- (`Sides`), its outer by its lanes and pool, a connect's body by its
-- source; above a connect's live source, of every position under the
-- skip (`Under`).
module adequacy.Engine.Ahead where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Empty using (⊥)
open import Data.List using (List; _++_; reverse)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Pos; Timeline; Events; Events∞; idle; hush; _∪_)
open import denotation.MonotonicList using (head; shownAt; Agreeᵀ)
open import denotation.Unfold using (NEnv; states; outerᴺ)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; free; cpAt; cutAt; overAt; closed)
open import adequacy.Engine.Meaning using (gh; lane; outerG; lanesL; deadL; poolT; tailsOn; outerT; envAt; srcState; srcG)
open import adequacy.Engine.Race using (First; NotBefore; After; TailNotBefore)

-- A flatMap's other parts, as a lane rising at `p` leads them.
Sides : ∀ {Γ A B} → Pos → (A → Obs Timeline Γ B) → Bool → St Γ A → List (St Γ B) → List (St Γ B) → NEnv Γ → Set
Sides p f d o pre post ρ =
  First p (outerᴺ (lane f) (outerG d (gh o)) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ)
    (outerT d (gh o) ρ (tailsOn (deadL pre) ρ (idle ∪ poolT (deadL post) ρ)))

-- Whether every frame up the context shows the hole's next step, rather
-- than reading only its tail: `Pass` is empty exactly where this fails.
shows : ∀ {R Γ A} → Ctx R Γ A → Bool → Bool
shows top                                                 f = true
shows (inMap g c)                                         f = shows c true
shows (inScan g z c)                                      f = shows c true
shows (inCut l a c)                                       f = l ∧ shows c true
shows (inLn b c)                                          f = shows c b
shows (inTake i q free c)                                 f = shows c true
shows (inTake i q (cpAt _) c)                             f = false
shows (inTake i q (cutAt _) c)                            f = false
shows (inTake i q (overAt _) c)                           f = false
shows (inOuter op g d n q ls c)                           f = not d ∧ shows c true
shows (inLanes op g d n q o pre post c)                   f = f ∧ shows c true
shows (inSrc (cs false true sa ba as nothing r en) b c)   f = shows c true
shows (inSrc (cs false true sa ba as (just _) r en) b c)  f = false
shows (inSrc (cs false false sa ba as ow r en) b c)       f = false
shows (inSrc (cs true sl sa ba as ow r en) b c)           f = false
shows (inBody (cs cl true sa ba as nothing r en) o c)     f = shows c true
shows (inBody (cs cl true sa ba as (just _) r en) o c)    f = false
shows (inBody (cs cl false sa ba as ow r en) o c)         f = false

-- A context showing its hole's next step is not closed.
shows-open : ∀ {R Γ A} (c : Ctx R Γ A) f → shows c f ≡ true → closed c ≡ false
shows-open top                                                 f e = refl
shows-open (inMap g c)                                         f e = shows-open c true e
shows-open (inScan g z c)                                      f e = shows-open c true e
shows-open (inCut true a c)                                    f e = shows-open c true e
shows-open (inCut false a c)                                   f ()
shows-open (inLn b c)                                          f e = shows-open c b e
shows-open (inTake i q free c)                                 f e = shows-open c true e
shows-open (inTake i q (cpAt _) c)                             f ()
shows-open (inTake i q (cutAt _) c)                            f ()
shows-open (inTake i q (overAt _) c)                           f ()
shows-open (inOuter op g false n q ls c)                       f e = shows-open c true e
shows-open (inOuter op g true n q ls c)                        f ()
shows-open (inLanes op g d n q o pre post c)                   true  e = shows-open c true e
shows-open (inLanes op g d n q o pre post c)                   false ()
shows-open (inSrc (cs false true sa ba as nothing r en) b c)   f e = refl
shows-open (inSrc (cs false true sa ba as (just _) r en) b c)  f ()
shows-open (inSrc (cs false false sa ba as ow r en) b c)       f ()
shows-open (inSrc (cs true sl sa ba as ow r en) b c)           f ()
shows-open (inBody (cs cl true sa ba as nothing r en) o c)     f e = shows-open c true e
shows-open (inBody (cs cl true sa ba as (just _) r en) o c)    f ()
shows-open (inBody (cs cl false sa ba as ow r en) o c)         f ()

-- The positions a skip at `P` puts under itself.
Under : (Pos → Set) → Pos → Set
Under P k′ = Σ Pos λ k → P k × Σ Pos λ y → k′ ≡ k ++ y

-- Where a source's next step shows, if it has one.
shown : ∀ {A} → Events A → Maybe Pos
shown hush = nothing
shown e    = just (shownAt e)

-- What every frame up the context asks of the skips at `P` it passes,
-- whatever the hole runs: a flatMap's other parts after each, a
-- connect's source no earlier and, hushed, nothing running.  Empty
-- exactly where `shows` fails.
Ahead : ∀ {R Γ A} → (Pos → Set) → Ctx R Γ A → Bool → Set
Ahead P top                                                 f = ⊤
Ahead P (inMap g c)                                         f = Ahead P c true
Ahead P (inScan g z c)                                      f = Ahead P c true
Ahead P (inCut true a c)                                    f = Ahead P c true
Ahead P (inCut false a c)                                   f = ⊥
Ahead P (inLn b c)                                          f = Ahead P c b
Ahead P (inTake i q free c)                                 f = Ahead P c true
Ahead P (inTake i q (cpAt _) c)                             f = ⊥
Ahead P (inTake i q (cutAt _) c)                            f = ⊥
Ahead P (inTake i q (overAt _) c)                           f = ⊥
Ahead P (inOuter op g true n q ls c)                        f = ⊥
Ahead P (inOuter op g false n q ls c)                       f =
  (∀ k → P k → All (λ l → After k (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore k (poolT (deadL ls) (envAt c)))
  × Ahead P c true
Ahead P (inLanes op g d n q o pre post c)                   false = ⊥
Ahead P (inLanes op g d n q o pre post c)                   true  = (∀ k → P k → Sides k g d o (reverse pre) post (envAt c)) × Ahead P c true
Ahead P (inSrc (cs false true sa ba as nothing r en) b c)   f = Ahead (Under P) c true
Ahead P (inSrc (cs false true sa ba as (just _) r en) b c)  f = ⊥
Ahead P (inSrc (cs false false sa ba as ow r en) b c)       f = ⊥
Ahead P (inSrc (cs true sl sa ba as ow r en) b c)           f = ⊥
Ahead P (inBody (cs cl true sa ba as nothing r en) o c)     f =
  (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) ≡ hush
     → ∀ d → Agreeᵀ d (Events∞.cut (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))) idle)
  × (∀ k → P k → NotBefore k (shown (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))))
  × Ahead P c true
Ahead P (inBody (cs cl true sa ba as (just _) r en) o c)    f = ⊥
Ahead P (inBody (cs cl false sa ba as ow r en) o c)         f = ⊥

-- Asked of fewer positions, the frames ask less.
under-mono : ∀ {P P′ : Pos → Set} → (∀ k → P′ k → P k) → ∀ k → Under P′ k → Under P k
under-mono m _ (k , pk , y , e) = k , m k pk , y , e

ahead-mono : ∀ {R Γ A} {P P′ : Pos → Set} → (∀ k → P′ k → P k) → (c : Ctx R Γ A) (f : Bool) → Ahead P c f → Ahead P′ c f
ahead-mono m top                                                 f a = a
ahead-mono m (inMap g c)                                         f a = ahead-mono m c true a
ahead-mono m (inScan g z c)                                      f a = ahead-mono m c true a
ahead-mono m (inCut true x c)                                    f a = ahead-mono m c true a
ahead-mono m (inCut false x c)                                   f ()
ahead-mono m (inLn b c)                                          f a = ahead-mono m c b a
ahead-mono m (inTake i q free c)                                 f a = ahead-mono m c true a
ahead-mono m (inTake i q (cpAt _) c)                             f ()
ahead-mono m (inTake i q (cutAt _) c)                            f ()
ahead-mono m (inTake i q (overAt _) c)                           f ()
ahead-mono m (inOuter op g true n q ls c)                        f ()
ahead-mono m (inOuter op g false n q ls c)                       f (o , a) = (λ k pk → o k (m k pk)) , ahead-mono m c true a
ahead-mono m (inLanes op g d n q o pre post c)                   false ()
ahead-mono m (inLanes op g d n q o pre post c)                   true (s , a) = (λ k pk → s k (m k pk)) , ahead-mono m c true a
ahead-mono m (inSrc (cs false true sa ba as nothing r en) b c)   f a = ahead-mono (under-mono m) c true a
ahead-mono m (inSrc (cs false true sa ba as (just _) r en) b c)  f ()
ahead-mono m (inSrc (cs false false sa ba as ow r en) b c)       f ()
ahead-mono m (inSrc (cs true sl sa ba as ow r en) b c)           f ()
ahead-mono m (inBody (cs cl true sa ba as nothing r en) o c)     f (hu , nb , a) = hu , (λ k pk → nb k (m k pk)) , ahead-mono m c true a
ahead-mono m (inBody (cs cl true sa ba as (just _) r en) o c)    f ()
ahead-mono m (inBody (cs cl false sa ba as ow r en) o c)         f ()

-- What is under a position under `p` is under `p`.
under-sub : ∀ p y k → Under (_≡ p ++ y) k → Under (_≡ p) k
under-sub p y _ (_ , refl , y′ , refl) = p , refl , y ++ y′ , ++-assoc p y y′
