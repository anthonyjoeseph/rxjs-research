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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; reverse)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Pos; Timeline; Events; Events∞; Tail; idle; pin; hush; ix; _∪_; <ᵖ-over; <ᵖ-split; <ᵖ-asym)
open import denotation.MonotonicList using (MonotonicList; head; headᴼ; shownAt; Agreeᵀ)
open import denotation.Unfold using (NEnv; states; outerᴺ)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; free; cpAt; cutAt; overAt; closed)
open import adequacy.Engine.Meaning using (gh; lane; outerG; lanesL; deadL; poolT; tailsOn; outerT; envAt; srcState; srcG)
open import adequacy.Engine.Race using (First; first; NotBefore; After; TailNotBefore)

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

-- Positions under a position under one are under it.
under-under : ∀ {P : Pos → Set} {k} → Under (Under P) k → Under P k
under-under (_ , (k₀ , p₀ , y₀ , refl) , y , refl) = k₀ , p₀ , y₀ ++ y , ++-assoc k₀ y₀ y

under-self : ∀ {P : Pos → Set} {k} → P k → Under P k
under-self {k = k} p = k , p , [] , sym (++-identityʳ k)

------------------------------------------------------------------------
-- Aloof of a skip's subtree

-- A head not below `k`.
Off : Pos → Maybe Pos → Set
Off k nothing  = ⊤
Off k (just h) = ∀ l ls → h ≡ k ++ l ∷ ls → ⊥

OffT : Pos → Tail → Set
OffT k idle      = ⊤
OffT k (pin h u) = Off k (just h)

-- A lane's siblings, none below `k`.
OffFirst : ∀ {B} → Pos → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → List (Events∞ B) → Tail → Set
OffFirst k o ls rs t =
  All (λ l → Off k (head (Events∞.force l))) ls × All (λ l → Off k (head (Events∞.force l))) rs × Off k (headᴼ o) × OffT k t

-- Every head the frames above a skip at `k` ask of, none below `k`.
Aloof : ∀ {R Γ A} → Pos → Ctx R Γ A → Bool → Set
Aloof k top                                                 f = ⊤
Aloof k (inMap g c)                                         f = Aloof k c true
Aloof k (inScan g z c)                                      f = Aloof k c true
Aloof k (inCut true a c)                                    f = Aloof k c true
Aloof k (inCut false a c)                                   f = ⊤
Aloof k (inLn b c)                                          f = Aloof k c b
Aloof k (inTake i q free c)                                 f = Aloof k c true
Aloof k (inTake i q (cpAt _) c)                             f = ⊤
Aloof k (inTake i q (cutAt _) c)                            f = ⊤
Aloof k (inTake i q (overAt _) c)                           f = ⊤
Aloof k (inOuter op g true n q ls c)                        f = ⊤
Aloof k (inOuter op g false n q ls c)                       f =
  All (λ l → Off k (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × OffT k (poolT (deadL ls) (envAt c)) × Aloof k c true
Aloof k (inLanes op g d n q o pre post c)                   false = ⊤
Aloof k (inLanes op g d n q o pre post c)                   true  =
  OffFirst k (outerᴺ (lane g) (outerG d (gh o)) (envAt c)) (states (lanesL post) (envAt c)) (states (lanesL (reverse pre)) (envAt c))
    (outerT d (gh o) (envAt c) (tailsOn (deadL (reverse pre)) (envAt c) (idle ∪ poolT (deadL post) (envAt c))))
  × Aloof k c true
Aloof k (inSrc (cs false true sa ba as nothing r en) b c)   f = Aloof k c true
Aloof k (inSrc (cs false true sa ba as (just _) r en) b c)  f = ⊤
Aloof k (inSrc (cs false false sa ba as ow r en) b c)       f = ⊤
Aloof k (inSrc (cs true sl sa ba as ow r en) b c)           f = ⊤
Aloof k (inBody (cs cl true sa ba as nothing r en) o c)     f =
  Off k (shown (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))) × Aloof k c true
Aloof k (inBody (cs cl true sa ba as (just _) r en) o c)    f = ⊤
Aloof k (inBody (cs cl false sa ba as ow r en) o c)         f = ⊤

off-after : ∀ k h {j} → Under (_≡ k) j → After (k ++ [ ix 0 ]) h → Off k h → After j h
off-after k nothing  u                       a o = tt
off-after k (just h) (_ , refl , ys , refl) a o = <ᵖ-over k h ys a o

off-nb : ∀ k h {j} → Under (_≡ k) j → NotBefore (k ++ [ ix 0 ]) h → Off k h → NotBefore j h
off-nb k nothing  u                       n o = tt
off-nb k (just h) (_ , refl , ys , refl) n o with <ᵖ-split (k ++ [ ix 0 ]) h n
... | inj₁ lt = <ᵖ-asym (k ++ ys) h (<ᵖ-over k h ys lt o)
... | inj₂ e  = ⊥-elim (o (ix 0) [] (sym e))

off-tnb : ∀ k t {j} → Under (_≡ k) j → TailNotBefore (k ++ [ ix 0 ]) t → OffT k t → TailNotBefore j t
off-tnb k idle      u n o = tt
off-tnb k (pin h v) u n o = off-nb k (just h) u n o

off-alls : ∀ {X : Set} (F : Pos → Maybe Pos → Set) (hd : X → Maybe Pos) k {j} → (∀ h → F (k ++ [ ix 0 ]) h → Off k h → F j h)
         → (xs : List X) → All (λ x → F (k ++ [ ix 0 ]) (hd x)) xs → All (λ x → Off k (hd x)) xs → All (λ x → F j (hd x)) xs
off-alls F hd k g []       []ᴬ        []ᴬ        = []ᴬ
off-alls F hd k g (x ∷ xs) (a ∷ᴬ as) (o ∷ᴬ os) = g (hd x) a o ∷ᴬ off-alls F hd k g xs as os

off-first : ∀ {B} k {j} {o : Maybe (Events∞ (MonotonicList B))} {ls rs t} → Under (_≡ k) j → First (k ++ [ ix 0 ]) o ls rs t → OffFirst k o ls rs t → First j o ls rs t
off-first k {o = o} {ls} {rs} {t} u (first b a on tn) (ob , oa , oo , ot) =
  first (off-alls NotBefore (λ l → head (Events∞.force l)) k (λ h → off-nb k h u) ls b ob)
        (off-alls After (λ l → head (Events∞.force l)) k (λ h → off-after k h u) rs a oa)
        (off-nb k (headᴼ o) u on oo) (off-tnb k t u tn ot)

-- What the frames above ask at `k ++ [ ix 0 ]`, they ask of every
-- position under `k`, none of their heads being below `k`.
ahead-over : ∀ {R Γ A} {P : Pos → Set} k → (∀ j → P j → Under (_≡ k) j) → (c : Ctx R Γ A) (f : Bool)
           → Ahead (_≡ k ++ [ ix 0 ]) c f → Aloof k c f → Ahead P c f
ahead-over k sub top                                                 f a al = tt
ahead-over k sub (inMap g c)                                         f a al = ahead-over k sub c true a al
ahead-over k sub (inScan g z c)                                      f a al = ahead-over k sub c true a al
ahead-over k sub (inCut true x c)                                    f a al = ahead-over k sub c true a al
ahead-over k sub (inCut false x c)                                   f () al
ahead-over k sub (inLn b c)                                          f a al = ahead-over k sub c b a al
ahead-over k sub (inTake i q free c)                                 f a al = ahead-over k sub c true a al
ahead-over k sub (inTake i q (cpAt _) c)                             f () al
ahead-over k sub (inTake i q (cutAt _) c)                            f () al
ahead-over k sub (inTake i q (overAt _) c)                           f () al
ahead-over k sub (inOuter op g true n q ls c)                        f () al
ahead-over k sub (inOuter op g false n q ls c)                       f (o , a) (ol , ot , al) =
  (λ j pj → off-alls After (λ l → head (Events∞.force l)) k (λ h → off-after k h (sub j pj)) _ (proj₁ (o _ refl)) ol
          , off-tnb k _ (sub j pj) (proj₂ (o _ refl)) ot)
  , ahead-over k sub c true a al
ahead-over k sub (inLanes op g d n q o pre post c)                   false () al
ahead-over k sub (inLanes op g d n q o pre post c)                   true (s , a) (so , al) =
  (λ j pj → off-first k (sub j pj) (s _ refl) so) , ahead-over k sub c true a al
ahead-over k sub (inSrc (cs false true sa ba as nothing r en) b c)   f a al =
  ahead-over k (λ j u → under-under (under-mono sub j u)) c true (ahead-mono (λ j e → under-self e) c true a) al
ahead-over k sub (inSrc (cs false true sa ba as (just _) r en) b c)  f () al
ahead-over k sub (inSrc (cs false false sa ba as ow r en) b c)       f () al
ahead-over k sub (inSrc (cs true sl sa ba as ow r en) b c)           f () al
ahead-over k sub (inBody (cs cl true sa ba as nothing r en) o c)     f (hu , nb , a) (on , al) =
  hu , (λ j pj → off-nb k _ (sub j pj) (nb _ refl) on) , ahead-over k sub c true a al
ahead-over k sub (inBody (cs cl true sa ba as (just _) r en) o c)    f () al
ahead-over k sub (inBody (cs cl false sa ba as ow r en) o c)         f () al
