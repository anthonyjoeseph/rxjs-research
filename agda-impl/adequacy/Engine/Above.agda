{-# OPTIONS --guardedness #-}

-- WHAT EVERY FRAME ABOVE A HOLE KEEPS OF ITS POSITIONS, the hole read as
-- a run: each ancestor's `adequacy.Engine.Keys.Here` with the run in its
-- child's place, frame by frame as `adequacy.Engine.Meaning.up` reads the
-- hole, and each sibling keyed (`Above`).  The whole tree's ghost has
-- already dropped an event in flight and not yet begun a pending
-- subscription; the hole's run (`Meaning.hole`) carries both, so a frame a
-- rise rewrites finds here what it owes the event (`Flight`).
--
-- A takeWhile failing a value ends one past it: the frames above saw the
-- failing value's run end there (`take-excl`, `take-incl`), and the end is
-- headed and ahead of what the source leaves running because the value
-- was (`take-here`).
module adequacy.Engine.Above where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; _++_; [_]; reverse)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Timeline; out; end; ix; last; _<ᵖ_; _∪_)
open import denotation.MonotonicList using (MonotonicList; taking)
open import denotation.Unfold using (Node; NEnv; stateᴺ; states; outerᴺ; endingᶜ; takeWhileᶜ)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; CS; Conf; ⟨_,_,_,_⟩; nx; cpAt; _⊕_)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; ≋-out; mapped; scanned; switched; taking∞; took; rested; outerFrame; lanesFrame; srcFrame; bodyFrame;
  lane; lanesL; deadL; poolT; outerT; outerG; laneRuns; poolRuns; gh; envAt; hole; flagOf; risen)
  renaming (outerOf to outerOfᴹ)
open import adequacy.Engine.Keys using (Shape; Shape′; TakeAt; FlatAt; ConnAt; Keyed; KeyedL; Keys; srcIn)
open import adequacy.Placed.Order using (Headed; Disjoint; Ext; every; everyT-mono)
open import adequacy.Placed.Trail using (trail)

open Events∞

------------------------------------------------------------------------
-- The frames above a hole

-- A merge's outer, as its lanes' generator reads it, the hole its run:
-- running, else done.
outerAt : ∀ {Γ A C} → Bool → (A → Obs Timeline Γ C) → NEnv Γ → Events∞ A → Maybe (Events∞ (MonotonicList C))
outerAt false g ρ h = just (outerOfᴹ (lane g) ρ h)
outerAt true  g ρ h = nothing

-- What a merge's pool leaves running, the hole its outer: done, it
-- joins the pool.
poolAt : ∀ {Γ A B} → Bool → Events∞ A → List (Node Γ B) → NEnv Γ → Tail
poolAt false h ds ρ = poolT ds ρ
poolAt true  h ds ρ = cut h ∪ poolT ds ρ

-- What a connect's source, the hole, feeds its body: its run, else, once
-- closed, its end; and what it runs as: itself, else its rest.
fedRun : ∀ {X} → Bool → Pos → Events∞ X → Events X
fedRun false e h = force h
fedRun true  e h = end e

srcRunning : ∀ {X} → Bool → Events∞ X → Events∞ X
srcRunning false h = h
srcRunning {X} true h = rested {B = X} h

-- Every frame above the hole keeping its own, its siblings keyed, the
-- hole's run `h` in its child's place.
Above : ∀ {R Γ A} → Ctx R Γ A → Bool → Events∞ A → Set
Above top                               f h = ⊤
Above (inMap g c)                       f h = Above c true (mapped g h)
Above (inScan g z c)                    f h = Above c true (scanned g z h)
Above (inCut l a c)                     f h = Above c true (switched l h)
Above (inLn b c)                        f h = Above c b h
Above (inTake i q w c)                  f h = TakeAt w h × Above c true (taking∞ i q w h)
Above (inOuter op g d n q ls c)         f h =
  (FlatAt (envAt c) (outerAt d g (envAt c) h) (states (lanesL ls) (envAt c)) (poolAt d h (deadL ls) (envAt c)) × KeyedL ls (envAt c))
  × Above c true (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h)
Above (inLanes op g d n q o pre post c) f h =
  (FlatAt (envAt c) (outerᴺ (lane g) (outerG d (gh o)) (envAt c)) (laneRuns (reverse pre) post f (envAt c) h)
          (outerT d (gh o) (envAt c) (poolRuns (reverse pre) post f (envAt c) h))
   × Keyed o (envAt c) × KeyedL pre (envAt c) × KeyedL post (envAt c))
  × Above c true (lanesFrame op (lane g) d q (gh o) (reverse pre) post f (envAt c) h)
Above (inSrc k b c)                     f h =
  (ConnAt k (stateᴺ (gh b) (fedRun (CS.closed k) (CS.endAt k) h ∷ᴬ envAt c)) (srcRunning (CS.closed k) h) (envAt c)
   × Keyed b (fedRun (CS.closed k) (CS.endAt k) h ∷ᴬ envAt c))
  × Above c true (srcFrame k (gh b) (envAt c) h)
Above (inBody k o c)                    f h =
  (ConnAt k h (srcIn k o (envAt c)) (envAt c) × Keyed o (envAt c))
  × Above c true (bodyFrame k o (envAt c) h)

-- A configuration's hole's run in shape, and every frame above it keeping
-- its own of that run.
Flight : ∀ {R} → Conf R → Set
Flight ⟨ c , s , m , p ⟩ = Shape (hole c s m p) × Above c (flagOf s) (hole c s m p)

postulate
  -- THE KEYS KEPT: runs alike at every depth are kept alike by every frame
  -- above them.
  above-≋ : ∀ {R Γ A} (c : Ctx R Γ A) f {h h′ : Events∞ A} → h ≋ h′ → Above c f h → Above c f h′
  -- Every frame above a hole keeping its own of the run the hole's ghost
  -- gives it, and the hole its own: the whole tree keyed.
  keys-above : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Above c (flagOf s) (stateᴺ (gh s) (envAt c)) → Keyed s (envAt c) → Keys (plug c s)
  -- Every frame above a hole keeping its own of a value rising out of it
  -- keeps its own of the hole's ghost past the value.
  keys-past : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) a p → Above c (flagOf s) (risen (gh s) (envAt c) (nx a) p) → Keyed s (envAt c)
            → Keys (plug c s)
  -- A position not before a disjoint one: one past its last child is
  -- after it, apart from it, and no prefix of it.
  past-last : ∀ p k → k <ᵖ p ≡ false → Disjoint p k → (p ++ [ last ]) <ᵖ k ≡ true × Disjoint ((p ++ [ last ]) ++ [ ix 1 ]) k × ¬ Ext (p ++ [ last ]) k

------------------------------------------------------------------------
-- A takeWhile failing a value

headed-last : ∀ p → Headed p → Headed (p ++ [ last ])
headed-last (ix _ ∷ _) h = tt

-- What a failing value's run leaves running trails the end one past it.
take-here : ∀ {A} p a (h : Events∞ A) → Shape′ (out p a h) (cut h) → TakeAt (cpAt p) h
take-here p a h ((_ , hd , _) , tr) =
  headed-last p (proj₁ (every hd)) , everyT-mono (λ k t → past-last p k (proj₁ t) (proj₂ t)) (cut h) (proj₁ (proj₂ (trail tr)))

-- A takeWhile's value, taken: the value as the node runs on; failed,
-- taken under its own position before the end one past it, else not.
take-true : ∀ {Γ A} i (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ true
          → took i q (risen n ρ (nx a) p) ≋ risen (takeWhileᶜ i q n) ρ (nx a) p
take-true i q n ρ a p e = ≋-out (cong (λ b → taking i q p a b (stateᴺ n ρ)) e) refl refl refl refl

take-incl : ∀ {Γ A} (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ false
          → took true q (risen n ρ (nx a) p) ≋ risen (endingᶜ (p ⊕ [ last ]) n) ρ (nx a) (p ⊕ [ ix 0 ])
take-incl q n ρ a p e = ≋-out (cong (λ b → taking true q p a b (stateᴺ n ρ)) e) refl refl refl refl

take-excl : ∀ {Γ A} (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ false
          → took false q (risen n ρ (nx a) p) ≋ stateᴺ (endingᶜ (p ⊕ [ last ]) n) ρ
take-excl q n ρ a p e = ≋-by (cong (λ b → taking false q p a b (stateᴺ n ρ)) e) refl
