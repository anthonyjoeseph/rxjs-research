{-# OPTIONS --guardedness #-}

-- A SKIP DROPPED AT A HOLE IS DROPPED AT THE ROOT, when every frame on
-- the way up shows it next (`Pass`): a run past leading skips at the hole
-- (`Dropsˢ`) is a run past leading skips at the root (`lift-drops`).
--
-- A frame with one child passes a skip as it is.  A switched-off cut, a
-- takeWhile past its decision, a connect that is over or whose source is
-- closed, and a lane in the pool read only the hole's tail: there a skip
-- is not shown at all, and `Pass` is empty.  A frame with siblings passes
-- the skip when it comes first among them.  A connect's source passes it
-- with what its joiners saw of it, each under the skip's position
-- (`Under`): the body fed the run drops its own skips to the body fed
-- the rest (`Fed`).
module adequacy.Engine.Drop where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (_∷_; _++_; reverse)
import Data.List as L
import denotation.MonotonicList as M′
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; skip; hush)
open import denotation.MonotonicList using (head; shownAt; Agree; stop; skip⁼; agree-trans; agreeᵀ-refl)
open import denotation.NonExpansive using (_,ˢ_; mapᴱ-ne; scanᴱ-ne; takeWhileᴱ-ne)
open import denotation.Unfold using (Node; NEnv; stateᴺ; states; outerᴺ)
open import denotation.Denote using (flatOp)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; free; cpAt; cutAt; overAt)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; up; mapped; scanned; took; outerFrame; lanesFrame; connSrc; bodyConn; srcState;
  srcG; envAt; gh; lane; lanesL; deadL; outerG; outerT; poolRuns; poolT; laneᴹ; lanesFrame-ne)
open import adequacy.Engine.Race using (First; After; NotBefore; TailNotBefore; go-rise)
open Events∞
open import denotation.NonExpansive using (Agreeˢ)
open Agreeˢ

------------------------------------------------------------------------
-- Runs past their leading skips

-- A run past one or more of its leading skips.
data Drops {A : Set} (e e′ : Events A) : Set where
  drop  : ∀ {k r} → (∀ n → Agree n e (skip k r)) → (∀ n → Agree n (force r) e′) → Drops e e′
  drops : ∀ {k r} → (∀ n → Agree n e (skip k r)) → Drops (force r) e′ → Drops e e′

-- And with its tail: each skip at a position `P` holds of.
data Dropsˢ {A : Set} (P : Pos → Set) (h h′ : Events∞ A) : Set where
  dropˢ  : ∀ {k r} → P k → (∀ n → Agree n (force h) (skip k r)) → r ≋ h′ → Dropsˢ P h h′
  dropsˢ : ∀ {k r} → P k → (∀ n → Agree n (force h) (skip k r)) → Dropsˢ P r h′ → Dropsˢ P h h′

-- A skip alike past it.
skip-≋ : ∀ {A k} {r r′ : Events∞ A} → r ≋ r′ → ∀ n → Agree n (skip k r) (skip k r′)
skip-≋ x zero    = stop
skip-≋ x (suc n) = skip⁼ (cutˢ (x n)) (nowˢ (x n))

-- The positions a skip at `P` puts under itself.
Under : (Pos → Set) → Pos → Set
Under P k′ = Σ Pos λ k → P k × Σ Pos λ y → k′ ≡ k ++ y

-- Where a source's next step shows, if it has one.
shown : ∀ {A} → Events A → Maybe Pos
shown hush = nothing
shown e    = just (shownAt e)

------------------------------------------------------------------------
-- What each frame asks of the skips it passes

-- The body fed the run and the body fed the rest: alike, or the one past
-- its leading skips, each under one of the source's.
Fed : ∀ {B} → (Pos → Set) → Events∞ B → Events∞ B → Set
Fed P β β′ = β ≋ β′ ⊎ Dropsˢ (Under P) β β′

mutual
  Pass : ∀ {R Γ A} → (Pos → Set) → Ctx R Γ A → Bool → Events∞ A → Events∞ A → Set
  Pass P top                               f h h′ = ⊤
  Pass P (inMap g c)                       f h h′ = Pass P c true (mapped g h) (mapped g h′)
  Pass P (inScan g z c)                    f h h′ = Pass P c true (scanned g z h) (scanned g z h′)
  Pass P (inCut true a c)                  f h h′ = Pass P c true h h′
  Pass P (inCut false a c)                 f h h′ = ⊥
  Pass P (inLn b c)                        f h h′ = Pass P c b h h′
  Pass P (inTake i q free c)               f h h′ = Pass P c true (took i q h) (took i q h′)
  Pass P (inTake i q (cpAt _) c)           f h h′ = ⊥
  Pass P (inTake i q (cutAt _) c)          f h h′ = ⊥
  Pass P (inTake i q (overAt _) c)         f h h′ = ⊥
  Pass P (inOuter op g true n q ls c)      f h h′ = ⊥
  Pass P (inOuter op g false n q ls c)     f h h′ =
    (∀ k → P k → All (λ l → After k (head (force l))) (states (lanesL ls) (envAt c)) × TailNotBefore k (poolT (deadL ls) (envAt c)))
    × Pass P c true (outerFrame op (lane g) false q (lanesL ls) (deadL ls) (envAt c) h) (outerFrame op (lane g) false q (lanesL ls) (deadL ls) (envAt c) h′)
  Pass P (inLanes op g d n q o pre post c) false h h′ = ⊥
  Pass P (inLanes op g d n q o pre post c) true  h h′ =
    (∀ k → P k → First k (outerᴺ (lane g) (outerG d (gh o)) (envAt c)) (states (lanesL post) (envAt c)) (states (lanesL (reverse pre)) (envAt c))
                     (outerT d (gh o) (envAt c) (poolRuns (reverse pre) post true (envAt c) h)))
    × Pass P c true (lanesFrame op (lane g) d q (gh o) (reverse pre) post true (envAt c) h)
                    (lanesFrame op (lane g) d q (gh o) (reverse pre) post true (envAt c) h′)
  Pass P (inSrc (cs false true sa ba as nothing r en) b c) f h h′ =
    SrcPass P (stateᴺ (gh b) (force h ∷ᴬ envAt c)) (stateᴺ (gh b) (force h′ ∷ᴬ envAt c)) h′
    × Pass (Under P) c true (connSrc false r en (gh b) (envAt c) h) (connSrc false r en (gh b) (envAt c) h′)
  Pass P (inSrc (cs false true sa ba as (just _) r en) b c) f h h′ = ⊥
  Pass P (inSrc (cs false false sa ba as ow r en) b c)      f h h′ = ⊥
  Pass P (inSrc (cs true sl sa ba as ow r en) b c)          f h h′ = ⊥
  Pass P (inBody (cs cl true sa ba as nothing r en) o c)    f h h′ =
    (∀ k → P k → NotBefore k (shown (force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))))
    × Pass P c true (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h)
                    (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h′)
  Pass P (inBody (cs cl true sa ba as (just _) r en) o c)   f h h′ = ⊥
  Pass P (inBody (cs cl false sa ba as ow r en) o c)        f h h′ = ⊥

  -- A source's skips pass its connect: the body drops what its joiners
  -- saw of them, and what the source and the body run next is later.
  record SrcPass {X B} (P : Pos → Set) (β β′ : Events∞ B) (h′ : Events∞ X) : Set where
    inductive
    field
      fed   : Fed P β β′
      srcOn : ∀ k → P k → After k (head (force h′))
      bodyOn : ∀ k → P k → After k (head (force β′))

------------------------------------------------------------------------
-- Each frame passes the skips

private
  -- A run as its next skip, its tail kept.
  skipped : ∀ {A} → Pos → Events∞ A → Events∞ A → Events∞ A
  skipped k r h .force = skip k r
  skipped k r h .cut   = cut h

  skipped-≋ : ∀ {A k} {r h : Events∞ A} → (∀ n → Agree n (force h) (skip k r)) → h ≋ skipped k r h
  skipped-≋ {h = h} ag n = agreeᵀ-refl n (cut h) ,ˢ ag n

mapped-drops : ∀ {A B P} (g : A → B) {h h′ : Events∞ A} → Dropsˢ P h h′ → Dropsˢ P (mapped g h) (mapped g h′)
mapped-drops g (dropˢ {r = r} pk ag x) =
  dropˢ {r = (mapped g r)} pk (λ n → agree-trans {y = M′.mapᴱ g (skip _ r)} (mapᴱ-ne g (ag n)) (skip-≋ (≋-by refl refl) n)) (λ n → cutˢ (x n) ,ˢ mapᴱ-ne g (nowˢ (x n)))
mapped-drops g (dropsˢ {r = r} pk ag d) =
  dropsˢ {r = (mapped g r)} pk (λ n → agree-trans {y = M′.mapᴱ g (skip _ r)} (mapᴱ-ne g (ag n)) (skip-≋ (≋-by refl refl) n)) (mapped-drops g d)

scanned-drops : ∀ {A B P} (g : B → A → B) z {h h′ : Events∞ A} → Dropsˢ P h h′ → Dropsˢ P (scanned g z h) (scanned g z h′)
scanned-drops g z (dropˢ {r = r} pk ag x) =
  dropˢ {r = (scanned g z r)} pk (λ n → agree-trans {y = M′.scanᴱ g z (skip _ r)} (scanᴱ-ne g z (ag n)) (skip-≋ (≋-by refl refl) n)) (λ n → cutˢ (x n) ,ˢ scanᴱ-ne g z (nowˢ (x n)))
scanned-drops g z (dropsˢ {r = r} pk ag d) =
  dropsˢ {r = (scanned g z r)} pk (λ n → agree-trans {y = M′.scanᴱ g z (skip _ r)} (scanᴱ-ne g z (ag n)) (skip-≋ (≋-by refl refl) n)) (scanned-drops g z d)

took-drops : ∀ {A P} i (q : A → Bool) {h h′ : Events∞ A} → Dropsˢ P h h′ → Dropsˢ P (took i q h) (took i q h′)
took-drops i q (dropˢ {r = r} pk ag x) =
  dropˢ {r = (took i q r)} pk (λ n → agree-trans {y = M′.takeWhileᴱ i q (skip _ r)} (takeWhileᴱ-ne i q (ag n)) (skip-≋ (≋-by refl refl) n)) (λ n → cutˢ (x n) ,ˢ takeWhileᴱ-ne i q (nowˢ (x n)))
took-drops i q (dropsˢ {r = r} pk ag d) =
  dropsˢ {r = (took i q r)} pk (λ n → agree-trans {y = M′.takeWhileᴱ i q (skip _ r)} (takeWhileᴱ-ne i q (ag n)) (skip-≋ (≋-by refl refl) n)) (took-drops i q d)

-- The lane's skip, first: the merge's next, the lane's rest in its place.
at-skip : ∀ {Γ A B} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) {h r : Events∞ B} {k}
        → First k (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ) (outerT d o ρ (poolRuns pre post true ρ h))
        → (∀ n → Agree n (force h) (skip k r))
        → ∀ n → Agree n (force (lanesFrame op g d q o pre post true ρ h)) (skip k (lanesFrame op g d q o pre post true ρ r))
at-skip op g d q o pre post ρ {h} {r} {k} fi ag n =
  agree-trans (nowˢ (lanesFrame-ne op g d q o pre post true ρ (skipped-≋ {r = r} {h = h} ag n)))
    (subst (λ x → Agree n x (skip k (lanesFrame op g d q o pre post true ρ r)))
      (sym (go-rise (flatOp op) (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (skipped k r h) (states (lanesL pre) ρ) (L.map (laneᴹ g ρ) q)
             (outerT d o ρ (poolRuns pre post true ρ h)) refl fi))
      (skip-≋ (≋-by refl refl) n))

-- A lane first among its flatMap's parts passes its skips.
lanes-drops : ∀ {Γ A B P} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) {h h′ : Events∞ B}
            → (∀ k → P k → First k (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ) (outerT d o ρ (poolRuns pre post true ρ h)))
            → Dropsˢ P h h′ → Dropsˢ P (lanesFrame op g d q o pre post true ρ h) (lanesFrame op g d q o pre post true ρ h′)
lanes-drops op g d q o pre post ρ {h} fi (dropˢ {k} {r} pk ag x) =
  dropˢ pk (at-skip op g d q o pre post ρ (fi k pk) ag) (λ n → lanesFrame-ne op g d q o pre post true ρ (x n))
lanes-drops op g d q o pre post ρ {h} fi (dropsˢ {k} {r} pk ag e) =
  dropsˢ pk (at-skip op g d q o pre post ρ (fi k pk) ag) (lanes-drops op g d q o pre post ρ fi e)

postulate
  -- THE OUTER FIRST: an outer whose skips come before every lane's next
  -- and every tail its ended parts left passes them.
  outer-drops : ∀ {Γ A B P} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A}
              → (∀ k → P k → All (λ l → After k (head (force l))) (states ls ρ) × TailNotBefore k (poolT ds ρ))
              → Dropsˢ P h h′ → Dropsˢ P (outerFrame op g false q ls ds ρ h) (outerFrame op g false q ls ds ρ h′)
  -- A SOURCE'S SKIPS AND ITS JOINERS': each source skip shows just past
  -- itself, each joiner's image of it under it, and what follows is
  -- later; so the connect drops them all, leading.
  src-drops : ∀ {Γ X B P} r en (b : Node (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
            → SrcPass P (stateᴺ b (force h ∷ᴬ ρ)) (stateᴺ b (force h′ ∷ᴬ ρ)) h′
            → Dropsˢ P h h′ → Dropsˢ (Under P) (connSrc false r en b ρ h) (connSrc false r en b ρ h′)
  -- A BODY'S SKIPS, THE SOURCE'S NEXT NO EARLIER: the body's skips pass.
  body-drops : ∀ {X B P} r (σ : Events∞ X) {h h′ : Events∞ B}
             → (∀ k → P k → NotBefore k (shown (force σ)))
             → Dropsˢ P h h′ → Dropsˢ P (bodyConn r σ h) (bodyConn r σ h′)

------------------------------------------------------------------------
-- Up to the root

top-drops : ∀ {A P} {h h′ : Events∞ A} → Dropsˢ P h h′ → Drops (force h) (force h′)
top-drops (dropˢ pk ag x)  = drop ag (λ n → nowˢ (x n))
top-drops (dropsˢ pk ag d) = drops ag (top-drops d)

-- THE LIFT: skips dropped at the hole, each passed by every frame above,
-- are dropped at the root.
lift-drops : ∀ {R Γ A} P (c : Ctx R Γ A) f {h h′ : Events∞ A} → Dropsˢ P h h′ → Pass P c f h h′ → Drops (up c f h) (up c f h′)
lift-drops P top                               f d ps       = top-drops d
lift-drops P (inMap g c)                       f d ps       = lift-drops P c true (mapped-drops g d) ps
lift-drops P (inScan g z c)                    f d ps       = lift-drops P c true (scanned-drops g z d) ps
lift-drops P (inCut true a c)                  f d ps       = lift-drops P c true d ps
lift-drops P (inLn b c)                        f d ps       = lift-drops P c b d ps
lift-drops P (inTake i q free c)               f d ps       = lift-drops P c true (took-drops i q d) ps
lift-drops P (inOuter op g false n q ls c)     f d (o , ps) =
  lift-drops P c true (outer-drops op (lane g) q (lanesL ls) (deadL ls) (envAt c) o d) ps
lift-drops P (inLanes op g d′ n q o pre post c) true d (fi , ps) =
  lift-drops P c true (lanes-drops op (lane g) d′ q (gh o) (reverse pre) post (envAt c) fi d) ps
lift-drops P (inSrc (cs false true sa ba as nothing r en) b c) f d (sp , ps) =
  lift-drops (Under P) c true (src-drops r en (gh b) (envAt c) sp d) ps
lift-drops P (inBody (cs cl true sa ba as nothing r en) o c) f d (bp , ps) =
  lift-drops P c true (body-drops r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) bp d) ps
