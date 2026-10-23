{-# OPTIONS --guardedness #-}

-- SPIKE: WHAT A CONFIGURATION OF `operation.Marked` MEANS, read node by
-- node.  The ghost (`gh`) maps every stored state to the `denotation.Unfold`
-- node that runs as it does; the context, top-down, to the environment
-- its connects give the hole (`envAt`); and, bottom-up, to the stream
-- function each frame applies to the hole's run (`up`).  Nothing here
-- looks anything up: every clause reads one node or one frame.
--
-- A frame is read as `meaning` reads the node it is a hole of, with the
-- hole's run in the child's place, so a configuration focused anywhere
-- means what its whole tree means (`spike.MarkedKept.lift-plug`).
--
-- Congruence is by the existing non-expansiveness of every stream
-- function (`denotation.NonExpansive`): runs alike to every depth at the
-- hole are alike at the root (`lift-ne`), and a hole whose observer is
-- closed is read only through its tail (`closed-hides`).
module spike.MarkedGhost where

open import Data.Bool using (Bool; true; false; not; _∨_)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import Tree using (Obs; FlatOp)
open import denotation.MonotonicList.Events using (Events; Events∞; Tail; Timeline; Pos; out; skip; end; hush; idle; _∪_; ix; last)
open import denotation.MonotonicList using (MonotonicList; tailᴱ; Agree; Agreeᵀ; stop; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agree-sym; agree-trans; agreeᵀ-refl; agreeᵀ-trans; _≈[_]_; agrees)
  renaming (cold to coldᴹ)
import denotation.MonotonicList as M′
open import denotation.NonExpansive using (Agreeˢ; _,ˢ_; Lanes; []ᴸ; _∷ᴸ_; Queue; []ᑫ; _∷ᑫ_; Outerᴿ; doneᴼ; liveᴼ;
  mapᴱ-ne; scanᴱ-ne; takeWhileᴱ-ne; tailᴱ-ne; ∪-ne; burstOn-ne; beside-ne; go-ne; whole-ne; mapᴱ-neᴹ)
open Agreeˢ
open import denotation.Unfold using (Node; burstᶜ; ofᶜ; mapᶜ; scanᶜ; takeWhileᶜ; flatMapᶜ; joinᶜ; connectᶜ; endingᶜ; restᶜ; idleᶜ; unionᶜ;
  restsᶜ; Source; live; ended; subscribe; NEnv; meaning; cutᴺ; stateᴺ; states; outerᴺ)
open import denotation.Denote using (flatOp)
open import operation.MarkedPure using (Tape; play; ending; over; due)
open import operation.MarkedPure using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; closed;
  CS; cs; Owe; free; cpAt; cutAt; overAt; Ev; nx; cp; _⊕_; Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising; alive)

open Events∞

------------------------------------------------------------------------
-- The ghost

-- A started cold: the burst it plays, the completion it owes, or nothing.
tape : ∀ {Γ A} → Bool → Tape A → Node Γ A
tape b     (ending e)          = endingᶜ e idleᶜ
tape true  (play τ u i t fr)   = burstᶜ τ u i fr
tape false (play τ u i t fr)   = idleᶜ
tape b     over                = idleᶜ

-- A takeWhile running, then ending at its owed completion, then its
-- source's rest.
taken : ∀ {Γ A} → Bool → (A → Bool) → Owe → Node Γ A → Node Γ A
taken i q free      n = takeWhileᶜ i q n
taken i q (cpAt p)  n = endingᶜ (p ⊕ [ last ]) n
taken i q (cutAt p) n = restᶜ n
taken i q (overAt p) n = restᶜ n

-- A joiner's inbox: its values up to the first completion, and where that is.
vals : ∀ {A} → List (Pos × Ev A) → List (Pos × Maybe A)
vals []               = []
vals ((q , nx a) ∷ ib) = (q , just a) ∷ vals ib
vals ((q , cp) ∷ ib)   = []

endOf : ∀ {A} → List (Pos × Ev A) → Maybe Pos
endOf []                = nothing
endOf ((q , nx a) ∷ ib) = endOf ib
endOf ((q , cp) ∷ ib)   = just q

joinG : ∀ {Γ A} → Bool → A ∈ Γ → Pos → List (Pos × Ev A) → Node Γ A
joinG false x j ib = idleᶜ
joinG true  x j ib = joinᶜ x j (vals ib) (endOf ib)

-- A flatMap's outer, once done, is in its pool.
outerG : ∀ {Γ A} → Bool → Node Γ A → Maybe (Node Γ A)
outerG true  n = nothing
outerG false n = just n

poolG : ∀ {Γ A B} → Bool → Node Γ A → List (Node Γ B) → Node Γ B
poolG false n ds = restsᶜ ds
poolG true  n ds = unionᶜ (restᶜ n) (restsᶜ ds)

-- A connect that completed is its rest.
doneG : ∀ {Γ A} → Maybe Pos → Bool → Node Γ A → Node Γ A
doneG (just _) l     n = restᶜ n
doneG nothing  false n = restᶜ n
doneG nothing  true  n = n

lane : ∀ {Γ} {A : Set} {B} → (A → Obs Timeline Γ B) → A → Pos → Node Γ B
lane f a r = subscribe (f a) r

mutual
  gh : ∀ {Γ A} → St Γ A → Node Γ A
  gh (pend o)                = idleᶜ
  gh (coldS b l)             = tape b l
  gh (ofS i p xs)            = ofᶜ p i xs
  gh doneS                   = idleᶜ
  gh (mapS f s)              = mapᶜ f (gh s)
  gh (scanS f z s)           = scanᶜ f z (gh s)
  gh (cutS true a s)         = gh s
  gh (cutS false a s)        = restᶜ (gh s)
  gh (lnS b s)               = gh s
  gh (takeS i q w s)         = taken i q w (gh s)
  gh (flatS op f d n q o ls) = flatMapᶜ op (lane f) (outerG d (gh o)) (lanesL ls) q (poolG d (gh o) (deadL ls))
  gh (connS k o b)           = doneG (CS.owedAt k) (CS.srcLive k) (connectᶜ (CS.srcAt k) (gh b) (srcOf (CS.bodyAt k) (CS.closed k) (CS.endAt k) o))
  gh (joinS j g x ib)        = joinG g x j ib

  -- A node about to be subscribed at `p`, as `Unfold` subscribes it; else
  -- its ghost.
  subOr : ∀ {Γ A} → Pos → St Γ A → Node Γ A
  subOr p (pend o) = subscribe o p
  subOr p s        = gh s

  -- A connect's source: subscribed at the body's mark, running, or ended.
  srcOf : ∀ {Γ X} → Maybe Pos → Bool → Pos → St Γ X → Source Γ X
  srcOf (just p) c     e o = live (subOr (p ⊕ [ ix 1 ]) o)
  srcOf nothing  false e o = live (gh o)
  srcOf nothing  true  e o = ended e (restᶜ (gh o))

  -- The lanes still in the list, newest first, as `Unfold.admit` keeps them.
  lanesL : ∀ {Γ B} → List (St Γ B) → List (Node Γ B)
  lanesL []       = []
  lanesL (s ∷ ls) = lanesL ls ++ liveL s

  -- A slot is live unless it is a lane taken out of the list.
  liveL : ∀ {Γ B} → St Γ B → List (Node Γ B)
  liveL (lnS false s) = []
  liveL s             = [ gh s ]

  -- The lanes ended or dropped, oldest first: the pool's rests.
  deadL : ∀ {Γ B} → List (St Γ B) → List (Node Γ B)
  deadL []       = []
  deadL (s ∷ ls) = deadOne s ++ deadL ls

  deadOne : ∀ {Γ B} → St Γ B → List (Node Γ B)
  deadOne (lnS false s) = [ gh s ]
  deadOne s             = []

------------------------------------------------------------------------
-- What a connect's source shows its body, and runs beside it

srcG : ∀ {Γ X} → CS → St Γ X → Source Γ X
srcG k o = srcOf (CS.bodyAt k) (CS.closed k) (CS.endAt k) o

srcRun : ∀ {Γ X} → Source Γ X → NEnv Γ → Events X
srcRun (live s)    ρ = meaning s ρ
srcRun (ended e t) ρ = end e

srcState : ∀ {Γ X} → Source Γ X → NEnv Γ → Events∞ X
srcState (live s)    ρ = stateᴺ s ρ
srcState (ended e t) ρ = stateᴺ t ρ

-- The environment a hole's connects give it, top-down.
envAt : ∀ {R Γ A} → Ctx R Γ A → NEnv Γ
envAt top                               = []ᴬ
envAt (inMap f c)                       = envAt c
envAt (inScan f z c)                    = envAt c
envAt (inCut l a c)                     = envAt c
envAt (inLn b c)                        = envAt c
envAt (inTake i q w c)                  = envAt c
envAt (inOuter op f d n q ls c)         = envAt c
envAt (inLanes op f d n q o pre post c) = envAt c
envAt (inSrc k b c)                     = envAt c
envAt (inBody k o c)                    = srcRun (srcG k o) (envAt c) ∷ᴬ envAt c

------------------------------------------------------------------------
-- Each frame, as `meaning` reads the node it is a hole of

mapped : ∀ {A B} → (A → B) → Events∞ A → Events∞ B
mapped f h .force = M′.mapᴱ f (force h)
mapped f h .cut   = cut h

scanned : ∀ {A B} → (B → A → B) → B → Events∞ A → Events∞ B
scanned f z h .force = M′.scanᴱ f z (force h)
scanned f z h .cut   = cut h

took : ∀ {A} → Bool → (A → Bool) → Events∞ A → Events∞ A
took i q h .force = M′.takeWhileᴱ i q (force h)
took i q h .cut   = cut h

-- A part run as its tail alone.
rested : ∀ {A B} → Events∞ A → Events∞ B
rested h .force = tailᴱ (cut h)
rested h .cut   = cut h

endingAt : ∀ {A} → Pos → Events∞ A → Events∞ A
endingAt e h .force = end e
endingAt e h .cut   = cut h

switched : ∀ {A} → Bool → Events∞ A → Events∞ A
switched true  h = h
switched false h = rested h

taking∞ : ∀ {A} → Bool → (A → Bool) → Owe → Events∞ A → Events∞ A
taking∞ i q free       h = took i q h
taking∞ i q (cpAt p)   h = endingAt (p ⊕ [ last ]) h
taking∞ i q (cutAt p)  h = rested h
taking∞ i q (overAt p) h = rested h

doneE : ∀ {A} → Maybe Pos → Bool → Events∞ A → Events∞ A
doneE (just _) l     h = rested h
doneE nothing  false h = rested h
doneE nothing  true  h = h

laneᴹ : ∀ {Γ} {A : Set} {B} → (A → Pos → Node Γ B) → NEnv Γ → A → MonotonicList B
laneᴹ g ρ a = coldᴹ λ q → stateᴺ (g a q) ρ

outerOf : ∀ {Γ A B} → (A → Pos → Node Γ B) → NEnv Γ → Events∞ A → Events∞ (MonotonicList B)
outerOf g ρ h .force = M′.mapᴱ (laneᴹ g ρ) (force h)
outerOf g ρ h .cut   = cut h

-- What a pool's rests leave running.
poolT : ∀ {Γ B} → List (Node Γ B) → NEnv Γ → Tail
poolT {B = B} ds ρ = cutᴺ (restsᶜ {B = B} ds) ρ

-- The hole a flatMap's outer: running, else done and in the pool.
outerFrame : ∀ {Γ A B} → FlatOp → (A → Pos → Node Γ B) → Bool → List A → List (Node Γ B) → List (Node Γ B) → NEnv Γ
           → Events∞ A → Events∞ B
outerFrame op g false q ls ds ρ h .force = M′.go (flatOp op) (just (outerOf g ρ h)) (states ls ρ) (L.map (laneᴹ g ρ) q) (poolT ds ρ)
outerFrame op g false q ls ds ρ h .cut   = M′.whole (just (outerOf g ρ h)) (states ls ρ) (poolT ds ρ)
outerFrame op g true  q ls ds ρ h .force = M′.go (flatOp op) nothing (states ls ρ) (L.map (laneᴹ g ρ) q) (cut h ∪ poolT ds ρ)
outerFrame op g true  q ls ds ρ h .cut   = M′.whole nothing (states ls ρ) (cut h ∪ poolT ds ρ)

-- The hole a lane: in the list while live, else in the pool.
holeL : ∀ {A} → Bool → Events∞ A → List (Events∞ A)
holeL true  h = [ h ]
holeL false h = []

holeT : ∀ {A} → Bool → Events∞ A → Tail
holeT true  h = idle
holeT false h = cut h

outerT : ∀ {Γ A} → Bool → Node Γ A → NEnv Γ → Tail → Tail
outerT false n ρ t = t
outerT true  n ρ t = cutᴺ n ρ ∪ t

laneRuns : ∀ {Γ B} → List (St Γ B) → List (St Γ B) → Bool → NEnv Γ → Events∞ B → List (Events∞ B)
laneRuns pre post f ρ h = states (lanesL post) ρ ++ holeL f h ++ states (lanesL pre) ρ

-- Tails run before one, in the order a pool's rests run them.
tailsOn : ∀ {Γ B} → List (Node Γ B) → NEnv Γ → Tail → Tail
tailsOn []       ρ t = t
tailsOn (d ∷ ds) ρ t = cutᴺ d ρ ∪ tailsOn ds ρ t

poolRuns : ∀ {Γ B} → List (St Γ B) → List (St Γ B) → Bool → NEnv Γ → Events∞ B → Tail
poolRuns pre post f ρ h = tailsOn (deadL pre) ρ (holeT f h ∪ poolT (deadL post) ρ)

lanesFrame : ∀ {Γ A B} → FlatOp → (A → Pos → Node Γ B) → Bool → List A → Node Γ A → List (St Γ B) → List (St Γ B) → Bool → NEnv Γ
           → Events∞ B → Events∞ B
lanesFrame op g d q o pre post f ρ h .force =
  M′.go (flatOp op) (outerᴺ g (outerG d o) ρ) (laneRuns pre post f ρ h) (L.map (laneᴹ g ρ) q) (outerT d o ρ (poolRuns pre post f ρ h))
lanesFrame op g d q o pre post f ρ h .cut   =
  M′.whole (outerᴺ g (outerG d o) ρ) (laneRuns pre post f ρ h) (outerT d o ρ (poolRuns pre post f ρ h))

-- The hole a connect's source: its body over it, running or ended.
connSrc : ∀ {Γ X B} → Bool → Pos → Pos → Node (X ∷ Γ) B → NEnv Γ → Events∞ X → Events∞ B
connSrc false r e b ρ h .force = M′.beside r (stateᴺ b (force h ∷ᴬ ρ)) h
connSrc false r e b ρ h .cut   = M′.burstOn r h ∪ cutᴺ b (force h ∷ᴬ ρ)
connSrc {X = X} true r e b ρ h .force = M′.beside r (stateᴺ b (end e ∷ᴬ ρ)) (rested {B = X} h)
connSrc {X = X} true r e b ρ h .cut = M′.burstOn r (rested {B = X} h) ∪ cutᴺ b (end e ∷ᴬ ρ)

srcFrame : ∀ {Γ X B} → CS → Node (X ∷ Γ) B → NEnv Γ → Events∞ X → Events∞ B
srcFrame k b ρ h = doneE (CS.owedAt k) (CS.srcLive k) (connSrc (CS.closed k) (CS.srcAt k) (CS.endAt k) b ρ h)

-- The hole a connect's body, its source beside it.
bodyConn : ∀ {X B} → Pos → Events∞ X → Events∞ B → Events∞ B
bodyConn r σ h .force = M′.beside r h σ
bodyConn r σ h .cut   = M′.burstOn r σ ∪ cut h

bodyFrame : ∀ {Γ X B} → CS → St Γ X → NEnv Γ → Events∞ B → Events∞ B
bodyFrame k o ρ h = doneE (CS.owedAt k) (CS.srcLive k) (bodyConn (CS.srcAt k) (srcState (srcG k o) ρ) h)

-- The hole's run carried to the root.  The flag says whether a lane is
-- still in its flatMap's list; only a lane's parent reads it.
up : ∀ {R Γ A} → Ctx R Γ A → Bool → Events∞ A → Events R
up top                               f h = force h
up (inMap g c)                       f h = up c true (mapped g h)
up (inScan g z c)                    f h = up c true (scanned g z h)
up (inCut l a c)                     f h = up c true (switched l h)
up (inLn b c)                        f h = up c b h
up (inTake i q w c)                  f h = up c true (taking∞ i q w h)
up (inOuter op g d n q ls c)         f h = up c true (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h)
up (inLanes op g d n q o pre post c) f h = up c true (lanesFrame op (lane g) d q (gh o) pre post f (envAt c) h)
up (inSrc k b c)                     f h = up c true (srcFrame k (gh b) (envAt c) h)
up (inBody k o c)                    f h = up c true (bodyFrame k o (envAt c) h)

------------------------------------------------------------------------
-- What a configuration means

-- A rise's event, then the node after it.
risen : ∀ {Γ A} → Node Γ A → NEnv Γ → Ev A → Pos → Events∞ A
risen n ρ (nx a) p .force = out p a (stateᴺ n ρ)
risen n ρ (nx a) p .cut   = cutᴺ n ρ
risen n ρ cp     p .force = end p
risen n ρ cp     p .cut   = cutᴺ n ρ

hole : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Mode A → Pos → Events∞ A
hole c s subscribing p = stateᴺ (subOr p s) (envAt c)
hole c s absorbed    p = stateᴺ (gh s) (envAt c)
hole c s (rising e)  p = risen (gh s) (envAt c) e p

flagOf : ∀ {Γ A} → St Γ A → Bool
flagOf s = alive s

M : ∀ {R} → Conf R → Events R
M ⟨ c , s , m , p ⟩ = up c (flagOf s) (hole c s m p)

------------------------------------------------------------------------
-- What a run shows, and runs alike

data Has {A : Set} : Events A → Pos → Maybe A → Set where
  atOut    : ∀ {k a r} → Has (out k a r) k (just a)
  atEnd    : ∀ {k} → Has (end k) k nothing
  pastOut  : ∀ {k a r q b} → Has (force r) q b → Has (out k a r) q b
  pastSkip : ∀ {k r q b} → Has (force r) q b → Has (skip k r) q b

infix 4 _≅_ _≋_

-- Showing the same values and completion at the same positions.
_≅_ : ∀ {A} → Events A → Events A → Set
x ≅ y = (∀ {k b} → Has x k b → Has y k b) × (∀ {k b} → Has y k b → Has x k b)

≅-refl : ∀ {A} {x : Events A} → x ≅ x
≅-refl = (λ h → h) , (λ h → h)

≅-sym : ∀ {A} {x y : Events A} → x ≅ y → y ≅ x
≅-sym (f , g) = g , f

≅-trans : ∀ {A} {x y z : Events A} → x ≅ y → y ≅ z → x ≅ z
≅-trans (f , g) (f′ , g′) = (λ h → f′ (f h)) , (λ h → g (g′ h))

-- States alike to every depth.
_≋_ : ∀ {A} → Events∞ A → Events∞ A → Set
h ≋ h′ = ∀ n → Agreeˢ n h h′

private
  size : ∀ {A} {x : Events A} {k b} → Has x k b → ℕ
  size atOut        = zero
  size atEnd        = zero
  size (pastOut h)  = suc (size h)
  size (pastSkip h) = suc (size h)

  has-n : ∀ {A} {x y : Events A} {k b} (h : Has x k b) → Agree (suc (size h)) x y → Has y k b
  has-n atOut        (out⁼ _ _)  = atOut
  has-n atEnd        end⁼        = atEnd
  has-n (pastOut h)  (out⁼ _ r)  = pastOut (has-n h r)
  has-n (pastSkip h) (skip⁼ _ r) = pastSkip (has-n h r)

has-agree : ∀ {A} {x y : Events A} → (∀ n → Agree n x y) → ∀ {k b} → Has x k b → Has y k b
has-agree a h = has-n h (a (suc (size h)))

agree-≅ : ∀ {A} {x y : Events A} → (∀ n → Agree n x y) → x ≅ y
agree-≅ a = has-agree a , has-agree (λ n → agree-sym (a n))

-- Alike by definition: the same next event and the same tail.
≋-by : ∀ {A} {h h′ : Events∞ A} → force h ≡ force h′ → cut h ≡ cut h′ → h ≋ h′
≋-by {h = h} e t n = subst (λ x → Agreeᵀ n (cut h) x) t (agreeᵀ-refl n _) ,ˢ subst (λ x → Agree n (force h) x) e (agree-refl n _)

-- The same value at the same position, then alike by definition.
≋-out : ∀ {A} {h h′ : Events∞ A} {p a r r′} → force h ≡ out p a r → force h′ ≡ out p a r′ → force r ≡ force r′ → cut r ≡ cut r′
      → cut h ≡ cut h′ → h ≋ h′
≋-out {h = h} {h′} {p} {a} {r} {r′} e e′ f t u n = subst (λ x → Agreeᵀ n (cut h) x) u (agreeᵀ-refl n _) ,ˢ
  subst (λ x → Agree n x (force h′)) (sym e) (subst (λ x → Agree n (out p a r) x) (sym e′) (outs n))
  where
    outs : ∀ m → Agree m (out p a r) (out p a r′)
    outs zero    = stop
    outs (suc m) = out⁼ (subst (λ x → Agreeᵀ m (cut r) x) t (agreeᵀ-refl m _)) (subst (λ x → Agree m (force r) x) f (agree-refl m _))

-- Alike, then the same by definition.
≋-trans : ∀ {A} {h h′ h″ : Events∞ A} → h ≋ h′ → h′ ≋ h″ → h ≋ h″
≋-trans x y n = agreeᵀ-trans (cutˢ (x n)) (cutˢ (y n)) ,ˢ agree-trans (nowˢ (x n)) (nowˢ (y n))

≋-tr : ∀ {A} {h h′ h″ : Events∞ A} → h ≋ h′ → force h′ ≡ force h″ → cut h′ ≡ cut h″ → h ≋ h″
≋-tr {h = h} x e t n = subst (Agreeᵀ n (cut h)) t (cutˢ (x n)) ,ˢ subst (Agree n (force h)) e (nowˢ (x n))

------------------------------------------------------------------------
-- Congruence, frame by frame

-- A body's meaning reads its source's run no deeper than it is alike.
postulate
  env-ne : ∀ {Γ X B n} (b : Node (X ∷ Γ) B) (ρ : NEnv Γ) {e e′ : Events X} → Agree n e e′
         → Agreeˢ n (stateᴺ b (e ∷ᴬ ρ)) (stateᴺ b (e′ ∷ᴬ ρ))

≈-refl : ∀ {B n} (x : MonotonicList B) → x ≈[ n ] x
≈-refl x = agrees (λ p → agreeᵀ-refl _ _) (λ p → agree-refl _ _)

same : ∀ {A} n (h : Events∞ A) → Agreeˢ n h h
same n h = agreeᵀ-refl n _ ,ˢ agree-refl n _

lanes-refl : ∀ {B} n (ls : List (Events∞ B)) → Lanes n ls ls
lanes-refl n []       = []ᴸ
lanes-refl n (l ∷ ls) = same n l ∷ᴸ lanes-refl n ls

queue-refl : ∀ {B} n (qs : List (MonotonicList B)) → Queue n qs qs
queue-refl n []       = []ᑫ
queue-refl n (q ∷ qs) = ≈-refl q ∷ᑫ queue-refl n qs

lanes-++ : ∀ {B n} {as as′ bs bs′ : List (Events∞ B)} → Lanes n as as′ → Lanes n bs bs′ → Lanes n (as ++ bs) (as′ ++ bs′)
lanes-++ []ᴸ      l = l
lanes-++ (x ∷ᴸ a) l = x ∷ᴸ lanes-++ a l

outer-refl : ∀ {Γ A B} n (g : A → Pos → Node Γ B) (mo : Maybe (Node Γ A)) (ρ : NEnv Γ) → Outerᴿ n (outerᴺ g mo ρ) (outerᴺ g mo ρ)
outer-refl n g nothing  ρ = doneᴼ
outer-refl n g (just o) ρ = liveᴼ (agreeᵀ-refl n _) (mapᴱ-neᴹ (λ a → ≈-refl _) (agree-refl n _))

-- What reads a run's tail alone takes the runs, which a tail does not name.
rested-ne : ∀ {A B n} (h h′ : Events∞ A) → Agreeᵀ n (cut h) (cut h′) → Agreeˢ n (rested {B = B} h) (rested h′)
rested-ne h h′ t = t ,ˢ tailᴱ-ne t

switched-ne : ∀ {A n} l {h h′ : Events∞ A} → Agreeˢ n h h′ → Agreeˢ n (switched l h) (switched l h′)
switched-ne true          x = x
switched-ne false {h} {h′} x = rested-ne h h′ (cutˢ x)

taking∞-ne : ∀ {A n} i (q : A → Bool) w {h h′ : Events∞ A} → Agreeˢ n h h′ → Agreeˢ n (taking∞ i q w h) (taking∞ i q w h′)
taking∞-ne {n = n} i q free                (t ,ˢ a) = t ,ˢ takeWhileᴱ-ne i q a
taking∞-ne {n = n} i q (cpAt p)            (t ,ˢ a) = t ,ˢ agree-refl n _
taking∞-ne {n = n} i q (cutAt p)  {h} {h′} (t ,ˢ a) = rested-ne h h′ t
taking∞-ne {n = n} i q (overAt p) {h} {h′} (t ,ˢ a) = rested-ne h h′ t

taking∞-cut : ∀ {A n} i (q : A → Bool) w (h h′ : Events∞ A) → Agreeᵀ n (cut h) (cut h′) → Agreeᵀ n (cut (taking∞ i q w h)) (cut (taking∞ i q w h′))
taking∞-cut i q free       h h′ t = t
taking∞-cut i q (cpAt p)   h h′ t = t
taking∞-cut i q (cutAt p)  h h′ t = t
taking∞-cut i q (overAt p) h h′ t = t

doneE-ne : ∀ {A n} mo l {h h′ : Events∞ A} → Agreeˢ n h h′ → Agreeˢ n (doneE mo l h) (doneE mo l h′)
doneE-ne (just _) l     {h} {h′} x = rested-ne h h′ (cutˢ x)
doneE-ne nothing  false {h} {h′} x = rested-ne h h′ (cutˢ x)
doneE-ne nothing  true           x = x

doneE-cut : ∀ {A n} mo l (h h′ : Events∞ A) → Agreeᵀ n (cut h) (cut h′) → Agreeᵀ n (cut (doneE mo l h)) (cut (doneE mo l h′))
doneE-cut (just _) l     h h′ t = t
doneE-cut nothing  false h h′ t = t
doneE-cut nothing  true  h h′ t = t

outerFrame-ne : ∀ {Γ A B n} op (g : A → Pos → Node Γ B) d q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A} → Agreeˢ n h h′
              → Agreeˢ n (outerFrame op g d q ls ds ρ h) (outerFrame op g d q ls ds ρ h′)
outerFrame-ne {n = n} op g false q ls ds ρ {h} {h′} (t ,ˢ a) =
  whole-ne (liveᴼ {e = outerOf g ρ h} {outerOf g ρ h′} t (mapᴱ-neᴹ (λ x → ≈-refl (laneᴹ g ρ x)) a)) (lanes-refl n (states ls ρ)) (agreeᵀ-refl n (poolT ds ρ)) ,ˢ
  go-ne (flatOp op) (liveᴼ {e = outerOf g ρ h} {outerOf g ρ h′} t (mapᴱ-neᴹ (λ x → ≈-refl (laneᴹ g ρ x)) a)) (lanes-refl n (states ls ρ)) (queue-refl n (L.map (laneᴹ g ρ) q))
    (agreeᵀ-refl n (poolT ds ρ))
outerFrame-ne {n = n} op g true  q ls ds ρ (t ,ˢ a) =
  whole-ne doneᴼ (lanes-refl n (states ls ρ)) (∪-ne t (agreeᵀ-refl n (poolT ds ρ))) ,ˢ
  go-ne (flatOp op) doneᴼ (lanes-refl n (states ls ρ)) (queue-refl n (L.map (laneᴹ g ρ) q)) (∪-ne t (agreeᵀ-refl n (poolT ds ρ)))

outerFrame-cut : ∀ {Γ A B n} op (g : A → Pos → Node Γ B) d q ls ds (ρ : NEnv Γ) (h h′ : Events∞ A) → Agreeᵀ n (cut h) (cut h′)
               → Agreeᵀ n (cut (outerFrame op g d q ls ds ρ h)) (cut (outerFrame op g d q ls ds ρ h′))
outerFrame-cut {n = n} op g false q ls ds ρ h h′ t = ∪-ne t (agreeᵀ-refl n (M′.cuts (states ls ρ) ∪ poolT ds ρ))
outerFrame-cut {n = n} op g true  q ls ds ρ h h′ t =
  ∪-ne (agreeᵀ-refl n idle) (∪-ne (agreeᵀ-refl n (M′.cuts (states ls ρ))) (∪-ne t (agreeᵀ-refl n (poolT ds ρ))))

holeL-ne : ∀ {A n} f {h h′ : Events∞ A} → Agreeˢ n h h′ → Lanes n (holeL f h) (holeL f h′)
holeL-ne true  x = x ∷ᴸ []ᴸ
holeL-ne false x = []ᴸ

holeT-cut : ∀ {A n} f (h h′ : Events∞ A) → Agreeᵀ n (cut h) (cut h′) → Agreeᵀ n (holeT f h) (holeT f h′)
holeT-cut true  h h′ t = agreeᵀ-refl _ idle
holeT-cut false h h′ t = t

outerT-ne : ∀ {Γ A n} d (o : Node Γ A) (ρ : NEnv Γ) {t t′} → Agreeᵀ n t t′ → Agreeᵀ n (outerT d o ρ t) (outerT d o ρ t′)
outerT-ne false o ρ x = x
outerT-ne true  o ρ x = ∪-ne (agreeᵀ-refl _ (cutᴺ o ρ)) x

tailsOn-ne : ∀ {Γ B n} (ds : List (Node Γ B)) (ρ : NEnv Γ) {t t′} → Agreeᵀ n t t′ → Agreeᵀ n (tailsOn ds ρ t) (tailsOn ds ρ t′)
tailsOn-ne []       ρ x = x
tailsOn-ne (d ∷ ds) ρ x = ∪-ne (agreeᵀ-refl _ (cutᴺ d ρ)) (tailsOn-ne ds ρ x)

poolRuns-cut : ∀ {Γ B n} (pre post : List (St Γ B)) f (ρ : NEnv Γ) (h h′ : Events∞ B) → Agreeᵀ n (cut h) (cut h′)
             → Agreeᵀ n (poolRuns pre post f ρ h) (poolRuns pre post f ρ h′)
poolRuns-cut pre post f ρ h h′ t = tailsOn-ne (deadL pre) ρ (∪-ne (holeT-cut f h h′ t) (agreeᵀ-refl _ (poolT (deadL post) ρ)))

cuts-hole : ∀ {B n} (as : List (Events∞ B)) f bs (h h′ : Events∞ B) → Agreeᵀ n (cut h) (cut h′)
          → Agreeᵀ n (M′.cuts (as ++ holeL f h ++ bs)) (M′.cuts (as ++ holeL f h′ ++ bs))
cuts-hole []       true  bs h h′ t = ∪-ne t (agreeᵀ-refl _ (M′.cuts bs))
cuts-hole []       false bs h h′ t = agreeᵀ-refl _ (M′.cuts bs)
cuts-hole (a ∷ as) f     bs h h′ t = ∪-ne (agreeᵀ-refl _ (cut a)) (cuts-hole as f bs h h′ t)

lanesFrame-ne : ∀ {Γ A B n} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post f (ρ : NEnv Γ) {h h′ : Events∞ B} → Agreeˢ n h h′
              → Agreeˢ n (lanesFrame op g d q o pre post f ρ h) (lanesFrame op g d q o pre post f ρ h′)
lanesFrame-ne {n = n} op g d q o pre post f ρ {h} {h′} x =
  whole-ne (outer-refl n g (outerG d o) ρ) runs (outerT-ne d o ρ (poolRuns-cut pre post f ρ h h′ (cutˢ x))) ,ˢ
  go-ne (flatOp op) (outer-refl n g (outerG d o) ρ) runs (queue-refl n (L.map (laneᴹ g ρ) q)) (outerT-ne d o ρ (poolRuns-cut pre post f ρ h h′ (cutˢ x)))
  where
    runs : Lanes n (laneRuns pre post f ρ h) (laneRuns pre post f ρ h′)
    runs = lanes-++ (lanes-refl n (states (lanesL post) ρ)) (lanes-++ (holeL-ne f x) (lanes-refl n (states (lanesL pre) ρ)))

lanesFrame-cut : ∀ {Γ A B n} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post f (ρ : NEnv Γ) (h h′ : Events∞ B)
               → Agreeᵀ n (cut h) (cut h′) → Agreeᵀ n (cut (lanesFrame op g d q o pre post f ρ h)) (cut (lanesFrame op g d q o pre post f ρ h′))
lanesFrame-cut {n = n} op g d q o pre post f ρ h h′ t =
  ∪-ne (agreeᵀ-refl n (M′.cutᴼ (outerᴺ g (outerG d o) ρ)))
    (∪-ne (cuts-hole (states (lanesL post) ρ) f (states (lanesL pre) ρ) h h′ t) (outerT-ne d o ρ (poolRuns-cut pre post f ρ h h′ t)))

-- A lane out of its flatMap's list is read through its tail alone.
lanes-dead : ∀ {Γ A B} op (g : A → Pos → Node Γ B) d q (o : Node Γ A) pre post (ρ : NEnv Γ) (h h′ : Events∞ B) → cut h ≡ cut h′
           → lanesFrame op g d q o pre post false ρ h ≋ lanesFrame op g d q o pre post false ρ h′
lanes-dead op g d q o pre post ρ h h′ e =
  ≋-by (cong (λ t → M′.go (flatOp op) O Ls (L.map (laneᴹ g ρ) q) (outerT d o ρ (tailsOn (deadL pre) ρ (t ∪ poolT (deadL post) ρ)))) e)
       (cong (λ t → M′.whole O Ls (outerT d o ρ (tailsOn (deadL pre) ρ (t ∪ poolT (deadL post) ρ)))) e)
  where
    O  = outerᴺ g (outerG d o) ρ
    Ls = states (lanesL post) ρ ++ states (lanesL pre) ρ

-- An ended source is read through its tail alone.
connSrc-closed : ∀ {Γ X B n} r e (b : Node (X ∷ Γ) B) (ρ : NEnv Γ) (h h′ : Events∞ X) → Agreeᵀ n (cut h) (cut h′)
               → Agreeˢ n (connSrc true r e b ρ h) (connSrc true r e b ρ h′)
connSrc-closed {X = X} r e b ρ h h′ t =
  ∪-ne (burstOn-ne r (rested-ne {B = X} h h′ t)) (agreeᵀ-refl _ (cutᴺ b (end e ∷ᴬ ρ))) ,ˢ beside-ne r (same _ (stateᴺ b (end e ∷ᴬ ρ))) (rested-ne {B = X} h h′ t)

connSrc-ne : ∀ {Γ X B n} cl r e (b : Node (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X} → Agreeˢ n h h′
           → Agreeˢ n (connSrc cl r e b ρ h) (connSrc cl r e b ρ h′)
connSrc-ne false r e b ρ x = ∪-ne (burstOn-ne r x) (cutˢ (env-ne b ρ (nowˢ x))) ,ˢ beside-ne r (env-ne b ρ (nowˢ x)) x
connSrc-ne true  r e b ρ {h} {h′} x = connSrc-closed r e b ρ h h′ (cutˢ x)

srcFrame-ne : ∀ {Γ X B n} k (b : Node (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X} → Agreeˢ n h h′ → Agreeˢ n (srcFrame k b ρ h) (srcFrame k b ρ h′)
srcFrame-ne k b ρ x = doneE-ne (CS.owedAt k) (CS.srcLive k) (connSrc-ne (CS.closed k) (CS.srcAt k) (CS.endAt k) b ρ x)

bodyFrame-ne : ∀ {Γ X B n} k (o : St Γ X) (ρ : NEnv Γ) {h h′ : Events∞ B} → Agreeˢ n h h′ → Agreeˢ n (bodyFrame k o ρ h) (bodyFrame k o ρ h′)
bodyFrame-ne k o ρ x = doneE-ne (CS.owedAt k) (CS.srcLive k)
  (∪-ne (agreeᵀ-refl _ (M′.burstOn (CS.srcAt k) (srcState (srcG k o) ρ))) (cutˢ x) ,ˢ beside-ne (CS.srcAt k) x (same _ (srcState (srcG k o) ρ)))

bodyFrame-cut : ∀ {Γ X B n} k (o : St Γ X) (ρ : NEnv Γ) (h h′ : Events∞ B) → Agreeᵀ n (cut h) (cut h′)
              → Agreeᵀ n (cut (bodyFrame k o ρ h)) (cut (bodyFrame k o ρ h′))
bodyFrame-cut k o ρ h h′ t =
  doneE-cut (CS.owedAt k) (CS.srcLive k) (bodyConn (CS.srcAt k) (srcState (srcG k o) ρ) h) (bodyConn (CS.srcAt k) (srcState (srcG k o) ρ) h′)
    (∪-ne (agreeᵀ-refl _ (M′.burstOn (CS.srcAt k) (srcState (srcG k o) ρ))) t)

-- Runs alike at the hole are alike at the root: each frame is one of the
-- denotation's stream functions, and each of those is non-expansive.
lift-ne : ∀ {R Γ A} (c : Ctx R Γ A) f {h h′ : Events∞ A} → h ≋ h′ → ∀ n → Agree n (up c f h) (up c f h′)
lift-ne top                               f x n = Agreeˢ.nowˢ (x n)
lift-ne (inMap g c)                       f x   = lift-ne c true (λ n → let t ,ˢ a = x n in t ,ˢ mapᴱ-ne g a)
lift-ne (inScan g z c)                    f x   = lift-ne c true (λ n → let t ,ˢ a = x n in t ,ˢ scanᴱ-ne g z a)
lift-ne (inCut l a c)                     f x   = lift-ne c true (λ n → switched-ne l (x n))
lift-ne (inLn b c)                        f x   = lift-ne c b x
lift-ne (inTake i q w c)                  f x   = lift-ne c true (λ n → taking∞-ne i q w (x n))
lift-ne (inOuter op g d m q ls c)         f x   = lift-ne c true (λ n → outerFrame-ne op (lane g) d q (lanesL ls) (deadL ls) (envAt c) (x n))
lift-ne (inLanes op g d m q o pre post c) f x   = lift-ne c true (λ n → lanesFrame-ne op (lane g) d q (gh o) pre post f (envAt c) (x n))
lift-ne (inSrc k b c)                     f x   = lift-ne c true (λ n → srcFrame-ne k (gh b) (envAt c) (x n))
lift-ne (inBody k o c)                    f x   = lift-ne c true (λ n → bodyFrame-ne k o (envAt c) (x n))

lift-≅ : ∀ {R Γ A} (c : Ctx R Γ A) f {h h′ : Events∞ A} → h ≋ h′ → up c f h ≅ up c f h′
lift-≅ c f x = agree-≅ (lift-ne c f x)

-- A hole whose observer is closed is read through its tail alone: every
-- frame on the way to the switch that closed it reads only the hole's
-- tail, and the switch reads only that.
closed-hides : ∀ {R Γ A} (c : Ctx R Γ A) f (h h′ : Events∞ A) → closed c ≡ true → (∀ n → Agreeᵀ n (cut h) (cut h′))
             → ∀ n → Agree n (up c f h) (up c f h′)
closed-hides top                               f h h′ () t
closed-hides (inMap g c)                       f h h′ e  t = closed-hides c true (mapped g h) (mapped g h′) e t
closed-hides (inScan g z c)                    f h h′ e  t = closed-hides c true (scanned g z h) (scanned g z h′) e t
closed-hides (inCut false a c)                 f h h′ e  t = lift-ne c true (λ n → rested-ne h h′ (t n))
closed-hides (inCut true a c)                  f h h′ e  t = closed-hides c true h h′ e t
closed-hides (inLn b c)                        f h h′ e  t = closed-hides c b h h′ e t
closed-hides (inTake i q w c)                  f h h′ e  t =
  closed-hides c true (taking∞ i q w h) (taking∞ i q w h′) e (λ n → taking∞-cut i q w h h′ (t n))
closed-hides (inOuter op g d m q ls c)         f h h′ e  t =
  closed-hides c true (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h) (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h′) e
    (λ n → outerFrame-cut op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h h′ (t n))
closed-hides (inLanes op g d m q o pre post c) f h h′ e  t =
  closed-hides c true (lanesFrame op (lane g) d q (gh o) pre post f (envAt c) h) (lanesFrame op (lane g) d q (gh o) pre post f (envAt c) h′) e
    (λ n → lanesFrame-cut op (lane g) d q (gh o) pre post f (envAt c) h h′ (t n))
closed-hides (inSrc (cs false sl sa ba as ow r en) b c) f h h′ () t
closed-hides (inSrc (cs true sl sa ba as ow r en) b c)  f h h′ e  t =
  lift-ne c true (λ n → doneE-ne ow sl (connSrc-closed r en (gh b) (envAt c) h h′ (t n)))
closed-hides (inBody k o c)                    f h h′ e  t =
  closed-hides c true (bodyFrame k o (envAt c) h) (bodyFrame k o (envAt c) h′) e (λ n → bodyFrame-cut k o (envAt c) h h′ (t n))
