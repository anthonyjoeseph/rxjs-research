{-# OPTIONS --guardedness #-}

-- THE RUN'S RE-ENTRY CONFIGURATIONS, against the ghost: between turns
-- with nothing owed, a value about to be shown at the root, a job about
-- to resume, a subscription about to begin, a turn about to play.
-- Every other configuration is reached from one of these by its own
-- silent steps, so is related to the ghost by nothing else.
--
-- The machine's tree holds every operator state but not what the meaning
-- keeps that the run does not: where each node was subscribed, a cold's
-- place on its timeline, what a flatMap's ended parts still run.  So the
-- relation is carried by a witness, `Sub`: the tree node for node, with
-- that ghost data besides.  `forget` drops it, giving the machine's tree
-- back (`Kernels`); `part` reads it as the ghost, exactly.
module port.Strong where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using ([])
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; suc; _+_; _<ᵇ_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

import Tree as T
open import denotation.MonotonicList.Events using (Time; Pos; From; Frame; at; ix; last; tick; root)
import denotation.Unfold as U
open import operation.PureObservable using (PureObs; Tape; tape; over; module Machine; module Driver)
open import port.Sane using (Sane; sane-subscribe)
open import port.Placed.Order using (Placed)
open import port.Sorted using (_≤ᵖ_)
open import port.Sorted.Walk using (module SortingWalk)

open Machine using (St; Ctx; Conf; CS; Job; Mode; plug; dirs; top; ⟨_,_,_,_,_⟩; absorbed; subscribing; resuming; rising; nx; cp;
  att; attBody; owed; next; owedCp; owedCut; feeding;
  coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS) renaming (pend to pendS)

module Strongly (R : Set) where
  open Driver R using (Mach; depthOf; begin)
  open SortingWalk R using (WellMach; begin-well)

  ------------------------------------------------------------------------
  -- Every subscription the run still reaches

  -- A started cold, subscribed at tick `τ`: between frames, its timeline
  -- from the frame it waits for, the frame's timer set at `e`; that
  -- frame's timer fired, its turn not yet played; or at step `i` of the
  -- frame at `r`.
  data Phase (A : Set) : Set where
    waiting : ∀ {u} → Time → Pos → From A u → Phase A
    fired   : ∀ {u} → Time → Pos → From A u → Phase A
    playing : ∀ {t} → Time → Pos → ℕ → Frame A t → Phase A

  -- A takeWhile running; its failing value passed at the position given,
  -- its completion under it owed, its source's configuration as the value
  -- left it; its completion delivered, its cut owed.
  data Taking (Γ : List Set) (A : Set) : Set₁ where
    taking : Taking Γ A
    ending : Pos → U.Node Γ A → Taking Γ A
    taken  : Taking Γ A

  -- Node for node the machine's tree, each with what the meaning keeps
  -- besides.
  data Sub : List Set → Set → Set₁ where
    -- Reached at `q`, not yet begun.
    pendingˢ   : ∀ {Γ A} → PureObs Γ A → Pos → Sub Γ A
    -- Live, and its phase.
    coldˢ      : ∀ {Γ A} → Bool → Phase A → Sub Γ A
    -- `of`, subscribed at `p`, `i` emitted, the rest to come.
    ofˢ        : ∀ {Γ A} → Pos → ℕ → List A → Sub Γ A
    -- Nothing left: `empty`, a spent `of`.
    doneˢ      : ∀ {Γ A} → Sub Γ A
    mapˢ       : ∀ {Γ A B} → (A → B) → Sub Γ A → Sub Γ B
    scanˢ      : ∀ {Γ A B} → (B → A → B) → B → Sub Γ A → Sub Γ B
    -- A kill switch, live and attached, over its subscription.
    cutˢ       : ∀ {Γ A} → Bool → Bool → Sub Γ A → Sub Γ A
    -- A lane, still running in its flatMap's list.
    laneˢ      : ∀ {Γ A} → Bool → Sub Γ A → Sub Γ A
    -- Inclusive, the predicate, where it is in failing, and its source's
    -- switch.
    takeWhileˢ : ∀ {Γ A} → Bool → (A → Bool) → Taking Γ A → Sub Γ A → Sub Γ A
    -- Outer done, lanes running, the values waiting, the meaning's pool
    -- of what its ended parts left running, the outer's switch, and
    -- every lane begun.
    flatMapˢ   : ∀ {Γ A B} → T.FlatOp → (A → PureObs Γ B) → Bool → ℕ → List A
               → U.Node Γ B → Sub Γ A → List (Sub Γ B) → Sub Γ B
    -- The subject; where the source subscribes, where it ended once it
    -- has and what the meaning keeps of it running past that; the
    -- source; the body.
    connectˢ   : ∀ {Γ X B} → CS X → Pos → Maybe Pos → U.Node Γ X → Sub Γ X → Sub (X ∷ Γ) B → Sub Γ B
    -- Joined at `j`, its gate, and what the meaning has fed it and not
    -- yet shown, with where it ends once told.
    joinˢ      : ∀ {Γ A} → Pos → Bool → A ∈ Γ → Maybe (List (Pos × Maybe A) × Maybe Pos) → Sub Γ A

  -- A node below another, by the child indices the machine moves down
  -- by.
  mutual
    data Path : ∀ {Γ A} → Sub Γ A → ∀ {Δ B} → Sub Δ B → List ℕ → Set₁ where
      here      : ∀ {Γ A} {t : Sub Γ A} → Path t t []
      in-map    : ∀ {Γ X A Δ B} {f : X → A} {t : Sub Γ X} {u : Sub Δ B} {π} → Path t u π → Path (mapˢ f t) u (0 ∷ π)
      in-scan   : ∀ {Γ X A Δ B} {f : A → X → A} {z} {t : Sub Γ X} {u : Sub Δ B} {π} → Path t u π → Path (scanˢ f z t) u (0 ∷ π)
      in-cut    : ∀ {Γ A Δ B l a} {t : Sub Γ A} {u : Sub Δ B} {π} → Path t u π → Path (cutˢ l a t) u (0 ∷ π)
      in-lane   : ∀ {Γ A Δ B r} {t : Sub Γ A} {u : Sub Δ B} {π} → Path t u π → Path (laneˢ r t) u (0 ∷ π)
      in-take   : ∀ {Γ A Δ B i q tk} {t : Sub Γ A} {u : Sub Δ B} {π} → Path t u π → Path (takeWhileˢ i q tk t) u (0 ∷ π)
      in-outer  : ∀ {Γ X A Δ B op f d n qs pl} {t : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Δ B} {π}
                → Path t u π → Path (flatMapˢ op f d n qs pl t ls) u (0 ∷ π)
      in-lanes  : ∀ {Γ X A Δ B op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} {u : Sub Δ B} {i π}
                → PathLanes ls u i π → Path (flatMapˢ op f d n qs pl o ls) u (suc i ∷ π)
      in-source : ∀ {Γ X A Δ B k r e rt} {t : Sub Γ X} {b : Sub (X ∷ Γ) A} {u : Sub Δ B} {π}
                → Path t u π → Path (connectˢ k r e rt t b) u (0 ∷ π)
      in-body   : ∀ {Γ X A Δ B k r e rt} {s : Sub Γ X} {t : Sub (X ∷ Γ) A} {u : Sub Δ B} {π}
                → Path t u π → Path (connectˢ k r e rt s t) u (1 ∷ π)

    data PathLanes : ∀ {Γ A} → List (Sub Γ A) → ∀ {Δ B} → Sub Δ B → ℕ → List ℕ → Set₁ where
      this-lane : ∀ {Γ A Δ B} {t : Sub Γ A} {ls} {u : Sub Δ B} {π} → Path t u π → PathLanes (t ∷ ls) u 0 π
      next-lane : ∀ {Γ A Δ B} {l : Sub Γ A} {ls} {u : Sub Δ B} {i π} → PathLanes ls u i π → PathLanes (l ∷ ls) u (suc i) π

  ------------------------------------------------------------------------
  -- The machine's tree, the ghost data dropped

  private
    taped : ∀ {A} → Phase A → Tape A
    taped (waiting τ e (at t _ b)) = tape t b
    taped (waiting τ e _)          = over
    taped (fired τ e (at t _ b))   = tape t b
    taped (fired τ e _)            = over
    taped (playing {t} τ r i b)    = tape t b

  mutual
    forget : ∀ {Γ A} → Sub Γ A → St Γ A
    forget (pendingˢ o q)                     = pendS o
    forget (coldˢ b ph)                       = coldS b (taped ph)
    forget (ofˢ p i xs)                       = ofS xs
    forget doneˢ                              = doneS
    forget (mapˢ f s)                         = mapS f (forget s)
    forget (scanˢ f z s)                      = scanS f z (forget s)
    forget (cutˢ l a s)                       = cutS l a (forget s)
    forget (laneˢ r s)                        = lnS r (forget s)
    forget (takeWhileˢ i q tk s)              = takeS i q (forget s)
    forget (flatMapˢ op f d n qs pl o ls)     = flatS op f d n qs (forget o) (forgetᴸ ls)
    forget (connectˢ k r e rt s b)            = connS k (forget s) (forget b)
    forget (joinˢ j g x st)                   = joinS j g x

    private
      forgetᴸ : ∀ {Γ B} → List (Sub Γ B) → List (St Γ B)
      forgetᴸ []       = []
      forgetᴸ (s ∷ ls) = forget s ∷ forgetᴸ ls

  -- The machine's tree is the witness, forgotten.
  Kernels : Sub [] R → Conf R → Set₁
  Kernels t k = forget t ≡ plug (Conf.ctx k) (Conf.foc k)

  ------------------------------------------------------------------------
  -- What is still open: the ghost, exactly

  -- The configuration a cold's phase is.
  nodeOf : ∀ {Γ A} → Phase A → U.Node Γ A
  nodeOf (waiting τ e m)   = U.framesᶜ τ e m
  nodeOf (fired τ e m)     = U.framesᶜ τ e m
  nodeOf (playing τ r i b) = U.burstᶜ τ r i b

  mapᴹ : ∀ {X Y : Set₁} → (X → Y) → Maybe X → Maybe Y
  mapᴹ f nothing  = nothing
  mapᴹ f (just x) = just (f x)

  consᴹ : ∀ {X : Set₁} → Maybe X → List X → List X
  consᴹ nothing  xs = xs
  consᴹ (just x) xs = x ∷ xs

  -- A flatMap is open while its outer, a lane or the queue is.
  merged : ∀ {Γ A B} → T.FlatOp → (A → Pos → U.Node Γ B) → Maybe (U.Node Γ A) → List (U.Node Γ B) → List A → U.Node Γ B → Maybe (U.Node Γ B)
  merged op g nothing []       []       pl = nothing
  merged op g o       ls       qs       pl = just (U.flatMapᶜ op g o ls qs pl)

  -- A connect is open while its body is, beside its source while that
  -- runs; past the source's end, every joiner the body holds told so.
  connected : ∀ {Γ A B} → Pos → Maybe Pos → U.Node Γ A → Maybe (U.Node Γ A) → Maybe (U.Node (A ∷ Γ) B) → Maybe (U.Node Γ B)
  connected r e        t s        nothing  = nothing
  connected r e        t (just s) (just b) = just (U.connectᶜ r b (U.live s))
  connected r (just c) t nothing  (just b) = just (U.connectᶜ r (U.shut (Any.here refl) c b) (U.ended c t))
  connected r nothing  t nothing  (just b) = nothing

  -- A joiner shows what it holds until it is gone.
  joinedᶜ : ∀ {Γ A} → A ∈ Γ → Pos → Maybe (List (Pos × Maybe A) × Maybe Pos) → Maybe (U.Node Γ A)
  joinedᶜ x j nothing         = nothing
  joinedᶜ x j (just (xs , e)) = just (U.joinᶜ x j xs e)

  taking? : ∀ {Γ A} → Bool → (A → Bool) → Taking Γ A → Maybe (U.Node Γ A) → Maybe (U.Node Γ A)
  taking? i p taking       s = mapᴹ (U.takeWhileᶜ i p) s
  taking? i p (ending k c) s = just (U.endingᶜ (k ++ [ last ]) c)
  taking? i p taken        s = nothing

  -- A switch's own state: off once cut; anything else is not a switch.
  private
    switched : ∀ {Γ A} → Sub Γ A → Bool
    switched (cutˢ l a s) = l
    switched _            = true

  mutual
    part : ∀ {Γ A} → Sub Γ A → Maybe (U.Node Γ A)
    part (pendingˢ o q)                     = just (U.subscribe o q)
    part (coldˢ b ph)                       = if b then just (nodeOf ph) else nothing
    part (ofˢ p i xs)                       = just (U.ofᶜ p i xs)
    part doneˢ                              = nothing
    part (mapˢ f s)                         = mapᴹ (U.mapᶜ f) (part s)
    part (scanˢ f z s)                      = mapᴹ (U.scanᶜ f z) (part s)
    part (cutˢ l a s)                       = if l then part s else nothing
    part (laneˢ r s)                        = part s
    part (takeWhileˢ i q tk s)              = if switched s then taking? i q tk (part s) else nothing
    part (flatMapˢ op f d n qs pl o ls)     = merged op (λ x r → U.subscribe (f x) r) (part o) (partLanes ls) qs pl
    part (connectˢ k r e rt s b)            = connected r e rt (part s) (part b)
    part (joinˢ j g x st)                   = if g then joinedᶜ x j st else nothing

    partLanes : ∀ {Γ B} → List (Sub Γ B) → List (U.Node Γ B)
    partLanes []       = []
    partLanes (s ∷ ls) = consᴹ (part s) (partLanes ls)

  ------------------------------------------------------------------------
  -- THE WORK OWED: one for each operator reached and not begun.  A
  -- defer's body is not counted: its expansion is a skip of the
  -- meaning's.

  syn : ∀ {Γ A} → PureObs Γ A → ℕ
  syn (T.cold c)          = 1
  syn T.empty             = 1
  syn (T.of xs)           = 1
  syn (T.map f s)         = suc (syn s)
  syn (T.scan f z s)      = suc (syn s)
  syn (T.takeWhile i q s) = suc (syn s)
  syn (T.flatMap op f s)  = suc (syn s)
  syn (T.connect s b)     = suc (syn s + syn b)
  syn (T.connected i)     = 1
  syn (T.defer l)         = 1

  mutual
    pend : ∀ {Γ A} → Sub Γ A → ℕ
    pend (pendingˢ s q)                     = syn s
    pend (mapˢ f s)                         = pend s
    pend (scanˢ f z s)                      = pend s
    pend (cutˢ l a s)                       = pend s
    pend (laneˢ r s)                        = pend s
    pend (takeWhileˢ i q tk s)              = pend s
    pend (flatMapˢ op f d n qs pl o ls)     = pend o + pendᴸ ls
    pend (connectˢ k r e rt s b)            = pend s + pend b
    pend _                                  = 0

    pendᴸ : ∀ {Γ B} → List (Sub Γ B) → ℕ
    pendᴸ []       = 0
    pendᴸ (s ∷ ls) = pend s + pendᴸ ls

  -- What each takeWhile has still to do: fail, then complete.
  stage : ∀ {Γ A} → Taking Γ A → ℕ
  stage taking       = 2
  stage (ending _ _) = 1
  stage taken        = 0

  mutual
    takes : ∀ {Γ A} → Sub Γ A → ℕ
    takes (mapˢ f s)                         = takes s
    takes (scanˢ f z s)                      = takes s
    takes (cutˢ l a s)                       = takes s
    takes (laneˢ r s)                        = takes s
    takes (takeWhileˢ i q tk s)              = stage tk + takes s
    takes (flatMapˢ op f d n qs pl o ls)     = takes o + takesᴸ ls
    takes (connectˢ k r e rt s b)            = takes s + takes b
    takes _                                  = 0

    takesᴸ : ∀ {Γ B} → List (Sub Γ B) → ℕ
    takesᴸ []       = 0
    takesᴸ (s ∷ ls) = takes s + takesᴸ ls

  -- The values the tree's `of`s have still to emit.
  mutual
    left : ∀ {Γ A} → Sub Γ A → ℕ
    left (ofˢ _ _ xs)                       = length xs
    left (mapˢ f s)                         = left s
    left (scanˢ f z s)                      = left s
    left (cutˢ l a s)                       = left s
    left (laneˢ r s)                        = left s
    left (takeWhileˢ i q tk s)              = left s
    left (flatMapˢ op f d n qs pl o ls)     = left o + leftᴸ ls
    left (connectˢ k r e rt s b)            = left s + left b
    left _                                  = 0

    leftᴸ : ∀ {Γ B} → List (Sub Γ B) → ℕ
    leftᴸ []       = 0
    leftᴸ (s ∷ ls) = left s + leftᴸ ls

  ------------------------------------------------------------------------
  -- THE RE-ENTRY STATES, by the machine's configuration: nothing owed
  -- and no turn to play; a value about to be shown at the root, at its
  -- tick; a job about to resume; a pending node about to begin; the next
  -- turn about to play, no job owed above it.

  data CtlAs (m : Mach) : Set₁ where
    calmAs  : ∀ {Γ A} {c : Ctx R Γ A} {s p} → Mach.conf m ≡ ⟨ c , s , absorbed , p , [] ⟩ → Mach.turns m ≡ [] → CtlAs m
    noteAs  : ∀ {s a p rs} → Mach.conf m ≡ ⟨ top , s , rising (nx a) , p , rs ⟩ → Mach.clock m ≡ tick p → CtlAs m
    runAs   : ∀ {Γ A} {c : Ctx R Γ A} {s t p rs} → Mach.conf m ≡ ⟨ c , s , resuming t , p , rs ⟩ → CtlAs m
    subAs   : ∀ {Γ A} {c : Ctx R Γ A} {o p rs} → Mach.conf m ≡ ⟨ c , pendS o , subscribing , p , rs ⟩ → CtlAs m
    burstAs : ∀ {Γ A} {c : Ctx R Γ A} {s p rs t ts} → Mach.conf m ≡ ⟨ c , s , absorbed , p , rs ⟩ → Mach.turns m ≡ t ∷ ts
            → (depthOf t <ᵇ length rs) ≡ false → CtlAs m

  -- The ghost the witness reads: a value about to be shown, the ghost
  -- before it; otherwise the witness's own.
  Meets : ∀ {m} → CtlAs m → Maybe (U.Node [] R) → U.Node [] R → Set₁
  Meets (noteAs {a = a} {p = p} _ _) n g = Σ (U.Node [] R) λ g′ → n ≡ just g′ × U.step g ≡ U.outˢ p a g′
  Meets _                            n g = n ≡ just g

  -- Its next event no earlier than `q`.
  Heads : ∀ {Γ A} → Pos → U.Node Γ A → Set
  Heads q c = ∀ {k} → U.headˢ (U.step c) ≡ just k → q ≤ᵖ k

  ------------------------------------------------------------------------
  -- THE JOBS, against the witness

  -- What is owed: the job about to resume, then every job suspended.
  agenda : Conf R → List Job
  agenda k = now (Conf.ctx k) (Conf.mode k) (Conf.pos k) ++ Conf.rets k
    where now : ∀ {Γ A} → Ctx R Γ A → Mode A → Pos → List Job
          now c (resuming t) p = [ (dirs c , t , p) ]
          now c _            p = []

  -- Whether the ghost holds the path's end: every switch on, every
  -- takeWhile taking, every connect open on the side the path leaves.
  isTaking : ∀ {Γ A} → Taking Γ A → Bool
  isTaking taking = true
  isTaking _      = false

  mutual
    seen : ∀ {Γ A Δ B} {t : Sub Γ A} {u : Sub Δ B} {π} → Path t u π → Bool
    seen here                                = true
    seen (in-map ψ)                          = seen ψ
    seen (in-scan ψ)                         = seen ψ
    seen (in-cut {l = l} ψ)                  = l ∧ seen ψ
    seen (in-lane ψ)                         = seen ψ
    seen (in-take {tk = tk} ψ)               = isTaking tk ∧ seen ψ
    seen (in-outer ψ)                        = seen ψ
    seen (in-lanes ψ)                        = seenL ψ
    seen (in-source {b = b} ψ)               = is-just (part b) ∧ seen ψ
    seen (in-body {e = e} {s = s} ψ)         = (is-just (part s) ∨ is-just e) ∧ seen ψ

    seenL : ∀ {Γ A Δ B} {ls : List (Sub Γ A)} {u : Sub Δ B} {i π} → PathLanes ls u i π → Bool
    seenL (this-lane ψ) = seen ψ
    seenL (next-lane ψ) = seenL ψ

  -- A pending node: the focus, about to begin where it was reached; or a
  -- connect's source, its subscription owed to the body's attach, one
  -- level down from where the connect was subscribed.
  data Begins (k : Conf R) (π : List ℕ) (q : Pos) : Set₁ where
    focused : dirs (Conf.ctx k) ≡ π → Conf.mode k ≡ subscribing → Conf.pos k ≡ q → Begins k π q
    sourced : ∀ ρ p → π ≡ ρ ++ [ 0 ] → (ρ , attBody , p) ∈ agenda k → q ≡ p ++ [ ix 1 ] → Begins k π q

  -- EVERYTHING DUE BEFORE THE NEXT TURN IS OWED, each a job at its
  -- node's path: an `of`'s next value; a pending node's subscription; a
  -- switch's attach; a takeWhile's completion, then its cut while its
  -- source's switch is on; a connect's feed, its body's attach, then its
  -- source's, and the source's teardown once a held body is gone.
  record Owned (t : Sub [] R) (m : Mach) : Set₁ where
    private k = Mach.conf m
    field
      ofs     : ∀ {Γ A p i xs π} → Path t (ofˢ {Γ} {A} p i xs) π → (π , next i , p) ∈ agenda k
      begun   : ∀ {Γ A o q π} → Path t (pendingˢ {Γ} {A} o q) π → Begins k π q
      attached : ∀ {Γ A l s π} → Path t (cutˢ {Γ} {A} l false s) π → Σ Pos λ q → (π , att , q) ∈ agenda k
      ends    : ∀ {Γ A i f q c s π} → Path t (takeWhileˢ {Γ} {A} i f (ending q c) s) π → (π , owedCp , q) ∈ agenda k
      cuts    : ∀ {Γ A i f a s π} → Path t (takeWhileˢ {Γ} {A} i f taken (cutˢ true a s)) π → Σ Pos λ q → (π , owedCut , q) ∈ agenda k
      feeds   : ∀ {Γ X B k′ r e rt s b π} → Path t (connectˢ {Γ} {X} {B} k′ r e rt s b) π → CS.feeds k′ ≢ []
              → Σ _ λ js → Σ Pos λ q → (π , feeding js , q) ∈ agenda k
      bodies  : ∀ {Γ X B k′ r e rt s b π} → Path t (connectˢ {Γ} {X} {B} k′ r e rt s b) π → CS.bodyAtt k′ ≡ false
              → Σ Pos λ p → (π , attBody , p) ∈ agenda k × r ≡ p ++ [ ix 1 ]
      sources : ∀ {Γ X B k′ r e rt s b π} → Path t (connectˢ {Γ} {X} {B} k′ r e rt s b) π → CS.bodyAtt k′ ≡ true → CS.srcAtt k′ ≡ false
              → (π , att , r) ∈ agenda k
      owes    : ∀ {Γ X B k′ r e rt s b π} (ψ : Path t (connectˢ {Γ} {X} {B} k′ r e rt s b) π) → seen ψ ≡ true
              → CS.srcLive k′ ≡ true → part b ≡ nothing → Σ Pos λ q → (π , owed , q) ∈ agenda k

  postulate
    -- Every live joiner holding what its feed owes it.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Against.agda
    Meaning : Sub [] R → Set₁

    -- The timers, each a waiting cold's next frame, in order, due no
    -- earlier than now and past where the run is.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Against.agda
    Queue : Pos → ℕ → List (Driver.Timer R) → Sub [] R → Set₁

    -- The clock where the control says.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Against.agda
    Books : Sub [] R → Mach → Set₁

    -- `P` of every node the ghost holds, and of every held flatMap's pool
    -- and ended connect's rest.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Against.agda
    Each : (∀ {Γ A} → U.Node Γ A → Set) → Sub [] R → Set₁

    -- What a held node keeps of its ended parts is what they still run.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Against.agda
    Lingers : Sub [] R → Set₁

    -- What a connect past its source's end has not told its body's
    -- joiners, it tells no sooner than `q`.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Held.agda
    Untold : Pos → Sub [] R → Set₁

    -- A connect still held past its source's end holds no source.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Held.agda
    Ended : Sub [] R → Set₁

    -- Every held flatMap's outer-done flag reads its outer gone.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Strong/Held.agda
    DoneBy : Sub [] R → Set₁

  -- THE CONFIGURATION RUNS THE GHOST FROM A RE-ENTRY STATE: a witness of
  -- every subscription the run reaches, which the machine's tree forgets
  -- to, whose open part is the ghost; the machine sorted; every node the
  -- ghost holds heading no earlier than where the run is; what it keeps
  -- of ended parts, what they still run.
  record Carried (g : U.Node [] R) (m : Mach) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      tree    : Sub [] R
      kernels : Kernels tree (Mach.conf m)
      ctlAs   : CtlAs m
      meets   : Meets ctlAs (part tree) g
      owned   : Owned tree m
      meaning : Meaning tree
      queue   : Queue (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) tree
      books   : Books tree m
      sorted  : Σ Pos λ lo → WellMach lo m
      behind  : Each (Heads (Conf.pos (Mach.conf m))) tree
      lingers : Lingers tree
      told    : Untold (Conf.pos (Mach.conf m)) tree
      ended   : Ended tree
      flags   : DoneBy tree

  -- A RE-ENTRY CONFIGURATION AGAINST THE GHOST: carried, or the root's
  -- completion about to be shown where the ghost ends.
  data Strong (g : U.Node [] R) (m : Mach) : Set₁ where
    carried : Carried g m → Strong g m
    closing : ∀ {s p rs} → Mach.conf m ≡ ⟨ top , s , rising cp , p , rs ⟩ → U.step g ≡ U.endˢ p → Sane [] g → Placed g [] → Strong g m

  ------------------------------------------------------------------------
  -- THE LAUNCH: the root pending, about to begin

  postulate
    -- A program subscribed at the root is placed.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Placed.agda
    placed-subscribe : (o : PureObs [] R) → Placed (U.subscribe o root) []

    -- Each invariant, of the root pending at the launch.
    meaning-begin : (o : PureObs [] R) → Meaning (pendingˢ o root)
    queue-begin   : (o : PureObs [] R) → Queue root 0 [] (pendingˢ o root)
    books-begin   : (o : PureObs [] R) → Books (pendingˢ o root) (begin o)
    behind-begin  : (o : PureObs [] R) → Each (Heads root) (pendingˢ o root)
    lingers-begin : (o : PureObs [] R) → Lingers (pendingˢ o root)
    told-begin    : (o : PureObs [] R) → Untold root (pendingˢ o root)
    ended-begin   : (o : PureObs [] R) → Ended (pendingˢ o root)
    flags-begin   : (o : PureObs [] R) → DoneBy (pendingˢ o root)

  -- The launch is a re-entry configuration against the program
  -- subscribed at the root.
  --
  -- RECOVERY: git show 6e83e02b:agda-impl/port/Deep.agda restores `Deep` and `deep-subscribe`, the order to every depth the old body holds a launch to
  strong-begin : (o : PureObs [] R) → Strong (U.subscribe o root) (begin o)
  strong-begin o = carried record
    { sane    = sane-subscribe o root (λ ())
    ; placed  = placed-subscribe o
    ; tree    = pendingˢ o root
    ; kernels = refl
    ; ctlAs   = subAs refl
    ; meets   = refl
    ; owned   = record
        { ofs = λ () ; begun = λ { here → focused refl refl refl } ; attached = λ () ; ends = λ () ; cuts = λ ()
        ; feeds = λ () ; bodies = λ () ; sources = λ () ; owes = λ () }
    ; meaning = meaning-begin o
    ; queue   = queue-begin o
    ; books   = books-begin o
    ; sorted  = root , begin-well o
    ; behind  = behind-begin o
    ; lingers = lingers-begin o
    ; told    = told-begin o
    ; ended   = ended-begin o
    ; flags   = flags-begin o
    }
