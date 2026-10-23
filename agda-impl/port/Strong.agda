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
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.All using (All; []; lookup)
open import Data.List.Relation.Unary.Linked using (Linked; [])
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat using (ℕ; suc; _+_; _<ᵇ_; _≡ᵇ_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

import Tree as T
open import denotation.MonotonicList.Events using (Time; Pos; From; Frame; at; ix; last; tick; root; _<ᵖ_) renaming (sub to subᴾ)
import denotation.Unfold as U
open import operation.PureObservable using (PureObs; Tape; tape; over; module Machine; module Driver)
open import port.Sane using (Sane; sane-subscribe)
open import port.Leaves using (Leaves; Twin; Restful)
open import port.Told using (untold; Tells)
open import port.Placed.Order using (Placed)
open import port.Sorted using (_≤ᵖ_)
open import port.Sorted.Walk using (module SortingWalk)

open Machine using (St; Ctx; Conf; CS; Job; Mode; Ev; plug; dirs; top; ⟨_,_,_,_,_⟩; absorbed; subscribing; resuming; rising; nx; cp; _⊕_;
  go; att; attBody; owed; next; owedCp; owedCut; feeding;
  coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS) renaming (pend to pendS)

module Strongly (R : Set) where
  open Driver R using (Mach; Timer; Turn; play; finish; cascade; depthOf; begin)
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
    attaching : ∀ ρ p → π ≡ ρ ++ [ 0 ] → (ρ , attBody , p) ∈ agenda k → q ≡ p ++ [ ix 1 ] → Begins k π q

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

  -- `P` of every node the ghost holds, and of what a held flatMap's ended
  -- parts left running, and what a held connect's ended source did.
  -- Held: `seen`, so a teardown, which leaves what it reached unseen,
  -- answers for nothing below its switch.
  record Each (P : ∀ {Γ A} → U.Node Γ A → Set) (t : Sub [] R) : Set₁ where
    field
      parts : ∀ {Δ B π} {u : Sub Δ B} (ψ : Path t u π) → seen ψ ≡ true → ∀ {c} → part u ≡ just c → P c
      pools : ∀ {Γ X A op f d n qs pl π} {o : Sub Γ X} {ls : List (Sub Γ A)}
            → (ψ : Path t (flatMapˢ op f d n qs pl o ls) π) → seen ψ ≡ true
            → ∀ {c} → part (flatMapˢ op f d n qs pl o ls) ≡ just c → P pl
      rests : ∀ {Γ X B k r e rt π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
            → (ψ : Path t (connectˢ k r e rt s b) π) → seen ψ ≡ true
            → ∀ {n} → part (connectˢ k r e rt s b) ≡ just n
            → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt

  ------------------------------------------------------------------------
  -- What a subscription leaves running past its end

  -- A source's node: what it shows while it runs, else what it left.
  sourced : ∀ {Γ A} → Maybe (U.Node Γ A) → U.Node Γ A → U.Node Γ A
  sourced (just s) _ = s
  sourced nothing  t = t

  -- Read off the witness past every switch and pool: each connect's
  -- source run under where it subscribed, beside its body's leftover; a
  -- pending node's, once begun.
  mutual
    leftover : ∀ {Γ A B} → Sub Γ A → U.Node Γ B
    leftover (pendingˢ o q)                 = U.restᶜ (U.subscribe o q)
    leftover (mapˢ f s)                     = leftover s
    leftover (scanˢ f z s)                  = leftover s
    leftover (cutˢ l a s)                   = leftover s
    leftover (laneˢ r s)                    = leftover s
    leftover (takeWhileˢ i q tk s)          = leftover s
    leftover (flatMapˢ op f d n qs pl o ls) = U.unionᶜ (leftover o) (leftoverL ls)
    leftover (connectˢ k r e rt s b)        = U.unionᶜ (U.burstingᶜ r m) (U.underᶜ (U.live m) (leftover {B = ⊤} b))
      where m = sourced (part s) (leftover s)
    leftover _                              = U.idleᶜ

    leftoverL : ∀ {Γ A B} → List (Sub Γ A) → U.Node Γ B
    leftoverL []       = U.idleᶜ
    leftoverL (s ∷ ls) = U.unionᶜ (leftover s) (leftoverL ls)

  -- What a flatMap's pool runs, by its own flags: its outer's leftover
  -- once it heard the outer end, each lane's once it cut the lane.
  pooledL : ∀ {Γ B} → List (Sub Γ B) → U.Node Γ B
  pooledL []                = U.idleᶜ
  pooledL (laneˢ r s ∷ ls)  = if r then pooledL ls else U.unionᶜ (leftover s) (pooledL ls)
  pooledL (_ ∷ ls)          = pooledL ls

  pooled : ∀ {Γ X B} → Bool → Sub Γ X → List (Sub Γ B) → U.Node Γ B
  pooled d o ls = U.unionᶜ (if d then leftover o else U.idleᶜ) (pooledL ls)

  -- WHAT A HELD NODE KEEPS OF ITS ENDED PARTS IS WHAT THEY STILL RUN,
  -- to every depth: below `t`, a held flatMap's pool, a rest's shape,
  -- leaves what the witness reads off as its ended parts' leftovers; a
  -- held connect's ended source's rest leaves the source's, its order
  -- read back besides.
  record Lingers (t : Sub [] R) : Set₁ where
    field
      pools : ∀ {Γ X A op f d n qs pl π} {o : Sub Γ X} {ls : List (Sub Γ A)}
            → (ψ : Path t (flatMapˢ op f d n qs pl o ls) π) → seen ψ ≡ true
            → ∀ {c} → part (flatMapˢ op f d n qs pl o ls) ≡ just c → Leaves pl (pooled d o ls) × Restful pl
      rests : ∀ {Γ X B k r e rt π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
            → (ψ : Path t (connectˢ k r e rt s b) π) → seen ψ ≡ true
            → ∀ {n} → part (connectˢ k r e rt s b) ≡ just n
            → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Twin rt (leftover {B = ⊤} s) × Restful rt

  -- What a connect past its source's end has not told its body's
  -- joiners, it tells no sooner than `q`.
  Untold : Pos → Sub [] R → Set₁
  Untold q t = ∀ {Γ X B k r c₀ rt π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
             → (ψ : Path t (connectˢ k r (just c₀) rt s b) π) → seen ψ ≡ true → part s ≡ nothing
             → ∀ {b₀} → part b ≡ just b₀ → Tells q c₀ (untold (Any.here refl) b₀)

  -- A connect still held past its source's end holds no source.
  Ended : Sub [] R → Set₁
  Ended t = ∀ {Γ X B k r e rt π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
          → (ψ : Path t (connectˢ k r e rt s b) π) → seen ψ ≡ true
          → ∀ {n} → part (connectˢ k r e rt s b) ≡ just n → ∀ {c₀} → e ≡ just c₀ → part s ≡ nothing

  -- EVERY SEEN FLATMAP'S DONE FLAG READS ITS OUTER GONE: an outer's end
  -- sets the flag as it rises to the flatMap, and no re-entry state
  -- falls between.
  DoneBy : Sub [] R → Set₁
  DoneBy t = ∀ {Γ X A op f d n qs pl π} {o : Sub Γ X} {ls : List (Sub Γ A)}
           → (ψ : Path t (flatMapˢ op f d n qs pl o ls) π) → seen ψ ≡ true → d ≡ is-nothing (part o)

  ------------------------------------------------------------------------
  -- The joiners' feed

  -- Each connect in scope: its path, its subject, where its source ended.
  record Feed (X : Set) : Set where
    constructor feed
    field
      binder  : List ℕ
      subject : CS X
      ended   : Maybe Pos

  Now : List Set → Set
  Now = All Feed

  private
    samePath : List ℕ → List ℕ → Bool
    samePath []       []       = true
    samePath (a ∷ as) (b ∷ bs) = (a ≡ᵇ b) ∧ samePath as bs
    samePath _        _        = false

    listed : List ℕ → List (List ℕ × Pos) → Bool
    listed π []              = false
    listed π ((π′ , _) ∷ js) = samePath π π′ ∨ listed π js

    -- The feeds under way at a connect, innermost first: the joiners
    -- each has still to feed, and the value's position.
    feedsAt : List ℕ → List Job → List (List (List ℕ × Pos) × Pos)
    feedsAt ρ []                          = []
    feedsAt ρ ((ρ′ , feeding js , p) ∷ jb) = if samePath ρ ρ′ then (js , p) ∷ feedsAt ρ jb else feedsAt ρ jb
    feedsAt ρ (_ ∷ jb)                    = feedsAt ρ jb

    -- The joiner at `π` about to read its binder's newest feed.
    goingAt : ∀ {Γ A} → Ctx R Γ A → Mode A → List ℕ → Bool
    goingAt c (resuming go) π = samePath (dirs c) π
    goingAt c _             π = false

    told₁ : ∀ {X} → Pos → Ev X → List (Pos × Maybe X) × Maybe Pos → List (Pos × Maybe X) × Maybe Pos
    told₁ q (nx a) (xs , c) = (q , just a) ∷ xs , c
    told₁ q cp     (xs , c) = xs , just q

    -- What the feeds under way owe the joiner at `π`, joined at `j`,
    -- innermost first: the newest to the joiner reading it, each to the
    -- joiners it has still to feed.
    owedFrom : ∀ {X} → Bool → List ℕ → Pos → List (Ev X) → List (List (List ℕ × Pos) × Pos) → List (Pos × Maybe X) × Maybe Pos
    owedFrom r π j (e ∷ es) ((js , p) ∷ ls) =
      if r ∨ listed π js then told₁ (p ⊕ [ subᴾ j ]) e (owedFrom false π j es ls) else owedFrom false π j es ls
    owedFrom r π j _        _               = [] , nothing

  -- What the meaning has fed the joiner at `π`, joined at `j`, and the
  -- run still owes it; owed nothing, waiting while its source runs, gone
  -- once the source has ended.
  owing : ∀ {X} → Conf R → Feed X → List ℕ → Pos → Maybe (List (Pos × Maybe X) × Maybe Pos)
  owing k b π j with owedFrom (goingAt (Conf.ctx k) (Conf.mode k) π) π j (CS.feeds (Feed.subject b)) (feedsAt (Feed.binder b) (agenda k))
  ... | [] , nothing = if is-just (Feed.ended b) then nothing else just ([] , nothing)
  ... | o            = just o

  -- EVERY LIVE JOINER HOLDS WHAT THE RUN OWES IT, read at its path.
  mutual
    Fed : ∀ {Γ A} → Conf R → Sub Γ A → List ℕ → Now Γ → Set
    Fed k (mapˢ f s)                     π ν = Fed k s (π ++ [ 0 ]) ν
    Fed k (scanˢ f z s)                  π ν = Fed k s (π ++ [ 0 ]) ν
    Fed k (cutˢ l a s)                   π ν = Fed k s (π ++ [ 0 ]) ν
    Fed k (laneˢ r s)                    π ν = Fed k s (π ++ [ 0 ]) ν
    Fed k (takeWhileˢ i q tk s)          π ν = Fed k s (π ++ [ 0 ]) ν
    Fed k (flatMapˢ op f d n qs pl o ls) π ν = Fed k o (π ++ [ 0 ]) ν × FedLanes k ls π 1 ν
    Fed k (connectˢ k′ r e rt s b)       π ν = Fed k s (π ++ [ 0 ]) ν × Fed k b (π ++ [ 1 ]) (feed π k′ e ∷ ν)
    Fed k (joinˢ j g x st)               π ν = g ≡ true → st ≡ owing k (lookup ν x) π j
    Fed k _                              π ν = ⊤

    FedLanes : ∀ {Γ B} → Conf R → List (Sub Γ B) → List ℕ → ℕ → Now Γ → Set
    FedLanes k []       π i ν = ⊤
    FedLanes k (s ∷ ls) π i ν = Fed k s (π ++ [ i ]) ν × FedLanes k ls π (suc i) ν

  Meaning : Sub [] R → Conf R → Set
  Meaning t k = Fed k t [] []

  ------------------------------------------------------------------------
  -- The queue and the clock

  -- The timer a waiting cold set for its next frame.
  Waits : ∀ {A} → Timer → Phase A → Set
  Waits tm (waiting τ e (at t _ _)) = Timer.due tm ≡ τ + t × Timer.from tm ≡ e
  Waits tm _                        = ⊥

  -- A timer is a cold's, live or torn down since, waiting for it.
  Timed : Sub [] R → Timer → Set₁
  Timed t tm = Σ (List Set) λ Γ → Σ Set λ A → Σ (Phase A) λ ph → Σ Bool λ b
             → Path t (coldˢ {Γ} {A} b ph) (Timer.path tm) × Waits tm ph

  -- Every joiner a connect's subject lists is at its listed path.
  Joined : Sub [] R → Set₁
  Joined t = ∀ {Γ X B k r e rt ρ} {s : Sub Γ X} {b : Sub (X ∷ Γ) B} → Path t (connectˢ k r e rt s b) ρ
           → All (λ sj → Σ (List Set) λ Δ → Σ Set λ A → Σ (A ∈ Δ) λ x → Σ (Maybe (List (Pos × Maybe A) × Maybe Pos)) λ st → Σ Bool λ g
                       → Path t (joinˢ {Δ} {A} (proj₂ sj) g x st) (ρ ++ proj₁ sj)) (CS.subs k)

  -- The queue: each timer a cold's, in order, each due no earlier than
  -- now and past where the run is; the subjects' joiners in place.
  record Queue (p : Pos) (clock : ℕ) (timers : List Timer) (t : Sub [] R) : Set₁ where
    field
      timed   : All (Timed t) timers
      joined  : Joined t
      ordered : Linked (λ x y → cascade x <ᵖ cascade y ≡ true) timers
      ahead   : All (λ tm → clock ≤ Timer.due tm × p <ᵖ cascade tm ≡ true) timers

  -- The frame a turn plays, at its cold's own tick.
  Plays : ∀ {A} → ℕ → Pos → Phase A → Set
  Plays n u (fired τ e (at t _ _))   = n ≡ τ + t
  Plays n u (playing {t} τ r i b)    = n ≡ τ + t × u ≡ r
  Plays n u (waiting _ _ _)          = ⊥
  Plays n u (fired _ _ _)            = ⊥

  -- Where the clock stands for a turn: at its frame's tick, its cold
  -- playing that frame.
  BurstClocked : Sub [] R → ℕ → Turn → Set₁
  BurstClocked t n (play π u i pl d) = n ≡ tick u × Σ (List Set) λ Γ → Σ Set λ A → Σ (Phase A) λ ph → Σ Bool λ b
                                     → Path t (coldˢ {Γ} {A} b ph) π × Plays n u ph
  BurstClocked t n (finish π e d)    = Lift _ (n ≡ tick e)

  -- A callback's position at the clock's tick; between turns, none.
  Clocked : ∀ {A} → ℕ → Mode A → Pos → Set
  Clocked n absorbed p = ⊤
  Clocked n _        p = n ≡ tick p

  -- THE CLOCK WHERE THE CONTROL SAYS: the job about to run and every
  -- job held at its tick; every turn held, at its frame's.
  record Books (t : Sub [] R) (m : Mach) : Set₁ where
    field
      clocked : Clocked (Mach.clock m) (Conf.mode (Mach.conf m)) (Conf.pos (Mach.conf m))
      ticked  : All (λ jb → Mach.clock m ≡ tick (proj₂ (proj₂ jb))) (Conf.rets (Mach.conf m))
      turned  : All (BurstClocked t (Mach.clock m)) (Mach.turns m)


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
      meaning : Meaning tree (Mach.conf m)
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
    -- A program subscribed at the root heads no earlier than the root.
    heads-subscribe : (o : PureObs [] R) → Heads root (U.subscribe o root)

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
    ; meaning = _
    ; queue   = record { timed = [] ; joined = λ () ; ordered = [] ; ahead = [] }
    ; books   = record { clocked = refl ; ticked = [] ; turned = [] }
    ; sorted  = root , begin-well o
    ; behind  = record { parts = λ { here _ refl → heads-subscribe o } ; pools = λ () ; rests = λ () }
    ; lingers = record { pools = λ () ; rests = λ () }
    ; told    = λ ()
    ; ended   = λ ()
    ; flags   = λ ()
    }
