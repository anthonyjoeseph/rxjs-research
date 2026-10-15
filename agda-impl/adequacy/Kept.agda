{-# OPTIONS --guardedness --large-indices #-}

-- B KEPT, C FINITE: a carried state's next step, against its
-- configuration's, passes each side alone finitely often before the two
-- meet again carried, or end, or fall quiet together.  Split by what the
-- machine is doing: running code, bursting a cold's frame, or between
-- turns.  The relation never rests at a return.
module adequacy.Kept where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Linked as Linked
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s⁻¹)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (≤-trans; ≤-refl; <-trans; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; subst₂; cong)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Pos; _<ᵖ_; <ᵖ-trans; <ᵖ-tick; emit; stall; close) renaming (sub to subᴾ)
open import denotation.Unfold using (Node; hushˢ; skipˢ) renaming (step to stepᵁ)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; _⊑_; Sink; Handle; same; module Pure)
open import operation.Machine using (module Machine)
open import denotation.MonotonicList using (Frame; at)
open import adequacy.Carrier using (module Carrying)
open import adequacy.Wait using (module Waiting)

module Keeping (R : Set) where
  open Run (Pureᴾ R) using (Act)
  open Pure R using (State; Timer; cascade; Callbacks)
  open Machine R using (Mach; ⟨_,_⟩; Stack; loop; run; ret; burst; turn; step; silent; drained; spent?; asked; push; cbs)
  open Carrying R using (Carried; module At; module Against; Owned; Ordered; Sub; Lane; lane; Call; feedC; finC; Spot
                        ; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ
                        ; waiting; playing; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer
                        ; this-lane; next-lane; Meaning; Kernels; Queue; Books; pendings; lanePendings; joiners; Joiner; firing)
  open Waiting R using (Wait; idles; left; right)

  ------------------------------------------------------------------------
  -- The run moving on: a later position

  private
    later-false : ∀ p q x → p <ᵖ q ≡ true → p <ᵖ x ≡ false → q <ᵖ x ≡ false
    later-false p q x pq px with q <ᵖ x in qx
    ... | false = refl
    ... | true  with trans (sym (<ᵖ-trans p q x pq qx)) px
    ...   | ()

  private
    linked-all : ∀ {ℓ} {X : Set ℓ} {_≺_ : X → X → Set} → (∀ {a b c} → a ≺ b → b ≺ c → a ≺ c)
               → ∀ {x xs} → Linked _≺_ (x ∷ xs) → All (x ≺_) xs
    linked-all {_≺_ = _≺_} tr {x} [-]      = []
    linked-all {_≺_ = _≺_} tr {x} (r ∷ rs) = go r rs
      where go : ∀ {y ys} → x ≺ y → Linked _≺_ (y ∷ ys) → All (x ≺_) (y ∷ ys)
            go r [-]        = r ∷ []
            go r (r′ ∷ rs′) = r ∷ go (tr r r′) rs′

  ------------------------------------------------------------------------
  -- Between turns

  -- The meaning falls quiet after silent steps of its own.
  data Quiets : Node [] R → Set₁ where
    hushes : ∀ {c} → stepᵁ c ≡ hushˢ → Quiets c
    skips  : ∀ {c c′ q} → stepᵁ c ≡ skipˢ q c′ → Quiets c′ → Quiets c

  quiets : ∀ {c} → Quiets c → Wait Carried drained (stepᵁ c)
  quiets (hushes e) rewrite e = idles
  quiets (skips e q) rewrite e = right (quiets q)

  -- The run moved to a timer's cascade, the queue's head dropped: the
  -- joiners and the queue's order still hold.
  module Moved {h} {st : State h} {tm : Timer h} {ts : List (Timer h)} (t : Sub h [] R) {fl} (q : Queue st t fl) (e : State.timers st ≡ tm ∷ ts) where
    St′ : State h
    St′ = record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }

    private
      linked : Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (tm ∷ ts)
      linked = subst (Linked _) e (proj₁ (Queue.ordered q))

      after : ∀ {t : Timer h} → cascade tm <ᵖ cascade t ≡ true → Timer.due tm ≤ Timer.due t × cascade tm <ᵖ cascade t ≡ true
      after {t} lt = <ᵖ-tick (Timer.due tm) (Timer.due t) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from t) ∷ []) lt , lt

    pos< : State.pos st <ᵖ cascade tm ≡ true
    pos< = go e (proj₂ (Queue.ordered q))
      where go : ∀ {xs} → xs ≡ tm ∷ ts → All (λ t → State.clock st ≤ Timer.due t × State.pos st <ᵖ cascade t ≡ true) xs
               → State.pos st <ᵖ cascade tm ≡ true
            go refl ((_ , lt) ∷ _) = lt

    past′ : All (λ j → cascade tm <ᵖ Joiner.at′ j ≡ false) (joiners t [])
    past′ = All.map (λ {j} → later-false (State.pos st) (cascade tm) (Joiner.at′ j) pos<) (Queue.past q)

    ordered′ : Ordered St′
    ordered′ = Linked.tail linked , All.map (λ {t} → after {t}) (linked-all (λ {a} {b} {c} → <ᵖ-trans (cascade a) (cascade b) (cascade c)) linked)

    books′ : Books st t → Books St′ t
    books′ bk = record { fresh = Books.fresh bk ; clocked = refl ; running = Books.running bk }

  -- A stale timer, its cold spent since it was set: the run moves to its
  -- cascade and on, and the meaning does not move.
  stale : ∀ {h} {st : State h} {c} {tm : Timer h} {ts : List (Timer h)} → Carried ⟨ st , turn ⟩ c → State.timers st ≡ tm ∷ ts → spent? st (Timer.handle tm) ≡ true
        → Carried ⟨ record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm } , turn ⟩ c
  stale {st = st} {tm = tm} {ts} r e sp = record
    { tree    = tree
    ; ctlAs   = ctlAs
    ; open≡   = open≡
    ; owned   = owned
    ; kernels = kernels
    ; meaning = meaning
    ; queue   = record { past = past′ ; timed = timed ; joined = Queue.joined queue ; ordered = ordered′ }
    ; books   = books′ books
    }
    where
      open Carried r
      open At (State.heap st) using (spentʰ)
      open Moved tree queue e

      timed : At.Timed (State.heap st) ts (pendings tree)
      timed with subst (λ xs → At.Timed (State.heap st) xs (pendings tree)) e (Queue.timed queue)
      ... | _ ∷ live , owed = live , All.map gone owed
        where gone : ∀ {t} → (spentʰ (Timer.handle t) ≡ false → t ∈ tm ∷ ts) → spentʰ (Timer.handle t) ≡ false → t ∈ ts
              gone f u with f u
              ... | here refl = ⊥-elim (bad (trans (sym u) sp))
                where bad : false ≡ true → _
                      bad ()
              ... | there m   = m

  -- A queued frame's cold, waiting on it.
  data Pended {h Δ₀ A₀} (t : Sub h Δ₀ A₀) : Timer h → Set₁ where
    pended : ∀ {Δ A u t′} {s : Sink h A} {hd τ e} {x : u ≤ t′} {b : Frame A t′} → Path t (coldˢ {Δ = Δ} s hd (waiting τ e (at t′ x b)))
           → Pended t (record { due = τ + t′ ; sink = s ; handle = hd ; at′ = t′ ; from = e ; frame = b })

  private
    under : ∀ {h Δ₀ A₀ Δ₁ A₁} {t : Sub h Δ₀ A₀} {t′ : Sub h Δ₁ A₁} {tm} → (∀ {Δ C} {u : Sub h Δ C} → Path t u → Path t′ u) → Pended t tm → Pended t′ tm
    under f (pended π) = pended (f π)

  mutual
    -- Every pending frame is a waiting cold's.
    pended-at : ∀ {h Δ A tm} (t : Sub h Δ A) → tm ∈ pendings t → Pended t tm
    pended-at (pendingˢ s q)                         ()
    pended-at (coldˢ s hd (waiting τ e (at t′ x b))) (here refl) = pended here
    pended-at (coldˢ s hd (waiting τ e (at t′ x b))) (there ())
    pended-at (ofˢ p i xs)                           ()
    pended-at doneˢ                                  ()
    pended-at (mapˢ f s)                             m = under in-map (pended-at s m)
    pended-at (scanˢ f r s)                          m = under in-scan (pended-at s m)
    pended-at (takeWhileˢ i p cu k tk s)             m = under in-take (pended-at s m)
    pended-at (flatMapˢ op f fl oc k r so ls)        m with ∈-++⁻ (pendings so) m
    ... | inj₁ m′ = under in-outer (pended-at so m′)
    ... | inj₂ m′ = laned-at ls in-lanes m′
    pended-at (connectˢ s₁ p S cu k fd e₀ src body) m with ∈-++⁻ (pendings src) m
    ... | inj₁ m′ = under in-source (pended-at src m′)
    ... | inj₂ m′ = under in-body (pended-at body m′)
    pended-at (joinˢ j sk l x st)                   ()
    pended-at (deferˢ k s)                           m = under in-defer (pended-at s m)

    laned-at : ∀ {h Δ₀ A₀ Δ B tm} {t′ : Sub h Δ₀ A₀} (ls : List (Lane h Δ B))
             → (∀ {Δ C} {u : Sub h Δ C} → PathLanes ls u → Path t′ u) → tm ∈ lanePendings ls → Pended t′ tm
    laned-at (lane cu k s ∷ ls) f m with ∈-++⁻ (pendings s) m
    ... | inj₁ m′ = under (λ π → f (this-lane π)) (pended-at s m′)
    ... | inj₂ m′ = laned-at ls (λ π → f (next-lane π)) m′

  private
    popped : ∀ {h} {st : State h} {c} {tm : Timer h} {ts : List (Timer h)} (t : Sub h [] R) → At.part (State.heap st) t ≡ just c
           → Owned (State.heap st) t Against.calmAs → Kernels (State.heap st) t → Meaning (State.heap st) t → (q : Queue st t []) → Books st t
           → (e : State.timers st ≡ tm ∷ ts) → Pended t tm
           → Carried ⟨ record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }
                    , burst (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same loop ⟩ c
    popped {st = st} {ts = ts} t o≡ ow ks mn q bk e (pended π) = record
      { tree    = t
      ; ctlAs   = Against.fireAs refl π Against.loopAs
      ; open≡   = o≡
      ; owned   = record { ofs = Owned.ofs ow ; plays = λ π′ l → there (Owned.plays ow π′ l) ; begun = Owned.begun ow
                         ; ends = Owned.ends ow ; cuts = Owned.cuts ow ; feeds = Owned.feeds ow ; fins = Owned.fins ow }
      ; kernels = ks
      ; meaning = mn
      ; queue   = record { past = past′ ; timed = subst (λ xs → At.Timed (State.heap st) xs (pendings t)) e (Queue.timed q)
                         ; joined = Queue.joined q ; ordered = ordered′ }
      ; books   = books′ bk
      }
      where open Moved t q e

  -- A live timer popped: the run moves to its cascade, bursting the frame
  -- its cold still waits on, and the meaning does not move.
  pop : ∀ {h} {st : State h} {c} {tm : Timer h} {ts : List (Timer h)} → Carried ⟨ st , turn ⟩ c → State.timers st ≡ tm ∷ ts → spent? st (Timer.handle tm) ≡ false
      → Carried ⟨ record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }
               , burst (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same loop ⟩ c
  pop {st = st} {c} {tm} {ts} r e sp = go (Carried.ctlAs r) (Carried.owned r) (Carried.queue r)
    where
      open Carried r using (tree; open≡; kernels; meaning; books)

      queued : Queue st tree [] → tm ∈ pendings tree
      queued q with subst (λ xs → At.Timed (State.heap st) xs (pendings tree)) e (Queue.timed q)
      ... | (inj₁ dead ∷ _) , _ = ⊥-elim (bad (trans (sym sp) dead))
        where bad : false ≡ true → _
              bad ()
      ... | (inj₂ m ∷ _) , _    = m

      go : (ca : Against.CtlAs tree turn) → Owned (State.heap st) tree ca → Queue st tree (firing ca)
         → Carried ⟨ record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }
                  , burst (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same loop ⟩ c
      go Against.calmAs ow q = popped tree open≡ ow kernels meaning q books e (pended-at tree (queued q))

  postulate
    -- No timer queued: every subscription still open waits on nothing,
    -- so the meaning falls quiet by silent steps.
    calm-hush : ∀ {h} {st : State h} {c} → Carried ⟨ st , turn ⟩ c → State.timers st ≡ [] → Quiets c

  ------------------------------------------------------------------------
  -- C: the measure

  -- What a subscription costs before it waits: one step per operator
  -- reached synchronously, a cold its start, its check and its first
  -- frame.
  weighᴼ : ∀ {C Γ A} → Obs C Γ A → ℕ
  weighᴼ (T.cold _)          = 3
  weighᴼ (T.map f s)         = suc (weighᴼ s)
  weighᴼ (T.scan f z s)      = suc (weighᴼ s)
  weighᴼ (T.takeWhile i p s) = suc (weighᴼ s)
  weighᴼ (T.flatMap op f s)  = suc (weighᴼ s)
  weighᴼ (T.connect s b)     = suc (weighᴼ s + weighᴼ b)
  weighᴼ _                   = 1

  -- The synchronous work a carried state owes before the meaning must
  -- move: each call on the agenda, a feed one per joiner; each burst in
  -- flight; each subscription reached and not begun.
  module Weigh {h} (t : Sub h [] R) where
    open Against t

    weighU : ∀ {Δ A} → Sub h Δ A → ℕ
    weighU (pendingˢ s q) = weighᴼ s
    weighU _              = 0

    weighC : Call t → ℕ
    weighC (feedC {ss = ss} π) = suc (length ss)
    weighC (finC {ss = ss} π)  = suc (length ss)
    weighC _                   = 1

    work : ∀ {ctl} → CtlAs ctl → ℕ
    work ca = sum (mapᴸ weighC (agenda ca)) + length (bursts ca) + sum (mapᴸ (λ x → weighU (Spot.u x)) (begins ca))

  -- The work owed, and a timer per frame still to fire.
  weight : ∀ {m c} → Carried m c → ℕ
  weight {m} r = Weigh.work (Carried.tree r) (Carried.ctlAs r) + length (State.timers (Mach.state m))

  -- The simulation already kept at every lighter carried state: what a
  -- step re-entering the relation with the meaning unmoved is handed.
  Lighter : ∀ {m c} → Carried m c → Set₁
  Lighter r = ∀ {m′ c′} (r′ : Carried m′ c′) → weight r′ < weight r → Wait Carried (step m′) (stepᵁ c′)

  -- Silent machine steps, the meaning unmoved.
  data Lefts : Mach → Mach → Set₁ where
    stay : ∀ {m} → Lefts m m
    next : ∀ {m m′ m″} → step m ≡ silent m′ → Lefts m′ m″ → Lefts m m″

  lefts : ∀ {m m′ s} → Lefts m m′ → Wait Carried (step m′) s → Wait Carried (step m) s
  lefts stay       w = w
  lefts (next e l) w rewrite e = left (lefts l w)

  private
    calm-work : ∀ {h} {t : Sub h [] R} (ca : Against.CtlAs t turn) → Weigh.work t ca ≡ 0
    calm-work Against.calmAs = refl

    fire-work : ∀ {h} {t : Sub h [] R} {A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u}
              → (ca : Against.CtlAs t (burst s hd τ p i b same loop)) → Weigh.work t ca ≡ 1
    fire-work (Against.burstAs π Against.loopAs)  = refl
    fire-work (Against.fireAs _ π Against.loopAs) = refl

  calm-weight : ∀ {h} {st : State h} {c} (r : Carried ⟨ st , turn ⟩ c) → weight r ≡ length (State.timers st)
  calm-weight {st = st} r = cong (_+ length (State.timers st)) (calm-work (Carried.ctlAs r))

  fire-weight : ∀ {h} {st : State h} {A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {c}
              → (r : Carried ⟨ st , burst s hd τ p i b same loop ⟩ c) → weight r ≡ suc (length (State.timers st))
  fire-weight {st = st} r = cong (_+ length (State.timers st)) (fire-work (Carried.ctlAs r))

  ------------------------------------------------------------------------
  -- B kept

  postulate
    -- Code running: the agenda's next call, or a subscription beginning.
    --
    -- At a connect's feed the meaning has fed every joiner at once, at
    -- the connect's skip, and the first owed joiner's value at
    -- `q ++ [ sub j ]` is its next shown event only if every other live
    -- node's next is past it.  `Carried` holds nothing positional for
    -- nodes the agenda does not owe, so this step needs a field placing
    -- each live node's next shown event past the agenda's region.
    kept-run : ∀ {h} {st : State h} {w B} {a : Act h B} {σ : w ⊑ h} {K : Stack w B} {c}
             → (r : Carried ⟨ st , run a σ K ⟩ c) → Lighter r → Wait Carried (step ⟨ st , run a σ K ⟩) (stepᵁ c)

    -- A burst whose cold is spent returns to what waits on it: the
    -- burst leaves the agenda, so whatever the return re-enters is
    -- lighter, and the meaning shows nothing of a spent cold.
    returned : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤} {c}
             → (r : Carried ⟨ st , burst s hd τ p i b σ K ⟩ c) → spent? st hd ≡ true → Lighter r
             → Wait Carried (step ⟨ st , ret tt σ K ⟩) (stepᵁ c)

    -- An unspent cold's subscriber reads open, its check only reading
    -- the heap.
    asks-open : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤} {c}
              → Carried ⟨ st , burst s hd τ p i b σ K ⟩ c → spent? st hd ≡ false
              → Lefts ⟨ st , run (Callbacks.isClosed (cbs st s)) same (push (asked s hd τ p i b) σ K) ⟩
                      ⟨ st , ret false same (push (asked s hd τ p i b) σ K) ⟩

    -- The frame's step is a value: the meaning's next event is it, at
    -- `p ++ [ ix i ]`, every other open node waiting past that.
    burst-emit : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {a k} {σ : w ⊑ h} {K : Stack w ⊤} {c}
               → (r : Carried ⟨ st , burst s hd τ p i (emit {A} {u} a k) σ K ⟩ c) → spent? st hd ≡ false → Lighter r
               → Wait Carried (step ⟨ st , ret false same (push (asked s hd τ p i (emit a k)) σ K) ⟩) (stepᵁ c)

    -- The frame's step is a stall: the meaning skips it, every other
    -- open node waiting past it.
    burst-stall : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {k} {σ : w ⊑ h} {K : Stack w ⊤} {c}
                → (r : Carried ⟨ st , burst s hd τ p i (stall {A} {u} k) σ K ⟩ c) → spent? st hd ≡ false → Lighter r
                → Wait Carried (step ⟨ st , ret false same (push (asked s hd τ p i (stall k)) σ K) ⟩) (stepᵁ c)

    -- The frame closes: the cold completes, falls quiet, or waits on a
    -- timer due past the clock.
    burst-close : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {k} {σ : w ⊑ h} {K : Stack w ⊤} {c}
                → (r : Carried ⟨ st , burst s hd τ p i (close {A} {u} k) σ K ⟩ c) → spent? st hd ≡ false → Lighter r
                → Wait Carried (step ⟨ st , ret false same (push (asked s hd τ p i (close k)) σ K) ⟩) (stepᵁ c)

  -- A burst whose cold is spent returns at once.
  burst-spent : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤}
              → spent? st hd ≡ true → step ⟨ st , burst s hd τ p i b σ K ⟩ ≡ silent ⟨ st , ret _ σ K ⟩
  burst-spent e rewrite e = refl

  -- Otherwise it asks its subscriber whether it is closed.
  burst-open : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤}
             → spent? st hd ≡ false
             → step ⟨ st , burst s hd τ p i b σ K ⟩ ≡ silent ⟨ st , run (Callbacks.isClosed (cbs st s)) same (push (asked s hd τ p i b) σ K) ⟩
  burst-open e rewrite e = refl

  played : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} (b : Frame A u) {σ : w ⊑ h} {K : Stack w ⊤} {c}
         → (r : Carried ⟨ st , burst s hd τ p i b σ K ⟩ c) → spent? st hd ≡ false → Lighter r
         → Wait Carried (step ⟨ st , ret false same (push (asked s hd τ p i b) σ K) ⟩) (stepᵁ c)
  played (emit a k) = burst-emit
  played (stall k)  = burst-stall
  played (close k)  = burst-close

  -- A cold's frame at its next step, its subscriber asked if closed; or
  -- a popped timer's at its first, its cold still waiting on it.
  kept-burst : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤} {c}
             → (r : Carried ⟨ st , burst s hd τ p i b σ K ⟩ c) → Lighter r → Wait Carried (step ⟨ st , burst s hd τ p i b σ K ⟩) (stepᵁ c)
  kept-burst {st = st} {hd = hd} {b = b} {c = c} r lt = by (spent? st hd) refl
    where
      by : (x : Bool) → spent? st hd ≡ x → Wait Carried (step ⟨ st , burst _ hd _ _ _ b _ _ ⟩) (stepᵁ c)
      by true  sp = subst (λ x → Wait Carried x (stepᵁ c)) (sym (burst-spent sp)) (left (returned r sp lt))
      by false sp = subst (λ x → Wait Carried x (stepᵁ c)) (sym (burst-open sp)) (left (lefts (asks-open r sp) (played b r sp lt)))

  private
    fired : ∀ {h} {st : State h} {c} {tm : Timer h} {ts : List (Timer h)} (r : Carried ⟨ st , turn ⟩ c) (e : State.timers st ≡ tm ∷ ts)
            (sp : spent? st (Timer.handle tm) ≡ false) → Lighter r → Lighter (pop r e sp)
    fired r e sp lt r′ l = lt r′ (subst (weight r′ <_) (trans (fire-weight (pop r e sp)) (sym (trans (calm-weight r) (cong length e)))) l)

    staled : ∀ {h} {st : State h} {c} {tm : Timer h} {ts : List (Timer h)} (r : Carried ⟨ st , turn ⟩ c) (e : State.timers st ≡ tm ∷ ts)
             (sp : spent? st (Timer.handle tm) ≡ true) → Lighter r → Lighter (stale r e sp)
    staled {ts = ts} r e sp lt r′ l =
      lt r′ (<-trans l (subst₂ _<_ (sym (calm-weight (stale r e sp))) (sym (trans (calm-weight r) (cong length e))) (n<1+n (length ts))))

  -- A queued timer pops.
  turn-pop : ∀ {h} {st : State h} {tm : Timer h} {ts : List (Timer h)} → State.timers st ≡ tm ∷ ts
           → step ⟨ st , turn ⟩ ≡ silent ⟨ record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }
                                        , burst (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same loop ⟩
  turn-pop e rewrite e = refl

  calm : ∀ {h} (ts : List (Timer h)) {st : State h} {c} → State.timers st ≡ ts → (r : Carried ⟨ st , turn ⟩ c) → Lighter r
       → Wait Carried (step ⟨ st , turn ⟩) (stepᵁ c)
  calm []        e r lt with calm-hush r e
  ... | q rewrite e = quiets q
  calm (tm ∷ ts) {st = st} {c} e r lt with spent? st (Timer.handle tm) in sp
  ... | false = subst (λ x → Wait Carried x (stepᵁ c)) (sym (turn-pop e)) (left (kept-burst (pop r e sp) (fired r e sp lt)))
  ... | true  = subst (λ x → Wait Carried x (stepᵁ c)) (sym (turn-pop e))
                  (left (subst (λ x → Wait Carried x (stepᵁ c)) (sym (burst-spent sp)) (left (left (calm ts refl (stale r e sp) (staled r e sp lt))))))

  keep : ∀ {m c} (r : Carried m c) → Lighter r → Wait Carried (step m) (stepᵁ c)
  keep {⟨ st , run a σ K ⟩}              r lt = kept-run r lt
  keep {⟨ st , ret x σ K ⟩}              r lt with Carried.ctlAs r
  ... | ()
  keep {⟨ st , burst s hd τ p i b σ K ⟩} r lt = kept-burst r lt
  keep {⟨ st , turn ⟩}                   r lt = calm _ refl r lt

  -- C: each step the meaning does not take with the machine re-enters
  -- the relation lighter.
  kept-under : ∀ n {m c} (r : Carried m c) → weight r < n → Wait Carried (step m) (stepᵁ c)
  kept-under zero    r ()
  kept-under (suc n) r w< = keep r λ r′ l → kept-under n r′ (≤-trans l (s≤s⁻¹ w<))

  -- Every node due before the next turn is owed (`Owned`): without it a
  -- state between turns with an `of` open steps drained while the
  -- meaning shows the `of`'s value, and `adequacy.Simulation.unowned`
  -- keeps that state out.
  kept : ∀ {m c} → Carried m c → Wait Carried (step m) (stepᵁ c)
  kept r = kept-under (suc (weight r)) r ≤-refl
