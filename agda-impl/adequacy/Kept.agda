{-# OPTIONS --guardedness --large-indices #-}

-- B KEPT, C FINITE: a carried state's next step, against its
-- configuration's, passes each side alone finitely often before the two
-- meet again carried, or end, or fall quiet together.  Split by what the
-- machine is doing: running code, bursting a cold's frame, or between
-- turns.  The relation never rests at a return.
module adequacy.Kept where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Linked as Linked
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import denotation.MonotonicList using (Pos; _<ᵖ_; <ᵖ-trans; <ᵖ-tick) renaming (sub to subᴾ)
open import denotation.Unfold using (Node; hushˢ; skipˢ) renaming (step to stepᵁ)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; World; _⊑_; Sink; Handle; module Pure)
open import operation.Machine using (module Machine)
open import denotation.MonotonicList using (Frame)
open import adequacy.Carrier using (module Carrying)
open import adequacy.Wait using (module Waiting)

module Keeping (R : Set) where
  open Run (Pureᴾ R) using (Act)
  open Pure R using (State; Timer; cascade)
  open Machine R using (Mach; ⟨_,_⟩; Stack; run; ret; burst; turn; step; silent; drained; spent?)
  open Carrying R using (Carried; module At; Lags; stay; skip; drop; Ordered; Sub; Lane; lane
                        ; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ
                        ; Meaning; Queue; Books; pendings; joiners; Joiner)
  open Waiting R using (Wait; idles; left; right)

  ------------------------------------------------------------------------
  -- The run moving on: a later position

  private
    later-false : ∀ p q x → p <ᵖ q ≡ true → p <ᵖ x ≡ false → q <ᵖ x ≡ false
    later-false p q x pq px with q <ᵖ x in qx
    ... | false = refl
    ... | true  with trans (sym (<ᵖ-trans p q x pq qx)) px
    ...   | ()

  -- A lag behind `p` is a lag behind any position past it.
  lags-later : ∀ {A} {p q : Pos} {c n : Node A} → p <ᵖ q ≡ true → Lags p c n → Lags q c n
  lags-later lt stay         = stay
  lags-later lt (skip e l)   = skip e (lags-later lt l)
  lags-later {p = p} {q} lt (drop {q = k} e nl l) = drop e (later-false p q k lt nl) (lags-later lt l)

  module _ {h : World} (H : _) where
    open At {h} H using (Caught; CaughtLanes; History; part)

    history-later : ∀ {A p q} {s₀ : Node A} (m : Maybe (Node A)) → p <ᵖ q ≡ true → History p s₀ m → History q s₀ m
    history-later (just n) lt l = lags-later lt l
    history-later nothing  lt l = l

    mutual
      caught-later : ∀ {p q Δ A} → p <ᵖ q ≡ true → (t : Sub h Δ A) → ∀ ρ ν → Caught p t ρ ν → Caught q t ρ ν
      caught-later lt (pendingˢ s q)                         ρ ν c = c
      caught-later lt (coldˢ s hd ph)                        ρ ν c = c
      caught-later lt (ofˢ p i xs)                           ρ ν c = c
      caught-later lt doneˢ                                  ρ ν c = c
      caught-later lt (mapˢ f s)                             ρ ν c = caught-later lt s ρ ν c
      caught-later lt (scanˢ f r s)                          ρ ν c = caught-later lt s ρ ν c
      caught-later lt (takeWhileˢ i p cu k tk s)             ρ ν c = caught-later lt s ρ ν c
      caught-later lt (flatMapˢ op f fl oc k r so ls)        ρ ν (co , cl) = caught-later lt so ρ ν co , lanes-later lt ls ρ ν cl
      caught-later lt (connectˢ s₁ p S cu k fd s₀ m src body) ρ ν (hi , cs , cb) =
        history-later (part src ρ) lt hi , caught-later lt src ρ ν cs , caught-later lt body _ _ cb
      caught-later lt (joinˢ j i sk l x (just cp))           ρ ν c = c
      caught-later lt (joinˢ j i sk l x nothing)             ρ ν c = c
      caught-later lt (deferˢ k s)                           ρ ν c = caught-later lt s ρ ν c

      lanes-later : ∀ {p q Δ B} → p <ᵖ q ≡ true → (ls : List (Lane h Δ B)) → ∀ ρ ν → CaughtLanes p ls ρ ν → CaughtLanes q ls ρ ν
      lanes-later lt []                ρ ν c        = c
      lanes-later lt (lane cu k s ∷ ls) ρ ν (cs , cl) = caught-later lt s ρ ν cs , lanes-later lt ls ρ ν cl

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
  data Quiets : Node R → Set₁ where
    hushes : ∀ {c} → stepᵁ c ≡ hushˢ → Quiets c
    skips  : ∀ {c c′ q} → stepᵁ c ≡ skipˢ q c′ → Quiets c′ → Quiets c

  quiets : ∀ {c} → Quiets c → Wait Carried drained (stepᵁ c)
  quiets (hushes e) rewrite e = idles
  quiets (skips e q) rewrite e = right (quiets q)

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
    ; meaning = record { caught = caught-later (State.heap st) pos< tree [] [] (Meaning.caught meaning) }
    ; queue   = record { past = All.map (λ {j} → later-false (State.pos st) (cascade tm) (Joiner.at′ j) pos<) (Queue.past queue) ; timed = timed ; joined = Queue.joined queue
                       ; ordered = Linked.tail linked , All.map (λ {t} → after {t}) (linked-all (λ {a} {b} {c} → <ᵖ-trans (cascade a) (cascade b) (cascade c)) linked) }
    ; books   = record { fresh = Books.fresh books ; clocked = refl ; running = Books.running books }
    }
    where
      open Carried r
      open At (State.heap st) using (spentʰ)

      linked : Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (tm ∷ ts)
      linked = subst (Linked _) e (proj₁ (Queue.ordered queue))

      pos< : State.pos st <ᵖ cascade tm ≡ true
      pos< = go e (proj₂ (Queue.ordered queue))
        where go : ∀ {xs} → xs ≡ tm ∷ ts → All (λ t → State.clock st ≤ Timer.due t × State.pos st <ᵖ cascade t ≡ true) xs
                 → State.pos st <ᵖ cascade tm ≡ true
              go refl ((_ , lt) ∷ _) = lt

      after : ∀ {t} → cascade tm <ᵖ cascade t ≡ true → Timer.due tm ≤ Timer.due t × cascade tm <ᵖ cascade t ≡ true
      after {t} lt = <ᵖ-tick (Timer.due tm) (Timer.due t) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from t) ∷ []) lt , lt

      timed : At.Timed (State.heap st) ts (pendings tree)
      timed with subst (λ xs → At.Timed (State.heap st) xs (pendings tree)) e (Queue.timed queue)
      ... | _ ∷ live , owed = live , All.map gone owed
        where gone : ∀ {t} → (spentʰ (Timer.handle t) ≡ false → t ∈ tm ∷ ts) → spentʰ (Timer.handle t) ≡ false → t ∈ ts
              gone f u with f u
              ... | here refl = ⊥-elim (bad (trans (sym u) sp))
                where bad : false ≡ true → _
                      bad ()
              ... | there m   = m

  postulate
    -- No timer queued: every subscription still open waits on nothing,
    -- and its copies and held sources catch up by silent steps.
    calm-hush : ∀ {h} {st : State h} {c} → Carried ⟨ st , turn ⟩ c → State.timers st ≡ [] → Quiets c

    -- The next timer's cold live: its frame's first step is the meaning's
    -- next event at its cascade, everything else open waiting past it.
    calm-fire : ∀ {h} {st : State h} {c} {tm : Timer h} {ts : List (Timer h)} → Carried ⟨ st , turn ⟩ c → State.timers st ≡ tm ∷ ts → spent? st (Timer.handle tm) ≡ false
              → Wait Carried (step ⟨ st , turn ⟩) (stepᵁ c)

  -- A burst whose cold is spent returns at once.
  burst-spent : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤}
              → spent? st hd ≡ true → step ⟨ st , burst s hd τ p i b σ K ⟩ ≡ silent ⟨ st , ret _ σ K ⟩
  burst-spent e rewrite e = refl

  calm : ∀ {h} (ts : List (Timer h)) {st : State h} {c} → State.timers st ≡ ts → Carried ⟨ st , turn ⟩ c → Wait Carried (step ⟨ st , turn ⟩) (stepᵁ c)
  calm []        e r with calm-hush r e
  ... | q rewrite e = quiets q
  calm (tm ∷ ts) {st = st} {c} e r with spent? st (Timer.handle tm) in sp
  ... | false = calm-fire r e sp
  ... | true rewrite e = left (subst (λ x → Wait Carried x (stepᵁ c)) (sym (burst-spent sp)) (left (left (calm ts refl (stale r e sp)))))

  ------------------------------------------------------------------------
  -- B kept

  postulate
    -- Code running: the agenda's next call, or a subscription beginning.
    --
    -- At a connect's feed the meaning's next shown event is the first
    -- owed joiner's, at `q ++ [ sub j ]`, only if every other live node
    -- reaches past it by silent steps; between the connect's own skip and
    -- that delivery lie only the lag steps of joiners subscribed mid-feed.
    -- `Carried` holds nothing positional for nodes the agenda does not
    -- owe, so this step needs a field placing each live node's next shown
    -- event past the agenda's region.
    --
    -- RECOVERY: `git show b75ee016` restores `adequacy.FeedTry`: an owed
    --   joiner reaches its delivery after its lag's silent steps
    --   (`joiner-delivers`).
    kept-run : ∀ {h} {st : State h} {w B} {a : Act h B} {σ : w ⊑ h} {K : Stack w B} {c}
             → Carried ⟨ st , run a σ K ⟩ c → Wait Carried (step ⟨ st , run a σ K ⟩) (stepᵁ c)

    -- A cold's frame at its next step, its subscriber asked if closed.
    kept-burst : ∀ {h} {st : State h} {w A u} {s : Sink h A} {hd : Handle h} {τ p i} {b : Frame A u} {σ : w ⊑ h} {K : Stack w ⊤} {c}
               → Carried ⟨ st , burst s hd τ p i b σ K ⟩ c → Wait Carried (step ⟨ st , burst s hd τ p i b σ K ⟩) (stepᵁ c)

  -- Every node due before the next turn is owed (`Owned`): without it a
  -- state between turns with an `of` open steps drained while the
  -- meaning shows the `of`'s value, and `adequacy.Simulation.unowned`
  -- keeps that state out.
  kept : ∀ {m c} → Carried m c → Wait Carried (step m) (stepᵁ c)
  kept {⟨ st , run a σ K ⟩}                r = kept-run r
  kept {⟨ st , ret x σ K ⟩}                r with Carried.ctlAs r
  ... | ()
  kept {⟨ st , burst s hd τ p i b σ K ⟩}   r = kept-burst r
  kept {⟨ st , turn ⟩}                     r = calm _ refl r
