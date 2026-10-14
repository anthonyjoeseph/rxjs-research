{-# OPTIONS --guardedness --large-indices #-}

-- A DELIVERY CLIMBS ITS CONTEXT.  At a hole, the delivery runs the
-- hole's frame's observer, which does its kernel's work and delivers on
-- to its parent's — a hole one frame up, in whatever world the work grew
-- the heap to.  So a delivery at a context is a delivery at each frame
-- given one at the context above it, and at every context it can grow to:
-- by recursion on the depth, which growing keeps.
--
-- A `map` and a `defer` only relabel: the frame's observer is its
-- parent's, and the hole one frame up is the plugged witness under the
-- frame's meaning.  So is a `scan`'s completion.
module adequacy.deliver.Climb where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Pos; Timeline) renaming (sub to subᴾ)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Run; base; list; sink; _⊗_)
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Pureᴾ; World; Sink; same; grow; _⨾_; module Pure) renaming (_⊑_ to _⊑ʷ_)
open import adequacy.Realize using (module Realizing)
open import adequacy.Segment using (module Seg)
open import adequacy.deliver.Context using (module Contexts)
open import adequacy.deliver.Mid using (module Middles)

-- Growing a world from where it stands, and in steps.
same-⨾ : ∀ {u v} (τ : u ⊑ʷ v) → same ⨾ τ ≡ τ
same-⨾ same     = refl
same-⨾ (grow τ) = cong grow (same-⨾ τ)

⨾-assoc : ∀ {u v w x} (ρ : u ⊑ʷ v) (σ : v ⊑ʷ w) (τ : w ⊑ʷ x) → (ρ ⨾ σ) ⨾ τ ≡ ρ ⨾ (σ ⨾ τ)
⨾-assoc ρ σ same     = refl
⨾-assoc ρ σ (grow τ) = cong grow (⨾-assoc ρ σ τ)

module Climbing (R : Set) where
  open Machine R using (⟨_,_⟩; run; ret; push; rest; Stack; cbs; trace)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Realizing R
  open Contexts R
  open Middles R
  open Pure R using (State; Callbacks)
  open Seg R

  ------------------------------------------------------------------------
  -- A delivery at a context

  NextAt : ∀ {h Δ A} → Ctx h Δ A → Set₁
  NextAt {h} k = ∀ {L : Owed} {t n fs c} {st : State h} {q a n′}
               → Mid L k t (just n) fs c st → U.step n ≡ U.outˢ q a n′ → State.pos st ≡ q → AtC.Fore (State.heap st) k q
               → ∀ {act} → act ≗ Observer.next (obsC k) a
               → ∀ {w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
               → (∀ {v} (τ : h ⊑ʷ v) {st′ : State v} {c′} → Back L τ k t q (just n′) fs c′ st′
                  → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ) K ⟩) (U.unfold c′))
               → ∀ {bd} → Seg bd (trace ⟨ st , run act σ K ⟩) (U.unfold c)

  DoneAt : ∀ {h Δ A} → Ctx h Δ A → Set₁
  DoneAt {h} k = ∀ {L : Owed} {t n fs c} {st : State h} {q}
               → Mid L k t (just n) fs c st → U.step n ≡ U.endˢ q → State.pos st ≡ q → AtC.Fore (State.heap st) k q
               → ∀ {act} → act ≗ Observer.complete (obsC k)
               → ∀ {w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
               → (∀ {v} (τ : h ⊑ʷ v) {st′ : State v} {c′} → Back L τ k t q nothing fs c′ st′
                  → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ) K ⟩) (U.unfold c′))
               → ∀ {bd} → Seg bd (trace ⟨ st , run act σ K ⟩) (U.unfold c)

  Delivers : ∀ {h Δ A} → Ctx h Δ A → Set₁
  Delivers k = NextAt k × DoneAt k

  -- At a context, and at every context it grows to.
  Above : ∀ {h Δ A} → Ctx h Δ A → Set₁
  Above {h} k = Delivers k × (∀ {v} {τ : h ⊑ʷ v} {k′} → Grown τ k k′ → Delivers k′)

  depth : ∀ {h Δ A} → Ctx h Δ A → ℕ
  depth top     = zero
  depth (f ◂ k) = suc (depth k)

  grown-depth : ∀ {h v Δ A} {τ : h ⊑ʷ v} {k : Ctx h Δ A} {k′} → Grown τ k k′ → depth k ≡ depth k′
  grown-depth topᵍ       = refl
  grown-depth (_ ◂ᵍ g)   = cong suc (grown-depth g)

  ------------------------------------------------------------------------
  -- The frames that only relabel

  up-map : ∀ {h Δ A B L} {f : A → B} {k : Ctx h Δ B} {t : Sub h Δ A} {m fs c} {st : State h}
         → Mid L (mapF f ◂ k) t m fs c st → Mid L k (mapˢ f t) (At.mapᴹ (State.heap st) (U.mapᶜ f) m) fs c st
  up-map M = record
    { holds = holds ; open≡ = open≡ ; caughtC = proj₂ caughtC ; caught = caught ; gatedC = proj₂ gatedC ; gated = gated
    ; past = past ; firing≡ = firing≡ ; clocked = clocked ; behind = behind ; rooted = rooted ; timed = timed
    ; joined = joined ; ordered = ordered ; fresh = fresh ; running = running }
    where open Mid M

  down-map : ∀ {h Δ A B L} {f : A → B} {k : Ctx h Δ B} {t : Sub h Δ A} {m fs c} {st : State h}
           → Mid L k (mapˢ f t) (At.mapᴹ (State.heap st) (U.mapᶜ f) m) fs c st → Mid L (mapF f ◂ k) t m fs c st
  down-map M = record
    { holds = holds ; open≡ = open≡ ; caughtC = lift tt , caughtC ; caught = caught ; gatedC = lift tt , gatedC ; gated = gated
    ; past = past ; firing≡ = firing≡ ; clocked = clocked ; behind = behind ; rooted = rooted ; timed = timed
    ; joined = joined ; ordered = ordered ; fresh = fresh ; running = running }
    where open Mid M

  back-map : ∀ {h v Δ A B L} {τ : h ⊑ʷ v} {f : A → B} {k : Ctx h Δ B} {t : Sub h Δ A} {q m′ fs c′} {st′ : State v}
           → Back L τ k (mapˢ f t) q (At.mapᴹ (State.heap st′) (U.mapᶜ f) m′) fs c′ st′ → Back L τ (mapF f ◂ k) t q m′ fs c′ st′
  back-map (back g (mapᵉ e) M Q) = back (mapᵍ ◂ᵍ g) e (down-map M) (lift tt , Q)

  up-defer : ∀ {h Δ A L} {u : Sink h ⊤} {k : Ctx h Δ A} {t : Sub h Δ A} {m fs c} {st : State h}
           → Mid L (deferF u ◂ k) t m fs c st → Mid L k (deferˢ u t) m fs c st
  up-defer M = record
    { holds = holds ; open≡ = open≡ ; caughtC = proj₂ caughtC ; caught = caught ; gatedC = proj₂ gatedC ; gated = gated
    ; past = past ; firing≡ = firing≡ ; clocked = clocked ; behind = behind ; rooted = rooted ; timed = timed
    ; joined = joined ; ordered = ordered ; fresh = fresh ; running = running }
    where open Mid M

  down-defer : ∀ {h Δ A L} {u : Sink h ⊤} {k : Ctx h Δ A} {t : Sub h Δ A} {m fs c} {st : State h}
             → Mid L k (deferˢ u t) m fs c st → Mid L (deferF u ◂ k) t m fs c st
  down-defer M = record
    { holds = holds ; open≡ = open≡ ; caughtC = lift tt , caughtC ; caught = caught ; gatedC = lift tt , gatedC ; gated = gated
    ; past = past ; firing≡ = firing≡ ; clocked = clocked ; behind = behind ; rooted = rooted ; timed = timed
    ; joined = joined ; ordered = ordered ; fresh = fresh ; running = running }
    where open Mid M

  back-defer : ∀ {h v Δ A L} {τ : h ⊑ʷ v} {u : Sink h ⊤} {k : Ctx h Δ A} {t : Sub h Δ A} {q m′ fs c′} {st′ : State v}
             → Back L τ k (deferˢ u t) q m′ fs c′ st′ → Back L τ (deferF u ◂ k) t q m′ fs c′ st′
  back-defer (back g (deferᵉ e) M Q) = back (deferᵍ ◂ᵍ g) e (down-defer M) (lift tt , Q)

  -- A scan's completion is its parent's: the accumulator is not read.
  up-scan : ∀ {h Δ A B L} {f : B → A → B} {r} {k : Ctx h Δ B} {t : Sub h Δ A} {m fs c} {st : State h}
          → Mid L (scanF f r ◂ k) t m fs c st
          → Mid L k (scanˢ f r t) (At.mapᴹ (State.heap st) (U.scanᶜ f (At.val (State.heap st) r)) m) fs c st
  up-scan M = record
    { holds = holds ; open≡ = open≡ ; caughtC = proj₂ caughtC ; caught = caught ; gatedC = proj₂ gatedC ; gated = gated
    ; past = past ; firing≡ = firing≡ ; clocked = clocked ; behind = behind ; rooted = rooted ; timed = timed
    ; joined = joined ; ordered = ordered ; fresh = fresh ; running = running }
    where open Mid M

  back-scan-done : ∀ {h v Δ A B L} {τ : h ⊑ʷ v} {f : B → A → B} {r} {k : Ctx h Δ B} {t : Sub h Δ A} {q fs c′} {st′ : State v}
                 → Back L τ k (scanˢ f r t) q nothing fs c′ st′ → Back L τ (scanF f r ◂ k) t q nothing fs c′ st′
  back-scan-done (back g (scanᵉ e) M Q) = back (scanᵍ ◂ᵍ g) e (down M) (lift tt , Q)
    where
      down : ∀ {k″ t″ fs″ c″} → Mid _ k″ (scanˢ _ _ t″) nothing fs″ c″ _ → Mid _ (scanF _ _ ◂ k″) t″ nothing fs″ c″ _
      down M′ = record
        { holds = holds ; open≡ = open≡ ; caughtC = lift tt , caughtC ; caught = caught ; gatedC = lift tt , gatedC ; gated = gated
        ; past = past ; firing≡ = firing≡ ; clocked = clocked ; behind = behind ; rooted = rooted ; timed = timed
        ; joined = joined ; ordered = ordered ; fresh = fresh ; running = running }
        where open Mid M′

  next-map : ∀ {h Δ A B} {f : A → B} {k : Ctx h Δ B} → Above k → NextAt (mapF f ◂ k)
  next-map {f = f} ((nx , _) , _) M e p (_ , F) a≗ κ = nx (up-map M) (cong (U.mapˢ f) e) p F a≗ λ τ B → κ τ (back-map B)

  done-map : ∀ {h Δ A B} {f : A → B} {k : Ctx h Δ B} → Above k → DoneAt (mapF f ◂ k)
  done-map {f = f} ((_ , dn) , _) M e p (_ , F) a≗ κ = dn (up-map M) (cong (U.mapˢ f) e) p F a≗ λ τ B → κ τ (back-map B)

  next-defer : ∀ {h Δ A} {u : Sink h ⊤} {k : Ctx h Δ A} → Above k → NextAt (deferF u ◂ k)
  next-defer ((nx , _) , _) M e p (_ , F) a≗ κ = nx (up-defer M) e p F a≗ λ τ B → κ τ (back-defer B)

  done-defer : ∀ {h Δ A} {u : Sink h ⊤} {k : Ctx h Δ A} → Above k → DoneAt (deferF u ◂ k)
  done-defer ((_ , dn) , _) M e p (_ , F) a≗ κ = dn (up-defer M) e p F a≗ λ τ B → κ τ (back-defer B)

  done-scan : ∀ {h Δ A B} {f : B → A → B} {r} {k : Ctx h Δ B} → Above k → DoneAt (scanF f r ◂ k)
  done-scan {f = f} {r} ((_ , dn) , _) {st = st} M e p (_ , F) a≗ κ =
    dn (up-scan M) (cong (U.scanˢ f (At.val (State.heap st) r)) e) p F a≗ λ τ B → κ τ (back-scan-done B)

  ------------------------------------------------------------------------
  -- The frames with work of their own

  postulate
    -- The root records the emit and returns.
    next-top : ∀ {h} → NextAt {h} top
    done-top : ∀ {h} → DoneAt {h} top

    -- The accumulator read and written, then the parent's delivery with
    -- the meaning's scan still before the emit.
    next-scan : ∀ {h Δ A B} {f : B → A → B} {r} {k : Ctx h Δ B} → Above k → NextAt (scanF f r ◂ k)

    -- Past the kill switch's guard; a failing predicate delivers its
    -- completion after its last value, then cuts the source — the hole.
    next-take : ∀ {h Δ A} {i} {p : A → Bool} {c u} {k : Ctx h Δ A} → Above k → NextAt (takeF i p c u ◂ k)
    done-take : ∀ {h Δ A} {i} {p : A → Bool} {c u} {k : Ctx h Δ A} → Above k → DoneAt (takeF i p c u ◂ k)

    -- An outer's value admitted: a lane subscribed beside the outer, or
    -- queued; a lane bursting inline delivers to the parent from a grown
    -- context.
    --
    -- The inline burst delivers at a hole inside the new lane, a context
    -- deeper than this frame's.  The meaning's own step here is a skip, so
    -- the run takes it as a guard and ends at a `delivering` calm point
    -- there, which the simulation resumes.
    --
    -- DEAD ROUTE: by `Above` alone.  No delivery at `k` or a growth of it
    --   reaches a context deeper than this frame's.
    next-outer : ∀ {h Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r ls} {k : Ctx h Δ B} → Above k → NextAt (outerF op f fl oc u r ls ◂ k)
    -- Its end settles the flatMap.
    done-outer : ∀ {h Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r ls} {k : Ctx h Δ B} → Above k → DoneAt (outerF op f fl oc u r ls ◂ k)

    -- A lane's value passed on.
    next-inner : ∀ {h Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r} {so : Sub h Δ A} {bs c d as} {k : Ctx h Δ B}
              → Above k → NextAt (laneF op f fl oc u r so bs c d as ◂ k)
    -- A lane's end hands on to the queue, a lane subscribed in its place.
    --
    -- DEAD ROUTE: by `Above` alone.  A lane dequeued may burst inline, at
    --   a context deeper than this frame's; as at `next-outer`.
    done-inner : ∀ {h Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r} {so : Sub h Δ A} {bs c d as} {k : Ctx h Δ B}
              → Above k → DoneAt (laneF op f fl oc u r so bs c d as ◂ k)

    -- The subject closed, each joiner finished.
    --
    -- DEAD ROUTE: by `Above` alone.  A joiner sits inside the body, a
    --   context deeper than this frame's, as at `next-outer`.
    done-source : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B}
                → Above k → DoneAt (sourceF S c u s₀ mm body ◂ k)

    -- A connect's body: its value its parent's; its end its parent's,
    -- then the source cut.
    next-body : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {src : Sub h Δ A} {k : Ctx h Δ B}
              → Above k → NextAt (bodyF S c u s₀ mm src ◂ k)
    done-body : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {src : Sub h Δ A} {k : Ctx h Δ B}
              → Above k → DoneAt (bodyF S c u s₀ mm src ◂ k)

  ------------------------------------------------------------------------
  -- A connect's source feeds its joiners

  -- A subject's subscribers, in a world.
  Subs : World → Set → Set
  Subs v A = El v (list (sink A ⊗ base Pos))

  wkSubs : ∀ {v v′ A} → v ⊑ʷ v′ → Subs v A → Subs v′ A
  wkSubs ρ = wkEl (list (sink _ ⊗ base Pos)) ρ

  wkSubs-same : ∀ {v A} (ss : Subs v A) → wkSubs same ss ≡ ss
  wkSubs-same []             = refl
  wkSubs-same ((s , j) ∷ ss) = cong ((s , j) ∷_) (wkSubs-same ss)

  wkSubs-length : ∀ {v v′ A} (ρ : v ⊑ʷ v′) (ss : Subs v A) → length (wkSubs ρ ss) ≡ length ss
  wkSubs-length ρ []       = refl
  wkSubs-length ρ (_ ∷ ss) = cong suc (wkSubs-length ρ ss)

  -- What the feeder does for one subscriber.
  feedOne : ∀ {v A} → Pos → A → Sink v A × Pos → Act v ⊤
  feedOne q a j = goto (q ++ [ subᴾ (proj₂ j) ]) (send (proj₁ j) a skipᴬ)

  wk-each : ∀ {v v′ A} {q} {a : A} (ss : Subs v A) {kk : Act v ⊤} (ρ : v ⊑ʷ v′)
          → kk ≗ each ss (feedOne q a) → wkAct ρ kk ≗ each (wkSubs ρ ss) (feedOne q a)
  wk-each []       ρ done≗              = done≗
  wk-each (_ ∷ ss) ρ (goto≗ (send≗ r)) = goto≗ (send≗ (wk-each ss ρ r))

  -- The source's event at `q`, owed to the subscribers `ss` not yet fed.
  Pend : ∀ {v A} → Owed → Pos → A → Subs v A → Owed
  Pend {A = A} L q a ss = map (λ j → A , q ++ [ subᴾ (proj₂ j) ] , just a) ss ++ L

  -- MID-FEED: the source's step to `n′` taken at `q`, showing `a`; in a
  -- world grown by `τ`, the subscribers `ss` left, each owed `a`.  The
  -- subject's subscribers are those fed, then `ss`, then any joined since.
  record Feeding {h v Δ A B} (L : Owed) (S : Subject A h) (c : Cut h) (u : Sink h ⊤) (s₀ : U.Node A) (mm : Maybe (U.Node A))
                 (body : Sub h (A ∷ Δ) B) (k : Ctx h Δ B) (t : Sub h Δ A) (q : Pos) (a : A) (n′ : U.Node A) (fs : List (Firing h))
                 (τ : h ⊑ʷ v) (ss : Subs v A) (c′ : U.Node R) (st′ : State v) : Set₁ where
    field
      {k′}    : Ctx v Δ A
      {t′}    : Sub v Δ A
      grown   : Grown τ (sourceF S c u s₀ mm body ◂ k) k′
      evolves : Evolves τ t t′
      mid     : Mid (Pend L q a ss) k′ t′ (just n′) (map (wkFiring τ) fs) c′ st′
      left    : Σ (Subs v A) λ fed → Σ (Subs v A) λ new
                → fed ++ ss ++ new ≡ At.val (State.heap st′) (Subject.subscribers (wkSubject τ S))

  -- The next subscriber of a feed, its position `j` the run's: silenced,
  -- or a joiner in the body about to be shown `a`, the feed resuming on
  -- the delivery's return.
  data Head {h v Δ A B} (L : Owed) (S : Subject A h) (c : Cut h) (u : Sink h ⊤) (s₀ : U.Node A) (mm : Maybe (U.Node A))
            (body : Sub h (A ∷ Δ) B) (k : Ctx h Δ B) (t : Sub h Δ A) (q : Pos) (a : A) (n′ : U.Node A) (fs : List (Firing h))
            (τ : h ⊑ʷ v) (sk : Sink v A) (j : Pos) (ss : Subs v A) (c′ : U.Node R) (st′ : State v) : Set₁ where
    hushed : ∀ {l : Ref v (base Bool)} {X : Act v ⊤}
           → At.val (State.heap st′) l ≡ false → Callbacks.onNext (cbs st′ sk) a ≗ readB l (λ b → when b X)
           → Feeding L S c u s₀ mm body k t q a n′ fs τ ss c′ (record st′ { pos = q ++ [ subᴾ j ] })
           → Head L S c u s₀ mm body k t q a n′ fs τ sk j ss c′ st′
    joins  : ∀ {Δj} {kj : Ctx v Δj A} {tj nj nj′} {l : Ref v (base Bool)}
           → At.val (State.heap st′) l ≡ true → Callbacks.onNext (cbs st′ sk) a ≗ readB l (λ b → when b (Observer.next (obsC kj) a))
           → Mid (Pend L q a ((sk , j) ∷ ss)) kj tj (just nj) (map (wkFiring τ) fs) c′ (record st′ { pos = q ++ [ subᴾ j ] })
           → U.step nj ≡ U.outˢ (q ++ [ subᴾ j ]) a nj′ → AtC.Fore (State.heap st′) kj (q ++ [ subᴾ j ])
           → (∀ {v′} (τ′ : v ⊑ʷ v′) {st″ : State v′} {c″}
              → Back (Pend L q a ((sk , j) ∷ ss)) τ′ kj tj (q ++ [ subᴾ j ]) (just nj′) (map (wkFiring τ) fs) c″ st″
              → Feeding L S c u s₀ mm body k t q a n′ fs (τ ⨾ τ′) (wkSubs τ′ ss) c″ st″)
           → Head L S c u s₀ mm body k t q a n′ fs τ sk j ss c′ st′

  postulate
    -- The source's event a skip of the connect, under the frames above:
    -- the body's next event is past it, the siblings' past every step
    -- under it.  Every subscriber is owed it.
    feed-start : ∀ {h Δ A B L} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B} {t n fs c₀} {st : State h} {a n′}
               → Mid L (sourceF S c u s₀ mm body ◂ k) t (just n) fs c₀ st → U.step n ≡ U.outˢ (State.pos st) a n′
               → AtC.Fore (State.heap st) (sourceF S c u s₀ mm body ◂ k) (State.pos st)
               → Passes c₀ (λ c₁ → Feeding L S c u s₀ mm body k t (State.pos st) a n′ fs same (At.val (State.heap st) (Subject.subscribers S)) c₁ st)

    -- A subscriber the subject holds: a joiner the tree holds, whose copy
    -- is owed `a`, or one silenced.
    feed-head : ∀ {h v Δ A B L} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B} {t q a n′ fs} {τ : h ⊑ʷ v}
                  {sk j ss c′} {st′ : State v}
              → Feeding L S c u s₀ mm body k t q a n′ fs τ ((sk , j) ∷ ss) c′ st′
              → Head L S c u s₀ mm body k t q a n′ fs τ sk j ss c′ st′

    -- Every subscriber fed: nothing owed but what was, the body past `q`.
    feed-end : ∀ {h v Δ A B L} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B} {t q a n′ fs} {τ : h ⊑ʷ v}
                 {c′} {st′ : State v}
             → Feeding L S c u s₀ mm body k t q a n′ fs τ [] c′ st′
             → Back L τ (sourceF S c u s₀ mm body ◂ k) t q (just n′) fs c′ st′

    -- Up to `_≗_`, a program in the world it was made in is itself.
    ≗-unweaken : ∀ {w B} {m m′ : Act w B} → m ≗ wkAct same m′ → m ≗ m′

  -- A silenced joiner's callback returns at once.
  hushed⇒ : ∀ {v} {st : State v} {l : Ref v (base Bool)} {X : Act v ⊤} {act : Act v ⊤} {kk : Act v ⊤} {w} {σ : w ⊑ʷ v} {K : Stack w ⊤}
          → act ≗ readB l (λ b → when b X) → At.val (State.heap st) l ≡ false
          → ⟨ st , run act same (push (rest kk) σ K) ⟩ ⇒ ⟨ st , run (wkAct same kk) σ K ⟩
  hushed⇒ {st = st} {l} {X} {kk = kk} {σ = σ} {K} (readRef≗ g) e = step⇒ refl (go (g same _) e)
    where
      go : ∀ {x m} → m ≗ wkAct same (when x X) → x ≡ false
         → ⟨ st , run m same (push (rest kk) σ K) ⟩ ⇒ ⟨ st , run (wkAct same kk) σ K ⟩
      go done≗ refl = step⇒ refl (step⇒ refl here⇒)

  -- A live joiner's callback, its flag read: a delivery at the joiner.
  joined⇒ : ∀ {v Δj A} {L : Owed} {kj : Ctx v Δj A} {tj nj nj′ fs c} {st : State v} {p a} {l : Ref v (base Bool)} {act : Act v ⊤}
              {K : Stack v ⊤}
          → act ≗ readB l (λ b → when b (Observer.next (obsC kj) a)) → At.val (State.heap st) l ≡ true
          → Mid L kj tj (just nj) fs c st → U.step nj ≡ U.outˢ p a nj′ → State.pos st ≡ p → AtC.Fore (State.heap st) kj p
          → (∀ {v′} (τ′ : v ⊑ʷ v′) {st′ : State v′} {c′} → Back L τ′ kj tj p (just nj′) fs c′ st′
             → Seg nothing (trace ⟨ st′ , ret tt (same ⨾ τ′) K ⟩) (U.unfold c′))
          → Seg nothing (trace ⟨ st , run act same K ⟩) (U.unfold c)
  joined⇒ {kj = kj} {a = a} (readRef≗ g) e M e′ p F κ = tauˡ (calm~ (delivering M e′ p F (on e (g same _)) κ) tt)
    where
      on : ∀ {x m} → x ≡ true → m ≗ wkAct same (when x (Observer.next (obsC kj) a)) → m ≗ Observer.next (obsC kj) a
      on refl d = ≗-unweaken d

  -- The feed, subscriber by subscriber, each live joiner's delivery a calm
  -- point: finitely many silent steps between them, by the list's length.
  feed : ∀ {h v Δ A B L} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B} {t q a n′ fs} {τ : h ⊑ʷ v}
           (n : ℕ) (ss : Subs v A) → length ss ≡ n → ∀ {c′} {st′ : State v} {act w} {σ : w ⊑ʷ h} {σ′ : w ⊑ʷ v} {K : Stack w ⊤}
       → Feeding L S c u s₀ mm body k t q a n′ fs τ ss c′ st′ → act ≗ each ss (feedOne q a) → σ′ ≡ σ ⨾ τ
       → (∀ {v′} (τ′ : h ⊑ʷ v′) {st″ : State v′} {c″} → Back L τ′ (sourceF S c u s₀ mm body ◂ k) t q (just n′) fs c″ st″
          → Seg nothing (trace ⟨ st″ , ret tt (σ ⨾ τ′) K ⟩) (U.unfold c″))
       → Seg nothing (trace ⟨ st′ , run act σ′ K ⟩) (U.unfold c′)
  feed zero    []              _   Fd done≗              refl κ = tauˡ (κ _ (feed-end Fd))
  feed zero    (_ ∷ _)         ()
  feed (suc n) []              ()
  feed (suc n) ((sk , j) ∷ ss) len Fd (goto≗ (send≗ r)) refl κ with feed-head Fd
  ... | hushed e cb Fd′ =
    tauˡ (tauˡ (taus (hushed⇒ cb e) (feed n ss (suc-injective len) Fd′ (subst (λ x → _ ≗ each x _) (wkSubs-same ss) (wk-each ss same r)) refl κ)))
  feed {τ = τ} (suc n) ((sk , j) ∷ ss) len {σ = σ} {K = K} Fd (goto≗ (send≗ {k = kk} r)) refl κ | joins e cb M e′ F onward =
    tauˡ (tauˡ (joined⇒ cb e M e′ refl F κ′))
    where
      κ′ : ∀ {v′} (τ′ : _ ⊑ʷ v′) {st″ : State v′} {c″} → Back _ τ′ _ _ _ _ _ c″ st″
         → Seg nothing (trace ⟨ st″ , ret tt (same ⨾ τ′) (push (rest kk) (σ ⨾ τ) K) ⟩) (U.unfold c″)
      κ′ τ′ B rewrite same-⨾ τ′ = tauˡ (feed n (wkSubs τ′ ss) (trans (wkSubs-length τ′ ss) (suc-injective len)) (onward τ′ B) (wk-each ss τ′ r) (⨾-assoc σ τ τ′) κ)

  -- The subscribers read, then fed.
  reading : ∀ {h Δ A B L} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B} {t a n′ fs c′} {st : State h}
              {act w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
          → act ≗ readRef (Subject.subscribers S) (λ _ ss → each ss (feedOne (State.pos st) a))
          → Feeding L S c u s₀ mm body k t (State.pos st) a n′ fs same (At.val (State.heap st) (Subject.subscribers S)) c′ st
          → (∀ {v′} (τ′ : h ⊑ʷ v′) {st″ : State v′} {c″} → Back L τ′ (sourceF S c u s₀ mm body ◂ k) t (State.pos st) (just n′) fs c″ st″
             → Seg nothing (trace ⟨ st″ , ret tt (σ ⨾ τ′) K ⟩) (U.unfold c″))
          → Seg nothing (trace ⟨ st , run act σ K ⟩) (U.unfold c′)
  reading (readRef≗ g) Fd κ = tauˡ (feed _ _ refl Fd (g same _) refl κ)

  -- A CONNECT'S SOURCE FED to the subject's subscribers in the order they
  -- joined.  The connect's skip under the source's event is the guard; each
  -- joiner's delivery, at a context deeper than this frame's, a calm point.
  next-source : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B}
              → NextAt (sourceF S c u s₀ mm body ◂ k)
  next-source M e refl F (here≗ g) κ = passing (feed-start M e F) λ Fd → reading (g _) Fd κ

  frame : ∀ {h Δ A Δ′ B} (f : Fr h Δ A Δ′ B) {k : Ctx h Δ′ B} → Above k → Delivers (f ◂ k)
  frame (mapF f)                            ih = next-map ih , done-map ih
  frame (scanF f r)                         ih = next-scan ih , done-scan ih
  frame (takeF i p c u)                     ih = next-take ih , done-take ih
  frame (outerF op f fl oc u r ls)          ih = next-outer ih , done-outer ih
  frame (laneF op f fl oc u r so bs c d as) ih = next-inner ih , done-inner ih
  frame (sourceF S c u s₀ mm body)          ih = next-source , done-source ih
  frame (bodyF S c u s₀ mm src)             ih = next-body ih , done-body ih
  frame (deferF u)                          ih = next-defer ih , done-defer ih

  delivers : ∀ {h Δ A} (k : Ctx h Δ A) → Delivers k
  delivers k = go (depth k) k refl
    where
      go : ∀ n {h Δ A} (k : Ctx h Δ A) → depth k ≡ n → Delivers k
      go zero    top     _    = next-top , done-top
      go (suc n) top     ()
      go zero    (f ◂ k) ()
      go (suc n) (f ◂ k) refl = frame f (go n k refl , λ g → go n _ (sym (grown-depth g)))
