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

open import Data.Bool using (Bool)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Pos; Timeline)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Run)
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Pureᴾ; Sink; _⨾_; module Pure) renaming (_⊑_ to _⊑ʷ_)
open import adequacy.Realize using (module Realizing)
open import adequacy.Segment using (module Seg)
open import adequacy.deliver.Context using (module Contexts)
open import adequacy.deliver.Mid using (module Middles)

module Climbing (R : Set) where
  open Machine R using (⟨_,_⟩; run; ret; Stack; trace)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Realizing R
  open Contexts R
  open Middles R
  open Pure R using (State)
  open Seg R

  ------------------------------------------------------------------------
  -- A delivery at a context

  NextAt : ∀ {h Δ A} → Ctx h Δ A → Set₁
  NextAt {h} k = ∀ {L : Pos → Set} {t n fs c} {st : State h} {q a n′}
               → Mid L k t (just n) fs c st → U.step n ≡ U.outˢ q a n′ → State.pos st ≡ q → AtC.Fore (State.heap st) k q
               → ∀ {act} → act ≗ Observer.next (obsC k) a
               → ∀ {w} {σ : w ⊑ʷ h} {K : Stack w ⊤}
               → (∀ {v} (τ : h ⊑ʷ v) {st′ : State v} {c′} → Back L τ k t q (just n′) fs c′ st′
                  → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ) K ⟩) (U.unfold c′))
               → ∀ {bd} → Seg bd (trace ⟨ st , run act σ K ⟩) (U.unfold c)

  DoneAt : ∀ {h Δ A} → Ctx h Δ A → Set₁
  DoneAt {h} k = ∀ {L : Pos → Set} {t n fs c} {st : State h} {q}
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
    -- DEAD ROUTE: by `Above` alone.  The inline burst delivers at a hole
    --   inside the new lane, a context deeper than this frame's, which no
    --   delivery at `k` or a growth of it reaches.  The meaning's own step
    --   here is a skip, so the run may take it as a guard and deliver
    --   anywhere after it: corecursion, which a postulate's argument cannot
    --   carry past Agda's guardedness check.
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

    -- A connect's source fed to the subject's subscribers in the order
    -- they joined, each a delivery at a joiner in the body.
    --
    -- DEAD ROUTE: by `Above` alone.  A joiner sits inside the body, a
    --   context deeper than this frame's; as at `next-outer`, with the
    --   connect's skip under the source's event as the guard.
    next-source : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B}
                → Above k → NextAt (sourceF S c u s₀ mm body ◂ k)
    -- The subject closed, each joiner finished.
    --
    -- DEAD ROUTE: by `Above` alone, as at `next-source`.
    done-source : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {body : Sub h (A ∷ Δ) B} {k : Ctx h Δ B}
                → Above k → DoneAt (sourceF S c u s₀ mm body ◂ k)

    -- A connect's body: its value its parent's; its end its parent's,
    -- then the source cut.
    next-body : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {src : Sub h Δ A} {k : Ctx h Δ B}
              → Above k → NextAt (bodyF S c u s₀ mm src ◂ k)
    done-body : ∀ {h Δ A B} {S : Subject A h} {c u s₀ mm} {src : Sub h Δ A} {k : Ctx h Δ B}
              → Above k → DoneAt (bodyF S c u s₀ mm src ◂ k)

  frame : ∀ {h Δ A Δ′ B} (f : Fr h Δ A Δ′ B) {k : Ctx h Δ′ B} → Above k → Delivers (f ◂ k)
  frame (mapF f)                            ih = next-map ih , done-map ih
  frame (scanF f r)                         ih = next-scan ih , done-scan ih
  frame (takeF i p c u)                     ih = next-take ih , done-take ih
  frame (outerF op f fl oc u r ls)          ih = next-outer ih , done-outer ih
  frame (laneF op f fl oc u r so bs c d as) ih = next-inner ih , done-inner ih
  frame (sourceF S c u s₀ mm body)          ih = next-source ih , done-source ih
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
