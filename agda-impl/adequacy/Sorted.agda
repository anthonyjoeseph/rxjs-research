{-# OPTIONS --guardedness --large-indices #-}

-- SORTEDNESS: the machine shows the root its values at positions that
-- never fall.  A fact about the machine alone; no meaning is consulted.
--
-- The position is SCOPED (`operation.AbstractObservable`'s `under`): it
-- is always the path of labels the run is under, put back when a scope
-- returns.  So the order of the run's positions is the pre-order of a
-- tree, and sortedness splits three ways.  THE WALK, once: a run that
-- enters each scope's children in increasing label order, and delivers
-- nothing at a position after entering one of its children, is sorted.
-- THE PROTOCOL, one kernel at a time: each kernel is well-positioned
-- (`Well`), given that the observer it delivers to is.  THE TIMERS: a
-- turn opens a fresh cascade past every position the run has shown.
--
-- `Well` is UNARY: it relates a computation to positions, never to a
-- meaning, so a kernel's case reads only the kernel.
module adequacy.Sorted where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Nat using (suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; _++_; [_]; map; null)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; maybe; just; nothing) renaming (map to mapMaybe)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapAll)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Level using (Lift; lift)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

import Tree as T
open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; From; done; quiet; at; emit; stall; close; From∞; ix; last; root; _<ᵖ_; <ᵖ-trans; <ᵖ-below; <ᵖ-part; <ᵖ-sub; <ᵖ-ix; Timeline) renaming (sub to subᴾ)
open import operation.AbstractObservable using (Ty; _⊗_; joins; fifo; gate; module Run; module Heap)
  renaming (base to baseᵗ; ref to refᵗ; sink to sinkᵗ; quiet to quietᵗ; list to listᵗ; maybe to maybeᵗ) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; note; fin; module Pure)
open Heap using (World; _⊑_; _⨾_; _∋_; here; there; new; wk∋; cell; slot; hush; play; same; Sink; Quiet; Handle)
open import operation.Machine using (module Machine)


------------------------------------------------------------------------
-- The order, reflexive

_≤ᵖ_ : Pos → Pos → Set
p ≤ᵖ q = p ≡ q ⊎ p <ᵖ q ≡ true

-- `q` is `p`, or under it.
Under : Pos → Pos → Set
Under p q = Σ Pos λ y → q ≡ p ++ y

-- Where a scope at `p` may leave the last delivery, starting from `lo`:
-- no earlier, and nowhere outside `p`'s subtree but `lo` itself.
Settled : Pos → Pos → Pos → Set
Settled p lo lo′ = lo ≤ᵖ lo′ × (lo ≡ lo′ ⊎ Under p lo′)

≤ᵖ-trans : ∀ {p q r} → p ≤ᵖ q → q ≤ᵖ r → p ≤ᵖ r
≤ᵖ-trans (inj₁ refl) h           = h
≤ᵖ-trans h           (inj₁ refl) = h
≤ᵖ-trans {p} {q} {r} (inj₂ a) (inj₂ b) = inj₂ (<ᵖ-trans p q r a b)

settled-refl : ∀ {p lo} → Settled p lo lo
settled-refl = inj₁ refl , inj₁ refl

settled-trans : ∀ {p lo lo′ lo″} → Settled p lo lo′ → Settled p lo′ lo″ → Settled p lo lo″
settled-trans (a , x) (b , inj₁ refl) = ≤ᵖ-trans a b , x
settled-trans (a , x) (b , inj₂ u)    = ≤ᵖ-trans a b , inj₂ u

-- Settled in a child scope is settled in its parent.
settled-out : ∀ {p l lo lo′} → Settled (p ++ [ l ]) lo lo′ → Settled p lo lo′
settled-out         (a , inj₁ e)            = a , inj₁ e
settled-out {p} {l} (a , inj₂ (y , refl)) = a , inj₂ (l ∷ y , ++-assoc p [ l ] y)

-- Settled from a delivery at the scope itself is settled from before it.
settled-note : ∀ {p lo lo′} → lo ≤ᵖ p → Settled p p lo′ → Settled p lo lo′
settled-note {p} le (a , inj₁ refl) = le , inj₂ ([] , sym (++-identityʳ p))
settled-note     le (a , inj₂ u)    = ≤ᵖ-trans le a , inj₂ u

-- Wherever a child left the last, it is before a later sibling.
settled-next : ∀ q {a b lo lo′} → (a ∷ []) <ᵖ (b ∷ []) ≡ true → lo ≤ᵖ (q ++ [ b ]) → Settled (q ++ [ a ]) lo lo′ → lo′ ≤ᵖ (q ++ [ b ])
settled-next q     h le (_ , inj₁ refl)       = le
settled-next q {a} h le (_ , inj₂ (y , refl)) rewrite ++-assoc q [ a ] y = inj₂ (<ᵖ-part q y [] h)

-- Before a scope, before each of its children.
≤ᵖ-child : ∀ q {l lo} → lo ≤ᵖ q → lo ≤ᵖ (q ++ [ l ])
≤ᵖ-child q le = ≤ᵖ-trans le (inj₂ (<ᵖ-below q []))

module Sorting (R : Set) where
  open Machine R using (Mach; mach; Playing; wkPlaying; Todo; resume; owing; starting; feed; Step; silent; value; complete; drained; step; trace; shown; begin; launch; reading; Read) renaming (play to playᴹ)
  open Shared Timeline (Out R) using (Conf; ⟨_,_,_⟩; go; Ctl; run; ret; held; asking; Stack; bottom; push; Wait; rest; back; rehold; told
                                     ; Heapᴹ; Callbacks; cbs; look; spent?; Val; Stored; get; put; store; extend; wkAll; wkVal; stored)
  open Run (Pureᴾ R) using (Act; Ref; El; wkEl; done; newRef; readRef; writeRef; register; send; finish; startCold; stop; stash; cancel; eff; here; under; diverge; unfold
                           ; Observer; Subscription; Subscribe; Kont; Env; Subject; wkEnv; wkR; compile; wkAct; wkObs; _>>=ᴬ_; _>>ᴬ_; module Kit; emptyᴷ; ofᴷ; mapᴷ; scanᴷ; takeWhileᴷ; flatMapᴷ; connectᴷ; joinᴷ; via; emitAll; wkSub; module FlatKit)
  open Pure R using (Timer; wkTimer; insert; cascade; recorder; mapList)
  open Kit using (Cut; wkCut; cut; guard; guarded; attach; when; skipᴬ; each; unsubscribeVia; readB; readF; modify; newCut)
  open FlatKit using (Flat; wkFlat; newFlat; module FlatMap)
  open Read

  ----------------------------------------------------------------------
  -- What is claimed: the root's values at positions that never fall

  mutual
    record Rising (lo : Pos) (m : Mach) : Set₁ where
      coinductive
      field rises : RisingStep lo (step m)

    data RisingStep (lo : Pos) : Step → Set₁ where
      silentʳ   : ∀ {m lo′} → lo ≤ᵖ lo′ → Rising lo′ m → RisingStep lo (silent m)
      valueʳ    : ∀ {t p a m} → lo ≤ᵖ p → Rising p m → RisingStep lo (value t p a m)
      completeʳ : ∀ {p} → lo ≤ᵖ p → RisingStep lo (complete p)
      drainedʳ  : RisingStep lo drained

  data Ascending (lo : Pos) : List Pos → Set where
    []ᵃ  : Ascending lo []
    _∷ᵃ_ : ∀ {p ps} → lo ≤ᵖ p → Ascending p ps → Ascending lo (p ∷ ps)

  ascending-from : ∀ {lo lo′ ps} → lo ≤ᵖ lo′ → Ascending lo′ ps → Ascending lo ps
  ascending-from le []ᵃ        = []ᵃ
  ascending-from le (h ∷ᵃ a)   = ≤ᵖ-trans le h ∷ᵃ a

  -- A rising run's record is ascending, however far it is read.
  mutual
    ascending : ∀ {lo m} → Rising lo m → ∀ n c → Ascending lo (marks (reading n c (trace m)))
    ascending r 0       c = []ᵃ
    ascending r (suc n) c = ascendingˢ (Rising.rises r) n c

    ascendingˢ : ∀ {lo s} → RisingStep lo s → ∀ n c → Ascending lo (marks (reading (suc n) c (shown s)))
    ascendingˢ (silentʳ le r)  n c = ascending-from le (ascending r n _)
    ascendingˢ (valueʳ le r)   n c = le ∷ᵃ ascending r n _
    ascendingˢ (completeʳ le)  n c = le ∷ᵃ []ᵃ
    ascendingˢ drainedʳ        n c = []ᵃ

  ----------------------------------------------------------------------
  -- THE PROTOCOL: a computation well-positioned

  -- What a cell may hold, the last delivery at `lo`: a subject's joiners
  -- listed in the order of the positions they joined at, every one of
  -- them before `lo`.  So a later join, at no position before `lo`, comes
  -- after every one listed.
  joined : ∀ {w A} → El w (joins A) → List Pos
  joined = map proj₂

  Fits : ∀ {w} → Pos → (t : Ty) → El w t → Set
  Fits lo (joins A) ss = AllPairs (λ i j → i <ᵖ j ≡ true) (joined ss) × All (λ i → i <ᵖ lo ≡ true) (joined ss)
  Fits lo (baseᵗ X)  _  = ⊤
  Fits lo (refᵗ t)   _  = ⊤
  Fits lo (sinkᵗ A)  _  = ⊤
  Fits lo quietᵗ     _  = ⊤
  Fits lo (listᵗ t)  _  = ⊤
  Fits lo (maybeᵗ t) _  = ⊤
  Fits lo (s ⊗ t)   _  = ⊤
  Fits lo (fifo X)   _  = ⊤
  Fits lo gate       _  = ⊤

  joined-wk : ∀ {w v A} (ρ : w ⊑ v) (ss : El w (joins A)) → joined (wkEl (joins A) ρ ss) ≡ joined ss
  joined-wk ρ []             = refl
  joined-wk ρ ((s , j) ∷ ss) = cong (j ∷_) (joined-wk ρ ss)

  fits-wk : ∀ {w v} lo t (ρ : w ⊑ v) (a : El w t) → Fits lo t a → Fits lo t (wkEl t ρ a)
  fits-wk lo (joins A) ρ ss f rewrite joined-wk ρ ss = f
  fits-wk lo (baseᵗ X)  ρ a  f = tt
  fits-wk lo (refᵗ t)   ρ a  f = tt
  fits-wk lo (sinkᵗ A)  ρ a  f = tt
  fits-wk lo quietᵗ     ρ a  f = tt
  fits-wk lo (listᵗ t)  ρ a  f = tt
  fits-wk lo (maybeᵗ t) ρ a  f = tt
  fits-wk lo (s ⊗ t)   ρ a  f = tt
  fits-wk lo (fifo X)   ρ a  f = tt
  fits-wk lo gate       ρ a  f = tt

  -- Still: delivers nothing and moves nothing — cells read, written so
  -- they fit wherever the last is, cancelled and stopped.  Asking whether
  -- an observer is closed is so, and so is an unsubscribe: which is why a
  -- source may ask before it opens a scope, and a lane start after a cut.
  data Still {w B} : Act w B → Set₁ where
    doneˢ     : ∀ {b} → Still (done b)
    newRefˢ   : ∀ {t a} {k : ∀ {v} → w ⊑ v → Ref v t → Act v B} → (∀ lo → Fits lo t a) → (∀ {v} (σ : w ⊑ v) r → Still (k σ r)) → Still (newRef t a k)
    readRefˢ  : ∀ {t} {r : Ref w t} {k : ∀ {v} → w ⊑ v → El v t → Act v B} → (∀ {v} (σ : w ⊑ v) a → Still (k σ a)) → Still (readRef {t = t} r k)
    writeRefˢ : ∀ {t} {r : Ref w t} {a : El w t} {k : Act w B} → (∀ lo → Fits lo t a) → Still k → Still (writeRef {t = t} r a k)
    cancelˢ   : ∀ {t : Quiet w} {k : Act w B} → Still k → Still (cancel t k)
    stopˢ     : ∀ {h : Handle w} {k : Act w B} → Still k → Still (stop h k)

  wk-still : ∀ {w v B} {m : Act w B} (ρ : w ⊑ v) → Still m → Still (wkAct ρ m)
  wk-still ρ doneˢ                     = doneˢ
  wk-still ρ (newRefˢ {t} {a} f h)     = newRefˢ (λ lo → fits-wk lo t ρ a (f lo)) λ σ r → h (ρ ⨾ σ) r
  wk-still ρ (readRefˢ h)              = readRefˢ λ σ a → h (ρ ⨾ σ) a
  wk-still ρ (writeRefˢ {t} {a = a} f k) = writeRefˢ (λ lo → fits-wk lo t ρ a (f lo)) (wk-still ρ k)
  wk-still ρ (cancelˢ k)               = cancelˢ (wk-still ρ k)
  wk-still ρ (stopˢ k)                 = stopˢ (wk-still ρ k)

  still-then : ∀ {w A B} {m : Act w A} {f : A → Act w B} → Still m → (∀ x → Still (f x)) → Still (m >>=ᴬ f)
  still-then doneˢ          hf = hf _
  still-then (newRefˢ f h)  hf = newRefˢ f λ σ r → still-then (h σ r) λ x → wk-still σ (hf x)
  still-then (readRefˢ h)   hf = readRefˢ λ σ a → still-then (h σ a) λ x → wk-still σ (hf x)
  still-then (writeRefˢ f k) hf = writeRefˢ f (still-then k hf)
  still-then (cancelˢ k)    hf = cancelˢ (still-then k hf)
  still-then (stopˢ k)      hf = stopˢ (still-then k hf)

  -- `Well p lo m`: run at position `p`, the last delivery at `lo`, `m`
  -- delivers at no position before the last, and every scope it opens
  -- leaves the last delivery `Settled` in it.  A delivery is the root's
  -- record, or an observer's callback run; an observer's callbacks are
  -- well wherever they are called no earlier than the last delivery.  An
  -- unsubscribe delivers nothing, so it is well wherever it runs: it is
  -- stashed only so, and cancelled anywhere.  A cell is read as it
  -- `Fits`, and written so; a write may move the last on, as a join's
  -- does past the position it joined at.
  mutual
    data Well {w B} (p lo : Pos) : Act w B → Set₁ where
      doneʷ     : ∀ {b} → Well p lo (done b)
      newRefʷ   : ∀ {t a} {k : ∀ {v} → w ⊑ v → Ref v t → Act v B} → Fits lo t a → (∀ {v} (σ : w ⊑ v) r → Well p lo (k σ r)) → Well p lo (newRef t a k)
      readRefʷ  : ∀ {t} {r : Ref w t} {k : ∀ {v} → w ⊑ v → El v t → Act v B} → (∀ {v} (σ : w ⊑ v) a → Fits lo t a → Well p lo (k σ a)) → Well p lo (readRef {t = t} r k)
      writeRefʷ : ∀ {t} {r : Ref w t} {a : El w t} {k : Act w B} lo′ → Settled p lo lo′ → Fits lo′ t a → Well p lo′ k → Well p lo (writeRef {t = t} r a k)
      registerʷ : ∀ {A} {n : A → Act w ⊤} {c : Act w ⊤} {x : Act w Bool} {k : ∀ {v} → w ⊑ v → Sink v A → Act v B} → WellObs (record { next = n ; complete = c ; closed = x })
                → (∀ {v} (σ : w ⊑ v) s → Well p lo (k σ s)) → Well p lo (register n c x k)
      sendʷ     : ∀ {A} {s : Sink w A} {a : A} {k : Act w B} → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → Well p lo′ k) → Well p lo (send s a k)
      finishʷ   : ∀ {A} {s : Sink w A} {k : Act w B} → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → Well p lo′ k) → Well p lo (finish {A = A} s k)
      startColdʷ : ∀ {A} {c : Timeline A} {s : Sink w A} {k : ∀ {v} → w ⊑ v → Handle v → Act v B} → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → ∀ {v} (σ : w ⊑ v) h → Well p lo′ (k σ h))
                 → Well p lo (startCold {A = A} c s k)
      stopʷ     : ∀ {h : Handle w} {k : Act w B} → Well p lo k → Well p lo (stop h k)
      stashʷ    : ∀ {m : Act w ⊤} {k : ∀ {v} → w ⊑ v → Quiet v → Act v B} → Still m → (∀ {v} (σ : w ⊑ v) t → Well p lo (k σ t)) → Well p lo (stash m k)
      cancelʷ   : ∀ {t : Quiet w} {k : Act w B} → Well p lo k → Well p lo (cancel t k)
      noteʷ     : ∀ {a} {k : ⊤ → Act w B} → lo ≤ᵖ p → Well p p (k _) → Well p lo (eff (note a) k)
      finʷ      : ∀ {k : ⊤ → Act w B} → lo ≤ᵖ p → Well p lo (eff fin k)
      hereʷ     : ∀ {k : Pos → Act w B} → Well p lo (k p) → Well p lo (here k)
      underʷ    : ∀ {l} {m : Act w ⊤} {k : Act w B} → Well (p ++ [ l ]) lo m → (∀ lo′ → Settled (p ++ [ l ]) lo lo′ → Well p lo′ k) → Well p lo (under l m k)
      divergeʷ  : Well p lo diverge
      unfoldʷ   : ∀ {Γ A} {l : T.Later Timeline Γ A} {e : Env Γ w} {n : A → Act w ⊤} {c : Act w ⊤} {x : Act w Bool}
                    {k : ∀ {v} → w ⊑ v → Quiet v → Act v ⊤} {m : Act w B} → WellEnv {Γ} e → WellObs {A} (record { next = n ; complete = c ; closed = x })
                → (∀ {v} (σ : w ⊑ v) t → Placeless (k σ t)) → lo ≤ᵖ p → (∀ lo′ → Settled p lo lo′ → Well p lo′ m) → Well p lo (unfold l e n c x k m)

    -- An observer: each callback well wherever it is called no earlier
    -- than the last delivery.  Asking whether it is closed is `Still`.
    WellObs : ∀ {A w} → Observer A w → Set₁
    WellObs o = (∀ a q lo → lo ≤ᵖ q → Well q lo (Observer.next o a))
              × (∀ q lo → lo ≤ᵖ q → Well q lo (Observer.complete o))
              × Still (Observer.closed o)

    -- Well wherever it runs, from wherever the last delivery was.
    Placeless : ∀ {w} → Act w ⊤ → Set₁
    Placeless m = ∀ p lo → Well p lo m

    -- The connects in scope: each subject's joins well.
    WellEnv : ∀ {Γ w} → Env Γ w → Set₁
    WellEnv e = Lift _ ⊤

  -- A continuation places nothing: well wherever it runs, handed a
  -- subscription whose unsubscribe is `Still`.
  WellKont : ∀ {w} → Kont w → Set₁
  WellKont {w} k = ∀ {v} (σ : w ⊑ v) (sub : Subscription v) → Still (Subscription.unsubscribe sub) → Placeless (k σ sub)

  -- A subscription: subscribed fresh, with a well observer and a
  -- continuation that places nothing, it is well.  So the subscription it
  -- hands that continuation must be `Still` to unsubscribe.
  WellSub : ∀ {A w} → Subscribe A w → Set₁
  WellSub {A} {w} s = ∀ {v} (ρ : w ⊑ v) (o : Observer A v) (k : Kont v) p lo → lo ≤ᵖ p → WellObs o → WellKont k → Well p lo (s ρ o k)

  -- Weakening moves no delivery.
  wk-well : ∀ {w v B p lo} {m : Act w B} (ρ : w ⊑ v) → Well p lo m → Well p lo (wkAct ρ m)
  wk-well ρ doneʷ                  = doneʷ
  wk-well ρ (newRefʷ {t} {a} f h)  = newRefʷ (fits-wk _ t ρ a f) λ σ r → h (ρ ⨾ σ) r
  wk-well ρ (readRefʷ h)           = readRefʷ λ σ a f → h (ρ ⨾ σ) a f
  wk-well ρ (writeRefʷ {t} {a = a} lo′ st f w) = writeRefʷ lo′ st (fits-wk lo′ t ρ a f) (wk-well ρ w)
  wk-well ρ (registerʷ (wn , wc , wx) h) =
    registerʷ ((λ a q lo le → wk-well ρ (wn a q lo le)) , (λ q lo le → wk-well ρ (wc q lo le)) , wk-still ρ wx) λ σ s → h (ρ ⨾ σ) s
  wk-well ρ (sendʷ le h)           = sendʷ le λ lo′ st → wk-well ρ (h lo′ st)
  wk-well ρ (finishʷ le h)         = finishʷ le λ lo′ st → wk-well ρ (h lo′ st)
  wk-well ρ (startColdʷ le h)      = startColdʷ le λ lo′ st σ hd → h lo′ st (ρ ⨾ σ) hd
  wk-well ρ (stopʷ w)              = stopʷ (wk-well ρ w)
  wk-well ρ (stashʷ sm h)          = stashʷ (wk-still ρ sm) λ σ t → h (ρ ⨾ σ) t
  wk-well ρ (cancelʷ w)            = cancelʷ (wk-well ρ w)
  wk-well ρ (noteʷ le w)           = noteʷ le (wk-well ρ w)
  wk-well ρ (finʷ le)              = finʷ le
  wk-well ρ (hereʷ w)              = hereʷ (wk-well ρ w)
  wk-well ρ (underʷ w h)           = underʷ (wk-well ρ w) λ lo′ st → wk-well ρ (h lo′ st)
  wk-well ρ divergeʷ               = divergeʷ
  wk-well ρ (unfoldʷ we (wn , wc , wx) kp le h) =
    unfoldʷ (lift tt) ((λ a q lo le → wk-well ρ (wn a q lo le)) , (λ q lo le → wk-well ρ (wc q lo le)) , wk-still ρ wx) (λ σ t → kp (ρ ⨾ σ) t) le λ lo′ st → wk-well ρ (h lo′ st)

  wk-obs : ∀ {A w v} {o : Observer A w} (ρ : w ⊑ v) → WellObs o → WellObs (wkObs ρ o)
  wk-obs ρ (wn , wc , wx) = (λ a q lo le → wk-well ρ (wn a q lo le)) , (λ q lo le → wk-well ρ (wc q lo le)) , wk-still ρ wx

  -- Sequencing: the rest well from wherever the first left the last.
  bind-well : ∀ {w A B p lo} {m : Act w A} {f : A → Act w B} → Well p lo m → (∀ lo′ → Settled p lo lo′ → ∀ x → Well p lo′ (f x)) → Well p lo (m >>=ᴬ f)
  bind-well doneʷ             hf = hf _ settled-refl _
  bind-well (newRefʷ f h)     hf = newRefʷ f λ σ r → bind-well (h σ r) λ lo′ st x → wk-well σ (hf lo′ st x)
  bind-well (readRefʷ h)      hf = readRefʷ λ σ a f → bind-well (h σ a f) λ lo′ st x → wk-well σ (hf lo′ st x)
  bind-well (writeRefʷ lo′ st f w) hf = writeRefʷ lo′ st f (bind-well w λ lo″ st′ → hf lo″ (settled-trans st st′))
  bind-well (registerʷ wo h)  hf = registerʷ wo λ σ s → bind-well (h σ s) λ lo′ st x → wk-well σ (hf lo′ st x)
  bind-well (sendʷ le h)      hf = sendʷ le λ lo′ st → bind-well (h lo′ st) λ lo″ st′ → hf lo″ (settled-trans st st′)
  bind-well (finishʷ le h)    hf = finishʷ le λ lo′ st → bind-well (h lo′ st) λ lo″ st′ → hf lo″ (settled-trans st st′)
  bind-well (startColdʷ le h) hf = startColdʷ le λ lo′ st σ hd → bind-well (h lo′ st σ hd) λ lo″ st′ x → wk-well σ (hf lo″ (settled-trans st st′) x)
  bind-well (stopʷ w)         hf = stopʷ (bind-well w hf)
  bind-well (stashʷ sm h)     hf = stashʷ sm λ σ t → bind-well (h σ t) λ lo′ st x → wk-well σ (hf lo′ st x)
  bind-well (cancelʷ w)       hf = cancelʷ (bind-well w hf)
  bind-well (noteʷ le w)      hf = noteʷ le (bind-well w λ lo′ st → hf lo′ (settled-note le st))
  bind-well (finʷ le)         hf = finʷ le
  bind-well (hereʷ w)         hf = hereʷ (bind-well w hf)
  bind-well (underʷ w h)      hf = underʷ w λ lo′ st → bind-well (h lo′ st) λ lo″ st′ → hf lo″ (settled-trans (settled-out st) st′)
  bind-well divergeʷ          hf = divergeʷ
  bind-well (unfoldʷ we wo kp le h) hf = unfoldʷ we wo kp le λ lo′ st → bind-well (h lo′ st) λ lo″ st′ → hf lo″ (settled-trans st st′)

  -- What is still is well wherever it runs, and the rest from there.
  still-bind : ∀ {w A B p lo} {m : Act w A} {f : A → Act w B} → Still m → (∀ x → Well p lo (f x)) → Well p lo (m >>=ᴬ f)
  still-bind doneˢ           hf = hf _
  still-bind (newRefˢ f h)   hf = newRefʷ (f _) λ σ r → still-bind (h σ r) λ x → wk-well σ (hf x)
  still-bind (readRefˢ h)    hf = readRefʷ λ σ a _ → still-bind (h σ a) λ x → wk-well σ (hf x)
  still-bind (writeRefˢ f k) hf = writeRefʷ _ settled-refl (f _) (still-bind k hf)
  still-bind (cancelˢ k)     hf = cancelʷ (still-bind k hf)
  still-bind (stopˢ k)       hf = stopʷ (still-bind k hf)

  still-well : ∀ {w B p lo} {m : Act w B} → Still m → Well p lo m
  still-well doneˢ           = doneʷ
  still-well (newRefˢ f h)   = newRefʷ (f _) λ σ r → still-well (h σ r)
  still-well (readRefˢ h)    = readRefʷ λ σ a _ → still-well (h σ a)
  still-well (writeRefˢ f k) = writeRefʷ _ settled-refl (f _) (still-well k)
  still-well (cancelˢ k)     = cancelʷ (still-well k)
  still-well (stopˢ k)       = stopʷ (still-well k)

  -- A cut cancels a stashed unsubscribe, if any.
  cut-still : ∀ {w} (c : Cut w) → Still (cut c)
  cut-still c = writeRefˢ (λ _ → tt) (readRefˢ λ where
    σ nothing  → doneˢ
    σ (just t) → cancelˢ doneˢ)

  when-well : ∀ {w p lo} (r : Ref w (baseᵗ Bool)) {m : Act w ⊤} → Well p lo m → Well p lo (Kit.readB r λ b → when b m)
  when-well r w = readRefʷ λ where
    σ true  _ → wk-well σ w
    σ false _ → doneʷ

  whenG-well : ∀ {w p lo} (r : Ref w gate) {m : Act w ⊤} → Well p lo m → Well p lo (Kit.readG r λ b → when b m)
  whenG-well r w = readRefʷ λ where
    σ true  _ → wk-well σ w
    σ false _ → doneʷ

  guard-well : ∀ {w p lo} (c : Cut w) {m : Act w ⊤} → Well p lo m → Well p lo (guard c m)
  guard-well c = when-well (Kit.live c)

  guarded-well : ∀ {A w} (c : Cut w) {o : Observer A w} → WellObs o → WellObs (guarded c o)
  guarded-well c (wn , wc , wx) = (λ a q lo le → guard-well c (wn a q lo le)) , (λ q lo le → guard-well c (wc q lo le))
                                , readRefˢ λ where
                                    σ true  → wk-still σ wx
                                    σ false → doneˢ

  -- Attaching a still unsubscribe places nothing.
  attach-well : ∀ {w} (c : Cut w) sub → Still (Subscription.unsubscribe sub) → Placeless (attach c sub)
  attach-well c sub sm p lo = stashʷ sm λ σ t → writeRefʷ lo settled-refl tt (readRefʷ λ where
    τ true  _ → doneʷ
    τ false _ → still-well (wk-still τ (wk-still σ sm)))

  -- takeWhile's observer: a failing value under `ix 0` when inclusive,
  -- then the completion under `last`, then the cut.
  takeWhile-obs : ∀ {A w} i (f : A → Bool) (c : Cut w) {o : Observer A w} → WellObs o
                → WellObs {A} {w} (record { next = λ a → if f a then Observer.next o a
                                                       else (when i (under (ix 0) (Observer.next o a) skipᴬ) >>ᴬ under last (Observer.complete o) (cut c))
                                         ; complete = Observer.complete o ; closed = Observer.closed o })
  takeWhile-obs true f c {o} (wn , wc , wx) = next′ , wc , wx
    where
    next′ : ∀ a q lo → lo ≤ᵖ q → Well q lo (if f a then Observer.next o a else under (ix 0) (Observer.next o a) (under last (Observer.complete o) (cut c)))
    next′ a q lo le with f a
    ... | true  = wn a q lo le
    ... | false = underʷ (wn a (q ++ [ ix 0 ]) lo (≤ᵖ-child q le))
                    λ lo′ st → underʷ (wc (q ++ [ last ]) lo′ (settled-next q refl (≤ᵖ-child q le) st)) λ _ _ → still-well (cut-still c)
  takeWhile-obs false f c {o} (wn , wc , wx) = next′ , wc , wx
    where
    next′ : ∀ a q lo → lo ≤ᵖ q → Well q lo (if f a then Observer.next o a else under last (Observer.complete o) (cut c))
    next′ a q lo le with f a
    ... | true  = wn a q lo le
    ... | false = underʷ (wc (q ++ [ last ]) lo (≤ᵖ-child q le)) λ _ _ → still-well (cut-still c)

  -- The risk of the protocol: two callbacks in one scope.  A callback
  -- may leave the last delivery anywhere settled in its scope, so a
  -- second callback in that scope needs its own later label: an
  -- inclusive `takeWhile` delivers its failing value under `ix 0` and
  -- completes under `last`.  Its cut cancels a stashed unsubscribe,
  -- which is `Still`, wherever the completion left the last.
  -- REFUTED: 72324013 with the failing value delivered unscoped beside the completion
  takeWhileᴷ-well : ∀ {A w} i f {s : Subscribe A w} → WellSub {A} {w} s → WellSub (takeWhileᴷ i f s)
  takeWhileᴷ-well i f hs ρ o k q lo le wo wk =
    newRefʷ tt λ σ l → newRefʷ tt λ τ h →
      let c = (wkR τ l , h) in
      hs _ _ _ q lo le (guarded-well c (takeWhile-obs i f c (wk-obs (σ ⨾ τ) wo)))
         λ υ sub sm q′ lo′ → bind-well (attach-well (wkCut υ c) sub sm q′ lo′) λ lo″ _ _ → wk ((σ ⨾ τ) ⨾ υ) _ (cut-still (wkCut υ c)) q′ lo″

  -- A subject's delivery to each joiner it lists, under `sub` of where it
  -- joined: listed in the order they joined, each is past where the one
  -- before it left the last.
  each-sub-well : ∀ {w A} q lo (ss : El w (joins A)) (g : Sink w A → Act w ⊤)
                → (∀ x lo′ → lo′ ≤ᵖ (q ++ [ subᴾ (proj₂ x) ]) → Well (q ++ [ subᴾ (proj₂ x) ]) lo′ (g (proj₁ x)))
                → AllPairs (λ i j → i <ᵖ j ≡ true) (joined ss) → All (λ j → lo ≤ᵖ (q ++ [ subᴾ j ])) (joined ss)
                → Well q lo (each ss λ j → under (subᴾ (proj₂ j)) (g (proj₁ j)) skipᴬ)
  each-sub-well q lo []       g hg _        _        = doneʷ
  each-sub-well q lo (x ∷ xs) g hg (r AllPairs.∷ rs) (l ∷ ls) = underʷ (hg x lo l) λ lo′ st → each-sub-well q lo′ xs g hg rs (moved st r ls)
    where
    moved : ∀ {lo′ js} → Settled (q ++ [ subᴾ (proj₂ x) ]) lo lo′ → All (λ j → proj₂ x <ᵖ j ≡ true) js
          → All (λ j → lo ≤ᵖ (q ++ [ subᴾ j ])) js → All (λ j → lo′ ≤ᵖ (q ++ [ subᴾ j ])) js
    moved st []                []       = []
    moved st (_∷_ {j} h hs) (k ∷ ks) = settled-next q (<ᵖ-sub (proj₂ x) j h) k st ∷ moved st hs ks

  before-each : ∀ q {lo} → lo ≤ᵖ q → (js : List Pos) → All (λ j → lo ≤ᵖ (q ++ [ subᴾ j ])) js
  before-each q le []       = []
  before-each q le (j ∷ js) = ≤ᵖ-child q le ∷ before-each q le js

  via-still : ∀ {w} (mb : _) → Still {w} (unsubscribeVia mb)
  via-still nothing  = doneˢ
  via-still (just t) = cancelˢ doneˢ

  -- The body under `ix 0`, the source under `ix 1`: whatever the body
  -- left, the source is past it.  The subject delivers to its joiners as
  -- its cell lists them, in the order they joined; the body's completion
  -- cuts the source, which is `Still`.
  -- REFUTED: 72324013 with the cut a send to a registered sink, which `Well` guards as a delivery
  -- REFUTED: f4ba20a9 with a cell read well whatever it holds, so a subject's joiners listed out of order
  connectᴷ-well : ∀ {A B w} {s : Subscribe A w} {b : ∀ {v} → w ⊑ v → Subject A v → Subscribe B v} → WellSub {A} {w} s → (∀ {v} σ st → WellSub {B} {v} (b σ st)) → WellSub (connectᴷ s b)
  connectᴷ-well hs hb ρ o k q lo le (wn , wc , wx) wk =
    newRefʷ (AllPairs.[] , []) λ σ subs → newRefʷ tt λ τ cl → newRefʷ tt λ υ₁ l → newRefʷ tt λ υ₂ h → newRefʷ tt λ υ′ bodyRef →
      underʷ (hb _ _ _ _ _ (q ++ [ ix 0 ]) lo (≤ᵖ-child q le)
                 ((λ a q′ lo′ le′ → wk-well _ (wn a q′ lo′ le′))
                 , (λ q′ lo′ le′ → bind-well (wk-well _ (wc q′ lo′ le′)) λ lo″ _ _ → still-well (cut-still _))
                 , wk-still _ wx)
                 λ π sub sm p′ lo′ → stashʷ sm λ π′ t → writeRefʷ lo′ settled-refl tt doneʷ)
        λ lo′ st → underʷ (hs _ _ _ (q ++ [ ix 1 ]) lo′ (settled-next q refl (≤ᵖ-child q le) st)
                    ((λ a q′ lo″ le″ → readRefʷ λ _ ss (asc , _) →
                        each-sub-well q′ lo″ ss _ (λ x lo‴ le‴ → sendʷ le‴ λ _ _ → doneʷ) asc (before-each q′ le″ (joined ss)))
                    , (λ q′ lo″ le″ → writeRefʷ lo″ settled-refl tt (readRefʷ λ _ ss (asc , _) →
                        each-sub-well q′ lo″ ss _ (λ x lo‴ le‴ → finishʷ le‴ λ _ _ → doneʷ) asc (before-each q′ le″ (joined ss))))
                    , readRefˢ λ _ _ → doneˢ)
                    λ ψ src sm p′ lo″ → bind-well (attach-well _ src sm p′ lo″) λ lo‴ _ _ → readRefʷ λ ψ′ mb _ →
                      wk (σ ⨾ τ ⨾ (υ₁ ⨾ υ₂) ⨾ υ′ ⨾ ψ ⨾ ψ′) _ (still-then (wk-still ψ′ sm) λ _ → via-still mb) p′ lo‴)
          λ _ _ → doneʷ

  ≤ᵖ-after : ∀ {i lo p} → i <ᵖ lo ≡ true → lo ≤ᵖ p → i <ᵖ p ≡ true
  ≤ᵖ-after         h (inj₁ refl) = h
  ≤ᵖ-after {i} {lo} {p} h (inj₂ g) = <ᵖ-trans i lo p h g

  all-snoc : ∀ {S : Set} {P : Pos → Set} (ss : List (S × Pos)) x → All P (map proj₂ ss) → P (proj₂ x) → All P (map proj₂ (ss ++ [ x ]))
  all-snoc []       x []       px = px ∷ []
  all-snoc (y ∷ ys) x (q ∷ qs) px = q ∷ all-snoc ys x qs px

  all-map : ∀ {P Q : Pos → Set} {js} → (∀ {j} → P j → Q j) → All P js → All Q js
  all-map f []       = []
  all-map f (q ∷ qs) = f q ∷ all-map f qs

  pairs-snoc : ∀ {S : Set} (ss : List (S × Pos)) x → AllPairs (λ i j → i <ᵖ j ≡ true) (map proj₂ ss)
             → All (λ i → i <ᵖ proj₂ x ≡ true) (map proj₂ ss) → AllPairs (λ i j → i <ᵖ j ≡ true) (map proj₂ (ss ++ [ x ]))
  pairs-snoc []       x AllPairs.[]        []       = [] AllPairs.∷ AllPairs.[]
  pairs-snoc (y ∷ ys) x (r AllPairs.∷ rs) (b ∷ bs) = all-snoc ys x r b AllPairs.∷ pairs-snoc ys x rs bs

  -- A join lists itself past every joiner listed, all before the last,
  -- and moves the last on past where it joined.  Joining a completed
  -- subject completes at once, under `last`.
  joinᴷ-well : ∀ {A w} st → WellSub (joinᴷ {A} {w} st)
  joinᴷ-well st ρ o k p lo le (wn , wc , wx) wk = hereʷ (readRefʷ λ where
    σ true  _ → underʷ (wk-well σ (wc (p ++ [ last ]) lo (≤ᵖ-child p le))) λ lo′ _ → wk-well σ (wk Heap.same _ doneˢ p lo′)
    σ false _ → newRefʷ tt λ σ′ l →
      registerʷ ((λ a q lo′ le′ → whenG-well l (wk-well (σ ⨾ σ′) (wn a q lo′ le′)))
                , (λ q lo′ le′ → whenG-well l (wk-well (σ ⨾ σ′) (wc q lo′ le′)))
                , readRefˢ λ where
                     τ true  → wk-still τ (wk-still (σ ⨾ σ′) wx)
                     τ false → doneˢ)
        λ τ sk → readRefʷ λ π ss (asc , below) →
          let below′ = all-map (λ {j} h → ≤ᵖ-after {j} h le) below in
          writeRefʷ (p ++ [ last ]) (≤ᵖ-child p le , inj₂ ([ last ] , refl))
            (pairs-snoc ss _ asc below′
            , all-snoc ss _ (all-map (λ {j} h → ≤ᵖ-after {j} h (≤ᵖ-child p (inj₁ refl))) below′) (<ᵖ-below p []))
            (wk-well π (wk ((σ ⨾ σ′) ⨾ τ) (record { unsubscribe = writeRef (wkR τ l) false skipᴬ })
                           (writeRefˢ (λ _ → tt) doneˢ) p (p ++ [ last ]))))

  -- The completion under `last`, then the continuation.
  emptyᴷ-well : ∀ {A w} → WellSub (emptyᴷ {A} {w})
  emptyᴷ-well ρ o k p lo le (wn , wc , wx) wk =
    underʷ (wc (p ++ [ last ]) lo (≤ᵖ-child p le)) λ lo′ _ → wk Heap.same _ doneˢ p lo′

  -- The i-th value under `ix i`, each after the last left by the one
  -- before; the completion under `last`, after them all.
  emit-well : ∀ {A w} (o : Observer A w) → WellObs o → ∀ i xs p lo → lo ≤ᵖ (p ++ [ ix i ]) → Well p lo (emitAll o i xs)
  emit-well o (wn , wc , wx) i []       p lo le = underʷ (wc (p ++ [ last ]) lo (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] refl)))) λ _ _ → doneʷ
  emit-well o wo@(wn , wc , wx) i (x ∷ xs) p lo le = still-bind wx λ where
    true  → doneʷ
    false → underʷ (wn x (p ++ [ ix i ]) lo le) λ lo′ st → emit-well o wo (suc i) xs p lo′ (settled-next p (<ᵖ-ix i) (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] (<ᵖ-ix i)))) st)

  ofᴷ-well : ∀ {A w} xs → WellSub (ofᴷ {A} {w} xs)
  ofᴷ-well xs ρ o k p lo le wo wk = bind-well (emit-well o wo 0 xs p lo (≤ᵖ-child p le)) λ lo′ _ _ → wk Heap.same _ doneˢ p lo′

  -- A cold source registers its observer and starts; its stop is `Still`.
  coldᴷ-well : ∀ {A w} c → WellSub (via {A} {w} (startCold c))
  coldᴷ-well c ρ o k p lo le wo wk = registerʷ wo λ σ s → startColdʷ le λ lo′ st τ h → wk (σ ⨾ τ) _ (stopˢ doneˢ) p lo′

  mapᴷ-well : ∀ {A B w} f {s : Subscribe A w} → WellSub {A} {w} s → WellSub (mapᴷ {A} {B} f s)
  mapᴷ-well f hs ρ o k p lo le (wn , wc , wx) wk = hs ρ _ k p lo le ((λ a → wn (f a)) , wc , wx) wk

  -- The accumulator is read, written, and only then delivered.
  scanᴷ-well : ∀ {A B w} f z {s : Subscribe A w} → WellSub {A} {w} s → WellSub (scanᴷ {A} {B} f z s)
  scanᴷ-well f z hs ρ o k p lo le wo wk = newRefʷ tt λ σ r →
    let (wn , wc , wx) = wk-obs σ wo in
    hs (ρ ⨾ σ) _ _ p lo le
       ((λ a q lo′ le′ → readRefʷ λ τ b _ → wk-well {m = writeRef r (f b a) (Observer.next (wkObs σ o) (f b a))} τ (writeRefʷ lo′ settled-refl tt (wn (f b a) q lo′ le′)))
       , wc , wx)
       λ τ → wk (σ ⨾ τ)

  readB-well : ∀ {v X C p lo} (r : Ref v (baseᵗ X)) {k : X → Act v C} → (∀ x → Well p lo (k x)) → Well p lo (readB r k)
  readB-well r h = readRefʷ λ σ x _ → wk-well σ (h x)

  readF-well : ∀ {v X C p lo} (r : Ref v (fifo X)) {k : List X → Act v C} → (∀ x → Well p lo (k x)) → Well p lo (readF r k)
  readF-well r h = readRefʷ λ σ x _ → wk-well σ (h x)

  when-ok : ∀ {v p lo} b {m : Act v ⊤} → Well p lo m → Well p lo (when b m)
  when-ok true  w = w
  when-ok false w = doneʷ

  if-ok : ∀ {v C p lo} b {m n : Act v C} → Well p lo m → Well p lo n → Well p lo (if b then m else n)
  if-ok true  wm wn = wm
  if-ok false wm wn = wn

  -- A cell rewritten so it fits wherever the last is.
  modify-still : ∀ {v t} (r : Ref v t) (f : ∀ {u} → v ⊑ u → El u t → El u t) → (∀ {u} (σ : v ⊑ u) x lo → Fits lo t (f σ x)) → Still (modify r f)
  modify-still r f h = readRefˢ λ σ x → writeRefˢ (h σ x) doneˢ

  each-cut : ∀ {v} (cs : List (Cut v)) → Still (each cs cut)
  each-cut []       = doneˢ
  each-cut (c ∷ cs) = still-then (cut-still c) λ _ → each-cut cs

  -- A lane is subscribed under `ix 1` of wherever the run is, so past
  -- the last; its completion hands its slot on by a send at no earlier a
  -- position.  Killing the lanes is `Still`, so a switch's next lane
  -- starts from where the last was.
  module FlatWell {A B w} (op : FlatOp) (f : A → Subscribe B w) (o : Observer B w) (st : Flat A w)
                  (hf : ∀ a → WellSub {B} {w} (f a)) (wo : WellObs o) where
    open FlatMap op f o st hiding (run)
    open FlatMap op f o st using () renaming (run to runᶠ)

    settle-well : ∀ q lo → lo ≤ᵖ q → Well q lo settle
    settle-well q lo le = readB-well (Flat.outerDone st) λ d → readB-well (Flat.active st) λ n → readF-well (Flat.queue st) λ qs →
      when-ok (d ∧ (n ≡ᵇ 0) ∧ null qs) (proj₁ (proj₂ wo) q lo le)

    killAll-still : Still killAll
    killAll-still = readRefˢ λ σ cs → writeRefˢ (λ _ → tt) (writeRefˢ (λ _ → tt) (each-cut cs))

    handOn-well : ∀ {v} (σ : w ⊑ v) mr q lo → lo ≤ᵖ q → Well q lo (handOn σ mr)
    handOn-well σ nothing  q lo le = wk-well {m = settle} σ (settle-well q lo le)
    handOn-well σ (just r) q lo le = sendʷ le λ _ _ → doneʷ

    lane-well : ∀ {v} (σ : w ⊑ v) c → WellObs (lane σ c)
    lane-well σ c = proj₁ (wk-obs σ wo)
                  , (λ q lo le → writeRefʷ lo settled-refl tt
                       (still-bind {f = λ _ → readRef (Flat.refill (wkFlat σ st)) λ τ → handOn (σ ⨾ τ)} (modify-still (Flat.active (wkFlat σ st)) (λ _ → pred) λ _ _ _ → tt) λ _ →
                         readRefʷ λ τ mr _ → handOn-well (σ ⨾ τ) mr q lo le))
                  , wk-still σ (proj₂ (proj₂ wo))

    -- The lane itself, once its cut exists.
    started : Subscribe B w → ∀ {v} → w ⊑ v → Cut v → Act v ⊤
    started l σ c = modify (Flat.lanes (wkFlat σ st)) (λ τ cs → wkCut τ c ∷ cs) >>ᴬ under (ix 1) (l σ (guarded c (lane σ c)) λ τ → attach (wkCut τ c)) skipᴬ

    started-well : ∀ (l : Subscribe B w) → WellSub l → ∀ {v} (σ : w ⊑ v) c q lo → lo ≤ᵖ q → Well q lo (started l σ c)
    started-well l hl σ c q lo le =
      still-bind {f = λ _ → under (ix 1) (l σ (guarded c (lane σ c)) λ τ → attach (wkCut τ c)) skipᴬ} (modify-still (Flat.lanes (wkFlat σ st)) (λ τ cs → wkCut τ c ∷ cs) λ _ _ _ → tt) λ _ →
        underʷ (hl σ (guarded c (lane σ c)) (λ τ → attach (wkCut τ c)) (q ++ [ ix 1 ]) lo (≤ᵖ-child q le) (guarded-well c (lane-well σ c)) λ π sub sm → attach-well (wkCut π c) sub sm) λ _ _ → doneʷ

    start-well : ∀ (l : Subscribe B w) → WellSub l → ∀ q lo → lo ≤ᵖ q → Well q lo (start l)
    start-well l hl q lo le = still-bind (proj₂ (proj₂ wo)) λ where
      true  → doneʷ
      false → still-bind {f = λ _ → newCut (started l)} (modify-still (Flat.active st) (λ _ → suc) λ _ _ _ → tt) λ _ →
                newRefʷ tt λ σ lv → newRefʷ tt λ τ h → started-well l hl (σ ⨾ τ) (wkR τ lv , h) q lo le

    dequeue-well : ∀ q lo → lo ≤ᵖ q → Well q lo dequeue
    dequeue-well q lo le = readF-well (Flat.queue st) λ where
      []       → settle-well q lo le
      (a ∷ as) → writeRefʷ lo settled-refl tt (start-well (f a) (hf a) q lo le)

    admit-well : ∀ op′ a q lo → lo ≤ᵖ q → Well q lo (admit op′ a)
    admit-well (mergeᶠ nothing)  a q lo le = start-well (f a) (hf a) q lo le
    admit-well (mergeᶠ (just n)) a q lo le = readB-well (Flat.active st) λ c →
      if-ok (c <ᵇ n) (start-well (f a) (hf a) q lo le) (still-well (modify-still (Flat.queue st) (λ _ → _++ [ a ]) λ _ _ _ → tt))
    admit-well switchᶠ           a q lo le = still-bind {f = λ _ → start (f a)} killAll-still λ _ → start-well (f a) (hf a) q lo le
    admit-well exhaustᶠ          a q lo le = readB-well (Flat.active st) λ c → when-ok (c ≡ᵇ 0) (start-well (f a) (hf a) q lo le)

    run-well : ∀ oc {s : Subscribe A w} → WellSub s → ∀ {k : Kont w} → WellKont k → ∀ p lo → lo ≤ᵖ p → Well p lo (runᶠ oc s k)
    run-well oc hs wk p lo le = registerʷ ((λ _ q lo′ le′ → dequeue-well q lo′ le′) , (λ _ _ _ → doneʷ) , doneˢ) λ σ r →
      writeRefʷ lo settled-refl tt (hs σ _ _ p lo le
        (guarded-well (wkCut σ oc) ((λ a q lo′ le′ → wk-well {m = admit op a} σ (admit-well op a q lo′ le′))
                                   , (λ q lo′ le′ → writeRefʷ lo′ settled-refl tt (wk-well {m = settle} σ (settle-well q lo′ le′)))
                                   , wk-still σ (proj₂ (proj₂ wo))))
        λ τ sub sm p′ lo′ → bind-well (attach-well (wkCut (σ ⨾ τ) oc) sub sm p′ lo′) λ lo″ _ _ →
          wk (σ ⨾ τ) _ (still-then (cut-still (wkCut (σ ⨾ τ) oc)) λ _ → wk-still (σ ⨾ τ) killAll-still) p′ lo″)

  newFlat-well : ∀ {A w C p lo} {k : ∀ {v} → w ⊑ v → Flat A v → Act v C} → (∀ {v} (σ : w ⊑ v) st → Well p lo (k σ st)) → Well p lo (newFlat k)
  newFlat-well h = newRefʷ tt λ _ _ → newRefʷ tt λ _ _ → newRefʷ tt λ _ _ → newRefʷ tt λ _ _ → newRefʷ tt λ _ _ → h _ _

  newCut-well : ∀ {w C p lo} {k : ∀ {v} → w ⊑ v → Cut v → Act v C} → (∀ {v} (σ : w ⊑ v) c → Well p lo (k σ c)) → Well p lo (newCut k)
  newCut-well h = newRefʷ tt λ _ _ → newRefʷ tt λ _ _ → h _ _

  -- Each lane subscribed under `ix 1`, its observer guarded by its cut.
  flatMapᴷ-well : ∀ {A B w} op {f : A → Subscribe B w} {s : Subscribe A w} → (∀ a → WellSub {B} {w} (f a)) → WellSub {A} {w} s → WellSub (flatMapᴷ op f s)
  flatMapᴷ-well op {f} {s} hf hs ρ o k p lo le wo wk = newFlat-well λ σ st → newCut-well λ τ oc →
    FlatWell.run-well op (λ a → wkSub (ρ ⨾ σ ⨾ τ) (f a)) (wkObs (σ ⨾ τ) o) (wkFlat τ st) (λ a ρ′ → hf a ((ρ ⨾ σ ⨾ τ) ⨾ ρ′)) (wk-obs (σ ⨾ τ) wo)
                      oc (λ ρ′ → hs ((ρ ⨾ σ ⨾ τ) ⨾ ρ′)) (λ υ → wk ((σ ⨾ τ) ⨾ υ)) p lo le
