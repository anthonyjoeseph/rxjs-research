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

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat using (ℕ; zero; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; _++_; [_]; map; null)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; maybe; just; nothing) renaming (map to mapMaybe)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Level using (Lift; lift; lower)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import Tree as T
open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList using (Pos; From; done; quiet; at; emit; stall; close; From∞; ix; last; root; _<ᵖ_; <ᵖ-trans; <ᵖ-below; <ᵖ-part; <ᵖ-sub; <ᵖ-ix; Timeline) renaming (sub to subᴾ)
open import operation.AbstractObservable using (Ty; _⊗_; joins; module Run; module Heap)
  renaming (base to baseᵗ; ref to refᵗ; sink to sinkᵗ; quiet to quietᵗ; list to listᵗ; maybe to maybeᵗ) renaming (module Machine to Shared)
open import operation.PureObservable using (PureObs; Pureᴾ; Out; note; fin; module Pure)
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
  open Pure R using (Timer; cascade; recorder; mapList)
  open Kit using (Cut; wkCut; cut; guard; guarded; attach; when; skipᴬ; each; unsubscribeVia; readB; modify; newCut)
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
      registerʷ ((λ a q lo′ le′ → when-well l (wk-well (σ ⨾ σ′) (wn a q lo′ le′)))
                , (λ q lo′ le′ → when-well l (wk-well (σ ⨾ σ′) (wc q lo′ le′)))
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
    settle-well q lo le = readB-well (Flat.outerDone st) λ d → readB-well (Flat.active st) λ n → readB-well (Flat.queue st) λ qs →
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
    dequeue-well q lo le = readB-well (Flat.queue st) λ where
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



  -- Every compiled tree well, kernel by kernel.
  compile-well : ∀ {Γ A w} (o : Obs _ Γ A) (e : Env Γ w) → WellEnv e → WellSub (compile o e)
  compile-well (T.cold c)          e we = coldᴷ-well c
  compile-well T.empty             e we = emptyᴷ-well
  compile-well (T.of xs)           e we = ofᴷ-well xs
  compile-well (T.map f s)         e we = mapᴷ-well f (compile-well s e we)
  compile-well (T.scan f z s)      e we = scanᴷ-well f z (compile-well s e we)
  compile-well (T.takeWhile i p s) e we = takeWhileᴷ-well i p (compile-well s e we)
  compile-well (T.flatMap op f s)  e we = flatMapᴷ-well op (λ a → compile-well (f a) e we) (compile-well s e we)
  compile-well (T.connect s b)     e we = connectᴷ-well (compile-well s e we) λ σ st → compile-well b (st ∷ wkEnv σ e) (lift tt)
  compile-well (T.connected i)     e we = joinᴷ-well _
  compile-well (T.defer l)         e we = λ ρ o k p lo le wo wk → unfoldʷ (lift tt) wo (λ τ t → wk τ _ (cancelˢ doneˢ)) le λ lo′ st → doneʷ

  ----------------------------------------------------------------------
  -- THE WALK: a well configuration rises

  -- A level's burst, by position: playing from `c` at its `i`-th frame,
  -- or over, its completion owed or delivered.
  data Entry : Set where
    playing : Pos → ℕ → Entry
    over    : Entry

  entry : ∀ {h} → Maybe (Playing h) → Entry
  entry (just b) = playing (Playing.under′ b) (Playing.index b)
  entry nothing  = over

  -- What is owed, by position: a resume, or a completion there.
  due : ∀ {h} → Todo h → Maybe Pos
  due resume        = nothing
  due (owing _ _ e) = just e

  -- The root's level, held over the bottom: a timer's burst playing, its
  -- completion owed, delivered, its frames rescheduled, or nothing.
  data RootAt (lo : Pos) : List Entry → List (Maybe Pos) → Set where
    playingʳ : ∀ {c i} → lo ≤ᵖ (c ++ [ ix i ]) → RootAt lo [ playing c i ] []
    owingʳ   : ∀ {e} → lo ≤ᵖ e → RootAt lo [ over ] [ just e ]
    overʳ    : RootAt lo [ over ] []
    resumeʳ  : RootAt lo [] [ nothing ]
    idleʳ    : RootAt lo [] []

  -- A cold's level, started at `P` over the levels `es`: its burst
  -- playing under `P`, its completion owed at `P ++ [ last ]`, delivered,
  -- or its frames on timers.
  data ColdAt (P lo : Pos) (es : List Entry) : List Entry → List (Maybe Pos) → Set where
    playingᶜ : ∀ {i} → lo ≤ᵖ (P ++ [ ix i ]) → ColdAt P lo es (playing P i ∷ es) []
    owingᶜ   : lo ≤ᵖ (P ++ [ last ]) → ColdAt P lo es (over ∷ es) [ just (P ++ [ last ]) ]
    overᶜ    : ColdAt P lo es (over ∷ es) []
    resumeᶜ  : ColdAt P lo es es [ nothing ]

  mutual
    -- What waits on the stack, well.  `WellStack p lo k es`: pushed at
    -- `p` with the last delivery at `lo`, `k` resumes well from wherever
    -- a scope at `p` may leave the last, as `Well`'s own continuations
    -- do; `es`, the bursts of the levels it holds.  A scope's frame puts
    -- back an enclosing position.  A delivery's frames hand the turn back
    -- to the level that fed it, from wherever the delivery left the last.
    data WellStack (p lo : Pos) : ∀ {w X} → Stack w X → List Entry → Set₁ where
      bottomʷ : ∀ {w} → WellStack p lo (bottom {w}) []
      restʷ   : ∀ {u w B lo₀ es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Settled p lo₀ lo → (∀ lo′ → Settled p lo lo′ → Well p lo′ m)
              → WellStack p lo₀ k es → WellStack p lo (push (rest m) ρ k) es
      backʷ   : ∀ {u w B lo₀ es} q {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Under q p → Settled q lo₀ lo → (∀ lo′ → Settled p lo lo′ → Well q lo′ m)
              → WellStack q lo₀ k es → WellStack p lo (push (back q m) ρ k) es
      fedʷ    : ∀ {t u w es} P {ρ : u ⊑ w} {σ : t ⊑ u} {k : Stack t ⊤} → (∀ lo′ → Settled p lo lo′ → WellHeld lo′ P k es [])
              → WellStack p lo (push (back P (done tt)) ρ (push rehold σ k)) es

    -- What waits on a `Still` computation: it returns to the last exactly
    -- where it found it.  A cancel's frame, a still frame, the turn handed
    -- back after a delivery, or a poll's answer.
    data StillStack (p lo : Pos) : ∀ {w X} → Stack w X → List Entry → Set₁ where
      stillRestʷ  : ∀ {u w B lo₀ es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Settled p lo₀ lo → Well p lo m → WellStack p lo₀ k es
                  → StillStack p lo (push (rest m) ρ k) es
      stillStillʷ : ∀ {u w B es} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Still m → StillStack p lo k es → StillStack p lo (push (rest m) ρ k) es
      reholdʷ     : ∀ {u w es} {ρ : u ⊑ w} {k : Stack u ⊤} → WellHeld lo p k es [] → StillStack p lo (push rehold ρ k) es
      toldʷ       : ∀ {u w c i es} {ρ : u ⊑ w} {k : Stack u ⊤} → WellHeld lo p k (playing c i ∷ es) [] → StillStack p lo (push told ρ k) (playing c i ∷ es)

    -- The driver's turn at `P`, well: over the bottom, the root's level;
    -- over a cold's frame, that cold's level, the last settled in `P`
    -- from where its frame was pushed.  `ts`: what is owed it.
    data WellHeld (lo P : Pos) : ∀ {w} → Stack w ⊤ → List Entry → List (Maybe Pos) → Set₁ where
      rootʰ : ∀ {w es ts} → RootAt lo es ts → WellHeld lo P (bottom {w}) es ts
      coldʰ : ∀ {u w B lo₀ es₀ es ts} {m : Act w B} {ρ : u ⊑ w} {k : Stack u B} → Settled P lo₀ lo → WellStack P lo₀ (push (rest m) ρ k) es₀
            → ColdAt P lo es₀ es ts → WellHeld lo P (push (rest m) ρ k) es ts

  -- What runs next, well at the configuration's position, the last
  -- delivery settled from where the top frame was pushed.  A `Still`
  -- computation runs over a `StillStack`.  Nothing is owed but at the
  -- driver's turn.
  data WellCtl {h : World} (lo p : Pos) : Ctl h → List Entry → List (Maybe Pos) → Set₁ where
    runʷ      : ∀ {w B a lo₀ es} {σ : w ⊑ h} {k : Stack w B} → Settled p lo₀ lo → Well p lo a → WellStack p lo₀ k es → WellCtl lo p (run a σ k) es []
    retʷ      : ∀ {w X x lo₀ es} {σ : w ⊑ h} {k : Stack w X} → Settled p lo₀ lo → WellStack p lo₀ k es → WellCtl lo p (ret x σ k) es []
    stillʷ    : ∀ {w B a es} {σ : w ⊑ h} {k : Stack w B} → Still a → StillStack p lo k es → WellCtl lo p (run a σ k) es []
    stillRetʷ : ∀ {w X x es} {σ : w ⊑ h} {k : Stack w X} → StillStack p lo k es → WellCtl lo p (ret x σ k) es []
    heldʷ     : ∀ {w es ts} {σ : w ⊑ h} {k : Stack w ⊤} → WellHeld lo p k es ts → WellCtl lo p (held σ k) es ts
    notingʷ   : ∀ {w B a lo₀ es} {k′ : ⊤ → Act h B} {σ : w ⊑ h} {k : Stack w B} → lo ≤ᵖ p → Settled p lo₀ lo → Well p p (k′ tt) → WellStack p lo₀ k es
              → WellCtl lo p (asking (note a) k′ σ k) es []
    finningʷ  : ∀ {w B es} {k′ : ⊤ → Act h B} {σ : w ⊑ h} {k : Stack w B} → lo ≤ᵖ p → WellCtl lo p (asking fin k′ σ k) es []

  -- What an entry holds, well: a cell fitting the last delivery, a well
  -- observer's callbacks, a `Still` unsubscribe.
  WellVal : ∀ {w} → Pos → ∀ k → Val w k → Set₁
  WellVal lo (cell t) x  = Lift _ (Fits lo t (lower x))
  WellVal lo (slot A) cb = WellObs (record { next = Callbacks.onNext cb ; complete = Callbacks.onComplete cb ; closed = Callbacks.isClosed cb })
  WellVal lo hush m      = Still m
  WellVal lo play _      = Lift _ ⊤

  -- Every entry the heap holds well, as it was stored.
  record WellHeap {h} (lo : Pos) (hp : Heapᴹ h) : Set₁ where
    constructor heapʷ
    field holds : ∀ {k} (i : h ∋ k) → WellVal lo k (Stored.val (get hp i))
  open WellHeap

  -- The run well: what runs next and every frame waiting on the stack,
  -- every level's burst playing past the last, everything the heap
  -- holds, and the root not yet complete.
  record WellRun (lo : Pos) (m : Mach) : Set₁ where
    constructor wellʳ
    field
      {es}    : List Entry
      {ts}    : List (Maybe Pos)
      ctl     : WellCtl lo (Conf.pos (Mach.conf m)) (Conf.ctl (Mach.conf m)) es ts
      entries : map entry (Mach.bursts m) ≡ es
      dues    : map due (Mach.todo m) ≡ ts
      heap    : WellHeap lo (Conf.heap (Mach.conf m))
      fresh   : Mach.ended m ≡ false

  -- One timer pops before another: its cascade is the earlier, so two
  -- due on one tick pop in the order of the positions they were set at.
  Before : ∀ {h} → Timer h → Timer h → Set
  Before tm t′ = cascade tm <ᵖ cascade t′ ≡ true

  -- The queue well: every timer past every position shown, and in the
  -- order they pop.
  record WellQueue (lo : Pos) (m : Mach) : Set₁ where
    field
      timers : All (λ tm → lo <ᵖ cascade tm ≡ true) (Mach.timers m)
      queued : AllPairs Before (Mach.timers m)

  record WellMach (lo : Pos) (m : Mach) : Set₁ where
    field
      going : WellRun lo m
      queue : WellQueue lo m

  -- One step, its next configuration `P` and never earlier.
  data StepBy (P : Pos → Mach → Set₁) (lo : Pos) : Step → Set₁ where
    silentʷ   : ∀ {m lo′} → lo ≤ᵖ lo′ → P lo′ m → StepBy P lo (silent m)
    valueʷ    : ∀ {t p a m} → lo ≤ᵖ p → P p m → StepBy P lo (value t p a m)
    completeʷ : ∀ {p} → lo ≤ᵖ p → StepBy P lo (complete p)
    drainedʷ  : StepBy P lo drained

  WellStep : Pos → Step → Set₁
  WellStep = StepBy WellMach

  -- The queue well where the run's step left the last.
  QueueAt : ∀ {lo s} → StepBy WellRun lo s → Set₁
  QueueAt (silentʷ {m} {lo′} _ _) = WellQueue lo′ m
  QueueAt (valueʷ {p = p} {m = m} _ _) = WellQueue p m
  QueueAt (completeʷ _)          = Lift _ ⊤
  QueueAt drainedʷ               = Lift _ ⊤

  joinʷ : ∀ {lo s} (r : StepBy WellRun lo s) → QueueAt r → WellStep lo s
  joinʷ (silentʷ le r)  q = silentʷ le (record { going = r ; queue = q })
  joinʷ (valueʷ le r)   q = valueʷ le (record { going = r ; queue = q })
  joinʷ (completeʷ le)  _ = completeʷ le
  joinʷ drainedʷ        _ = drainedʷ

  -- The loop's turn: held, nothing playing or owed, so the next step pops
  -- a timer.
  idle : Mach → Bool
  idle m with Conf.ctl (Mach.conf m) | Mach.bursts m | Mach.todo m
  ... | held _ _ | [] | [] = true
  ... | _        | _  | _  = false

  -- A cell's fit holds of any later last.
  fits-up : ∀ {w lo lo′} t {a : El w t} → lo ≤ᵖ lo′ → Fits lo t a → Fits lo′ t a
  fits-up (joins A)  le (ps , below) = ps , All-map le below
    where All-map : ∀ {lo lo′} → lo ≤ᵖ lo′ → ∀ {xs} → All (λ i → i <ᵖ lo ≡ true) xs → All (λ i → i <ᵖ lo′ ≡ true) xs
          All-map le []                 = []
          All-map (inj₁ refl) (x ∷ xs)  = x ∷ All-map (inj₁ refl) xs
          All-map {lo} {lo′} (inj₂ h) {i ∷ _} (x ∷ xs) = <ᵖ-trans i lo lo′ x h ∷ All-map (inj₂ h) xs
  fits-up (baseᵗ X)  le f = tt
  fits-up (refᵗ t)   le f = tt
  fits-up (sinkᵗ A)  le f = tt
  fits-up quietᵗ     le f = tt
  fits-up (listᵗ t)  le f = tt
  fits-up (maybeᵗ t) le f = tt
  fits-up (s ⊗ t)   le f = tt

  heap-up : ∀ {h lo lo′} {hp : Heapᴹ h} → lo ≤ᵖ lo′ → WellHeap lo hp → WellHeap lo′ hp
  heap-up le wh = heapʷ λ where
    {cell t} i → lift (fits-up t le (lower (holds wh i)))
    {slot A} i → holds wh i
    {hush}   i → holds wh i
    {play}   i → holds wh i

  -- The last at a delivery: settled there from any no later.
  settled-at : ∀ {p lo₀ lo} → Settled p lo₀ lo → lo ≤ᵖ p → Settled p lo₀ p
  settled-at {p} (a , _) le = ≤ᵖ-trans a le , inj₂ ([] , sym (++-identityʳ p))

  -- The machine's driver state weakened, by position unmoved.
  entries-wk : ∀ {h v} (ρ : h ⊑ v) (bs : List (Maybe (Playing h))) → map entry (mapList (mapMaybe (wkPlaying ρ)) bs) ≡ map entry bs
  entries-wk ρ []             = refl
  entries-wk ρ (just b ∷ bs)  = cong (_ ∷_) (entries-wk ρ bs)
  entries-wk ρ (nothing ∷ bs) = cong (_ ∷_) (entries-wk ρ bs)

  -- An entry well, weakened.
  val-wk : ∀ {w v lo} k (ρ : w ⊑ v) {x : Val w k} → WellVal lo k x → WellVal lo k (wkVal k ρ x)
  val-wk (cell t) ρ {x} f = lift (fits-wk _ t ρ (lower x) (lower f))
  val-wk (slot A) ρ wo    = wk-obs ρ wo
  val-wk hush     ρ s     = wk-still ρ s
  val-wk play     ρ _     = lift tt

  look-well : ∀ {h lo} {hp : Heapᴹ h} → WellHeap lo hp → ∀ {k} (i : h ∋ k) → WellVal lo k (look hp i)
  look-well {hp = hp} wh {k} i = val-wk k (Stored.into (get hp i)) (holds wh i)

  -- The heap grown, and written, well.
  wkAll-well : ∀ {h v w lo} (ρ : h ⊑ v) (xs : All (Stored h) w) → (∀ {k} (i : w ∋ k) → WellVal lo k (Stored.val (get xs i)))
             → ∀ {k} (i : w ∋ k) → WellVal lo k (Stored.val (get (wkAll ρ xs) i))
  wkAll-well ρ (stored x σ ∷ xs) wx here      = wx here
  wkAll-well ρ (stored x σ ∷ xs) wx (there i) = wkAll-well ρ xs (λ j → wx (there j)) i

  extend-well : ∀ {h lo k} {hp : Heapᴹ h} {x : Val (k ∷ h) k} → WellHeap lo hp → WellVal lo k x → WellHeap lo (extend hp x)
  extend-well {hp = hp} wh wx = heapʷ λ where
    here      → wx
    (there i) → wkAll-well new hp (holds wh) i

  put-well : ∀ {h w lo k} (xs : All (Stored h) w) (i : w ∋ k) {y : Stored h k} → WellVal lo k (Stored.val y) → (∀ {k′} (j : w ∋ k′) → WellVal lo k′ (Stored.val (get xs j)))
           → ∀ {k′} (j : w ∋ k′) → WellVal lo k′ (Stored.val (get (put xs i y) j))
  put-well (x ∷ xs) here      wy wx here      = wy
  put-well (x ∷ xs) here      wy wx (there j) = wx (there j)
  put-well (x ∷ xs) (there i) wy wx here      = wx here
  put-well (x ∷ xs) (there i) wy wx (there j) = put-well xs i wy (λ j′ → wx (there j′)) j

  store-well : ∀ {h lo k} {hp : Heapᴹ h} (i : h ∋ k) {x : Val h k} → WellHeap lo hp → WellVal lo k x → WellHeap lo (store hp i x)
  store-well {hp = hp} i wh wx = heapʷ (put-well hp i wx (holds wh))

  -- A cold started at `p`: its first frame playing, or its completion
  -- owed, or its frames on timers.
  started-well : ∀ {lo h A} {hp : Heapᴹ h} {p u B es} {m : Act h B} {ρ : u ⊑ h} {k : Stack u B} {cl tm bu lg mk}
                 (s : Sink h A) (hd : Handle h) (f : From A 0) → lo ≤ᵖ p → WellStack p lo (push (rest m) ρ k) es → map entry bu ≡ es → WellHeap lo hp
               → WellRun lo (starting (mach ⟨ hp , p , held same (push (rest m) ρ k) ⟩ cl tm bu [] lg false mk) s hd f)
  started-well s hd done            le ws eb wh = wellʳ (heldʷ (coldʰ settled-refl ws (owingᶜ (≤ᵖ-child _ le)))) (cong (over ∷_) eb) refl wh refl
  started-well s hd quiet           le ws eb wh = wellʳ (heldʷ (coldʰ settled-refl ws resumeᶜ)) eb refl wh refl
  started-well s hd (at zero _ b)   le ws eb wh = wellʳ (heldʷ (coldʰ settled-refl ws (playingᶜ (≤ᵖ-child _ le)))) (cong (_ ∷_) eb) refl wh refl
  started-well s hd (at (suc t) _ b) le ws eb wh = wellʳ (heldʷ (coldʰ settled-refl ws resumeᶜ)) eb refl wh refl

  -- A run step from a well computation.
  runs-run : ∀ {lo lo₀ h} {hp : Heapᴹ h} {p w B es} {a : Act h B} {σ : w ⊑ h} {k : Stack w B} {cl tm bu lg mk}
           → Settled p lo₀ lo → Well p lo a → WellStack p lo₀ k es → map entry bu ≡ es → WellHeap lo hp
           → StepBy WellRun lo (step (mach ⟨ hp , p , run a σ k ⟩ cl tm bu [] lg false mk))
  runs-run st doneʷ ws eb wh = silentʷ (inj₁ refl) (wellʳ (retʷ st ws) eb refl wh refl)
  runs-run {lo} {bu = bu} st (newRefʷ {t} {a} f h) ws eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ st (h new here) ws) (trans (entries-wk new bu) eb) refl (extend-well wh (lift (fits-wk lo t new a f))) refl)
  runs-run {hp = hp} st (readRefʷ {r = r} h) ws eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ st (h same _ (lower (look-well {hp = hp} wh r))) ws) eb refl wh refl)
  runs-run {hp = hp} st (writeRefʷ {r = r} lo′ st′ f wk) ws eb wh =
    silentʷ (proj₁ st′) (wellʳ (runʷ (settled-trans st st′) wk ws) eb refl (store-well r (heap-up {hp = hp} (proj₁ st′) wh) (lift f)) refl)
  runs-run {bu = bu} st (registerʷ wo h) ws eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ st (h new here) ws) (trans (entries-wk new bu) eb) refl (extend-well wh (wk-obs new wo)) refl)
  runs-run {lo = lo} {hp = hp} {p = p} st (sendʷ {s = s} {a = a} le h) ws eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (proj₁ (look-well {hp = hp} wh s) a p lo le) (restʷ st h ws)) eb refl wh refl)
  runs-run {lo = lo} {hp = hp} {p = p} st (finishʷ {s = s} le h) ws eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (proj₁ (proj₂ (look-well {hp = hp} wh s)) p lo le) (restʷ st h ws)) eb refl wh refl)
  runs-run {bu = bu} st (startColdʷ {c = c} {s = s} le h) ws eb wh =
    silentʷ (inj₁ refl) (started-well (wk∋ new s) here (lower c) le (restʷ st (λ lo′ st′ → h lo′ st′ new here) ws) (trans (entries-wk new bu) eb)
                                      (extend-well wh (lift tt)))
  runs-run st (stopʷ {h = hd} wk) ws eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ st wk ws) eb refl (store-well hd wh (lift tt)) refl)
  runs-run {bu = bu} st (stashʷ sm h) ws eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ st (h new here) ws) (trans (entries-wk new bu) eb) refl (extend-well wh (wk-still new sm)) refl)
  runs-run {hp = hp} st (cancelʷ {t = t} wk) ws eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ (look-well {hp = hp} wh t) (stillRestʷ st wk ws)) eb refl wh refl)
  runs-run st (noteʷ le wk) ws eb wh = silentʷ (inj₁ refl) (wellʳ (notingʷ le st wk ws) eb refl wh refl)
  runs-run st (finʷ le) ws eb wh = silentʷ (inj₁ refl) (wellʳ (finningʷ le) eb refl wh refl)
  runs-run st (hereʷ wk) ws eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ st wk ws) eb refl wh refl)
  runs-run {p = p} st (underʷ {l = l} wm h) ws eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl wm (backʷ p ([ l ] , refl) st h ws)) eb refl wh refl)
  runs-run st divergeʷ ws eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ st divergeʷ ws) eb refl wh refl)
  runs-run {p = p} st (unfoldʷ {l = l} {e = e} we wo kp le h) ws eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (underʷ (compile-well (T.Later.force l) e (lift tt) same _ _ (p ++ [ ix 1 ]) _ (≤ᵖ-child p le) wo
                                                         λ σ′ sub us p′ lo′ → stashʷ us λ τ t → kp (σ′ ⨾ τ) t p′ lo′)
                                                 λ _ _ → doneʷ)
                                (restʷ st h ws)) eb refl wh refl)

  -- A run step from a still computation.
  runs-still : ∀ {lo h} {hp : Heapᴹ h} {p w B es} {a : Act h B} {σ : w ⊑ h} {k : Stack w B} {cl tm bu lg mk}
             → Still a → StillStack p lo k es → map entry bu ≡ es → WellHeap lo hp
             → StepBy WellRun lo (step (mach ⟨ hp , p , run a σ k ⟩ cl tm bu [] lg false mk))
  runs-still doneˢ ss eb wh = silentʷ (inj₁ refl) (wellʳ (stillRetʷ ss) eb refl wh refl)
  runs-still {lo} {bu = bu} (newRefˢ {t} {a} f h) ss eb wh =
    silentʷ (inj₁ refl) (wellʳ (stillʷ (h new here) ss) (trans (entries-wk new bu) eb) refl (extend-well wh (lift (fits-wk lo t new a (f lo)))) refl)
  runs-still (readRefˢ h) ss eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ (h same _) ss) eb refl wh refl)
  runs-still {lo} (writeRefˢ {r = r} f k) ss eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ k ss) eb refl (store-well r wh (lift (f lo))) refl)
  runs-still {hp = hp} (cancelˢ {t = t} k) ss eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ (look-well {hp = hp} wh t) (stillStillʷ k ss)) eb refl wh refl)
  runs-still (stopˢ {h = hd} k) ss eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ k ss) eb refl (store-well hd wh (lift tt)) refl)

  runs-well : ∀ {lo h} {hp : Heapᴹ h} {p w B} {a : Act h B} {σ : w ⊑ h} {k : Stack w B} {cl tm bu td lg en mk}
            → WellRun lo (mach ⟨ hp , p , run a σ k ⟩ cl tm bu td lg en mk) → StepBy WellRun lo (step (mach ⟨ hp , p , run a σ k ⟩ cl tm bu td lg en mk))
  runs-well {td = []} (wellʳ (runʷ st wa ws) eb refl wh refl) = runs-run st wa ws eb wh
  runs-well {td = []} (wellʳ (stillʷ sa ss) eb refl wh refl)  = runs-still sa ss eb wh
  runs-well {td = _ ∷ _} (wellʳ (runʷ _ _ _) _ () _ _)
  runs-well {td = _ ∷ _} (wellʳ (stillʷ _ _) _ () _ _)

  -- Settled in a scope is settled in any enclosing one.
  settled-up : ∀ {q p lo lo′} → Under q p → Settled p lo lo′ → Settled q lo lo′
  settled-up         u            (a , inj₁ e)            = a , inj₁ e
  settled-up {q} (y , refl) (a , inj₂ (z , refl)) = a , inj₂ (y ++ z , ++-assoc q y z)

  ∷-tail : ∀ {x y : Entry} {xs ys : List Entry} → _≡_ {A = List Entry} (x ∷ xs) (y ∷ ys) → xs ≡ ys
  ∷-tail refl = refl

  -- A poll answered closed: the level's burst over, a resume owed.
  quit-well : ∀ {lo P w c i es} {k : Stack w ⊤} → WellHeld lo P k (playing c i ∷ es) [] → WellHeld lo P k es [ nothing ]
  quit-well (rootʰ (playingʳ _))     = rootʰ resumeʳ
  quit-well (coldʰ st ws (playingᶜ _)) = coldʰ st ws resumeᶜ

  -- A return to a well stack.
  returns-run : ∀ {lo lo₀ h} {hp : Heapᴹ h} {p w X es} {x : X} {σ : w ⊑ h} {k : Stack w X} {cl tm bu lg mk}
              → Settled p lo₀ lo → WellStack p lo₀ k es → map entry bu ≡ es → WellHeap lo hp
              → StepBy WellRun lo (step (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu [] lg false mk))
  returns-run st bottomʷ eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl)
  returns-run {lo} {σ = σ} st (restʷ st₁ h ws) eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ (settled-trans st₁ st) (wk-well σ (h lo st)) ws) eb refl wh refl)
  returns-run {lo} {σ = σ} st (backʷ q u st₁ h ws) eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ (settled-trans st₁ (settled-up u st)) (wk-well σ (h lo st)) ws) eb refl wh refl)
  returns-run {lo} st (fedʷ P h) eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ doneˢ (reholdʷ (h lo st))) eb refl wh refl)

  -- A return to a still stack: the last where it was.
  returns-still : ∀ {lo h} {hp : Heapᴹ h} {p w X es} {x : X} {σ : w ⊑ h} {k : Stack w X} {cl tm bu lg mk}
                → StillStack p lo k es → map entry bu ≡ es → WellHeap lo hp
                → StepBy WellRun lo (step (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu [] lg false mk))
  returns-still {σ = σ} (stillRestʷ st h ws) eb wh = silentʷ (inj₁ refl) (wellʳ (runʷ st (wk-well σ h) ws) eb refl wh refl)
  returns-still {σ = σ} (stillStillʷ sm ss) eb wh = silentʷ (inj₁ refl) (wellʳ (stillʷ (wk-still σ sm) ss) eb refl wh refl)
  returns-still (reholdʷ wh′) eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ wh′) eb refl wh refl)
  returns-still {x = false} (toldʷ wh′) eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ wh′) eb refl wh refl)
  returns-still {x = true} {bu = b ∷ bu} (toldʷ wh′) eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ (quit-well wh′)) (∷-tail eb) refl wh refl)
  returns-still {x = true} {bu = []} (toldʷ wh′) () wh

  returns-well : ∀ {lo h} {hp : Heapᴹ h} {p w X} {x : X} {σ : w ⊑ h} {k : Stack w X} {cl tm bu td lg en mk}
               → WellRun lo (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu td lg en mk) → StepBy WellRun lo (step (mach ⟨ hp , p , ret x σ k ⟩ cl tm bu td lg en mk))
  returns-well {td = []} (wellʳ (retʷ st ws) eb refl wh refl)  = returns-run st ws eb wh
  returns-well {td = []} (wellʳ (stillRetʷ ss) eb refl wh refl) = returns-still ss eb wh
  returns-well {td = _ ∷ _} (wellʳ (retʷ _ _) _ () _ _)
  returns-well {td = _ ∷ _} (wellʳ (stillRetʷ _) _ () _ _)

  ∷-head : ∀ {x y : Entry} {xs ys : List Entry} → _≡_ {A = List Entry} (x ∷ xs) (y ∷ ys) → x ≡ y
  ∷-head refl = refl

  -- At most one thing is owed.
  owed-once : ∀ {lo P w es x y zs} {k : Stack w ⊤} → WellHeld lo P k es (x ∷ y ∷ zs) → ⊥
  owed-once (rootʰ ())
  owed-once (coldʰ _ _ ())

  -- A resume paid: the level returns to the frame its cold was started
  -- from, or the root's turn comes round.
  paid-resume : ∀ {lo h} {hp : Heapᴹ h} {p w es} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm bu lg mk}
              → WellHeld lo p k es [ nothing ] → map entry bu ≡ es → WellHeap lo hp
              → StepBy WellRun lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm bu (resume ∷ []) lg false mk))
  paid-resume (rootʰ resumeʳ)       eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl)
  paid-resume (coldʰ st ws resumeᶜ) eb wh = returns-run st ws eb wh

  -- A completion paid: delivered at its position, the level's turn
  -- handed back from wherever it leaves the last, the burst over.
  paid-owing : ∀ {lo h A} {hp : Heapᴹ h} {p w es e} {σ : w ⊑ h} {k : Stack w ⊤} {hd : Handle h} {s : Sink h A} {cl tm bu lg mk}
             → WellHeld lo p k es [ just e ] → map entry bu ≡ es → WellHeap lo hp
             → StepBy WellRun lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm bu (owing hd s e ∷ []) lg false mk))
  paid-owing {lo} {hp = hp} {p} {e = e} {hd = hd} {s} (rootʰ (owingʳ le)) eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (proj₁ (proj₂ (look-well wh s)) e lo le) (fedʷ p λ lo′ st → rootʰ overʳ)) eb refl wh′ refl)
    where wh′ = store-well {hp = hp} hd wh (lift tt)
  paid-owing {lo} {hp = hp} {p} {hd = hd} {s} (coldʰ st ws (owingᶜ le)) eb wh =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (proj₁ (proj₂ (look-well wh s)) (p ++ [ last ]) lo le)
                                     (fedʷ p λ lo′ st′ → coldʰ (settled-trans st (settled-up ([ last ] , refl) st′)) ws overᶜ)) eb refl wh′ refl)
    where wh′ = store-well {hp = hp} hd wh (lift tt)

  paid-well : ∀ {lo h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm bu t td lg en mk}
            → WellRun lo (mach ⟨ hp , p , held σ k ⟩ cl tm bu (t ∷ td) lg en mk) → StepBy WellRun lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm bu (t ∷ td) lg en mk))
  paid-well {t = resume}        {td = []}    (wellʳ (heldʷ wh) eb refl wh′ refl) = paid-resume wh eb wh′
  paid-well {t = owing hd s e} {td = []}    (wellʳ (heldʷ wh) eb refl wh′ refl) = paid-owing wh eb wh′
  paid-well                     {td = _ ∷ _} (wellʳ (heldʷ wh) eb refl wh′ refl) = ⊥-elim (owed-once wh)

  -- The top level's burst over: the level returns, or the root's turn
  -- comes round.
  leave-well : ∀ {lo h} {hp : Heapᴹ h} {p w x es} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm bu lg mk}
             → WellHeld lo p k (x ∷ es) [] → map entry bu ≡ es → WellHeap lo hp
             → StepBy WellRun lo (silent (feed (mach ⟨ hp , p , held σ k ⟩ cl tm bu [] lg false mk) go))
  leave-well (rootʰ (playingʳ _))      eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl)
  leave-well (rootʰ overʳ)             eb wh = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ idleʳ)) eb refl wh refl)
  leave-well (coldʰ st ws (playingᶜ _)) eb wh = returns-run st ws eb wh
  leave-well (coldʰ st ws overᶜ)        eb wh = returns-run st ws eb wh

  -- A frame played on: its value delivered at its index, a stall
  -- skipped, or the burst closed and the rest scheduled.
  play-well : ∀ {lo h} {hp : Heapᴹ h} {p w es c i} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm lg mk} (b : Playing h) {bu}
            → Playing.under′ b ≡ c → Playing.index b ≡ i → WellHeld lo p k (playing c i ∷ es) [] → map entry bu ≡ es → WellHeap lo hp
            → StepBy WellRun lo (silent (playᴹ (mach ⟨ hp , p , held σ k ⟩ cl tm (just b ∷ bu) [] lg false mk) b bu))
  play-well b refl refl wh eb hw with Playing.frame b
  play-well {lo} {p = p} {c = c} {i} b refl refl (rootʰ (playingʳ le)) eb hw | emit a k′ =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (proj₁ (look-well hw (Playing.sink b)) a (c ++ [ ix i ]) lo le)
                                     (fedʷ p λ lo′ st → rootʰ (playingʳ (settled-next c (<ᵖ-ix i) (≤ᵖ-trans le (inj₂ (<ᵖ-part c [] [] (<ᵖ-ix i)))) st))))
                               (cong (_ ∷_) eb) refl hw refl)
  play-well {lo} {p = p} {i = i} b refl refl (coldʰ st ws (playingᶜ le)) eb hw | emit a k′ =
    silentʷ (inj₁ refl) (wellʳ (runʷ settled-refl (proj₁ (look-well hw (Playing.sink b)) a (p ++ [ ix i ]) lo le)
                                     (fedʷ p λ lo′ st′ → coldʰ (settled-trans st (settled-up ([ ix i ] , refl) st′)) ws
                                                               (playingᶜ (settled-next p (<ᵖ-ix i) (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] (<ᵖ-ix i)))) st′))))
                               (cong (_ ∷_) eb) refl hw refl)
  play-well {c = c} {i} b refl refl (rootʰ (playingʳ le)) eb hw | stall k′ =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ (playingʳ (≤ᵖ-trans le (inj₂ (<ᵖ-part c [] [] (<ᵖ-ix i))))))) (cong (_ ∷_) eb) refl hw refl)
  play-well {p = p} {i = i} b refl refl (coldʰ st ws (playingᶜ le)) eb hw | stall k′ =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws (playingᶜ (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] (<ᵖ-ix i))))))) (cong (_ ∷_) eb) refl hw refl)
  play-well b refl refl wh eb hw | close k′ with From∞.force k′
  play-well {c = c} b refl refl (rootʰ (playingʳ le)) eb hw | close k′ | done =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ (owingʳ (≤ᵖ-trans le (inj₂ (<ᵖ-part c [] [] refl)))))) (cong (_ ∷_) eb) refl hw refl)
  play-well {p = p} b refl refl (coldʰ st ws (playingᶜ le)) eb hw | close k′ | done =
    silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws (owingᶜ (≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] refl)))))) (cong (_ ∷_) eb) refl hw refl)
  play-well b refl refl (rootʰ (playingʳ le)) eb hw | close k′ | quiet = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ resumeʳ)) eb refl hw refl)
  play-well b refl refl (coldʰ st ws (playingᶜ le)) eb hw | close k′ | quiet = silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws resumeᶜ)) eb refl hw refl)
  play-well b refl refl (rootʰ (playingʳ le)) eb hw | close k′ | at _ _ _ = silentʷ (inj₁ refl) (wellʳ (heldʷ (rootʰ resumeʳ)) eb refl hw refl)
  play-well b refl refl (coldʰ st ws (playingᶜ le)) eb hw | close k′ | at _ _ _ = silentʷ (inj₁ refl) (wellʳ (heldʷ (coldʰ st ws resumeᶜ)) eb refl hw refl)

  playing-inj : ∀ {c c′ i i′} → playing c i ≡ playing c′ i′ → c ≡ c′ × i ≡ i′
  playing-inj refl = refl , refl

  -- A playing burst: spent, it is over; polled, it plays; else its sink
  -- is asked whether it is closed, which is `Still`.
  turned-playing : ∀ {lo h} {hp : Heapᴹ h} {p w es c i} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm lg mk} (b : Playing h) {bu}
                 → Playing.under′ b ≡ c → Playing.index b ≡ i → WellHeld lo p k (playing c i ∷ es) [] → map entry bu ≡ es → WellHeap lo hp
                 → StepBy WellRun lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm (just b ∷ bu) [] lg false mk))
  turned-playing {hp = hp} b ec ei wh eb hw with spent? hp (Playing.handle b)
  ... | true  = leave-well wh eb hw
  ... | false with Playing.polled b
  ...   | true  = play-well b ec ei wh eb hw
  ...   | false rewrite ec | ei = silentʷ (inj₁ refl) (wellʳ (stillʷ (proj₂ (proj₂ (look-well hw (Playing.sink b)))) (toldʷ wh)) (cong (_ ∷_) eb) refl hw refl)

  turned-well : ∀ {lo h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {k : Stack w ⊤} {cl tm b bu lg en mk}
              → WellRun lo (mach ⟨ hp , p , held σ k ⟩ cl tm (b ∷ bu) [] lg en mk) → StepBy WellRun lo (step (mach ⟨ hp , p , held σ k ⟩ cl tm (b ∷ bu) [] lg en mk))
  turned-well {b = nothing} (wellʳ (heldʷ wh@(rootʰ overʳ)) eb refl hw refl)        = leave-well wh (∷-tail eb) hw
  turned-well {b = nothing} (wellʳ (heldʷ wh@(coldʰ _ _ overᶜ)) eb refl hw refl)    = leave-well wh (∷-tail eb) hw
  turned-well {b = nothing} (wellʳ (heldʷ (rootʰ (playingʳ _))) eb refl hw refl)     with ∷-head eb
  ... | ()
  turned-well {b = nothing} (wellʳ (heldʷ (coldʰ _ _ (playingᶜ _))) eb refl hw refl) with ∷-head eb
  ... | ()
  turned-well {b = nothing} (wellʳ (heldʷ (rootʰ idleʳ)) () refl hw refl)
  turned-well {b = just b} (wellʳ (heldʷ wh@(rootʰ (playingʳ _))) eb refl hw refl) =
    turned-playing b (proj₁ (playing-inj (∷-head eb))) (proj₂ (playing-inj (∷-head eb))) wh (∷-tail eb) hw
  turned-well {b = just b} (wellʳ (heldʷ wh@(coldʰ _ _ (playingᶜ _))) eb refl hw refl) =
    turned-playing b (proj₁ (playing-inj (∷-head eb))) (proj₂ (playing-inj (∷-head eb))) wh (∷-tail eb) hw
  turned-well {b = just b} (wellʳ (heldʷ (rootʰ overʳ)) eb refl hw refl) with ∷-head eb
  ... | ()
  turned-well {b = just b} (wellʳ (heldʷ (coldʰ _ _ overᶜ)) eb refl hw refl) with ∷-head eb
  ... | ()
  turned-well {b = just b} (wellʳ (heldʷ (rootʰ idleʳ)) () refl hw refl)

  -- THE TREE WALK: a step that is not the loop's turn runs the
  -- computation, or plays the top level's burst, at the configuration's
  -- position; the protocol's indices carry the last delivery, so the run
  -- stays well and a value shown is no earlier than the last.
  walk-tree : ∀ {lo m} → WellMach lo m → idle m ≡ false → StepBy WellRun lo (step m)
  walk-tree {lo} {m = mach ⟨ hp , p , asking (note a) k σ s ⟩ cl tm bu td lg en mk} w b with WellRun.fresh (WellMach.going w)
  ... | refl with WellRun.ctl (WellMach.going w)
  ...   | notingʷ le st wk ws = valueʷ le (record { ctl = runʷ (settled-at st le) wk ws ; entries = WellRun.entries (WellMach.going w)
                                                  ; dues = WellRun.dues (WellMach.going w) ; heap = heap-up {hp = hp} le (WellRun.heap (WellMach.going w)) ; fresh = refl })
  walk-tree {m = mach ⟨ hp , p , asking fin k σ s ⟩ cl tm bu td lg en mk} w b with WellRun.fresh (WellMach.going w)
  ... | refl with WellRun.ctl (WellMach.going w)
  ...   | finningʷ le = completeʷ le
  walk-tree {m = mach ⟨ hp , p , run a σ k ⟩ cl tm bu td lg en mk} w b = runs-well (WellMach.going w)
  walk-tree {m = mach ⟨ hp , p , ret x σ k ⟩ cl tm bu td lg en mk} w b = returns-well (WellMach.going w)
  walk-tree {m = mach ⟨ hp , p , held σ k ⟩ cl tm bu (t ∷ td) lg en mk} w b = paid-well (WellMach.going w)
  walk-tree {m = mach ⟨ hp , p , held σ k ⟩ cl tm (x ∷ bu) [] lg en mk} w b = turned-well (WellMach.going w)
  walk-tree {m = mach ⟨ hp , p , held σ k ⟩ cl tm [] [] lg en mk} w ()

  postulate
    -- THE TIMERS: a step that is not the loop's turn shows values only
    -- under the playing burst's cascade, and moves the last on only past
    -- a join in it, so every timer queued stays past them; a timer it
    -- sets is queued at its due tick after every timer set earlier on
    -- that tick.
    walk-timers : ∀ {lo m} (w : WellMach lo m) (b : idle m ≡ false) → QueueAt (walk-tree w b)

    -- THE LOOP'S TURN: the earliest timer popped, its frame played from
    -- its cascade, which every other timer is past.
    turn : ∀ {lo m} → WellMach lo m → idle m ≡ true → WellStep lo (step m)

  walk : ∀ {lo m} → WellMach lo m → idle m ≡ false → WellStep lo (step m)
  walk w b = joinʷ (walk-tree w b) (walk-timers w b)

  -- The machine's fundamental lemma: a well configuration's step keeps
  -- it well, and a value it shows is no earlier than the last.
  preserve : ∀ {lo m} → WellMach lo m → WellStep lo (step m)
  preserve {m = m} w with idle m in eq
  ... | true  = turn w eq
  ... | false = walk w eq

  -- The recorder is well: a value or completion at no earlier a position.
  recorder-well : WellObs recorder
  recorder-well = (λ a q lo le → noteʷ le doneʷ) , (λ q lo le → finʷ le) , doneˢ

  -- The run begins well: the program compiled at the root, the recorder
  -- its observer, nothing on the heap, queued or playing.
  begin-well : (o : PureObs [] R) → WellMach root (begin o)
  begin-well o = record
    { going = record { ctl     = runʷ (inj₁ refl , inj₁ refl) (compile-well o [] (lift tt) same recorder _ root root (inj₁ refl) recorder-well (λ σ sub _ p lo → doneʷ)) bottomʷ
                     ; entries = refl ; dues = refl ; heap = heapʷ λ () ; fresh = refl }
    ; queue = record { timers = [] ; queued = AllPairs.[] } }

  mutual
    rising : ∀ {lo m} → WellMach lo m → Rising lo m
    rising w .Rising.rises = risingˢ (preserve w)

    risingˢ : ∀ {lo s} → WellStep lo s → RisingStep lo s
    risingˢ (silentʷ le w)  = silentʳ le (rising w)
    risingˢ (valueʷ le w)   = valueʳ le (rising w)
    risingˢ (completeʷ le)  = completeʳ le
    risingˢ drainedʷ        = drainedʳ

  -- SORTEDNESS: the program's run rises from the root.
  sorted : (o : PureObs [] R) → Rising root (begin o)
  sorted o = rising (begin-well o)
