{-# OPTIONS --guardedness #-}

-- THE SIMULATION.  The machine's trace and the events the root is shown
-- are the same run up to silent steps: each value the machine shows is
-- the events' next `out`, at its position and on that position's tick;
-- its completion their `end`; its queue run dry their `hush`.  A silent
-- step on either side passes alone, finitely often; one on each side
-- passes together, as often as they come, so a burst stalling forever
-- in both is related.  A machine working forever where the events
-- `hush` is not.
--
-- The relation is built by guarded corecursion up to CALM points
-- (`Realize`): a segment of the run shows at least one step on each side,
-- or reaches the loop again with fewer dead timers, related to what the
-- meaning has left.  So the run is cut where the machine's state is a
-- configuration — at its loop, or between two steps of a frame — and
-- nothing is related step by step inside a delivery.
--
-- Both halves of adequacy are read off the one relation.  Every prefix
-- of the trace is `Placed` against the events, so shows nothing they do
-- not; every item the events show is within some prefix.  The prefixes
-- are a chain with no clock condition: a longer one extends the record
-- of a cut one.
module Simulation where

open import Data.List using ([]; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _∸_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; Σ; proj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (Acc; acc)
open import Level using (lift; lower)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.MonotonicList using (Events; Events∞; Frame; Frame∞; From∞; Pos; ix; last; emit; stall; close; done; quiet; at; out; skip; end; hush; tick; observe; root)
open import denotation.Order using (_⊑_; Chain)
open import denotation.Unfold using (⟦_⟧)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.Placed using (Placed; cut; ends; quiets; sends; skips; items; Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; frames-cut)
open import operation.PureObservable using (PureObs; Sink; same; module Pure)
open import Realize using (module Realizing)
open import Focus using (module Focusing)

module Sim (R : Set) where
  open Machine R using (Mach; ⟨_,_⟩; turn; burst; run; ret; loop; push; asked; sent; Stack; step; cbs; play; silent; shown; Trace; Trace∞; tau; out; end; idle; trace; begin; Read; read; noted; reading; prefix)
  open Realizing R using (Calm; calm; bursting; Holding; firing; Sub; Phase; waiting; playing; nodeOf; spot-of; spot-step; forget; module At; dead; dry-hush; pop-dead; pop-live)
  open Pure R using (State; Timer; Callbacks; get; put; insert; cascade)
  open Pure R using (cutOff; frames)
  open Focusing R using (module On; clear)
  open Read

  ------------------------------------------------------------------------
  -- The relation

  mutual
    infix 4 _~_ _~∞_
    data _~_ : Trace → Events R → Set where
      out~  : ∀ {p a l r} → l ~∞ r → out (tick p) p a l ~ out p a r
      tau~  : ∀ {t p l r} → l ~∞ r → tau t l ~ skip p r
      tauˡ  : ∀ {t l e} → Trace∞.force l ~ e → tau t l ~ e
      skipʳ : ∀ {m p r} → m ~ Events∞.force r → m ~ skip p r
      end~  : ∀ {p} → end p ~ end p
      idle~ : idle ~ hush

    record _~∞_ (l : Trace∞) (r : Events∞ R) : Set where
      coinductive
      field force : Trace∞.force l ~ Events∞.force r

  open _~∞_

  ------------------------------------------------------------------------
  -- Up to calm points

  -- A calm point inside a segment no guard has passed must have fewer
  -- dead timers than where the segment began.
  Below : Maybe ℕ → Mach → Set
  Below (just k) m = dead m < k
  Below nothing  m = ⊤

  -- The relation's constructors, and a calm point to resume from.
  mutual
    data Seg (b : Maybe ℕ) : Trace → Events R → Set₁ where
      out~  : ∀ {p a l r} → Seg∞ (Trace∞.force l) (Events∞.force r) → Seg b (out (tick p) p a l) (out p a r)
      tau~  : ∀ {t p l r} → Seg∞ (Trace∞.force l) (Events∞.force r) → Seg b (tau t l) (skip p r)
      tauˡ  : ∀ {t l e} → Seg b (Trace∞.force l) e → Seg b (tau t l) e
      skipʳ : ∀ {m p r} → Seg b m (Events∞.force r) → Seg b m (skip p r)
      end~  : ∀ {p} → Seg b (end p) (end p)
      idle~ : Seg b idle hush
      calm~ : ∀ {m e} → Calm m e → Below b m → Seg b (trace m) e

    record Seg∞ (l : Trace) (r : Events R) : Set₁ where
      coinductive
      field force : Seg nothing l r

  open Seg∞

  -- The machine passing silent steps only.
  infix 4 _⇒_
  data _⇒_ : Mach → Mach → Set₁ where
    here⇒ : ∀ {m} → m ⇒ m
    step⇒ : ∀ {m m₁ m′} → step m ≡ silent m₁ → m₁ ⇒ m′ → m ⇒ m′

  taus : ∀ {b m m′ e} → m ⇒ m′ → Seg b (trace m′) e → Seg b (trace m) e
  taus here⇒        s = s
  taus (step⇒ eq r) s = subst (λ x → Seg _ (shown x) _) (sym eq) (tauˡ (taus r s))

  -- The meaning passing silent steps only.
  data Skips : U.Node R → U.Node R → Set₁ where
    noneˢ : ∀ {c} → Skips c c
    skipˢ : ∀ {c p c₁ c′} → U.step c ≡ U.skipˢ p c₁ → Skips c₁ c′ → Skips c c′

  skipping : ∀ {b m c c′} → Skips c c′ → Seg b m (U.unfold c′) → Seg b m (U.unfold c)
  skipping noneˢ         s = s
  skipping (skipˢ eq sk) s = subst (λ x → Seg _ _ (U.shown x)) (sym eq) (skipʳ (skipping sk s))

  -- At least one silent step of the meaning, to a configuration where `P`.
  record Passes (c : U.Node R) (P : U.Node R → Set₁) : Set₁ where
    constructor passes
    field
      {c₁ c′} : U.Node R
      {p}     : Pos
      first   : U.step c ≡ U.skipˢ p c₁
      rest    : Skips c₁ c′
      holds   : P c′

  -- The witness at a burst point, its firing cold's phase moved.
  moved : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
        → Holding (firing s hd τ r i b ∷ []) c st → Phase A → Sub h [] R
  moved {st = st} H ph = At.stepAt (State.heap st) (spot-of (Holding.tree H) (Holding.firing≡ H)) ph [] []

  -- … and every joiner's copy caught up with its source.
  settled : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
          → Holding (firing s hd τ r i b ∷ []) c st → Phase A → Sub h [] R
  settled {st = st} H ph = At.refresh (State.heap st) (moved H ph) [] [] []

  -- What is running is `c′`, by the settled witness up to the sources the
  -- meaning holds: a joiner's step drops an ending source in every
  -- connect above it.
  Settles : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
          → Holding (firing s hd τ r i b ∷ []) c st → Phase A → U.Node R → Set₁
  Settles {h} {st = st} H ph c′ = Σ (Sub h [] R) λ t → forget t ≡ forget (settled H ph) × At.part (State.heap st) t [] [] ≡ just c′

  mapᴾ : ∀ {c} {P Q : U.Node R → Set₁} → (∀ {c′} → P c′ → Q c′) → Passes c P → Passes c Q
  mapᴾ f (passes e sk p) = passes e sk (f p)

  postulate
    -- The subscribe burst, up to the first calm point.
    start-seg : (o : PureObs [] R) → Seg nothing (trace (begin o)) (observe (⟦ o ⟧ []) root)

    -- A firing cold's subscriber is read open, and reading it moves nothing.
    closed-read : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u} {K : Stack h Bool}
                → Holding (firing s hd τ r i b ∷ []) c st → lower (get (State.heap st) hd) ≡ false
                → ⟨ st , run (Callbacks.isClosed (cbs st s)) same K ⟩ ⇒ ⟨ st , ret false same K ⟩

    -- Then each joiner's copy of a source the step moved takes the same
    -- step, shown below its join point (`past`), silently: sources before
    -- their joiners, and joiners in the order they joined.
    catch-up : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
             → (H : Holding (firing s hd τ r i b ∷ []) c st) → lower (get (State.heap st) hd) ≡ false
             → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
             → ∀ {c₁} → At.part (State.heap st) (moved H ph) [] [] ≡ just c₁
             → Σ (U.Node R) λ c′ → Skips c₁ c′ × Settles H ph c′

    -- The witness with the cold's phase moved by a silent step holds what
    -- is running: one step on, quiet, or its next frame queued.
    reheld-stall : ∀ {h c c′} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : Frame∞ A u}
                 → (H : Holding (firing s hd τ r i (stall k′) ∷ []) c st)
                 → Settles H (playing τ r (suc i) (Frame∞.force k′)) c′
                 → Holding (firing s hd τ r (suc i) (Frame∞.force k′) ∷ []) c′ st
    reheld-quiet : ∀ {h c c′} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)}
                 → (H : Holding (firing s hd τ r i (close k′) ∷ []) c st)
                 → Settles H (waiting {u = suc u} τ (r ++ [ last ]) quiet) c′
                 → Holding [] c′ st
    reheld-later : ∀ {h c c′} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)} {t} {le : suc u ≤ t} {b : Frame A t}
                 → (H : Holding (firing s hd τ r i (close k′) ∷ []) c st)
                 → Settles H (waiting τ (r ++ [ last ]) (at t le b)) c′
                 → Holding [] c′ (record st { timers = insert (record { due = State.clock st + (t ∸ u) ; sink = s ; handle = hd
                                                                      ; at′ = t ; from = r ++ [ last ] ; frame = b })
                                                            (State.timers st) })

    -- An emit delivered down the observer chain the cold's slot holds.
    --
    -- RECOVERY: `git show a2e0bb8b:agda-impl/Realize.agda` restores `obsAt`
    --   — the observer a spot's slot holds — over the fuel engine's witness.
    emit-seg : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {a : A} {k′ : Frame∞ A u}
             → Holding (firing s hd τ r i (emit a k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false
             → ∀ {bd} → Seg bd (shown (silent ⟨ record st { pos = r ++ [ ix i ] }
                                              , run (Callbacks.onNext (cbs st s) a) same (push (sent s hd u r (suc i) (Frame∞.force k′)) same loop) ⟩))
                                (U.unfold c)

    -- A frame closing on its timeline's end: the cold spent, its
    -- completion delivered.
    done-seg : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)}
             → Holding (firing s hd τ r i (close k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false → From∞.force k′ ≡ done
             → ∀ {bd} → Seg bd (shown (silent ⟨ record st { heap = put (State.heap st) hd (lift true) ; pos = r ++ [ last ] }
                                              , run (Callbacks.onComplete (cbs st s)) same loop ⟩))
                                (U.unfold c)

  -- A live firing cold's step silent at its own position: the meaning's
  -- next step is it, lifted through the cold's context, to the witness
  -- with the cold's phase moved, every connect above it stepped, and
  -- every joiner's copy where it was.
  cold-skip : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
            → (H : Holding (firing s hd τ r i b ∷ []) c st) → lower (get (State.heap st) hd) ≡ false
            → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
            → Σ Pos λ p → Σ (U.Node R) λ c₁ → U.step c ≡ U.skipˢ p c₁ × At.part (State.heap st) (moved H ph) [] [] ≡ just c₁
  cold-skip {st = st} H lv eq with On.lift-skip (State.heap st) (spot-of (Holding.tree H) (Holding.firing≡ H)) {E = []} {ρ = []} lv (Holding.gated H)
                                                 (clear H lv eq) (trans (spot-step (Holding.tree H) (Holding.firing≡ H)) eq)
  ... | n , c₁ , open≡ , first , moved≡ = _ , c₁ , subst (λ x → U.step x ≡ _) (just-injective (trans (sym open≡) (Holding.open≡ H))) first , moved≡

  -- A live firing cold's step silent at its own position: the meaning's
  -- next steps are it, then its joiners' copies catching up.
  focus-skip : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
             → (H : Holding (firing s hd τ r i b ∷ []) c st) → lower (get (State.heap st) hd) ≡ false
             → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
             → Passes c (Settles H ph)
  focus-skip H lv eq with cold-skip H lv eq
  ... | _ , _ , first , moved≡ with catch-up H lv eq moved≡
  ... | _ , rest , settled≡ = passes first rest settled≡

  -- A stall: the cold's step, silent at the root, and the next one stands.
  stall-step : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : Frame∞ A u}
             → Holding (firing s hd τ r i (stall k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false
             → Passes c λ c′ → Holding (firing s hd τ r (suc i) (Frame∞.force k′) ∷ []) c′ st
  stall-step H lv = mapᴾ (reheld-stall H) (focus-skip H lv refl)

  -- A frame closing on a timeline gone quiet, or on a later frame, its
  -- timer queued: silent at the root, and the loop is calm again.
  quiet-step : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)}
             → Holding (firing s hd τ r i (close k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false → From∞.force k′ ≡ quiet
             → Passes c λ c′ → Holding [] c′ st
  quiet-step {u = u} {τ} {r = r} {i} H lv fk =
    mapᴾ (reheld-quiet H) (focus-skip H lv {ph = waiting {u = suc u} τ (r ++ [ last ]) quiet}
                                       (cong (λ m → U.skipˢ (r ++ [ ix i ]) (U.framesᶜ τ (r ++ [ last ]) m)) fk))

  later-step : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {k′ : From∞ A (suc u)} {t} {le : suc u ≤ t} {b : Frame A t}
             → Holding (firing s hd τ r i (close k′) ∷ []) c st → lower (get (State.heap st) hd) ≡ false → From∞.force k′ ≡ at t le b
             → Passes c λ c′ → Holding [] c′ (record st { timers = insert (record { due = State.clock st + (t ∸ u) ; sink = s ; handle = hd
                                                                                    ; at′ = t ; from = r ++ [ last ] ; frame = b })
                                                                          (State.timers st) })
  later-step {τ = τ} {r = r} {i} {t = t} {le} {b} H lv fk =
    mapᴾ (reheld-later H) (focus-skip H lv {ph = waiting τ (r ++ [ last ]) (at t le b)}
                                       (cong (λ m → U.skipˢ (r ++ [ ix i ]) (U.framesᶜ τ (r ++ [ last ]) m)) fk))

  if-true : ∀ {ℓ ℓ′} {X : Set ℓ} {x : Bool} {a b : X} (P : X → Set ℓ′) → x ≡ true → P a → P (if x then a else b)
  if-true P refl p = p

  if-false : ∀ {ℓ ℓ′} {X : Set ℓ} {x : Bool} {a b : X} (P : X → Set ℓ′) → x ≡ false → P b → P (if x then a else b)
  if-false P refl p = p

  -- A segment resumed after a guard.
  later : ∀ {m e} → Seg nothing m e → Seg∞ m e
  force (later s) = s

  -- A frame's step silent at the root, the run resuming at a calm point.
  passing : ∀ {c m bd} {P : U.Node R → Set₁} → Passes c P → (∀ {c′} → P c′ → Seg nothing (trace m) (U.unfold c′))
          → Seg bd (shown (silent m)) (U.unfold c)
  passing (passes eq sk p) k = subst (λ x → Seg _ _ (U.shown x)) (sym eq) (tau~ (later (skipping sk (k p))))

  -- A live cold's frame, burst from the loop, a step at a time: it shows
  -- at least one step on each side before a calm point, so the segment
  -- passes a guard first, whatever bound it is under.
  played : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} (b : Frame A u)
         → Holding (firing s hd τ r i b ∷ []) c st → lower (get (State.heap st) hd) ≡ false
         → ∀ {bd} → Seg bd (shown (silent (play st s hd u r i b same loop))) (U.unfold c)
  played (emit a k′) h lv = if-false (λ m → Seg _ (shown (silent m)) _) lv (emit-seg h lv)
  played (stall k′)  h lv = passing (stall-step h lv) λ h′ → calm~ (bursting h′ lv) tt
  played (close k′)  h lv with From∞.force k′ in fk
  ... | done      = if-false (λ m → Seg _ (shown (silent m)) _) lv (done-seg h lv fk)
  ... | quiet     = passing (quiet-step h lv fk) λ h′ → tauˡ (calm~ (calm h′) tt)
  ... | at t le b = passing (later-step h lv fk) λ h′ → tauˡ (calm~ (calm h′) tt)

  burst-seg : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
            → Holding (firing s hd τ r i b ∷ []) c st → lower (get (State.heap st) hd) ≡ false
            → ∀ {bd} → Seg bd (trace ⟨ st , burst s hd u r i b same loop ⟩) (U.unfold c)
  burst-seg {b = b} h lv = tauˡ (if-false (λ m → Seg _ (trace m) _) lv (taus (closed-read h lv) (played b h lv)))

  -- From a calm point: a turn of the loop shows a step on each side, or
  -- returns to the loop having popped a dead timer; a burst shows a step
  -- on each side.
  resume : ∀ {m e} → Calm m e → Seg (just (dead m)) (trace m) e
  resume (calm {st = st} h) = turning st h
    where
      turning : ∀ {h c} (st : State h) → Holding [] c st → Seg (just (dead ⟨ st , turn ⟩)) (trace ⟨ st , turn ⟩) (U.unfold c)
      turning record { timers = [] } h =
        subst (λ s → Seg _ idle (U.shown s)) (sym (dry-hush h refl)) idle~
      turning record { heap = H ; timers = tm ∷ ts } h with lower (get H (Timer.handle tm)) in sp
      ... | true  = tauˡ (if-true (λ m → Seg _ (shown (silent m)) _) sp (tauˡ (tauˡ (calm~ (calm (pop-dead h refl sp)) ≤-refl))))
      ... | false = tauˡ (burst-seg (proj₂ (pop-live h refl sp)) sp)
  resume (bursting h lv) = burst-seg h lv

  -- Segments glued at their calm points: each turn is a segment, and a run
  -- of unguarded ones pops a dead timer each, so ends.
  mutual
    glue : ∀ {k l e} → Acc _<_ k → Seg (just k) l e → l ~ e
    glue a (out~ s)            = out~ (glue∞ s)
    glue a (tau~ s)            = tau~ (glue∞ s)
    glue a (tauˡ s)            = tauˡ (glue a s)
    glue a (skipʳ s)           = skipʳ (glue a s)
    glue a end~                = end~
    glue a idle~               = idle~
    glue (acc rs) (calm~ c lt) = glue (rs lt) (resume c)

    glue∞ : ∀ {l r} → Seg∞ (Trace∞.force l) (Events∞.force r) → l ~∞ r
    force (glue∞ s) = glueⁿ (force s)

    glueⁿ : ∀ {l e} → Seg nothing l e → l ~ e
    glueⁿ (out~ s)             = out~ (glue∞ s)
    glueⁿ (tau~ s)             = tau~ (glue∞ s)
    glueⁿ (tauˡ s)             = tauˡ (glueⁿ s)
    glueⁿ (skipʳ s)            = skipʳ (glueⁿ s)
    glueⁿ end~                 = end~
    glueⁿ idle~                = idle~
    glueⁿ (calm~ {m} c _)      = glue (<-wellFounded (dead m)) (resume c)

  -- The program's run is what the root is shown.
  sim : (o : PureObs [] R) → trace (begin o) ~ observe (⟦ o ⟧ []) root
  sim o = glueⁿ (start-seg o)

  ------------------------------------------------------------------------
  -- Below: every prefix placed

  placed : ∀ n c {l e} → l ~ e → Placed (ending (reading n c l)) (marks (reading n c l)) (log (reading n c l)) e
  placed zero    c s         = cut
  placed (suc n) c (out~ s)  = sends (placed n _ (force s))
  placed (suc n) c (tau~ s)  = skips (placed n _ (force s))
  placed (suc n) c (tauˡ s)  = placed n _ s
  placed (suc n) c (skipʳ s) = skips (placed (suc n) c s)
  placed (suc n) c end~      = ends
  placed (suc n) c idle~     = quiets

  ------------------------------------------------------------------------
  -- Above: every item within a prefix

  got : ∀ {e k l} c → Ahead e k → l ~ e → Σ ℕ λ n → k ≤ length (items (log (reading n c l)) (ending (reading n c l)))
  got c none s = 0 , z≤n
  got c a (tauˡ s) with got _ a s
  ... | n , le = suc n , le
  got c (outᵃ a) (out~ s) with got _ a (force s)
  ... | n , le = suc n , s≤s le
  got c (skipᵃ a) (tau~ s) with got _ a (force s)
  ... | n , le = suc n , le
  got c (skipᵃ a) (skipʳ s) = got c a s
  got c endᵃ end~ = 1 , ≤-refl
  got c hushᵃ idle~ = 1 , ≤-refl

  ------------------------------------------------------------------------
  -- The prefixes, a chain

  -- A longer prefix is the same, or extends the record of a cut one.
  data Grows : Read → Read → Set where
    stays : ∀ {r} → Grows r r
    cuts  : ∀ {ms xs c ms′ e′} ys → Grows (read ms xs (cutOff c)) (read ms′ (xs ++ ys) e′)

  private
    noted-grows : ∀ {p x r r′} → Grows r r′ → Grows (noted p x r) (noted p x r′)
    noted-grows stays     = stays
    noted-grows (cuts ys) = cuts ys

  grows : ∀ n c l → Grows (reading n c l) (reading (suc n) c l)
  grows zero    c (tau t k)     = cuts []
  grows zero    c (out t p a k) = cuts [ (t , a) ]
  grows zero    c (end p)       = cuts []
  grows zero    c idle          = cuts []
  grows (suc n) c (tau t k)     = grows n t (Trace∞.force k)
  grows (suc n) c (out t p a k) = noted-grows (grows n t (Trace∞.force k))
  grows (suc n) c (end p)       = stays
  grows (suc n) c idle          = stays

  grows-⊑ : ∀ {r r′} → Grows r r′ → frames (log r) (ending r) ⊑ frames (log r′) (ending r′)
  grows-⊑ stays s                                     = s
  grows-⊑ (cuts {xs = xs} {c = c} {e′ = e′} ys) = frames-cut xs ys c e′

  prefix-chain : (o : PureObs [] R) → Chain (λ n → prefix n o)
  prefix-chain o n = grows-⊑ (grows n 0 (trace (begin o)))
