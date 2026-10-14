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
-- configuration, and nothing is related step by step inside a cascade.
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
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; Σ)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc)
open import Level using (lower)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.MonotonicList using (Events; Events∞; out; skip; end; hush; tick; observe; root)
open import denotation.Order using (_⊑_; Chain)
open import denotation.Unfold using (⟦_⟧)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.Placed using (Placed; cut; ends; quiets; sends; skips; items; Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; frames-cut)
open import operation.PureObservable using (PureObs; module Pure)
open import Realize using (module Realizing)

module Sim (R : Set) where
  open Machine R using (Mach; ⟨_,_⟩; turn; silent; shown; Trace; Trace∞; tau; out; end; idle; trace; begin; Read; read; noted; reading; prefix)
  open Realizing R using (Calm; calm; Holding; dead; dry-hush; pop-dead)
  open Pure R using (State; Timer; get; cascade)
  open Pure R using (cutOff; frames)
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
      out~  : ∀ {p a l r} → Seg∞ l r → Seg b (out (tick p) p a l) (out p a r)
      tau~  : ∀ {t p l r} → Seg∞ l r → Seg b (tau t l) (skip p r)
      tauˡ  : ∀ {t l e} → Seg b (Trace∞.force l) e → Seg b (tau t l) e
      skipʳ : ∀ {m p r} → Seg b m (Events∞.force r) → Seg b m (skip p r)
      end~  : ∀ {p} → Seg b (end p) (end p)
      idle~ : Seg b idle hush
      calm~ : ∀ {m e} → Calm m e → Below b m → Seg b (trace m) e

    record Seg∞ (l : Trace∞) (r : Events∞ R) : Set₁ where
      coinductive
      field force : Seg nothing (Trace∞.force l) (Events∞.force r)

  open Seg∞

  postulate
    -- The subscribe burst, up to the first calm point.
    start-seg : (o : PureObs [] R) → Seg nothing (trace (begin o)) (observe (⟦ o ⟧ []) root)

    -- A live timer popped from a calm point: its frame shows at least
    -- one step on each side before the loop is reached again, so the
    -- segment passes a guard first, whatever bound it is under.
    --
    -- RECOVERY: `git show a2e0bb8b:agda-impl/Realize.agda` restores
    --   `Spot`, `setAt`, `obsAt` and `Playing` — one cold picked out of the
    --   witness mid-frame, and the observer its slot holds — over the fuel
    --   engine's witness.
    fire : ∀ {h c} {st : State h} {tm ts} → Holding c st → State.timers st ≡ tm ∷ ts
         → lower (get (State.heap st) (Timer.handle tm)) ≡ false → ∀ {b} → Seg b (trace ⟨ st , turn ⟩) (U.unfold c)

  if-true : ∀ {ℓ ℓ′} {X : Set ℓ} {x : Bool} {a b : X} (P : X → Set ℓ′) → x ≡ true → P a → P (if x then a else b)
  if-true P refl p = p

  -- One turn of the loop from a calm point: it shows a step on each side,
  -- or returns to the loop having popped a dead timer.
  turn-seg : ∀ {m e} → Calm m e → Seg (just (dead m)) (trace m) e
  turn-seg (calm {st = st} h) = turning st h
    where
      turning : ∀ {h c} (st : State h) → Holding c st → Seg (just (dead ⟨ st , turn ⟩)) (trace ⟨ st , turn ⟩) (U.unfold c)
      turning record { timers = [] } h =
        subst (λ s → Seg _ idle (U.shown s)) (sym (dry-hush h refl)) idle~
      turning record { heap = H ; timers = tm ∷ ts } h with lower (get H (Timer.handle tm)) in sp
      ... | true  = tauˡ (if-true (λ m → Seg _ (shown (silent m)) _) sp (tauˡ (tauˡ (calm~ (calm (pop-dead h refl sp)) ≤-refl))))
      ... | false = fire h refl sp

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
    glue (acc rs) (calm~ c lt) = glue (rs lt) (turn-seg c)

    glue∞ : ∀ {l r} → Seg∞ l r → l ~∞ r
    force (glue∞ s) = glueⁿ (force s)

    glueⁿ : ∀ {l e} → Seg nothing l e → l ~ e
    glueⁿ (out~ s)             = out~ (glue∞ s)
    glueⁿ (tau~ s)             = tau~ (glue∞ s)
    glueⁿ (tauˡ s)             = tauˡ (glueⁿ s)
    glueⁿ (skipʳ s)            = skipʳ (glueⁿ s)
    glueⁿ end~                 = end~
    glueⁿ idle~                = idle~
    glueⁿ (calm~ {m} c _)      = glue (<-wellFounded (dead m)) (turn-seg c)

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
