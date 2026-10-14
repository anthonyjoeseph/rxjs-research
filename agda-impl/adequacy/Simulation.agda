{-# OPTIONS --guardedness --large-indices #-}

-- THE SIMULATION.  The machine's trace and the events the root is shown
-- are the same run up to silent steps: each value the machine shows is
-- the events' next `out`, at its position and on that position's tick;
-- its completion their `end`; its queue run dry their `hush`.  A silent
-- step on either side passes alone, finitely often; one on each side
-- passes together, as often as they come, so a burst stalling forever
-- in both is related.  A machine working forever where the events
-- `hush` is not.
--
-- Both halves of adequacy are read off the one relation.  Every prefix
-- of the trace is `Placed` against the events, so shows nothing they do
-- not; every item the events show is within some prefix.  The prefixes
-- are a chain with no clock condition: a longer one extends the record
-- of a cut one.
module adequacy.Simulation where

open import Data.List using ([]; _++_; [_]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; Σ)

open import denotation.MonotonicList using (Events; Events∞; out; skip; end; hush; tick; observe; root)
open import denotation.Order using (_⊑_; Chain)
open import denotation.Unfold using (⟦_⟧; Node; subscribe; unfold; shown; outˢ; skipˢ; endˢ; hushˢ) renaming (step to stepᵁ; Step to Stepᵁ)
open import adequacy.Carrier using (module Carrying)
open import operation.Machine using (module Machine)
open import operation.Placed using (Placed; cut; ends; quiets; sends; skips; items; Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; frames-cut)
open import operation.PureObservable using (PureObs; module Pure)

module Sim (R : Set) where
  open Machine R using (Trace; Trace∞; tau; out; end; idle; trace; begin; Read; read; noted; reading; prefix; Mach; Step; silent; value; complete; drained; step)
  open Machine R using () renaming (shown to shownᴹ)
  open Carrying R using (Carried)
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
  -- The corecursion

  -- The machine's next step against the meaning's: matched events and
  -- paired silent steps guarded, a side's lone silent step inductive, so
  -- each side passes finitely many alone.  `Rel` is where the
  -- corecursion re-enters.
  module _ {ℓ} (Rel : Mach → Node R → Set ℓ) where
    data Wait : Step → Stepᵁ R → Set ℓ where
      both  : ∀ {m c p} → Rel m c → Wait (silent m) (skipˢ p c)
      outs  : ∀ {m c p a} → Rel m c → Wait (value (tick p) p a m) (outˢ p a c)
      ends  : ∀ {p} → Wait (complete p) (endˢ p)
      idles : Wait drained hushˢ
      left  : ∀ {m s} → Wait (step m) s → Wait (silent m) s
      right : ∀ {t c p} → Wait t (stepᵁ c) → Wait t (skipˢ p c)

    module From (kept : ∀ {m c} → Rel m c → Wait (step m) (stepᵁ c)) where
      mutual
        sim-from : ∀ {m c} → Rel m c → trace m ~ unfold c
        sim-from r = go (kept r)

        go : ∀ {t s} → Wait t s → shownᴹ t ~ shown s
        go (both r)  = tau~ λ where .force → sim-from r
        go (outs r)  = out~ λ where .force → sim-from r
        go ends      = end~
        go idles     = idle~
        go (left w)  = tauˡ (go w)
        go (right w) = skipʳ (go w)

  postulate
    -- B KEPT, C FINITE: a carried state's next step, against its
    -- configuration's, passes each side alone finitely often before the
    -- two meet again carried, or end, or fall quiet together.
    --
    -- At a connect's feed the meaning's next shown event is the first
    -- owed joiner's, at `q ++ [ sub j ]`, only if every other live node
    -- reaches past it by silent steps; between the connect's own skip
    -- and that delivery lie only the lag steps of joiners subscribed
    -- mid-feed.  `Carried` holds nothing positional for nodes the agenda
    -- does not owe, so this step needs a field placing each live node's
    -- next shown event past the agenda's region.
    --
    -- RECOVERY: `git show b75ee016` restores `adequacy.FeedTry`: an owed
    --   joiner reaches its delivery after its lag's silent steps
    --   (`joiner-delivers`); a lag behind the run's position is a lag
    --   behind any joiner subscribed at or past it (`lags-later`); and
    --   `<ᵖ-trans`.
    kept : ∀ {m c} → Carried m c → Wait Carried (step m) (stepᵁ c)

    -- The run begins carried: the program pending at the root.
    carried-begin : (o : PureObs [] R) → Carried (begin o) (subscribe o [] root)

  -- The program's run is what the root is shown.
  --
  -- The corecursion re-enters on `adequacy.Carrier`'s relation: every
  -- live observer the machine has made held to its subtree's meaning
  -- (`Oracle-CLI exact`), and what the machine owes next an agenda
  -- located in the witness.  An observer is dead once it completes, a
  -- switch moves off it, or the observer that subscribed it is dead.
  --
  -- Tested, both halves, against `Unfold`'s own node meanings, each
  -- joiner held to its own copy of the source: the invariant on drawn
  -- seeds (`Oracle-CLI exact`) and at the connect feed's edges, a
  -- joiner subscribed or the body completing mid-feed
  -- (`quickcheck.Adversary`); progress on programs spinning with no
  -- budget, a source spinning beside its body's later events, a switch
  -- onto a lane spinning on subscribe, a cut ending a source emitting
  -- forever (`quickcheck.Spin`).
  --
  -- DEAD ROUTE: one exact relation at a single hole of the tree,
  --   delivery climbing the context frame by frame.  A connect's feed
  --   and a lane bursting inline deliver at a context deeper than the
  --   frame's, and refocusing the hole there needs the whole invariant
  --   rebuilt at every frame on the way up and down.
  --
  -- RECOVERY: `git show 94ae8083` restores the single-hole route
  --   (`adequacy.Realize`, `adequacy.Segment`, `adequacy.deliver`,
  --   `adequacy.step`): the heap realizing a configuration (`Holds`,
  --   `Joined`, `Dead`), calm points and the glue over them.  The same commit restores
  --   the order on positions in `denotation.MonotonicList`: strict,
  --   transitive, total, past a position past everything under it, a
  --   burst's steps before its close, cascades never nesting.
  sim : (o : PureObs [] R) → trace (begin o) ~ observe (⟦ o ⟧ []) root
  sim o = From.sim-from Carried kept (carried-begin o)

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
