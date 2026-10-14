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
-- Both halves of adequacy are read off the one relation.  Every prefix
-- of the trace is `Placed` against the events, so shows nothing they do
-- not; every item the events show is within some prefix.  The prefixes
-- are a chain with no clock condition: a longer one extends the record
-- of a cut one.
module Simulation where

open import Data.List using ([]; _++_; [_]; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; Σ)

open import denotation.MonotonicList using (Events; Events∞; out; skip; end; hush; tick; observe; root)
open import denotation.Order using (_⊑_; Chain)
open import denotation.Unfold using (⟦_⟧)
open import operation.Machine using (module Machine)
open import operation.Placed using (Placed; cut; ends; quiets; sends; skips; items; Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; frames-cut)
open import operation.PureObservable using (PureObs; module Pure)

module Sim (R : Set) where
  open Machine R using (Trace; Trace∞; tau; out; end; idle; trace; begin; Read; read; noted; reading; prefix)
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

  postulate
    -- The program's run is what the root is shown.
    --
    -- RECOVERY: `git show a2e0bb8b` restores `Config` and `Realize`, a
    --   configuration of the whole running program realized by the fuel
    --   engine's heap, and `Bound`'s frame-by-frame invariant over it.
    sim : (o : PureObs [] R) → trace (begin o) ~ observe (⟦ o ⟧ []) root

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
