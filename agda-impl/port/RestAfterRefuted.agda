{-# OPTIONS --guardedness #-}

-- REFUTATION of `rest-after`:
--
--   rest-after : ∀ {Γ A B q} (n : U.Node Γ A) → Heads q n → HeadsS q (U.restˢ {B = B} n)
--
-- The claim would say a node whose step is at or after q has its REST
-- also at or after q.  This is FALSE.
--
-- COUNTEREXAMPLE:
--   n = connectᶜ [] bdy (live s)
--   s = connectᶜ [] bdy (live src)    -- inner connect
--   src = ofᶜ [] 0 [tt]               -- steps to outˢ [ix 0] ...
--   bdy = joinᶜ (here refl) [] [] nothing   -- steps to hushˢ
--
-- step src  = outˢ [ix 0] tt ...
-- step s    = skipˢ [ix 0, ix 0] ...    (source's out before body's hush)
-- step n    = skipˢ [ix 0, ix 0, ix 0] ...   (head = q)
-- restˢ n   → burstsˢ [] s (step s)
--           = skipˢ [ix 0, ix 0] ...    (inside [] [ix 0,ix 0] = true → keeps raw k)
-- headˢ (restˢ n) = just [ix 0, ix 0]
--
-- But q = [ix 0, ix 0, ix 0] > [ix 0, ix 0], so q ≰ [ix 0, ix 0].
--
-- MECHANISM: `sourceˢ` prepends an [ix 0] to the source's step position
-- (giving k ++ [ix 0]) before the step becomes the connect's step.
-- `burstsˢ` uses the RAW source position k.  When inside r k holds,
-- burstsˢ emits skipˢ k ..., which is strictly BEFORE k ++ [ix 0].
-- So the rest can head before q while the step heads exactly at q.
--
-- REACHABILITY: yes, directly reachable from U.subscribe.
-- `subscribe (connect s b) p = connectᶜ (p ++ [ix 1]) (subscribe b ...) (live (subscribe s ...))`
-- Nesting two connects gives exactly this shape.
-- After one step that feeds the inner source, the configuration is
-- `connectᶜ r b (live (connectᶜ r′ b′ (live src′)))` — step is at q,
-- rest is one level short.
--
-- IMPACT ON shut-heads: see DEAD ROUTE below.
--
-- DEAD ROUTE: extending this to a shut-heads counterexample via
-- b = burstingᶜ r t where t contains a joiner on (there i).
--
-- The candidate needs step (shut i c t) to fall outside the burst range
-- r (or become endˢ/hushˢ), so that burstsˢ falls back to restˢ (shut t),
-- which heads before q by the rest-after mechanism.
--
-- Structural block: any shut that tells a joinᶜ at subscription p
-- assigns the end c ++ [subᴾ p] or p ++ [last] (from told-formula).
-- Both end-positions carry a `sub` or `last` label, which cmpLabel
-- places STRICTLY ABOVE every `ix n` label.  Inside a connect
-- connectᶜ r′ body (live src), the sourceˢ function races (source
-- step ++ [ix 0]) against (body step).  After a shut, the body step
-- becomes endˢ (c ++ [sub p]) — a sub-label position — while the
-- source step remains outˢ/skipˢ at ix-label positions.  Since
-- ix < sub in cmpLabel, the source step wins every such race.
-- Consequence: step (shut i c t) = same ix-label position as step t,
-- still inside r, still heading at q.  The burst stays; it does not
-- fall to restˢ.
--
-- Therefore no shut-over-burstingᶜ counterexample can be constructed
-- by this route.  shut-heads may be true; its old proof fails only
-- because it invokes bursts-down at an overly general type (unrelated
-- t, t′) instead of the specific t′ = shut i c t case, where the
-- step-position invariant is preserved.
module port.RestAfterRefuted where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; ix; _<ᵖ_)
open import port.Sorted using (_≤ᵖ_)
import denotation.Unfold as U

-- Same predicates as port.Strong / port.Frame, copied locally for the
-- scratch proof.
Heads : ∀ {Γ A} → Pos → U.Node Γ A → Set
Heads q c = ∀ {k} → U.headˢ (U.step c) ≡ just k → q ≤ᵖ k

HeadsS : ∀ {Γ A} → Pos → U.Step Γ A → Set
HeadsS q s = ∀ {k} → U.headˢ s ≡ just k → q ≤ᵖ k

private
  -- Concrete counterexample
  src : U.Node [] ⊤
  src = U.ofᶜ [] 0 (tt ∷ [])

  bdy : U.Node (⊤ ∷ []) ⊤
  bdy = U.joinᶜ (here refl) [] [] nothing

  -- Inner connect: step lands at [ix 0, ix 0]
  s : U.Node [] ⊤
  s = U.connectᶜ [] bdy (U.live src)

  -- Outer connect: step lands at q = [ix 0, ix 0, ix 0]
  n : U.Node [] ⊤
  n = U.connectᶜ [] bdy (U.live s)

  q : Pos
  q = ix 0 ∷ ix 0 ∷ ix 0 ∷ []

  -- step n heads exactly at q.
  step-head : U.headˢ (U.step n) ≡ just q
  step-head = refl

  -- restˢ n heads at [ix 0, ix 0], strictly before q.
  rest-head : U.headˢ (U.restˢ {B = ⊤} n) ≡ just (ix 0 ∷ ix 0 ∷ [])
  rest-head = refl

  -- q ≰ [ix 0, ix 0]: q = [ix 0,ix 0,ix 0] > [ix 0,ix 0].
  not-le : ¬ (q ≤ᵖ (ix 0 ∷ ix 0 ∷ []))
  not-le (inj₁ ())  -- [ix 0,ix 0,ix 0] ≢ [ix 0,ix 0]
  not-le (inj₂ ())  -- [ix 0,ix 0,ix 0] <ᵖ [ix 0,ix 0] = false ≢ true

-- The refutation: rest-after is FALSE.
¬rest-after : ¬ (∀ {Γ A B q} (n : U.Node Γ A) → Heads q n → HeadsS q (U.restˢ {B = B} n))
¬rest-after ra =
  not-le (ra {Γ = []} {A = ⊤} {B = ⊤} {q = q} n (λ{ refl → inj₁ refl }) rest-head)
