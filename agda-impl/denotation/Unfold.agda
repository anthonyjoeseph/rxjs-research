{-# OPTIONS --guardedness #-}

-- A PROGRAM TREE'S MEANING, UNFOLDED.  A subscription is an inductive
-- configuration: one node per operator still running, a `defer` left
-- unexpanded until its turn.  `step` finds the configuration's next event
-- by structural recursion, and `unfold` repeats it, guarded by the event
-- it found.  So the meaning is productive without fuel and without
-- approximants, recursion through `defer` included.
--
-- Each node steps exactly as its operator in `MonotonicList` does, clause
-- for clause, positions included.  A `connect`'s source is held as the
-- configuration it starts in; each joiner steps a copy of it and rejoins,
-- and the `connect` steps one more beside its body, which shows the
-- events a shared run would, since a configuration is a value.
--
-- DEAD ROUTE: `⟦_⟧` by guarded corecursion over the tree directly, the
--   `defer` clause a `skip` whose tail is `⟦ force l ⟧`.  Agda refuses it:
--   every other clause puts its recursive call under a stream function
--   (`mapᴱ`, `go`, `rejoin`), which could strip the guard, so the call
--   through `defer` is never seen guarded.
module denotation.Unfold where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Level using (lower)

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (MonotonicList; Events; Events∞; out; skip; end; hush; Time; Pos; ix; last; tick; _<ᵖ_;
  Timeline; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close) renaming (sub to subᴾ; cold to coldᴹ)

open Events∞

------------------------------------------------------------------------
-- Configurations

mutual
  data Node : Set → Set₁ where
    -- A cold between frames, the next frame's timer set at `e`; or at
    -- step `i` of the frame at `r`.  Its timeline subscribed at tick `τ`.
    framesᶜ    : ∀ {A t} → Time → Pos → From A t → Node A
    burstᶜ     : ∀ {A t} → Time → Pos → ℕ → Frame A t → Node A
    endᶜ       : ∀ {A} → Pos → Node A
    ofᶜ        : ∀ {A} → Pos → ℕ → List A → Node A
    mapᶜ       : ∀ {A B} → (A → B) → Node A → Node B
    scanᶜ      : ∀ {A B} → (B → A → B) → B → Node A → Node B
    takeWhileᶜ : ∀ {A} → Bool → (A → Bool) → Node A → Node A
    -- The outer while it lasts, the lanes in flight newest first, the
    -- elements queued; a lane subscribed by `g` where it arrives.
    flatMapᶜ   : ∀ {A B} → T.FlatOp → (A → Pos → Node B) → Maybe (Node A) → List (Node B) → List A → Node B
    -- Joined at `p`, `i` events dropped so far, a copy of the source.
    joinᶜ      : ∀ {A} → Pos → ℕ → Node A → Node A
    -- A connect's body, its own source running beside it.
    connectᶜ   : ∀ {A B} → Node B → Node A → Node B
    deferᶜ     : ∀ {Γ A} → Later Timeline Γ A → Srcs Γ → Pos → Node A

  -- Each connect in scope, as the configuration its source starts in.
  Srcs : List Set → Set₁
  Srcs = All Node

------------------------------------------------------------------------
-- Subscribing: `MonotonicList`'s operators, observed at `p`

startᶜ : ∀ {A} → Pos → From A 0 → Node A
startᶜ p (at zero _ b) = burstᶜ (tick p) p 0 b
startᶜ p m             = framesᶜ (tick p) (p ++ [ last ]) m

-- Every operator subscribes its source where it is itself subscribed;
-- a `defer` waits.
subscribe : ∀ {Γ A} → Obs Timeline Γ A → Srcs Γ → Pos → Node A
subscribe (cold c)          ρ p = startᶜ p (lower c)
subscribe empty             ρ p = endᶜ (p ++ [ last ])
subscribe (of xs)           ρ p = ofᶜ p 0 xs
subscribe (map f s)         ρ p = mapᶜ f (subscribe s ρ p)
subscribe (scan f z s)      ρ p = scanᶜ f z (subscribe s ρ p)
subscribe (takeWhile i q s) ρ p = takeWhileᶜ i q (subscribe s ρ p)
subscribe (flatMap op f s)  ρ p = flatMapᶜ op (λ a q → subscribe (f a) ρ q) (just (subscribe s ρ p)) [] []
subscribe (connect s b)     ρ p = connecting (subscribe s ρ (p ++ [ ix 1 ]))
  where connecting : _ → _
        connecting c = connectᶜ (subscribe b (c ∷ ρ) (p ++ [ ix 0 ])) c
subscribe (connected i)     ρ p = joinᶜ p 0 (lookup ρ i)
subscribe (defer l)         ρ p = deferᶜ l ρ p

------------------------------------------------------------------------
-- One event

data Step (A : Set) : Set₁ where
  outˢ  : Pos → A → Node A → Step A
  skipˢ : Pos → Node A → Step A
  endˢ  : Pos → Step A
  hushˢ : Step A

headˢ : ∀ {A} → Step A → Maybe Pos
headˢ (outˢ k _ _) = just k
headˢ (skipˢ k _)  = just k
headˢ (endˢ k)     = just k
headˢ hushˢ        = nothing

burstˢ : ∀ {A t} → Time → Pos → ℕ → Frame A t → Step A
burstˢ τ r i (emit a k) = outˢ (r ++ [ ix i ]) a (burstᶜ τ r (suc i) (Frame∞.force k))
burstˢ τ r i (stall k)  = skipˢ (r ++ [ ix i ]) (burstᶜ τ r (suc i) (Frame∞.force k))
burstˢ τ r i (close k)  = skipˢ (r ++ [ ix i ]) (framesᶜ τ (r ++ [ last ]) (From∞.force k))

framesˢ : ∀ {A t} → Time → Pos → From A t → Step A
framesˢ τ e done       = endˢ e
framesˢ τ e quiet      = hushˢ
framesˢ τ e (at t _ b) = burstˢ τ (ix (τ + t) ∷ subᴾ e ∷ []) 0 b

ofˢ : ∀ {A} → Pos → ℕ → List A → Step A
ofˢ p i []       = endˢ (p ++ [ last ])
ofˢ p i (x ∷ xs) = outˢ (p ++ [ ix i ]) x (ofᶜ p (suc i) xs)

mapˢ : ∀ {A B} → (A → B) → Step A → Step B
mapˢ f (outˢ k a c) = outˢ k (f a) (mapᶜ f c)
mapˢ f (skipˢ k c)  = skipˢ k (mapᶜ f c)
mapˢ f (endˢ k)     = endˢ k
mapˢ f hushˢ        = hushˢ

scanˢ : ∀ {A B} → (B → A → B) → B → Step A → Step B
scanˢ f z (outˢ k a c) = outˢ k (f z a) (scanᶜ f (f z a) c)
scanˢ f z (skipˢ k c)  = skipˢ k (scanᶜ f z c)
scanˢ f z (endˢ k)     = endˢ k
scanˢ f z hushˢ        = hushˢ

taking : ∀ {A} → Bool → (A → Bool) → Pos → A → Node A → Bool → Step A
taking i     p k a c true  = outˢ k a (takeWhileᶜ i p c)
taking true  p k a c false = outˢ k a (endᶜ (k ++ [ last ]))
taking false p k a c false = endˢ (k ++ [ last ])

takeWhileˢ : ∀ {A} → Bool → (A → Bool) → Step A → Step A
takeWhileˢ i p (outˢ k a c) = taking i p k a c (p a)
takeWhileˢ i p (skipˢ k c)  = skipˢ k (takeWhileᶜ i p c)
takeWhileˢ i p (endˢ k)     = endˢ k
takeWhileˢ i p hushˢ        = hushˢ

shownˢ : ∀ {A} → Pos → ℕ → Pos → Maybe A → Node A → Bool → Step A
shownˢ p i q (just a) c true  = outˢ (q ++ [ subᴾ p ]) a (joinᶜ p i c)
shownˢ p i q nothing  c true  = skipˢ (q ++ [ subᴾ p ]) (joinᶜ p i c)
shownˢ p i q _        c false = skipˢ (p ++ [ ix i ]) (joinᶜ p (suc i) c)

rejoinˢ : ∀ {A} → Pos → ℕ → Step A → Step A
rejoinˢ p i (outˢ q a c) = shownˢ p i q (just a) c (p <ᵖ q)
rejoinˢ p i (skipˢ q c)  = shownˢ p i q nothing c (p <ᵖ q)
rejoinˢ p i (endˢ c)     = if p <ᵖ c then endˢ (c ++ [ subᴾ p ]) else endˢ (p ++ [ last ])
rejoinˢ p i hushˢ        = hushˢ

-- `connect`'s body `b` and source `s` stepped, as `MonotonicList.beside`
-- interleaves them; the source left unmoved when the body comes first.
beforeˢ : ∀ {B} → Pos → Step B → Bool
beforeˢ q (outˢ k _ _) = q <ᵖ k
beforeˢ q (skipˢ k _)  = q <ᵖ k
beforeˢ q (endˢ k)     = q <ᵖ k
beforeˢ q hushˢ        = true

aheadˢ : ∀ {A B} → Node B → Step B → Node A → Pos → Node A → Bool → Step B
aheadˢ b sb             s q s′ true  = skipˢ q (connectᶜ b s′)
aheadˢ b (outˢ k a b′)  s q s′ false = outˢ k a (connectᶜ b′ s)
aheadˢ b (skipˢ k b′)   s q s′ false = skipˢ k (connectᶜ b′ s)
aheadˢ b (endˢ c)       s q s′ false = endˢ c
aheadˢ b hushˢ          s q s′ false = hushˢ

besideˢ : ∀ {A B} → Node B → Step B → Node A → Step A → Step B
besideˢ b sb s (outˢ q _ s′) = aheadˢ b sb s (q ++ [ ix 0 ]) s′ (beforeˢ (q ++ [ ix 0 ]) sb)
besideˢ b sb s (skipˢ q s′)  = aheadˢ b sb s (q ++ [ ix 0 ]) s′ (beforeˢ (q ++ [ ix 0 ]) sb)
besideˢ b sb s (endˢ _)      = sb
besideˢ b sb s hushˢ         = sb

-- A lane arriving, subscribed at `q`.
admit : ∀ {A B : Set} → T.FlatOp → (A → Pos → Node B) → Pos → A → List (Node B) → List A → List (Node B) × List A
admit (T.mergeᶠ nothing)  g q a ls       qs = g a q ∷ ls , qs
admit (T.mergeᶠ (just n)) g q a ls       qs = if length ls <ᵇ n then (g a q ∷ ls , qs) else (ls , qs ++ [ a ])
admit T.switchᶠ           g q a ls       qs = [ g a q ] , qs
admit T.exhaustᶠ          g q a []       qs = [ g a q ] , qs
admit T.exhaustᶠ          g q a (l ∷ ls) qs = l ∷ ls , qs

-- The lane whose next event comes first, with the lanes around it, and
-- its own configuration unmoved, for when the outer comes first instead.
data Earliest (B : Set) : Set₁ where
  none  : Earliest B
  found : Pos → List (Node B) → Node B → Step B → List (Node B) → Earliest B

pick : ∀ {B} → Node B → Step B → List (Node B) → Maybe Pos → Earliest B → Earliest B
pick l s ls nothing  none                  = none
pick l s ls nothing  (found k bs c sc as)  = found k (l ∷ bs) c sc as
pick l s ls (just k) none                  = found k [] l s ls
pick l s ls (just k) (found k′ bs c sc as) = if k <ᵖ k′ then found k [] l s ls else found k′ (l ∷ bs) c sc as

-- `flatMap`'s outer stepped, and a lane stepped.
outerˢ : ∀ {A B} → T.FlatOp → (A → Pos → Node B) → Step A → List (Node B) → List A → Step B
outerˢ op g (outˢ q a o) ls qs with admit op g (q ++ [ ix 1 ]) a ls qs
... | ls′ , qs′ = skipˢ (q ++ [ ix 0 ]) (flatMapᶜ op g (just o) ls′ qs′)
outerˢ op g (skipˢ q o)  ls qs = skipˢ q (flatMapᶜ op g (just o) ls qs)
outerˢ op g (endˢ c)     [] [] = endˢ c
outerˢ op g (endˢ c)     ls qs = skipˢ c (flatMapᶜ op g nothing ls qs)
outerˢ op g hushˢ        ls qs = hushˢ

laneˢ : ∀ {A B} → T.FlatOp → (A → Pos → Node B) → Maybe (Node A) → List (Node B) → Step B → List (Node B) → List A → Step B
laneˢ op g o       bs (outˢ k b c) as qs       = outˢ k b (flatMapᶜ op g o (bs ++ c ∷ as) qs)
laneˢ op g o       bs (skipˢ k c)  as qs       = skipˢ k (flatMapᶜ op g o (bs ++ c ∷ as) qs)
laneˢ op g o       bs (endˢ c)     as (a ∷ qs) = skipˢ (c ++ [ ix 0 ]) (flatMapᶜ op g o (g a (c ++ [ ix 1 ]) ∷ bs ++ as) qs)
laneˢ op g nothing [] (endˢ c)     [] []       = endˢ c
laneˢ op g o       bs (endˢ c)     as []       = skipˢ c (flatMapᶜ op g o (bs ++ as) [])
laneˢ op g o       bs hushˢ        as qs       = hushˢ

-- The outer comes first when its next event is earlier than the lane's.
raceˢ : ∀ {A B} → T.FlatOp → (A → Pos → Node B) → Node A → Step A → Maybe Pos → Pos → List (Node B) → Node B → Step B → List (Node B)
      → List A → Step B
raceˢ op g o so nothing   k bs l s as qs = laneˢ op g (just o) bs s as qs
raceˢ op g o so (just k′) k bs l s as qs =
  if k′ <ᵖ k then outerˢ op g so (bs ++ l ∷ as) qs else laneˢ op g (just o) bs s as qs

mutual
  step : ∀ {A} → Node A → Step A
  step (framesᶜ τ e m)         = framesˢ τ e m
  step (burstᶜ τ r i b)        = burstˢ τ r i b
  step (endᶜ p)                = endˢ p
  step (ofᶜ p i xs)            = ofˢ p i xs
  step (mapᶜ f c)              = mapˢ f (step c)
  step (scanᶜ f z c)           = scanˢ f z (step c)
  step (takeWhileᶜ i p c)      = takeWhileˢ i p (step c)
  step (flatMapᶜ op g o ls qs) = goˢ op g o ls qs (earliest ls)
  step (joinᶜ p i c)           = rejoinˢ p i (step c)
  step (connectᶜ b s)          = besideˢ b (step b) s (step s)
  step (deferᶜ l ρ p)          = skipˢ (p ++ [ ix 0 ]) (subscribe (Later.force l) ρ (p ++ [ ix 1 ]))

  earliest : ∀ {B} → List (Node B) → Earliest B
  earliest []       = none
  earliest (l ∷ ls) = pick l s ls (headˢ s) (earliest ls)
    where s = step l

  goˢ : ∀ {A B} → T.FlatOp → (A → Pos → Node B) → Maybe (Node A) → List (Node B) → List A → Earliest B → Step B
  goˢ op g nothing  ls qs none                 = hushˢ
  goˢ op g (just o) ls qs none                 = outerˢ op g (step o) ls qs
  goˢ op g nothing  ls qs (found k bs l s as)  = laneˢ op g nothing bs s as qs
  goˢ op g (just o) ls qs (found k bs l s as)  = raceˢ op g o so (headˢ so) k bs l s as qs
    where so = step o

------------------------------------------------------------------------
-- The meaning

mutual
  unfold : ∀ {A} → Node A → Events A
  unfold c = shown (step c)

  shown : ∀ {A} → Step A → Events A
  shown (outˢ k a c) = out k a λ where .force → unfold c
  shown (skipˢ k c)  = skip k λ where .force → unfold c
  shown (endˢ k)     = end k
  shown hushˢ        = hush

-- THE meaning of a program: what each subscriber sees.
⟦_⟧ : ∀ {Γ A} → Obs Timeline Γ A → Srcs Γ → MonotonicList A
⟦ o ⟧ ρ = coldᴹ λ p → unfold (subscribe o ρ p)
