{-# OPTIONS --guardedness #-}

-- A RUN IN PROGRESS, AS A CONFIGURATION.  A subscription is an inductive
-- configuration: one node per operator still running, a `defer` left
-- unexpanded until its turn.  It has two readings.
--
-- ITS MEANING (`meaning`, `cutᴺ`): each node read by its operator's own
-- stream function in `MonotonicList`, its next event and what it leaves
-- running were it cut there; the source of a `connect` handed to its
-- joiners whole, as `connectᴰ` hands it, and a `defer` by the fold's
-- meaning of what it defers, so no node needs approximants.  So a
-- program subscribed is `Denote`'s meaning (`subscribed`).
--
-- ITS STEPPER (`step`, `unfold`), the test harness's reading of a run: `step`
-- finds the configuration's next event by structural recursion, and
-- `unfold` repeats it, guarded by the event it found, so it needs no
-- approximants.  Each node but `connect` steps exactly as its operator's
-- stream function does, clause for clause, positions included; a
-- `connect` steps its source once, beside its body, and feeds each value
-- to the joiners the body holds, as an rxjs Subject's `next` does: a
-- joiner shows what it was fed, at the value's position under its own.
-- A configuration is typed by the connects in scope, so a joiner names
-- its connect and is fed only its values.
--
-- WHAT A CUT LEAVES RUNNING is a configuration too (`restˢ`): a rest node
-- runs a node's tail as skips, so a flatMap's ended parts run on in its
-- pool and a connect's source burst runs out past its body's end.
--
-- DEAD ROUTE: the meaning by guarded corecursion over the tree directly, the
--   `defer` clause a `skip` whose tail is `⟦ force l ⟧`.  Agda refuses it:
--   every other clause puts its recursive call under a stream function
--   (`mapᴱ`, `go`, `rejoin`), which could strip the guard, so the call
--   through `defer` is never seen guarded.
module denotation.Unfold where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.List.Relation.Unary.All using (All; lookup; updateAt) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
import Data.List as L

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (timelineAt; Events; Events∞; out; skip; end; hush; Time; Pos; ix; last; tick; _<ᵖ_; inside; Tail; pin; idle; Tail∞; _∪_; Timeline; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close) renaming (sub to subᴾ)
open import denotation.MonotonicList using (MonotonicList; tailᴱ) renaming (cold to coldᴹ)
import denotation.MonotonicList as M′
open import denotation.MonotonicList using (Agree; agree-refl; agreeᵀ-refl; agree-trans; agreeᵀ-trans; _≈[_]_; agrees; agree; agreeᵀ; ≈ₖ-sym; ≈ₖ-trans; ≈ₖ-pred; hot; deferᴰ)
open import denotation.Denote using (DenEnv; flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (EnvAgree; _∷ᵉ_; lookup-agree; deferᴰ-contractive; approx-ne; from; toward; Compositional; compositional)
module C = Compositional compositional
open import denotation.NonExpansive using (mapᴰ-ne; scanᴰ-ne; takeWhileᴰ-ne; flatMapᴰ-ne; beside-ne; hot-ne; burstOn-ne; ∪-ne;
  entered; Agreeˢ; go-ne; whole-ne; liveᴼ; []ᴸ; []ᑫ; mapᴱ-neᴹ)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- Configurations

-- A step of connect `i`'s source, a value or a skip, that a node not yet
-- subscribed has still to be fed once it is.
data Notice (Γ : List Set) : Set₁ where
  notice : ∀ {A} → A ∈ Γ → Pos → Maybe A → Notice Γ

mutual
  data Node : List Set → Set → Set₁ where
    framesᶜ    : ∀ {Γ A t} → Time → Pos → From A t → Node Γ A
    burstᶜ     : ∀ {Γ A t} → Time → Pos → ℕ → Frame A t → Node Γ A
    ofᶜ        : ∀ {Γ A} → Pos → ℕ → List A → Node Γ A
    mapᶜ       : ∀ {Γ A B} → (A → B) → Node Γ A → Node Γ B
    scanᶜ      : ∀ {Γ A B} → (B → A → B) → B → Node Γ A → Node Γ B
    takeWhileᶜ : ∀ {Γ A} → Bool → (A → Bool) → Node Γ A → Node Γ A
    -- The outer, the lanes, the queue, and the pool: what ended parts left running.
    flatMapᶜ   : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Maybe (Node Γ A) → List (Node Γ B) → List A → Node Γ B → Node Γ B
    -- Joined to connect `i` at `p`: what it has been fed and not yet
    -- shown, a value or a skip, and where it ends once its source has.
    joinᶜ      : ∀ {Γ A} → A ∈ Γ → Pos → List (Pos × Maybe A) → Maybe Pos → Node Γ A
    -- A connect whose source is subscribed at `r`: its body, and its source.
    connectᶜ   : ∀ {Γ A B} → Pos → Node (A ∷ Γ) B → Source Γ A → Node Γ B
    -- Reached at `p`, and the source steps it has still to be fed.
    deferᶜ     : ∀ {Γ A} → Later Timeline Γ A → Pos → List (Notice Γ) → Node Γ A
    -- Ending at `p`, leaving `n`'s rest running.
    endingᶜ    : ∀ {Γ A} → Pos → Node Γ A → Node Γ A
    -- Rests, each run as skips: a node's; none; two side by side; a
    -- source's burst under `r` run out; a body's under its source.
    restᶜ      : ∀ {Γ A B} → Node Γ A → Node Γ B
    idleᶜ      : ∀ {Γ B} → Node Γ B
    unionᶜ     : ∀ {Γ B} → Node Γ B → Node Γ B → Node Γ B
    burstingᶜ  : ∀ {Γ A B} → Pos → Node Γ A → Node Γ B
    underᶜ     : ∀ {Γ A C B} → Source Γ A → Node (A ∷ Γ) C → Node Γ B

  -- A source running, else where it ended and what it left running.
  data Source (Γ : List Set) (A : Set) : Set₁ where
    live  : Node Γ A → Source Γ A
    ended : Pos → Node Γ A → Source Γ A

-- The connects in scope, innermost first, each as its source's
-- subscription and configuration.
data Srcs : List Set → Set₁ where
  []  : Srcs []
  _∷_ : ∀ {Γ A} → Pos × Node Γ A → Srcs Γ → Srcs (A ∷ Γ)

wrap : ∀ {Γ A} → Srcs Γ → Node Γ A → Node [] A
wrap []            n = n
wrap ((r , s) ∷ δ) n = wrap δ (connectᶜ r n (live s))

------------------------------------------------------------------------
-- Subscribing

startᶜ : ∀ {Γ A} → Pos → From A 0 → Node Γ A
startᶜ p (at zero _ b) = burstᶜ (tick p) p 0 b
startᶜ p m             = framesᶜ (tick p) (p ++ [ last ]) m

subscribe : ∀ {Γ A} → Obs Timeline Γ A → Pos → Node Γ A
subscribe (cold c)          p = startᶜ p (timelineAt c p)
subscribe empty             p = ofᶜ p 0 []
subscribe (of xs)           p = ofᶜ p 0 xs
subscribe (map f s)         p = mapᶜ f (subscribe s p)
subscribe (scan f z s)      p = scanᶜ f z (subscribe s p)
subscribe (takeWhile i q s) p = takeWhileᶜ i q (subscribe s p)
subscribe (flatMap op f s)  p = flatMapᶜ op (λ a q → subscribe (f a) q) (just (subscribe s p)) [] [] idleᶜ
subscribe (connect s b)     p = connectᶜ (p ++ [ ix 1 ]) (subscribe b (p ++ [ ix 0 ])) (live (subscribe s (p ++ [ ix 1 ])))
subscribe (connected i)     p = joinᶜ i p [] nothing
subscribe (defer l)         p = deferᶜ l p []

------------------------------------------------------------------------
-- A connect's source, delivered to its joiners

same? : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → B ∈ Γ → Maybe (A ≡ B)
same? (here refl) (here refl) = just refl
same? (there i)   (there j)   = same? i j
same? _           _           = nothing

-- A joiner of connect `i` is fed the source's step at `q`, a value or a
-- skip, under its own position if it joined before `q`, else as a skip
-- at its subscription.
fed : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe A → B ∈ Γ → Pos → List (Pos × Maybe B) → Maybe (A ≡ B) → List (Pos × Maybe B)
fed i q a j p xs (just refl) = if p <ᵖ q then xs ++ [ q ++ [ subᴾ p ] , a ] else xs ++ [ p ++ [ ix 0 ] , nothing ]
fed i q a j p xs nothing     = xs

-- And told where it ends, once: at the source's end if it joined before
-- it, else at once.
told : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → B ∈ Γ → Pos → Maybe Pos → Maybe (A ≡ B) → Maybe Pos
told i c j p nothing  (just refl) = just (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ])
told i c j p e        _           = e

mutual
  feed : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe A → Node Γ B → Node Γ B
  feed i q a (mapᶜ f c)                 = mapᶜ f (feed i q a c)
  feed i q a (scanᶜ f z c)              = scanᶜ f z (feed i q a c)
  feed i q a (takeWhileᶜ b p c)         = takeWhileᶜ b p (feed i q a c)
  feed i q a (flatMapᶜ op g o ls qs pl) = flatMapᶜ op (λ x r → feed i q a (g x r)) (feedᴹ i q a o) (feedᴸ i q a ls) qs (feed i q a pl)
  feed i q a (joinᶜ j p xs e)           = joinᶜ j p (fed i q a j p xs (same? i j)) e
  feed i q a (connectᶜ r b s)           = connectᶜ r (feed (there i) q a b) (feedˢ i q a s)
  feed i q a (deferᶜ l p ns)            = deferᶜ l p (ns ++ [ notice i q a ])
  feed i q a (endingᶜ p n)              = endingᶜ p (feed i q a n)
  feed i q a (restᶜ n)                  = restᶜ (feed i q a n)
  feed i q a (unionᶜ x y)               = unionᶜ (feed i q a x) (feed i q a y)
  feed i q a (burstingᶜ r t)            = burstingᶜ r (feed i q a t)
  feed i q a (underᶜ s b)               = underᶜ (feedˢ i q a s) (feed (there i) q a b)
  feed i q a c                          = c

  feedᴹ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe A → Maybe (Node Γ B) → Maybe (Node Γ B)
  feedᴹ i q a nothing  = nothing
  feedᴹ i q a (just c) = just (feed i q a c)

  feedᴸ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe A → List (Node Γ B) → List (Node Γ B)
  feedᴸ i q a []       = []
  feedᴸ i q a (c ∷ cs) = feed i q a c ∷ feedᴸ i q a cs

  feedˢ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe A → Source Γ B → Source Γ B
  feedˢ i q a (live s)    = live (feed i q a s)
  feedˢ i q a (ended c t) = ended c (feed i q a t)

feeds : ∀ {Γ B} → List (Notice Γ) → Node Γ B → Node Γ B
feeds []                  c = c
feeds (notice i q a ∷ ns) c = feeds ns (feed i q a c)

mutual
  shut : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Node Γ B → Node Γ B
  shut i c (mapᶜ f n)                 = mapᶜ f (shut i c n)
  shut i c (scanᶜ f z n)              = scanᶜ f z (shut i c n)
  shut i c (takeWhileᶜ b p n)         = takeWhileᶜ b p (shut i c n)
  shut i c (flatMapᶜ op g o ls qs pl) = flatMapᶜ op g (shutᴹ i c o) (shutᴸ i c ls) qs (shut i c pl)
  shut i c (joinᶜ j p xs e)           = joinᶜ j p xs (told i c j p e (same? i j))
  shut i c (connectᶜ r b s)           = connectᶜ r (shut (there i) c b) (shutˢ i c s)
  shut i c (endingᶜ p n)              = endingᶜ p (shut i c n)
  shut i c (restᶜ n)                  = restᶜ (shut i c n)
  shut i c (unionᶜ x y)               = unionᶜ (shut i c x) (shut i c y)
  shut i c (burstingᶜ r t)            = burstingᶜ r (shut i c t)
  shut i c (underᶜ s b)               = underᶜ (shutˢ i c s) (shut (there i) c b)
  shut i c n                          = n

  shutᴹ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe (Node Γ B) → Maybe (Node Γ B)
  shutᴹ i c nothing  = nothing
  shutᴹ i c (just n) = just (shut i c n)

  shutᴸ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → List (Node Γ B) → List (Node Γ B)
  shutᴸ i c []       = []
  shutᴸ i c (n ∷ ns) = shut i c n ∷ shutᴸ i c ns

  shutˢ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Source Γ B → Source Γ B
  shutˢ i c (live s)    = live (shut i c s)
  shutˢ i c (ended e t) = ended e (shut i c t)

------------------------------------------------------------------------
-- One event

data Step (Γ : List Set) (A : Set) : Set₁ where
  outˢ  : Pos → A → Node Γ A → Step Γ A
  skipˢ : Pos → Node Γ A → Step Γ A
  endˢ  : Pos → Step Γ A
  hushˢ : Step Γ A

headˢ : ∀ {Γ A} → Step Γ A → Maybe Pos
headˢ (outˢ k _ _) = just k
headˢ (skipˢ k _)  = just k
headˢ (endˢ k)     = just k
headˢ hushˢ        = nothing

burstˢ : ∀ {Γ A t} → Time → Pos → ℕ → Frame A t → Step Γ A
burstˢ τ r i (emit a k) = outˢ (r ++ [ ix i ]) a (burstᶜ τ r (suc i) (Frame∞.force k))
burstˢ τ r i (stall k)  = skipˢ (r ++ [ ix i ]) (burstᶜ τ r (suc i) (Frame∞.force k))
burstˢ τ r i (close k)  = skipˢ (r ++ [ ix i ]) (framesᶜ τ (r ++ [ last ]) (From∞.force k))

framesˢ : ∀ {Γ A t} → Time → Pos → From A t → Step Γ A
framesˢ τ e done       = endˢ e
framesˢ τ e quiet      = hushˢ
framesˢ τ e (at t _ b) = burstˢ τ (ix (τ + t) ∷ subᴾ e ∷ []) 0 b

ofˢ : ∀ {Γ A} → Pos → ℕ → List A → Step Γ A
ofˢ p i []       = endˢ (p ++ [ last ])
ofˢ p i (x ∷ xs) = outˢ (p ++ [ ix i ]) x (ofᶜ p (suc i) xs)

mapˢ : ∀ {Γ A B} → (A → B) → Step Γ A → Step Γ B
mapˢ f (outˢ k a c) = outˢ k (f a) (mapᶜ f c)
mapˢ f (skipˢ k c)  = skipˢ k (mapᶜ f c)
mapˢ f (endˢ k)     = endˢ k
mapˢ f hushˢ        = hushˢ

scanˢ : ∀ {Γ A B} → (B → A → B) → B → Step Γ A → Step Γ B
scanˢ f z (outˢ k a c) = outˢ k (f z a) (scanᶜ f (f z a) c)
scanˢ f z (skipˢ k c)  = skipˢ k (scanᶜ f z c)
scanˢ f z (endˢ k)     = endˢ k
scanˢ f z hushˢ        = hushˢ

-- An inclusive take's failing value leaves first, then the take ends,
-- leaving its source's rest running.
taking : ∀ {Γ A} → Bool → (A → Bool) → Pos → A → Node Γ A → Bool → Step Γ A
taking i     p k a c true  = outˢ k a (takeWhileᶜ i p c)
taking true  p k a c false = outˢ (k ++ [ ix 0 ]) a (endingᶜ (k ++ [ last ]) c)
taking false p k a c false = endˢ (k ++ [ last ])

takeWhileˢ : ∀ {Γ A} → Bool → (A → Bool) → Step Γ A → Step Γ A
takeWhileˢ i p (outˢ k a c) = taking i p k a c (p a)
takeWhileˢ i p (skipˢ k c)  = skipˢ k (takeWhileᶜ i p c)
takeWhileˢ i p (endˢ k)     = endˢ k
takeWhileˢ i p hushˢ        = hushˢ

joinˢ : ∀ {Γ A} → A ∈ Γ → Pos → List (Pos × Maybe A) → Maybe Pos → Step Γ A
joinˢ i p ((q , just a) ∷ xs) e   = outˢ q a (joinᶜ i p xs e)
joinˢ i p ((q , nothing) ∷ xs) e  = skipˢ q (joinᶜ i p xs e)
joinˢ i p []             (just c) = endˢ c
joinˢ i p []             nothing  = hushˢ

-- Two rests side by side, in position order, as `_∪_` runs them.
unionˢ : ∀ {Γ B} → Node Γ B → Step Γ B → Node Γ B → Step Γ B → Step Γ B
unionˢ x (skipˢ k x′) y (skipˢ k′ y′) = if k <ᵖ k′ then skipˢ k (unionᶜ x′ y) else skipˢ k′ (unionᶜ x y′)
unionˢ x (skipˢ k x′) y _             = skipˢ k (unionᶜ x′ y)
unionˢ x _            y sy            = sy

-- A body's rest, its source carried along.
underˢ : ∀ {Γ A B C} → Source Γ A → Step (A ∷ Γ) C → Step Γ B
underˢ s (skipˢ k b) = skipˢ k (underᶜ s b)
underˢ s _           = hushˢ

-- The body stepped, its source carried along.
bodyˢ : ∀ {Γ A B} → Pos → Source Γ A → Step (A ∷ Γ) B → Step Γ B
bodyˢ r s (outˢ k a b) = outˢ k a (connectᶜ r b s)
bodyˢ r s (skipˢ k b)  = skipˢ k (connectᶜ r b s)
bodyˢ r s (endˢ c)     = endˢ c
bodyˢ r s hushˢ        = hushˢ

-- Past its source's end, every joiner the body makes is told so at once.
shutˢᵗ : ∀ {Γ A B} → Pos → Pos → Node Γ A → Step (A ∷ Γ) B → Step Γ B
shutˢᵗ r c t (outˢ k a b) = outˢ k a (connectᶜ r (shut (here refl) c b) (ended c t))
shutˢᵗ r c t (skipˢ k b)  = skipˢ k (connectᶜ r (shut (here refl) c b) (ended c t))
shutˢᵗ r c t (endˢ e)     = endˢ e
shutˢᵗ r c t hushˢ        = hushˢ

beforeˢ : ∀ {Γ B} → Pos → Step Γ B → Bool
beforeˢ q (outˢ k _ _) = q <ᵖ k
beforeˢ q (skipˢ k _)  = q <ᵖ k
beforeˢ q (endˢ k)     = q <ᵖ k
beforeˢ q hushˢ        = true

-- The source's next event, when it comes before the body's; at its end,
-- what it leaves running runs on beside the body.
sourceˢ : ∀ {Γ A B} → Pos → Node (A ∷ Γ) B → Step (A ∷ Γ) B → Node Γ A → Step Γ A → Step Γ B
sourceˢ r b sb s (outˢ q a s′) =
  if beforeˢ (q ++ [ ix 0 ]) sb then skipˢ (q ++ [ ix 0 ]) (connectᶜ r (feed (here refl) q (just a) b) (live s′)) else bodyˢ r (live s) sb
sourceˢ r b sb s (skipˢ q s′)  =
  if beforeˢ (q ++ [ ix 0 ]) sb then skipˢ (q ++ [ ix 0 ]) (connectᶜ r (feed (here refl) q nothing b) (live s′)) else bodyˢ r (live s) sb
sourceˢ r b sb s (endˢ c)      =
  if beforeˢ (c ++ [ ix 0 ]) sb then skipˢ (c ++ [ ix 0 ]) (connectᶜ r (shut (here refl) c b) (ended c (restᶜ s))) else bodyˢ r (live s) sb
sourceˢ r b sb s hushˢ         = bodyˢ r (live s) sb

-- Past the source's end, its rest's next skip, when it comes before the body's.
endedˢ : ∀ {Γ A B} → Pos → Node (A ∷ Γ) B → Step (A ∷ Γ) B → Pos → Node Γ A → Step Γ A → Step Γ B
endedˢ r b sb c t (skipˢ k t′) =
  if beforeˢ (k ++ [ ix 0 ]) sb then skipˢ (k ++ [ ix 0 ]) (connectᶜ r b (ended c t′)) else shutˢᵗ r c t sb
endedˢ r b sb c t _            = shutˢᵗ r c t sb

-- Every lane's rest.
restsᶜ : ∀ {Γ A B} → List (Node Γ A) → Node Γ B
restsᶜ []       = idleᶜ
restsᶜ (l ∷ ls) = unionᶜ (restᶜ l) (restsᶜ ls)

-- A lane arriving, subscribed at `q`; and the rests of the lanes it drops.
admit : ∀ {Γ} {A B : Set} → T.FlatOp → (A → Pos → Node Γ B) → Pos → A → List (Node Γ B) → List A → Node Γ B
      → List (Node Γ B) × List A × Node Γ B
admit (T.mergeᶠ nothing)  g q a ls       qs d = g a q ∷ ls , qs , idleᶜ
admit (T.mergeᶠ (just n)) g q a ls       qs d = if length ls <ᵇ n then (g a q ∷ ls , qs , idleᶜ) else (ls , qs ++ [ a ] , idleᶜ)
admit T.switchᶠ           g q a ls       qs d = [ g a q ] , qs , d
admit T.exhaustᶠ          g q a []       qs d = [ g a q ] , qs , idleᶜ
admit T.exhaustᶠ          g q a (l ∷ ls) qs d = l ∷ ls , qs , idleᶜ

data Earliest (Γ : List Set) (B : Set) : Set₁ where
  none  : Earliest Γ B
  found : Pos → List (Node Γ B) → Node Γ B → Step Γ B → List (Node Γ B) → Earliest Γ B

pick : ∀ {Γ B} → Node Γ B → Step Γ B → List (Node Γ B) → Maybe Pos → Earliest Γ B → Earliest Γ B
pick l s ls nothing  none                  = none
pick l s ls nothing  (found k bs c sc as)  = found k (l ∷ bs) c sc as
pick l s ls (just k) none                  = found k [] l s ls
pick l s ls (just k) (found k′ bs c sc as) = if k <ᵖ k′ then found k [] l s ls else found k′ (l ∷ bs) c sc as

-- The outer, with its next step, or done.
data Outer (Γ : List Set) (A : Set) : Set₁ where
  doneᵒ : Outer Γ A
  runᵒ  : Node Γ A → Step Γ A → Outer Γ A

nodeᵒ : ∀ {Γ A} → Outer Γ A → Maybe (Node Γ A)
nodeᵒ doneᵒ      = nothing
nodeᵒ (runᵒ o _) = just o

clearˢ : Pos → Maybe Pos → Bool
clearˢ k nothing   = true
clearˢ k (just k′) = k <ᵖ k′

-- The pool's next skip comes before every part's next event.
aheadˢ : ∀ {Γ A B} → Pos → Outer Γ A → Earliest Γ B → Bool
aheadˢ k doneᵒ        none                = true
aheadˢ k doneᵒ        (found k′ _ _ _ _)  = k <ᵖ k′
aheadˢ k (runᵒ _ so)  none                = clearˢ k (headˢ so)
aheadˢ k (runᵒ _ so)  (found k′ _ _ _ _)  = clearˢ k (headˢ so) ∧ (k <ᵖ k′)

outerˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Node Γ A → Step Γ A → List (Node Γ B) → List A → Node Γ B → Step Γ B
outerˢ op g o (outˢ q a o′) ls qs p with admit op g (q ++ [ ix 1 ]) a ls qs (restsᶜ ls)
... | ls′ , qs′ , d = skipˢ (q ++ [ ix 0 ]) (flatMapᶜ op g (just o′) ls′ qs′ (unionᶜ p d))
outerˢ op g o (skipˢ q o′) ls qs p = skipˢ q (flatMapᶜ op g (just o′) ls qs p)
outerˢ op g o (endˢ c)     [] [] p = endˢ c
outerˢ op g o (endˢ c)     ls qs p = skipˢ c (flatMapᶜ op g nothing ls qs (unionᶜ p (restᶜ o)))
outerˢ op g o hushˢ        ls qs p = hushˢ

laneˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Maybe (Node Γ A) → List (Node Γ B) → Node Γ B → Step Γ B → List (Node Γ B)
      → List A → Node Γ B → Step Γ B
laneˢ op g o       bs l (outˢ k b c) as qs       p = outˢ k b (flatMapᶜ op g o (bs ++ c ∷ as) qs p)
laneˢ op g o       bs l (skipˢ k c)  as qs       p = skipˢ k (flatMapᶜ op g o (bs ++ c ∷ as) qs p)
laneˢ op g o       bs l (endˢ c)     as (a ∷ qs) p =
  skipˢ (c ++ [ ix 0 ]) (flatMapᶜ op g o (g a (c ++ [ ix 1 ]) ∷ bs ++ as) qs (unionᶜ p (restᶜ l)))
laneˢ op g nothing [] l (endˢ c)     [] []       p = endˢ c
laneˢ op g o       bs l (endˢ c)     as []       p = skipˢ c (flatMapᶜ op g o (bs ++ as) [] (unionᶜ p (restᶜ l)))
laneˢ op g o       bs l hushˢ        as qs       p = hushˢ

raceˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Node Γ A → Step Γ A → Maybe Pos → Pos → List (Node Γ B) → Node Γ B → Step Γ B
      → List (Node Γ B) → List A → Node Γ B → Step Γ B
raceˢ op g o so nothing   k bs l s as qs p = laneˢ op g (just o) bs l s as qs p
raceˢ op g o so (just k′) k bs l s as qs p =
  if k′ <ᵖ k then outerˢ op g o so (bs ++ l ∷ as) qs p else laneˢ op g (just o) bs l s as qs p

goˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Outer Γ A → List (Node Γ B) → List A → Node Γ B → Earliest Γ B → Step Γ B
goˢ op g doneᵒ       ls qs p none                = hushˢ
goˢ op g (runᵒ o so) ls qs p none                = outerˢ op g o so ls qs p
goˢ op g doneᵒ       ls qs p (found k bs l s as) = laneˢ op g nothing bs l s as qs p
goˢ op g (runᵒ o so) ls qs p (found k bs l s as) = raceˢ op g o so (headˢ so) k bs l s as qs p

-- The pool's next skip first, when it comes before every part's.
flatˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Outer Γ A → List (Node Γ B) → List A → Node Γ B → Step Γ B → Earliest Γ B
      → Step Γ B
flatˢ op g o ls qs p (skipˢ k p′) e = if aheadˢ k o e then skipˢ k (flatMapᶜ op g (nodeᵒ o) ls qs p′) else goˢ op g o ls qs p e
flatˢ op g o ls qs p _            e = goˢ op g o ls qs p e

-- The source's subscribe burst under `r`, run out: each step under `r`
-- pinned, then what the source leaves running.
mutual
  burstsˢ : ∀ {Γ A B} → Pos → Node Γ A → Step Γ A → Step Γ B
  burstsˢ r t (outˢ k _ t′) = if inside r k then skipˢ k (burstingᶜ r t′) else restˢ t
  burstsˢ r t (skipˢ k t′)  = if inside r k then skipˢ k (burstingᶜ r t′) else restˢ t
  burstsˢ r t _             = restˢ t

  -- What a node leaves running were it cut now, as its next skip.
  restˢ : ∀ {Γ A B} → Node Γ A → Step Γ B
  restˢ (mapᶜ f c)                            = restˢ c
  restˢ (scanᶜ f z c)                         = restˢ c
  restˢ (takeWhileᶜ i p c)                    = restˢ c
  restˢ (flatMapᶜ op g o ls qs p)             =
    unionˢ (outerᶜ o) (restᴹ o) (unionᶜ (restsᶜ ls) (restᶜ p)) (unionˢ (restsᶜ ls) (restsˢ ls) (restᶜ p) (restˢ p))
  restˢ (connectᶜ {B = C} r b (live s))       =
    unionˢ (burstingᶜ r s) (burstsˢ r s (step s)) (underᶜ (live s) b) (underˢ (live s) (restˢ {B = C} b))
  restˢ (connectᶜ {B = C} r b (ended c t))    =
    unionˢ (burstingᶜ r t) (burstsˢ r t (step t)) (underᶜ (ended c t) b) (underˢ (ended c t) (restˢ {B = C} b))
  restˢ (endingᶜ p n)                         = restˢ n
  restˢ (restᶜ n)                             = restˢ n
  restˢ (unionᶜ x y)                          = unionˢ (restᶜ x) (restˢ x) (restᶜ y) (restˢ y)
  restˢ (burstingᶜ r t)                       = burstsˢ r t (step t)
  restˢ (underᶜ {C = C} s b)                  = underˢ s (restˢ {B = C} b)
  restˢ _                                     = hushˢ

  outerᶜ : ∀ {Γ A B} → Maybe (Node Γ A) → Node Γ B
  outerᶜ nothing  = idleᶜ
  outerᶜ (just o) = restᶜ o

  restᴹ : ∀ {Γ A B} → Maybe (Node Γ A) → Step Γ B
  restᴹ nothing  = hushˢ
  restᴹ (just o) = restˢ o

  restsˢ : ∀ {Γ A B} → List (Node Γ A) → Step Γ B
  restsˢ []       = hushˢ
  restsˢ (l ∷ ls) = unionˢ (restᶜ l) (restˢ l) (restsᶜ ls) (restsˢ ls)

  step : ∀ {Γ A} → Node Γ A → Step Γ A
  step (framesᶜ τ e m)            = framesˢ τ e m
  step (burstᶜ τ r i b)           = burstˢ τ r i b
  step (ofᶜ p i xs)               = ofˢ p i xs
  step (mapᶜ f c)                 = mapˢ f (step c)
  step (scanᶜ f z c)              = scanˢ f z (step c)
  step (takeWhileᶜ i p c)         = takeWhileˢ i p (step c)
  step (flatMapᶜ op g o ls qs p)  = flatˢ op g (outerOf o) ls qs p (step p) (earliest ls)
  step (joinᶜ i p xs e)           = joinˢ i p xs e
  step (connectᶜ r b (live s))    = sourceˢ r b (step b) s (step s)
  step (connectᶜ r b (ended c t)) = endedˢ r b (step b) c t (step t)
  step (deferᶜ l p ns)            = skipˢ (p ++ [ ix 0 ]) (feeds ns (subscribe (Later.force l) (p ++ [ ix 1 ])))
  step (endingᶜ p n)              = endˢ p
  step (restᶜ n)                  = restˢ n
  step idleᶜ                      = hushˢ
  step (unionᶜ x y)               = unionˢ x (restˢ x) y (restˢ y)
  step (burstingᶜ r t)            = burstsˢ r t (step t)
  step (underᶜ {C = C} s b)       = underˢ s (restˢ {B = C} b)

  outerOf : ∀ {Γ A} → Maybe (Node Γ A) → Outer Γ A
  outerOf nothing  = doneᵒ
  outerOf (just o) = runᵒ o (step o)

  earliest : ∀ {Γ B} → List (Node Γ B) → Earliest Γ B
  earliest []       = none
  earliest (l ∷ ls) = pick l s ls (headˢ s) (earliest ls)
    where s = step l

------------------------------------------------------------------------
-- The stepper's run

mutual
  unfold : ∀ {Γ A} → Node Γ A → Events A
  unfold c = shown (step c)

  shown : ∀ {Γ A} → Step Γ A → Events A
  shown (outˢ k a c) = out k a λ where
    .force → unfold c
    .cut   → tailᵘ c
  shown (skipˢ k c)  = skip k λ where
    .force → unfold c
    .cut   → tailᵘ c
  shown (endˢ k)     = end k
  shown hushˢ        = hush

  -- What a configuration leaves running, run as its rest.
  tailᵘ : ∀ {Γ A} → Node Γ A → Tail
  tailᵘ {A = A} c = pinned (restˢ {B = A} c)

  pinned : ∀ {Γ A} → Step Γ A → Tail
  pinned (skipˢ k c) = pin k λ where .later → tailᵘ c
  pinned _           = idle

⟦_⟧ˢ : ∀ {Γ A} → Obs Timeline Γ A → Srcs Γ → MonotonicList A
⟦ o ⟧ˢ δ = coldᴹ λ p → λ where
  .force → unfold (wrap δ (subscribe o p))
  .cut   → tailᵘ (wrap δ (subscribe o p))

------------------------------------------------------------------------
-- The meaning: each node read by its operator's own stream function

-- Each connect in scope, as its source's run from where the source stands.
NEnv : List Set → Set₁
NEnv = All Events

-- A joiner's handle is its source's run, made hot.
hots : ∀ {Γ} → NEnv Γ → DenEnv Γ
hots []ᴬ      = []ᴬ
hots (e ∷ᴬ ρ) = hot e ∷ᴬ hots ρ

lookup-hots : ∀ {Γ A} (ρ : NEnv Γ) (i : A ∈ Γ) → lookup (hots ρ) i ≡ hot (lookup ρ i)
lookup-hots (e ∷ᴬ ρ) (here refl) = refl
lookup-hots (e ∷ᴬ ρ) (there i)   = lookup-hots ρ i

-- A source's step at `q`, a value or a skip, then the rest, which leaves
-- nothing running.
put : ∀ {A} → Pos → Maybe A → Events A → Events A
put q (just a) e = out q a λ where
  .force → e
  .cut   → idle
put q nothing  e = skip q λ where
  .force → e
  .cut   → idle

-- The source steps a defer has still to be fed, put back on its sources.
replay : ∀ {Γ} → List (Notice Γ) → NEnv Γ → NEnv Γ
replay []                  ρ = ρ
replay (notice i q a ∷ ns) ρ = updateAt i (put q a) (replay ns ρ)

-- What a joiner was fed and has not shown, then the rest.
fedᴺ : ∀ {A} → List (Pos × Maybe A) → Events A → Events A
fedᴺ []             e = e
fedᴺ ((q , a) ∷ xs) e = put q a (fedᴺ xs e)

-- A joiner after its feed: told its end, or the source's run, rejoined.
joined : ∀ {Γ A} → A ∈ Γ → Pos → Maybe Pos → NEnv Γ → Events A
joined i p (just c) ρ = end c
joined i p nothing  ρ = M′.rejoin p (lookup ρ i)

-- A node's meaning, each read by its operator's own stream function, a
-- `defer` by the fold's meaning of the program it defers; a rest, its
-- tail run.
mutual
  meaning : ∀ {Γ A} → Node Γ A → NEnv Γ → Events A
  meaning (framesᶜ τ e m)             ρ = M′.frames τ e m
  meaning (burstᶜ τ r i b)            ρ = M′.burst τ r i b
  meaning (ofᶜ p i xs)                ρ = M′.ofᴱ p i xs
  meaning (mapᶜ f c)                  ρ = M′.mapᴱ f (meaning c ρ)
  meaning (scanᶜ f z c)               ρ = M′.scanᴱ f z (meaning c ρ)
  meaning (takeWhileᶜ i p c)          ρ = M′.takeWhileᴱ i p (meaning c ρ)
  meaning (flatMapᶜ op g o ls qs pl)  ρ =
    M′.go (flatOp op) (outerᴺ g o ρ) (states ls ρ) (L.map (λ a → coldᴹ λ q → stateᴺ (g a q) ρ) qs) (cutᴺ pl ρ)
  meaning (joinᶜ i p xs e)            ρ = fedᴺ xs (joined i p e ρ)
  meaning (connectᶜ r b (live s))     ρ = M′.beside r (stateᴺ b (meaning s ρ ∷ᴬ ρ)) (stateᴺ s ρ)
  meaning (connectᶜ r b (ended c t))  ρ = M′.beside r (stateᴺ b (end c ∷ᴬ ρ)) (stateᴺ t ρ)
  meaning (deferᶜ l p ns)             ρ = M′.observe (deferᴰ (⟦ Later.force l ⟧ᴰ (hots (replay ns ρ)))) p
  meaning (endingᶜ p n)               ρ = end p
  meaning (restᶜ n)                   ρ = tailᴱ (cutᴺ n ρ)
  meaning idleᶜ                       ρ = hush
  meaning (unionᶜ x y)                ρ = tailᴱ (cutᴺ x ρ ∪ cutᴺ y ρ)
  meaning (burstingᶜ r t)             ρ = tailᴱ (M′.burstOn r (stateᴺ t ρ))
  meaning (underᶜ (live s) b)         ρ = tailᴱ (cutᴺ b (meaning s ρ ∷ᴬ ρ))
  meaning (underᶜ (ended c t) b)      ρ = tailᴱ (cutᴺ b (end c ∷ᴬ ρ))

  -- What a node leaves running were it cut now.
  cutᴺ : ∀ {Γ A} → Node Γ A → NEnv Γ → Tail
  cutᴺ (mapᶜ f c)                 ρ = cutᴺ c ρ
  cutᴺ (scanᶜ f z c)              ρ = cutᴺ c ρ
  cutᴺ (takeWhileᶜ i p c)         ρ = cutᴺ c ρ
  cutᴺ (flatMapᶜ op g o ls qs pl) ρ = M′.whole (outerᴺ g o ρ) (states ls ρ) (cutᴺ pl ρ)
  cutᴺ (connectᶜ r b (live s))    ρ = M′.burstOn r (stateᴺ s ρ) ∪ cutᴺ b (meaning s ρ ∷ᴬ ρ)
  cutᴺ (connectᶜ r b (ended c t)) ρ = M′.burstOn r (stateᴺ t ρ) ∪ cutᴺ b (end c ∷ᴬ ρ)
  cutᴺ (endingᶜ p n)              ρ = cutᴺ n ρ
  cutᴺ (restᶜ n)                  ρ = cutᴺ n ρ
  cutᴺ (unionᶜ x y)               ρ = cutᴺ x ρ ∪ cutᴺ y ρ
  cutᴺ (burstingᶜ r t)            ρ = M′.burstOn r (stateᴺ t ρ)
  cutᴺ (underᶜ (live s) b)        ρ = cutᴺ b (meaning s ρ ∷ᴬ ρ)
  cutᴺ (underᶜ (ended c t) b)     ρ = cutᴺ b (end c ∷ᴬ ρ)
  cutᴺ _                          ρ = idle

  stateᴺ : ∀ {Γ A} → Node Γ A → NEnv Γ → Events∞ A
  stateᴺ n ρ .force = meaning n ρ
  stateᴺ n ρ .cut   = cutᴺ n ρ

  -- The outer, each element made the lane it opens.
  outer∞ : ∀ {Γ A B} → (A → Pos → Node Γ B) → Node Γ A → NEnv Γ → Events∞ (MonotonicList B)
  outer∞ g o ρ .force = M′.mapᴱ (λ a → coldᴹ λ q → stateᴺ (g a q) ρ) (meaning o ρ)
  outer∞ g o ρ .cut   = cutᴺ o ρ

  outerᴺ : ∀ {Γ A B} → (A → Pos → Node Γ B) → Maybe (Node Γ A) → NEnv Γ → Maybe (Events∞ (MonotonicList B))
  outerᴺ g nothing  ρ = nothing
  outerᴺ g (just o) ρ = just (outer∞ g o ρ)

  states : ∀ {Γ A} → List (Node Γ A) → NEnv Γ → List (Events∞ A)
  states []       ρ = []
  states (c ∷ cs) ρ = stateᴺ c ρ ∷ states cs ρ

-- A program subscribed wherever it is asked.
nodeᴹ : ∀ {Γ A} → Obs Timeline Γ A → NEnv Γ → MonotonicList A
nodeᴹ o ρ = coldᴹ λ p → stateᴺ (subscribe o p) ρ

------------------------------------------------------------------------
-- The meaning is the fold's

start-meaning : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → meaning (startᶜ p m) ρ ≡ M′.start p m
start-meaning p (at zero _ b)    ρ = refl
start-meaning p (at (suc _) _ b) ρ = refl
start-meaning p done             ρ = refl
start-meaning p quiet            ρ = refl

start-cut : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → cutᴺ (startᶜ p m) ρ ≡ idle
start-cut p (at zero _ b)    ρ = refl
start-cut p (at (suc _) _ b) ρ = refl
start-cut p done             ρ = refl
start-cut p quiet            ρ = refl

-- The fold's meaning reads its environment non-expansively.
⟦⟧-ne : ∀ {Γ A k} (o : Obs Timeline Γ A) {ρ σ : DenEnv Γ} → EnvAgree k ρ σ → ⟦ o ⟧ᴰ ρ ≈[ k ] ⟦ o ⟧ᴰ σ
⟦⟧-ne {k = k} o {ρ} {σ} e = ≈ₖ-trans (from k o ρ) (≈ₖ-trans (approx-ne k o e) (toward k o σ))

-- A program subscribed is the fold's meaning, for as long as the
-- environments agree.  Each operator's state is its fold's field by
-- field, so each clause re-reads the fold's agreement at its own.
subscribed : ∀ {Γ A k} (o : Obs Timeline Γ A) {ρ : NEnv Γ} {σ : DenEnv Γ} → EnvAgree k (hots ρ) σ → nodeᴹ o ρ ≈[ k ] ⟦ o ⟧ᴰ σ
subscribed {k = k} (cold c) {ρ} {σ} e = ≈ₖ-trans {y = M′.coldᴰ c} (agrees
  (λ p → subst (λ x → M′.Agreeᵀ _ x idle) (sym (start-cut p (timelineAt c p) ρ)) (agreeᵀ-refl _ _))
  (λ p → subst (λ x → Agree _ x (M′.start p (timelineAt c p))) (sym (start-meaning p (timelineAt c p) ρ)) (agree-refl _ _)))
  (≈ₖ-sym (C.coldᶜ c σ k))
subscribed {k = k} empty             {σ = σ} e = agrees (agreeᵀ h) (agree h)
  where h = ≈ₖ-sym (C.emptyᶜ σ k)
subscribed {k = k} (of xs)           {σ = σ} e = agrees (agreeᵀ h) (agree h)
  where h = ≈ₖ-sym (C.ofᶜ xs σ k)
subscribed {k = k} (map f s)         {σ = σ} e = agrees (agreeᵀ h) (agree h)
  where h = ≈ₖ-trans (mapᴰ-ne f (subscribed s e)) (≈ₖ-sym (C.mapᶜ f s σ k))
subscribed {k = k} (scan f z s)      {σ = σ} e = agrees (agreeᵀ h) (agree h)
  where h = ≈ₖ-trans (scanᴰ-ne f z (subscribed s e)) (≈ₖ-sym (C.scanᶜ f z s σ k))
subscribed {k = k} (takeWhile i p s) {σ = σ} e = agrees (agreeᵀ h) (agree h)
  where h = ≈ₖ-trans (takeWhileᴰ-ne i p (subscribed s e)) (≈ₖ-sym (C.takeWhileᶜ i p s σ k))
subscribed {k = k} (flatMap op f s)  {ρ} {σ} e = agrees
  (λ p → agreeᵀ-trans (whole-ne (alike p) []ᴸ (agreeᵀ-refl _ idle)) (agreeᵀ h p))
  (λ p → agree-trans (go-ne (flatOp op) (alike p) []ᴸ []ᑫ (agreeᵀ-refl _ idle)) (agree h p))
  where
    F = λ a → nodeᴹ (f a) ρ
    h = ≈ₖ-trans (flatMapᴰ-ne (flatOp op) {f = F} (subscribed s e) λ a → subscribed (f a) e) (≈ₖ-sym (C.flatMapᶜ op f s σ k))
    alike = λ p → liveᴼ {e = outer∞ (λ a q → subscribe (f a) q) (subscribe s p) ρ} {M′.enter (M′.mapᴰ F (nodeᴹ s ρ)) p}
      (agreeᵀ-refl _ _) (mapᴱ-neᴹ (λ a → agrees (λ q → agreeᵀ-refl _ _) (λ q → agree-refl _ _)) (agree-refl _ _))
subscribed {k = k} (connect s b)     {ρ} {σ} e = ≈ₖ-trans (agrees
  (λ p → ∪-ne (burstOn-ne (p ++ [ ix 1 ]) {stateᴺ (subscribe s (p ++ [ ix 1 ])) ρ} {M′.enter (⟦ s ⟧ᴰ σ) (p ++ [ ix 1 ])}
                (entered src (p ++ [ ix 1 ])))
              (Agreeˢ.cutˢ (bodies p)))
  (λ p → beside-ne (p ++ [ ix 1 ]) (bodies p) (entered src (p ++ [ ix 1 ]))))
  (≈ₖ-sym (C.connectᶜ s b σ k))
  where src = subscribed s e
        bodies = λ p → entered (subscribed b (hot-ne (agree src (p ++ [ ix 1 ])) ∷ᵉ e)) (p ++ [ ix 0 ])
subscribed {k = k} (connected i)     {ρ} {σ} e = ≈ₖ-trans (agrees (agreeᵀ h) (agree h)) (≈ₖ-sym (C.connectedᶜ i σ k))
  where h = subst (λ r → r ≈[ k ] lookup σ i) (lookup-hots ρ i) (lookup-agree e i)
subscribed {k = k} (defer l)         {ρ} {σ} e = ≈ₖ-trans (agrees (λ p → agreeᵀ-refl _ _) (λ p → agree-refl _ _))
  (≈ₖ-trans (≈ₖ-pred (deferᴰ-contractive (⟦⟧-ne (Later.force l) e))) (≈ₖ-sym (C.deferᶜ l σ k)))
