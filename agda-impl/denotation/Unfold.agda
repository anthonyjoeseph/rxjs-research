{-# OPTIONS --guardedness #-}

-- A RUN IN PROGRESS, AS A CONFIGURATION.  A subscription is an inductive
-- configuration: one node per operator still running, a `defer` left
-- unexpanded until its turn.  It has two readings.
--
-- ITS MEANING (`meaning`, `⟦_⟧`): each node read by its operator's own
-- stream function in `MonotonicList`, the source of a `connect` handed to
-- its joiners whole, as `connectᴰ` hands it.  So a program subscribed is
-- `Denote`'s approximant (`subscribed`), and its meaning the fold's
-- (`denoted`).
--
-- ITS STEPPER (`step`, `unfold`), the machine's proof device: `step`
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
-- DEAD ROUTE: the meaning by guarded corecursion over the tree directly, the
--   `defer` clause a `skip` whose tail is `⟦ force l ⟧`.  Agda refuses it:
--   every other clause puts its recursive call under a stream function
--   (`mapᴱ`, `go`, `rejoin`), which could strip the guard, so the call
--   through `defer` is never seen guarded.
module denotation.Unfold where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Level using (lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
import Data.List as L

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList using (MonotonicList; Events; Events∞; out; skip; end; hush; Time; Pos; ix; last; tick; _<ᵖ_;
  Timeline; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close) renaming (sub to subᴾ; cold to coldᴹ)
import denotation.MonotonicList as M
open import denotation.MonotonicList using (Agree; agree-refl; _≈[_]_; _≈_; agrees; agree; Settling; lub; lub-limit; ≈ₖ-refl; ≈ₖ-sym;
  ≈ₖ-trans; ≈ₖ-pred; hot; deferᴰ; ⊥ᴰ)
open import denotation.Denote using (DenEnv; flatOp; approx) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (EnvAgree; []ᵉ; _∷ᵉ_; lookup-agree; deferᴰ-contractive; settles; toward)
open import denotation.NonExpansive using (mapᴰ-ne; scanᴰ-ne; takeWhileᴰ-ne; flatMapᴰ-ne; beside-ne; hot-ne)

open Events∞

------------------------------------------------------------------------
-- Configurations

mutual
  data Node : List Set → Set → Set₁ where
    framesᶜ    : ∀ {Γ A t} → Time → Pos → From A t → Node Γ A
    burstᶜ     : ∀ {Γ A t} → Time → Pos → ℕ → Frame A t → Node Γ A
    endᶜ       : ∀ {Γ A} → Pos → Node Γ A
    ofᶜ        : ∀ {Γ A} → Pos → ℕ → List A → Node Γ A
    mapᶜ       : ∀ {Γ A B} → (A → B) → Node Γ A → Node Γ B
    scanᶜ      : ∀ {Γ A B} → (B → A → B) → B → Node Γ A → Node Γ B
    takeWhileᶜ : ∀ {Γ A} → Bool → (A → Bool) → Node Γ A → Node Γ A
    flatMapᶜ   : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Maybe (Node Γ A) → List (Node Γ B) → List A → Node Γ B
    -- Joined to connect `i` at `p`: what it has been fed and not yet
    -- shown, and where it ends once its source has.
    joinᶜ      : ∀ {Γ A} → A ∈ Γ → Pos → List (Pos × A) → Maybe Pos → Node Γ A
    -- A connect's body, and its source while it runs, else where it ended.
    connectᶜ   : ∀ {Γ A B} → Node (A ∷ Γ) B → Source Γ A → Node Γ B
    deferᶜ     : ∀ {Γ A} → Later Timeline Γ A → Pos → Node Γ A

  data Source (Γ : List Set) (A : Set) : Set₁ where
    live  : Node Γ A → Source Γ A
    ended : Pos → Source Γ A

-- The connects in scope, innermost first, each as its source's configuration.
data Srcs : List Set → Set₁ where
  []  : Srcs []
  _∷_ : ∀ {Γ A} → Node Γ A → Srcs Γ → Srcs (A ∷ Γ)

wrap : ∀ {Γ A} → Srcs Γ → Node Γ A → Node [] A
wrap []      n = n
wrap (s ∷ δ) n = wrap δ (connectᶜ n (live s))

------------------------------------------------------------------------
-- Subscribing

startᶜ : ∀ {Γ A} → Pos → From A 0 → Node Γ A
startᶜ p (at zero _ b) = burstᶜ (tick p) p 0 b
startᶜ p m             = framesᶜ (tick p) (p ++ [ last ]) m

subscribe : ∀ {Γ A} → Obs Timeline Γ A → Pos → Node Γ A
subscribe (cold c)          p = startᶜ p (lower c)
subscribe empty             p = endᶜ (p ++ [ last ])
subscribe (of xs)           p = ofᶜ p 0 xs
subscribe (map f s)         p = mapᶜ f (subscribe s p)
subscribe (scan f z s)      p = scanᶜ f z (subscribe s p)
subscribe (takeWhile i q s) p = takeWhileᶜ i q (subscribe s p)
subscribe (flatMap op f s)  p = flatMapᶜ op (λ a q → subscribe (f a) q) (just (subscribe s p)) [] []
subscribe (connect s b)     p = connectᶜ (subscribe b (p ++ [ ix 0 ])) (live (subscribe s (p ++ [ ix 1 ])))
subscribe (connected i)     p = joinᶜ i p [] nothing
subscribe (defer l)         p = deferᶜ l p

------------------------------------------------------------------------
-- A connect's source, delivered to its joiners

same? : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → B ∈ Γ → Maybe (A ≡ B)
same? (here refl) (here refl) = just refl
same? (there i)   (there j)   = same? i j
same? _           _           = nothing

-- A joiner of connect `i` is fed a value at `q` if it joined before `q`.
fed : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → A → B ∈ Γ → Pos → List (Pos × B) → Maybe (A ≡ B) → List (Pos × B)
fed i q a j p xs (just refl) = if p <ᵖ q then xs ++ [ q ++ [ subᴾ p ] , a ] else xs
fed i q a j p xs nothing     = xs

-- And told where it ends, once: at the source's end if it joined before
-- it, else at once.
told : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → B ∈ Γ → Pos → Maybe Pos → Maybe (A ≡ B) → Maybe Pos
told i c j p nothing  (just refl) = just (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ])
told i c j p e        _           = e

mutual
  feed : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → A → Node Γ B → Node Γ B
  feed i q a (mapᶜ f c)              = mapᶜ f (feed i q a c)
  feed i q a (scanᶜ f z c)           = scanᶜ f z (feed i q a c)
  feed i q a (takeWhileᶜ b p c)      = takeWhileᶜ b p (feed i q a c)
  feed i q a (flatMapᶜ op g o ls qs) = flatMapᶜ op g (feedᴹ i q a o) (feedᴸ i q a ls) qs
  feed i q a (joinᶜ j p xs e)        = joinᶜ j p (fed i q a j p xs (same? i j)) e
  feed i q a (connectᶜ b s)          = connectᶜ (feed (there i) q a b) (feedˢ i q a s)
  feed i q a c                       = c

  feedᴹ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → A → Maybe (Node Γ B) → Maybe (Node Γ B)
  feedᴹ i q a nothing  = nothing
  feedᴹ i q a (just c) = just (feed i q a c)

  feedᴸ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → A → List (Node Γ B) → List (Node Γ B)
  feedᴸ i q a []       = []
  feedᴸ i q a (c ∷ cs) = feed i q a c ∷ feedᴸ i q a cs

  feedˢ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → A → Source Γ B → Source Γ B
  feedˢ i q a (live s)  = live (feed i q a s)
  feedˢ i q a (ended c) = ended c

mutual
  shut : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Node Γ B → Node Γ B
  shut i c (mapᶜ f n)              = mapᶜ f (shut i c n)
  shut i c (scanᶜ f z n)           = scanᶜ f z (shut i c n)
  shut i c (takeWhileᶜ b p n)      = takeWhileᶜ b p (shut i c n)
  shut i c (flatMapᶜ op g o ls qs) = flatMapᶜ op g (shutᴹ i c o) (shutᴸ i c ls) qs
  shut i c (joinᶜ j p xs e)        = joinᶜ j p xs (told i c j p e (same? i j))
  shut i c (connectᶜ b s)          = connectᶜ (shut (there i) c b) (shutˢ i c s)
  shut i c n                       = n

  shutᴹ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Maybe (Node Γ B) → Maybe (Node Γ B)
  shutᴹ i c nothing  = nothing
  shutᴹ i c (just n) = just (shut i c n)

  shutᴸ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → List (Node Γ B) → List (Node Γ B)
  shutᴸ i c []       = []
  shutᴸ i c (n ∷ ns) = shut i c n ∷ shutᴸ i c ns

  shutˢ : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → Pos → Source Γ B → Source Γ B
  shutˢ i c (live s)  = live (shut i c s)
  shutˢ i c (ended e) = ended e

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

taking : ∀ {Γ A} → Bool → (A → Bool) → Pos → A → Node Γ A → Bool → Step Γ A
taking i     p k a c true  = outˢ k a (takeWhileᶜ i p c)
taking true  p k a c false = outˢ k a (endᶜ (k ++ [ last ]))
taking false p k a c false = endˢ (k ++ [ last ])

takeWhileˢ : ∀ {Γ A} → Bool → (A → Bool) → Step Γ A → Step Γ A
takeWhileˢ i p (outˢ k a c) = taking i p k a c (p a)
takeWhileˢ i p (skipˢ k c)  = skipˢ k (takeWhileᶜ i p c)
takeWhileˢ i p (endˢ k)     = endˢ k
takeWhileˢ i p hushˢ        = hushˢ

joinˢ : ∀ {Γ A} → A ∈ Γ → Pos → List (Pos × A) → Maybe Pos → Step Γ A
joinˢ i p ((q , a) ∷ xs) e        = outˢ q a (joinᶜ i p xs e)
joinˢ i p []             (just c) = endˢ c
joinˢ i p []             nothing  = hushˢ

-- The body stepped, its source carried along.
bodyˢ : ∀ {Γ A B} → Source Γ A → Step (A ∷ Γ) B → Step Γ B
bodyˢ s (outˢ k a b) = outˢ k a (connectᶜ b s)
bodyˢ s (skipˢ k b)  = skipˢ k (connectᶜ b s)
bodyˢ s (endˢ c)     = endˢ c
bodyˢ s hushˢ        = hushˢ

-- Past its source's end, every joiner the body makes is told so at once.
shutˢᵗ : ∀ {Γ A B} → Pos → Step (A ∷ Γ) B → Step Γ B
shutˢᵗ c (outˢ k a b) = outˢ k a (connectᶜ (shut (here refl) c b) (ended c))
shutˢᵗ c (skipˢ k b)  = skipˢ k (connectᶜ (shut (here refl) c b) (ended c))
shutˢᵗ c (endˢ e)     = endˢ e
shutˢᵗ c hushˢ        = hushˢ

beforeˢ : ∀ {Γ B} → Pos → Step Γ B → Bool
beforeˢ q (outˢ k _ _) = q <ᵖ k
beforeˢ q (skipˢ k _)  = q <ᵖ k
beforeˢ q (endˢ k)     = q <ᵖ k
beforeˢ q hushˢ        = true

-- The source's next event, when it comes before the body's.
sourceˢ : ∀ {Γ A B} → Node (A ∷ Γ) B → Step (A ∷ Γ) B → Node Γ A → Step Γ A → Step Γ B
sourceˢ b sb s (outˢ q a s′) =
  if beforeˢ (q ++ [ ix 0 ]) sb then skipˢ (q ++ [ ix 0 ]) (connectᶜ (feed (here refl) q a b) (live s′)) else bodyˢ (live s) sb
sourceˢ b sb s (skipˢ q s′)  =
  if beforeˢ (q ++ [ ix 0 ]) sb then skipˢ (q ++ [ ix 0 ]) (connectᶜ b (live s′)) else bodyˢ (live s) sb
sourceˢ b sb s (endˢ c)      =
  if beforeˢ (c ++ [ ix 0 ]) sb then skipˢ (c ++ [ ix 0 ]) (connectᶜ (shut (here refl) c b) (ended c)) else bodyˢ (live s) sb
sourceˢ b sb s hushˢ         = bodyˢ (live s) sb

-- A lane arriving, subscribed at `q`.
admit : ∀ {Γ} {A B : Set} → T.FlatOp → (A → Pos → Node Γ B) → Pos → A → List (Node Γ B) → List A → List (Node Γ B) × List A
admit (T.mergeᶠ nothing)  g q a ls       qs = g a q ∷ ls , qs
admit (T.mergeᶠ (just n)) g q a ls       qs = if length ls <ᵇ n then (g a q ∷ ls , qs) else (ls , qs ++ [ a ])
admit T.switchᶠ           g q a ls       qs = [ g a q ] , qs
admit T.exhaustᶠ          g q a []       qs = [ g a q ] , qs
admit T.exhaustᶠ          g q a (l ∷ ls) qs = l ∷ ls , qs

data Earliest (Γ : List Set) (B : Set) : Set₁ where
  none  : Earliest Γ B
  found : Pos → List (Node Γ B) → Node Γ B → Step Γ B → List (Node Γ B) → Earliest Γ B

pick : ∀ {Γ B} → Node Γ B → Step Γ B → List (Node Γ B) → Maybe Pos → Earliest Γ B → Earliest Γ B
pick l s ls nothing  none                  = none
pick l s ls nothing  (found k bs c sc as)  = found k (l ∷ bs) c sc as
pick l s ls (just k) none                  = found k [] l s ls
pick l s ls (just k) (found k′ bs c sc as) = if k <ᵖ k′ then found k [] l s ls else found k′ (l ∷ bs) c sc as

outerˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Step Γ A → List (Node Γ B) → List A → Step Γ B
outerˢ op g (outˢ q a o) ls qs with admit op g (q ++ [ ix 1 ]) a ls qs
... | ls′ , qs′ = skipˢ (q ++ [ ix 0 ]) (flatMapᶜ op g (just o) ls′ qs′)
outerˢ op g (skipˢ q o)  ls qs = skipˢ q (flatMapᶜ op g (just o) ls qs)
outerˢ op g (endˢ c)     [] [] = endˢ c
outerˢ op g (endˢ c)     ls qs = skipˢ c (flatMapᶜ op g nothing ls qs)
outerˢ op g hushˢ        ls qs = hushˢ

laneˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Maybe (Node Γ A) → List (Node Γ B) → Step Γ B → List (Node Γ B) → List A → Step Γ B
laneˢ op g o       bs (outˢ k b c) as qs       = outˢ k b (flatMapᶜ op g o (bs ++ c ∷ as) qs)
laneˢ op g o       bs (skipˢ k c)  as qs       = skipˢ k (flatMapᶜ op g o (bs ++ c ∷ as) qs)
laneˢ op g o       bs (endˢ c)     as (a ∷ qs) = skipˢ (c ++ [ ix 0 ]) (flatMapᶜ op g o (g a (c ++ [ ix 1 ]) ∷ bs ++ as) qs)
laneˢ op g nothing [] (endˢ c)     [] []       = endˢ c
laneˢ op g o       bs (endˢ c)     as []       = skipˢ c (flatMapᶜ op g o (bs ++ as) [])
laneˢ op g o       bs hushˢ        as qs       = hushˢ

raceˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Node Γ A → Step Γ A → Maybe Pos → Pos → List (Node Γ B) → Node Γ B → Step Γ B
      → List (Node Γ B) → List A → Step Γ B
raceˢ op g o so nothing   k bs l s as qs = laneˢ op g (just o) bs s as qs
raceˢ op g o so (just k′) k bs l s as qs =
  if k′ <ᵖ k then outerˢ op g so (bs ++ l ∷ as) qs else laneˢ op g (just o) bs s as qs

mutual
  step : ∀ {Γ A} → Node Γ A → Step Γ A
  step (framesᶜ τ e m)          = framesˢ τ e m
  step (burstᶜ τ r i b)         = burstˢ τ r i b
  step (endᶜ p)                 = endˢ p
  step (ofᶜ p i xs)             = ofˢ p i xs
  step (mapᶜ f c)               = mapˢ f (step c)
  step (scanᶜ f z c)            = scanˢ f z (step c)
  step (takeWhileᶜ i p c)       = takeWhileˢ i p (step c)
  step (flatMapᶜ op g o ls qs)  = goˢ op g o ls qs (earliest ls)
  step (joinᶜ i p xs e)         = joinˢ i p xs e
  step (connectᶜ b (live s))    = sourceˢ b (step b) s (step s)
  step (connectᶜ b (ended c))   = shutˢᵗ c (step b)
  step (deferᶜ l p)             = skipˢ (p ++ [ ix 0 ]) (subscribe (Later.force l) (p ++ [ ix 1 ]))

  earliest : ∀ {Γ B} → List (Node Γ B) → Earliest Γ B
  earliest []       = none
  earliest (l ∷ ls) = pick l s ls (headˢ s) (earliest ls)
    where s = step l

  goˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → Node Γ B) → Maybe (Node Γ A) → List (Node Γ B) → List A → Earliest Γ B → Step Γ B
  goˢ op g nothing  ls qs none                 = hushˢ
  goˢ op g (just o) ls qs none                 = outerˢ op g (step o) ls qs
  goˢ op g nothing  ls qs (found k bs l s as)  = laneˢ op g nothing bs s as qs
  goˢ op g (just o) ls qs (found k bs l s as)  = raceˢ op g o so (headˢ so) k bs l s as qs
    where so = step o

------------------------------------------------------------------------
-- The stepper's run

mutual
  unfold : ∀ {Γ A} → Node Γ A → Events A
  unfold c = shown (step c)

  shown : ∀ {Γ A} → Step Γ A → Events A
  shown (outˢ k a c) = out k a λ where .force → unfold c
  shown (skipˢ k c)  = skip k λ where .force → unfold c
  shown (endˢ k)     = end k
  shown hushˢ        = hush

⟦_⟧ˢ : ∀ {Γ A} → Obs Timeline Γ A → Srcs Γ → MonotonicList A
⟦ o ⟧ˢ δ = coldᴹ λ p → unfold (wrap δ (subscribe o p))

------------------------------------------------------------------------
-- The meaning: each node read by its operator's own stream function

-- Each connect in scope, as its source's run from where the source stands.
NEnv : List Set → Set₁
NEnv = All Events

-- What a joiner was fed and has not shown, then the rest.
fedᴺ : ∀ {A} → List (Pos × A) → Events A → Events A
fedᴺ []             e = e
fedᴺ ((q , a) ∷ xs) e = out q a λ where .force → fedᴺ xs e

-- A joiner after its feed: told its end, or the source's run, rejoined.
joined : ∀ {Γ A} → A ∈ Γ → Pos → Maybe Pos → NEnv Γ → Events A
joined i p (just c) ρ = end c
joined i p nothing  ρ = M.rejoin p 0 (lookup ρ i)

outerᴺ : ∀ {A B} → (A → MonotonicList B) → Maybe (Events A) → Maybe (Events (MonotonicList B))
outerᴺ f nothing  = nothing
outerᴺ f (just e) = just (M.mapᴱ f e)

-- APPROXIMANT n of a node's meaning: `Denote`'s approximant, for a
-- configuration, every path through more than n `defer`s cut off at ⊥ᴰ.
-- Lexicographic on (n , node), as `approx` is.
mutual
  meaning : ∀ {Γ A} → ℕ → Node Γ A → NEnv Γ → Events A
  meaning n       (framesᶜ τ e m)         ρ = M.frames τ e m
  meaning n       (burstᶜ τ r i b)        ρ = M.burst τ r i b
  meaning n       (endᶜ p)                ρ = end p
  meaning n       (ofᶜ p i xs)            ρ = M.ofᴱ p i xs
  meaning n       (mapᶜ f c)              ρ = M.mapᴱ f (meaning n c ρ)
  meaning n       (scanᶜ f z c)           ρ = M.scanᴱ f z (meaning n c ρ)
  meaning n       (takeWhileᶜ i p c)      ρ = M.takeWhileᴱ i p (meaning n c ρ)
  meaning n       (flatMapᶜ op g o ls qs) ρ =
    M.go (flatOp op) (outerᴺ (λ a → coldᴹ λ q → meaning n (g a q) ρ) (meaningᴹ n o ρ)) (meanings n ls ρ)
         (L.map (λ a → coldᴹ λ q → meaning n (g a q) ρ) qs)
  meaning n       (joinᶜ i p xs e)        ρ = fedᴺ xs (joined i p e ρ)
  meaning n       (connectᶜ b (live s))   ρ = M.beside (meaning n b (meaning n s ρ ∷ᴬ ρ)) (meaning n s ρ)
  meaning n       (connectᶜ b (ended c))  ρ = meaning n b (end c ∷ᴬ ρ)
  meaning zero    (deferᶜ l p)            ρ = M.observe ⊥ᴰ p
  meaning (suc n) (deferᶜ l p)            ρ = M.observe (deferᴰ (nodeᴹ n (Later.force l) ρ)) p

  meaningᴹ : ∀ {Γ A} → ℕ → Maybe (Node Γ A) → NEnv Γ → Maybe (Events A)
  meaningᴹ n nothing  ρ = nothing
  meaningᴹ n (just c) ρ = just (meaning n c ρ)

  meanings : ∀ {Γ A} → ℕ → List (Node Γ A) → NEnv Γ → List (Events A)
  meanings n []       ρ = []
  meanings n (c ∷ cs) ρ = meaning n c ρ ∷ meanings n cs ρ

  -- A program subscribed wherever it is asked.
  nodeᴹ : ∀ {Γ A} → ℕ → Obs Timeline Γ A → NEnv Γ → MonotonicList A
  nodeᴹ n o ρ = coldᴹ λ p → meaning n (subscribe o p) ρ

-- THE MEANING: the limit of the approximants.
⟦_⟧ : ∀ {Γ A} → Obs Timeline Γ A → Srcs Γ → MonotonicList A
⟦ o ⟧ δ = lub λ n → coldᴹ λ p → meaning n (wrap δ (subscribe o p)) []ᴬ

------------------------------------------------------------------------
-- The meaning is the fold's

-- A joiner's handle is its source's run, made hot.
hots : ∀ {Γ} → NEnv Γ → DenEnv Γ
hots []ᴬ      = []ᴬ
hots (e ∷ᴬ ρ) = hot e ∷ᴬ hots ρ

lookup-hots : ∀ {Γ A} (ρ : NEnv Γ) (i : A ∈ Γ) → lookup (hots ρ) i ≡ hot (lookup ρ i)
lookup-hots (e ∷ᴬ ρ) (here refl) = refl
lookup-hots (e ∷ᴬ ρ) (there i)   = lookup-hots ρ i

start-meaning : ∀ {Γ A} n p (m : From A 0) (ρ : NEnv Γ) → meaning n (startᶜ p m) ρ ≡ M.start p m
start-meaning n p (at zero _ b)    ρ = refl
start-meaning n p (at (suc _) _ b) ρ = refl
start-meaning n p done             ρ = refl
start-meaning n p quiet            ρ = refl

-- Approximant n of a program's meaning is the fold's, for as long as the
-- environments agree.
subscribed : ∀ {Γ A k} n (o : Obs Timeline Γ A) {ρ : NEnv Γ} {σ : DenEnv Γ} → EnvAgree k (hots ρ) σ → nodeᴹ n o ρ ≈[ k ] approx n o σ
subscribed n       (cold c)          {ρ} e = agrees λ p →
  subst (λ x → Agree _ x (M.start p (lower c))) (sym (start-meaning n p (lower c) ρ)) (agree-refl _ _)
subscribed n       empty             e = ≈ₖ-refl _
subscribed n       (of xs)           e = ≈ₖ-refl _
subscribed n       (map f s)         e = mapᴰ-ne f (subscribed n s e)
subscribed n       (scan f z s)      e = scanᴰ-ne f z (subscribed n s e)
subscribed n       (takeWhile i p s) e = takeWhileᴰ-ne i p (subscribed n s e)
subscribed n       (flatMap op f s)  {ρ} e =
  flatMapᴰ-ne (flatOp op) {f = λ a → nodeᴹ n (f a) ρ} (subscribed n s e) λ a → subscribed n (f a) e
subscribed n       (connect s b)     e = agrees λ p →
  beside-ne (agree (subscribed n b (hot-ne (agree src (p ++ [ ix 1 ])) ∷ᵉ e)) (p ++ [ ix 0 ])) (agree src (p ++ [ ix 1 ]))
  where src = subscribed n s e
subscribed {k = k} n (connected i) {ρ} {σ} e =
  agrees λ p → agree (subst (λ r → r ≈[ k ] lookup σ i) (lookup-hots ρ i) (lookup-agree e i)) p
subscribed zero    (defer l)         e = ≈ₖ-refl _
subscribed (suc n) (defer l)         e = ≈ₖ-pred (deferᴰ-contractive (subscribed n (Later.force l) e))

-- The approximants settle, as the fold's do, and their limit is the
-- fold's meaning.
denoted : ∀ {A} (o : Obs Timeline [] A) → ⟦ o ⟧ [] ≈ ⟦ o ⟧ᴰ []ᴬ
denoted o k = ≈ₖ-trans (≈ₖ-sym (lub-limit {c = λ n → nodeᴹ n o []ᴬ} settling k)) (≈ₖ-trans (subscribed k o []ᵉ) (toward k o []ᴬ))
  where
    settling : Settling (λ n → nodeᴹ n o []ᴬ)
    settling n = ≈ₖ-trans (subscribed n o []ᵉ) (≈ₖ-trans (settles o []ᴬ n) (≈ₖ-sym (subscribed (suc n) o []ᵉ)))
