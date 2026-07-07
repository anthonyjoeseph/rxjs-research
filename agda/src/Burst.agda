-- BURST BATCHING: the ratified spec change — one subscribe() call is one
-- root cause, so the entire synchronous subscription frame is ONE instant.
--
-- The technical device is the subscription-time-parameterized denotation:
-- ⟦ e ⟧ env t is the observable obtained by subscribing e at time t. Cold
-- values (`of`) emit at whatever subscription time they are handed — they
-- no longer own a private origin instant — and `concat` hands its second
-- argument the first argument's close time. For a static (source-free)
-- program every close IS the subscription instant, so the whole frame
-- lands at a single Time, and batchSpec delivers it as ONE batch:
--
--   merge(of(1), of(2))      ↦ [ [1, 2] ]        (merge-of-example)
--   concat(of(1,2), of(3))   ↦ [ [1, 2, 3] ]     (concat-of-example)
--
-- Root sources stay hot and async: subscribing at t sees only emissions
-- strictly after t, and their events keep distinct times, so the diamond
-- anchor law transfers unchanged (diamond-burst).
--
-- This module supersedes the per-occurrence origin discipline of Exp.agda
-- (ofE's (0 , origin) instants; of-batch; distinct-origins) — kept there
-- as the record of the old spec.
module Burst where

open import Prelude
open import Time
open import TimedObs
open import Sorting
open import Obs
open import Diamond

Val : Set
Val = ℕ

data BExp : Set where
  srcB    : ℕ → BExp                  -- a root (hot, async) source, by index
  emptyB  : BExp
  ofB     : List Val → BExp           -- NO origin: colds don't own an instant
  mapB    : (Val → Val) → BExp → BExp
  takeB   : ℕ → BExp → BExp
  mergeB  : BExp → BExp → BExp
  concatB : BExp → BExp → BExp

Env : Set
Env = ℕ → Obs Val

-- the close of `take n` when the subscription happened at t: the time of
-- the nth emission if it exists, the source's close if it has fewer, and
-- the subscription instant itself for take 0 (which completes immediately)
takeCloseB : {A : Set} → Time → ℕ → TimedObs A → Time → Time
takeCloseB t zero          _               _ = t
takeCloseB t (suc n)       []              c = c
takeCloseB t (suc zero)    ((t′ , _) ∷ _)  _ = t′
takeCloseB t (suc (suc n)) (_ ∷ xs)        c = takeCloseB t (suc n) xs c

-- the denotation: subscribe e at time t. Note concat needs no filterAfter
-- of its own — the hot filtering lives at srcB, and colds legitimately
-- emit AT the pivot (that is the burst rule).
⟦_⟧ : BExp → Env → Time → Obs Val
⟦ srcB i ⟧ env t =
  obs (filterAfter t (emits (env i))) (timeMax t (close (env i)))
⟦ emptyB ⟧ env t = obs [] t
⟦ ofB vs ⟧ env t = obs (map (λ v → (t , v)) vs) t
⟦ mapB f e ⟧ env t = mapO f (⟦ e ⟧ env t)
⟦ takeB n e ⟧ env t =
  obs (takeT n (emits (⟦ e ⟧ env t)))
      (takeCloseB t n (emits (⟦ e ⟧ env t)) (close (⟦ e ⟧ env t)))
⟦ mergeB a b ⟧ env t = mergeO (⟦ a ⟧ env t) (⟦ b ⟧ env t)
⟦ concatB a b ⟧ env t =
  obs (emits (⟦ a ⟧ env t) ++ emits (⟦ b ⟧ env (close (⟦ a ⟧ env t))))
      (close (⟦ b ⟧ env (close (⟦ a ⟧ env t))))

-- well-formedness relative to a subscription time: emissions start no
-- earlier than the subscription, the close is no earlier than the
-- subscription, and emissions happen before the close
record WFAt {A : Set} (t : Time) (o : Obs A) : Set where
  constructor wfAt
  field
    sortedAt  : SortedFrom t (emits o)
    closeAt   : timeLeq t (close o) ≡ true
    boundedAt : BoundedBy (close o) (emits o)
open WFAt public

-- take machinery: the takeCloseB analogues of the Sorting lemmas ---------------

head-leq-takeCloseB : {A : Set} (t₀ : Time) (n : ℕ) (xs : TimedObs A)
  (c t : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeCloseB t₀ (suc n) xs c) ≡ true
head-leq-takeCloseB t₀ n       []              c t _          _           tc = tc
head-leq-takeCloseB t₀ zero    ((t′ , v) ∷ xs) c t (sf∷ le _) _           _  = le
head-leq-takeCloseB t₀ (suc n) ((t′ , v) ∷ xs) c t (sf∷ le s) (bb∷ lc bx) _  =
  timeLeq-trans t t′ _ le (head-leq-takeCloseB t₀ n xs c t′ s bx lc)

takeB-closeAt : {A : Set} (t : Time) (n : ℕ) (xs : TimedObs A) (c : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeCloseB t n xs c) ≡ true
takeB-closeAt t zero    xs c _ _ _  = timeLeq-refl t
takeB-closeAt t (suc n) xs c s b tc = head-leq-takeCloseB t n xs c t s b tc

take-boundedB : {A : Set} (t₀ : Time) {b : Time} (n : ℕ) (xs : TimedObs A)
  (c : Time)
  → SortedFrom b xs → BoundedBy c xs
  → BoundedBy (takeCloseB t₀ n xs c) (takeT n xs)
take-boundedB t₀ zero          xs             c _          _           = bb[]
take-boundedB t₀ (suc n)       []             c _          _           = bb[]
take-boundedB t₀ (suc zero)    ((t , v) ∷ xs) c _          _           =
  bb∷ (timeLeq-refl t) bb[]
take-boundedB t₀ (suc (suc n)) ((t , v) ∷ xs) c (sf∷ le s) (bb∷ tc bx) =
  bb∷ (head-leq-takeCloseB t₀ n xs c t s bx tc)
      (take-boundedB t₀ (suc n) xs c s bx)

-- ANY program, subscribed at ANY time, is well-formed relative to that
-- subscription time -----------------------------------------------------------

denote-wfAt : (e : BExp) (env : Env)
  → ((i : ℕ) → WF (env i))
  → (t : Time) → WFAt t (⟦ e ⟧ env t)
denote-wfAt (srcB i) env wfe t =
  wfAt (filterAfter-from t (emits (env i)) (sorted (wfe i)))
       (timeMax-left t (close (env i)))
       (boundedBy-weaken (timeMax-right t (close (env i)))
         (filterAfter-bounded t (emits (env i)) (bounded (wfe i))))
denote-wfAt emptyB env wfe t = wfAt sf[] (timeLeq-refl t) bb[]
denote-wfAt (ofB vs) env wfe t =
  wfAt (const-sortedFrom t vs) (timeLeq-refl t) (const-bounded t vs)
denote-wfAt (mapB f e) env wfe t with denote-wfAt e env wfe t
... | wfAt s c b =
  wfAt (mapT-sortedFrom f (emits (⟦ e ⟧ env t)) s)
       c
       (mapT-bounded f (emits (⟦ e ⟧ env t)) b)
denote-wfAt (takeB n e) env wfe t with denote-wfAt e env wfe t
... | wfAt s c b =
  wfAt (take-sortedFrom n (emits (⟦ e ⟧ env t)) s)
       (takeB-closeAt t n (emits (⟦ e ⟧ env t)) (close (⟦ e ⟧ env t)) s b c)
       (take-boundedB t n (emits (⟦ e ⟧ env t)) (close (⟦ e ⟧ env t)) s b)
denote-wfAt (mergeB a b) env wfe t
  with denote-wfAt a env wfe t | denote-wfAt b env wfe t
... | wfAt s₁ c₁ b₁ | wfAt s₂ c₂ b₂ =
  wfAt (merge-sortedFrom (emits (⟦ a ⟧ env t)) (emits (⟦ b ⟧ env t)) s₁ s₂)
       (timeLeq-trans t (close (⟦ a ⟧ env t)) _ c₁
         (timeMax-left (close (⟦ a ⟧ env t)) (close (⟦ b ⟧ env t))))
       (merge-bounded (emits (⟦ a ⟧ env t)) (emits (⟦ b ⟧ env t))
         (boundedBy-weaken
           (timeMax-left (close (⟦ a ⟧ env t)) (close (⟦ b ⟧ env t))) b₁)
         (boundedBy-weaken
           (timeMax-right (close (⟦ a ⟧ env t)) (close (⟦ b ⟧ env t))) b₂))
denote-wfAt (concatB a b) env wfe t
  with denote-wfAt a env wfe t
     | denote-wfAt b env wfe (close (⟦ a ⟧ env t))
... | wfAt s₁ c₁ b₁ | wfAt s₂ c₂ b₂ =
  wfAt (append-sortedFrom (emits (⟦ a ⟧ env t))
         (emits (⟦ b ⟧ env (close (⟦ a ⟧ env t)))) s₁ b₁ s₂ c₁)
       (timeLeq-trans t (close (⟦ a ⟧ env t)) _ c₁ c₂)
       (append-bounded (emits (⟦ a ⟧ env t))
         (emits (⟦ b ⟧ env (close (⟦ a ⟧ env t))))
         (boundedBy-weaken c₂ b₁) b₂)

-- static programs: no root sources — everything the program does happens
-- inside the subscription frame ------------------------------------------------

data Static : BExp → Set where
  st-empty  : Static emptyB
  st-of     : {vs : List Val} → Static (ofB vs)
  st-map    : {f : Val → Val} {e : BExp} → Static e → Static (mapB f e)
  st-take   : {n : ℕ} {e : BExp} → Static e → Static (takeB n e)
  st-merge  : {a b : BExp} → Static a → Static b → Static (mergeB a b)
  st-concat : {a b : BExp} → Static a → Static b → Static (concatB a b)

-- every emission in the list happens at exactly time t
data AllAt {A : Set} (t : Time) : TimedObs A → Set where
  aa[] : AllAt t []
  aa∷  : {v : A} {xs : TimedObs A} → AllAt t xs → AllAt t ((t , v) ∷ xs)

allAt-const : {A : Set} (t : Time) (vs : List A)
  → AllAt t (map (λ v → (t , v)) vs)
allAt-const t []       = aa[]
allAt-const t (v ∷ vs) = aa∷ (allAt-const t vs)

allAt-mapT : {A B : Set} {t : Time} (f : A → B) (xs : TimedObs A)
  → AllAt t xs → AllAt t (mapT f xs)
allAt-mapT f []             aa[]     = aa[]
allAt-mapT f ((_ , v) ∷ xs) (aa∷ ax) = aa∷ (allAt-mapT f xs ax)

allAt-take : {A : Set} {t : Time} (n : ℕ) (xs : TimedObs A)
  → AllAt t xs → AllAt t (takeT n xs)
allAt-take zero    xs             _        = aa[]
allAt-take (suc n) []             aa[]     = aa[]
allAt-take (suc n) ((_ , v) ∷ xs) (aa∷ ax) = aa∷ (allAt-take n xs ax)

allAt-merge : {A : Set} {t : Time} (xs ys : TimedObs A)
  → AllAt t xs → AllAt t ys → AllAt t (mergeT xs ys)
allAt-merge []       ys       aa[]     ay       = ay
allAt-merge (x ∷ xs) []       ax       aa[]     = ax
allAt-merge {A} {t} ((_ , v) ∷ xs) ((_ , w) ∷ ys) (aa∷ ax) (aa∷ ay)
  rewrite timeLeq-refl t = aa∷ (allAt-merge xs ((t , w) ∷ ys) ax (aa∷ ay))

allAt-append : {A : Set} {t : Time} (xs ys : TimedObs A)
  → AllAt t xs → AllAt t ys → AllAt t (xs ++ ys)
allAt-append []       ys aa[]     ay = ay
allAt-append (_ ∷ xs) ys (aa∷ ax) ay = aa∷ (allAt-append xs ys ax ay)

takeCloseB-allAt : {A : Set} (t : Time) (n : ℕ) (xs : TimedObs A)
  → AllAt t xs → takeCloseB t n xs t ≡ t
takeCloseB-allAt t zero          xs             _        = refl
takeCloseB-allAt t (suc n)       []             aa[]     = refl
takeCloseB-allAt t (suc zero)    ((_ , v) ∷ xs) (aa∷ ax) = refl
takeCloseB-allAt t (suc (suc n)) ((_ , v) ∷ xs) (aa∷ ax) =
  takeCloseB-allAt t (suc n) xs ax

-- THE BURST RULE, both halves, by mutual structural induction: a static
-- program subscribed at t emits everything at t and closes at t. (The
-- close half is what makes concat's second argument subscribe INSIDE the
-- same instant — the crux of concat(of(1,2), of(3)) = [1,2,3].)

static-allAt : (e : BExp) → Static e → (env : Env) (t : Time)
  → AllAt t (emits (⟦ e ⟧ env t))
static-close : (e : BExp) → Static e → (env : Env) (t : Time)
  → close (⟦ e ⟧ env t) ≡ t

static-allAt emptyB st-empty env t = aa[]
static-allAt (ofB vs) st-of env t = allAt-const t vs
static-allAt (mapB f e) (st-map se) env t =
  allAt-mapT f (emits (⟦ e ⟧ env t)) (static-allAt e se env t)
static-allAt (takeB n e) (st-take se) env t =
  allAt-take n (emits (⟦ e ⟧ env t)) (static-allAt e se env t)
static-allAt (mergeB a b) (st-merge sa sb) env t =
  allAt-merge (emits (⟦ a ⟧ env t)) (emits (⟦ b ⟧ env t))
    (static-allAt a sa env t) (static-allAt b sb env t)
static-allAt (concatB a b) (st-concat sa sb) env t
  rewrite static-close a sa env t =
  allAt-append (emits (⟦ a ⟧ env t)) (emits (⟦ b ⟧ env t))
    (static-allAt a sa env t) (static-allAt b sb env t)

static-close emptyB st-empty env t = refl
static-close (ofB vs) st-of env t = refl
static-close (mapB f e) (st-map se) env t = static-close e se env t
static-close (takeB n e) (st-take se) env t
  rewrite static-close e se env t =
  takeCloseB-allAt t n (emits (⟦ e ⟧ env t)) (static-allAt e se env t)
static-close (mergeB a b) (st-merge sa sb) env t
  rewrite static-close a sa env t | static-close b sb env t
        | timeLeq-refl t = refl
static-close (concatB a b) (st-concat sa sb) env t
  rewrite static-close a sa env t = static-close b sb env t

-- batching a single-instant stream yields exactly one batch --------------------

vals : {A : Set} → TimedObs A → List A
vals = map snd

allAt-batch : {A : Set} (t : Time) (v : A) (xs : TimedObs A)
  → AllAt t xs
  → batchSpec ((t , v) ∷ xs) ≡ (t , v ∷ vals xs) ∷ []
allAt-batch t v []             aa[]     = refl
allAt-batch t v ((_ , w) ∷ xs) (aa∷ ax)
  rewrite allAt-batch t w xs ax | timeEq-refl t = refl

-- [] for the empty stream, one batch of all the values otherwise
oneBatch : {A : Set} → Time → TimedObs A → TimedObs (List A)
oneBatch t []       = []
oneBatch t (x ∷ xs) = (t , vals (x ∷ xs)) ∷ []

-- THE FRAME-BATCH THEOREM: any static program, nested to any depth,
-- subscribed at any time, batches to AT MOST ONE batch — the whole
-- subscription frame is one instant
frame-batch : (e : BExp) → Static e → (env : Env) (t : Time)
  → batchSpec (emits (⟦ e ⟧ env t)) ≡ oneBatch t (emits (⟦ e ⟧ env t))
frame-batch e se env t with emits (⟦ e ⟧ env t) | static-allAt e se env t
... | []            | aa[]   = refl
... | (_ , v) ∷ xs  | aa∷ ax = allAt-batch t v xs ax

-- the two motivating examples, as concrete equations ---------------------------

-- merge(of(1), of(2)) delivers ONE batch [1, 2]
merge-of-example : (env : Env) (t : Time)
  → batchSpec (emits (⟦ mergeB (ofB (1 ∷ [])) (ofB (2 ∷ [])) ⟧ env t))
    ≡ (t , 1 ∷ 2 ∷ []) ∷ []
merge-of-example env t rewrite timeLeq-refl t | timeEq-refl t = refl

-- concat(of(1, 2), of(3)) delivers ONE batch [1, 2, 3]
concat-of-example : (env : Env) (t : Time)
  → batchSpec (emits (⟦ concatB (ofB (1 ∷ 2 ∷ [])) (ofB (3 ∷ [])) ⟧ env t))
    ≡ (t , 1 ∷ 2 ∷ 3 ∷ []) ∷ []
concat-of-example env t = allAt-batch t 1 ((t , 2) ∷ (t , 3) ∷ []) (aa∷ (aa∷ aa[]))

-- the async half of the burst rule: a cold triggered by a source event
-- shares that event's root cause, so it batches WITH the event.
-- concat(take 1 (src), of(9)) delivers the source's first value and the 9
-- as ONE batch, at the source event's time.
cascade-example : (i : ℕ) (env : Env) (t t₁ : Time) (v₁ : Val)
  (rest : TimedObs Val) (c : Time)
  → env i ≡ obs ((t₁ , v₁) ∷ rest) c
  → timeLt t t₁ ≡ true      -- subscribed before the source's first event
  → batchSpec (emits (⟦ concatB (takeB 1 (srcB i)) (ofB (9 ∷ [])) ⟧ env t))
    ≡ (t₁ , v₁ ∷ 9 ∷ []) ∷ []
cascade-example i env t t₁ v₁ rest c eq lt
  rewrite eq | lt = allAt-batch t₁ v₁ ((t₁ , 9) ∷ []) (aa∷ aa[])

-- the diamond anchor law transfers: source events keep distinct times, so
-- batching the self-merge of any strictly monotone denotation still pairs
-- every value with itself
diamond-burst : (e : BExp) (env : Env) (t : Time)
  → StrictMono (emits (⟦ e ⟧ env t))
  → batchSpec (emits (⟦ mergeB e e ⟧ env t))
    ≡ mapT dbl (emits (⟦ e ⟧ env t))
diamond-burst e env t m = diamond (emits (⟦ e ⟧ env t)) m
