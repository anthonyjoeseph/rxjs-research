{-# OPTIONS --guardedness #-}

-- EVERY STEP KEEPS THE INVARIANT (`inv-next`): its fold part
-- (`Base`, kept by `base-next`) and its order part (`adequacy.Engine.Pick.Order`,
-- kept by `ord-next`).  The fold part is dispatched as the
-- step is: by mode, then by the one frame a rise passes, the one former
-- a subscribe begins, or the one node a mark runs.  The invariant is a
-- fold over the tree (`Wf`), split at the focus into the context's share
-- (`WfC`) and the focus's own; each case rebuilds only the node the step
-- rewrites, and the context's share rides along.
module adequacy.Engine.Inv where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; _ʳ++_; null; [_]; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; Timeline; emit; stall; close; Events∞; hush; idle; ix)
open import denotation.MonotonicList using (Agreeᵀ)
open import operation.Key using (at)
open import denotation.Unfold using (same?; NEnv; stateᴺ; subscribe)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Ahead using (Under; shown; ahead-mono; under-sub)
open import adequacy.Engine.Race using (NotBefore)
open import adequacy.Engine.Meaning using (envAt)
open import adequacy.Engine.Pick using (Order; order; module Order; whole; Lead; Clear; Ends; EndsIf; Won; won-clear; won-ends; search-won; Apart; Searched)
open import operation.PureObservable using (Tape; due; play; ending; over; module Machine; module Driver)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; closedUp;
  CS; cs; shows; outOf; attAt; attached; free; cpAt; cutAt; overAt; nx; cp;
  Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; search; found; leaf;
  rise; run; begin; start; admit; dequeue; settle; ended; alive; feed; feedL; unsub; killAll; unsubIf; _⊕_)
  renaming (cut to cutᴹ)

------------------------------------------------------------------------
-- The invariant, node by node

-- A node a run has settled on is not one still to be subscribed.
Unpended : ∀ {Γ A} → St Γ A → Set
Unpended (pend o) = ⊥
Unpended _        = ⊤

IsPend : ∀ {Γ A} → St Γ A → Set
IsPend (pend o) = ⊤
IsPend _        = ⊥

-- What subscribes now is a node still to subscribe; what runs now,
-- rising or absorbed, never is.
Settled : ∀ {R} → Conf R → Set
Settled ⟨ c , s , subscribing , p ⟩ = IsPend s
Settled ⟨ c , s , absorbed , p ⟩    = Unpended s
Settled ⟨ c , s , rising e , p ⟩    = Unpended s

-- A connect whose body is still to subscribe has neither subscribed nor
-- ended its source.
Opened : ∀ {Γ X} → CS → St Γ X → Set
Opened (cs cl _ _ (just _) _ _ _ _) o = cl ≡ false × IsPend o
Opened (cs _ _ _ nothing _ _ _ _)   o = ⊤

mutual
  Wf : ∀ {Γ A} → St Γ A → Set
  Wf (mapS f s)              = Wf s
  Wf (scanS f z s)           = Wf s
  Wf (cutS l a s)            = Wf s
  Wf (lnS b s)               = Wf s
  Wf (takeS i q w s)         = Wf s
  Wf (flatS op f d n q o ls) = Wf o × Wfs ls
  Wf (connS k o b)           = Opened k o × Wf o × Wf b
  Wf _                       = ⊤

  Wfs : ∀ {Γ A} → List (St Γ A) → Set
  Wfs []       = ⊤
  Wfs (s ∷ ls) = Wf s × Wfs ls

-- The context's share: every sibling well formed, and a connect whose
-- source holds the hole has its body subscribed.
WfC : ∀ {R Γ A} → Ctx R Γ A → Set
WfC top                               = ⊤
WfC (inMap f c)                       = WfC c
WfC (inScan f z c)                    = WfC c
WfC (inCut l a c)                     = WfC c
WfC (inLn b c)                        = WfC c
WfC (inTake i q w c)                  = WfC c
WfC (inOuter op f d n q ls c)         = Wfs ls × WfC c
WfC (inLanes op f d n q o pre post c) = Wf o × Wfs pre × Wfs post × WfC c
WfC (inSrc k b c)                     = CS.bodyAt k ≡ nothing × Wf b × WfC c
WfC (inBody k o c)                    = Opened k o × Wf o × WfC c

-- The fold part of the invariant.
record Base {R} (k : Conf R) : Set where
  constructor inv
  field
    settled : Settled k
    ctxWf   : WfC (Conf.ctx k)
    focWf   : Wf (Conf.foc k)

------------------------------------------------------------------------
-- Splitting the fold at the focus and joining it back

-- A lane's context keeps the lanes before it nearest first.
wfs-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {ys} → Wfs pre → Wfs ys → Wfs (pre ʳ++ ys)
wfs-ʳ++ []        _        ws = ws
wfs-ʳ++ (x ∷ pre) (u , us) ws = wfs-ʳ++ pre us (u , ws)

wfs-++ : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Wfs pre → Wf s → Wfs post → Wfs (pre ʳ++ s ∷ post)
wfs-++ pre wp w wq = wfs-ʳ++ pre wp (w , wq)

wfs-ʳsplit : ∀ {Γ A} (pre : List (St Γ A)) {ys} → Wfs (pre ʳ++ ys) → Wfs pre × Wfs ys
wfs-ʳsplit []        ws = tt , ws
wfs-ʳsplit (x ∷ pre) ws with wfs-ʳsplit pre ws
... | a , (u , b) = (u , a) , b

wfs-split : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Wfs (pre ʳ++ s ∷ post) → Wfs pre × Wf s × Wfs post
wfs-split pre ws with wfs-ʳsplit pre ws
... | a , (w , b) = a , w , b

opened-none : ∀ {Γ X} k (o : St Γ X) → CS.bodyAt k ≡ nothing → Opened k o
opened-none (cs cl sl sa ba as ow r e) o refl = tt

pend-un : ∀ {Γ A} (s : St Γ A) → Unpended s → IsPend s → ⊥
pend-un (pend o) u _ = u

pend-un (coldS xb xl) u ()
pend-un (ofS xi xp xxs) u ()
pend-un doneS u ()
pend-un (mapS xf xs) u ()
pend-un (scanS xf xz xs) u ()
pend-un (cutS xl xa xs) u ()
pend-un (lnS xb xs) u ()
pend-un (takeS xi xq xw xs) u ()
pend-un (flatS xop xf xd xn xq xo xls) u ()
pend-un (connS xk xo xb) u ()
pend-un (joinS xj xg xx xib) u ()

-- A source holding a settled node has its body subscribed.
body-on : ∀ {Γ X} k (s : St Γ X) → Unpended s → Opened k s → CS.bodyAt k ≡ nothing
body-on (cs cl sl sa nothing as ow r e)  s u o        = refl
body-on (cs cl sl sa (just x) as ow r e) s u (_ , ip) with pend-un s u ip
... | ()

wf-join : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → WfC c → Wf s → Wf (plug c s)
wf-join top                               s v                  w = w
wf-join (inMap f c)                       s v                  w = wf-join c (mapS f s) v w
wf-join (inScan f z c)                    s v                  w = wf-join c (scanS f z s) v w
wf-join (inCut l a c)                     s v                  w = wf-join c (cutS l a s) v w
wf-join (inLn b c)                        s v                  w = wf-join c (lnS b s) v w
wf-join (inTake i q x c)                  s v                  w = wf-join c (takeS i q x s) v w
wf-join (inOuter op f d n q ls c)         s (ws , v)           w = wf-join c (flatS op f d n q s ls) v (w , ws)
wf-join (inLanes op f d n q o pre post c) s (wo , wp , wq , v) w = wf-join c (flatS op f d n q o (pre ʳ++ s ∷ post)) v (wo , wfs-++ pre wp w wq)
wf-join (inSrc k b c)                     s (e , wb , v)       w = wf-join c (connS k s b) v (opened-none k s e , w , wb)
wf-join (inBody k o c)                    s (op , wo , v)      w = wf-join c (connS k o s) v (op , wo , w)

wf-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Unpended s → Wf (plug c s) → WfC c × Wf s
wf-split top                               s u w = tt , w
wf-split (inMap f c)                       s u w = wf-split c (mapS f s) tt w
wf-split (inScan f z c)                    s u w = wf-split c (scanS f z s) tt w
wf-split (inCut l a c)                     s u w = wf-split c (cutS l a s) tt w
wf-split (inLn b c)                        s u w = wf-split c (lnS b s) tt w
wf-split (inTake i q x c)                  s u w = wf-split c (takeS i q x s) tt w
wf-split (inOuter op f d n q ls c)         s u w with wf-split c (flatS op f d n q s ls) tt w
... | v , (w′ , ws) = (ws , v) , w′
wf-split (inLanes op f d n q o pre post c) s u w with wf-split c (flatS op f d n q o (pre ʳ++ s ∷ post)) tt w
... | v , (wo , ws) with wfs-split pre ws
...   | wp , w′ , wq = (wo , wp , wq , v) , w′
wf-split (inSrc k b c)                     s u w with wf-split c (connS k s b) tt w
... | v , (op , w′ , wb) = (body-on k s u op , wb , v) , w′
wf-split (inBody k o c)                    s u w with wf-split c (connS k o s) tt w
... | v , (op , wo , w′) = (op , wo , v) , w′

-- The whole tree's fold, read off the invariant.
wfI : ∀ {R} {k : Conf R} → Base k → Wf (plug (Conf.ctx k) (Conf.foc k))
wfI {k = ⟨ c , s , m , p ⟩} v = wf-join c s (Base.ctxWf v) (Base.focWf v)

-- A settled node anywhere in a well-formed tree: the invariant at it.
base-at : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Unpended s → Wf (plug c s) → Base ⟨ c , s , absorbed , p ⟩
base-at c s p u w with wf-split c s u w
... | v , w′ = inv u v w′

------------------------------------------------------------------------
-- What a step does to one node keeps its fold

pend-unsubIf : ∀ {Γ A} b (s : St Γ A) → IsPend s → IsPend (proj₁ (unsubIf b s))
pend-unsubIf true  (pend o) _ = tt
pend-unsubIf false (pend o) _ = tt

pend-unsubIf b (coldS xb xl) ()
pend-unsubIf b (ofS xi xp xxs) ()
pend-unsubIf b doneS ()
pend-unsubIf b (mapS xf xs) ()
pend-unsubIf b (scanS xf xz xs) ()
pend-unsubIf b (cutS xl xa xs) ()
pend-unsubIf b (lnS xb xs) ()
pend-unsubIf b (takeS xi xq xw xs) ()
pend-unsubIf b (flatS xop xf xd xn xq xo xls) ()
pend-unsubIf b (connS xk xo xb) ()
pend-unsubIf b (joinS xj xg xx xib) ()

pend-feed : ∀ {Γ X A} (i : X ∈ Γ) p e (s : St Γ A) → IsPend s → IsPend (feed i p e s)
pend-feed i p e (pend o) _ = tt

pend-feed i p e (coldS xb xl) ()
pend-feed i p e (ofS xi xp xxs) ()
pend-feed i p e doneS ()
pend-feed i p e (mapS xf xs) ()
pend-feed i p e (scanS xf xz xs) ()
pend-feed i p e (cutS xl xa xs) ()
pend-feed i p e (lnS xb xs) ()
pend-feed i p e (takeS xi xq xw xs) ()
pend-feed i p e (flatS xop xf xd xn xq xo xls) ()
pend-feed i p e (connS xk xo xb) ()
pend-feed i p e (joinS xj xg xx xib) ()

-- Opened reads only whether the source closed and whether the body is
-- subscribed, and a still-pending source.
opened-move : ∀ {Γ X} cl sl sa ba as ow r e sl′ sa′ as′ ow′ r′ e′ {o o′ : St Γ X} → (IsPend o → IsPend o′)
            → Opened (cs cl sl sa ba as ow r e) o → Opened (cs cl sl′ sa′ ba as′ ow′ r′ e′) o′
opened-move cl sl sa (just x) as ow r e sl′ sa′ as′ ow′ r′ e′ f (c , ip) = c , f ip
opened-move cl sl sa nothing  as ow r e sl′ sa′ as′ ow′ r′ e′ f _        = tt

opened-unsub : ∀ {Γ X} k (o : St Γ X) → Opened k o → Opened k (proj₁ (unsub o))
opened-unsub (cs cl sl sa ba as ow r e) o = opened-move cl sl sa ba as ow r e sl sa as ow r e (pend-unsubIf true o)

opened-feed : ∀ {Γ X Y} (i : Y ∈ Γ) p ev k (o : St Γ X) → Opened k o → Opened k (feed i p ev o)
opened-feed i p ev (cs cl sl sa ba as ow r e) o = opened-move cl sl sa ba as ow r e sl sa as ow r e (pend-feed i p ev o)

mutual
  wf-unsub : ∀ {Γ A} (s : St Γ A) → Wf s → Wf (proj₁ (unsub s))
  wf-unsub (coldS true l)          w = tt
  wf-unsub (coldS false l)         w = tt
  wf-unsub (mapS f s)              w with unsub s | wf-unsub s w
  ... | s′ , t | w′ = w′
  wf-unsub (scanS f z s)           w with unsub s | wf-unsub s w
  ... | s′ , t | w′ = w′
  wf-unsub (takeS i p x s)         w with cutᴹ s | wf-cut s w
  ... | s′ , t | w′ = w′
  wf-unsub (flatS op f d n q o ls) (wo , ws) with cutᴹ o | wf-cut o wo | killAll ls | wf-killAll ls ws
  ... | o′ , t | wo′ | ls′ , u | ws′ = wo′ , ws′
  wf-unsub (connS k o b)           (op , wo , wb) with unsub o | wf-unsub o wo | opened-unsub k o op | unsub b | wf-unsub b wb
  ... | o′ , t | wo′ | op′ | b′ , u | wb′ = op′ , wo′ , wb′
  wf-unsub (joinS j g x ib)        w = tt
  wf-unsub (pend o)                w = w
  wf-unsub (ofS i p xs)            w = w
  wf-unsub doneS                   w = w
  wf-unsub (cutS l a s)            w = w
  wf-unsub (lnS b s)               w = w

  wf-cut : ∀ {Γ A} (s : St Γ A) → Wf s → Wf (proj₁ (cutᴹ s))
  wf-cut (cutS l attached s)  w with unsub s | wf-unsub s w
  ... | s′ , t | w′ = w′
  wf-cut (cutS l (attAt p) s) w = w

  wf-cut (pend xo) w = w
  wf-cut (coldS xb xl) w = w
  wf-cut (ofS xi xp xxs) w = w
  wf-cut doneS w = w
  wf-cut (mapS xf xs) w = w
  wf-cut (scanS xf xz xs) w = w
  wf-cut (lnS xb xs) w = w
  wf-cut (takeS xi xq xw xs) w = w
  wf-cut (flatS xop xf xd xn xq xo xls) w = w
  wf-cut (connS xk xo xb) w = w
  wf-cut (joinS xj xg xx xib) w = w

  wf-killAll : ∀ {Γ B} (ls : List (St Γ B)) → Wfs ls → Wfs (proj₁ (killAll ls))
  wf-killAll []                 _        = tt
  wf-killAll (lnS true s ∷ ls)  (w , ws) with cutᴹ s | wf-cut s w | killAll ls | wf-killAll ls ws
  ... | s′ , t | w′ | ls′ , u | ws′ = w′ , ws′
  wf-killAll (lnS false s ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′

  wf-killAll (pend xo ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (coldS xb xl ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (ofS xi xp xxs ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (doneS ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (mapS xf xs ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (scanS xf xz xs ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (cutS xl xa xs ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (takeS xi xq xw xs ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (flatS xop xf xd xn xq xo xls ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (connS xk xo xb ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′
  wf-killAll (joinS xj xg xx xib ∷ ls) (w , ws) with killAll ls | wf-killAll ls ws
  ... | ls′ , u | ws′ = w , ws′

wf-unsubIf : ∀ {Γ A} b (s : St Γ A) → Wf s → Wf (proj₁ (unsubIf b s))
wf-unsubIf true  s w = wf-unsub s w
wf-unsubIf false s w = w

mutual
  wf-feed : ∀ {Γ X A} (i : X ∈ Γ) p e (s : St Γ A) → Wf s → Wf (feed i p e s)
  wf-feed i p e (joinS j true x ib) w with same? i x
  ... | just refl = tt
  ... | nothing   = tt
  wf-feed i p e (joinS j false x ib)    w = tt
  wf-feed i p e (mapS f s)              w = wf-feed i p e s w
  wf-feed i p e (scanS f z s)           w = wf-feed i p e s w
  wf-feed i p e (cutS l a s)            w = wf-feed i p e s w
  wf-feed i p e (lnS b s)               w = wf-feed i p e s w
  wf-feed i p e (takeS v q x s)         w = wf-feed i p e s w
  wf-feed i p e (flatS op f d n q o ls) (wo , ws) = wf-feed i p e o wo , wf-feedL i p e ls ws
  wf-feed i p e (connS k o b)           (op , wo , wb) = opened-feed i p e k o op , wf-feed i p e o wo , wf-feed (there i) p e b wb
  wf-feed i p e (pend o)                w = w
  wf-feed i p e (coldS b l)             w = w
  wf-feed i p e (ofS v q xs)            w = w
  wf-feed i p e doneS                   w = w

  wf-feedL : ∀ {Γ X A} (i : X ∈ Γ) p e (ls : List (St Γ A)) → Wfs ls → Wfs (feedL i p e ls)
  wf-feedL i p e []       _        = tt
  wf-feedL i p e (s ∷ ls) (w , ws) = wf-feed i p e s w , wf-feedL i p e ls ws

wf-ended : ∀ {Γ A} (s : St Γ A) → Wf s → Wf (ended s)
wf-ended (lnS b (cutS l a s)) w = w

wf-ended (lnS b (pend xo)) w = w
wf-ended (lnS b (coldS xb xl)) w = w
wf-ended (lnS b (ofS xi xp xxs)) w = w
wf-ended (lnS b doneS) w = w
wf-ended (lnS b (mapS xf xs)) w = w
wf-ended (lnS b (scanS xf xz xs)) w = w
wf-ended (lnS b (lnS xb xs)) w = w
wf-ended (lnS b (takeS xi xq xw xs)) w = w
wf-ended (lnS b (flatS xop xf xd xn xq xo xls)) w = w
wf-ended (lnS b (connS xk xo xb)) w = w
wf-ended (lnS b (joinS xj xg xx xib)) w = w
wf-ended (pend xo) w = w
wf-ended (coldS xb xl) w = w
wf-ended (ofS xi xp xxs) w = w
wf-ended doneS w = w
wf-ended (mapS xf xs) w = w
wf-ended (scanS xf xz xs) w = w
wf-ended (cutS xl xa xs) w = w
wf-ended (takeS xi xq xw xs) w = w
wf-ended (flatS xop xf xd xn xq xo xls) w = w
wf-ended (connS xk xo xb) w = w
wf-ended (joinS xj xg xx xib) w = w

if-inv : ∀ {ℓ} {X : Set ℓ} (P : X → Set) b {x y} → P x → P y → P (if b then x else y)
if-inv P true  px py = px
if-inv P false px py = py

settle-settled : ∀ {R Γ A} {c : Ctx R Γ A} {s : St Γ A} d n e {p} → Unpended s → Settled ⟨ c , s , settle d n e , p ⟩
settle-settled {c = c} {s} d n e {p} u = if-inv (λ m → Settled ⟨ c , s , m , p ⟩) (d ∧ (n ≡ᵇ 0) ∧ e) u u

------------------------------------------------------------------------
-- The marks a node owns, as `own` lists them

data Owns {Γ} : ∀ {A} → St Γ A → Mark → Set₁ where
  ofO     : ∀ {A i p} {xs : List A} → Owns (ofS i p xs) ofM
  attO    : ∀ {A l p} {s : St Γ A} → Owns (cutS l (attAt p) s) attM
  cpO     : ∀ {A i q p} {s : St Γ A} → Owns (takeS i q (cpAt p) s) cpM
  cutO    : ∀ {A i q p} {s : St Γ A} → Owns (takeS i q (cutAt p) s) cutM
  bodyO   : ∀ {X B k p} {o : St Γ X} {b : St (X ∷ Γ) B} → CS.bodyAt k ≡ just p → Owns (connS k o b) bodyM
  srcAttO : ∀ {X B k p} {o : St Γ X} {b : St (X ∷ Γ) B} → CS.attSrc k ≡ just p → Owns (connS k o b) srcAttM
  owedO   : ∀ {X B k p} {o : St Γ X} {b : St (X ∷ Γ) B} → CS.owedAt k ≡ just p → Owns (connS k o b) owedM
  joinO   : ∀ {A j g x q e ib} → Owns (joinS {A = A} j g x ((q , e) ∷ ib)) joinM
  leafO   : ∀ {A b key} {l : Tape A} → due l ≡ just key → Owns (coldS b l) leafM

owned : ∀ {Γ A} {s : St Γ A} {m} → Owns s m → Unpended s
owned ofO     = tt
owned attO    = tt
owned cpO     = tt
owned cutO    = tt
owned (bodyO _)   = tt
owned (srcAttO _) = tt
owned (owedO _)   = tt
owned joinO       = tt
owned (leafO _)   = tt

------------------------------------------------------------------------
-- The step, case by case

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; step; played; took)

  NextBase : Step → Set
  NextBase (silent t k)    = Base k
  NextBase (value t p a k) = Base k
  NextBase (complete p)    = ⊤
  NextBase drained         = ⊤

  postulate
    -- The least mark is a node's own, and its focus plugs back to the tree.
    search-hit : ∀ {Γ A} (t : St [] R) {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key)
               → plug c s ≡ t × Owns s m

  -- A leaf's turn: whatever the runtime plays, the leaf is all that moves.
  played-inv : ∀ {A} b (l : Tape A) cl dv st → (∀ e l′ b′ p′ → Base (dv e l′ b′ p′)) → (∀ l′ → Base (st l′))
             → NextBase (played (leaf b l cl dv st))
  played-inv b     (ending e)                  cl    dv st d s = d cp over false e
  played-inv false (play τ u i t fr)           cl    dv st d s = s over
  played-inv false over                        cl    dv st d s = s over
  played-inv true  (play τ u i t fr)           true  dv st d s = s over
  played-inv true  over                        true  dv st d s = s over
  played-inv true  (play τ u i t (emit a k))   false dv st d s = d _ _ _ _
  played-inv true  (play τ u i t (stall k))    false dv st d s = s _
  played-inv true  (play τ u i t (close k))    false dv st d s = s _
  played-inv true  over                        false dv st d s = s over

  start-inv : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → WfC c → Wf o → Wfs ls
            → Base (start c op f d n q o ls a p)
  start-inv c op f d n q o ls a p v wo ws with closed c
  ... | true  = inv tt v (wo , ws)
  ... | false = inv tt (wo , wfs-ʳ++ ls ws tt , tt , v) tt

  dequeue-inv : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls p → WfC c → Wf o → Wfs ls
              → Base (dequeue c op f d n q o ls p)
  dequeue-inv c op f d n []      o ls p v wo ws = inv (settle-settled d n true tt) v (wo , ws)
  dequeue-inv c op f d n (a ∷ q) o ls p v wo ws = start-inv c op f d n q o ls a p v wo ws

  admit-inv : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → WfC c → Wf o → Wfs ls
            → NextBase (took (admit c op f d n q o ls a p))
  admit-inv c (mergeᶠ nothing)  f d n q o ls a p v wo ws = start-inv c (mergeᶠ nothing) f d n q o ls a p v wo ws
  admit-inv c (mergeᶠ (just m)) f d n q o ls a p v wo ws =
    if-inv Base (n <ᵇ m) (start-inv c (mergeᶠ (just m)) f d n q o ls a p v wo ws) (inv tt v (wo , ws))
  admit-inv c switchᶠ           f d n q o ls a p v wo ws with killAll ls | wf-killAll ls ws
  ... | ls′ , t | ws′ = start-inv c switchᶠ f d 0 q o ls′ a p v wo ws′
  admit-inv c exhaustᶠ          f d n q o ls a p v wo ws with n ≡ᵇ 0
  ... | true  = start-inv c exhaustᶠ f d n q o ls a p v wo ws
  ... | false = inv tt v (wo , ws)

  -- A rise, by the frame it passes.
  rise-inv : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → NextBase (took (rise c s e p))
  rise-inv top                               s (nx a) p (inv u v w) = inv u v w
  rise-inv top                               s cp     p (inv u v w) = tt
  rise-inv (inMap f c)                       s e      p (inv u v w) = inv tt v w
  rise-inv (inScan f z c)                    s (nx a) p (inv u v w) = inv tt v w
  rise-inv (inScan f z c)                    s cp     p (inv u v w) = inv tt v w
  rise-inv (inCut true a c)                  s e      p (inv u v w) = inv tt v w
  rise-inv (inCut false a c)                 s e      p (inv u v w) = inv tt v w
  rise-inv (inLn b c)                        s e      p (inv u v w) = inv tt v w
  rise-inv (inTake i q free c)               s (nx a) p (inv u v w) with q a | i
  ... | true  | _     = inv tt v w
  ... | false | true  = inv tt v w
  ... | false | false = inv tt v w
  rise-inv (inTake i q free c)               s cp     p (inv u v w) = inv tt v w
  rise-inv (inTake i q (cpAt r) c)           s e      p (inv u v w) = inv tt v w
  rise-inv (inTake i q (cutAt r) c)          s e      p (inv u v w) = inv tt v w
  rise-inv (inTake i q (overAt r) c)         s e      p (inv u v w) = inv tt v w
  rise-inv (inOuter op f d n q ls c)         s (nx a) p (inv u (ws , v) w) = admit-inv c op f d n q s ls a p v w ws
  rise-inv (inOuter op f d n q ls c)         s cp     p (inv u (ws , v) w) =
    inv (settle-settled true n (Data.List.null q) tt) v (w , ws)
  rise-inv (inLanes op f d n q o pre post c) s (nx b) p (inv u (wo , wp , wq , v) w) =
    if-inv Base (alive s) (inv tt v (wo , wfs-++ pre wp w wq)) (inv tt v (wo , wfs-++ pre wp w wq))
  rise-inv (inLanes op f d n q o pre post c) s cp     p (inv u (wo , wp , wq , v) w) =
    if-inv Base (alive s) (dequeue-inv c op f d _ q o (pre ʳ++ ended s ∷ post) p v wo (wfs-++ pre wp (wf-ended s w) wq)) (inv tt v (wo , wfs-++ pre wp w wq))
  rise-inv (inSrc k b c)                     s (nx a) p (inv u (e , wb , v) w) =
    inv tt v (opened-none k s e , w , wf-feed (here refl) p (nx a) b wb)
  rise-inv (inSrc k b c)                     s cp     p (inv u (e , wb , v) w) =
    inv tt v (opened-none (record k { closed = true ; endAt = p }) s e , w , wf-feed (here refl) p cp b wb)
  rise-inv (inBody k o c)                    s (nx b) p (inv u (op , wo , v) w) = inv tt v (op , wo , w)
  rise-inv (inBody (cs cl sl sa ba as ow r e) o c) s cp p (inv u (op , wo , v) w) =
    inv tt v (opened-move cl sl sa ba as ow r e sl sa as (just p) r e (λ ip → ip) op , wo , w)

  -- A subscribe, by the former it begins.
  begin-inv : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Base ⟨ c , pend o , subscribing , p ⟩ → NextBase (took (begin c o p))
  begin-inv c (cold x)          p (inv u v w) = inv tt v tt
  begin-inv c empty             p (inv u v w) = inv tt v tt
  begin-inv c (of xs)           p (inv u v w) = inv tt v tt
  begin-inv c (map f s)         p (inv u v w) = inv tt v tt
  begin-inv c (scan f z s)      p (inv u v w) = inv tt v tt
  begin-inv c (takeWhile i q s) p (inv u v w) = inv tt v tt
  begin-inv c (flatMap op f s)  p (inv u v w) = inv tt (tt , v) tt
  begin-inv c (connect s b)     p (inv u v w) = inv tt ((refl , tt) , tt , v) tt
  begin-inv c (connected x)     p (inv u v w) with closedUp c x
  ... | true  = inv tt v tt
  ... | false = inv tt v tt
  begin-inv c (defer l)         p (inv u v w) = inv tt v tt

  -- A mark run, by the node that owns it.
  run-inv : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} p → Owns s m → WfC c → Wf s → NextBase (took (run c s m p))
  run-inv c p (ofO {xs = xs}) v w with closed c | xs
  ... | true  | _       = inv tt v tt
  ... | false | []      = inv tt v tt
  ... | false | x ∷ xs′ = inv tt v tt
  run-inv c p (attO {l = l} {s = s}) v w with unsubIf (not l) s | wf-unsubIf (not l) s w
  ... | s′ , t | w′ = inv tt v w′
  run-inv c p cpO v w = inv tt v w
  run-inv c p (cutO {s = s}) v w with cutᴹ s | wf-cut s w
  ... | s′ , t | w′ = inv tt v w′
  run-inv c p (bodyO {k = cs cl sl sa (just q) as ow r e} _) v (op , wo , wb) = inv (proj₂ op) (refl , wb , v) wo
  run-inv c p (bodyO {k = cs cl sl sa nothing as ow r e} ()) v w
  run-inv c p (srcAttO {k = cs cl sl sa ba (just q) ow r e} {o = o} _) v (op , wo , wb)
    with unsubIf (not sl) o | wf-unsubIf (not sl) o wo | pend-unsubIf (not sl) o
  ... | o′ , t | wo′ | pu = inv tt v (opened-move cl sl sa ba (just q) ow r e sl true nothing ow r e pu op , wo′ , wb)
  run-inv c p (srcAttO {k = cs cl sl sa ba nothing ow r e} ()) v w
  run-inv c p (owedO {k = cs cl sl sa ba as (just q) r e} {o = o} _) v (op , wo , wb)
    with unsubIf sa o | wf-unsubIf sa o wo | pend-unsubIf sa o
  ... | o′ , t | wo′ | pu = inv tt v (opened-move cl sl sa ba as (just q) r e false sa as nothing r e pu op , wo′ , wb)
  run-inv c p (owedO {k = cs cl sl sa ba as nothing r e} ()) v w
  run-inv c p (joinO {g = true}  {e = nx a}) v w with closed c
  ... | true  = inv tt v tt
  ... | false = inv tt v tt
  run-inv c p (joinO {g = true}  {e = cp})   v w with closed c
  ... | true  = inv tt v tt
  ... | false = inv tt v tt
  run-inv c p (joinO {g = false} {e = nx a}) v w = inv tt v tt
  run-inv c p (joinO {g = false} {e = cp})   v w = inv tt v tt
  run-inv c p (leafO {b = b} {l = l} _) v w =
    played-inv b l (closed c) (λ e l′ b′ p′ → ⟨ c , coldS b′ l′ , rising e , p′ ⟩) (λ l′ → ⟨ c , coldS b l′ , absorbed , p ⟩)
      (λ e l′ b′ p′ → inv tt v tt) (λ l′ → inv tt v tt)

  -- EVERY STEP KEEPS THE INVARIANT.
  base-next : ∀ k → Base k → NextBase (step k)
  base-next ⟨ c , s , rising e , p ⟩     v = rise-inv c s e p v
  base-next ⟨ c , pend o , subscribing , p ⟩ v = begin-inv c o p v

  base-next ⟨ c , (coldS xb xl) , subscribing , p ⟩ v = v
  base-next ⟨ c , (ofS xi xp xxs) , subscribing , p ⟩ v = v
  base-next ⟨ c , doneS , subscribing , p ⟩ v = v
  base-next ⟨ c , (mapS xf xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (scanS xf xz xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (cutS xl xa xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (lnS xb xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (takeS xi xq xw xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (flatS xop xf xd xn xq xo xls) , subscribing , p ⟩ v = v
  base-next ⟨ c , (connS xk xo xb) , subscribing , p ⟩ v = v
  base-next ⟨ c , (joinS xj xg xx xib) , subscribing , p ⟩ v = v
  base-next ⟨ c , s , absorbed , p ⟩ v with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , own with wf-split c′ s′ (owned own) (subst Wf (sym pl) (wfI v))
  ...     | v′ , w′ = run-inv c′ p own v′ w′

  base-load : (o : Obs Timeline [] R) → Base (Machine.load o)
  base-load o = inv tt tt tt

  ----------------------------------------------------------------------
  -- The whole invariant: the fold and the order

  record Inv (k : Conf R) : Set where
    constructor _&_
    field
      base : Base k
      ord  : Order k

  NextOrd : Step → Set
  NextOrd (silent t k)    = Order k
  NextOrd (value t p a k) = Order k
  NextOrd (complete p)    = ⊤
  NextOrd drained         = ⊤

  NextInv : Step → Set
  NextInv (silent t k)    = Inv k
  NextInv (value t p a k) = Inv k
  NextInv (complete p)    = ⊤
  NextInv drained         = ⊤

  NextShape NextLead NextApart : Step → Set
  NextShape (silent t k)    = Frag (whole k)
  NextShape (value t p a k) = Frag (whole k)
  NextShape (complete p)    = ⊤
  NextShape drained         = ⊤
  NextLead (silent t k)    = Lead k
  NextLead (value t p a k) = Lead k
  NextLead (complete p)    = ⊤
  NextLead drained         = ⊤
  NextApart (silent t k)    = Searched k
  NextApart (value t p a k) = Searched k
  NextApart (complete p)    = ⊤
  NextApart drained         = ⊤

  postulate
    -- THE SHAPE: a step keeps the whole tree in the fragment.
    shape-next : ∀ k → Base k → Frag (whole k) → NextShape (step k)
    -- THE STILL'S SUBTREE: where the search runs after a step, what it
    -- finds still leads every race above it past each live source's skips.
    apart-next : ∀ k → Base k → Order k → NextApart (step k)
    -- A mark run rises, if at all, the event it showed, at its own key,
    -- leaving a node as live as the one it ran.
    run-lead : ∀ (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} p → search top t ≡ just (found (Γ , A , c , s) m key)
             → (∀ q a (s′ : St Γ A) → key ≡ at q → outOf c s m ≡ shows (nx a) → alive s ≡ alive s′ → Clear q a c s′)
             → (∀ q (s′ : St Γ A) → key ≡ at q → outOf c s m ≡ shows cp → alive s ≡ alive s′ → Ends q c s′)
             → NextLead (took (run c s m p))

  -- Where a lane begins, every frame above it, its flatMap's other parts
  -- among them, passes every skip under it.
  Begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Set
  Begun c op f d n q o ls a p =
    closed c ≡ false → Lead ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc n) q o (reverse ls) [] c)) , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩

  Dequeues : ∀ {Γ A B} (c : Ctx R Γ B) (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A) (ls : List (St Γ B)) (p : Pos) → Set
  Dequeues c op f d n []      o ls p = ⊤
  Dequeues c op f d n (a ∷ q) o ls p = Begun c op f d n q o ls a p

  postulate
    -- A LANE BEGUN IS CLEAR BENEATH: what an admitted value or a lane's end
    -- leaves the frames above, it leaves under the lane it begins.
    outer-begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
                → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Begun c op f d n q o ls a p
    switch-begun : ∀ {Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
                 → Inv ⟨ inOuter switchᶠ f d n q ls c , o , rising (nx a) , p ⟩ → Begun c switchᶠ f d 0 q o (proj₁ (killAll ls)) a p
    lane-begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
               → alive s ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
               → Begun c op f d (pred n) q o (pre ʳ++ ended s ∷ post) a p
    -- A SOURCE ABOUT TO BE SUBSCRIBED shows no earlier than its body's
    -- subscription and, hushed, leaves nothing running.
    fresh-src : ∀ {Γ X} (o : Obs Timeline Γ X) p (ρ : NEnv Γ)
              → (Events∞.force (stateᴺ (subscribe o (p ⊕ [ ix 1 ])) ρ) ≡ hush
                   → ∀ d → Agreeᵀ d (Events∞.cut (stateᴺ (subscribe o (p ⊕ [ ix 1 ])) ρ)) idle)
              × (∀ k → Under (_≡ p ⊕ [ ix 0 ]) k → NotBefore k (shown (Events∞.force (stateᴺ (subscribe o (p ⊕ [ ix 1 ])) ρ))))

  dequeues : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
           → alive s ≡ true → Inv ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Dequeues c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p
  dequeues c op f d n []      o pre post s p al iv = tt
  dequeues c op f d n (a ∷ q) o pre post s p al iv = lane-begun c op f d n a q o pre post s p al iv

  -- Nothing a subscription starts or a slot frees rises a value; an
  -- outer completing rises its flatMap's end with the end's lead.
  start-lead : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Begun c op f d n q o ls a p
             → Lead (start c op f d n q o ls a p)
  start-lead c op f d n q o ls a p b with closed c
  ... | true  = tt
  ... | false = b refl

  lead-if : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p b → EndsIf b p c s → Lead ⟨ c , s , (if b then rising cp else absorbed) , p ⟩
  lead-if c s p true  l = l
  lead-if c s p false l = tt

  settle-lead : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) d n e p → EndsIf (d ∧ (n ≡ᵇ 0) ∧ e) p c s → Lead ⟨ c , s , settle d n e , p ⟩
  settle-lead c s d n e p l = lead-if c s p (d ∧ (n ≡ᵇ 0) ∧ e) l

  dequeue-lead : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls p
               → EndsIf (d ∧ (n ≡ᵇ 0) ∧ null q) p c (flatS op f d n q o ls) → Dequeues c op f d n q o ls p → Lead (dequeue c op f d n q o ls p)
  dequeue-lead c op f d n []      o ls p l b = settle-lead c (flatS op f d n [] o ls) d n true p l
  dequeue-lead c op f d n (a ∷ q) o ls p l b = start-lead c op f d n q o ls a p b

  admit-lead : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
             → NextLead (took (admit c op f d n q o ls a p))
  admit-lead c (mergeᶠ nothing)  f d n q o ls a p iv = start-lead c (mergeᶠ nothing) f d n q o ls a p (outer-begun c (mergeᶠ nothing) f d n q o ls a p iv)
  admit-lead c (mergeᶠ (just m)) f d n q o ls a p iv with n <ᵇ m
  ... | true  = start-lead c (mergeᶠ (just m)) f d n q o ls a p (outer-begun c (mergeᶠ (just m)) f d n q o ls a p iv)
  ... | false = tt
  admit-lead c switchᶠ           f d n q o ls a p iv with killAll ls | switch-begun c f d n q o ls a p iv
  ... | ls′ , t | b = start-lead c switchᶠ f d 0 q o ls′ a p b
  admit-lead c exhaustᶠ          f d n q o ls a p iv with n ≡ᵇ 0
  ... | true  = start-lead c exhaustᶠ f d n q o ls a p (outer-begun c exhaustᶠ f d n q o ls a p iv)
  ... | false = tt

  -- A rise carries its lead: each frame was clear at the position the
  -- value reaches it.
  rise-lead : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Lead ⟨ c , s , rising e , p ⟩ → Inv ⟨ c , s , rising e , p ⟩
            → NextLead (took (rise c s e p))
  rise-lead top                               s (nx a) p l iv = tt
  rise-lead top                               s cp     p l iv = tt
  rise-lead (inMap f c)                       s (nx a) p l iv = l
  rise-lead (inMap f c)                       s cp     p l iv = l
  rise-lead (inScan f z c)                    s (nx a) p l iv = l
  rise-lead (inScan f z c)                    s cp     p l iv = l
  rise-lead (inCut true x c)                  s (nx a) p l iv = l refl
  rise-lead (inCut true x c)                  s cp     p l iv = l refl
  rise-lead (inCut false x c)                 s (nx a) p l iv = tt
  rise-lead (inCut false x c)                 s cp     p l iv = tt
  rise-lead (inLn b c)                        s (nx a) p l iv = l
  rise-lead (inLn b c)                        s cp     p l iv = l
  rise-lead (inTake i q free c)               s (nx a) p l iv with q a | i
  ... | true  | _     = proj₁ l refl
  ... | false | true  = proj₂ l refl refl
  ... | false | false = tt
  rise-lead (inTake i q free c)               s cp     p l iv = l
  rise-lead (inTake i q (cpAt r) c)           s (nx a) p l iv = tt
  rise-lead (inTake i q (cpAt r) c)           s cp     p l iv = tt
  rise-lead (inTake i q (cutAt r) c)          s (nx a) p l iv = tt
  rise-lead (inTake i q (cutAt r) c)          s cp     p l iv = tt
  rise-lead (inTake i q (overAt r) c)         s (nx a) p l iv = tt
  rise-lead (inTake i q (overAt r) c)         s cp     p l iv = tt
  rise-lead (inOuter op f d n q ls c)         s (nx a) p l iv = admit-lead c op f d n q s ls a p iv
  rise-lead (inOuter op f d n q ls c)         s cp     p l iv = settle-lead c (flatS op f true n q s ls) true n (null q) p l
  rise-lead (inLanes op f d n q o pre post c) s (nx b) p l iv with alive s
  ... | true  = proj₂ (l refl)
  ... | false = tt
  rise-lead (inLanes op f d n q o pre post c) s cp     p l iv with alive s in al
  ... | true  = dequeue-lead c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p (proj₁ (proj₂ (proj₂ l))) (dequeues c op f d n q o pre post s p al iv)
  ... | false = tt
  rise-lead (inSrc k b c)                     s (nx a) p l iv = tt
  rise-lead (inSrc k b c)                     s cp     p l iv = tt
  rise-lead (inBody k o c)                    s (nx b) p l iv = l
  rise-lead (inBody k o c)                    s cp     p l iv = l _

  -- A subscribe rises nothing, and carries its lead down.
  sub-lead : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Lead ⟨ c , s , subscribing , p ⟩ → NextLead (step ⟨ c , s , subscribing , p ⟩)
  sub-lead c (pend (cold x))          p l = tt
  sub-lead c (pend empty)             p l = tt
  sub-lead c (pend (of xs))           p l = tt
  sub-lead c (pend (map f o))         p l = l
  sub-lead c (pend (scan f z o))      p l = l
  sub-lead c (pend (takeWhile i q o)) p l = l
  sub-lead c (pend (flatMap op f o))  p l = λ sh → (λ k _ → Data.List.Relation.Unary.All.[] , tt) , l sh
  sub-lead c (pend (connect o b))     p l =
    λ sh → proj₁ (fresh-src o p (envAt c)) , proj₂ (fresh-src o p (envAt c)) , ahead-mono (under-sub p [ ix 0 ]) c true (l sh)
  sub-lead c (pend (connected x))     p l with closedUp c x
  ... | true  = tt
  ... | false = tt
  sub-lead c (pend (defer d))         p l = λ sh → ahead-mono (under-sub p [ ix 1 ]) c true (l sh)
  sub-lead c (coldS b l′)             p l = l
  sub-lead c (ofS i q xs)             p l = l
  sub-lead c doneS                    p l = l
  sub-lead c (mapS f s)               p l = l
  sub-lead c (scanS f z s)            p l = l
  sub-lead c (cutS l′ a s)            p l = l
  sub-lead c (lnS b s)                p l = l
  sub-lead c (takeS i q w s)          p l = l
  sub-lead c (flatS op f d n q o ls)  p l = l
  sub-lead c (connS k o b)            p l = l
  sub-lead c (joinS j g x ib)         p l = l

  -- THE PICK: the run of the least mark leads every frame above it.
  lead-next : ∀ k → Base k → Order k → NextLead (step k)
  lead-next ⟨ c , s , rising e , p ⟩    b o = rise-lead c s e p (Order.lead o) (b & o)
  lead-next ⟨ c , s , subscribing , p ⟩ b o = sub-lead c s p (Order.lead o)
  lead-next ⟨ c , s , absorbed , p ⟩    b o with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , _ = run-lead (plug c s) p e
                     (λ q a s″ kq oa al → won-clear q a c′ s′ s″ al
                        (subst₂ (λ k x → Won (k , x) c′ s′) kq oa (search-won (plug c s) e)) (subst Frag (sym pl) (Order.shape o)))
                     (λ q s″ kq oc al → won-ends q c′ s′ s″ al
                        (subst₂ (λ k x → Won (k , x) c′ s′) kq oc (search-won (plug c s) e)) (subst Frag (sym pl) (Order.shape o)))

  joined : ∀ x → NextShape x → NextLead x → NextApart x → NextOrd x
  joined (silent t k)    f l u = order f l u
  joined (value t p a k) f l u = order f l u
  joined (complete p)    f l u = tt
  joined drained         f l u = tt

  -- EVERY STEP KEEPS THE ORDER.
  ord-next : ∀ k → Base k → Order k → NextOrd (step k)
  ord-next k b o = joined (step k) (shape-next k b (Order.shape o)) (lead-next k b o) (apart-next k b o)

  both : ∀ x → NextBase x → NextOrd x → NextInv x
  both (silent t k)    b o = b & o
  both (value t p a k) b o = b & o
  both (complete p)    b o = tt
  both drained         b o = tt

  inv-next : ∀ k → Inv k → NextInv (step k)
  inv-next k (b & o) = both (step k) (base-next k b) (ord-next k b o)

  inv-load : (o : Obs Timeline [] R) → Inv (Machine.load o)
  inv-load o = base-load o & order tt (λ _ → tt) tt

  -- A settled node anywhere in a tree the invariant holds of, absorbed at
  -- the same position: the invariant at it.
  inv-at : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Unpended s → Wf (plug c s) → Frag (plug c s) → Apart (plug c s)
         → Inv ⟨ c , s , absorbed , p ⟩
  inv-at c s p u w f t = base-at c s p u w & order f tt t
