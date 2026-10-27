{-# OPTIONS --guardedness #-}

-- THE FOLD PART of the engine's invariant (`Base`): a fold over the tree
-- (`Wf`), split at the focus into the context's share (`WfC`) and the
-- focus's own, and the marks a node owns (`Owns`).
module adequacy.Engine.Fold where

open import Data.Bool using (true; false; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
import Data.List.Relation.Unary.All
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Unfold using (same?)
open import operation.PureObservable using (Tape; due; module Machine)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; closedUp;
  CS; cs; shows; outOf; attAt; attached; free; cpAt; cutAt; overAt; nx; cp;
  Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; search; found; leaf; own;
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

postulate
  -- The least mark is a node's own, and its focus plugs back to the tree.
  search-hit : ∀ {R Γ A} (t : St [] R) {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key)
             → plug c s ≡ t × Owns s m
  -- The search finds a node by one of its own marks.
  found-own : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key)
            → (m , key) ∈ own s
