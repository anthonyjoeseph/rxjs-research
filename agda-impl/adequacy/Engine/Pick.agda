{-# OPTIONS --guardedness #-}

-- A LANE FIRST, FROM THE PICK.  The order a rising lane needs
-- (`adequacy.Engine.Race.First`, per flatMap frame: `Sides`) is read off the
-- search that picked it, frame by frame (`won-clear`), not off a
-- predicate on every key the tree owns.  At each frame the engine's race
-- puts every sibling's candidate no earlier than the winner's key, older
-- lanes strictly later (`Won`, as `search` computes it); each sibling's
-- step heads no earlier than its candidate (`adequacy.Engine.Head.Agrees`,
-- by `head-agrees` at the sibling); and the stepper's head is the
-- meaning's (`sides-link`).
--
-- So a configuration carries the fragment's shape (`Frag` of its whole
-- tree), while a value rises what that pick established about the frames
-- above it (`Clear`), and where the search runs, that a still find leads
-- every race above it past each live source's skips (`Apart`): the
-- engine's race reads a source's skip at one key, while the frames above
-- are asked of every position under it.
--
-- `Clear` follows the value up as `rise` carries it, each frame at the
-- position the value has there: an inclusive takeWhile's failing value
-- reaches the frames above at `p ⊕ [ ix 0 ]`.  `Won` follows the
-- winner's candidate up as `seek` retags it, which moves the key at the
-- same frames by the same `shift`, so each frame's race is read at the
-- position the value will rise to.

-- DEAD ROUTE: one position for every frame (`Clear p c`, the winner's own
--   key throughout).  Above an inclusive takeWhile failing at `p` the value
--   rises at `p ⊕ [ ix 0 ]`; an older lane headed exactly there is after
--   `p` but not after where the value arrives, so no step from the lead at
--   `p` reaches the lead the frame above needs.  The engine's race there
--   is already at the shifted key.
module adequacy.Engine.Pick where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse; null; map)
open import Data.List.Properties using (ʳ++-defn; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import denotation.Unfold using (NEnv)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺; map⁺ to all-map⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; pred; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline; Events∞; idle; out; skip; end; hush; ix; _<ᵖ_; <ᵖ-below)
open import denotation.MonotonicList using (head; Agreeᵀ)
open import denotation.Unfold using (Step; states; step; headˢ; hushˢ; outˢ; skipˢ; endˢ; meaning; subscribe)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (peek; module Machine)
open Machine using (St; cs; mapS; scanS; cutS; lnS; takeS; flatS; connS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes;
  inSrc; inBody; plug; closed; Out; still; shows; seek; search; found; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; pend; coldS; ofS; doneS; joinS; own; Found; nx; cp; alive; ended; free; cpAt; cutAt; overAt; _⊕_; mapT; scanT; cutT; takeT; laneT; shift; over; outOf)
  renaming (outerT to outerK)
open import adequacy.Engine.Meaning using (gh; poolG; lanesL; deadL; poolT; outerT; envAt; srcState; srcG)
open import adequacy.Engine.Race using (NotBefore; After; TailNotBefore)
open import adequacy.Engine.Head using (Frag; Lanes; Lane; Agrees; exact; early; HeadAt; HeadAtⁿ; cand; pool-step; dead-idle; at-<ᵖ; <≮ᴷ; ≮ᴷ-trans; ext-≮)
open import adequacy.Engine.Head.Race using (shift-≮)
open import adequacy.Engine.Head.Agrees using (head-agrees; head-agreesⱽ)
open import adequacy.Engine.Shuts using (shutAll)
open import adequacy.Engine.Head.Within using (frag-flat; frag-body; frag-parts; fr-at; conn-src)
open import adequacy.Engine.Keys using (ConnAt; Keyed; Keys; keyed-at)
open import adequacy.Engine.Trails using (envAt-sorted)
open import adequacy.Placed.Order using (Headed; Sorted; every)
open import adequacy.Placed.Rising using (past-sub)
open import adequacy.Engine.Above using (Flight)
open import adequacy.Engine.Ahead using (Sides; Ahead; Under; shown; shows-open) renaming (shows to showsᶜ)
open import adequacy.Engine.Scope using (Scope; modes; firsts-after; FloorAt; FloorSrc; first-floor; floor-lower; scope-src; past-floor; closures; ended-at; shut-floor; shut-states; Gh; Ghᴸ; gh-at; gh-told)
open import adequacy.Sane using (Mode)
open import adequacy.Stepper using (first; firstᴸ)
open import adequacy.Stepper.Past using (Floor; Floorᴱ)

------------------------------------------------------------------------
-- What a rising lane leads

-- Every frame a value `a` rising at `p` passes, at the position it has
-- there and the node `rise` leaves below; each flatMap frame while its
-- observer is open.
Clear : ∀ {R Γ A} → Pos → A → Ctx R Γ A → St Γ A → Set
Clear p a top                               s = ⊤
Clear p a (inMap f c)                       s = Clear p (f a) c (mapS f s)
Clear p a (inScan f z c)                    s = Clear p (f z a) c (scanS f (f z a) s)
Clear p a (inCut l x c)                     s = l ≡ true → Clear p a c (cutS l x s)
Clear p a (inLn b c)                        s = Clear p a c (lnS b s)
Clear p a (inTake i q free c)               s = (q a ≡ true → Clear p a c (takeS i q free s))
                                              × (q a ≡ false → i ≡ true → Clear (p ⊕ [ ix 0 ]) a c (takeS i q (cpAt p) s))
Clear p a (inTake i q (cpAt r) c)           s = ⊤
Clear p a (inTake i q (cutAt r) c)          s = ⊤
Clear p a (inTake i q (overAt r) c)         s = ⊤
Clear p a (inOuter op f true n q ls c)      s = ⊥
Clear p a (inOuter op f false n q ls c)     s =
  closed c ≡ false × All (λ l → After p (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore p (poolT (deadL ls) (envAt c))
  × (showsᶜ c true ≡ true → Ahead (_≡ p ⊕ [ ix 0 ]) c true)
Clear p a (inLanes op f d n q o pre post c) s =
  alive s ≡ true → Sides p f d o (reverse pre) post (envAt c) × Clear p a c (flatS op f d n q o (pre ʳ++ s ∷ post))
Clear p a (inSrc k b c)                     s = over k ≡ false → closed c ≡ false → After (p ⊕ [ ix 0 ]) (headˢ (step (gh b)))
Clear p a (inBody (cs cl true sa ba as nothing r en) o c) s =
  (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) ≡ hush
     → ∀ d → Agreeᵀ d (Events∞.cut (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))) idle)
  × NotBefore p (shown (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))))
  × Clear p a c (connS (cs cl true sa ba as nothing r en) o s)
Clear p a (inBody (cs cl true sa ba as (just _) r en) o c) s = ⊥
Clear p a (inBody (cs cl false sa ba as ow r en) o c)      s = ⊥

-- Where a lane's end begins a queued value: the frames above, at the
-- skip just past the end.
Queued : ∀ {R Γ B} {A : Set} → List A → Pos → Ctx R Γ B → Set
Queued []      p c = ⊤
Queued (_ ∷ _) p c = showsᶜ c true ≡ true → Ahead (_≡ p ⊕ [ ix 0 ]) c true

-- Every frame a completion rising at `p` passes, and the node `rise`
-- leaves below: a lane's flatMap, the lane live, while its parts are
-- open, and above it only where the lane's end ends the flatMap, or
-- where it begins a queued value.
mutual
  Ends : ∀ {R Γ A} → Pos → Ctx R Γ A → St Γ A → Set
  Ends p top                               s = ⊤
  Ends p (inMap f c)                       s = Ends p c (mapS f s)
  Ends p (inScan f z c)                    s = Ends p c (scanS f z s)
  Ends p (inCut l x c)                     s = l ≡ true → Ends p c (cutS l x s)
  Ends p (inLn b c)                        s = Ends p c (lnS b s)
  Ends p (inTake i q free c)               s = Ends p c (takeS i q free s)
  Ends p (inTake i q (cpAt r) c)           s = ⊤
  Ends p (inTake i q (cutAt r) c)          s = ⊤
  Ends p (inTake i q (overAt r) c)         s = ⊤
  Ends p (inOuter op f d n q ls c)         s =
    (d ≡ false → closed c ≡ false
       → All (λ l → After p (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore p (poolT (deadL ls) (envAt c)))
    × EndsIf ((n ≡ᵇ 0) ∧ null q) p c (flatS op f true n q s ls)
  Ends p (inLanes op f d n q o pre post c) s =
    alive s ≡ true × (closed c ≡ false → Sides p f d o (reverse pre) post (envAt c))
                   × EndsIf (d ∧ (pred n ≡ᵇ 0) ∧ null q) p c (flatS op f d (pred n) q o (pre ʳ++ ended s ∷ post)) × Queued q p c
  Ends p (inSrc k b c)                     s = ⊤
  Ends p (inBody (cs cl true sa ba as nothing r en) o c) s =
    (closed c ≡ false
       → (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) ≡ hush
            → ∀ d → Agreeᵀ d (Events∞.cut (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))) idle)
         × NotBefore p (shown (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))))
    × (∀ k′ → Ends p c (connS k′ o s))
  Ends p (inBody (cs cl true sa ba as (just _) r en) o c) s = ⊥
  Ends p (inBody (cs cl false sa ba as ow r en) o c)      s = ⊥

  EndsIf : ∀ {R Γ A} → Bool → Pos → Ctx R Γ A → St Γ A → Set
  EndsIf true  p c s = Ends p c s
  EndsIf false p c s = ⊤

-- A rise's lead; a subscription's, every frame above passing each skip
-- under it.
Lead : ∀ {R} → Conf R → Set
Lead ⟨ c , s , rising (nx a) , p ⟩ = Clear p a c s
Lead ⟨ c , s , rising cp , p ⟩     = Ends p c s
Lead ⟨ c , s , subscribing , p ⟩   = showsᶜ c true ≡ true → Ahead (Under (_≡ p)) c true
Lead ⟨ c , s , absorbed , p ⟩      = ⊤

-- A value shows only under an open observer.
out-open : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) m {a : A} → outOf c s m ≡ shows (nx a) → closed c ≡ false
out-open c (pend o)                        m = λ ()
out-open c (coldS b l)                     leafM with peek l
... | nothing        = λ ()
... | just nothing   with closed c
...   | false = λ _ → refl
...   | true  = λ ()
out-open c (coldS b l)                     leafM | just (just _) with b | closed c
...   | true  | false = λ _ → refl
...   | true  | true  = λ ()
...   | false | _     = λ ()
out-open c (coldS b l)                     ofM = λ ()
out-open c (coldS b l)                     attM = λ ()
out-open c (coldS b l)                     bodyM = λ ()
out-open c (coldS b l)                     srcAttM = λ ()
out-open c (coldS b l)                     owedM = λ ()
out-open c (coldS b l)                     cpM = λ ()
out-open c (coldS b l)                     cutM = λ ()
out-open c (coldS b l)                     joinM = λ ()
out-open c (ofS i p xs)                    ofM with closed c
... | false = λ _ → refl
... | true  = λ ()
out-open c (ofS i p xs)                    attM = λ ()
out-open c (ofS i p xs)                    bodyM = λ ()
out-open c (ofS i p xs)                    srcAttM = λ ()
out-open c (ofS i p xs)                    owedM = λ ()
out-open c (ofS i p xs)                    cpM = λ ()
out-open c (ofS i p xs)                    cutM = λ ()
out-open c (ofS i p xs)                    joinM = λ ()
out-open c (ofS i p xs)                    leafM = λ ()
out-open c doneS                                    m = λ ()
out-open c (mapS f s)                               m = λ ()
out-open c (scanS f z s)                            m = λ ()
out-open c (cutS l x s)                             m = λ ()
out-open c (lnS b s)                                m = λ ()
out-open c (takeS i q free s)                       m = λ ()
out-open c (takeS i q (cutAt r) s)                  m = λ ()
out-open c (takeS i q (overAt r) s)                 m = λ ()
out-open c (flatS op f d n q o ls)                  m = λ ()
out-open c (connS k o b)                            m = λ ()
out-open c (joinS j g x [])                         m = λ ()
out-open c (takeS i q (cpAt r) s)          ofM = λ ()
out-open c (takeS i q (cpAt r) s)          attM = λ ()
out-open c (takeS i q (cpAt r) s)          bodyM = λ ()
out-open c (takeS i q (cpAt r) s)          srcAttM = λ ()
out-open c (takeS i q (cpAt r) s)          owedM = λ ()
out-open c (takeS i q (cpAt r) s)          cpM with closed c
... | false = λ ()
... | true  = λ ()
out-open c (takeS i q (cpAt r) s)          cutM = λ ()
out-open c (takeS i q (cpAt r) s)          joinM = λ ()
out-open c (takeS i q (cpAt r) s)          leafM = λ ()
out-open c (joinS j false x (_ ∷ ib))      joinM = λ ()
out-open c (joinS j true x (_ ∷ ib))       joinM with closed c
... | false = λ _ → refl
... | true  = λ ()
out-open c (joinS j g x (_ ∷ ib))          ofM = λ ()
out-open c (joinS j g x (_ ∷ ib))          attM = λ ()
out-open c (joinS j g x (_ ∷ ib))          bodyM = λ ()
out-open c (joinS j g x (_ ∷ ib))          srcAttM = λ ()
out-open c (joinS j g x (_ ∷ ib))          owedM = λ ()
out-open c (joinS j g x (_ ∷ ib))          cpM = λ ()
out-open c (joinS j g x (_ ∷ ib))          cutM = λ ()
out-open c (joinS j g x (_ ∷ ib))          leafM = λ ()

whole : ∀ {R} → Conf R → St [] R
whole ⟨ c , s , m , p ⟩ = plug c s

-- What a configuration keeps of its positions: where a value rises, its
-- hole's own, the frames above keeping theirs of the run the value is in
-- (`Flight`), not of the ghost that has dropped it; else the whole tree's.
KeysAt : ∀ {R} → Conf R → Set
KeysAt ⟨ c , s , rising e , p ⟩    = Keyed s (envAt c)
KeysAt ⟨ c , s , subscribing , p ⟩ = Keys (plug c s)
KeysAt ⟨ c , s , absorbed , p ⟩    = Keys (plug c s)

Shaped : ∀ {R} → Conf R → Set
Shaped k = Frag (whole k) × KeysAt k

------------------------------------------------------------------------
-- The engine's race, as the winner's frames saw it

-- Strictly after a key; not before it.
KAfter KNotBefore : ∀ {A} → Key → Maybe (Key × Out A) → Set
KAfter     k nothing        = ⊤
KAfter     k (just (h , _)) = k <ᴷ h ≡ true
KNotBefore k nothing        = ⊤
KNotBefore k (just (h , _)) = h <ᴷ k ≡ false

-- Strictly before each of a node's own marks.
Before : Key → List (Mark × Key) → Set
Before k = All (λ mk → k <ᴷ proj₂ mk ≡ true)

-- Each lane of `ls`, sought as the engine's fold seeks it, `P` of `k`;
-- `acc` the lanes before, nearest first, `tl` the lanes after the list.
Race : ∀ {R Γ A B} → (Key → Maybe (Key × Out B) → Set) → Key → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → St Γ A
     → List (St Γ B) → List (St Γ B) → List (St Γ B) → Set
Race P k c op f d n q o acc []       tl = ⊤
Race P k c op f d n q o acc (x ∷ xs) tl = P k (cand (inLanes op f d n q o acc (xs ++ tl) c) x) × Race P k c op f d n q o (x ∷ acc) xs tl

-- The lane `s` won its flatMap's race: the outer and the newer lanes no
-- earlier, the older lanes strictly later.
record LaneWon {R Γ A B} (k : Key) (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) (pre post : List (St Γ B)) (s : St Γ B) : Set where
  constructor lane-won
  field
    outerW : KNotBefore k (cand (inOuter op f d n q (pre ʳ++ s ∷ post) c) o)
    olderW : Race KAfter k c op f d n q o [] (reverse pre) (s ∷ post)
    newerW : Race KNotBefore k c op f d n q o (s ∷ pre) post []

-- What runs under a completed outer, or where nothing is shown, rises
-- no value.
Unrisen : ∀ {A} → Bool → Out A → Set
Unrisen true (shows (nx a)) = ⊥
Unrisen _    _              = ⊤

unrisen-open : ∀ {A} b {a : A} → Unrisen b (shows (nx a)) → b ≡ false
unrisen-open false u = refl

-- A lane in the pool rises nothing.
Pooled : ∀ {A} → Bool → Out A → Set
Pooled false (shows _) = ⊥
Pooled _     _         = ⊤

pooled-live : ∀ b {A} {e} → Pooled {A} b (shows e) → b ≡ true
pooled-live true u = refl

-- The source's candidate, read as its connect's race reads it, no
-- earlier than a key.
Lost : ∀ {A} → Bool → Key → Maybe (Key × Out A) → Set
Lost v k nothing        = ⊤
Lost v k (just (h , _)) = (if v then h else shift h) <ᴷ k ≡ false

-- A body shows only while its connect is not over.
Showing : ∀ {A} → Bool → Out A → Set
Showing v still     = ⊤
Showing v (shows _) = v ≡ false

-- Every flatMap above the found node raced it in, each at the key and
-- event its candidate has there, and a value reaches its outer frame only
-- shown and before the outer completes, a lane's frame only from a live
-- lane; every connect's source lost to its body, and its body to its
-- source.
Won : ∀ {R Γ A} → Key × Out A → Ctx R Γ A → St Γ A → Set
Won h       top                                s = ⊤
Won (k , o) (inMap f c)                        s = Won (mapT f k o) c (mapS f s)
Won (k , o) (inScan f z c)                     s = Won (scanT f z k o) c (scanS f z s)
Won (k , o) (inCut l a c)                      s = Won (cutT l k o) c (cutS l a s)
Won h       (inLn b c)                         s = Won h c (lnS b s)
Won (k , o) (inTake i q w c)                   s = Won (takeT i q w k o) c (takeS i q w s)
Won (k , o) (inOuter op f d n q ls c)          s = Race KAfter k c op f d n q s [] ls [] × Won (outerK n q k o) c (flatS op f d n q s ls) × Unrisen (d ∨ closed c) o
Won (k , o) (inLanes op f d n q o′ pre post c) s =
  LaneWon k c op f d n q o′ pre post s × Pooled (alive s) o × Won (uncurry (laneT d n q) (cutT (alive s) k o)) c (flatS op f d n q o′ (pre ʳ++ s ∷ post))
Won (k , o) (inSrc kk b c)                     s =
  KAfter (if over kk then k else shift k) (cand (inBody kk s c) b) × Before (if over kk then k else shift k) (own (connS kk s b))
  × Won ((if over kk then k else shift k) , still) c (connS kk s b)
Won (k , o) (inBody kk o′ c)                   s = Showing (over kk) o × Lost (over kk) k (cand (inSrc kk s c) o′) × Before k (own (connS kk o′ s)) × Won (k , o) c (connS kk o′ s)

-- A key past a live source's skips: after every position under it.
past : Bool → Key → Key
past true  k         = k
past false (at p)    = after p
past false (after p) = after p

-- Every race above a still found node, at its key read past each live
-- source's skips: every flatMap's as `Won` reads it; at a connect's
-- source, its body and its own marks after; at its body, its source no
-- earlier and its own marks after.
Beat : ∀ {R Γ A} → Key → Ctx R Γ A → St Γ A → Set
Beat k top                                s = ⊤
Beat k (inMap f c)                        s = Beat k c (mapS f s)
Beat k (inScan f z c)                     s = Beat k c (scanS f z s)
Beat k (inCut l a c)                      s = Beat k c (cutS l a s)
Beat k (inLn b c)                         s = Beat k c (lnS b s)
Beat k (inTake i q w c)                   s = Beat k c (takeS i q w s)
Beat k (inOuter op f d n q ls c)          s = Race KAfter k c op f d n q s [] ls [] × Beat k c (flatS op f d n q s ls)
Beat k (inLanes op f d n q o pre post c)  s = LaneWon k c op f d n q o pre post s × Beat k c (flatS op f d n q o (pre ʳ++ s ∷ post))
Beat k (inSrc kk b c)                     s =
  KAfter (past (over kk) k) (cand (inBody kk s c) b) × Before (past (over kk) k) (own (connS kk s b)) × Beat (past (over kk) k) c (connS kk s b)
Beat k (inBody kk o c)                    s = KNotBefore k (cand (inSrc kk s c) o) × Before k (own (connS kk o s)) × Beat k c (connS kk o s)

-- What the search finds still beats every race above it.
Beats : ∀ {R} → Maybe (Found R) → Set
Beats nothing                                  = ⊤
Beats (just (found (Γ , A , c , s) m key)) = outOf c s m ≡ still → Beat key c s

Apart : ∀ {R} → St [] R → Set
Apart t = Beats (search top t)

-- Where the search runs, the tree is apart.
Searched : ∀ {R} → Conf R → Set
Searched ⟨ c , s , subscribing , p ⟩ = ⊤
Searched ⟨ c , s , absorbed , p ⟩    = Apart (plug c s)
Searched ⟨ c , s , rising e , p ⟩    = ⊤

-- A rise is read by an open observer: every leaf and every owed end asks
-- before it rises, and a frame's rise passes only to one no more closed.
Heard : ∀ {R} → Conf R → Set
Heard ⟨ c , s , rising e , p ⟩   = closed c ≡ false
Heard ⟨ c , s , subscribing , p ⟩ = ⊤
Heard ⟨ c , s , absorbed , p ⟩    = ⊤

record Order {R} (k : Conf R) : Set where
  constructor order
  field
    shape  : Shaped k
    flight : Flight k
    lead   : Lead k
    apart  : Searched k
    heard  : Heard k
    ghosted : Gh top (whole k)

postulate
  -- The engine's search: the found node's key leads every race above it.
  search-won : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} → Frag t → search top t ≡ just (found (Γ , A , c , s) m key)
             → Won (key , outOf c s m) c s

------------------------------------------------------------------------
-- From the race to the stepper's heads

after-step : ∀ {Γ A} q (x : Maybe (Key × Out A)) (st : Step Γ A) → KAfter (at q) x → Agrees x st → After q (headˢ st)
after-step q _ (outˢ h a n) w (exact refl) = subst (λ b → b ≡ true) (at-<ᵖ q h) w
after-step q _ (skipˢ h n)  w (exact refl) = subst (λ b → b ≡ true) (at-<ᵖ q h) w
after-step q _ (endˢ h)     w (exact refl) = subst (λ b → b ≡ true) (at-<ᵖ q h) w
after-step q _ hushˢ        w (exact refl) = tt
after-step q (just (k , still)) st w (early u) with headˢ st
... | nothing = tt
... | just h  = subst (λ b → b ≡ true) (at-<ᵖ q h) (<≮ᴷ (at q) k (at h) w u)

not-before-step : ∀ {Γ A} q (x : Maybe (Key × Out A)) (st : Step Γ A) → KNotBefore (at q) x → Agrees x st → NotBefore q (headˢ st)
not-before-step q _ (outˢ h a n) w (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ h q) w
not-before-step q _ (skipˢ h n)  w (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ h q) w
not-before-step q _ (endˢ h)     w (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ h q) w
not-before-step q _ hushˢ        w (exact refl) = tt
not-before-step q (just (k , still)) st w (early u) with headˢ st
... | nothing = tt
... | just h  = subst (λ b → b ≡ false) (at-<ᵖ h q) (≮ᴷ-trans (at h) k (at q) u w)

-- A node's head, read at an open observer.
open-agrees : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → closed c ≡ false → Frag s → Agrees (cand c s) (step (gh s))
open-agrees c s cl fs = subst (λ b → HeadAt b (cand c s) s) cl (head-agrees c s fs)

-- Each live lane of a race, its step's head related as its candidate.
race-steps : ∀ {R Γ A B} (P : Key → Maybe (Key × Out B) → Set) (Q : Maybe Pos → Set) (k : Key)
           → (∀ {Γ′} (x : Maybe (Key × Out B)) (st : Step Γ′ B) → P k x → Agrees x st → Q (headˢ st))
           → ∀ (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) acc ls tl → closed c ≡ false → Lanes ls
           → Race P k c op f d n q o acc ls tl → All (λ m → Q (headˢ (step m))) (lanesL ls)
race-steps P Q k h c op f d n q o acc [] tl cl _ _ = []
race-steps P Q k h c op f d n q o acc (lnS true (cutS true a y) ∷ xs) tl cl (fy , fl) (r , rs) =
  all-++⁺ (race-steps P Q k h c op f d n q o (lnS true (cutS true a y) ∷ acc) xs tl cl fl rs)
          (h _ (step (gh y)) r (open-agrees (inLn true (inLanes op f d n q o acc (xs ++ tl) c)) (cutS true a y) cl fy) ∷ [])
race-steps P Q k h c op f d n q o acc (lnS false (cutS false a y) ∷ xs) tl cl (fy , fl) (r , rs) =
  all-++⁺ (race-steps P Q k h c op f d n q o (lnS false (cutS false a y) ∷ acc) xs tl cl fl rs) []

-- An open frame's node read through the ended connects in scope
-- (`Scope.closures`) steps as its candidate, as the plain node does: a
-- shut tells only a joiner a pending subscription makes, under that
-- subscription's mark (`Head.Race.sub-head`).  Over `Frag` alone it is
-- false: a live joiner of an ended connect, nothing queued, has no
-- candidate and ends once shut.  The machine feeds every live joiner its
-- connect's end (`Machine.rise`), which `Scope.Gh` keeps (`Scope.gh-told`).
shut-head : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → closed c ≡ false → Frag s → Gh c s
          → Agrees (cand c s) (step (shutAll (closures c) (gh s)))
shut-head c s cl fs g = subst (λ b → HeadAtⁿ b (cand c s) (shutAll (closures c) (gh s))) cl (head-agreesⱽ c s (closures c) (gh-told c s g) fs)

-- Likewise, each read through the ended connects in scope.
race-shut : ∀ {R Γ A B} (P : Key → Maybe (Key × Out B) → Set) (Q : Maybe Pos → Set) (k : Key)
          → (∀ {Γ′} (x : Maybe (Key × Out B)) (st : Step Γ′ B) → P k x → Agrees x st → Q (headˢ st))
          → ∀ (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) acc ls tl → closed c ≡ false → Lanes ls
          → Ghᴸ c op f d n q o acc (ls ++ tl)
          → Race P k c op f d n q o acc ls tl → All (λ m → Q (headˢ (step (shutAll (closures c) m)))) (lanesL ls)
race-shut P Q k h c op f d n q o acc [] tl cl _ _ _ = []
race-shut P Q k h c op f d n q o acc (lnS true (cutS true a y) ∷ xs) tl cl (fy , fl) (gy , gl) (r , rs) =
  all-++⁺ (race-shut P Q k h c op f d n q o (lnS true (cutS true a y) ∷ acc) xs tl cl fl gl rs)
          (h _ (step (shutAll (closures c) (gh y))) r (shut-head (inLn true (inLanes op f d n q o acc (xs ++ tl) c)) (cutS true a y) cl fy gy) ∷ [])
race-shut P Q k h c op f d n q o acc (lnS false (cutS false a y) ∷ xs) tl cl (fy , fl) (_ , gl) (r , rs) =
  all-++⁺ (race-shut P Q k h c op f d n q o (lnS false (cutS false a y) ∷ acc) xs tl cl fl gl rs) []

-- A flatMap's lanes, at their places in the list.
lanes-gh : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
         → Gh top (plug c (flatS op f d n q o ls)) → Ghᴸ c op f d n q o [] (ls ++ [])
lanes-gh c op f d n q o ls gt =
  subst (Ghᴸ c op f d n q o []) (sym (++-identityʳ ls)) (proj₂ (proj₂ (gh-at c (flatS op f d n q o ls) gt)))

-- A subscribed connect's source, read so, steps as its candidate.
shut-agrees : ∀ {R Γ X B} (c : Ctx R Γ B) sl sa as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug c (connS (cs false sl sa nothing as ow r en) o b)) → Gh top (plug c (connS (cs false sl sa nothing as ow r en) o b))
            → Agrees (cand (inSrc (cs false sl sa nothing as ow r en) b c) o) (step (shutAll (closures c) (gh o)))
shut-agrees c sl sa as ow r en o b ft gt =
  shut-head (inSrc K b c) o refl (conn-src K o b (fr-at c (connS K o b) ft)) (proj₁ (proj₂ (gh-at c (connS K o b) gt)))
  where K = cs false sl sa nothing as ow r en

lanes-split : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Lanes (pre ++ s ∷ post) → Lanes pre × Lane s × Lanes post
lanes-split []        (l , ls) = tt , l , ls
lanes-split (x ∷ pre) (l , ls) with lanes-split pre ls
... | u , v , w = (l , u) , v , w

-- A lane's context keeps the lanes before it nearest first.
lanes-ʳsplit : ∀ {Γ A} (pre : List (St Γ A)) {s post} → Lanes (pre ʳ++ s ∷ post) → Lanes (reverse pre) × Lane s × Lanes post
lanes-ʳsplit pre l = lanes-split (reverse pre) (subst Lanes (ʳ++-defn pre) l)

------------------------------------------------------------------------
-- From the stepper's heads to the meaning's

-- What the stepper shows of a flatMap's other parts, a lane rising at `p`.
record StepSides {Γ A B} (p : Pos) d (o : St Γ A) (pre post : List (St Γ B)) (s : St Γ B) : Set₁ where
  constructor step-sides
  field
    newerS : All (λ m → NotBefore p (headˢ (step m))) (lanesL post)
    olderS : All (λ m → After p (headˢ (step m))) (lanesL pre)
    outerS : d ≡ false → NotBefore p (headˢ (step (gh o)))
    poolS  : step (poolG d (gh o) (deadL (pre ++ s ∷ post))) ≡ hushˢ

-- A pool leaves nothing running before any position: its lanes are dead,
-- and a dead lane has no connect.
pool-link : ∀ {R Γ A B} (c : Ctx R Γ B) q op (f : A → Obs Timeline Γ B) n q′ (o : St Γ A) ls
          → Frag (plug c (flatS op f false n q′ o ls)) → TailNotBefore q (poolT (deadL ls) (envAt c))
pool-link {B = B} c q op f n q′ o ls ft =
  subst (TailNotBefore q) (sym (dead-idle {B = B} ls (envAt c) (proj₂ (frag-parts op f false n q′ o ls (frag-flat c op f false n q′ o ls ft))))) tt

postulate
  -- The meaning's heads are the stepper's, every running source in scope
  -- clear of `p`; a pool the stepper hushes leaves nothing running.
  --
  -- REFUTED: 74fd133e `sides-link` without `Scope`, by a newer lane joined to
  --   a running source and fed nothing: its step hushes, its meaning shows
  --   the source.
  sides-link : ∀ {R Γ A B} (c : Ctx R Γ B) p (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre post (s : St Γ B)
             → Frag (plug c (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ s ∷ post))) → Scope p c → StepSides p d o (reverse pre) post s
             → Sides p f d o (reverse pre) post (envAt c)

  -- A bounded, switching or exhausting flatMap's lane that won: its
  -- queue and its one-lane rule sit outside the stepper's race, so the
  -- merge clause's route does not apply as written.
  --
  -- REFUTED: 07e6d07a `limited-sides` without `Scope`, by a switch whose outer
  --   joins a running source and is fed nothing: no candidate, so the lane
  --   wins, while the outer's meaning shows the source.
  limited-sides : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
                → (op ≡ mergeᶠ nothing → ⊥) → closed c ≡ false → Scope p c → LaneWon (at p) c op f d n q o pre post s
                → Frag (plug c (flatS op f d n q o (pre ʳ++ s ∷ post))) → Sides p f d o (reverse pre) post (envAt c)

-- A candidate lost to its body: lost where the race reads it past.
lost-past : ∀ {A} v k (x : Maybe (Key × Out A)) → Lost v k x → Lost false k x
lost-past false k x                    lo = lo
lost-past true  k nothing              lo = tt
lost-past true  k (just (at h , _))    lo = ≮ᴷ-trans (at (h ++ [ ix 0 ])) (at h) k (ext-≮ h [ ix 0 ]) lo
lost-past true  k (just (after h , _)) lo = lo

-- A source's step, its candidate lost to a body at `p`, shows at or past `p`.
lost-floor : ∀ {Γ A} p (x : Maybe (Key × Out A)) (t : Step Γ A) → Lost false (at p) x → Agrees x t → FloorAt p (headˢ t)
lost-floor p _ (outˢ h a n) lo (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ (h ++ [ ix 0 ]) p) lo
lost-floor p _ (skipˢ h n)  lo (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ (h ++ [ ix 0 ]) p) lo
lost-floor p _ (endˢ h)     lo (exact refl) = subst (λ b → b ≡ false) (at-<ᵖ (h ++ [ ix 0 ]) p) lo
lost-floor p _ hushˢ        lo _            = tt
lost-floor p (just (k , still)) (outˢ h a n) lo (early u) =
  subst (λ b → b ≡ false) (at-<ᵖ (h ++ [ ix 0 ]) p) (≮ᴷ-trans (at (h ++ [ ix 0 ])) (shift k) (at p) (shift-≮ h k u) lo)
lost-floor p (just (k , still)) (skipˢ h n)  lo (early u) =
  subst (λ b → b ≡ false) (at-<ᵖ (h ++ [ ix 0 ]) p) (≮ᴷ-trans (at (h ++ [ ix 0 ])) (shift k) (at p) (shift-≮ h k u) lo)
lost-floor p (just (k , still)) (endˢ h)     lo (early u) =
  subst (λ b → b ≡ false) (at-<ᵖ (h ++ [ ix 0 ]) p) (≮ᴷ-trans (at (h ++ [ ix 0 ])) (shift k) (at p) (shift-≮ h k u) lo)

-- A subscription headed past `q`, its environment in order, shows at or
-- past `q`.
sub-meaning : ∀ {Γ A} (o : Obs Timeline Γ A) r (ρ : NEnv Γ) q → Headed r → Sorted ρ → q <ᵖ r ≡ true → Floorᴱ q (meaning (subscribe o r) ρ)
sub-meaning o r ρ q hr so lt with meaning (subscribe o r) ρ | past-sub o q r ρ hr so lt
... | out h _ _ | pe = past-floor q h (proj₂ (proj₁ (every pe)))
... | skip h _  | pe = past-floor q h (proj₂ (proj₁ (every pe)))
... | end h     | pe = past-floor q h (proj₂ (every pe))
... | hush      | pe = tt

-- A connect's source, its race lost to a body at `p` and every running
-- source above at or past `p`, shows at or past `p`.  Subscribed, its
-- step agrees with the candidate that lost, and its meaning starts there
-- or past a source above; not yet, it subscribes at the connect's own
-- mark, after `p`.
src-floor : ∀ {R Γ X B} p (c : Ctx R Γ B) kk (o : St Γ X) (b : St (X ∷ Γ) B)
          → Lost false (at p) (cand (inSrc kk b c) o) → Before (at p) (own (connS kk o b)) → Frag (plug c (connS kk o b)) → Gh top (plug c (connS kk o b)) → Keys (plug c (connS kk o b)) → Scope p c
          → FloorSrc p (srcG kk o) (envAt c)
src-floor p c (cs false sl sa nothing as ow r en) o b lo bf ft gt kt sc =
  shut-floor p (closures c) (gh o) (envAt c) (ended-at c)
    (first-floor (modes c) (envAt c) p (step V) (meaning V (envAt c)) sc
      (first {ν = modes c} V (envAt c) (proj₁ G) (proj₂ G))
      (lost-floor p (cand (inSrc K b c) o) (step V) lo (shut-agrees c sl sa as ow r en o b ft gt)))
  where K = cs false sl sa nothing as ow r en
        V = shutAll (closures c) (gh o)
        G = proj₁ (gh-at c (connS K o b) gt)
src-floor p c (cs true sl sa nothing as ow r en) o b lo bf ft gt kt sc = tt
src-floor p c (cs cl sl sa (just q) nothing ow r en) (pend o) b lo (bm ∷ _) ft gt kt sc =
  sub-meaning o (q ⊕ [ ix 1 ]) (envAt c) p (proj₁ (ConnAt.sub (proj₁ (keyed-at c (connS K (pend o) b) kt))))
    (envAt-sorted c (connS K (pend o) b) (ft , kt)) (subst (λ b → b ≡ true) (at-<ᵖ p (q ⊕ [ ix 1 ])) bm)
  where K = cs cl sl sa (just q) nothing ow r en
src-floor p c (cs cl sl sa (just q) (just x) ow r en) o b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ o b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (coldS x y) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (coldS x y) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (ofS x y z) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (ofS x y z) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (doneS) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (doneS) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (mapS x y) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (mapS x y) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (scanS x y z) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (scanS x y z) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (cutS x y z) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (cutS x y z) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (lnS x y) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (lnS x y) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (takeS x y z w) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (takeS x y z w) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (flatS x y z w u v t) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (flatS x y z w u v t) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (connS x y z) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (connS x y z) b) ft)
src-floor p c (cs cl sl sa (just q) nothing ow r en) (joinS x y z w) b lo bf ft gt kt sc = ⊥-elim (fr-at c (connS _ (joinS x y z w) b) ft)

-- Every running source in scope at or past a key's position; past an
-- `after`, nothing asked.
FloorK : ∀ {Γ} → Key → All (λ _ → Mode) Γ → NEnv Γ → Set
FloorK (at p)    ν ρ = Floor ν p ρ
FloorK (after p) ν ρ = ⊤

-- The key a frame's retag passes up: the same, or just past it.
data Rises (k : Key) : Key → Set where
  same  : Rises k k
  moved : Rises k (shift k)

rises-floor : ∀ {Γ} {k k′} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) → Rises k k′ → FloorK k′ ν ρ → FloorK k ν ρ
rises-floor               ν ρ same  f = f
rises-floor {k = at p}    ν ρ moved f = floor-lower ν ρ p (p ++ [ ix 0 ]) (<ᵖ-below p []) f
rises-floor {k = after p} ν ρ moved f = tt

map-rises : ∀ {A B} (f : A → B) k (o : Out A) → Rises k (proj₁ (mapT f k o))
map-rises f k still     = same
map-rises f k (shows e) = same

scan-rises : ∀ {A B} (f : B → A → B) z k (o : Out A) → Rises k (proj₁ (scanT f z k o))
scan-rises f z k (shows (nx a)) = same
scan-rises f z k (shows cp)     = same
scan-rises f z k still          = same

take-rises : ∀ {A} i (q : A → Bool) w k (o : Out A) → Rises k (proj₁ (takeT i q w k o))
take-rises true  q free k (shows (nx a)) with q a
... | true  = same
... | false = moved
take-rises false q free k (shows (nx a)) with q a
... | true  = same
... | false = same
take-rises i q free       k (shows cp) = same
take-rises i q free       k still      = same
take-rises i q (cpAt r)   k o          = same
take-rises i q (cutAt r)  k o          = same
take-rises i q (overAt r) k o          = same

outer-rises : ∀ {A B : Set} n (q : List A) k (o : Out A) → Rises k (proj₁ (outerK {B = B} n q k o))
outer-rises n q k (shows cp)     = same
outer-rises n q k (shows (nx a)) = moved
outer-rises n q k still          = same

lane-rises : ∀ {A B : Set} d n (q : List A) k (o : Out B) → Rises k (proj₁ (laneT d n q k o))
lane-rises d n []      k (shows cp)     = same
lane-rises d n (_ ∷ _) k (shows cp)     = moved
lane-rises d n []      k (shows (nx a)) = same
lane-rises d n (_ ∷ _) k (shows (nx a)) = same
lane-rises d n []      k still          = same
lane-rises d n (_ ∷ _) k still          = same

src-rises : ∀ kk k → Rises k (if over kk then k else shift k)
src-rises kk k with over kk
... | true  = same
... | false = moved

-- Up the found node's frames: every connect the pick passes runs its
-- source at or past where the pick lands there.
won-floor : ∀ {R Γ A} k o (c : Ctx R Γ A) (s : St Γ A) → Won (k , o) c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → FloorK k (modes c) (envAt c)
won-floor (at p)    o top s w ft gt kt = tt
won-floor (after p) o top s w ft gt kt = tt
won-floor k o (inMap f c) s w ft gt kt =
  rises-floor (modes c) (envAt c) (map-rises f k o) (won-floor (proj₁ (mapT f k o)) (proj₂ (mapT f k o)) c (mapS f s) w ft gt kt)
won-floor k o (inScan f z c) s w ft gt kt =
  rises-floor (modes c) (envAt c) (scan-rises f z k o) (won-floor (proj₁ (scanT f z k o)) (proj₂ (scanT f z k o)) c (scanS f z s) w ft gt kt)
won-floor k o (inCut l a c) s w ft gt kt = won-floor k (proj₂ (cutT l k o)) c (cutS l a s) w ft gt kt
won-floor k o (inLn b c) s w ft gt kt = won-floor k o c (lnS b s) w ft gt kt
won-floor k o (inTake i q w c) s wn ft gt kt =
  rises-floor (modes c) (envAt c) (take-rises i q w k o) (won-floor (proj₁ (takeT i q w k o)) (proj₂ (takeT i q w k o)) c (takeS i q w s) wn ft gt kt)
won-floor k o (inOuter op f d n q ls c) s (_ , w , _) ft gt kt =
  rises-floor (modes c) (envAt c) (outer-rises n q k o) (won-floor (proj₁ (outerK n q k o)) (proj₂ (outerK n q k o)) c (flatS op f d n q s ls) w ft gt kt)
won-floor k o (inLanes op f d n q o′ pre post c) s (_ , _ , w) ft gt kt =
  rises-floor (modes c) (envAt c) (lane-rises d n q k o′′)
    (won-floor (proj₁ (laneT d n q k o′′)) (proj₂ (laneT d n q k o′′)) c (flatS op f d n q o′ (pre ʳ++ s ∷ post)) w ft gt kt)
  where o′′ = if alive s then o else still
won-floor k o (inSrc kk b c) s (_ , _ , w) ft gt kt =
  rises-floor (modes c) (envAt c) (src-rises kk k) (won-floor (if over kk then k else shift k) still c (connS kk s b) w ft gt kt)
won-floor (after p) o (inBody kk o′ c) s w ft gt kt = tt
won-floor (at p) o (inBody kk o′ c) s (_ , lo , bf , w) ft gt kt =
  scope-src (modes c) p (srcG kk o′) (envAt c)
    (src-floor p c kk o′ s (lost-past (over kk) (at p) (cand (inSrc kk s c) o′) lo) bf ft gt kt sc) sc
  where sc = won-floor (at p) o c (connS kk o′ s) w ft gt kt

-- Every connect the pick passes on its way up runs its source at or past
-- where the pick lands.
won-scope : ∀ {R Γ A} p o (c : Ctx R Γ A) (s : St Γ A) → Won (at p , o) c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → Scope p c
won-scope p o c s w ft gt kt = won-floor (at p) o c s w ft gt kt

-- An outer first: its flatMap's lanes, each after it as the race read
-- them and every running source in scope clear of it, are after it in
-- the meaning.
--
-- REFUTED: 74fd133e `outer-link` without `Scope`, by a lane joined to a
--   running source and fed nothing: its step hushes, its meaning shows the
--   source.
outer-link : ∀ {R Γ A B} (c : Ctx R Γ B) q op (f : A → Obs Timeline Γ B) n q′ (o : St Γ A) ls
           → Frag (plug c (flatS op f false n q′ o ls)) → Gh top (plug c (flatS op f false n q′ o ls)) → Scope q c
           → All (λ m → After q (headˢ (step (shutAll (closures c) m)))) (lanesL ls)
           → All (λ l → After q (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore q (poolT (deadL ls) (envAt c))
outer-link c q op f n q′ o ls ft gt sc hs =
  shut-states q (closures c) (lanesL ls) (envAt c) (ended-at c)
    (firsts-after (modes c) (envAt c) q V sc (firstᴸ {ν = modes c} V (envAt c) (proj₁ L) (proj₂ L))
      (all-map⁺ hs))
  , pool-link c q op f n q′ o ls ft
  where V = map (shutAll (closures c)) (lanesL ls)
        L = proj₁ (gh-at c (flatS op f false n q′ o ls) gt)

-- The frame a lane won: what the pick establishes of its siblings.
lane-sides : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
           → closed c ≡ false → Scope p c → LaneWon (at p) c op f d n q o pre post s → Frag (plug c (flatS op f d n q o (pre ʳ++ s ∷ post)))
           → Frag (flatS op f d n q o (pre ʳ++ s ∷ post)) → Sides p f d o (reverse pre) post (envAt c)
lane-sides p c (mergeᶠ nothing) f d n [] o pre post s cl sc (lane-won wo wold wnew) ft (fo , fl , en , dd) =
  sides-link c p f d n o pre post s ft sc
    (step-sides (race-steps KNotBefore (NotBefore p) (at p) (not-before-step p) c (mergeᶠ nothing) f d n [] o (s ∷ pre) post [] cl
                  (proj₂ (proj₂ (lanes-ʳsplit pre fl))) wnew)
                (race-steps KAfter (After p) (at p) (after-step p) c (mergeᶠ nothing) f d n [] o [] (reverse pre) (s ∷ post) cl
                  (proj₁ (lanes-ʳsplit pre fl)) wold)
                (λ { refl → not-before-step p _ (step (gh o)) wo (open-agrees (inOuter (mergeᶠ nothing) f false n [] (pre ʳ++ s ∷ post) c) o cl fo) })
                (subst (λ ls → step (poolG d (gh o) (deadL ls)) ≡ hushˢ) (ʳ++-defn pre) (pool-step d o (pre ʳ++ s ∷ post) fo fl (λ e → proj₂ (dd e)))))
lane-sides p c (mergeᶠ (just m)) f d n q o pre post s cl sc w ft _ = limited-sides p c (mergeᶠ (just m)) f d n q o pre post s (λ ()) cl sc w ft
lane-sides p c switchᶠ f d n q o pre post s cl sc w ft _ = limited-sides p c switchᶠ f d n q o pre post s (λ ()) cl sc w ft
lane-sides p c exhaustᶠ f d n q o pre post s cl sc w ft _ = limited-sides p c exhaustᶠ f d n q o pre post s (λ ()) cl sc w ft

-- A live lane's value passes its flatMap's retag unchanged.
lane-on : ∀ {R Γ A B} d n (q : List A) {b} {k} (a : B) {c : Ctx R Γ B} {t} → b ≡ true
        → Won (uncurry (laneT d n q) (cutT b k (shows (nx a)))) c t → Won (k , shows (nx a)) c t
lane-on d n []      a refl w = w
lane-on d n (_ ∷ _) a refl w = w

-- A still candidate's lane passes its flatMap's retag as it is.
lane-still : ∀ {R Γ A B} d n (q : List A) b {k} {c : Ctx R Γ B} {t} → Won (uncurry (laneT d n q) (cutT b k still)) c t → Won (k , still) c t
lane-still d n []      true  w = w
lane-still d n []      false w = w
lane-still d n (_ ∷ _) true  w = w
lane-still d n (_ ∷ _) false w = w

postulate
  -- A LIVE SOURCE'S WON SKIP IS AHEAD UNDER IT: every frame above a
  -- connect whose source won at `k` is ahead of each position under `k`.
  won-src : ∀ {R Γ X B} k (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
          → KAfter (shift (at k)) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
          → Won (shift (at k) , still) c (connS (cs false true sa ba as nothing r en) o b)
          → Frag (plug c (connS (cs false true sa ba as nothing r en) o b)) → showsᶜ c true ≡ true → Ahead (Under (_≡ k)) c true
  -- A body first: the source's candidate, which its connect's race did not
  -- put before it, and the connect's own marks, after it, put the source's
  -- meaning no earlier; a source hushed leaves nothing running.
  body-link : ∀ {R Γ X B} q (c : Ctx R Γ B) kk (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug c (connS kk o b)) → closed c ≡ false → over kk ≡ false
            → Lost false (at q) (cand (inSrc kk b c) o) → Before (at q) (own (connS kk o b))
            → (Events∞.force (srcState (srcG kk o) (envAt c)) ≡ hush → ∀ d → Agreeᵀ d (Events∞.cut (srcState (srcG kk o) (envAt c))) idle)
              × NotBefore q (shown (Events∞.force (srcState (srcG kk o) (envAt c))))

-- A still candidate that won is ahead at its key in every frame above
-- it that shows it.
won-ahead : ∀ {R Γ A} k (c : Ctx R Γ A) (s : St Γ A) f → Won (at k , still) c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → showsᶜ c f ≡ true → Ahead (_≡ k) c f
won-ahead k top                     s f w ft gt kt sh = tt
won-ahead k (inMap g c)             s f w ft gt kt sh = won-ahead k c (mapS g s) true w ft gt kt sh
won-ahead k (inScan g z c)          s f w ft gt kt sh = won-ahead k c (scanS g z s) true w ft gt kt sh
won-ahead k (inCut true a c)        s f w ft gt kt sh = won-ahead k c (cutS true a s) true w ft gt kt sh
won-ahead k (inCut false a c)       s f w ft gt kt ()
won-ahead k (inLn b c)              s f w ft gt kt sh = won-ahead k c (lnS b s) b w ft gt kt sh
won-ahead k (inTake i q free c)     s f w ft gt kt sh = won-ahead k c (takeS i q free s) true w ft gt kt sh
won-ahead k (inTake i q (cpAt _) c)   s f w ft gt kt ()
won-ahead k (inTake i q (cutAt _) c)  s f w ft gt kt ()
won-ahead k (inTake i q (overAt _) c) s f w ft gt kt ()
won-ahead k (inOuter op g true n q ls c) s f w ft gt kt ()
won-ahead k (inOuter op g false n q ls c) s f wn@(r , w , _) ft gt kt sh =
  (λ { _ refl → outer-link c k op g n q s ls ft gt (won-scope k still (inOuter op g false n q ls c) s wn ft gt kt)
                  (race-shut KAfter (After k) (at k) (after-step k) c op g false n q s [] ls [] cl (proj₂ parts) (lanes-gh c op g false n q s ls gt) r) })
  , won-ahead k c (flatS op g false n q s ls) true w ft gt kt sh
  where
    cl    = shows-open c true sh
    parts = frag-parts op g false n q s ls (frag-flat c op g false n q s ls ft)
won-ahead k (inLanes op g d n q o pre post c) s false w ft gt kt ()
won-ahead k (inLanes op g d n q o pre post c) s true wn@(l , _ , w) ft gt kt sh =
  (λ { _ refl → lane-sides k c op g d n q o pre post s (shows-open c true sh)
                  (won-scope k still (inLanes op g d n q o pre post c) s wn ft gt kt) l ft (frag-flat c op g d n q o (pre ʳ++ s ∷ post) ft) })
  , won-ahead k c (flatS op g d n q o (pre ʳ++ s ∷ post)) true (lane-still d n q (alive s) {at k} {c} w) ft gt kt sh
won-ahead k (inSrc (cs false true sa ba as nothing r en) b c) s f (ka , _ , w) ft gt kt sh = won-src k c sa ba as r en s b ka w ft sh
won-ahead k (inSrc (cs false true sa ba as (just _) r en) b c) s f w ft gt kt ()
won-ahead k (inSrc (cs false false sa ba as ow r en) b c)      s f w ft gt kt ()
won-ahead k (inSrc (cs true sl sa ba as ow r en) b c)          s f w ft gt kt ()
won-ahead k (inBody (cs cl true sa ba as nothing r en) o c) s f (_ , lo , bf , w) ft gt kt sh =
  proj₁ bb , (λ { _ refl → proj₂ bb }) , won-ahead k c (connS (cs cl true sa ba as nothing r en) o s) true w ft gt kt sh
  where bb = body-link k c (cs cl true sa ba as nothing r en) o s ft (shows-open c true sh) refl lo bf
won-ahead k (inBody (cs cl true sa ba as (just _) r en) o c) s f w ft gt kt ()
won-ahead k (inBody (cs cl false sa ba as ow r en) o c)      s f w ft gt kt ()

-- Up the found node's frames: each one the value reaches is clear there.
-- `s` is the node the search saw, `s′` the one the rise leaves.
won-clear : ∀ {R Γ A} p (a : A) (c : Ctx R Γ A) (s s′ : St Γ A) → alive s ≡ alive s′ → closed c ≡ false
          → Won (at p , shows (nx a)) c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → Clear p a c s′
won-clear p a top                               s s′ al ce w ft gt kt = tt
won-clear p a (inMap f c)                       s s′ al ce w ft gt kt = won-clear p (f a) c (mapS f s) (mapS f s′) refl ce w ft gt kt
won-clear p a (inScan f z c)                    s s′ al ce w ft gt kt = won-clear p (f z a) c (scanS f z s) (scanS f (f z a) s′) refl ce w ft gt kt
won-clear p a (inCut true x c)                  s s′ al ce w ft gt kt = λ _ → won-clear p a c (cutS true x s) (cutS true x s′) refl ce w ft gt kt
won-clear p a (inCut false x c)                 s s′ al ce w ft gt kt = λ ()
won-clear p a (inLn b c)                        s s′ al ce w ft gt kt = won-clear p a c (lnS b s) (lnS b s′) refl ce w ft gt kt
won-clear p a (inTake i q free c)               s s′ al ce w ft gt kt with q a | i
... | true  | _     = (λ _ → won-clear p a c (takeS _ q free s) (takeS _ q free s′) refl ce w ft gt kt) , (λ ())
... | false | true  = (λ ()) , (λ _ _ → won-clear (p ⊕ [ ix 0 ]) a c (takeS true q free s) (takeS true q (cpAt p) s′) refl ce w ft gt kt)
... | false | false = (λ ()) , (λ _ ())
won-clear p a (inTake i q (cpAt r) c)           s s′ al ce w ft gt kt = tt
won-clear p a (inTake i q (cutAt r) c)          s s′ al ce w ft gt kt = tt
won-clear p a (inTake i q (overAt r) c)         s s′ al ce w ft gt kt = tt
won-clear p a (inOuter op f true n q ls c)      s s′ al ce (_ , _ , ()) ft gt kt
won-clear p a (inOuter op f false n q ls c)     s s′ al ce wn@(r , w , u) ft gt kt =
  cl , proj₁ ol , proj₂ ol , won-ahead (p ⊕ [ ix 0 ]) c (flatS op f false n q s ls) true w ft gt kt
  where
    cl    = unrisen-open (closed c) u
    parts = frag-parts op f false n q s ls (frag-flat c op f false n q s ls ft)
    ol    = outer-link c p op f n q s ls ft gt (won-scope p (shows (nx a)) (inOuter op f false n q ls c) s wn ft gt kt) (race-shut KAfter (After p) (at p) (after-step p) c op f false n q s [] ls [] cl (proj₂ parts) (lanes-gh c op f false n q s ls gt) r)
won-clear p a (inLanes op f d n q o pre post c) s s′ al ce wn@(l , _ , w) ft gt kt lv =
  lane-sides p c op f d n q o pre post s ce (won-scope p (shows (nx a)) (inLanes op f d n q o pre post c) s wn ft gt kt) l ft (frag-flat c op f d n q o (pre ʳ++ s ∷ post) ft)
  , won-clear p a c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s′ ∷ post)) refl ce
      (lane-on d n q {alive s} {at p} a {c} {flatS op f d n q o (pre ʳ++ s ∷ post)} (trans al lv) w) ft gt kt
won-clear p a (inSrc kk b c)                    s s′ al ce (w , _) ft gt kt with over kk
... | true  = λ ()
... | false = λ _ cl → after-step (p ⊕ [ ix 0 ]) (cand (inBody kk s c) b) (step (gh b)) w (open-agrees (inBody kk s c) b cl (frag-body c kk s b ft))
won-clear p a (inBody (cs cl true sa ba as nothing r en) o c) s s′ al ce (_ , lo , bf , w) ft gt kt =
  proj₁ bb , proj₂ bb , won-clear p a c (connS (cs cl true sa ba as nothing r en) o s) (connS (cs cl true sa ba as nothing r en) o s′) refl ce w ft gt kt
  where bb = body-link p c (cs cl true sa ba as nothing r en) o s ft ce refl lo bf
won-clear p a (inBody (cs cl true sa ba as (just _) r en) o c)  s s′ al ce (() , _) ft gt kt
won-clear p a (inBody (cs cl false sa ba as (just _) r en) o c) s s′ al ce (() , _) ft gt kt
won-clear p a (inBody (cs cl false sa ba as nothing r en) o c)  s s′ al ce (() , _) ft gt kt

-- A lane's completion passes its flatMap's retag as the lane's end.
lane-off : ∀ {R Γ A B} d n (q : List A) {b} {k} {c : Ctx R Γ B} {t} → b ≡ true
         → Won (uncurry (laneT d n q) (cutT b k (shows cp))) c t → Won (laneT d n q k (shows cp)) c t
lane-off d n q refl w = w

-- A live lane's completion under a queue passes its flatMap's retag as
-- a still skip just past it.
lane-shift : ∀ {R Γ A B} d n (a : A) q {b} {k} {c : Ctx R Γ B} {t} → b ≡ true
           → Won (uncurry (laneT d n (a ∷ q)) (cutT b k (shows cp))) c t → Won (shift k , still) c t
lane-shift d n a q refl w = w

-- No end waits where a lane is queued.
ends-queued : ∀ {R Γ A} d x p (c : Ctx R Γ A) s → EndsIf (d ∧ x ∧ false) p c s
ends-queued false x     p c s = tt
ends-queued true  false p c s = tt
ends-queued true  true  p c s = tt

-- An open outer's end, won, leads its lanes and its pool.
outer-ends : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (s : St Γ A) ls
           → Won (at p , shows cp) (inOuter op f d n q ls c) s → Frag (plug c (flatS op f d n q s ls)) → Gh top (plug c (flatS op f d n q s ls)) → Keys (plug c (flatS op f d n q s ls)) → d ≡ false → closed c ≡ false
           → All (λ l → After p (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore p (poolT (deadL ls) (envAt c))
outer-ends p c op f d n q s ls wn ft gt kt refl cl =
  outer-link c p op f n q s ls ft gt (won-scope p (shows cp) (inOuter op f false n q ls c) s wn ft gt kt)
    (race-shut KAfter (After p) (at p) (after-step p) c op f false n q s [] ls [] cl (proj₂ parts) (lanes-gh c op f false n q s ls gt) (proj₁ wn))
  where parts = frag-parts op f false n q s ls (frag-flat c op f false n q s ls ft)

-- Up the found node's frames: each one the completion reaches is clear
-- there, as `won-clear` for a value.
mutual
  won-ends : ∀ {R Γ A} p (c : Ctx R Γ A) (s s′ : St Γ A) → alive s ≡ alive s′
           → Won (at p , shows cp) c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → Ends p c s′
  won-ends p top                               s s′ al w ft gt kt = tt
  won-ends p (inMap f c)                       s s′ al w ft gt kt = won-ends p c (mapS f s) (mapS f s′) refl w ft gt kt
  won-ends p (inScan f z c)                    s s′ al w ft gt kt = won-ends p c (scanS f z s) (scanS f z s′) refl w ft gt kt
  won-ends p (inCut true x c)                  s s′ al w ft gt kt = λ _ → won-ends p c (cutS true x s) (cutS true x s′) refl w ft gt kt
  won-ends p (inCut false x c)                 s s′ al w ft gt kt = λ ()
  won-ends p (inLn b c)                        s s′ al w ft gt kt = won-ends p c (lnS b s) (lnS b s′) refl w ft gt kt
  won-ends p (inTake i q free c)               s s′ al w ft gt kt = won-ends p c (takeS i q free s) (takeS i q free s′) refl w ft gt kt
  won-ends p (inTake i q (cpAt r) c)           s s′ al w ft gt kt = tt
  won-ends p (inTake i q (cutAt r) c)          s s′ al w ft gt kt = tt
  won-ends p (inTake i q (overAt r) c)         s s′ al w ft gt kt = tt
  won-ends p (inOuter op f d n q ls c)         s s′ al wn@(r , w , _) ft gt kt =
    outer-ends p c op f d n q s ls wn ft gt kt , ends-if p c ((n ≡ᵇ 0) ∧ null q) (flatS op f d n q s ls) (flatS op f true n q s′ ls) refl w ft gt kt
  won-ends p (inLanes op f d n [] o pre post c) s s′ al wn@(l , u , w) ft gt kt =
    trans (sym al) lv , (λ cl → lane-sides p c op f d n [] o pre post s cl (won-scope p (shows cp) (inLanes op f d n [] o pre post c) s wn ft gt kt) l ft (frag-flat c op f d n [] o (pre ʳ++ s ∷ post) ft))
    , subst (λ b → EndsIf (d ∧ b) p c (flatS op f d (pred n) [] o (pre ʳ++ ended s′ ∷ post))) (sym (∧-identityʳ (pred n ≡ᵇ 0)))
        (ends-if p c (d ∧ (pred n ≡ᵇ 0)) (flatS op f d n [] o (pre ʳ++ s ∷ post)) (flatS op f d (pred n) [] o (pre ʳ++ ended s′ ∷ post)) refl
           (lane-off d n [] {alive s} {at p} {c} lv w) ft gt kt)
    , tt
    where lv = pooled-live (alive s) u
  won-ends p (inLanes op f d n (a ∷ q) o pre post c) s s′ al wn@(l , u , w) ft gt kt =
    trans (sym al) lv , (λ cl → lane-sides p c op f d n (a ∷ q) o pre post s cl (won-scope p (shows cp) (inLanes op f d n (a ∷ q) o pre post c) s wn ft gt kt) l ft (frag-flat c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft))
    , ends-queued d (pred n ≡ᵇ 0) p c (flatS op f d (pred n) (a ∷ q) o (pre ʳ++ ended s′ ∷ post))
    , λ sh → won-ahead (p ⊕ [ ix 0 ]) c (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post)) true (lane-shift d n a q {alive s} {at p} {c} lv w) ft gt kt sh
    where lv = pooled-live (alive s) u
  won-ends p (inSrc kk b c)                    s s′ al w ft gt kt = tt
  won-ends p (inBody (cs cl true sa ba as nothing r en) o c) s s′ al (_ , lo , bf , w) ft gt kt =
    (λ ce → body-link p c (cs cl true sa ba as nothing r en) o s ft ce refl lo bf)
    , λ k′ → won-ends p c (connS (cs cl true sa ba as nothing r en) o s) (connS k′ o s′) refl w ft gt kt
  won-ends p (inBody (cs cl true sa ba as (just _) r en) o c)  s s′ al (() , _) ft gt kt
  won-ends p (inBody (cs cl false sa ba as (just _) r en) o c) s s′ al (() , _) ft gt kt
  won-ends p (inBody (cs cl false sa ba as nothing r en) o c)  s s′ al (() , _) ft gt kt

  ends-if : ∀ {R Γ A} p (c : Ctx R Γ A) b (s s′ : St Γ A) → alive s ≡ alive s′
          → Won (at p , (if b then shows cp else still)) c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → EndsIf b p c s′
  ends-if p c true  s s′ al w ft gt kt = won-ends p c s s′ al w ft gt kt
  ends-if p c false s s′ al w ft gt kt = tt
