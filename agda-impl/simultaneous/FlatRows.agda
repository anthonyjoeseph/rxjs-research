{-# OPTIONS --guardedness #-}

-- AN ELABORATED FLATMAP'S VALUE ROWS, read back.  The elaborated flatMap
-- shows only what its scan relays, and the scan relays a value only of
-- the real flatMap's: every other input, the outer opened, a bracket
-- closed, a lane's frame or a connect's routes, sends marks.  So a value
-- it shows is one of a lane's own rows, read through the lane's frame
-- (`framed`) and relayed (`relay`), and that lane runs an outer value
-- the shared outer shows, uncut where the real flatMap reads it.
--
-- Each operator's value rows read back one layer at a time (`conn-out`,
-- `merge-out`, `bounded-out`, `hot-out`, …); `Rows` stacks them.
module simultaneous.FlatRows where

import Data.List as L
open import Data.List using (List; []; _∷_; [_]; _++_; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Bool using (Bool; true; false; T; not; if_then_else_; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _+_; _∸_; _⊓_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import Relation.Nullary using (¬_; does)

import Tree
open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect; connected; of; takeWhile)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; ix; sub; last)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (out; end; EmissionSet; Den; hot; DenEnv; Proper; Truncate; _≺_; _≼_; enter; approx; After;
  LaneOf; InE; at-out; on-out; shown; map-out; module Op; module Joiner; module Switch;
  module Exhaust; module Bounded; module Connect; module Scan; module TakeWhile; module Values)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-refl; ≺→≼)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (of-end; of-reach)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed; valuesOf)
open import simultaneous.SObs using (lone; isZero; flat; Part; lanePart; burstPart; isLane; Branch; outerB; laneB; closeB; Flat; module Elaborate)
open import simultaneous.Sim using (Shown; outerAt)
open import simultaneous.ToldRows using (sib-≺)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; E; Routes; Out; Input; laneˢ; each; combined; closer;
  setAt; react; onMark; unpark; cut; arrive; ended; burstOver; left; begun; stopped; overed; stops; anyHolds; share; laneStep; undone;
  opening; closing; own; fed; going; branch; piece; counted; marked; shareˢ)
  renaming (framed to framedˢ)

------------------------------------------------------------------------
-- The unbounded joiners

-- A flatMap whose lanes start where their values arrive.
data Jn : FlatOp → Set where
  merge∞ : Jn (mergeᶠ nothing)
  sw     : Jn switchᶠ
  ex     : Jn exhaustᶠ

-- Which values run a lane.
RunsOf : ∀ {op A Y} → Jn op → (A → Den Y) → EmissionSet A → Pos → Set
RunsOf merge∞ g o _ = ⊤
RunsOf sw     g o _ = ⊤
RunsOf ex     g o q = Exhaust.Run g o q

-- Where a lane is cut.
CutOf : ∀ {op A Y} → Jn op → (A → Den Y) → EmissionSet A → Pos → Pos → Set
CutOf merge∞ g o _ _ = ⊥
CutOf sw     g o q k = Switch.Cut g o q k
CutOf ex     g o _ _ = ⊥

-- Each is its joiner.
inst : ∀ {op A Y} (j : Jn op) (g : A → Den Y) (d : Den A) p
     → enter (Op.flatMap op g d) p ≡ Truncate (Joiner.JoinT g (enter d p) (RunsOf j g (enter d p)) (CutOf j g (enter d p)))
inst merge∞ g d p = refl
inst sw     g d p = refl
inst ex     g d p = refl

------------------------------------------------------------------------
-- Where the elaboration puts things

-- Where a framed lane subscribes its lane, under the frame's
-- subscription: the lane part's share, then its gate.
laneAt : Pos → Pos
laneAt w = (outerAt ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

-- Where a framed lane's frame reads its lane's rows: the frame's middle
-- piece, past its start.
frameAt : Pos → Pos
frameAt w = ((((((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ])

-- A lane row, framed: read, counted.
framed : Pos → Pos → Pos
framed w l = ((l ⊕ [ sub (frameAt w) ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

------------------------------------------------------------------------
-- Marks

-- An emit list showing no value.
Marks : ∀ {B} → List (IE B) → Set
Marks xs = ∀ {y} → y ∈ xs → valuesOf y ≡ []

mk-[] : ∀ {B} → Marks {B} []
mk-[] ()

mk-one : ∀ {B} m n → Marks {B} (instEmit (mark m) n ∷ [])
mk-one m n (here refl) = refl
mk-one m n (there ())

mk-++ : ∀ {B} (xs ys : List (IE B)) → Marks xs → Marks ys → Marks (xs ++ ys)
mk-++ xs ys mx my i with ∈-++⁻ xs i
... | inj₁ i′ = mx i′
... | inj₂ i′ = my i′

mk-rep : ∀ {B} k m n → Marks {B} (replicate k (instEmit (mark m) n))
mk-rep zero    m n ()
mk-rep (suc k) m n (here refl) = refl
mk-rep (suc k) m n (there i)   = mk-rep k m n i

-- An emit list the flatMap's scan sends: marks, none ending a lane.
Sends : ∀ {B} → List (IE B) → Set
Sends xs = ∀ {y} → y ∈ xs → valuesOf y ≡ [] × T (undone y)

sd-[] : ∀ {B} → Sends {B} []
sd-[] ()

sd-one : ∀ {B} m n → {T (undone {B} (instEmit (mark m) n))} → Sends {B} (instEmit (mark m) n ∷ [])
sd-one m n {u} (here refl) = refl , u
sd-one m n (there ())

sd-rep : ∀ {B} k m n → {T (undone {B} (instEmit (mark m) n))} → Sends {B} (replicate k (instEmit (mark m) n))
sd-rep zero    m n ()
sd-rep (suc k) m n {u} (here refl) = refl , u
sd-rep (suc k) m n {u} (there i)   = sd-rep k m n {u} i

cut-mk : ∀ {B} k n s → Sends {B} (proj₂ (cut k n s))
cut-mk k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | _     = sd-[]
... | false | true  = sd-[]
... | false | false = sd-rep k stop n

unpark-mk : ∀ {B} n s → Sends {B} (proj₂ (unpark n s))
unpark-mk n s with anyHolds (Flat.at s) (Flat.live s)
... | true  = sd-[]
... | false = sd-rep (Flat.parked s) stop n

arrive-mk : ∀ {B} op n s → Sends {B} (proj₂ (arrive op n s))
arrive-mk (mergeᶠ (just k)) n s with Flat.active s <ᵇ k
... | true  = sd-[]
... | false = sd-[]
arrive-mk (mergeᶠ nothing) n s = sd-[]
arrive-mk switchᶠ          n s = cut-mk (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
arrive-mk exhaustᶠ         n s = sd-[]

ended-mk : ∀ {B} k n s → Sends {B} (proj₂ (ended k n s))
ended-mk k n s with isZero (Flat.queue s)
... | false = sd-[]
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = sd-[]
...   | false = cut-mk (k + Flat.held s) n (record s { held = 0 })

burstOver-mk : ∀ {B} b n s → Sends {B} (proj₂ (burstOver b n s))
burstOver-mk true  n s = sd-[]
burstOver-mk false n s = cut-mk (Flat.held s) n (record s { held = 0 })

left-mk : ∀ {B} n s → Sends {B} (proj₂ (left n s))
left-mk n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = sd-[]
... | false = cut-mk (Flat.outer s) n (record s { outer = 0 })

begun-mk : ∀ {B} b n s → Sends {B} (proj₂ (begun b n s))
begun-mk b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
... | true  = sd-[]
... | false = sd-one begin n

stopped-mk : ∀ {B} b n s k → Sends {B} (proj₂ (stopped b n s k))
stopped-mk b n s zero    = sd-[]
stopped-mk b n s (suc _) = sd-one stop n

overed-mk : ∀ {B} n s → Sends {B} (proj₂ (overed n s))
overed-mk n s with Flat.spent s
... | true  = sd-[]
... | false = sd-one over n

onMark-mk : ∀ {B} op b s m n → Sends {B} (proj₂ (onMark op b s m n))
onMark-mk op b s begin      n = begun-mk b n s
onMark-mk op b s stop       n = stopped-mk b n s (if Flat.spent s then 0 else share b s)
onMark-mk op b s over       n = overed-mk n s
onMark-mk op b s carry      n = sd-[]
onMark-mk op b s outerOpen  n = arrive-mk op n s
onMark-mk op b s outerClose n = sd-[]
onMark-mk op b s laneStart  n = sd-[]
onMark-mk op b s laneDone   n =
  ended-mk (Flat.acc s ⊓ Flat.lanes s) n
    (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0
              ; popping = not (isZero (Flat.queue s)) ; dead = true })
onMark-mk op b s burstEnd   n = burstOver-mk (isZero (Flat.held s) ∨ Flat.dead s) n s
onMark-mk op b s outerDone  n = left-mk n (record s { finished = true })
onMark-mk op b s subscribed n = sd-one subscribed n
onMark-mk op b s completed  n = sd-one completed n

-- THE SCAN SHOWS A VALUE ONLY OF A VALUE INPUT, and alone.
react-val : ∀ {B} op (st : Out B) inp {y} → y ∈ proj₂ (react op st inp) → Shown y
          → Σ Branch λ br → Σ B λ v → Σ Pos λ nm → y ≡ instEmit (value v) nm × inp ≡ just (inj₁ (br , instEmit (value v) nm))
react-val op (s , _) (just (inj₁ (br , instEmit (value v) nm))) (here refl) _ = br , v , nm , refl , refl
react-val op (s , _) (just (inj₁ (br , instEmit (value v) nm))) (there ()) _
react-val op (s , _) (just (inj₁ (br , instEmit (mark m) nm))) i sh = ⊥-elim (sh (proj₁ (onMark-mk op br s m nm i)))
react-val op (s , _) (just (inj₂ (ix′ , r))) i sh = ⊥-elim (sh (proj₁ (unpark-mk root (record s { live = setAt ix′ r (Flat.live s) }) i)))
react-val op (s , _) nothing () _

-- THE SCAN ENDS NO LANE: it sends a value, or routes.
react-sends : ∀ {B} op (st : Out B) inp {y} → y ∈ proj₂ (react op st inp) → T (undone y)
react-sends op (s , _) (just (inj₁ (br , instEmit (value v) nm))) (here refl) = tt
react-sends op (s , _) (just (inj₁ (br , instEmit (value v) nm))) (there ())
react-sends op (s , _) (just (inj₁ (br , instEmit (mark m) nm))) i = proj₂ (onMark-mk op br s m nm i)
react-sends op (s , _) (just (inj₂ (ix′ , r))) i = proj₂ (unpark-mk root (record s { live = setAt ix′ r (Flat.live s) }) i)
react-sends op (s , _) nothing ()

-- A LANE'S COUNT SHOWS A VALUE ONLY OF A VALUE, and alone.
laneStep-mk : ∀ {B} (st : Routes × List (IE B)) m n → Marks (proj₂ (laneStep st (instEmit (mark m) n)))
laneStep-mk ((r , k) , _) laneDone   n = mk-++ (replicate k (marked carry)) _ (mk-rep k carry _) (mk-one laneDone n)
laneStep-mk st begin      n = mk-one begin n
laneStep-mk st over       n = mk-one over n
laneStep-mk st stop       n = mk-one stop n
laneStep-mk st outerOpen  n = mk-one outerOpen n
laneStep-mk st outerClose n = mk-one outerClose n
laneStep-mk st laneStart  n = mk-one laneStart n
laneStep-mk st carry      n = mk-one carry n
laneStep-mk st burstEnd   n = mk-one burstEnd n
laneStep-mk st outerDone  n = mk-one outerDone n
laneStep-mk st subscribed n = mk-one subscribed n
laneStep-mk st completed  n = mk-one completed n

laneStep-val : ∀ {B} (st : Routes × List (IE B)) e {y} → y ∈ proj₂ (laneStep st e) → Shown y → y ≡ e × proj₂ (laneStep st e) ≡ e ∷ []
laneStep-val st (instEmit (value v) n) (here refl) _ = refl , refl
laneStep-val st (instEmit (value v) n) (there ()) _
laneStep-val st (instEmit (mark m) n) i sh = ⊥-elim (sh (laneStep-mk st m n i))

-- What ends a lane is a mark.
undone-mk : ∀ {B} (y : IE B) → T (not (undone y)) → valuesOf y ≡ []
undone-mk (instEmit (value _) _) ()
undone-mk (instEmit (mark _) _)  _ = refl

opening-mk : ∀ {A B} (x : IE A) → valuesOf (opening {A} {B} x) ≡ []
opening-mk (instEmit (value _) _) = refl
opening-mk (instEmit (mark _) _)  = refl

closing-mk : ∀ {A B} (x : IE A) → Marks (closing {A} {B} x)
closing-mk (instEmit (value _) n) = mk-one outerClose n
closing-mk (instEmit (mark _) _)  = mk-[]

------------------------------------------------------------------------
-- One layer read back

module _ {A B : Set} (s : Den A) (F : Den A → Den B) (p : Pos) where
  private module Cn = Connect s F p

  -- A connect's value is its body's.
  conn-out : ∀ {k b} → enter (Op.connect s F) p k (out b) → Cn.β k (out b)
  conn-out (Cn.body x , _) = x

module _ {A B : Set} (f : A → Den B) (o : EmissionSet A) (Runs : Pos → Set) (Cut : Pos → Pos → Set) where
  private module Jr = Joiner f o Runs Cut

  -- A joiner's value is a running lane's, uncut.
  joiner-out : ∀ {k y} → Jr.JoinT k (out y) → Σ Pos λ q → Σ A λ x → o q (out x) × Runs q × LaneOf f q x k (out y) × ¬ Cut q k
  joiner-out (Jr.lane oq rq l nc _) = _ , _ , oq , rq , l , nc
  joiner-out (Jr.run () _)

-- A merge's value is a lane's, past its subscription.
merge-out : ∀ {A B : Set} (f : A → Den B) (d : Den A) p {k y} → enter (Op.flatMap (mergeᶠ nothing) f d) p k (out y)
          → Σ Pos λ q → Σ A λ x → enter d p q (out x) × enter (f x) (q ⊕ [ ix 1 ]) k (out y) × (q ⊕ [ ix 1 ]) ≺ k
merge-out f d p x with joiner-out f (enter d p) (λ _ → ⊤) (λ _ _ → ⊥) (proj₁ x)
... | q , a , oq , _ , (l , lt) , _ = q , a , oq , l , lt

module _ {A B : Set} (m : ℕ) (f : A → Den B) (d : Den A) (p : Pos) where
  private module Bd = Bounded m f (enter d p)

  -- A bounded merge's value is a scheduled lane's.
  bounded-out : ∀ {k y} → enter (Op.flatMap (mergeᶠ (just m)) f d) p k (out y)
              → Σ Pos λ q → Σ A λ x → Σ ℕ λ i → Σ Pos λ s → enter d p q (out x) × Bd.Sub i q s x × After (f x) s k (out y)
  bounded-out (Bd.lane oq _ (i , s , sb , aft) _ _ , _) = _ , _ , i , s , oq , sb , aft
  bounded-out (Bd.run () _ , _)

-- A hot's value, joined: a shown row past the subscription.
hot-out : ∀ {A} {t : EmissionSet A} {z k b} → enter (hot t) z k (out b) → Σ Pos λ q → t q (out b) × z ≺ q × k ≡ q ⊕ [ sub z ]
hot-out (shown tq _ zq , _) = _ , tq , zq , refl

-- A map's value, of its source's.
map-out′ : ∀ {A B} (f : A → B) (d : Den A) p {k y} → enter (Op.map f d) p k (out y) → Σ A λ x → enter d p k (out x) × y ≡ f x
map-out′ f d p (map-out t , _) = _ , t , refl

module _ {A B : Set} (f : B → A → B) (z : B) (d : Den A) (p : Pos) where
  private module Sc = Scan f z (enter d p)

  -- A scan's value folds its source's value at its row.
  scan-out : ∀ {k y} → enter (Op.scan f z d) p k (out y) → Σ B λ st → Σ A λ a → enter d p k (out a) × y ≡ f st a
  scan-out (Sc.sval (Sc.acc₀ t _) , _)     = z , _ , t , refl
  scan-out (Sc.sval (Sc.acc _ t _ _) , _)  = _ , _ , t , refl

module _ {A : Set} (keep : A → Bool) (d : Den A) (p : Pos) where
  private
    module Tf = TakeWhile false keep (enter d p)
    module Tt = TakeWhile true keep (enter d p)

  -- An exclusive takeWhile's value passed.
  take-pass : ∀ {k y} → enter (Op.takeWhile false keep d) p k (out y) → enter d p k (out y) × T (keep y)
  take-pass (Tf.pass t kp _ , _) = t , kp
  take-pass (Tf.fail _ _ _ () , _)

  -- An inclusive one's passed, or failed.
  take-incl : ∀ {k y} → enter (Op.takeWhile true keep d) p k (out y) → (enter d p k (out y) × T (keep y)) ⊎ T (not (keep y))
  take-incl (Tt.pass t kp _ , _)   = inj₁ (t , kp)
  take-incl (Tt.fail _ nk _ _ , _) = inj₂ nk

-- An `of`'s value is one of its list.
of-mem : ∀ {A} p i (xs : List A) {k y} → InE (ofᴱ p i xs) k (out y) → y ∈ xs
of-mem p i []       ()
of-mem p i (x ∷ xs) at-out     = here refl
of-mem p i (x ∷ xs) (on-out r) = there (of-mem p (suc i) xs r)

of-one : ∀ {A} p (x : A) {k y} → InE (ofᴱ p 0 (x ∷ [])) k (out y) → k ≡ p ⊕ [ ix 0 ] × y ≡ x
of-one p x at-out          = refl , refl
of-one p x (on-out ())

-- An `each`'s value, of its source's value at the lane's one row.
each-one : ∀ {A B} (f : A → List B) (d : Den A) p {k y} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (f x)) d) p k (out y)
         → Σ Pos λ q → Σ A λ x → enter d p q (out x) × y ∈ f x × InE (ofᴱ (q ⊕ [ ix 1 ]) 0 (f x)) k (out y)
each-one f d p r with merge-out (λ x → Op.of (f x)) d p r
... | q , x , dq , (l , _) , _ = q , x , dq , of-mem _ 0 (f x) l , l

-- A value a relaying scan shows is a branch's value it read.
scan-relay : ∀ {B} op (z : Out B) (D : Den (Maybe (Input B))) p {l b}
           → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) z D)) p l (out b) → Shown b
           → Σ Pos λ q₄ → Σ Branch λ br → enter D p q₄ (out (just (inj₁ (br , b)))) × l ≡ (q₄ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
scan-relay op z D p u sh with each-one proj₂ (Op.scan (react op) z D) p u
... | q₄ , y , dq , bi , ine with scan-out (react op) z D p dq
...   | st , inp , tr , refl with react-val op st inp bi sh
...     | br , v , nm , refl , refl with of-one (q₄ ⊕ [ ix 1 ]) (instEmit (value v) nm) ine
...       | refl , _ = q₄ , br , tr , refl

-- A value's index holds its row.
nth-row : ∀ {A} {o : EmissionSet A} {i q a} → Values.Nth o i q a → o q (out a)
nth-row (Values.first o _)    = o
nth-row (Values.next _ o _ _) = o

------------------------------------------------------------------------
-- Concats

-- A concat of two: the first lane at once.
module Cat {B : Set} (F : Bool → Den B) (p : Pos) where
  O : EmissionSet Bool
  O = enter (Op.of (true ∷ false ∷ [])) p

  private module Bd = Bounded 1 F O

  min0 : ∀ {k b} → O k (out b) → (p ⊕ [ ix 0 ]) ≼ k
  min0 (at-out , _)             = ≼-refl {p ⊕ [ ix 0 ]}
  min0 (on-out at-out , _)      = ≺→≼ {p ⊕ [ ix 0 ]} {p ⊕ [ ix 1 ]} (ix-asc p (s≤s z≤n))
  min0 (on-out (on-out ()) , _)

  first-sub : ∀ {i q s} → O q (out true) → Bd.Sub i q s true → s ≡ (p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
  first-sub (at-out , _) (Values.first _ _ , Bd.room _)          = refl
  first-sub (at-out , _) (Values.first _ _ , Bd.freed () _)
  first-sub (at-out , _) (Values.first _ _ , Bd.queued () _ _ _ _)
  first-sub (at-out , _) (Values.next nt _ lt _ , _)             = ⊥-elim (min0 (nth-row nt) lt)
  first-sub (on-out (on-out ()) , _) _

  -- A concat's value: the first lane's, or the second's.
  cat-out : ∀ {k y} → enter (Op.flatMap (mergeᶠ (just 1)) F (Op.of (true ∷ false ∷ []))) p k (out y)
          → enter (F true) ((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) k (out y) ⊎ Σ Pos λ s → enter (F false) s k (out y)
  cat-out r with bounded-out 1 F (Op.of (true ∷ false ∷ [])) p r
  ... | q , true , i , s , oq , sb , (l , _) with first-sub oq sb
  ...   | refl = inj₁ l
  cat-out r | q , false , i , s , oq , sb , (l , _) = inj₂ (s , l)

-- A concat of three whose first and last lanes show nothing, the first
-- ending at once: its value is the middle lane's, subscribed at its value.
module Three {B : Set} (F : ℕ → Den B) (p : Pos) (V : B → Set)
             (h0 : ∀ {s k y} → enter (F 0) s k (out y) → V y → ⊥) (h2 : ∀ {s k y} → enter (F 2) s k (out y) → V y → ⊥)
             (e0 : ∀ {s c} → enter (F 0) s c end → c ≡ s ⊕ [ last ]) where
  O : EmissionSet ℕ
  O = enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) p

  private module Bd = Bounded 1 F O
  open Values O using (Nth)

  data OV : Pos → ℕ → Set where
    v0 : OV (p ⊕ [ ix 0 ]) 0
    v1 : OV (p ⊕ [ ix 1 ]) 1
    v2 : OV (p ⊕ [ ix 2 ]) 2

  ov : ∀ {k a} → O k (out a) → OV k a
  ov (at-out , _)                      = v0
  ov (on-out at-out , _)               = v1
  ov (on-out (on-out at-out) , _)      = v2
  ov (on-out (on-out (on-out ())) , _)

  lt01 : (p ⊕ [ ix 0 ]) ≺ (p ⊕ [ ix 1 ])
  lt01 = ix-asc p (s≤s z≤n)

  lt02 : (p ⊕ [ ix 0 ]) ≺ (p ⊕ [ ix 2 ])
  lt02 = ix-asc p (s≤s z≤n)

  lt12 : (p ⊕ [ ix 1 ]) ≺ (p ⊕ [ ix 2 ])
  lt12 = ix-asc p (s≤s (s≤s z≤n))

  r0 : O (p ⊕ [ ix 0 ]) (out 0)
  r0 = at-out , of-reach p 0 (0 ∷ 1 ∷ 2 ∷ []) {p ⊕ [ ix 0 ]} {out 0}

  min0 : ∀ {k a} → O k (out a) → (p ⊕ [ ix 0 ]) ≼ k
  min0 o with ov o
  ... | v0 = ≼-refl {p ⊕ [ ix 0 ]}
  ... | v1 = ≺→≼ {p ⊕ [ ix 0 ]} {p ⊕ [ ix 1 ]} lt01
  ... | v2 = ≺→≼ {p ⊕ [ ix 0 ]} {p ⊕ [ ix 2 ]} lt02

  nth-z : ∀ {i a} → Nth i (p ⊕ [ ix 0 ]) a → i ≡ 0
  nth-z (Values.first _ _)      = refl
  nth-z (Values.next nt _ lt _) = ⊥-elim (min0 (nth-row nt) lt)

  nth0 : ∀ {q a} → Nth 0 q a → q ≡ p ⊕ [ ix 0 ] × a ≡ 0
  nth0 (Values.first o mn) with ov o
  ... | v0 = refl , refl
  ... | v1 = ⊥-elim (mn r0 lt01)
  ... | v2 = ⊥-elim (mn r0 lt02)

  nth1 : ∀ {i a} → Nth i (p ⊕ [ ix 1 ]) a → i ≡ 1
  nth1 (Values.first _ mn) = ⊥-elim (mn r0 lt01)
  nth1 (Values.next nt _ lt _) with ov (nth-row nt)
  ... | v0 = cong suc (nth-z nt)
  ... | v1 = ⊥-elim (≺-irrefl {p ⊕ [ ix 1 ]} lt)
  ... | v2 = ⊥-elim (≺-absurd {p ⊕ [ ix 1 ]} {p ⊕ [ ix 2 ]} lt12 lt)

  -- The first lane ends before the middle value.
  end0 : ∀ {c} → Bd.Ends 0 [] c → c ≡ ((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ last ]
  end0 (q , a , s , nt , st , aft) with nth0 nt
  ... | refl , refl with st
  ...   | Bd.room _          = e0 (proj₁ aft)
  ...   | Bd.freed () _
  ...   | Bd.queued () _ _ _ _

  lt-end : (((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ last ]) ≺ (p ⊕ [ ix 1 ])
  lt-end = subst₂ _≺_ (sym (⊕-assoc (p ⊕ [ ix 0 ]) [ ix 1 ] [ last ])) (⊕-identityʳ (p ⊕ [ ix 1 ])) (sib-≺ p lt01 (ix 1 ∷ last ∷ []) [])

  no-q : ∀ {c} → (p ⊕ [ ix 1 ]) ≺ c → Bd.Kth (_≡ c) (Bd.Sched 1) 0 → ⊥
  no-q {c} qc (inj₁ (c′ , e , refl)) = ≺-absurd {p ⊕ [ ix 1 ]} {c} qc (subst (_≺ (p ⊕ [ ix 1 ])) (sym (end0 e)) lt-end)
  no-q qc (inj₂ ())

  -- The middle lane subscribes at its value.
  starts1 : ∀ {i s} → Bd.Sub i (p ⊕ [ ix 1 ]) s 1 → s ≡ (p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]
  starts1 (_ , Bd.room _)              = refl
  starts1 (_ , Bd.freed _ _)           = refl
  starts1 (nt , Bd.queued _ qc kk _ _) with nth1 nt
  ... | refl = ⊥-elim (no-q qc kk)

  frame-out : ∀ {k y} → enter (Op.flatMap (mergeᶠ (just 1)) F (Op.of (0 ∷ 1 ∷ 2 ∷ []))) p k (out y) → V y
            → After (F 1) ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) k (out y)
  frame-out r v with bounded-out 1 F (Op.of (0 ∷ 1 ∷ 2 ∷ [])) p r
  ... | q , x , i , s , oq , sb , aft with ov oq
  ...   | v0 = ⊥-elim (h0 (proj₁ aft) v)
  ...   | v2 = ⊥-elim (h2 (proj₁ aft) v)
  ...   | v1 with starts1 sb
  ...     | refl = aft

------------------------------------------------------------------------
-- The scan's input and the outer, read back

-- A fed branch value is the flatMap's own side's.
fed-own : ∀ {X C : Set} (F : Bool → Den (Maybe (X ⊎ C))) p
        → (∀ {s k y} → enter (F true) s k (out (just (inj₁ y))) → ⊥)
        → ∀ {q y} → enter (Op.takeWhile false going (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ [])))) p q (out (just (inj₁ y)))
        → enter (F false) ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) q (out (just (inj₁ y)))
fed-own F p no t with take-pass going (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) p t
... | r , _ with merge-out F (Op.of (true ∷ false ∷ [])) p r
...   | _ , _ , (at-out , _) , l , _ = ⊥-elim (no l)
...   | _ , _ , (on-out at-out , _) , l , _ = l
...   | _ , _ , (on-out (on-out ()) , _) , _ , _

-- The trackers feed no branch value.
map-inj₂ : ∀ {X C : Set} (D : Den C) s {k y} → enter (Op.map (λ x → just (inj₂ {A = X} x)) D) s k (out (just (inj₁ y))) → ⊥
map-inj₂ D s r with map-out′ (λ x → just (inj₂ x)) D s r
... | _ , _ , ()

-- A concat's value, where its second lane shows none, is its first's.
cat-first : ∀ {X : Set} (F : Bool → Den X) p (V : X → Set)
          → (∀ {s k y} → enter (F false) s k (out y) → V y → ⊥)
          → ∀ {k y} → enter (Op.flatMap (mergeᶠ (just 1)) F (Op.of (true ∷ false ∷ []))) p k (out y) → V y
          → enter (F true) ((p ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) k (out y)
cat-first F p V no r v with Cat.cat-out F p r
... | inj₁ l       = l
... | inj₂ (_ , l) = ⊥-elim (no l v)

-- An end marker is no value.
of-nothing : ∀ {X : Set} s {k y} → enter (Op.of (nothing {A = X} ∷ [])) s k (out y) → y ≡ nothing
of-nothing s (l , _) with of-one s nothing l
... | _ , eq = eq

-- A concat whose lanes show no values shows none.
cat-none : ∀ {X : Set} (F : Bool → Den (IE X)) p
         → (∀ {s k y} → enter (F true) s k (out y) → valuesOf y ≡ []) → (∀ {s k y} → enter (F false) s k (out y) → valuesOf y ≡ [])
         → ∀ {k y} → enter (Op.flatMap (mergeᶠ (just 1)) F (Op.of (true ∷ false ∷ []))) p k (out y) → valuesOf y ≡ []
cat-none F p h₁ h₂ r with Cat.cat-out F p r
... | inj₁ l       = h₁ l
... | inj₂ (_ , l) = h₂ l

-- The closings show no values.
closing-none : ∀ {A B : Set} (D : Den (IE A)) s {k y} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (closing {A} {B} x)) D) s k (out y)
             → valuesOf y ≡ []
closing-none D s l with each-one closing D s l
... | _ , x , _ , yi , _ = closing-mk x yi

-- A mark is no value.
marked-none : ∀ {B : Set} m s {k y} → enter (Op.of (marked {B} m ∷ [])) s k (out y) → valuesOf y ≡ []
marked-none m s (l , _) with of-one s (marked m) l
... | _ , refl = refl

-- An opening is no value.
opening-none : ∀ {A B : Set} (D : Den (IE A)) s {k y} → enter (Op.map (opening {A} {B}) D) s k (out y) → Shown y → ⊥
opening-none D s r sh with map-out′ opening D s r
... | x , _ , refl = sh (opening-mk x)

-- A value the branches show is the lane branch's.
branch-gen : ∀ {B : Set} (G : Branch → Den (IE B)) p
           → (∀ {s k y} → enter (G outerB) s k (out y) → Shown y → ⊥) → (∀ {s k y} → enter (G closeB) s k (out y) → Shown y → ⊥)
           → ∀ {q₄ br b} → enter (Op.flatMap (mergeᶠ nothing) (λ c → Op.map (λ e → just (inj₁ {B = ℕ × Routes} (c , e))) (G c)) (Op.of (outerB ∷ laneB ∷ closeB ∷ []))) p q₄
                                 (out (just (inj₁ (br , b))))
           → Shown b → enter (G laneB) ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) q₄ (out b)
branch-gen G p hO hC r sh with merge-out (λ c → Op.map (λ e → just (inj₁ {B = ℕ × Routes} (c , e))) (G c)) (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) p r
... | qb , br′ , (orow , _) , mr , _ with map-out′ (λ e → just (inj₁ {B = ℕ × Routes} (br′ , e))) (G br′) (qb ⊕ [ ix 1 ]) mr
...   | y , brow , refl with orow
...     | at-out                       = ⊥-elim (hO brow sh)
...     | on-out at-out                = brow
...     | on-out (on-out at-out)       = ⊥-elim (hC brow sh)
...     | on-out (on-out (on-out ()))

-- A lane of the trigger's one row: the shared outer, at its foot.
trig-lane : ∀ {X : Set} (D : Den X) z s {k′ x}
          → enter (Op.flatMap (mergeᶠ nothing) (λ _ → D) (hot (Proper (enter (Op.of (tt ∷ [])) z)))) s k′ (out x)
          → enter D (((z ⊕ [ ix 0 ]) ⊕ [ sub s ]) ⊕ [ ix 1 ]) k′ (out x)
trig-lane D z s r with merge-out (λ _ → D) (hot (Proper (enter (Op.of (tt ∷ [])) z))) s r
... | qt , t , hr , l , _ with hot-out hr
...   | kt , ((tr , _) , _) , _ , refl with of-one z tt tr
...     | refl , _ = l

-- A value read off a hot's values: one the hot shows.
vals-back : ∀ {X : Set} (σ : EmissionSet (IE X)) z {q a} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot (Proper σ))) z q (out a)
          → Σ Pos λ k′ → Σ (IE X) λ x → σ k′ (out x) × valuesOf x ≡ a ∷ [] × q ≡ ((k′ ⊕ [ sub z ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
vals-back σ z r with each-one valuesOf (hot (Proper σ)) z r
... | q₁ , instEmit (mark m) nm , hr , () , ine
... | q₁ , instEmit (value a′) nm , hr , _ , ine with of-one (q₁ ⊕ [ ix 1 ]) a′ ine
...   | refl , refl with hot-out hr
...     | k′ , (sr , _) , _ , refl = k′ , instEmit (value a′) nm , sr , refl , refl

-- A value a lane count shows is one its source shows.
counted-back : ∀ {B} (D : Den (IE B)) z {K b}
             → enter (Op.flatMap (mergeᶠ nothing) (λ y → Op.of (proj₂ y)) (Op.scan laneStep ((root , 0) , []) D)) z K (out b) → Shown b
             → Σ Pos λ q₇ → enter D z q₇ (out b) × K ≡ (q₇ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
counted-back D z {K} r sh with each-one proj₂ (Op.scan laneStep ((root , 0) , []) D) z r
... | q₇ , y , srow , bi , ine with scan-out laneStep ((root , 0) , []) D z srow
...   | st , e , frow , refl with laneStep-val st e bi sh
...     | refl , eq with of-one (q₇ ⊕ [ ix 1 ]) e (subst (λ xs → InE (ofᴱ (q₇ ⊕ [ ix 1 ]) 0 xs) K (out e)) eq ine)
...       | refl , _ = q₇ , frow , refl

-- A gated lane's value: the lane's row, the gate open.
gate-back : ∀ {X Y : Set} (D : Den Y) (keep : X → Bool) (part : X) z {K b}
          → enter (Op.flatMap (mergeᶠ nothing) (λ _ → D) (Op.takeWhile false keep (Op.of (part ∷ [])))) z K (out b)
          → enter D ((z ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) K (out b) × ((z ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ≺ K × T (keep part)
gate-back D keep part z r with merge-out (λ _ → D) (Op.takeWhile false keep (Op.of (part ∷ []))) z r
... | qx , part′ , trow , xrow , lt with take-pass keep (Op.of (part ∷ [])) z trow
...   | (orow , _) , il with of-one z part orow
...     | refl , refl = xrow , lt , il

-- A lane's value is a part's.
part-back : ∀ {Y : Set} (F : Part → Den (IE Y)) w {K b}
          → enter (Op.takeWhile true undone (Op.flatMap (mergeᶠ nothing) F (Op.of (lanePart ∷ burstPart ∷ [])))) w K (out b) → Shown b
          → Σ Pos λ qk → Σ Part λ part → enter (Op.of (lanePart ∷ burstPart ∷ [])) w qk (out part) × enter (F part) (qk ⊕ [ ix 1 ]) K (out b)
part-back F w {b = b} r sh with take-incl undone (Op.flatMap (mergeᶠ nothing) F (Op.of (lanePart ∷ burstPart ∷ []))) w r
... | inj₂ nk = ⊥-elim (sh (undone-mk b nk))
... | inj₁ (r₁ , _) with merge-out F (Op.of (lanePart ∷ burstPart ∷ [])) w r₁
...   | qk , part , prow , srow , _ = qk , part , prow , srow

-- The lane part is the first.
lane-first : ∀ w {qk part} → enter (Op.of (lanePart ∷ burstPart ∷ [])) w qk (out part) → T (isLane part) → qk ≡ w ⊕ [ ix 0 ]
lane-first w (at-out , _) _ = refl
lane-first w (on-out at-out , _) ()
lane-first w (on-out (on-out ()) , _) _

-- A lane's value, by its part's.
lane-gen : ∀ n {Θ Y} (G : Part → E Θ (IE Y)) (ρ : DenEnv Θ) (R : Pos → Pos → Set) (fr : Pos → Pos → Pos) w {K b}
         → (∀ part w₀ → enter (approx n (G part) ρ) w₀ K (out b) → Σ Pos λ K₀ → R w₀ K₀ × T (isLane part) × K ≡ fr w₀ K₀)
         → enter (approx n (takeWhile true undone (flatMap (mergeᶠ nothing) G (of (lanePart ∷ burstPart ∷ [])))) ρ) w K (out b) → Shown b
         → Σ Pos λ K₀ → R ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) K₀ × K ≡ fr ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) K₀
lane-gen n G ρ R fr w sb r sh with part-back (λ k → approx n (G k) ρ) w r sh
... | qk , part , prow , srow with sb part (qk ⊕ [ ix 1 ]) srow
...   | K₀ , rr , il , e with lane-first w prow il
...     | refl = K₀ , rr , e

-- Regrouped, with no `with` to normalise the context.
pair₂ : ∀ {P Q E : Pos → Set} {S : Set} → Σ Pos (λ K₀ → P K₀ × Q K₀ × S × E K₀) → Σ Pos λ K₀ → (P K₀ × Q K₀) × S × E K₀
pair₂ (K₀ , a , b , c , d) = K₀ , (a , b) , c , d

unpair₂ : ∀ {P Q E : Pos → Set} → Σ Pos (λ K₀ → (P K₀ × Q K₀) × E K₀) → Σ Pos λ K₀ → P K₀ × Q K₀ × E K₀
unpair₂ (K₀ , (a , b) , d) = K₀ , a , b , d

------------------------------------------------------------------------
-- A lane, framed

module Framing (n : ℕ) {Θ B} (x : E (⊤ ∷ Θ) (IE B)) (ρ : DenEnv Θ) where

  -- A lane part's share: its trigger, its gated lane, the gate's env.
  σttW : Pos → EmissionSet ⊤
  σttW w₀ = enter (Op.of (tt ∷ [])) (w₀ ⊕ [ ix 1 ])

  envW : Pos → DenEnv (⊤ ∷ Θ)
  envW w₀ = hot (Proper (σttW w₀)) ∷ᴬ ρ

  Xs : Part → E (⊤ ∷ Θ) (IE B)
  Xs part = flatMap (mergeᶠ nothing) (λ _ → x) (takeWhile false isLane (of (part ∷ [])))

  σX : Part → Pos → EmissionSet (IE B)
  σX part w₀ = enter (approx n (flatMap (mergeᶠ nothing) (λ _ → Xs part) (connected (here refl))) (envW w₀)) ((w₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

  -- The frame's first and last pieces show nothing, the first ending
  -- at once.
  p0-mk : ∀ part {Θ′} (ρ′ : DenEnv (IE B ∷ Θ′)) {s k y} → enter (approx n (piece part 0) ρ′) s k (out y) → Shown y → ⊥
  p0-mk lanePart  ρ′ {s} (r , _) sh with of-one s (marked laneStart) r
  ... | _ , refl = sh refl
  p0-mk burstPart ρ′ {s} (r , _) sh with of-one s (marked burstEnd) r
  ... | _ , refl = sh refl

  p2-mk : ∀ part {Θ′} (ρ′ : DenEnv (IE B ∷ Θ′)) {s k y} → enter (approx n (piece part 2) ρ′) s k (out y) → Shown y → ⊥
  p2-mk lanePart  ρ′ {s} (r , _) sh with of-one s (marked laneDone) r
  ... | _ , refl = sh refl
  p2-mk burstPart ρ′ (() , _) sh

  p0-end : ∀ part {Θ′} (ρ′ : DenEnv (IE B ∷ Θ′)) {s c} → enter (approx n (piece part 0) ρ′) s c end → c ≡ s ⊕ [ last ]
  p0-end lanePart  ρ′ {s} (r , _) = of-end s 0 _ r
  p0-end burstPart ρ′ {s} (r , _) = of-end s 0 _ r

  p1-hot : ∀ part {Θ′} (σ : EmissionSet (IE B)) (ρ′ : DenEnv Θ′) {z q y}
         → enter (approx n (piece part 1) (hot (Proper σ) ∷ᴬ ρ′)) z q (out y) → enter (hot (Proper σ)) z q (out y)
  p1-hot lanePart  σ ρ′ r = r
  p1-hot burstPart σ ρ′ r = r

  -- A frame's value is its middle piece's.
  frame-step : ∀ part {Θ′} (ρ′ : DenEnv (IE B ∷ Θ′)) c₀ {q y} → enter (approx n (framedˢ part) ρ′) c₀ q (out y) → Shown y
             → After (approx n (piece part 1) ρ′) ((c₀ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) q (out y)
  frame-step part ρ′ c₀ fr shy =
    Three.frame-out (λ m → approx n (piece part m) ρ′) c₀ Shown (p0-mk part ρ′) (p2-mk part ρ′) (p0-end part ρ′) fr shy

  -- A share's value: its gated lane's row, framed, and the gate open.
  share-back : ∀ part w₀ {K b} → enter (approx n (shareˢ (Xs part) (counted (framedˢ part))) ρ) w₀ K (out b) → Shown b
             → Σ Pos λ K₀ → enter (approx n x (envW w₀)) ((outerAt w₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) K₀ (out b)
               × ((outerAt w₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ≺ K₀ × T (isLane part)
               × K ≡ ((K₀ ⊕ [ sub ((((w₀ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
  share-back part w₀ r sh =
    let (q₇ , frow , e₁) = counted-back (approx n (framedˢ part) (hot (Proper (σX part w₀)) ∷ᴬ envW w₀)) ((w₀ ⊕ [ ix 0 ]) ⊕ [ ix 0 ])
                             (conn-out (approx n (flatMap (mergeᶠ nothing) (λ _ → Xs part) (connected (here refl))) (envW w₀))
                                       (λ h → approx n (counted (framedˢ part)) (h ∷ᴬ envW w₀)) (w₀ ⊕ [ ix 0 ])
                               (conn-out (Op.of (tt ∷ []))
                                         (λ h → approx n (connect (flatMap (mergeᶠ nothing) (λ _ → Xs part) (connected (here refl))) (counted (framedˢ part)))
                                                         (h ∷ᴬ ρ)) w₀ r)) sh
        (K₀ , (xr , _) , _ , e₂) = hot-out (p1-hot part (σX part w₀) (envW w₀)
                                     (proj₁ (frame-step part (hot (Proper (σX part w₀)) ∷ᴬ envW w₀) ((w₀ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) frow sh)))
        (xrow , lt , il) = gate-back (approx n x (envW w₀)) isLane part (outerAt w₀)
                             (trig-lane (approx n (Xs part) (envW w₀)) (w₀ ⊕ [ ix 1 ]) ((w₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) xr)
    in K₀ , xrow , lt , il , trans e₁ (cong (λ q → (q ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) e₂)

  -- A part's value, gated and framed.
  LR : IE B → Pos → Pos → Set
  LR b w₀ K₀ = enter (approx n x (envW w₀)) ((outerAt w₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) K₀ (out b) × ((outerAt w₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ≺ K₀

  lfr : Pos → Pos → Pos
  lfr w₀ K₀ = ((K₀ ⊕ [ sub ((((w₀ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  lsb : ∀ {K b} → Shown b → ∀ part w₀ → enter (approx n (shareˢ (Xs part) (counted (framedˢ part))) ρ) w₀ K (out b)
      → Σ Pos λ K₀ → LR b w₀ K₀ × T (isLane part) × K ≡ lfr w₀ K₀
  lsb sh part w₀ srow = pair₂ (share-back part w₀ srow sh)

  -- A lane, its parts' shares named.
  lane-obs : laneˢ x ≡ takeWhile true undone (flatMap (mergeᶠ nothing) (λ k → shareˢ (Xs k) (counted (framedˢ k))) (of (lanePart ∷ burstPart ∷ [])))
  lane-obs = refl

  -- A lane's value: its own lane's row, framed.
  lane-back : ∀ w {K b} → enter (approx n (laneˢ x) ρ) w K (out b) → Shown b
            → Σ Pos λ K₀ → enter (approx n x (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) K₀ (out b) × laneAt w ≺ K₀ × K ≡ framed w K₀
  lane-back w {K} {b} r sh = unpair₂ (lane-gen n (λ k → shareˢ (Xs k) (counted (framedˢ k))) ρ (LR b) lfr w (lsb sh)
                                       (subst (λ o → enter (approx n o ρ) w K (out b)) lane-obs r) sh)

  postulate
    -- A lane's own row past its subscription and before its end, where
    -- none of its rows ends a lane: the lane's value, framed.
    --
    -- DEAD ROUTE: forward through each layer's reach alone.  The lane
    --   count is a scan, and its row needs its fold (`Acc`), built from
    --   every earlier value in order; a reach lists positions, not
    --   events, and which are rows is not decidable without excluded middle.
    lane-fwd : ∀ w {K₀ b} → enter (approx n x (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) K₀ (out b) → laneAt w ≺ K₀
             → (∀ {c} → enter (approx n x (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) c end → K₀ ≼ c)
             → (∀ {k y} → enter (approx n x (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) k (out y) → T (undone y))
             → enter (approx n (laneˢ x) ρ) w (framed w K₀) (out b)

------------------------------------------------------------------------
-- The elaborated flatMap's rows

module Rows (n : ℕ) {Δ A B} (env′ : DenEnv Δ) {op : FlatOp} (j : Jn op)
            (s′ : E (⊤ ∷ Δ) (IE A)) (g′ : A → E (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B))
            (tk : E (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (ℕ × Routes)) (p′ : Pos) where

  -- The closer, each lane and the scan, sealed: a type compared through
  -- them compares their environments instead of unfolding them.
  opaque
    CL : E (IE A ∷ ⊤ ∷ Δ) (IE B)
    CL = closer

    LS : A → E (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
    LS a = laneˢ (g′ a)

    CB : E (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
    CB = combined op tk

  -- The trigger, its shared outer, the outer's closer.
  σtt : EmissionSet ⊤
  σtt = enter (Op.of (tt ∷ [])) (p′ ⊕ [ ix 1 ])

  env₀′ : DenEnv (⊤ ∷ Δ)
  env₀′ = hot (Proper σtt) ∷ᴬ env′

  σ₁ : EmissionSet (IE A)
  σ₁ = enter (approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′) ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

  env₁′ : DenEnv (IE A ∷ ⊤ ∷ Δ)
  env₁′ = hot (Proper σ₁) ∷ᴬ env₀′

  pcl : Pos
  pcl = ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  σcl : EmissionSet (IE B)
  σcl = enter (approx n CL env₁′) pcl

  envY : DenEnv (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  envY = hot (Proper σcl) ∷ᴬ env₁′

  -- The real flatMap: its outer the shared outer's values, its lanes
  -- framed.
  z₂ : Pos
  z₂ = (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  D₂ : Den A
  D₂ = approx n (each valuesOf (connected (there (here refl)))) envY

  o₂ : EmissionSet A
  o₂ = enter D₂ z₂

  g₂ : A → Den (IE B)
  g₂ a = approx n (LS a) envY

  RF : E (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  RF = flatMap op LS (each valuesOf (connected (there (here refl))))

  σRF : EmissionSet (IE B)
  σRF = enter (approx n RF envY) z₂

  envZ : DenEnv (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  envZ = hot (Proper σRF) ∷ᴬ envY

  -- An outer row, read by the real flatMap.
  rd : Pos → Pos
  rd k′ = ((k′ ⊕ [ sub z₂ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  -- The scan beside the real flatMap: its subscription, its own
  -- branches', and where it reads the real flatMap's rows.
  p₄ : Pos
  p₄ = (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ]

  p₅ : Pos
  p₅ = (p₄ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

  p₆ : Pos
  p₆ = (p₅ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  z₃ : Pos
  z₃ = (p₆ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

  -- A real flatMap row, relayed by the scan.
  relay : Pos → Pos
  relay k = ((k ⊕ [ sub z₃ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  q₀′ : Pos
  q₀′ = outerAt p′

  -- What the trigger's one row runs.
  body : E (⊤ ∷ Δ) (IE B)
  body = connect (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) (connect CL (connect RF CB))

  U : EmissionSet (IE B)
  U = enter (approx n (connect (of (tt ∷ [])) body) env′) p′

  -- The body, unsealed: the elaborated flatMap's.
  opaque
    unfolding CL LS CB
    body-eq : body ≡ connect (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl)))
                       (connect closer (connect (flatMap op (λ a → laneˢ (g′ a)) (each valuesOf (connected (there (here refl))))) (combined op tk)))
    body-eq = refl

  U₀ : EmissionSet (IE A)
  U₀ = enter (approx n s′ env₀′) q₀′

  ----------------------------------------------------------------------
  -- Down to the scan

  U₄ : EmissionSet (IE B)
  U₄ = enter (approx n CB envZ) p₄

  to-U₄ : ∀ {l b} → U l (out b) → U₄ l (out b)
  to-U₄ u =
    conn-out (approx n RF envY) (λ h → approx n CB (h ∷ᴬ envY)) (((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 0 ])
      (conn-out (approx n CL env₁′) (λ h → approx n (connect RF CB) (h ∷ᴬ env₁′)) ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 0 ])
        (conn-out (approx n (flatMap (mergeᶠ nothing) (λ _ → s′) (connected (here refl))) env₀′)
                  (λ h → approx n (connect CL (connect RF CB)) (h ∷ᴬ env₀′)) (p′ ⊕ [ ix 0 ])
          (conn-out (Op.of (tt ∷ [])) (λ h → approx n body (h ∷ᴬ env′)) p′ u)))

  -- The scan's input: the connects in scope, then its own branches.
  BR : E (IE B ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ) (Maybe (Input B))
  BR = flatMap (mergeᶠ nothing) (λ b → Tree.map (λ e → just (inj₁ (b , e))) (branch b)) (of (outerB ∷ laneB ∷ closeB ∷ []))

  Dfm : Den (Maybe (Input B))
  Dfm = Op.flatMap (mergeᶠ nothing) (λ b → approx n (fed tk b) envZ) (Op.of (true ∷ false ∷ []))

  Dtk : Den (Maybe (Input B))
  Dtk = Op.takeWhile false going Dfm

  init : Out B
  init = flat root 0 0 false false false false 0 0 0 0 0 [] , []

  -- A value the scan shows is a branch's value it read.
  opaque
    unfolding CB
    scanned : ∀ {l b} → U₄ l (out b) → Shown b
            → Σ Pos λ q₄ → Σ Branch λ br → enter Dtk p₄ q₄ (out (just (inj₁ (br , b)))) × l ≡ (q₄ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
    scanned u sh = scan-relay op init Dtk p₄ u sh

  -- A branch's value read is the flatMap's own.
  fed-row : ∀ {q₄ br b} → enter Dtk p₄ q₄ (out (just (inj₁ (br , b)))) → enter (approx n own envZ) p₅ q₄ (out (just (inj₁ (br , b))))
  fed-row t = fed-own (λ c → approx n (fed tk c) envZ) p₄ (λ l → map-inj₂ (approx n tk envZ) _ l) t

  own-row : ∀ {q₄ br b} → enter (approx n own envZ) p₅ q₄ (out (just (inj₁ (br , b)))) → enter (approx n BR envZ) p₆ q₄ (out (just (inj₁ (br , b))))
  own-row r = cat-first (λ c → approx n (if c then BR else of (nothing ∷ [])) envZ) p₅ (λ y → y ≡ nothing → ⊥)
                (λ l ne → ne (of-nothing _ l)) r (λ ())

  -- The closer shows nothing.
  opaque
    unfolding CL
    closer-mk : ∀ {k y} → σcl k (out y) → valuesOf y ≡ []
    closer-mk r = cat-none (λ c → approx n (if c then each closing (connected (here refl)) else of (marked outerDone ∷ [])) env₁′) pcl
                    (λ l → closing-none (hot (Proper σ₁)) _ l) (λ l → marked-none outerDone _ l) r

  -- A value the flatMap's branches show is the real flatMap's.
  branch-lane : ∀ {q₄ br b} → enter (approx n BR envZ) p₆ q₄ (out (just (inj₁ (br , b)))) → Shown b
              → Σ Pos λ K → Proper σRF K (out b) × q₄ ≡ K ⊕ [ sub z₃ ]
  branch-lane r sh =
    let (K , kr , _ , eq) = hot-out (branch-gen (λ c → approx n (branch c) envZ) p₆ (λ l s → opening-none (hot (Proper σ₁)) _ l s)
                                       (λ l s → s (closer-mk (proj₁ (proj₁ (proj₂ (hot-out l)))))) r sh)
    in K , kr , eq

  ----------------------------------------------------------------------
  -- The outer, read by the real flatMap

  σ₁-back : ∀ {k′ x} → σ₁ k′ (out x) → U₀ k′ (out x)
  σ₁-back r = trig-lane (approx n s′ env₀′) (p′ ⊕ [ ix 1 ]) ((p′ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) r

  -- A value of the real flatMap's outer is a value the shared outer
  -- shows, read.
  outer-back : ∀ {q a} → o₂ q (out a) → Σ Pos λ k′ → Σ (IE A) λ x → U₀ k′ (out x) × valuesOf x ≡ a ∷ [] × q ≡ rd k′
  outer-back r = let (k′ , x , sr , vx , eq) = vals-back σ₁ z₂ r in k′ , x , σ₁-back sr , vx , eq

  ----------------------------------------------------------------------
  -- A lane, framed

  -- A lane part's share's env.
  envW : Pos → DenEnv (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  envW w₀ = hot (Proper (enter (Op.of (tt ∷ [])) (w₀ ⊕ [ ix 1 ]))) ∷ᴬ envY

  -- A lane's value: its own lane's row, framed.
  opaque
    unfolding LS
    lane-back : ∀ a w {K b} → enter (g₂ a) w K (out b) → Shown b
              → Σ Pos λ K₀ → enter (approx n (g′ a) (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) K₀ (out b) × laneAt w ≺ K₀ × K ≡ framed w K₀
    lane-back a w r sh = Framing.lane-back n (g′ a) envY w r sh

    -- A lane's own row, framed: the real flatMap's lane's.
    lane-fwd : ∀ a w {K₀ b} → enter (approx n (g′ a) (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) K₀ (out b) → laneAt w ≺ K₀
             → (∀ {c} → enter (approx n (g′ a) (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) c end → K₀ ≼ c)
             → (∀ {k y} → enter (approx n (g′ a) (envW ((w ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt w) k (out y) → T (undone y))
             → enter (g₂ a) w (framed w K₀) (out b)
    lane-fwd a w r lt pr ud = Framing.lane-fwd n (g′ a) envY w r lt pr ud

  postulate
    -- A value the real flatMap shows, before its end: the scan relays it.
    relay-fwd : ∀ {K b} → Proper σRF K (out b) → Shown b → U (relay K) (out b)

  ----------------------------------------------------------------------
  -- Read back

  -- A value the elaborated flatMap shows: an outer value the shared outer
  -- shows, running a lane uncut, the lane's own row framed and relayed.
  record Back (l : Pos) (b : IE B) : Set where
    field
      k′    : Pos
      x     : IE A
      a     : A
      K₀    : Pos
      u₀    : U₀ k′ (out x)
      vx    : valuesOf x ≡ a ∷ []
      o₂r   : o₂ (rd k′) (out a)
      runs  : RunsOf j g₂ o₂ (rd k′)
      uncut : ¬ CutOf j g₂ o₂ (rd k′) (framed (rd k′ ⊕ [ ix 1 ]) K₀)
      ul    : enter (approx n (g′ a) (envW (((rd k′ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) (laneAt (rd k′ ⊕ [ ix 1 ])) K₀ (out b)
      aft   : laneAt (rd k′ ⊕ [ ix 1 ]) ≺ K₀
      at    : l ≡ relay (framed (rd k′ ⊕ [ ix 1 ]) K₀)

  back : ∀ {l b} → U l (out b) → Shown b → Back l b
  back {l} {b} u sh =
    let (q₄ , br , trow , e₁) = scanned (to-U₄ u) sh
        (K , (rf , _) , e₂) = branch-lane (own-row (fed-row trow)) sh
        (q , a , oq , rq , (lr , _) , nc) = joiner-out g₂ o₂ (RunsOf j g₂ o₂) (CutOf j g₂ o₂) (proj₁ (subst (λ t → t K (out b)) (inst j g₂ D₂ z₂) rf))
        (k′ , x , u₀ , vx , e₃) = outer-back oq
        (K₀ , ul , aft , e₄) = lane-back a (rd k′ ⊕ [ ix 1 ]) (subst (λ q′ → enter (g₂ a) (q′ ⊕ [ ix 1 ]) K (out b)) e₃ lr) sh
    in record { k′ = k′ ; x = x ; a = a ; K₀ = K₀ ; u₀ = u₀ ; vx = vx
              ; o₂r = subst (λ q′ → o₂ q′ (out a)) e₃ oq
              ; runs = subst (RunsOf j g₂ o₂) e₃ rq
              ; uncut = subst₂ (λ q′ K′ → ¬ CutOf j g₂ o₂ q′ K′) e₃ e₄ nc
              ; ul = ul ; aft = aft
              ; at = trans e₁ (trans (cong (λ z → (z ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) e₂) (cong relay e₄)) }
