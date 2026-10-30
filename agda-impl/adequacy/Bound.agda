{-# OPTIONS --guardedness #-}

-- WHAT A FOUND MARK PROMISES, AND WHAT A GOOD NODE CARRIES: keys and
-- their order, `OK` over a node's rows, and the node facts `G` that the
-- search's proofs read.
module adequacy.Bound where

open import Data.Bool using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.List.Properties using (++-identityʳ; ∷ʳ-injectiveˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (ofᴱ)
open import denotation.Events using (Pos; Timeline; ix; last; <ᵖ-asym; <ᵖ-split; <ᵖ-step; <ᵖ-shift; <ᵖ-below; <ᵖ-part; <ᵖ-ix)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; _≺_; _≼_; InE; enter; at-out; at-end; on-out; MapT; map-out;
  map-skip; map-pin; map-end; module Scan; DenEnv)
open import denotation.Laws.Modulus using (≼-refl)
open import denotation.Laws.Worlds using (InvAt; Hots; W; inW; plain-ix; apart-w) renaming (⊑-refl to ⊑ᵖ-refl)
open import operation.Key using (Key; at; after; _<ᴷ_; ≮ᴷ-trans; <ᴷ-trans; <ᴷ-irrefl; at-<ᵖ; clash)
open import operation.PureObservable using (module Machine)

open Machine using (St; Ctx; CS; Cand; Found; found; Focus; Mark; Out; still; shows; seek; kids; lanes; own; ownBest; raceT; outerT; laneT; sourceT; retag; first; mapT; scanT; takeT; cutT; shift; alive; outOf; ofM; closed; same?;
                    free; cpAt; cutAt; overAt; inScan; inTake; inSrc; inBody;
                    ofS; doneS; mapS; cutS; cpM; cutM; lnS; flatS; coldS; scanS; takeS; connS; joinS; inMap; inCut; inLn; inOuter; inLanes; nx; cp; attached; attAt; attM; pend) renaming (Ev to Evᴹ; over to overᶜ)
open import adequacy.Rows using (acc-val; rows; rowsL; pendRows; toEv; Lanes; Each; Kth; AllEnd; EndsOf; Lane; reads; module Flat; module SwitchF; module ExhaustF; module BoundedF; ∅; Hot; Inbox; _∪_; Kept; Stops) renaming (kept to keptᴿ; stop to stopᴿ; left to leftᴿ; sub to subᴿ)

------------------------------------------------------------------------
-- Keys

postulate
  -- Just past a position, still before a mark's `after` the position is before.
  shift-after : ∀ q r → at q <ᴷ after r ≡ true → after r <ᴷ at (q ++ [ ix 0 ]) ≡ false

-- `a` no later than `b`.
record _⊑_ (a b : Key) : Set where
  constructor ⊑i
  field un : b <ᴷ a ≡ false
open _⊑_

⊑-refl : ∀ k → k ⊑ k
⊑-refl k = ⊑i (<ᴷ-irrefl k)

⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans {a} {b} {c} ab bc = ⊑i (≮ᴷ-trans c b a (un bc) (un ab))

<→⊑ : ∀ a b → a <ᴷ b ≡ true → a ⊑ b
<→⊑ a b ab with b <ᴷ a in ba
... | false = ⊑i ba
... | true  = ⊥-elim (clash (<ᴷ-trans a b a ab ba) (<ᴷ-irrefl a))

≺→⊑ : ∀ {p q} → p ≺ q → at p ⊑ at q
≺→⊑ {p} {q} pq = ⊑i (trans (at-<ᵖ q p) (<ᵖ-asym p q (Equivalence.to T-≡ pq)))

⊑→≼ : ∀ {p q} → at p ⊑ at q → p ≼ q
⊑→≼ {p} {q} h qp = clash (Equivalence.to T-≡ qp) (trans (sym (at-<ᵖ q p)) (un h))

-- Under a position is no earlier.
ext-⊑ : ∀ p x → at p ⊑ at (p ++ x)
ext-⊑ p []      rewrite ++-identityʳ p = ⊑-refl (at p)
ext-⊑ p (l ∷ x) = ⊑i (trans (at-<ᵖ (p ++ l ∷ x) p) (<ᵖ-asym p (p ++ l ∷ x) (<ᵖ-below p x)))

-- A lane's first effect is before its subscription.
ix01 : ∀ p → at (p ++ [ ix 0 ]) ⊑ at (p ++ [ ix 1 ])
ix01 p = ⊑i (trans (at-<ᵖ (p ++ [ ix 1 ]) (p ++ [ ix 0 ])) (<ᵖ-asym (p ++ [ ix 0 ]) (p ++ [ ix 1 ]) (<ᵖ-part p [] [] (<ᵖ-ix 0))))

-- Just past is no earlier.
shift-⊑ : ∀ h → h ⊑ shift h
shift-⊑ (at p)    = ext-⊑ p [ ix 0 ]
shift-⊑ (after p) = ⊑-refl (after p)

-- No earlier stays no earlier a step past each.
shift-≮ : ∀ q h → h ⊑ at q → shift h ⊑ at (q ++ [ ix 0 ])
shift-≮ q (at p)    u = ⊑i (trans (at-<ᵖ (q ++ [ ix 0 ]) (p ++ [ ix 0 ])) (<ᵖ-shift q p (trans (sym (at-<ᵖ q p)) (un u))))
shift-≮ q (after p) u = ⊑-trans u (ext-⊑ q [ ix 0 ])

-- Strictly before a key: just past it is no later.
shift-< : ∀ h k → h <ᴷ k ≡ true → shift h ⊑ k
shift-< (at q)    (at r)    h = ⊑i (trans (at-<ᵖ r (q ++ [ ix 0 ])) (<ᵖ-step q r (trans (sym (at-<ᵖ q r)) h)))
shift-< (at q)    (after r) h = ⊑i (shift-after q r h)
shift-< (after p) k         h = <→⊑ (after p) k h

-- Strictly past a position: no earlier than just past it.
past-⊑ : ∀ {p q} → at p ⊑ at q → ¬ p ≡ q → at (p ++ [ ix 0 ]) ⊑ at q
past-⊑ {p} {q} pq ne with <ᵖ-split p q (trans (sym (at-<ᵖ q p)) (un pq))
... | inj₁ lt = ⊑i (trans (at-<ᵖ q (p ++ [ ix 0 ])) (<ᵖ-step p q lt))
... | inj₂ eq = ⊥-elim (ne eq)

------------------------------------------------------------------------
-- What a found mark promises

Empty : ∀ {A} → EmissionSet A → Set
Empty t = ∀ {q e} → ¬ t q e

From : ∀ {A} → Key → EmissionSet A → Set
From K t = ∀ {q e} → t q e → K ⊑ at q

Single : ∀ {A} → EmissionSet A → Set
Single t = ∀ {q e e′} → t q e → t q e′ → e ≡ e′

-- Keyed `K`, the mark itself at `κ`, showing `o`.
record Bd {A : Set} (t : EmissionSet A) (κ K : Key) (o : Out A) : Set where
  field
    from  : From K t
    mark  : κ ⊑ K
    shown : ∀ {e} → o ≡ shows e → Σ Pos λ q → K ≡ at q × t q (toEv e)
open Bd

OK : ∀ {R A} → EmissionSet A → Maybe (Cand R A) → Set
OK t nothing                      = Empty t
OK t (just (found f m κ , K , o)) = Bd t κ K o

-- Over a list of lanes, lane by lane.
OKL : ∀ {R B} → List (EmissionSet B) → Maybe (Cand R B) → Set
OKL Ls nothing                      = Each Empty Ls
OKL Ls (just (found f m κ , K , o)) =
  Each (From K) Ls × κ ⊑ K × (∀ {e} → o ≡ shows e → Σ Pos λ q → K ≡ at q × Lanes Ls q (toEv e))

------------------------------------------------------------------------
-- The mark no later than its key, at every node

-- Every rise keys its event at its child's key or past it, so whatever a
-- search finds, its mark is no later than the key it is raced by.
Mk : ∀ {R A} → Maybe (Cand R A) → Set
Mk nothing                      = ⊤
Mk (just (found f m κ , K , o)) = κ ⊑ K

ok-mk : ∀ {R A} {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → Mk y
ok-mk nothing                      _ = tt
ok-mk (just (found f m κ , K , o)) b = mark b

Raises : ∀ {A B} → (Key → Out A → Key × Out B) → Set
Raises {A} t = ∀ h (o : Out A) → h ⊑ proj₁ (t h o)

retag-mk : ∀ {R A B} {t : Key → Out A → Key × Out B} → Raises t → (y : Maybe (Cand R A)) → Mk y → Mk (retag t y)
retag-mk r nothing                      _  = tt
retag-mk r (just (found f m κ , K , o)) mk = ⊑-trans mk (r K o)

first-mk : ∀ {R A} (x y : Maybe (Cand R A)) → Mk x → Mk y → Mk (first x y)
first-mk nothing                           y                                  _  my = my
first-mk (just _)                          nothing                            mx _  = mx
first-mk (just (found f m κ , h , o)) (just (found g m′ κ′ , h′ , o′)) mx my with h′ <ᴷ h
... | true  = my
... | false = mx

own-mk : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) ms → Mk (ownBest c s ms)
own-mk c s []             = tt
own-mk c s ((m , k) ∷ ms) = first-mk (just (found (_ , _ , c , s) m k , k , outOf c s m)) (ownBest c s ms) (⊑-refl k) (own-mk c s ms)

raise-map : ∀ {A B} (f : A → B) → Raises (mapT f)
raise-map f h still     = ⊑-refl h
raise-map f h (shows e) = ⊑-refl h

raise-scan : ∀ {A B} (f : B → A → B) z → Raises (scanT f z)
raise-scan f z h (shows (nx a)) = ⊑-refl h
raise-scan f z h (shows cp)     = ⊑-refl h
raise-scan f z h still          = ⊑-refl h

raise-cut : ∀ {A} l → Raises {A} (cutT l)
raise-cut l h o = ⊑-refl h

raise-take : ∀ {A} i (q : A → Bool) w → Raises (takeT i q w)
raise-take i q free h (shows (nx a)) with q a | i
... | true  | _     = ⊑-refl h
... | false | true  = shift-⊑ h
... | false | false = ⊑-refl h
raise-take i q free       h (shows cp) = ⊑-refl h
raise-take i q free       h still      = ⊑-refl h
raise-take i q (cpAt _)   h o          = ⊑-refl h
raise-take i q (cutAt _)  h o          = ⊑-refl h
raise-take i q (overAt _) h o          = ⊑-refl h

raise-outer : ∀ {A B : Set} n (q : List A) → Raises (outerT {A} {B} n q)
raise-outer n q h (shows cp)     = ⊑-refl h
raise-outer n q h (shows (nx a)) = shift-⊑ h
raise-outer n q h still          = ⊑-refl h

raise-lane : ∀ {A B : Set} d n (q : List A) → Raises (laneT {A} {B} d n q)
raise-lane d n []      h (shows cp)     = ⊑-refl h
raise-lane d n (_ ∷ _) h (shows cp)     = shift-⊑ h
raise-lane d n []      h (shows (nx b)) = ⊑-refl h
raise-lane d n (_ ∷ _) h (shows (nx b)) = ⊑-refl h
raise-lane d n []      h still          = ⊑-refl h
raise-lane d n (_ ∷ _) h still          = ⊑-refl h

race-mk : ∀ {R A B} d n (q : List A) (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Mk x → Mk y → Mk (raceT d n q x y)
race-mk d n q nothing                      nothing                      _  _  = tt
race-mk d n q nothing                      (just (found g m κ , k , o)) _  my = ⊑-trans my (raise-lane d n q k o)
race-mk d n q (just (found f m κ , h , o)) nothing                      mx _  = ⊑-trans mx (raise-outer n q h o)
race-mk d n q (just (found f m κ , h , o)) (just (found g m′ κ′ , k , o′)) mx my with h <ᴷ k
... | true  = ⊑-trans mx (raise-outer n q h o)
... | false = ⊑-trans my (raise-lane d n q k o′)

raise-src : ∀ v h → h ⊑ (if v then h else shift h)
raise-src true  h = ⊑-refl h
raise-src false h = shift-⊑ h

source-mk : ∀ {R A B} v (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Mk x → Mk y → Mk (sourceT v x y)
source-mk v nothing                      y                            _  my = my
source-mk v (just (found f m κ , h , o)) nothing                      mx _  = ⊑-trans mx (raise-src v h)
source-mk v (just (found f m κ , h , o)) (just (found g m′ κ′ , k , o′)) mx my with (if v then h else shift h) <ᴷ k
... | true  = ⊑-trans mx (raise-src v h)
... | false = my

mutual
  seek-mark : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Mk (seek c s)
  seek-mark c s = first-mk (ownBest c s (own s)) (kids c s) (own-mk c s (own s)) (kids-mark c s)

  kids-mark : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Mk (kids c s)
  kids-mark c (mapS f s)      = retag-mk (raise-map f) (seek (inMap f c) s) (seek-mark (inMap f c) s)
  kids-mark c (scanS f z s)   = retag-mk (raise-scan f z) (seek (inScan f z c) s) (seek-mark (inScan f z c) s)
  kids-mark c (cutS l a s)    = retag-mk (raise-cut l) (seek (inCut l a c) s) (seek-mark (inCut l a c) s)
  kids-mark c (lnS b s)       = seek-mark (inLn b c) s
  kids-mark c (takeS i q w s) = retag-mk (raise-take i q w) (seek (inTake i q w c) s) (seek-mark (inTake i q w c) s)
  kids-mark c (flatS op f d n q o ls) =
    race-mk d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls) (seek-mark (inOuter op f d n q ls c) o) (lanes-mark c op f d n q o [] ls)
  kids-mark c (connS k o b)   = source-mk (overᶜ k) (seek (inSrc k b c) o) (seek (inBody k o c) b) (seek-mark (inSrc k b c) o) (seek-mark (inBody k o c) b)
  kids-mark c (pend _ _)        = tt
  kids-mark c (coldS _ _)     = tt
  kids-mark c (ofS _ _ _)     = tt
  kids-mark c doneS           = tt
  kids-mark c (joinS _ _ _ _) = tt

  lanes-mark : ∀ {R Γ A B} (c : Ctx R Γ B) op f d n q (o : St Γ A) pre (ls : List (St Γ B)) → Mk (lanes c op f d n q o pre ls)
  lanes-mark c op f d n q o pre []         = tt
  lanes-mark c op f d n q o pre (s ∷ post) =
    first-mk _ _ (retag-mk (raise-cut (alive s)) (seek (inLanes op f d n q o pre post c) s) (seek-mark (inLanes op f d n q o pre post c) s))
                 (lanes-mark c op f d n q o (s ∷ pre) post)

-- An end, every row still owed by it.
EndLast : ∀ {A} → EmissionSet A → Set
EndLast t = ∀ {c q e} → t c end → t q e → q ≼ c

module _ {B : Set} where
  empty-any : ∀ (Ls : List (EmissionSet B)) → Each Empty Ls → Empty (Lanes Ls)
  empty-any (_ ∷ _)  (n , _)  (inj₁ r) = n r
  empty-any (_ ∷ Ls) (_ , ns) (inj₂ x) = empty-any Ls ns x

  from-any : ∀ {K} (Ls : List (EmissionSet B)) → Each (From K) Ls → From K (Lanes Ls)
  from-any (_ ∷ _)  (f , _)  (inj₁ r) = f r
  from-any (_ ∷ Ls) (_ , fs) (inj₂ x) = from-any Ls fs x

  from-weak : ∀ {K K′} (Ls : List (EmissionSet B)) → K ⊑ K′ → Each (From K′) Ls → Each (From K) Ls
  from-weak []       h _        = _
  from-weak (_ ∷ Ls) h (f , fs) = (λ r → ⊑-trans h (f r)) , from-weak Ls h fs

  from-empty : ∀ {K} (Ls : List (EmissionSet B)) → Each Empty Ls → Each (From K) Ls
  from-empty []       _        = _
  from-empty (_ ∷ Ls) (n , ns) = (λ r → ⊥-elim (n r)) , from-empty Ls ns

  -- A lane's end at `q`: some lane ends by `q`.
  lanes-kth : ∀ (Ls : List (EmissionSet B)) {q} → Lanes Ls q end → Kth (_≼ q) (EndsOf Ls) 0
  lanes-kth (_ ∷ _)  {q} (inj₁ r) = inj₁ (q , r , ≼-refl {q})
  lanes-kth (_ ∷ Ls)     (inj₂ x) = inj₂ (lanes-kth Ls x)

  -- At most one lane running: a lane's end ends every running lane.
  one-end : ∀ n (Ls : List (EmissionSet B)) → pred n ≡ 0 → ∀ {q} → Lanes Ls q end → AllEnd (_≼ q) n (EndsOf Ls)
  one-end zero          Ls _  _ = tt
  one-end (suc zero)    Ls _  x = lanes-kth Ls x
  one-end (suc (suc n)) Ls () _

------------------------------------------------------------------------
-- The node facts the race reads

-- The lanes still in their list.
live : ∀ {Γ A} → List (St Γ A) → ℕ
live []       = 0
live (s ∷ ls) = if alive s then suc (live ls) else live ls

-- No position owed by both.
Apart : ∀ {X Y} → EmissionSet X → EmissionSet Y → Set
Apart t u = ∀ {q e e′} → t q e → u q e′ → ⊥

-- Each lane apart from every later one.
Spread : ∀ {B} → List (EmissionSet B) → Set
Spread []       = ⊤
Spread (t ∷ Ls) = Apart t (Lanes Ls) × Spread Ls

-- A merge's outer and lanes, all apart: a tie between them is never a
-- row of both, so the race's winner leads the losers strictly.
Parts : ∀ {A B} → EmissionSet A → List (EmissionSet B) → Set
Parts O Ls = Apart O (Lanes Ls) × Spread Ls

-- Asked of a live node only.
Live : Bool → Set → Set
Live true  X = X
Live false X = ⊤

Live₁ : Bool → Set₁ → Set₁
Live₁ true  X = X
Live₁ false X = ⊤₁

data ⊥₁ : Set₁ where

------------------------------------------------------------------------
-- A merge's parts, read off its outer's entry

-- A lane begun at a value of `X` at `q`: its rows in the world of the
-- value's second child, where the lane subscribed.
Root : ∀ {A B} → (Pos → Set) → EmissionSet A → Pos → EmissionSet B → Set
Root {A} H X q t = Σ A λ a → X q (out a) × (∀ {y e} → t y e → W H (q ++ [ ix 1 ]) y)

-- Each lane at a value of its own.
Roots : ∀ {A B} → (Pos → Set) → EmissionSet A → List Pos → List (EmissionSet B) → Set
Roots H X []       []       = ⊤
Roots H X (q ∷ qs) (t ∷ Ls) = Root H X q t × (q ∈ qs → ⊥) × Roots H X qs Ls
Roots H X _        _        = ⊥

-- A merge's outer still inside what it entered, every lane begun at one
-- of that entry's values: the entry keeps Tier −1's invariant, so the
-- outer's rows are single and its parts apart. The entry's rows `X` and
-- hots `H` are frozen when the outer subscribes: a binder's step moves
-- rows from the environment into a joiner's inbox, and the entry re-read
-- at the current environment would lose them.
record Rooted {A B} (O : EmissionSet A) (Ls : List (EmissionSet B)) : Set₁ where
  field
    H     : Pos → Set
    X     : EmissionSet A
    p₀    : Pos
    inv   : InvAt H p₀ X
    sub   : ∀ {q e} → O q e → X q e
    qs    : List Pos
    roots : Roots H X qs Ls

module _ {A B} {O : EmissionSet A} {Ls : List (EmissionSet B)} (r : Rooted O Ls) where
  open Rooted r
  open InvAt inv using (func; under)

  private
    root-of : ∀ qs′ (Ls′ : List (EmissionSet B)) → Roots H X qs′ Ls′ → ∀ {y e} → Lanes Ls′ y e
            → Σ Pos λ q → q ∈ qs′ × Σ A λ a → X q (out a) × W H (q ++ [ ix 1 ]) y
    root-of (q ∷ qs′) (t ∷ Ls′) ((a , x , w) , _ , _) (inj₁ l) = q , here refl , a , x , w l
    root-of (q ∷ qs′) (t ∷ Ls′) (_ , _ , rs) (inj₂ l) with root-of qs′ Ls′ rs l
    ... | q′ , m , rest = q′ , there m , rest
    root-of []        []        _  ()
    root-of []        (_ ∷ _)   () _
    root-of (_ ∷ _)   []        () _

    spread : ∀ qs′ (Ls′ : List (EmissionSet B)) → Roots H X qs′ Ls′ → Spread Ls′
    spread []        []        _ = tt
    spread (q ∷ qs′) (t ∷ Ls′) ((a , x , w) , nq , rs) = apart′ , spread qs′ Ls′ rs
      where
        apart′ : Apart t (Lanes Ls′)
        apart′ l l′ with root-of qs′ Ls′ rs l′
        ... | q′ , m , a′ , x′ , w′ =
          apart-w plain-ix plain-ix (λ eq → nq (subst (_∈ qs′) (sym (∷ʳ-injectiveˡ q q′ eq)) m))
                  (λ v → under x′ x plain-ix v (⊑ᵖ-refl _)) (λ v → under x x′ plain-ix v (⊑ᵖ-refl _)) (inW (w l)) (inW w′)
    spread []        (_ ∷ _)   ()
    spread (_ ∷ _)   []        ()

  -- One event a row: the entry's.
  rooted-single : Single O
  rooted-single x x′ = func (sub x) (sub x′)

  -- No outer row in a lane's world; no two lanes' worlds meet.
  rooted-parts : Parts O Ls
  rooted-parts = (λ oy l → let (q , _ , a , xq , w) = root-of qs Ls roots l in under xq (sub oy) plain-ix (inW w) (⊑ᵖ-refl _)) , spread qs Ls roots

-- A merge node: its outer and lanes good, nothing queued; where live,
-- its count, its done outer owing nothing, and its parts rooted at the
-- outer's entry.
record MergeG {Γ A B} (Go Gl : Set₁) (ρ : DenEnv Γ) (b : Bool) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A) (ls : List (St Γ B)) : Set₁ where
  field
    outer  : Go
    lanesG : Gl
    fresh  : q ≡ []
    count  : Live b (n ≡ live ls)
    spent  : Live b (T d → Empty (rows ρ o))
    rooted : Live₁ b (Rooted (rows ρ o) (rowsL ρ ls))

-- Off: only the shape.
mergeG₀ : ∀ {Γ A B Go Gl} {ρ : DenEnv Γ} {f : A → Obs Timeline Γ B} {d n q o} {ls : List (St Γ B)} → Go → Gl → q ≡ [] → MergeG Go Gl ρ false f d n q o ls
mergeG₀ go gl qe = record { outer = go ; lanesG = gl ; fresh = qe ; count = tt ; spent = tt ; rooted = tt₁ }

-- The same merge over other parts, its facts carried.
mergeG-map : ∀ {Γ A B Go Gl Go′ Gl′} {ρ : DenEnv Γ} {b} {f : A → Obs Timeline Γ B} {d n n′ q} {o o′ : St Γ A} {ls ls′ : List (St Γ B)}
           → (Go → Go′) → (Gl → Gl′) → (Live b (n ≡ live ls) → Live b (n′ ≡ live ls′)) → (Live b (T d → Empty (rows ρ o)) → Live b (T d → Empty (rows ρ o′)))
           → (Live₁ b (Rooted (rows ρ o) (rowsL ρ ls)) → Live₁ b (Rooted (rows ρ o′) (rowsL ρ ls′)))
           → MergeG Go Gl ρ b f d n q o ls → MergeG Go′ Gl′ ρ b f d n′ q o′ ls′
mergeG-map ho hl hc hs hr m = record { outer = ho outer ; lanesG = hl lanesG ; fresh = fresh ; count = hc count ; spent = hs spent ; rooted = hr rooted }
  where open MergeG m

-- A subscription still owed.
Held : ∀ {Γ A} → St Γ A → Set₁
Held (pend _ _) = ⊤₁
Held _          = ⊥₁

-- A joiner's inbox in order, each entry strictly before every later one,
-- and before every row the source still owes it but the one it is: a
-- closed source's end, fed to the joiner, is still among its binder's rows.
Fed : ∀ {A} → List (Pos × Evᴹ A) → EmissionSet A → Set₁
Fed []             t = ⊤₁
Fed ((q , e) ∷ ib) t = (∀ {y e′} → Inbox ib y e′ → q ≺ y) × (∀ {y e′} → t y e′ → q ≺ y ⊎ (y ≡ q × e′ ≡ toEv e)) × Fed ib t

-- An inbox the end was fed to, still waiting last.
data Ends {A : Set} : List (Pos × Evᴹ A) → Set where
  end₁ : ∀ {q} → Ends [ (q , cp) ]
  more : ∀ {x ib} → Ends ib → Ends (x ∷ ib)

ToldAt : ∀ {A B} → Maybe (A ≡ B) → List (Pos × Evᴹ B) → Set
ToldAt nothing  _  = ⊤
ToldAt (just _) ib = Ends ib

-- Every live joiner of binder `x` already fed its end: what a closed
-- source leaves under it, its end fed to each joiner as it came.  Nothing
-- under a switched-off cut is asked.
mutual
  Told : ∀ {Γ X A} → X ∈ Γ → St Γ A → Set
  Told x (joinS j true y ib) = ToldAt (same? x y) ib
  Told x (mapS f s)              = Told x s
  Told x (scanS f z s)           = Told x s
  Told x (cutS true a s)         = Told x s
  Told x (lnS b s)               = Told x s
  Told x (takeS v q w s)         = Told x s
  Told x (flatS op f d n q o ls) = Told x o × ToldL x ls
  Told x (connS k o b)           = Told x o × Told (there x) b
  Told x _                       = ⊤

  ToldL : ∀ {Γ X A} → X ∈ Γ → List (St Γ A) → Set
  ToldL x []       = ⊤
  ToldL x (s ∷ ls) = Told x s × ToldL x ls

-- The fragment's shape everywhere, its row facts only where live: under
-- a cut switched off nothing is owed, so nothing there is asked to agree.
--
-- REFUTED: 85ad69b9 found-lead without the parts apart, by a merge whose outer and lane are empty ofs at one position
mutual
  G : ∀ {Γ A} → DenEnv Γ → Bool → St Γ A → Set₁
  G ρ b (ofS i p xs)                          = ⊤₁
  G ρ b doneS                                 = ⊤₁
  G ρ b (mapS f s)                            = G ρ b s
  G ρ b (scanS f z s)                         = G ρ b s
  G ρ b (takeS i q w s)                       = G ρ b s
  G ρ b (cutS l a s)                          = G ρ (b ∧ l) s
  G ρ b (flatS (mergeᶠ nothing) f d n q o ls) = MergeG (G ρ b o) (GL ρ b ls) ρ b f d n q o ls
  G ρ b (flatS (mergeᶠ (just m)) f d n q o ls) = MergeG (G ρ b o) (GL ρ b ls) ρ b f d n [] o ls × Live b ((q ≡ []) ⊎ (n ≡ m))
  G ρ b (flatS switchᶠ f d n q o ls)          = MergeG (G ρ b o) (GL ρ b ls) ρ b f d n q o ls
  G ρ b (flatS exhaustᶠ f d n q o ls)         = MergeG (G ρ b o) (GL ρ b ls) ρ b f d n q o ls
  G ρ b (connS k o s)                         = SrcG ρ b (CS.bodyAt k) o × G (Hot (rows ρ o) k ∷ᴬ ρ) b s × Live b (T (CS.closed k) → Empty (rows ρ o)) × Live b (T (CS.closed k) → Told (here refl) s)
  G ρ b (joinS j true x ib)                   = Live₁ b (Fed ib (enter (lookup ρ x) j))
  G ρ b (joinS j false x ib)                  = Live₁ b (Fed ib ∅)
  G ρ b (coldS v l)                           = ⊤₁
  G ρ b _                                     = ⊥₁

  -- A connect's source: still owed while its body subscribes, then good;
  -- once its connect has seen it complete, owing nothing.
  SrcG : ∀ {Γ A} → DenEnv Γ → Bool → Maybe Pos → St Γ A → Set₁
  SrcG ρ b (just _) s = Held s
  SrcG ρ b nothing  s          = G ρ b s

  GL : ∀ {Γ A} → DenEnv Γ → Bool → List (St Γ A) → Set₁
  GL ρ b []       = ⊤₁
  GL ρ b (s ∷ ls) = GLn ρ b s × GL ρ b ls

  -- A lane: in its list and switched on, or out of it and off.
  GLn : ∀ {Γ A} → DenEnv Γ → Bool → St Γ A → Set₁
  GLn ρ b (lnS l s) = LnBody ρ b l s
  GLn ρ b _         = ⊥₁

  LnBody : ∀ {Γ A} → DenEnv Γ → Bool → Bool → St Γ A → Set₁
  LnBody ρ b l (cutS l′ a s) = l ≡ l′ × G ρ (b ∧ l) s × Live (b ∧ l) (EndLast (rows ρ s))
  LnBody ρ b l _             = ⊥₁

Good : ∀ {Γ A} → DenEnv Γ → St Γ A → Set₁
Good ρ = G ρ true

GoodL : ∀ {Γ A} → DenEnv Γ → List (St Γ A) → Set₁
GoodL ρ = GL ρ true

GoodLn : ∀ {Γ A} → DenEnv Γ → St Γ A → Set₁
GoodLn ρ = GLn ρ true

-- Live, a fortiori of the right shape, which reads no environment.
mutual
  shape : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} {v} (s : St Γ A) → G ρ v s → G ρ′ false s
  shape (pend o _)                                  ()
  shape (ofS i p xs)                              g = g
  shape doneS                                     g = g
  shape (mapS f s)                                g = shape s g
  shape {v = v} (cutS l a s)                      g = shape {v = v ∧ l} s g
  shape (flatS (mergeᶠ nothing) f d n q o ls)     m = mergeG₀ (shape o outer) (shapeL ls lanesG) fresh
    where open MergeG m
  shape (flatS (mergeᶠ (just _)) f d n q o ls)    (m , _) = mergeG₀ (shape o outer) (shapeL ls lanesG) refl , tt
    where open MergeG m
  shape (flatS switchᶠ f d n q o ls)              m = mergeG₀ (shape o outer) (shapeL ls lanesG) fresh
    where open MergeG m
  shape (flatS exhaustᶠ f d n q o ls)             m = mergeG₀ (shape o outer) (shapeL ls lanesG) fresh
    where open MergeG m
  shape (coldS _ _)                               g = g
  shape (scanS f z s)                             g = shape s g
  shape (lnS _ _)                                 ()
  shape (takeS i q w s)                           g = shape s g
  shape {v = v} (connS k o b)                     (gs , gb , _) = shapeSrc {v = v} (CS.bodyAt k) o gs , shape b gb , tt , tt
  shape (joinS j true x ib)                       _ = tt₁
  shape (joinS j false x ib)                      _ = tt₁

  shapeSrc : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} {v} m (s : St Γ A) → SrcG ρ v m s → SrcG ρ′ false m s
  shapeSrc (just _) s g = g
  shapeSrc {v = v} nothing s g  = shape {v = v} s g

  shapeL : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} {v} (ls : List (St Γ A)) → GL ρ v ls → GL ρ′ false ls
  shapeL []       _        = tt₁
  shapeL (s ∷ ls) (g , gs) = shapeLn s g , shapeL ls gs

  shapeLn : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} {v} (s : St Γ A) → GLn ρ v s → GLn ρ′ false s
  shapeLn {v = v} (lnS l (cutS l′ a s)) (eq , g , _) = eq , shape {v = v ∧ l} s g , tt
  shapeLn (lnS _ (pend _ _))              ()
  shapeLn (lnS _ (coldS _ _))           ()
  shapeLn (lnS _ (ofS _ _ _))           ()
  shapeLn (lnS _ doneS)                 ()
  shapeLn (lnS _ (mapS _ _))            ()
  shapeLn (lnS _ (scanS _ _ _))         ()
  shapeLn (lnS _ (lnS _ _))             ()
  shapeLn (lnS _ (takeS _ _ _ _))       ()
  shapeLn (lnS _ (flatS _ _ _ _ _ _ _)) ()
  shapeLn (lnS _ (connS _ _ _))         ()
  shapeLn (lnS _ (joinS _ _ _ _))       ()
  shapeLn (pend _ _)              ()
  shapeLn (coldS _ _)           ()
  shapeLn (ofS _ _ _)           ()
  shapeLn doneS                 ()
  shapeLn (mapS _ _)            ()
  shapeLn (scanS _ _ _)         ()
  shapeLn (cutS _ _ _)          ()
  shapeLn (takeS _ _ _ _)       ()
  shapeLn (flatS _ _ _ _ _ _ _) ()
  shapeLn (connS _ _ _)         ()
  shapeLn (joinS _ _ _ _)       ()

data LaneV {Γ A} (ρ : DenEnv Γ) : St Γ A → Set₁ where
  on  : ∀ a s → Good ρ s → EndLast (rows ρ s) → LaneV ρ (lnS true (cutS true a s))
  off : ∀ a s → LaneV ρ (lnS false (cutS false a s))

lane-v : ∀ {Γ A} {ρ : DenEnv Γ} (s : St Γ A) → GoodLn ρ s → LaneV ρ s
lane-v (lnS true  (cutS true  a s)) (refl , g , e) = on a s g e
lane-v (lnS false (cutS false a s)) (refl , _)     = off a s
lane-v (lnS true  (cutS false a s)) (() , _)
lane-v (lnS false (cutS true  a s)) (() , _)
lane-v (lnS _ (lnS _ _)) ()
lane-v (lnS _ (pend _ _)) ()
lane-v (lnS _ (coldS _ _)) ()
lane-v (lnS _ (ofS _ _ _)) ()
lane-v (lnS _ (doneS)) ()
lane-v (lnS _ (mapS _ _)) ()
lane-v (lnS _ (scanS _ _ _)) ()
lane-v (lnS _ (takeS _ _ _ _)) ()
lane-v (lnS _ (flatS _ _ _ _ _ _ _)) ()
lane-v (lnS _ (connS _ _ _)) ()
lane-v (lnS _ (joinS _ _ _ _)) ()
lane-v (pend _ _) ()
lane-v (coldS _ _) ()
lane-v (ofS _ _ _) ()
lane-v (doneS) ()
lane-v (mapS _ _) ()
lane-v (scanS _ _ _) ()
lane-v (takeS _ _ _ _) ()
lane-v (flatS _ _ _ _ _ _ _) ()
lane-v (connS _ _ _) ()
lane-v (joinS _ _ _ _) ()
lane-v (cutS _ _ _) ()

-- No lane in the list: none owes anything.
dead-empty : ∀ {Γ A} {ρ : DenEnv Γ} (ls : List (St Γ A)) → GoodL ρ ls → live ls ≡ 0 → Each Empty (rowsL ρ ls)
dead-empty []       _         _ = _
dead-empty (s ∷ ls) (gs , gl) z with lane-v s gs
dead-empty (_ ∷ ls) (gs , gl) () | on _ _ _ _
dead-empty (_ ∷ ls) (gs , gl) z  | off _ _ =(λ ()) , dead-empty ls gl z


------------------------------------------------------------------------
-- An of

ofPos : ∀ {A : Set} → Pos → ℕ → List A → Pos
ofPos p i []      = p ++ [ last ]
ofPos p i (_ ∷ _) = p ++ [ ix i ]

of-from : ∀ {A} p i (xs : List A) → From (at (ofPos p i xs)) (InE (ofᴱ p i xs))
of-from p i []       at-end     = ⊑-refl _
of-from p i (x ∷ xs) at-out     = ⊑-refl _
of-from p i (x ∷ xs) (on-out r) = ⊑-trans (next xs) (of-from p (suc i) xs r)
  where
    next : ∀ {A : Set} (ys : List A) → at (p ++ [ ix i ]) ⊑ at (ofPos p (suc i) ys)
    next []      = ≺→⊑ (subst T (sym (<ᵖ-part p [] [] refl)) tt)
    next (_ ∷ _) = ≺→⊑ (subst T (sym (<ᵖ-part p [] [] (<ᵖ-ix i))) tt)

of-shows : ∀ {R Γ A} (c : Ctx R Γ A) i p (xs : List A) {e} → outOf c (ofS i p xs) ofM ≡ shows e → InE (ofᴱ p i xs) (ofPos p i xs) (toEv e)
of-shows c i p []       eq with closed c
of-shows c i p []       ()   | true
of-shows c i p []       refl | false = at-end
of-shows c i p (x ∷ xs) eq with closed c
of-shows c i p (x ∷ xs) ()   | true
of-shows c i p (x ∷ xs) refl | false = at-out

------------------------------------------------------------------------
-- One child

-- A mark of the node's own, shown silently, before or after its child's.
own-first : ∀ {R A} {t : EmissionSet A} (fc : Focus R) (m : Mark) (κ : Key) (y : Maybe (Cand R A)) → OK t y → OK t (first (just (found fc m κ , κ , still)) y)
own-first fc m κ nothing            e = record { from = λ r → ⊥-elim (e r) ; mark = ⊑-refl _ ; shown = λ () }
own-first fc m κ (just (g′ , K , o)) b with K <ᴷ κ in lt
... | true  = b
... | false = record { from = λ r → ⊑-trans (⊑i lt) (from b r) ; mark = ⊑-refl _ ; shown = λ () }

-- Silent, a node owes nothing it shows; its key still bounds its mark.
silenced : ∀ {R A} (y : Maybe (Cand R A)) → Mk y → OK {R} {A} (λ _ _ → ⊥) (retag (cutT false) y)
silenced nothing                        _  = λ ()
silenced (just (found f m κ , K , o)) mk = record { from = λ () ; mark = mk ; shown = λ () }

kept : ∀ {R A} {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OK t (retag (cutT true) y)
kept nothing            b = b
kept (just (g , K , o)) b = b

mapped : ∀ {R A B} (f : A → B) {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OK (MapT f t) (retag (mapT f) y)
mapped f nothing e (map-out r) = e r
mapped f nothing e (map-skip r) = e r
mapped f nothing e (map-pin r) = e r
mapped f nothing e (map-end r) = e r
mapped f (just (g , K , still)) b =
  record { from = λ { (map-out r) → from b r ; (map-skip r) → from b r ; (map-pin r) → from b r ; (map-end r) → from b r } ; mark = mark b ; shown = λ () }
mapped f (just (g , K , shows (nx a))) b =
  record { from = λ { (map-out r) → from b r ; (map-skip r) → from b r ; (map-pin r) → from b r ; (map-end r) → from b r } ; mark = mark b
         ; shown = λ { refl → let (q , k , r) = shown b refl in q , k , map-out r } }
mapped f (just (g , K , shows cp)) b =
  record { from = λ { (map-out r) → from b r ; (map-skip r) → from b r ; (map-pin r) → from b r ; (map-end r) → from b r } ; mark = mark b
         ; shown = λ { refl → let (q , k , r) = shown b refl in q , k , map-end r } }

-- A scan's next value folds its source's least one, keyed as its source.
scanned : ∀ {R A B} (f : B → A → B) z {t : EmissionSet A} (y : Maybe (Cand R A)) → OK t y → OK (Scan.ScanT f z t) (retag (scanT f z) y)
scanned f z nothing e (Scan.sval a)  = e (proj₂ (acc-val a))
scanned f z nothing e (Scan.sstep r) = e r
scanned f z nothing e (Scan.spin r)  = e r
scanned f z nothing e (Scan.send r)  = e r
scanned f z (just (g , K , still)) b =
  record { from = λ { (Scan.sval a) → from b (proj₂ (acc-val a)) ; (Scan.sstep r) → from b r ; (Scan.spin r) → from b r ; (Scan.send r) → from b r } ; mark = mark b ; shown = λ () }
scanned f z (just (g , K , shows (nx a))) b =
  record { from = λ { (Scan.sval a) → from b (proj₂ (acc-val a)) ; (Scan.sstep r) → from b r ; (Scan.spin r) → from b r ; (Scan.send r) → from b r } ; mark = mark b
         ; shown = λ { refl → let (q , k , r) = shown b refl in q , k , Scan.sval (Scan.acc₀ r (λ r′ → ⊑→≼ (subst (_⊑ at _) k (from b r′)))) } }
scanned f z (just (g , K , shows cp)) b =
  record { from = λ { (Scan.sval a) → from b (proj₂ (acc-val a)) ; (Scan.sstep r) → from b r ; (Scan.spin r) → from b r ; (Scan.send r) → from b r } ; mark = mark b
         ; shown = λ { refl → let (q , k , r) = shown b refl in q , k , Scan.send r } }

------------------------------------------------------------------------
-- The lanes, one by one

-- A lane read through its list's switch: an ended lane shows nothing.
lane-ok : ∀ {R Γ B} {ρ : DenEnv Γ} (s : St Γ B) (y : Maybe (Cand R B)) → OK (rows ρ s) y → OK (rows ρ s) (retag (cutT (alive s)) y)
lane-ok (lnS true s)  y b = kept y b
lane-ok (lnS false s) y b = silenced y (ok-mk y b)
lane-ok (ofS i p xs)          y b = kept y b
lane-ok doneS                 y b = kept y b
lane-ok (mapS f s)            y b = kept y b
lane-ok (cutS l a s)          y b = kept y b
lane-ok (flatS op f d n q o ls) y b = kept y b
lane-ok (pend o _)      y b = kept y b
lane-ok (coldS v l)   y b = kept y b
lane-ok (scanS f z s) y b = kept y b
lane-ok (takeS i q w s) y b = kept y b
lane-ok (connS k o b′) y b = kept y b
lane-ok (joinS j g x ib) y b = kept y b

-- The first of a lane and the lanes after it.
lanes-first : ∀ {R B} {l : EmissionSet B} {Ls} (x y : Maybe (Cand R B)) → OK l x → OKL Ls y → OKL (l ∷ Ls) (first x y)
lanes-first nothing nothing ex ey = ex , ey
lanes-first nothing (just (g , K , o)) ex (fy , my , sy) =
  ((λ r → ⊥-elim (ex r)) , fy) , my , λ eq → let (q , k , x) = sy eq in q , k , inj₂ x
lanes-first {Ls = Ls} (just (g , K , o)) nothing bx ey =
  (from bx , from-empty Ls ey) , mark bx , λ eq → let (q , k , r) = shown bx eq in q , k , inj₁ r
lanes-first {Ls = Ls} (just (g , K , o)) (just (g′ , K′ , o′)) bx (fy , my , sy) with K′ <ᴷ K in lt
... | true  = ((λ r → ⊑-trans (<→⊑ K′ K lt) (from bx r)) , fy) , my
            , λ eq → let (q , k , x) = sy eq in q , k , inj₂ x
... | false = (from bx , from-weak Ls (⊑i lt) fy) , mark bx
            , λ eq → let (q , k , r) = shown bx eq in q , k , inj₁ r

------------------------------------------------------------------------
-- The race
