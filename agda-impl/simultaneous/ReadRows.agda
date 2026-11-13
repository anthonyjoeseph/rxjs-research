{-# OPTIONS --guardedness #-}

-- THE READER'S ROWS: the joined fold of `joinStep` over a reading, each
-- row hung under the row of the reading it came from — at it, at its
-- first child (a value's silent step), or on its lane under its second.
-- Over a reading with no pins, one event a position, no row under
-- another and none past its end, rows hung under distinct reading rows
-- are ordered as those are, so every row before one hangs under a
-- reading row at or before its own, and a listing of the reading lists
-- the joined rows.
--
-- A fold's emits are the routes a reader joining late sends, each a
-- mark, then the emit folded in: the only value on a lane is its last
-- row, so the carrier of a value is the lane's last value row.
module simultaneous.ReadRows where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter; length; replicate)
import Data.List as L
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import denotation.Position using (Pos; Label; ix; last; _∙_; _⊕_; _<ᵖ_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; Truncate; Reach; Few; _≺_; _≼_;
  InE; at-out; on-out; LaneOf; module Scan; module Merge; module Op)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≺-≼-≺; ≼-refl; ≼-or-≻; ≼-split; ≼-antisym; ≺-ext; reach-few)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊑-≼; full)
open import denotation.Laws.Shows using (∈-stable)
open import denotation.Laws.Worlds.Leaves using (module AccF; of-rows; of-in; of-row; of-reach; of-idx; of-end-row; ine-pin)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark; begin; over; stop; outerOpen; outerClose;
  laneStart; carry; laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.Attribution using (Live; Shown; Carried; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Folds using (reach-kin; few-¬¬listed; module ListedFold)
open import simultaneous.CarryBase using (Kin; k-out; k-skip; k-pin; k-end; apart; sub-listed)
open import simultaneous.Carry using (annValues)
open import simultaneous.Rejoined using (Flat; nest; few-reach)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; joinStep; joins)

------------------------------------------------------------------------
-- A fold's emits: marks, then the emit folded in

Marked : ∀ {X : Set} → IE X → Set
Marked y = valuesOf y ≡ []

private
  rep-marks : ∀ {X : Set} k n → All (Marked {X}) (replicate k (instEmit (mark begin) n))
  rep-marks zero    n = []
  rep-marks (suc k) n = refl ∷ rep-marks k n

  joins-marks : ∀ {X : Set} r (y : IE X) → All Marked (joins r y)
  joins-marks (m , k) (instEmit (mark begin) n) with does (n ≟ᵖ m)
  ... | true  = rep-marks k m
  ... | false = []
  joins-marks (m , k) (instEmit (value _) _)        = rep-marks k m
  joins-marks (m , k) (instEmit (mark over) _)       = rep-marks k m
  joins-marks (m , k) (instEmit (mark stop) _)       = rep-marks k m
  joins-marks (m , k) (instEmit (mark outerOpen) _)  = rep-marks k m
  joins-marks (m , k) (instEmit (mark outerClose) _) = rep-marks k m
  joins-marks (m , k) (instEmit (mark laneStart) _)  = rep-marks k m
  joins-marks (m , k) (instEmit (mark carry) _)      = rep-marks k m
  joins-marks (m , k) (instEmit (mark laneDone) _)   = rep-marks k m
  joins-marks (m , k) (instEmit (mark burstEnd) _)   = rep-marks k m
  joins-marks (m , k) (instEmit (mark outerDone) _)  = rep-marks k m
  joins-marks (m , k) (instEmit (mark subscribed) _) = rep-marks k m
  joins-marks (m , k) (instEmit (mark completed) _)  = rep-marks k m

step-just : ∀ {X : Set} (b : Bool × List (IE X)) r x → Σ (List (IE X)) λ ms → All Marked ms × proj₂ (joinStep b (r , just x)) ≡ ms ++ [ x ]
step-just (true  , _) r x = joins r x , joins-marks r x , refl
step-just (false , _) r x = [] , [] , refl

step-none : ∀ {X : Set} (b : Bool × List (IE X)) r → All Marked (proj₂ (joinStep b (r , nothing)))
step-none (true  , _) (m , k) = rep-marks k m
step-none (false , _) r       = []

------------------------------------------------------------------------
-- An of's rows

of-skip : ∀ {A : Set} p i (xs : List A) {k} → InE (ofᴱ p i xs) k skip → ⊥
of-skip p i (x ∷ xs) (on-out r) = of-skip p (suc i) xs r

-- The value appended, at its index.
of-at : ∀ {A : Set} p i (ms : List A) x → InE (ofᴱ p i (ms ++ [ x ])) (p ⊕ [ ix (i + length ms) ]) (out x)
of-at p i []       x = subst (λ j → InE (ofᴱ p i [ x ]) (p ⊕ [ ix j ]) (out x)) (sym (+-identityʳ i)) at-out
of-at p i (m ∷ ms) x = subst (λ j → InE (ofᴱ p i (m ∷ ms ++ [ x ])) (p ⊕ [ ix j ]) (out x)) (sym (+-suc i (length ms)))
  (on-out (of-at p (suc i) ms x))

private
  marked-one : ∀ {X : Set} {y : IE X} {a} → Marked y → valuesOf y ≡ a ∷ [] → ⊥
  marked-one mk eq with trans (sym mk) eq
  ... | ()

-- Past marks, the only value shown is the last.
of-shown : ∀ {X : Set} p i (ms : List (IE X)) x → All Marked ms → ∀ {k v} → InE (ofᴱ p i (ms ++ [ x ])) k (out v)
         → Shown (One valuesOf) (out v) → k ≡ p ⊕ [ ix (i + length ms) ] × v ≡ x
of-shown p i []       x _        at-out      _        = cong (λ j → p ⊕ [ ix j ]) (sym (+-identityʳ i)) , refl
of-shown p i []       x _        (on-out ()) _
of-shown p i (m ∷ ms) x (mk ∷ _) at-out      (_ , eq) = ⊥-elim (marked-one mk eq)
of-shown p i (m ∷ ms) x (_ ∷ al) (on-out r)  sh with of-shown p (suc i) ms x al r sh
... | eq , refl = trans eq (cong (λ j → p ⊕ [ ix j ]) (sym (+-suc i (length ms)))) , refl

-- Marks alone show nothing.
of-marks : ∀ {X : Set} p i (xs : List (IE X)) → All Marked xs → ∀ {k v} → InE (ofᴱ p i xs) k (out v) → Shown (One valuesOf) (out v) → ⊥
of-marks p i []       []       ()          _
of-marks p i (m ∷ xs) (mk ∷ _) at-out      (_ , eq) = marked-one mk eq
of-marks p i (m ∷ xs) (_ ∷ al) (on-out r)  sh       = of-marks p (suc i) xs al r sh

------------------------------------------------------------------------
-- A position one label up

private
  dropLast : List Label → List Label
  dropLast []           = []
  dropLast (_ ∷ [])     = []
  dropLast (x ∷ y ∷ ys) = x ∷ dropLast (y ∷ ys)

  dropLast-snoc : ∀ xs a → dropLast (xs ++ [ a ]) ≡ xs
  dropLast-snoc []           a = refl
  dropLast-snoc (x ∷ [])     a = refl
  dropLast-snoc (x ∷ y ∷ xs) a = cong (x ∷_) (dropLast-snoc (y ∷ xs) a)

up : Pos → Pos
up (i ∙ p) = i ∙ dropLast p

up-⊕ : ∀ l a → up (l ⊕ [ a ]) ≡ l
up-⊕ (i ∙ p) a = cong (i ∙_) (dropLast-snoc p a)

------------------------------------------------------------------------
-- Lists built along membership

mapIn : ∀ {A B : Set} (xs : List A) → (∀ {x} → x ∈ xs → B) → List B
mapIn []       g = []
mapIn (x ∷ xs) g = g (here refl) ∷ mapIn xs (λ m → g (there m))

mapIn-in : ∀ {A B : Set} (xs : List A) (g : ∀ {x} → x ∈ xs → B) {x} (m : x ∈ xs) → g m ∈ mapIn xs g
mapIn-in (x ∷ xs) g (here refl) = here refl
mapIn-in (x ∷ xs) g (there m)   = there (mapIn-in xs (λ m′ → g (there m′)) m)

mapIn-out : ∀ {A B : Set} (xs : List A) (g : ∀ {x} → x ∈ xs → B) {y} → y ∈ mapIn xs g → Σ A λ x → Σ (x ∈ xs) λ m → y ≡ g m
mapIn-out (x ∷ xs) g (here eq) = x , here refl , eq
mapIn-out (x ∷ xs) g (there m) with mapIn-out xs (λ m′ → g (there m′)) m
... | z , mz , eq = z , there mz , eq

------------------------------------------------------------------------
-- The rows

module Rows {X : Set} {u : EmissionSet (AIE X)}
  (funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′)
  (flatU : Flat u)
  (pinU : ∀ {y r} → u y (pin r) → ⊥)
  (rchU : ∀ {q e} → u q e → Reach u q e)
  (quietU : ∀ {c y e} → u c end → u y e → c ≺ y → ⊥) where

  St : Set
  St = Bool × List (IE X)

  module S = Scan (joinStep {X}) (true , []) u
  open S using (Acc; acc₀; acc; ScanT)
  module A = AccF (joinStep {X}) (true , []) {u} funcU
  module EL = ListedFold (joinStep {X}) (true , []) {u} funcU

  Sc : EmissionSet St
  Sc = Truncate ScanT

  F : St → Den (IE X)
  F x = Op.of (proj₂ x)

  module J = Merge F Sc

  R : EmissionSet (IE X)
  R = Truncate J.JoinT

  private
    o≢s : ∀ {a : AIE X} → out a ≡ skip → ⊥
    o≢s ()

    o≢e : ∀ {a : AIE X} → out a ≡ end → ⊥
    o≢e ()

    s≢e : skip {A = AIE X} ≡ end → ⊥
    s≢e ()

  ----------------------------------------------------------------------
  -- The scan's rows

  sc-u : ∀ {k e′} → ScanT k e′ → Σ (Ev (AIE X)) λ e → u k e × Kin e e′
  sc-u (S.sval a)  = out _ , proj₂ (A.acc-val a) , k-out
  sc-u (S.sstep x) = skip , x , k-skip
  sc-u (S.spin x)  = pin _ , x , k-pin
  sc-u (S.send x)  = end , x , k-end

  sc-out : ∀ {l a st} → u l (out a) → Acc l st → Sc l (out st)
  sc-out {a = a} {st} x ac = S.sval ac , reach-kin {a = u} {b = ScanT} (λ {k} {e′} → sc-u {k} {e′}) {e = out a} {e′ = out st} k-out (rchU x)

  sc-skip : ∀ {l} → u l skip → Sc l skip
  sc-skip x = S.sstep x , reach-kin {a = u} {b = ScanT} (λ {k} {e′} → sc-u {k} {e′}) {e = skip} {e′ = skip} k-skip (rchU x)

  sc-end : ∀ {l} → u l end → Sc l end
  sc-end x = S.send x , reach-kin {a = u} {b = ScanT} (λ {k} {e′} → sc-u {k} {e′}) {e = end} {e′ = end} k-end (rchU x)

  acc-u : ∀ {l st} (ac : Acc l st) → u l (out (proj₁ (A.acc-val ac)))
  acc-u ac = proj₂ (A.acc-val ac)

  -- The fold at a row: one step past the fold before it.
  acc-step : ∀ {l st} → Acc l st → Σ St λ b → Σ (AIE X) λ a → u l (out a) × st ≡ joinStep b a
  acc-step (acc₀ x _)          = (true , []) , _ , x , refl
  acc-step (acc {b = b} _ x _ _) = b , _ , x , refl

  step-of : ∀ {l st r v} → Acc l st → u l (out (r , just v)) → Σ (List (IE X)) λ ms → All Marked ms × proj₂ st ≡ ms ++ [ v ]
  step-of ac x with acc-step ac
  ... | b , a , y , refl with funcU x y
  ...   | refl = step-just b _ _

  ----------------------------------------------------------------------
  -- Where a row hangs

  data Hang (l : Pos) : Pos → Set where
    h-at   : Hang l l
    h-val  : Hang l (l ⊕ [ ix 0 ])
    h-lane : ∀ b → Hang l (l ⊕ [ ix 1 ] ⊕ [ b ])

  hang-⊑ : ∀ {l k} → Hang l k → l ⊑ k
  hang-⊑ {l} h-at       = ⊑-refl l
  hang-⊑ {l} h-val      = ⊑-snoc⁺ l
  hang-⊑ {l} (h-lane b) = ⊑-trans (⊑-snoc⁺ l) (⊑-snoc⁺ (l ⊕ [ ix 1 ]))

  -- Hung under rows in order: in that order.
  hang-lt : ∀ {l₁ l₂ e₁ e₂ k₁ k₂} → u l₁ e₁ → u l₂ e₂ → l₁ ≺ l₂ → Hang l₁ k₁ → Hang l₂ k₂ → k₁ ≺ k₂
  hang-lt {l₁} {l₂} x₁ x₂ lt h₁ h₂ =
    let (σ , e₁) = hang-⊑ h₁ ; (σ′ , e₂) = hang-⊑ h₂ in subst₂ _≺_ (sym e₁) (sym e₂) (apart {l₁} {l₂} lt (nest {S = u} flatU x₁ x₂ lt) σ σ′)

  hang-≼ : ∀ {l₁ l₂ e₁ e₂ k₁ k₂} → u l₁ e₁ → u l₂ e₂ → Hang l₁ k₁ → Hang l₂ k₂ → k₁ ≺ k₂ → l₁ ≼ l₂
  hang-≼ {k₁ = k₁} {k₂} x₁ x₂ h₁ h₂ kk l₂₁ = ≺-absurd {k₁} {k₂} kk (hang-lt x₂ x₁ l₂₁ h₂ h₁)

  hang-uniq : ∀ {l₁ l₂ e₁ e₂ k} → u l₁ e₁ → u l₂ e₂ → Hang l₁ k → Hang l₂ k → l₁ ≡ l₂
  hang-uniq {k = k} x₁ x₂ h₁ h₂ = ≼-antisym (λ l₂₁ → ≺-irrefl {k} (hang-lt x₂ x₁ l₂₁ h₂ h₁)) (λ l₁₂ → ≺-irrefl {k} (hang-lt x₁ x₂ l₁₂ h₁ h₂))

  private
    lane-shape : ∀ {p} {xs : List (IE X)} {k e} → InE (ofᴱ p 0 xs) k e → Σ Label λ b → k ≡ p ⊕ [ b ]
    lane-shape {p} {xs} r with of-idx p 0 xs r
    ... | inj₁ (j , _ , eq) = ix j , eq
    ... | inj₂ eq           = last , eq

  lane-hang : ∀ {l} {xs : List (IE X)} {k e} → InE (ofᴱ (l ⊕ [ ix 1 ]) 0 xs) k e → Hang l k
  lane-hang {l} r = let (b , eq) = lane-shape r in subst (Hang l) (sym eq) (h-lane b)

  lane-row : ∀ {q} (a : St) {k e} → InE (ofᴱ (q ⊕ [ ix 1 ]) 0 (proj₂ a)) k e → LaneOf F q a k e
  lane-row {q} a r = (r , of-reach (q ⊕ [ ix 1 ]) 0 (proj₂ a)) , subst ((q ⊕ [ ix 1 ]) ≺_) (sym (proj₂ (lane-shape r))) (≺-ext (q ⊕ [ ix 1 ]) [])

  ----------------------------------------------------------------------
  -- Every lane before an end of the reading has ended by it; none past
  -- its own value's row has

  private
    srow : ∀ {k e′} (sc : Sc k e′) → u k (proj₁ (sc-u (proj₁ sc)))
    srow sc = proj₁ (proj₂ (sc-u (proj₁ sc)))

  sc-end-u : ∀ {c} → Sc c end → u c end
  sc-end-u (S.send x , _) = x

  done-at : ∀ {c} → Sc c end → J.Done c
  done-at {c} sc = (c , sc , ≼-refl {c}) , λ {q} {a} sq _ qc _ →
    q ⊕ [ ix 1 ] ⊕ [ last ] , lane-row {q} a (of-end-row (q ⊕ [ ix 1 ]) 0 (proj₂ a))
    , ≺→≼ {q ⊕ [ ix 1 ] ⊕ [ last ]} {c} (hang-lt (srow sq) (sc-end-u sc) qc (h-lane last) h-at)

  not-done : ∀ {l a k} → u l (out a) → Hang l k → ¬ J.Done k
  not-done {l} {k = k} x h ((c₀ , sc₀ , c₀k) , _) with ≼-or-≻ c₀ l
  ... | inj₂ lc₀ = c₀k (hang-lt x (sc-end-u sc₀) lc₀ h h-at)
  ... | inj₁ c₀l with ≼-split {c₀} {l} c₀l
  ...   | inj₁ c₀≺l = quietU (sc-end-u sc₀) x c₀≺l
  ...   | inj₂ refl = o≢e (funcU x (sc-end-u sc₀))

  ----------------------------------------------------------------------
  -- A joined row, read by the reading row it hangs under

  data View : Pos → Ev (IE X) → Set where
    v-val  : ∀ {q a st} → u q (out a) → Acc q st → View (q ⊕ [ ix 0 ]) skip
    v-step : ∀ {q} → u q skip → View q skip
    v-end  : ∀ {q e} → u q end → View q e
    v-lane : ∀ {q a st k e₁ e} → u q (out a) → Acc q st → InE (ofᴱ (q ⊕ [ ix 1 ]) 0 (proj₂ st)) k e₁ → View k e

  view : ∀ {k e} → J.JoinT k e → View k e
  view (J.val (S.sval ac , _))                       = v-val (acc-u ac) ac
  view (J.step (S.sstep x , _))                      = v-step x
  view (J.opin (S.spin x , _))                       = ⊥-elim (pinU x)
  view (J.oend (S.send x , _) _)                     = v-end x
  view (J.opass (S.send x , _) _)                    = v-end x
  view (J.lane (S.sval ac , _) _ ((r , _) , _) _ _)    = v-lane (acc-u ac) ac r
  view (J.lend (S.sval ac , _) _ ((r , _) , _) _ _ _)  = v-lane (acc-u ac) ac r
  view (J.lpass (S.sval ac , _) _ ((r , _) , _) _ _ _) = v-lane (acc-u ac) ac r
  view (J.hand _ _ _ _ ())
  view (J.left _ _ ((r , _) , _) _ _)                = ⊥-elim (ine-pin r)
  view (J.run () _)
  view (J.rend () _ _)
  view (J.rpass () _ _)
  view (J.rhand () _)

  -- The reading has no pins: its outer has none, nor has a lane.
  pin-free : ∀ {k r} → J.JoinT k (pin r) → ⊥
  pin-free (J.opin (S.spin x , _))          = pinU x
  pin-free (J.lane _ _ ((r , _) , _) _ _) = ine-pin r
  pin-free (J.left _ _ ((r , _) , _) _ _) = ine-pin r
  pin-free (J.run () _)

  vpos : ∀ {k e} → View k e → Pos
  vpos (v-val {q} _ _)    = q
  vpos (v-step {q} _)     = q
  vpos (v-end {q} _)      = q
  vpos (v-lane {q} _ _ _) = q

  vev : ∀ {k e} → View k e → Ev (AIE X)
  vev (v-val {a = a} _ _)    = out a
  vev (v-step _)             = skip
  vev (v-end _)              = end
  vev (v-lane {a = a} _ _ _) = out a

  vrow : ∀ {k e} (v : View k e) → u (vpos v) (vev v)
  vrow (v-val x _)    = x
  vrow (v-step x)     = x
  vrow (v-end x)      = x
  vrow (v-lane x _ _) = x

  vhang : ∀ {k e} (v : View k e) → Hang (vpos v) k
  vhang (v-val _ _)                  = h-val
  vhang (v-step _)                   = h-at
  vhang (v-end _)                    = h-at
  vhang (v-lane {st = st} _ _ r) = lane-hang {xs = proj₂ st} r

  ----------------------------------------------------------------------
  -- A reading row with its fold, and the joined rows hung under it

  data Cell (l : Pos) : Set where
    c-out  : ∀ {a st} → u l (out a) → Acc l st → Cell l
    c-skip : u l skip → Cell l
    c-end  : u l end → Cell l

  cellRows : ∀ {l} → Cell l → List Pos
  cellRows {l} (c-out {st = st} _ _) = (l ⊕ [ ix 0 ]) ∷ of-rows (l ⊕ [ ix 1 ]) 0 (proj₂ st)
  cellRows {l} (c-skip _)            = [ l ]
  cellRows {l} (c-end _)             = [ l ]

  cell : ∀ {l e} → u l e → Listed u l → Cell l
  cell {e = out a} x L = c-out x (proj₂ (EL.fold-listed L x))
  cell {e = skip}  x _ = c-skip x
  cell {e = end}   x _ = c-end x
  cell {e = pin _} x _ = ⊥-elim (pinU x)

  -- A joined row is among its reading row's.
  vin : ∀ {k e} (v : View k e) (c : Cell (vpos v)) → k ∈ cellRows c
  vin (v-val _ _)  (c-out _ _) = here refl
  vin (v-val x _)  (c-skip y)  = ⊥-elim (o≢s (funcU x y))
  vin (v-val x _)  (c-end y)   = ⊥-elim (o≢e (funcU x y))
  vin (v-step _)   (c-skip _)  = here refl
  vin (v-step x)   (c-out y _) = ⊥-elim (o≢s (funcU y x))
  vin (v-step x)   (c-end y)   = ⊥-elim (s≢e (funcU x y))
  vin (v-end _)    (c-end _)   = here refl
  vin (v-end x)    (c-out y _) = ⊥-elim (o≢e (funcU y x))
  vin (v-end x)    (c-skip y)  = ⊥-elim (s≢e (funcU y x))
  vin (v-lane {q} {st = st} {k} _ ac r) (c-out _ ac′) =
    there (subst (λ z → k ∈ of-rows (q ⊕ [ ix 1 ]) 0 (proj₂ z)) (A.acc-func refl ac ac′) (of-in (q ⊕ [ ix 1 ]) 0 (proj₂ st) r))
  vin (v-lane x _ _) (c-skip y) = ⊥-elim (o≢s (funcU x y))
  vin (v-lane x _ _) (c-end y)  = ⊥-elim (o≢e (funcU x y))

  vin′ : ∀ {k e} (v : View k e) {l} (c : Cell l) → vpos v ≡ l → k ∈ cellRows c
  vin′ v c refl = vin v c

  -- Each of a reading row's joined rows is a row.
  cell-row : ∀ {l} (c : Cell l) {k} → k ∈ cellRows c → Σ _ (J.JoinT k) × Hang l k
  cell-row (c-out x ac) (here refl) = (skip , J.val (sc-out x ac)) , h-val
  cell-row {l} (c-out {st = st} x ac) {k} (there m) with of-row (l ⊕ [ ix 1 ]) 0 (proj₂ st) m
  ... | out v , r = (out v , J.lane (sc-out x ac) tt (lane-row {l} st r) (λ ()) tt) , lane-hang {l} {proj₂ st} r
  ... | end , r   = (skip , J.lpass (sc-out x ac) tt (lane-row {l} st r) (λ ()) (λ ()) (not-done x (lane-hang {l} {proj₂ st} r)))
                    , lane-hang {l} {proj₂ st} r
  ... | skip , r  = ⊥-elim (of-skip (l ⊕ [ ix 1 ]) 0 (proj₂ st) r)
  ... | pin _ , r = ⊥-elim (ine-pin r)
  cell-row (c-skip x) (here refl) = (skip , J.step (sc-skip x)) , h-at
  cell-row (c-end x)  (here refl) = (end , J.oend (sc-end x) (done-at (sc-end x))) , h-at

  ----------------------------------------------------------------------
  -- The joined rows of a listing

  rowsOf : ∀ (ks : List Pos) → (∀ {x} → x ∈ ks → Cell x) → List Pos
  rowsOf []       g = []
  rowsOf (x ∷ ks) g = cellRows (g (here refl)) ++ rowsOf ks (λ m → g (there m))

  rowsOf-in : ∀ ks (g : ∀ {x} → x ∈ ks → Cell x) {x} (m : x ∈ ks) {k} → k ∈ cellRows (g m) → k ∈ rowsOf ks g
  rowsOf-in (x ∷ ks) g (here refl) km = ∈-++⁺ˡ km
  rowsOf-in (x ∷ ks) g (there m)   km = ∈-++⁺ʳ (cellRows (g (here refl))) (rowsOf-in ks (λ m′ → g (there m′)) m km)

  rowsOf-out : ∀ ks (g : ∀ {x} → x ∈ ks → Cell x) {k} → k ∈ rowsOf ks g → Σ Pos λ x → Σ (x ∈ ks) λ m → k ∈ cellRows (g m)
  rowsOf-out (x ∷ ks) g km with ∈-++⁻ (cellRows (g (here refl))) km
  ... | inj₁ k′ = x , here refl , k′
  ... | inj₂ k′ with rowsOf-out ks (λ m′ → g (there m′)) k′
  ...   | y , m , k″ = y , there m , k″

  cells : ∀ {l} (L : Listed u l) → ∀ {x} → x ∈ proj₁ L → Cell x
  cells L m = cell (proj₂ (proj₂ (proj₂ (proj₂ L) m))) (sub-listed L (proj₁ (proj₂ (proj₂ L) m)))

  before : ∀ {l} → Listed u l → List Pos
  before L = rowsOf (proj₁ L) (cells L)

  -- Before a row hung under a listed reading row: the joined rows of the
  -- listing, and the row's own.
  few-at : ∀ {l e₀} (x : u l e₀) (L : Listed u l) {k} → Hang l k → Few J.JoinT k
  few-at {l} x L {k} h = before L ++ cellRows (cell x L) , λ y kk → pick (view y) kk
    where
      pick : ∀ {k′ e′} (v : View k′ e′) → k′ ≺ k → k′ ∈ before L ++ cellRows (cell x L)
      pick v kk with ≼-split (hang-≼ (vrow v) x (vhang v) h kk)
      ... | inj₁ lt = let m = proj₁ (proj₂ L) (vrow v) lt in ∈-++⁺ˡ (rowsOf-in (proj₁ L) (cells L) m (vin v (cells L m)))
      ... | inj₂ eq = ∈-++⁺ʳ (before L) (vin′ v (cell x L) eq)

  r-at : ∀ {l e₀} (x : u l e₀) (L : Listed u l) {k} → k ∈ cellRows (cell x L) → Σ _ (R k)
  r-at x L km with cell-row (cell x L) km
  ... | (e , y) , h = e , y , few-reach {S = J.JoinT} {e = e} (few-at x L h)

  listed-at : ∀ {l e₀} (x : u l e₀) (L : Listed u l) {k} → Hang l k → Listed R k
  listed-at x L {k} h = filter (λ y → T? (y <ᵖ k)) (proj₁ (few-at x L h))
    , (λ y kk → ∈-filter⁺ (λ y → T? (y <ᵖ k)) (proj₂ (few-at x L h) (proj₁ y) kk) kk)
    , λ m → let (m′ , yk) = ∈-filter⁻ (λ y → T? (y <ᵖ k)) m in yk , any-row m′
    where
      any-row : ∀ {y} → y ∈ before L ++ cellRows (cell x L) → Σ _ (R y)
      any-row m with ∈-++⁻ (before L) m
      ... | inj₂ m′ = r-at x L m′
      ... | inj₁ m′ with rowsOf-out (proj₁ L) (cells L) m′
      ...   | z , zm , km = r-at (proj₂ (proj₂ (proj₂ (proj₂ L) zm))) (sub-listed L (proj₁ (proj₂ (proj₂ L) zm))) km

  -- A reading row's first joined row: at it, or at its first child.
  head-row : ∀ {l e} (x : u l e) (L : Listed u l) → Σ Pos λ k → Hang l k × Σ _ (R k) × (k ≡ l ⊎ up k ≡ l)
  head-row {l} {e = out _} x L = _ , h-val , r-at x L (here refl) , inj₂ (up-⊕ l (ix 0))
  head-row {e = skip}  x L = _ , h-at , r-at x L (here refl) , inj₁ refl
  head-row {e = end}   x L = _ , h-at , r-at x L (here refl) , inj₁ refl
  head-row {e = pin _} x L = ⊥-elim (pinU x)

  end-row : ∀ {c} → u c end → Listed u c → R c end
  end-row x L = J.oend (sc-end x) (done-at (sc-end x)) , few-reach {S = J.JoinT} {e = end} (few-at x L h-at)

  -- A joined end is the reading's.
  end-src : ∀ {c} → R c end → u c end
  end-src (J.oend (S.send x , _) _ , _)                     = x
  end-src (J.lend (S.sval ac , _) _ ((r , _) , _) _ _ d , _) = ⊥-elim (not-done (acc-u ac) (lane-hang r) d)
  end-src (J.lane _ _ _ _ () , _)
  end-src (J.rend () _ _ , _)

  ----------------------------------------------------------------------
  -- A reading row's carrier

  PtO : Pos → AIE X → Pos → Set
  PtO l (r , nothing) l′ = l′ ≡ l ⊕ [ ix 0 ]
  PtO l (r , just x)  l′ = Σ St λ st → Acc l st × Σ (List (IE X)) λ ys → proj₂ st ≡ ys ++ [ x ] × l′ ≡ l ⊕ [ ix 1 ] ⊕ [ ix (length ys) ]

  -- At the row itself unless it is a value, at its silent step for a
  -- value with no emit, on its lane where the emit is sent otherwise.
  Pt : Pos → Pos → Set
  Pt l l′ = (l′ ≡ l × (∀ {a} → u l (out a) → ⊥)) ⊎ Σ (AIE X) λ a → u l (out a) × PtO l a l′

  pt-hang : ∀ {l l′} → Pt l l′ → Hang l l′
  pt-hang (inj₁ (refl , _))                                  = h-at
  pt-hang (inj₂ ((_ , nothing) , _ , refl))                  = h-val
  pt-hang (inj₂ ((_ , just _) , _ , _ , _ , ys , _ , refl)) = h-lane (ix (length ys))

  pt-fun : ∀ {l l₁ l₂} → Pt l l₁ → Pt l l₂ → l₁ ≡ l₂
  pt-fun (inj₁ (refl , _)) (inj₁ (refl , _))     = refl
  pt-fun (inj₁ (_ , no))   (inj₂ (_ , y , _))    = ⊥-elim (no y)
  pt-fun (inj₂ (_ , y , _)) (inj₁ (_ , no))      = ⊥-elim (no y)
  pt-fun {l} (inj₂ (a , y , po)) (inj₂ (a′ , y′ , po′)) with funcU y y′
  ... | refl = pto a po po′
    where
      pto : ∀ a {l₁ l₂} → PtO l a l₁ → PtO l a l₂ → l₁ ≡ l₂
      pto (r , nothing) refl refl = refl
      pto (r , just x) (st , ac , ys , eq , refl) (st′ , ac′ , ys′ , eq′ , refl) =
        cong (λ zs → l ⊕ [ ix 1 ] ⊕ [ ix (length zs) ])
          (∷ʳ-injectiveˡ ys ys′ (trans (sym eq) (trans (cong proj₂ (A.acc-func refl ac ac′)) eq′)))

  -- How a plain row matches a reading row, it matches its carrier.
  Tr : Ev (AIE X) → Ev (IE X) → Set
  Tr e₀ e″ = ∀ {e : Ev X} → Match Every (One annValues) (Reads annValues) e e₀ → Match Every (One valuesOf) (Reads valuesOf) e e″

  private
    car-just : ∀ {r v} {a : X} → Carried (Reads annValues) (out a) (out (r , just v)) → Carried (Reads valuesOf) (out a) (out v)
    car-just (_ , refl , eq) = _ , refl , eq

    car-none : ∀ {r} {a : X} → Carried (Reads annValues) (out a) (out (r , nothing)) → ⊥
    car-none (_ , refl , ())

    eo : ∀ {B : Set} {x : B} → end ≡ out x → ⊥
    eo ()

    so : ∀ {B : Set} {x : B} → skip ≡ out x → ⊥
    so ()

    oe : ∀ {B : Set} {x : B} → out x ≡ end → ⊥
    oe ()

    se : skip {A = AIE X} ≡ end → ⊥
    se ()

  tr-just : ∀ {r v} → Tr (out (r , just v)) (out v)
  tr-just {e = out a} (c , n) = (λ s → car-just (c s)) , n
  tr-just {e = end}   (c , n) = (λ s → ⊥-elim (oe (c s))) , n
  tr-just {e = skip}  (c , n) = (λ ()) , n
  tr-just {e = pin _} (c , n) = (λ ()) , n

  tr-none : ∀ {r} → Tr (out (r , nothing)) skip
  tr-none {e = out a} (c , n) = (λ s → ⊥-elim (car-none (c s))) , λ _ ()
  tr-none {e = end}   (c , n) = (λ s → ⊥-elim (oe (c s))) , λ _ ()
  tr-none {e = skip}  (c , n) = (λ ()) , λ _ ()
  tr-none {e = pin _} (c , n) = (λ ()) , λ _ ()

  tr-skip : Tr skip skip
  tr-skip {e = out a} (c , n) = (λ s → ⊥-elim (so (proj₁ (proj₂ (c s))))) , λ _ ()
  tr-skip {e = end}   (c , n) = (λ s → ⊥-elim (se (c s))) , λ _ ()
  tr-skip {e = skip}  (c , n) = (λ ()) , λ _ ()
  tr-skip {e = pin _} (c , n) = (λ ()) , λ _ ()

  tr-end : Tr end end
  tr-end {e = out a} (c , n) = (λ s → ⊥-elim (eo (proj₁ (proj₂ (c s))))) , n
  tr-end {e = end}   _       = (λ _ → refl) , λ n _ → n tt
  tr-end {e = skip}  (c , n) = (λ ()) , n
  tr-end {e = pin _} (c , n) = (λ ()) , n

  -- A listed reading row's carrier: a row, listed.
  post : ∀ {l e₀} (x : u l e₀) (L : Listed u l) → Σ Pos λ l′ → Pt l l′ × Σ (Ev (IE X)) λ e″ → R l′ e″ × Listed R l′ × Tr e₀ e″
  post {l} {out (r , just v)} x L with EL.fold-listed L x
  ... | st , ac with step-of ac x
  ...   | ms , _ , eq =
    l ⊕ [ ix 1 ] ⊕ [ ix (length ms) ] , inj₂ ((r , just v) , x , st , ac , ms , eq , refl) , out v
    , (J.lane (sc-out x ac) tt (lane-row {l} st (subst (λ z → InE (ofᴱ (l ⊕ [ ix 1 ]) 0 z) _ (out v)) (sym eq) (of-at (l ⊕ [ ix 1 ]) 0 ms v))) (λ ()) tt
      , few-reach {S = J.JoinT} {e = out v} (few-at x L (h-lane (ix (length ms)))))
    , listed-at x L (h-lane (ix (length ms))) , tr-just
  post {l} {out (r , nothing)} x L with EL.fold-listed L x
  ... | st , ac = l ⊕ [ ix 0 ] , inj₂ ((r , nothing) , x , refl) , skip , (J.val (sc-out x ac) , few-reach {S = J.JoinT} {e = skip} (few-at x L h-val))
    , listed-at x L h-val , tr-none
  post {l} {skip} x L = l , inj₁ (refl , λ y → o≢s (funcU y x)) , skip , (J.step (sc-skip x) , few-reach {S = J.JoinT} {e = skip} (few-at x L h-at))
    , listed-at x L h-at , tr-skip
  post {l} {end} x L = l , inj₁ (refl , λ y → o≢e (funcU y x)) , end , end-row x L , listed-at x L h-at , tr-end
  post {e₀ = pin _} x L = ⊥-elim (pinU x)

  ----------------------------------------------------------------------
  -- The reading, read back off the joined rows

  unpU : ∀ {l e} → u l e → Unpinned e
  unpU {e = out _} _ = tt
  unpU {e = skip}  _ = tt
  unpU {e = end}   _ = tt
  unpU {e = pin _} x = pinU x

  fewU : ∀ {l e} → u l e → Few u l
  fewU {l} {e} x = reach-few (λ {k} {e′} → full {q = l} {e = e} (unpU x) {k} {e′}) (rchU x)

  -- Live where a joined row hung under it is: an end before would be a
  -- joined end before.
  liveU : ∀ {l e l′} → u l e → Hang l l′ → Live R l′ → Live u l
  liveU {l} {l′ = l′} x h lv {c} xc cl = few-¬¬listed (fewU xc) λ Lc → lv (end-row xc Lc) (≺-≼-≺ {c} {l} {l′} cl (⊑-≼ (hang-⊑ h)))

  -- Few rows before it: each reading row before has a joined row before.
  fewU′ : ∀ {l e l′} → u l e → Hang l l′ → Few R l′ → Few u l
  fewU′ {l} x h (ks , G) = ks ++ L.map up ks , λ {k₁} y k₁l → ∈-stable λ n → few-¬¬listed (fewU y) λ L₁ → n (cand y L₁ k₁l)
    where
      cand : ∀ {k₁ e₁} → u k₁ e₁ → Listed u k₁ → k₁ ≺ l → k₁ ∈ ks ++ L.map up ks
      cand {k₁} y L₁ k₁l with head-row y L₁
      ... | k , hk , (_ , r) , inj₁ refl = ∈-++⁺ˡ (G r (hang-lt y x k₁l hk h))
      ... | k , hk , (_ , r) , inj₂ eq   = ∈-++⁺ʳ ks (subst (_∈ L.map up ks) eq (∈-map⁺ up (G r (hang-lt y x k₁l hk h))))

  -- Listed where a listed joined row hung under it is.
  listedU : ∀ {l e m} → u l e → Hang l m → Listed R m → Listed u l
  listedU {l} {m = m} x h (ks , G , B) = filter (λ z → T? (z <ᵖ l)) srcs , fwd , bwd
    where
      vw : ∀ {k} (mm : k ∈ ks) → View k (proj₁ (proj₂ (B mm)))
      vw mm = view (proj₁ (proj₂ (proj₂ (B mm))))

      srcs : List Pos
      srcs = mapIn ks (λ mm → vpos (vw mm))

      fwd : ∀ {k₁ e₁} → u k₁ e₁ → k₁ ≺ l → k₁ ∈ filter (λ z → T? (z <ᵖ l)) srcs
      fwd {k₁} y k₁l = ∈-filter⁺ (λ z → T? (z <ᵖ l)) (∈-stable λ n → few-¬¬listed (fewU y) λ L₁ → n (inS L₁)) k₁l
        where
          inS : Listed u k₁ → k₁ ∈ srcs
          inS L₁ with head-row y L₁
          ... | k , hk , (_ , r) , _ =
            let mm = G r (hang-lt y x k₁l hk h) in
            subst (_∈ srcs) (hang-uniq (vrow (vw mm)) y (vhang (vw mm)) hk) (mapIn-in ks (λ mm′ → vpos (vw mm′)) mm)

      bwd : ∀ {z} → z ∈ filter (λ z → T? (z <ᵖ l)) srcs → z ≺ l × Σ _ (u z)
      bwd mz with ∈-filter⁻ (λ z → T? (z <ᵖ l)) mz
      ... | mz′ , zl with mapIn-out ks (λ mm → vpos (vw mm)) mz′
      ...   | k , mm , refl = zl , vev (vw mm) , vrow (vw mm)
