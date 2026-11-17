-- AN OPERATOR'S VALUE ROWS, READ BACK ONE LAYER: a connect's value is its
-- body's, a joiner's a running lane's, a hot's a shown row past the
-- subscription, a map's and a scan's their source's value at the row, a
-- takeWhile's a value it read, an `of`'s one of its list, and a concat of
-- two's one of its two lanes'.
module simultaneous.DenRows where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; sub; _⊕_)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (out; EmissionSet; Den; hot; enter; After; LaneOf; InE; at-out; on-out; shown;
  map-out; _≺_; _≼_; module Op; module Joiner; module Bounded; module Connect; module Scan; module TakeWhile; module Values)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼)
open import denotation.Laws.Cut using (ix-asc)

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

module _ {A : Set} (i : Bool) (keep : A → Bool) (d : Den A) (p : Pos) where
  private module Tk = TakeWhile i keep (enter d p)

  -- A takeWhile's value is its source's.
  take-row : ∀ {k y} → enter (Op.takeWhile i keep d) p k (out y) → Σ Pos λ q → enter d p q (out y)
  take-row (Tk.pass t _ _ , _)   = _ , t
  take-row (Tk.fail t _ _ _ , _) = _ , t

-- An `of`'s value is one of its list.
of-mem : ∀ {A} p i (xs : List A) {k y} → InE (ofᴱ p i xs) k (out y) → y ∈ xs
of-mem p i []       ()
of-mem p i (x ∷ xs) at-out     = here refl
of-mem p i (x ∷ xs) (on-out r) = there (of-mem p (suc i) xs r)

-- An `each`'s value, of its source's value at the lane's one row.
each-one : ∀ {A B} (f : A → List B) (d : Den A) p {k y} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (f x)) d) p k (out y)
         → Σ Pos λ q → Σ A λ x → enter d p q (out x) × y ∈ f x
each-one f d p r with merge-out (λ x → Op.of (f x)) d p r
... | q , x , dq , (l , _) , _ = q , x , dq , of-mem _ 0 (f x) l

-- A value's index holds its row.
nth-row : ∀ {A} {o : EmissionSet A} {i q a} → Values.Nth o i q a → o q (out a)
nth-row (Values.first o _)    = o
nth-row (Values.next _ o _ _) = o

------------------------------------------------------------------------
-- A concat of two

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
