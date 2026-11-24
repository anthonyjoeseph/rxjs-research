{-# OPTIONS --guardedness #-}

-- THE LANES COUNTER IS AT MOST WHAT LIVE LANES HOLD OF ITS INSTANT
-- (`lanes-held`).  Along a run each lane keeps its own count (`OC`), and
-- the scan's lanes counter stays within a sum, over the lanes met, of each
-- lane's share: what it began of the counter's name since that name was
-- last entered.  A `begin` adds to its lane's share, a `stop` or an `over`
-- takes from it, a cut or a new name empties every share, and a lane's
-- `laneDone` drops its share as the scan drops the routes it carried.  A
-- share is never more than its lane's own count, and is held only by a
-- live lane; so where the counter is not empty, some live lane holds a
-- route of its instant.
module simultaneous.LaneEpoch where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injective; ++-conicalʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁻)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Bool using (true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; n≤0⇒n≡0; ∸-monoˡ-≤; ∸-monoʳ-≤; m∸n≤m; +-comm; +-assoc; +-identityʳ;
  +-suc; +-cancelˡ-≡; m+n∸n≡m; 0∸n≡0)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (FlatOp; switchᶠ; mergeᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import denotation.Laws.Count using (em)
open import simultaneous.SObs using (Flat; laneB; outerB; closeB; lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.HeldComb using (past; init)
open import simultaneous.ScanCount using (rowKind; markAct; pstep; past-snoc)
open import simultaneous.LaneCount using (kStart; kDone; kCut; kOther; module Count)
open import simultaneous.FlatLanes using (Tg; brTag; Within; within; cl; react-own; react-other; within-zero; within₀; cut-same; ended-same;
  module Same)
open import simultaneous.Shut using (r₀)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; Out; Input; react; ended)

------------------------------------------------------------------------
-- Arithmetic and lists

cancelʳ : ∀ k a b → a + k ≡ b + k → a ≡ b
cancelʳ k a b eq = +-cancelˡ-≡ k a b (trans (+-comm k a) (trans eq (+-comm b k)))

private
  -- One step of a counter that a stop lowers by at most one.
  stop-le : ∀ a e S → a + e ≡ S + (e ∸ 1) → S ∸ 1 ≤ a
  stop-le a zero    S eq = ≤-trans (m∸n≤m S 1) (≤-reflexive (sym (trans (sym (+-identityʳ a)) (trans eq (+-identityʳ S)))))
  stop-le a (suc e) S eq = ≤-reflexive (cong (_∸ 1) (sym (cancelʳ e (suc a) S (trans (sym (+-suc a e)) eq))))

  -- A begin of the counter's own name adds one.
  begin-eq : ∀ a e S → a + e ≡ S + suc e → suc S ≤ a
  begin-eq a e S eq = ≤-reflexive (sym (cancelʳ e a (suc S) (trans eq (+-suc S e))))

  done-eq : ∀ a e S → a + e ≡ S + 0 → a ≡ S ∸ e
  done-eq a e S eq = trans (sym (m+n∸n≡m a e)) (cong (_∸ e) (trans eq (+-identityʳ S)))

  -- A list ending in a row, split anywhere: the row is in the second part,
  -- unless that part is empty.
  split-snoc : ∀ {A : Set} (a b xs : List A) x → a ++ b ≡ xs ++ [ x ] → b ≡ [] ⊎ Σ (List A) λ b′ → b ≡ b′ ++ [ x ] × xs ≡ a ++ b′
  split-snoc []      b xs        x eq = inj₂ (xs , eq , refl)
  split-snoc (y ∷ a) b []        x eq = inj₁ (++-conicalʳ a b (proj₂ (∷-injective eq)))
  split-snoc (y ∷ a) b (z ∷ xs) x eq with ∷-injective eq
  ... | refl , eq′ with split-snoc a b xs x eq′
  ...   | inj₁ e              = inj₁ e
  ...   | inj₂ (b′ , eb , ex) = inj₂ (b′ , eb , cong (y ∷_) ex)

------------------------------------------------------------------------
-- A share per lane

set : Pos → ℕ → (Pos → ℕ) → Pos → ℕ
set q₀ v e q with q ≟ᵖ q₀
... | yes _ = v
... | no _  = e q

set-self : ∀ q₀ v e → set q₀ v e q₀ ≡ v
set-self q₀ v e with q₀ ≟ᵖ q₀
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

set-other : ∀ {q q₀} v e → ¬ q ≡ q₀ → set q₀ v e q ≡ e q
set-other {q} {q₀} v e ne with q ≟ᵖ q₀
... | yes eq = ⊥-elim (ne eq)
... | no _   = refl

sumK : List Pos → (Pos → ℕ) → ℕ
sumK []      e = 0
sumK (q ∷ K) e = e q + sumK K e

sum-zero : ∀ K → sumK K (λ _ → 0) ≡ 0
sum-zero []      = refl
sum-zero (_ ∷ K) = sum-zero K

sum-out : ∀ {q₀} K v e → ¬ q₀ ∈ K → sumK K (set q₀ v e) ≡ sumK K e
sum-out []      v e _  = refl
sum-out (q ∷ K) v e ni = cong₂ _+_ (set-other v e (λ eq → ni (here (sym eq)))) (sum-out K v e (λ i → ni (there i)))

sum-set : ∀ {q₀} K v e → Unique K → q₀ ∈ K → sumK K (set q₀ v e) + e q₀ ≡ sumK K e + v
sum-set {q₀} (q ∷ K) v e (fr ∷ᵖ u) (here refl)
  rewrite set-self q v e | sum-out K v e (All¬⇒¬Any fr) =
    trans (+-comm (v + sumK K e) (e q)) (trans (cong (e q +_) (+-comm v (sumK K e))) (sym (+-assoc (e q) (sumK K e) v)))
sum-set {q₀} (q ∷ K) v e (fr ∷ᵖ u) (there i)
  rewrite set-other {q} {q₀} v e (lookup fr i) =
    trans (+-assoc (e q) (sumK K (set q₀ v e)) (e q₀)) (trans (cong (e q +_) (sum-set K v e u i)) (sym (+-assoc (e q) (sumK K e) v)))

sum-pos : ∀ K e → ¬ sumK K e ≡ 0 → Σ Pos λ q → q ∈ K × ¬ e q ≡ 0
sum-pos []      e nz = ⊥-elim (nz refl)
sum-pos (q ∷ K) e nz with e q in eq
... | suc _ = q , here refl , λ z → 0≢s (trans (sym z) eq)
  where 0≢s : ∀ {n} → 0 ≡ suc n → ⊥
        0≢s ()
... | zero with sum-pos K e nz
...   | q′ , i , nz′ = q′ , there i , nz′

------------------------------------------------------------------------
-- The scan's lanes counter under one row

within-mono : ∀ {b s n S S′} → Within b s (n , S) → S ≤ S′ → Within b s (n , S′)
within-mono (within sp le nm) l = within sp (≤-trans le l) nm

-- A begin starts its count afresh unless it is of the count's own name.
begin-count : ∀ {A} (c : Routes) n₁ → (proj₁ c ≡ n₁ × count {A} c (instEmit (mark begin) n₁) ≡ (proj₁ c , suc (proj₂ c)))
                                     ⊎ (¬ proj₁ c ≡ n₁ × count {A} c (instEmit (mark begin) n₁) ≡ (n₁ , 1))
begin-count (m , k) n₁ with n₁ ≟ᵖ m
... | yes refl = inj₁ (refl , refl)
... | no ne    = inj₂ ((λ e → ne (sym e)) , refl)

-- Only a switch's `outerOpen` cuts.
cut-mark : ∀ op m → markAct op m ≡ kCut → op ≡ switchᶠ × m ≡ outerOpen
cut-mark switchᶠ    outerOpen  _ = refl , refl
cut-mark (mergeᶠ _) outerOpen  ()
cut-mark exhaustᶠ   outerOpen  ()
cut-mark _          begin      ()
cut-mark _          over       ()
cut-mark _          stop       ()
cut-mark _          outerClose ()
cut-mark _          laneStart  ()
cut-mark _          (laneDone _) ()
cut-mark _          burstEnd   ()
cut-mark _          outerDone  ()
cut-mark _          subscribed ()
cut-mark _          completed  ()

-- A CUT EMPTIES THE LANES COUNTER.
cut-lanes : ∀ {B} op (o : Out B) x → rowKind markAct op x ≡ kCut → Flat.lanes (proj₁ (pstep op o x)) ≡ 0
cut-lanes op (s , os) (k , out (just (inj₁ (b , instEmit (mark m) n)))) eq with cut-mark op m eq
... | refl , refl = n≤0⇒n≡0 (Same.lowL (cut-same (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })))
cut-lanes op o (k , out (just (inj₁ (b , instEmit (value _) _)))) ()
cut-lanes op o (k , out (just (inj₂ _))) ()
cut-lanes op o (k , out nothing) ()
cut-lanes op o (k , end)   ()
cut-lanes op o (k , skip)  ()
cut-lanes op o (k , pin _) ()

-- A LANE'S `laneDone` DROPS THE ROUTES IT TELLS: the counter falls by
-- them, so by any share within them.
done-within : ∀ {B} op (o : Out B) n₁ {n S e kd} → Within laneB (proj₁ o) (n , S) → e ≤ kd
            → Within laneB (proj₁ (react op o (just (inj₁ (laneB , instEmit (mark (laneDone kd)) n₁))))) (n , S ∸ e)
done-within op (s , os) n₁ {n} {S} {e} {kd} (within sp le nm) ea = within sp′ le′ nm′
  where
    s₁ : Flat Pos
    s₁ = record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true }

    sm = ended-same {_} (kd ⊓ Flat.lanes s) n₁ s₁

    low : Flat.lanes (proj₁ (ended {_} (kd ⊓ Flat.lanes s) n₁ s₁)) ≤ Flat.lanes s ∸ kd
    low = Same.lowL sm

    zero-at : Flat.lanes s ≡ 0 → Flat.lanes (proj₁ (ended {_} (kd ⊓ Flat.lanes s) n₁ s₁)) ≡ 0
    zero-at z = n≤0⇒n≡0 (≤-trans low (≤-reflexive (trans (cong (_∸ kd) z) (0∸n≡0 kd))))

    sp′ = λ t → zero-at (sp (trans (sym (Same.sp≡ sm)) t))
    le′ = ≤-trans low (≤-trans (∸-monoˡ-≤ kd le) (∸-monoʳ-≤ S ea))
    nm′ = [ (λ z → inj₁ (zero-at z)) , (λ a → inj₂ (trans (Same.at≡ sm) a)) ]′ nm

------------------------------------------------------------------------
-- The count along a run

module Lanes {B : Set} (op : FlatOp) (Own : Pos → Set) (St Dn : Pos → Pos × Ev (Maybe (Input B)) → Set)
             (act : List (Pos × Ev (Maybe (Input B))) → ℕ) (LE : Pos → Pos × Ev (Maybe (Input B)) → IE B → Set) where

  Row : Set
  Row = Pos × Ev (Maybe (Input B))

  module AC = Count _≟ᵖ_ (rowKind markAct op) Own St Dn act

  Sc : List Row → Flat Pos
  Sc r = proj₁ (past op init r)

  -- LANE `q`'S OWN COUNT along rows met, read forward.
  data OC (q : Pos) : List Row → Routes → Set where
    oc[]   : OC q [] r₀
    oc-in  : ∀ {r c x v} → OC q r c → LE q x v → OC q (r ++ [ x ]) (count c v)
    oc-out : ∀ {r c x} → OC q r c → (∀ {v} → LE q x v → ⊥) → OC q (r ++ [ x ]) c

  -- Every lane has its count, read classically.
  oc-total : ∀ q xs → ¬ ¬ Σ Routes λ c → OC q xs c
  oc-total q xs = go [] xs oc[]
    where
      go : ∀ r ys {c} → OC q r c → ¬ ¬ Σ Routes λ c′ → OC q (r ++ ys) c′
      go r []       oc κ = κ (_ , subst (λ z → OC q z _) (sym (++-identityʳ r)) oc)
      go r (y ∷ ys) oc κ = em {P = Σ (IE B) λ v → LE q y v}
        (λ (v , l) κ′ → go (r ++ [ y ]) ys (oc-in oc l) (ret κ′))
        (λ nl κ′ → go (r ++ [ y ]) ys (oc-out oc (λ l → nl (_ , l))) (ret κ′))
        κ
        where
          ret : ((Σ Routes λ c′ → OC q (r ++ y ∷ ys) c′) → ⊥) → (Σ Routes λ c′ → OC q ((r ++ [ y ]) ++ ys) c′) → ⊥
          ret κ′ (c′ , o) = κ′ (c′ , subst (λ z → OC q z c′) (++-assoc r [ y ] ys) o)

  -- A LANE STAYS LIVE past a row that neither cuts nor ends it.
  live-keep : ∀ {xs x q} → AC.Live [] xs q → (rowKind markAct op x ≡ kCut → ⊥) → (Dn q x → ⊥) → AC.Live [] (xs ++ [ x ]) q
  live-keep {xs} {x} (o , si , nd , nc) nk ndn = o , ++⁺ˡ si , (λ d → [ nd , (λ { (here dn) → ndn dn }) ]′ (++⁻ xs d)) , no-cut
    where
      no-cut : AC.CutIn [] (xs ++ [ x ]) _ → ⊥
      no-cut (a , b , eq , sa , cb) with split-snoc a b xs x (sym eq)
      ... | inj₁ refl = noAny cb
        where noAny : ∀ {P : Row → Set} → Data.List.Relation.Unary.Any.Any P [] → ⊥
              noAny ()
      ... | inj₂ (b′ , refl , ex) = [ (λ c′ → nc (a , b′ , ex , sa , c′)) , (λ { (here k) → nk k }) ]′ (++⁻ b′ cb)

  -- What a share asks of its lane: no more than the lane's count, of the
  -- counter's name, and held only while the lane is live.
  R : Pos → List Row → Pos → Routes → ℕ → Set
  R n xs q c v = v ≤ proj₂ c × (v ≡ 0 ⊎ proj₁ c ≡ n) × (v ≡ 0 ⊎ AC.Live [] xs q)

  zero-R : ∀ {n xs q c} → R n xs q c 0
  zero-R = z≤n , inj₁ refl , inj₁ refl

  record Ep (xs : List Row) : Set where
    constructor ep
    field
      nm  : Pos
      K   : List Pos
      sh  : Pos → ℕ
      uq  : Unique K
      ent : ∀ {q} → q ∈ K → Σ Routes λ c → OC q xs c × R nm xs q c (sh q)
      wn  : Within laneB (Sc xs) (nm , sumK K sh)

  module Run (rx : List Row)
             (no-end : ∀ {c} → (c , end) ∈ rx → ⊥)
             (lane-of : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {k v} → x ≡ (k , out (Tg laneB v)) → ¬ ¬ Σ Pos λ q → LE q x v)
             (le-row : ∀ {q x v} → LE q x v → Σ Pos λ k → x ≡ (k , out (Tg laneB v)))
             (le-one : ∀ {q q′ x v v′} → LE q x v → LE q′ x v′ → q ≡ q′)
             (dn-le : ∀ {q x} → Dn q x → Σ _ λ kd → Σ _ λ n → LE q x (instEmit (mark (laneDone kd)) n))
             (emit-live : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {q n} → LE q x (instEmit (mark begin) n) → AC.Live [] xs q)
             (done-told : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {q kd n c} → LE q x (instEmit (mark (laneDone kd)) n) → OC q xs c
                        → proj₂ c ≤ kd) where

    module _ (xs : List Row) (x : Row) (ys : List Row) (eq : rx ≡ xs ++ x ∷ ys) where
      x-in : x ∈ rx
      x-in = subst (x ∈_) (sym eq) (Data.List.Relation.Unary.Any.Properties.++⁺ʳ xs (here refl))

      ne : ∀ {c} → (c , end) ∈ xs → ⊥
      ne i = no-end (subst (_ ∈_) (sym eq) (++⁺ˡ i))

      Wt : ∀ {c} → Within laneB (proj₁ (pstep op (past op init xs) x)) c → Within laneB (Sc (xs ++ [ x ])) c
      Wt {c} = subst (λ o → Within laneB (proj₁ o) c) (sym (past-snoc op init xs x ne))

      -- A row no lane sent leaves every share, unless it cuts.
      keep-all : Ep xs → (∀ {q v} → LE q x v → ⊥) → (rowKind markAct op x ≡ kCut → ⊥)
               → (∀ {c} → Within laneB (Sc xs) c → Within laneB (Sc (xs ++ [ x ])) c) → Ep (xs ++ [ x ])
      keep-all (ep n K e u ent W) nl nk W′ = ep n K e u ent′ (W′ W)
        where
          ent′ : ∀ {q} → q ∈ K → Σ Routes λ c → OC q (xs ++ [ x ]) c × R n (xs ++ [ x ]) q c (e q)
          ent′ i with ent i
          ... | c , oc , le , nmd , lv = c , oc-out oc nl , le , nmd , [ inj₁ , (λ l → inj₂ (live-keep l nk (λ d → nl (proj₂ (proj₂ (dn-le d)))))) ]′ lv

      -- A cut empties every share.
      reset-all : Ep xs → (∀ {q c} → OC q xs c → Σ Routes λ c′ → OC q (xs ++ [ x ]) c′) → Flat.lanes (Sc (xs ++ [ x ])) ≡ 0
                → Ep (xs ++ [ x ])
      reset-all (ep n K e u ent W) step z =
        ep n K (λ _ → 0) u (λ i → let (c′ , oc′) = step (proj₁ (proj₂ (ent i))) in c′ , oc′ , zero-R) (within-zero z)

      -- The lane that sent a row is in the count.
      ensure : ∀ q₀ → Ep xs → ¬ ¬ Σ (Ep xs) λ E → q₀ ∈ Ep.K E
      ensure q₀ E@(ep n K e u ent W) with any? (q₀ ≟ᵖ_) K
      ... | yes i = λ κ → κ (E , i)
      ... | no ni = λ κ → oc-total q₀ xs λ c₀ → κ (add c₀)
        where
          sum≡ : sumK (q₀ ∷ K) (set q₀ 0 e) ≡ sumK K e
          sum≡ = cong₂ _+_ (set-self q₀ 0 e) (sum-out K 0 e ni)

          add : (Σ Routes λ c → OC q₀ xs c) → Σ (Ep xs) λ E′ → q₀ ∈ Ep.K E′
          add (c₀ , oc₀) = ep n (q₀ ∷ K) (set q₀ 0 e) ((¬Any⇒All¬ K ni) ∷ᵖ u) ent′
                             (subst (λ S → Within laneB (Sc xs) (n , S)) (sym sum≡) W) , here refl
            where
              ent′ : ∀ {q} → q ∈ q₀ ∷ K → Σ Routes λ c → OC q xs c × R n xs q c (set q₀ 0 e q)
              ent′ (here refl) = c₀ , oc₀ , subst (R n xs q₀ c₀) (sym (set-self q₀ 0 e)) zero-R
              ent′ {q} (there i) with ent i
              ... | c , oc , r = c , oc , subst (R n xs q c) (sym (set-other 0 e (λ { refl → ni i }))) r

    ------------------------------------------------------------------------
    -- A lane's row

    module LaneRow (xs : List Row) (k : Pos) (v : IE B) (ys : List Row) (eq : rx ≡ xs ++ (k , out (Tg laneB v)) ∷ ys)
                   (q₀ : Pos) (le₀ : LE q₀ (k , out (Tg laneB v)) v) (E : Ep xs) (i₀ : q₀ ∈ Ep.K E) where
      x : Row
      x = (k , out (Tg laneB v))

      open Ep E public renaming (nm to n; sh to e; uq to u; wn to W)

      S : ℕ
      S = sumK K e

      e₀ : ℕ
      e₀ = e q₀

      -- No other lane sent it.
      other : ∀ {q v′} → ¬ q ≡ q₀ → LE q x v′ → ⊥
      other ne′ l = ne′ (le-one l le₀)

      -- Its emit is the row's.
      emit≡ : ∀ {q v′} → LE q x v′ → v′ ≡ v
      emit≡ l with le-row l
      ... | _ , refl = refl

      W₀ : Within laneB (Sc (xs ++ [ x ])) (count (n , S) v)
      W₀ = Wt xs x ys eq (react-own cl op (past op init xs) v (n , S) W)

      -- The shares past the row: the sending lane's moved by `f`, every
      -- other kept (`keep`) or emptied.
      build : ∀ (n′ : Pos) (e′ : Pos → ℕ) → Within laneB (Sc (xs ++ [ x ])) (n′ , sumK K e′)
            → (∀ {c} → OC q₀ xs c → R n xs q₀ c e₀ → R n′ (xs ++ [ x ]) q₀ (count c v) (e′ q₀))
            → (∀ {q c} → ¬ q ≡ q₀ → R n xs q c (e q) → R n′ (xs ++ [ x ]) q c (e′ q))
            → Ep (xs ++ [ x ])
      build n′ e′ W′ f g = ep n′ K e′ u ent′ W′
        where
          ent′ : ∀ {q} → q ∈ K → Σ Routes λ c → OC q (xs ++ [ x ]) c × R n′ (xs ++ [ x ]) q c (e′ q)
          ent′ {q} i with q ≟ᵖ q₀ | ent i
          ... | yes refl | c , oc , r = count c v , oc-in oc le₀ , f oc r
          ... | no ne′   | c , oc , r = c , oc-out oc (other ne′) , g ne′ r

      -- Another lane's share, past a row that neither cuts nor ends it.
      keep : (rowKind markAct op x ≡ kCut → ⊥) → ∀ {n′} (e′ : Pos → ℕ) → n′ ≡ n → (∀ {q} → ¬ q ≡ q₀ → e′ q ≡ e q)
           → ∀ {q c} → ¬ q ≡ q₀ → R n xs q c (e q) → R n′ (xs ++ [ x ]) q c (e′ q)
      keep nk e′ refl same {q} {c} ne′ (le , nmd , lv) = subst (R n (xs ++ [ x ]) q c) (sym (same ne′))
        (le , nmd , [ inj₁ , (λ l → inj₂ (live-keep l nk (λ d → other ne′ (proj₂ (proj₂ (dn-le d)))))) ]′ lv)

      -- The sending lane's own share, past a row that neither cuts nor ends it.
      live₀ : (rowKind markAct op x ≡ kCut → ⊥) → (∀ {kd n₁} → v ≡ instEmit (mark (laneDone kd)) n₁ → ⊥)
            → AC.Live [] xs q₀ → AC.Live [] (xs ++ [ x ]) q₀
      live₀ nk nd l = live-keep l nk (λ d → nd (sym (emit≡ (proj₂ (proj₂ (dn-le d))))))

    ------------------------------------------------------------------------
    -- Each kind of lane row

    module _ (xs : List Row) (k : Pos) (ys : List Row) (q₀ : Pos) (E : Ep xs) (i₀ : q₀ ∈ Ep.K E) where

      begin-row : ∀ n₁ (eq : rx ≡ xs ++ (k , out (Tg laneB (instEmit (mark begin) n₁))) ∷ ys)
                → LE q₀ (k , out (Tg laneB (instEmit (mark begin) n₁))) (instEmit (mark begin) n₁)
                → Ep (xs ++ [ (k , out (Tg laneB (instEmit (mark begin) n₁))) ])
      begin-row n₁ eq le₀ = body (n₁ ≟ᵖ n)
        where
          open LaneRow xs k (instEmit (mark begin) n₁) ys eq q₀ le₀ E i₀

          nk : rowKind markAct op x ≡ kCut → ⊥
          nk ()

          nd : ∀ {kd n₂} → instEmit (mark begin) n₁ ≡ instEmit (mark (laneDone kd)) n₂ → ⊥
          nd ()

          lv : AC.Live [] (xs ++ [ x ]) q₀
          lv = live₀ nk nd (emit-live xs x ys eq le₀)

          body : _ → Ep (xs ++ [ x ])
          body (yes n₁≡n) = build n e′ W′ f (keep nk e′ refl (λ ne′ → set-other (suc e₀) e ne′))
            where
              e′ : Pos → ℕ
              e′ = set q₀ (suc e₀) e

              W₁ : Within laneB (Sc (xs ++ [ x ])) (n , suc S)
              W₁ with begin-count {B} (n , S) n₁ | W₀
              ... | inj₁ (_ , ceq) | w = subst (Within laneB (Sc (xs ++ [ x ]))) ceq w
              ... | inj₂ (n≢ , _)  | _ = ⊥-elim (n≢ (sym n₁≡n))

              W′ = within-mono W₁ (begin-eq (sumK K e′) e₀ S (sum-set K (suc e₀) e u i₀))

              f : ∀ {c} → OC q₀ xs c → R n xs q₀ c e₀ → R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark begin) n₁)) (e′ q₀)
              f {c} _ (le , nmd , _) = subst (R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark begin) n₁))) (sym (set-self q₀ (suc e₀) e)) r′
                where
                  r′ : R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark begin) n₁)) (suc e₀)
                  r′ with begin-count {B} c n₁
                  ... | inj₁ (pc , ceq) = subst (λ c′ → R n (xs ++ [ x ]) q₀ c′ (suc e₀)) (sym ceq) (s≤s le , inj₂ (trans pc n₁≡n) , inj₂ lv)
                  ... | inj₂ (pc≢ , ceq) = subst (λ c′ → R n (xs ++ [ x ]) q₀ c′ (suc e₀)) (sym ceq)
                        (s≤s (≤-reflexive ([ (λ z → z) , (λ pcn → ⊥-elim (pc≢ (trans pcn (sym n₁≡n)))) ]′ nmd)) , inj₂ n₁≡n , inj₂ lv)
          body (no n₁≢n) = build n₁ e′ W′ f g
            where
              e′ : Pos → ℕ
              e′ = set q₀ 1 (λ _ → 0)

              W₁ : Within laneB (Sc (xs ++ [ x ])) (n₁ , 1)
              W₁ with begin-count {B} (n , S) n₁ | W₀
              ... | inj₁ (n≡ , _) | _ = ⊥-elim (n₁≢n (sym n≡))
              ... | inj₂ (_ , ceq) | w = subst (Within laneB (Sc (xs ++ [ x ]))) ceq w

              sum₁ : sumK K e′ ≡ 1
              sum₁ = trans (sym (+-identityʳ (sumK K e′))) (trans (sum-set K 1 (λ _ → 0) u i₀) (cong (_+ 1) (sum-zero K)))

              W′ = within-mono W₁ (≤-reflexive (sym sum₁))

              f : ∀ {c} → OC q₀ xs c → R n xs q₀ c e₀ → R n₁ (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark begin) n₁)) (e′ q₀)
              f {c} _ _ = subst (R n₁ (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark begin) n₁))) (sym (set-self q₀ 1 (λ _ → 0))) r′
                where
                  r′ : R n₁ (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark begin) n₁)) 1
                  r′ with begin-count {B} c n₁
                  ... | inj₁ (pc , ceq) = subst (λ c′ → R n₁ (xs ++ [ x ]) q₀ c′ 1) (sym ceq) (s≤s z≤n , inj₂ pc , inj₂ lv)
                  ... | inj₂ (_ , ceq)  = subst (λ c′ → R n₁ (xs ++ [ x ]) q₀ c′ 1) (sym ceq) (s≤s z≤n , inj₂ refl , inj₂ lv)

              g : ∀ {q c} → ¬ q ≡ q₀ → R n xs q c (e q) → R n₁ (xs ++ [ x ]) q c (e′ q)
              g {q} {c} ne′ _ = subst (R n₁ (xs ++ [ x ]) q c) (sym (set-other 1 (λ _ → 0) ne′)) zero-R

      stop-row : ∀ n₁ (eq : rx ≡ xs ++ (k , out (Tg laneB (instEmit (mark stop) n₁))) ∷ ys)
               → LE q₀ (k , out (Tg laneB (instEmit (mark stop) n₁))) (instEmit (mark stop) n₁)
               → Ep (xs ++ [ (k , out (Tg laneB (instEmit (mark stop) n₁))) ])
      stop-row n₁ eq le₀ = build n e′ (within-mono W₀ (stop-le (sumK K e′) e₀ S (sum-set K (e₀ ∸ 1) e u i₀))) f
                             (keep nk e′ refl (λ ne′ → set-other (e₀ ∸ 1) e ne′))
        where
          open LaneRow xs k (instEmit (mark stop) n₁) ys eq q₀ le₀ E i₀

          nk : rowKind markAct op x ≡ kCut → ⊥
          nk ()

          nd : ∀ {kd n₂} → instEmit (mark stop) n₁ ≡ instEmit (mark (laneDone kd)) n₂ → ⊥
          nd ()

          e′ : Pos → ℕ
          e′ = set q₀ (e₀ ∸ 1) e

          f : ∀ {c} → OC q₀ xs c → R n xs q₀ c e₀ → R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark stop) n₁)) (e′ q₀)
          f {c} _ (le , nmd , lv′) = subst (R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark stop) n₁))) (sym (set-self q₀ (e₀ ∸ 1) e))
            ( ∸-monoˡ-≤ 1 le
            , [ (λ z → inj₁ (cong (_∸ 1) z)) , inj₂ ]′ nmd
            , [ (λ z → inj₁ (cong (_∸ 1) z)) , (λ l → inj₂ (live₀ nk nd l)) ]′ lv′ )

      over-row : ∀ n₁ (eq : rx ≡ xs ++ (k , out (Tg laneB (instEmit (mark over) n₁))) ∷ ys)
               → LE q₀ (k , out (Tg laneB (instEmit (mark over) n₁))) (instEmit (mark over) n₁)
               → Ep (xs ++ [ (k , out (Tg laneB (instEmit (mark over) n₁))) ])
      over-row n₁ eq le₀ = build n e′ (within-mono W₀ z≤n)
                             (λ {c} _ _ → subst (R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark over) n₁))) (sym (set-self q₀ 0 e)) zero-R)
                             (keep nk e′ refl (λ ne′ → set-other 0 e ne′))
        where
          open LaneRow xs k (instEmit (mark over) n₁) ys eq q₀ le₀ E i₀

          nk : rowKind markAct op x ≡ kCut → ⊥
          nk ()

          e′ : Pos → ℕ
          e′ = set q₀ 0 e

      done-row : ∀ kd n₁ (eq : rx ≡ xs ++ (k , out (Tg laneB (instEmit (mark (laneDone kd)) n₁))) ∷ ys)
               → LE q₀ (k , out (Tg laneB (instEmit (mark (laneDone kd)) n₁))) (instEmit (mark (laneDone kd)) n₁)
               → Ep (xs ++ [ (k , out (Tg laneB (instEmit (mark (laneDone kd)) n₁))) ])
      done-row kd n₁ eq le₀ = build n e′ W′
                             (λ {c} _ _ → subst (R n (xs ++ [ x ]) q₀ (count {B} c (instEmit (mark (laneDone kd)) n₁))) (sym (set-self q₀ 0 e)) zero-R)
                             (keep nk e′ refl (λ ne′ → set-other 0 e ne′))
        where
          open LaneRow xs k (instEmit (mark (laneDone kd)) n₁) ys eq q₀ le₀ E i₀

          nk : rowKind markAct op x ≡ kCut → ⊥
          nk ()

          e′ : Pos → ℕ
          e′ = set q₀ 0 e

          ea : e₀ ≤ kd
          ea with ent i₀
          ... | c₀ , oc₀ , le , _ = ≤-trans le (done-told xs x ys eq le₀ oc₀)

          W′ : Within laneB (Sc (xs ++ [ x ])) (n , sumK K e′)
          W′ = subst (λ z → Within laneB (Sc (xs ++ [ x ])) (n , z)) (sym (done-eq (sumK K e′) e₀ S (sum-set K 0 e u i₀)))
                 (Wt xs x ys eq (done-within op (past op init xs) n₁ W ea))

      -- A row its lane's count and the scan's counter both pass over.
      idle-row : ∀ v (eq : rx ≡ xs ++ (k , out (Tg laneB v)) ∷ ys) → LE q₀ (k , out (Tg laneB v)) v
               → (∀ c → count c v ≡ c) → (∀ {kd n₁} → v ≡ instEmit (mark (laneDone kd)) n₁ → ⊥)
               → (rowKind markAct op (k , out (Tg laneB v)) ≡ kCut → ⊥)
               → Ep (xs ++ [ (k , out (Tg laneB v)) ])
      idle-row v eq le₀ cid nd nk = build n e (subst (Within laneB (Sc (xs ++ [ x ]))) (cid (n , S)) W₀) f (keep nk e refl (λ _ → refl))
        where
          open LaneRow xs k v ys eq q₀ le₀ E i₀

          f : ∀ {c} → OC q₀ xs c → R n xs q₀ c e₀ → R n (xs ++ [ x ]) q₀ (count c v) e₀
          f {c} _ (le , nmd , lv′) = subst (λ c′ → R n (xs ++ [ x ]) q₀ c′ e₀) (sym (cid c))
            (le , nmd , [ inj₁ , (λ l → inj₂ (live₀ nk nd l)) ]′ lv′)

      -- A row that cuts empties every share.
      cut-row : ∀ v (eq : rx ≡ xs ++ (k , out (Tg laneB v)) ∷ ys) → LE q₀ (k , out (Tg laneB v)) v
              → rowKind markAct op (k , out (Tg laneB v)) ≡ kCut
              → Ep (xs ++ [ (k , out (Tg laneB v)) ])
      cut-row v eq le₀ kc = reset-all xs x ys eq E step′ lanes0
        where
          open LaneRow xs k v ys eq q₀ le₀ E i₀

          step′ : ∀ {q c} → OC q xs c → Σ Routes λ c′ → OC q (xs ++ [ x ]) c′
          step′ {q} oc with q ≟ᵖ q₀
          ... | yes refl = _ , oc-in oc le₀
          ... | no ne′   = _ , oc-out oc (other ne′)

          lanes0 : Flat.lanes (Sc (xs ++ [ x ])) ≡ 0
          lanes0 = trans (cong (λ o → Flat.lanes (proj₁ o)) (past-snoc op init xs x (ne xs x ys eq))) (cut-lanes op (past op init xs) x kc)

      -- A lane row, by its emit.
      lane-row : ∀ v (eq : rx ≡ xs ++ (k , out (Tg laneB v)) ∷ ys) → LE q₀ (k , out (Tg laneB v)) v
               → Ep (xs ++ [ (k , out (Tg laneB v)) ])
      lane-row (instEmit (value w) n₁)        eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())
      lane-row (instEmit (mark begin) n₁)     eq le₀ = begin-row n₁ eq le₀
      lane-row (instEmit (mark stop) n₁)      eq le₀ = stop-row n₁ eq le₀
      lane-row (instEmit (mark over) n₁)      eq le₀ = over-row n₁ eq le₀
      lane-row (instEmit (mark (laneDone kd)) n₁) eq le₀ = done-row kd n₁ eq le₀
      lane-row (instEmit (mark outerOpen) n₁) eq le₀ with markAct op outerOpen in kx
      ... | kCut   = cut-row _ eq le₀ kx
      ... | kStart = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ c → kS (trans (sym kx) c))
        where kS : kStart ≡ kCut → ⊥
              kS ()
      ... | kDone  = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ c → kD (trans (sym kx) c))
        where kD : kDone ≡ kCut → ⊥
              kD ()
      ... | kOther = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ c → kO (trans (sym kx) c))
        where kO : kOther ≡ kCut → ⊥
              kO ()
      lane-row (instEmit (mark outerClose) n₁) eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())
      lane-row (instEmit (mark laneStart) n₁)  eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())
      lane-row (instEmit (mark burstEnd) n₁)   eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())
      lane-row (instEmit (mark outerDone) n₁)  eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())
      lane-row (instEmit (mark subscribed) n₁) eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())
      lane-row (instEmit (mark completed) n₁)  eq le₀ = idle-row _ eq le₀ (λ _ → refl) (λ ()) (λ ())

    ------------------------------------------------------------------------
    -- Any other row

    -- A row of another branch, or a tracker's.
    branch-row : ∀ xs k x′ ys (eq : rx ≡ xs ++ (k , out x′) ∷ ys) → brTag {B} laneB (out x′) ≡ nothing → (∀ {v} → x′ ≡ Tg laneB v → ⊥)
               → Ep xs → Ep (xs ++ [ (k , out x′) ])
    branch-row xs k x′ ys eq nt nv E with rowKind markAct op (k , out x′) in kx
    ... | kCut   = reset-all xs (k , out x′) ys eq E (λ oc → _ , oc-out oc nl)
                     (trans (cong (λ o → Flat.lanes (proj₁ o)) (past-snoc op init xs (k , out x′) (ne xs (k , out x′) ys eq))) (cut-lanes op (past op init xs) (k , out x′) kx))
      where
        nl : ∀ {q v} → LE q (k , out x′) v → ⊥
        nl l with le-row l
        ... | _ , refl = nv refl
    ... | kStart = keep-all xs (k , out x′) ys eq E nl (λ c → kS (trans (sym kx) c)) (λ w → Wt xs (k , out x′) ys eq (react-other laneB op (past op init xs) x′ _ nt w))
      where
        kS : kStart ≡ kCut → ⊥
        kS ()
        nl : ∀ {q v} → LE q (k , out x′) v → ⊥
        nl l with le-row l
        ... | _ , refl = nv refl
    ... | kDone  = keep-all xs (k , out x′) ys eq E nl (λ c → kD (trans (sym kx) c)) (λ w → Wt xs (k , out x′) ys eq (react-other laneB op (past op init xs) x′ _ nt w))
      where
        kD : kDone ≡ kCut → ⊥
        kD ()
        nl : ∀ {q v} → LE q (k , out x′) v → ⊥
        nl l with le-row l
        ... | _ , refl = nv refl
    ... | kOther = keep-all xs (k , out x′) ys eq E nl (λ c → kO (trans (sym kx) c)) (λ w → Wt xs (k , out x′) ys eq (react-other laneB op (past op init xs) x′ _ nt w))
      where
        kO : kOther ≡ kCut → ⊥
        kO ()
        nl : ∀ {q v} → LE q (k , out x′) v → ⊥
        nl l with le-row l
        ... | _ , refl = nv refl

    step : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → Ep xs → ¬ ¬ Ep (xs ++ [ x ])
    step xs (k , end) ys eq E _ = no-end (x-in xs (k , end) ys eq)
    step xs (k , skip) ys eq E κ = κ (keep-all xs _ ys eq E (λ l → noOut (le-row l)) (λ ()) (Wt xs _ ys eq))
      where
        noOut : ∀ {v} → Σ Pos (λ k′ → (k , skip) ≡ (k′ , out (Tg laneB v))) → ⊥
        noOut (_ , ())
    step xs (k , pin r) ys eq E κ = κ (keep-all xs _ ys eq E (λ l → noOut (le-row l)) (λ ()) (Wt xs _ ys eq))
      where
        noOut : ∀ {v} → Σ Pos (λ k′ → (k , pin r) ≡ (k′ , out (Tg laneB v))) → ⊥
        noOut (_ , ())
    step xs (k , out (just (inj₁ (laneB , v)))) ys eq E κ =
      lane-of xs _ ys eq refl λ (q₀ , le₀) → ensure xs _ ys eq q₀ E λ (E′ , i₀) → κ (lane-row xs k ys q₀ E′ i₀ v eq le₀)
    step xs (k , out (just (inj₁ (outerB , w)))) ys eq E κ = κ (branch-row xs k _ ys eq refl (λ ()) E)
    step xs (k , out (just (inj₁ (closeB , w)))) ys eq E κ = κ (branch-row xs k _ ys eq refl (λ ()) E)
    step xs (k , out (just (inj₂ t))) ys eq E κ = κ (branch-row xs k _ ys eq refl (λ ()) E)
    step xs (k , out nothing) ys eq E κ = κ (branch-row xs k _ ys eq refl (λ ()) E)

    go : ∀ xs ys → rx ≡ xs ++ ys → Ep xs → ¬ ¬ Ep rx
    go xs []       eq E κ = κ (subst Ep (sym (trans eq (++-identityʳ xs))) E)
    go xs (y ∷ ys) eq E κ = step xs y ys eq E λ E′ → go (xs ++ [ y ]) ys (trans eq (sym (++-assoc xs [ y ] ys))) E′ κ

    -- WHERE THE COUNTER IS NOT EMPTY, A LIVE LANE HOLDS A ROUTE OF ITS INSTANT.
    lanes-held : ¬ Flat.lanes (Sc rx) ≡ 0
               → ¬ ¬ Σ Pos λ q → AC.Live [] rx q × Σ Routes λ c → OC q rx c × proj₁ c ≡ Flat.at (Sc rx) × Σ ℕ λ j → proj₂ c ≡ suc j
    lanes-held nz κ = go [] rx refl (ep (proj₁ r₀) [] (λ _ → 0) []ᵖ (λ ()) (within₀ {B} laneB _)) λ E → κ (pick E)
      where
        suc-of : ∀ {a b} → a ≤ b → ¬ a ≡ 0 → Σ ℕ λ j → b ≡ suc j
        suc-of {b = suc j} _ _ = j , refl
        suc-of {a = zero}  _ z = ⊥-elim (z refl)
        suc-of {a = suc _} {b = zero} () _

        pick : Ep rx → Σ Pos λ q → AC.Live [] rx q × Σ Routes λ c → OC q rx c × proj₁ c ≡ Flat.at (Sc rx) × Σ ℕ λ j → proj₂ c ≡ suc j
        pick (ep n K e u ent (within sp le nmd)) with nmd
        ... | inj₁ z = ⊥-elim (nz z)
        ... | inj₂ at≡ with sum-pos K e (λ s0 → nz (n≤0⇒n≡0 (subst (Flat.lanes (Sc rx) ≤_) s0 le)))
        ...   | q , i , nz′ with ent i
        ...     | c , oc , lq , nmq , lvq = q , [ (λ z → ⊥-elim (nz′ z)) , (λ l → l) ]′ lvq , c , oc
                                          , [ (λ z → ⊥-elim (nz′ z)) , (λ a → trans a (sym at≡)) ]′ nmq , suc-of lq nz′
