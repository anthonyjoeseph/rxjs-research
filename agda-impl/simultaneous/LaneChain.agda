-- A QUEUED LANE'S CHAIN OF ENDS HAS A BASE.  A bounded merge subscribes
-- a queued lane at an earlier lane's end.  A lane ending inside its own
-- subscription was itself queued: one subscribed at its value's `ix 1`
-- and ending there would hold the later value queued at that end under
-- its own value (`flat`).  Down the lane index, the chain reaches a lane
-- whose end lies outside its subscription.
module simultaneous.LaneChain where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Nat using (ℕ; _<_; <-cmp)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; _⊕_; _≟ᵖ_; inside)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; After; enter; out; end; _≺_; module Bounded)
open import denotation.Laws.Worlds using (InvD; InvAt; Ok; W⁼; here; nest⁼; plain-ix; inside-⊑; conv; ⊕-identityʳ; ⊑-refl; ⊑-trans;
  ⊑-snoc⁺; _⊑_; nest; inW; ⊕-injˡ; world-after; nest-in; ⊑-inside; step)
open import denotation.Laws.Modulus using (≺→≼; ≺-irrefl; ≺-ext; ≺-trans; ≼-or-≻; ≼-antisym)
open import denotation.Laws.JoinInv using (end≢out)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI; end-uniq)
open BoundedI using (seat′)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.Routed using (Sync)
open import simultaneous.RealView using (module View; lane-at; lane-at₂; lane-fwd)

module Chains {A B H} (d : Den A) (f : A → Den B) (Id : InvD H d) (If : ∀ a → InvD H (f a)) (p : Pos) (ok : Ok H p) where
  O : EmissionSet A
  O = enter d p

  open View f O using (Lane; Runs; CutAt)

  -- Where a lane subscribes, read off one of its rows.
  subOf : ∀ op {q a k e} → O q (out a) → Lane op q a k e → Pos
  subOf op x l = proj₁ (lane-at op d f Id If p ok x l)

  -- A lane subscribed down a chain of ends from `c`: at `c`'s `ix 1`, or
  -- at the end of a lane so subscribed that ended inside its subscription.
  data Chain (op : FlatOp) (c : Pos) : Pos → Set where
    from : Chain op c (c ⊕ [ ix 1 ])
    link : ∀ {q a y e c′} (x : O q (out a)) (l : Lane op q a y e) → Lane op q a c′ end
         → Sync (subOf op x l) c′ → Chain op c (subOf op x l) → Chain op c (c′ ⊕ [ ix 1 ])

  -- A chain lies under its start.
  chain-⊑ : ∀ {op c s} → Chain op c s → c ⊑ s
  chain-⊑ {c = c} from = ⊑-snoc⁺ c
  chain-⊑ (link {c′ = c′} _ _ _ (ins , _) ch) = ⊑-trans (⊑-trans (chain-⊑ ch) (inside-⊑ _ _ ins)) (⊑-snoc⁺ c′)

  -- A chain stays in its start's instant.
  chain-inst : ∀ {op c s} → Chain op c s → instantOf s ≡ instantOf c
  chain-inst {c = c} from = inst-⊕ c [ ix 1 ]
  chain-inst (link {c′ = c′} _ _ _ (_ , rt) ch) = trans (inst-⊕ c′ [ ix 1 ]) (trans (cong instantOf rt) (chain-inst ch))

  -- A lane's subscription is admissible, and every row of the lane is
  -- its value's row there.
  sub-ok : ∀ op {q a k e} (x : O q (out a)) (l : Lane op q a k e) → Ok H (subOf op x l)
  sub-ok op x l = proj₁ (proj₂ (lane-at op d f Id If p ok x l))

  sub-inv : ∀ op {q a k e} (x : O q (out a)) (l : Lane op q a k e) → InvAt H (subOf op x l) (enter (f a) (subOf op x l))
  sub-inv op {a = a} x l = If a (subOf op x l) (sub-ok op x l)

  sub-row : ∀ op {q a k e k′ e′} (x : O q (out a)) (l : Lane op q a k e) → Lane op q a k′ e′ → enter (f a) (subOf op x l) k′ e′
  sub-row op x l l′ = lane-fwd op d f Id If p ok x l l′

  -- A lane not at its value's `ix 1` is a bounded merge's.
  bounded : ∀ op {q a k e} (x : O q (out a)) (l : Lane op q a k e) → ¬ subOf op x l ≡ q ⊕ [ ix 1 ] → Σ ℕ λ n → op ≡ mergeᶠ (just n)
  bounded (mergeᶠ nothing)  x l nq = ⊥-elim (nq refl)
  bounded switchᶠ           x l nq = ⊥-elim (nq refl)
  bounded exhaustᶠ          x l nq = ⊥-elim (nq refl)
  bounded (mergeᶠ (just n)) x l nq = n , refl

  -- A bounded merge runs every lane it has and cuts none.
  runs-of : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {q a k e} → Lane op q a k e → Runs op q
  runs-of _ refl (i , _ , (ni , _) , _) = i , _ , ni

  uncut-of : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {q y} → ¬ CutAt op q y
  uncut-of _ refl ()

  -- A LANE'S SUBSCRIPTION SITS IN THE WORLD OF A VALUE'S SECOND CHILD:
  -- its own value's, or, queued, the value down its chain of ends.
  seated : ∀ op {q a k e} (x : O q (out a)) (l : Lane op q a k e) → Σ Pos λ r → Σ A λ b → O r (out b) × W⁼ H (r ⊕ [ ix 1 ]) (subOf op x l)
  seated (mergeᶠ nothing)  x l = _ , _ , x , here
  seated switchᶠ           x l = _ , _ , x , here
  seated exhaustᶠ          x l = _ , _ , x , here
  seated (mergeᶠ (just n)) x (i , s , sb , r) = seat-at (BoundedI.seat* ok n f If (Id p ok) sb)
    where
      seat-at : ∀ {i} → BoundedI.Seat ok n f If (Id p ok) i s → Σ Pos λ r → Σ A λ b → O r (out b) × W⁼ H (r ⊕ [ ix 1 ]) s
      seat-at (seat′ _ _ _ nr rw) = _ , _ , Nths.nth-val O nr , rw

  -- SO NO VALUE LIES UNDER A LANE'S WORLD: a value there would sit
  -- under the world of another value's second child.
  past-lane : ∀ op {q a k e q′ a′ w} (x : O q (out a)) (l : Lane op q a k e) → W⁼ H (subOf op x l) w → O q′ (out a′) → w ⊑ q′ → ⊥
  past-lane op x l ww x′ wq =
    let (_ , _ , xr , rw) = seated op x l in InvAt.under (Id p ok) xr x′ plain-ix (nest⁼ rw ww) wq

  -- NO HOT ROW LIES UNDER A LANE'S SUBSCRIPTION: it sits in the world of
  -- a value's second child, which holds none.
  sub-cold : ∀ op {q a k e} (x : O q (out a)) (l : Lane op q a k e) → ∀ {h} → H h → subOf op x l ⊑ h → ⊥
  sub-cold op x l hh le =
    let (_ , _ , xr , rw) = seated op x l in proj₂ ok hh (nest-in (step (inW (InvAt.world (Id p ok) xr)) plain-ix) rw) (⊑-inside le)

  -- One value's lanes share one subscription.
  sub-one : ∀ op {q a k e k′ e′} (x : O q (out a)) (l : Lane op q a k e) (l′ : Lane op q a k′ e′) → subOf op x l ≡ subOf op x l′
  sub-one (mergeᶠ nothing)  x l l′ = refl
  sub-one switchᶠ           x l l′ = refl
  sub-one exhaustᶠ          x l l′ = refl
  sub-one (mergeᶠ (just n)) x (_ , _ , sb , _) (_ , _ , sb′ , _) = BoundedI.sub-same ok n f If (Id p ok) sb sb′

  -- A lane ends once.
  end-one : ∀ op {q a c c′} → O q (out a) → Lane op q a c end → Lane op q a c′ end → c ≡ c′
  end-one op x l l′ = let (s , oks , r , r′) = lane-at₂ op d f Id If p ok x l l′ in end-uniq (If _ s oks) r r′

  -- A LANE WITH A ROW UNDER AN ENDED LANE'S WORLD IS THAT LANE'S VALUE,
  -- OR SUBSCRIBED UNDER ITS END: a lane apart lies in another value's
  -- second child, and one the ended lane is queued under leads none of
  -- that world.
  module Under (n : ℕ) where
    open Bounded n f O using (Sub; room; freed; queued)
    open BoundedI ok n f If (Id p ok) using (Lr; lr-row; lr-hand; lr-w; LI; sub-fun; rel; apart; queued-in; apart-lead; apart-ww; lane-end; nest-back;
      x-lead; end-w; row-w; sub-same)

    -- A lane subscribed past its value's second child was queued at an
    -- end after the value.
    q-before : ∀ {i q s a c} → Sub i q s a → s ≡ c ⊕ [ ix 1 ] → ¬ s ≡ q ⊕ [ ix 1 ] → q ≺ c
    q-before (_ , room _)    _ nq = ⊥-elim (nq refl)
    q-before (_ , freed _ _) _ nq = ⊥-elim (nq refl)
    q-before {q = q} {c = c} (_ , queued {c′} _ qc _ _ _) e _ = subst (q ≺_) (⊕-injˡ c′ c e) qc

    -- A lane subscribed in a lane's world is that lane, or subscribed
    -- under an end of it.
    sub-in : ∀ {i₀ q₀ s₀ a₀ i q s a} → Sub i₀ q₀ s₀ a₀ → Sub i q s a → W⁼ H s₀ s
           → (q ≡ q₀ × a ≡ a₀) ⊎ Σ Pos λ c → After (f a₀) s₀ c end × W⁼ H (c ⊕ [ ix 1 ]) s
    sub-in {i₀} {i = i} sb₀ sb v with <-cmp i₀ i
    ... | tri≈ _ refl _ = let (eq , ea , _) = sub-fun sb sb₀ in inj₁ (eq , ea)
    ... | tri< lt _ _ with rel lt sb₀ sb
    ...   | apart xr xr′ nr rw rw′ = ⊥-elim (apart-ww xr xr′ nr (nest⁼ rw v) rw′)
    ...   | queued-in ac _ v′ = inj₂ (_ , ac , v′)
    sub-in {i₀} {i = i} sb₀ sb v | tri> _ _ gt with rel gt sb sb₀
    ... | apart xr xr′ nr rw rw′ = ⊥-elim (apart-ww xr xr′ nr rw (nest⁼ rw′ v))
    ... | queued-in ac Q v′ = ⊥-elim (nest-back sb ac (nest⁼ (nest⁼ v′ v) (inW (lr-w sb hd))) hd (⊑-refl _))
      where
        hd = lr-hand ac Q refl

    ly : ∀ {i q s a y e} → Sub i q s a → After (f a) s y e → (e ≡ end → ⊥) → Lr a s y
    ly sb r ne = lr-row r (λ re _ → ne (InvAt.func (LI sb) (proj₁ r) (proj₁ re)))

    go : ∀ {i₀ q₀ s₀ a₀ c₀ i q s a y e w} → Sub i₀ q₀ s₀ a₀ → After (f a₀) s₀ c₀ end → Sub i q s a → After (f a) s y e
       → (e ≡ end → ⊥) → W⁼ H s₀ w → w ⊑ y → (q ≡ q₀ × a ≡ a₀) ⊎ W⁼ H (c₀ ⊕ [ ix 1 ]) s
    go {i₀} {i = i} sb₀ ac₀ sb r ne ww le with <-cmp i₀ i
    ... | tri≈ _ refl _ = let (eq , ea , _) = sub-fun sb sb₀ in inj₁ (eq , ea)
    ... | tri< lt _ _ with rel lt sb₀ sb
    ...   | apart xr xr′ nr rw rw′ = ⊥-elim (apart-lead xr xr′ nr (nest⁼ rw ww) (nest rw′ (lr-w sb (ly sb r ne))) le)
    ...   | queued-in ac _ v with lane-end sb₀ ac ac₀
    ...     | refl = inj₂ v
    go {i₀} {i = i} sb₀ ac₀ sb r ne ww le | tri> _ _ gt with rel gt sb sb₀
    ... | apart xr xr′ nr rw rw′ = ⊥-elim (apart-lead xr′ xr (λ eq → nr (sym eq)) (nest⁼ rw′ ww) (nest rw (lr-w sb (ly sb r ne))) le)
    ... | queued-in ac _ v = ⊥-elim (nest-back sb ac (nest⁼ v ww) (ly sb r ne) le)

    -- A LANE SUBSCRIBED UNDER A LANE'S END LIES PAST THAT LANE'S ROWS:
    -- the end follows them, and the second lane is queued after the
    -- first, which leads none of its rows.
    -- The first leads none of the second's rows.
    past-lead : ∀ {iT qT sT aT yT bT c i q s a y e} → Sub iT qT sT aT → After (f aT) sT yT (out bT) → After (f aT) sT c end
              → Sub i q s a → After (f a) s y e → (e ≡ end → ⊥) → W⁼ H (c ⊕ [ ix 1 ]) s → yT ⊑ y → ⊥
    past-lead {iT} {i = i} {y = y} sbT rT acT sb r ne v le with <-cmp iT i
    ... | tri≈ _ refl _ with sub-fun sb sbT
    ...   | refl , refl , refl = nest-back sbT acT (nest⁼ v (inW (row-w sbT r))) (ly sbT r ne) (⊑-refl y)
    past-lead sbT rT acT sb r ne v le | tri< lt _ _ = x-lead sbT sb (rel lt sbT sb) (ly sbT rT (λ ())) (ly sb r ne) le
    past-lead {y = y} sbT rT acT sb r ne v le | tri> _ _ gt with rel gt sb sbT
    ... | apart xr xr′ nr rw rw′ = apart-ww xr xr′ nr rw (nest⁼ rw′ (nest⁼ (inW (end-w sbT acT)) v))
    ... | queued-in ac _ v′ = nest-back sb ac (nest⁼ (nest⁼ v′ (nest⁼ (inW (end-w sbT acT)) v)) (inW (row-w sb r))) (ly sb r ne) (⊑-refl y)

    -- A LANE SUBSCRIBED UNDER A LANE'S END LIES PAST THAT LANE'S ROWS:
    -- the end follows them, and the second lane is queued after the
    -- first, which leads none of its rows.
    past-end : ∀ {iT qT sT aT yT bT c i q s a y e} → Sub iT qT sT aT → After (f aT) sT yT (out bT) → After (f aT) sT c end
             → Sub i q s a → After (f a) s y e → (e ≡ end → ⊥) → W⁼ H (c ⊕ [ ix 1 ]) s → yT ≺ y × (yT ⊑ y → ⊥)
    past-end {yT = yT} {c = c} {y = y} sbT rT acT sb r ne v = before , past-lead sbT rT acT sb r ne v
      where
        cy : c ≺ y
        cy with nest⁼ v (inW (row-w sb r))
        ... | here   = ≺-ext c []
        ... | inW w′ = ≺-trans {c} {c ⊕ [ ix 1 ]} {y} (≺-ext c []) (world-after w′ (InvAt.real (LI sb) (proj₁ r)))

        before : yT ≺ y
        before with ≼-or-≻ yT c
        ... | inj₂ cy′ with InvAt.quiet (LI sbT) (proj₁ acT) (proj₁ rT) cy′
        ...   | _ , () , _
        before | inj₁ le with ≼-or-≻ c yT
        ... | inj₂ lt = ≺-trans {yT} {c} {y} lt cy
        ... | inj₁ le′ = ⊥-elim (end≢out (InvAt.func (LI sbT) (proj₁ acT) (subst (λ t → enter (f _) _ t (out _)) (≼-antisym {yT} {c} le le′) (proj₁ rT))))

  past-end : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {qT aT yT bT c q a y e} (xT : O qT (out aT)) → Lane op qT aT yT (out bT) → Lane op qT aT c end
           → (x : O q (out a)) (l : Lane op q a y e) → (e ≡ end → ⊥) → W⁼ H (c ⊕ [ ix 1 ]) (subOf op x l) → yT ≺ y × (yT ⊑ y → ⊥)
  past-end _ {n} refl {aT = aT} {c = c} xT (_ , _ , sbT , rT) (_ , _ , sbT′ , acT) x (_ , _ , sb , r) =
    Under.past-end n sbT rT (subst (λ t → After (f aT) t c end) (BoundedI.sub-same ok n f If (Id p ok) sbT′ sbT) acT) sb r

  under-ended : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {q₀ a₀ c₀ q a y e w} (x₀ : O q₀ (out a₀)) (l₀ : Lane op q₀ a₀ c₀ end)
                (x : O q (out a)) (l : Lane op q a y e) → (e ≡ end → ⊥) → W⁼ H (subOf op x₀ l₀) w → w ⊑ y
              → (q ≡ q₀ × a ≡ a₀) ⊎ W⁼ H (c₀ ⊕ [ ix 1 ]) (subOf op x l)
  under-ended _ {n} refl x₀ (_ , _ , sb₀ , ac₀) x (_ , _ , sb , r) = Under.go n sb₀ ac₀ sb r

  -- A lane subscribed past its value's second child was queued at an
  -- end after the value.
  queued-at : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {q a k e c} (x : O q (out a)) (l : Lane op q a k e)
            → subOf op x l ≡ c ⊕ [ ix 1 ] → ¬ subOf op x l ≡ q ⊕ [ ix 1 ] → q ≺ c
  queued-at _ {n} refl x (_ , _ , sb , _) = Under.q-before n sb

  -- A LANE SUBSCRIBED IN A LANE'S WORLD IS THAT LANE'S VALUE, OR
  -- SUBSCRIBED UNDER THAT LANE'S END.
  sub-in : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {q₀ a₀ k₀ e₀ q a k e} (x₀ : O q₀ (out a₀)) (l₀ : Lane op q₀ a₀ k₀ e₀)
           (x : O q (out a)) (l : Lane op q a k e) → W⁼ H (subOf op x₀ l₀) (subOf op x l)
         → (q ≡ q₀ × a ≡ a₀) ⊎ Σ Pos λ c → Lane op q₀ a₀ c end × W⁼ H (c ⊕ [ ix 1 ]) (subOf op x l)
  sub-in _ {n} refl x₀ (_ , _ , sb₀ , _) x (_ , _ , sb , _) v with Under.sub-in n sb₀ sb v
  ... | inj₁ e = inj₁ e
  ... | inj₂ (c , ac , w) = inj₂ (c , (_ , _ , sb₀ , ac) , w)

  -- A lane subscribed at `t`.
  Sat : FlatOp → Pos → Set
  Sat op t = Σ Pos λ q → Σ A λ a → Σ Pos λ k → Σ (Ev B) λ e → Σ (O q (out a)) λ x → Σ (Lane op q a k e) λ l → subOf op x l ≡ t

  -- A value's lane ending inside its subscription.
  Linked : FlatOp → Pos → A → Set
  Linked op q a = Σ Pos λ c′ → Σ (O q (out a)) λ x → Σ (Lane op q a c′ end) λ le → Sync (subOf op x le) c′

  -- EVERY LANE SUBSCRIBED UNDER A CHAIN'S START IS A LINK, ENDING IN ITS
  -- SUBSCRIPTION WITH A LANE SUBSCRIBED AT ITS END, OR LIES UNDER THE
  -- CHAIN'S TOP.
  along : ∀ op {n} → op ≡ mergeᶠ (just n) → ∀ {c s} → Chain op c s → Sat op s → ∀ {q a k e} (x : O q (out a)) (l : Lane op q a k e)
        → W⁼ H (c ⊕ [ ix 1 ]) (subOf op x l)
        → ((∀ {c′} → Lane op q a c′ end → Sat op (c′ ⊕ [ ix 1 ])) × Linked op q a) ⊎ W⁼ H s (subOf op x l)
  along op bd from _ x l v = inj₂ v
  along op bd (link {c′ = c′} x′ l′ le sy ch) top x l v with along op bd ch (_ , _ , _ , _ , x′ , l′ , refl) x l v
  ... | inj₁ k = inj₁ k
  ... | inj₂ v′ with sub-in op bd x′ l′ x l v′
  ...   | inj₁ (refl , refl) = inj₁ ((λ lc → subst (λ t → Sat op (t ⊕ [ ix 1 ])) (end-one op x′ le lc) top)
                                    , c′ , x′ , le , subst (λ t → Sync t c′) (sub-one op x′ l′ le) sy)
  ...   | inj₂ (c″ , lc″ , w) = inj₂ (subst (λ t → W⁼ H (t ⊕ [ ix 1 ]) (subOf op x l)) (end-one op x′ lc″ le) w)

  -- The chain to `s` starts at the end of a lane ending outside its
  -- subscription, where its first lane, of a value before that end, was
  -- queued.
  record Base (op : FlatOp) (s : Pos) : Set where
    field
      {q₀ c₀} : Pos
      {a₀}    : A
      x₀      : O q₀ (out a₀)
      l₀      : Lane op q₀ a₀ c₀ end
      out₀    : ¬ Sync (subOf op x₀ l₀) c₀
      chain   : Chain op c₀ s
      {q₁ k₁} : Pos
      {a₁}    : A
      {e₁}    : Ev B
      x₁      : O q₁ (out a₁)
      l₁      : Lane op q₁ a₁ k₁ e₁
      sub₁    : subOf op x₁ l₁ ≡ c₀ ⊕ [ ix 1 ]
      before₁ : q₁ ≺ c₀

  -- Down the lane index of a bounded merge.
  module Down (n : ℕ) where
    open Bounded n f O using (Sub; room; freed; queued)
    open BoundedI ok n f If (Id p ok) using (kth-lane; ending)
    open Nths O using (nth-val; nth-lt)

    -- No value lies strictly between another and a position under it.
    between : ∀ {q q′ c a a′} → O q (out a) → O q′ (out a′) → q ≺ q′ → q′ ≺ c → T (inside (q ⊕ [ ix 1 ]) c) → ⊥
    between {q} {q′} {c} x x′ qq cq ins with conv {q} {q} {q′} {c} (⊑-refl q) (≺→≼ {q} {q′} qq) cq (⊑-trans (⊑-snoc⁺ q) (inside-⊑ _ _ ins))
    ... | [] , e = ≺-irrefl {q} (subst (q ≺_) (trans e (⊕-identityʳ q)) qq)
    ... | (_ ∷ _) , refl = InvAt.flat (Id p ok) x x′

    go : ∀ i → Acc _<_ i → ∀ {q s a k e} → Sub i q s a → After (f a) s k e → ¬ s ≡ q ⊕ [ ix 1 ] → Base (mergeᶠ (just n)) s
    go i _ (_ , room _)    _ nq = ⊥-elim (nq refl)
    go i _ (_ , freed _ _) _ nq = ⊥-elim (nq refl)
    go i (acc rs) {q} (ni , queued {c} n≤i qc kc kl nk) r _ with kth-lane i kc
    ... | ending {j} j<i (qj , aj , sj , nj , stj , ac) refl with T? (inside sj c) | rootOf c ≟ᵖ rootOf sj
    ...   | no ins  | _      = record { x₀ = nth-val nj ; l₀ = j , sj , (nj , stj) , ac ; out₀ = λ sy → ins (proj₁ sy) ; chain = from
                                      ; x₁ = nth-val ni ; l₁ = i , _ , (ni , queued n≤i qc kc kl nk) , r ; sub₁ = refl ; before₁ = qc }
    ...   | yes _   | no nr  = record { x₀ = nth-val nj ; l₀ = j , sj , (nj , stj) , ac ; out₀ = λ sy → nr (proj₂ sy) ; chain = from
                                      ; x₁ = nth-val ni ; l₁ = i , _ , (ni , queued n≤i qc kc kl nk) , r ; sub₁ = refl ; before₁ = qc }
    ...   | yes ins | yes rt =
      let B′ = go j (rs j<i) (nj , stj) ac (λ { refl → between (nth-val nj) (nth-val ni) (nth-lt j<i nj ni) qc ins })
      in record { x₀ = Base.x₀ B′ ; l₀ = Base.l₀ B′ ; out₀ = Base.out₀ B′
                ; chain = link (nth-val nj) (j , sj , (nj , stj) , ac) (j , sj , (nj , stj) , ac) (ins , rt) (Base.chain B′)
                ; x₁ = Base.x₁ B′ ; l₁ = Base.l₁ B′ ; sub₁ = Base.sub₁ B′ ; before₁ = Base.before₁ B′ }

  -- A LANE NOT AT ITS VALUE'S `ix 1` WAS QUEUED DOWN A CHAIN FROM A BASE.
  base : ∀ op {q a k e} (x : O q (out a)) (l : Lane op q a k e) → ¬ subOf op x l ≡ q ⊕ [ ix 1 ] → Base op (subOf op x l)
  base (mergeᶠ nothing)  x l nq = ⊥-elim (nq refl)
  base switchᶠ           x l nq = ⊥-elim (nq refl)
  base exhaustᶠ          x l nq = ⊥-elim (nq refl)
  base (mergeᶠ (just n)) x (i , s , sb , r) nq = Down.go n i (<-wellFounded i) sb r nq
