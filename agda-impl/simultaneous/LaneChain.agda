-- A QUEUED LANE'S CHAIN OF ENDS HAS A BASE.  A bounded merge subscribes
-- a queued lane at an earlier lane's end.  A lane ending inside its own
-- subscription was itself queued: one subscribed at its value's `ix 1`
-- and ending there would hold the later value queued at that end under
-- its own value (`flat`).  Down the lane index, the chain reaches a lane
-- whose end lies outside its subscription.
module simultaneous.LaneChain where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; _⊕_; _≟ᵖ_; inside)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; After; enter; out; end; _≺_; module Bounded)
open import denotation.Laws.Worlds using (InvD; InvAt; Ok; inside-⊑; conv; ⊑-refl; ⊑-trans; ⊑-snoc⁺; _⊑_)
open import denotation.Laws.Modulus using (≺→≼; ≺-irrefl)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI; end-uniq)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.Routed using (Sync)
open import simultaneous.RealView using (module View; lane-at; lane-at₂; lane-fwd)

module Chains {A B H} (d : Den A) (f : A → Den B) (Id : InvD H d) (If : ∀ a → InvD H (f a)) (p : Pos) (ok : Ok H p) where
  O : EmissionSet A
  O = enter d p

  open View f O using (Lane)

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

  -- One value's lanes share one subscription.
  sub-one : ∀ op {q a k e k′ e′} (x : O q (out a)) (l : Lane op q a k e) (l′ : Lane op q a k′ e′) → subOf op x l ≡ subOf op x l′
  sub-one (mergeᶠ nothing)  x l l′ = refl
  sub-one switchᶠ           x l l′ = refl
  sub-one exhaustᶠ          x l l′ = refl
  sub-one (mergeᶠ (just n)) x (_ , _ , sb , _) (_ , _ , sb′ , _) = BoundedI.sub-same ok n f If (Id p ok) sb sb′

  -- A lane ends once.
  end-one : ∀ op {q a c c′} → O q (out a) → Lane op q a c end → Lane op q a c′ end → c ≡ c′
  end-one op x l l′ = let (s , oks , r , r′) = lane-at₂ op d f Id If p ok x l l′ in end-uniq (If _ s oks) r r′

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
    ... | [] , e = ≺-irrefl {q} (subst (q ≺_) e qq)
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
