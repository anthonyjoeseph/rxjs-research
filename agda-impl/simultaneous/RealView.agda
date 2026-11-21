{-# OPTIONS --guardedness #-}

-- A FLATMAP'S JOINER, READ THROUGH ITS POLICY: each value's lane, which
-- values run one, and which are cut by a later value.  The joiner has
-- ended by an instant once its outer has and every lane run and never
-- cut has (`real-ends`).
module simultaneous.RealView where

open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)

open import Data.List using (List)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (DenEnv; enter)
open import denotation.Laws.Worlds using (InvD; Ok; InvAt; ⊕-injˡ)
open import denotation.Laws.Shows using (k-shows; shows-k)
import denotation.Laws.ShowsJoin as SJ
open import simultaneous.HeldComb using (ev)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import denotation.Position using (ix; _⊕_)
open import denotation.EmissionSet using (Ev; Ended; Superseded; _≼_; module Joining; module Values)
open import denotation.Laws.Modulus using (≼-refl; ≼-trans; ≼-or-≻; ≺→≼; ≺-trans; ≺-ext; ≺-≼-≺; ≺-absurd)
open import denotation.Laws.Count using (em)
open import denotation.Laws.Shows using (∈-stable)
open import denotation.Laws.Lift using (few-lift)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Up using (up; up-⊕)
open import simultaneous.Instants using (triⁱ; transⁱ; instant-≺)
open import simultaneous.TakeCut using (inst-⊕)
open import denotation.Position using (Pos)
open import denotation.EmissionSet using (EmissionSet; Den; out; end; LaneOf; _≺_; Few; Truncate; module Merge; module Bounded;
  module Switch; module Exhaust)
open import denotation.Laws.Worlds using (Shows)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_)

module View {A B : Set} (f : A → Den B) (o : EmissionSet A) where

  -- The value at `q`'s lane.
  Lane : FlatOp → Pos → A → EmissionSet B
  Lane (mergeᶠ nothing)  = LaneOf f
  Lane (mergeᶠ (just n)) = Bounded.Lane n f o
  Lane switchᶠ           = LaneOf f
  Lane exhaustᶠ          = LaneOf f

  -- The value at `q` runs its lane.
  Runs : FlatOp → Pos → Set
  Runs (mergeᶠ nothing)  _ = ⊤
  Runs (mergeᶠ (just n)) q = Bounded.Indexed n f o q
  Runs switchᶠ           _ = ⊤
  Runs exhaustᶠ          q = Exhaust.Run f o q

  -- A later value cuts the value at `q`'s lane.
  Cut : FlatOp → Pos → Set
  Cut switchᶠ q = Σ Pos λ q′ → Σ A λ a′ → o q′ (out a′) × q ≺ q′
  Cut _       _ = ⊥

  -- The joiner itself.
  Join : FlatOp → EmissionSet B
  Join (mergeᶠ nothing)  = Merge.JoinT f o
  Join (mergeᶠ (just n)) = Bounded.JoinT n f o
  Join switchᶠ           = Switch.JoinT f o
  Join exhaustᶠ          = Exhaust.JoinT f o

  -- The outer has ended by the instant `I`,
  OuterBy : _ → Set
  OuterBy I = Σ Pos λ c → o c end × ¬ (I ≺ⁱ instantOf c)

  -- and so has every lane run and never cut.
  LanesBy : FlatOp → _ → Set
  LanesBy op I = ∀ {q a} → o q (out a) → Runs op q → ¬ Cut op q → ¬ ¬ Σ Pos λ c → Lane op q a c end × ¬ (I ≺ⁱ instantOf c)

-- An elaborated flatMap's policy's joiner, read past finitely many rows, is a row of it.
real-from : ∀ m op {Γ A B} (F : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (E : DenEnv Γ) p {k e}
          → Truncate (View.Join (λ a → ev m (F a) E) (enter (ev m s E) p) op) k e → enter (ev m (flatMap op F s) E) p k e
real-from nothing  (mergeᶠ nothing)  F s E p x = x
real-from nothing  (mergeᶠ (just _)) F s E p x = x
real-from nothing  switchᶠ           F s E p x = x
real-from nothing  exhaustᶠ          F s E p x = x
real-from (just _) (mergeᶠ nothing)  F s E p x = x
real-from (just _) (mergeᶠ (just _)) F s E p x = x
real-from (just _) switchᶠ           F s E p x = x
real-from (just _) exhaustᶠ          F s E p x = x

-- Each policy's joiner shows its hangs where its outer and lanes do.
join-shows : ∀ {A B H} op (d : Den A) (f : A → Den B) → InvD H d → (∀ a → InvD H (f a)) → ∀ p → Ok H p
           → Shows (enter d p) → (∀ a s → Ok H s → Shows (enter (f a) s)) → Shows (View.Join f (enter d p) op)
join-shows (mergeᶠ nothing)  d f Id If p ok so sf = k-shows λ n →
  SJ.Flat.sk-merge {n = n} d f Id If p ok (shows-k so) (λ a s oks → shows-k (sf a s oks))
join-shows (mergeᶠ (just m)) d f Id If p ok so sf = k-shows λ n →
  SJ.Flat.Bnd.sk-bounded {n = n} d f Id If p ok (shows-k so) (λ a s oks → shows-k (sf a s oks)) m
join-shows switchᶠ           d f Id If p ok so sf = k-shows λ n →
  SJ.Flat.sk-switch {n = n} d f Id If p ok (shows-k so) (λ a s oks → shows-k (sf a s oks))
join-shows exhaustᶠ          d f Id If p ok so sf = k-shows λ n →
  SJ.Flat.sk-exhaust {n = n} d f Id If p ok (shows-k so) (λ a s oks → shows-k (sf a s oks))

-- The latest of finitely many positions where `P` holds.
nn-max : ∀ (P : Pos → Set) (L : List Pos) → (∀ {c} → P c → c ∈ L) → ∀ {c₀} → P c₀
       → ¬ ¬ Σ Pos λ c → P c × (∀ {c′} → P c′ → c′ ≼ c)
nn-max P L inL {c₀} p₀ ¬g = go L λ where
    (inj₁ (c , pc , _ , mx)) → ¬g (c , pc , λ pc′ → mx pc′ (inL pc′))
    (inj₂ none)              → none p₀ (inL p₀)
  where
    Res : List Pos → Set
    Res L′ = (Σ Pos λ c → P c × c ∈ L′ × (∀ {c′} → P c′ → c′ ∈ L′ → c′ ≼ c)) ⊎ (∀ {c′} → P c′ → c′ ∈ L′ → ⊥)

    yes : ∀ {x L′} → P x → Res L′ → Res (x ∷ L′)
    yes {x} px (inj₁ (c , pc , ci , mx)) with ≼-or-≻ c x
    ... | inj₁ cx = inj₁ (x , px , here refl , λ { pc′ (here refl) → ≼-refl {x} ; pc′ (there i) → ≼-trans {_} {c} {x} (mx pc′ i) cx })
    ... | inj₂ xc = inj₁ (c , pc , there ci , λ { pc′ (here refl) → ≺→≼ {x} {c} xc ; pc′ (there i) → mx pc′ i })
    yes {x} px (inj₂ none) = inj₁ (x , px , here refl , λ { pc′ (here refl) → ≼-refl {x} ; pc′ (there i) → ⊥-elim (none pc′ i) })

    no : ∀ {x L′} → ¬ P x → Res L′ → Res (x ∷ L′)
    no ¬px (inj₁ (c , pc , ci , mx)) = inj₁ (c , pc , there ci , λ { pc′ (here refl) → ⊥-elim (¬px pc′) ; pc′ (there i) → mx pc′ i })
    no ¬px (inj₂ none)               = inj₂ λ { pc′ (here refl) → ¬px pc′ ; pc′ (there i) → none pc′ i }

    go : ∀ L′ → ¬ Res L′ → ⊥
    go []       k = k (inj₂ λ _ ())
    go (x ∷ L′) k = go L′ λ r → k (no (λ px → k (yes px r)) r)

-- What holds of each of finitely many values, at one value per position,
-- holds of all of them.
nn-all : ∀ {A : Set} (R P : Pos → A → Set) (ks : List Pos)
       → (∀ {q a} → R q a → (q ⊕ [ ix 0 ]) ∈ ks) → (∀ {q a a′} → R q a → R q a′ → a ≡ a′)
       → (∀ {q a} → R q a → ¬ ¬ P q a) → ¬ ¬ (∀ {q a} → R q a → P q a)
nn-all {A} R P ks mem func each ¬all = go ks λ g → ¬all λ r → g r (mem r)
  where
    Gs : List Pos → Set
    Gs ks′ = ∀ {q a} → R q a → (q ⊕ [ ix 0 ]) ∈ ks′ → P q a

    go : ∀ ks′ → ¬ Gs ks′ → ⊥
    go []         κ = κ λ _ ()
    go (k₀ ∷ ks′) κ = go ks′ λ g → em {P = Σ Pos λ q → Σ A λ a → k₀ ≡ q ⊕ [ ix 0 ] × R q a}
      (λ (q₀ , a₀ , eq , r₀) ¬G → each r₀ λ p₀ → ¬G λ where
        {q} r (here e) → yes r r₀ p₀ (⊕-injˡ q q₀ (trans e eq))
        r (there i)    → g r i)
      (λ no ¬G → ¬G λ where
        {q} {a} r (here e) → ⊥-elim (no (q , a , sym e , r))
        r (there i)        → g r i)
      κ
      where
        yes : ∀ {q a q₀ a₀} → R q a → R q₀ a₀ → P q₀ a₀ → q ≡ q₀ → P q a
        yes r r₀ p₀ refl with func r r₀
        ... | refl = p₀

-- A JOINER HAS ENDED BY AN INSTANT BEFORE ONE WHERE IT HAS FEW ROWS, once
-- its outer and every lane run and never cut have: at the last of those
-- ends every part running has ended, and nothing is handed on past it.
module Ends {A B : Set} (Lane : Pos → A → EmissionSet B) (o : EmissionSet A) (Bg : EmissionSet B)
            (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set)
            (CutV : Pos → Set) (cut-v : ∀ {q c} → Cut q c → CutV q) where
  open Joining Lane o Bg (Ended o) Runs Cut Hand

  Rel : Pos → A → Set
  Rel q a = o q (out a) × Runs q × ¬ CutV q

  module _ {I c₀} (oc : o c₀ end) (ic₀ : ¬ (I ≺ⁱ instantOf c₀))
           (lanes : ∀ {q a} → Rel q a → Σ Pos λ c → Lane q a c end × ¬ (I ≺ⁱ instantOf c))
           (cut-late : ∀ {q c} → CutV q → c₀ ≼ c → Cut q c)
           (hand-past : ∀ {c} → Hand c → Σ Pos λ q → Σ A λ a → Rel q a × (∀ {c′} → Lane q a c′ end → c ≺ c′)) where

    -- Where the outer ends, or a lane run and never cut, by `I`.
    Cand : Pos → Set
    Cand c = ((c ≡ c₀) ⊎ (Σ Pos λ q → Σ A λ a → Rel q a × Lane q a c end)) × ¬ (I ≺ⁱ instantOf c)

    at-max : ∀ {c} → Cand c → (∀ {c′} → Cand c′ → c′ ≼ c) → JoinT c end
    at-max {c} cc mx with proj₁ cc
    ... | inj₁ refl                       = oend oc done
      where
        done : Done c
        done = (c₀ , oc , mx (inj₁ refl , ic₀)) , λ {q} {a} x r _ nct →
          let (c′ , l′ , i′) = lanes (x , r , λ cv → nct (cut-late cv (mx (inj₁ refl , ic₀)))) in
          c′ , l′ , mx (inj₂ (q , a , (x , r , λ cv → nct (cut-late cv (mx (inj₁ refl , ic₀)))) , l′) , i′)
    ... | inj₂ (q , a , (x , r , nv) , l) = lend x r l (λ ct → nv (cut-v ct)) nh done
      where
        done : Done c
        done = (c₀ , oc , mx (inj₁ refl , ic₀)) , λ {q′} {a′} x′ r′ _ nct →
          let (c′ , l′ , i′) = lanes (x′ , r′ , λ cv → nct (cut-late cv (mx (inj₁ refl , ic₀)))) in
          c′ , l′ , mx (inj₂ (q′ , a′ , (x′ , r′ , λ cv → nct (cut-late cv (mx (inj₁ refl , ic₀)))) , l′) , i′)
        nh : ¬ Hand c
        nh h with hand-past h
        ... | q′ , a′ , rl , aft with lanes rl
        ...   | c′ , l′ , i′ = mx (inj₂ (q′ , a′ , rl , l′) , i′) (aft l′)

    -- Each candidate is where the joiner has a row, or one step down.
    ev-at : ∀ {c} → Cand c → ¬ ¬ ((Σ (Ev B) λ e → JoinT c e) ⊎ (Σ (Ev B) λ e → JoinT (c ⊕ [ ix 0 ]) e))
    ev-at {c} cc with proj₁ cc
    ... | inj₁ refl = em (λ d ¬r → ¬r (inj₁ (_ , oend oc d))) (λ nd ¬r → ¬r (inj₁ (_ , opass oc nd)))
    ... | inj₂ (q , a , (x , r , nv) , l) =
      em (λ h ¬r → ¬r (inj₂ (_ , hand x r l (λ ct → nv (cut-v ct)) h)))
         (λ nh → em (λ d ¬r → ¬r (inj₁ (_ , lend x r l (λ ct → nv (cut-v ct)) nh d)))
                    (λ nd ¬r → ¬r (inj₁ (_ , lpass x r l (λ ct → nv (cut-v ct)) nh nd))))

    ends : Shows JoinT → ∀ {v} → Few (Truncate JoinT) v → I ≺ⁱ instantOf v
         → ¬ ¬ Σ Pos λ y → Truncate JoinT y end × ¬ (I ≺ⁱ instantOf y)
    ends sh {v} (ks , h) iv ¬g =
      nn-max Cand (ks ++ L.map up ks) inL (inj₁ refl , ic₀) λ (c , cc , mx) →
        few-lift sh (ks , h) (at-max cc mx) (≺→≼ {c} {v} (bv c (proj₂ cc))) λ t → ¬g (c , t , proj₂ cc)
      where
        bv : ∀ k → ¬ (I ≺ⁱ instantOf k) → k ≺ v
        bv k nk with triⁱ (instantOf k) I
        ... | inj₁ kI        = instant-≺ k v (transⁱ kI iv)
        ... | inj₂ (inj₁ eq) = instant-≺ k v (subst (_≺ⁱ instantOf v) (sym eq) iv)
        ... | inj₂ (inj₂ Ik) = ⊥-elim (nk Ik)

        i₀ : ∀ c → ¬ (I ≺ⁱ instantOf c) → ¬ (I ≺ⁱ instantOf (c ⊕ [ ix 0 ]))
        i₀ c = subst (λ j → ¬ (I ≺ⁱ j)) (sym (inst-⊕ c [ ix 0 ]))

        inL : ∀ {c} → Cand c → c ∈ ks ++ L.map up ks
        inL {c} cc = ∈-stable λ ¬i → ev-at cc λ where
          (inj₁ (_ , j)) → few-lift sh (ks , h) j (≺→≼ {c} {v} (bv c (proj₂ cc))) λ t → ¬i (∈-++⁺ˡ (h t (bv c (proj₂ cc))))
          (inj₂ (_ , j)) → few-lift sh (ks , h) j (≺→≼ {c ⊕ [ ix 0 ]} {v} (bv (c ⊕ [ ix 0 ]) (i₀ c (proj₂ cc)))) λ t →
            ¬i (∈-++⁺ʳ ks (subst (_∈ L.map up ks) (up-⊕ c (ix 0)) (∈-map⁺ up (h t (bv (c ⊕ [ ix 0 ]) (i₀ c (proj₂ cc)))))))

  -- The same, each lane known to end by `I` only up to double negation:
  -- the values before the outer's end are finitely many rows of it.
  ends¬ : ∀ {I c₀} → o c₀ end → ¬ (I ≺ⁱ instantOf c₀)
        → (∀ {q a} → Rel q a → ¬ ¬ Σ Pos λ c → Lane q a c end × ¬ (I ≺ⁱ instantOf c))
        → (∀ {q c} → CutV q → c₀ ≼ c → Cut q c)
        → (∀ {c} → Hand c → Σ Pos λ q → Σ A λ a → Rel q a × (∀ {c′} → Lane q a c′ end → c ≺ c′))
        → (∀ {q a a′} → o q (out a) → o q (out a′) → a ≡ a′) → (∀ {q a} → o q (out a) → q ≺ c₀)
        → Shows JoinT → ∀ {v} → Few (Truncate JoinT) v → I ≺ⁱ instantOf v
        → ¬ ¬ Σ Pos λ y → Truncate JoinT y end × ¬ (I ≺ⁱ instantOf y)
  ends¬ {I} {c₀} oc ic₀ ln cl hp func be sh {v} (ks , h) iv ¬g =
    nn-all Rel (λ q a → Σ Pos λ c → Lane q a c end × ¬ (I ≺ⁱ instantOf c)) ks mem
      (λ (x , _) (x′ , _) → func x x′) ln λ lanes → ends oc ic₀ lanes cl hp sh (ks , h) iv ¬g
    where
      nq : ∀ {q a} → o q (out a) → ¬ (I ≺ⁱ instantOf (q ⊕ [ ix 0 ]))
      nq {q} x Iq with triⁱ (instantOf c₀) (instantOf q)
      ... | inj₁ cq        = ≺-absurd {q} {c₀} (be x) (instant-≺ c₀ q cq)
      ... | inj₂ (inj₁ eq) = ic₀ (subst (I ≺ⁱ_) (trans (inst-⊕ q [ ix 0 ]) (sym eq)) Iq)
      ... | inj₂ (inj₂ qc) = ic₀ (transⁱ (subst (I ≺ⁱ_) (inst-⊕ q [ ix 0 ]) Iq) qc)

      bv : ∀ k → ¬ (I ≺ⁱ instantOf k) → k ≺ v
      bv k nk with triⁱ (instantOf k) I
      ... | inj₁ kI        = instant-≺ k v (transⁱ kI iv)
      ... | inj₂ (inj₁ eq) = instant-≺ k v (subst (_≺ⁱ instantOf v) (sym eq) iv)
      ... | inj₂ (inj₂ Ik) = ⊥-elim (nk Ik)

      mem : ∀ {q a} → Rel q a → (q ⊕ [ ix 0 ]) ∈ ks
      mem {q} (x , _) = ∈-stable λ ¬i →
        few-lift sh (ks , h) (val x) (≺→≼ {q ⊕ [ ix 0 ]} {v} (bv (q ⊕ [ ix 0 ]) (nq x))) λ t → ¬i (h t (bv (q ⊕ [ ix 0 ]) (nq x)))


-- The i-th value is a value.
nth-out : ∀ {A} {o : EmissionSet A} {i q a} → Values.Nth o i q a → o q (out a)
nth-out (Values.first x _)       = x
nth-out (Values.next _ x _ _)    = x

-- One value at a position.
o-func : ∀ {A H} {d : Den A} → InvD H d → ∀ p → Ok H p → ∀ {q a a′} → enter d p q (out a) → enter d p q (out a′) → a ≡ a′
o-func Id p ok x x′ with InvAt.func (Id p ok) x x′
... | refl = refl

-- EACH POLICY'S JOINER HAS ENDED BY AN INSTANT BEFORE ONE WHERE IT HAS
-- FEW ROWS, once its outer and every lane run and never cut have.
real-ends : ∀ {A B H} op (d : Den A) (f : A → Den B) (Id : InvD H d) (If : ∀ a → InvD H (f a)) p (ok : Ok H p)
          → Shows (enter d p) → (∀ a s → Ok H s → Shows (enter (f a) s))
          → (∀ {q a c} → enter d p q (out a) → enter d p c end → q ≺ c) → ∀ {I v}
          → Few (Truncate (View.Join f (enter d p) op)) v → I ≺ⁱ instantOf v
          → View.OuterBy f (enter d p) I → View.LanesBy f (enter d p) op I
          → ¬ ¬ Σ Pos λ y → Truncate (View.Join f (enter d p) op) y end × ¬ (I ≺ⁱ instantOf y)
real-ends (mergeᶠ nothing) d f Id If p ok so sf be fv iv (c₀ , oc , ic) ln =
  Ends.ends¬ (LaneOf f) (enter d p) (λ _ _ → ⊥) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ → ⊥) (λ ())
    oc ic (λ (x , r , nv) → ln x r nv) (λ ()) (λ ()) (o-func {d = d} Id p ok) (λ x → be x oc) (join-shows (mergeᶠ nothing) d f Id If p ok so sf) fv iv
real-ends (mergeᶠ (just n)) d f Id If p ok so sf be fv iv (c₀ , oc , ic) ln =
  Ends.ends¬ (Bounded.Lane n f o) o (λ _ _ → ⊥) (Bounded.Indexed n f o) (λ _ _ → ⊥) (Bounded.Queued n f o) (λ _ → ⊥) (λ ())
    oc ic (λ (x , r , nv) → ln x r nv) (λ ()) hp (o-func {d = d} Id p ok) (λ x → be x oc) (join-shows (mergeᶠ (just n)) d f Id If p ok so sf) fv iv
  where
    o = enter d p
    open BoundedI ok n f If (Id p ok) using (sub-same)
    hp : ∀ {c} → Bounded.Queued n f o c → Σ Pos λ q → Σ _ λ a → Ends.Rel (Bounded.Lane n f o) o (λ _ _ → ⊥) (Bounded.Indexed n f o)
           (λ _ _ → ⊥) (Bounded.Queued n f o) (λ _ → ⊥) (λ ()) q a × (∀ {c′} → Bounded.Lane n f o q a c′ end → c ≺ c′)
    hp {c} (i , q , a , sb) = q , a , (nth-out (proj₁ sb) , (i , a , proj₁ sb) , λ ()) ,
      λ { {c′} (_ , s′ , sb′ , (_ , lt)) → ≺-trans {c} {c ⊕ [ ix 1 ]} {c′} (≺-ext c []) (subst (_≺ c′) (sym (sub-same sb sb′)) lt) }
real-ends switchᶠ d f Id If p ok so sf be fv iv (c₀ , oc , ic) ln =
  Ends.ends¬ (LaneOf f) (enter d p) (λ _ _ → ⊥) (λ _ → ⊤) (Superseded (enter d p)) (λ _ → ⊥) (View.Cut f (enter d p) switchᶠ)
    (λ (q′ , a′ , x , lt , _) → q′ , a′ , x , lt)
    oc ic (λ (x , r , nv) → ln x r nv) (λ (q′ , a′ , x , lt) c₀c → q′ , a′ , x , lt , ≺-≼-≺ {q′} {c₀} {_} (be x oc) c₀c) (λ ())
    (o-func {d = d} Id p ok) (λ x → be x oc) (join-shows switchᶠ d f Id If p ok so sf) fv iv
real-ends exhaustᶠ d f Id If p ok so sf be fv iv (c₀ , oc , ic) ln =
  Ends.ends¬ (LaneOf f) (enter d p) (λ _ _ → ⊥) (Exhaust.Run f (enter d p)) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ → ⊥) (λ ())
    oc ic (λ (x , r , nv) → ln x r nv) (λ ()) (λ ()) (o-func {d = d} Id p ok) (λ x → be x oc) (join-shows exhaustᶠ d f Id If p ok so sf) fv iv

