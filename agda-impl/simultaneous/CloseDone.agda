{-# OPTIONS --guardedness #-}

-- THE CLOSER'S `outerDone` LIES IN THE OUTER END'S INSTANT: the closer's
-- first part, each outer value's bracket, ends one `sub` under the outer's
-- end, where the concat queues its second part, whose `of` sends
-- `outerDone` one step down.  Every end of the closer lies past it.
module simultaneous.CloseDone where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; Instant; ix; sub; last; root; _≟ᵖ_; _⊕_; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; pin; end; EmissionSet; Den; DenEnv; hot; enter; After; Reach;
  Rejoin; shown; heard; ended; late; at-out; on-out; module Op; module Merge; module Bounded; module Values; _≺_; _≼_; Few)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺-irrefl; ≺-absurd; ≼-refl; ≼-split; ≺→≼; ≺-≼-≺)
open import denotation.Laws.Worlds using (Lawful; ⊕-assoc)
open import denotation.Laws.Worlds.Leaves using (of-in; of-reach; of-end; of-end-row)
open import denotation.Laws.Rejoined using (row-reach)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Truth using () renaming (past to ix≺last)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.HeldComb using (ev)
open import simultaneous.CombSent using (Clo; assoc³; module EachEnd)
open import simultaneous.Readings using (instantOf)
open import simultaneous.InstEmit using (instEmit; value; mark; outerDone)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; closer; closing; marked)

inst-⊕ : ∀ p zs → instantOf (p ⊕ zs) ≡ instantOf p
inst-⊕ (_ ∙ _) _ = refl

module CloseDone (m : Maybe ℕ) {Δ A B} (t : EmissionSet (IE A)) (env : DenEnv Δ) (L : Lawful t) (s : Pos)
                 (past : ∀ zs {k e} → t k e → (s ⊕ zs) ≺ k) where

  ρ : DenEnv (IE A ∷ Δ)
  ρ = hot t ∷ env

  -- The concat's parts, its outer, and the first part's reading.
  G : Bool → Den (IE B)
  G b = ev m (Clo {Δ} {A} {B} b) ρ

  O : EmissionSet Bool
  O = enter (Op.of (true ∷ false ∷ [])) s

  D₀ : Den (IE B)
  D₀ = Op.flatMap (mergeᶠ nothing) (λ x → Op.of (closing {A} {B} x)) (hot t)

  private
    closer-op′ : ∀ m′ → ev m′ (closer {Δ} {A} {B}) ρ ≡ Op.flatMap (mergeᶠ (just 1)) (λ b → ev m′ (Clo {Δ} {A} {B} b) ρ) (Op.of (true ∷ false ∷ []))
    closer-op′ nothing  = refl
    closer-op′ (just _) = refl

    first-op′ : ∀ m′ → ev m′ (Clo {Δ} {A} {B} true) ρ ≡ D₀
    first-op′ nothing  = refl
    first-op′ (just _) = refl

    second-op′ : ∀ m′ → ev m′ (Clo {Δ} {A} {B} false) ρ ≡ Op.of (marked {B} outerDone ∷ [])
    second-op′ nothing  = refl
    second-op′ (just _) = refl

  closer-op : ev m (closer {Δ} {A} {B}) ρ ≡ Op.flatMap (mergeᶠ (just 1)) G (Op.of (true ∷ false ∷ []))
  closer-op = closer-op′ m

  first-op : G true ≡ D₀
  first-op = first-op′ m

  second-op : G false ≡ Op.of (marked {B} outerDone ∷ [])
  second-op = second-op′ m

  module Bd = Bounded 1 G O

  q₀ q₁ s₁ : Pos
  q₀ = s ⊕ [ ix 0 ]
  q₁ = s ⊕ [ ix 1 ]
  s₁ = q₀ ⊕ [ ix 1 ]

  pastS : ∀ {k e} → t k e → s₁ ≺ k
  pastS {k} r = subst (_≺ k) (sym (⊕-assoc s [ ix 0 ] [ ix 1 ])) (past (ix 0 ∷ ix 1 ∷ []) r)

  module Mg = Merge (λ x → Op.of (closing {A} {B} x)) (enter (hot t) s₁)
  module EE = EachEnd (closing {A} {B}) t L (λ _ → ⊤) (λ _ _ → tt) (λ _ → tt) s₁ tt

  ------------------------------------------------------------------------
  -- The concat's outer: the first part's value, then the second's

  o₀ : O q₀ (out true)
  o₀ = at-out , of-reach s 0 (true ∷ false ∷ []) {q₀} {out true}

  o₁ : O q₁ (out false)
  o₁ = on-out at-out , of-reach s 0 (true ∷ false ∷ []) {q₁} {out false}

  q₀≺q₁ : q₀ ≺ q₁
  q₀≺q₁ = ix-asc s (s≤s z≤n)

  o-rows : ∀ {k b} → O k (out b) → (k ≡ q₀ × b ≡ true) ⊎ (k ≡ q₁ × b ≡ false)
  o-rows (at-out , _)                = inj₁ (refl , refl)
  o-rows (on-out at-out , _)         = inj₂ (refl , refl)
  o-rows (on-out (on-out ()) , _)

  nth₀ : Values.Nth O 0 q₀ true
  nth₀ = Values.first o₀ least
    where
      least : ∀ {k b} → O k (out b) → q₀ ≼ k
      least r with o-rows r
      ... | inj₁ (refl , _) = ≼-refl {q₀}
      ... | inj₂ (refl , _) = ≺→≼ {q₀} {q₁} q₀≺q₁

  nth₁ : Values.Nth O 1 q₁ false
  nth₁ = Values.next nth₀ o₁ q₀≺q₁ next
    where
      next : ∀ {k b} → O k (out b) → q₀ ≺ k → q₁ ≼ k
      next r lt with o-rows r
      ... | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q₀} lt)
      ... | inj₂ (refl , _) = ≼-refl {q₁}

  nth-row : ∀ {i q a} → Values.Nth O i q a → O q (out a)
  nth-row (Values.first r _)    = r
  nth-row (Values.next _ r _ _) = r

  nth-q₀ : ∀ {i a} → Values.Nth O i q₀ a → i ≡ 0
  nth-q₀ (Values.first _ _) = refl
  nth-q₀ (Values.next n _ lt _) with o-rows (nth-row n)
  ... | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q₀} lt)
  ... | inj₂ (refl , _) = ⊥-elim (≺-absurd {q₀} {q₁} q₀≺q₁ lt)

  nth-q₁ : ∀ {i a} → Values.Nth O i q₁ a → i ≡ 1
  nth-q₁ (Values.first _ least) = ⊥-elim (least o₀ q₀≺q₁)
  nth-q₁ (Values.next n _ lt _) with o-rows (nth-row n)
  ... | inj₁ (refl , _) = cong suc (nth-q₀ n)
  ... | inj₂ (refl , _) = ⊥-elim (≺-irrefl {q₁} lt)

  -- The first value is the first part's.
  nth-first : ∀ {q a} → Values.Nth O 0 q a → q ≡ q₀ × a ≡ true
  nth-first (Values.first r least) with o-rows r
  ... | inj₁ eqs = eqs
  ... | inj₂ (refl , _) = ⊥-elim (least o₀ q₀≺q₁)

  ------------------------------------------------------------------------
  -- The first part's end, one `sub` under the outer's

  module FirstEnd {y} (ry : t y end) (fy : Few t y) where

    c₁ : Pos
    c₁ = y ⊕ [ sub s₁ ]

    rd : enter (hot t) s₁ c₁ end
    rd = ended ry (pastS ry) , row-reach L ry fy (pastS ry) {end}

    -- A value's bracket ends before the outer does.
    bracket : ∀ {r a} → t r (out a) → (((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) ⊕ [ last ]) ≺ c₁
    bracket {r} x = ≺-trans {((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {y} {c₁}
      (subst (_≺ y) (sym (assoc³ r (sub s₁) (ix 1) last)) (EE.under-before x ry (sub s₁ ∷ ix 1 ∷ last ∷ []))) (≺-ext y [])

    done : Mg.Done c₁
    done = (c₁ , rd , ≼-refl {c₁}) , lanes
      where
        lanes : ∀ {q a} → enter (hot t) s₁ q (out a) → ⊤ → q ≺ c₁ → _ → Σ Pos λ c₀ → _ × c₀ ≼ c₁
        lanes {a = a} (shown {q = r} x _ _ , _) _ _ _ =
          ((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) ⊕ [ last ] ,
          ((of-end-row ((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) 0 (closing {A} {B} a) ,
            of-reach ((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) 0 (closing {A} {B} a) {((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {end}) ,
           ≺-ext ((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) []) ,
          ≺→≼ {((r ⊕ [ sub s₁ ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {c₁} (bracket x)

    -- The rows before it: the reader's, and one or two below each.
    reader : List Pos
    reader = proj₁ (row-reach {j = s₁} L ry fy (pastS ry) {end})

    in-reader : ∀ {q e} → enter (hot t) s₁ q e → q ≺ c₁ → q ∈ reader
    in-reader (r , _) lt = proj₂ (row-reach {j = s₁} L ry fy (pastS ry) {end}) r lt tt

    below : List Pos
    below = reader ++ L.map (λ q → q ⊕ [ ix 0 ]) reader ++ L.map (λ q → (q ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) reader
          ++ L.map (λ q → (q ⊕ [ ix 1 ]) ⊕ [ last ]) reader

    in-val : ∀ {q} → q ∈ reader → (q ⊕ [ ix 0 ]) ∈ below
    in-val i = ∈-++⁺ʳ reader (∈-++⁺ˡ (∈-map⁺ _ i))

    in-lane : ∀ {q a k e} → q ∈ reader → enter (Op.of (closing {A} {B} a)) (q ⊕ [ ix 1 ]) k e → k ∈ below
    in-lane {q} {instEmit (value _) _} i (x , _) with of-in (q ⊕ [ ix 1 ]) 0 _ x
    ... | here refl         = ∈-++⁺ʳ reader (∈-++⁺ʳ (L.map _ reader) (∈-++⁺ˡ (∈-map⁺ _ i)))
    ... | there (here refl) = ∈-++⁺ʳ reader (∈-++⁺ʳ (L.map _ reader) (∈-++⁺ʳ (L.map _ reader) (∈-map⁺ _ i)))
    in-lane {q} {instEmit (mark _) _} i (x , _) with of-in (q ⊕ [ ix 1 ]) 0 _ x
    ... | here refl = ∈-++⁺ʳ reader (∈-++⁺ʳ (L.map _ reader) (∈-++⁺ʳ (L.map _ reader) (∈-map⁺ _ i)))

    -- A row under a reader row lies past it.
    under : ∀ {q k} l ls → (q ⊕ (l ∷ ls)) ≺ c₁ → k ≡ q ⊕ (l ∷ ls) → q ≺ c₁
    under {q} l ls lt refl = ≺-trans {q} {q ⊕ (l ∷ ls)} {c₁} (≺-ext q ls) lt

    lane-under : ∀ {q a k e} → enter (Op.of (closing {A} {B} a)) (q ⊕ [ ix 1 ]) k e → (q ⊕ [ ix 1 ]) ≺ k → k ≺ c₁ → q ≺ c₁
    lane-under {q} {k = k} _ sk kc = ≺-trans {q} {q ⊕ [ ix 1 ]} {c₁} (≺-ext q []) (≺-trans {q ⊕ [ ix 1 ]} {k} {c₁} sk kc)

    few₀ : ∀ {k e} → Mg.JoinT k e → k ≺ c₁ → k ∈ below
    few₀ (Mg.val {q} o) lt              = in-val (in-reader o (under {q} {q ⊕ [ ix 0 ]} (ix 0) [] lt refl))
    few₀ (Mg.step o) lt                 = ∈-++⁺ˡ (in-reader o lt)
    few₀ (Mg.opin o) lt                 = ∈-++⁺ˡ (in-reader o lt)
    few₀ (Mg.oend o _) lt               = ∈-++⁺ˡ (in-reader o lt)
    few₀ (Mg.opass o _) lt              = ∈-++⁺ˡ (in-reader o lt)
    few₀ (Mg.lane o _ (l , sl) _ _) lt  = in-lane (in-reader o (lane-under l sl lt)) l
    few₀ (Mg.lend o _ (l , sl) _ _ _) lt  = in-lane (in-reader o (lane-under l sl lt)) l
    few₀ (Mg.lpass o _ (l , sl) _ _ _) lt = in-lane (in-reader o (lane-under l sl lt)) l
    few₀ (Mg.hand _ _ _ _ ())
    few₀ (Mg.left o _ (l , sl) _ _) lt  = in-lane (in-reader o (lane-under l sl lt)) l
    few₀ (Mg.run () _)
    few₀ (Mg.rend () _ _)
    few₀ (Mg.rpass () _ _)
    few₀ (Mg.rhand () _)

    end₀ : enter D₀ s₁ c₁ end
    end₀ = Mg.oend rd done , below , λ x lt _ → few₀ x lt

    -- It is the first part's only end.
    end-only : ∀ {c} → enter D₀ s₁ c end → c ≡ c₁
    end-only (Mg.oend (ended {y′} r′ _ , _) _ , _) with ≼-split {y′} {y} (Lawful.proper L ry r′)
    ... | inj₂ refl = refl
    ... | inj₁ lt   = ⊥-elim (Lawful.proper L r′ ry lt)
    end-only (Mg.oend (late {y′} r′ y′s , _) _ , _) = ⊥-elim (≺-irrefl {s₁} (≺-≼-≺ {s₁} {y′} {s₁} (pastS r′) y′s))
    end-only (Mg.oend (shown _ () _ , _) _ , _)
    end-only (Mg.lane _ _ _ _ () , _)
    end-only (Mg.lend {q} {a} (shown x _ sr , _) _ (l , _) _ _ ((_ , (rj , _) , c₀c) , _) , _)
      with of-end (q ⊕ [ ix 1 ]) 0 (closing {A} {B} a) (proj₁ l)
    ... | refl = ⊥-elim (EE.lane-past x sr rj c₀c)
    end-only (Mg.run () _ , _)
    end-only (Mg.rend () _ _ , _)

    ----------------------------------------------------------------------
    -- The concat's lanes: the first part at once, the second where it ends

    s₁≺c₁ : s₁ ≺ c₁
    s₁≺c₁ = ≺-trans {s₁} {y} {c₁} (pastS ry) (≺-ext y [])

    q₁≺c₁ : q₁ ≺ c₁
    q₁≺c₁ = ≺-trans {q₁} {y} {c₁} (past [ ix 1 ] ry) (≺-ext y [])

    ends₀ : Bd.Ends 0 [] c₁
    ends₀ = q₀ , true , s₁ , nth₀ , Bd.room (s≤s z≤n) , subst (λ d → enter d s₁ c₁ end) (sym first-op) end₀ , s₁≺c₁

    ends₀-only : ∀ {c} → Bd.Ends 0 [] c → c ≡ c₁
    ends₀-only {c} (_ , _ , _ , nth , Bd.room _ , en , _) with nth-first nth
    ... | refl , refl = end-only (subst (λ d → enter d s₁ c end) first-op en)
    ends₀-only (_ , _ , _ , _ , Bd.freed () _ , _)
    ends₀-only (_ , _ , _ , _ , Bd.queued () _ _ _ _ , _)

    k-not : ¬ Bd.Kth (_≺ c₁) (Bd.Sched 1) 0
    k-not (inj₁ (c , e , lt)) = ≺-irrefl {c₁} (subst (_≺ c₁) (ends₀-only e) lt)
    k-not (inj₂ ())

    c₂ z₀ : Pos
    c₂ = c₁ ⊕ [ ix 1 ]
    z₀ = c₂ ⊕ [ ix 0 ]

    q₁≺c₂ : q₁ ≺ c₂
    q₁≺c₂ = ≺-trans {q₁} {c₁} {c₂} q₁≺c₁ (≺-ext c₁ [])

    st₁ : Bd.Starts 1 q₁ (Bd.Sched 1) c₂
    st₁ = Bd.queued (s≤s z≤n) q₁≺c₁ (inj₁ (c₁ , ends₀ , refl)) (inj₁ (c₁ , ends₀ , ≼-refl {c₁})) k-not

    -- The second lane starts nowhere else.
    st₁-only : ∀ {s′} → Bd.Starts 1 q₁ (Bd.Sched 1) s′ → s′ ≡ c₂
    st₁-only (Bd.room (s≤s ()))
    st₁-only (Bd.freed _ (inj₁ (c , e , lt))) = ⊥-elim (≺-absurd {q₁} {c₁} q₁≺c₁ (subst (_≺ q₁) (ends₀-only e) lt))
    st₁-only (Bd.freed _ (inj₂ ()))
    st₁-only (Bd.queued _ _ (inj₁ (c , e , refl)) _ _) = cong (_⊕ [ ix 1 ]) (ends₀-only e)
    st₁-only (Bd.queued _ _ (inj₂ ()) _ _)

    -- THE RAW `outerDone`, in the outer end's instant.
    raw : Bd.JoinT z₀ (out (marked {B} outerDone))
    raw = Bd.lane o₁ (1 , false , nth₁)
      (1 , c₂ , (nth₁ , st₁) ,
       subst (λ d → enter d c₂ z₀ (out (marked {B} outerDone))) (sym second-op)
         (at-out , of-reach c₂ 0 (marked {B} outerDone ∷ []) {z₀} {out (marked {B} outerDone)}) ,
       ≺-ext c₂ [])
      (λ ()) tt

    raw-inst : instantOf z₀ ≡ instantOf y
    raw-inst = trans (inst-⊕ c₂ [ ix 0 ]) (trans (inst-⊕ c₁ [ ix 1 ]) (inst-⊕ y [ sub s₁ ]))

    -- Every raw end lies past it: the second lane has ended there.
    done-past : ∀ {c} → Bd.Done c → q₁ ≺ c → z₀ ≺ c
    done-past {c} d q₁c with proj₂ d o₁ (1 , false , nth₁) q₁c (λ ())
    ... | c₀ , (i , s′ , (nth , st) , en , _) , c₀c with nth-q₁ nth
    ...   | refl with st₁-only st
    ...     | refl with of-end c₂ 0 (marked {B} outerDone ∷ []) (proj₁ (subst (λ d → enter d c₂ c₀ end) second-op en))
    ...       | refl = ≺-≼-≺ {z₀} {c₀} {c} (ix≺last c₂ 0) c₀c

    raw-end-after : ∀ {c} → Bd.JoinT c end → z₀ ≺ c
    raw-end-after (Bd.oend (r , _) d) with of-end s 0 (true ∷ false ∷ []) r
    ... | refl = done-past d (ix≺last s 1)
    raw-end-after (Bd.lane _ _ _ _ ())
    raw-end-after (Bd.lend {q} r _ (i , s′ , (nth , st) , en , lt) _ _ d) with o-rows r
    ... | inj₁ (refl , refl) with nth-q₀ nth
    ...   | refl = done-past d (subst (q₁ ≺_) (sym (ends₀-only (q₀ , true , s′ , nth , st , en , lt))) q₁≺c₁)
    raw-end-after (Bd.lend {q} r _ (i , s′ , (nth , st) , en , lt) _ _ d) | inj₂ (refl , refl) with nth-q₁ nth
    ...   | refl with st₁-only st
    ...     | refl = done-past d (≺-trans {q₁} {c₂} {_} q₁≺c₂ lt)
    raw-end-after (Bd.run () _)
    raw-end-after (Bd.rend () _ _)
