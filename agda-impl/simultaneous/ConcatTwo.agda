{-# OPTIONS --guardedness #-}

-- A BOUNDED MERGE OF TWO VALUES ENDS ONCE BOTH LANES HAVE (`Two.End.row`):
-- where its outer does, the second lane having ended before that, or
-- else where the second lane does.  The second lane starts past the
-- first's end, so nothing is queued at the second's end; and the merge's
-- rows before its end are its outer's, its lanes', and the silent firsts
-- of their ends.
module simultaneous.ConcatTwo where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Position using (Pos; ix; last; instant; _∙_; _⊕_)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; enter; out; end; at-out; on-out; at-end; _≺_; _≼_; After; Truncate; module Op; module Values; module Bounded)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺; ≼-refl; ≺→≼; ≺-irrefl; ≼-or-≻)
open import denotation.Laws.Worlds using (⊕-injˡ)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end-row)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Nth using (module Nths)
open import simultaneous.LaneLayers using (starts-after)
open import simultaneous.ColdIdle using (mid)

-- A step below a position stays in its instant.
inst-ext : ∀ p zs → instant (p ⊕ zs) ≡ instant p
inst-ext (_ ∙ _) _ = refl

-- `O` holds the rows of `of [ a₀ , a₁ ]` read at `Q`.
module Two {A B : Set} (f : A → Den B) (O : EmissionSet A) (Q : Pos) (a₀ a₁ : A)
           (to : ∀ {y e} → O y e → enter (Op.of (a₀ ∷ a₁ ∷ [])) Q y e) (from : ∀ {y e} → enter (Op.of (a₀ ∷ a₁ ∷ [])) Q y e → O y e) where

  open Bounded 1 f O
  open Values O using (Nth; first; next)
  open Nths O using (nth-val; nth-inj)

  q₀ q₁ qL : Pos
  q₀ = Q ⊕ [ ix 0 ]
  q₁ = Q ⊕ [ ix 1 ]
  qL = Q ⊕ [ last ]

  ob₀ : O q₀ (out a₀)
  ob₀ = from (at-out , of-reach Q 0 (a₀ ∷ a₁ ∷ []) {q₀} {out a₀})

  ob₁ : O q₁ (out a₁)
  ob₁ = from (on-out at-out , of-reach Q 0 (a₀ ∷ a₁ ∷ []) {q₁} {out a₁})

  obL : O qL end
  obL = from (of-end-row Q 0 (a₀ ∷ a₁ ∷ []) , of-reach Q 0 (a₀ ∷ a₁ ∷ []) {qL} {end})

  lt01 : q₀ ≺ q₁
  lt01 = ix-asc Q (s≤s z≤n)

  -- The outer's rows.
  data ORow : Pos → Ev A → Set where
    r₀ : ORow q₀ (out a₀)
    r₁ : ORow q₁ (out a₁)
    rL : ORow qL end

  of-row : ∀ {y e} → enter (Op.of (a₀ ∷ a₁ ∷ [])) Q y e → ORow y e
  of-row (at-out , _)                 = r₀
  of-row (on-out at-out , _)          = r₁
  of-row (on-out (on-out at-end) , _) = rL

  o-row : ∀ {y e} → O y e → ORow y e
  o-row x = of-row (to x)

  lo : ∀ {k b} → O k (out b) → q₀ ≼ k
  lo x with o-row x
  ... | r₀ = ≼-refl {q₀}
  ... | r₁ = ≺→≼ {q₀} {q₁} lt01

  nx₁ : ∀ {k b} → O k (out b) → q₀ ≺ k → q₁ ≼ k
  nx₁ x lt with o-row x
  ... | r₀ = ⊥-elim (≺-irrefl {q₀} lt)
  ... | r₁ = ≼-refl {q₁}

  nth₀ : Nth 0 q₀ a₀
  nth₀ = first ob₀ lo

  nth₁ : Nth 1 q₁ a₁
  nth₁ = next nth₀ ob₁ lt01 nx₁

  -- The outer's two values, by index.
  data NthC : ℕ → Pos → A → Set where
    n₀ : NthC 0 q₀ a₀
    n₁ : NthC 1 q₁ a₁

  nth-c : ∀ {i q a} → Nth i q a → NthC i q a
  nth-c n with o-row (nth-val n)
  ... | r₀ with nth-inj n nth₀
  ...   | refl = n₀
  nth-c n | r₁ with nth-inj n nth₁
  ...   | refl = n₁

  -- The first lane starts at once.
  starts₀ : ∀ {q s} → Starts 0 q [] s → s ≡ q ⊕ [ ix 1 ]
  starts₀ (room _)            = refl
  starts₀ (freed () _)
  starts₀ (queued () _ _ _ _)

  sub₀ : Sub 0 q₀ (q₀ ⊕ [ ix 1 ]) a₀
  sub₀ = nth₀ , room (s≤s z≤n)

  -- A lane of the second value starts as the second lane.
  second : (a₀ ≡ a₁ → ⊥) → ∀ {i q s a} → a ≡ a₁ → Sub i q s a → Starts 1 q₁ (Sched 1) s
  second ne eq (n , st) with nth-c n
  ... | n₀ = ⊥-elim (ne eq)
  ... | n₁ = st

  -- The first lane's end, and the second lane starts at one.
  end-of : ∀ {c} → Ends 0 [] c → After (f a₀) (q₀ ⊕ [ ix 1 ]) c end
  end-of (_ , _ , _ , n , st , e) with nth-c n
  ... | n₀ with starts₀ st
  ...   | refl = e

  first-end : ∀ {s} → Starts 1 q₁ (Sched 1) s → Σ Pos λ c₀ → After (f a₀) (q₀ ⊕ [ ix 1 ]) c₀ end
  first-end (room (s≤s ()))
  first-end (freed _ (inj₁ (c , ec , _)))               = c , end-of ec
  first-end (freed _ (inj₂ ()))
  first-end (queued {c} _ _ (inj₁ (_ , ec , refl)) _ _) = c , end-of ec
  first-end (queued _ _ (inj₂ ()) _ _)

  module End {c₀ c₁ s₁ : Pos} (e₀ : After (f a₀) (q₀ ⊕ [ ix 1 ]) c₀ end) (u₀ : ∀ {c} → After (f a₀) (q₀ ⊕ [ ix 1 ]) c end → c ≡ c₀)
             (st₁ : Starts 1 q₁ (Sched 1) s₁) (e₁ : After (f a₁) s₁ c₁ end) where

    sub₁ : Sub 1 q₁ s₁ a₁
    sub₁ = nth₁ , st₁

    -- The first lane ends once.
    ends₀ : ∀ {c} → Ends 0 [] c → c ≡ c₀
    ends₀ ec = u₀ (end-of ec)

    -- The second lane starts past the first's end.
    past₀ : ∀ {s} → Starts 1 q₁ (Sched 1) s → c₀ ≺ s
    past₀ (room (s≤s ()))
    past₀ (freed _ (inj₁ (c , ec , lt))) = subst (_≺ (q₁ ⊕ [ ix 1 ])) (ends₀ ec) (≺-trans {c} {q₁} {q₁ ⊕ [ ix 1 ]} lt (≺-ext q₁ []))
    past₀ (freed _ (inj₂ ()))
    past₀ (queued {c} _ _ (inj₁ (_ , ec , refl)) _ _) = subst (_≺ (c ⊕ [ ix 1 ])) (ends₀ ec) (≺-ext c [])
    past₀ (queued _ _ (inj₂ ()) _ _)

    -- The second lane starts once.
    starts₁ : ∀ {s} → Starts 1 q₁ (Sched 1) s → s ≡ s₁
    starts₁ st = go st st₁
      where
        go : ∀ {s s′} → Starts 1 q₁ (Sched 1) s → Starts 1 q₁ (Sched 1) s′ → s ≡ s′
        go (room (s≤s ())) _
        go _ (room (s≤s ()))
        go (freed _ _) (freed _ _) = refl
        go (freed _ (inj₁ (c , ec , lt))) (queued {c′} _ qc (inj₁ (_ , ec′ , refl)) _ _) =
          ⊥-elim (≺-irrefl {c₀} (≺-trans {c₀} {q₁} {c₀} (subst (_≺ q₁) (ends₀ ec) lt) (subst (q₁ ≺_) (ends₀ ec′) qc)))
        go (freed _ (inj₂ ())) _
        go _ (freed _ (inj₂ ()))
        go (queued _ _ (inj₂ ()) _ _) _
        go _ (queued _ _ (inj₂ ()) _ _)
        go (queued {c′} _ qc (inj₁ (_ , ec′ , refl)) _ _) (freed _ (inj₁ (c , ec , lt))) =
          ⊥-elim (≺-irrefl {c₀} (≺-trans {c₀} {q₁} {c₀} (subst (_≺ q₁) (ends₀ ec) lt) (subst (q₁ ≺_) (ends₀ ec′) qc)))
        go (queued {c} _ _ (inj₁ (_ , ec , refl)) _ _) (queued {c′} _ _ (inj₁ (_ , ec′ , refl)) _ _) =
          subst (λ z → c ⊕ [ ix 1 ] ≡ z ⊕ [ ix 1 ]) (sym (trans (ends₀ ec′) (sym (ends₀ ec)))) refl

    q₁c₁ : q₁ ≺ c₁
    q₁c₁ = ≺-trans {q₁} {s₁} {c₁} (starts-after st₁) (proj₂ e₁)

    q₀c₁ : q₀ ≺ c₁
    q₀c₁ = ≺-trans {q₀} {q₁} {c₁} lt01 q₁c₁

    c₀c₁ : c₀ ≺ c₁
    c₀c₁ = ≺-trans {c₀} {s₁} {c₁} (past₀ st₁) (proj₂ e₁)

    Qc₁ : Q ≺ c₁
    Qc₁ = ≺-trans {Q} {q₀} {c₁} (≺-ext Q []) q₀c₁

    -- Both lanes have ended by a position past both ends and the outer's.
    done : ∀ {E} → qL ≼ E → c₁ ≼ E → Done E
    done {E} le ce = (qL , obL , le) , lanes
      where
        lanes : ∀ {q a} → O q (out a) → Indexed q → q ≺ E → (⊥ → ⊥) → Σ Pos λ c → Lane q a c end × c ≼ E
        lanes x _ _ _ with o-row x
        ... | r₀ = c₀ , (0 , q₀ ⊕ [ ix 1 ] , sub₀ , e₀) , ≺→≼ {c₀} {E} (≺-≼-≺ {c₀} {c₁} {E} c₀c₁ ce)
        ... | r₁ = c₁ , (1 , s₁ , sub₁ , e₁) , ce

    -- Nothing is queued at the second lane's end.
    no₀ : ∀ {s} → Starts 0 q₀ [] s → s ≡ c₁ ⊕ [ ix 1 ] → ⊥
    no₀ st eq = ≺-irrefl {c₁} (subst (_≺ c₁) (⊕-injˡ q₀ c₁ (trans (sym (starts₀ st)) eq)) q₀c₁)

    no₁ : ∀ {s} → Starts 1 q₁ (Sched 1) s → s ≡ c₁ ⊕ [ ix 1 ] → ⊥
    no₁ (room (s≤s ())) _
    no₁ (freed _ _) eq = ≺-irrefl {c₁} (subst (_≺ c₁) (⊕-injˡ q₁ c₁ eq) q₁c₁)
    no₁ (queued {c} _ _ (inj₁ (_ , ec , refl)) _ _) eq = ≺-irrefl {c₁} (subst (_≺ c₁) (trans (sym (ends₀ ec)) (⊕-injˡ c c₁ eq)) c₀c₁)
    no₁ (queued _ _ (inj₂ ()) _ _) _

    not-queued : Queued c₁ → ⊥
    not-queued (_ , _ , _ , n , st) with nth-c n
    ... | n₀ = no₀ st refl
    ... | n₁ = no₁ st refl

    -- Where the merge ends.
    data EndAt : Pos → Set where
      at-outer : c₁ ≺ qL → EndAt qL
      at-lane  : qL ≼ c₁ → EndAt c₁

    end-at : Σ Pos EndAt
    end-at with ≼-or-≻ qL c₁
    ... | inj₁ le = c₁ , at-lane le
    ... | inj₂ lt = qL , at-outer lt

    raw-end : ∀ {E} → EndAt E → JoinT E end
    raw-end (at-outer lt) = oend obL (done (≼-refl {qL}) (≺→≼ {c₁} {qL} lt))
    raw-end (at-lane le)  = lend ob₁ (1 , a₁ , nth₁) (1 , s₁ , sub₁ , e₁) (λ ()) not-queued (done le (≼-refl {c₁}))

    -- The merge ends in its second lane's end's instant.
    end-inst : ∀ {E} → EndAt E → instant E ≡ instant c₁
    end-inst (at-lane _)   = refl
    end-inst (at-outer lt) = trans (inst-ext Q [ last ]) (sym (mid Q Q c₁ qL (≼-refl {Q}) Qc₁ (≺→≼ {c₁} {qL} lt) (sym (inst-ext Q [ last ]))))

    -- THE MERGE'S END, with few rows before it when its lanes have.
    module Row (E : Pos) (ks : List Pos) (fl₀ : ∀ {y e} → After (f a₀) (q₀ ⊕ [ ix 1 ]) y e → y ≺ E → y ∈ ks)
               (fl₁ : ∀ {y e} → After (f a₁) s₁ y e → y ≺ E → y ∈ ks) where

      fl : ∀ {i q s a y e} → Sub i q s a → After (f a) s y e → y ≺ E → y ∈ ks
      fl (n , st) l lt with nth-c n
      ... | n₀ with starts₀ st
      ...   | refl = fl₀ l lt
      fl (n , st) l lt | n₁ with starts₁ st
      ...   | refl = fl₁ l lt

      ks′ : List Pos
      ks′ = (q₀ ⊕ [ ix 0 ]) ∷ (q₁ ⊕ [ ix 0 ]) ∷ qL ∷ (ks ++ L.map (_⊕ [ ix 0 ]) ks)

      lane-ks : ∀ {q a y e} → Lane q a y e → y ≺ E → y ∈ ks
      lane-ks (_ , _ , sb , l) lt = fl sb l lt

      lane-in : ∀ {q a y e} → Lane q a y e → y ≺ E → y ∈ ks′
      lane-in l lt = there (there (there (∈-++⁺ˡ (lane-ks l lt))))

      reach : ∀ {k e′} → JoinT k e′ → k ≺ E → k ∈ ks′
      reach (val x) _ with o-row x
      ... | r₀ = here refl
      ... | r₁ = there (here refl)
      reach (step x) _ with o-row x
      ... | ()
      reach (opin x) _ with o-row x
      ... | ()
      reach (oend x _) _ with o-row x
      ... | rL = there (there (here refl))
      reach (opass x _) _ with o-row x
      ... | rL = there (there (here refl))
      reach (lane _ _ l _ _) lt       = lane-in l lt
      reach (lend _ _ l _ _ _) lt     = lane-in l lt
      reach (lpass _ _ l _ _ _) lt    = lane-in l lt
      reach (hand {c = c} _ _ l _ _) lt =
        there (there (there (∈-++⁺ʳ ks (∈-map⁺ (_⊕ [ ix 0 ]) (lane-ks l (≺-trans {c} {c ⊕ [ ix 0 ]} {E} (≺-ext c []) lt))))))
      reach (left _ _ l _ _) lt       = lane-in l lt
      reach (run () _)
      reach (rend () _ _)
      reach (rpass () _ _)
      reach (rhand () _)

      row : EndAt E → Truncate JoinT E end
      row ea = raw-end ea , ks′ , λ x lt _ → reach x lt
