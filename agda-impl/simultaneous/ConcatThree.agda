{-# OPTIONS --guardedness #-}

-- A BOUNDED-1 MERGE OF `of [ 0 , 1 , 2 ]` WHOSE MIDDLE LANE READS A HOT
-- SHOWS ITS THIRD LANE'S VALUE ONE LABEL UNDER THE HOT'S END
-- (`Three.row`).  The first lane is a one-value `of`, ending before the
-- second value arrives, so the second starts at once; it reads the hot,
-- ending where the hot does, rejoined; the third value arrives before
-- that and is queued there.  Every lane has finitely many rows, so the
-- merge has few rows before anywhere.
module simultaneous.ConcatThree where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import denotation.Position using (Pos; ix; sub; last; instant; _⊕_)
open import denotation.EmissionSet using (EmissionSet; Den; Ev; hot; enter; out; end; at-out; on-out; at-end; _≺_; _≼_; After; Few; Truncate; Work;
  Rejoin; shown; heard; ended; late; module Op; module Values; module Bounded)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd; ≼-split)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end-row)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Nth using (module Nths)
open import simultaneous.LaneLayers using (under-refl; under-⊕; under-≺; join-few)
open import simultaneous.ConcatTwo using (starts₀)
open import denotation.Laws.Truth using (instant-⊕)

-- A one-value `of`'s rows: its value, then its end.
data R1 {B : Set} (x : B) (s : Pos) : Pos → Ev B → Set where
  o1 : R1 x s (s ⊕ [ ix 0 ]) (out x)
  e1 : R1 x s (s ⊕ [ last ]) end

r1 : ∀ {B} (x : B) s {y e} → enter (Op.of (x ∷ [])) s y e → R1 x s y e
r1 x s (at-out , _)        = o1
r1 x s (on-out at-end , _) = e1

-- `of [ 0 , 1 , 2 ]` read at `F`: its rows, and its values by index.
module Of3 (F : Pos) where
  O : EmissionSet ℕ
  O = enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) F

  open Values O using (Nth; first; next)
  open Nths O using (nth-val; nth-inj)

  q₀ q₁ q₂ qL : Pos
  q₀ = F ⊕ [ ix 0 ]
  q₁ = F ⊕ [ ix 1 ]
  q₂ = F ⊕ [ ix 2 ]
  qL = F ⊕ [ last ]

  lt01 : q₀ ≺ q₁
  lt01 = ix-asc F (s≤s z≤n)

  lt12 : q₁ ≺ q₂
  lt12 = ix-asc F (s≤s (s≤s z≤n))

  data ORow : Pos → Ev ℕ → Set where
    r₀ : ORow q₀ (out 0)
    r₁ : ORow q₁ (out 1)
    r₂ : ORow q₂ (out 2)
    rL : ORow qL end

  o-row : ∀ {y e′} → O y e′ → ORow y e′
  o-row (at-out , _)                          = r₀
  o-row (on-out at-out , _)                   = r₁
  o-row (on-out (on-out at-out) , _)          = r₂
  o-row (on-out (on-out (on-out at-end)) , _) = rL

  ob₀ : O q₀ (out 0)
  ob₀ = at-out , of-reach F 0 (0 ∷ 1 ∷ 2 ∷ []) {q₀} {out 0}

  ob₁ : O q₁ (out 1)
  ob₁ = on-out at-out , of-reach F 0 (0 ∷ 1 ∷ 2 ∷ []) {q₁} {out 1}

  ob₂ : O q₂ (out 2)
  ob₂ = on-out (on-out at-out) , of-reach F 0 (0 ∷ 1 ∷ 2 ∷ []) {q₂} {out 2}

  lo : ∀ {k b} → O k (out b) → q₀ ≼ k
  lo x with o-row x
  ... | r₀ = ≼-refl {q₀}
  ... | r₁ = ≺→≼ {q₀} {q₁} lt01
  ... | r₂ = ≺→≼ {q₀} {q₂} (≺-trans {q₀} {q₁} {q₂} lt01 lt12)

  nx₁ : ∀ {k b} → O k (out b) → q₀ ≺ k → q₁ ≼ k
  nx₁ x lt with o-row x
  ... | r₀ = ⊥-elim (≺-irrefl {q₀} lt)
  ... | r₁ = ≼-refl {q₁}
  ... | r₂ = ≺→≼ {q₁} {q₂} lt12

  nx₂ : ∀ {k b} → O k (out b) → q₁ ≺ k → q₂ ≼ k
  nx₂ x lt with o-row x
  ... | r₀ = ⊥-elim (≺-absurd {q₀} {q₁} lt01 lt)
  ... | r₁ = ⊥-elim (≺-irrefl {q₁} lt)
  ... | r₂ = ≼-refl {q₂}

  nth₀ : Nth 0 q₀ 0
  nth₀ = first ob₀ lo

  nth₁ : Nth 1 q₁ 1
  nth₁ = next nth₀ ob₁ lt01 nx₁

  nth₂ : Nth 2 q₂ 2
  nth₂ = next nth₁ ob₂ lt12 nx₂

  data NthC : ℕ → Pos → ℕ → Set where
    n₀ : NthC 0 q₀ 0
    n₁ : NthC 1 q₁ 1
    n₂ : NthC 2 q₂ 2

  nth-c : ∀ {i q a} → Nth i q a → NthC i q a
  nth-c n with o-row (nth-val n)
  ... | r₀ with nth-inj n nth₀
  ...   | refl = n₀
  nth-c n | r₁ with nth-inj n nth₁
  ...   | refl = n₁
  nth-c n | r₂ with nth-inj n nth₂
  ...   | refl = n₂

  ofin : ∀ {k e′} → O k e′ → k ∈ (q₀ ∷ q₁ ∷ q₂ ∷ qL ∷ [])
  ofin x with o-row x
  ... | r₀ = here refl
  ... | r₁ = there (here refl)
  ... | r₂ = there (there (here refl))
  ... | rL = there (there (there (here refl)))

-- THE FRAME'S FIRST LANE, a one-value `of`, ends before the second value
-- arrives, so the second lane starts at once, whatever it reads.
module Front {B : Set} (f : ℕ → Den B) (F : Pos) (x₀ : B)
             (f0→ : ∀ s {y e′} → enter (f 0) s y e′ → enter (Op.of (x₀ ∷ [])) s y e′)
             (f0← : ∀ s {y e′} → enter (Op.of (x₀ ∷ [])) s y e′ → enter (f 0) s y e′) where

  open Of3 F public
  open Bounded 1 f O

  S₀ c₀ s₁ : Pos
  S₀ = q₀ ⊕ [ ix 1 ]
  c₀ = S₀ ⊕ [ last ]
  s₁ = q₁ ⊕ [ ix 1 ]

  c₀q₁ : c₀ ≺ q₁
  c₀q₁ = under-≺ F (s≤s z≤n) (under-⊕ (under-⊕ (under-refl q₀) (ix 1)) last)

  ------------------------------------------------------------------------
  -- The first lane

  end₀ : After (f 0) S₀ c₀ end
  end₀ = f0← S₀ (of-end-row S₀ 0 (x₀ ∷ []) , of-reach S₀ 0 (x₀ ∷ []) {c₀} {end}) , ≺-ext S₀ []

  ends₀ : Ends 0 [] c₀
  ends₀ = q₀ , 0 , S₀ , nth₀ , room (s≤s z≤n) , end₀

  end-of₀ : ∀ {c} → Ends 0 [] c → c ≡ c₀
  end-of₀ (_ , _ , _ , n , st , (r , _)) with nth-c n
  ... | n₀ with starts₀ st
  ...   | refl with r1 x₀ S₀ (f0→ S₀ r)
  ...     | e1 = refl

  starts₁ : ∀ {s} → Starts 1 q₁ (Sched 1) s → s ≡ s₁
  starts₁ (room (s≤s ()))
  starts₁ (freed _ _) = refl
  starts₁ (queued {c} _ qc (inj₁ (_ , ec , refl)) _ _) = ⊥-elim (≺-absurd {c₀} {q₁} c₀q₁ (subst (q₁ ≺_) (end-of₀ ec) qc))
  starts₁ (queued _ _ (inj₂ ()) _ _)

  st₁ : Starts 1 q₁ (Sched 1) s₁
  st₁ = freed (s≤s z≤n) (inj₁ (c₀ , ends₀ , c₀q₁))

-- A ROW OF THE MIDDLE LANE, BUT ITS END, IS THE MERGE'S (`Mid.row`), its
-- rows before it few: the first lane's are two, the middle's its own, and
-- the third lane starts past some end of the middle's, so past the row.
-- Nothing is asked of the hot's end.
module Mid {B : Set} (f : ℕ → Den B) (F : Pos) (x₀ : B) (T : EmissionSet B)
           (f0→ : ∀ s {y e′} → enter (f 0) s y e′ → enter (Op.of (x₀ ∷ [])) s y e′)
           (f0← : ∀ s {y e′} → enter (Op.of (x₀ ∷ [])) s y e′ → enter (f 0) s y e′)
           (f1→ : ∀ s {y e′} → enter (f 1) s y e′ → enter (hot T) s y e′)
           (f1← : ∀ s {y e′} → enter (hot T) s y e′ → enter (f 1) s y e′)
           (rp : ∀ {y e′ c} → enter (hot T) ((F ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) y e′ → enter (hot T) ((F ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) c end → y ≼ c)
           (rf : ∀ {y e′} → enter (hot T) ((F ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) y e′ → Few (enter (hot T) ((F ⊕ [ ix 1 ]) ⊕ [ ix 1 ])) y) where

  open Front f F x₀ f0→ f0← public
  open Bounded 1 f O

  c₀q₂ : c₀ ≺ q₂
  c₀q₂ = ≺-trans {c₀} {q₁} {q₂} c₀q₁ lt12

  -- An end of the middle lane is the hot's, read.
  end-row₁ : ∀ {c} → Ends 1 (Sched 1) c → enter (hot T) s₁ c end
  end-row₁ (_ , _ , _ , n , st , (r , _)) with nth-c n
  ... | n₁ with starts₁ st
  ...   | refl = f1→ s₁ r

  -- The third lane starts past an end of the middle's.
  starts₂ : ∀ {s} → Starts 2 q₂ (Sched 2) s → Σ Pos λ c → Ends 1 (Sched 1) c × c ≺ s
  starts₂ (room (s≤s ()))
  starts₂ (freed _ (inj₁ ((c , ec , lt) , _))) = c , ec , ≺-trans {c} {q₂} {q₂ ⊕ [ ix 1 ]} lt (≺-ext q₂ [])
  starts₂ (freed _ (inj₂ (inj₁ (_ , ()))))
  starts₂ (freed _ (inj₂ (inj₂ ())))
  starts₂ (queued _ _ (inj₁ (c , ec , refl)) _ _) = c , ec , ≺-ext c []
  starts₂ (queued _ qc (inj₂ (inj₁ (_ , ec , refl))) _ _) = ⊥-elim (≺-absurd {c₀} {q₂} c₀q₂ (subst (q₂ ≺_) (end-of₀ ec) qc))
  starts₂ (queued _ _ (inj₂ (inj₂ ())) _ _)

  module _ {y e′} (r : enter (hot T) s₁ y e′) where

    kl : List Pos
    kl = (S₀ ⊕ [ ix 0 ]) ∷ c₀ ∷ proj₁ (rf r)

    lf₀ : ∀ {s k e″} → Starts 0 q₀ [] s → enter (f 0) s k e″ → k ∈ kl
    lf₀ st r′ with starts₀ st
    ... | refl with r1 x₀ S₀ (f0→ S₀ r′)
    ...   | o1 = here refl
    ...   | e1 = there (here refl)

    lanes : ∀ {q a k e″} → Lane q a k e″ → k ≺ y → k ∈ kl
    lanes (_ , _ , (n , st) , (r′ , _)) lt with nth-c n
    ... | n₀ = lf₀ st r′
    lanes (_ , _ , (n , st) , (r′ , _)) lt | n₁ with starts₁ st
    ... | refl = there (there (proj₂ (rf r) (f1→ s₁ r′) lt))
    lanes {k = k} (_ , s , (n , st) , (_ , sk)) lt | n₂ with starts₂ st
    ... | c , ec , cs = ⊥-elim (rp r (end-row₁ ec) (≺-trans {c} {s} {y} cs (≺-trans {s} {k} {y} sk lt)))

    -- Few rows before it,
    few : Few JoinT y
    few = join-few {v = y} (q₀ ∷ q₁ ∷ q₂ ∷ qL ∷ [] , λ x _ → ofin x) (kl , λ _ l lt → lanes l lt) ([] , λ ())

    -- and the row itself.
    row : s₁ ≺ y → Work e′ → Truncate JoinT y e′
    row sy wk = lane ob₁ (1 , 1 , nth₁) (1 , s₁ , (nth₁ , st₁) , (f1← s₁ r , sy)) (λ ()) wk , proj₁ few , λ x lt _ → proj₂ few x lt

module Three {B : Set} (f : ℕ → Den B) (F : Pos) (x₀ x₂ : B) (T : EmissionSet B) {e : Pos}
             (f0→ : ∀ s {y e′} → enter (f 0) s y e′ → enter (Op.of (x₀ ∷ [])) s y e′)
             (f0← : ∀ s {y e′} → enter (Op.of (x₀ ∷ [])) s y e′ → enter (f 0) s y e′)
             (f1→ : ∀ s {y e′} → enter (f 1) s y e′ → enter (hot T) s y e′)
             (f1← : ∀ s {y e′} → enter (hot T) s y e′ → enter (f 1) s y e′)
             (f2→ : ∀ s {y e′} → enter (f 2) s y e′ → enter (Op.of (x₂ ∷ [])) s y e′)
             (f2← : ∀ s {y e′} → enter (Op.of (x₂ ∷ [])) s y e′ → enter (f 2) s y e′)
             (te : T e end) (tu : ∀ {c} → T c end → c ≡ e) (tl : ∀ {y e′} → T y e′ → y ≼ e) (tf : Few T e)
             (q₂e : (F ⊕ [ ix 2 ]) ≺ e) where

  open Front f F x₀ f0→ f0← public
  open Bounded 1 f O

  -- The second lane's end, and where the third lane's value lies.
  c₁ s₂ w : Pos
  c₁ = e ⊕ [ sub s₁ ]
  s₂ = c₁ ⊕ [ ix 1 ]
  w  = s₂ ⊕ [ ix 0 ]

  ------------------------------------------------------------------------
  -- Order

  c₀q₂ : c₀ ≺ q₂
  c₀q₂ = ≺-trans {c₀} {q₁} {q₂} c₀q₁ lt12

  s₁q₂ : s₁ ≺ q₂
  s₁q₂ = under-≺ F (s≤s (s≤s z≤n)) (under-⊕ (under-refl q₁) (ix 1))

  s₁e : s₁ ≺ e
  s₁e = ≺-trans {s₁} {q₂} {e} s₁q₂ q₂e

  ec₁ : e ≺ c₁
  ec₁ = ≺-ext e []

  q₂c₁ : q₂ ≺ c₁
  q₂c₁ = ≺-trans {q₂} {e} {c₁} q₂e ec₁

  c₀c₁ : c₀ ≺ c₁
  c₀c₁ = ≺-trans {c₀} {q₂} {c₁} c₀q₂ q₂c₁

  ------------------------------------------------------------------------
  -- The second lane

  -- The hot's rows, rejoined: finitely many.
  rj : Σ (List Pos) λ ks → ∀ {k e′} → Rejoin s₁ T k e′ → k ∈ ks
  rj = (s₁ ⊕ [ last ]) ∷ L.map (_⊕ [ sub s₁ ]) (e ∷ proj₁ tf) , go
    where
      tin : ∀ {q e′} → T q e′ → q ∈ (e ∷ proj₁ tf)
      tin {q} x = [ (λ lt → there (proj₂ tf x lt)) , (λ eq → here eq) ]′ (≼-split {q} {e} (tl x))

      go : ∀ {k e′} → Rejoin s₁ T k e′ → k ∈ ((s₁ ⊕ [ last ]) ∷ L.map (_⊕ [ sub s₁ ]) (e ∷ proj₁ tf))
      go (shown x _ _) = there (∈-map⁺ (_⊕ [ sub s₁ ]) (tin x))
      go (heard x _)   = there (∈-map⁺ (_⊕ [ sub s₁ ]) (tin x))
      go (ended x _)   = there (∈-map⁺ (_⊕ [ sub s₁ ]) (tin x))
      go (late _ _)    = here refl

  end₁ : After (f 1) s₁ c₁ end
  end₁ = f1← s₁ (ended te s₁e , proj₁ rj , λ x _ _ → proj₂ rj x) , ≺-trans {s₁} {e} {c₁} s₁e ec₁

  ends₁ : Ends 1 (Sched 1) c₁
  ends₁ = q₁ , 1 , s₁ , nth₁ , st₁ , end₁

  end-of₁ : ∀ {c} → Ends 1 (Sched 1) c → c ≡ c₁
  end-of₁ (_ , _ , _ , n , st , (r , _)) with nth-c n
  ... | n₁ with starts₁ st
  ...   | refl with f1→ s₁ r
  ...     | (shown _ () _ , _)
  ...     | (ended x _ , _) = cong (_⊕ [ sub s₁ ]) (tu x)
  ...     | (late x le , _) = ⊥-elim (le (subst (s₁ ≺_) (sym (tu x)) s₁e))

  ------------------------------------------------------------------------
  -- The third lane, queued at the second's end

  starts₂ : ∀ {s} → Starts 2 q₂ (Sched 2) s → s ≡ s₂
  starts₂ (room (s≤s ()))
  starts₂ (freed _ (inj₁ ((c , ec , lt) , _))) = ⊥-elim (≺-absurd {c₁} {q₂} (subst (_≺ q₂) (end-of₁ ec) lt) q₂c₁)
  starts₂ (freed _ (inj₂ (inj₁ (_ , ()))))
  starts₂ (freed _ (inj₂ (inj₂ ())))
  starts₂ (queued _ _ (inj₁ (_ , ec , refl)) _ _) = cong (_⊕ [ ix 1 ]) (end-of₁ ec)
  starts₂ (queued _ qc (inj₂ (inj₁ (_ , ec , refl))) _ _) = ⊥-elim (≺-absurd {c₀} {q₂} c₀q₂ (subst (q₂ ≺_) (end-of₀ ec) qc))
  starts₂ (queued _ _ (inj₂ (inj₂ ())) _ _)

  st₂ : Starts 2 q₂ (Sched 2) s₂
  st₂ = queued (s≤s z≤n) q₂c₁ (inj₁ (c₁ , ends₁ , refl)) (inj₁ ((c₁ , ends₁ , ≼-refl {c₁}) , inj₁ (c₀ , ends₀ , ≺→≼ {c₀} {c₁} c₀c₁))) nk
    where
      nk : Kth (_≺ c₁) (Sched 2) 1 → ⊥
      nk (inj₁ ((c , ec , lt) , _)) = ≺-irrefl {c₁} (subst (_≺ c₁) (end-of₁ ec) lt)
      nk (inj₂ (inj₁ (_ , ())))
      nk (inj₂ (inj₂ ()))

  val₂ : After (f 2) s₂ w (out x₂)
  val₂ = f2← s₂ (at-out , of-reach s₂ 0 (x₂ ∷ []) {w} {out x₂}) , ≺-ext s₂ []

  ------------------------------------------------------------------------
  -- The merge's rows

  raw : JoinT w (out x₂)
  raw = lane ob₂ (2 , 2 , nth₂) (2 , s₂ , (nth₂ , st₂) , val₂) (λ ()) tt

  kl : List Pos
  kl = (S₀ ⊕ [ ix 0 ]) ∷ c₀ ∷ w ∷ (s₂ ⊕ [ last ]) ∷ proj₁ rj

  lf₀ : ∀ {s y e′} → Starts 0 q₀ [] s → enter (f 0) s y e′ → y ∈ kl
  lf₀ st r with starts₀ st
  ... | refl with r1 x₀ S₀ (f0→ S₀ r)
  ...   | o1 = here refl
  ...   | e1 = there (here refl)

  lf₁ : ∀ {s y e′} → Starts 1 q₁ (Sched 1) s → enter (f 1) s y e′ → y ∈ kl
  lf₁ st r with starts₁ st
  ... | refl = there (there (there (there (proj₂ rj (proj₁ (f1→ s₁ r))))))

  lf₂ : ∀ {s y e′} → Starts 2 q₂ (Sched 2) s → enter (f 2) s y e′ → y ∈ kl
  lf₂ st r with starts₂ st
  ... | refl with r1 x₂ s₂ (f2→ s₂ r)
  ...   | o1 = there (there (here refl))
  ...   | e1 = there (there (there (here refl)))

  lanes : ∀ {q a y e′} → Lane q a y e′ → y ∈ kl
  lanes (_ , _ , (n , st) , (r , _)) with nth-c n
  ... | n₀ = lf₀ st r
  ... | n₁ = lf₁ st r
  ... | n₂ = lf₂ st r

  -- Few rows before anywhere.
  few : ∀ v → Few JoinT v
  few v = join-few {v = v} (q₀ ∷ q₁ ∷ q₂ ∷ qL ∷ [] , λ x _ → ofin x) (kl , λ _ l _ → lanes l) ([] , λ ())

  row : Truncate JoinT w (out x₂)
  row = raw , proj₁ (few w) , λ x lt _ → proj₂ (few w) x lt

  e≺w : e ≺ w
  e≺w = ≺-trans {e} {c₁} {w} ec₁ (≺-trans {c₁} {s₂} {w} (≺-ext c₁ []) (≺-ext s₂ []))

  w-inst : instant w ≡ instant e
  w-inst = trans (instant-⊕ s₂ [ ix 0 ]) (trans (instant-⊕ c₁ [ ix 1 ]) (instant-⊕ e [ sub s₁ ]))
