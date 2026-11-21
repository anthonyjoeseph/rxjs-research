{-# OPTIONS --guardedness #-}

-- A LANE'S `laneDone` FOLLOWS ITS OWN `laneStart`, both past its
-- subscription (`lane-starts`).  Read down, the `laneDone` is the lane
-- part's: its frame's second or third piece, scheduled after the first,
-- whose mark is the `laneStart`.  Read back up, that mark is a row of every
-- layer, each with finitely many rows before it because the `laneDone`'s
-- row in that layer, later, has; only the scan's one-value split is read
-- whole, its rows being few.
module simultaneous.LaneStart where

open import Data.Bool using (true; false; T; not; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; Label; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; ofᴱ; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; Proper; InE; at-out; on-out; at-end; _≺_; _≼_;
  module Op; module Joining; module Values; module Bounded; module Merge; module Scan;
  module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds using (⊕-assoc; ⊕-identityʳ; notT)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-idx)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Count using (reach-down)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (conn-out; merge-out; scan-out; bounded-out; hot-out; each-one; of-mem)
open import simultaneous.LaneEndSched using (ls-one; ls-true; of-one)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; laneDone)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; laneˢ; laneSrc; laneStep; undone; marked; piece)

------------------------------------------------------------------------
-- Positions below a position

Under : Pos → Pos → Set
Under x y = Σ (List Label) λ ys → y ≡ x ⊕ ys

under-refl : ∀ x → Under x x
under-refl x = [] , sym (⊕-identityʳ x)

under-⊕ : ∀ {x y} → Under x y → ∀ l → Under x (y ⊕ [ l ])
under-⊕ {x} (ys , refl) l = ys ++ [ l ] , ⊕-assoc x ys [ l ]

under-trans : ∀ {x y z} → Under x y → Under y z → Under x z
under-trans {x} (ys , refl) (zs , refl) = ys ++ zs , ⊕-assoc x ys zs

-- A position below a child lies past its parent,
under-ext : ∀ x {l y} → Under (x ⊕ [ l ]) y → x ≺ y
under-ext x {l} (ys , refl) = subst (x ≺_) (sym (⊕-assoc x [ l ] ys)) (≺-ext x ys)

-- and before every later child.
under-≺ : ∀ p {i j y} → i < j → Under (p ⊕ [ ix i ]) y → y ≺ (p ⊕ [ ix j ])
under-≺ p {i} {j} lt (ys , refl) = subst (_≺ (p ⊕ [ ix j ])) (sym (⊕-assoc p [ ix i ] ys)) (Equivalence.from T-≡ (<ᵖ-part p ys [] (ix-< lt)))

------------------------------------------------------------------------
-- The lane, as layers of operators over its children

z₀ : ∀ {B} → Routes × (List (IE B) × List (IE B))
z₀ = (root , 0) , ([] , [])

module Core {B : Set} (SH : Part → Den ⊤ → Den (IE B)) (PC : Part → ℕ → Den ⊤ → Den (IE B) → Den (IE B))
  -- The lane part's first piece shows its mark at its first child,
  (pc0    : ∀ h h′ s → enter (PC lanePart 0 h h′) s (s ⊕ [ ix 0 ]) (out (marked laneStart)))
  -- and either part's shows only there, and ends no lane.
  (pc0-at : ∀ k h h′ s {y a} → enter (PC k 0 h h′) s y (out a) → y ≡ s ⊕ [ ix 0 ] × T (undone a))
  -- The second piece reads the share.
  (pc1    : ∀ k h h′ s {y a} → enter (PC k 1 h h′) s y (out a) → enter h′ s y (out a))
  -- The burst part's third piece shows nothing,
  (pc2    : ∀ h h′ s {y a} → enter (PC burstPart 2 h h′) s y (out a) → ⊥)
  -- nor does its share.
  (sh-b   : ∀ h p {y a} → enter (SH burstPart h) p y (out a) → ⊥) where

  ls : IE B
  ls = marked laneStart

  Inner : Routes × (List (IE B) × List (IE B)) → Den (IE B)
  Inner y = Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (Op.of (true ∷ false ∷ []))

  Fr : Part → Den ⊤ → Den (IE B) → Den (IE B)
  Fr k h h′ = Op.flatMap (mergeᶠ (just 1)) (λ j → PC k j h h′) (Op.of (0 ∷ 1 ∷ 2 ∷ []))

  Sc : Part → Den ⊤ → Den (IE B) → Den (Routes × (List (IE B) × List (IE B)))
  Sc k h h′ = Op.scan laneStep z₀ (Fr k h h′)

  Ct : Part → Den ⊤ → Den (IE B) → Den (IE B)
  Ct k h h′ = Op.flatMap (mergeᶠ nothing) Inner (Sc k h h′)

  Sv : Part → Den (IE B)
  Sv k = Op.connect Op.empty (λ h → Op.connect (SH k h) (λ h′ → Ct k h h′))

  MM : Den (IE B)
  MM = Op.flatMap (mergeᶠ nothing) Sv (Op.of (lanePart ∷ burstPart ∷ []))

  LaneD : Den (IE B)
  LaneD = Op.takeWhile true undone MM

  -- A part's lane, its connect at `P`.
  H₁ : Pos → Den ⊤
  H₁ P = hot (Proper (enter Op.empty (P ⊕ [ ix 1 ])))

  H₂ : Pos → Part → Den (IE B)
  H₂ P k = hot (Proper (enter (SH k (H₁ P)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])))

  Bp : Pos → Pos
  Bp P = (P ⊕ [ ix 0 ]) ⊕ [ ix 0 ]

  mid-out : ∀ k P {y a} → enter (Sv k) P y (out a) → enter (Op.connect (SH k (H₁ P)) (λ h′ → Ct k (H₁ P) h′)) (P ⊕ [ ix 0 ]) y (out a)
  mid-out k P r = conn-out Op.empty (λ h → Op.connect (SH k h) (λ h′ → Ct k h h′)) P r

  sv-out : ∀ k P {y a} → enter (Sv k) P y (out a) → enter (Ct k (H₁ P) (H₂ P k)) (Bp P) y (out a)
  sv-out k P r = conn-out (SH k (H₁ P)) (λ h′ → Ct k (H₁ P) h′) (P ⊕ [ ix 0 ]) (mid-out k P r)

  sv-in : ∀ k P {y a y₂ a₂} → enter (Sv k) P y₂ (out a₂) → y ≺ y₂ → enter (Ct k (H₁ P) (H₂ P k)) (Bp P) y (out a) → enter (Sv k) P y (out a)
  sv-in k P {y} {a} {y₂} {a₂} r₂ lt c =
      Connecting.body (Connecting.body c , reach-down {q = y₂} {w = y} {e = out a₂} {e₁ = out a} (proj₂ (mid-out k P r₂)) lt tt)
    , reach-down {q = y₂} {w = y} {e = out a₂} {e₁ = out a} (proj₂ r₂) lt tt

  ----------------------------------------------------------------------
  -- The frame's schedule

  -- A lane starts past its value.
  starts-after : ∀ {A} {n : ℕ} {f : A → Den (IE B)} {o : EmissionSet A} {i q ls′ s} → Bounded.Starts n f o i q ls′ s → q ≺ s
  starts-after {q = q} (Bounded.room _)                    = ≺-ext q []
  starts-after {q = q} (Bounded.freed _ _)                 = ≺-ext q []
  starts-after {q = q} (Bounded.queued {c} _ qc _ _ _)     = ≺-trans {q} {c} {c ⊕ [ ix 1 ]} qc (≺-ext c [])

  module Frame (k : Part) (h : Den ⊤) (h′ : Den (IE B)) (P : Pos) where
    O : EmissionSet ℕ
    O = enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P

    f : ℕ → Den (IE B)
    f j = PC k j h h′

    module Bd = Bounded 1 f O
    open Values O using (Nth)

    ob₀ : O (P ⊕ [ ix 0 ]) (out 0)
    ob₀ = at-out , of-reach P 0 (0 ∷ 1 ∷ 2 ∷ []) {P ⊕ [ ix 0 ]} {out 0}

    ob-min : ∀ {q b} → O q (out b) → (P ⊕ [ ix 0 ]) ≼ q
    ob-min (at-out , _)                         = ≼-refl {P ⊕ [ ix 0 ]}
    ob-min (on-out at-out , _)                  = ≺→≼ {P ⊕ [ ix 0 ]} {P ⊕ [ ix 1 ]} (ix-asc P (s≤s z≤n))
    ob-min (on-out (on-out at-out) , _)         = ≺→≼ {P ⊕ [ ix 0 ]} {P ⊕ [ ix 2 ]} (ix-asc P (s≤s z≤n))
    ob-min (on-out (on-out (on-out ())) , _)

    nth₀ : Nth 0 (P ⊕ [ ix 0 ]) 0
    nth₀ = Values.first ob₀ ob-min

    S₀ : Pos
    S₀ = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

    sb₀ : Bd.Sub 0 (P ⊕ [ ix 0 ]) S₀ 0
    sb₀ = nth₀ , Bd.room (s≤s z≤n)

    -- No value precedes the first.
    nth-o : ∀ {i q a} → Nth i q a → O q (out a)
    nth-o (Values.first x _)    = x
    nth-o (Values.next _ x _ _) = x

    before-0 : ∀ {q a} → O q (out a) → q ≺ (P ⊕ [ ix 0 ]) → ⊥
    before-0 (at-out , _)                 lt = ≺-irrefl {P ⊕ [ ix 0 ]} lt
    before-0 (on-out at-out , _)          lt = ≺-absurd {P ⊕ [ ix 1 ]} {P ⊕ [ ix 0 ]} lt (ix-asc P (s≤s z≤n))
    before-0 (on-out (on-out at-out) , _) lt = ≺-absurd {P ⊕ [ ix 2 ]} {P ⊕ [ ix 0 ]} lt (ix-asc P (s≤s z≤n))
    before-0 (on-out (on-out (on-out ())) , _) _

    nth-zero : ∀ {i a} → Nth i (P ⊕ [ ix 0 ]) a → i ≡ 0
    nth-zero (Values.first _ _)       = refl
    nth-zero (Values.next n _ lt _)   = ⊥-elim (before-0 (nth-o n) lt)

    -- The first lane starts at its value's second child.
    starts-0 : ∀ {s} → Bd.Starts 0 (P ⊕ [ ix 0 ]) [] s → s ≡ S₀
    starts-0 (Bd.room _)        = refl
    starts-0 (Bd.freed () _)
    starts-0 (Bd.queued () _ _ _ _)

    -- The first piece's mark, a row of the frame,
    V₀ : Pos
    V₀ = S₀ ⊕ [ ix 0 ]

    u-V₀ : Under (P ⊕ [ ix 0 ]) V₀
    u-V₀ = under-⊕ (under-⊕ (under-refl (P ⊕ [ ix 0 ])) (ix 1)) (ix 0)

    fr₀ : k ≡ lanePart → Bd.JoinT V₀ (out ls)
    fr₀ refl = Joining.lane ob₀ (0 , 0 , nth₀) (0 , S₀ , sb₀ , (pc0 h h′ S₀ , ≺-ext S₀ [])) (λ ()) tt

    -- precedes every other.
    fr-min : ∀ {y b} → enter (Fr k h h′) P y (out b) → V₀ ≼ y
    fr-min r with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | q , j , i , s , oq , sb , (l , sl) = go oq sb l sl
      where
        go : ∀ {q j i s y b} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out b) → s ≺ y → V₀ ≼ y
        go {i = i} {s} {y} (at-out , _) (nth , st) l _ with nth-zero nth
        ... | refl with starts-0 st
        ...   | refl with pc0-at k h h′ S₀ l
        ...     | refl , _ = ≼-refl {V₀}
        go {s = s} {y} (on-out at-out , _) (_ , st) _ sl =
          ≺→≼ {V₀} {y} (≺-trans {V₀} {P ⊕ [ ix 1 ]} {y} (under-≺ P (s≤s z≤n) u-V₀) (≺-trans {P ⊕ [ ix 1 ]} {s} {y} (starts-after st) sl))
        go {s = s} {y} (on-out (on-out at-out) , _) (_ , st) _ sl =
          ≺→≼ {V₀} {y} (≺-trans {V₀} {P ⊕ [ ix 2 ]} {y} (under-≺ P (s≤s z≤n) u-V₀) (≺-trans {P ⊕ [ ix 2 ]} {s} {y} (starts-after st) sl))
        go (on-out (on-out (on-out ())) , _) _ _ _

    -- What ends a lane in the frame is the lane part's second or third
    -- piece, past every position below the first value.
    fr-done : ∀ {y n} → enter (Fr k h h′) P y (out (instEmit (mark laneDone) n))
            → (k ≡ burstPart → (∀ {p y a} → enter h′ p y (out a) → ⊥)) → k ≡ lanePart × (∀ {u} → Under (P ⊕ [ ix 0 ]) u → u ≺ y)
    fr-done r hb with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P r
    ... | q , j , i , s , oq , sb , (l , sl) = go k refl oq sb l sl
      where
        go : ∀ k′ → k′ ≡ k → ∀ {q j i s y n} → O q (out j) → Bd.Sub i q s j → enter (f j) s y (out (instEmit (mark laneDone) n)) → s ≺ y
           → k ≡ lanePart × (∀ {u} → Under (P ⊕ [ ix 0 ]) u → u ≺ y)
        go _ _ {s = s} (at-out , _) _ l _ = ⊥-elim (proj₂ (pc0-at k h h′ s l))
        go lanePart refl {s = s} {y} (on-out at-out , _) (_ , st) _ sl =
          refl , λ {u} un → ≺-trans {u} {P ⊕ [ ix 1 ]} {y} (under-≺ P {0} {1} {u} (s≤s z≤n) un) (≺-trans {P ⊕ [ ix 1 ]} {s} {y} (starts-after st) sl)
        go burstPart refl {s = s} (on-out at-out , _) _ l _ = ⊥-elim (hb refl (pc1 burstPart h h′ s l))
        go lanePart refl {s = s} {y} (on-out (on-out at-out) , _) (_ , st) _ sl =
          refl , λ {u} un → ≺-trans {u} {P ⊕ [ ix 2 ]} {y} (under-≺ P {0} {2} {u} (s≤s z≤n) un) (≺-trans {P ⊕ [ ix 2 ]} {s} {y} (starts-after st) sl)
        go burstPart refl {s = s} (on-out (on-out at-out) , _) _ l _ = ⊥-elim (pc2 h h′ s l)
        go _ _ (on-out (on-out (on-out ())) , _) _ _ _

  ----------------------------------------------------------------------
  -- The scan's split

  -- What the split shows that ends a lane is what the scan read.
  pick : ∀ (y : Routes × (List (IE B) × List (IE B))) st a₀ → y ≡ laneStep st a₀ → ∀ {U w c q a}
       → InE (ofᴱ U 0 (true ∷ false ∷ [])) w (out c)
       → InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) q (out a) → T (not (undone a)) → a ≡ a₀
  pick _ st a₀ refl at-out l nu = ⊥-elim (notT _ nu (ls-true st a₀ (of-mem _ 0 _ l)))
  pick _ st a₀ refl (on-out at-out) l nu with of-one _ a₀ (subst (λ xs → InE (ofᴱ _ 0 xs) _ (out _)) (ls-one st a₀) l)
  ... | refl , refl = refl
  pick _ _ _ refl (on-out (on-out ())) _ _

  -- The split of the first piece's mark, at `U`, shows it at its second
  -- lane's first child: one of few rows.
  module Split (U : Pos) where
    W₀ E₀ : Pos
    W₀ = U ⊕ [ ix 1 ]
    E₀ = (W₀ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    ks : List Pos
    ks = ((U ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ∷ (W₀ ⊕ [ ix 0 ]) ∷ (U ⊕ [ last ]) ∷ (((U ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ last ])
       ∷ E₀ ∷ ((W₀ ⊕ [ ix 1 ]) ⊕ [ last ]) ∷ []

    Sp : EmissionSet (IE B)
    Sp = enter (Inner (laneStep z₀ ls)) U

    Raw : EmissionSet (IE B)
    Raw = Merge.JoinT (λ b → Op.of (if b then proj₁ (proj₂ (laneStep z₀ ls)) else proj₂ (proj₂ (laneStep z₀ ls)))) (enter (Op.of (true ∷ false ∷ [])) U)

    all-in : ∀ {y e} → Raw y e → y ∈ ks
    all-in (Joining.val (at-out , _))                                         = here refl
    all-in (Joining.val (on-out at-out , _))                                  = there (here refl)
    all-in (Joining.val (on-out (on-out ()) , _))
    all-in (Joining.step (on-out (on-out ()) , _))
    all-in (Joining.opin (on-out (on-out ()) , _))
    all-in (Joining.oend (on-out (on-out at-end) , _) _)                      = there (there (here refl))
    all-in (Joining.opass (on-out (on-out at-end) , _) _)                     = there (there (here refl))
    all-in (Joining.lane (at-out , _) _ ((at-end , _) , _) _ ())
    all-in (Joining.lane (on-out at-out , _) _ ((at-out , _) , _) _ _)        = there (there (there (there (here refl))))
    all-in (Joining.lane (on-out at-out , _) _ ((on-out at-end , _) , _) _ ())
    all-in (Joining.lane (on-out (on-out ()) , _) _ _ _ _)
    all-in (Joining.lend (at-out , _) _ ((at-end , _) , _) _ _ _)             = there (there (there (here refl)))
    all-in (Joining.lend (on-out at-out , _) _ ((on-out at-end , _) , _) _ _ _) = there (there (there (there (there (here refl)))))
    all-in (Joining.lend (on-out (on-out ()) , _) _ _ _ _ _)
    all-in (Joining.lpass (at-out , _) _ ((at-end , _) , _) _ _ _)            = there (there (there (here refl)))
    all-in (Joining.lpass (on-out at-out , _) _ ((on-out at-end , _) , _) _ _ _) = there (there (there (there (there (here refl)))))
    all-in (Joining.lpass (on-out (on-out ()) , _) _ _ _ _ _)
    all-in (Joining.hand _ _ _ _ ())
    all-in (Joining.left (at-out , _) _ ((() , _) , _) _ _)
    all-in (Joining.left (on-out at-out , _) _ ((on-out () , _) , _) _ _)
    all-in (Joining.left (on-out (on-out ()) , _) _ _ _ _)
    all-in (Joining.run () _)
    all-in (Joining.rend () _ _)
    all-in (Joining.rpass () _ _)
    all-in (Joining.rhand () _)

    row : Sp E₀ (out ls)
    row = Joining.lane (on-out at-out , of-reach U 0 (true ∷ false ∷ []) {W₀} {out false}) tt ((at-out , of-reach (W₀ ⊕ [ ix 1 ]) 0 (ls ∷ []) {E₀} {out ls}) , ≺-ext (W₀ ⊕ [ ix 1 ]) [])
            (λ ()) tt
        , ks , λ x _ _ → all-in x

  ----------------------------------------------------------------------
  -- Down, then up

  -- The `laneDone` a part's connect shows is the lane part's, past its
  -- frame's first piece.
  down : ∀ k P {e₂ n} → enter (Sv k) P e₂ (out (instEmit (mark laneDone) n))
       → k ≡ lanePart × Σ Pos λ v₂ → Σ _ λ yst → Σ _ λ a₂ → enter (Sc k (H₁ P) (H₂ P k)) (Bp P) v₂ (out yst)
         × enter (Fr k (H₁ P) (H₂ P k)) (Bp P) v₂ (out a₂) × (∀ {u} → Under (Bp P ⊕ [ ix 0 ]) u → u ≺ v₂) × v₂ ≺ e₂
  down k P {e₂} svr with merge-out Inner (Sc k (H₁ P) (H₂ P k)) (Bp P) (sv-out k P svr)
  ... | v₂ , yst , scr , inr , lt₁ with merge-out (λ b → Op.of (if b then proj₁ (proj₂ yst) else proj₂ (proj₂ yst))) (Op.of (true ∷ false ∷ [])) (v₂ ⊕ [ ix 1 ]) inr
  ...   | w , c , ow , ll , _ with scan-out laneStep z₀ (Fr k (H₁ P) (H₂ P k)) (Bp P) scr
  ...     | st , a₀ , fa , eq with pick yst st a₀ eq (proj₁ ow) (proj₁ ll) tt
  ...       | refl with Frame.fr-done k (H₁ P) (H₂ P k) (Bp P) fa (λ { refl r → sh-b (H₁ P) _ (proj₁ (proj₁ (proj₂ (hot-out r)))) })
  ...         | refl , vlt = refl , v₂ , yst , _ , scr , fa , vlt , ≺-trans {v₂} {v₂ ⊕ [ ix 1 ]} {e₂} (≺-ext v₂ []) lt₁

  -- The lane part's split of its first mark, a row of its connect's body.
  module Up (P : Pos) where
    open Frame lanePart (H₁ P) (H₂ P lanePart) (Bp P) using (V₀; u-V₀; fr₀; fr-min)
    open Split (V₀ ⊕ [ ix 1 ]) using (W₀; E₀; row)

    u-E₀ : Under (Bp P ⊕ [ ix 0 ]) E₀
    u-E₀ = under-⊕ (under-⊕ (under-⊕ (under-⊕ u-V₀ (ix 1)) (ix 1)) (ix 1)) (ix 0)

    u-P : Under (P ⊕ [ ix 0 ]) E₀
    u-P = under-trans (under-⊕ (under-⊕ (under-refl (P ⊕ [ ix 0 ])) (ix 0)) (ix 0)) u-E₀

    ct-in : ∀ {v₂ yst a₂ e₂ b₂} → enter (Sc lanePart (H₁ P) (H₂ P lanePart)) (Bp P) v₂ (out yst)
          → enter (Fr lanePart (H₁ P) (H₂ P lanePart)) (Bp P) v₂ (out a₂) → (∀ {u} → Under (Bp P ⊕ [ ix 0 ]) u → u ≺ v₂)
          → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) e₂ (out b₂) → v₂ ≺ e₂
          → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) E₀ (out ls)
    ct-in {v₂} {yst} {a₂} {e₂} {b₂} scr fa vlt ct v₂e₂ =
      Joining.lane (Scan.sval (Scan.acc₀ (fr₀ refl , reach-down {q = v₂} {w = V₀} {e = out a₂} {e₁ = out ls} (proj₂ fa) (vlt u-V₀) tt) fr-min)
                     , reach-down {q = v₂} {w = V₀} {e = out yst} {e₁ = out (laneStep z₀ ls)} (proj₂ scr) (vlt u-V₀) tt)
        tt (row , under-ext (V₀ ⊕ [ ix 1 ]) (under-⊕ (under-⊕ (under-refl W₀) (ix 1)) (ix 0))) (λ ()) tt
      , reach-down {q = e₂} {w = E₀} {e = out b₂} {e₁ = out ls} (proj₂ ct) (≺-trans {E₀} {v₂} {e₂} (vlt u-E₀) v₂e₂) tt

  -- A part's value is past the subscription.
  of-after : ∀ s {kq k} → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k) → s ≺ kq
  of-after s okq with of-idx s 0 (lanePart ∷ burstPart ∷ []) (proj₁ okq)
  ... | inj₁ (j , _ , refl) = ≺-ext s []
  ... | inj₂ refl           = ≺-ext s []

  -- A LANE'S `laneDone` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  core : ∀ s {y n} → enter LaneD s y (out (instEmit (mark laneDone) n))
       → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ y
  core s (TakeWhile.pass _ () _ , _)
  core s x@(TakeWhile.fail r _ nF _ , _) = split₁ s x r nF (merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s r)
    where
    split₂ : ∀ s {q n} kq k → enter LaneD s (q ⊕ [ ix 0 ]) (out (instEmit (mark laneDone) n)) → enter MM s q (out (instEmit (mark laneDone) n))
           → ¬ TakeWhile.Failed true undone (enter MM s) q → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
           → enter (Sv k) (kq ⊕ [ ix 1 ]) q (out (instEmit (mark laneDone) n))
           → (k ≡ lanePart × Σ Pos λ v₂ → Σ (Routes × (List (IE B) × List (IE B))) λ yst → Σ (IE B) λ a₂
               → enter (Sc k (H₁ (kq ⊕ [ ix 1 ])) (H₂ (kq ⊕ [ ix 1 ]) k)) (Bp (kq ⊕ [ ix 1 ])) v₂ (out yst)
               × enter (Fr k (H₁ (kq ⊕ [ ix 1 ])) (H₂ (kq ⊕ [ ix 1 ]) k)) (Bp (kq ⊕ [ ix 1 ])) v₂ (out a₂)
               × (∀ {u} → Under (Bp (kq ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) u → u ≺ v₂) × v₂ ≺ q)
           → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ (q ⊕ [ ix 0 ])

    split₁ : ∀ s {q n} → enter LaneD s (q ⊕ [ ix 0 ]) (out (instEmit (mark laneDone) n)) → enter MM s q (out (instEmit (mark laneDone) n))
           → ¬ TakeWhile.Failed true undone (enter MM s) q
           → (Σ Pos λ kq → Σ Part λ k → enter (Op.of (lanePart ∷ burstPart ∷ [])) s kq (out k)
               × enter (Sv k) (kq ⊕ [ ix 1 ]) q (out (instEmit (mark laneDone) n)) × (kq ⊕ [ ix 1 ]) ≺ q)
           → Σ Pos λ y₀ → enter LaneD s y₀ (out ls) × s ≺ y₀ × y₀ ≺ (q ⊕ [ ix 0 ])
    split₁ s x r nF (kq , k , okq , svr , _) = split₂ s kq k x r nF okq svr (down k (kq ⊕ [ ix 1 ]) svr)
    split₂ s {q} {n} kq k x r nF okq svr (refl , v₂ , yst , a₂ , scr , fa , vlt , v₂e₂) = E₀ , take₀ , s-E₀ , ≺-trans {E₀} {q} {q ⊕ [ ix 0 ]} lt₀ (≺-ext q [])
     where
      P : Pos
      P = kq ⊕ [ ix 1 ]
      open Up P using (u-E₀; u-P; ct-in)
      open Split (Frame.V₀ lanePart (H₁ P) (H₂ P lanePart) (Bp P) ⊕ [ ix 1 ]) using (E₀)

      lt₀ : E₀ ≺ q
      lt₀ = ≺-trans {E₀} {v₂} {q} (vlt u-E₀) v₂e₂

      sv₀ : enter (Sv lanePart) P E₀ (out ls)
      sv₀ = sv-in lanePart P svr lt₀ (ct-in scr fa vlt (sv-out lanePart P svr) v₂e₂)

      P-E₀ : P ≺ E₀
      P-E₀ = under-ext P u-P

      s-E₀ : s ≺ E₀
      s-E₀ = ≺-trans {s} {kq} {E₀} (of-after s okq) (under-ext kq (under-trans (under-⊕ (under-refl P) (ix 0)) u-P))

      mm₀ : enter MM s E₀ (out ls)
      mm₀ = Joining.lane okq tt (sv₀ , P-E₀) (λ ()) tt , reach-down {q = q} {w = E₀} {e = out (instEmit (mark laneDone) n)} {e₁ = out ls} (proj₂ r) lt₀ tt

      nF₀ : ¬ TakeWhile.Failed true undone (enter MM s) E₀
      nF₀ (q′ , a′ , x′ , nk′ , lt′) = nF (q′ , a′ , x′ , nk′ , ≺-trans {q′} {E₀} {q} lt′ lt₀)

      take₀ : enter LaneD s E₀ (out ls)
      take₀ = TakeWhile.pass mm₀ tt nF₀ , reach-down {q = q ⊕ [ ix 0 ]} {w = E₀} {e = out (instEmit (mark laneDone) n)} {e₁ = out ls} (proj₂ x) (≺-trans {E₀} {q} {q ⊕ [ ix 0 ]} lt₀ (≺-ext q [])) tt

------------------------------------------------------------------------
-- The lane, read at either meaning

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where

  Sh : Part → Obs Timeline (⊤ ∷ Θ) (IE B)
  Sh k = flatMap (mergeᶠ (just 1)) (laneSrc ρ′ o k) (of (true ∷ false ∷ []))

  pc0 : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s → enter (ev m (piece {B = B} lanePart 0) (h′ ∷ h ∷ ρ)) s (s ⊕ [ ix 0 ]) (out (marked laneStart))
  pc0 nothing  h h′ s = at-out , of-reach s 0 (marked laneStart ∷ []) {s ⊕ [ ix 0 ]} {out (marked laneStart)}
  pc0 (just _) h h′ s = at-out , of-reach s 0 (marked laneStart ∷ []) {s ⊕ [ ix 0 ]} {out (marked laneStart)}

  pc0-at : ∀ m k (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} k 0) (h′ ∷ h ∷ ρ)) s y (out a) → y ≡ s ⊕ [ ix 0 ] × T (undone a)
  pc0-at nothing  lanePart  h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt
  pc0-at nothing  burstPart h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt
  pc0-at (just _) lanePart  h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt
  pc0-at (just _) burstPart h h′ s (r , _) with of-one s _ r
  ... | refl , refl = refl , tt

  pc1 : ∀ m k (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} k 1) (h′ ∷ h ∷ ρ)) s y (out a) → enter h′ s y (out a)
  pc1 nothing  lanePart  h h′ s r = r
  pc1 nothing  burstPart h h′ s r = r
  pc1 (just _) lanePart  h h′ s r = r
  pc1 (just _) burstPart h h′ s r = r

  pc2 : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y a} → enter (ev m (piece {B = B} burstPart 2) (h′ ∷ h ∷ ρ)) s y (out a) → ⊥
  pc2 nothing  h h′ s (() , _)
  pc2 (just _) h h′ s (() , _)

  sh-b : ∀ m (h : Den ⊤) p {y a} → enter (ev m (Sh burstPart) (h ∷ ρ)) p y (out a) → ⊥
  sh-b m h p r with bounded-out 1 (λ c → ev m (laneSrc ρ′ o burstPart c) (h ∷ ρ)) (Op.of (true ∷ false ∷ [])) p (sh-at m r)
    where
      sh-at : ∀ m {y a} → enter (ev m (Sh burstPart) (h ∷ ρ)) p y (out a)
            → enter (Op.flatMap (mergeᶠ (just 1)) (λ c → ev m (laneSrc ρ′ o burstPart c) (h ∷ ρ)) (Op.of (true ∷ false ∷ []))) p y (out a)
      sh-at nothing  r = r
      sh-at (just _) r = r
  ... | _ , _ , _ , _ , (at-out , _) , _ , (l , _) = blk m l
    where
      blk : ∀ m {s y a} → enter (ev m (laneSrc ρ′ o burstPart true) (h ∷ ρ)) s y (out a) → ⊥
      blk nothing  {s} l with each-one (λ _ → []) h s l
      ... | _ , _ , _ , ()
      blk (just _) {s} l with each-one (λ _ → []) h s l
      ... | _ , _ , _ , ()
  ... | _ , _ , _ , _ , (on-out at-out , _) , _ , (l , _) = emp m l
    where
      emp : ∀ m {s y a} → enter (ev m (laneSrc ρ′ o burstPart false) (h ∷ ρ)) s y (out a) → ⊥
      emp nothing  (() , _)
      emp (just _) (() , _)
  ... | _ , _ , _ , _ , (on-out (on-out ()) , _) , _ , _

  module C (m : Maybe ℕ) = Core (λ k (h : Den ⊤) → ev m (Sh k) (h ∷ ρ)) (λ k j (h : Den ⊤) (h′ : Den (IE B)) → ev m (piece k j) (h′ ∷ h ∷ ρ))
    (pc0 m) (pc0-at m) (pc1 m) (pc2 m) (sh-b m)

  -- A LANE'S `laneDone` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  lane-starts : ∀ m s {y n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y (out (instEmit (mark laneDone) n))
              → Σ Pos λ y₀ → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y₀ (out (marked laneStart)) × s ≺ y₀ × y₀ ≺ y
  lane-starts nothing  s r = C.core nothing s r
  lane-starts (just n) s r = C.core (just n) s r
