{-# OPTIONS --guardedness #-}

-- AN ELABORATED FLATMAP'S ROWS, FORWARD.  A row is built where every row
-- before it is listed: a joiner's rows before `v` are its outer's there,
-- their first children, and its lanes' rows there (`joiner-few`); a hot
-- read's, the hot's rows read (`rejoin-all`).
--
-- THE OUTER RE-READ.  A value the shared outer shows is the trigger's one
-- lane's row (`trig-fwd`), and the real flatMap's outer reads its values
-- (`vals-fwd`): the rows before it are the hot's rows before it, and the
-- one-value lanes of those.
module simultaneous.FlatFwd where

import Data.List as L
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import denotation.Position using (Pos; _⊕_; ix; sub; last)
open import denotation.Events using (<ᵖ-part)
open import denotation.EmissionSet using (out; end; EmissionSet; Den; hot; Proper; Few; Truncate; Rejoin; shown; heard; ended; late;
  _≺_; _≼_; enter; LaneOf; at-out; module Op; module Joiner)
open import Tree using (mergeᶠ)
open import Data.Maybe using (nothing)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺-ext; ≼-or-≻; ≼-split; entered-few)
open import denotation.Laws.Worlds using (InvAt; _⊑_; ⊑-trans; ⊑-snoc⁺; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end; of-in; of-rows)
open import denotation.Laws.Count using (⊑?)
open import denotation.Laws.Shows using (few-reach)
open import simultaneous.SimPos using (apart)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; valuesOf)
open import simultaneous.FlatRows using (hot-out; of-one)
open import simultaneous.ToldRows using (sib-≺)

------------------------------------------------------------------------
-- Few before

-- Every row listed: few before any position.
all-few : ∀ {A} {X : EmissionSet A} {v} ks → (∀ {k e} → X k e → k ∈ ks) → Few X v
all-few ks h = ks , λ x _ → h x

-- A row with few before it: a row of its truncation.
trunc : ∀ {A} {X : EmissionSet A} {k e} → X k e → Few X k → Truncate X k e
trunc x F = x , few-reach F

-- A hot's rows read: the rows read, and the late end.
rejoin-rows : ∀ {A} {S : EmissionSet A} {s} ks → (∀ {q e} → S q e → q ∈ ks) → ∀ {k e} → Rejoin s (Proper S) k e
            → k ∈ (L.map (_⊕ [ sub s ]) ks ++ [ s ⊕ [ last ] ])
rejoin-rows {s = s} ks h (shown r _ _) = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub s ]) (h (proj₁ r)))
rejoin-rows {s = s} ks h (heard r _)   = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub s ]) (h (proj₁ r)))
rejoin-rows {s = s} ks h (ended r _)   = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub s ]) (h (proj₁ r)))
rejoin-rows {s = s} ks h (late _ _)    = ∈-++⁺ʳ (L.map (_⊕ [ sub s ]) ks) (here refl)

-- Two rows of a flat set, under ordered positions: in order, or one.
read-≺ : ∀ {X} {S : EmissionSet X} → (∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥) → ∀ {r k e e′} → S r e → S k e′
       → ∀ {u w} → r ⊑ u → k ⊑ w → u ≺ w → r ≺ k ⊎ r ≡ k
read-≺ fl {r} {k} sr sk (σ , refl) (σ′ , refl) lt with ≼-or-≻ r k
... | inj₁ rk = ≼-split {r} {k} rk
... | inj₂ kr with ⊑? k r
...   | yes ([] , eq)       = ⊥-elim (≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) kr))
...   | yes (z ∷ zs , refl) = ⊥-elim (fl sk sr)
...   | no nk               = ⊥-elim (≺-absurd {r ⊕ σ} {k ⊕ σ′} lt (apart kr nk σ′ σ))

-- A value row of a lawful reading lies at or before its end.
proper-out : ∀ {A H p} {X : EmissionSet A} → InvAt H p X → ∀ {k a} → X k (out a) → ∀ {c} → X c end → k ≼ c
proper-out I x ce ck with InvAt.quiet I ce x ck
... | _ , () , _

------------------------------------------------------------------------
-- A joiner's rows before a position

module JoinFew {A B : Set} (f : A → Den B) (o : EmissionSet A) (R : Pos → Set) (C : Pos → Pos → Set) where
  open Joiner f o R C public

  -- Before `v`: the outer's rows there, their first children, and the
  -- lanes' rows there.
  joiner-few : ∀ {v} os → (∀ {q e} → o q e → q ≺ v → q ∈ os) → ∀ ls → (∀ {q a k e} → o q (out a) → LaneOf f q a k e → k ≺ v → k ∈ ls)
             → Few JoinT v
  joiner-few {v} os ho ls hl = os ++ (L.map (_⊕ [ ix 0 ]) os ++ ls) , pick
    where
      inO : ∀ {q e} → o q e → q ≺ v → q ∈ os ++ (L.map (_⊕ [ ix 0 ]) os ++ ls)
      inO x lt = ∈-++⁺ˡ (ho x lt)

      inL : ∀ {q a k e} → o q (out a) → LaneOf f q a k e → k ≺ v → k ∈ os ++ (L.map (_⊕ [ ix 0 ]) os ++ ls)
      inL x l lt = ∈-++⁺ʳ os (∈-++⁺ʳ (L.map (_⊕ [ ix 0 ]) os) (hl x l lt))

      pick : ∀ {k e} → JoinT k e → k ≺ v → k ∈ os ++ (L.map (_⊕ [ ix 0 ]) os ++ ls)
      pick (val {q} x) lt =
        ∈-++⁺ʳ os (∈-++⁺ˡ (∈-map⁺ (_⊕ [ ix 0 ]) (ho x (≺-trans {q} {q ⊕ [ ix 0 ]} {v} (≺-ext q []) lt))))
      pick (step x)            lt = inO x lt
      pick (opin x)            lt = inO x lt
      pick (oend x _)          lt = inO x lt
      pick (opass x _)         lt = inO x lt
      pick (lane x _ l _ _)    lt = inL x l lt
      pick (lend x _ l _ _ _)  lt = inL x l lt
      pick (lpass x _ l _ _ _) lt = inL x l lt
      pick (hand _ _ _ _ ())   _
      pick (left x _ l _ _)    lt = inL x l lt
      pick (run () _)          _
      pick (rend () _ _)       _
      pick (rpass () _ _)      _
      pick (rhand () _)        _

------------------------------------------------------------------------
-- The outer re-read

-- The trigger's one row, read.
trig-row : ∀ z s → s ≺ (z ⊕ [ ix 0 ]) → enter (hot (Proper (enter (Op.of (tt ∷ [])) z))) s ((z ⊕ [ ix 0 ]) ⊕ [ sub s ]) (out tt)
trig-row z s sz =
  trunc (shown ((at-out , of-reach z 0 (tt ∷ []) {z ⊕ [ ix 0 ]} {out tt}) , (λ {c} → prop {c})) tt sz)
        (all-few (L.map (_⊕ [ sub s ]) (of-rows z 0 (tt ∷ [])) ++ [ s ⊕ [ last ] ])
                 (rejoin-rows (of-rows z 0 (tt ∷ [])) (λ r → of-in z 0 (tt ∷ []) (proj₁ r))))
  where
    prop : ∀ {c} → enter (Op.of (tt ∷ [])) z c end → (z ⊕ [ ix 0 ]) ≼ c
    prop (r , _) with of-end z 0 (tt ∷ []) r
    ... | refl = λ lt → ≺-absurd {z ⊕ [ ix 0 ]} {z ⊕ [ last ]} (Equivalence.from T-≡ (<ᵖ-part z [] [] refl)) lt

-- A row of the shared outer, at its foot: a lane of the trigger's one row.
trig-fwd : ∀ {X : Set} (D : Den X) z s {k′ x} → s ≺ (z ⊕ [ ix 0 ])
         → enter D (((z ⊕ [ ix 0 ]) ⊕ [ sub s ]) ⊕ [ ix 1 ]) k′ (out x) → (((z ⊕ [ ix 0 ]) ⊕ [ sub s ]) ⊕ [ ix 1 ]) ≺ k′
         → enter (Op.flatMap (mergeᶠ nothing) (λ _ → D) (hot (Proper (enter (Op.of (tt ∷ [])) z)))) s k′ (out x)
trig-fwd {X} D z s {k′} sz r lt =
  trunc (J.lane (trig-row z s sz) tt (r , lt) (λ ()) tt)
        (J.joiner-few os (λ x _ → rejoin-rows (of-rows z 0 (tt ∷ [])) (λ r′ → of-in z 0 (tt ∷ []) (proj₁ r′)) (proj₁ x))
                      (proj₁ F) lanes)
  where
    σz = enter (Op.of (tt ∷ [])) z
    o = enter (hot (Proper σz)) s
    module J = JoinFew (λ _ → D) o (λ _ → ⊤) (λ _ _ → ⊥)
    os = L.map (_⊕ [ sub s ]) (of-rows z 0 (tt ∷ [])) ++ [ s ⊕ [ last ] ]
    F = entered-few D (((z ⊕ [ ix 0 ]) ⊕ [ sub s ]) ⊕ [ ix 1 ]) (λ {k} {e′} → tt) r

    lanes : ∀ {q a k e} → o q (out a) → LaneOf (λ _ → D) q a k e → k ≺ k′ → k ∈ proj₁ F
    lanes x l kk with hot-out x
    ... | _ , ((tr , _) , _) , _ , refl with of-one z tt tr
    ...   | refl , _ = proj₂ F (proj₁ l) kk

-- A one-value-at-most lane's rows: its value's, or its end.
lane-two : ∀ {N X : Set} (y : InstEmit N X) w {k e} → enter (Op.of (valuesOf y)) w k e → k ≡ w ⊕ [ ix 0 ] ⊎ k ≡ w ⊕ [ last ]
lane-two (instEmit (value a) _) w (r , _) with of-in w 0 (a ∷ []) r
... | here refl          = inj₁ refl
... | there (here refl)  = inj₂ refl
... | there (there ())
lane-two (instEmit (mark _) _) w (r , _) with of-in w 0 [] r
... | here refl = inj₂ refl
... | there ()

-- The lanes' rows of the outer rows at `qs`, read at `z`.
lanes : Pos → List Pos → List Pos
lanes z []       = []
lanes z (q ∷ qs) = (((q ⊕ [ sub z ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ∷ (((q ⊕ [ sub z ]) ⊕ [ ix 1 ]) ⊕ [ last ]) ∷ lanes z qs

lanes-∈ : ∀ z {q qs k} → q ∈ qs → k ≡ ((q ⊕ [ sub z ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] ⊎ k ≡ ((q ⊕ [ sub z ]) ⊕ [ ix 1 ]) ⊕ [ last ]
        → k ∈ lanes z qs
lanes-∈ z (here refl) (inj₁ refl) = here refl
lanes-∈ z (here refl) (inj₂ refl) = there (here refl)
lanes-∈ z (there m)   h           = there (there (lanes-∈ z m h))

⊑³ : ∀ x {a b c} → x ⊑ (((x ⊕ [ a ]) ⊕ [ b ]) ⊕ [ c ])
⊑³ x {a} {b} = ⊑-trans (⊑-snoc⁺ x) (⊑-trans (⊑-snoc⁺ (x ⊕ [ a ])) (⊑-snoc⁺ ((x ⊕ [ a ]) ⊕ [ b ])))

-- Under two ordered siblings: ordered.
sib-⊑ : ∀ x {a b u v} → (x ⊕ [ a ]) ≺ (x ⊕ [ b ]) → (x ⊕ [ a ]) ⊑ u → (x ⊕ [ b ]) ⊑ v → u ≺ v
sib-⊑ x h (σ , refl) (σ′ , refl) = sib-≺ x h σ σ′

-- A value of a flat outer, proper and with few rows before it, holding
-- one value: the flatMap reading its values shows that value, read.
vals-fwd : ∀ {N X : Set} (σ : EmissionSet (InstEmit N X)) z {k′ x a} → (∀ {y e l ys e′} → σ y e → σ (y ⊕ (l ∷ ys)) e′ → ⊥)
         → σ k′ (out x) → (∀ {c} → σ c end → k′ ≼ c) → Few σ k′ → z ≺ k′ → valuesOf x ≡ a ∷ []
         → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot (Proper σ))) z (((k′ ⊕ [ sub z ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out a)
vals-fwd {N} {X} σ z {k′} {x} {a} fl sx pr F zk vs =
  trunc (J.lane orow tt lrow (λ ()) tt) (J.joiner-few OS (λ y lt → rj (⊑³ k′) (proj₁ y) lt) (lanes z qs) ln)
  where
    f : InstEmit N X → Den X
    f y = Op.of (valuesOf y)
    o = enter (hot (Proper σ)) z
    module J = JoinFew f o (λ _ → ⊤) (λ _ _ → ⊥)

    qs = k′ ∷ proj₁ F
    OS = L.map (_⊕ [ sub z ]) qs ++ [ z ⊕ [ last ] ]

    -- An outer row under a position before one over `k′`: at or before `k′`.
    at : ∀ {q e u w} → k′ ⊑ w → σ q e → q ⊑ u → u ≺ w → q ∈ qs
    at kw sq qu lt with read-≺ {S = σ} fl sq sx qu kw lt
    ... | inj₁ qk   = there (proj₂ F sq qk)
    ... | inj₂ refl = here refl

    rj : ∀ {w} → k′ ⊑ w → ∀ {q e} → Rejoin z (Proper σ) q e → q ≺ w → q ∈ OS
    rj kw (shown r _ _) lt = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub z ]) (at kw (proj₁ r) (⊑-snoc⁺ _) lt))
    rj kw (heard r _)   lt = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub z ]) (at kw (proj₁ r) (⊑-snoc⁺ _) lt))
    rj kw (ended r _)   lt = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub z ]) (at kw (proj₁ r) (⊑-snoc⁺ _) lt))
    rj kw (late _ _)    _  = ∈-++⁺ʳ (L.map (_⊕ [ sub z ]) qs) (here refl)

    orow : o (k′ ⊕ [ sub z ]) (out x)
    orow = trunc (shown (sx , (λ {c} → pr {c})) tt zk) (OS , λ r lt → rj (⊑-snoc⁺ k′) r lt)

    w = (k′ ⊕ [ sub z ]) ⊕ [ ix 1 ]

    lrow : LaneOf f (k′ ⊕ [ sub z ]) x (w ⊕ [ ix 0 ]) (out a)
    lrow = subst (λ xs → enter (Op.of xs) w (w ⊕ [ ix 0 ]) (out a)) (sym vs) (at-out , of-reach w 0 (a ∷ []) {w ⊕ [ ix 0 ]} {out a}) , ≺-ext w []

    ln : ∀ {q b k e} → o q (out b) → LaneOf f q b k e → k ≺ (w ⊕ [ ix 0 ]) → k ∈ lanes z qs
    ln {b = b} y l lt with hot-out y
    ... | q₀ , (sq , _) , _ , refl with lane-two b ((q₀ ⊕ [ sub z ]) ⊕ [ ix 1 ]) (proj₁ l)
    ...   | inj₁ refl = lanes-∈ z (at (⊑³ k′) sq (⊑³ q₀) lt) (inj₁ refl)
    ...   | inj₂ refl = lanes-∈ z (at (⊑³ k′) sq (⊑³ q₀) lt) (inj₂ refl)
