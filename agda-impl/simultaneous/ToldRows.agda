{-# OPTIONS --guardedness #-}

-- THE TOLD RUN'S ROWS, against the run's.  `told x S` subscribed at `q`
-- runs `S` at `q ⊕ [ ix 1 ]` (`σ`) and reads it back through its subject
-- as the first lane of a concat at `w`, the queued `of [ x ]` second.
-- Each row of `σ` at `l` has one image at `l ⊕ δ e`: a pin the connect's
-- own copy, an end the queued lane's end, any other row the lane's copy.
-- Every other row of the told run is silent, or the queued value, and
-- lies in the subscribe instant or under a row of `σ`.
module simultaneous.ToldRows where

open import Data.Bool using (Bool; true; false; if_then_else_; T; not; _∨_)
open import Data.List using (List; []; _∷_; [_]; _++_; concat; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-concat⁺′; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Relation.Nullary.Decidable.Core using (T?)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (Obs; connect; connected; of)
open import denotation.Position using (_≟ᵖ_; _<ᵖ_; Pos; _∙_; Path; Label; ix; sub; last; _⊕_; root; inside)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Few; Reach; Truncate; Proper; Bare; Unpinned; Work; After; Ended;
  InE; at-out; at-end; on-out; Rejoin; shown; heard; ended; late; Den; hot; DenEnv; enter; approx; _≺_; _≼_; module Op; module Values;
  module Bounded; module Connecting)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; _⊑_; InvAt; inside-⊑; world-after; ok-step; ⊑-refl; ⊑-snoc; ⊑-snoc⁺;
  ⊑-trans; ⊑-≼; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ)
open import denotation.Laws.Modulus using (≺-≼-≺; ≼-≺-≺; ≺-ext; ≺-trans; ≺-irrefl; ≺-absurd; ≺→≼; ≼-refl; ≼-trans; ≼-split; ≼-or-≻; entered-few)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Shows using (few-down; few-reach)
open import denotation.Laws.Truth using (past)
open import denotation.Laws.BoundedInv using (end-uniq)
open import denotation.Laws using (inv-approx)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Listing using (Listed)
open import simultaneous.SimPos using (apart)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (concatˢ)

-- Every row listed, each with its row.
Whole : ∀ {A : Set} → EmissionSet A → Set
Whole t = Σ (List Pos) λ ks → (∀ {k e} → t k e → k ∈ ks) × (∀ {k} → k ∈ ks → Σ _ (t k))

instant-⊕ : ∀ x zs → instantOf (x ⊕ zs) ≡ instantOf x
instant-⊕ (i ∙ p) zs = refl

private
  -- Two rows of a flat set, one before the other, are apart.
  nest : ∀ {A} {S : EmissionSet A} → (∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥) → ∀ {x y e e′} → S x e → S y e′ → x ≺ y → ¬ (x ⊑ y)
  nest fl {x} sx sy xy ([] , refl) = ≺-irrefl {x} (subst (x ≺_) (⊕-identityʳ x) xy)
  nest fl sx sy xy (l ∷ ys , refl) = fl sx sy

  -- Joined at one label, the order read back.
  joined-back : ∀ x y {a} → (x ⊕ [ a ]) ≺ (y ⊕ [ a ]) → (y ≺ x → ¬ (y ⊑ x)) → x ≺ y
  joined-back x y {a} h ny with T? (x <ᵖ y)
  ... | yes xy = xy
  ... | no nxy with ≼-split {y} {x} nxy
  ...   | inj₂ refl = ⊥-elim (≺-irrefl {x ⊕ [ a ]} h)
  ...   | inj₁ yx = ⊥-elim (≺-irrefl {x ⊕ [ a ]} (≺-trans {x ⊕ [ a ]} {y ⊕ [ a ]} {x ⊕ [ a ]} h (apart yx (ny yx) [ a ] [ a ])))

-- Before a joined row, the joined rows before its row, and the late end.
rejoin-few : ∀ {A} {S : EmissionSet A} {j q e} → (∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥) → S q e → Few S q
           → Few (Rejoin j (Proper S)) (q ⊕ [ sub j ])
rejoin-few {S = S} {j} {q} fl sq (ks , F) = L.map (_⊕ [ sub j ]) ks ++ [ j ⊕ [ last ] ] , pick
  where
    apt : ∀ {q′ e′} → S q′ e′ → q ≺ q′ → ¬ (q ⊑ q′)
    apt r qq le = nest {S = S} fl sq r qq le

    pick : ∀ {k e′} → Rejoin j (Proper S) k e′ → k ≺ (q ⊕ [ sub j ]) → k ∈ L.map (_⊕ [ sub j ]) ks ++ [ j ⊕ [ last ] ]
    pick (shown {q′} r _ _) h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (joined-back q′ q h (apt (proj₁ r)))))
    pick (heard {q′} r _)   h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (joined-back q′ q h (apt (proj₁ r)))))
    pick (ended {q′} r _)   h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (joined-back q′ q h (apt (proj₁ r)))))
    pick (late _ _)         _ = ∈-++⁺ʳ (L.map (_⊕ [ sub j ]) ks) (here refl)

-- A run read through its own subject by a concat queueing one more row.
told : ∀ {Γ Y} → Y → Obs Timeline Γ Y → Obs Timeline Γ Y
told x s = connect s (concatˢ (connected (here refl)) (of (x ∷ [])))

-- Under two siblings, the earlier's subtree lies first.
sib-≺ : ∀ x {a b} → (x ⊕ [ a ]) ≺ (x ⊕ [ b ]) → ∀ ys zs → ((x ⊕ [ a ]) ⊕ ys) ≺ ((x ⊕ [ b ]) ⊕ zs)
sib-≺ x {a} {b} h = apart h np
  where
    np : ¬ ((x ⊕ [ a ]) ⊑ (x ⊕ [ b ]))
    np pr with ⊑-snoc x pr
    ... | inj₁ le = ⊑-≼ {x ⊕ [ a ]} {x} le (≺-ext x [])
    ... | inj₂ eq = ≺-irrefl {x ⊕ [ a ]} (subst ((x ⊕ [ a ]) ≺_) (sym eq) h)

module Told {Γ Y} n (S : Obs Timeline Γ Y) (x : Y) (env : DenEnv Γ) (genv : GoodEnv env) (q : Pos) (ok : Ok (Hots env) q) where

  σ : EmissionSet Y
  σ = enter (approx n S env) (q ⊕ [ ix 1 ])

  τ : EmissionSet Y
  τ = enter (approx n (told x S) env) q

  -- The told run's source and body subscriptions.
  r : Pos
  r = q ⊕ [ ix 1 ]

  Q0 : Pos
  Q0 = q ⊕ [ ix 0 ]

  -- The first lane's subscription: the concat's first value's second child.
  w : Pos
  w = (Q0 ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

  -- Where a row of `σ` shows again.
  δ : Ev Y → Path
  δ (out _) = [ sub w ]
  δ skip    = [ sub w ]
  δ (pin _) = [ ix 0 ]
  δ end     = sub w ∷ ix 1 ∷ last ∷ []

  -- A row and its image: the same, a pin pinned by its own connect or,
  -- in the subscribe burst, by the told connect.
  data Told : Ev Y → Ev Y → Set where
    t-out  : ∀ {a} → Told (out a) (out a)
    t-skip : Told skip skip
    t-end  : Told end end
    t-pin  : ∀ {r r′} → r′ ≡ r ⊎ r′ ≡ q → Told (pin r) (pin r′)

  -- `σ`'s invariant, at the told run's second child.
  invσ : InvAt (Hots env) (q ⊕ [ ix 1 ]) σ
  invσ = inv-approx n S env genv (q ⊕ [ ix 1 ]) (ok-step q ok)

  ------------------------------------------------------------------------
  -- The told run, unfolded

  -- The concat's outer, its lanes, and the connect over them.
  O : EmissionSet Bool
  O = enter (Op.of (true ∷ false ∷ [])) Q0

  Lanes : Bool → Den Y
  Lanes b = approx n (if b then connected (here refl) else of (x ∷ [])) (hot (Proper σ) ∷ env)

  module V = Values O
  module Bd = Bounded 1 Lanes O

  β : EmissionSet Y
  β = Truncate Bd.JoinT

  module Cn = Connecting q σ β

  flatσ : ∀ {y e l ys e′} → σ y e → σ (y ⊕ (l ∷ ys)) e′ → ⊥
  flatσ = InvAt.flat invσ

  -- Every row of `σ` lies past its subscription.
  r≺ : ∀ {k e} → σ k e → r ≺ k
  r≺ y = world-after (InvAt.world invσ y) (InvAt.real invσ y)

  -- The concat's subtree lies before the source's.
  q0≺r : ∀ ys → (Q0 ⊕ ys) ≺ r
  q0≺r ys = subst ((Q0 ⊕ ys) ≺_) (⊕-identityʳ r) (sib-≺ q {ix 0} {ix 1} (ix-asc q (s≤s z≤n)) ys [])

  -- So before every row of `σ` and what lies under it.
  q0≺ : ∀ ys {k e m} → σ k e → k ⊑ m → (Q0 ⊕ ys) ≺ m
  q0≺ ys {k} {_} {m} y km = ≺-≼-≺ {Q0 ⊕ ys} {k} {m} (≺-trans {Q0 ⊕ ys} {r} {k} (q0≺r ys) (r≺ y)) (⊑-≼ {k} {m} km)

  w≺ : ∀ {k e} → σ k e → w ≺ k
  w≺ {k} y = subst (_≺ k) (sym (⊕-assoc Q0 [ ix 0 ] [ ix 1 ])) (q0≺ (ix 0 ∷ ix 1 ∷ []) y (⊑-refl k))

  -- The end of `σ` ends every row of it but a pin.
  proper-end : ∀ {k} → σ k end → Proper σ k end
  proper-end {k} y = y , λ y′ → subst (k ≼_) (end-uniq invσ y y′) (≼-refl {k})

  few-unp : ∀ {k e} → σ k e → Unpinned e → Few σ k
  few-unp {e = out _} y _ = entered-few (approx n S env) r (λ {_} {_} → tt) y
  few-unp {e = skip}  y _ = entered-few (approx n S env) r (λ {_} {_} → tt) y
  few-unp {e = end}   y _ = entered-few (approx n S env) r (λ {_} {_} → tt) y
  few-unp {e = pin _} y ()

  -- The outer's rows.
  data OV : Pos → Bool → Set where
    v0 : OV (Q0 ⊕ [ ix 0 ]) true
    v1 : OV (Q0 ⊕ [ ix 1 ]) false

  ov : ∀ {m a} → O m (out a) → OV m a
  ov (at-out , _)        = v0
  ov (on-out at-out , _) = v1
  ov (on-out (on-out ()) , _)

  o-mem : ∀ {k e} → InE (ofᴱ Q0 0 (true ∷ false ∷ [])) k e → k ∈ (Q0 ⊕ [ ix 0 ]) ∷ (Q0 ⊕ [ ix 1 ]) ∷ (Q0 ⊕ [ last ]) ∷ []
  o-mem at-out                   = here refl
  o-mem (on-out at-out)          = there (here refl)
  o-mem (on-out (on-out at-end)) = there (there (here refl))

  o-reach : ∀ {m e} → Reach (InE (ofᴱ Q0 0 (true ∷ false ∷ []))) m e
  o-reach = _ , λ y _ _ → o-mem y

  o0 : O (Q0 ⊕ [ ix 0 ]) (out true)
  o0 = at-out , o-reach {Q0 ⊕ [ ix 0 ]} {out true}

  o1 : O (Q0 ⊕ [ ix 1 ]) (out false)
  o1 = on-out at-out , o-reach {Q0 ⊕ [ ix 1 ]} {out false}

  oe : O (Q0 ⊕ [ last ]) end
  oe = on-out (on-out at-end) , o-reach {Q0 ⊕ [ last ]} {end}

  lt01 : (Q0 ⊕ [ ix 0 ]) ≺ (Q0 ⊕ [ ix 1 ])
  lt01 = ix-asc Q0 (s≤s z≤n)

  nth0 : V.Nth 0 (Q0 ⊕ [ ix 0 ]) true
  nth0 = V.first o0 λ o → first-le (ov o)
    where
      first-le : ∀ {k b} → OV k b → (Q0 ⊕ [ ix 0 ]) ≼ k
      first-le v0 = ≼-refl {Q0 ⊕ [ ix 0 ]}
      first-le v1 = ≺→≼ {Q0 ⊕ [ ix 0 ]} {Q0 ⊕ [ ix 1 ]} lt01

  nth1 : V.Nth 1 (Q0 ⊕ [ ix 1 ]) false
  nth1 = V.next nth0 o1 lt01 λ o lt → next-le (ov o) lt
    where
      next-le : ∀ {k b} → OV k b → (Q0 ⊕ [ ix 0 ]) ≺ k → (Q0 ⊕ [ ix 1 ]) ≼ k
      next-le v0 lt = ⊥-elim (≺-irrefl {Q0 ⊕ [ ix 0 ]} lt)
      next-le v1 _  = ≼-refl {Q0 ⊕ [ ix 1 ]}

  -- The outer's values, in order.
  nth-inv : ∀ {i m a} → V.Nth i m a → (i ≡ 0 × m ≡ Q0 ⊕ [ ix 0 ] × a ≡ true) ⊎ (i ≡ 1 × m ≡ Q0 ⊕ [ ix 1 ] × a ≡ false)
  nth-inv (V.first o mn) with ov o
  ... | v0 = inj₁ (refl , refl , refl)
  ... | v1 = ⊥-elim (mn o0 lt01)
  nth-inv (V.next nt o lt _) with nth-inv nt | ov o
  ... | inj₁ (refl , refl , refl) | v0 = ⊥-elim (≺-irrefl {Q0 ⊕ [ ix 0 ]} lt)
  ... | inj₁ (refl , refl , refl) | v1 = inj₂ (refl , refl , refl)
  ... | inj₂ (refl , refl , refl) | v0 = ⊥-elim (≺-absurd {Q0 ⊕ [ ix 1 ]} {Q0 ⊕ [ ix 0 ]} lt lt01)
  ... | inj₂ (refl , refl , refl) | v1 = ⊥-elim (≺-irrefl {Q0 ⊕ [ ix 1 ]} lt)

  -- The first lane subscribes at once.
  starts0 : ∀ {m s} → Bd.Starts 0 m [] s → s ≡ m ⊕ [ ix 1 ]
  starts0 (Bd.room _)          = refl
  starts0 (Bd.freed () _)
  starts0 (Bd.queued () _ _ _ _)

  sub0 : Bd.Sub 0 (Q0 ⊕ [ ix 0 ]) w true
  sub0 = nth0 , Bd.room (s≤s z≤n)

  -- The first lane never ends late: `σ` ends past it.
  late-no : ∀ {c} → Proper σ c end → c ≼ w → ⊥
  late-no {c} p cw = cw (w≺ (proj₁ p))

  -- The first lane's end, `σ`'s, read through the subject.
  end0-row : ∀ {k} → σ k end → After (Lanes true) w (k ⊕ [ sub w ]) end
  end0-row {k} y = (ended (proper-end y) (w≺ y) , few-reach {t = Rejoin w (Proper σ)} {k ⊕ [ sub w ]} {end} (rejoin-few flatσ y (few-unp y tt))) , ≺-trans {w} {k} {k ⊕ [ sub w ]} (w≺ y) (≺-ext k [])

  -- Where the first lane ends.
  end0 : ∀ {c} → Bd.Ends 0 [] c → Σ Pos λ k → Proper σ k end × c ≡ k ⊕ [ sub w ]
  end0 (_ , _ , _ , nt , st , aft) with nth-inv nt
  ... | inj₂ (() , _)
  ... | inj₁ (refl , refl , refl) with starts0 st
  ...   | refl with aft
  ...     | (ended p _ , _) , _ = _ , p , refl
  ...     | (late p cw , _) , _ = ⊥-elim (late-no p cw)

  ends0 : ∀ {k} → σ k end → Bd.Ends 0 [] (k ⊕ [ sub w ])
  ends0 y = Q0 ⊕ [ ix 0 ] , true , w , nth0 , Bd.room (s≤s z≤n) , end0-row y

  kth0 : ∀ {P} → Bd.Kth P (Bd.Sched 1) 0 → Σ Pos λ c → Bd.Ends 0 [] c × P c
  kth0 (inj₁ k) = k
  kth0 (inj₂ ())

  -- The second lane is never free at its value: the first ends past it.
  no-freed : Bd.Kth (_≺ (Q0 ⊕ [ ix 1 ])) (Bd.Sched 1) 0 → ⊥
  no-freed kk with kth0 kk
  ... | c , e0 , lt with end0 e0
  ...   | k , p , refl = ≺-absurd {k ⊕ [ sub w ]} {Q0 ⊕ [ ix 1 ]} lt (q0≺ [ ix 1 ] (proj₁ p) (⊑-snoc⁺ k))

  -- The second lane starts where the first ends.
  start1 : ∀ {k} → σ k end → Bd.Starts 1 (Q0 ⊕ [ ix 1 ]) (Bd.Sched 1) ((k ⊕ [ sub w ]) ⊕ [ ix 1 ])
  start1 {k} y = Bd.queued (s≤s z≤n) (q0≺ [ ix 1 ] y (⊑-snoc⁺ k)) (inj₁ (_ , ends0 y , refl)) (inj₁ (_ , ends0 y , ≼-refl {k ⊕ [ sub w ]})) none
    where
      none : ¬ Bd.Kth (_≺ (k ⊕ [ sub w ])) (Bd.Sched 1) 0
      none kk with kth0 kk
      ... | c , e0 , lt with end0 e0
      ...   | k′ , p , refl with end-uniq invσ y (proj₁ p)
      ...     | refl = ≺-irrefl {k ⊕ [ sub w ]} lt

  starts1 : ∀ {s} → Bd.Starts 1 (Q0 ⊕ [ ix 1 ]) (Bd.Sched 1) s → Σ Pos λ k → Proper σ k end × s ≡ (k ⊕ [ sub w ]) ⊕ [ ix 1 ]
  starts1 (Bd.room (s≤s ()))
  starts1 (Bd.freed _ kk) = ⊥-elim (no-freed kk)
  starts1 (Bd.queued _ _ kk _ _) with kth0 kk
  ... | _ , e0 , refl with end0 e0
  ...   | k , p , refl = k , p , refl

  -- The first lane's end hands its place to the second.
  hand0 : ∀ {k} → σ k end → Bd.Queued (k ⊕ [ sub w ])
  hand0 y = 1 , Q0 ⊕ [ ix 1 ] , false , nth1 , start1 y

  of1-mem : ∀ s {k e} → InE (ofᴱ s 0 (x ∷ [])) k e → k ∈ (s ⊕ [ ix 0 ]) ∷ (s ⊕ [ last ]) ∷ []
  of1-mem s at-out          = here refl
  of1-mem s (on-out at-end) = there (here refl)

  of1-reach : ∀ s {m e} → Reach (InE (ofᴱ s 0 (x ∷ []))) m e
  of1-reach s = _ , λ y _ _ → of1-mem s y

  -- The told run's end: the second lane's, with nothing left running.
  c₁ : Pos → Pos
  c₁ k = ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ last ]

  under-c₁ : ∀ k → k ⊑ c₁ k
  under-c₁ k = sub w ∷ ix 1 ∷ last ∷ [] , trans (⊕-assoc (k ⊕ [ sub w ]) [ ix 1 ] [ last ]) (⊕-assoc k [ sub w ] (ix 1 ∷ last ∷ []))

  end1-row : ∀ {k} → After (Lanes false) ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) (c₁ k) end
  end1-row {k} = (on-out at-end , of1-reach ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) {c₁ k} {end}) , ≺-ext ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) []

  done1 : ∀ {k} → σ k end → Bd.Done (c₁ k)
  done1 {k} y = (Q0 ⊕ [ last ] , oe , ≺→≼ {Q0 ⊕ [ last ]} {c₁ k} (q0≺ [ last ] y (under-c₁ k))) , λ o _ _ _ → ended-by (ov o)
    where
      c0≺ : (k ⊕ [ sub w ]) ≺ c₁ k
      c0≺ = ≺-trans {k ⊕ [ sub w ]} {(k ⊕ [ sub w ]) ⊕ [ ix 1 ]} {c₁ k} (≺-ext (k ⊕ [ sub w ]) []) (≺-ext ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) [])

      ended-by : ∀ {m a} → OV m a → Ended (Bd.Lane m a) (c₁ k)
      ended-by v0 = k ⊕ [ sub w ] , (0 , w , sub0 , end0-row y) , ≺→≼ {k ⊕ [ sub w ]} {c₁ k} c0≺
      ended-by v1 = c₁ k , (1 , _ , (nth1 , start1 y) , end1-row) , ≼-refl {c₁ k}

  -- Where a lane ends.
  data LEnd : Pos → Set where
    le0 : ∀ {k} → Proper σ k end → LEnd (k ⊕ [ sub w ])
    le1 : ∀ {k} → σ k end → LEnd (c₁ k)

  lane-end : ∀ {i m s a c} → Bd.Sub i m s a → After (Lanes a) s c end → LEnd c
  lane-end (nt , st) aft with nth-inv nt
  ... | inj₁ (refl , refl , refl) with starts0 st
  ...   | refl with aft
  ...     | (ended p _ , _) , _ = le0 p
  ...     | (late p cw , _) , _ = ⊥-elim (late-no p cw)
  lane-end (nt , st) aft | inj₂ (refl , refl , refl) with starts1 st
  ... | k , p , refl with aft
  ...   | (on-out at-end , _) , _ = le1 (proj₁ p)

  -- The second lane's end hands to nothing.
  no-hand1 : ∀ {k} → σ k end → Bd.Queued (c₁ k) → ⊥
  no-hand1 {k} y (_ , _ , _ , nt , st) with nth-inv nt
  ... | inj₁ (refl , refl , refl) =
    ≺-irrefl {Q0 ⊕ [ ix 0 ]} (subst ((Q0 ⊕ [ ix 0 ]) ≺_) (⊕-injˡ (c₁ k) (Q0 ⊕ [ ix 0 ]) (starts0 st)) (q0≺ [ ix 0 ] y (under-c₁ k)))
  ... | inj₂ (refl , refl , refl) with starts1 st
  ...   | k′ , _ , eq with ⊕-injʳ ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) k′ (⊕-injˡ (c₁ k) (k′ ⊕ [ sub w ]) eq)
  ...     | ()

  -- No lane is over before `σ` runs.
  no-oend : Bd.Done (Q0 ⊕ [ last ]) → ⊥
  no-oend (_ , all) with all o0 (0 , true , nth0) (past Q0 0) (λ ())
  ... | c , (_ , _ , sb , aft) , cle with lane-end sb aft
  ...   | le0 {k} p = cle (q0≺ [ last ] (proj₁ p) (⊑-snoc⁺ k))
  ...   | le1 {k} y = cle (q0≺ [ last ] y (under-c₁ k))

  ------------------------------------------------------------------------
  -- The told run's rows

  data Raw : Pos → Ev Y → Set where
    r-v0    : Raw ((Q0 ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) skip
    r-v1    : Raw ((Q0 ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) skip
    r-pass  : Raw (Q0 ⊕ [ last ]) skip
    r-burst : ∀ {k e} → σ k e → T (inside r k) → Raw (k ⊕ [ ix 0 ]) (pin q)
    r-echo  : ∀ {k e} → σ k e → Cn.Alive k → Unpinned e → T (not (inside r k)) → Raw (k ⊕ [ ix 0 ]) skip
    r-kept  : ∀ {k p′} → σ k (pin p′) → Cn.Alive p′ → T (not (inside r k)) → T (inside p′ k) → Raw (k ⊕ [ ix 0 ]) (pin p′)
    r-shown : ∀ {k e} → Proper σ k e → Bare e → Raw (k ⊕ [ sub w ]) e
    r-heard : ∀ {k p′} → Proper σ k (pin p′) → Raw (k ⊕ [ sub w ]) skip
    r-hand  : ∀ {k} → σ k end → Raw ((k ⊕ [ sub w ]) ⊕ [ ix 0 ]) skip
    r-x     : ∀ {k} → σ k end → Raw (((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out x)
    r-end   : ∀ {k} → σ k end → Raw (c₁ k) end

  lane0-raw : ∀ {m e} → After (Lanes true) w m e → Work e → Raw m e
  lane0-raw ((shown p b _ , _) , _) _ = r-shown p b
  lane0-raw ((heard p _ , _) , _) _   = r-heard p
  lane0-raw ((ended _ _ , _) , _) ()
  lane0-raw ((late _ _ , _) , _) ()

  lane-raw : ∀ {i m′ s a m e} → Bd.Sub i m′ s a → After (Lanes a) s m e → Work e → Raw m e
  lane-raw (nt , st) aft wk with nth-inv nt
  ... | inj₁ (refl , refl , refl) with starts0 st
  ...   | refl = lane0-raw aft wk
  lane-raw (nt , st) aft wk | inj₂ (refl , refl , refl) with starts1 st
  ... | k , p , refl with aft
  ...   | (at-out , _) , _ = r-x (proj₁ p)
  lane-raw (nt , st) aft () | inj₂ (refl , refl , refl) | k , p , refl | (on-out at-end , _) , _

  raw-j : ∀ {m e} → Bd.JoinT m e → Raw m e
  raw-j (Bd.val o) with ov o
  ... | v0 = r-v0
  ... | v1 = r-v1
  raw-j (Bd.step (on-out (on-out ()) , _))
  raw-j (Bd.opin (on-out (on-out ()) , _))
  raw-j (Bd.oend (on-out (on-out at-end) , _) d) = ⊥-elim (no-oend d)
  raw-j (Bd.opass (on-out (on-out at-end) , _) _) = r-pass
  raw-j (Bd.lane _ _ (_ , _ , sb , aft) _ wk) = lane-raw sb aft wk
  raw-j (Bd.lend _ _ (_ , _ , sb , aft) _ nh dn) with lane-end sb aft
  ... | le0 p = ⊥-elim (nh (hand0 (proj₁ p)))
  ... | le1 y = r-end y
  raw-j (Bd.lpass _ _ (_ , _ , sb , aft) _ nh nd) with lane-end sb aft
  ... | le0 p = ⊥-elim (nh (hand0 (proj₁ p)))
  ... | le1 y = ⊥-elim (nd (done1 y))
  raw-j (Bd.hand _ _ (_ , _ , sb , aft) _ h) with lane-end sb aft
  ... | le0 p = r-hand (proj₁ p)
  ... | le1 y = ⊥-elim (no-hand1 y h)
  raw-j (Bd.left _ _ (_ , _ , sb , aft) _ _) = lane-raw sb aft tt
  raw-j (Bd.run () _)
  raw-j (Bd.rend () _ _)
  raw-j (Bd.rpass () _ _)
  raw-j (Bd.rhand () _)

  -- Every told row, by where it lies.
  rawC : ∀ {m e} → Cn.ConnT m e → Raw m e
  rawC (Cn.body (j , _))  = raw-j j
  rawC (Cn.burst y i)     = r-burst y i
  rawC (Cn.echo y a u ni) = r-echo y a u ni
  rawC (Cn.kept y a ni i) = r-kept y a ni i

  raw : ∀ {m e} → τ m e → Raw m e
  raw t = rawC (proj₁ t)

  ------------------------------------------------------------------------
  -- Where the told rows lie

  -- The rows a row of `σ` shows under itself.
  imgs : Pos → List Pos
  imgs k = (k ⊕ [ ix 0 ]) ∷ (k ⊕ [ sub w ]) ∷ ((k ⊕ [ sub w ]) ⊕ [ ix 0 ]) ∷ (((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ∷ c₁ k ∷ []

  -- The rows of the subscribe instant.
  fixedL : List Pos
  fixedL = ((Q0 ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ∷ ((Q0 ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ∷ (Q0 ⊕ [ last ]) ∷ []

  data Owner (u : Pos) : Set where
    o-fix : u ∈ fixedL → Owner u
    o-row : ∀ {k e} → σ k e → u ∈ imgs k → Owner u

  owner : ∀ {u e} → Raw u e → Owner u
  owner r-v0            = o-fix (here refl)
  owner r-v1            = o-fix (there (here refl))
  owner r-pass          = o-fix (there (there (here refl)))
  owner (r-burst y _)   = o-row y (here refl)
  owner (r-echo y _ _ _) = o-row y (here refl)
  owner (r-kept y _ _ _) = o-row y (here refl)
  owner (r-shown p _)   = o-row (proj₁ p) (there (here refl))
  owner (r-heard p)     = o-row (proj₁ p) (there (here refl))
  owner (r-hand y)      = o-row y (there (there (here refl)))
  owner (r-x y)         = o-row y (there (there (there (here refl))))
  owner (r-end y)       = o-row y (there (there (there (there (here refl)))))

  imgs-⊑ : ∀ k {v} → v ∈ imgs k → k ⊑ v
  imgs-⊑ k (here refl)                                 = ⊑-snoc⁺ k
  imgs-⊑ k (there (here refl))                         = ⊑-snoc⁺ k
  imgs-⊑ k (there (there (here refl)))                 = ⊑-trans {k} (⊑-snoc⁺ k) (⊑-snoc⁺ (k ⊕ [ sub w ]))
  imgs-⊑ k (there (there (there (here refl))))         =
    ⊑-trans {k} (⊑-trans {k} (⊑-snoc⁺ k) (⊑-snoc⁺ (k ⊕ [ sub w ]))) (⊑-snoc⁺ ((k ⊕ [ sub w ]) ⊕ [ ix 1 ]))
  imgs-⊑ k (there (there (there (there (here refl))))) = under-c₁ k

  fixed-at : ∀ {v} → v ∈ fixedL → Σ Path λ ys → v ≡ Q0 ⊕ ys
  fixed-at (here refl)                 = ix 0 ∷ ix 0 ∷ [] , ⊕-assoc Q0 [ ix 0 ] [ ix 0 ]
  fixed-at (there (here refl))         = ix 1 ∷ ix 0 ∷ [] , ⊕-assoc Q0 [ ix 1 ] [ ix 0 ]
  fixed-at (there (there (here refl))) = last ∷ [] , refl

  fixed-≺ : ∀ {v} → v ∈ fixedL → v ≺ r
  fixed-≺ {v} m with fixed-at m
  ... | ys , refl = q0≺r ys

  -- Rows of `σ`, one before another, apart: so what lies under them too.
  img-≺ : ∀ {a b ea eb} → σ a ea → σ b eb → a ≺ b → ∀ as bs → (a ⊕ as) ≺ (b ⊕ bs)
  img-≺ {a} {b} ya yb ab = apart ab np
    where
      np : ¬ (a ⊑ b)
      np ([] , eq)    = ≺-irrefl {a} (subst (a ≺_) (trans eq (⊕-identityʳ a)) ab)
      np (l ∷ ls , eq) = flatσ ya (subst (λ z → σ z _) eq yb)

  -- A row of `σ` and what lies under it, before another and what lies
  -- under that: the row is at or before the other.
  img-≼ : ∀ {k k₀ e e₀ v u} → σ k e → σ k₀ e₀ → k ⊑ v → k₀ ⊑ u → v ≺ u → k ≼ k₀
  img-≼ {k} {k₀} {v = v} {u} y y₀ (zs , refl) (zs₀ , refl) vu with ≼-or-≻ k k₀
  ... | inj₁ le = le
  ... | inj₂ lt = ⊥-elim (≺-absurd {k ⊕ zs} {k₀ ⊕ zs₀} vu (img-≺ y₀ y lt zs₀ zs))

  -- Few rows before any told row under few of `σ`'s, or in the
  -- subscribe instant.
  few-at : ∀ {t : EmissionSet Y} → (∀ {v e} → t v e → Raw v e) → ∀ {u} ks
         → (∀ {k e v} → σ k e → k ⊑ v → v ≺ u → k ∈ ks) → Few t u
  few-at rw {u} ks h = fixedL ++ concat (L.map imgs ks) , λ tv lt → go (owner (rw tv)) lt
    where
      go : ∀ {v} → Owner v → v ≺ u → v ∈ fixedL ++ concat (L.map imgs ks)
      go (o-fix m) _ = ∈-++⁺ˡ m
      go (o-row {k} y m) lt = ∈-++⁺ʳ fixedL (∈-concat⁺′ m (∈-map⁺ imgs (h y (imgs-⊑ k m) lt)))

  few-under : ∀ {k e u} {t : EmissionSet Y} → σ k e → Few σ k → k ⊑ u → (∀ {v e′} → t v e′ → Raw v e′) → Few t u
  few-under {k} y (ks , F) ku rw = few-at rw (k ∷ ks) λ y′ kv vu → pick y′ (img-≼ y′ y kv ku vu)
    where
      pick : ∀ {k′ e′} → σ k′ e′ → k′ ≼ k → k′ ∈ k ∷ ks
      pick {k′} y′ le with ≼-split {k′} {k} le
      ... | inj₁ lt   = there (F y′ lt)
      ... | inj₂ refl = here refl

  few-fixed : ∀ {u} {t : EmissionSet Y} → u ∈ fixedL → (∀ {v e′} → t v e′ → Raw v e′) → Few t u
  few-fixed {u} m rw = few-at rw [] λ {k} {_} {v} y kv vu → ⊥-elim (≺-absurd {r} {k} (r≺ y) (≺-trans {k} {u} {r} (≼-≺-≺ {k} {v} {u} (⊑-≼ {k} {v} kv) vu) (fixed-≺ m)))

  ------------------------------------------------------------------------
  -- The told rows made

  T-or : ∀ b → T b ⊎ T (not b)
  T-or true  = inj₁ tt
  T-or false = inj₂ tt

  c₁-≻ : ∀ k → k ≺ c₁ k
  c₁-≻ k = subst (k ≺_) (sym (proj₂ (under-c₁ k))) (≺-ext k (ix 1 ∷ last ∷ []))

  ends-raw : ∀ {c} → Raw c end → Σ Pos λ k → σ k end × c ≡ c₁ k
  ends-raw (r-shown _ ())
  ends-raw (r-end y) = _ , y , refl

  -- A row of `σ` other than a pin lies at or before its end.
  proper-unp : ∀ {k e} → σ k e → Unpinned e → Proper σ k e
  proper-unp {k} y u = y , λ {c} yc → le yc
    where
      le : ∀ {c} → σ c end → k ≼ c
      le {c} yc with ≼-or-≻ k c
      ... | inj₁ l = l
      ... | inj₂ lt with InvAt.quiet invσ yc y lt
      ...   | _ , refl , _ = ⊥-elim u

  alive-unp : ∀ {k e} → σ k e → Unpinned e → Cn.Alive k
  alive-unp {k} y u bc with ends-raw (raw-j (proj₁ bc))
  ... | k′ , y′ , refl = ≼-≺-≺ {k} {k′} {c₁ k′} (proj₂ (proper-unp y u) y′) (c₁-≻ k′)

  alive-pin : ∀ {k p′} → σ k (pin p′) → Cn.Alive p′
  alive-pin {k} {p′} y bc with ends-raw (raw-j (proj₁ bc))
  ... | k′ , y′ , refl with ≼-or-≻ k k′
  ...   | inj₁ le = ≼-≺-≺ {p′} {k′} {c₁ k′} (≼-trans {p′} {k} {k′} (⊑-≼ {p′} {k} (inside-⊑ p′ k (proj₂ (InvAt.pinned invσ y)))) le) (c₁-≻ k′)
  ...   | inj₂ lt with InvAt.quiet invσ y′ y lt
  ...     | _ , refl , pk = ≺-trans {p′} {k′} {c₁ k′} pk (c₁-≻ k′)

  lane0-row : ∀ {k e e′} → σ k e → Few σ k → Rejoin w (Proper σ) (k ⊕ [ sub w ]) e′ → After (Lanes true) w (k ⊕ [ sub w ]) e′
  lane0-row {k} {e} {e′} y fk rj =
    (rj , few-reach {t = Rejoin w (Proper σ)} {k ⊕ [ sub w ]} {e′} (rejoin-few flatσ y fk)) , ≺-trans {w} {k} {k ⊕ [ sub w ]} (w≺ y) (≺-ext k [])

  j-lane0 : ∀ {k e e′} → σ k e → Few σ k → Rejoin w (Proper σ) (k ⊕ [ sub w ]) e′ → Work e′ → Bd.JoinT (k ⊕ [ sub w ]) e′
  j-lane0 y fk rj wk = Bd.lane o0 (0 , true , nth0) (0 , w , sub0 , lane0-row y fk rj) (λ ()) wk

  j-hand : ∀ {k} → σ k end → Bd.JoinT ((k ⊕ [ sub w ]) ⊕ [ ix 0 ]) skip
  j-hand y = Bd.hand o0 (0 , true , nth0) (0 , w , sub0 , end0-row y) (λ ()) (hand0 y)

  j-x : ∀ {k} → σ k end → Bd.JoinT (((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out x)
  j-x {k} y = Bd.lane o1 (1 , false , nth1) (1 , s , (nth1 , start1 y) , ((at-out , of1-reach s {s ⊕ [ ix 0 ]} {out x}) , ≺-ext s [])) (λ ()) tt
    where s = (k ⊕ [ sub w ]) ⊕ [ ix 1 ]

  j-end : ∀ {k} → σ k end → Bd.JoinT (c₁ k) end
  j-end y = Bd.lend o1 (1 , false , nth1) (1 , _ , (nth1 , start1 y) , end1-row) (λ ()) (no-hand1 y) (done1 y)

  -- A body row under a row of `σ` with few before it.
  τ-under : ∀ {k e u e′} → σ k e → Few σ k → k ⊑ u → Bd.JoinT u e′ → τ u e′
  τ-under y fk ku j = Cn.body (j , few-reach (few-under y fk ku raw-j)) , few-reach (few-under y fk ku rawC)

  ------------------------------------------------------------------------
  -- The leaves

  told-row : ∀ {l e} → σ l e → Few σ l → Σ (Ev Y) λ e′ → τ (l ⊕ δ e) e′ × Told e e′
  told-row {l} {out a} y fk = out a , τ-under y fk (⊑-snoc⁺ l) (j-lane0 y fk (shown (proper-unp y tt) tt (w≺ y)) tt) , t-out
  told-row {l} {skip}  y fk = skip , τ-under y fk (⊑-snoc⁺ l) (j-lane0 y fk (shown (proper-unp y tt) tt (w≺ y)) tt) , t-skip
  told-row {l} {end}   y fk = end , subst (λ z → τ z end) (proj₂ (under-c₁ l)) (τ-under y fk (under-c₁ l) (j-end y)) , t-end
  told-row {l} {pin p′} y fk with T-or (inside r l)
  ... | inj₁ i  = pin q , (Cn.burst y i , few-reach (few-under y fk (⊑-snoc⁺ l) rawC)) , t-pin (inj₂ refl)
  ... | inj₂ ni = pin p′ , (Cn.kept y (alive-pin y) ni (proj₂ (InvAt.pinned invσ y)) , few-reach (few-under y fk (⊑-snoc⁺ l) rawC)) , t-pin (inj₁ refl)

  -- An image split at its last label.
  lab : Ev Y → Label
  lab (out _) = sub w
  lab skip    = sub w
  lab (pin _) = ix 0
  lab end     = last

  base : Pos → Ev Y → Pos
  base l end = (l ⊕ [ sub w ]) ⊕ [ ix 1 ]
  base l _   = l

  δ-split : ∀ l e → l ⊕ δ e ≡ base l e ⊕ [ lab e ]
  δ-split l (out _) = refl
  δ-split l skip    = refl
  δ-split l (pin _) = refl
  δ-split l end     = sym (proj₂ (under-c₁ l))

  split-eq : ∀ {b a} l e → b ⊕ [ a ] ≡ l ⊕ δ e → a ≡ lab e × b ≡ base l e
  split-eq {b} l e eq = ⊕-injʳ b (base l e) (trans eq (δ-split l e)) , ⊕-injˡ b (base l e) (trans eq (δ-split l e))

  -- No image lies at a position of the subscribe instant.
  fix-not : ∀ {m l e} → m ∈ fixedL → σ l e → m ≡ l ⊕ δ e → ⊥
  fix-not {m} {l} {e} mem y eq =
    ≺-irrefl {m} (subst (m ≺_) (sym eq) (≺-≼-≺ {m} {l} {l ⊕ δ e} (≺-trans {m} {r} {l} (fixed-≺ mem) (r≺ y)) (⊑-≼ {l} {l ⊕ δ e} (δ e , refl))))

  -- At a row's first child, only its own pin's image.
  at-ix0 : ∀ {b k e l e₂} → σ k e → σ l e₂ → b ⊕ [ ix 0 ] ≡ l ⊕ δ e₂ → b ≡ l × Σ Pos λ p → e₂ ≡ pin p
  at-ix0 {b} {e₂ = e₂} y y₂ eq with e₂ | split-eq _ e₂ eq
  ... | pin p | _ , be = be , p , refl
  ... | out _ | () , _
  ... | skip  | () , _
  ... | end   | () , _

  Source : Pos → Set
  Source m = (Σ Pos λ l → Σ (Ev Y) λ e → σ l e × m ≡ l ⊕ δ e) ⊎ (∀ {l e} → σ l e → m ≡ l ⊕ δ e → ⊥)

  shadow-src : ∀ {k e} → σ k e → Source (k ⊕ [ ix 0 ])
  shadow-src {k} {pin p} y = inj₁ (k , pin p , y , refl)
  shadow-src {k} {out a} y = inj₂ λ y₂ eq → not-pin y y₂ eq (λ ())
    where
      not-pin : ∀ {e l e₂} → σ k e → σ l e₂ → k ⊕ [ ix 0 ] ≡ l ⊕ δ e₂ → (∀ {p} → e ≡ pin p → ⊥) → ⊥
      not-pin y y₂ eq np with at-ix0 y y₂ eq
      ... | refl , p , refl = np (InvAt.func invσ y y₂)
  shadow-src {k} {skip} y = inj₂ λ y₂ eq → not-pin y y₂ eq (λ ())
    where
      not-pin : ∀ {e l e₂} → σ k e → σ l e₂ → k ⊕ [ ix 0 ] ≡ l ⊕ δ e₂ → (∀ {p} → e ≡ pin p → ⊥) → ⊥
      not-pin y y₂ eq np with at-ix0 y y₂ eq
      ... | refl , p , refl = np (InvAt.func invσ y y₂)
  shadow-src {k} {end} y = inj₂ λ y₂ eq → not-pin y y₂ eq (λ ())
    where
      not-pin : ∀ {e l e₂} → σ k e → σ l e₂ → k ⊕ [ ix 0 ] ≡ l ⊕ δ e₂ → (∀ {p} → e ≡ pin p → ⊥) → ⊥
      not-pin y y₂ eq np with at-ix0 y y₂ eq
      ... | refl , p , refl = np (InvAt.func invσ y y₂)

  -- Under a row, at a first child: no row of `σ` there.
  under-ix0 : ∀ {k e b} → σ k e → Σ Path (λ zs → Σ Label λ a → b ≡ k ⊕ (a ∷ zs)) → ∀ {l e₂} → σ l e₂ → b ⊕ [ ix 0 ] ≡ l ⊕ δ e₂ → ⊥
  under-ix0 y (zs , a , refl) y₂ eq with at-ix0 y y₂ eq
  ... | refl , _ = flatσ y y₂

  source-raw : ∀ {m e′} → Raw m e′ → Source m
  source-raw r-v0              = inj₂ (fix-not (here refl))
  source-raw r-v1              = inj₂ (fix-not (there (here refl)))
  source-raw r-pass            = inj₂ (fix-not (there (there (here refl))))
  source-raw (r-burst y _)     = shadow-src y
  source-raw (r-echo y _ _ _)  = shadow-src y
  source-raw (r-kept y _ _ _)  = shadow-src y
  source-raw (r-shown {k} {out a} p _) = inj₁ (k , out a , proj₁ p , refl)
  source-raw (r-shown {k} {skip} p _)  = inj₁ (k , skip , proj₁ p , refl)
  source-raw (r-shown {e = end} p ())
  source-raw (r-shown {e = pin _} p ())
  source-raw (r-heard {k} p)   = inj₂ heard-not
    where
      heard-not : ∀ {l e₂} → σ l e₂ → k ⊕ [ sub w ] ≡ l ⊕ δ e₂ → ⊥
      heard-not {e₂ = e₂} y₂ eq with e₂ | split-eq _ e₂ eq
      ... | out _ | _ , refl with InvAt.func invσ (proj₁ p) y₂
      ...   | ()
      heard-not y₂ eq | skip | _ , refl with InvAt.func invσ (proj₁ p) y₂
      ...   | ()
      heard-not y₂ eq | pin _ | () , _
      heard-not y₂ eq | end   | () , _
  source-raw (r-hand {k} y)    = inj₂ (under-ix0 y ([] , sub w , refl))
  source-raw (r-x {k} y)       = inj₂ (under-ix0 y (ix 1 ∷ [] , sub w , ⊕-assoc k [ sub w ] [ ix 1 ]))
  source-raw (r-end {k} y)     = inj₁ (k , end , y , proj₂ (under-c₁ k))

  told-source? : ∀ {m e′} → τ m e′ → Source m
  told-source? t = source-raw (raw t)

  ------------------------------------------------------------------------
  -- The told rows, listed

  few-of : ∀ {l} → Listed σ l → Few σ l
  few-of (ks , F , _) = ks , F

  -- The row at a row's first child: its burst copy, its echo, or its pin.
  img0 : ∀ {k e} → σ k e → Few σ k → Σ (Ev Y) λ e′ → τ (k ⊕ [ ix 0 ]) e′
  img0 {k} {pin p′} y F = proj₁ (told-row y F) , proj₁ (proj₂ (told-row y F))
  img0 {k} {out a}  y F = img0u y tt F
    where
      img0u : ∀ {e} → σ k e → Unpinned e → Few σ k → Σ (Ev Y) λ e′ → τ (k ⊕ [ ix 0 ]) e′
      img0u y u F with T-or (inside r k)
      ... | inj₁ i  = pin q , Cn.burst y i , few-reach {t = Cn.ConnT} {k ⊕ [ ix 0 ]} {pin q} (few-under y F (⊑-snoc⁺ k) rawC)
      ... | inj₂ ni = skip , Cn.echo y (alive-unp y u) u ni , few-reach {t = Cn.ConnT} {k ⊕ [ ix 0 ]} {skip} (few-under y F (⊑-snoc⁺ k) rawC)
  img0 {k} {skip}   y F with T-or (inside r k)
  ... | inj₁ i  = pin q , Cn.burst y i , few-reach {t = Cn.ConnT} {k ⊕ [ ix 0 ]} {pin q} (few-under y F (⊑-snoc⁺ k) rawC)
  ... | inj₂ ni = skip , Cn.echo y (alive-unp y tt) tt ni , few-reach {t = Cn.ConnT} {k ⊕ [ ix 0 ]} {skip} (few-under y F (⊑-snoc⁺ k) rawC)
  img0 {k} {end}    y F with T-or (inside r k)
  ... | inj₁ i  = pin q , Cn.burst y i , few-reach {t = Cn.ConnT} {k ⊕ [ ix 0 ]} {pin q} (few-under y F (⊑-snoc⁺ k) rawC)
  ... | inj₂ ni = skip , Cn.echo y (alive-unp y tt) tt ni , few-reach {t = Cn.ConnT} {k ⊕ [ ix 0 ]} {skip} (few-under y F (⊑-snoc⁺ k) rawC)

  τ-fixed : ∀ {u e′} → u ∈ fixedL → Bd.JoinT u e′ → τ u e′
  τ-fixed m j = Cn.body (j , few-reach (few-fixed m raw-j)) , few-reach (few-fixed m rawC)

  -- A row of `σ` with few before it.
  Entry : Set
  Entry = Σ Pos λ k → Σ (Ev Y) λ e → σ k e × Few σ k

  Row : Set
  Row = Σ Pos λ v → Σ (Ev Y) (τ v)

  At : List Entry → Pos → Set
  At es k = Any (λ en → proj₁ en ≡ k) es

  Has : List Row → Pos → Set
  Has rs v = Any (λ rw → v ≡ proj₁ rw) rs

  at-in : ∀ {fs k} → At fs k → Σ Entry λ en → en ∈ fs × proj₁ en ≡ k
  at-in (here eq) = _ , here refl , eq
  at-in (there a) with at-in a
  ... | en , m , eq = en , there m , eq

  or-l : ∀ {a} b → T a → T (a ∨ b)
  or-l {true} _ _ = tt

  or-r : ∀ a {b} → T b → T (a ∨ b)
  or-r true  _ = tt
  or-r false t = t

  or-split : ∀ a {b} → T (a ∨ b) → T a ⊎ T b
  or-split true  t = inj₁ tt
  or-split false t = inj₂ t

  not-T : ∀ {b} → T (not b) → T b → ⊥
  not-T {true}  () _
  not-T {false} _  ()

  -- Whether an entry ends before `k`.
  endB : List Entry → Pos → Bool
  endB []                     k = false
  endB ((c , end , _) ∷ es)   k = (c <ᵖ k) ∨ endB es k
  endB ((_ , out _ , _) ∷ es) k = endB es k
  endB ((_ , skip , _) ∷ es)  k = endB es k
  endB ((_ , pin _ , _) ∷ es) k = endB es k

  endB-sound : ∀ es {k} → T (endB es k) → Σ Pos λ c → σ c end × c ≺ k
  endB-sound []                           ()
  endB-sound ((c , end , y , _) ∷ es) {k} h with or-split (c <ᵖ k) h
  ... | inj₁ ck = c , y , ck
  ... | inj₂ h′ = endB-sound es h′
  endB-sound ((_ , out _ , _) ∷ es) h = endB-sound es h
  endB-sound ((_ , skip , _) ∷ es)  h = endB-sound es h
  endB-sound ((_ , pin _ , _) ∷ es) h = endB-sound es h

  endB-any : ∀ {es c k} → At es c → σ c end → c ≺ k → T (endB es k)
  endB-any {(_ , end , _) ∷ es} {k = k} (here refl) _ ck = or-l (endB es k) ck
  endB-any {(_ , out _ , y , _) ∷ es} (here refl) yc _ with InvAt.func invσ y yc
  ... | ()
  endB-any {(_ , skip , y , _) ∷ es} (here refl) yc _ with InvAt.func invσ y yc
  ... | ()
  endB-any {(_ , pin _ , y , _) ∷ es} (here refl) yc _ with InvAt.func invσ y yc
  ... | ()
  endB-any {(c′ , end , _) ∷ es} {k = k} (there a) yc ck = or-r (c′ <ᵖ k) (endB-any a yc ck)
  endB-any {(_ , out _ , _) ∷ es} (there a) yc ck = endB-any a yc ck
  endB-any {(_ , skip , _) ∷ es}  (there a) yc ck = endB-any a yc ck
  endB-any {(_ , pin _ , _) ∷ es} (there a) yc ck = endB-any a yc ck

  -- A pin's copy in the first lane: there unless the run ended before it.
  pinRows : ∀ {k p′} → σ k (pin p′) → Few σ k → (b : Bool) → (T (not b) → Proper σ k (pin p′)) → List Row
  pinRows     y F true  _  = []
  pinRows {k} y F false pr = (k ⊕ [ sub w ] , skip , τ-under y F (⊑-snoc⁺ k) (j-lane0 y F (heard (pr tt) (w≺ y)) tt)) ∷ []

  pin-in : ∀ {k p′} (y : σ k (pin p′)) F (b : Bool) pr → (T b → ⊥) → Has (pinRows y F b pr) (k ⊕ [ sub w ])
  pin-in y F true  pr nb = ⊥-elim (nb tt)
  pin-in y F false pr nb = here refl

  fixedRows : List Row
  fixedRows = ((Q0 ⊕ [ ix 0 ]) ⊕ [ ix 0 ] , skip , τ-fixed (here refl) (Bd.val o0))
            ∷ ((Q0 ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , skip , τ-fixed (there (here refl)) (Bd.val o1))
            ∷ (Q0 ⊕ [ last ] , skip , τ-fixed (there (there (here refl))) (Bd.opass oe no-oend))
            ∷ []

  -- THE TOLD ROWS OF A LIST OF ENTRIES closed under the ends before them:
  -- each entry's every image, and the subscribe instant's.
  module Image (es : List Entry) where
    Clo : Pos → Set
    Clo k = ∀ {c} → σ c end → c ≺ k → At es c

    proper-pin : ∀ {k p′} → σ k (pin p′) → Clo k → T (not (endB es k)) → Proper σ k (pin p′)
    proper-pin {k} y cl ne = y , le
      where
        le : ∀ {c} → σ c end → k ≼ c
        le {c} yc with ≼-or-≻ k c
        ... | inj₁ l  = l
        ... | inj₂ ck = ⊥-elim (not-T ne (endB-any (cl yc ck) yc ck))

    rowsOf : (en : Entry) → Clo (proj₁ en) → List Row
    rowsOf (k , out a , y , F) _  = (k ⊕ [ ix 0 ] , img0 y F) ∷ (k ⊕ [ sub w ] , proj₁ (told-row y F) , proj₁ (proj₂ (told-row y F))) ∷ []
    rowsOf (k , skip , y , F)  _  = (k ⊕ [ ix 0 ] , img0 y F) ∷ (k ⊕ [ sub w ] , proj₁ (told-row y F) , proj₁ (proj₂ (told-row y F))) ∷ []
    rowsOf (k , end , y , F)   _  =
        (k ⊕ [ ix 0 ] , img0 y F)
      ∷ ((k ⊕ [ sub w ]) ⊕ [ ix 0 ] , skip , τ-under y F (imgs-⊑ k (there (there (here refl)))) (j-hand y))
      ∷ (((k ⊕ [ sub w ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , out x , τ-under y F (imgs-⊑ k (there (there (there (here refl))))) (j-x y))
      ∷ (c₁ k , end , τ-under y F (under-c₁ k) (j-end y))
      ∷ []
    rowsOf (k , pin p′ , y , F) cl = (k ⊕ [ ix 0 ] , img0 y F) ∷ pinRows y F (endB es k) (proper-pin y cl)

    walk : (fs : List Entry) → (∀ {en} → en ∈ fs → Clo (proj₁ en)) → List Row
    walk []        _  = []
    walk (en ∷ fs) cl = rowsOf en (cl (here refl)) ++ walk fs (λ m → cl (there m))

    has-walk : ∀ {v en fs} (cl : ∀ {en} → en ∈ fs → Clo (proj₁ en)) → en ∈ fs → (∀ (c : Clo (proj₁ en)) → Has (rowsOf en c) v) → Has (walk fs cl) v
    has-walk {fs = en ∷ _}  cl (here refl) h = AnyP.++⁺ˡ {xs = rowsOf en (cl (here refl))} (h (cl (here refl)))
    has-walk {fs = en ∷ fs} cl (there m)   h = AnyP.++⁺ʳ (rowsOf en (cl (here refl))) (has-walk (λ m′ → cl (there m′)) m h)

    head-in : ∀ {k} e (y : σ k e)  F (c : Clo k) → Has (rowsOf (k , e , y , F) c) (k ⊕ [ ix 0 ])
    head-in (out _) _ _ _ = here refl
    head-in skip    _ _ _ = here refl
    head-in end     _ _ _ = here refl
    head-in (pin _) _ _ _ = here refl

    shown-in : ∀ {k e} → σ k e → Bare e → ∀ {e₁} (y₁ : σ k e₁)  F (c : Clo k) → Has (rowsOf (k , e₁ , y₁ , F) c) (k ⊕ [ sub w ])
    shown-in {e = out _} y _ y₁ F c with InvAt.func invσ y₁ y
    ... | refl = there (here refl)
    shown-in {e = skip}  y _ y₁ F c with InvAt.func invσ y₁ y
    ... | refl = there (here refl)
    shown-in {e = end}   y ()
    shown-in {e = pin _} y ()

    heard-in : ∀ {k p′} → Proper σ k (pin p′) → ∀ {e₁} (y₁ : σ k e₁)  F (c : Clo k) → Has (rowsOf (k , e₁ , y₁ , F) c) (k ⊕ [ sub w ])
    heard-in {k} pr y₁ F c with InvAt.func invσ y₁ (proj₁ pr)
    ... | refl = there (pin-in y₁ F (endB es k) (proper-pin y₁ c) λ h → let (_ , yc , ck) = endB-sound es h in proj₂ pr yc ck)

    end-in : ∀ {k} → σ k end → ∀ {v} → (∀ (y′ : σ k end) F (c : Clo k) → Has (rowsOf (k , end , y′ , F) c) v) → ∀ {e₁} (y₁ : σ k e₁)  F (c : Clo k) → Has (rowsOf (k , e₁ , y₁ , F) c) v
    end-in y h y₁ F c with InvAt.func invσ y₁ y
    ... | refl = h y₁ F c

    module Cover (clo : ∀ {en} → en ∈ es → Clo (proj₁ en)) where
      all : List Row
      all = fixedRows ++ walk es clo

      via : ∀ {k e v} → σ k e → At es k → (∀ {e₁} (y₁ : σ k e₁)  F (c : Clo k) → Has (rowsOf (k , e₁ , y₁ , F) c) v) → Has all v
      via y a h with at-in a
      ... | (_ , e₁ , y₁ , F) , m , refl = AnyP.++⁺ʳ fixedRows (has-walk clo m (h y₁ F))

      -- Every told row, where its owner is an entry.
      cover : ∀ {v e′} → τ v e′ → (∀ {k e} → σ k e → k ⊑ v → At es k) → Has all v
      cover t own = go own (raw t)
        where
          go : ∀ {v e′} → (∀ {k e} → σ k e → k ⊑ v → At es k) → Raw v e′ → Has all v
          go own r-v0              = AnyP.++⁺ˡ {xs = fixedRows} (here refl)
          go own r-v1              = AnyP.++⁺ˡ {xs = fixedRows} (there (here refl))
          go own r-pass            = AnyP.++⁺ˡ {xs = fixedRows} (there (there (here refl)))
          go own (r-burst {k} y _)     = via y (own y (⊑-snoc⁺ k)) (λ {e₁} → head-in e₁)
          go own (r-echo {k} y _ _ _)  = via y (own y (⊑-snoc⁺ k)) (λ {e₁} → head-in e₁)
          go own (r-kept {k} y _ _ _)  = via y (own y (⊑-snoc⁺ k)) (λ {e₁} → head-in e₁)
          go own (r-shown {k} p b) = via (proj₁ p) (own (proj₁ p) (⊑-snoc⁺ k)) (λ {e₁} → shown-in (proj₁ p) b {e₁})
          go own (r-heard {k} p)   = via (proj₁ p) (own (proj₁ p) (⊑-snoc⁺ k)) (λ {e₁} → heard-in p {e₁})
          go own (r-hand {k} y)    = via y (own y (imgs-⊑ k (there (there (here refl))))) (λ {e₁} → end-in y (λ _ _ _ → there (here refl)) {e₁})
          go own (r-x {k} y)       = via y (own y (imgs-⊑ k (there (there (there (here refl)))))) (λ {e₁} → end-in y (λ _ _ _ → there (there (here refl))) {e₁})
          go own (r-end {k} y)     = via y (own y (under-c₁ k)) (λ {e₁} → end-in y (λ _ _ _ → there (there (there (here refl)))) {e₁})

      back : ∀ {v} → v ∈ L.map proj₁ all → Σ (Ev Y) (τ v)
      back m with ∈-map⁻ proj₁ {xs = all} m
      ... | (_ , e′ , t) , _ , refl = e′ , t

  -- Entries for the listed positions.
  ents : (fs : List Pos) → (∀ {k} → k ∈ fs → Σ (Ev Y) (σ k) × Few σ k) → List Entry
  ents []       _ = []
  ents (k ∷ fs) b = (k , proj₁ (proj₁ (b (here refl))) , proj₂ (proj₁ (b (here refl))) , proj₂ (b (here refl))) ∷ ents fs (λ m → b (there m))

  ents-at : ∀ {fs k} {b : ∀ {k} → k ∈ fs → Σ (Ev Y) (σ k) × Few σ k} → k ∈ fs → At (ents fs b) k
  ents-at (here refl) = here refl
  ents-at (there m)   = there (ents-at m)

  ents-in : ∀ {fs en} {b : ∀ {k} → k ∈ fs → Σ (Ev Y) (σ k) × Few σ k} → en ∈ ents fs b → proj₁ en ∈ fs
  ents-in {_ ∷ _} (here refl) = here refl
  ents-in {_ ∷ _} (there m)   = there (ents-in m)

  -- A row with few before it shows again, and every told row before its
  -- image is the image of a row before it or of the subscribe instant.
  told-listed : ∀ {l e} → σ l e → Listed σ l → Listed τ (l ⊕ δ e)
  told-listed {l} {e} y Ll@(ks , cov , bk) = filter (λ v → T? (v <ᵖ u)) (L.map proj₁ C.all) , cover′ , back′
    where
      u : Pos
      u = l ⊕ δ e
      Fl : Few σ l
      Fl = few-of Ll
      es : List Entry
      es = (l , e , y , Fl) ∷ ents ks (λ m → proj₂ (bk m) , few-down Fl (≺→≼ {_} {l} (proj₁ (bk m))))
      bound : ∀ {en} → en ∈ es → proj₁ en ≼ l
      bound (here refl) = ≼-refl {l}
      bound (there m)   = ≺→≼ {_} {l} (proj₁ (bk (ents-in m)))
      clo : ∀ {en} → en ∈ es → Image.Clo es (proj₁ en)
      clo {en} m {c} yc ck = there (ents-at (cov yc (≺-≼-≺ {c} {proj₁ en} {l} ck (bound m))))
      module C = Image.Cover es clo
      own : ∀ {v} → v ≺ u → ∀ {k e₁} → σ k e₁ → k ⊑ v → At es k
      own {v} vu {k} y₁ kv with ≼-split {k} {l} (img-≼ y₁ y kv (δ e , refl) vu)
      ... | inj₁ kl   = there (ents-at (cov y₁ kl))
      ... | inj₂ refl = here refl
      cover′ : ∀ {v e′} → τ v e′ → v ≺ u → v ∈ filter (λ v → T? (v <ᵖ u)) (L.map proj₁ C.all)
      cover′ t vu = ∈-filter⁺ (λ v → T? (v <ᵖ u)) (AnyP.map⁺ (C.cover t (own vu))) vu
      back′ : ∀ {v} → v ∈ filter (λ v → T? (v <ᵖ u)) (L.map proj₁ C.all) → v ≺ u × Σ _ (τ v)
      back′ m with ∈-filter⁻ (λ v → T? (v <ᵖ u)) {xs = L.map proj₁ C.all} m
      ... | m′ , vu = vu , C.back m′

  -- Where a told row lies under a row of the run: the run's rows before it.
  src1 : ∀ {v} → Source v → List Pos
  src1 (inj₁ (l , _)) = l ∷ []
  src1 (inj₂ _)       = []

  srcs : (ms : List Pos) → (∀ {v} → v ∈ ms → Σ _ (τ v)) → List Pos
  srcs []       _ = []
  srcs (v ∷ ms) b = src1 (told-source? (proj₂ (b (here refl)))) ++ srcs ms (λ m → b (there m))

  srcs-sound : ∀ ms {b : ∀ {v} → v ∈ ms → Σ _ (τ v)} {k} → k ∈ srcs ms b → Σ _ (σ k)
  srcs-sound (v ∷ ms) {b} m with told-source? (proj₂ (b (here refl))) | ∈-++⁻ {v = _} (src1 (told-source? (proj₂ (b (here refl))))) m
  ... | inj₁ (_ , e , y , _) | inj₁ (here refl) = e , y
  ... | inj₂ _               | inj₁ ()
  ... | _                    | inj₂ m′ = srcs-sound ms m′
