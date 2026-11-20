{-# OPTIONS --guardedness #-}

-- EVERY PROGRAM'S CUTS ARE BOUNDED BY ITS TREE'S BOUNDARIES
-- (`tree-bounded`): a row before every boundary of a cut is a row of
-- every deeper cut, so of the meaning, and nothing decides where the
-- program hangs.  One induction over the tree, in any lawful scope, at
-- any admissible subscription; it reads no elaboration, so it bounds a
-- plain program and its elaboration alike.
--
-- Each case is its former's: a leaf never moves, a spin has its next
-- tick (`SpinB`), a map keeps its child's rows in place, a take is
-- `TakeB`'s, a connect `ConnB`'s over its source and its body in the
-- scope the source's hot extends, a reader `RejoinB`'s over its hot.
--
-- A hot carries its boundaries (`HotD`), and the one hot there is, a
-- connect's (`listHot`), hangs at its source's by the theorem itself:
-- the two are one recursion, the hot's on the same tree, the theorem's
-- on a smaller.
--
-- A source's boundaries lie before its connect or past its subscription
-- (`src-out`), never under the connect short of the source.  Not all
-- past it: a reader in a lane under a late row of its hot keeps every
-- boundary of the hot, a running lane's tick before that row among them.
module simultaneous.TreeBounded where

open import Data.Bool using (T)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; Later; cold; empty; of; map; scan; takeWhile; flatMap;
  connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; inside; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; Rejoin; _≺_; _≼_; enter; Proper; module Op; at-end; end; module Connecting)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺→≼; ≼-refl; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_; Ok; InvAt; Lawful; Real; _∪ʰ_; ok-step; W; join; here; real-snoc; real-sub; plain-ix;
  plain-last; ok-in)
open import denotation.Laws.Worlds.Leaves using (empty-inv)
open import denotation.Laws.Cut using (capprox; inv-capprox)
import denotation.Laws.Connect as Cn
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; rejoin)
open import quickcheck.Tabled.Exact using (truncate-exact; rejoin-exact; proper-exact)
open import quickcheck.Tabled.Exact.Base using (Exact; Exactly; sound; complete)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.ElabUndone using (EnvU; AUndone; ann-u; elab-undone)
open import simultaneous.DenRows using (hot-out)
open import simultaneous.Listing using (listC; listC-ok; listC-exact; UncutEnv; Uncut)
open import simultaneous.TableKit using (Rows)
open import simultaneous.TableCorr using (keys; in-keys)
open import simultaneous.TableMap using (map-bounded)
open import simultaneous.TableScan using (scan-bounded)
open import simultaneous.TableTake using (tr-take→; tr-take←; failed?)
open import simultaneous.TableRows using (part-≺)
open import simultaneous.TableEnv using (_⊕ˡ_; admits-ix; Ren; HotD; hotD; hev; DenOf; den; den-ex; den-ok; dbd; dbounded; dapart; HotsAll; w-mono; ok-mono; Past; past-up; past-⊕;
  Admits; admits-at; admits-step; admits-row; den-cons; tab-func; tab-flat; pin-ok; after-ok; pin-after-ok)
open import simultaneous.Horizon using (Tag; held; module Cuts; module SpinB; module TakeB; module ConnB; module RejoinB; const-bounded; bounded-≃)
open import simultaneous.HorizonTree using (Cut; srcL; bodyρ; bodyU; bd; cold-bd)
open import simultaneous.HorizonJoin using (module MergeJ; module MergeB)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (elab; annotate)

------------------------------------------------------------------------
-- A reader's table is its hot's, rejoined

private
  rj : ∀ {X : Set} (L : Tb.Listed X) p → Σ (Tb.Listed X) (λ x → just (rejoin p L) ≡ just x × Uncut x) → Exact (rejoin p L) (Rejoin p (Rows L))
  rj L p (_ , refl , u) = rejoin-exact {l = L} {t = Rows L} (λ _ → record { sound = λ m → m ; complete = λ m → m }) p u

-- A connect's source's proper rows, cut by cut: what its hot lists.
listEv : ∀ {Γ X} → ℕ → Obs Timeline Γ X → {ρ : ℕ → All Tb.Listed Γ} → DenOf ρ → Pos → ℕ → EmissionSet X
listEv n o D c N = Proper (enter (capprox (3 + N) n o (den D N)) (c ⊕ [ ix 1 ]))

------------------------------------------------------------------------
-- The leaves owed

postulate
  -- A COLD'S CUTS: the listing stops short of the timeline only at its
  -- boundaries.
  cold-bounded : ∀ {Γ A} n (c : Timeline A) (ρ : ℕ → All Tb.Listed Γ) p → Cuts.Bounded (Cut n (cold c) ρ p) (cold-bd c p)

  -- A HOT'S ROWS are its source's proper rows, cut where the source is.
  hot-rows-bounded : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {Bd : ℕ → Pos → Tag → Set}
                   → Cuts.Bounded (Cut n s ρ (p ⊕ [ ix 1 ])) Bd → Cuts.Bounded (λ N → Rows (hotOf (srcL n s uρ p N))) Bd

  -- A CONNECT'S TABLE is the connect of its parts'.
  conn-tr→ : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N y e}
           → Cut n (connect s b) ρ p N y e → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N) y e
  conn-tr← : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N y e}
           → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N) y e → Cut n (connect s b) ρ p N y e

  -- A MERGE'S TABLE is the merge of its parts'.
  merge-tr→ : ∀ {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N y e}
            → Cut n (flatMap (mergeᶠ nothing) f s) ρ p N y e → MergeJ.Jc (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) N y e
  merge-tr← : ∀ {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N y e}
            → MergeJ.Jc (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) N y e → Cut n (flatMap (mergeᶠ nothing) f s) ρ p N y e

module _ {Γ} (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) where
  postulate
    -- A SOURCE'S BOUNDARIES lie before its connect or past its
    -- subscription, and a held one in its burst waits on a connect there.
    src-out  : ∀ {A} n (s : Obs Timeline Γ A) p → Admits D p → ∀ {N b g} → bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b g → b ≺ p ⊎ (p ⊕ [ ix 1 ]) ≺ b
    src-held : ∀ {A} n (s : Obs Timeline Γ A) p → Admits D p → ∀ {N b q} → bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b (held q) → T (inside (p ⊕ [ ix 1 ]) b) → (p ⊕ [ ix 1 ]) ≼ q

    -- A SOURCE'S BOUNDARIES lie apart from the late end of any reader its
    -- hot's rows admit, subscribed at or past the connect's body.
    src-apart : ∀ {A} n (s : Obs Timeline Γ A) p {q} → Ok (λ k → Σ ℕ λ N → Σ (Ev A) (listEv n s D p N k)) q → (p ⊕ [ ix 0 ]) ≼ q
              → ∀ {N b g} → bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b g → ¬ b ⊑ (q ⊕ [ last ]) × ¬ (q ⊕ [ last ]) ⊑ b

    -- THE OTHER JOINS' CUTS: the outer's boundaries, and each running
    -- lane's before the lane's cut.
    cc-bounded : ∀ {A B} n k (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p → Admits D p
               → Cuts.Bounded (Cut n (flatMap (mergeᶠ (just k)) f s) ρ p) (bd n (flatMap (mergeᶠ (just k)) f s) ρ uρ (dbd D) p)
    sw-bounded : ∀ {A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p → Admits D p
               → Cuts.Bounded (Cut n (flatMap switchᶠ f s) ρ p) (bd n (flatMap switchᶠ f s) ρ uρ (dbd D) p)
    ex-bounded : ∀ {A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p → Admits D p
               → Cuts.Bounded (Cut n (flatMap exhaustᶠ f s) ρ p) (bd n (flatMap exhaustᶠ f s) ρ uρ (dbd D) p)

    -- A DEFER'S CUTS: its marker under its first label, apart from every
    -- boundary of its body, subscribed one label down.
    later-bounded : ∀ {A} n (l : Later Timeline Γ A) p → Admits D p
                  → Cuts.Bounded (Cut (suc n) (defer l) ρ p) (bd (suc n) (defer l) ρ uρ (dbd D) p)

------------------------------------------------------------------------
-- Every tree, and the hot a connect lists

-- A connect's body is past every connect it lies in.
past-body : ∀ {fs} c → Past fs c → Past ((c ⊕ [ ix 0 ]) ∷ fs) (c ⊕ [ ix 0 ])
past-body c fp = ≼-refl {c ⊕ [ ix 0 ]} ∷ past-⊕ c (ix 0) [] fp

mutual
  -- A CONNECT'S HOT: its source listed under the connect's second label.
  listHot : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c → Admits D c
          → HotD (λ N → hotOf (proj₁ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ]))))

  -- Its body admissible where the connect is.
  admits-body : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c (a : Admits D c)
              → Admits (den-cons (listHot n o u D c a) D) (c ⊕ [ ix 0 ])

  -- EVERY TREE'S CUTS ARE BOUNDED BY ITS BOUNDARIES.
  tree-bounded : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ)
               → ∀ p → Admits D p → Cuts.Bounded (Cut n o ρ p) (bd n o ρ uρ (dbd D) p)

  listHot {X = X} n o {ρ} u D c a =
    hotD hv hx hl (c ⊕ [ ix 0 ]) (bd n o ρ u (dbd D) (c ⊕ [ ix 1 ]))
      (hot-rows-bounded n o u c (tree-bounded n o ρ u D (c ⊕ [ ix 1 ]) (admits-step D a)))
      (λ {q} ok lp {N} {b} {g} → src-apart ρ u D n o c {q} ok lp {N} {b} {g})
    where
      hv : ℕ → EmissionSet _
      hv = listEv n o D c

      hx : ∀ N p → Exactly (rejoin p (hotOf (proj₁ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ]))))) (enter (ES.hot (hv N)) p)
      hx N p = truncate-exact (rejoin-exact (proper-exact (listC-exact (3 + N) n o (den-ex D N) (c ⊕ [ ix 1 ]) (proj₁ (proj₂ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ])))))) p)

      hl : ∀ N → Lawful (hv N)
      hl N = Cn.lawful {s = capprox (3 + N) n o (den D N)} {F = λ _ → Op.empty {X}} (inv-capprox (3 + N) n o (den D N) (den-ok D N)) (λ _ → empty-inv) c (admits-at D a N)

  admits-body {X = X} n o u D c a = ok-mono into (Cn.Apart.ok₀ σ∞ c (proj₁ a) σw) , past-body c (proj₂ a)
    where
      hD = listHot n o u D c a

      -- The source's rows at every cut, each in the source's world.
      σ∞ : EmissionSet X
      σ∞ h e = Σ ℕ λ N → hev hD N h e

      σw : ∀ {h e} → σ∞ h e → W (HotsAll D) (c ⊕ [ ix 1 ]) h
      σw (N , x) = w-mono (λ hh → N , hh)
        (InvAt.world (inv-capprox (3 + N) n o (den D N) (den-ok D N) (c ⊕ [ ix 1 ]) (ok-step c (admits-at D a N))) (proj₁ x))

      into : ∀ {h} → HotsAll (den-cons hD D) h → (HotsAll D ∪ʰ σ∞) h
      into (N , inj₁ (e , x)) = inj₁ (e , N , x)
      into (N , inj₂ hh)      = inj₂ (N , hh)

  tree-bounded n       (cold c)          ρ uρ D p a = cold-bounded n c ρ p
  tree-bounded n       empty             ρ uρ D p a = const-bounded _
  tree-bounded n       (of xs)           ρ uρ D p a = const-bounded _
  tree-bounded n       (map f s)         ρ uρ D p a = map-bounded f (λ N → listC (3 + N) n s (ρ N) p) (tree-bounded n s ρ uρ D p a)
  tree-bounded n       (scan f z s)      ρ uρ D p a = scan-bounded f z (λ N → listC (3 + N) n s (ρ N) p) (tree-bounded n s ρ uρ D p a)
  tree-bounded n       (takeWhile i q s) ρ uρ D p a =
    bounded-≃ (λ {N} → tr-take← i q (listC (3 + N) n s (ρ N) p)) (λ {N} → tr-take→ i q (listC (3 + N) n s (ρ N) p))
      (TakeB.bounded′ i q (Cut n s ρ p) (bd n s ρ uρ (dbd D) p)
        (λ N → record { func = tab-func n s uρ D a {N} ; flat = tab-flat n s uρ D a {N} ; pin-in = pin-ok (3 + N) n s p })
        (λ N → failed? i q (listC (3 + N) n s (ρ N) p))
        (λ N w → keys (listC (3 + N) n s (ρ N) p) , λ x _ → in-keys x)
        (tree-bounded n s ρ uρ D p a))
  tree-bounded n (flatMap (mergeᶠ nothing) f s) ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → merge-tr← n f s uρ p {N} {y} {e}) (λ {N} {y} {e} → merge-tr→ n f s uρ p {N} {y} {e})
      (MergeB.bounded (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (tree-bounded n s ρ uρ D p a)
        (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q)
        (λ {N} {q} {v} x → tree-bounded n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x))
        (λ {N} {M} {q} {v} x l → pin-after-ok (3 + M) n (f v) {ρ M} (q ⊕ [ ix 1 ]) l))
  tree-bounded n (flatMap (mergeᶠ (just k)) f s) ρ uρ D p a = cc-bounded ρ uρ D n k f s p a
  tree-bounded n (flatMap switchᶠ f s)           ρ uρ D p a = sw-bounded ρ uρ D n f s p a
  tree-bounded n (flatMap exhaustᶠ f s)          ρ uρ D p a = ex-bounded ρ uρ D n f s p a
  tree-bounded n       (connect s b)     ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → conn-tr← n s b uρ p {N} {y} {e}) (λ {N} {y} {e} → conn-tr→ n s b uρ p {N} {y} {e})
      (ConnB.bounded p (Cut n s ρ (p ⊕ [ ix 1 ])) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]))
        (bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]))
        (bd n b (bodyρ n s uρ p) (bodyU n s uρ p) (dbd (den-cons (listHot n s uρ D p a) D)) (p ⊕ [ ix 0 ]))
        (tree-bounded n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a))
        (tree-bounded n b (bodyρ n s uρ p) (bodyU n s uρ p) (den-cons (listHot n s uρ D p a) D) (p ⊕ [ ix 0 ]) (admits-body n s uρ D p a))
        (λ {N} {b′} {g} → src-out ρ uρ D n s p a {N} {b′} {g})
        (λ {N} {b′} {q} → src-held ρ uρ D n s p a {N} {b′} {q})
        (λ {N} {c} x → ≺-≼-≺ {p} {p ⊕ [ ix 0 ]} {c} (≺-ext p []) (after-ok (3 + N) n b (p ⊕ [ ix 0 ]) x)))
  tree-bounded n       (connected i)     ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} x → rejoin p (lookup (ρ N) i) , refl , complete (ex N) x)
              (λ {N} {y} {e} → λ { (_ , refl , m) → sound (ex N) m })
      (RejoinB.bounded-j p (λ N → Rows (lookup (ρ N) i)) (dbd D i) (dbounded D i) (λ {N} {b} {g} → dapart D i (proj₁ a) (proj₂ a) {N} {b} {g}))
    where
      ex : ∀ N → Exact (rejoin p (lookup (ρ N) i)) (Rejoin p (Rows (lookup (ρ N) i)))
      ex N = rj (lookup (ρ N) i) p (listC-ok (3 + N) n (connected i) (uρ N) p)
  tree-bounded zero    (defer l)         ρ uρ D p a = SpinB.bounded p
  tree-bounded (suc n) (defer l)         ρ uρ D p a = later-bounded ρ uρ D n l p a

-- A SHARED CHILD'S LANE: a connect at `c` whose source is `empty`, its
-- end read by a blocker lane of a flatMap subscribed one label under
-- the body, the child queued behind that blocker.  The child's lane,
-- past the trigger's end, is admissible.
admits-trig : ∀ {Γ} n {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c (a : Admits D c)
            → Admits (den-cons (listHot n (empty {A = ⊤}) u D c a) D)
                     (c ⊕ˡ (ix 1 ∷ last ∷ sub (c ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ []))
admits-trig n u D c a =
  ok-step (h ⊕ [ sub r ]) (ok-in (proj₁ ar) (join (inj₁ hh) here lt) (real-sub h rh (proj₁ (proj₁ ar)) (≺-trans {r} {h} {h ⊕ [ sub r ]} lt (≺-ext h [])))) ,
  past-⊕ (h ⊕ [ sub r ]) (ix 1) [] (past-⊕ h (sub r) [] (past-up r h (proj₂ ar) (≺→≼ {r} {h} lt)))
  where
    hD = listHot n (empty {A = ⊤}) u D c a
    r h : Pos
    r = c ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])
    h = c ⊕ˡ (ix 1 ∷ last ∷ [])

    ar : Admits (den-cons hD D) r
    ar = admits-ix (den-cons hD D) 1 (admits-ix (den-cons hD D) 0 (admits-step (den-cons hD D) (admits-body n (empty {A = ⊤}) u D c a)))

    rh : Real h
    rh = real-snoc (c ⊕ [ ix 1 ]) plain-last (real-snoc c plain-ix (proj₁ (proj₁ a)))

    lt : r ≺ h
    lt = part-≺ c (ix 1 ∷ ix 0 ∷ ix 1 ∷ []) (last ∷ []) refl

    -- The trigger's end.
    row : hev hD 0 h end
    row = (at-end , (h ∷ []) , λ { at-end _ _ → here refl }) , λ { (at-end , _) → ≼-refl {h} }

    hh : HotsAll (den-cons hD D) h
    hh = 0 , inj₁ (end , row)

-- An elaborated connect's hot ends no lane, wherever its scope's hots end none.
listHot-u : ∀ {Γ Δ X} n {ρι : Ren Γ Δ} (s : Obs Timeline Γ X) {ρ* : ℕ → All Tb.Listed Δ} (u : ∀ N → UncutEnv (ρ* N)) (D : DenOf ρ*) c a
          → (∀ N → EnvU ρι (den D N)) → ∀ N → AUndone (ES.hot (hev (listHot n (annotate (elab ρι s)) u D c a) N))
listHot-u n {ρι} s u D c a eu N p r with hot-out r
... | _ , (x , _) , _ = ann-u (3 + N) n (elab ρι s) (den D N) (elab-undone (3 + N) n ρι s (den D N) (eu N)) (c ⊕ [ ix 1 ]) x
