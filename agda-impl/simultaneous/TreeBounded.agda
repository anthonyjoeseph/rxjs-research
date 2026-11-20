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

open import Data.Bool using (Bool; T)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; Later; cold; empty; of; map; scan; takeWhile; flatMap;
  connect; connected; defer)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; inside; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; module TakeWhile; Rejoin; _≺_; _≼_; enter; Proper; module Op; module Connecting; at-end; end; At; Superseded; module ExhaustOn)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≼-refl; ≺-≼-≺; ≼-or-≻; ≼-split; AgreeTo-sym)
open import denotation.Laws.JoinInv using (switch-cut-up; switch-cut-to)
open import denotation.Laws.Worlds using (_⊑_; InvAt; Lawful; Real; _∪ʰ_; ok-step; W; W⁼; Hots; join; here; real-snoc; real-sub;
  plain-ix; plain-last; ok-in; world-after; world-after⁼; inW; step; ⊑-refl; inside-⊑;
  ⊑-inside; ⊑-snoc; lead; l-root; l-in; l-hot; w-up; not-up; ⊕-injʳ; narrow; narrow⁼; shrink; shrink⁼; Plain; nest⁼;
  anc-lead; anc-view; world-anc⁼; world-anc; anc-trans; Anc; self; up; apart; Lead; parent-fun; step-parent; ⊕-injˡ; ext≢)
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
open import simultaneous.TableMap using (map-bounded; tr-map→)
open import simultaneous.TableScan using (scan-bounded; scan-of; scan-src)
open import simultaneous.TableTake using (tr-take→; tr-take←; failed?)
open import simultaneous.TableRows using (part-≺)
open import simultaneous.TableEnv using (_⊕ˡ_; admits-ix; Ren; HotD; hotD; hev; hin; hbd; DenOf; den; den-ex; tab-at; den-ok; dbd; dsettles; HotsAll; w-mono; w-mono⁼; ok-mono; transfer; scope-lead; reader-lead; each; each-at; inside-by; inside-at; dnest; dH; dlo;
  Admits; admits-at; admits-step; admits-row; den-cons; tab-func; tab-flat; tab-inv; pin-ok; after-ok; pin-after-ok)
open import simultaneous.SpinKit using (sp→)
open import simultaneous.Horizon using (Tag; held; past-child; under-child; module Cuts; module SpinB; module TakeB; module ConnB; module ConnBd; module RejoinB; const-bounded;
  bounded-≃)
open import simultaneous.HorizonTree using (Cut; BdEnv; bodyρ; bodyU; bd)
open import simultaneous.Placed using (module Placing)
open import simultaneous.ListTR using (tr-at; ent)
open import simultaneous.HorizonCc using (module CcB)
open import simultaneous.ColdBounded using (cold-bounded; cold-placed)
open import simultaneous.HotRows using (hot-rows-settle)
open import simultaneous.HorizonJoin using (module JoinB; module JoinP)
open import simultaneous.CutParts using (merge-tr→; merge-tr←; cc-tr→; cc-tr←; sw-tr→; sw-tr←; ex-tr→; ex-tr←; conn-tr→; conn-tr←; defer-tr→; defer-tr←; module MarkB)
open import simultaneous.JoinPolicy using (module ExhaustRuns)

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

-- A boundary of one of the scope's hots.
EnvB : ∀ {Γ} → BdEnv Γ → ℕ → Pos → Tag → Set
EnvB {[]}    β N b g = ⊥
EnvB {_ ∷ Γ} β N b g = β (here refl) N b g ⊎ EnvB {Γ} (λ {X} i → β {X} (there i)) N b g

-- Which hot's.
env-elim : ∀ {Γ} (β : BdEnv Γ) {N b g} {P : Set} → (∀ {X : Set} (i : X ∈ Γ) → β i N b g → P) → EnvB β N b g → P
env-elim {[]}    β k ()
env-elim {_ ∷ Γ} β k (inj₁ x) = k (here refl) x
env-elim {_ ∷ Γ} β k (inj₂ y) = env-elim (λ {X} i → β {X} (there i)) (λ i → k (there i)) y

-- One of them.
env-in : ∀ {Γ} (β : BdEnv Γ) {X : Set} (i : X ∈ Γ) {N b g} → β i N b g → EnvB β N b g
env-in {_ ∷ Γ} β (here refl) x = inj₁ x
env-in {_ ∷ Γ} β (there i)   x = inj₂ (env-in (λ {X} j → β {X} (there j)) i x)

------------------------------------------------------------------------
-- Placement carried from a child

-- A row standing on a row of another cut: at it, or one plain label
-- under it.
StandsOn : ∀ {A} → EmissionSet A → Pos → Set
StandsOn {A} c x = Σ Pos λ y → Σ (Ev A) (c y) × (x ≡ y ⊎ Σ Label λ l → Plain l × x ≡ y ⊕ [ l ])

-- A cut whose rows stand on another's keeps the other's placement of
-- fewer boundaries: a plain child of its row lies in the world of one of
-- the other's.
placed-sub : ∀ {A B : Set} {H : ℕ → Pos → Set} {Env : ℕ → Pos → Tag → Set} {p} {c : ℕ → EmissionSet A} {c′ : ℕ → EmissionSet B}
             {Bd Bd′ : ℕ → Pos → Tag → Set}
           → (∀ {N x e} → c′ N x e → StandsOn (c N) x) → (∀ {N b g} → Bd′ N b g → Bd N b g)
           → Placing.Placed H Env p c Bd → Placing.Placed H Env p c′ Bd′
placed-sub {A} {B} {H} {Env} {p} {c} {c′} {Bd} {Bd′} st sb P bd′ = [ (λ own → inj₁ (keep own)) , inj₂ ]′ (P (sb bd′))
  where
    module O = Placing H Env p c
    module O′ = Placing H Env p c′

    under′ : ∀ {N b g} → O.Own N b g → ∀ {x l w} → StandsOn (c N) x → Plain l → W⁼ (H N) (x ⊕ [ l ]) w → ¬ w ⊑ b
    under′ own (y , (_ , cy) , inj₁ refl)            pl v = O.Own.under own cy pl v
    under′ own (y , (_ , cy) , inj₂ (l′ , pl′ , refl)) pl v = O.Own.under own cy pl′ (nest⁼ (inW (step here pl)) v)

    keep : ∀ {N b g} → O.Own N b g → O′.Own N b g
    keep own = record { world = O.Own.world own ; real = O.Own.real own ; holder = O.Own.holder own
                      ; under = λ x pl v → under′ own (st x) pl v }

-- A take's rows stand on its child's: at a passing value, a step, an end
-- or a pin, and one label under the failing value.
take-stands : ∀ {X : Set} i (keep : X → Bool) {t : EmissionSet X} {k e} → TakeWhile.TakeT i keep t k e → StandsOn t k
take-stands i keep (TakeWhile.pass x _ _)   = _ , (_ , x) , inj₁ refl
take-stands i keep (TakeWhile.fail x _ _ _) = _ , (_ , x) , inj₂ (ix 0 , plain-ix , refl)
take-stands i keep (TakeWhile.stop x _ _)   = _ , (_ , x) , inj₂ (last , plain-last , refl)
take-stands i keep (TakeWhile.step x _)     = _ , (_ , x) , inj₁ refl
take-stands i keep (TakeWhile.tend x _)     = _ , (_ , x) , inj₁ refl
take-stands i keep (TakeWhile.left x _ _)   = _ , (_ , x) , inj₁ refl

module _ {Γ} (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) where
  -- A tree subscribed at `p`'s placement.
  PlacedAt : ∀ {A} n (o : Obs Timeline Γ A) p → Set
  PlacedAt n o p = Placing.Placed (λ N → Hots (den D N)) (EnvB (dbd D)) p (Cut n o ρ p) (bd n o ρ uρ (dbd D) p)

  -- A SPIN'S NEXT TICK lies one label under its subscription, and a plain
  -- child of an earlier tick reaches nothing that leads it: not the
  -- subscription, which precedes the tick, nor the next tick, whose only
  -- parent is the subscription.
  placed-spin : ∀ {A} (l : Later Timeline Γ A) p → Admits D p → PlacedAt zero (defer l) p
  placed-spin l p a {N} (refl , refl) = inj₁ (record
    { world = step here plain-ix ; real = real-snoc p plain-ix rp ; under = under ; holder = λ () })
    where
      rp = proj₁ (proj₁ a)

      under : ∀ {x e k w} → Cut zero (defer l) ρ p N x e → Plain k → W⁼ (Hots (den D N)) (x ⊕ [ k ]) w → ¬ w ⊑ (p ⊕ [ ix (3 + N) ])
      under x pl v le with sp→ x
      ... | i , _ , refl , refl with ⊑-snoc p le
      ...   | inj₁ wp   = anc-lead (world-anc⁼ v) wp rp (≺-trans {p} {p ⊕ [ ix i ]} (≺-ext p []) (≺-ext (p ⊕ [ ix i ]) []))
      ...   | inj₂ refl with anc-view (world-anc⁼ v)
      ...     | inj₁ eq = ext≢ p [] (⊕-injˡ (p ⊕ [ ix i ]) p eq)
      ...     | inj₂ (b , ab , pb) with parent-fun pb (step-parent p plain-ix)
      ...       | refl = anc-lead ab (⊑-refl p) rp (≺-trans {p} {p ⊕ [ ix i ]} (≺-ext p []) (≺-ext (p ⊕ [ ix i ]) []))

  -- A DEFER'S are its body's, one label down: the body's world lies in
  -- the defer's, and its marker's plain children reach nothing leading a
  -- position of the body's world, apart from it under the subscription.
  placed-defer : ∀ {A} n (l : Later Timeline Γ A) p → Admits D p → PlacedAt n (Later.force l) (p ⊕ [ ix 1 ])
               → PlacedAt (suc n) (defer l) p
  placed-defer n l p a P {N} bi = [ (λ own → inj₁ (keep own)) , inj₂ ]′ (P bi)
    where
      H : Pos → Set
      H = Hots (den D N)

      module O  = Placing (λ M → Hots (den D M)) (EnvB (dbd D)) (p ⊕ [ ix 1 ]) (Cut n (Later.force l) ρ (p ⊕ [ ix 1 ]))
      module O′ = Placing (λ M → Hots (den D M)) (EnvB (dbd D)) p (Cut (suc n) (defer l) ρ p)

      rp : Real p
      rp = proj₁ (proj₁ a)

      from0 : ∀ {k w} → Plain k → W⁼ H ((p ⊕ [ ix 0 ]) ⊕ [ k ]) w → Anc (p ⊕ [ ix 0 ]) w
      from0 pl v = anc-trans (up self (step-parent (p ⊕ [ ix 0 ]) pl)) (world-anc⁼ v)

      root-case : ∀ {k w} → Plain k → W⁼ H ((p ⊕ [ ix 0 ]) ⊕ [ k ]) w → w ⊑ (p ⊕ [ ix 1 ]) → ⊥
      root-case pl v r with ⊑-snoc p r
      ... | inj₁ wp   = anc-lead (world-anc⁼ v) wp rp (≺-trans {p} {p ⊕ [ ix 0 ]} (≺-ext p []) (≺-ext (p ⊕ [ ix 0 ]) []))
      ... | inj₂ refl = apart rp (from0 pl v) self

      lead-case : ∀ {k w} → Plain k → W⁼ H ((p ⊕ [ ix 0 ]) ⊕ [ k ]) w → Lead H (p ⊕ [ ix 1 ]) w → ⊥
      lead-case pl v (l-root r)  = root-case pl v r
      lead-case pl v (l-in u)    = apart rp (from0 pl v) (world-anc u)
      lead-case pl v (l-hot hh r) = proj₂ (admits-at D a N) hh (shrink⁼ (nest⁼ (inW (step here pl)) v)) (⊑-inside r)

      keep : ∀ {b g} → O.Own N b g → O′.Own N b g
      keep {b} own = record
        { world = shrink (O.Own.world own) ; real = O.Own.real own
        ; under = under
        ; holder = λ eq → inW (shrink⁼ (proj₁ (O.Own.holder own eq))) , proj₂ (O.Own.holder own eq) }
        where
          under : ∀ {x e k w} → Cut (suc n) (defer l) ρ p N x e → Plain k → W⁼ H (x ⊕ [ k ]) w → ¬ w ⊑ b
          under x pl v le with defer-tr→ n l uρ p x
          ... | inj₁ (refl , refl) = lead-case pl v (lead (inW (O.Own.world own)) le)
          ... | inj₂ cx            = O.Own.under own cx pl v le

  -- A SCOPE'S BOUNDARY is led by no position of an admissible world: its
  -- hot's body's world holds it.
  env-lead : ∀ {p} → Admits D p → ∀ {N b g} → EnvB (dbd D) N b g → ∀ {w} → W⁼ (Hots (den D N)) p w → ¬ w ⊑ b
  env-lead a {N} env v = env-elim (dbd D) (λ i bi → reader-lead D a i bi {N} v) env

  -- A SOURCE'S BOUNDARIES lie before its connect or past its
  -- subscription: its own in its world, its scope's led by neither the
  -- connect nor the subscription.
  src-out : ∀ {A} n (s : Obs Timeline Γ A) p → Admits D p → PlacedAt n s (p ⊕ [ ix 1 ]) → ∀ {N b g} → bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b g → b ≺ p ⊎ (p ⊕ [ ix 1 ]) ≺ b
  src-out n s p a P {N} {b} bd with P bd
  ... | inj₁ own = inj₂ (world-after (Placing.Own.world own) (Placing.Own.real own))
  ... | inj₂ env with ≼-or-≻ b p
  ...   | inj₂ pb = inj₂ (past-child (ix 1) pb (env-lead a env here))
  ...   | inj₁ bp with ≼-split {b} {p} bp
  ...     | inj₁ lt   = inj₁ lt
  ...     | inj₂ refl = ⊥-elim (env-lead a env here (⊑-refl b))

  -- A held one in its burst waits on a connect there: its own's in the
  -- source's world, and no scope boundary lies under the subscription.
  src-held : ∀ {A} n (s : Obs Timeline Γ A) p → Admits D p → PlacedAt n s (p ⊕ [ ix 1 ]) → ∀ {N b q} → bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b (held q) → T (inside (p ⊕ [ ix 1 ]) b) → (p ⊕ [ ix 1 ]) ≼ q
  src-held n s p a P {N} {b} {q} bd ins with P bd
  ... | inj₁ own = world-after⁼ (proj₁ (Placing.Own.holder own refl)) (proj₂ (Placing.Own.holder own refl))
  ... | inj₂ env = ⊥-elim (env-lead a env (inW (step here plain-ix)) (inside-⊑ (p ⊕ [ ix 1 ]) b ins))

  -- A DEFER'S MARKER, under its first label, leads no boundary of its
  -- body, subscribed one label down: the body's own lie in its world,
  -- which the marker's sibling does not lead, and its scope's under no
  -- position of the defer's.
  defer-apart : ∀ {A} n (l : Later Timeline Γ A) p → Admits D p → PlacedAt n (Later.force l) (p ⊕ [ ix 1 ])
              → ∀ {N b g} → bd n (Later.force l) ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b g → ¬ (p ⊕ [ ix 0 ]) ⊑ b
  defer-apart n l p a P {N} bd le with P bd
  ... | inj₂ env = env-lead a env (inW (step here plain-ix)) le
  ... | inj₁ own with lead (inW (Placing.Own.world own)) le
  ...   | l-hot hh r = proj₂ (admits-at D a N) hh (step here plain-ix) (⊑-inside r)
  ...   | l-in v with w-up plain-ix (inW v)
  ...     | inj₂ v′ = not-up (proj₁ (proj₁ a)) v′ (⊑-refl p)
  ...     | inj₁ eq with ⊕-injʳ p p eq
  ...       | ()
  defer-apart n l p a P {N} bd le | inj₁ own | l-root r with ⊑-snoc p r
  ...   | inj₁ r′ = not-up {H = Hots (den D N)} (proj₁ (proj₁ a)) here r′
  ...   | inj₂ eq with ⊕-injʳ p p eq
  ...     | ()

-- A cut's row is a row of its reading.
cut-enter : ∀ {Γ A} n (o : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) q N
          → ∀ {k e} → Cut n o ρ q N k e → enter (capprox (3 + N) n o (den D N)) q k e
cut-enter n o uρ D q N x with listC-ok (3 + N) n o (uρ N) q
... | L , eq , uL = sound (listC-exact (3 + N) n o (den-ex D N) q eq uL) (tr-at eq x)

-- A CONNECT'S GAPS, over the hot `hD` listing its source's rows.  A
-- source boundary of its own lies in the source's world, which no body
-- position leads; a scope's, under no position of the connect's.
conn-gap-sb : ∀ {Γ A B} (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (a : Admits D p)
            {t : ℕ → Tb.Listed A} (hD : HotD D t) (u′ : ∀ N → UncutEnv (t N ∷ ρ N)) (a′ : Admits (den-cons hD) (p ⊕ [ ix 0 ]))
            (σrow : ∀ N {h e} → hev hD N h e → enter (capprox (3 + N) n s (den D N)) (p ⊕ [ ix 1 ]) h e)
            → PlacedAt ρ uρ D n s (p ⊕ [ ix 1 ])
            → ∀ {N b′ g y e} → bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]) N b′ g → Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ]) N y e → ¬ y ⊑ b′
conn-gap-sb ρ uρ D n s b p a {t} hD u′ a′ σrow P {N} {b′} {g} {y} bd′ x le =
  [ (λ own → Cn.Apart.body-leads (hev hD N) p (admits-at D a N) σw (inW yw) (inW (Placing.Own.world own)) le)
  , (λ env → env-lead ρ uρ D a env (inW (narrow⁼ (λ z → shrink (σw z)) (inW yw))) le) ]′
  (P bd′)
  where
    σw : ∀ {h e} → hev hD N h e → W (Hots (den D N)) (p ⊕ [ ix 1 ]) h
    σw z = InvAt.world (inv-capprox (3 + N) n s (den D N) (den-ok D N) (p ⊕ [ ix 1 ]) (ok-step p (admits-at D a N))) (σrow N z)

    yw : W (Hots (den (den-cons hD) N)) (p ⊕ [ ix 0 ]) y
    yw = InvAt.world (tab-at n b u′ (den-cons hD) a′ N) x

-- A body boundary of its own is led by a source position only through a
-- joined source row, which would lie under another's plain child; the
-- body's scope's are its source's, or the connect's scope's.
conn-gap-bs : ∀ {Γ A B} (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (a : Admits D p)
            {t : ℕ → Tb.Listed A} (hD : HotD D t) (u′ : ∀ N → UncutEnv (t N ∷ ρ N)) (a′ : Admits (den-cons hD) (p ⊕ [ ix 0 ]))
            (σrow : ∀ N {h e} → hev hD N h e → enter (capprox (3 + N) n s (den D N)) (p ⊕ [ ix 1 ]) h e)
            (sgap : ∀ {N b′ g k e} → hbd hD N b′ g → Cut n s ρ (p ⊕ [ ix 1 ]) N k e → ¬ k ⊑ b′)
            → PlacedAt (λ M → t M ∷ ρ M) u′ (den-cons hD) n b (p ⊕ [ ix 0 ])
            → ∀ {N b′ g k e} → bd n b (λ M → t M ∷ ρ M) u′ (dbd (den-cons hD)) (p ⊕ [ ix 0 ]) N b′ g → Cut n s ρ (p ⊕ [ ix 1 ]) N k e → ¬ (k ⊕ [ ix 0 ]) ⊑ b′
conn-gap-bs ρ uρ D n s b p a {t} hD u′ a′ σrow sgap P {N} {b′} {g} {k} {e} bd′ x le =
  [ (λ own → through (Cn.Apart.source-leads (hev hD N) p (admits-at D a N) σw (inW (step (inW kw) plain-ix)) (inW (Placing.Own.world own)) le))
  , [ (λ sb → under-child (ix 0) (sgap sb x) le)
    , (λ env → env-lead ρ uρ D a env (inW (shrink⁼ (inW (step (inW kw) plain-ix)))) le) ]′ ]′
  (P bd′)
  where
    I : InvAt (Hots (den D N)) (p ⊕ [ ix 1 ]) (enter (capprox (3 + N) n s (den D N)) (p ⊕ [ ix 1 ]))
    I = inv-capprox (3 + N) n s (den D N) (den-ok D N) (p ⊕ [ ix 1 ]) (ok-step p (admits-at D a N))

    σw : ∀ {h e} → hev hD N h e → W (Hots (den D N)) (p ⊕ [ ix 1 ]) h
    σw z = InvAt.world I (σrow N z)

    kx : enter (capprox (3 + N) n s (den D N)) (p ⊕ [ ix 1 ]) k e
    kx = cut-enter n s uρ D (p ⊕ [ ix 1 ]) N x

    kw : W (Hots (den D N)) (p ⊕ [ ix 1 ]) k
    kw = InvAt.world I kx

    through : ∀ {z} → Cn.Apart.Through (hev hD N) p (admits-at D a N) σw (k ⊕ [ ix 0 ]) z → ⊥
    through (_ , _ , (_ , σh) , kh , _) = InvAt.under I kx (σrow N σh) plain-ix here kh

-- A CONNECT'S BOUNDARIES ARE PLACED, over the hot `hD` listing its
-- source's rows: a source boundary of its own lies in the source's
-- world, a body boundary of its own in the body's, and the body's scope
-- is the source's hot or the connect's scope.  A plain child of a source
-- row leads a body position only through a joined source row, which
-- would lie under it; a plain child of a body row lies in the body's
-- world, which leads no source position.  A burst's boundary lies under
-- the connect, where no scope boundary does.
conn-placed : ∀ {Γ A B} (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (a : Admits D p)
            {t : ℕ → Tb.Listed A} (hD : HotD D t) (u′ : ∀ N → UncutEnv (t N ∷ ρ N)) (a′ : Admits (den-cons hD) (p ⊕ [ ix 0 ]))
            (σrow : ∀ N {h e} → hev hD N h e → enter (capprox (3 + N) n s (den D N)) (p ⊕ [ ix 1 ]) h e)
            → Placing.Placed (λ N → Hots (den D N)) (EnvB (dbd D)) (p ⊕ [ ix 1 ]) (Cut n s ρ (p ⊕ [ ix 1 ])) (hbd hD)
            → Placing.Placed (λ N → Hots (den (den-cons hD) N)) (EnvB (dbd (den-cons hD))) (p ⊕ [ ix 0 ])
                (Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ])) (bd n b (λ M → t M ∷ ρ M) u′ (dbd (den-cons hD)) (p ⊕ [ ix 0 ]))
            → Placing.Placed (λ N → Hots (den D N)) (EnvB (dbd D)) p
                (λ N → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ]) N))
                (ConnBd.CBd p (Cut n s ρ (p ⊕ [ ix 1 ])) (Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ])) (hbd hD)
                  (bd n b (λ M → t M ∷ ρ M) u′ (dbd (den-cons hD)) (p ⊕ [ ix 0 ])))
conn-placed ρ uρ D n s b p a {t} hD u′ a′ σrow Ps Pb {N} bi = placed bi
  where
    H : Pos → Set
    H = Hots (den D N)

    σ β : EmissionSet _
    σ = Cut n s ρ (p ⊕ [ ix 1 ]) N
    β = Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ]) N

    module S  = Placing (λ M → Hots (den D M)) (EnvB (dbd D)) (p ⊕ [ ix 1 ]) (Cut n s ρ (p ⊕ [ ix 1 ]))
    module Bo = Placing (λ M → Hots (den (den-cons hD) M)) (EnvB (dbd (den-cons hD))) (p ⊕ [ ix 0 ]) (Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ]))
    module C  = Placing (λ M → Hots (den D M)) (EnvB (dbd D)) p (λ M → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) M) (Cut n b (λ M′ → t M′ ∷ ρ M′) (p ⊕ [ ix 0 ]) M))
    rp : Real p
    rp = proj₁ (proj₁ a)

    I : InvAt H (p ⊕ [ ix 1 ]) (enter (capprox (3 + N) n s (den D N)) (p ⊕ [ ix 1 ]))
    I = inv-capprox (3 + N) n s (den D N) (den-ok D N) (p ⊕ [ ix 1 ]) (ok-step p (admits-at D a N))

    σw : ∀ {h e} → hev hD N h e → W H (p ⊕ [ ix 1 ]) h
    σw z = InvAt.world I (σrow N z)

    σwp : ∀ {h e} → hev hD N h e → W H p h
    σwp z = shrink (σw z)

    module Ap = Cn.Apart (hev hD N) p (admits-at D a N) σw

    -- A plain child of a source row, in the source's world.
    src-child : ∀ {k e l w} → σ k e → Plain l → W⁼ H ((k ⊕ [ ix 0 ]) ⊕ [ l ]) w → W⁼ H (p ⊕ [ ix 1 ]) w
    src-child x pl v = nest⁼ (inW (step (inW (InvAt.world I (cut-enter n s uρ D (p ⊕ [ ix 1 ]) N x))) plain-ix)) (nest⁼ (inW (step here pl)) v)

    -- A plain child of a body row, in the body's world.
    body-child : ∀ {y e l w} → β y e → Plain l → W⁼ H (y ⊕ [ l ]) w → W⁼ (Hots (den (den-cons hD) N)) (p ⊕ [ ix 0 ]) w
    body-child x pl v = nest⁼ (inW (InvAt.world (tab-at n b u′ (den-cons hD) a′ N) x)) (nest⁼ (inW (step here pl)) (w-mono⁼ inj₂ v))

    -- A source boundary of its own, kept by the connect under its tag.
    src-own : ∀ {c g g′} → S.Own N c g′ → (∀ {q} → g ≡ held q → W⁼ H p q × Real q) → C.Own N c g
    src-own {c} own hold = record { world = shrink (S.Own.world own) ; real = S.Own.real own ; under = under ; holder = hold }
      where
        under : ∀ {x e l w} → Connecting.ConnT p σ β x e → Plain l → W⁼ H (x ⊕ [ l ]) w → ¬ w ⊑ c
        under (Connecting.body y)       pl v le = Ap.body-leads (body-child y pl v) (inW (S.Own.world own)) le
        under (Connecting.burst x _)     pl v le = S.Own.under own x plain-ix (nest⁼ (inW (step here pl)) v) le
        under (Connecting.echo x _ _ _)  pl v le = S.Own.under own x plain-ix (nest⁼ (inW (step here pl)) v) le
        under (Connecting.kept x _ _ _)  pl v le = S.Own.under own x plain-ix (nest⁼ (inW (step here pl)) v) le

    -- Its held tag waits where the source's does.
    src-hold : ∀ {c g′} → S.Own N c g′ → ∀ {q} → g′ ≡ held q → W⁼ H p q × Real q
    src-hold own eq = inW (shrink⁼ (proj₁ (S.Own.holder own eq))) , proj₂ (S.Own.holder own eq)

    -- A body boundary of its own, in the body's world.
    body-own : ∀ {c g} → Bo.Own N c g → C.Own N c g
    body-own {c} own = record
      { world = narrow σwp (Bo.Own.world own) ; real = Bo.Own.real own ; under = under
      ; holder = λ eq → inW (narrow⁼ σwp (proj₁ (Bo.Own.holder own eq))) , proj₂ (Bo.Own.holder own eq) }
      where
        through : ∀ {k e l w} → σ k e → Plain l → W⁼ H ((k ⊕ [ ix 0 ]) ⊕ [ l ]) w → Ap.Through w c → ⊥
        through x pl v (_ , _ , (_ , σh) , wh , _) =
          InvAt.under I (cut-enter n s uρ D (p ⊕ [ ix 1 ]) N x) (σrow N σh) plain-ix (nest⁼ (inW (step here pl)) v) wh

        under : ∀ {x e l w} → Connecting.ConnT p σ β x e → Plain l → W⁼ H (x ⊕ [ l ]) w → ¬ w ⊑ c
        under (Connecting.body y)       pl v le = Bo.Own.under own y pl (w-mono⁼ inj₂ v) le
        under (Connecting.burst x _)     pl v le = through x pl v (Ap.source-leads (src-child x pl v) (inW (Bo.Own.world own)) le)
        under (Connecting.echo x _ _ _)  pl v le = through x pl v (Ap.source-leads (src-child x pl v) (inW (Bo.Own.world own)) le)
        under (Connecting.kept x _ _ _)  pl v le = through x pl v (Ap.source-leads (src-child x pl v) (inW (Bo.Own.world own)) le)

    placed : ∀ {c g} → ConnBd.CBd p (Cut n s ρ (p ⊕ [ ix 1 ])) (Cut n b (λ M → t M ∷ ρ M) (p ⊕ [ ix 0 ])) (hbd hD)
                         (bd n b (λ M → t M ∷ ρ M) u′ (dbd (den-cons hD)) (p ⊕ [ ix 0 ])) N c g → C.Own N c g ⊎ EnvB (dbd D) N c g
    placed (ConnBd.bodyB x) with Pb x
    ... | inj₁ own         = inj₁ (body-own own)
    ... | inj₂ (inj₂ env)  = inj₂ env
    ... | inj₂ (inj₁ sb) with Ps sb
    ...   | inj₁ own = inj₁ (src-own own (src-hold own))
    ...   | inj₂ env = inj₂ env
    placed (ConnBd.burstB x ins) with Ps x
    ... | inj₁ own = inj₁ (src-own own (λ { refl → here , rp }))
    ... | inj₂ env = ⊥-elim (env-lead ρ uρ D a env (inW (step here plain-ix)) (inside-⊑ (p ⊕ [ ix 1 ]) _ ins))
    placed (ConnBd.echoB x _ _) with Ps x
    ... | inj₁ own = inj₁ (src-own own (λ ()))
    ... | inj₂ env = inj₂ env
    placed (ConnBd.keptB x _ _) with Ps x
    ... | inj₁ own = inj₁ (src-own own (src-hold own))
    ... | inj₂ env = inj₂ env

------------------------------------------------------------------------
-- Every tree, and the hot a connect lists

mutual
  -- A CONNECT'S HOT: its source listed under the connect's second label.
  listHot : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c → Admits D c
          → HotD D (λ N → hotOf (proj₁ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ]))))

  -- Its body admissible where the connect is.
  admits-body : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c (a : Admits D c)
              → Admits (den-cons (listHot n o u D c a)) (c ⊕ [ ix 0 ])

  -- EVERY TREE'S CUTS ARE BOUNDED BY ITS BOUNDARIES.
  tree-bounded : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ)
               → ∀ p → Admits D p → Cuts.Bounded (Cut n o ρ p) (bd n o ρ uρ (dbd D) p)

  -- EVERY TREE'S BOUNDARIES ARE PLACED: its own in its world, its scope's
  -- named by the scope.
  tree-placed : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ)
              → ∀ p → Admits D p → PlacedAt ρ uρ D n o p

  listHot {X = X} n o {ρ} u D c a =
    hotD hv hx hl c a src-in (bd n o ρ u (dbd D) (c ⊕ [ ix 1 ]))
      (hot-rows-settle n o u c (tree-bounded n o ρ u D (c ⊕ [ ix 1 ]) (admits-step D a)))
      src-lead
    where
      hv : ℕ → EmissionSet _
      hv = listEv n o D c

      -- The source's rows at every cut, each in the source's world.
      src-in : ∀ N {h e} → hv N h e → W (HotsAll D) (c ⊕ [ ix 1 ]) h
      src-in N x = w-mono (λ hh → N , hh)
        (InvAt.world (inv-capprox (3 + N) n o (den D N) (den-ok D N) (c ⊕ [ ix 1 ]) (ok-step c (admits-at D a N))) (proj₁ x))

      σ∞ : EmissionSet X
      σ∞ h e = Σ ℕ λ N → hv N h e

      -- The body's world, read from a scope hot's body's.
      into : ∀ {Y : Set} (i : Y ∈ _) {h} → (HotsAll D ∪ʰ σ∞) h → dH D i h ⊎ W (dH D i) (dlo D i) h
      into i (inj₂ hh)          = dnest D i hh
      into i (inj₁ (_ , M , x)) = inj₂ (transfer (dnest D i) (inW (step (each-at (proj₂ a) i) plain-ix)) (src-in M x))

      -- A source boundary of its own lies in the source's world, which no
      -- body position leads; a scope's, in its hot's body's world.
      src-lead : ∀ {N b g w} → bd n o ρ u (dbd D) (c ⊕ [ ix 1 ]) N b g → W⁼ (HotsAll D ∪ʰ σ∞) (c ⊕ [ ix 0 ]) w → ¬ w ⊑ b
      src-lead {N} bi v =
        [ (λ own → Cn.Apart.body-leads σ∞ c (proj₁ a) (λ { (M , x) → src-in M x }) v (inW (w-mono (λ hh → N , hh) (Placing.Own.world own))))
        , env-elim (dbd D) (λ i bj → scope-lead D i bj (into i) (inW (step (each-at (proj₂ a) i) plain-ix)) v) ]′
        (tree-placed n o ρ u D (c ⊕ [ ix 1 ]) (admits-step D a) bi)

      hx : ∀ N p → Exactly (rejoin p (hotOf (proj₁ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ]))))) (enter (ES.hot (hv N)) p)
      hx N p = truncate-exact (rejoin-exact (proper-exact (listC-exact (3 + N) n o (den-ex D N) (c ⊕ [ ix 1 ]) (proj₁ (proj₂ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ])))))) p)

      hl : ∀ N → Lawful (hv N)
      hl N = Cn.lawful {s = capprox (3 + N) n o (den D N)} {F = λ _ → Op.empty {X}} (inv-capprox (3 + N) n o (den D N) (den-ok D N)) (λ _ → empty-inv) c (admits-at D a N)

  admits-body {X = X} n o u D c a =
    ok-mono into (Cn.Apart.ok₀ σ∞ c (proj₁ a) σw) , here , each (λ i → inW (step (each-at (proj₂ a) i) plain-ix))
    where
      hD = listHot n o u D c a

      σ∞ : EmissionSet X
      σ∞ h e = Σ ℕ λ N → hev hD N h e

      σw : ∀ {h e} → σ∞ h e → W (HotsAll D) (c ⊕ [ ix 1 ]) h
      σw (N , x) = hin hD N x

      into : ∀ {h} → HotsAll (den-cons hD) h → (HotsAll D ∪ʰ σ∞) h
      into (N , inj₁ (e , x)) = inj₁ (e , N , x)
      into (N , inj₂ hh)      = inj₂ (N , hh)

  tree-placed n       (cold c)          ρ uρ D p a = cold-placed n c ρ p (admits-at D a)
  tree-placed n       empty             ρ uρ D p a = λ ()
  tree-placed n       (of xs)           ρ uρ D p a = λ ()
  tree-placed n       (map f s)         ρ uρ D p a =
    placed-sub (λ {N} x → let (e₀ , x₀ , _) = tr-map→ f (listC (3 + N) n s (ρ N) p) x in _ , (e₀ , x₀) , inj₁ refl) (λ b → b)
      (tree-placed n s ρ uρ D p a)
  tree-placed n       (scan f z s)      ρ uρ D p a =
    placed-sub (λ {N} x → _ , scan-src (proj₁ (scan-of f z (listC-ok (3 + N) n s (uρ N) p)) x) , inj₁ refl) (λ b → b)
      (tree-placed n s ρ uρ D p a)
  tree-placed n       (takeWhile i q s) ρ uρ D p a =
    placed-sub {Bd′ = bd n (takeWhile i q s) ρ uρ (dbd D) p} (λ {N} x → take-stands i q (tr-take→ i q (listC (3 + N) n s (ρ N) p) x)) (λ { (b , _) → b }) (tree-placed n s ρ uρ D p a)
  tree-placed n (flatMap (mergeᶠ nothing) f s)  ρ uρ D p a =
    placed-sub (λ {N} x → _ , (_ , merge-tr→ n f s uρ p x) , inj₁ refl) (λ b → b)
      (JoinP.placed (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q) (λ _ _ → ⊤) (λ _ _ _ → ⊥)
        (λ {N} {y} {e} {e′} → tab-func n s uρ D a {N} {y} {e} {e′})
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → tab-at n s uρ D a N) (λ N → proj₂ (admits-at D a N))
        (λ {N} {q} {v} {y} {e} x l → InvAt.world (tab-at n (f v) uρ D (admits-row n s uρ D a x) N) l)
        (tree-placed n s ρ uρ D p a)
        (λ {N} {q} {v} x → tree-placed n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x)))
  tree-placed n (flatMap (mergeᶠ (just k)) f s) ρ uρ D p a =
    placed-sub (λ {N} x → _ , (_ , cc-tr→ n f s uρ p k x) , inj₁ refl) (λ b → b)
      (CcB.placed k (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (tree-bounded n s ρ uρ D p a)
        (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q) (Admits D)
        (λ {v} {q} ad → tree-bounded n (f v) ρ uρ D q ad)
        (λ {N} {v} {q} x → proj₂ (ent (3 + N) n (f v) (uρ N) q x))
        (λ {N} {v} {q} l → pin-after-ok (3 + N) n (f v) {ρ N} q l)
        (λ {N} {v} {q} l → pin-ok (3 + N) n (f v) {ρ N} q l)
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → admits-at D a N) (λ N → tab-at n s uρ D a N)
        (λ N v q oks → tab-inv (3 + N) n (f v) (den-ex D N) (den-ok D N) (uρ N) q oks)
        (λ {N} x → admits-row n s uρ D a x) (λ {N} {v} {q} ad x → admits-row n (f v) uρ D ad x)
        (λ {N} {b} {g} → tree-placed n s ρ uρ D p a {N} {b} {g})
        (λ {v} {q} ad {M} {b} {g} → tree-placed n (f v) ρ uρ D q ad {M} {b} {g})
        (λ {N} {b} {g} env {w} → env-lead ρ uρ D a {N} {b} {g} env {w}))
  tree-placed n (flatMap switchᶠ f s)           ρ uρ D p a =
    placed-sub (λ {N} x → _ , (_ , sw-tr→ n f s uρ p x) , inj₁ refl) (λ b → b)
      (JoinP.placed (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q) (λ _ _ → ⊤) (λ N → Superseded (Cut n s ρ p N))
        (λ {N} {y} {e} {e′} → tab-func n s uρ D a {N} {y} {e} {e′})
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → tab-at n s uρ D a N) (λ N → proj₂ (admits-at D a N))
        (λ {N} {q} {v} {y} {e} x l → InvAt.world (tab-at n (f v) uρ D (admits-row n s uρ D a x) N) l)
        (tree-placed n s ρ uρ D p a)
        (λ {N} {q} {v} x → tree-placed n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x)))
  tree-placed n (flatMap exhaustᶠ f s)           ρ uρ D p a =
    placed-sub (λ {N} x → _ , (_ , ex-tr→ n f s uρ p x) , inj₁ refl) (λ b → b)
      (JoinP.placed (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q) (λ N → ExhaustOn.Run (At (λ v q → Cut n (f v) ρ q N)) (Cut n s ρ p N)) (λ _ _ _ → ⊥)
        (λ {N} {y} {e} {e′} → tab-func n s uρ D a {N} {y} {e} {e′})
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → tab-at n s uρ D a N) (λ N → proj₂ (admits-at D a N))
        (λ {N} {q} {v} {y} {e} x l → InvAt.world (tab-at n (f v) uρ D (admits-row n s uρ D a x) N) l)
        (tree-placed n s ρ uρ D p a)
        (λ {N} {q} {v} x → tree-placed n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x)))
  tree-placed n       (connect s b)     ρ uρ D p a =
    placed-sub (λ {N} x → _ , (_ , conn-tr→ n s b uρ p x) , inj₁ refl) (λ b → b)
      (conn-placed ρ uρ D n s b p a (listHot n s uρ D p a) (bodyU n s uρ p) (admits-body n s uρ D p a) (λ N → proj₁)
        (tree-placed n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a))
        (tree-placed n b (bodyρ n s uρ p) (bodyU n s uρ p) (den-cons (listHot n s uρ D p a)) (p ⊕ [ ix 0 ]) (admits-body n s uρ D p a)))
  tree-placed n       (connected i)     ρ uρ D p a = λ bi → inj₂ (env-in (dbd D) i bi)
  tree-placed zero    (defer l)         ρ uρ D p a = placed-spin ρ uρ D l p a
  tree-placed (suc n) (defer l)         ρ uρ D p a = placed-defer ρ uρ D n l p a (tree-placed n (Later.force l) ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a))

  tree-bounded n       (cold c)          ρ uρ D p a = cold-bounded n c ρ p (proj₁ a)
  tree-bounded n       empty             ρ uρ D p a = const-bounded _
  tree-bounded n       (of xs)           ρ uρ D p a = const-bounded _
  tree-bounded n       (map f s)         ρ uρ D p a = map-bounded f (λ N → listC (3 + N) n s (ρ N) p) (tree-bounded n s ρ uρ D p a)
  tree-bounded n       (scan f z s)      ρ uρ D p a = scan-bounded f z (λ N → listC (3 + N) n s (ρ N) p) (λ N → listC-ok (3 + N) n s (uρ N) p) (tree-bounded n s ρ uρ D p a)
  tree-bounded n       (takeWhile i q s) ρ uρ D p a =
    bounded-≃ (λ {N} → tr-take← i q (listC (3 + N) n s (ρ N) p)) (λ {N} → tr-take→ i q (listC (3 + N) n s (ρ N) p))
      (TakeB.bounded′ i q (Cut n s ρ p) (bd n s ρ uρ (dbd D) p)
        (λ N → record { func = tab-func n s uρ D a {N} ; flat = tab-flat n s uρ D a {N} ; pin-in = pin-ok (3 + N) n s p })
        (λ N → failed? i q (listC (3 + N) n s (ρ N) p))
        (λ N w → keys (listC (3 + N) n s (ρ N) p) , λ x _ → in-keys x)
        (tree-bounded n s ρ uρ D p a))
  tree-bounded n (flatMap (mergeᶠ nothing) f s) ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → merge-tr← n f s uρ p {N} {y} {e}) (λ {N} {y} {e} → merge-tr→ n f s uρ p {N} {y} {e})
      (JoinB.bounded (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (tree-bounded n s ρ uρ D p a)
        (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q)
        (λ {N} {q} {v} x → tree-bounded n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x))
        (λ {N} {M} {q} {v} x l → pin-after-ok (3 + M) n (f v) {ρ M} (q ⊕ [ ix 1 ]) l)
        (λ {N} {q} {v} x l → pin-ok (3 + N) n (f v) {ρ N} (q ⊕ [ ix 1 ]) l)
        (λ {N} {y} {e} {e′} → tab-func n s uρ D a {N} {y} {e} {e′})
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → tab-at n s uρ D a N) (λ N → proj₂ (admits-at D a N))
        (λ {N} {q} {v} {y} {e} x l → InvAt.world (tab-at n (f v) uρ D (admits-row n s uρ D a x) N) l)
        (λ {N} {b} {g} → tree-placed n s ρ uρ D p a {N} {b} {g})
        (λ {N} {q} {v} x {M} {b} {g} → tree-placed n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x) {M} {b} {g})
        (λ {N} {b} {g} env {w} → env-lead ρ uρ D a {N} {b} {g} env {w})
        (λ _ _ → ⊤) (λ _ _ _ → ⊥) (λ ()) (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ → tt) (λ _ _ _ _ → tt))
  tree-bounded n (flatMap (mergeᶠ (just k)) f s) ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → cc-tr← n f s uρ p {N} k {y} {e}) (λ {N} {y} {e} → cc-tr→ n f s uρ p {N} k {y} {e})
      (CcB.bounded k (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (tree-bounded n s ρ uρ D p a)
        (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q) (Admits D)
        (λ {v} {q} ad → tree-bounded n (f v) ρ uρ D q ad)
        (λ {N} {v} {q} x → proj₂ (ent (3 + N) n (f v) (uρ N) q x))
        (λ {N} {v} {q} l → pin-after-ok (3 + N) n (f v) {ρ N} q l)
        (λ {N} {v} {q} l → pin-ok (3 + N) n (f v) {ρ N} q l)
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → admits-at D a N) (λ N → tab-at n s uρ D a N)
        (λ N v q oks → tab-inv (3 + N) n (f v) (den-ex D N) (den-ok D N) (uρ N) q oks)
        (λ {N} x → admits-row n s uρ D a x) (λ {N} {v} {q} ad x → admits-row n (f v) uρ D ad x)
        (λ {N} {b} {g} → tree-placed n s ρ uρ D p a {N} {b} {g})
        (λ {v} {q} ad {M} {b} {g} → tree-placed n (f v) ρ uρ D q ad {M} {b} {g})
        (λ {N} {b} {g} env {w} → env-lead ρ uρ D a {N} {b} {g} env {w}))
  tree-bounded n (flatMap switchᶠ f s) ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → sw-tr← n f s uρ p {N} {y} {e}) (λ {N} {y} {e} → sw-tr→ n f s uρ p {N} {y} {e})
      (JoinB.bounded (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (tree-bounded n s ρ uρ D p a)
        (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q)
        (λ {N} {q} {v} x → tree-bounded n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x))
        (λ {N} {M} {q} {v} x l → pin-after-ok (3 + M) n (f v) {ρ M} (q ⊕ [ ix 1 ]) l)
        (λ {N} {q} {v} x l → pin-ok (3 + N) n (f v) {ρ N} (q ⊕ [ ix 1 ]) l)
        (λ {N} {y} {e} {e′} → tab-func n s uρ D a {N} {y} {e} {e′})
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → tab-at n s uρ D a N) (λ N → proj₂ (admits-at D a N))
        (λ {N} {q} {v} {y} {e} x l → InvAt.world (tab-at n (f v) uρ D (admits-row n s uρ D a x) N) l)
        (λ {N} {b} {g} → tree-placed n s ρ uρ D p a {N} {b} {g})
        (λ {N} {q} {v} x {M} {b} {g} → tree-placed n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x) {M} {b} {g})
        (λ {N} {b} {g} env {w} → env-lead ρ uρ D a {N} {b} {g} env {w})
        (λ _ _ → ⊤) (λ N → Superseded (Cut n s ρ p N))
        (λ {N} {q} {k} {y} → switch-cut-up (Cut n s ρ p N) {q} {k} {y})
        (λ {N} {N′} {k} {q} {y} ag yk → switch-cut-to {o = Cut n s ρ p N} {Cut n s ρ p N′} {k} {q} {y} ag yk)
        (λ {N} {N′} {k} {q} {y} ag yk → switch-cut-to {o = Cut n s ρ p N′} {Cut n s ρ p N} {k} {q} {y} (AgreeTo-sym ag) yk)
        (λ _ _ _ _ → tt) (λ _ _ _ _ → tt))
  tree-bounded n (flatMap exhaustᶠ f s) ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → ex-tr← n f s uρ p {N} {y} {e}) (λ {N} {y} {e} → ex-tr→ n f s uρ p {N} {y} {e})
      (JoinB.bounded (Cut n s ρ p) (bd n s ρ uρ (dbd D) p) (tree-bounded n s ρ uρ D p a)
        (λ v q → Cut n (f v) ρ q) (λ v q → bd n (f v) ρ uρ (dbd D) q)
        (λ {N} {q} {v} x → tree-bounded n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x))
        (λ {N} {M} {q} {v} x l → pin-after-ok (3 + M) n (f v) {ρ M} (q ⊕ [ ix 1 ]) l)
        (λ {N} {q} {v} x l → pin-ok (3 + N) n (f v) {ρ N} (q ⊕ [ ix 1 ]) l)
        (λ {N} {y} {e} {e′} → tab-func n s uρ D a {N} {y} {e} {e′})
        (λ N → Hots (den D N)) (EnvB (dbd D)) p (λ N → tab-at n s uρ D a N) (λ N → proj₂ (admits-at D a N))
        (λ {N} {q} {v} {y} {e} x l → InvAt.world (tab-at n (f v) uρ D (admits-row n s uρ D a x) N) l)
        (λ {N} {b} {g} → tree-placed n s ρ uρ D p a {N} {b} {g})
        (λ {N} {q} {v} x {M} {b} {g} → tree-placed n (f v) ρ uρ D (q ⊕ [ ix 1 ]) (admits-row n s uρ D a x) {M} {b} {g})
        (λ {N} {b} {g} env {w} → env-lead ρ uρ D a {N} {b} {g} env {w})
        (λ N → ExhaustOn.Run (At (λ v q → Cut n (f v) ρ q N)) (Cut n s ρ p N)) (λ _ _ _ → ⊥) (λ ()) (λ _ _ ()) (λ _ _ ())
        (λ {N} {N′} {k} {q} → ExhaustRuns.runs→ (Cut n s ρ p) (λ v q′ → Cut n (f v) ρ q′) {N} {N′} {k} {q})
        (λ {N} {N′} {k} {q} → ExhaustRuns.runs← (Cut n s ρ p) (λ v q′ → Cut n (f v) ρ q′) {N} {N′} {k} {q}))
  tree-bounded n       (connect s b)     ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → conn-tr← n s b uρ p {N} {y} {e}) (λ {N} {y} {e} → conn-tr→ n s b uρ p {N} {y} {e})
      (ConnB.bounded p (Cut n s ρ (p ⊕ [ ix 1 ])) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]))
        (bd n s ρ uρ (dbd D) (p ⊕ [ ix 1 ]))
        (bd n b (bodyρ n s uρ p) (bodyU n s uρ p) (dbd (den-cons (listHot n s uρ D p a))) (p ⊕ [ ix 0 ]))
        (tree-bounded n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a))
        (tree-bounded n b (bodyρ n s uρ p) (bodyU n s uρ p) (den-cons (listHot n s uρ D p a)) (p ⊕ [ ix 0 ]) (admits-body n s uρ D p a))
        (λ {N} {b′} {g} → src-out ρ uρ D n s p a (tree-placed n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a)) {N} {b′} {g})
        (λ {N} {b′} {q} → src-held ρ uρ D n s p a (tree-placed n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a)) {N} {b′} {q})
        (λ {N} {c} x → ≺-≼-≺ {p} {p ⊕ [ ix 0 ]} {c} (≺-ext p []) (after-ok (3 + N) n b (p ⊕ [ ix 0 ]) x))
        (λ {N} {b′} {g} {y} {e} → conn-gap-sb ρ uρ D n s b p a (listHot n s uρ D p a) (bodyU n s uρ p) (admits-body n s uρ D p a) (λ N → proj₁)
           (tree-placed n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a)) {N} {b′} {g} {y} {e})
        (λ {N} {b′} {g} {k} {e} → conn-gap-bs ρ uρ D n s b p a (listHot n s uρ D p a) (bodyU n s uρ p) (admits-body n s uρ D p a) (λ N → proj₁)
           (λ {M} {b″} {g′} {k′} {e′} → Cuts.Bounded.gap (tree-bounded n s ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a)) {M} {b″} {g′} {k′} {e′})
           (tree-placed n b (bodyρ n s uρ p) (bodyU n s uρ p) (den-cons (listHot n s uρ D p a)) (p ⊕ [ ix 0 ]) (admits-body n s uρ D p a)) {N} {b′} {g} {k} {e}))
  tree-bounded n       (connected i)     ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} x → rejoin p (lookup (ρ N) i) , refl , complete (ex N) x)
              (λ {N} {y} {e} → λ { (_ , refl , m) → sound (ex N) m })
      (RejoinB.bounded-j p (λ N → Rows (lookup (ρ N) i)) (dbd D i) (dsettles D i) (λ {N} {b} {g} bi → reader-lead D a i bi {N} (inW (step here plain-last))))
    where
      ex : ∀ N → Exact (rejoin p (lookup (ρ N) i)) (Rejoin p (Rows (lookup (ρ N) i)))
      ex N = rj (lookup (ρ N) i) p (listC-ok (3 + N) n (connected i) (uρ N) p)
  tree-bounded zero    (defer l)         ρ uρ D p a = SpinB.bounded p
  tree-bounded (suc n) (defer l)         ρ uρ D p a =
    bounded-≃ (λ {N} {y} {e} → defer-tr← n l uρ p {N} {y} {e}) (λ {N} {y} {e} → defer-tr→ n l uρ p {N} {y} {e})
      (MarkB.bounded (p ⊕ [ ix 0 ]) (Cut n (Later.force l) ρ (p ⊕ [ ix 1 ])) (bd n (Later.force l) ρ uρ (dbd D) (p ⊕ [ ix 1 ]))
        (tree-bounded n (Later.force l) ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a))
        (λ {N} {b} {g} → defer-apart ρ uρ D n l p a (tree-placed n (Later.force l) ρ uρ D (p ⊕ [ ix 1 ]) (admits-step D a)) {N} {b} {g}))

-- A SHARED CHILD'S LANE: a connect at `c` whose source is `empty`, its
-- end read by a blocker lane of a flatMap subscribed one label under
-- the body, the child queued behind that blocker.  The child's lane,
-- past the trigger's end, is admissible.
admits-trig : ∀ {Γ} n {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c (a : Admits D c)
            → Admits (den-cons (listHot n (empty {A = ⊤}) u D c a))
                     (c ⊕ˡ (ix 1 ∷ last ∷ sub (c ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ []))
admits-trig n u D c a =
  ok-step (h ⊕ [ sub r ]) (ok-in (proj₁ ar) (join (inj₁ hh) here lt) (real-sub h rh (proj₁ (proj₁ ar)) (≺-trans {r} {h} {h ⊕ [ sub r ]} lt (≺-ext h [])))) ,
  inside-by (den-cons hD) (λ i → inW (step (inW (join (dnest (den-cons hD) i hh) (inside-at (den-cons hD) (proj₂ ar) i) lt)) plain-ix))
  where
    hD = listHot n (empty {A = ⊤}) u D c a
    r h : Pos
    r = c ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])
    h = c ⊕ˡ (ix 1 ∷ last ∷ [])

    ar : Admits (den-cons hD) r
    ar = admits-ix (den-cons hD) 1 (admits-ix (den-cons hD) 0 (admits-step (den-cons hD) (admits-body n (empty {A = ⊤}) u D c a)))

    rh : Real h
    rh = real-snoc (c ⊕ [ ix 1 ]) plain-last (real-snoc c plain-ix (proj₁ (proj₁ a)))

    lt : r ≺ h
    lt = part-≺ c (ix 1 ∷ ix 0 ∷ ix 1 ∷ []) (last ∷ []) refl

    -- The trigger's end.
    row : hev hD 0 h end
    row = (at-end , (h ∷ []) , λ { at-end _ _ → here refl }) , λ { (at-end , _) → ≼-refl {h} }

    hh : HotsAll (den-cons hD) h
    hh = 0 , inj₁ (end , row)

-- An elaborated connect's hot ends no lane, wherever its scope's hots end none.
listHot-u : ∀ {Γ Δ X} n {ρι : Ren Γ Δ} (s : Obs Timeline Γ X) {ρ* : ℕ → All Tb.Listed Δ} (u : ∀ N → UncutEnv (ρ* N)) (D : DenOf ρ*) c a
          → (∀ N → EnvU ρι (den D N)) → ∀ N → AUndone (ES.hot (hev (listHot n (annotate (elab ρι s)) u D c a) N))
listHot-u n {ρι} s u D c a eu N p r with hot-out r
... | _ , (x , _) , _ = ann-u (3 + N) n (elab ρι s) (den D N) (elab-undone (3 + N) n ρι s (den D N) (eu N)) (c ⊕ [ ix 1 ]) x
