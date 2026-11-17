------------------------------------------------------------------------
-- A LISTED ROW LIES PAST ITS SUBSCRIPTION, in any environment: a leaf
-- lists at steps under it, a former places its rows at or under its
-- children's, a lane is read past its own start, and a reader keeps only
-- the hot's rows past it, under them, or ends one label past itself.
-- Likewise every listed pin names a connect past it: only a connect pins.
------------------------------------------------------------------------

module simultaneous.ListAfter where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁻; ∈-applyUpTo⁻)
open import Data.List.Relation.Unary.All using (All; lookup; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; _<ᵇ_; _≤ᵇ_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; inside; ix; sub; last; _⊕_; _<ᵖ_)
open import denotation.Events using (Timeline; timelineAt)
open import denotation.EmissionSet using (out; skip; end; pin; _≺_; _≼_)
open import denotation.Laws.Modulus using (≼-refl; ≼-trans; ≺→≼; ≺-≼-≺)
open import denotation.Laws.Worlds using (⊑-≼)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; Listed; _⊣_; rows; mapRow; scanRows; takeRows; mergeRows; switchRows; exhaustRows;
  connRows; rejoinRow; outerRow; afterL; lanes; values; concatMap; when; module ScanL; module TakeL;
  module MergeL; module SwitchL; module ExhaustL; module BoundedL; module ConnL)
open import quickcheck.Tabled.Exact.Base using (cm⁻; when⁻; if⁻; bind⁻; mapM⁻; pastRows⁻; ∧-true; values⁻)
open import simultaneous.Listing using (listC)
open import simultaneous.ColdOrder using (walk-past; walk-nopin)
open import simultaneous.ListPin using (no-endpin; queued-endpin; Keeps; rejoin-nopin; merge-keeps; exhaust-keeps)
open import simultaneous.TableOf using (after-W)

-- Every row of a table lies at or past `p`.
Past : ∀ {A} → Pos → List (Row A) → Set
Past p rs = ∀ {k e} → (k , e) ∈ rs → p ≼ k

private
  ≼-⊕ : ∀ q ys → q ≼ (q ⊕ ys)
  ≼-⊕ q ys = ⊑-≼ {q} {q ⊕ ys} (ys , refl)

  up : ∀ {p q} ys → p ≼ q → p ≼ (q ⊕ ys)
  up {p} {q} ys h = ≼-trans {p} {q} {q ⊕ ys} h (≼-⊕ q ys)

  down : ∀ {p q} ys → (p ⊕ ys) ≼ q → p ≼ q
  down {p} {q} ys h = ≼-trans {p} {p ⊕ ys} {q} (≼-⊕ p ys) h

  strict : ∀ {p q} ys → p ≺ q → p ≼ (q ⊕ ys)
  strict {p} {q} ys h = ≺→≼ {p} {q ⊕ ys} (≺-≼-≺ {p} {q} {q ⊕ ys} h (≼-⊕ q ys))

  past-≺ : ∀ {p s k} → p ≼ s → s ≺ k → p ≼ k
  past-≺ {p} {s} {k} h sk = ≼-trans {p} {s} {k} h (≺→≼ {s} {k} sk)

  -- A row a former passes on at its child row's position.
  Stays : ∀ {B : Set} → (Row B → Row B) → Set
  Stays lr = ∀ x → proj₁ (lr x) ≡ proj₁ x

  mapped-past : ∀ {B : Set} {p} (lr : Row B → Row B) → Stays lr → (rs : List (Row B)) → Past p rs → Past p (mapL lr rs)
  mapped-past {p = p} lr kp rs h m with ∈-map⁻ lr m
  ... | (x , xm , eq) = subst (p ≼_) (sym (trans (cong proj₁ eq) (kp x))) (h xm)

  values-past : ∀ {A : Set} {p} {rs : List (Row A)} → Past p rs → ∀ {q a} → (q , a) ∈ values rs → p ≼ q
  values-past h m = h (values⁻ m)

  -- A lane read past its start lies past it.
  afterL-past : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} {a s l} → afterL ln a s ≡ just l → ∀ {k e} → (k , e) ∈ rows l → s ≺ k
  afterL-past {ln = ln} {a} {s} e m with bind⁻ {m = ln a s} e
  ... | ((rs ⊣ b) , _ , refl) = proj₂ (pastRows⁻ rs m)

  -- Each value's lane lies past the value.
  LanesPast : ∀ {A B : Set} → Pos → List (Pos × A × Listed B) → Set
  LanesPast p ls = ∀ {q a l} → (q , a , l) ∈ ls → Past p (rows l)

  lanes-past : ∀ {A B : Set} {p} {ln : A → Pos → Maybe (Listed B)} {rs : List (Row A)} {ls}
             → Past p rs → lanes (afterL ln) (values rs) ≡ just ls → LanesPast p ls
  lanes-past {p = p} {ln = ln} {rs = rs} h e m {k} km with mapM⁻ {xs = values rs} e m
  ... | ((q′ , a′) , vm , fx) with bind⁻ {m = afterL ln a′ (q′ ⊕ [ ix 1 ])} fx
  ... | (_ , el , refl) = past-≺ {p} {q′ ⊕ [ ix 1 ]} {k} (up {p} {q′} [ ix 1 ] (values-past h vm)) (afterL-past {ln = ln} el km)

  outer-past : ∀ {A B : Set} {p} (d : Pos → Bool) (x : Row A) → p ≼ proj₁ x → ∀ {y} → y ∈ outerRow {A} {B} d x → p ≼ proj₁ y
  outer-past {p = p} d (q , out _) h (here refl) = up {p} {q} [ ix 0 ] h
  outer-past d (q , skip)  h (here refl) = h
  outer-past d (q , pin _) h (here refl) = h
  outer-past d (c , end)   h (here refl) = h
  outer-past d (q , out _) h (there ())
  outer-past d (q , skip)  h (there ())
  outer-past d (q , pin _) h (there ())
  outer-past d (c , end)   h (there ())

  outers-past : ∀ {A B : Set} {p} (d : Pos → Bool) {rs : List (Row A)} → Past p rs → Past p (concatMap (outerRow {A} {B} d) rs)
  outers-past d {rs} h m with cm⁻ {f = outerRow d} {xs = rs} m
  ... | (x , xm , h′) = outer-past d x (h xm) h′

  rejoin-past : ∀ {A : Set} p (rs : List (Row A)) → Past p (concatMap (rejoinRow p) rs)
  rejoin-past p rs m with cm⁻ {f = rejoinRow p} {xs = rs} m
  ... | ((q , out a) , _ , h) with when⁻ {b = p <ᵖ q} {x = (q ⊕ [ sub p ] , out a)} h
  ...   | (b , refl) = strict {p} {q} [ sub p ] (Equivalence.from T-≡ b)
  rejoin-past p rs m | ((q , skip) , _ , h) with when⁻ {b = p <ᵖ q} {x = (q ⊕ [ sub p ] , skip)} h
  ...   | (b , refl) = strict {p} {q} [ sub p ] (Equivalence.from T-≡ b)
  rejoin-past p rs m | ((q , pin _) , _ , h) with when⁻ {b = p <ᵖ q} {x = (q ⊕ [ sub p ] , skip)} h
  ...   | (b , refl) = strict {p} {q} [ sub p ] (Equivalence.from T-≡ b)
  rejoin-past p rs m | ((q , end) , _ , h) with if⁻ {b = p <ᵖ q} h
  ...   | inj₁ (b , here refl) = strict {p} {q} [ sub p ] (Equivalence.from T-≡ b)
  ...   | inj₁ (_ , there ())
  ...   | inj₂ (_ , here refl) = ≼-⊕ p [ last ]
  ...   | inj₂ (_ , there ())

  map-keeps : ∀ {A B : Set} (f : A → B) (x : Row A) → proj₁ (mapRow f x) ≡ proj₁ x
  map-keeps f (q , out _) = refl
  map-keeps f (q , skip)  = refl
  map-keeps f (q , pin _) = refl
  map-keeps f (q , end)   = refl

  map-past : ∀ {A B : Set} {p} (f : A → B) (rs : List (Row A)) → Past p rs → Past p (mapL (mapRow f) rs)
  map-past {p = p} f rs h m with ∈-map⁻ (mapRow f) m
  ... | (x , xm , eq) = subst (p ≼_) (sym (trans (cong proj₁ eq) (map-keeps f x))) (h xm)

  -- A scan's folds lie at its source's values.
  scan-past : ∀ {A B : Set} {p} (f : B → A → B) z (o : Listed A) → Past p (rows o) → Past p (rows (scanRows f z o))
  scan-past {A} {B} {p} f z o h m with ∈-++⁻ (concatMap (ScanL.folds f z o) (ScanL.table f z o)) m
  ... | inj₁ fm with cm⁻ {f = ScanL.folds f z o} {xs = ScanL.table f z o} fm
  ...   | ((q , a , bs) , tm , fm′) with ∈-map⁻ (λ b → q , out b) fm′
  ...     | (_ , _ , refl) = lv (length vals) (O.nths 0) (mapL (ScanL.opening f z o) (O.nths 0)) nth0 (λ c → open0 c) tm
    where
      vals = ScanL.vals f z o
      module O = Tb.Order vals
      inV : ∀ {q a} → (q , a) ∈ vals → p ≼ q
      inV = values-past h
      after-in : ∀ prev {q a} → (q , a) ∈ O.after prev → p ≼ q
      after-in prev am with cm⁻ {f = λ { (q′ , a′) → when (Tb.anyᵇ (λ { (q , _) → O.nextᵇ q q′ }) prev) (q′ , a′) }} {xs = vals} am
      ... | ((q′ , a′) , vm , w) with when⁻ {b = Tb.anyᵇ (λ { (q , _) → O.nextᵇ q q′ }) prev} {x = (q′ , a′)} w
      ...   | (_ , refl) = inV vm
      nth0 : ∀ {q a} → (q , a) ∈ O.nths 0 → p ≼ q
      nth0 am with cm⁻ {f = λ { (q , a) → when (O.minᵇ q) (q , a) }} {xs = vals} am
      ... | ((q′ , a′) , vm , w) with when⁻ {b = O.minᵇ q′} {x = (q′ , a′)} w
      ...   | (_ , refl) = inV vm
      open0 : ∀ {q a bs} → (q , a , bs) ∈ mapL (ScanL.opening f z o) (O.nths 0) → p ≼ q
      open0 om with ∈-map⁻ (ScanL.opening f z o) om
      ... | (_ , xm , refl) = nth0 xm
      lv : ∀ k vs cur → (∀ {q a} → (q , a) ∈ vs → p ≼ q) → (∀ {q a bs} → (q , a , bs) ∈ cur → p ≼ q)
         → ∀ {q a bs} → (q , a , bs) ∈ ScanL.levels f z o k vs cur → p ≼ q
      lv zero    vs cur hv hc ()
      lv (suc k) vs cur hv hc lm with ∈-++⁻ cur lm
      ... | inj₁ c = hc c
      ... | inj₂ r = lv k (O.after vs) (mapL (ScanL.step f z o cur) (O.after vs)) (after-in vs) stepped r
        where
          stepped : ∀ {q a bs} → (q , a , bs) ∈ mapL (ScanL.step f z o cur) (O.after vs) → p ≼ q
          stepped sm with ∈-map⁻ (ScanL.step f z o cur) sm
          ... | (_ , xm , refl) = after-in vs xm
  scan-past f z o h m | inj₂ om with cm⁻ {f = ScanL.others f z o} {xs = rows o} om
  ... | ((q , skip)  , rm , here refl) = h rm
  ... | ((q , pin _) , rm , here refl) = h rm
  ... | ((q , end)   , rm , here refl) = h rm
  ... | ((q , out _) , _ , ())
  ... | ((q , skip)  , _ , there ())
  ... | ((q , pin _) , _ , there ())
  ... | ((q , end)   , _ , there ())

  take-row : ∀ {A : Set} {p} i (keep : A → Bool) (o : Listed A) fs (x : Row A) → p ≼ proj₁ x
           → ∀ {y} → y ∈ TakeL.takeRow i keep o fs x → p ≼ proj₁ y
  take-row i keep o fs (q , pin r) h w with when⁻ {b = not (TakeL.failed i keep o fs r) ∧ inside r q} {x = (q , pin r)} w
  ... | (_ , refl) = h
  take-row {p = p} i keep o fs (q , out a) h w with if⁻ {b = TakeL.failed i keep o fs q} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , w′) with if⁻ {b = keep a} w′
  ...   | inj₁ (_ , here refl) = h
  ...   | inj₁ (_ , there ())
  ...   | inj₂ (_ , w″) with ∈-++⁻ (when i (q ⊕ [ ix 0 ] , out a)) w″
  ...     | inj₁ v with when⁻ {b = i} {x = (q ⊕ [ ix 0 ] , out a)} v
  ...       | (_ , refl) = up {p} {q} [ ix 0 ] h
  take-row {p = p} i keep o fs (q , out a) h w | inj₂ (_ , w′) | inj₂ (_ , w″) | inj₂ (here refl) = up {p} {q} [ last ] h
  take-row {p = p} i keep o fs (q , out a) h w | inj₂ (_ , w′) | inj₂ (_ , w″) | inj₂ (there ())
  take-row i keep o fs (q , skip) h w with if⁻ {b = TakeL.failed i keep o fs q} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here refl) = h
  ... | inj₂ (_ , there ())
  take-row i keep o fs (q , end) h w with if⁻ {b = TakeL.failed i keep o fs q} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here refl) = h
  ... | inj₂ (_ , there ())

  take-past : ∀ {A : Set} {p} i (keep : A → Bool) (o : Listed A) → Past p (rows o) → Past p (rows (takeRows i keep o))
  take-past i keep o h m with cm⁻ {f = TakeL.takeRow i keep o (TakeL.failures i keep o)} {xs = rows o} m
  ... | (x , xm , w) = take-row i keep o (TakeL.failures i keep o) x (h xm) w

  merge-stays : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) es → Stays (MergeL.Ended.laneRow o ls es)
  merge-stays o ls es (c , end)   = refl
  merge-stays o ls es (k , out _) = refl
  merge-stays o ls es (k , skip)  = refl
  merge-stays o ls es (k , pin _) = refl

  merge-past : ∀ {A B : Set} {p} (o : Listed A) (ls : List (Pos × A × Listed B)) → Past p (rows o) → LanesPast p ls
             → Past p (rows (mergeRows o ls))
  merge-past o ls ho hl m with ∈-++⁻ (concatMap (outerRow (MergeL.Ended.done o ls (Tb.ends (rows o)))) (rows o)) m
  ... | inj₁ h = outers-past (MergeL.Ended.done o ls (Tb.ends (rows o))) ho h
  ... | inj₂ h with cm⁻ {f = λ { (_ , _ , l) → mapL (MergeL.Ended.laneRow o ls (Tb.ends (rows o))) (rows l) }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) = mapped-past _ (merge-stays o ls (Tb.ends (rows o))) (rows l) (hl lm) h′

  exhaust-stays : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) rs → Stays (ExhaustL.Ran.laneRow o ls rs)
  exhaust-stays o ls rs (c , end)   = refl
  exhaust-stays o ls rs (k , out _) = refl
  exhaust-stays o ls rs (k , skip)  = refl
  exhaust-stays o ls rs (k , pin _) = refl

  exhaust-past : ∀ {A B : Set} {p} (o : Listed A) (ls : List (Pos × A × Listed B)) → Past p (rows o) → LanesPast p ls
               → Past p (rows (exhaustRows o ls))
  exhaust-past o ls ho hl m with ∈-++⁻ (concatMap (outerRow (ExhaustL.Ran.done o ls (ExhaustL.runs o ls))) (rows o)) m
  ... | inj₁ h = outers-past (ExhaustL.Ran.done o ls (ExhaustL.runs o ls)) ho h
  ... | inj₂ h with cm⁻ {f = λ { (q , _ , l) → if ExhaustL.Ran.ranᵇ o ls (ExhaustL.runs o ls) q then mapL (ExhaustL.Ran.laneRow o ls (ExhaustL.runs o ls)) (rows l) else [] }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) with if⁻ {b = ExhaustL.Ran.ranᵇ o ls (ExhaustL.runs o ls) q} h′
  ...     | inj₂ (_ , ())
  ...     | inj₁ (_ , h″) = mapped-past _ (exhaust-stays o ls (ExhaustL.runs o ls)) (rows l) (hl lm) h″

  switch-row : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) q (x : Row B) → ∀ {y} → y ∈ SwitchL.laneRow o ls q x → proj₁ y ≡ proj₁ x
  switch-row o ls q (k , pin r) w with if⁻ {b = SwitchL.cutᵇ o ls q k} w
  ... | inj₁ (_ , w′) with when⁻ {b = not (SwitchL.cutᵇ o ls q r) ∧ inside r k} {x = (k , pin r)} w′
  ...   | (_ , refl) = refl
  switch-row o ls q (k , pin r) w | inj₂ (_ , here refl) = refl
  switch-row o ls q (k , pin r) w | inj₂ (_ , there ())
  switch-row o ls q (k , out _) w with if⁻ {b = SwitchL.cutᵇ o ls q k} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here refl) = refl
  ... | inj₂ (_ , there ())
  switch-row o ls q (k , skip) w with if⁻ {b = SwitchL.cutᵇ o ls q k} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here refl) = refl
  ... | inj₂ (_ , there ())
  switch-row o ls q (c , end) w with if⁻ {b = SwitchL.cutᵇ o ls q c} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here refl) = refl
  ... | inj₂ (_ , there ())

  switch-past : ∀ {A B : Set} {p} (o : Listed A) (ls : List (Pos × A × Listed B)) → Past p (rows o) → LanesPast p ls
              → Past p (rows (switchRows o ls))
  switch-past {p = p} o ls ho hl m with ∈-++⁻ (concatMap (outerRow (SwitchL.done o ls)) (rows o)) m
  ... | inj₁ h = outers-past (SwitchL.done o ls) ho h
  ... | inj₂ h with cm⁻ {f = λ { (q , _ , l) → concatMap (SwitchL.laneRow o ls q) (rows l) }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) with cm⁻ {f = SwitchL.laneRow o ls q} {xs = rows l} h′
  ...     | (x , xm , h″) = subst (p ≼_) (sym (switch-row o ls q x h″)) (hl lm xm)

  -- A bounded merge's starts lie past their values.
  starts-past : ∀ {A B : Set} k (ln : A → Pos → Maybe (Listed B)) (o : Listed A) i q ess {s}
              → s ∈ BoundedL.starts k ln o i q ess → q ≼ s
  starts-past k ln o i q ess w with if⁻ {b = i <ᵇ k} w
  ... | inj₁ (_ , here refl) = ≼-⊕ q [ ix 1 ]
  ... | inj₁ (_ , there ())
  ... | inj₂ (_ , w′) with if⁻ {b = suc (i ∸ k) ≤ᵇ Tb.count (λ c → c <ᵖ q) ess} w′
  ...   | inj₁ (_ , here refl) = ≼-⊕ q [ ix 1 ]
  ...   | inj₁ (_ , there ())
  ...   | inj₂ (_ , w″) with cm⁻ {f = concatMap (BoundedL.queuedAt k ln o i q ess)} {xs = ess} w″
  ...     | (es , _ , w‴) with cm⁻ {f = BoundedL.queuedAt k ln o i q ess} {xs = es} w‴
  ...       | (c , _ , v) with when⁻ {b = (q <ᵖ c) ∧ ((suc (i ∸ k) ≤ᵇ Tb.count (λ c′ → c′ Tb.≼ᵇ c) ess)
                                       ∧ not (suc (i ∸ k) ≤ᵇ Tb.count (λ c′ → c′ <ᵖ c) ess))} {x = c ⊕ [ ix 1 ]} v
  ...         | (b , refl) = strict {q} {c} [ ix 1 ] (Equivalence.from T-≡ (proj₁ (∧-true b)))

  -- Each level's lanes lie at starts past their values.
  levels-past : ∀ {A B : Set} k (ln : A → Pos → Maybe (Listed B)) (o : Listed A)
              → ∀ c i ess vs {G} → BoundedL.levels k ln o c i ess vs ≡ just G
              → (∀ {q a} → (q , a) ∈ vs → (q , a) ∈ BoundedL.vals k ln o)
              → ∀ {j q a ss s l} → (j , q , a , ss) ∈ G → (s , l) ∈ ss
              → (q , a) ∈ BoundedL.vals k ln o × q ≼ s × ln a s ≡ just l
  levels-past k ln o zero    i ess vs refl hv ()
  levels-past k ln o (suc c) i ess vs e hv gm sm with bind⁻ {m = mapM′} e
    where mapM′ = Tb.mapM (BoundedL.entry k ln o i ess) vs
  ... | (gs , egs , e′) with bind⁻ {m = BoundedL.levels k ln o c (suc i) (BoundedL.endsOf k ln o gs ∷ ess) (Tb.Order.after (BoundedL.vals k ln o) vs)} e′
  ... | (rest , erest , refl) with ∈-++⁻ (mapL (i ,_) gs) gm
  ... | inj₂ rm = levels-past k ln o c (suc i) (BoundedL.endsOf k ln o gs ∷ ess) (Tb.Order.after (BoundedL.vals k ln o) vs) erest after-in rm sm
    where
      after-in : ∀ {q a} → (q , a) ∈ Tb.Order.after (BoundedL.vals k ln o) vs → (q , a) ∈ BoundedL.vals k ln o
      after-in am with cm⁻ {f = λ { (q′ , a′) → when (Tb.anyᵇ (λ { (q , _) → Tb.Order.nextᵇ (BoundedL.vals k ln o) q q′ }) vs) (q′ , a′) }} {xs = BoundedL.vals k ln o} am
      ... | ((q′ , a′) , vm , w) with when⁻ {b = Tb.anyᵇ (λ { (q , _) → Tb.Order.nextᵇ (BoundedL.vals k ln o) q q′ }) vs} {x = (q′ , a′)} w
      ...   | (_ , refl) = vm
  ... | inj₁ im with ∈-map⁻ (i ,_) im
  ...   | (_ , xm , refl) with mapM⁻ {f = BoundedL.entry k ln o i ess} {xs = vs} egs xm
  ...       | ((q′ , a′) , vm , fx) with bind⁻ {m = Tb.mapM (BoundedL.laneAt k ln o a′) (BoundedL.starts k ln o i q′ ess)} fx
  ...         | (ss′ , ess′ , refl) with mapM⁻ {xs = BoundedL.starts k ln o i q′ ess} ess′ sm
  ...           | (s′ , stm , fy) with bind⁻ {m = ln a′ s′} fy
  ...             | (_ , el , refl) = hv vm , starts-past k ln o i q′ ess stm , el

  bounded-keeps : ∀ {A B : Set} k (ln : A → Pos → Maybe (Listed B)) (o : Listed A) G {p} (x : Row B)
                → p ≼ proj₁ x → p ≼ proj₁ (BoundedL.laneRow k ln o G x)
  bounded-keeps k ln o G {p} (c , end) h with BoundedL.queued k ln o G c
  ... | true  = up {p} {c} [ ix 0 ] h
  ... | false = h
  bounded-keeps k ln o G (q , out _) h = h
  bounded-keeps k ln o G (q , skip)  h = h
  bounded-keeps k ln o G (q , pin _) h = h

  bounded-past : ∀ {A B C : Set} {p} k (lr : A → Pos → Maybe (Listed B)) (o : Listed A) → Past p (rows o)
               → ∀ {l} → BoundedL.listB k (afterL lr) o ≡ just l → Past p (rows l)
  bounded-past {A} {B} {C} {p} k lr o ho e with bind⁻ {m = BoundedL.levels k ln o (length (BoundedL.vals k ln o)) 0 [] (Tb.Order.nths (BoundedL.vals k ln o) 0)} e
    where ln = afterL lr
  ... | (G , eG , refl) = go
    where
      ln = afterL lr
      vals = BoundedL.vals k ln o
      nth0 : ∀ {q a} → (q , a) ∈ Tb.Order.nths vals 0 → (q , a) ∈ vals
      nth0 am with cm⁻ {f = λ { (q , a) → when (Tb.Order.minᵇ vals q) (q , a) }} {xs = vals} am
      ... | ((q′ , a′) , vm , w) with when⁻ {b = Tb.Order.minᵇ vals q′} {x = (q′ , a′)} w
      ...   | (_ , refl) = vm
      go : Past p (rows (BoundedL.boundedRows k ln o G))
      go m with ∈-++⁻ (concatMap (outerRow (BoundedL.done k ln o G)) (rows o)) m
      ... | inj₁ h = outers-past (BoundedL.done k ln o G) ho h
      ... | inj₂ h with cm⁻ {f = λ { (_ , _ , _ , ss) → concatMap (λ { (_ , l) → mapL (BoundedL.laneRow k ln o G) (rows l) }) ss }} {xs = G} h
      ...   | ((j , q , a , ss) , gm , h′) with cm⁻ {f = λ { (_ , l) → mapL (BoundedL.laneRow k ln o G) (rows l) }} {xs = ss} h′
      ...     | ((s , l) , sm , h″) with ∈-map⁻ (BoundedL.laneRow k ln o G) h″
      ...       | (x , xm , eq) with levels-past k ln o (length vals) 0 [] (Tb.Order.nths vals 0) eG nth0 gm sm
      ...         | (vm , qs , el) = subst (p ≼_) (sym (cong proj₁ eq))
                      (bounded-keeps k ln o G x (past-≺ {p} {s} {proj₁ x} (≼-trans {p} {q} {s} (values-past ho vm) qs) (afterL-past {ln = lr} el xm)))

  -- A connect's rows: its body's, and its source's one label down.
  shown-at : ∀ {A B : Set} p (σ : Listed A) (β : Listed B) es (x : Row A) {y} → y ∈ ConnL.shown p σ β es x → proj₁ y ≡ proj₁ x ⊕ [ ix 0 ]
  shown-at p σ β es (k , e) w with if⁻ {b = inside (p ⊕ [ ix 1 ]) k} w
  ... | inj₁ (_ , here refl) = refl
  ... | inj₁ (_ , there ())
  shown-at p σ β es (k , pin r) w | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β es r ∧ inside r k} {x = (k ⊕ [ ix 0 ] , pin r)} u
  ... | (_ , refl) = refl
  shown-at p σ β es (k , out a) w | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β es k} {x = (k ⊕ [ ix 0 ] , skip)} u
  ... | (_ , refl) = refl
  shown-at p σ β es (k , skip) w | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β es k} {x = (k ⊕ [ ix 0 ] , skip)} u
  ... | (_ , refl) = refl
  shown-at p σ β es (k , end) w | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β es k} {x = (k ⊕ [ ix 0 ] , skip)} u
  ... | (_ , refl) = refl

  conn-past : ∀ {A B : Set} p (σ : Listed A) (β : Listed B) → Past (p ⊕ [ ix 1 ]) (rows σ) → Past (p ⊕ [ ix 0 ]) (rows β)
            → Past p (rows (connRows p σ β))
  conn-past p σ β hσ hβ {k} m with ∈-++⁻ (rows β) m
  ... | inj₁ bm = down {p} {k} [ ix 0 ] (hβ bm)
  ... | inj₂ h with cm⁻ {f = ConnL.shown p σ β (Tb.ends (rows β))} {xs = rows σ} h
  ...   | (x , xm , w) = subst (p ≼_) (sym (shown-at p σ β (Tb.ends (rows β)) x w)) (up {p} {proj₁ x} [ ix 0 ] (down {p} {proj₁ x} [ ix 1 ] (hσ xm)))

-- A LISTED ROW LIES PAST ITS SUBSCRIPTION.
listC-past : ∀ {Γ A} N n (o : Obs Timeline Γ A) {ρL : All Listed Γ} p {l} → listC N n o ρL p ≡ just l → Past p (rows l)
listC-past N n       (cold c)          p refl m = ≺→≼ {p} (walk-past N p (timelineAt c p) m)
listC-past N n       empty             p refl (here refl) = ≼-⊕ p [ last ]
listC-past N n       empty             p refl (there ())
listC-past N n       (of xs)           p refl m = after-W p 0 xs m
listC-past N n       (map f s) {ρL}    p e with bind⁻ {m = listC N n s ρL p} e
... | ((rs ⊣ b) , e₀ , refl) = map-past f rs (listC-past N n s p e₀)
listC-past N n       (scan f z s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , refl) = scan-past f z o (listC-past N n s p e₀)
listC-past N n       (takeWhile i q s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , refl) = take-past i q o (listC-past N n s p e₀)
listC-past N n       (flatMap (mergeᶠ nothing) f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = merge-past o ls h (lanes-past {ln = λ a → listC N n (f a) ρL} {rs = rows o} h els)
  where h = listC-past N n s p e₀
listC-past N n       (flatMap (mergeᶠ (just k)) f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) = bounded-past {C = ⊤′} k (λ a → listC N n (f a) ρL) o (listC-past N n s p e₀) e₁
  where open import Data.Unit using () renaming (⊤ to ⊤′)
listC-past N n       (flatMap switchᶠ f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = switch-past o ls h (lanes-past {ln = λ a → listC N n (f a) ρL} {rs = rows o} h els)
  where h = listC-past N n s p e₀
listC-past N n       (flatMap exhaustᶠ f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = exhaust-past o ls h (lanes-past {ln = λ a → listC N n (f a) ρL} {rs = rows o} h els)
  where h = listC-past N n s p e₀
listC-past N n       (connect s b) {ρL} p e with bind⁻ {m = listC N n s ρL (p ⊕ [ ix 1 ])} e
... | (σ , eσ , e₁) with bind⁻ {m = listC N n b (Tb.hotOf σ ∷ ρL) (p ⊕ [ ix 0 ])} e₁
... | (β , eβ , refl) = conn-past p σ β (listC-past N n s (p ⊕ [ ix 1 ]) eσ) (listC-past N n b (p ⊕ [ ix 0 ]) eβ)
listC-past N n       (connected i) {ρL} p refl with lookup ρL i
... | rs ⊣ b = rejoin-past p rs
listC-past N zero    (defer l)         p refl m with ∈-applyUpTo⁻ _ m
... | (i , _ , refl) = ≼-⊕ p [ ix i ]
listC-past N (suc n) (defer l) {ρL}    p e {k} m with bind⁻ {m = listC N n (Later.force l) ρL (p ⊕ [ ix 1 ])} e
... | (b , eb , refl) with m
...   | here refl = ≼-⊕ p [ ix 0 ]
...   | there m′  = down {p} {k} [ ix 1 ] (listC-past N n (Later.force l) (p ⊕ [ ix 1 ]) eb m′)

-- Every pin of a table names a connect at or past `p`.
PinsPast : ∀ {A} → Pos → List (Row A) → Set
PinsPast p rs = ∀ {k r} → (k , pin r) ∈ rs → p ≼ r

private
  outer-pp : ∀ {A B : Set} {p} (d : Pos → Bool) {rs : List (Row A)} → PinsPast p rs → ∀ {x} → x ∈ rs
           → ∀ {y r} → (y , pin r) ∈ outerRow {A} {B} d x → p ≼ r
  outer-pp d h {q , out _} xm (here ())
  outer-pp d h {q , out _} xm (there ())
  outer-pp d h {q , skip}  xm (here ())
  outer-pp d h {q , skip}  xm (there ())
  outer-pp d h {q , pin _} xm (here refl) = h xm
  outer-pp d h {q , pin _} xm (there ())
  outer-pp d h {c , end}   xm (here eq) = ⊥-elim (no-endpin (d c) (cong proj₂ eq))
  outer-pp d h {c , end}   xm (there ())

  outers-pp : ∀ {A B : Set} {p} (d : Pos → Bool) {rs : List (Row A)} → PinsPast p rs → PinsPast p (concatMap (outerRow {A} {B} d) rs)
  outers-pp d {rs} h m with cm⁻ {f = outerRow d} {xs = rs} m
  ... | (x , xm , h′) = outer-pp d h xm h′

  mapped-pp : ∀ {B : Set} {p} (lr : Row B → Row B) → Keeps lr → (rs : List (Row B)) → PinsPast p rs → PinsPast p (mapL lr rs)
  mapped-pp lr kp rs h m with ∈-map⁻ lr m
  ... | (x , xm , eq) with kp x eq
  ...   | refl = h xm

  -- A lane read past its start keeps its pins, which name connects past it.
  afterL-pp : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} → (∀ {a s l} → ln a s ≡ just l → PinsPast s (rows l))
            → ∀ {a s l} → afterL ln a s ≡ just l → PinsPast s (rows l)
  afterL-pp {ln = ln} ih {a} {s} e with bind⁻ {m = ln a s} e
  ... | ((rs ⊣ b) , e₀ , refl) = λ m → ih e₀ (proj₁ (pastRows⁻ rs m))

  LanesPP : ∀ {A B : Set} → Pos → List (Pos × A × Listed B) → Set
  LanesPP p ls = ∀ {q a l} → (q , a , l) ∈ ls → PinsPast p (rows l)

  lanes-pp : ∀ {A B : Set} {p} {ln : A → Pos → Maybe (Listed B)} {rs : List (Row A)} {ls}
           → Past p rs → (∀ {a s l} → ln a s ≡ just l → PinsPast s (rows l)) → lanes (afterL ln) (values rs) ≡ just ls → LanesPP p ls
  lanes-pp {p = p} {ln = ln} {rs = rs} h ih e m {k} {r} km with mapM⁻ {xs = values rs} e m
  ... | ((q′ , a′) , vm , fx) with bind⁻ {m = afterL ln a′ (q′ ⊕ [ ix 1 ])} fx
  ... | (_ , el , refl) = ≼-trans {p} {q′ ⊕ [ ix 1 ]} {r} (up {p} {q′} [ ix 1 ] (values-past h vm)) (afterL-pp {ln = ln} ih el km)

  map-pp : ∀ {A B : Set} {p} (f : A → B) (rs : List (Row A)) → PinsPast p rs → PinsPast p (mapL (mapRow f) rs)
  map-pp f rs h m with ∈-map⁻ (mapRow f) m
  ... | ((q , pin _) , rm , refl) = h rm
  ... | ((q , out _) , _ , ())
  ... | ((q , skip) , _ , ())
  ... | ((q , end) , _ , ())

  scan-pp : ∀ {A B : Set} {p} (f : B → A → B) z (o : Listed A) → PinsPast p (rows o) → PinsPast p (rows (scanRows f z o))
  scan-pp f z o h m with ∈-++⁻ (concatMap (ScanL.folds f z o) (ScanL.table f z o)) m
  ... | inj₁ fm with cm⁻ {xs = ScanL.table f z o} fm
  ...   | (_ , _ , fm′) with ∈-map⁻ _ fm′
  ...     | (_ , _ , ())
  scan-pp f z o h m | inj₂ om with cm⁻ {xs = rows o} om
  ... | ((q , pin _) , rm , here refl) = h rm
  ... | ((q , pin _) , rm , there ())
  ... | ((q , out _) , _ , ())
  ... | ((q , skip) , _ , here ())
  ... | ((q , skip) , _ , there ())
  ... | ((q , end) , _ , here ())
  ... | ((q , end) , _ , there ())

  take-pp : ∀ {A : Set} {p} i (keep : A → Bool) (o : Listed A) → PinsPast p (rows o) → PinsPast p (rows (takeRows i keep o))
  take-pp {A} i keep o h m with cm⁻ {f = TakeL.takeRow i keep o fs} {xs = rows o} m
    where fs = TakeL.failures i keep o
  ... | ((q , pin _) , xm , w) with when⁻ w
  ...   | (_ , refl) = h xm
  take-pp i keep o h m | ((q , out a) , _ , w) with if⁻ {b = TakeL.failed i keep o (TakeL.failures i keep o) q} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , w′) with if⁻ {b = keep a} w′
  ...   | inj₁ (_ , here ())
  ...   | inj₁ (_ , there ())
  ...   | inj₂ (_ , w″) with ∈-++⁻ (when i (q ⊕ [ ix 0 ] , out a)) w″
  ...     | inj₁ v with when⁻ v
  ...       | (_ , ())
  take-pp i keep o h m | ((q , out a) , _ , w) | inj₂ (_ , w′) | inj₂ (_ , w″) | inj₂ (here ())
  take-pp i keep o h m | ((q , out a) , _ , w) | inj₂ (_ , w′) | inj₂ (_ , w″) | inj₂ (there ())
  take-pp i keep o h m | ((q , skip) , _ , w) with if⁻ {b = TakeL.failed i keep o (TakeL.failures i keep o) q} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())
  take-pp i keep o h m | ((q , end) , _ , w) with if⁻ {b = TakeL.failed i keep o (TakeL.failures i keep o) q} w
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())

  merge-pp : ∀ {A B : Set} {p} (o : Listed A) (ls : List (Pos × A × Listed B)) → PinsPast p (rows o) → LanesPP p ls
           → PinsPast p (rows (mergeRows o ls))
  merge-pp o ls ho hl m with ∈-++⁻ (concatMap (outerRow (MergeL.Ended.done o ls (Tb.ends (rows o)))) (rows o)) m
  ... | inj₁ h = outers-pp (MergeL.Ended.done o ls (Tb.ends (rows o))) ho h
  ... | inj₂ h with cm⁻ {f = λ { (_ , _ , l) → mapL (MergeL.Ended.laneRow o ls (Tb.ends (rows o))) (rows l) }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) = mapped-pp _ (merge-keeps o ls (Tb.ends (rows o))) (rows l) (hl lm) h′

  exhaust-pp : ∀ {A B : Set} {p} (o : Listed A) (ls : List (Pos × A × Listed B)) → PinsPast p (rows o) → LanesPP p ls
             → PinsPast p (rows (exhaustRows o ls))
  exhaust-pp o ls ho hl m with ∈-++⁻ (concatMap (outerRow (ExhaustL.Ran.done o ls (ExhaustL.runs o ls))) (rows o)) m
  ... | inj₁ h = outers-pp (ExhaustL.Ran.done o ls (ExhaustL.runs o ls)) ho h
  ... | inj₂ h with cm⁻ {f = λ { (q , _ , l) → if ExhaustL.Ran.ranᵇ o ls (ExhaustL.runs o ls) q then mapL (ExhaustL.Ran.laneRow o ls (ExhaustL.runs o ls)) (rows l) else [] }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) with if⁻ {b = ExhaustL.Ran.ranᵇ o ls (ExhaustL.runs o ls) q} h′
  ...     | inj₂ (_ , ())
  ...     | inj₁ (_ , h″) = mapped-pp _ (exhaust-keeps o ls (ExhaustL.runs o ls)) (rows l) (hl lm) h″

  switch-pp : ∀ {A B : Set} {p} (o : Listed A) (ls : List (Pos × A × Listed B)) → PinsPast p (rows o) → LanesPP p ls
            → PinsPast p (rows (switchRows o ls))
  switch-pp o ls ho hl m with ∈-++⁻ (concatMap (outerRow (SwitchL.done o ls)) (rows o)) m
  ... | inj₁ h = outers-pp (SwitchL.done o ls) ho h
  ... | inj₂ h with cm⁻ {f = λ { (q , _ , l) → concatMap (SwitchL.laneRow o ls q) (rows l) }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) with cm⁻ {f = SwitchL.laneRow o ls q} {xs = rows l} h′
  ...     | ((k , pin r) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q k} h″
  ...       | inj₁ (_ , w) with when⁻ {b = not (SwitchL.cutᵇ o ls q r) ∧ inside r k} {x = (k , pin r)} w
  ...         | (_ , refl) = hl lm xm
  switch-pp o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , pin r) , xm , h″) | inj₂ (_ , here refl) = hl lm xm
  switch-pp o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , pin r) , xm , h″) | inj₂ (_ , there ())
  switch-pp o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , out _) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q k} h″
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())
  switch-pp o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , skip) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q k} h″
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())
  switch-pp o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((c , end) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q c} h″
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here eq) = ⊥-elim (no-endpin (SwitchL.done o ls c) (cong proj₂ eq))
  ... | inj₂ (_ , there ())

  bounded-pp : ∀ {A B : Set} {p} k (lr : A → Pos → Maybe (Listed B)) (o : Listed A) → Past p (rows o) → PinsPast p (rows o)
             → (∀ {a s l} → lr a s ≡ just l → PinsPast s (rows l))
             → ∀ {l} → BoundedL.listB k (afterL lr) o ≡ just l → PinsPast p (rows l)
  bounded-pp {A} {B} {p} k lr o hp ho ih e with bind⁻ {m = BoundedL.levels k (afterL lr) o (length (BoundedL.vals k (afterL lr) o)) 0 [] (Tb.Order.nths (BoundedL.vals k (afterL lr) o) 0)} e
  ... | (G , eG , refl) = go
    where
      ln = afterL lr
      vals = BoundedL.vals k ln o
      nth0 : ∀ {q a} → (q , a) ∈ Tb.Order.nths vals 0 → (q , a) ∈ vals
      nth0 am with cm⁻ {f = λ { (q , a) → when (Tb.Order.minᵇ vals q) (q , a) }} {xs = vals} am
      ... | ((q′ , a′) , vm , w) with when⁻ {b = Tb.Order.minᵇ vals q′} {x = (q′ , a′)} w
      ...   | (_ , refl) = vm
      go : PinsPast p (rows (BoundedL.boundedRows k ln o G))
      go m with ∈-++⁻ (concatMap (outerRow (BoundedL.done k ln o G)) (rows o)) m
      ... | inj₁ h = outers-pp (BoundedL.done k ln o G) ho h
      ... | inj₂ h with cm⁻ {f = λ { (_ , _ , _ , ss) → concatMap (λ { (_ , l) → mapL (BoundedL.laneRow k ln o G) (rows l) }) ss }} {xs = G} h
      ...   | ((j , q , a , ss) , gm , h′) with cm⁻ {f = λ { (_ , l) → mapL (BoundedL.laneRow k ln o G) (rows l) }} {xs = ss} h′
      ...     | ((s , l) , sm , h″) with ∈-map⁻ (BoundedL.laneRow k ln o G) h″
      ...       | ((y , out _) , _ , ())
      ...       | ((y , skip) , _ , ())
      ...       | ((c , end) , _ , eq) = ⊥-elim (queued-endpin (BoundedL.queued k ln o G c) (BoundedL.done k ln o G c) c eq)
      ...       | ((y , pin r) , xm , refl) with levels-past k ln o (length vals) 0 [] (Tb.Order.nths vals 0) eG nth0 gm sm
      ...         | (vm , qs , el) = ≼-trans {p} {s} {r} (≼-trans {p} {q} {s} (values-past hp vm) qs) (afterL-pp {ln = lr} ih el xm)

  conn-pp : ∀ {A B : Set} p (σ : Listed A) (β : Listed B) → PinsPast (p ⊕ [ ix 1 ]) (rows σ) → PinsPast (p ⊕ [ ix 0 ]) (rows β)
          → PinsPast p (rows (connRows p σ β))
  conn-pp p σ β hσ hβ {y} {r} m with ∈-++⁻ (rows β) m
  ... | inj₁ bm = down {p} {r} [ ix 0 ] (hβ bm)
  ... | inj₂ h with cm⁻ {f = ConnL.shown p σ β (Tb.ends (rows β))} {xs = rows σ} h
  ...   | ((k , e) , km , w) with if⁻ {b = inside (p ⊕ [ ix 1 ]) k} w
  ...     | inj₁ (_ , here refl) = ≼-refl {p}
  ...     | inj₁ (_ , there ())
  conn-pp p σ β hσ hβ {y} {r} m | inj₂ h | ((k , pin r′) , km , w) | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β (Tb.ends (rows β)) r′ ∧ inside r′ k} {x = (k ⊕ [ ix 0 ] , pin r′)} u
  ... | (_ , refl) = down {p} {r} [ ix 1 ] (hσ km)
  conn-pp p σ β hσ hβ m | inj₂ h | ((k , out _) , km , w) | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β (Tb.ends (rows β)) k} {x = (k ⊕ [ ix 0 ] , skip)} u
  ... | (_ , ())
  conn-pp p σ β hσ hβ m | inj₂ h | ((k , skip) , km , w) | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β (Tb.ends (rows β)) k} {x = (k ⊕ [ ix 0 ] , skip)} u
  ... | (_ , ())
  conn-pp p σ β hσ hβ m | inj₂ h | ((k , end) , km , w) | inj₂ (_ , u) with when⁻ {b = ConnL.alive p σ β (Tb.ends (rows β)) k} {x = (k ⊕ [ ix 0 ] , skip)} u
  ... | (_ , ())

-- A LISTED PIN NAMES A CONNECT PAST ITS SUBSCRIPTION: a connect pins its
-- source's rows with its own subscription, a reader turns a hot's pins to
-- skips, and every other former passes a child's pin on.
listC-pinpast : ∀ {Γ A} N n (o : Obs Timeline Γ A) {ρL : All Listed Γ} p {l} → listC N n o ρL p ≡ just l → PinsPast p (rows l)
listC-pinpast N n       (cold c)          p refl m = ⊥-elim (walk-nopin N _ m)
listC-pinpast N n       empty             p refl (here ())
listC-pinpast N n       empty             p refl (there ())
listC-pinpast N n       (of xs)           p refl m = ⊥-elim (walk-nopin (suc (length xs)) _ m)
listC-pinpast N n       (map f s) {ρL}    p e with bind⁻ {m = listC N n s ρL p} e
... | ((rs ⊣ b) , e₀ , refl) = map-pp f rs (listC-pinpast N n s p e₀)
listC-pinpast N n       (scan f z s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , refl) = scan-pp f z o (listC-pinpast N n s p e₀)
listC-pinpast N n       (takeWhile i q s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , refl) = take-pp i q o (listC-pinpast N n s p e₀)
listC-pinpast N n       (flatMap (mergeᶠ nothing) f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = merge-pp o ls (listC-pinpast N n s p e₀)
        (lanes-pp {ln = λ a → listC N n (f a) ρL} {rs = rows o} (listC-past N n s p e₀) (λ {a} {s′} → listC-pinpast N n (f a) s′) els)
listC-pinpast N n       (flatMap (mergeᶠ (just k)) f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) = bounded-pp k (λ a → listC N n (f a) ρL) o (listC-past N n s p e₀) (listC-pinpast N n s p e₀)
                        (λ {a} {s′} → listC-pinpast N n (f a) s′) e₁
listC-pinpast N n       (flatMap switchᶠ f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = switch-pp o ls (listC-pinpast N n s p e₀)
        (lanes-pp {ln = λ a → listC N n (f a) ρL} {rs = rows o} (listC-past N n s p e₀) (λ {a} {s′} → listC-pinpast N n (f a) s′) els)
listC-pinpast N n       (flatMap exhaustᶠ f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = exhaust-pp o ls (listC-pinpast N n s p e₀)
        (lanes-pp {ln = λ a → listC N n (f a) ρL} {rs = rows o} (listC-past N n s p e₀) (λ {a} {s′} → listC-pinpast N n (f a) s′) els)
listC-pinpast N n       (connect s b) {ρL} p e with bind⁻ {m = listC N n s ρL (p ⊕ [ ix 1 ])} e
... | (σ , eσ , e₁) with bind⁻ {m = listC N n b (Tb.hotOf σ ∷ ρL) (p ⊕ [ ix 0 ])} e₁
... | (β , eβ , refl) = conn-pp p σ β (listC-pinpast N n s (p ⊕ [ ix 1 ]) eσ) (listC-pinpast N n b (p ⊕ [ ix 0 ]) eβ)
listC-pinpast N n       (connected i) {ρL} p refl with lookup ρL i
... | rs ⊣ b = λ m → ⊥-elim (rejoin-nopin p rs m)
listC-pinpast N zero    (defer l)         p refl m with ∈-applyUpTo⁻ _ m
... | (_ , _ , ())
listC-pinpast N (suc n) (defer l) {ρL}    p e {k} {r} m with bind⁻ {m = listC N n (Later.force l) ρL (p ⊕ [ ix 1 ])} e
... | (b , eb , refl) with m
...   | here ()
...   | there m′ = down {p} {r} [ ix 1 ] (listC-pinpast N n (Later.force l) (p ⊕ [ ix 1 ]) eb m′)
