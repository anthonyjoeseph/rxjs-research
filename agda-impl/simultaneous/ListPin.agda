------------------------------------------------------------------------
-- A LISTED PIN LIES INSIDE ITS CONNECT, in any environment: a connect
-- pins only rows under its own subscription, one label down; every other
-- former passes a child's pin on unmoved or drops it, a takeWhile keeping
-- only pins inside their connect; a reader turns a hot's pins to skips.
------------------------------------------------------------------------

module simultaneous.ListPin where

open import Data.Bool using (Bool; true; false; T; not; _∧_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; applyUpTo) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁻; ∈-applyUpTo⁻)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; inside; ix; _⊕_; _<ᵖ_)
open import denotation.Events using (Timeline; inside-++; inside-self)
open import denotation.EmissionSet using (out; skip; end; pin)
open import denotation.Laws.Worlds using (⊕-assoc; inside-⊑)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; Listed; _⊣_; rows; mapRow; scanRows; takeRows; mergeRows; switchRows; exhaustRows;
  connRows; rejoinRow; outerRow; afterL; lanes; values; concatMap; when; mapM; module ScanL;
  module TakeL; module MergeL; module SwitchL; module ExhaustL; module BoundedL)
open import quickcheck.Tabled.Exact.Base using (cm⁻; when⁻; if⁻; bind⁻; mapM⁻; pastRows⁻; ∧-true)
open import simultaneous.Listing using (listC)
open import simultaneous.ColdOrder using (walk-nopin)

-- Every pin of a table lies inside its connect.
PinsIn : ∀ {A} → List (Row A) → Set
PinsIn rs = ∀ {k r} → (k , pin r) ∈ rs → T (inside r k)

private
  -- An end shown as an end or a skip is no pin.
  no-endpin : ∀ {B : Set} b {r} → pin {B} r ≡ (if b then end else skip) → ⊥
  no-endpin true  ()
  no-endpin false ()

  -- A lane end a bounded merge queues on or shows is no pin.
  queued-endpin : ∀ {B : Set} b d c {y r} → (y , pin {B} r) ≡ (if b then (c ⊕ [ ix 0 ] , skip) else (c , (if d then end else skip))) → ⊥
  queued-endpin true  d c ()
  queued-endpin false d c eq = no-endpin d (cong proj₂ eq)

  outer-pin : ∀ {A B : Set} (d : Pos → Bool) {rs : List (Row A)} → PinsIn rs → ∀ {x} → x ∈ rs
            → ∀ {y r} → (y , pin r) ∈ outerRow {A} {B} d x → T (inside r y)
  outer-pin d h {q , out _} xm (here ())
  outer-pin d h {q , out _} xm (there ())
  outer-pin d h {q , skip}  xm (here ())
  outer-pin d h {q , skip}  xm (there ())
  outer-pin d h {q , pin _} xm (here refl) = h xm
  outer-pin d h {q , pin _} xm (there ())
  outer-pin d h {c , end}   xm (here eq) = ⊥-elim (no-endpin (d c) (cong proj₂ eq))
  outer-pin d h {c , end}   xm (there ())

  outers-pin : ∀ {A B : Set} (d : Pos → Bool) {rs : List (Row A)} → PinsIn rs → PinsIn (concatMap (outerRow {A} {B} d) rs)
  outers-pin d {rs} h m with cm⁻ {f = outerRow d} {xs = rs} m
  ... | (x , xm , h′) = outer-pin d h xm h′

  -- A lane's rows mapped by a former keeping every pin where it is.
  Keeps : ∀ {B : Set} → (Row B → Row B) → Set
  Keeps {B} lr = ∀ x {y r} → (y , pin r) ≡ lr x → x ≡ (y , pin r)

  mapped-pin : ∀ {B : Set} (lr : Row B → Row B) → Keeps lr → (rs : List (Row B)) → PinsIn rs → PinsIn (mapL lr rs)
  mapped-pin lr kp rs h m with ∈-map⁻ lr m
  ... | (x , xm , eq) with kp x eq
  ...   | refl = h xm

  -- A lane read past its subscription keeps its pins.
  afterL-pin : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} → (∀ {a s l} → ln a s ≡ just l → PinsIn (rows l))
             → ∀ {a s l} → afterL ln a s ≡ just l → PinsIn (rows l)
  afterL-pin {ln = ln} ih {a} {s} e with bind⁻ {m = ln a s} e
  ... | ((rs ⊣ b) , e₀ , refl) = λ m → ih e₀ (proj₁ (pastRows⁻ rs m))

  lanes-pin : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} {vs : List (Pos × A)} {ls}
            → (∀ {a s l} → ln a s ≡ just l → PinsIn (rows l)) → lanes ln vs ≡ just ls
            → ∀ {q a l} → (q , a , l) ∈ ls → PinsIn (rows l)
  lanes-pin {ln = ln} {vs = vs} ih e m with mapM⁻ {xs = vs} e m
  ... | ((q′ , a′) , _ , fx) with bind⁻ {m = ln a′ (q′ ⊕ [ ix 1 ])} fx
  ... | (_ , el , refl) = ih el

  -- A lane at every start a bounded merge's levels list.
  levels-pin : ∀ {A B : Set} k (ln : A → Pos → Maybe (Listed B)) (o : Listed A) → (∀ {a s l} → ln a s ≡ just l → PinsIn (rows l))
             → ∀ c i ess vs {G} → BoundedL.levels k ln o c i ess vs ≡ just G
             → ∀ {j q a ss s l} → (j , q , a , ss) ∈ G → (s , l) ∈ ss → PinsIn (rows l)
  levels-pin k ln o ih zero    i ess vs refl ()
  levels-pin k ln o ih (suc c) i ess vs e gm sm with bind⁻ {m = mapM (BoundedL.entry k ln o i ess) vs} e
  ... | (gs , egs , e′) with bind⁻ {m = BoundedL.levels k ln o c (suc i) (BoundedL.endsOf k ln o gs ∷ ess) (Tb.Order.after (BoundedL.vals k ln o) vs)} e′
  ... | (rest , erest , refl) with ∈-++⁻ (mapL (i ,_) gs) gm
  ... | inj₂ rm = levels-pin k ln o ih c (suc i) (BoundedL.endsOf k ln o gs ∷ ess) (Tb.Order.after (BoundedL.vals k ln o) vs) erest rm sm
  ... | inj₁ im with ∈-map⁻ (i ,_) im
  ...   | (_ , xm , refl) with mapM⁻ {xs = vs} egs xm
  ...     | ((q′ , a′) , _ , fx) with bind⁻ {m = mapM (BoundedL.laneAt k ln o a′) (BoundedL.starts k ln o i q′ ess)} fx
  ...       | (ss′ , ess′ , refl) with mapM⁻ {xs = BoundedL.starts k ln o i q′ ess} ess′ sm
  ...         | (s′ , _ , fy) with bind⁻ {m = ln a′ s′} fy
  ...           | (_ , el , refl) = ih el

  -- A connect's pins: its body's, and its source's burst one label down.
  conn-pin : ∀ {A B : Set} p (σ : Listed A) (β : Listed B) → PinsIn (rows σ) → PinsIn (rows β) → PinsIn (rows (connRows p σ β))
  conn-pin {A} {B} p σ β hσ hβ m with ∈-++⁻ (rows β) m
  ... | inj₁ bm = hβ bm
  ... | inj₂ h with cm⁻ {xs = rows σ} h
  ...   | ((k , e) , km , h′) with if⁻ {b = inside (p ⊕ [ ix 1 ]) k} h′
  ...     | inj₁ (ik , here refl) with inside-⊑ (p ⊕ [ ix 1 ]) k (Equivalence.from T-≡ ik)
  ...       | (zs , refl) = Equivalence.from T-≡ (subst (λ z → inside p z ≡ true)
                              (sym (trans (⊕-assoc (p ⊕ [ ix 1 ]) zs [ ix 0 ]) (⊕-assoc p [ ix 1 ] (zs ++ [ ix 0 ]))))
                              (inside-++ p p (ix 1 ∷ (zs ++ [ ix 0 ])) (inside-self p)))
  conn-pin p σ β hσ hβ m | inj₂ h | ((k , e) , km , h′) | inj₁ (_ , there ())
  conn-pin p σ β hσ hβ m | inj₂ h | ((k , pin r) , km , h′) | inj₂ (_ , u) with when⁻ u
  ... | (b , refl) = Equivalence.from T-≡ (inside-++ r k [ ix 0 ] (proj₂ (∧-true b)))
  conn-pin p σ β hσ hβ m | inj₂ h | ((k , out _) , km , h′) | inj₂ (_ , u) with when⁻ u
  ... | (_ , ())
  conn-pin p σ β hσ hβ m | inj₂ h | ((k , skip) , km , h′) | inj₂ (_ , u) with when⁻ u
  ... | (_ , ())
  conn-pin p σ β hσ hβ m | inj₂ h | ((k , end) , km , h′) | inj₂ (_ , u) with when⁻ u
  ... | (_ , ())

  -- A reader shows no pin.
  rejoin-nopin : ∀ {A : Set} p (rs : List (Row A)) {y r} → (y , pin r) ∈ concatMap (rejoinRow p) rs → ⊥
  rejoin-nopin p rs m with cm⁻ {f = rejoinRow p} {xs = rs} m
  ... | ((q , out _) , _ , h) with when⁻ h
  ...   | (_ , ())
  rejoin-nopin p rs m | ((q , skip) , _ , h) with when⁻ h
  ...   | (_ , ())
  rejoin-nopin p rs m | ((q , pin _) , _ , h) with when⁻ h
  ...   | (_ , ())
  rejoin-nopin p rs m | ((q , end) , _ , h) with if⁻ {b = p <ᵖ q} h
  ...   | inj₁ (_ , here ())
  ...   | inj₁ (_ , there ())
  ...   | inj₂ (_ , here ())
  ...   | inj₂ (_ , there ())

  map-pin : ∀ {A B : Set} (f : A → B) (rs : List (Row A)) → PinsIn rs → PinsIn (mapL (mapRow f) rs)
  map-pin f rs h m with ∈-map⁻ (mapRow f) m
  ... | ((q , pin _) , rm , refl) = h rm
  ... | ((q , out _) , _ , ())
  ... | ((q , skip) , _ , ())
  ... | ((q , end) , _ , ())

  scan-pin : ∀ {A B : Set} (f : B → A → B) z (o : Listed A) → PinsIn (rows o) → PinsIn (rows (scanRows f z o))
  scan-pin f z o h m with ∈-++⁻ (concatMap (ScanL.folds f z o) (ScanL.table f z o)) m
  ... | inj₁ fm with cm⁻ {xs = ScanL.table f z o} fm
  ...   | (_ , _ , fm′) with ∈-map⁻ _ fm′
  ...     | (_ , _ , ())
  scan-pin f z o h m | inj₂ om with cm⁻ {xs = rows o} om
  ... | ((q , pin _) , rm , here refl) = h rm
  ... | ((q , pin _) , rm , there ())
  ... | ((q , out _) , _ , ())
  ... | ((q , skip) , _ , here ())
  ... | ((q , skip) , _ , there ())
  ... | ((q , end) , _ , here ())
  ... | ((q , end) , _ , there ())

  take-pin : ∀ {A : Set} i (keep : A → Bool) (o : Listed A) → PinsIn (rows (takeRows i keep o))
  take-pin {A} i keep o m with cm⁻ {f = TakeL.takeRow i keep o fs} {xs = rows o} m
    where fs = TakeL.failures i keep o
  ... | ((q , pin _) , _ , h) with when⁻ h
  ...   | (b , refl) = Equivalence.from T-≡ (proj₂ (∧-true b))
  take-pin i keep o m | ((q , out a) , _ , h) with if⁻ {b = TakeL.failed i keep o (TakeL.failures i keep o) q} h
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , h′) with if⁻ {b = keep a} h′
  ...   | inj₁ (_ , here ())
  ...   | inj₁ (_ , there ())
  ...   | inj₂ (_ , h″) with ∈-++⁻ (when i (q ⊕ [ ix 0 ] , out a)) h″
  ...     | inj₁ w with when⁻ w
  ...       | (_ , ())
  take-pin i keep o m | ((q , out a) , _ , h) | inj₂ (_ , h′) | inj₂ (_ , h″) | inj₂ (here ())
  take-pin i keep o m | ((q , out a) , _ , h) | inj₂ (_ , h′) | inj₂ (_ , h″) | inj₂ (there ())
  take-pin i keep o m | ((q , skip) , _ , h) with if⁻ {b = TakeL.failed i keep o (TakeL.failures i keep o) q} h
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())
  take-pin i keep o m | ((q , end) , _ , h) with if⁻ {b = TakeL.failed i keep o (TakeL.failures i keep o) q} h
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())

  merge-keeps : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) es → Keeps (MergeL.Ended.laneRow o ls es)
  merge-keeps o ls es (c , end)   eq = ⊥-elim (no-endpin (MergeL.Ended.done o ls es c) (cong proj₂ eq))
  merge-keeps o ls es (k , out _) ()
  merge-keeps o ls es (k , skip)  ()
  merge-keeps o ls es (k , pin _) refl = refl

  merge-pin : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) → PinsIn (rows o)
            → (∀ {q a l} → (q , a , l) ∈ ls → PinsIn (rows l)) → PinsIn (rows (mergeRows o ls))
  merge-pin {A} {B} o ls ho hl m with ∈-++⁻ (concatMap (outerRow (MergeL.Ended.done o ls (Tb.ends (rows o)))) (rows o)) m
  ... | inj₁ h = outers-pin (MergeL.Ended.done o ls (Tb.ends (rows o))) ho h
  ... | inj₂ h with cm⁻ {f = λ { (_ , _ , l) → mapL (MergeL.Ended.laneRow o ls (Tb.ends (rows o))) (rows l) }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) = mapped-pin _ (merge-keeps o ls (Tb.ends (rows o))) (rows l) (hl lm) h′

  exhaust-keeps : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) rs → Keeps (ExhaustL.Ran.laneRow o ls rs)
  exhaust-keeps o ls rs (c , end)   eq = ⊥-elim (no-endpin (ExhaustL.Ran.done o ls rs c) (cong proj₂ eq))
  exhaust-keeps o ls rs (k , out _) ()
  exhaust-keeps o ls rs (k , skip)  ()
  exhaust-keeps o ls rs (k , pin _) refl = refl

  exhaust-pin : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) → PinsIn (rows o)
              → (∀ {q a l} → (q , a , l) ∈ ls → PinsIn (rows l)) → PinsIn (rows (exhaustRows o ls))
  exhaust-pin {A} {B} o ls ho hl m with ∈-++⁻ (concatMap (outerRow (ExhaustL.Ran.done o ls (ExhaustL.runs o ls))) (rows o)) m
  ... | inj₁ h = outers-pin (ExhaustL.Ran.done o ls (ExhaustL.runs o ls)) ho h
  ... | inj₂ h with cm⁻ {f = λ { (q , _ , l) → if ExhaustL.Ran.ranᵇ o ls (ExhaustL.runs o ls) q then mapL (ExhaustL.Ran.laneRow o ls (ExhaustL.runs o ls)) (rows l) else [] }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) with if⁻ {b = ExhaustL.Ran.ranᵇ o ls (ExhaustL.runs o ls) q} h′
  ...     | inj₂ (_ , ())
  ...     | inj₁ (_ , h″) = mapped-pin _ (exhaust-keeps o ls (ExhaustL.runs o ls)) (rows l) (hl lm) h″

  switch-pin : ∀ {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) → PinsIn (rows o)
             → (∀ {q a l} → (q , a , l) ∈ ls → PinsIn (rows l)) → PinsIn (rows (switchRows o ls))
  switch-pin {A} {B} o ls ho hl m with ∈-++⁻ (concatMap (outerRow (SwitchL.done o ls)) (rows o)) m
  ... | inj₁ h = outers-pin (SwitchL.done o ls) ho h
  ... | inj₂ h with cm⁻ {f = λ { (q , _ , l) → concatMap (SwitchL.laneRow o ls q) (rows l) }} {xs = ls} h
  ...   | ((q , a , l) , lm , h′) with cm⁻ {f = SwitchL.laneRow o ls q} {xs = rows l} h′
  ...     | ((k , pin r) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q k} h″
  ...       | inj₁ (_ , w) with when⁻ {b = not (SwitchL.cutᵇ o ls q r) ∧ inside r k} {x = (k , pin r)} w
  ...         | (b , refl) = Equivalence.from T-≡ (proj₂ (∧-true b))
  switch-pin o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , pin r) , xm , h″) | inj₂ (_ , here refl) = hl lm xm
  switch-pin o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , pin r) , xm , h″) | inj₂ (_ , there ())
  switch-pin o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , out _) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q k} h″
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())
  switch-pin o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((k , skip) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q k} h″
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here ())
  ... | inj₂ (_ , there ())
  switch-pin o ls ho hl m | inj₂ h | ((q , a , l) , lm , h′) | ((c , end) , xm , h″) with if⁻ {b = SwitchL.cutᵇ o ls q c} h″
  ... | inj₁ (_ , ())
  ... | inj₂ (_ , here eq) = ⊥-elim (no-endpin (SwitchL.done o ls c) (cong proj₂ eq))
  ... | inj₂ (_ , there ())

  bounded-pin : ∀ {A B : Set} k (ln : A → Pos → Maybe (Listed B)) (o : Listed A) → PinsIn (rows o)
              → (∀ {a s l} → ln a s ≡ just l → PinsIn (rows l)) → ∀ {l} → BoundedL.listB k ln o ≡ just l → PinsIn (rows l)
  bounded-pin {A} {B} k ln o ho ih e with bind⁻ {m = BoundedL.levels k ln o (Data.List.length (BoundedL.vals k ln o)) 0 [] (Tb.Order.nths (BoundedL.vals k ln o) 0)} e
  ... | (G , eG , refl) = go
    where
      go : PinsIn (rows (BoundedL.boundedRows k ln o G))
      go m with ∈-++⁻ (concatMap (outerRow (BoundedL.done k ln o G)) (rows o)) m
      ... | inj₁ h = outers-pin (BoundedL.done k ln o G) ho h
      ... | inj₂ h with cm⁻ {f = λ { (_ , _ , _ , ss) → concatMap (λ { (_ , l) → mapL (BoundedL.laneRow k ln o G) (rows l) }) ss }} {xs = G} h
      ...   | ((j , q , a , ss) , gm , h′) with cm⁻ {f = λ { (_ , l) → mapL (BoundedL.laneRow k ln o G) (rows l) }} {xs = ss} h′
      ...     | ((s , l) , sm , h″) with ∈-map⁻ (BoundedL.laneRow k ln o G) h″
      ...       | ((y , pin r) , xm , refl) = levels-pin k ln o ih (Data.List.length (BoundedL.vals k ln o)) 0 [] (Tb.Order.nths (BoundedL.vals k ln o) 0) eG gm sm xm
      ...       | ((y , out _) , _ , ())
      ...       | ((y , skip) , _ , ())
      ...       | ((c , end) , _ , eq) = ⊥-elim (queued-endpin (BoundedL.queued k ln o G c) (BoundedL.done k ln o G c) c eq)

-- A LISTED PIN LIES INSIDE ITS CONNECT.
listC-pin : ∀ {Γ A} N n (o : Obs Timeline Γ A) {ρL : All Listed Γ} p {l} → listC N n o ρL p ≡ just l → PinsIn (rows l)
listC-pin N n       (cold c)          p refl m = ⊥-elim (walk-nopin N _ m)
listC-pin N n       empty             p refl (here ())
listC-pin N n       empty             p refl (there ())
listC-pin N n       (of xs)           p refl m = ⊥-elim (walk-nopin (suc (Data.List.length xs)) _ m)
listC-pin N n       (map f s) {ρL}    p e with bind⁻ {m = listC N n s ρL p} e
... | ((rs ⊣ b) , e₀ , refl) = map-pin f rs (listC-pin N n s p e₀)
listC-pin N n       (scan f z s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , refl) = scan-pin f z o (listC-pin N n s p e₀)
listC-pin N n       (takeWhile i q s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , refl) = take-pin i q o
listC-pin N n       (flatMap (mergeᶠ nothing) f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) =
  merge-pin o ls (listC-pin N n s p e₀) (lanes-pin {ln = afterL (λ a → listC N n (f a) ρL)} {vs = values (rows o)} (afterL-pin {ln = λ a → listC N n (f a) ρL} (λ {a} {s′} → listC-pin N n (f a) s′)) els)
listC-pin N n       (flatMap (mergeᶠ (just k)) f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) = bounded-pin k (afterL (λ a → listC N n (f a) ρL)) o (listC-pin N n s p e₀)
                        (afterL-pin {ln = λ a → listC N n (f a) ρL} (λ {a} {s′} → listC-pin N n (f a) s′)) e₁
listC-pin N n       (flatMap switchᶠ f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) =
  switch-pin o ls (listC-pin N n s p e₀) (lanes-pin {ln = afterL (λ a → listC N n (f a) ρL)} {vs = values (rows o)} (afterL-pin {ln = λ a → listC N n (f a) ρL} (λ {a} {s′} → listC-pin N n (f a) s′)) els)
listC-pin N n       (flatMap exhaustᶠ f s) {ρL} p e with bind⁻ {m = listC N n s ρL p} e
... | (o , e₀ , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) =
  exhaust-pin o ls (listC-pin N n s p e₀) (lanes-pin {ln = afterL (λ a → listC N n (f a) ρL)} {vs = values (rows o)} (afterL-pin {ln = λ a → listC N n (f a) ρL} (λ {a} {s′} → listC-pin N n (f a) s′)) els)
listC-pin N n       (connect s b) {ρL} p e with bind⁻ {m = listC N n s ρL (p ⊕ [ ix 1 ])} e
... | (σ , eσ , e₁) with bind⁻ {m = listC N n b (Tb.hotOf σ All.∷ ρL) (p ⊕ [ ix 0 ])} e₁
... | (β , eβ , refl) = conn-pin p σ β (listC-pin N n s (p ⊕ [ ix 1 ]) eσ) (listC-pin N n b (p ⊕ [ ix 0 ]) eβ)
listC-pin N n       (connected i) {ρL} p refl with lookup ρL i
... | rs ⊣ b = λ m → ⊥-elim (rejoin-nopin p rs m)
listC-pin N zero    (defer l)         p refl m with ∈-applyUpTo⁻ _ m
... | (_ , _ , ())
listC-pin N (suc n) (defer l) {ρL}    p e with bind⁻ {m = listC N n (Later.force l) ρL (p ⊕ [ ix 1 ])} e
... | (b , eb , refl) = λ { (here ()) ; (there m) → listC-pin N n (Later.force l) (p ⊕ [ ix 1 ]) eb m }
