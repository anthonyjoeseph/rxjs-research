{-# OPTIONS --guardedness #-}

-- EXHAUST, LISTED EXACTLY: merge's listing (`quickcheck.Tabled.Exact`'s
-- `MergeX`) over the lanes `Exhaust.Run` runs, where the last runs are
-- chained value by value as `Scan.Acc`'s folds are
-- (`quickcheck.Tabled.Exact.Scan`).  A last run's lane is one that runs,
-- so the chain reads only lanes the listing shows.
module quickcheck.Tabled.Exact.Exhaust where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (<-≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (does)

open import denotation.Events using (Pos; _<ᵖ_; _≟ᵖ_; ix)
open import denotation.EmissionSet using (out; skip; end; EmissionSet; Den; After; LaneOf)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled
  using (Row; Listed; rows; short; concatMap; when; endBy; endBefore; values; outerRow; exhaustRows;
  module ExhaustL; module Order)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; fromT; offT; ∨-false; ∧-true; ∧-intro; off; or-of; or-right; ≟-refl; ≟-true;
  any⁻; any⁺; any-off; all⁻; all⁺; single⁻; when⁻; when⁺; if⁻; if-t; cm⁻; cm⁺; values⁻; values⁺;
  endBy→; →endBy; endBefore→; →endBefore; proper→; →proper; cnt; cnt≤; cnt-lt; module OrderX)

module ExhaustX {A B : Set} (fD : A → Den B) (t : EmissionSet A) (o : Listed A) (ls : List (Pos × A × Listed B))
  (u : short (exhaustRows o ls) ≡ false)
  (eo : Exactly o t)
  (ls-from : ∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (After (fD a) (q ++ [ ix 1 ])))
  (ls-to : ∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  where
  open Tb.Exhaust fD t
  open Tb.Values t using (Next)
  open ExhaustL o ls using (vals; moves; curs; prior; runᵇ; runs)
  open ExhaustL.Ran o ls runs using (ranᵇ; done; laneRow)
  open Order vals using (minᵇ; nextᵇ)

  private
    exo : Exact o t
    exo = eo (proj₁ (∨-false {short o} u))

    uncut : ∀ {q a l} → (q , a , l) ∈ ls → short l ≡ false
    uncut m = any-off {xs = ls} (proj₂ (∨-false {short o} u)) m

    exl : ∀ {q a l} → (q , a , l) ∈ ls → Exact l (After (fD a) (q ++ [ ix 1 ]))
    exl m = proj₂ (ls-from m) (uncut m)

    out-of : ∀ {q a l} → (q , a , l) ∈ ls → t q (out a)
    out-of m = sound exo (values⁻ (proj₁ (ls-from m)))

    lane-of : ∀ {q a} → t q (out a) → Σ (Listed B) λ l → (q , a , l) ∈ ls
    lane-of x = ls-to (values⁺ (complete exo x))

  open OrderX exo using (min→; →min; next→; →next)

  ----------------------------------------------------------------------
  -- The last runs

  cur-val : ∀ {q₂ q} → Cur q₂ q → Σ A λ a → t q₂ (out a)
  cur-val (cur₀ x _)           = _ , x
  cur-val (run _ _ _ _ x _ _)  = _ , x
  cur-val (drop _ _ _ x _ _)   = _ , x

  moves-s : ∀ {q₁ q q₂ a₂ r p} → Cur q₁ q → t q₂ (out a₂) → q₁ Tb.≺ q₂ → Next q₁ q₂ → r ∈ ls → p ∈ moves q₂ q r → Cur q₂ p
  moves-s {q = q} {q₂} {r = q′ , a , l} C x₂ lt nx m h with if⁻ {b = does (q′ ≟ᵖ q)} h
  ... | inj₂ (_ , ())
  ... | inj₁ (d , h′) with ≟-true {q′} {q} d
  ... | refl with ∈-++⁻ (when (endBefore (rows l) q₂) q₂) h′
  ... | inj₁ h″ = let (eb , e) = when⁻ h″ ; (c , y , cq) = endBefore→ (exl m) eb in
    subst (Cur q₂) (sym e) (run C (out-of m) y cq x₂ lt nx)
  ... | inj₂ h″ = let (pb , e) = when⁻ h″ in subst (Cur q₂) (sym e) (drop C (out-of m) (proper→ (exl m) pb) x₂ lt nx)

  curs-s : ∀ n {q₂ a₂ q} → t q₂ (out a₂) → q ∈ curs n q₂ → Cur q₂ q
  curs-s zero x ()
  curs-s (suc n) {q₂} x m with ∈-++⁻ (when (minᵇ q₂) q₂) m
  ... | inj₁ h with when⁻ h
  ... | (mn , refl) = cur₀ x (min→ mn)
  curs-s (suc n) {q₂} x m | inj₂ h with cm⁻ {xs = vals} h
  ... | ((q₁ , a₁) , vm , h′) with if⁻ {b = nextᵇ q₁ q₂} h′
  ... | inj₂ (_ , ())
  ... | inj₁ (nx , h″) with cm⁻ {xs = curs n q₁} h″
  ... | (q , qm , h‴) with cm⁻ {xs = ls} h‴
  ... | (r , rm , h⁗) =
    moves-s (curs-s n (sound exo (values⁻ vm)) qm) x (proj₁ (next→ q₁ q₂ nx)) (proj₂ (next→ q₁ q₂ nx)) rm h⁗

  curs-c : ∀ {q₂ q} → Cur q₂ q → ∀ n → cnt q₂ vals < n → q ∈ curs n q₂
  curs-c (cur₀ x mn) zero    ()
  curs-c (cur₀ x mn) (suc n) _ = ∈-++⁺ˡ (when⁺ (→min mn))
  curs-c (run C x y cq x₂ lt nx) zero ()
  curs-c (run {q₁} {q} {a} {c} {q₂} C x y cq x₂ lt nx) (suc n) (s≤s le) =
    let (a₁ , x₁) = cur-val C ; v₁ = values⁺ (complete exo x₁) ; (l , lm) = lane-of x in
    ∈-++⁺ʳ (when (minᵇ q₂) q₂) (cm⁺ v₁ (if-t (→next q₁ q₂ lt nx)
      (cm⁺ (curs-c C n (<-≤-trans (cnt-lt v₁ (fromT lt)) le))
        (cm⁺ lm (if-t (≟-refl q) (∈-++⁺ˡ (when⁺ (→endBefore (exl lm) y cq))))))))
  curs-c (drop C x f x₂ lt nx) zero ()
  curs-c (drop {q₁} {q} {a} {q₂} C x f x₂ lt nx) (suc n) (s≤s le) =
    let (a₁ , x₁) = cur-val C ; v₁ = values⁺ (complete exo x₁) ; (l , lm) = lane-of x in
    ∈-++⁺ʳ (when (minᵇ q₂) q₂) (cm⁺ v₁ (if-t (→next q₁ q₂ lt nx)
      (cm⁺ (curs-c C n (<-≤-trans (cnt-lt v₁ (fromT lt)) le))
        (cm⁺ lm (if-t (≟-refl q) (∈-++⁺ʳ (when (endBefore (rows l) q₂) q₂) (when⁺ (→proper (exl lm) f))))))))

  run→ : ∀ q {a} → t q (out a) → runᵇ q ≡ true → Run q
  run→ q x e with any⁻ {xs = curs (suc (length vals)) q} e
  ... | (q′ , m , d) with ≟-true {q′} {q} d
  ... | refl = curs-s (suc (length vals)) x m

  →run : ∀ q → Run q → runᵇ q ≡ true
  →run q R = any⁺ {xs = curs (suc (length vals)) q} (curs-c R (suc (length vals)) (s≤s (cnt≤ vals))) (≟-refl q)

  ran→ : ∀ q → ranᵇ q ≡ true → Run q
  ran→ q e with any⁻ {xs = runs} e
  ... | (q′ , m , d) with ≟-true {q′} {q} d
  ... | refl with cm⁻ {xs = ls} m
  ... | ((q″ , a , l) , lm , h) with when⁻ h
  ... | (rn , refl) = run→ q′ (out-of lm) rn

  →ran : ∀ q {a} → t q (out a) → Run q → ranᵇ q ≡ true
  →ran q x R = let (l , m) = lane-of x in any⁺ {xs = runs} (cm⁺ m (when⁺ (→run q R))) (≟-refl q)

  ----------------------------------------------------------------------
  -- The rows

  private
    done→ : ∀ c → done c ≡ true → Done c
    done→ c e = endBy→ exo {c} (proj₁ (∧-true {endBy (rows o) c} e)) , λ {q} x R qc _ →
      let (l , m) = lane-of x
      in endBy→ (exl m) {c} (or-right (→ran q x R) (or-right (fromT qc) (all⁻ {xs = ls} (proj₂ (∧-true {endBy (rows o) c} e)) m)))

    →done : ∀ c → Done c → done c ≡ true
    →done c ((c₀ , x , le) , lanes) = ∧-intro (→endBy exo {c₀} {c} x le) (all⁺ {xs = ls} λ { {q , a , l} m →
      or-of (q <ᵖ c) λ qc → or-of (ranᵇ q) λ rn →
        let (c′ , y , le′) = lanes (out-of m) (ran→ q rn) (Equivalence.from T-≡ qc) (λ ()) in →endBy (exl m) {c′} {c} y le′ })

    end-row : ∀ {c} → t c end → JoinT c (if done c then end else skip)
    end-row {c} x with done c in dc
    ... | true  = oend x (done→ c dc)
    ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    lend-row : ∀ {q a c} → t q (out a) → Run q → LaneOf fD q a c end → JoinT c (if done c then end else skip)
    lend-row {c = c} x R y with done c in dc
    ... | true  = lend x R y (λ ()) (λ ()) (done→ c dc)
    ... | false = lpass x R y (λ ()) (λ ()) (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow done r → JoinT q e
    outer-s {k , out a} rm h with single⁻ h
    ... | refl = val (sound exo rm)
    outer-s {k , skip} rm h with single⁻ h
    ... | refl = step (sound exo rm)
    outer-s {c , end} rm h with single⁻ h
    ... | refl = end-row (sound exo rm)

    lane-s : ∀ {q₀ a l r q e} → (q₀ , a , l) ∈ ls → Run q₀ → r ∈ rows l → (q , e) ≡ laneRow r → JoinT q e
    lane-s {r = k , out b} m R rm refl = lane (out-of m) R (sound (exl m) rm) (λ ()) tt
    lane-s {r = k , skip}  m R rm refl = lane (out-of m) R (sound (exl m) rm) (λ ()) tt
    lane-s {r = c , end}   m R rm refl = lend-row (out-of m) R (sound (exl m) rm)

    outer-end : ∀ {c b} → done c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} done (c , end)
    outer-end refl = here refl

    lane-end : ∀ {c b} {rs : List (Row B)} → done c ≡ b → (c , end) ∈ rs → (c , (if b then end else skip)) ∈ mapL laneRow rs
    lane-end refl r = ∈-map⁺ laneRow r

    lane-in : ∀ {k e} {rs : List (Row B)} → Tb.Work e → (k , e) ∈ rs → (k , e) ∈ mapL laneRow rs
    lane-in {e = out b} _ r = ∈-map⁺ laneRow r
    lane-in {e = skip}  _ r = ∈-map⁺ laneRow r
    lane-in {e = end}   () r

    -- A row of a lane that runs.
    shown : ∀ {q a r} → t q (out a) → Run q → (∀ {l} → (q , a , l) ∈ ls → r ∈ mapL laneRow (rows l)) → r ∈ rows (exhaustRows o ls)
    shown {q} x R h = let (l , m) = lane-of x in
      ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (if-t (→ran q x R) (h m)))

  sound-e : ∀ {q e} → (q , e) ∈ rows (exhaustRows o ls) → JoinT q e
  sound-e m with ∈-++⁻ (concatMap (outerRow done) (rows o)) m
  ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
  ... | inj₂ h with cm⁻ {xs = ls} h
  ... | ((q₀ , a , l) , lm , h′) with if⁻ {b = ranᵇ q₀} h′
  ... | inj₂ (_ , ())
  ... | inj₁ (rn , h″) with ∈-map⁻ laneRow h″
  ... | (r , rm , eq) = lane-s lm (ran→ q₀ rn) rm eq

  complete-e : ∀ {q e} → JoinT q e → (q , e) ∈ rows (exhaustRows o ls)
  complete-e (val x)          = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-e (step x)         = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-e (oend {c} x D)   = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→done c D)))
  complete-e (opass {c} x nD) = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (done→ c) nD)))
  complete-e (lane x R y _ w) = shown x R λ m → lane-in w (complete (exl m) y)
  complete-e (lend {c = c} x R y _ _ D) = shown x R λ m → lane-end {c} (→done c D) (complete (exl m) y)
  complete-e (lpass {c = c} x R y _ _ nD) = shown x R λ m → lane-end {c} (off (done→ c) nD) (complete (exl m) y)
  complete-e (left _ _ _ () _)
  complete-e (run () _)
  complete-e (rend () _ _)
  complete-e (rpass () _ _)
  complete-e (hand _ _ _ _ ())
  complete-e (rhand () _)

exhaust-exact : ∀ {A B} (fD : A → Den B) {t : EmissionSet A} (o : Listed A) (ls : List (Pos × A × Listed B)) → Exactly o t
  → (∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (After (fD a) (q ++ [ ix 1 ])))
  → (∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  → Exactly (exhaustRows o ls) (Tb.Exhaust.JoinT fD t)
exhaust-exact fD {t} o ls eo from to u = record { sound = sound-e ; complete = complete-e }
  where open ExhaustX fD t o ls u eo from to
