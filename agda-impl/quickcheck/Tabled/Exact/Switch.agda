{-# OPTIONS --guardedness #-}

-- SWITCH, LISTED EXACTLY: merge's listing (`quickcheck.Tabled.Exact`'s
-- `MergeX`), each lane row cut once a later value arrives before it, and
-- only the latest lane's end counted toward the whole's.
module quickcheck.Tabled.Exact.Switch where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.List using (List; []; _∷_; _++_; [_]) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; _<ᵖ_; ix)
open import denotation.EmissionSet using (out; skip; end; EmissionSet; Den; enter)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled using (Listed; rows; short; concatMap; endBy; values; outerRow; switchRows; module SwitchL)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; fromT; offT; not-T; T-not; ∨-false; ∧-true; ∧-intro; off; or-of; or-right;
  any⁻; any⁺; any-off; all⁻; all⁺; single⁻; when⁻; when⁺; if⁻; if-t; if-f; cm⁻; cm⁺; values⁻; values⁺; endBy→; →endBy)

module SwitchX {A B : Set} (fD : A → Den B) (t : EmissionSet A) (o : Listed A) (ls : List (Pos × A × Listed B))
  (u : short (switchRows o ls) ≡ false)
  (eo : Exactly o t)
  (ls-from : ∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (enter (fD a) (q ++ [ ix 1 ])))
  (ls-to : ∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  where
  open Tb.Switch fD t
  open SwitchL o ls using (vals; cutᵇ; latest; done; live; laneRow)

  private
    exo : Exact o t
    exo = eo (proj₁ (∨-false {short o} u))

    uncut : ∀ {q a l} → (q , a , l) ∈ ls → short l ≡ false
    uncut m = any-off {xs = ls} (proj₂ (∨-false {short o} u)) m

    exl : ∀ {q a l} → (q , a , l) ∈ ls → Exact l (enter (fD a) (q ++ [ ix 1 ]))
    exl m = proj₂ (ls-from m) (uncut m)

    out-of : ∀ {q a l} → (q , a , l) ∈ ls → t q (out a)
    out-of m = sound exo (values⁻ (proj₁ (ls-from m)))

    cut→ : ∀ q k → cutᵇ q k ≡ true → Cut q k
    cut→ q k e with any⁻ {xs = vals} e
    ... | ((q′ , a′) , m , h) with ∧-true {q <ᵖ q′} h
    ... | (l₁ , l₂) = q′ , a′ , sound exo (values⁻ m) , Equivalence.from T-≡ l₁ , Equivalence.from T-≡ l₂

    →cut : ∀ q k → Cut q k → cutᵇ q k ≡ true
    →cut q k (q′ , a′ , x , l₁ , l₂) = any⁺ (values⁺ (complete exo x)) (∧-intro (fromT l₁) (fromT l₂))

    latest→ : ∀ q → latest q ≡ true → Latest q
    latest→ q e x = not-T (all⁻ e (values⁺ (complete exo x)))

    →latest : ∀ q → Latest q → latest q ≡ true
    →latest q h = all⁺ {xs = vals} λ { {q′ , a′} m → T-not (h (sound exo (values⁻ m))) }

    done→ : ∀ c → done c ≡ true → Done c
    done→ c e = endBy→ exo {c} (proj₁ (∧-true {endBy (rows o) c} e)) , λ {q} x L →
      let (l , m) = ls-to (values⁺ (complete exo x))
      in endBy→ (exl m) {c} (or-right (→latest q L) (all⁻ {xs = ls} (proj₂ (∧-true {endBy (rows o) c} e)) m))

    →done : ∀ c → Done c → done c ≡ true
    →done c ((c₀ , x , le) , lanes) = ∧-intro (→endBy exo {c₀} {c} x le) (all⁺ {xs = ls} λ { {q , a , l} m →
      or-of (latest q) λ lt → let (c′ , y , le′) = lanes (out-of m) (latest→ q lt) in →endBy (exl m) {c′} {c} y le′ })

    end-row : ∀ {c} → t c end → SwitchT c (if done c then end else skip)
    end-row {c} x with done c in dc
    ... | true  = oend x (done→ c dc)
    ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    lend-row : ∀ {q a c} → t q (out a) → Lane q a c end → ¬ Cut q c → SwitchT c (if done c then end else skip)
    lend-row {c = c} x y nC with done c in dc
    ... | true  = lend x y nC (done→ c dc)
    ... | false = lpass x y nC (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow done r → SwitchT q e
    outer-s {k , out a} rm h with single⁻ h
    ... | refl = val (sound exo rm)
    outer-s {k , skip} rm h with single⁻ h
    ... | refl = step (sound exo rm)
    outer-s {c , end} rm h with single⁻ h
    ... | refl = end-row (sound exo rm)

    live-s : ∀ {q₀ a l k e₀ q e} → (q₀ , a , l) ∈ ls → Lane q₀ a k e₀ → ¬ Cut q₀ k → (q , e) ≡ live (k , e₀) → SwitchT q e
    live-s {e₀ = out b} m y nC refl = lane (out-of m) y tt nC
    live-s {e₀ = skip}  m y nC refl = lane (out-of m) y tt nC
    live-s {e₀ = end}   m y nC refl = lend-row (out-of m) y nC

    lane-s : ∀ {q₀ a l r q e} → (q₀ , a , l) ∈ ls → r ∈ rows l → (q , e) ∈ laneRow q₀ r → SwitchT q e
    lane-s {q₀} {r = k , e₀} m rm h with if⁻ {b = cutᵇ q₀ k} h
    ... | inj₁ (ct , h′) with when⁻ h′
    ... | (ins , refl) = left (out-of m) (sound (exl m) rm) (cut→ q₀ k ct) (Equivalence.from T-≡ ins)
    lane-s {q₀} {r = k , e₀} m rm h | inj₂ (nc , h′) =
      live-s m (sound (exl m) rm) (λ C → offT nc (Equivalence.from T-≡ (→cut q₀ k C))) (single⁻ h′)

    outer-end : ∀ {c b} → done c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} done (c , end)
    outer-end refl = here refl

    live-end : ∀ {c b} → done c ≡ b → (c , (if b then end else skip)) ∈ [ live (c , end) ]
    live-end refl = here refl

    live-in : ∀ {k e} → Tb.Work e → (k , e) ∈ [ live (k , e) ]
    live-in {e = out b} _ = here refl
    live-in {e = skip}  _ = here refl
    live-in {e = end}   ()

    -- A lane's row, uncut.
    kept : ∀ {q a k e r} → t q (out a) → Lane q a k e → ¬ Cut q k → r ∈ [ live (k , e) ] → r ∈ rows (switchRows o ls)
    kept {q} {a} {k} {e} x y nC h =
      let (l , m) = ls-to (values⁺ (complete exo x)) in
      ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (cm⁺ (complete (exl m) y) (if-f (off (cut→ q k) nC) h)))

  sound-w : ∀ {q e} → (q , e) ∈ rows (switchRows o ls) → SwitchT q e
  sound-w m with ∈-++⁻ (concatMap (outerRow done) (rows o)) m
  ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
  ... | inj₂ h with cm⁻ {xs = ls} h
  ... | ((q₀ , a , l) , lm , h′) with cm⁻ {xs = rows l} h′
  ... | (r , rm , h″) = lane-s lm rm h″

  complete-w : ∀ {q e} → SwitchT q e → (q , e) ∈ rows (switchRows o ls)
  complete-w (val x)          = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-w (step x)         = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-w (oend {c} x D)   = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→done c D)))
  complete-w (opass {c} x nD) = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (done→ c) nD)))
  complete-w (lane x y w nC)  = kept x y nC (live-in w)
  complete-w (lend {c = c} x y nC D)   = kept x y nC (live-end {c} (→done c D))
  complete-w (lpass {c = c} x y nC nD) = kept x y nC (live-end {c} (off (done→ c) nD))
  complete-w (left {q} {a} {k} x y C ins) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (cm⁺ (complete (exl m) y) (if-t (→cut q k C) (when⁺ (fromT ins)))))

switch-exact : ∀ {A B} (fD : A → Den B) {t : EmissionSet A} (o : Listed A) (ls : List (Pos × A × Listed B)) → Exactly o t
  → (∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (enter (fD a) (q ++ [ ix 1 ])))
  → (∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  → Exactly (switchRows o ls) (Tb.Switch.SwitchT fD t)
switch-exact fD {t} o ls eo from to u = record { sound = sound-w ; complete = complete-w }
  where open SwitchX fD t o ls u eo from to
