{-# OPTIONS --guardedness #-}

-- THE LISTING IS THE EMISSION SET: an uncut listing (`quickcheck.Tabled`) holds
-- exactly the rows of the emission set approximant it mirrors, so every trace
-- the oracle compares against rxjs is read off the relation itself.
--
-- Exact, not merely sound: a listed end or skip decides an emission set predicate
-- that quantifies over the inputs' rows (`Merge.Done`, `Bounded.Queued`,
-- `Connect.Alive`, `Proper`), so it is sound only if those inputs were
-- listed completely.  A cut listing claims nothing.
module quickcheck.Tabled.Exact where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; null) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Timeline; _<ᵖ_; inside; ix)
open import denotation.EmissionSet
  using (out; skip; end; EmissionSet; InE; at-out; at-skip; at-end; on-out; on-skip; Proper; Truncate; Rejoin;
  ended; late; Den; enter; After; MapT; map-out; map-skip; map-end; DeferT; guard; DenEnv; approxᵀ)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled
  using (Row; Listed; _⊣_; rows; short; concatMap; when; endBy; proper; values; fuel; horizon; walk;
  mapRow; mapRows; rejoinRow; rejoin; hotOf; outerRow; mergeRows; connRows; takeRows; lanes; afterL;
  module MergeL; module TakeL; module ConnL; listT)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; fromT; fromNot; offT; T-not; ∨-false; ∧-true; ∧-intro; off; or-of; or-right;
  any⁻; any⁺; any-off; all⁻; all⁺; single⁻; when⁻; when⁺; if⁻; if-t; if-f; cm⁻; cm⁺; bind⁻;
  values⁻; values⁺; endBy→; →endBy; proper→; →proper; lanes-from; lanes-to; afterL-exact)
open import quickcheck.Tabled.Exact.Scan using (scan-exact)
open import quickcheck.Tabled.Exact.Switch using (switch-exact)
open import quickcheck.Tabled.Exact.Exhaust using (exhaust-exact)
open import quickcheck.Tabled.Exact.Bounded using (bounded-exact)

------------------------------------------------------------------------
-- Leaves

walk-exact : ∀ {A} n (ev : E.Events A) → Exactly (walk n ev) (InE ev)
walk-exact zero ev ()
walk-exact (suc n) (E.out k a r) u with E.tick k Data.Nat.≤ᵇ horizon
... | true = let ih = walk-exact n (E.Events∞.force r) u in record
  { sound    = λ { (here refl) → at-out ; (there m) → on-out (sound ih m) }
  ; complete = λ { at-out → here refl ; (on-out x) → there (complete ih x) } }
... | false = ⊥-elim (offT u (Equivalence.from T-≡ refl))
walk-exact (suc n) (E.skip k r) u with E.tick k Data.Nat.≤ᵇ horizon
... | true = let ih = walk-exact n (E.Events∞.force r) u in record
  { sound    = λ { (here refl) → at-skip ; (there m) → on-skip (sound ih m) }
  ; complete = λ { at-skip → here refl ; (on-skip x) → there (complete ih x) } }
... | false = ⊥-elim (offT u (Equivalence.from T-≡ refl))
walk-exact (suc n) (E.end k) u with E.tick k Data.Nat.≤ᵇ horizon
... | true  = record { sound = λ { (here refl) → at-end ; (there ()) } ; complete = λ { at-end → here refl } }
... | false = ⊥-elim (offT u (Equivalence.from T-≡ refl))
walk-exact (suc n) E.hush u = record { sound = λ () ; complete = λ () }

end-exact : ∀ {A} (k : Pos) → Exactly {A} ([ k , end ] ⊣ false) (InE (E.end k))
end-exact k _ = record { sound = λ { (here refl) → at-end ; (there ()) } ; complete = λ { at-end → here refl } }

------------------------------------------------------------------------
-- One input

map-exact : ∀ {A B} (f : A → B) {l : Listed A} {t : EmissionSet A} → Exactly l t → Exactly (mapRows f l) (MapT f t)
map-exact f {l} {t} el u = record { sound = s ; complete = c }
  where
    ex = el u
    s : ∀ {q e} → (q , e) ∈ mapL (mapRow f) (rows l) → MapT f t q e
    s m with ∈-map⁻ (mapRow f) m
    ... | ((q , out a) , m′ , refl) = map-out (sound ex m′)
    ... | ((q , skip)  , m′ , refl) = map-skip (sound ex m′)
    ... | ((q , end)   , m′ , refl) = map-end (sound ex m′)
    c : ∀ {q e} → MapT f t q e → (q , e) ∈ mapL (mapRow f) (rows l)
    c (map-out x)  = ∈-map⁺ (mapRow f) (complete ex x)
    c (map-skip x) = ∈-map⁺ (mapRow f) (complete ex x)
    c (map-end x)  = ∈-map⁺ (mapRow f) (complete ex x)

defer-exact : ∀ {A} {s : Den A} {p} {b : Listed A} → Exactly b (enter s (p ++ [ ix 1 ]))
  → Exactly (((p ++ [ ix 0 ] , skip) ∷ rows b) ⊣ short b) (DeferT s p)
defer-exact eb u = record
  { sound    = λ { (here refl) → guard ; (there m) → Tb.body (sound (eb u) m) }
  ; complete = λ { guard → here refl ; (Tb.body x) → there (complete (eb u) x) } }

-- `EmissionSet.Truncate` keeps every row of a listing: a list puts
-- finitely many rows before any.
truncate-exact : ∀ {A} {l : Listed A} {t : EmissionSet A} → Exactly l t → Exactly l (Truncate t)
truncate-exact {l = l} el u = record
  { sound    = λ m → sound (el u) m , mapL proj₁ (rows l) , λ x _ → ∈-map⁺ proj₁ (complete (el u) x)
  ; complete = λ x → complete (el u) (proj₁ x) }

-- `EmissionSet.Proper`, the rows a hot shows.
proper-exact : ∀ {A} {l : Listed A} {t : EmissionSet A} → Exactly l t → Exactly (hotOf l) (Proper t)
proper-exact {A} {l} {t} el u = record { sound = s ; complete = c }
  where
    ex = el u
    s : ∀ {q e} → (q , e) ∈ proper (rows l) → Proper t q e
    s m with cm⁻ {xs = rows l} m
    ... | ((k , e′) , m′ , h) with when⁻ h
    ... | (pb , refl) = sound ex m′ , proper→ ex pb
    c : ∀ {q e} → Proper t q e → (q , e) ∈ proper (rows l)
    c (x , h) = cm⁺ (complete ex x) (when⁺ (→proper ex h))

-- `EmissionSet.Rejoin`, joining a hot at `p`.
private
  rj-row : ∀ {A} {t : EmissionSet A} p {k e q e′} → t k e → (q , e′) ∈ rejoinRow p (k , e) → Rejoin p t q e′
  rj-row p {k} {end} x h with if⁻ {b = p <ᵖ k} h
  ... | inj₁ (pk , m) with single⁻ m
  ... | refl = ended x (Equivalence.from T-≡ pk)
  rj-row p {k} {end} x h | inj₂ (pk , m) with single⁻ m
  ... | refl = late x (offT pk)
  rj-row p {k} {out a} x h with when⁻ h
  ... | (pk , refl) = Tb.shown x tt (Equivalence.from T-≡ pk)
  rj-row p {k} {skip} x h with when⁻ h
  ... | (pk , refl) = Tb.shown x tt (Equivalence.from T-≡ pk)

  rj-in : ∀ {A} {t : EmissionSet A} p {q e} → Rejoin p t q e → Σ (Row A) λ r → t (proj₁ r) (proj₂ r) × (q , e) ∈ rejoinRow p r
  rj-in p (Tb.shown {k} {out a} x _ pk) = (k , out a) , x , when⁺ (fromT pk)
  rj-in p (Tb.shown {k} {skip} x _ pk)  = (k , skip) , x , when⁺ (fromT pk)
  rj-in p (Tb.shown {k} {end} x () pk)
  rj-in p (ended {c} x pc) = (c , end) , x , if-t (fromT pc) (here refl)
  rj-in p (late {c} x cp)  = (c , end) , x , if-f (fromNot cp) (here refl)

rejoin-exact : ∀ {A} {l : Listed A} {t : EmissionSet A} → Exactly l t → ∀ p → Exactly (rejoin p l) (Rejoin p t)
rejoin-exact {l = l} {t} el p u = record { sound = s ; complete = c }
  where
    ex = el u
    s : ∀ {q e} → (q , e) ∈ concatMap (rejoinRow p) (rows l) → Rejoin p t q e
    s m with cm⁻ {xs = rows l} m
    ... | (r , rm , h) = rj-row p (sound ex rm) h
    c : ∀ {q e} → Rejoin p t q e → (q , e) ∈ concatMap (rejoinRow p) (rows l)
    c x with rj-in p x
    ... | ((k , e) , y , h) = cm⁺ (complete ex y) h

------------------------------------------------------------------------
-- Merge

module MergeX {A B : Set} (fD : A → Den B) (t : EmissionSet A) (o : Listed A) (ls : List (Pos × A × Listed B))
  (u : short (mergeRows o ls) ≡ false)
  (eo : Exactly o t)
  (ls-from : ∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (After (fD a) (q ++ [ ix 1 ])))
  (ls-to : ∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  where
  open Tb.Merge fD t
  open MergeL o ls using (done; laneRow)

  private
    exo : Exact o t
    exo = eo (proj₁ (∨-false {short o} u))

    uncut : ∀ {q a l} → (q , a , l) ∈ ls → short l ≡ false
    uncut m = any-off {xs = ls} (proj₂ (∨-false {short o} u)) m

    exl : ∀ {q a l} → (q , a , l) ∈ ls → Exact l (After (fD a) (q ++ [ ix 1 ]))
    exl m = proj₂ (ls-from m) (uncut m)

    out-of : ∀ {q a l} → (q , a , l) ∈ ls → t q (out a)
    out-of m = sound exo (values⁻ (proj₁ (ls-from m)))

    done→ : ∀ c → done c ≡ true → Done c
    done→ c e = endBy→ exo {c} (proj₁ (∧-true {endBy (rows o) c} e)) , λ x qc →
      let (l , m) = ls-to (values⁺ (complete exo x))
      in endBy→ (exl m) {c} (or-right (fromT qc) (all⁻ {xs = ls} (proj₂ (∧-true {endBy (rows o) c} e)) m))

    →done : ∀ c → Done c → done c ≡ true
    →done c ((c₀ , x , le) , lanes) = ∧-intro (→endBy exo {c₀} {c} x le) (all⁺ {xs = ls} λ { {q , a , l} m →
      or-of (q <ᵖ c) λ qc → let (c′ , y , le′) = lanes (out-of m) (Equivalence.from T-≡ qc) in →endBy (exl m) {c′} {c} y le′ })

    end-row : ∀ {c} → t c end → MergeT c (if done c then end else skip)
    end-row {c} x with done c in dc
    ... | true  = oend x (done→ c dc)
    ... | false = opass x (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    lend-row : ∀ {q a c} → t q (out a) → Lane q a c end → MergeT c (if done c then end else skip)
    lend-row {c = c} x y with done c in dc
    ... | true  = lend x y (done→ c dc)
    ... | false = lpass x y (λ D → offT dc (Equivalence.from T-≡ (→done c D)))

    outer-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ outerRow done r → MergeT q e
    outer-s {k , out a} rm h with single⁻ h
    ... | refl = val (sound exo rm)
    outer-s {k , skip} rm h with single⁻ h
    ... | refl = step (sound exo rm)
    outer-s {c , end} rm h with single⁻ h
    ... | refl = end-row (sound exo rm)

    lane-s : ∀ {q₀ a l r q e} → (q₀ , a , l) ∈ ls → r ∈ rows l → (q , e) ≡ laneRow r → MergeT q e
    lane-s {r = k , out b} m rm refl = lane (out-of m) (sound (exl m) rm) tt
    lane-s {r = k , skip}  m rm refl = lane (out-of m) (sound (exl m) rm) tt
    lane-s {r = c , end}   m rm refl = lend-row (out-of m) (sound (exl m) rm)

    outer-end : ∀ {c b} → done c ≡ b → (c , (if b then end else skip)) ∈ outerRow {A} {B} done (c , end)
    outer-end refl = here refl

    lane-end : ∀ {c b} {rs : List (Row B)} → done c ≡ b → (c , end) ∈ rs → (c , (if b then end else skip)) ∈ mapL laneRow rs
    lane-end refl r = ∈-map⁺ laneRow r

    lane-in : ∀ {k e} {rs : List (Row B)} → Tb.Work e → (k , e) ∈ rs → (k , e) ∈ mapL laneRow rs
    lane-in {e = out b} _ r = ∈-map⁺ laneRow r
    lane-in {e = skip}  _ r = ∈-map⁺ laneRow r
    lane-in {e = end}   () r

  sound-m : ∀ {q e} → (q , e) ∈ rows (mergeRows o ls) → MergeT q e
  sound-m m with ∈-++⁻ (concatMap (outerRow done) (rows o)) m
  ... | inj₁ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in outer-s rm h′
  ... | inj₂ h with cm⁻ {xs = ls} h
  ... | ((q₀ , a , l) , lm , h′) with ∈-map⁻ laneRow h′
  ... | (r , rm , eq) = lane-s lm rm eq

  complete-m : ∀ {q e} → MergeT q e → (q , e) ∈ rows (mergeRows o ls)
  complete-m (val x)      = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-m (step x)     = ∈-++⁺ˡ (cm⁺ (complete exo x) (here refl))
  complete-m (oend {c} x D)   = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (→done c D)))
  complete-m (opass {c} x nD) = ∈-++⁺ˡ (cm⁺ (complete exo x) (outer-end {c} (off (done→ c) nD)))
  complete-m (lane x y w) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (lane-in w (complete (exl m) y)))
  complete-m (lend {c = c} x y D) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (lane-end {c} (→done c D) (complete (exl m) y)))
  complete-m (lpass {c = c} x y nD) =
    let (l , m) = ls-to (values⁺ (complete exo x)) in
    ∈-++⁺ʳ (concatMap (outerRow done) (rows o)) (cm⁺ m (lane-end {c} (off (done→ c) nD) (complete (exl m) y)))

merge-exact : ∀ {A B} (fD : A → Den B) {t : EmissionSet A} (o : Listed A) (ls : List (Pos × A × Listed B)) → Exactly o t
  → (∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ values (rows o) × Exactly l (After (fD a) (q ++ [ ix 1 ])))
  → (∀ {q a} → (q , a) ∈ values (rows o) → Σ (Listed B) λ l → (q , a , l) ∈ ls)
  → Exactly (mergeRows o ls) (Tb.Merge.MergeT fD t)
merge-exact fD {t} o ls eo from to u = record { sound = sound-m ; complete = complete-m }
  where open MergeX fD t o ls u eo from to

------------------------------------------------------------------------
-- takeWhile

module TakeX {A : Set} (incl : Bool) (keep : A → Bool) (p : Pos) (t : EmissionSet A) (o : Listed A) (ex : Exact o t) where
  open Tb.TakeWhile incl keep t p
  open TakeL incl keep p o using (failed; takeRow)

  private
    false-of : ∀ {b} → T (not b) → b ≡ false
    false-of {false} _ = refl

    failed→ : ∀ k → failed k ≡ true → Failed k
    failed→ k e with any⁻ {xs = values (rows o)} e
    ... | ((q , a) , m , h) = let (nk , qk) = ∧-true h in
      q , a , sound ex (values⁻ m) , Equivalence.from T-≡ nk , Equivalence.from T-≡ qk

    →failed : ∀ k → Failed k → failed k ≡ true
    →failed k (q , a , x , nk , qk) = any⁺ (values⁺ (complete ex x)) (∧-intro (fromT nk) (fromT qk))

    unfailed : ∀ k → failed k ≡ false → ¬ Failed k
    unfailed k nf F = offT nf (Equivalence.from T-≡ (→failed k F))

    kept-row : ∀ {k e₀ q e} → t k e₀ → ¬ Failed k → (q , e) ∈ TakeL.kept incl keep p o (k , e₀) → TakeT q e
    kept-row {e₀ = out a} x nF h with if⁻ {b = keep a} h
    ... | inj₁ (ka , m) with single⁻ m
    ... | refl = pass x (Equivalence.from T-≡ ka) nF
    kept-row {e₀ = out a} x nF h | inj₂ (nk , m) with ∈-++⁻ (when incl _) m
    ... | inj₁ m′ with when⁻ {b = incl} m′
    ... | (inc , refl) = fail x (Equivalence.from T-≡ (T-not (offT nk))) nF (Equivalence.from T-≡ inc)
    kept-row {e₀ = out a} x nF h | inj₂ (nk , m) | inj₂ m′ with single⁻ m′
    ... | refl = stop x (Equivalence.from T-≡ (T-not (offT nk))) nF
    kept-row {e₀ = skip} x nF h with single⁻ h
    ... | refl = step x nF
    kept-row {e₀ = end} x nF h with single⁻ h
    ... | refl = tend x nF

  sound-t : ∀ {q e} → (q , e) ∈ rows (takeRows incl keep p o) → TakeT q e
  sound-t m with cm⁻ {xs = rows o} m
  ... | ((k , e₀) , km , h) with if⁻ {b = failed k} h
  ... | inj₁ (fk , h′) with when⁻ {b = inside p k} h′
  ... | (ins , refl) = left (sound ex km) (failed→ k fk) (Equivalence.from T-≡ ins)
  sound-t m | ((k , e₀) , km , h) | inj₂ (nf , h′) = kept-row (sound ex km) (unfailed k nf) h′

  complete-t : ∀ {q e} → TakeT q e → (q , e) ∈ rows (takeRows incl keep p o)
  complete-t (pass {q} x kp nF) =
    cm⁺ (complete ex x) (if-f (off (failed→ q) nF) (if-t (fromT kp) (here refl)))
  complete-t (fail {q} x nk nF inc) =
    cm⁺ (complete ex x) (if-f (off (failed→ q) nF) (if-f (false-of nk) (∈-++⁺ˡ (when⁺ (fromT inc)))))
  complete-t (stop {q} x nk nF) =
    cm⁺ (complete ex x) (if-f (off (failed→ q) nF) (if-f (false-of nk) (∈-++⁺ʳ (when incl _) (here refl))))
  complete-t (step {q} x nF) = cm⁺ (complete ex x) (if-f (off (failed→ q) nF) (here refl))
  complete-t (tend {q} x nF) = cm⁺ (complete ex x) (if-f (off (failed→ q) nF) (here refl))
  complete-t (left {q} x F ins) = cm⁺ (complete ex x) (if-t (→failed q F) (when⁺ (fromT ins)))

take-exact : ∀ {A} (i : Bool) (keep : A → Bool) (p : Pos) {t : EmissionSet A} (o : Listed A) → Exactly o t
  → Exactly (takeRows i keep p o) (Tb.TakeWhile.TakeT i keep t p)
take-exact i keep p {t} o eo u = record { sound = sound-t ; complete = complete-t }
  where open TakeX i keep p t o (eo u)

------------------------------------------------------------------------
-- Connect

module ConnX {A B : Set} (sD : Den A) (F : Den A → Den B) (p : Pos) (σl : Listed A) (βl : Listed B)
  (eσ : Exact σl (Tb.Connect.σ sD F p)) (eβ : Exact βl (Tb.Connect.β sD F p))
  where
  open Tb.Connect sD F p using (Alive; ConnT; body; shown; pinned)
  open ConnL (p ++ [ ix 1 ]) σl βl using (alive) renaming (shown to shownL)

  private
    alive→ : ∀ q → alive q ≡ true → Alive q
    alive→ q e x = Equivalence.from T-≡ (all⁻ e (complete eβ x))

    →alive : ∀ q → Alive q → alive q ≡ true
    →alive q h = all⁺ {xs = rows βl} λ { {c , end} m → fromT (h (sound eβ m)) ; {c , out _} m → refl ; {c , skip} m → refl }

    pinned-row : ∀ {k e₀ q e} → Tb.Connect.σ sD F p k e₀ → ¬ Alive k → (q , e) ∈ when (inside (p ++ [ ix 1 ]) k) (k , skip) → ConnT q e
    pinned-row x na h with when⁻ h
    ... | (ins , refl) = pinned x na (Equivalence.from T-≡ ins)

    shown-row : ∀ {k e₀ q e} → Tb.Connect.σ sD F p k e₀ → (q , e) ∈ shownL (k , e₀) → ConnT q e
    shown-row {k} x h with if⁻ {b = alive k} h
    ... | inj₁ (al , m) with single⁻ m
    ... | refl = shown x (alive→ k al)
    shown-row {k} x h | inj₂ (al , h′) = pinned-row x (λ A → offT al (Equivalence.from T-≡ (→alive k A))) h′

  sound-k : ∀ {q e} → (q , e) ∈ rows (connRows (p ++ [ ix 1 ]) σl βl) → ConnT q e
  sound-k m with ∈-++⁻ (rows βl) m
  ... | inj₁ h = body (sound eβ h)
  ... | inj₂ h = let ((k , e₀) , km , h′) = cm⁻ {xs = rows σl} h in shown-row (sound eσ km) h′

  complete-k : ∀ {q e} → ConnT q e → (q , e) ∈ rows (connRows (p ++ [ ix 1 ]) σl βl)
  complete-k (body x)         = ∈-++⁺ˡ (complete eβ x)
  complete-k (shown {k} x A)      = ∈-++⁺ʳ (rows βl) (cm⁺ (complete eσ x) (if-t (→alive k A) (here refl)))
  complete-k (pinned {k} x nA ins) = ∈-++⁺ʳ (rows βl) (cm⁺ (complete eσ x) (if-f (off (alive→ k) nA) (when⁺ (fromT ins))))

conn-exact : ∀ {A B} (sD : Den A) (F : Den A → Den B) (p : Pos) (σl : Listed A) (βl : Listed B)
  → Exactly σl (Tb.Connect.σ sD F p) → Exactly βl (Tb.Connect.β sD F p)
  → Exactly (connRows (p ++ [ ix 1 ]) σl βl) (Tb.Connect.ConnT sD F p)
conn-exact sD F p σl βl eσ eβ u = record { sound = sound-k ; complete = complete-k }
  where open ConnX sD F p σl βl (eσ (proj₁ (∨-false {short σl} u))) (eβ (proj₂ (∨-false {short σl} u)))

------------------------------------------------------------------------
-- A program tree

-- Each listed hot in scope, joined anywhere, is exactly its emission set joined.
data EnvRel : ∀ {Γ} → All Listed Γ → DenEnv Γ → Set₁ where
  []  : EnvRel [] []
  _∷_ : ∀ {A Γ} {l : Listed A} {d : Den A} {ρL : All Listed Γ} {ρD : DenEnv Γ}
      → (∀ p → Exactly (rejoin p l) (enter d p)) → EnvRel ρL ρD → EnvRel (l ∷ ρL) (d ∷ ρD)

env-lookup : ∀ {Γ A} {ρL : All Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD → (i : A ∈ Γ)
  → ∀ p → Exactly (rejoin p (lookup ρL i)) (enter (lookup ρD i) p)
env-lookup (r ∷ _) (here refl) = r
env-lookup (_ ∷ ρ) (there i)   = env-lookup ρ i

-- THE LISTING IS THE EMISSION SET: whatever `listT` lists uncut is exactly the
-- rows of `approxᵀ` at the same approximant.
listT-exact : ∀ {Γ A} n (o : Obs Timeline Γ A) {ρL : All Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD
  → ∀ p {l} → listT n o ρL p ≡ just l → Exactly l (enter (approxᵀ n o ρD) p)
listT-exact n (cold c)  ρ p refl = truncate-exact (walk-exact fuel _)
listT-exact n empty     ρ p refl = truncate-exact (end-exact _)
listT-exact n (of xs)   ρ p refl = truncate-exact (walk-exact fuel _)
listT-exact n (map f s) {ρL} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (l₀ , e₀ , refl) = truncate-exact (map-exact f (listT-exact n s ρ p e₀))
listT-exact n (scan f z s) {ρL} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (l₀ , e₀ , refl) = truncate-exact (scan-exact f z l₀ (listT-exact n s ρ p e₀))
listT-exact n (takeWhile i q s) {ρL} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (l₀ , e₀ , refl) = truncate-exact (take-exact i q p l₀ (listT-exact n s ρ p e₀))
listT-exact n (flatMap (mergeᶠ nothing) f s) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (o , eo , e₁) with bind⁻ {m = lanes (afterL (λ a → listT n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = truncate-exact (merge-exact (λ a → approxᵀ n (f a) ρD) o ls (listT-exact n s ρ p eo)
  (lanes-from {ln = afterL (λ a → listT n (f a) ρL)} {D = λ a → After (approxᵀ n (f a) ρD)} (afterL-exact {ln = λ a → listT n (f a) ρL} {D = λ a → enter (approxᵀ n (f a) ρD)} (λ {a} {s′} el → listT-exact n (f a) ρ s′ el)) els) (lanes-to {ln = afterL (λ a → listT n (f a) ρL)} els))
listT-exact n (flatMap (mergeᶠ (just k)) f s) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (o , eo , e₁) =
  truncate-exact (bounded-exact k (λ a → approxᵀ n (f a) ρD) _ (afterL (λ a → listT n (f a) ρL)) o (listT-exact n s ρ p eo)
    (afterL-exact {ln = λ a → listT n (f a) ρL} {D = λ a → enter (approxᵀ n (f a) ρD)} (λ {a} {s′} el → listT-exact n (f a) ρ s′ el)) e₁)
listT-exact n (flatMap switchᶠ f s) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (o , eo , e₁) with bind⁻ {m = lanes (afterL (λ a → listT n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = truncate-exact (switch-exact (λ a → approxᵀ n (f a) ρD) o ls (listT-exact n s ρ p eo)
  (lanes-from {ln = afterL (λ a → listT n (f a) ρL)} {D = λ a → After (approxᵀ n (f a) ρD)} (afterL-exact {ln = λ a → listT n (f a) ρL} {D = λ a → enter (approxᵀ n (f a) ρD)} (λ {a} {s′} el → listT-exact n (f a) ρ s′ el)) els) (lanes-to {ln = afterL (λ a → listT n (f a) ρL)} els))
listT-exact n (flatMap exhaustᶠ f s) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL p} e
... | (o , eo , e₁) with bind⁻ {m = lanes (afterL (λ a → listT n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = truncate-exact (exhaust-exact (λ a → approxᵀ n (f a) ρD) o ls (listT-exact n s ρ p eo)
  (lanes-from {ln = afterL (λ a → listT n (f a) ρL)} {D = λ a → After (approxᵀ n (f a) ρD)} (afterL-exact {ln = λ a → listT n (f a) ρL} {D = λ a → enter (approxᵀ n (f a) ρD)} (λ {a} {s′} el → listT-exact n (f a) ρ s′ el)) els) (lanes-to {ln = afterL (λ a → listT n (f a) ρL)} els))
listT-exact n (connect s b) {ρL} {ρD} ρ p e with bind⁻ {m = listT n s ρL (p ++ [ ix 1 ])} e
... | (σl , eσ , e₁) with bind⁻ {m = listT n b (hotOf σl ∷ ρL) (p ++ [ ix 0 ])} e₁
... | (βl , eβ , refl) =
  truncate-exact (conn-exact (approxᵀ n s ρD) (λ h → approxᵀ n b (h ∷ ρD)) p σl βl σx
    (listT-exact n b ((λ p′ → truncate-exact (rejoin-exact (proper-exact σx) p′)) ∷ ρ) (p ++ [ ix 0 ]) eβ))
  where
    σx = listT-exact n s ρ (p ++ [ ix 1 ]) eσ
listT-exact n (connected i) ρ p refl = env-lookup ρ i p
listT-exact zero    (defer l) ρ p refl = λ ()
listT-exact (suc n) (defer l) {ρL} ρ p e with bind⁻ {m = listT n (Later.force l) ρL (p ++ [ ix 1 ])} e
... | (b , eb , refl) = truncate-exact (defer-exact (listT-exact n (Later.force l) ρ (p ++ [ ix 1 ]) eb))

-- A closed program, as the oracle lists it.
tabled-exact : ∀ {A} n (o : Obs Timeline [] A) p {l} → listT n o [] p ≡ just l → Exactly l (enter (approxᵀ n o []) p)
tabled-exact n o p = listT-exact n o [] p
