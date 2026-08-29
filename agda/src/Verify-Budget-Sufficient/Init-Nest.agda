------------------------------------------------------------------
-- INIT-NEST: `nestOK?` holds at the initial state, at every instant.
--
-- Its own module for the reason `Init-Caps` has one: this is a lemma
-- family that consumes Nest-Store and Nest-Walk as finished facts, and
-- the spine module that spends it should not pay the grind's recheck.
--
-- THE FOUR PLACES of `storeNestMax`, at `st-init`:
--   (1) slotsNestSum slots  — a summand of the base cap itself
--   (2) the live fold       — the branch that was open
--   (3) the nodes fold      — refl, `nodes` is []
--   (4) regsNestMax registry — refl, the registry is []
--
-- PLACE (2) IS THE ONE THAT WAS OPEN, and `scripted`'s own index
-- closes it, exactly as it closes the width conjunct one module over:
-- the constructor carries `{ok : T (isData t)}`, every data type has
-- `nestDᵛ ≡ 0`, and a hot script's pendings are values at that type.
-- Cold and shared slots put no live source there at all.  So no
-- observable enters a run from outside the program -- which is the
-- reading `slotNest` already writes into its scripted clause, arriving
-- here as the fact rather than as the comment.
--
-- AND THE INSTANT IS FREE.  The cap only climbs, so the whole content
-- is at instant zero and every later one is a weakening: the
-- recurrence multiplies by a factor already proven at least one and
-- adds an increment, so `nestCap-mono` iterated is the entire lift.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Init-Nest where

open import Data.Bool    using (true; T)
open import Data.Nat     using (ℕ; zero; suc; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n)
open import Data.List    using (List; []; _∷_; foldr; _++_; concat; tabulate)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)

open import Rx.Prim  using (Tick; hot; cold)
open import Rx.Exp   using (Ty; Ctx; Closed; Val; isData)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵉ)
open import Rx.Evaluator
  using (Sched; mkHot; sched-init; st-init; resolve)

open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; storeNestMax; storeNestMax-lub; nestUnit;
         nestCapAt; nestCapAt-0; nestCap-mono; nestOK?; nestOK?-intro)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛ-data)

-- a data-typed script's pendings carry no nesting at all, which is
-- the whole of place (2) at one slot
pend-nest-data : ∀ {n} {Γ : Ctx n} (u : Ty) → T (isData u) →
  (ps : List (Tick × Val Γ u)) →
  foldr (λ tv acc → nestDᵛ u (proj₂ tv) ⊔ acc) 0 ps ≡ 0
pend-nest-data u ok []             = refl
pend-nest-data u ok ((tk , v) ∷ ps) =
  cong₂ _⊔_ (nestDᵛ-data u ok v) (pend-nest-data u ok ps)

mkHot-nest : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (i : Fin n) →
  foldr (λ l acc → liveNest l ⊔ acc) 0 (mkHot ins i) ≡ 0
mkHot-nest {Γ = Γ} ins i with ins i
... | scripted {ok = ok} (hot async) =
      cong (_⊔ 0) (pend-nest-data (lookup Γ i) ok (resolve 0 async))
... | scripted (cold _ _) = refl
... | shared _            = refl

-- a maximum is zero exactly when both sides are, and the split has to
-- name both arguments: `suc a ⊔ b` does not reduce until `b` is known
⊔≡0ˡ : ∀ a b → a ⊔ b ≡ 0 → a ≡ 0
⊔≡0ˡ zero    b       h = refl
⊔≡0ˡ (suc a) zero    ()
⊔≡0ˡ (suc a) (suc b) ()

⊔≡0ʳ : ∀ a b → a ⊔ b ≡ 0 → b ≡ 0
⊔≡0ʳ zero    b       h = h
⊔≡0ʳ (suc a) zero    ()
⊔≡0ʳ (suc a) (suc b) ()

-- the same append/tabulate walk `all-concat-tab` does one module over,
-- at a maximum rather than a conjunction
foldr⊔-++-0 : ∀ {A : Set} (f : A → ℕ) (xs ys : List A) →
  foldr (λ x acc → f x ⊔ acc) 0 xs ≡ 0 →
  foldr (λ x acc → f x ⊔ acc) 0 ys ≡ 0 →
  foldr (λ x acc → f x ⊔ acc) 0 (xs ++ ys) ≡ 0
foldr⊔-++-0 f []       ys hx hy = hy
foldr⊔-++-0 f (x ∷ xs) ys hx hy =
  cong₂ _⊔_ (⊔≡0ˡ (f x) _ hx) (foldr⊔-++-0 f xs ys (⊔≡0ʳ (f x) _ hx) hy)

foldr⊔-concat-tab-0 : ∀ {A : Set} (f : A → ℕ) {m} (g : Fin m → List A) →
  (∀ i → foldr (λ x acc → f x ⊔ acc) 0 (g i) ≡ 0) →
  foldr (λ x acc → f x ⊔ acc) 0 (concat (tabulate g)) ≡ 0
foldr⊔-concat-tab-0 f {zero}  g h = refl
foldr⊔-concat-tab-0 f {suc m} g h =
  foldr⊔-++-0 f (g Fin.zero) (concat (tabulate (λ i → g (Fin.suc i))))
    (h Fin.zero)
    (foldr⊔-concat-tab-0 f (λ i → g (Fin.suc i)) (λ i → h (Fin.suc i)))

init-liveNest : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (sched-init e ins)) ≡ 0
init-liveNest e ins = foldr⊔-concat-tab-0 liveNest (mkHot ins) (mkHot-nest ins)

-- the cap only climbs, so instant zero carries every instant
nestCapAt-0≤ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) → nestCapAt e sl 0 ≤ nestCapAt e sl id
nestCapAt-0≤ e sl zero    = ≤-refl
nestCapAt-0≤ e sl (suc id) =
  ≤-trans (nestCapAt-0≤ e sl id)
          (≤-trans (m≤m+n (nestCapAt e sl id) _) (nestCap-mono e sl id))

init-storeNest : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  storeNestMax (sched-init e ins) (st-init e) ≤ nestUnit e ins
init-storeNest e ins =
  storeNestMax-lub (sched-init e ins) (st-init e) (nestUnit e ins)
    (≤-trans (m≤n+m (slotsNestSum ins) (nestDᵉ e)) (n≤1+n _))
    (≤-trans (≤-reflexive (init-liveNest e ins)) z≤n)
    z≤n
    z≤n

init-nestOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (id : ℕ) → nestOK? e ins id (sched-init e ins) (st-init e) ≡ true
init-nestOK? e ins id =
  nestOK?-intro e ins id (sched-init e ins) (st-init e)
    (≤-trans (init-storeNest e ins)
             (≤-trans (≤-reflexive (sym (nestCapAt-0 e ins)))
                      (nestCapAt-0≤ e ins id)))
