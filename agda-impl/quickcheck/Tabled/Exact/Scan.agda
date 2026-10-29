{-# OPTIONS --guardedness #-}

-- SCAN, LISTED EXACTLY: the listing's level `i` holds the values
-- `Values.Nth` counts `i`th, each with the folds ending at it.  `AccV`
-- is `Scan.Acc` carrying that count and the value it ends at, so a
-- level is read against the level before alone.  Every value's count is
-- below the number of values, so the listing's levels reach it.
module quickcheck.Tabled.Exact.Scan where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n)
open import Data.Nat.Properties using (≤⇒≯; m≤n⇒m<n∨m≡n; +-suc; +-identityʳ; ≤-<-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (out; skip; end; EmissionSet)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled using (Listed; rows; concatMap; scanRows; module ScanL; module Order)
open import quickcheck.Tabled.Exact.Base
  using (Exact; Exactly; sound; complete; if⁻; if-t; single⁻; cm⁻; cm⁺; values⁺; cnt-in; module OrderX)

module ScanX {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) (o : Listed A) (ex : Exact o t) where
  open Tb.Scan f z t using (Acc; acc₀; acc; ScanT; sval; sstep; send)
  open Tb.Values t using (Next; Nth; first; next)
  open ScanL f z o using (vals; opening; step; levels; table; folds; others)
  open Order vals using (nextᵇ; nths)
  open OrderX ex using (next→; →next; nth-s; nth-c; nth-out; nth-cnt)

  -- A fold ending at the value `a` at `q`, the `i`th value.
  data AccV : ℕ → Pos → A → B → Set where
    v₀ : ∀ {q a} → t q (out a) → (∀ {k b} → t k (out b) → q Tb.≼ k) → AccV 0 q a (f z a)
    v  : ∀ {i q₀ a₀ b q a} → AccV i q₀ a₀ b → t q (out a) → q₀ Tb.≺ q → Next q₀ q → AccV (suc i) q a (f b a)

  accv-acc : ∀ {i q a b} → AccV i q a b → Acc q b
  accv-acc (v₀ x mn)      = acc₀ x mn
  accv-acc (v y x lt nx)  = acc (accv-acc y) x lt nx

  acc-accv : ∀ {q b} → Acc q b → Σ ℕ λ i → Σ A λ a → AccV i q a b
  acc-accv (acc₀ x mn) = 0 , _ , v₀ x mn
  acc-accv (acc y x lt nx) with acc-accv y
  ... | (i , _ , y′) = suc i , _ , v y′ x lt nx

  accv-nth : ∀ {i q a b} → AccV i q a b → Nth i q a
  accv-nth (v₀ x mn)     = first x mn
  accv-nth (v y x lt nx) = next (accv-nth y) x lt nx

  -- An entry lists exactly its value's folds; a level lists every value
  -- of its count.
  Ent : ℕ → Pos × A × List B → Set
  Ent i (q , a , bs) = (∀ {b} → b ∈ bs → AccV i q a b) × (∀ {b} → AccV i q a b → b ∈ bs)

  Lvl : ℕ → List (Pos × A × List B) → Set
  Lvl i cur = (∀ {e} → e ∈ cur → Ent i e) × (∀ {q a} → Nth i q a → Σ (List B) λ bs → (q , a , bs) ∈ cur)

  lv₀ : Lvl 0 (mapL opening (nths 0))
  lv₀ = snd , cmp
    where
    snd : ∀ {e} → e ∈ mapL opening (nths 0) → Ent 0 e
    snd m with ∈-map⁻ opening m
    ... | ((q , a) , nm , refl) with nth-s 0 nm
    ... | first x mn = (λ { (here refl) → v₀ x mn ; (there ()) }) , λ { (v₀ _ _) → here refl }

    cmp : ∀ {q a} → Nth 0 q a → Σ (List B) λ bs → (q , a , bs) ∈ mapL opening (nths 0)
    cmp N = _ , ∈-map⁺ opening (nth-c N)

  step-ok : ∀ {i cur q a} → Lvl i cur → (q , a) ∈ nths (suc i) → Ent (suc i) (step cur (q , a))
  step-ok {i} {cur} {q} {a} lv nm = snd , cmp
    where
    snd : ∀ {b} → b ∈ _ → AccV (suc i) q a b
    snd m with cm⁻ {xs = cur} m
    ... | ((q₀ , a₀ , bs₀) , em , h) with if⁻ {b = nextᵇ q₀ q} h
    ... | inj₂ (_ , ())
    ... | inj₁ (nx , h′) with ∈-map⁻ (λ b → f b a) h′
    ... | (b₀ , bm , refl) =
      v (proj₁ (proj₁ lv em) bm) (nth-out (nth-s (suc i) nm)) (proj₁ (next→ q₀ q nx)) (proj₂ (next→ q₀ q nx))

    cmp : ∀ {b} → AccV (suc i) q a b → b ∈ proj₂ (proj₂ (step cur (q , a)))
    cmp (v {q₀ = q₀} y x lt nx) with proj₂ lv (accv-nth y)
    ... | (bs₀ , em) = cm⁺ em (if-t (→next q₀ q lt nx) (∈-map⁺ (λ b → f b a) (proj₂ (proj₁ lv em) y)))

  lv-step : ∀ {i cur} → Lvl i cur → Lvl (suc i) (mapL (step cur) (nths (suc i)))
  lv-step {i} {cur} lv = snd , cmp
    where
    snd : ∀ {e} → e ∈ mapL (step cur) (nths (suc i)) → Ent (suc i) e
    snd m with ∈-map⁻ (step cur) m
    ... | ((q , a) , nm , refl) = step-ok lv nm

    cmp : ∀ {q a} → Nth (suc i) q a → Σ (List B) λ bs → (q , a , bs) ∈ mapL (step cur) (nths (suc i))
    cmp N = _ , ∈-map⁺ (step cur) (nth-c N)

  levels-ok : ∀ K i cur → Lvl i cur
    → (∀ {e} → e ∈ levels K (nths i) cur → Σ ℕ λ j → Ent j e)
    × (∀ {j q a} → i ≤ j → j < K + i → Nth j q a → Σ (List B) λ bs → (q , a , bs) ∈ levels K (nths i) cur × Ent j (q , a , bs))
  levels-ok zero    i cur lv = (λ ()) , λ le lt N → ⊥-elim (≤⇒≯ le lt)
  levels-ok (suc K) i cur lv = snd , cmp
    where
    ih = levels-ok K (suc i) (mapL (step cur) (nths (suc i))) (lv-step lv)

    snd : ∀ {e} → e ∈ levels (suc K) (nths i) cur → Σ ℕ λ j → Ent j e
    snd m with ∈-++⁻ cur m
    ... | inj₁ h = i , proj₁ lv h
    ... | inj₂ h = proj₁ ih h

    cmp : ∀ {j q a} → i ≤ j → j < suc K + i → Nth j q a
      → Σ (List B) λ bs → (q , a , bs) ∈ levels (suc K) (nths i) cur × Ent j (q , a , bs)
    cmp {j} le lt N with m≤n⇒m<n∨m≡n le
    ... | inj₂ refl = let (bs , m) = proj₂ lv N in bs , ∈-++⁺ˡ m , proj₁ lv m
    ... | inj₁ lt′ = let (bs , m , e) = proj₂ ih lt′ (subst (λ x → j < x) (sym (+-suc K i)) lt) N in
      bs , ∈-++⁺ʳ cur m , e

  private
    levT = levels-ok (length vals) 0 (mapL opening (nths 0)) lv₀

    other-s : ∀ {r q e} → r ∈ rows o → (q , e) ∈ others r → ScanT q e
    other-s {_ , out _} rm ()
    other-s {_ , skip}  rm h with single⁻ h
    ... | refl = sstep (sound ex rm)
    other-s {_ , end}   rm h with single⁻ h
    ... | refl = send (sound ex rm)

  sound-s : ∀ {q e} → (q , e) ∈ rows (scanRows f z o) → ScanT q e
  sound-s m with ∈-++⁻ (concatMap folds table) m
  ... | inj₂ h = let (r , rm , h′) = cm⁻ {xs = rows o} h in other-s rm h′
  ... | inj₁ h with cm⁻ {xs = table} h
  ... | ((q , a , bs) , em , h′) with ∈-map⁻ (λ b → q , out b) h′
  ... | (b , bm , refl) = sval (accv-acc (proj₁ (proj₂ (proj₁ levT em)) bm))

  complete-s : ∀ {q e} → ScanT q e → (q , e) ∈ rows (scanRows f z o)
  complete-s (sval {q} y) with acc-accv y
  ... | (j , a , y′) =
    let N = accv-nth y′
        bound = subst (λ x → j < x) (sym (+-identityʳ (length vals)))
          (≤-<-trans (nth-cnt N) (cnt-in (values⁺ (complete ex (nth-out N)))))
        (bs , m , e) = proj₂ levT z≤n bound N
    in ∈-++⁺ˡ (cm⁺ m (∈-map⁺ (λ b → q , out b) (proj₂ e y′)))
  complete-s (sstep x) = ∈-++⁺ʳ (concatMap folds table) (cm⁺ (complete ex x) (here refl))
  complete-s (send x)  = ∈-++⁺ʳ (concatMap folds table) (cm⁺ (complete ex x) (here refl))

scan-exact : ∀ {A B} (f : B → A → B) (z : B) {t : EmissionSet A} (o : Listed A) → Exactly o t
  → Exactly (scanRows f z o) (Tb.Scan.ScanT f z t)
scan-exact f z {t} o eo u = record { sound = sound-s ; complete = complete-s }
  where open ScanX f z t o (eo u)
