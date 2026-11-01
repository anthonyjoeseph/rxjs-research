{-# OPTIONS --guardedness #-}

-- THE RUN SIMULATED: each step dispatched over the cursor invariant, told
-- by the run's tie what it reads before the cursor.
module adequacy.Told where

open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (root)
open import denotation.EmissionSet using (EmissionSet; enter; ⟦_⟧; out; end)
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Ctx; Conf; ⟨_,_,_,_⟩; rising; closed; load) renaming (Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (≃-refl; Vis; Past; Lowest; _≃_; _⇄_; silent; shown)
open import adequacy.Cursor using (Cur; Inv; settled; pending; flying; adrift; origin; f-top; RT)
open import adequacy.Simulation using (Simulation)
open import adequacy.Path using (Path)
import adequacy.Path as P
open import adequacy.Dispatch using (Told; module Over; τ-moved; val-moved; fin-moved; quiet-τ; quiet-val; quiet-fin; hush-val; hush-fin; hush-drained; mv-drained)
open import adequacy.Tie using (few-body; few-outer; few-lane)

-- A rise in flight is in a context still open.
rising-open : ∀ {R} {Rt : EmissionSet R} {C Γ A} {c : Ctx R Γ A} {s e p} → Inv Rt C ⟨ c , s , rising e , p ⟩ → closed c ≡ false
rising-open (settled () _ _)
rising-open (flying _ op _) = op
rising-open (adrift _ op)   = op

-- What the run tells a step from `k`, by its tie.
told : ∀ {R} {o : PureObs [] R} {Rt : EmissionSet R} {rs k C} → Path (load o) rs k → Inv Rt C k → Told k
told {o = o} pth i = record
  { atBody  = λ { refl lv → few-body o pth (rising-open i) lv }
  ; atOuter = λ { refl → few-outer o pth (rising-open i) }
  ; atLane  = λ { refl → few-lane o pth (rising-open i) }
  }

------------------------------------------------------------------------
-- THE CURSOR SIMULATES EVERY RUN: the carrier a cursor, the invariant at
-- it, read as what the root owes past it, and the run so far.

cursor : ∀ {R} (o : PureObs [] R) → Simulation o
cursor {R} o = record
  { I   = Car
  ; T   = λ i → RT Rt (proj₁ i)
  ; i₀  = origin , pending {Rg = λ _ → ⊤} (f-top ≃-refl) (λ _ → tt , (tt , λ ()) , tt , ≃-refl , λ _ → tt) , [] , P.[]
  ; t₀  = (λ { ((x , v , _) , v′) → x , v′ }) ⇄ (λ { (x , v) → (x , v , tt) , v })
  ; tau = tau
  ; val = val
  ; fin = fin
  ; dry = dry
  }
  where
    Rt : EmissionSet R
    Rt = enter (⟦ o ⟧ []ᴬ) root
    open Over Rt

    Car : Conf R → Set₁
    Car k = Σ Cur λ C → Inv Rt C k × Σ (Shownᴹ R) λ rs → Path (load o) rs k

    tau : ∀ {k k′ t} (i : Car k) → Driver.step R k ≡ Driver.silent t k′
        → Σ (Car k′) λ i′ → Vis (RT Rt (proj₁ i)) ≃ Vis (RT Rt (proj₁ i′))
    tau {k} {t = t} (C , i , rs , pth) e = go (reach k (told pth i))
      where
        go : Reach k → _
        go (driven h sim) with sim e i
        ... | C′ , i′ , silent q = (C′ , i′ , rs , pth P.▸τ (t , e)) , q
        go (within mv sim) with τ-moved (stepᴹ k) mv e
        ... | _ , eq with sim eq i
        ...   | C′ , i′ , silent q = (C′ , i′ , rs , pth P.▸τ (t , e)) , q
        go (stills eq _) = ⊥-elim (quiet-τ eq e)

    val : ∀ {k k′ t p a} (i : Car k) → Driver.step R k ≡ Driver.value t p a k′
        → Σ (Car k′) λ i′ → Lowest (RT Rt (proj₁ i)) p (out a) × Vis (Past p (RT Rt (proj₁ i))) ≃ Vis (RT Rt (proj₁ i′))
    val {k} {k′} {t} {p} {a} (C , i , rs , pth) e = go (reach k (told pth i))
      where
        go : Reach k → Σ (Car k′) λ i′ → Lowest (RT Rt C) p (out a) × Vis (Past p (RT Rt C)) ≃ Vis (RT Rt (proj₁ i′))
        go (driven h _) = ⊥-elim (hush-val h e)
        go (stills eq _) = ⊥-elim (quiet-val eq e)
        go (within mv sim) with val-moved (stepᴹ k) mv e
        ... | rest , tr , eq with sim eq i
        ...   | C′ , i′ , shown v l q = (C′ , i′ , _ , pth P.▸ P.val e P.[]) , (v , l) , q

    fin : ∀ {k p} (i : Car k) → Driver.step R k ≡ Driver.complete p → Lowest (RT Rt (proj₁ i)) p end
    fin {k} {p} (C , i , _ , pth) e = go (reach k (told pth i))
      where
        go : Reach k → Lowest (RT Rt C) p end
        go (driven h _) = ⊥-elim (hush-fin h e)
        go (stills eq _) = ⊥-elim (quiet-fin eq e)
        go (within mv sim) with fin-moved (stepᴹ k) mv e
        ... | k′ , rest , tr , eq with sim eq i
        ...   | C′ , i′ , shown v l q = v , l

    dry : ∀ {k} (i : Car k) → Driver.step R k ≡ Driver.drained → ∀ {q e} → Vis (RT Rt (proj₁ i)) q e → ⊥
    dry {k} (C , i , _ , pth) e = go (reach k (told pth i))
      where
        go : Reach k → ∀ {q e′} → Vis (RT Rt C) q e′ → ⊥
        go (driven h _)   = ⊥-elim (hush-drained h e)
        go (within mv _)  = ⊥-elim (mv-drained (stepᴹ k) mv e)
        go (stills _ sp) v = sp i (proj₁ v)
