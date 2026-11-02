{-# OPTIONS --guardedness #-}

-- THE RUN SIMULATED: each step dispatched over the cursor invariant.
module adequacy.Simulated where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Events using (root)
open import denotation.EmissionSet using (EmissionSet; enter; ⟦_⟧; out; end)
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Ctx; Conf; ⟨_,_,_,_⟩; rising; closed; load) renaming (Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (Vis; Past; Lowest; _≃_; _⇄_; silent; shown)
open import adequacy.Cursor using (Cur; ≈-refl; Inv; pending; origin; f-top; RT)
open import adequacy.Simulation using (Simulation)
open import adequacy.Path using (Path)
import adequacy.Path as P
open import adequacy.Dispatch using (module Over; τ-moved; val-moved; fin-moved; quiet-τ; quiet-val; quiet-fin; hush-val; hush-fin; hush-drained; mv-drained)

------------------------------------------------------------------------
-- THE CURSOR SIMULATES EVERY RUN: the carrier a cursor, the invariant at
-- it, read as what the root owes past it, and the run so far.

cursor : ∀ {R} (o : PureObs [] R) → Simulation o
cursor {R} o = record
  { I   = Car
  ; T   = λ i → RT Rt (proj₁ i)
  ; i₀  = origin , pending {Rg = λ _ → ⊤} (f-top ≈-refl) (λ _ → tt , (tt , λ ()) , tt , ≈-refl , λ _ → tt) , [] , P.[]
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
    tau {k} {t = t} (C , i , rs , pth) e = go (reach k)
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
    val {k} {k′} {t} {p} {a} (C , i , rs , pth) e = go (reach k)
      where
        go : Reach k → Σ (Car k′) λ i′ → Lowest (RT Rt C) p (out a) × Vis (Past p (RT Rt C)) ≃ Vis (RT Rt (proj₁ i′))
        go (driven h _) = ⊥-elim (hush-val h e)
        go (stills eq _) = ⊥-elim (quiet-val eq e)
        go (within mv sim) with val-moved (stepᴹ k) mv e
        ... | rest , tr , eq with sim eq i
        ...   | C′ , i′ , shown v l q = (C′ , i′ , _ , pth P.▸ P.val e P.[]) , (v , l) , q

    fin : ∀ {k p} (i : Car k) → Driver.step R k ≡ Driver.complete p → Lowest (RT Rt (proj₁ i)) p end
    fin {k} {p} (C , i , _ , pth) e = go (reach k)
      where
        go : Reach k → Lowest (RT Rt C) p end
        go (driven h _) = ⊥-elim (hush-fin h e)
        go (stills eq _) = ⊥-elim (quiet-fin eq e)
        go (within mv sim) with fin-moved (stepᴹ k) mv e
        ... | k′ , rest , tr , eq with sim eq i
        ...   | C′ , i′ , shown v l q = v , l

    dry : ∀ {k} (i : Car k) → Driver.step R k ≡ Driver.drained → ∀ {q e} → Vis (RT Rt (proj₁ i)) q e → ⊥
    dry {k} (C , i , _ , pth) e = go (reach k)
      where
        go : Reach k → ∀ {q e′} → Vis (RT Rt C) q e′ → ⊥
        go (driven h _)   = ⊥-elim (hush-drained h e)
        go (within mv _)  = ⊥-elim (mv-drained (stepᴹ k) mv e)
        go (stills _ sp) v = sp i (proj₁ v)
