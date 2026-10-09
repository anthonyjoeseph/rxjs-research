-- WHAT `elemᵛ` MAKES OF ONE OUTER EMIT, read off the evaluator: the
-- echo leaves under the emit's own instant carrying the echoed value of
-- its one payload if it has one, and the payload's lane passes as it
-- came.  The evaluator is stuck only on the emit's event list, so every
-- fact here is about a fold over one: the split keeps the payloads in
-- order and leaves none in its bookkeeping, and the reassembly puts out
-- exactly the values it is handed.
module Simulation.Elem where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; reverse; reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Rx.Exp using (Ctx; Ty; Val; Env; Tm; _∷ᵉ_; evalWith; foldVals; applyClo; renTm; ext∈;
                          unitᵗ; uniqᵗ; listᵗ; obs; _×ᵗ_; _+ᵗ_; varᵗ; fstᵗ; consᵗ)
open import SExp.InstEmit using (instEventᵗ; splitAccᵗ; splitStepᵛ; splitEventsᵛ; valueᵛ)
open import SExp.InstEmit.Decode using (decodeEmit)
open import SExp.Syntax using (emitᵗ; plainᵗ)
open import SExp.Elaborate using (elemᵛ; elemBodyᵛ)
open import Batchable.Inst-Extract using (emitValues)

-- a pointwise relation over a mapped list, against one value or none
pw-one : ∀ {A B C : Set} {R : B → C → Set} {f : A → B} xs {w}
       → Pointwise R (map f xs) (w ∷ []) → Σ A λ p → xs ≡ p ∷ [] × R (f p) w
pw-one (p ∷ [])    (r ∷ [])  = p , refl , r
pw-one []          ()
pw-one (_ ∷ _ ∷ _) (_ ∷ ())

pw-none : ∀ {A B C : Set} {R : B → C → Set} {f : A → B} xs
        → Pointwise R (map f xs) [] → xs ≡ []
pw-none [] [] = refl

module _ {n} {Γ : Ctx n} where

  -- the payloads a run of events carries, in order
  paysOf : ∀ {a} → List (Val Γ (instEventᵗ uniqᵗ a)) → List (Val Γ a)
  paysOf []                   = []
  paysOf (inj₂ (inj₁ v) ∷ es) = v ∷ paysOf es
  paysOf (inj₁ _ ∷ es)        = paysOf es
  paysOf (inj₂ (inj₂ _) ∷ es) = paysOf es

  -- an emit's values are its payloads under its instant
  values-decode : ∀ {a} evs i s k
                → emitValues (decodeEmit {Γ = Γ} {a = a} (evs , i , s , k)) ≡ map (i ,_) (paysOf evs)
  values-decode []                                  i s k = refl
  values-decode (inj₁ _ ∷ evs)                      i s k = values-decode evs i s k
  values-decode (inj₂ (inj₁ v) ∷ evs)               i s k = cong ((i , v) ∷_) (values-decode evs i s k)
  values-decode (inj₂ (inj₂ (inj₁ _)) ∷ evs)        i s k = values-decode evs i s k
  values-decode (inj₂ (inj₂ (inj₂ (inj₁ _))) ∷ evs) i s k = values-decode evs i s k
  values-decode (inj₂ (inj₂ (inj₂ (inj₂ _))) ∷ evs) i s k = values-decode evs i s k

  paysOf-rev : ∀ {a} (acc xs : List (Val Γ (instEventᵗ uniqᵗ a)))
             → paysOf {a = a} (reverseAcc acc xs) ≡ reverseAcc (paysOf {a = a} acc) (paysOf {a = a} xs)
  paysOf-rev acc []                   = refl
  paysOf-rev acc (inj₁ x ∷ xs)        = paysOf-rev (inj₁ x ∷ acc) xs
  paysOf-rev acc (inj₂ (inj₁ v) ∷ xs) = paysOf-rev (inj₂ (inj₁ v) ∷ acc) xs
  paysOf-rev acc (inj₂ (inj₂ c) ∷ xs) = paysOf-rev (inj₂ (inj₂ c) ∷ acc) xs

  -- the step `revᵗ` and `appendᵗ` fold, and the one the reassembly
  -- wraps each value with
  revStep : ∀ {Θ s} → Tm Γ [] [] (s ∷ listᵗ s ∷ Θ) (listᵗ s)
  revStep = consᵗ (varᵗ (here refl)) (varᵗ (there (here refl)))

  valStep : ∀ {Θ b} → Tm Γ [] [] (b ∷ listᵗ (instEventᵗ uniqᵗ b) ∷ Θ) (listᵗ (instEventᵗ uniqᵗ b))
  valStep = consᵗ (valueᵛ (varᵗ (here refl))) (varᵗ (there (here refl)))

  fold-rev : ∀ {Θ s} (env : Env Γ Θ) (xs acc : List (Val Γ s))
           → foldVals (revStep {s = s}) env xs acc ≡ reverseAcc acc xs
  fold-rev env []       acc = refl
  fold-rev env (x ∷ xs) acc = fold-rev env xs (x ∷ acc)

  fold-value : ∀ {Θ b} (env : Env Γ Θ) (xs : List (Val Γ b)) acc
             → paysOf {a = b} (foldVals {u = listᵗ (instEventᵗ uniqᵗ b)} (valStep {b = b}) env xs acc) ≡ reverseAcc (paysOf {a = b} acc) xs
  fold-value env []       acc = refl
  fold-value env (x ∷ xs) acc = fold-value env xs (inj₂ (inj₁ x) ∷ acc)

  -- the split, folding: the payloads onto the reversed ones, everything
  -- else onto the bookkeeping, which gains none
  fold-split : ∀ {Θ a b} (env : Env Γ Θ) (evs : List (Val Γ (instEventᵗ uniqᵗ a))) bk ps f
             → proj₁ (proj₂ (foldVals (splitStepᵛ {u = uniqᵗ} {a = a} {b = b}) env evs (bk , ps , f)))
                 ≡ reverseAcc ps (paysOf {a = a} evs)
             × paysOf {a = b} (proj₁ (foldVals (splitStepᵛ {u = uniqᵗ} {a = a} {b = b}) env evs (bk , ps , f)))
                 ≡ paysOf {a = b} bk
  fold-split env []                                  bk ps f = refl , refl
  fold-split env (inj₁ x ∷ evs)                      bk ps f = fold-split env evs (inj₁ x ∷ bk) ps f
  fold-split env (inj₂ (inj₁ v) ∷ evs)               bk ps f = fold-split env evs bk (v ∷ ps) f
  fold-split env (inj₂ (inj₂ (inj₁ c)) ∷ evs)        bk ps f = fold-split env evs (inj₂ (inj₂ (inj₁ c)) ∷ bk) ps f
  fold-split env (inj₂ (inj₂ (inj₂ (inj₁ h))) ∷ evs) bk ps f = fold-split env evs (inj₂ (inj₂ (inj₂ (inj₁ h))) ∷ bk) ps f
  fold-split env (inj₂ (inj₂ (inj₂ (inj₂ _))) ∷ evs) bk ps f = fold-split env evs bk ps true

  split-eval : ∀ {Θ a b} (t : Tm Γ [] [] Θ (listᵗ (instEventᵗ uniqᵗ a))) (env : Env Γ Θ)
             → proj₁ (proj₂ (evalWith (splitEventsᵛ {b = b} t) env)) ≡ paysOf {a = a} (evalWith t env)
             × paysOf {a = b} (proj₁ (evalWith (splitEventsᵛ {b = b} t) env)) ≡ []
  split-eval {a = a} {b = b} t env =
    trans (fold-rev {s = a} _ (proj₁ (proj₂ R)) []) (trans (cong reverse (proj₁ fs)) (reverse-involutive (paysOf {a = a} (evalWith t env))))
    , trans (cong (paysOf {a = b}) (fold-rev {s = instEventᵗ uniqᵗ b} _ (proj₁ R) []))
            (trans (paysOf-rev {a = b} [] (proj₁ R)) (cong (reverseAcc []) (proj₂ fs)))
    where
    R  = foldVals (splitStepᵛ {u = uniqᵗ} {a = a} {b = b}) env (evalWith t env) ([] , [] , false)
    fs = fold-split {a = a} {b = b} env (evalWith t env) [] [] false

  -- an append of the first list's events onto the second's
  app-pays : ∀ {Θ a} (env : Env Γ Θ) (xs ys : List (Val Γ (instEventᵗ uniqᵗ a)))
           → paysOf {a = a} (foldVals (revStep {s = instEventᵗ uniqᵗ a}) env (foldVals (revStep {s = instEventᵗ uniqᵗ a}) env xs []) ys)
               ≡ reverseAcc (paysOf {a = a} ys) (reverse (paysOf {a = a} xs))
  app-pays {a = a} env xs ys =
    trans (cong (paysOf {a = a}) (trans (fold-rev {s = instEventᵗ uniqᵗ a} env (foldVals (revStep {s = instEventᵗ uniqᵗ a}) env xs []) ys) (cong (reverseAcc ys) (fold-rev {s = instEventᵗ uniqᵗ a} env xs []))))
          (trans (paysOf-rev {a = a} ys (reverse xs)) (cong (reverseAcc (paysOf {a = a} ys)) (paysOf-rev {a = a} [] xs)))

  end-quiet : ∀ {b} (f : Bool)
            → paysOf {a = b} (if f then inj₂ (inj₂ (inj₂ (inj₂ tt))) ∷ [] else []) ≡ []
  end-quiet true  = refl
  end-quiet false = refl

  -- the reassembly over bookkeeping carrying no payload puts out the
  -- values it is handed, whether or not it completes
  re-pays : ∀ {Θ b} (env : Env Γ Θ) (bk : List (Val Γ (instEventᵗ uniqᵗ b))) (vs : List (Val Γ b)) (fin : Bool)
          → paysOf {a = b} bk ≡ []
          → paysOf {a = b} (foldVals (revStep {s = instEventᵗ uniqᵗ b}) env (foldVals (revStep {s = instEventᵗ uniqᵗ b}) env bk [])
                     (foldVals (revStep {s = instEventᵗ uniqᵗ b}) env
                        (foldVals (revStep {s = instEventᵗ uniqᵗ b}) env
                           (foldVals {u = listᵗ (instEventᵗ uniqᵗ b)} (valStep {b = b}) env (foldVals (revStep {s = b}) env vs []) []) [])
                        (if fin then inj₂ (inj₂ (inj₂ (inj₂ tt))) ∷ [] else [])))
            ≡ vs
  re-pays {b = b} env bk vs fin nb =
    trans (app-pays {a = b} env bk rest)
    (trans (cong (λ z → reverseAcc (paysOf {a = b} rest) (reverse z)) nb)
    (trans (app-pays {a = b} env pv end)
    (trans (cong (λ z → reverseAcc z (reverse (paysOf {a = b} pv))) (end-quiet {b = b} fin))
    (trans (reverse-involutive (paysOf {a = b} pv))
    (trans (fold-value {b = b} env (foldVals (revStep {s = b}) env vs []) [])
    (trans (cong reverse (fold-rev {s = b} env vs []))
           (reverse-involutive vs)))))))
    where
    pv : List (Val Γ (instEventᵗ uniqᵗ b))
    pv = foldVals {u = listᵗ (instEventᵗ uniqᵗ b)} (valStep {b = b}) env (foldVals (revStep {s = b}) env vs []) []

    end : List (Val Γ (instEventᵗ uniqᵗ b))
    end = if fin then inj₂ (inj₂ (inj₂ (inj₂ tt))) ∷ [] else []

    rest : List (Val Γ (instEventᵗ uniqᵗ b))
    rest = foldVals (revStep {s = instEventᵗ uniqᵗ b}) env (foldVals (revStep {s = instEventᵗ uniqᵗ b}) env pv []) end

  -- an element's echo: its value, if it has one
  echoList : ∀ {u} → Val Γ (unitᵗ +ᵗ u) → List (Val Γ u)
  echoList (inj₁ _) = []
  echoList (inj₂ v) = v ∷ []

  module _ {t : Ty} {Θ} (ρ : Env Γ Θ) (e′ : Val Γ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)))) where

    P : Ty
    P = plainᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))

    private
      R : Ty
      R = (unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t))

      SP : Ty
      SP = splitAccᵗ uniqᵗ P (plainᵗ t)

      env₀ : Env Γ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)) ∷ Θ)
      env₀ = e′ ∷ᵉ ρ

      -- `elemᵛ`'s body over a split
      Body : Val Γ SP → Val Γ R
      Body sp = evalWith (renTm (λ x → x) (λ x → x) (ext∈ (there {x = R})) (elemBodyᵛ {t = t}))
                         (_∷ᵉ_ {s = SP} sp (_∷ᵉ_ {s = R} (inj₁ tt , inj₁ tt) env₀))

      -- the emit the echo leaves on, once the body has put it out
      echoOut : Val Γ R → Val Γ (emitᵗ t)
      echoOut (inj₂ x , _) = x
      echoOut (inj₁ _ , _) = [] , 0 , 0 , inj₁ tt

      decoded : ∀ (x : Val Γ (emitᵗ t))
              → emitValues (decodeEmit x) ≡ map (proj₁ (proj₂ x) ,_) (paysOf {a = plainᵗ t} (proj₁ x))
      decoded x = values-decode {a = plainᵗ t} (proj₁ x) (proj₁ (proj₂ x)) (proj₁ (proj₂ (proj₂ x))) (proj₂ (proj₂ (proj₂ x)))

      body-one : ∀ bk ps f ech ln → ps ≡ (ech , ln) ∷ [] → paysOf {a = plainᵗ t} bk ≡ []
               → Σ (Val Γ (emitᵗ t)) λ x → Body (bk , ps , f) ≡ (inj₂ x , ln)
                 × emitValues (decodeEmit x) ≡ map (proj₁ (proj₂ e′) ,_) (echoList ech)
      body-one bk _ f ech@(inj₁ _) ln@(inj₁ _) refl nb =
        echoOut (Body (bk , (ech , ln) ∷ [] , f)) , refl
        , trans (decoded (echoOut (Body (bk , (ech , ln) ∷ [] , f)))) (cong (map (proj₁ (proj₂ e′) ,_)) (re-pays {b = plainᵗ t} _ bk [] f nb))
      body-one bk _ f ech@(inj₁ _) ln@(inj₂ _) refl nb =
        echoOut (Body (bk , (ech , ln) ∷ [] , f)) , refl
        , trans (decoded (echoOut (Body (bk , (ech , ln) ∷ [] , f)))) (cong (map (proj₁ (proj₂ e′) ,_)) (re-pays {b = plainᵗ t} _ bk [] f nb))
      body-one bk _ f ech@(inj₂ v) ln@(inj₁ _) refl nb =
        echoOut (Body (bk , (ech , ln) ∷ [] , f)) , refl
        , trans (decoded (echoOut (Body (bk , (ech , ln) ∷ [] , f)))) (cong (map (proj₁ (proj₂ e′) ,_)) (re-pays {b = plainᵗ t} _ bk (v ∷ []) f nb))
      body-one bk _ f ech@(inj₂ v) ln@(inj₂ _) refl nb =
        echoOut (Body (bk , (ech , ln) ∷ [] , f)) , refl
        , trans (decoded (echoOut (Body (bk , (ech , ln) ∷ [] , f)))) (cong (map (proj₁ (proj₂ e′) ,_)) (re-pays {b = plainᵗ t} _ bk (v ∷ []) f nb))

      body-none : ∀ bk ps f → ps ≡ [] → paysOf {a = plainᵗ t} bk ≡ []
                → Σ (Val Γ (emitᵗ t)) λ x → Body (bk , ps , f) ≡ (inj₂ x , inj₁ tt) × emitValues (decodeEmit x) ≡ []
      body-none bk _ f refl nb =
        echoOut (Body (bk , [] , f)) , refl , trans (decoded (echoOut (Body (bk , [] , f)))) (cong (map (proj₁ (proj₂ e′) ,_)) (re-pays {b = plainᵗ t} _ bk [] f nb))

      S : Val Γ SP
      S = evalWith (splitEventsᵛ {b = plainᵗ t} (fstᵗ (varᵗ (here refl)))) env₀

      sv = split-eval {a = P} {b = plainᵗ t} (fstᵗ (varᵗ (here refl))) env₀

    -- an emit carrying one payload: its echo, and its lane as it came
    elem-run : ∀ ech ln → paysOf {a = P} (proj₁ e′) ≡ (ech , ln) ∷ []
             → Σ (Val Γ (emitᵗ t)) λ x → applyClo (Θ , elemᵛ {t = t} , ρ) e′ ≡ (inj₂ x , ln)
               × emitValues (decodeEmit x) ≡ map (proj₁ (proj₂ e′) ,_) (echoList ech)
    elem-run ech ln eq =
      body-one (proj₁ S) (proj₁ (proj₂ S)) (proj₂ (proj₂ S)) ech ln (trans (proj₁ sv) eq) (proj₂ sv)

    -- and one carrying none: an echo carrying nothing, and no lane
    quiet-run : paysOf {a = P} (proj₁ e′) ≡ []
              → Σ (Val Γ (emitᵗ t)) λ x → applyClo (Θ , elemᵛ {t = t} , ρ) e′ ≡ (inj₂ x , inj₁ tt)
                × emitValues (decodeEmit x) ≡ []
    quiet-run eq = body-none (proj₁ S) (proj₁ (proj₂ S)) (proj₂ (proj₂ S)) (trans (proj₁ sv) eq) (proj₂ sv)
