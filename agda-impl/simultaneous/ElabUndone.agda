{-# OPTIONS --guardedness #-}

-- AN ELABORATED PROGRAM ENDS NO LANE: none of its rows shows a
-- `laneDone`, wherever none of the hots it reads does (`elab-undone`).
-- A lane's frame sends one, and only the flatMap's scan reads it, which
-- sends values and routes alone (`react-sends`); every other former
-- passes on what it reads, or sends routes.
module simultaneous.ElabUndone where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
import Data.List as L
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (does)

open import Tree using (Obs; Later; merge; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; ix)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (out; Den; hot; Proper; DenEnv; enter; approx; DeferT; module Op; module TakeWhile)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; carry;
  laneDone; burstEnd; outerDone; subscribed; completed; valuesOf)
open import simultaneous.SObs using (lone; ext; Tag; val; cdone; tick; flat; module Elaborate)
open import simultaneous.Sim using (EnvSim; HotSim)
open import simultaneous.FlatRows using (conn-out; merge-out; hot-out; map-out′; scan-out; of-mem; each-one; react-sends; module Cat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; E; AIE; Routes; elab; elabˡ; annotate; undone; joins;
  joinStep; annStep; render; phase; passes; mapIE; scanIE; combined; react; concatˢ; marked;
  closer; laneˢ; each; trackers; Out; Input; going; fed)

------------------------------------------------------------------------
-- What ends no lane

-- No row of `d` ends a lane.
Undone : ∀ {X} → Den (IE X) → Set
Undone d = ∀ p {k y} → enter d p k (out y) → T (undone y)

-- No annotated row of `d` ends a lane.
AUndone : ∀ {X} → Den (AIE X) → Set
AUndone d = ∀ p {k r y} → enter d p k (out (r , just y)) → T (undone y)

-- No hot a program reads ends a lane.
EnvU : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Δ → Set₁
EnvU {Γ} ρ env = ∀ {X} (i : X ∈ Γ) → AUndone (lookup env (ρ (∈-map⁺ AIE i)))

env-ext : ∀ {Γ Δ A} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {h : Den (AIE A)}
        → AUndone h → EnvU ρ env → EnvU {A ∷ Γ} (ext ρ) (h ∷ᴬ env)
env-ext uh eu (here refl) = uh
env-ext uh eu (there i)   = eu i

-- A simulated hot ends no lane.
env-u : ∀ {Γ Δ Amb} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env} {env′ : DenEnv Δ} → EnvSim ρ Amb env env′ → EnvU ρ env′
env-u es i = subst AUndone (sym (HotSim.isE (es i))) λ p r → let (_ , x , _) = hot-out r in HotSim.undone′ (es i) x

------------------------------------------------------------------------
-- Lists sent

rep-u : ∀ {X} k n {y} → y ∈ replicate k (instEmit {A = X} (mark begin) n) → T (undone y)
rep-u (suc k) n (here refl) = tt
rep-u (suc k) n (there i)   = rep-u k n i

joins-u : ∀ {X} (r : Routes) (e : IE X) {y} → y ∈ joins r e → T (undone y)
joins-u (m , k) (instEmit (value _) _) i = rep-u k m i
joins-u (m , k) (instEmit (mark begin) n) i with does (n ≟ᵖ m)
... | true  = rep-u k m i
joins-u (m , k) (instEmit (mark begin) n) () | false
joins-u (m , k) (instEmit (mark over) _)       i = rep-u k m i
joins-u (m , k) (instEmit (mark stop) _)       i = rep-u k m i
joins-u (m , k) (instEmit (mark outerOpen) _)  i = rep-u k m i
joins-u (m , k) (instEmit (mark outerClose) _) i = rep-u k m i
joins-u (m , k) (instEmit (mark laneStart) _)  i = rep-u k m i
joins-u (m , k) (instEmit (mark carry) _)      i = rep-u k m i
joins-u (m , k) (instEmit (mark laneDone) _)   i = rep-u k m i
joins-u (m , k) (instEmit (mark burstEnd) _)   i = rep-u k m i
joins-u (m , k) (instEmit (mark outerDone) _)  i = rep-u k m i
joins-u (m , k) (instEmit (mark subscribed) _) i = rep-u k m i
joins-u (m , k) (instEmit (mark completed) _)  i = rep-u k m i

-- A reader's step sends routes, or the emit it met.
join-u : ∀ {X} (β : Bool × List (IE X)) (a : AIE X) {y} → y ∈ proj₂ (joinStep β a) → T (undone y) ⊎ proj₂ a ≡ just y
join-u (true , _) (r , just e) i with ∈-++⁻ (joins r e) i
... | inj₁ j         = inj₁ (joins-u r e j)
... | inj₂ (here refl) = inj₂ refl
... | inj₂ (there ())
join-u (true , _)  ((m , k) , nothing) i  = inj₁ (rep-u k m i)
join-u (false , _) (r , just e) (here refl) = inj₂ refl
join-u (false , _) (r , just e) (there ())
join-u (false , _) (r , nothing) ()

-- A mark ends no lane at any type, or at every one.
mark-u : ∀ {A B} m n → T (undone {A} (instEmit (mark m) n)) → T (undone {B} (instEmit (mark m) n))
mark-u begin      _ u = u
mark-u over       _ u = u
mark-u stop       _ u = u
mark-u outerOpen  _ u = u
mark-u outerClose _ u = u
mark-u laneStart  _ u = u
mark-u carry      _ u = u
mark-u laneDone   _ ()
mark-u burstEnd   _ u = u
mark-u outerDone  _ u = u
mark-u subscribed _ u = u
mark-u completed  _ u = u

mapIE-u : ∀ {A B} (f : A → B) (x : IE A) → T (undone x) → T (undone (mapIE f x))
mapIE-u f (instEmit (value _) _) u = tt
mapIE-u f (instEmit (mark m) n)  u = mark-u m n u

scanIE-u : ∀ {A B} (f : B → A → B) (st : B × IE B) (x : IE A) → T (undone x) → T (undone (proj₂ (scanIE f st x)))
scanIE-u f st (instEmit (value _) _) u = tt
scanIE-u f st (instEmit (mark m) n)  u = mark-u m n u

-- An annotated step shows the emit it met.
ann-step : ∀ {A} (st : Routes × AIE A) (a : Maybe (IE A)) {r y} → (r , just y) ≡ proj₂ (annStep st a) → a ≡ just y
ann-step st (just e) refl = refl
ann-step st nothing ()

------------------------------------------------------------------------
-- One layer

-- A connect shows its body's rows, the source made hot.
connE-u : ∀ {A B} (s : Den A) (F : Den A → Den (IE B)) → (∀ q → Undone (F (hot (Proper (enter s q))))) → Undone (Op.connect s F)
connE-u s F h p r = h (p ⊕ (ix 1 ∷ [])) (p ⊕ (ix 0 ∷ [])) (conn-out s F p r)

connE : ∀ n {Δ A B} (s : E Δ A) (b : E (A ∷ Δ) (IE B)) (env : DenEnv Δ)
      → (∀ q → Undone (approx n b (hot (Proper (enter (approx n s env) q)) ∷ᴬ env))) → Undone (approx n (connect s b) env)
connE n s b env = connE-u (approx n s env) (λ h → approx n b (h ∷ᴬ env))

module _ {A : Set} (i : Bool) (keep : A → Bool) (d : Den A) (p : Pos) where
  private module Tk = TakeWhile i keep (enter d p)

  -- A takeWhile's value is its source's.
  take-row : ∀ {k y} → enter (Op.takeWhile i keep d) p k (out y) → Σ Pos λ q → enter d p q (out y)
  take-row (Tk.pass t _ _ , _)   = _ , t
  take-row (Tk.fail t _ _ _ , _) = _ , t

-- A cold's steps send values and routes.
render-u : ∀ n {Δ A} (x : Bool × Tag A) (env : DenEnv Δ) → Undone (approx n (render x) env)
render-u n (false , val a) env p (r , _) with of-mem p 0 _ r
... | here refl = tt
... | there ()
render-u n (true , val a) env p r
  with merge-out (λ m → Op.of (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ [])) (approx n (cold (fresh (λ p → p))) env) p r
... | q , m , _ , (l , _) , _ with of-mem (q ⊕ (ix 1 ∷ [])) 0 (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ []) l
...   | here refl                 = tt
...   | there (here refl)         = tt
...   | there (there (here refl)) = tt
...   | there (there (there ()))
render-u n (true , cdone) env p r with map-out′ (λ m → instEmit (mark begin) m) (approx n (cold (fresh (λ p → p))) env) p r
... | _ , _ , refl = tt
render-u n (false , cdone) env p (() , _)
render-u n (false , tick)  env p (() , _)
render-u n (true , tick)   env p (() , _)

-- The flatMap's scan sends values and routes, whatever it reads.
react-u : ∀ n {Δ B} op (z : Out B) (d : E Δ (Maybe (Input B))) (env : DenEnv Δ) → Undone (approx n (each proj₂ (scan (react op) z d)) env)
react-u n op z d env p r with each-one proj₂ (Op.scan (react op) z (approx n d env)) p r
... | _ , x , dx , yi , _ with scan-out (react op) z (approx n d env) p dx
...   | st , inp , _ , eq = react-sends op st inp (subst (λ w → _ ∈ proj₂ w) eq yi)

comb-u : ∀ n {Δ A B} op (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) → Undone (approx n (combined op tk) env)
comb-u n op tk env =
  subst (λ o → Undone (approx n o env)) {x = each proj₂ (scan (react op) z₁ d₁)} {y = combined op tk} refl (react-u n op z₁ d₁ env)
  where
    z₁ = (flat root 0 0 false false false false 0 0 0 0 0 [] , [])
    d₁ = takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))

-- Four connects show their innermost body's rows.
conn⁴ : ∀ n {Δ X₁ X₂ X₃ X₄ B} (o : E Δ (IE B)) (s₁ : E Δ X₁) (s₂ : E (X₁ ∷ Δ) X₂) (s₃ : E (X₂ ∷ X₁ ∷ Δ) X₃) (s₄ : E (X₃ ∷ X₂ ∷ X₁ ∷ Δ) X₄)
      (k : E (X₄ ∷ X₃ ∷ X₂ ∷ X₁ ∷ Δ) (IE B)) (env : DenEnv Δ) → o ≡ connect s₁ (connect s₂ (connect s₃ (connect s₄ k)))
      → (∀ e → Undone (approx n k e)) → Undone (approx n o env)
conn⁴ n o s₁ s₂ s₃ s₄ k env refl h =
  connE n s₁ (connect s₂ (connect s₃ (connect s₄ k))) env λ q →
    let e₁ = hot (Proper (enter (approx n s₁ env) q)) ∷ᴬ env in
    connE n s₂ (connect s₃ (connect s₄ k)) e₁ λ q₂ →
    let e₂ = hot (Proper (enter (approx n s₂ e₁) q₂)) ∷ᴬ e₁ in
    connE n s₃ (connect s₄ k) e₂ λ q₃ →
    let e₃ = hot (Proper (enter (approx n s₃ e₂) q₃)) ∷ᴬ e₂ in
    connE n s₄ k e₃ λ q₄ → h (hot (Proper (enter (approx n s₄ e₃) q₄)) ∷ᴬ e₃)

-- A connect, named by an equation.
conn≡ : ∀ n {Δ A B} (o : E Δ (IE B)) (s : E Δ A) (b : E (A ∷ Δ) (IE B)) (env : DenEnv Δ) → o ≡ connect s b
      → (∀ q → Undone (approx n b (hot (Proper (enter (approx n s env) q)) ∷ᴬ env))) → Undone (approx n o env)
conn≡ n o s b env refl h = connE n s b env h

-- An annotated source shows the source's emits.
z₀ : ∀ {A} → Routes × AIE A
z₀ = (root , 0) , ((root , 0) , nothing)

ann-u : ∀ n {Δ A} (s : E Δ (IE A)) (env : DenEnv Δ) → Undone (approx n s env) → AUndone (approx n (annotate s) env)
ann-u n s env us p {y = y} rw with map-out′ proj₂ (Op.scan annStep z₀ (approx n (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))) env)) p rw
... | x , sx , eq with scan-out annStep z₀ (approx n (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))) env) p sx
...   | st , a , ca , eq′ with ann-step st a (trans eq (cong proj₂ eq′))
...     | refl with Cat.cat-out (λ c → approx n (if c then connected (here refl) else of (nothing ∷ []))
                                    (hot (Proper (enter (approx n (map just s) env) (p ⊕ (ix 1 ∷ [])))) ∷ᴬ env))
                              (p ⊕ (ix 0 ∷ []))
                              (conn-out (approx n (map just s) env) (λ h → approx n (concatˢ (connected (here refl)) (of (nothing ∷ []))) (h ∷ᴬ env)) p ca)
...       | inj₂ (_ , (l , _)) with of-mem _ 0 _ l
...         | here ()
...         | there ()
ann-u n s env us p {y = y} rw | x , sx , eq | st , a , ca , eq′ | refl | inj₁ l with hot-out {b = just y} l
... | _ , (σx , _) , _ , _ with map-out′ just (approx n s env) (p ⊕ (ix 1 ∷ [])) σx
...   | _ , sy , refl = us _ sy

------------------------------------------------------------------------
-- The elaboration

elab-undone : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) (env : DenEnv Δ) → EnvU ρ env
            → Undone (approx n (elab ρ o) env)
elab-undone n ρ (cold c) env eu p r
  with merge-out (λ x → approx n (render x) env)
         (approx n (scan phase (false , tick) (merge (concatˢ (map val (cold c)) (of (cdone ∷ []))) (of (tick ∷ [])))) env) p r
... | _ , x , _ , l , _ = render-u n x env _ l
elab-undone n ρ empty env eu p (() , _)
elab-undone n ρ (of xs) env eu p (r , _) with ∈-map⁻ _ (of-mem p 0 _ r)
... | _ , _ , refl = tt
elab-undone n ρ (map f s) env eu p r with map-out′ (mapIE f) (approx n (elab ρ s) env) p r
... | x , sx , refl = mapIE-u f x (elab-undone n ρ s env eu p sx)
elab-undone n ρ (scan f z s) env eu p r with map-out′ proj₂ (Op.scan (scanIE f) (z , marked begin) (approx n (elab ρ s) env)) p r
... | _ , sx , refl with scan-out (scanIE f) (z , marked begin) (approx n (elab ρ s) env) p sx
...   | st , x , dx , refl = scanIE-u f st x (elab-undone n ρ s env eu p dx)
elab-undone n ρ (takeWhile i keep s) env eu p r = let (_ , sx) = take-row i (passes keep) (approx n (elab ρ s) env) p r in elab-undone n ρ s env eu p sx
elab-undone n {Γ} ρ (flatMap op f s) env eu =
  conn⁴ n (elab ρ (flatMap op f s)) (of (tt ∷ [])) (flatMap (mergeᶠ nothing) (λ _ → elab (λ i → there (ρ i)) s) (connected (here refl)))
    closer (flatMap op (λ a → laneˢ (elab (λ i → there (there (there (there (ρ i))))) (f a))) (each valuesOf (connected (there (here refl)))))
    (combined op (trackers Γ 0 (λ i → there (there (there (there (ρ i))))))) env refl
    λ e → comb-u n op (trackers Γ 0 (λ i → there (there (there (there (ρ i)))))) e
elab-undone n ρ (connect s b) env eu =
  conn≡ n (elab ρ (connect s b)) (annotate (elab ρ s)) (elab (ext ρ) b) env refl λ q →
    elab-undone n (ext ρ) b (hot (Proper (enter (approx n (annotate (elab ρ s)) env) q)) ∷ᴬ env) (env-ext (λ z r →
      let (_ , (x , _) , _) = hot-out {t = Proper (enter (approx n (annotate (elab ρ s)) env) q)} r
      in ann-u n (elab ρ s) env (elab-undone n ρ s env eu) q x) eu)
elab-undone n ρ (connected i) env eu p r with each-one proj₂ (Op.scan joinStep (true , []) (lookup env (ρ (∈-map⁺ AIE i)))) p r
... | _ , x , dx , yi , _ with scan-out joinStep (true , []) (lookup env (ρ (∈-map⁺ AIE i))) p dx
...   | st , a , da , eq with join-u st a (subst (λ z → _ ∈ proj₂ z) eq yi)
...     | inj₁ u = u
...     | inj₂ e = eu i p (subst (λ m → enter (lookup env (ρ (∈-map⁺ AIE i))) p _ (out (proj₁ a , m))) e da)
elab-undone zero    ρ (defer l) env eu p (() , _)
elab-undone (suc n) ρ (defer l) env eu p (DeferT.body r , _) = elab-undone n ρ (Later.force l) env eu _ r
