-- AN ELABORATED PROGRAM ENDS NO LANE: none of its rows shows a
-- `laneDone`, wherever none of the hots it reads does (`elab-undone`).
-- A lane's frame sends one, and only the flatMap's scan reads it, which
-- sends values and routes alone (`react-u`); every other former passes
-- on what it reads, or sends routes.  Proved for each approximant
-- (`elab-undoneᵃ`) and for the meaning (`elab-undone⟦⟧`), whose one limit,
-- a `defer`, holds what some approximant holds.
module simultaneous.ElabUndone where

open import Data.Bool using (Bool; true; false; T; if_then_else_; _∧_)
import Data.List as L
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (does)

open import Tree using (Obs; Later; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (root; _≟ᵖ_; _⊕_; ix)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (out; Den; hot; Proper; DenEnv; enter; module Op; module DeferT; approx; ⟦_⟧; from)
open import denotation.Laws.Cut using (capprox)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (lone; ext; Tag; val; cdone; tick; flat; Flat; isZero; module Elaborate)
open import simultaneous.DenRows using (conn-out; merge-out; hot-out; map-out′; scan-out; take-row; of-mem; each-one; module Cat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; E; AIE; Routes; elab; srcLane; laneSrc; annotate; undone; joins;
  joinStep; annStep; tell; render; phase; passes; mapIE; scanIE; combined; react; onMark; cut; unpark; arrive; ended; burstOver;
  left; begun; stopped; overed; share; setAt; concatˢ; marked; closer; laneˢ; each; Out; Input; going; fed)

------------------------------------------------------------------------
-- What ends no lane

-- A lane's tell ends a lane just where its emit does.
tell-undone : ∀ {X} r (e : IE X) → undone (tell r e) ≡ undone e
tell-undone r (instEmit (value _) _)        = refl
tell-undone r (instEmit (mark (laneDone _)) _) = refl
tell-undone r (instEmit (mark begin) _)      = refl
tell-undone r (instEmit (mark over) _)       = refl
tell-undone r (instEmit (mark stop) _)       = refl
tell-undone r (instEmit (mark outerOpen) _)  = refl
tell-undone r (instEmit (mark outerClose) _) = refl
tell-undone r (instEmit (mark laneStart) _)  = refl
tell-undone r (instEmit (mark burstEnd) _)   = refl
tell-undone r (instEmit (mark outerDone) _)  = refl
tell-undone r (instEmit (mark subscribed) _) = refl
tell-undone r (instEmit (mark completed) _)  = refl

-- What a lane tells that ends no lane is what it read.
tell-back : ∀ {X} r (e : IE X) {a} → tell r e ≡ a → T (undone a) → e ≡ a
tell-back r (instEmit (mark (laneDone _)) _) refl ()
tell-back r (instEmit (value _) _)        q _ = q
tell-back r (instEmit (mark begin) _)      q _ = q
tell-back r (instEmit (mark over) _)       q _ = q
tell-back r (instEmit (mark stop) _)       q _ = q
tell-back r (instEmit (mark outerOpen) _)  q _ = q
tell-back r (instEmit (mark outerClose) _) q _ = q
tell-back r (instEmit (mark laneStart) _)  q _ = q
tell-back r (instEmit (mark burstEnd) _)   q _ = q
tell-back r (instEmit (mark outerDone) _)  q _ = q
tell-back r (instEmit (mark subscribed) _) q _ = q
tell-back r (instEmit (mark completed) _)  q _ = q

-- A told `laneDone` carries its lane's routes.
tell-done : ∀ {X} r (e : IE X) {kd n} → tell r e ≡ instEmit (mark (laneDone kd)) n → kd ≡ proj₂ r
tell-done r (instEmit (mark (laneDone _)) _) refl = refl
tell-done r (instEmit (value _) _)        ()
tell-done r (instEmit (mark begin) _)      ()
tell-done r (instEmit (mark over) _)       ()
tell-done r (instEmit (mark stop) _)       ()
tell-done r (instEmit (mark outerOpen) _)  ()
tell-done r (instEmit (mark outerClose) _) ()
tell-done r (instEmit (mark laneStart) _)  ()
tell-done r (instEmit (mark burstEnd) _)   ()
tell-done r (instEmit (mark outerDone) _)  ()
tell-done r (instEmit (mark subscribed) _) ()
tell-done r (instEmit (mark completed) _)  ()

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

------------------------------------------------------------------------
-- Lists sent

-- A list none of whose emits ends a lane.
Sends : ∀ {B} → List (IE B) → Set
Sends xs = ∀ {y} → y ∈ xs → T (undone y)

sd-[] : ∀ {B} → Sends {B} []
sd-[] ()

sd-one : ∀ {B} m n → T (undone {B} (instEmit (mark m) n)) → Sends {B} (instEmit (mark m) n ∷ [])
sd-one m n u (here refl) = u
sd-one m n u (there ())

sd-rep : ∀ {B} k m n → T (undone {B} (instEmit (mark m) n)) → Sends {B} (replicate k (instEmit (mark m) n))
sd-rep (suc k) m n u (here refl) = u
sd-rep (suc k) m n u (there i)   = sd-rep k m n u i

cut-u : ∀ {B} k n s → Sends {B} (proj₂ (cut k n s))
cut-u k n s with Flat.spent s | Elaborate.anyHolds {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone (Flat.at s) (Flat.live s)
... | true  | _     = sd-[]
... | false | true  = sd-[]
... | false | false = sd-rep k stop n tt

unpark-u : ∀ {B} n s → Sends {B} (proj₂ (unpark n s))
unpark-u n s with Elaborate.anyHolds {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone (Flat.at s) (Flat.live s)
... | true  = sd-[]
... | false = sd-rep (Flat.parked s) stop n tt

arrive-u : ∀ {B} op n s → Sends {B} (proj₂ (arrive op n s))
arrive-u (mergeᶠ (just _)) n s = sd-[]
arrive-u (mergeᶠ nothing)  n s = sd-[]
arrive-u Tree.switchᶠ      n s = cut-u (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
arrive-u Tree.exhaustᶠ     n s = sd-[]

ended-u : ∀ {B} k n s → Sends {B} (proj₂ (ended k n s))
ended-u k n s with isZero (Flat.queue s)
... | false = sd-[]
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = sd-[]
...   | false = cut-u (k + Flat.held s) n (record s { held = 0 })

burstOver-u : ∀ {B} b n s → Sends {B} (proj₂ (burstOver b n s))
burstOver-u true  n s = sd-[]
burstOver-u false n s = cut-u (Flat.held s) n (record s { held = 0 })

left-u : ∀ {B} n s → Sends {B} (proj₂ (left n s))
left-u n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = sd-[]
... | false = cut-u (Flat.outer s) n (record s { outer = 0 })

begun-u : ∀ {B} b n s → Sends {B} (proj₂ (begun b n s))
begun-u b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
... | true  = sd-[]
... | false = sd-one begin n tt

stopped-u : ∀ {B} b n s k → Sends {B} (proj₂ (stopped b n s k))
stopped-u b n s zero    = sd-[]
stopped-u b n s (suc _) = sd-one stop n tt

overed-u : ∀ {B} n s → Sends {B} (proj₂ (overed n s))
overed-u n s with Flat.spent s
... | true  = sd-[]
... | false = sd-one over n tt

onMark-u : ∀ {B} op b s m n → Sends {B} (proj₂ (onMark op b s m n))
onMark-u op b s begin      n = begun-u b n s
onMark-u op b s stop       n = stopped-u b n s (if Flat.spent s then 0 else share b s)
onMark-u op b s over       n = overed-u n s
onMark-u op b s outerOpen  n = arrive-u op n s
onMark-u op b s outerClose n = sd-[]
onMark-u op b s laneStart  n = sd-[]
onMark-u op b s (laneDone k) n =
  ended-u (k ⊓ Flat.lanes s) n
    (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ k ; dead = true })
onMark-u op b s burstEnd   n = burstOver-u (isZero (Flat.held s) Data.Bool.∨ Flat.dead s) n s
onMark-u op b s outerDone  n = left-u n (record s { finished = true })
onMark-u op b s subscribed n = sd-one subscribed n tt
onMark-u op b s completed  n = sd-one completed n tt

-- THE SCAN ENDS NO LANE: it sends a value, or routes.
react-sends : ∀ {B} op (st : Out B) inp → Sends (proj₂ (react op st inp))
react-sends op (s , _) (just (inj₁ (br , instEmit (value v) nm))) (here refl) = tt
react-sends op (s , _) (just (inj₁ (br , instEmit (value v) nm))) (there ())
react-sends op (s , _) (just (inj₁ (br , instEmit (mark m) nm))) i = onMark-u op br s m nm i
react-sends op (s , _) (just (inj₂ (ix′ , r))) i = unpark-u root (record s { live = setAt ix′ r (Flat.live s) }) i
react-sends op (s , _) nothing ()

joins-u : ∀ {X} (r : Routes) (e : IE X) → Sends (joins r e)
joins-u (m , k) (instEmit (value _) _) i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark begin) n) i with does (n ≟ᵖ m)
... | true  = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark begin) n) () | false
joins-u (m , k) (instEmit (mark over) _)       i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark stop) _)       i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark outerOpen) _)  i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark outerClose) _) i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark laneStart) _)  i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark (laneDone _)) _)   i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark burstEnd) _)   i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark outerDone) _)  i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark subscribed) _) i = sd-rep k begin m tt i
joins-u (m , k) (instEmit (mark completed) _)  i = sd-rep k begin m tt i

-- A reader's step sends routes, or the emit it met.
join-u : ∀ {X} (β : Bool × (List (IE X) × List (IE X))) (a : AIE X) (b : Bool) {y}
       → y ∈ (if b then proj₁ (proj₂ (joinStep β a)) else proj₂ (proj₂ (joinStep β a))) → T (undone y) ⊎ proj₂ a ≡ just y
join-u (true , _)  (r , just e) true  i = inj₁ (joins-u r e i)
join-u (true , _)  (r , just e) false (here refl) = inj₂ refl
join-u (true , _)  (r , just e) false (there ())
join-u (true , _)  ((m , k) , nothing) true i = inj₁ (sd-rep k begin m tt i)
join-u (true , _)  ((m , k) , nothing) false ()
join-u (false , _) (r , just e) true ()
join-u (false , _) (r , just e) false (here refl) = inj₂ refl
join-u (false , _) (r , just e) false (there ())
join-u (false , _) (r , nothing) true ()
join-u (false , _) (r , nothing) false ()

-- A mark ends no lane at any type, or at every one.
mark-u : ∀ {A B} m n → T (undone {A} (instEmit (mark m) n)) → T (undone {B} (instEmit (mark m) n))
mark-u begin      _ u = u
mark-u over       _ u = u
mark-u stop       _ u = u
mark-u outerOpen  _ u = u
mark-u outerClose _ u = u
mark-u laneStart  _ u = u
mark-u (laneDone _) _ ()
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
connD : ∀ {A B} (ds : Den A) (F : Den A → Den (IE B)) → (∀ q → Undone (F (hot (Proper (enter ds q))))) → Undone (Op.connect ds F)
connD ds F h p r = h (p ⊕ (ix 1 ∷ [])) (p ⊕ (ix 0 ∷ [])) (conn-out ds F p r)

-- A cold's steps send values and routes.
render-u : ∀ N n {Δ A} (x : Bool × Tag A) (env : DenEnv Δ) → Undone (capprox N n (render x) env)
render-u N n (false , val a) env p (r , _) with of-mem p 0 _ r
... | here refl = tt
... | there ()
render-u N n (true , val a) env p r
  with merge-out (λ m → Op.of (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ [])) (capprox N n (cold (fresh (λ p → p))) env) p r
... | q , m , _ , (l , _) , _ with of-mem (q ⊕ (ix 1 ∷ [])) 0 (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ []) l
...   | here refl                 = tt
...   | there (here refl)         = tt
...   | there (there (here refl)) = tt
...   | there (there (there ()))
render-u N n (true , cdone) env p r with map-out′ (λ m → instEmit (mark begin) m) (capprox N n (cold (fresh (λ p → p))) env) p r
... | _ , _ , refl = tt
render-u N n (false , cdone) env p (() , _)
render-u N n (false , tick)  env p (() , _)
render-u N n (true , tick)   env p (() , _)

-- The flatMap's scan sends values and routes, whatever it reads.
react-u : ∀ {B} op (z : Out B) (d : Den (Maybe (Input B))) → Undone (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan (react op) z d))
react-u op z d p r with each-one proj₂ (Op.scan (react op) z d) p r
... | _ , x , dx , yi with scan-out (react op) z d p dx
...   | st , inp , _ , eq = react-sends op st inp (subst (λ w → _ ∈ proj₂ w) eq yi)

comb-u : ∀ N n {Δ A B} op (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) → Undone (capprox N n (combined op tk) env)
comb-u N n op tk env = react-u op (flat root 0 0 false false false 0 0 0 0 [] , [])
  (capprox N n (takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))) env)

comb-uᵃ : ∀ n {Δ A B} op (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) → Undone (approx n (combined op tk) env)
comb-uᵃ n op tk env = react-u op (flat root 0 0 false false false 0 0 0 0 [] , [])
  (approx n (takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))) env)

comb-u⟦⟧ : ∀ {Δ A B} op (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) → Undone (⟦ combined op tk ⟧ env)
comb-u⟦⟧ op tk env = react-u op (flat root 0 0 false false false 0 0 0 0 [] , [])
  (⟦ takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ []))) ⟧ env)

-- Four connects show their innermost body's rows.
Eval : Set₁
Eval = ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A

-- An evaluator reading a connect as one.
Hom : Eval → Set₁
Hom 𝓔 = ∀ {Δ A B} (s : E Δ A) (b : E (A ∷ Δ) B) (env : DenEnv Δ) → 𝓔 (connect s b) env ≡ Op.connect (𝓔 s env) (λ h → 𝓔 b (h ∷ᴬ env))

connH : ∀ (𝓔 : Eval) → Hom 𝓔 → ∀ {Δ A B} (s : E Δ A) (b : E (A ∷ Δ) (IE B)) (env : DenEnv Δ)
      → (∀ q → Undone (𝓔 b (hot (Proper (enter (𝓔 s env) q)) ∷ᴬ env))) → Undone (𝓔 (connect s b) env)
connH 𝓔 hom s b env h = subst Undone (sym (hom s b env)) (connD (𝓔 s env) (λ h′ → 𝓔 b (h′ ∷ᴬ env)) h)

-- Four connects show their innermost body's rows.
conn⁴ : ∀ (𝓔 : Eval) → Hom 𝓔 → ∀ {Δ X₁ X₂ X₃ X₄ B} (o : E Δ (IE B)) (s₁ : E Δ X₁) (s₂ : E (X₁ ∷ Δ) X₂) (s₃ : E (X₂ ∷ X₁ ∷ Δ) X₃) (s₄ : E (X₃ ∷ X₂ ∷ X₁ ∷ Δ) X₄)
      (k : E (X₄ ∷ X₃ ∷ X₂ ∷ X₁ ∷ Δ) (IE B)) (env : DenEnv Δ) → o ≡ connect s₁ (connect s₂ (connect s₃ (connect s₄ k)))
      → (∀ e → Undone (𝓔 k e)) → Undone (𝓔 o env)
conn⁴ 𝓔 hom o s₁ s₂ s₃ s₄ k env refl h =
  connH 𝓔 hom s₁ (connect s₂ (connect s₃ (connect s₄ k))) env λ q →
    let e₁ = hot (Proper (enter (𝓔 s₁ env) q)) ∷ᴬ env in
    connH 𝓔 hom s₂ (connect s₃ (connect s₄ k)) e₁ λ q₂ →
    let e₂ = hot (Proper (enter (𝓔 s₂ e₁) q₂)) ∷ᴬ e₁ in
    connH 𝓔 hom s₃ (connect s₄ k) e₂ λ q₃ →
    let e₃ = hot (Proper (enter (𝓔 s₃ e₂) q₃)) ∷ᴬ e₂ in
    connH 𝓔 hom s₄ k e₃ λ q₄ → h (hot (Proper (enter (𝓔 s₄ e₃) q₄)) ∷ᴬ e₃)

-- An annotated source shows the source's emits.
z₀ : ∀ {A} → Routes × AIE A
z₀ = (root , 0) , ((root , 0) , nothing)

ann-u : ∀ N n {Δ A} (s : E Δ (IE A)) (env : DenEnv Δ) → Undone (capprox N n s env) → AUndone (capprox N n (annotate s) env)
ann-u N n s env us p {y = y} rw with map-out′ proj₂ (Op.scan annStep z₀ (capprox N n (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))) env)) p rw
... | x , sx , eq with scan-out annStep z₀ (capprox N n (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))) env) p sx
...   | st , a , ca , eq′ with ann-step st a (trans eq (cong proj₂ eq′))
...     | refl with Cat.cat-out (λ c → capprox N n (if c then connected (here refl) else of (nothing ∷ []))
                                    (hot (Proper (enter (capprox N n (map just s) env) (p ⊕ (ix 1 ∷ [])))) ∷ᴬ env))
                              (p ⊕ (ix 0 ∷ []))
                              (conn-out (capprox N n (map just s) env) (λ h → capprox N n (concatˢ (connected (here refl)) (of (nothing ∷ []))) (h ∷ᴬ env)) p ca)
...       | inj₂ (_ , (l , _)) with of-mem _ 0 _ l
...         | here ()
...         | there ()
ann-u N n s env us p {y = y} rw | x , sx , eq | st , a , ca , eq′ | refl | inj₁ l with hot-out {b = just y} l
... | _ , (σx , _) , _ , _ with map-out′ just (capprox N n s env) (p ⊕ (ix 1 ∷ [])) σx
...   | _ , sy , refl = us _ sy

-- A connect's elaboration ends no lane where its source's and body's end none.
conn-u : ∀ N n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (env : DenEnv Δ) → EnvU ρ env
       → Undone (capprox N n (elab ρ s) env) → (∀ e → EnvU (ext ρ) e → Undone (capprox N n (elab (ext ρ) b) e))
       → Undone (capprox N n (elab ρ (connect s b)) env)
conn-u N n ρ s b env eu us ub =
  connH (capprox N n) (λ _ _ _ → refl) (annotate (elab ρ s)) (elab (ext ρ) b) env λ q →
    ub (hot (Proper (enter (capprox N n (annotate (elab ρ s)) env) q)) ∷ᴬ env) (env-ext (λ z r →
      let (_ , (x , _) , _) = hot-out {t = Proper (enter (capprox N n (annotate (elab ρ s)) env) q)} r
      in ann-u N n (elab ρ s) env us q x) eu)

------------------------------------------------------------------------
-- The elaboration

elab-undone : ∀ N n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) (env : DenEnv Δ) → EnvU ρ env
            → Undone (capprox N n (elab ρ o) env)
elab-undone N n ρ (cold c) env eu p r
  with merge-out (λ x → capprox N n (render x) env)
         (capprox N n (scan phase (false , tick) (Tree.merge (concatˢ (map val (cold c)) (of (cdone ∷ []))) (of (tick ∷ [])))) env) p r
... | _ , x , _ , l , _ = render-u N n x env _ l
elab-undone N n ρ empty env eu p (() , _)
elab-undone N n ρ (of xs) env eu p (r , _) with ∈-map⁻ _ (of-mem p 0 _ r)
... | _ , _ , refl = tt
elab-undone N n ρ (map f s) env eu p r with map-out′ (mapIE f) (capprox N n (elab ρ s) env) p r
... | x , sx , refl = mapIE-u f x (elab-undone N n ρ s env eu p sx)
elab-undone N n ρ (scan f z s) env eu p r with map-out′ proj₂ (Op.scan (scanIE f) (z , marked begin) (capprox N n (elab ρ s) env)) p r
... | _ , sx , refl with scan-out (scanIE f) (z , marked begin) (capprox N n (elab ρ s) env) p sx
...   | st , x , dx , refl = scanIE-u f st x (elab-undone N n ρ s env eu p dx)
elab-undone N n ρ (takeWhile i keep s) env eu p r =
  let (_ , sx) = take-row i (passes keep) (capprox N n (elab ρ s) env) p r in elab-undone N n ρ s env eu p sx
elab-undone N n ρ (flatMap op f s) env eu =
  conn⁴ (capprox N n) (λ _ _ _ → refl) (elab _ (flatMap op f s)) _ _ _ _ _ env refl λ e → comb-u N n op _ e
elab-undone N n ρ (connect s b) env eu =
  conn-u N n ρ s b env eu (elab-undone N n ρ s env eu) (λ e eu′ → elab-undone N n (ext ρ) b e eu′)
elab-undone N n ρ (connected i) env eu p r
  with merge-out (λ x → Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])))
         (Op.scan joinStep (true , ([] , [])) (lookup env (ρ (∈-map⁺ AIE i)))) p r
... | _ , x , dx , l₁ , _ with merge-out (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])) _ l₁
...   | _ , b , _ , (l₂ , _) , _ with scan-out joinStep (true , ([] , [])) (lookup env (ρ (∈-map⁺ AIE i))) p dx
...     | st , a , da , refl with join-u st a b (of-mem _ 0 _ l₂)
...       | inj₁ u = u
...       | inj₂ e = eu i p (subst (λ m → enter (lookup env (ρ (∈-map⁺ AIE i))) p _ (out (proj₁ a , m))) e da)
elab-undone N zero    ρ (defer l) env eu p (((), _) , _)
elab-undone N (suc n) ρ (defer l) env eu p (DeferT.body r , _) = elab-undone N n ρ (Later.force l) env eu _ r

------------------------------------------------------------------------
-- The approximants and the meaning

render-uᵃ : ∀ n {Δ A} (x : Bool × Tag A) (env : DenEnv Δ) → Undone (approx n (render x) env)
render-uᵃ n (false , val a) env p (r , _) with of-mem p 0 _ r
... | here refl = tt
... | there ()
render-uᵃ n (true , val a) env p r
  with merge-out (λ m → Op.of (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ [])) (approx n (cold (fresh (λ p → p))) env) p r
... | q , m , _ , (l , _) , _ with of-mem (q ⊕ (ix 1 ∷ [])) 0 (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ []) l
...   | here refl                 = tt
...   | there (here refl)         = tt
...   | there (there (here refl)) = tt
...   | there (there (there ()))
render-uᵃ n (true , cdone) env p r with map-out′ (λ m → instEmit (mark begin) m) (approx n (cold (fresh (λ p → p))) env) p r
... | _ , _ , refl = tt
render-uᵃ n (false , cdone) env p (() , _)
render-uᵃ n (false , tick)  env p (() , _)
render-uᵃ n (true , tick)   env p (() , _)

render-u⟦⟧ : ∀ {Δ A} (x : Bool × Tag A) (env : DenEnv Δ) → Undone (⟦ render x ⟧ env)
render-u⟦⟧ (false , val a) env p (r , _) with of-mem p 0 _ r
... | here refl = tt
... | there ()
render-u⟦⟧ (true , val a) env p r
  with merge-out (λ m → Op.of (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ [])) (⟦ cold (fresh (λ p → p)) ⟧ env) p r
... | q , m , _ , (l , _) , _ with of-mem (q ⊕ (ix 1 ∷ [])) 0 (instEmit (mark begin) m ∷ instEmit (value a) m ∷ instEmit (mark over) m ∷ []) l
...   | here refl                 = tt
...   | there (here refl)         = tt
...   | there (there (here refl)) = tt
...   | there (there (there ()))
render-u⟦⟧ (true , cdone) env p r with map-out′ (λ m → instEmit (mark begin) m) (⟦ cold (fresh (λ p → p)) ⟧ env) p r
... | _ , _ , refl = tt
render-u⟦⟧ (false , cdone) env p (() , _)
render-u⟦⟧ (false , tick)  env p (() , _)
render-u⟦⟧ (true , tick)   env p (() , _)

ann-uᵃ : ∀ n {Δ A} (s : E Δ (IE A)) (env : DenEnv Δ) → Undone (approx n s env) → AUndone (approx n (annotate s) env)
ann-uᵃ n s env us p {y = y} rw with map-out′ proj₂ (Op.scan annStep z₀ (approx n (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))) env)) p rw
... | x , sx , eq with scan-out annStep z₀ (approx n (connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ [])))) env) p sx
...   | st , a , ca , eq′ with ann-step st a (trans eq (cong proj₂ eq′))
...     | refl with Cat.cat-out (λ c → approx n (if c then connected (here refl) else of (nothing ∷ []))
                                    (hot (Proper (enter (approx n (map just s) env) (p ⊕ (ix 1 ∷ [])))) ∷ᴬ env))
                              (p ⊕ (ix 0 ∷ []))
                              (conn-out (approx n (map just s) env) (λ h → approx n (concatˢ (connected (here refl)) (of (nothing ∷ []))) (h ∷ᴬ env)) p ca)
...       | inj₂ (_ , (l , _)) with of-mem _ 0 _ l
...         | here ()
...         | there ()
ann-uᵃ n s env us p {y = y} rw | x , sx , eq | st , a , ca , eq′ | refl | inj₁ l with hot-out {b = just y} l
... | _ , (σx , _) , _ , _ with map-out′ just (approx n s env) (p ⊕ (ix 1 ∷ [])) σx
...   | _ , sy , refl = us _ sy

ann-u⟦⟧ : ∀ {Δ A} (s : E Δ (IE A)) (env : DenEnv Δ) → Undone (⟦ s ⟧ env) → AUndone (⟦ annotate s ⟧ env)
ann-u⟦⟧ s env us p {y = y} rw with map-out′ proj₂ (Op.scan annStep z₀ (⟦ connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ []))) ⟧ env)) p rw
... | x , sx , eq with scan-out annStep z₀ (⟦ connect (map just s) (concatˢ (connected (here refl)) (of (nothing ∷ []))) ⟧ env) p sx
...   | st , a , ca , eq′ with ann-step st a (trans eq (cong proj₂ eq′))
...     | refl with Cat.cat-out (λ c → ⟦ if c then connected (here refl) else of (nothing ∷ []) ⟧
                                    (hot (Proper (enter (⟦ map just s ⟧ env) (p ⊕ (ix 1 ∷ [])))) ∷ᴬ env))
                              (p ⊕ (ix 0 ∷ []))
                              (conn-out (⟦ map just s ⟧ env) (λ h → ⟦ concatˢ (connected (here refl)) (of (nothing ∷ [])) ⟧ (h ∷ᴬ env)) p ca)
...       | inj₂ (_ , (l , _)) with of-mem _ 0 _ l
...         | here ()
...         | there ()
ann-u⟦⟧ s env us p {y = y} rw | x , sx , eq | st , a , ca , eq′ | refl | inj₁ l with hot-out {b = just y} l
... | _ , (σx , _) , _ , _ with map-out′ just (⟦ s ⟧ env) (p ⊕ (ix 1 ∷ [])) σx
...   | _ , sy , refl = us _ sy

-- A binder's hot ends no lane where its annotated source ends none.
hot-u : ∀ {X} (d : Den (AIE X)) {q} → AUndone d → AUndone (hot (Proper (enter d q)))
hot-u d u z r = let (_ , (x , _) , _) = hot-out {t = Proper (enter d _)} r in u _ x

elab-undoneᵃ : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) (env : DenEnv Δ) → EnvU ρ env
             → Undone (approx n (elab ρ o) env)
elab-undoneᵃ n ρ (cold c) env eu p r
  with merge-out (λ x → approx n (render x) env)
         (approx n (scan phase (false , tick) (Tree.merge (concatˢ (map val (cold c)) (of (cdone ∷ []))) (of (tick ∷ [])))) env) p r
... | _ , x , _ , l , _ = render-uᵃ n x env _ l
elab-undoneᵃ n ρ empty env eu p (() , _)
elab-undoneᵃ n ρ (of xs) env eu p (r , _) with ∈-map⁻ _ (of-mem p 0 _ r)
... | _ , _ , refl = tt
elab-undoneᵃ n ρ (map f s) env eu p r with map-out′ (mapIE f) (approx n (elab ρ s) env) p r
... | x , sx , refl = mapIE-u f x (elab-undoneᵃ n ρ s env eu p sx)
elab-undoneᵃ n ρ (scan f z s) env eu p r with map-out′ proj₂ (Op.scan (scanIE f) (z , marked begin) (approx n (elab ρ s) env)) p r
... | _ , sx , refl with scan-out (scanIE f) (z , marked begin) (approx n (elab ρ s) env) p sx
...   | st , x , dx , refl = scanIE-u f st x (elab-undoneᵃ n ρ s env eu p dx)
elab-undoneᵃ n ρ (takeWhile i keep s) env eu p r =
  let (_ , sx) = take-row i (passes keep) (approx n (elab ρ s) env) p r in elab-undoneᵃ n ρ s env eu p sx
elab-undoneᵃ n ρ (flatMap op f s) env eu =
  conn⁴ (approx n) (λ _ _ _ → refl) (elab _ (flatMap op f s)) _ _ _ _ _ env refl λ e → comb-uᵃ n op _ e
elab-undoneᵃ n ρ (connect s b) env eu =
  connH (approx n) (λ _ _ _ → refl) (annotate (elab ρ s)) (elab (ext ρ) b) env λ q → elab-undoneᵃ n (ext ρ) b _ (env-ext (hot-u (approx n (annotate (elab ρ s)) env) (ann-uᵃ n (elab ρ s) env (elab-undoneᵃ n ρ s env eu))) eu)
elab-undoneᵃ n ρ (connected i) env eu p r
  with merge-out (λ x → Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])))
         (Op.scan joinStep (true , ([] , [])) (lookup env (ρ (∈-map⁺ AIE i)))) p r
... | _ , x , dx , l₁ , _ with merge-out (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])) _ l₁
...   | _ , b , _ , (l₂ , _) , _ with scan-out joinStep (true , ([] , [])) (lookup env (ρ (∈-map⁺ AIE i))) p dx
...     | st , a , da , refl with join-u st a b (of-mem _ 0 _ l₂)
...       | inj₁ u = u
...       | inj₂ e = eu i p (subst (λ m → enter (lookup env (ρ (∈-map⁺ AIE i))) p _ (out (proj₁ a , m))) e da)
elab-undoneᵃ zero    ρ (defer l) env eu p (() , _)
elab-undoneᵃ (suc n) ρ (defer l) env eu p (DeferT.body r , _) = elab-undoneᵃ n ρ (Later.force l) env eu _ r

elab-undone⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) (env : DenEnv Δ) → EnvU ρ env
              → Undone (⟦ elab ρ o ⟧ env)
elab-undone⟦⟧ ρ (cold c) env eu p r
  with merge-out (λ x → ⟦ render x ⟧ env)
         (⟦ scan phase (false , tick) (Tree.merge (concatˢ (map val (cold c)) (of (cdone ∷ []))) (of (tick ∷ []))) ⟧ env) p r
... | _ , x , _ , l , _ = render-u⟦⟧ x env _ l
elab-undone⟦⟧ ρ empty env eu p (() , _)
elab-undone⟦⟧ ρ (of xs) env eu p (r , _) with ∈-map⁻ _ (of-mem p 0 _ r)
... | _ , _ , refl = tt
elab-undone⟦⟧ ρ (map f s) env eu p r with map-out′ (mapIE f) (⟦ elab ρ s ⟧ env) p r
... | x , sx , refl = mapIE-u f x (elab-undone⟦⟧ ρ s env eu p sx)
elab-undone⟦⟧ ρ (scan f z s) env eu p r with map-out′ proj₂ (Op.scan (scanIE f) (z , marked begin) (⟦ elab ρ s ⟧ env)) p r
... | _ , sx , refl with scan-out (scanIE f) (z , marked begin) (⟦ elab ρ s ⟧ env) p sx
...   | st , x , dx , refl = scanIE-u f st x (elab-undone⟦⟧ ρ s env eu p dx)
elab-undone⟦⟧ ρ (takeWhile i keep s) env eu p r =
  let (_ , sx) = take-row i (passes keep) (⟦ elab ρ s ⟧ env) p r in elab-undone⟦⟧ ρ s env eu p sx
elab-undone⟦⟧ ρ (flatMap op f s) env eu =
  conn⁴ ⟦_⟧ (λ _ _ _ → refl) (elab _ (flatMap op f s)) _ _ _ _ _ env refl λ e → comb-u⟦⟧ op _ e
elab-undone⟦⟧ ρ (connect s b) env eu =
  connH ⟦_⟧ (λ _ _ _ → refl) (annotate (elab ρ s)) (elab (ext ρ) b) env λ q → elab-undone⟦⟧ (ext ρ) b _ (env-ext (hot-u (⟦ annotate (elab ρ s) ⟧ env) (ann-u⟦⟧ (elab ρ s) env (elab-undone⟦⟧ ρ s env eu))) eu)
elab-undone⟦⟧ ρ (connected i) env eu p r
  with merge-out (λ x → Op.flatMap (mergeᶠ nothing) (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])))
         (Op.scan joinStep (true , ([] , [])) (lookup env (ρ (∈-map⁺ AIE i)))) p r
... | _ , x , dx , l₁ , _ with merge-out (λ b → Op.of (if b then proj₁ (proj₂ x) else proj₂ (proj₂ x))) (Op.of (true ∷ false ∷ [])) _ l₁
...   | _ , b , _ , (l₂ , _) , _ with scan-out joinStep (true , ([] , [])) (lookup env (ρ (∈-map⁺ AIE i))) p dx
...     | st , a , da , refl with join-u st a b (of-mem _ 0 _ l₂)
...       | inj₁ u = u
...       | inj₂ e = eu i p (subst (λ m → enter (lookup env (ρ (∈-map⁺ AIE i))) p _ (out (proj₁ a , m))) e da)
elab-undone⟦⟧ ρ (defer l) env eu p (from N h , _) = elab-undoneᵃ N ρ (defer l) env eu p (h N ≤-refl)
