{-# OPTIONS --guardedness #-}

-- THE CORE NEVER COMPLETES ALOUD: no emit the elaborated core shows is
-- the completion mark.  Only `completing` mints that mark, and `elab`
-- never applies it; every other emit is a value, a mark one of the
-- elaboration's own functions sends, or one it passes on from a child,
-- a connect's source, or a connect in scope.  So the fact goes up the
-- tree former by former (`denotation.Laws.Outs`), a connect in scope
-- carrying it for its source's emits.
module simultaneous.CoreOuts where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; replicate)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _⊓_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (does)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap;
  connect; connected; defer)
open import denotation.Position using (_≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; DenEnv; enter; approx; out)
open import denotation.Laws.Outs using (Outs; outs-⊥; outs-defer; Good; g-sem; g-of; g-empty; g-map; g-scan; g-take; g-flat; g-conn;
  sound; g-top; g-map′; g-flat′)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate; Flat; isZero; Tag; val; cdone; tick; lanePart; burstPart; outerB; laneB; closeB; ext)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (E; IE; AIE; Input; Out; unfinished; marked; concatˢ; each;
  annStep; annotate; joins; joinStep; reader; render; coldˢ; mapIE; scanIE; opening; closing; closer; piece; framed; laneStep; counted;
  laneˢ; stops; cut; unpark; arrive; ended; burstOver; left; stopped; share; begun; overed; onMark; setAt; react; branch; fed; combined;
  flatMapˢ; elab; anyHolds)

------------------------------------------------------------------------
-- Emits

-- Not the completion mark.
U : ∀ {A} → IE A → Set
U e = T (unfinished e)

-- A connect's emit, or its end.
AnnOK : ∀ {A} → AIE A → Set
AnnOK (_ , just e)  = U e
AnnOK (_ , nothing) = ⊤

JustOK : ∀ {A} → Maybe (IE A) → Set
JustOK (just e) = U e
JustOK nothing  = ⊤

-- What a flatMap's scan reads.
InOK : ∀ {B} → Maybe (Input B) → Set
InOK (just (inj₁ (_ , e))) = U e
InOK (just (inj₂ _))       = ⊤
InOK nothing               = ⊤

-- A mark is the completion whatever the values beside it.
U-mark : ∀ {A B} m n → U {A} (instEmit (mark m) n) → U {B} (instEmit (mark m) n)
U-mark begin _ _ = tt
U-mark over _ _ = tt
U-mark stop _ _ = tt
U-mark outerOpen _ _ = tt
U-mark outerClose _ _ = tt
U-mark laneStart _ _ = tt
U-mark carry _ _ = tt
U-mark laneDone _ _ = tt
U-mark burstEnd _ _ = tt
U-mark outerDone _ _ = tt
U-mark subscribed _ _ = tt
U-mark completed _ u = u

rep-U : ∀ {A} {e : IE A} k → U e → All U (replicate k e)
rep-U zero    _ = []
rep-U (suc k) u = u ∷ rep-U k u

stops-U : ∀ {B} k n → All (U {B}) (stops k n)
stops-U k n = rep-U {e = instEmit (mark stop) n} k tt

vals-U : ∀ {A} (xs : List A) → All U (L.map (λ x → instEmit (value x) root) xs)
vals-U []       = []
vals-U (_ ∷ xs) = tt ∷ vals-U xs

mapIE-U : ∀ {A B} (f : A → B) e → U e → U (mapIE f e)
mapIE-U f (instEmit (value _) _) _ = tt
mapIE-U f (instEmit (mark m) n)  u = U-mark m n u

scanIE-U : ∀ {A B} (f : B → A → B) acc e → U e → U (proj₂ (scanIE f acc e))
scanIE-U f (_ , _) (instEmit (value _) _) _ = tt
scanIE-U f (_ , _) (instEmit (mark m) n)  u = U-mark m n u

opening-U : ∀ {A B} (e : IE A) → U e → U {B} (opening e)
opening-U (instEmit (value _) _) _ = tt
opening-U (instEmit (mark m) n)  u = U-mark m n u

closing-U : ∀ {A B} (e : IE A) → All (U {B}) (closing e)
closing-U (instEmit (value _) _) = tt ∷ []
closing-U (instEmit (mark _) _)  = []

annStep-U : ∀ {A} acc (x : Maybe (IE A)) → JustOK x → AnnOK (proj₂ (annStep acc x))
annStep-U (_ , _) (just _) u = u
annStep-U (_ , _) nothing  _ = tt

joins-U : ∀ {A} r (e : IE A) → All U (joins r e)
joins-U (m , k) (instEmit (mark begin) n) with does (n ≟ᵖ m)
... | true  = rep-U {e = instEmit (mark begin) m} k tt
... | false = []
joins-U (m , k) (instEmit (value _) _)          = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark over) _)       = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark stop) _)       = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark outerOpen) _)  = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark outerClose) _) = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark laneStart) _)  = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark carry) _)      = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark laneDone) _)   = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark burstEnd) _)   = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark outerDone) _)  = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark subscribed) _) = rep-U {e = instEmit (mark begin) m} k tt
joins-U (m , k) (instEmit (mark completed) _)  = rep-U {e = instEmit (mark begin) m} k tt

joinStep-U : ∀ {A} acc (x : AIE A) → AnnOK x → All U (proj₂ (joinStep acc x))
joinStep-U (true , _)  (r , just e)  u = ++⁺ (joins-U r e) (u ∷ [])
joinStep-U (true , _)  (r , nothing) _ = rep-U {e = instEmit (mark begin) (proj₁ r)} (proj₂ r) tt
joinStep-U (false , _) (r , just e)  u = u ∷ []
joinStep-U (false , _) (r , nothing) _ = []

laneStep-U : ∀ {A} acc (e : IE A) → U e → All U (proj₂ (laneStep acc e))
laneStep-U (r , _) (instEmit (mark laneDone) n)   _ = ++⁺ (rep-U {e = marked carry} (proj₂ r) tt) (tt ∷ [])
laneStep-U (r , _) (instEmit (value _) _)          u = u ∷ []
laneStep-U (r , _) (instEmit (mark begin) _)       u = u ∷ []
laneStep-U (r , _) (instEmit (mark over) _)        u = u ∷ []
laneStep-U (r , _) (instEmit (mark stop) _)        u = u ∷ []
laneStep-U (r , _) (instEmit (mark outerOpen) _)   u = u ∷ []
laneStep-U (r , _) (instEmit (mark outerClose) _)  u = u ∷ []
laneStep-U (r , _) (instEmit (mark laneStart) _)   u = u ∷ []
laneStep-U (r , _) (instEmit (mark carry) _)       u = u ∷ []
laneStep-U (r , _) (instEmit (mark burstEnd) _)    u = u ∷ []
laneStep-U (r , _) (instEmit (mark outerDone) _)   u = u ∷ []
laneStep-U (r , _) (instEmit (mark subscribed) _)  u = u ∷ []
laneStep-U (r , _) (instEmit (mark completed) _)   u = u ∷ []

------------------------------------------------------------------------
-- A flatMap's scan

cut-U : ∀ {B} k n s → All (U {B}) (proj₂ (cut k n s))
cut-U k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | _     = []
... | false | true  = []
... | false | false = stops-U k n

unpark-U : ∀ {B} n s → All (U {B}) (proj₂ (unpark n s))
unpark-U n s with anyHolds (Flat.at s) (Flat.live s)
... | true  = []
... | false = stops-U (Flat.parked s) n

arrive-U : ∀ {B} op n s → All (U {B}) (proj₂ (arrive op n s))
arrive-U (mergeᶠ (just k)) n s with Flat.active s <ᵇ k
... | true  = []
... | false = []
arrive-U (mergeᶠ nothing) n s = []
arrive-U switchᶠ          n s = cut-U (Flat.lanes s) n (record s { active = 0 ; lanes = 0 })
arrive-U exhaustᶠ         n s = []

ended-U : ∀ {B} k n s → All (U {B}) (proj₂ (ended k n s))
ended-U k n s with isZero (Flat.queue s)
... | false = []
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = []
...   | false = cut-U (k + Flat.held s) n (record s { held = 0 })

burstOver-U : ∀ {B} b n s → All (U {B}) (proj₂ (burstOver b n s))
burstOver-U true  n s = []
burstOver-U false n s = cut-U (Flat.held s) n (record s { held = 0 })

left-U : ∀ {B} n s → All (U {B}) (proj₂ (left n s))
left-U n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = []
... | false = cut-U (Flat.outer s) n (record s { outer = 0 })

stopped-U : ∀ {B} b n s k → All (U {B}) (proj₂ (stopped b n s k))
stopped-U b n s zero    = []
stopped-U b n s (suc _) = tt ∷ []

begun-U : ∀ {B} b n s → All (U {B}) (proj₂ (begun b n s))
begun-U b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
... | true  = []
... | false = tt ∷ []

overed-U : ∀ {B} n s → All (U {B}) (proj₂ (overed n s))
overed-U n s with Flat.spent s
... | true  = []
... | false = tt ∷ []

onMark-U : ∀ {B} op b s m n → U {B} (instEmit (mark m) n) → All U (proj₂ (onMark {B} op b s m n))
onMark-U op b s begin      n _ = begun-U b n s
onMark-U op b s stop       n _ = stopped-U b n s (if Flat.spent s then 0 else share b s)
onMark-U op b s over       n _ = overed-U n s
onMark-U op b s carry      n _ = []
onMark-U op b s outerOpen  n _ = arrive-U op n s
onMark-U op b s outerClose n _ = []
onMark-U op b s laneStart  n _ = []
onMark-U op b s laneDone   n _ =
  ended-U (Flat.acc s ⊓ Flat.lanes s) n
    (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0
              ; popping = not (isZero (Flat.queue s)) ; dead = true })
onMark-U op b s burstEnd   n _ = burstOver-U (isZero (Flat.held s) ∨ Flat.dead s) n s
onMark-U op b s outerDone  n _ = left-U n (record s { finished = true })
onMark-U op b s subscribed n _ = tt ∷ []
onMark-U op b s completed  n ()

react-U : ∀ {B} op (acc : Out B) x → InOK x → All U (proj₂ (react op acc x))
react-U op (s , _) (just (inj₁ (b , instEmit (value _) _))) _ = tt ∷ []
react-U op (s , _) (just (inj₁ (b , instEmit (mark m) n)))  u = onMark-U op b s m n u
react-U {B} op (s , _) (just (inj₂ (i , r)))                _ = unpark-U {B} root (record s { live = setAt i r (Flat.live s) })
react-U op (s , _) nothing                                  _ = []

------------------------------------------------------------------------
-- The plumbing

module _ (n : ℕ) where

  concat-G : ∀ {Δ X} {env : DenEnv Δ} {Q : X → Set} {s t : E Δ X} → Good n env s Q → Good n env t Q → Good n env (concatˢ s t) Q
  concat-G {env = env} {Q} {s} {t} gs gt = g-flat′ pick
    where
      pick : ∀ {b} → Good n env (if b then s else t) Q
      pick {true}  = gs
      pick {false} = gt

  each-G : ∀ {Δ X Y} {env : DenEnv Δ} {P : X → Set} {Q : Y → Set} {f : X → List Y} {s : E Δ X} → Good n env s P
         → (∀ {x} → P x → All Q (f x)) → Good n env (each f s) Q
  each-G gs hf = g-flat gs (λ px → g-of (hf px))

  render-G : ∀ {Δ A} {env : DenEnv Δ} (x : Bool × Tag A) → Good n env (render {Δ} {A} x) U
  render-G (false , val _) = g-of (tt ∷ [])
  render-G (true  , val _) = g-flat′ (g-of (tt ∷ tt ∷ tt ∷ []))
  render-G (true  , cdone) = g-map′ tt
  render-G (false , cdone) = g-empty
  render-G (false , tick)  = g-empty
  render-G (true  , tick)  = g-empty

  piece-G : ∀ {Θ B} {env : DenEnv Θ} {h : Den (IE B)} k i → Outs U h → Good n (h ∷ env) (piece k i) U
  piece-G lanePart  zero                hh = g-of (tt ∷ [])
  piece-G burstPart zero                hh = g-of (tt ∷ [])
  piece-G lanePart  (suc zero)          hh = g-sem hh
  piece-G burstPart (suc zero)          hh = g-sem hh
  piece-G lanePart  (suc (suc zero))    hh = g-of (tt ∷ [])
  piece-G burstPart (suc (suc zero))    hh = g-empty
  piece-G lanePart  (suc (suc (suc _))) hh = g-empty
  piece-G burstPart (suc (suc (suc _))) hh = g-empty

  counted-G : ∀ {Θ B} {env : DenEnv Θ} {s : E Θ (IE B)} → Good n env s U → Good n env (counted s) U
  counted-G g = each-G (g-scan {R = λ acc → All U (proj₂ acc)} g [] (λ {acc} {e} _ u → laneStep-U acc e u)) (λ r → r)

  laneˢ-G : ∀ {Θ B} {env : DenEnv Θ} {x : E Θ (IE B)} → Good n env x U → Good n env (laneˢ x) U
  laneˢ-G gx = g-take (g-flat′ λ {k} → g-conn (g-flat′ gx) (λ h hh → counted-G (g-flat′ (λ {i} → piece-G k i hh))))

  closer-G : ∀ {Δ A B} {env : DenEnv Δ} {h : Den (IE A)} → Good n (h ∷ env) (closer {Δ} {A} {B}) U
  closer-G = concat-G (each-G g-top (λ {x} _ → closing-U x)) (g-of (tt ∷ []))

  annotate-G : ∀ {Δ A} {env : DenEnv Δ} {s : E Δ (IE A)} → Good n env s U → Good n env (annotate s) AnnOK
  annotate-G g =
    g-map {P = λ acc → AnnOK (proj₂ acc)}
      (g-scan {P = JustOK} {R = λ acc → AnnOK (proj₂ acc)}
        (g-conn {P = JustOK} (g-map {Q = JustOK} g (λ u → u)) (λ h hh → concat-G (g-sem hh) (g-of (tt ∷ []))))
        tt (λ {acc} {x} _ j → annStep-U acc x j))
      (λ r → r)

  reader-G : ∀ {Δ A} {env : DenEnv Δ} {s : E Δ (AIE A)} → Good n env s AnnOK → Good n env (reader s) U
  reader-G g = each-G (g-scan {R = λ acc → All U (proj₂ acc)} g [] (λ {acc} {x} _ a → joinStep-U acc x a)) (λ r → r)

  module _ {Δ A B} {env : DenEnv Δ} {h₁ : Den (IE A)} {h₂ h₃ : Den (IE B)} (u₁ : Outs U h₁) (u₂ : Outs U h₂) (u₃ : Outs U h₃) where

    branch-G : ∀ b → Good n (h₃ ∷ h₂ ∷ h₁ ∷ env) (branch b) U
    branch-G outerB = g-map (g-sem u₁) (λ {e} u → opening-U e u)
    branch-G laneB  = g-sem u₃
    branch-G closeB = g-sem u₂

    fed-G : ∀ {tk} b → Good n (h₃ ∷ h₂ ∷ h₁ ∷ env) (fed tk b) InOK
    fed-G true  = g-map′ tt
    fed-G false = concat-G (g-flat′ (λ {b} → g-map {Q = InOK} (branch-G b) (λ u → u))) (g-of (tt ∷ []))

    combined-G : ∀ op {tk} → Good n (h₃ ∷ h₂ ∷ h₁ ∷ env) (combined op tk) U
    combined-G op = each-G
      (g-scan {P = InOK} {R = λ acc → All U (proj₂ acc)} (g-take (g-flat′ (λ {b} → fed-G b))) []
        (λ {acc} {x} _ i → react-U op acc x i))
      (λ r → r)

  flatMapˢ-G : ∀ {Δ A B} op {tk} {g : A → E (IE B ∷ IE A ∷ Δ) (IE B)} {s : E Δ (IE A)} {env : DenEnv Δ} → Good n env s U
             → (∀ {a h₁ h₂} → Good n (h₂ ∷ h₁ ∷ env) (g a) U) → Good n env (flatMapˢ op tk g s) U
  flatMapˢ-G op gs hg =
    g-conn gs λ h₁ u₁ → g-conn closer-G λ h₂ u₂ → g-conn (g-flat′ (laneˢ-G hg)) λ h₃ u₃ → combined-G u₁ u₂ u₃ op

------------------------------------------------------------------------
-- The elaboration

-- Every connect in scope shows no completion mark.
EnvOK : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Δ → Set₁
EnvOK {Γ} ρ env = ∀ {Y} (i : Y ∈ Γ) → Outs AnnOK (lookup env (ρ (∈-map⁺ AIE i)))

ext-ok : ∀ {Γ Δ X} (ρ : ∀ {Y} → Y ∈ L.map AIE Γ → Y ∈ Δ) {env : DenEnv Δ} {h : Den (AIE X)} → EnvOK ρ env → Outs AnnOK h
       → EnvOK {X ∷ Γ} (ext ρ) (h ∷ env)
ext-ok ρ ok hh (here refl) = hh
ext-ok ρ ok hh (there i)   = ok i

mutual
  elab-U : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) {env : DenEnv Δ} → EnvOK ρ env
         → Outs U (approx n (elab ρ o) env)
  elab-U n ρ o {env} ok = sound {n} {env = env} {s = elab ρ o} {Q = U} (elab-G n ρ o ok)

  elab-G : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) {env : DenEnv Δ} → EnvOK ρ env
         → Good n env (elab ρ o) U
  elab-G n ρ (cold c)          ok = g-flat′ (λ {x} → render-G n x)
  elab-G n ρ empty             ok = g-empty
  elab-G n ρ (of xs)           ok = g-of (vals-U xs)
  elab-G n ρ (map f s)         ok = g-map (g-sem (elab-U n ρ s ok)) (λ {e} u → mapIE-U f e u)
  elab-G n ρ (scan f z s)      ok =
    g-map {P = λ acc → U (proj₂ acc)} (g-scan {R = λ acc → U (proj₂ acc)} (g-sem (elab-U n ρ s ok)) tt (λ {acc} {e} _ u → scanIE-U f acc e u)) (λ u → u)
  elab-G n ρ (takeWhile i p s) ok = g-take (g-sem (elab-U n ρ s ok))
  elab-G n ρ (flatMap op f s)  ok =
    flatMapˢ-G n op (g-sem (elab-U n ρ s ok)) (λ {a} → g-sem (elab-U n (λ i → there (there (ρ i))) (f a) (λ i → ok i)))
  elab-G n ρ (connect s b)     ok =
    g-conn {P = AnnOK} (annotate-G n (g-sem (elab-U n ρ s ok))) (λ h hh → g-sem (elab-U n (ext ρ) b (ext-ok ρ ok hh)))
  elab-G n ρ (connected i)     ok = reader-G n (g-sem (ok i))
  elab-G zero    ρ (defer l)   ok = g-sem (outs-⊥ {P = U})
  elab-G (suc n) ρ (defer l)   ok = g-sem (outs-defer (elab-U n ρ (Later.force l) ok))

-- THE CORE NEVER COMPLETES ALOUD.
core-unfinished : ∀ n {A} (o : SObs [] A) {p k a} → enter (approx n (elab (λ i → i) (plain o)) []) p k (out a) → T (unfinished a)
core-unfinished n o = elab-U n (λ i → i) (plain o) (λ ())
