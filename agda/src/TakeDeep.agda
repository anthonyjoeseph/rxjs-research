-- TAKE IN THE DEEP EMBEDDING: expansion with per-leaf horizons.
--
-- A merge/map tree over one source where any FLAT branch may carry takes:
-- each root-to-leaf path contributes its composed function together with a
-- HORIZON — how many source instants the path survives (takes along the
-- path cap it; no take ⇒ unbounded). The normal form generalizes Deep's
-- `expand`: per instant, the block holds the values of the still-live
-- leaves, and leaves die as their horizons run out. The theorem:
--
--   batchSpec ⟦ e ⟧ ≡ specH (funsH e) source
--
-- one batch per source instant containing every live leaf's value (and no
-- batch at all once every leaf has expired). TakeDiamond's law
-- batchSpec (merge a (take n a)) is recovered as the two-leaf instance.
module TakeDeep where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Obs
open import Exp
open import Deep
open import MergeMap
open import TakeDiamond

-- horizons --------------------------------------------------------------------

Horizon : Set
Horizon = Maybe ℕ  -- nothing = never closes; just n = n more instants

activeH : Horizon → Bool
activeH nothing        = true
activeH (just zero)    = false
activeH (just (suc _)) = true

tickH : Horizon → Horizon
tickH nothing        = nothing
tickH (just zero)    = just zero
tickH (just (suc n)) = just n

capH : ℕ → Horizon → Horizon
capH k nothing  = just k
capH k (just m) = just (min k m)

HFn : Set → Set → Set
HFn A B = (A → B) × Horizon

-- one instant's live values
applyH : {A B : Set} → List (HFn A B) → A → List B
applyH []             v = []
applyH ((f , h) ∷ fs) v =
  if activeH h then (f v ∷ applyH fs v) else applyH fs v

tickAll : {A B : Set} → List (HFn A B) → List (HFn A B)
tickAll = map (λ fh → (fst fh , tickH (snd fh)))

compAll : {A B C : Set} → (B → C) → List (HFn A B) → List (HFn A C)
compAll h = map (λ fh → ((h ∘ fst fh) , snd fh))

capAll : {A B : Set} → ℕ → List (HFn A B) → List (HFn A B)
capAll k = map (λ fh → (fst fh , capH k (snd fh)))

-- the normal form and the expected batches
expandH : {A B : Set} → List (HFn A B) → TimedObs A → TimedObs B
expandH fs []             = []
expandH fs ((t , v) ∷ xs) =
  map (λ w → (t , w)) (applyH fs v) ++ expandH (tickAll fs) xs

prependBatch : {A : Set} → Time → List A → TimedObs (List A)
             → TimedObs (List A)
prependBatch t []       rest = rest
prependBatch t (w ∷ ws) rest = (t , w ∷ ws) ∷ rest

specH : {A B : Set} → List (HFn A B) → TimedObs A → TimedObs (List B)
specH fs []             = []
specH fs ((t , v) ∷ xs) =
  prependBatch t (applyH fs v) (specH (tickAll fs) xs)

-- list bookkeeping -------------------------------------------------------------

applyH-++ : {A B : Set} (fs ks : List (HFn A B)) (v : A)
  → applyH (fs ++ ks) v ≡ applyH fs v ++ applyH ks v
applyH-++ []             ks v = refl
applyH-++ ((f , h) ∷ fs) ks v with activeH h
... | true  = cong (_∷_ (f v)) (applyH-++ fs ks v)
... | false = applyH-++ fs ks v

tickAll-++ : {A B : Set} (fs ks : List (HFn A B))
  → tickAll (fs ++ ks) ≡ tickAll fs ++ tickAll ks
tickAll-++ = map-++ (λ fh → (fst fh , tickH (snd fh)))

applyH-comp : {A B C : Set} (h : B → C) (fs : List (HFn A B)) (v : A)
  → applyH (compAll h fs) v ≡ map h (applyH fs v)
applyH-comp h []              v = refl
applyH-comp h ((f , hz) ∷ fs) v with activeH hz
... | true  = cong (_∷_ (h (f v))) (applyH-comp h fs v)
... | false = applyH-comp h fs v

tickAll-comp : {A B C : Set} (h : B → C) (fs : List (HFn A B))
  → tickAll (compAll h fs) ≡ compAll h (tickAll fs)
tickAll-comp h []              = refl
tickAll-comp h ((f , hz) ∷ fs) =
  cong (_∷_ ((h ∘ f) , tickH hz)) (tickAll-comp h fs)

-- AllAfter machinery for expanded streams ---------------------------------------

allAfter-++ : {A : Set} {t₀ : Time} {xs ys : TimedObs A}
  → AllAfter t₀ xs → AllAfter t₀ ys → AllAfter t₀ (xs ++ ys)
allAfter-++ aa[]        ay = ay
allAfter-++ (aa∷ lt ax) ay = aa∷ lt (allAfter-++ ax ay)

allAfter-vals-block : {A : Set} {t₀ t : Time}
  → timeLt t₀ t ≡ true → (ws : List A)
  → AllAfter t₀ (map (λ w → (t , w)) ws)
allAfter-vals-block lt []       = aa[]
allAfter-vals-block lt (w ∷ ws) = aa∷ lt (allAfter-vals-block lt ws)

expandH-allAfter : {A B : Set} {t₀ : Time} (fs : List (HFn A B))
  (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (expandH fs xs)
expandH-allAfter fs []             aa[]       = aa[]
expandH-allAfter fs ((t , v) ∷ xs) (aa∷ lt a) =
  allAfter-++ (allAfter-vals-block lt (applyH fs v))
              (expandH-allAfter (tickAll fs) xs a)

allAfter-headLeq : {A : Set} {t₀ : Time} {zs : TimedObs A}
  → AllAfter t₀ zs → HeadLeqB t₀ zs ≡ true
allAfter-headLeq aa[] = refl
allAfter-headLeq {t₀ = t₀} (aa∷ {t = t₁} lt _) = timeLt⇒timeLeq t₀ t₁ lt

allAfter-headGt : {A : Set} {t₀ : Time} {zs : TimedObs A}
  → AllAfter t₀ zs → HeadGtB t₀ zs ≡ true
allAfter-headGt aa[]           = refl
allAfter-headGt (aa∷ lt _)     = lt

headLeq-vals-++ : {A : Set} (t : Time) (ws : List A) (E : TimedObs A)
  → AllAfter t E
  → HeadLeqB t (map (λ w → (t , w)) ws ++ E) ≡ true
headLeq-vals-++ t []       E a = allAfter-headLeq a
headLeq-vals-++ t (w ∷ ws) E _ = timeLeq-refl t

-- merging expansions fuses the leaf lists ---------------------------------------

pull-left-vals : {A : Set} (t : Time) (ws : List A) (M R : TimedObs A)
  → HeadLeqB t R ≡ true
  → mergeT (map (λ w → (t , w)) ws ++ M) R
  ≡ map (λ w → (t , w)) ws ++ mergeT M R
pull-left-vals t []       M R  _ = refl
pull-left-vals t (w ∷ ws) M [] _ rewrite mergeT-idr M = refl
pull-left-vals t (w ∷ ws) M ((tr , u) ∷ rs) hl rewrite hl =
  cong (_∷_ (t , w)) (pull-left-vals t ws M ((tr , u) ∷ rs) hl)

expandH-split : {A B : Set} (fs ks : List (HFn A B)) (t : Time) (v : A)
  (xs : TimedObs A)
  → expandH (fs ++ ks) ((t , v) ∷ xs)
  ≡ map (λ w → (t , w)) (applyH fs v)
    ++ (map (λ w → (t , w)) (applyH ks v)
        ++ expandH (tickAll fs ++ tickAll ks) xs)
expandH-split fs ks t v xs =
  trans (cong₂ (λ a b → map (λ w → (t , w)) a ++ expandH b xs)
          (applyH-++ fs ks v) (tickAll-++ fs ks))
 (trans (cong (_++ expandH (tickAll fs ++ tickAll ks) xs)
          (map-++ (λ w → (t , w)) (applyH fs v) (applyH ks v)))
        (++-assoc (map (λ w → (t , w)) (applyH fs v))
                  (map (λ w → (t , w)) (applyH ks v))
                  (expandH (tickAll fs ++ tickAll ks) xs)))

merge-expandH : {A B : Set} (fs ks : List (HFn A B)) (xs : TimedObs A)
  → StrictMono xs
  → mergeT (expandH fs xs) (expandH ks xs) ≡ expandH (fs ++ ks) xs
merge-expandH fs ks [] _ = refl
merge-expandH fs ks ((t , v) ∷ xs) m =
  trans (pull-left-vals t (applyH fs v) (expandH (tickAll fs) xs)
          (expandH ks ((t , v) ∷ xs))
          (headLeq-vals-++ t (applyH ks v) (expandH (tickAll ks) xs)
            (expandH-allAfter (tickAll ks) xs (strictMono-allAfter m))))
 (trans (cong (_++_ (map (λ w → (t , w)) (applyH fs v)))
          (pull-right-vals t (applyH ks v) (expandH (tickAll fs) xs)
            (expandH (tickAll ks) xs)
            (allAfter-headGt (expandH-allAfter (tickAll fs) xs
              (strictMono-allAfter m)))))
 (trans (cong (λ z → map (λ w → (t , w)) (applyH fs v)
                     ++ (map (λ w → (t , w)) (applyH ks v) ++ z))
          (merge-expandH (tickAll fs) (tickAll ks) xs (mono-tail m)))
        (sym (expandH-split fs ks t v xs))))

-- map composes onto every leaf --------------------------------------------------

mapT-vals-block : {A B : Set} (h : A → B) (t : Time) (ws : List A)
  → mapT h (map (λ w → (t , w)) ws) ≡ map (λ w → (t , w)) (map h ws)
mapT-vals-block h t []       = refl
mapT-vals-block h t (w ∷ ws) = cong (_∷_ (t , h w)) (mapT-vals-block h t ws)

mapT-expandH : {A B C : Set} (h : B → C) (fs : List (HFn A B))
  (xs : TimedObs A)
  → mapT h (expandH fs xs) ≡ expandH (compAll h fs) xs
mapT-expandH h fs []             = refl
mapT-expandH h fs ((t , v) ∷ xs) =
  trans (mapT-++ h (map (λ w → (t , w)) (applyH fs v))
          (expandH (tickAll fs) xs))
        (cong₂ _++_
          (trans (mapT-vals-block h t (applyH fs v))
                 (cong (map (λ w → (t , w))) (sym (applyH-comp h fs v))))
          (trans (mapT-expandH h (tickAll fs) xs)
                 (cong (λ z → expandH z xs) (sym (tickAll-comp h fs)))))

-- take caps the (single) leaf's horizon ------------------------------------------

takeT-nil : {A : Set} (k : ℕ) → takeT {A} k [] ≡ []
takeT-nil zero    = refl
takeT-nil (suc k) = refl

min-0r : (k : ℕ) → min k 0 ≡ 0
min-0r zero    = refl
min-0r (suc k) = refl

expandH-dead : {A B : Set} (f : A → B) (xs : TimedObs A)
  → expandH ((f , just zero) ∷ []) xs ≡ []
expandH-dead f []             = refl
expandH-dead f ((t , v) ∷ xs) = expandH-dead f xs

take-cap : {A B : Set} (k : ℕ) (f : A → B) (h : Horizon) (xs : TimedObs A)
  → takeT k (expandH ((f , h) ∷ []) xs)
  ≡ expandH ((f , capH k h) ∷ []) xs
take-cap zero    f h []       = refl
take-cap (suc k) f h []       = refl
take-cap k f (just zero) ((t , v) ∷ xs)
  rewrite min-0r k
        | expandH-dead f ((t , v) ∷ xs)
  = takeT-nil k
take-cap zero f nothing ((t , v) ∷ xs) =
  sym (expandH-dead f ((t , v) ∷ xs))
take-cap zero f (just (suc m)) ((t , v) ∷ xs) =
  sym (expandH-dead f ((t , v) ∷ xs))
take-cap (suc k) f nothing ((t , v) ∷ xs) =
  cong (_∷_ (t , f v)) (take-cap k f nothing xs)
take-cap (suc k) f (just (suc m)) ((t , v) ∷ xs) =
  cong (_∷_ (t , f v)) (take-cap k f (just m) xs)

-- batching an expansion: one batch per instant with live leaves ------------------

specH-allAfter : {A B : Set} {t₀ : Time} (fs : List (HFn A B))
  (xs : TimedObs A)
  → AllAfter t₀ xs → AllAfter t₀ (specH fs xs)
specH-allAfter fs []             aa[]       = aa[]
specH-allAfter fs ((t , v) ∷ xs) (aa∷ lt a) with applyH fs v
... | []       = specH-allAfter (tickAll fs) xs a
... | (w ∷ ws) = aa∷ lt (specH-allAfter (tickAll fs) xs a)

join-far-allAfter : {A : Set} (t : Time) (vs : List A)
  {S : TimedObs (List A)}
  → AllAfter t S → joinHead t vs S ≡ (t , vs) ∷ S
join-far-allAfter t vs aa[] = refl
join-far-allAfter t vs (aa∷ {t = t₁} lt _)
  rewrite timeLt⇒timeEq-false t t₁ lt = refl

batch-expandH : {A B : Set} (fs : List (HFn A B)) (xs : TimedObs A)
  → StrictMono xs
  → batchSpec (expandH fs xs) ≡ specH fs xs
batch-expandH fs [] _ = refl
batch-expandH fs ((t , v) ∷ xs) m with applyH fs v
... | []       = batch-expandH (tickAll fs) xs (mono-tail m)
... | (w ∷ ws) =
  trans (batch-cons-block t w ws (expandH (tickAll fs) xs))
 (trans (cong (joinHead t (w ∷ ws))
          (batch-expandH (tickAll fs) xs (mono-tail m)))
        (join-far-allAfter t (w ∷ ws)
          (specH-allAfter (tickAll fs) xs (strictMono-allAfter m))))

-- the fragment: merge/map trees whose take-carrying branches are flat -------------

data FlatOver (i : ℕ) : Exp → Set where
  fo-src  : FlatOver i (srcE i)
  fo-map  : {g : Val → Val} {e : Exp}
          → FlatOver i e → FlatOver i (mapE g e)
  fo-take : {k : ℕ} {e : Exp}
          → FlatOver i e → FlatOver i (takeE k e)

data DTOver (i : ℕ) : Exp → Set where
  dt-flat  : {e : Exp} → FlatOver i e → DTOver i e
  dt-map   : {g : Val → Val} {e : Exp}
           → DTOver i e → DTOver i (mapE g e)
  dt-merge : {a b : Exp}
           → DTOver i a → DTOver i b → DTOver i (mergeE a b)

-- the leaves: composed function + horizon per root-to-leaf path
funsH : Exp → List (HFn Val Val)
funsH (srcE i)      = ((λ v → v) , nothing) ∷ []
funsH (mapE g e)    = compAll g (funsH e)
funsH (takeE k e)   = capAll k (funsH e)
funsH (mergeE a b)  = funsH a ++ funsH b
funsH emptyE        = []
funsH (ofE _ _)     = []
funsH (concatE _ _) = []

flatFn : Exp → (Val → Val)
flatFn (mapE g e)  = g ∘ flatFn e
flatFn (takeE _ e) = flatFn e
flatFn _           = λ v → v

flatHz : Exp → Horizon
flatHz (mapE _ e)  = flatHz e
flatHz (takeE k e) = capH k (flatHz e)
flatHz _           = nothing

flat-funsH : {i : ℕ} {e : Exp} → FlatOver i e
  → funsH e ≡ (flatFn e , flatHz e) ∷ []
flat-funsH fo-src      = refl
flat-funsH (fo-map d)  rewrite flat-funsH d = refl
flat-funsH (fo-take d) rewrite flat-funsH d = refl

expandH-id : {A : Set} (xs : TimedObs A)
  → expandH (((λ v → v) , nothing) ∷ []) xs ≡ xs
expandH-id []             = refl
expandH-id ((t , v) ∷ xs) = cong (_∷_ (t , v)) (expandH-id xs)

flat-denote : {i : ℕ} {e : Exp} (env : Env) → FlatOver i e
  → emits (⟦ e ⟧ env) ≡ expandH ((flatFn e , flatHz e) ∷ []) (emits (env i))
flat-denote env fo-src = sym (expandH-id _)
flat-denote {i} env (fo-map {g} {e} d) =
  trans (cong (mapT g) (flat-denote env d))
        (mapT-expandH g ((flatFn e , flatHz e) ∷ []) (emits (env i)))
flat-denote {i} env (fo-take {k} {e} d) =
  trans (cong (takeT k) (flat-denote env d))
        (take-cap k (flatFn e) (flatHz e) (emits (env i)))

dt-denote : {i : ℕ} {e : Exp} (env : Env) → DTOver i e
  → StrictMono (emits (env i))
  → emits (⟦ e ⟧ env) ≡ expandH (funsH e) (emits (env i))
dt-denote {i} env (dt-flat {e} d) m =
  trans (flat-denote env d)
        (cong (λ z → expandH z (emits (env i))) (sym (flat-funsH d)))
dt-denote {i} env (dt-map {g} {e} d) m =
  trans (cong (mapT g) (dt-denote env d m))
        (mapT-expandH g (funsH e) (emits (env i)))
dt-denote {i} env (dt-merge {a} {b} da db) m =
  trans (cong₂ mergeT (dt-denote env da m) (dt-denote env db m))
        (merge-expandH (funsH a) (funsH b) (emits (env i)) m)

-- THE THEOREM: any merge/map tree with takes on flat branches, at any
-- depth, batches to one batch per source instant holding every live leaf's
-- value — and no batch once every leaf's horizon has expired
dt-diamond : (i : ℕ) (e : Exp) (env : Env)
  → DTOver i e
  → StrictMono (emits (env i))
  → batchSpec (emits (⟦ e ⟧ env)) ≡ specH (funsH e) (emits (env i))
dt-diamond i e env d m =
  trans (cong batchSpec (dt-denote env d m))
        (batch-expandH (funsH e) (emits (env i)) m)

impl-dt-diamond : (i : ℕ) (e : Exp) (env : Env)
  → DTOver i e
  → StrictMono (emits (env i))
  → batchImpl (emits (⟦ e ⟧ env)) ≡ specH (funsH e) (emits (env i))
impl-dt-diamond i e env d m =
  trans (batchImpl-spec (emits (⟦ e ⟧ env))) (dt-diamond i e env d m)

-- sanity: TakeDiamond's law is the two-leaf instance -----------------------------

specH-take-two : {A : Set} (n : ℕ) (xs : TimedObs A)
  → specH (((λ v → v) , nothing) ∷ ((λ v → v) , just n) ∷ []) xs
  ≡ takeDiamondSpec n xs
specH-take-two zero    []             = refl
specH-take-two (suc n) []             = refl
specH-take-two zero    ((t , v) ∷ xs) =
  cong (_∷_ (t , v ∷ [])) (specH-take-two zero xs)
specH-take-two (suc n) ((t , v) ∷ xs) =
  cong (_∷_ (t , v ∷ v ∷ [])) (specH-take-two n xs)

dt-take-two : (i n : ℕ) (env : Env)
  → StrictMono (emits (env i))
  → batchSpec (emits (⟦ mergeE (srcE i) (takeE n (srcE i)) ⟧ env))
  ≡ takeDiamondSpec n (emits (env i))
dt-take-two i n env m =
  trans (dt-diamond i (mergeE (srcE i) (takeE n (srcE i))) env
          (dt-merge (dt-flat fo-src) (dt-flat (fo-take fo-src))) m)
        (specH-take-two n (emits (env i)))
