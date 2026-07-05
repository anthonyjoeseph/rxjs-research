-- THE ARBITRARY-DEPTH DIAMOND THEOREM.
--
-- For ANY expression built from srcE i / mapE / mergeE — a merge of a merge
-- of a merge of ..., nested to any depth, with maps anywhere — batching the
-- denotation produces exactly one batch per source instant, containing the
-- values of every leaf path in left-to-right order:
--
--   batchSpec ⟦ e ⟧ ≡ mapT (λ v → [ f₁ v , … , fₖ v ]) source
--
-- where f₁ … fₖ = funs e, the composed map-functions along each path from
-- the root to a source leaf. The two-way diamond is the depth-one instance
-- (funs = [id, id]). The proof is structural induction on the expression,
-- via a normal form: every such expression denotes `expand (funs e) source`.
module Deep where

open import Prelude
open import Time
open import TimedObs
open import Diamond
open import BatchImpl
open import Obs
open import Exp

-- a list of functions applied pointwise: the batch of one source instant
applyAll : {A B : Set} → List (A → B) → A → List B
applyAll fs v = map (λ f → f v) fs

-- the normal form: each source emission (t , v) becomes the block
-- [(t , f v) | f ∈ fs] — k simultaneous emissions, one per leaf path
expand : {A B : Set} → List (A → B) → TimedObs A → TimedObs B
expand fs []             = []
expand fs ((t , v) ∷ xs) = map (λ f → (t , f v)) fs ++ expand fs xs

-- small facts --------------------------------------------------------------

mergeT-idr : {A : Set} (xs : TimedObs A) → mergeT xs [] ≡ xs
mergeT-idr []       = refl
mergeT-idr (x ∷ xs) = refl

mapT-++ : {A B : Set} (h : A → B) (xs ys : TimedObs A)
        → mapT h (xs ++ ys) ≡ mapT h xs ++ mapT h ys
mapT-++ h []             ys = refl
mapT-++ h ((t , v) ∷ xs) ys = cong (_∷_ (t , h v)) (mapT-++ h xs ys)

mapT-block : {A B C : Set} (h : B → C) (t : Time) (v : A) (fs : List (A → B))
  → mapT h (map (λ f → (t , f v)) fs)
  ≡ map (λ f → (t , f v)) (map (λ f → h ∘ f) fs)
mapT-block h t v []       = refl
mapT-block h t v (f ∷ fs) = cong (_∷_ (t , h (f v))) (mapT-block h t v fs)

-- map commutes with expand ---------------------------------------------------

expand-map : {A B C : Set} (h : B → C) (fs : List (A → B)) (xs : TimedObs A)
  → mapT h (expand fs xs) ≡ expand (map (λ f → h ∘ f) fs) xs
expand-map h fs []             = refl
expand-map h fs ((t , v) ∷ xs) =
  trans (mapT-++ h (map (λ f → (t , f v)) fs) (expand fs xs))
        (cong₂ _++_ (mapT-block h t v fs) (expand-map h fs xs))

-- merge concatenates blocks: the block-pulling lemmas -------------------------

HeadLeqB : {A : Set} → Time → TimedObs A → Bool
HeadLeqB t []             = true
HeadLeqB t ((t′ , _) ∷ _) = timeLeq t t′

HeadGtB : {A : Set} → Time → TimedObs A → Bool
HeadGtB t []             = true
HeadGtB t ((t′ , _) ∷ _) = timeLt t t′

-- a block of emissions at time t at the head of merge's left argument is
-- emitted first (stability: ties go left)
pull-left-block : {A B : Set} (t : Time) (v : A) (fs : List (A → B))
                  (M R : TimedObs B)
  → HeadLeqB t R ≡ true
  → mergeT (map (λ f → (t , f v)) fs ++ M) R
  ≡ map (λ f → (t , f v)) fs ++ mergeT M R
pull-left-block t v []       M R  _ = refl
pull-left-block t v (f ∷ fs) M [] _ rewrite mergeT-idr M = refl
pull-left-block t v (f ∷ fs) M ((tr , w) ∷ rs) hl rewrite hl =
  cong (_∷_ (t , f v)) (pull-left-block t v fs M ((tr , w) ∷ rs) hl)

-- a block at time t at the head of merge's right argument is emitted before
-- a left argument whose emissions are all later
pull-right-block : {A B : Set} (t : Time) (v : A) (gs : List (A → B))
                   (M R : TimedObs B)
  → HeadGtB t M ≡ true
  → mergeT M (map (λ g → (t , g v)) gs ++ R)
  ≡ map (λ g → (t , g v)) gs ++ mergeT M R
pull-right-block t v []       M              R _  = refl
pull-right-block t v (g ∷ gs) []             R _  = refl
pull-right-block t v (g ∷ gs) ((tm , w) ∷ ms) R hg
  rewrite timeLt⇒timeLeq-flip-false t tm hg =
  cong (_∷_ (t , g v)) (pull-right-block t v gs ((tm , w) ∷ ms) R hg)

expand-headGt : {A B : Set} (f : A → B) (fs : List (A → B))
                (t : Time) (v : A) (xs : TimedObs A)
  → StrictMono ((t , v) ∷ xs)
  → HeadGtB t (expand (f ∷ fs) xs) ≡ true
expand-headGt f fs t v []              _            = refl
expand-headGt f fs t v ((t₁ , w) ∷ xs) (mono-∷ lt _) = lt

expand-block-++ : {A B : Set} (hs ks : List (A → B)) (t : Time) (v : A)
                  (xs : TimedObs A)
  → expand (hs ++ ks) ((t , v) ∷ xs)
  ≡ map (λ h → (t , h v)) hs
    ++ (map (λ h → (t , h v)) ks ++ expand (hs ++ ks) xs)
expand-block-++ hs ks t v xs =
  trans (cong (_++ expand (hs ++ ks) xs) (map-++ (λ h → (t , h v)) hs ks))
        (++-assoc (map (λ h → (t , h v)) hs) (map (λ h → (t , h v)) ks)
                  (expand (hs ++ ks) xs))

-- merging two expansions of the same source concatenates their functions
expand-merge : {A B : Set} (f : A → B) (fs : List (A → B))
               (g : A → B) (gs : List (A → B)) (xs : TimedObs A)
  → StrictMono xs
  → mergeT (expand (f ∷ fs) xs) (expand (g ∷ gs) xs)
  ≡ expand ((f ∷ fs) ++ (g ∷ gs)) xs
expand-merge f fs g gs [] _ = refl
expand-merge f fs g gs ((t , v) ∷ xs) m =
  trans (pull-left-block t v (f ∷ fs) (expand (f ∷ fs) xs)
          (expand (g ∷ gs) ((t , v) ∷ xs)) (timeLeq-refl t))
 (trans (cong (_++_ (map (λ h → (t , h v)) (f ∷ fs)))
          (pull-right-block t v (g ∷ gs) (expand (f ∷ fs) xs)
            (expand (g ∷ gs) xs) (expand-headGt f fs t v xs m)))
 (trans (cong (λ z → map (λ h → (t , h v)) (f ∷ fs)
                     ++ (map (λ h → (t , h v)) (g ∷ gs) ++ z))
          (expand-merge f fs g gs xs (mono-tail m)))
        (sym (expand-block-++ (f ∷ fs) (g ∷ gs) t v xs))))

-- batching an expansion ------------------------------------------------------

insert-into-join : {A : Set} (t : Time) (x : A) (ys : List A)
                   (S : TimedObs (List A))
  → insertBatch t x (joinHead t ys S) ≡ joinHead t (x ∷ ys) S
insert-into-join t x ys [] rewrite timeEq-refl t = refl
insert-into-join t x ys ((t″ , g) ∷ rest) with timeEq t t″
... | true  rewrite timeEq-refl t = refl
... | false rewrite timeEq-refl t = refl

batch-block : {A B : Set} (t : Time) (v : A) (g : A → B) (gs : List (A → B))
              (rest : TimedObs B)
  → batchSpec (map (λ h → (t , h v)) (g ∷ gs) ++ rest)
  ≡ joinHead t (applyAll (g ∷ gs) v) (batchSpec rest)
batch-block t v g []        rest = insert-join t (g v) (batchSpec rest)
batch-block t v g (g′ ∷ gs) rest =
  trans (cong (insertBatch t (g v)) (batch-block t v g′ gs rest))
        (insert-into-join t (g v) (applyAll (g′ ∷ gs) v) (batchSpec rest))

join-far : {A : Set} (t t₁ : Time) (vs g : List A) (rest : TimedObs (List A))
  → timeEq t t₁ ≡ false
  → joinHead t vs ((t₁ , g) ∷ rest) ≡ (t , vs) ∷ (t₁ , g) ∷ rest
join-far t t₁ vs g rest ne rewrite ne = refl

-- batching an expansion of a strictly monotone source yields exactly one
-- batch per source instant: the pointwise application of every function
batch-expand : {A B : Set} (f : A → B) (fs : List (A → B)) (xs : TimedObs A)
  → StrictMono xs
  → batchSpec (expand (f ∷ fs) xs) ≡ mapT (applyAll (f ∷ fs)) xs
batch-expand f fs []             _        = refl
batch-expand f fs ((t , v) ∷ []) mono-one = batch-block t v f fs []
batch-expand f fs ((t , v) ∷ (t₁ , w) ∷ xs) (mono-∷ lt m) =
  trans (batch-block t v f fs (expand (f ∷ fs) ((t₁ , w) ∷ xs)))
 (trans (cong (joinHead t (applyAll (f ∷ fs) v))
          (batch-expand f fs ((t₁ , w) ∷ xs) m))
        (join-far t t₁ (applyAll (f ∷ fs) v) (applyAll (f ∷ fs) w)
          (mapT (applyAll (f ∷ fs)) xs) (timeLt⇒timeEq-false t t₁ lt)))

-- the merge/map fragment over one source --------------------------------------

data NonEmptyL {X : Set} : List X → Set where
  neL : {x : X} {xs : List X} → NonEmptyL (x ∷ xs)

map-ne : {X Y : Set} (h : X → Y) {l : List X} → NonEmptyL l → NonEmptyL (map h l)
map-ne h neL = neL

++-ne : {X : Set} {l r : List X} → NonEmptyL l → NonEmptyL (l ++ r)
++-ne neL = neL

-- the composed map-functions along each root-to-leaf path
funs : Exp → List (Val → Val)
funs (srcE i)      = (λ v → v) ∷ []
funs (mapE g e)    = map (λ f → g ∘ f) (funs e)
funs (mergeE a b)  = funs a ++ funs b
funs emptyE        = []
funs (ofE _ _)     = []
funs (takeE _ _)   = []
funs (concatE _ _) = []

-- expressions built from srcE i / mapE / mergeE only — arbitrary depth
data DiamondOver (i : ℕ) : Exp → Set where
  d-src   : DiamondOver i (srcE i)
  d-map   : {g : Val → Val} {e : Exp}
          → DiamondOver i e → DiamondOver i (mapE g e)
  d-merge : {a b : Exp}
          → DiamondOver i a → DiamondOver i b → DiamondOver i (mergeE a b)

funs-ne : {i : ℕ} {e : Exp} → DiamondOver i e → NonEmptyL (funs e)
funs-ne d-src               = neL
funs-ne (d-map {g} {e} d)   = map-ne (λ f → g ∘ f) (funs-ne d)
funs-ne (d-merge da db)     = ++-ne (funs-ne da)

expand-id : {A : Set} (xs : TimedObs A) → expand ((λ v → v) ∷ []) xs ≡ xs
expand-id []             = refl
expand-id ((t , v) ∷ xs) = cong (_∷_ (t , v)) (expand-id xs)

expand-merge′ : {A B : Set} (fs gs : List (A → B)) (xs : TimedObs A)
  → NonEmptyL fs → NonEmptyL gs → StrictMono xs
  → mergeT (expand fs xs) (expand gs xs) ≡ expand (fs ++ gs) xs
expand-merge′ (f ∷ fs) (g ∷ gs) xs neL neL m = expand-merge f fs g gs xs m

batch-expand′ : {A B : Set} (fs : List (A → B)) (xs : TimedObs A)
  → NonEmptyL fs → StrictMono xs
  → batchSpec (expand fs xs) ≡ mapT (applyAll fs) xs
batch-expand′ (f ∷ fs) xs neL m = batch-expand f fs xs m

-- the normal form theorem: every merge/map tree over source i denotes an
-- expansion of that source (structural induction over arbitrary depth)
expand-denote : (i : ℕ) (e : Exp) (env : Env)
  → DiamondOver i e
  → StrictMono (emits (env i))
  → emits (⟦ e ⟧ env) ≡ expand (funs e) (emits (env i))
expand-denote i .(srcE i) env d-src m = sym (expand-id (emits (env i)))
expand-denote i .(mapE g e) env (d-map {g} {e} d) m =
  trans (cong (mapT g) (expand-denote i e env d m))
        (expand-map g (funs e) (emits (env i)))
expand-denote i .(mergeE a b) env (d-merge {a} {b} da db) m =
  trans (cong₂ mergeT (expand-denote i a env da m)
                      (expand-denote i b env db m))
        (expand-merge′ (funs a) (funs b) (emits (env i))
          (funs-ne da) (funs-ne db) m)

-- THE THEOREM: any combination of merge and map over one source, nested to
-- any depth, batches to exactly one batch per source instant, containing
-- every leaf path's value in left-to-right order
deep-diamond : (i : ℕ) (e : Exp) (env : Env)
  → DiamondOver i e
  → StrictMono (emits (env i))
  → batchSpec (emits (⟦ e ⟧ env)) ≡ mapT (applyAll (funs e)) (emits (env i))
deep-diamond i e env d m =
  trans (cong batchSpec (expand-denote i e env d m))
        (batch-expand′ (funs e) (emits (env i)) (funs-ne d) m)

-- and the implementation port satisfies it too
impl-deep-diamond : (i : ℕ) (e : Exp) (env : Env)
  → DiamondOver i e
  → StrictMono (emits (env i))
  → batchImpl (emits (⟦ e ⟧ env)) ≡ mapT (applyAll (funs e)) (emits (env i))
impl-deep-diamond i e env d m =
  trans (batchImpl-spec (emits (⟦ e ⟧ env))) (deep-diamond i e env d m)

-- sanity: the two-way diamond is the depth-one instance
deep-diamond-two : (i : ℕ) (env : Env)
  → StrictMono (emits (env i))
  → batchSpec (emits (⟦ mergeE (srcE i) (srcE i) ⟧ env))
  ≡ mapT (λ v → v ∷ v ∷ []) (emits (env i))
deep-diamond-two i env m =
  deep-diamond i (mergeE (srcE i) (srcE i)) env (d-merge d-src d-src) m
