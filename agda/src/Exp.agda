-- The deep embedding: "batchSimultaneous behaves correctly for ANY
-- combination of the primitives" is a quantification over programs, so
-- programs must be data. Theorems about all combinations — at any nesting
-- depth — are structural inductions on Exp.
module Exp where

open import Prelude
open import Time
open import TimedObs
open import Obs
open import Diamond
open import BatchImpl

Val : Set
Val = ℕ

data Exp : Set where
  srcE    : ℕ → Exp                  -- a root source, by index
  emptyE  : Exp
  ofE     : ℕ → List Val → Exp       -- origin + sync values (the origin
                                     -- discipline: each occurrence owns its
                                     -- subscription instant (0 , origin))
  mapE    : (Val → Val) → Exp → Exp
  takeE   : ℕ → Exp → Exp
  mergeE  : Exp → Exp → Exp
  concatE : Exp → Exp → Exp

-- an environment assigns every root source its observable
Env : Set
Env = ℕ → Obs Val

⟦_⟧ : Exp → Env → Obs Val
⟦ srcE i      ⟧ env = env i
⟦ emptyE      ⟧ env = emptyO
⟦ ofE o vs    ⟧ env = ofO o vs
⟦ mapE f e    ⟧ env = mapO f (⟦ e ⟧ env)
⟦ takeE n e   ⟧ env = takeO n (⟦ e ⟧ env)
⟦ mergeE a b  ⟧ env = mergeO (⟦ a ⟧ env) (⟦ b ⟧ env)
⟦ concatE a b ⟧ env = concatO (⟦ a ⟧ env) (⟦ b ⟧ env)

-- ANY combination of the primitives, nested to ANY depth, denotes a
-- well-formed observable: time-ordered emissions, all before the close.
-- One case per primitive; each case is the operator's preservation theorem.
denote-wf : (e : Exp) (env : Env)
  → ((i : ℕ) → WF (env i))
  → WF (⟦ e ⟧ env)
denote-wf (srcE i)      env wfe = wfe i
denote-wf emptyE        env wfe = wf-empty
denote-wf (ofE o vs)    env wfe = wf-of o vs
denote-wf (mapE f e)    env wfe = wf-map f (denote-wf e env wfe)
denote-wf (takeE n e)   env wfe = wf-take n (denote-wf e env wfe)
denote-wf (mergeE a b)  env wfe =
  wf-merge (denote-wf a env wfe) (denote-wf b env wfe)
denote-wf (concatE a b) env wfe =
  wf-concat (denote-wf a env wfe) (denote-wf b env wfe)

-- the anchor law over the syntax: for any expression whose denotation is
-- strictly monotone, batching its self-merge doubles every value — and the
-- implementation port agrees
diamond-exp : (e : Exp) (env : Env)
  → StrictMono (emits (⟦ e ⟧ env))
  → batchSpec (emits (⟦ mergeE e e ⟧ env)) ≡ mapT dbl (emits (⟦ e ⟧ env))
diamond-exp e env m = diamond (emits (⟦ e ⟧ env)) m

impl-diamond-exp : (e : Exp) (env : Env)
  → StrictMono (emits (⟦ e ⟧ env))
  → batchImpl (emits (⟦ mergeE e e ⟧ env)) ≡ mapT dbl (emits (⟦ e ⟧ env))
impl-diamond-exp e env m = impl-diamond (emits (⟦ e ⟧ env)) m

-- the origin discipline at work: all values of one `of` are simultaneous
-- (one batch), and distinct occurrences can never be simultaneous
const-batch : {A : Set} (t : Time) (v : A) (vs : List A)
  → batchSpec (map (λ w → (t , w)) (v ∷ vs)) ≡ (t , v ∷ vs) ∷ []
const-batch t v []       = refl
const-batch t v (w ∷ ws) rewrite const-batch t w ws | timeEq-refl t = refl

of-batch : (o : ℕ) (v : Val) (vs : List Val) (env : Env)
  → batchSpec (emits (⟦ ofE o (v ∷ vs) ⟧ env)) ≡ ((0 , o) , v ∷ vs) ∷ []
of-batch o v vs env = const-batch (0 , o) v vs
