-- Observables with close times: an observable is its emission history plus
-- the instant it completes. Closes are what make concat and take definable
-- (concat subscribes its second argument at the first one's close; take
-- manufactures a close). Sources here are HOT: concat's second argument
-- misses everything at or before the pivot — the cold case (`of` under
-- concat, whose emissions move to the subscription instant) needs
-- subscription-time-parameterized denotations and is future work.
module Obs where

open import Prelude
open import Time
open import TimedObs
open import Sorting

record Obs (A : Set) : Set where
  constructor obs
  field
    emits : TimedObs A
    close : Time
open Obs public

-- the operators (defined with projections, not pattern matching, so they
-- reduce even on neutral arguments — proofs rely on this)

emptyO : {A : Set} → Obs A
emptyO = obs [] timeMin

ofO : {A : Set} → ℕ → List A → Obs A
ofO o vs = obs (map (λ v → ((0 , o) , v)) vs) (0 , o)

mapO : {A B : Set} → (A → B) → Obs A → Obs B
mapO f x = obs (mapT f (emits x)) (close x)

takeO : {A : Set} → ℕ → Obs A → Obs A
takeO n x = obs (takeT n (emits x)) (takeClose n (emits x) (close x))

mergeO : {A : Set} → Obs A → Obs A → Obs A
mergeO x y = obs (mergeT (emits x) (emits y)) (timeMax (close x) (close y))

concatO : {A : Set} → Obs A → Obs A → Obs A
concatO x y =
  obs (emits x ++ filterAfter (close x) (emits y))
      (timeMax (close x) (close y))

-- well-formedness: emissions are time-ordered and happen before the close
record WF {A : Set} (o : Obs A) : Set where
  constructor wf
  field
    sorted  : Sorted (emits o)
    bounded : BoundedBy (close o) (emits o)
open WF public

-- every operator preserves well-formedness ------------------------------------

wf-empty : {A : Set} → WF (emptyO {A})
wf-empty = wf sf[] bb[]

wf-of : {A : Set} (o : ℕ) (vs : List A) → WF (ofO o vs)
wf-of o vs =
  wf (sortedFrom-weaken (timeMin-least (0 , o)) (const-sortedFrom (0 , o) vs))
     (const-bounded (0 , o) vs)

wf-map : {A B : Set} (f : A → B) {x : Obs A} → WF x → WF (mapO f x)
wf-map f {x} (wf s b) =
  wf (mapT-sortedFrom f (emits x) s) (mapT-bounded f (emits x) b)

wf-take : {A : Set} (n : ℕ) {x : Obs A} → WF x → WF (takeO n x)
wf-take n {x} (wf s b) =
  wf (take-sortedFrom n (emits x) s) (take-bounded n (emits x) (close x) s b)

wf-merge : {A : Set} {x y : Obs A} → WF x → WF y → WF (mergeO x y)
wf-merge {A} {x} {y} (wf s₁ b₁) (wf s₂ b₂) =
  wf (merge-sortedFrom (emits x) (emits y) s₁ s₂)
     (merge-bounded (emits x) (emits y)
       (boundedBy-weaken (timeMax-left (close x) (close y)) b₁)
       (boundedBy-weaken (timeMax-right (close x) (close y)) b₂))

wf-concat : {A : Set} {x y : Obs A} → WF x → WF y → WF (concatO x y)
wf-concat {A} {x} {y} (wf s₁ b₁) (wf s₂ b₂) =
  wf (append-sortedFrom (emits x) (filterAfter (close x) (emits y))
       s₁ b₁ (filterAfter-from (close x) (emits y) s₂)
       (timeMin-least (close x)))
     (append-bounded (emits x) (filterAfter (close x) (emits y))
       (boundedBy-weaken (timeMax-left (close x) (close y)) b₁)
       (boundedBy-weaken (timeMax-right (close x) (close y))
         (filterAfter-bounded (close x) (emits y) b₂)))
