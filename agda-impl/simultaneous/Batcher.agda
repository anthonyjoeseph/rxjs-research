{-# OPTIONS --guardedness #-}

-- THE BATCHER ENDS WITH WHAT IT BATCHES: read through its two layers, an
-- `each` over a `scan`, a batched run that completes is an elaborated
-- run that completes, every batch released along the way; and the last
-- emit an elaborated run makes is its completion mark, which releases
-- whatever is still held.
module simultaneous.Batcher where

open import Data.List using (List; []; _∷_; _++_; [_]; concat; concatMap)
import Data.List as L
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++; concat-++)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Tree using (scan; merge; of)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import simultaneous.InstEmit using (InstEmit; instEmit; mark; completed; valuesOf)
import simultaneous.InstEmit as Marks
open import simultaneous.SObs using (SObs; Batching; module Elaborate)
open import simultaneous.Readings using (stamped)
open import simultaneous.Relations using (Met; values; joined; vals; Ends; EndsWith; elaborated; batched)
open import simultaneous.Layers using (scans; scan-out; scan-in; each-out; each-in; map-back; concat-last)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; elaborate; Step; bstep; bstart; bstep-held; completed-held; unbatched;
  restamp; marked; concatˢ; elab; E)

------------------------------------------------------------------------
-- The fold, as lists

-- What the batcher releases over `vs`, from `s`.
released : ∀ {A} → Step A → List (IE A) → List (IE (List A))
released s vs = concatMap proj₂ (scans bstep s vs)

-- The state it ends in.
after : ∀ {A} → Step A → List (IE A) → Step A
after s []       = s
after s (v ∷ vs) = after (bstep s v) vs

after-snoc : ∀ {A} (s : Step A) vs v → after s (vs ++ [ v ]) ≡ bstep (after s vs) v
after-snoc s []       v = refl
after-snoc s (w ∷ vs) v = after-snoc (bstep s w) vs v

unbatched-++ : ∀ {A} (xs ys : List (IE (List A))) → unbatched (xs ++ ys) ≡ unbatched xs ++ unbatched ys
unbatched-++ xs ys = trans (cong concat (trans (cong concat (map-++ valuesOf xs ys)) (sym (concat-++ (L.map valuesOf xs) (L.map valuesOf ys)))))
                           (sym (concat-++ (concat (L.map valuesOf xs)) (concat (L.map valuesOf ys))))

-- A completion carries no values.
map-snoc : ∀ {A} (vs : List (IE A)) n → concatMap valuesOf (vs ++ [ instEmit (mark completed) n ]) ≡ concatMap valuesOf vs
map-snoc vs n = trans (cong concat (map-++ valuesOf vs _)) (trans (sym (concat-++ (L.map valuesOf vs) _)) (++-identityʳ _))

-- Every value goes out, released or held.
released-held : ∀ {A} (s : Step A) vs
              → unbatched (released s vs) ++ Batching.held (proj₁ (after s vs)) ≡ Batching.held (proj₁ s) ++ concatMap valuesOf vs
released-held s []       = sym (++-identityʳ _)
released-held s (v ∷ vs) =
  let s′ = bstep s v in
  begin
    unbatched (proj₂ s′ ++ released s′ vs) ++ Batching.held (proj₁ (after s′ vs))
      ≡⟨ cong (_++ Batching.held (proj₁ (after s′ vs))) (unbatched-++ (proj₂ s′) (released s′ vs)) ⟩
    (unbatched (proj₂ s′) ++ unbatched (released s′ vs)) ++ Batching.held (proj₁ (after s′ vs))
      ≡⟨ ++-assoc (unbatched (proj₂ s′)) _ _ ⟩
    unbatched (proj₂ s′) ++ (unbatched (released s′ vs) ++ Batching.held (proj₁ (after s′ vs)))
      ≡⟨ cong (unbatched (proj₂ s′) ++_) (released-held s′ vs) ⟩
    unbatched (proj₂ s′) ++ (Batching.held (proj₁ s′) ++ concatMap valuesOf vs)
      ≡⟨ sym (++-assoc (unbatched (proj₂ s′)) _ _) ⟩
    (unbatched (proj₂ s′) ++ Batching.held (proj₁ s′)) ++ concatMap valuesOf vs
      ≡⟨ cong (_++ concatMap valuesOf vs) (bstep-held s v) ⟩
    (Batching.held (proj₁ s) ++ valuesOf v) ++ concatMap valuesOf vs
      ≡⟨ ++-assoc (Batching.held (proj₁ s)) (valuesOf v) _ ⟩
    Batching.held (proj₁ s) ++ concatMap valuesOf (v ∷ vs)
  ∎
  where open ≡-Reasoning

-- Run from the start and closed by a completion, everything is released.
released-all : ∀ {A} (vs : List (IE A)) n → unbatched (released bstart (vs ++ [ instEmit (mark completed) n ])) ≡ concatMap valuesOf vs
released-all vs n =
  begin
    unbatched (released bstart ws)
      ≡⟨ sym (++-identityʳ _) ⟩
    unbatched (released bstart ws) ++ []
      ≡⟨ cong (unbatched (released bstart ws) ++_) (sym held-end) ⟩
    unbatched (released bstart ws) ++ Batching.held (proj₁ (after bstart ws))
      ≡⟨ released-held bstart ws ⟩
    concatMap valuesOf ws
      ≡⟨ map-snoc vs n ⟩
    concatMap valuesOf vs
  ∎
  where
    open ≡-Reasoning
    c = instEmit (mark completed) n
    ws = vs ++ [ c ]
    held-end : Batching.held (proj₁ (after bstart ws)) ≡ []
    held-end = trans (cong (λ s → Batching.held (proj₁ s)) (after-snoc bstart vs c)) (completed-held (after bstart vs) n)

-- The values of emits, stamped then unstamped.
vals-of : ∀ {N A} (xs : List (InstEmit N A)) → L.map proj₂ (stamped xs) ≡ concatMap valuesOf xs
vals-of []       = refl
vals-of (x ∷ xs) = trans (map-++ proj₂ (L.map (λ a → InstEmit.instant x , a) (valuesOf x)) (stamped xs))
                         (trans (cong (_++ L.map proj₂ (stamped xs)) (unstamp (valuesOf x))) (cong (valuesOf x ++_) (vals-of xs)))
  where
    unstamp : ∀ vs → L.map proj₂ (L.map (λ a → InstEmit.instant x , a) vs) ≡ vs
    unstamp []       = refl
    unstamp (v ∷ vs) = cong (v ∷_) (unstamp vs)

joined-unbatched : ∀ {A} rs → joined {A} rs ≡ unbatched (values rs)
joined-unbatched rs = cong concat (vals-of (values rs))

------------------------------------------------------------------------
-- The protocol

-- The elaboration's parts: the restamp's start, and the run with the end
-- of its subscribe burst.
stamp₀ : ∀ {A : Set} → Pos × IE A
stamp₀ = root , marked Marks.begin

sourced : ∀ {A : Set} → SObs [] A → E [] (IE A)
sourced o = merge (elab (λ i → i) o) (of (marked Marks.subscribed ∷ []))

scans-snoc : ∀ {X Y : Set} (f : Y → X → Y) z (xs : List X) x → scans f z (xs ++ [ x ]) ≡ scans f z xs ++ [ f (L.foldl f z xs) x ]
scans-snoc f z []       x = refl
scans-snoc f z (y ∷ xs) x = cong (f z y ∷_) (scans-snoc f (f z y) xs x)

-- THE LAST EMIT IS THE COMPLETION: the elaboration is a map over a scan
-- over a concat of the run with a lone completion mark, so a completed
-- run's last value is that mark, restamped.
completed-last : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Ends rx
               → Σ (List (IE A)) λ vs → Σ Pos λ n → values rx ≡ vs ++ [ instEmit (mark completed) n ]
completed-last o {rx} mx ex with map-back proj₂ (scan restamp stamp₀ (concatˢ (sourced o) (of (marked completed ∷ [])))) mx
... | sc , msc , eqm , enm with scan-out restamp stamp₀ (concatˢ (sourced o) (of (marked completed ∷ []))) msc
...   | kx , mk , eqs , ens with concat-last (sourced o) (marked completed) mk (ens (enm ex))
...     | vs , eqk =
  L.map proj₂ (scans restamp stamp₀ vs) , proj₁ (L.foldl restamp stamp₀ vs) ,
  trans eqm (trans (cong (L.map proj₂) (trans eqs (trans (cong (scans restamp stamp₀) eqk) (scans-snoc restamp stamp₀ vs (marked completed)))))
                   (map-++ proj₂ (scans restamp stamp₀ vs) _))

------------------------------------------------------------------------
-- The batcher ends with what it batches

-- A completed run's values, released from the start.
ended-released : ∀ {A} (o : SObs [] A) {rx} → Met (elaborated o) rx → Ends rx → unbatched (released bstart (values rx)) ≡ vals rx
ended-released o {rx} mx ex with completed-last o mx ex
... | vs , n , eq =
  begin
    unbatched (released bstart (values rx))
      ≡⟨ cong (λ ws → unbatched (released bstart ws)) eq ⟩
    unbatched (released bstart (vs ++ [ instEmit (mark completed) n ]))
      ≡⟨ released-all vs n ⟩
    concatMap valuesOf vs
      ≡⟨ sym (map-snoc vs n) ⟩
    concatMap valuesOf (vs ++ [ instEmit (mark completed) n ])
      ≡⟨ cong (concatMap valuesOf) (sym eq) ⟩
    concatMap valuesOf (values rx)
      ≡⟨ sym (vals-of (values rx)) ⟩
    vals rx
  ∎
  where open ≡-Reasoning

batcher-ends : ∀ {A : Set} (o : SObs [] A) → EndsWith (batched o) (elaborated o)
batcher-ends o = out , into
  where
    S = scan bstep bstart (elaborate o)

    out : ∀ {rs} → Met (batched o) rs → Ends rs → Σ _ λ rx → Met (elaborated o) rx × Ends rx × joined rs ≡ vals rx
    out {rs} mb eb with each-out proj₂ S mb
    ... | sc , ms , _ , ends-e with ends-e eb | scan-out bstep bstart (elaborate o) ms
    ...   | es , eqb | rx , mx , eqs , ends-s =
      rx , mx , ends-s es ,
      trans (joined-unbatched rs) (trans (cong unbatched (trans eqb (cong (concatMap proj₂) eqs))) (ended-released o mx (ends-s es)))

    into : ∀ {rx} → Met (elaborated o) rx → Ends rx → Σ _ λ rs → Met (batched o) rs × Ends rs × vals rx ≡ joined rs
    into {rx} mx ex with scan-in bstep bstart (elaborate o) mx
    ... | sc , ms , eqs , ends-s with each-in proj₂ S ms
    ...   | rs , mb , eqb , ends-e =
      rs , mb , ends-e (ends-s ex) ,
      sym (trans (joined-unbatched rs) (trans (cong unbatched (trans eqb (cong (concatMap proj₂) eqs))) (ended-released o mx ex)))
