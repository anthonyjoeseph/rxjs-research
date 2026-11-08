{-# OPTIONS --guardedness #-}

-- THE BATCHER ENDS WITH WHAT IT BATCHES: read through its two layers, an
-- `each` over a `scan`, a batched run that completes is an elaborated
-- run that completes, every batch released along the way; and the last
-- emit an elaborated run makes is its completion mark, which releases
-- whatever is still held.
module simultaneous.Batcher where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; _∷ʳ_; concat; concatMap)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
import Data.List as L
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++; concat-++)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Sum
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)

open import Tree using (scan)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; skip; end; pin) renaming (out to emit)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; completed; valuesOf)
open import simultaneous.SObs using (SObs; Batching; module Elaborate)
open import simultaneous.Readings using (stamped; closed)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchFrom; batchSimultaneousᴰ)
import simultaneous.Flatten as F
open F _≟ᵖ_ using (prefix-≡; prefix-trans; prefix-++; closed-prefix)
open import simultaneous.Relations using (Met; outs; values; joined; vals; batchesOut; grouped; Closes; Batches; Ends; EndsWith; elaborated; batched)
open import simultaneous.Layers using (scans; scan-out; scan-in; each-out; each-in)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; elaborate; Step; bstep; bstart; bstep-held; completed-held; unbatched;
  pending; asEmits; mark-step)

------------------------------------------------------------------------
-- The fold, as lists

-- What the batcher releases over `vs`, from `s`.
released : ∀ {A : Set} → Step A → List (IE A) → List (IE (List A))
released s vs = concatMap proj₂ (scans bstep s vs)

-- The state it ends in.
after : ∀ {A : Set} → Step A → List (IE A) → Step A
after s []       = s
after s (v ∷ vs) = after (bstep s v) vs

after-snoc : ∀ {A : Set} (s : Step A) vs v → after s (vs ++ [ v ]) ≡ bstep (after s vs) v
after-snoc s []       v = refl
after-snoc s (w ∷ vs) v = after-snoc (bstep s w) vs v

unbatched-++ : ∀ {A : Set} (xs ys : List (IE (List A))) → unbatched (xs ++ ys) ≡ unbatched xs ++ unbatched ys
unbatched-++ xs ys = trans (cong concat (trans (cong concat (map-++ valuesOf xs ys)) (sym (concat-++ (L.map valuesOf xs) (L.map valuesOf ys)))))
                           (sym (concat-++ (concat (L.map valuesOf xs)) (concat (L.map valuesOf ys))))

-- A completion carries no values.
map-snoc : ∀ {A : Set} (vs : List (IE A)) n → concatMap valuesOf (vs ++ [ instEmit (mark completed) n ]) ≡ concatMap valuesOf vs
map-snoc vs n = trans (cong concat (map-++ valuesOf vs _)) (trans (sym (concat-++ (L.map valuesOf vs) _)) (++-identityʳ _))

-- Every value goes out, released or held.
released-held : ∀ {A : Set} (s : Step A) vs
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
released-all : ∀ {A : Set} (vs : List (IE A)) n → unbatched (released bstart (vs ++ [ instEmit (mark completed) n ])) ≡ concatMap valuesOf vs
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
vals-of : ∀ {N A : Set} (xs : List (InstEmit N A)) → L.map proj₂ (stamped xs) ≡ concatMap valuesOf xs
vals-of []       = refl
vals-of (x ∷ xs) = trans (map-++ proj₂ (L.map (λ a → InstEmit.instant x , a) (valuesOf x)) (stamped xs))
                         (trans (cong (_++ L.map proj₂ (stamped xs)) (unstamp (valuesOf x))) (cong (valuesOf x ++_) (vals-of xs)))
  where
    unstamp : ∀ vs → L.map proj₂ (L.map (λ a → InstEmit.instant x , a) vs) ≡ vs
    unstamp []       = refl
    unstamp (v ∷ vs) = cong (v ∷_) (unstamp vs)

joined-unbatched : ∀ {A : Set} rs → joined {A} rs ≡ unbatched (values rs)
joined-unbatched rs = cong concat (vals-of (values rs))

------------------------------------------------------------------------
-- The protocol

-- THE LAST EMIT IS THE COMPLETION: the elaboration concatenates the run
-- with a lone completion mark, so a completed run's last value is it.
postulate
  completed-last : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Ends rx
                 → Σ (List (IE A)) λ vs → Σ Pos λ n → values rx ≡ vs ++ [ instEmit (mark completed) n ]

------------------------------------------------------------------------
-- The batcher ends with what it batches

-- A completed run's values, released from the start.
ended-released : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Ends rx → unbatched (released bstart (values rx)) ≡ vals rx
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

------------------------------------------------------------------------
-- The batches, against the spec's grouping

-- The spec's grouping, a batch perhaps already open.
cont : ∀ {A : Set} → List (Pos × List A) → List (Pos × A) → List (Pos × List A)
cont []             xs = batchSimultaneousᴰ xs
cont ((i , vs) ∷ _) xs = batchFrom i vs xs

-- The next value, if any, is of another instant.
Fresh : ∀ {A : Set} → Pos → List (Pos × A) → Set
Fresh i []            = ⊤
Fresh i ((j , _) ∷ _) = i ≢ j

-- A value is of the instant held.
Named : ∀ {A : Set} → Batching A Pos → IE A → Set
Named b (instEmit (value _) n) = n ≡ Batching.at b
Named b (instEmit (mark _) _)  = ⊤

-- THE ELABORATED RUN AS THE BATCHER NEEDS IT: each value of the instant
-- held, and after a release, the next value of another instant.
Good : ∀ {A : Set} → Step A → List (IE A) → Set
Good s []       = ⊤
Good s (w ∷ ws) = (Named (proj₁ s) w × (proj₂ (bstep s w) ≡ [] ⊎ Fresh (Batching.at (proj₁ s)) (stamped ws))) × Good (bstep s w) ws

stamped-++ : ∀ {N A : Set} (xs ys : List (InstEmit N A)) → stamped (xs ++ ys) ≡ stamped xs ++ stamped ys
stamped-++ []       ys = refl
stamped-++ (x ∷ xs) ys = trans (cong (L.map (λ a → InstEmit.instant x , a) (valuesOf x) ++_) (stamped-++ xs ys))
                               (sym (++-assoc (L.map (λ a → InstEmit.instant x , a) (valuesOf x)) (stamped xs) (stamped ys)))

stamped-asEmits : ∀ {A : Set} (P : List (Pos × List A)) → stamped (asEmits P) ≡ P
stamped-asEmits []             = refl
stamped-asEmits ((i , vs) ∷ P) = cong ((i , vs) ∷_) (stamped-asEmits P)

stamped-prefix : ∀ {N A : Set} {xs ys : List (InstEmit N A)} → Prefix _≡_ xs ys → Prefix _≡_ (stamped xs) (stamped ys)
stamped-prefix []                  = []
stamped-prefix {xs = x ∷ _} (refl ∷ p) = prefix-++ (L.map (λ a → InstEmit.instant x , a) (valuesOf x)) (stamped-prefix p)

batchFrom-same : ∀ {A : Set} i (vs : List A) v X → batchFrom i vs ((i , v) ∷ X) ≡ batchFrom i (vs ∷ʳ v) X
batchFrom-same i vs v X with i ≟ᵖ i
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

batchFrom-fresh : ∀ {A : Set} i (vs : List A) X → Fresh i X → batchFrom i vs X ≡ (i , vs) ∷ batchSimultaneousᴰ X
batchFrom-fresh i vs []            _  = refl
batchFrom-fresh i vs ((j , v) ∷ X) ne with i ≟ᵖ j
... | yes eq = ⊥-elim (ne eq)
... | no _   = refl

-- What is held, then nothing more: its own batch.
cont-nil : ∀ {A : Set} (b : Batching A Pos) → pending b ≡ cont (pending b) []
cont-nil b with Batching.held b
... | []     = refl
... | _ ∷ _  = refl

-- A release ahead of a value of another instant closes the open batch.
flush-eq : ∀ {A : Set} (b : Batching A Pos) X → (asEmits (pending b) ≡ [] ⊎ Fresh (Batching.at b) X)
         → pending b ++ batchSimultaneousᴰ X ≡ cont (pending b) X
flush-eq b X h with Batching.held b
... | []     = refl
... | v ∷ vs with h
...   | inj₁ ()
...   | inj₂ fr = sym (batchFrom-fresh (Batching.at b) (v ∷ vs) X fr)

-- One step of the batcher against the grouping.
grouped-step : ∀ {A : Set} (s : Step A) w X → Named (proj₁ s) w → (proj₂ (bstep s w) ≡ [] ⊎ Fresh (Batching.at (proj₁ s)) X)
             → stamped (proj₂ (bstep s w)) ++ cont (pending (proj₁ (bstep s w))) X
             ≡ cont (pending (proj₁ s)) (L.map (λ a → InstEmit.instant w , a) (valuesOf w) ++ X)
grouped-step (b , r) (instEmit (value a) .(Batching.at b)) X refl _ with Batching.held b
... | []     = refl
... | v ∷ vs = sym (batchFrom-same (Batching.at b) (v ∷ vs) a X)
grouped-step (b , r) (instEmit (mark m) n) X _ fr with mark-step (Batching.late b) m n b
... | inj₁ (e₁ , e₂) = cong₂ (λ u P → stamped u ++ cont P X) e₁ e₂
... | inj₂ (e₁ , e₂) =
  trans (cong₂ (λ u P → stamped u ++ cont P X) e₁ e₂)
        (trans (cong (_++ batchSimultaneousᴰ X) (stamped-asEmits (pending b)))
               (flush-eq b X (Data.Sum.[ (λ e₀ → inj₁ (trans (sym e₁) e₀)) , inj₂ ] fr)))

-- THE BATCHER IS THE GROUPING: what it has released, then what it holds,
-- is the spec's grouping of every value.
grouped-run : ∀ {A : Set} (s : Step A) ws → Good s ws
            → stamped (released s ws) ++ pending (proj₁ (after s ws)) ≡ cont (pending (proj₁ s)) (stamped ws)
grouped-run s []       _                  = cont-nil (proj₁ s)
grouped-run s (w ∷ ws) ((nm , fr) , g) =
  let s′ = bstep s w ; P = proj₂ s′ in
  begin
    stamped (P ++ released s′ ws) ++ pending (proj₁ (after s′ ws))
      ≡⟨ cong (_++ pending (proj₁ (after s′ ws))) (stamped-++ P (released s′ ws)) ⟩
    (stamped P ++ stamped (released s′ ws)) ++ pending (proj₁ (after s′ ws))
      ≡⟨ ++-assoc (stamped P) _ _ ⟩
    stamped P ++ (stamped (released s′ ws) ++ pending (proj₁ (after s′ ws)))
      ≡⟨ cong (stamped P ++_) (grouped-run s′ ws g) ⟩
    stamped P ++ cont (pending (proj₁ s′)) (stamped ws)
      ≡⟨ grouped-step s w (stamped ws) nm fr ⟩
    cont (pending (proj₁ s)) (stamped (w ∷ ws))
  ∎
  where open ≡-Reasoning

-- What is held is one batch or none.
pending-one : ∀ {A : Set} (b : Batching A Pos) → pending b ≡ [] ⊎ Σ (Pos × List A) λ g → pending b ≡ [ g ]
pending-one b with Batching.held b
... | []     = inj₁ refl
... | v ∷ vs = inj₂ (_ , refl)

closed-snoc : ∀ {X : Set} (xs : List X) g → closed false (xs ++ [ g ]) ≡ xs
closed-snoc []           g = refl
closed-snoc (x ∷ [])     g = refl
closed-snoc (x ∷ y ∷ xs) g = cong (x ∷_) (closed-snoc (y ∷ xs) g)

released-++ : ∀ {A : Set} (s : Step A) u v → released s (u ++ v) ≡ released s u ++ released (after s u) v
released-++ s []       v = refl
released-++ s (w ∷ u) v = trans (cong (proj₂ (bstep s w) ++_) (released-++ (bstep s w) u v))
                                (sym (++-assoc (proj₂ (bstep s w)) (released (bstep s w) u) _))

outs-++ : ∀ {A : Set} (xs ys : List (Pos × Ev A)) → outs (xs ++ ys) ≡ outs xs ++ outs ys
outs-++ []                  ys = refl
outs-++ ((q , emit a) ∷ xs) ys = cong ((q , a) ∷_) (outs-++ xs ys)
outs-++ ((q , skip) ∷ xs)   ys = outs-++ xs ys
outs-++ ((q , end) ∷ xs)    ys = outs-++ xs ys
outs-++ ((q , pin _) ∷ xs)  ys = outs-++ xs ys

values-++ : ∀ {A : Set} (xs ys : List (Pos × Ev A)) → values (xs ++ ys) ≡ values xs ++ values ys
values-++ xs ys = trans (cong (L.map proj₂) (outs-++ xs ys)) (map-++ proj₂ (outs xs) (outs ys))

------------------------------------------------------------------------
-- The protocol, read off the elaborated run

-- THE ELABORATED RUN IS GOOD: every prefix met is.
-- THE RUN IS CLOSED WHERE NOTHING IS HELD: past every release, no value
--   of the instant released, and the run leaves it.
-- A CLOSED INSTANT IS RELEASED: the run met on, the batcher releases what
--   it holds before it holds anything new.
postulate
  good-run     : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Good bstart (values rx)
  flush-closes : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → pending (proj₁ (after bstart (values rx))) ≡ []
               → Closes (elaborated o) rx true
  closes-flush : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Closes (elaborated o) rx true
               → Σ _ λ ext → Met (elaborated o) (rx ++ ext)
               × Prefix _≡_ (pending (proj₁ (after bstart (values rx)))) (stamped (released (after bstart (values rx)) (values ext)))

------------------------------------------------------------------------
-- The batcher batches as the spec groups

batches : ∀ {A : Set} (o : SObs [] A) → Batches (batched o) (elaborated o)
batches o = early , late
  where
    S = scan bstep bstart (elaborate o)

    early : ∀ {rs} → Met (batched o) rs → Σ _ λ rs′ → Σ Bool λ ov → Met (elaborated o) rs′ × Closes (elaborated o) rs′ ov
          × Prefix _≡_ (batchesOut rs) (grouped ov rs′)
    early {rs} mb with each-out proj₂ S mb
    ... | sc , ms , pre , _ with scan-out bstep bstart (elaborate o) ms
    ...   | rx , mx , eqs , _ with pending-one (proj₁ (after bstart (values rx)))
    ...     | inj₁ e = rx , true , mx , flush-closes o mx e ,
                prefix-trans out⊑ (prefix-≡ (trans (sym (++-identityʳ _)) (trans (cong (stamped (released bstart (values rx)) ++_) (sym e)) run)))
      where
        out⊑ = stamped-prefix (prefix-trans pre (prefix-≡ (cong (concatMap proj₂) eqs)))
        run = grouped-run bstart (values rx) (good-run o mx)
    ...     | inj₂ (g , e) = rx , false , mx , tt ,
                prefix-trans out⊑ (prefix-≡ (sym (trans (cong (closed false) (sym (trans (cong (stamped (released bstart (values rx)) ++_) (sym e)) run)))
                                                        (closed-snoc (stamped (released bstart (values rx))) g))))
      where
        out⊑ = stamped-prefix (prefix-trans pre (prefix-≡ (cong (concatMap proj₂) eqs)))
        run = grouped-run bstart (values rx) (good-run o mx)

    -- what is met of the batched program, from what is met of the elaborated
    met-from : ∀ {rx} → Met (elaborated o) rx → Σ _ λ rs → Met (batched o) rs × batchesOut rs ≡ stamped (released bstart (values rx))
    met-from mx with scan-in bstep bstart (elaborate o) mx
    ... | sc , ms , eqs , _ with each-in proj₂ S ms
    ...   | rs , mb , eqb , _ = rs , mb , cong stamped (trans eqb (cong (concatMap proj₂) eqs))

    late : ∀ {rs′ ov} → Met (elaborated o) rs′ → Closes (elaborated o) rs′ ov → Σ _ λ rs → Met (batched o) rs × Prefix _≡_ (grouped ov rs′) (batchesOut rs)
    late {rs′} {false} mx _ with met-from mx | pending-one (proj₁ (after bstart (values rs′)))
    ... | rs , mb , eq | inj₁ e = rs , mb ,
          prefix-trans (closed-prefix false _)
            (prefix-≡ (trans (sym run′) (trans (cong (stamped (released bstart (values rs′)) ++_) e) (trans (++-identityʳ _) (sym eq)))))
      where run′ = grouped-run bstart (values rs′) (good-run o mx)
    ... | rs , mb , eq | inj₂ (g , e) = rs , mb ,
          prefix-≡ (trans (cong (closed false) (sym (trans (cong (stamped (released bstart (values rs′)) ++_) (sym e)) run′)))
                          (trans (closed-snoc _ g) (sym eq)))
      where run′ = grouped-run bstart (values rs′) (good-run o mx)
    late {rs′} {true} mx cl with closes-flush o mx cl
    ... | ext , mx′ , pre with met-from mx′
    ...   | rs , mb , eq = rs , mb ,
          prefix-trans (prefix-≡ (sym (grouped-run bstart (values rs′) (good-run o mx))))
            (prefix-trans (prefix-++ (stamped (released bstart (values rs′))) pre)
              (prefix-≡ (sym (trans eq (trans (cong (λ ws → stamped (released bstart ws)) (values-++ rs′ ext))
                (trans (cong stamped (released-++ bstart (values rs′) (values ext)))
                       (stamped-++ (released bstart (values rs′)) _)))))))
