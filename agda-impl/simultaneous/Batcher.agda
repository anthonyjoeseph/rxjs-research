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
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++; concat-++; foldl-++)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Sum
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (zero; suc; _≤_; z≤n; s≤s)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)

open import Tree using (scan; map; merge; of)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; skip; end; pin) renaming (out to emit)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; completed; valuesOf)
import simultaneous.InstEmit as Marks
open import simultaneous.SObs using (SObs; Batching; batching; module Elaborate)
open import simultaneous.Readings using (stamped; closed)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchFrom; batchSimultaneousᴰ)
import simultaneous.Flatten as F
open F _≟ᵖ_ using (prefix-≡; prefix-trans; prefix-++; closed-prefix)
open import simultaneous.Relations using (Met; values; values-++; joined; vals; batchesOut; grouped; Closes; Batches; Ends; EndsWith;
  elaborated; batched)
open import simultaneous.Layers using (scans; scan-out; scan-in; each-out; each-in; map-back; concat-last)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; elaborate; Step; bstep; bstart; bstep-held; completed-held; unbatched;
  pending; asEmits; mark-step; restamp; marked; concatˢ; elab; E)

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

------------------------------------------------------------------------
-- The protocol, read off the elaborated run

-- THE RUN IS CLOSED WHERE NOTHING IS HELD: past every release, no value
--   of the instant released, and the run leaves it.
-- A CLOSED INSTANT IS RELEASED: the run met on, the batcher releases what
--   it holds before it holds anything new.
postulate
  flush-closes : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → pending (proj₁ (after bstart (values rx))) ≡ []
               → Closes (elaborated o) rx true
  closes-flush : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Closes (elaborated o) rx true
               → Σ _ λ ext → Met (elaborated o) (rx ++ ext)
               × Prefix _≡_ (pending (proj₁ (after bstart (values rx)))) (stamped (released (after bstart (values rx)) (values ext)))

------------------------------------------------------------------------
-- The protocol, stream by stream

nameStep : ∀ {A : Set} → Pos → IE A → Pos
nameStep a (instEmit (mark Marks.begin) n) = n
nameStep a (instEmit _ _)                  = a

-- The name of the last begin, `a` if none.
lastBegin : ∀ {A : Set} → Pos → List (IE A) → Pos
lastBegin a xs = L.foldl nameStep a xs

subStep : ∀ {A : Set} → Bool → IE A → Bool
subStep b (instEmit (mark Marks.subscribed) _) = true
subStep b (instEmit _ _)                       = b

-- The subscribe burst is over.
seenSub : ∀ {A : Set} → List (IE A) → Bool
seenSub xs = L.foldl subStep false xs

NameOk : ∀ {A : Set} → Pos → IE A → Set
NameOk a (instEmit (value _) n) = n ≡ a
NameOk a (instEmit (mark _) _)  = ⊤

-- Every value carries the name of the last begin before it.
Stamps : ∀ {A : Set} → Pos → List (IE A) → Set
Stamps a []       = ⊤
Stamps a (w ∷ ws) = NameOk a w × Stamps (nameStep a w) ws

restamp-ok : ∀ {A : Set} a (e : IE A) k → NameOk a (proj₂ (restamp (a , e) k)) × proj₁ (restamp (a , e) k) ≡ nameStep a (proj₂ (restamp (a , e) k))
restamp-ok a e (instEmit (value _) _)             = refl , refl
restamp-ok a e (instEmit (mark Marks.begin) _)      = tt , refl
restamp-ok a e (instEmit (mark Marks.over) _)       = tt , refl
restamp-ok a e (instEmit (mark Marks.stop) _)       = tt , refl
restamp-ok a e (instEmit (mark Marks.outerOpen) _)  = tt , refl
restamp-ok a e (instEmit (mark Marks.outerClose) _) = tt , refl
restamp-ok a e (instEmit (mark Marks.laneStart) _)  = tt , refl
restamp-ok a e (instEmit (mark Marks.laneDone) _)   = tt , refl
restamp-ok a e (instEmit (mark Marks.burstEnd) _)   = tt , refl
restamp-ok a e (instEmit (mark Marks.outerDone) _)  = tt , refl
restamp-ok a e (instEmit (mark Marks.subscribed) _) = tt , refl
restamp-ok a e (instEmit (mark completed) _)        = tt , refl

stamps-restamp : ∀ {A : Set} a (e : IE A) ks → Stamps a (L.map proj₂ (scans restamp (a , e) ks))
stamps-restamp a e []       = tt
stamps-restamp a e (k ∷ ks) =
  proj₁ (restamp-ok a e k) ,
  subst (λ b → Stamps b (L.map proj₂ (scans restamp (restamp (a , e) k) ks))) (proj₂ (restamp-ok a e k))
        (stamps-restamp (proj₁ (restamp (a , e) k)) (proj₂ (restamp (a , e) k)) ks)

-- An elaborated run's values are named by its begins.
stamps-of : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Stamps root (values rx)
stamps-of o {rx} mx with map-back proj₂ (scan restamp stamp₀ (concatˢ (sourced o) (of (marked completed ∷ [])))) mx
... | sc , msc , eqm , _ with scan-out restamp stamp₀ (concatˢ (sourced o) (of (marked completed ∷ []))) msc
...   | kx , _ , eqs , _ =
  subst (Stamps root) (sym (trans eqm (cong (L.map proj₂) eqs))) (stamps-restamp root (marked Marks.begin) (values kx))

lb-snoc : ∀ {A : Set} (xs : List (IE A)) w → lastBegin root (xs ++ [ w ]) ≡ nameStep (lastBegin root xs) w
lb-snoc xs w = foldl-++ nameStep root xs [ w ]

ss-snoc : ∀ {A : Set} (xs : List (IE A)) w → seenSub (xs ++ [ w ]) ≡ subStep (seenSub xs) w
ss-snoc xs w = foldl-++ subStep false xs [ w ]

-- THE RUN'S PROTOCOL, ONE MARK AT A TIME: begins only past the subscribe
-- burst, which ends once; past each release of an instant, the next value
-- of another; no value past the completion.
postulate
  begin-late    : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.begin) n ∷ ys → seenSub xs ≡ true
  sub-once      : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.subscribed) n ∷ ys → seenSub xs ≡ false
  sub-fresh     : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.subscribed) n ∷ ys → Fresh root (stamped ys)
  begin-fresh   : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.begin) n ∷ ys → n ≢ lastBegin root xs → Fresh (lastBegin root xs) (stamped ys)
  over-fresh    : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.over) n ∷ ys → seenSub xs ≡ true → Fresh (lastBegin root xs) (stamped ys)
  stop-fresh    : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.stop) n ∷ ys → seenSub xs ≡ true
                → Batching.routes (proj₁ (after bstart xs)) ≤ 1 → Fresh (lastBegin root xs) (stamped ys)
  completed-end : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark completed) n ∷ ys → stamped ys ≡ []

true≢false : true ≢ false
true≢false ()

-- A begin, past the burst, names the instant held; it releases only on a
-- new one.
begin-step : ∀ {A : Set} a (h : List A) r rel n
           → Batching.at (proj₁ (bstep (batching true a h r , rel) (instEmit (mark Marks.begin) n))) ≡ n
           × Batching.late (proj₁ (bstep (batching true a h r , rel) (instEmit (mark Marks.begin) n))) ≡ true
           × (n ≢ a ⊎ proj₂ (bstep (batching true a h r , rel) (instEmit (mark Marks.begin) n)) ≡ [])
begin-step a h r rel n with n ≟ᵖ a
... | yes refl = refl , refl , inj₂ refl
... | no ne    = refl , refl , inj₁ ne

-- The batcher walks the run, its state the run's so far: named by the last
-- begin, late once the burst is over, and at the root until then.
module Walk {A : Set} (o : SObs [] A) {rx} (mx : Met (elaborated o) rx) where
  ws = values rx

  fresh-at : ∀ {a L} (ys : List (IE A)) → a ≡ L → Fresh L (stamped ys) → Fresh a (stamped ys)
  fresh-at ys ea = subst (λ x → Fresh x (stamped ys)) (sym ea)

  mutual
    go : ∀ (s : Step A) xs ys → ws ≡ xs ++ ys → after bstart xs ≡ s
       → Batching.at (proj₁ s) ≡ lastBegin root xs → Batching.late (proj₁ s) ≡ seenSub xs
       → (seenSub xs ≡ false → lastBegin root xs ≡ root) → Stamps (lastBegin root xs) ys → Good s ys
    go s xs [] _ _ _ _ _ _ = tt
    go s@(batching l a h r , rel) xs (w@(instEmit (value _) _) ∷ ys) eq es ea el e0 (nk , st) =
      continue s xs w ys eq es st (trans nk (sym ea) , inj₁ refl) ea el e0
    go s@(batching true a h r , rel) xs (w@(instEmit (mark Marks.begin) n) ∷ ys) eq es ea el e0 (_ , st) with begin-step a h r rel n
    ... | ea′ , el′ , c =
      continue s xs w ys eq es st (tt , Data.Sum.[ (λ ne → inj₂ (fresh-at ys ea (begin-fresh o mx xs n ys eq (λ e → ne (trans e (sym ea)))))) , inj₁ ] c)
        ea′ (trans el′ el) (λ f → ⊥-elim (true≢false (trans el f)))
    go s@(batching false a h r , rel) xs (w@(instEmit (mark Marks.begin) n) ∷ ys) eq es ea el e0 (_ , st) =
      ⊥-elim (true≢false (trans (sym (begin-late o mx xs n ys eq)) (sym el)))
    go s@(batching true a h r , rel) xs (w@(instEmit (mark Marks.over) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (fresh-at ys ea (over-fresh o mx xs n ys eq (sym el)))) ea el e0
    go s@(batching false a h r , rel) xs (w@(instEmit (mark Marks.over) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching true a h zero , rel) xs (w@(instEmit (mark Marks.stop) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (fresh-at ys ea (stop-fresh o mx xs n ys eq (sym el) (subst (λ t → Batching.routes (proj₁ t) ≤ 1) (sym es) z≤n))))
        ea el e0
    go s@(batching true a h (suc zero) , rel) xs (w@(instEmit (mark Marks.stop) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (fresh-at ys ea (stop-fresh o mx xs n ys eq (sym el) (subst (λ t → Batching.routes (proj₁ t) ≤ 1) (sym es) (s≤s z≤n)))))
        ea el e0
    go s@(batching true a h (suc (suc _)) , rel) xs (w@(instEmit (mark Marks.stop) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching false a h r , rel) xs (w@(instEmit (mark Marks.stop) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.subscribed) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (fresh-at ys (trans ea (e0 (sub-once o mx xs n ys eq))) (sub-fresh o mx xs n ys eq))) ea refl (λ ())
    go s@(batching l a h r , rel) xs (w@(instEmit (mark completed) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (subst (Fresh a) (sym (completed-end o mx xs n ys eq)) tt)) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.outerOpen) _) ∷ ys) eq es ea el e0 (_ , st)  = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.outerClose) _) ∷ ys) eq es ea el e0 (_ , st) = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.laneStart) _) ∷ ys) eq es ea el e0 (_ , st)  = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.laneDone) _) ∷ ys) eq es ea el e0 (_ , st)   = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.burstEnd) _) ∷ ys) eq es ea el e0 (_ , st)   = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.outerDone) _) ∷ ys) eq es ea el e0 (_ , st)  = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0

    continue : ∀ (s : Step A) xs w ys → ws ≡ xs ++ w ∷ ys → after bstart xs ≡ s → Stamps (nameStep (lastBegin root xs) w) ys
             → (Named (proj₁ s) w × (proj₂ (bstep s w) ≡ [] ⊎ Fresh (Batching.at (proj₁ s)) (stamped ys)))
             → Batching.at (proj₁ (bstep s w)) ≡ nameStep (lastBegin root xs) w
             → Batching.late (proj₁ (bstep s w)) ≡ subStep (seenSub xs) w
             → (subStep (seenSub xs) w ≡ false → nameStep (lastBegin root xs) w ≡ root)
             → Good s (w ∷ ys)
    continue s xs w ys eq es st here ea′ el′ e0′ =
      here ,
      go (bstep s w) (xs ++ [ w ]) ys (trans eq (sym (++-assoc xs [ w ] ys))) (trans (after-snoc bstart xs w) (cong (λ t → bstep t w) es))
         (trans ea′ (sym (lb-snoc xs w))) (trans el′ (sym (ss-snoc xs w)))
         (λ f → trans (lb-snoc xs w) (e0′ (trans (sym (ss-snoc xs w)) f)))
         (subst (λ x → Stamps x ys) (sym (lb-snoc xs w)) st)

-- THE ELABORATED RUN IS GOOD: the batcher, walked along it, meets the
-- protocol at every mark.
good-run : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Good bstart (values rx)
good-run o {rx} mx = Walk.go o mx bstart [] (values rx) refl refl refl refl (λ _ → refl) (stamps-of o mx)

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
