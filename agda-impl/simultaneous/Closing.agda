{-# OPTIONS --guardedness #-}

-- THE BATCHER BATCHES AS THE SPEC GROUPS: walked along an elaborated run,
-- it meets the protocol at every mark, and it holds nothing exactly where
-- the run has closed its last instant.
module simultaneous.Closing where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; concatMap)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Sum
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Nat using (zero; suc; _≤_; z≤n; s≤s)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Tree using (scan)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import simultaneous.InstEmit using (instEmit; value; mark; completed)
import simultaneous.InstEmit as Marks
open import simultaneous.SObs using (SObs; Batching; batching; module Elaborate)
open import simultaneous.Readings using (stamped; closed)
open import simultaneous.Protocol using (nameStep; lastBegin; subStep; seenSub; Fresh; lb-snoc; ss-snoc; module Leaves)
import simultaneous.Flatten as F
open F _≟ᵖ_ using (prefix-≡; prefix-trans; prefix-++; closed-prefix)
open import simultaneous.Relations using (Met; values; values-++; batchesOut; grouped; Closes; Batches; elaborated; batched)
open import simultaneous.Layers using (scan-out; scan-in; each-out; each-in)
open import simultaneous.Batcher using (released; after; after-snoc; released-++; Stamps; stamps-of; Named; Good; stamped-prefix; stamped-++;
  grouped-run; pending-one; closed-snoc; stamped-asEmits)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; elaborate; Step; bstep; bstart; pending; asEmits; mark-step)

------------------------------------------------------------------------
-- The protocol, read off the elaborated run

-- THE RUN IS CLOSED WHERE NOTHING IS HELD: past every release, no value
-- of the instant released, and the run leaves it.
--
-- An instant that never ends never reaches its release: the batcher
-- releases only once every route of the instant is closed, and every row
-- a synchronous loop makes, its subscriptions' skips included, lies under
-- the value whose cascade it is, before that value's `over` and before
-- its route's `stop`.  So past a release only finitely many rows of the
-- instant remain.
postulate
  flush-closes : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → pending (proj₁ (after bstart (values rx))) ≡ []
               → Closes (elaborated o) rx true

-- Marks only, each keeping the batch held, until one releases it.
data Releases {A : Set} : Step A → List (IE A) → Set where
  now  : ∀ {s m n vs} → proj₂ (bstep s (instEmit (mark m) n)) ≢ [] → Releases s (instEmit (mark m) n ∷ vs)
  wait : ∀ {s m n vs} → proj₂ (bstep s (instEmit (mark m) n)) ≡ []
       → Releases (bstep s (instEmit (mark m) n)) vs → Releases s (instEmit (mark m) n ∷ vs)

-- A CLOSED INSTANT IS RELEASED: met on, the run reaches a mark releasing
-- what is held, with no value before it.
postulate
  releases : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Closes (elaborated o) rx true
           → pending (proj₁ (after bstart (values rx))) ≢ []
           → Σ _ λ ext → Met (elaborated o) (rx ++ ext) × Releases (after bstart (values rx)) (values ext)

asEmits-[] : ∀ {A : Set} (P : List (Pos × List A)) → asEmits P ≡ [] → P ≡ []
asEmits-[] []      _ = refl
asEmits-[] (_ ∷ _) ()

prefix-self : ∀ {X : Set} (P Q : List X) → Prefix _≡_ P (P ++ Q)
prefix-self P Q = prefix-trans (prefix-≡ (sym (++-identityʳ P))) (prefix-++ P Prefix.[])

-- What is held goes out whole at the release.
released-pending : ∀ {A : Set} (s : Step A) {vs} → Releases s vs → pending (proj₁ s) ≢ [] → Prefix _≡_ (pending (proj₁ s)) (stamped (released s vs))
released-pending (b , rel) (now {m = m} {n} {vs} ne) _ with mark-step (Batching.late b) m n b
... | inj₁ (e , _) = ⊥-elim (ne e)
... | inj₂ (e , _) =
  subst (Prefix _≡_ (pending b))
    (sym (trans (cong (λ x → stamped (x ++ released (bstep (b , rel) (instEmit (mark m) n)) vs)) e)
           (trans (stamped-++ (asEmits (pending b)) R) (cong (_++ stamped R) (stamped-asEmits (pending b))))))
    (prefix-self (pending b) (stamped R))
  where R = released (bstep (b , rel) (instEmit (mark m) n)) vs
released-pending (b , rel) (wait {m = m} {n} {vs} z r) ne with mark-step (Batching.late b) m n b
... | inj₁ (_ , ep) =
  subst (λ x → Prefix _≡_ (pending b) (stamped (x ++ released (bstep (b , rel) (instEmit (mark m) n)) vs))) (sym z)
    (subst (λ P → Prefix _≡_ P (stamped (released (bstep (b , rel) (instEmit (mark m) n)) vs))) ep
      (released-pending (bstep (b , rel) (instEmit (mark m) n)) r (λ e → ne (trans (sym ep) e))))
... | inj₂ (e , _) = ⊥-elim (ne (asEmits-[] (pending b) (trans (sym e) z)))

one≢[] : ∀ {X : Set} {g : X} → [ g ] ≢ []
one≢[] ()

closes-flush : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Closes (elaborated o) rx true
             → Σ _ λ ext → Met (elaborated o) (rx ++ ext)
             × Prefix _≡_ (pending (proj₁ (after bstart (values rx)))) (stamped (released (after bstart (values rx)) (values ext)))
closes-flush o {rx} mx cl with pending-one (proj₁ (after bstart (values rx)))
... | inj₁ e = [] , subst (Met (elaborated o)) (sym (++-identityʳ rx)) mx , subst (λ P → Prefix _≡_ P _) (sym e) Prefix.[]
... | inj₂ (g , e) with releases o mx cl (λ e′ → one≢[] (trans (sym e) e′))
...   | ext , mx′ , r = ext , mx′ , released-pending _ r (λ e′ → one≢[] (trans (sym e) e′))

-- PAST THE LAST ROUTE'S STOP, the next value is of another instant: the
-- one release the run's positions alone do not give, since a stop's name
-- is not its route's.
postulate
  stop-fresh    : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
                → values rx ≡ xs ++ instEmit (mark Marks.stop) n ∷ ys → seenSub xs ≡ true
                → Batching.routes (proj₁ (after bstart xs)) ≤ 1 → Fresh (lastBegin root xs) (stamped ys)

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
  open Leaves o mx using (begin-late; sub-once; sub-fresh; begin-fresh; over-fresh; completed-end)

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
      continue s xs w ys eq es st (tt , Data.Sum.[ (λ ne → inj₂ (fresh-at ys ea (begin-fresh xs n ys eq (λ e → ne (trans e (sym ea)))))) , inj₁ ] c)
        ea′ (trans el′ el) (λ f → ⊥-elim (true≢false (trans el f)))
    go s@(batching false a h r , rel) xs (w@(instEmit (mark Marks.begin) n) ∷ ys) eq es ea el e0 (_ , st) =
      ⊥-elim (true≢false (trans (sym (begin-late xs n ys eq)) (sym el)))
    go s@(batching true a h r , rel) xs (w@(instEmit (mark Marks.over) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (fresh-at ys ea (over-fresh xs n ys eq (sym el)))) ea el e0
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
      continue s xs w ys eq es st (tt , inj₂ (fresh-at ys (trans ea (e0 (sub-once xs n ys eq))) (sub-fresh xs n ys eq))) ea refl (λ ())
    go s@(batching l a h r , rel) xs (w@(instEmit (mark completed) n) ∷ ys) eq es ea el e0 (_ , st) =
      continue s xs w ys eq es st (tt , inj₂ (subst (Fresh a) (sym (completed-end xs n ys eq)) tt)) ea el e0
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
