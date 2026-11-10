{-# OPTIONS --guardedness #-}

-- THE BATCHER BATCHES AS THE SPEC GROUPS: walked along an elaborated run,
-- it meets the protocol at every mark, and it holds nothing exactly where
-- the run has closed its last instant.
module simultaneous.Closing where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; concatMap)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ; ∈-∃++; ∈-++⁻; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Bool.Properties using (T?)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-conicalʳ; foldl-++)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Sum
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; _∸_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (m≤n⇒m∸n≡0)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)

open import Tree using (scan)
open import denotation.Position using (Pos; root; frame; _∙_; _≟ᵖ_; _<ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; Seen; Few; _≺_; _≼_; ⟦_⟧)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Modulus using (≺-trans; ≺-absurd; ≼-refl; ≼-split; ≼-trans; ≺→≼)
open import denotation.Simultaneity using (between)
open import simultaneous.InstEmit using (instEmit; value; mark; completed; valuesOf)
import simultaneous.InstEmit as Marks
open import simultaneous.SObs using (SObs; Batching; batching; module Elaborate)
open import simultaneous.Readings using (stamped; closed; instantOf; rootOf)
open import simultaneous.Protocol using (nameStep; lastBegin; subStep; seenSub; Fresh; fresh-all; lb-snoc; ss-snoc; lb-view; seen-sub; named; sub-async; done-last; module Leaves; module Split)
open import simultaneous.Shut using (r₀)
open import simultaneous.Held using (shut; held)
open import simultaneous.Routed using (Held; cnt)
open import simultaneous.Reach using (module Reached)
open import simultaneous.Project using (run-prefix)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Prefixes using (prefix-≡; prefix-trans; prefix-++; closed-prefix)
open import simultaneous.Relations using (Met; values; values-++; ranked; Left; Exits; Over; lastValue; carried; stampedᴮ; grouped; Closes; Batches; elaborated; batched)
open import simultaneous.Ranks using (unrank; Carries; carried-rel; closed-rel; module Relabel; ranks-x; ranks-b; batch-rank; name-rank; rank-name)
open import simultaneous.Layers using (scan-out; scan-in; each-out; each-in; run-row; at-func; cursor-snoc; run-has; from≺)
open import simultaneous.Batcher using (released; released-held; after; after-snoc; released-++; Stamps; stamps-of; Named; Good; stamped-prefix; stamped-++;
  grouped-run; pending-one; closed-snoc; stamped-asEmits)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; elaborate; Step; bstep; bstart; pending; pendingOf; asEmits; mark-step; Routes; count)

------------------------------------------------------------------------
-- The protocol, read off the elaborated run

-- Marks only, each keeping the batch held, until one releases it.
data Releases {A : Set} : Step A → List (IE A) → Set where
  now  : ∀ {s m n vs} → proj₂ (bstep s (instEmit (mark m) n)) ≢ [] → Releases s (instEmit (mark m) n ∷ vs)
  wait : ∀ {s m n vs} → proj₂ (bstep s (instEmit (mark m) n)) ≡ []
       → Releases (bstep s (instEmit (mark m) n)) vs → Releases s (instEmit (mark m) n ∷ vs)

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

------------------------------------------------------------------------
-- The batcher's routes are the run's count

-- The batcher's routes and instant, as the count reads them; none open
-- during the burst.
Tally : ∀ {A : Set} → Step A → Routes → Set
Tally (b , _) (m , k) = Batching.routes b ≡ k × Batching.at b ≡ m × (Batching.late b ≡ false → k ≡ 0)

-- What the count needs of an emit, the burst flag `b` before it: a begin
-- past the burst, the subscribe mark during it, no completion.
Fits : ∀ {A : Set} → Bool → IE A → Set
Fits b (instEmit (mark Marks.begin) _)      = b ≡ true
Fits b (instEmit (mark Marks.subscribed) _) = b ≡ false
Fits b (instEmit (mark completed) _)        = ⊥
Fits b (instEmit _ _)                       = ⊤

FitsRun : ∀ {A : Set} → Bool → List (IE A) → Set
FitsRun b []       = ⊤
FitsRun b (w ∷ ws) = Fits b w × FitsRun (subStep b w) ws

tally-step : ∀ {A : Set} (s : Step A) r w → Tally s r → Fits (Batching.late (proj₁ s)) w
           → Tally (bstep s w) (count r w) × Batching.late (proj₁ (bstep s w)) ≡ subStep (Batching.late (proj₁ s)) w
tally-step (batching l a h k , rel) _ (instEmit (value _) _) (refl , refl , z) f = (refl , refl , z) , refl
tally-step (batching true a h k , rel) _ (instEmit (mark Marks.begin) n) (refl , refl , z) f with n ≟ᵖ a
... | yes refl = (refl , refl , λ ()) , refl
... | no _     = (refl , refl , λ ()) , refl
tally-step (batching false a h k , rel) _ (instEmit (mark Marks.begin) n) (refl , refl , z) ()
tally-step (batching true a h zero , rel) _ (instEmit (mark Marks.stop) n) (refl , refl , z) f = (refl , refl , λ ()) , refl
tally-step (batching true a h (suc zero) , rel) _ (instEmit (mark Marks.stop) n) (refl , refl , z) f = (refl , refl , λ ()) , refl
tally-step (batching true a h (suc (suc k)) , rel) _ (instEmit (mark Marks.stop) n) (refl , refl , z) f = (refl , refl , λ ()) , refl
tally-step (batching false a h k , rel) _ (instEmit (mark Marks.stop) n) (refl , refl , z) f with z refl
... | refl = (refl , refl , λ _ → refl) , refl
tally-step (batching true a h k , rel) _ (instEmit (mark Marks.over) n) (refl , refl , z) f = (refl , refl , λ ()) , refl
tally-step (batching false a h k , rel) _ (instEmit (mark Marks.over) n) (refl , refl , z) f with z refl
... | refl = (refl , refl , λ _ → refl) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.subscribed) n) (refl , refl , z) f with z f
... | refl = (refl , refl , λ ()) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark completed) n) (refl , refl , z) ()
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.outerOpen) n) (refl , refl , z) f  = (refl , refl , z) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.outerClose) n) (refl , refl , z) f = (refl , refl , z) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.laneStart) n) (refl , refl , z) f  = (refl , refl , z) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.carry) n) (refl , refl , z) f      = (refl , refl , z) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.laneDone) n) (refl , refl , z) f   = (refl , refl , z) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.burstEnd) n) (refl , refl , z) f   = (refl , refl , z) , refl
tally-step (batching l a h k , rel) _ (instEmit (mark Marks.outerDone) n) (refl , refl , z) f  = (refl , refl , z) , refl

tally-run : ∀ {A : Set} (s : Step A) r (xs : List (IE A)) → Tally s r → FitsRun (Batching.late (proj₁ s)) xs
          → Tally (after s xs) (L.foldl count r xs)
tally-run s r []       t _        = t
tally-run s r (w ∷ ws) t (f , fs) with tally-step s r w t f
... | t′ , e = tally-run (bstep s w) (count r w) ws t′ (subst (λ b → FitsRun b ws) (sym e) fs)

-- The count's instant is the last begin's.
count-name : ∀ {A : Set} (r : Routes) (xs : List (IE A)) → L.foldl nameStep (proj₁ r) xs ≡ proj₁ (L.foldl count r xs)
count-name r       []                                     = refl
count-name (m , k) (instEmit (mark Marks.begin) n ∷ xs) with n ≟ᵖ m
... | yes refl = count-name (n , suc k) xs
... | no _     = count-name (n , 1) xs
count-name (m , k) (instEmit (mark Marks.stop) _ ∷ xs)  = count-name (m , k ∸ 1) xs
count-name (m , k) (instEmit (mark Marks.over) _ ∷ xs)  = count-name (m , 0) xs
count-name r       (instEmit (value _) _ ∷ xs)            = count-name r xs
count-name r       (instEmit (mark Marks.subscribed) _ ∷ xs) = count-name r xs
count-name r       (instEmit (mark completed) _ ∷ xs)        = count-name r xs
count-name r       (instEmit (mark Marks.outerOpen) _ ∷ xs)  = count-name r xs
count-name r       (instEmit (mark Marks.outerClose) _ ∷ xs) = count-name r xs
count-name r       (instEmit (mark Marks.laneStart) _ ∷ xs)  = count-name r xs
count-name r       (instEmit (mark Marks.carry) _ ∷ xs)      = count-name r xs
count-name r       (instEmit (mark Marks.laneDone) _ ∷ xs)   = count-name r xs
count-name r       (instEmit (mark Marks.burstEnd) _ ∷ xs)   = count-name r xs
count-name r       (instEmit (mark Marks.outerDone) _ ∷ xs)  = count-name r xs

-- The run meets what the count needs, up to its completion.
module Count {A : Set} (o : SObs [] A) {rx} (mx : Met (elaborated o) rx) where
  open Leaves o mx using (begin-late; sub-once)

  fit : ∀ pre w rest → values rx ≡ pre ++ w ∷ rest → Fits (seenSub pre) w ⊎ Σ Pos λ m → w ≡ instEmit (mark completed) m
  fit pre (instEmit (mark Marks.begin) n) rest e      = inj₁ (begin-late pre n rest e)
  fit pre (instEmit (mark Marks.subscribed) n) rest e = inj₁ (sub-once pre n rest e)
  fit pre (instEmit (mark completed) n) rest e        = inj₂ (n , refl)
  fit pre (instEmit (value _) _) rest e               = inj₁ tt
  fit pre (instEmit (mark Marks.stop) _) rest e       = inj₁ tt
  fit pre (instEmit (mark Marks.over) _) rest e       = inj₁ tt
  fit pre (instEmit (mark Marks.outerOpen) _) rest e  = inj₁ tt
  fit pre (instEmit (mark Marks.outerClose) _) rest e = inj₁ tt
  fit pre (instEmit (mark Marks.laneStart) _) rest e  = inj₁ tt
  fit pre (instEmit (mark Marks.carry) _) rest e      = inj₁ tt
  fit pre (instEmit (mark Marks.laneDone) _) rest e   = inj₁ tt
  fit pre (instEmit (mark Marks.burstEnd) _) rest e   = inj₁ tt
  fit pre (instEmit (mark Marks.outerDone) _) rest e  = inj₁ tt

  fits : ∀ pre xs ys → values rx ≡ pre ++ xs ++ ys
       → FitsRun (seenSub pre) xs ⊎ Σ (List (IE A)) λ c₁ → Σ (List (IE A)) λ c₂ → Σ Pos λ m → xs ≡ c₁ ++ instEmit (mark completed) m ∷ c₂
  fits pre []       ys e = inj₁ tt
  fits pre (w ∷ ws) ys e with fit pre w (ws ++ ys) e
  ... | inj₂ (m , refl) = inj₂ ([] , ws , m , refl)
  ... | inj₁ f with fits (pre ++ [ w ]) ws ys (trans e (sym (++-assoc pre [ w ] (ws ++ ys))))
  ...   | inj₁ fs                    = inj₁ (f , subst (λ b → FitsRun b ws) (ss-snoc pre w) fs)
  ...   | inj₂ (c₁ , c₂ , m , refl) = inj₂ (w ∷ c₁ , c₂ , m , refl)

-- A run split where its values split.
split-at : ∀ {X : Set} (rs : List (Pos × Ev X)) xs ys → values rs ≡ xs ++ ys
         → Σ _ λ r₁ → Σ _ λ r₂ → rs ≡ r₁ ++ r₂ × values r₁ ≡ xs × values r₂ ≡ ys
split-at rs []       ys e = [] , rs , refl , refl , e
split-at rs (x ∷ xs) ys e with Split.split rs [] x (xs ++ ys) e
... | r₁ , r₂ , k , refl , e₁ , e₂ with split-at r₂ xs ys e₂
...   | s₁ , s₂ , refl , f₁ , f₂ =
  r₁ ++ (k , out x) ∷ s₁ , s₂ , sym (++-assoc r₁ ((k , out x) ∷ s₁) s₂) ,
  trans (values-++ r₁ ((k , out x) ∷ s₁)) (cong₂ _++_ e₁ (cong (x ∷_) f₁)) , f₂

-- A row met is a row.
row-of : ∀ {A : Set} (o : SObs [] A) {rs k x} → Met (elaborated o) rs → (k , x) ∈ rs → elaborated o k x
row-of o mx h = proj₁ (run-row mx h)

-- PAST THE SUBSCRIBE BURST, A DEAD INSTANT STAYS DEAD at the top: the
-- count's instant is its last begin's, named for the begin's position,
-- or the subscribe frame, which no value past the burst is of.
top-shut : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs ys → values rx ≡ xs ++ ys → seenSub xs ≡ true
         → proj₂ (L.foldl count r₀ xs) ≡ 0 → ∀ {a} → instEmit (value a) (proj₁ (L.foldl count r₀ xs)) ∈ ys → ⊥
top-shut o {rx} mx xs ys e s z {a} v with split-at rx xs ys e
... | r₁ , r₂ , refl , refl , refl with Split.val-in r₂ v | lb-view root (values r₁)
...   | y , ym | inj₂ hb with Split.val-in r₁ (subst (λ i → instEmit (mark Marks.begin) i ∈ values r₁) (count-name r₀ (values r₁)) hb)
...     | q , qm = shut o mx r₁ r₂ refl z qm ym
                   (cong (_∙ []) (trans (sym (named o (row-of o mx (∈-++⁺ʳ r₁ ym)))) (named o (row-of o mx (∈-++⁺ˡ qm)))))
top-shut o {rx} mx xs ys e s z {a} v | r₁ , r₂ , refl , refl , refl | y , ym | inj₁ e₀ with seen-sub false (values r₁) s
... | inj₁ ()
... | inj₂ (m , hm) with Split.val-in r₁ hm | ∈-∃++ ym
...   | ks , km | r₂a , r₂b , refl =
  Leaves.async-name o mx (row-of o mx (∈-++⁺ʳ r₁ ym))
    (sub-async o (row-of o mx (∈-++⁺ˡ km)) (row-of o mx (∈-++⁺ʳ r₁ ym))
      (Split.run-before (r₁ ++ r₂a) (subst (Met (elaborated o)) (sym (++-assoc r₁ r₂a _)) mx) (∈-++⁺ˡ km)))
    (trans (sym (count-name r₀ (values r₁))) e₀)

-- PAST THE LAST ROUTE'S STOP, the next value is of another instant: the
-- batcher's routes are the run's count, which the stop empties.
stop-fresh : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → ∀ xs n ys
           → values rx ≡ xs ++ instEmit (mark Marks.stop) n ∷ ys → seenSub xs ≡ true
           → Batching.routes (proj₁ (after bstart xs)) ≤ 1 → Fresh (lastBegin root xs) (stamped ys)
stop-fresh o {rx} mx xs n ys e s le with Count.fits o mx [] xs (instEmit (mark Marks.stop) n ∷ ys) e
... | inj₂ (c₁ , c₂ , m , refl) =
  subst (Fresh (lastBegin root (c₁ ++ instEmit (mark completed) m ∷ c₂))) (sym gone) tt
  where
    gone : stamped ys ≡ []
    gone = ++-conicalʳ (stamped c₂) (stamped ys)
      (trans (sym (stamped-++ c₂ (instEmit (mark Marks.stop) n ∷ ys)))
        (Leaves.completed-end o mx c₁ m (c₂ ++ instEmit (mark Marks.stop) n ∷ ys) (trans e (++-assoc c₁ _ _))))
... | inj₁ fs with tally-run bstart r₀ xs (refl , refl , λ _ → refl) fs
...   | er , _ , _ = fresh-all (lastBegin root xs) ys λ v eq → top-shut o mx (xs ++ [ w ]) ys e′ s′ z′ (renamed v eq)
  where
    w = instEmit (mark Marks.stop) n
    K = L.foldl count r₀ xs
    split : L.foldl count r₀ (xs ++ [ w ]) ≡ count K w
    split = foldl-++ count r₀ xs [ w ]
    e′ : values rx ≡ (xs ++ [ w ]) ++ ys
    e′ = trans e (sym (++-assoc xs [ w ] ys))
    s′ : seenSub (xs ++ [ w ]) ≡ true
    s′ = trans (ss-snoc xs w) s
    z′ : proj₂ (L.foldl count r₀ (xs ++ [ w ])) ≡ 0
    z′ = trans (cong proj₂ split) (m≤n⇒m∸n≡0 (subst (_≤ 1) er le))
    renamed : ∀ {a j} → instEmit (value a) j ∈ ys → lastBegin root xs ≡ j → instEmit (value a) (proj₁ (L.foldl count r₀ (xs ++ [ w ]))) ∈ ys
    renamed {a} v eq = subst (λ i → instEmit (value a) i ∈ ys) (trans (sym eq) (trans (count-name r₀ xs) (sym (cong proj₁ split)))) v

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
    go s@(batching l a h r , rel) xs (w@(instEmit (mark Marks.carry) _) ∷ ys) eq es ea el e0 (_ , st)      = continue s xs w ys eq es st (tt , inj₁ refl) ea el e0

    continue : ∀ (s : Step A) xs w ys → ws ≡ xs ++ w ∷ ys → after bstart xs ≡ s → Stamps (nameStep (lastBegin root xs) w) ys
             → (Named (proj₁ s) w × (proj₂ (bstep s w) ≡ [] ⊎ Fresh (Batching.at (proj₁ s)) (stamped ys)))
             → Batching.at (proj₁ (bstep s w)) ≡ nameStep (lastBegin root xs) w
             → Batching.late (proj₁ (bstep s w)) ≡ subStep (seenSub xs) w
             → (subStep (seenSub xs) w ≡ false → nameStep (lastBegin root xs) w ≡ root)
             → Good s (w ∷ ys)
    continue s xs w ys eq es st now′ ea′ el′ e0′ =
      now′ ,
      go (bstep s w) (xs ++ [ w ]) ys (trans eq (sym (++-assoc xs [ w ] ys))) (trans (after-snoc bstart xs w) (cong (λ t → bstep t w) es))
         (trans ea′ (sym (lb-snoc xs w))) (trans el′ (sym (ss-snoc xs w)))
         (λ f → trans (lb-snoc xs w) (e0′ (trans (sym (ss-snoc xs w)) f)))
         (subst (λ x → Stamps x ys) (sym (lb-snoc xs w)) st)

-- THE ELABORATED RUN IS GOOD: the batcher, walked along it, meets the
-- protocol at every mark.
good-run : ∀ {A : Set} (o : SObs [] A) {rx} → Met (elaborated o) rx → Good bstart (values rx)
good-run o {rx} mx = Walk.go o mx bstart [] (values rx) refl refl refl refl (λ _ → refl) (stamps-of o mx)

------------------------------------------------------------------------
-- Runs met on

-- A run's cursor is no earlier than where it began.
cursor-≽ : ∀ {A} {t : EmissionSet A} {q} xs → Run t (just q) xs → Σ Pos λ c → cursor (just q) xs ≡ just c × q ≼ c
cursor-≽ {q = q} []          []                        = q , refl , ≼-refl {q}
cursor-≽ {q = q} ((q′ , _) ∷ xs) ((_ , _ , aft , _) ∷ run) with cursor-≽ xs run
... | c , eq , qc = c , eq , ≼-trans {q} {q′} {c} (≺→≼ {q} {q′} aft) qc

-- No row a run met lies past its cursor.
not-past : ∀ {A} {t : EmissionSet A} {c xs k e} → Run t c xs → (k , e) ∈ xs → After (cursor c xs) k → ⊥
not-past {xs = (q , _) ∷ xs} (_ ∷ run) (here refl) a with cursor-≽ xs run
... | c , eq , qc = qc (subst (λ m → After m q) eq a)
not-past (_ ∷ run) (there m) a = not-past run m a

-- A cursor is where the run began or a row it met.
cursor-in : ∀ {A} c (xs : List (Pos × Ev A)) {y} → cursor c xs ≡ just y → c ≡ just y ⊎ Σ (Ev A) λ e → (y , e) ∈ xs
cursor-in c []             eq = inj₁ eq
cursor-in c ((q , e) ∷ xs) eq with cursor-in (just q) xs eq
... | inj₁ refl     = inj₂ (e , here refl)
... | inj₂ (e′ , m) = inj₂ (e′ , there m)

cursor-cases : ∀ {A} (xs : List (Pos × Ev A)) → cursor nothing xs ≡ nothing ⊎ Σ Pos λ c → cursor nothing xs ≡ just c
cursor-cases xs with cursor nothing xs
... | nothing = inj₁ refl
... | just c  = inj₂ (c , refl)

-- No visible row up to `y` is left past the run.
Covers : ∀ {A : Set} → EmissionSet A → List (Pos × Ev A) → Pos → Set
Covers t rs y = ∀ {k e} → t k e → Visible e → k ≼ y → After (cursor nothing rs) k → ⊥

-- No visible row is left past the run.
Dry : ∀ {A : Set} → EmissionSet A → List (Pos × Ev A) → Set
Dry t rs = ∀ {k e} → t k e → Visible e → After (cursor nothing rs) k → ⊥

-- A RUN IS MET ON PAST ANY ROW WITH FINITELY MANY BEFORE IT: some
-- extension meets every visible row up to it.  The rows before `y` are
-- listed (`listed`) and the latest visible one past the run is met as
-- `Reaching.reach` meets a row, the two runs comparable by `run-det`;
-- what is open is `y` itself, whose row a listing before `y` omits — a
-- listing up to a position just past `y`.
postulate
  pass : ∀ {A : Set} (o : SObs [] A) {rs y} → Met (elaborated o) rs → Few (elaborated o) y
       → Σ _ λ ext → Met (elaborated o) (rs ++ ext) × Covers (elaborated o) (rs ++ ext) y

-- A visible row past a run is met on it.
meet : ∀ {A : Set} (o : SObs [] A) {rs y e} → Met (elaborated o) rs → Seen (elaborated o) y e → Visible e
     → After (cursor nothing rs) y → Σ _ λ ext → Met (elaborated o) (rs ++ ext) × (y , e) ∈ ext
meet {A} o {rs} {y} {e} mx ((xy , _) , fy) vi ay with pass o mx fy
... | ext , mx′ , cv = found (cursor-cases (rs ++ ext))
  where
    found : (cursor nothing (rs ++ ext) ≡ nothing ⊎ Σ Pos λ c → cursor nothing (rs ++ ext) ≡ just c)
          → Σ _ λ ext′ → Met (elaborated o) (rs ++ ext′) × (y , e) ∈ ext′
    found (inj₁ eq) = ⊥-elim (cv xy vi (≼-refl {y}) (subst (λ c → After c y) (sym eq) tt))
    found (inj₂ (c , eq)) with cursor-in nothing (rs ++ ext) eq
    ... | inj₁ ()
    ... | inj₂ (_ , cm) with ∈-++⁻ rs (run-has (at-func (elaborate o)) mx′ xy vi tt (λ cy → cv xy vi (≼-refl {y}) (subst (λ m → After m y) (sym eq) cy)) cm)
    ...   | inj₁ m = ⊥-elim (not-past mx m ay)
    ...   | inj₂ m = ext , mx′ , m

-- Rows past one with finitely many before it, finitely many, leave
-- finitely many before any row.
few-past : ∀ {A} {t : EmissionSet A} {q ks} → Few t q → (∀ {y e} → t y e → q ≺ y → y ∈ ks) → ∀ {b} → Few t b
few-past {t = t} {q = q} {ks} (fs , cover) past = fs ++ q ∷ ks , λ {y} x _ → at y x
  where
    at : ∀ y {e} → t y e → y ∈ fs ++ q ∷ ks
    at y x with T? (y <ᵖ q)
    ... | yes yq = ∈-++⁺ˡ (cover x yq)
    ... | no qy with ≼-split {q} {y} qy
    ...   | inj₁ qy′ = ∈-++⁺ʳ fs (there (past x qy′))
    ...   | inj₂ refl = ∈-++⁺ʳ fs (here refl)

-- The latest of a list of positions, and a start.
maxᵖ : Pos → List Pos → Pos
maxᵖ b []       = b
maxᵖ b (k ∷ ks) with T? (b <ᵖ k)
... | yes _ = maxᵖ k ks
... | no _  = maxᵖ b ks

max-≽ : ∀ b ks → b ≼ maxᵖ b ks
max-≽ b []       = ≼-refl {b}
max-≽ b (k ∷ ks) with T? (b <ᵖ k)
... | yes bk = ≼-trans {b} {k} {maxᵖ k ks} (≺→≼ {b} {k} bk) (max-≽ k ks)
... | no _   = max-≽ b ks

max-∈ : ∀ b ks {k} → k ∈ ks → k ≼ maxᵖ b ks
max-∈ b (k ∷ ks) (here refl) with T? (b <ᵖ k)
... | yes _ = max-≽ k ks
... | no kb = ≼-trans {k} {b} {maxᵖ b ks} kb (max-≽ b ks)
max-∈ b (k ∷ ks) (there m) with T? (b <ᵖ k)
... | yes _ = max-∈ k ks m
... | no _  = max-∈ b ks m

------------------------------------------------------------------------
-- The last value met

last-in : ∀ {X : Set} (xs : List X) {y} → L.last xs ≡ just y → y ∈ xs
last-in []           ()
last-in (x ∷ [])     refl = here refl
last-in (x ∷ y ∷ ys) e    = there (last-in (y ∷ ys) e)

last-none : ∀ {X : Set} (xs : List X) → L.last xs ≡ nothing → xs ≡ []
last-none []           _ = refl
last-none (x ∷ [])     ()
last-none (x ∷ y ∷ ys) e with last-none (y ∷ ys) e
... | ()

carried-in : ∀ {A B : Set} (f : A → List B) (rx : List (Pos × Ev (ℕ × A))) {q n b} → (q , n , b) ∈ carried f rx
           → Σ A λ a → (q , out (n , a)) ∈ rx
carried-in f ((q , out (n , a)) ∷ rx) m with ∈-++⁻ (L.map (λ b → q , n , b) (f a)) m
... | inj₁ m₁ with ∈-map⁻ (λ b → q , n , b) m₁
...   | _ , _ , refl = a , here refl
carried-in f ((q , out (n , a)) ∷ rx) m | inj₂ m₂ with carried-in f rx m₂
...   | a′ , m′ = a′ , there m′
carried-in f ((_ , skip) ∷ rx)  m with carried-in f rx m
... | a′ , m′ = a′ , there m′
carried-in f ((_ , end) ∷ rx)   m with carried-in f rx m
... | a′ , m′ = a′ , there m′
carried-in f ((_ , pin _) ∷ rx) m with carried-in f rx m
... | a′ , m′ = a′ , there m′

-- The last value met is a row.
last-row : ∀ {A : Set} (o : SObs [] A) {rx q} → Met (ranked (elaborated o)) rx → lastValue valuesOf rx ≡ just q
         → Σ (IE A) λ x → elaborated o q (out x)
last-row o {rx} mxr lv with ∈-map⁻ proj₁ (last-in (L.map proj₁ (carried valuesOf rx)) lv)
... | (_ , _ , _) , cm , refl with carried-in valuesOf rx cm
...   | a , rm = a , proj₁ (proj₁ (run-row mxr rm))

-- No value met, nothing held.
none-carried : ∀ {A : Set} (rx : List (Pos × Ev (ℕ × IE A))) → L.map proj₁ (carried valuesOf rx) ≡ []
             → concatMap valuesOf (values (unrank rx)) ≡ []
none-carried []                                         _ = refl
none-carried ((_ , out (_ , instEmit (value _) _)) ∷ _)  ()
none-carried ((_ , out (_ , instEmit (mark _) _)) ∷ rx)  e = none-carried rx e
none-carried ((_ , skip) ∷ rx)                           e = none-carried rx e
none-carried ((_ , end) ∷ rx)                            e = none-carried rx e
none-carried ((_ , pin _) ∷ rx)                          e = none-carried rx e

none-held : ∀ {A : Set} (rx : List (Pos × Ev (ℕ × IE A))) → lastValue valuesOf rx ≡ nothing
          → pending (proj₁ (after bstart (values (unrank rx)))) ≡ []
none-held rx lv = cong (pendingOf (Batching.at (proj₁ (after bstart (values (unrank rx))))))
  (++-conicalʳ _ _ (trans (released-held bstart (values (unrank rx))) (none-carried rx (last-none _ lv))))

------------------------------------------------------------------------
-- The release

-- Finitely many rows of `q`'s instant lie past it.
Bounded : ∀ {A : Set} → EmissionSet A → Pos → Set
Bounded t q = Σ (List Pos) λ ks → ∀ {y e} → t y e → q ≺ y → instantOf y ≡ instantOf q → y ∈ ks

-- How a release at `k` leaves the instant of the value `q` before it,
-- the run met through the release `rk`: at a row of another instant, at
-- the end of the subscribe burst or the completion, or at a count
-- holding no route of the instant last begun.
data How {A : Set} (o : SObs [] A) (q : Pos) (rk : List (Pos × Ev (IE A))) (k : Pos) : Set where
  apart : instantOf k ≢ instantOf q → How o q rk k
  sub   : ∀ {m} → elaborated o k (out (instEmit (mark Marks.subscribed) m)) → instantOf q ≡ frame → How o q rk k
  done  : ∀ {m} → elaborated o k (out (instEmit (mark completed) m)) → How o q rk k
  emptied : ∀ {b} → proj₂ (cnt rk) ≡ 0 → (b , out (instEmit (mark Marks.begin) (proj₁ (cnt rk)))) ∈ rk → rootOf b ≡ rootOf q
        → How o q rk k

-- Where a run released the value `q`: at a mark past it, no value between.
record Release {A : Set} (o : SObs [] A) (rs : List (Pos × Ev (IE A))) (q : Pos) : Set where
  field
    r₁ r₂ : List (Pos × Ev (IE A))
    k     : Pos
    mk    : Marks.Mark
    nk    : Pos
    split : rs ≡ (r₁ ++ [ (k , out (instEmit (mark mk) nk)) ]) ++ r₂
    past  : q ≺ k
    none  : ∀ {y a j} → elaborated o y (out (instEmit (value a) j)) → q ≺ y → y ≺ k → ⊥
    how   : How o q (r₁ ++ [ (k , out (instEmit (mark mk) nk)) ]) k

-- WHERE THE BATCH WENT: past the last value met, with nothing held, a
-- mark of the run released it.  The batcher releases only at a mark,
-- each release named by `marking`: a begin of a name other than the one
-- held, of another instant (`one-name`, `named`); the subscribe mark,
-- whose burst is the frame's; the completion; an over or the last
-- route's stop, which leave the count at zero under the instant's begin.
postulate
  release-at : ∀ {A : Set} (o : SObs [] A) {rx q} → Met (ranked (elaborated o)) rx
             → pending (proj₁ (after bstart (values (unrank rx)))) ≡ [] → lastValue valuesOf rx ≡ just q
             → Release o (unrank rx) q

-- The completion mark comes before the end: the run's last `of` is
-- the completion's, which completes as it emits.
postulate
  done-end : ∀ {A : Set} (o : SObs [] A) {k m} → elaborated o k (out (instEmit (mark completed) m))
           → Σ Pos λ c → elaborated o c end × k ≺ c

-- Past the subscribe mark, finitely many rows of the subscribe frame:
-- the mark is the frame's last emit, and what the frame does past it is
-- the completion of the mark's own `of`.
postulate
  sub-rest : ∀ {A : Set} (o : SObs [] A) {k m} → elaborated o k (out (instEmit (mark Marks.subscribed) m))
           → Σ (List Pos) λ ks → ∀ {y e} → elaborated o y e → k ≺ y → instantOf y ≡ frame → y ∈ ks

-- A VALUE WHOSE INSTANT FINISHES IS LEFT: past finitely many rows of its
-- instant, the program reaches a row of another instant or its end, or
-- makes no row at all.  Which, is decided by the program: every leaf's
-- timeline forces to its next frame or to `done` or `quiet`, so the next
-- row past a position is decided the way `listed` decides the rows
-- before one.
postulate
  exits-bounded : ∀ {A : Set} (o : SObs [] A) {q x} → elaborated o q (out x) → Bounded (elaborated o) q → Exits (elaborated o) q

-- PAST A RELEASE, THE INSTANT IS OVER: no value of it, and the run
-- leaves it.
module Released {A : Set} (o : SObs [] A) {rs q} (mx : Met (elaborated o) rs) (R : Release o rs q)
                (xq : Σ (IE A) λ x → elaborated o q (out x)) where
  open Release R
  open Reached (⟦ elaborate o ⟧ []) root (inv-⟦⟧ (elaborate o) [] (λ ()) root (tt , λ ())) using (seen)

  X = elaborated o

  rk : List (Pos × Ev (IE A))
  rk = r₁ ++ [ (k , out (instEmit (mark mk) nk)) ]

  mrk : Met X rk
  mrk = run-prefix rk (subst (Met X) split mx)

  xk : X k (out (instEmit (mark mk) nk))
  xk = proj₁ (run-row mrk (∈-++⁺ʳ r₁ (here refl)))

  ck : cursor nothing rk ≡ just k
  ck = cursor-snoc nothing r₁

  -- Past the release, no value of `q`'s instant.
  beyond : ∀ {y a j} → How o q rk k → X y (out (instEmit (value a) j)) → k ≺ y → instantOf y ≡ instantOf q → ⊥
  beyond {y} (apart ne)     xy ky iy = ne (between {q} {k} {y} (from≺ q k past) (from≺ k y ky) (sym iy))
  beyond     (sub xs fq)    xy ky iy = sub-async o xs xy ky (trans iy fq)
  beyond {y} (done xc)      xy ky iy = ≺-absurd {k} {y} ky (done-last o xy xc)
  beyond {y} (emptied z bm rb) xy ky iy with meet o mrk (seen xy tt) tt (subst (λ c → After c y) (sym ck) ky)
  ... | ext , mx′ , yin = shut o mx′ rk ext refl z bm yin (trans (cong (_∙ []) iy) (sym rb))

  gone : ∀ {y a j} → X y (out (instEmit (value a) j)) → q ≺ y → instantOf y ≡ instantOf q → ⊥
  gone {y} xy qy iy with T? (y <ᵖ k)
  ... | yes yk = none xy qy yk
  ... | no ky with ≼-split {k} {y} ky
  ...   | inj₁ ky′ = beyond how xy ky′ iy
  ...   | inj₂ refl with at-func (elaborate o) xk xy
  ...     | ()

  left : Left valuesOf X q
  left {a = instEmit (mark _) _}  _  _  _  = refl
  left {a = instEmit (value _) _} xy qy iy = ⊥-elim (gone xy qy iy)

  -- Rows of `q`'s instant past `k`, finitely many, leave finitely many past `q`.
  bounded : ∀ {ks} → (∀ {y e} → X y e → k ≺ y → instantOf y ≡ instantOf q → y ∈ ks) → Bounded X q
  bounded {ks} h with proj₂ (seen xk tt)
  ... | fs , cover = fs ++ k ∷ ks , λ {y} xy _ iy → at y xy iy
    where
      at : ∀ y {e} → X y e → instantOf y ≡ instantOf q → y ∈ fs ++ k ∷ ks
      at y xy iy with T? (y <ᵖ k)
      ... | yes yk = ∈-++⁺ˡ (cover xy yk)
      ... | no ky with ≼-split {k} {y} ky
      ...   | inj₁ ky′ = ∈-++⁺ʳ fs (there (h xy ky′ iy))
      ...   | inj₂ refl = ∈-++⁺ʳ fs (here refl)

  exits : Exits X q
  exits = by how
    where
      by : How o q rk k → Exits X q
      by (apart ne) = inj₁ (k , _ , seen xk tt , past , inj₁ ne)
      by (done xc) with done-end o xc
      ... | c , xe , kc = inj₁ (c , end , seen xe tt , ≺-trans {q} {k} {c} past kc , inj₂ refl)
      by (sub xs fq) with sub-rest o xs
      ... | ks , h = exits-bounded o (proj₂ xq) (bounded {ks} λ xy ky iy → h xy ky (trans iy fq))
      by (emptied z bm rb) with Held.rest (held o) mrk z bm
      ... | ks , h = exits-bounded o (proj₂ xq)
                       (bounded {ks} λ {y} xy ky iy → h xy (subst (λ c → After c y) (sym ck) ky) (trans (cong (_∙ []) iy) (sym rb)))

-- THE RUN IS CLOSED WHERE NOTHING IS HELD: past every release, no value
-- of the instant released, and the run leaves it.
flush-closes : ∀ {A : Set} (o : SObs [] A) {rx} → Met (ranked (elaborated o)) rx → pending (proj₁ (after bstart (values (unrank rx)))) ≡ []
             → Closes valuesOf (elaborated o) rx true
flush-closes o {rx} mxr e = go (lastValue valuesOf rx) refl
  where
    go : ∀ v → lastValue valuesOf rx ≡ v → Over valuesOf (elaborated o) v
    go nothing  _  = tt
    go (just q) lv = left , exits
      where open Released o (proj₂ (ranks-x o) mxr) (release-at o mxr e lv) (last-row o mxr lv)

-- Where a run met past `q` has left `q`'s instant: through a row of
-- another instant or the end, or with no visible row left.
data Gone {A : Set} (o : SObs [] A) (q : Pos) (rs : List (Pos × Ev (IE A))) : Set where
  moved : ∀ {k e} → elaborated o k e → q ≺ k → (instantOf k ≢ instantOf q ⊎ e ≡ end) → Covers (elaborated o) rs k → Gone o q rs
  dry   : Dry (elaborated o) rs → Gone o q rs

-- A HELD BATCH IS RELEASED BEFORE THE RUN LEAVES ITS INSTANT, by marks
-- only.  The run meets no value of the held instant (`Left`), and a value
-- of another is named for a begin of its own (`Stamps`), which releases;
-- the end follows the completion, which releases; and once no visible row
-- is left, the instant's last over or stop has been met, which releases.
postulate
  release-on : ∀ {A : Set} (o : SObs [] A) {rx q ext} → Met (ranked (elaborated o)) rx → lastValue valuesOf rx ≡ just q
             → Left valuesOf (elaborated o) q → Met (elaborated o) (unrank rx ++ ext) → Gone o q (unrank rx ++ ext)
             → pending (proj₁ (after bstart (values (unrank rx)))) ≢ []
             → Σ _ λ e₁ → Σ _ λ e₂ → ext ≡ e₁ ++ e₂ × Releases (after bstart (values (unrank rx))) (values e₁)

-- A CLOSED INSTANT IS RELEASED: met on, the run reaches a mark releasing
-- what is held, with no value before it.
releases : ∀ {A : Set} (o : SObs [] A) {rx} → Met (ranked (elaborated o)) rx → Closes valuesOf (elaborated o) rx true
         → pending (proj₁ (after bstart (values (unrank rx)))) ≢ []
         → Σ _ λ ext → Met (elaborated o) (unrank rx ++ ext) × Releases (after bstart (values (unrank rx))) (values ext)
releases {A} o {rx} mxr cl ne = go (lastValue valuesOf rx) refl cl
  where
    X = elaborated o
    mx = proj₂ (ranks-x o) mxr
    open Reached (⟦ elaborate o ⟧ []) root (inv-⟦⟧ (elaborate o) [] (λ ()) root (tt , λ ())) using (seen)

    leave : ∀ {q} → Σ (IE A) (λ x → X q (out x)) → Exits X q → Σ _ λ ext → Met X (unrank rx ++ ext) × Gone o q (unrank rx ++ ext)
    leave _ (inj₁ (k , e , ((xk , _) , fk) , qk , ne′)) with pass o mx fk
    ... | ext , mx′ , cv = ext , mx′ , moved xk qk ne′ cv
    leave {q} (_ , xq) (inj₂ (ks , h)) with pass o mx (few-past (proj₂ (seen xq tt)) (λ xy qy → proj₁ (h xy qy)) {maxᵖ q ks})
    ... | ext , mx′ , cv = ext , mx′ , dry λ {k} xk vi ak → cv xk vi (below k xk) ak
      where
        below : ∀ k {e} → X k e → k ≼ maxᵖ q ks
        below k xk with T? (q <ᵖ k)
        ... | yes qk = max-∈ q ks (proj₁ (h xk qk))
        ... | no kq  = ≼-trans {k} {q} {maxᵖ q ks} kq (max-≽ q ks)

    go : ∀ v → lastValue valuesOf rx ≡ v → Over valuesOf X v
       → Σ _ λ ext → Met X (unrank rx ++ ext) × Releases (after bstart (values (unrank rx))) (values ext)
    go nothing  lv _ = ⊥-elim (ne (none-held rx lv))
    go (just q) lv (left , ex) with leave (last-row o mxr lv) ex
    ... | ext , mx′ , g with release-on o mxr lv left mx′ g ne
    ...   | e₁ , e₂ , refl , r = e₁ , run-prefix (unrank rx ++ e₁) (subst (Met X) (sym (++-assoc (unrank rx) e₁ e₂)) mx′) , r

-- Closed or not, what is held is released along some extension.
Flushes : ∀ {A : Set} (o : SObs [] A) → List (Pos × Ev (IE A)) → Bool → Set
Flushes o rx false = ⊤
Flushes o rx true  = Σ _ λ ext → Met (elaborated o) (rx ++ ext)
                   × Prefix _≡_ (pending (proj₁ (after bstart (values rx)))) (stamped (released (after bstart (values rx)) (values ext)))

closes-flush : ∀ {A : Set} (o : SObs [] A) {rx} → Met (ranked (elaborated o)) rx → Closes valuesOf (elaborated o) rx true
             → Flushes o (unrank rx) true
closes-flush o {rx} mx cl with pending-one (proj₁ (after bstart (values (unrank rx))))
... | inj₁ e = [] , subst (Met (elaborated o)) (sym (++-identityʳ (unrank rx))) (proj₂ (ranks-x o) mx) , subst (λ P → Prefix _≡_ P _) (sym e) Prefix.[]
... | inj₂ (g , e) with releases o mx cl (λ e′ → one≢[] (trans (sym e) e′))
...   | ext , mx′ , r = ext , mx′ , released-pending _ r (λ e′ → one≢[] (trans (sym e) e′))

------------------------------------------------------------------------
-- The batcher batches as the spec groups

-- The batches, by name: what the batcher has released is the spec's
-- grouping of the run's values by name, the last group once nothing is held.
byName : ∀ {A : Set} → Bool → List (Pos × Ev (IE A)) → List (Pos × List A)
byName ov rx = closed ov (batchSimultaneousᴰ (stamped (values rx)))

batches : ∀ {A : Set} (o : SObs [] A) → Batches (batched o) (elaborated o)
batches o = early , late
  where
    S = scan bstep bstart (elaborate o)
    X = elaborated o
    B = batched o
    open Relabel _≟ᵖ_ _≟_ (Carries X) using (Lab; group-rel; prefix-rel)

    -- Names to ranks: the batches carry the ranks of the values they release.
    bs-rel : ∀ {rs} → Met (ranked B) rs → Pointwise.Pointwise Lab (stamped (values (unrank rs))) (stampedᴮ rs)
    bs-rel mb = Pointwise.map (λ ce → batch-rank o (proj₁ ce) , proj₂ ce) (carried-rel mb)

    groups : ∀ ov {rx} → Met (ranked X) rx → Pointwise.Pointwise Lab (byName ov (unrank rx)) (grouped ov (stampedᴮ rx))
    groups ov mx = closed-rel ov (group-rel (name-rank o) (rank-name o) (carried-rel mx))

    early₀ : ∀ {rs} → Met B rs → Σ _ λ rx → Met X rx
           × ((pending (proj₁ (after bstart (values rx))) ≡ [] × Prefix _≡_ (stamped (values rs)) (byName true rx))
             ⊎ Prefix _≡_ (stamped (values rs)) (byName false rx))
    early₀ {rs} mb with each-out proj₂ S mb
    ... | sc , ms , pre , _ with scan-out bstep bstart (elaborate o) ms
    ...   | rx , mx , eqs , _ with pending-one (proj₁ (after bstart (values rx)))
    ...     | inj₁ e = rx , mx , inj₁ (e ,
                prefix-trans out⊑ (prefix-≡ (trans (sym (++-identityʳ _)) (trans (cong (stamped (released bstart (values rx)) ++_) (sym e)) run))))
      where
        out⊑ = stamped-prefix (prefix-trans pre (prefix-≡ (cong (concatMap proj₂) eqs)))
        run = grouped-run bstart (values rx) (good-run o mx)
    ...     | inj₂ (g , e) = rx , mx , inj₂
                (prefix-trans out⊑ (prefix-≡ (sym (trans (cong (closed false) (sym (trans (cong (stamped (released bstart (values rx)) ++_) (sym e)) run)))
                                                         (closed-snoc (stamped (released bstart (values rx))) g)))))
      where
        out⊑ = stamped-prefix (prefix-trans pre (prefix-≡ (cong (concatMap proj₂) eqs)))
        run = grouped-run bstart (values rx) (good-run o mx)

    early : ∀ {rs} → Met (ranked B) rs → Σ _ λ rx → Σ Bool λ ov → Met (ranked X) rx × Closes valuesOf X rx ov
          × Prefix _≡_ (stampedᴮ rs) (grouped ov (stampedᴮ rx))
    early {rs} mbr with early₀ (proj₂ (ranks-b o) mbr)
    ... | rx₀ , mx , c with proj₁ (ranks-x o) mx
    ...   | rx , mxr , refl with c
    ...     | inj₁ (e , pre) = rx , true , mxr , flush-closes o mxr e , prefix-rel (name-rank o) (bs-rel mbr) (groups true mxr) pre
    ...     | inj₂ pre       = rx , false , mxr , tt , prefix-rel (name-rank o) (bs-rel mbr) (groups false mxr) pre

    -- what is met of the batched program, from what is met of the elaborated
    met-from : ∀ {rx} → Met X rx → Σ _ λ rs → Met B rs × stamped (values rs) ≡ stamped (released bstart (values rx))
    met-from mx with scan-in bstep bstart (elaborate o) mx
    ... | sc , ms , eqs , _ with each-in proj₂ S ms
    ...   | rs , mb , eqb , _ = rs , mb , cong stamped (trans eqb (cong (concatMap proj₂) eqs))

    late₀ : ∀ {rs′ ov} → Met X rs′ → Flushes o rs′ ov → Σ _ λ rs → Met B rs × Prefix _≡_ (byName ov rs′) (stamped (values rs))
    late₀ {rs′} {false} mx _ with met-from mx | pending-one (proj₁ (after bstart (values rs′)))
    ... | rs , mb , eq | inj₁ e = rs , mb ,
          prefix-trans (closed-prefix false _)
            (prefix-≡ (trans (sym run′) (trans (cong (stamped (released bstart (values rs′)) ++_) e) (trans (++-identityʳ _) (sym eq)))))
      where run′ = grouped-run bstart (values rs′) (good-run o mx)
    ... | rs , mb , eq | inj₂ (g , e) = rs , mb ,
          prefix-≡ (trans (cong (closed false) (sym (trans (cong (stamped (released bstart (values rs′)) ++_) (sym e)) run′)))
                          (trans (closed-snoc _ g) (sym eq)))
      where run′ = grouped-run bstart (values rs′) (good-run o mx)
    late₀ {rs′} {true} mx (ext , mx′ , pre) with met-from mx′
    ... | rs , mb , eq = rs , mb ,
          prefix-trans (prefix-≡ (sym (grouped-run bstart (values rs′) (good-run o mx))))
            (prefix-trans (prefix-++ (stamped (released bstart (values rs′))) pre)
              (prefix-≡ (sym (trans eq (trans (cong (λ ws → stamped (released bstart ws)) (values-++ rs′ ext))
                (trans (cong stamped (released-++ bstart (values rs′) (values ext)))
                       (stamped-++ (released bstart (values rs′)) _)))))))

    flush : ∀ {rx} ov → Met (ranked X) rx → Closes valuesOf X rx ov → Flushes o (unrank rx) ov
    flush false _   _  = tt
    flush true  mxr cl = closes-flush o mxr cl

    late : ∀ {rx ov} → Met (ranked X) rx → Closes valuesOf X rx ov → Σ _ λ rs → Met (ranked B) rs × Prefix _≡_ (grouped ov (stampedᴮ rx)) (stampedᴮ rs)
    late {rx} {ov} mxr cl with late₀ {unrank rx} {ov} (proj₂ (ranks-x o) mxr) (flush ov mxr cl)
    ... | rs₀ , mb , pre with proj₁ (ranks-b o) mb
    ...   | rs , mbr , refl = rs , mbr , prefix-rel (name-rank o) (groups ov mxr) (bs-rel mbr) pre
