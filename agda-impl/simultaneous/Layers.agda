{-# OPTIONS --guardedness #-}

-- A PROGRAM READ THROUGH THE OPERATOR ON TOP: what a subscriber to a
-- `scan`, or to an `each` (a merge of `of`s), meets, read back as what a
-- subscriber to its source meets.  Generic in the source: nothing here
-- knows the batcher.
module simultaneous.Layers where

open import Data.List using (List; []; _∷_; concatMap; _++_; [_])
import Data.List as L
open import Data.List.Properties using (∷-injectiveʳ; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-concatMap⁺; ∈-++⁺ʳ; ∈-++⁺ˡ; ∈-∃++)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; s≤s)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Tree using (Obs; scan; map; of)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; _<ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh; finals; ofᴱ; <ᵖ-apart; <ᵖ-between; <ᵖ-part; ix-<)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; _≺_; _≼_; enter; ⟦_⟧; module Scan; Den; module Op; InE; at-out; on-out; Seen; Reach; Dep; Ended; LaneOf; module Merge; module Bounded; module Values; MapT; map-out; map-end; map-skip; map-pin)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.Worlds using (InvAt; PinBy; ⊕-assoc; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (module AccF; of-end; of-end-row; of-idx)
open import denotation.Laws.Modulus using (≼-split; ≼-antisym; entered-reach; entered-few; ≺-trans; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≺-≼-≺; ≼-trans; ≼-or-≻; ≺-ext)
open import denotation.Laws.Fold using (fold)
open import adequacy.SubOne using (scan-reach; map-reach; lift-in)
open import adequacy.SubJoin using (of-rows; of-in; of-reach)
open import adequacy.Complete using (reach)
open import adequacy.Simulated using () renaming (cursor to simulated)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met; values; values-++; Ends)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) finals using (each; concatˢ)

-- A closed program's emission set, subscribed at the root.
at : ∀ {A} → Obs Timeline [] A → EmissionSet A
at s = enter (⟦ s ⟧ []) root

-- A closed program has one row at a position.
at-func : ∀ {A} (s : Obs Timeline [] A) {y e e′} → at s y e → at s y e′ → e ≡ e′
at-func s = InvAt.func (inv-⟦⟧ s [] (λ ()) root (tt , λ ()))

-- A visible row is no pin.
pinby-vis : ∀ {A c} {e : Ev A} → Visible e → PinBy c e → ⊥
pinby-vis {e = out _} _ (_ , () , _)
pinby-vis {e = end}   _ (_ , () , _)
pinby-vis {e = skip}  ()
pinby-vis {e = pin _} ()

-- A visible row of a closed program lies at or before its end.
vis-end-at : ∀ {A} (s : Obs Timeline [] A) {q e c} → at s q e → Visible e → at s c end → q ≼ c
vis-end-at s x vi y cq = pinby-vis vi (InvAt.quiet (inv-⟦⟧ s [] (λ ()) root (tt , λ ())) y x cq)

-- A visible row of a closed program is reached.
seen-at : ∀ {A} (s : Obs Timeline [] A) {q e} → at s q e → Visible e → Seen (at s) q e
seen-at s {e = out _} x _ = (x , vis-end-at s x tt) , entered-few (⟦ s ⟧ []) root tt x
seen-at s {e = end}   x _ = (x , vis-end-at s x tt) , entered-few (⟦ s ⟧ []) root tt x
seen-at s {e = skip}  _ ()
seen-at s {e = pin _} _ ()

-- The states a fold passes through, one per value.
scans : ∀ {A B : Set} → (B → A → B) → B → List A → List B
scans f z []       = []
scans f z (a ∷ as) = f z a ∷ scans f (f z a) as

-- Nothing is met past an end.
run-past-end : ∀ {A} {t : EmissionSet A} {q rs} → t q end → Run t (just q) rs → rs ≡ []
run-past-end _ []                                    = refl
run-past-end x ((((_ , prop) , _) , _ , aft , _) ∷ _) = ⊥-elim (prop x aft)

-- A SCAN IS ITS SOURCE, ROW FOR ROW: what is met of it is what is met of
-- its source, each value the fold's state, completing when it does.  A
-- value of the source has its fold, so a row least among the scan's is
-- least among the source's; the fold met is the fold of the values met,
-- for the one before a value is the value met before it.
module ScanLayer {A B : Set} (f : B → A → B) (z : B) (s : Obs Timeline [] A) where
  open Scan f z (at s) using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)

  S  = at s
  Sc = at (scan f z s)

  open AccF f z {S} (at-func s) using (acc-val; acc-func)

  toSc : ∀ {y e} → ScanT y e → Sc y e
  toSc x = x , scan-reach (entered-reach (⟦ s ⟧ []) root) x

  -- The fold so far, at the cursor: none before any value.
  data St : Maybe Pos → B → Set where
    none : St nothing z
    some : ∀ {q b} → Acc q b → St (just q) b

  -- What is least among the scan's rows is least among the source's.
  least-src : ∀ {c q} → (∀ {k e} → Sc k e → Visible e → After c k → q ≼ k)
            → ∀ {k e} → S k e → Visible e → After c k → q ≼ k
  least-src lst {e = out _} y _ ak kq = fold f z S (entered-few (⟦ s ⟧ []) root tt y) y λ { (_ , ac) → lst (toSc (sval ac)) tt ak kq }
  least-src lst {e = end}   y _ ak    = lst (toSc (send y)) tt ak

  least-scan : ∀ {c q} → (∀ {k e} → S k e → Visible e → After c k → q ≼ k)
             → ∀ {k e} → Sc k e → Visible e → After c k → q ≼ k
  least-scan lst (sval ac , _) _ ak = lst (proj₂ (acc-val ac)) tt ak
  least-scan lst (send y , _)  _ ak = lst y tt ak

  -- The fold met at a value is the state's, stepped by it.
  stepped : ∀ {c b q b′} → St c b → (ac : Acc q b′) → After c q → (∀ {k e} → Sc k e → Visible e → After c k → q ≼ k)
          → b′ ≡ f b (proj₁ (acc-val ac))
  stepped none (acc₀ _ _) _ _ = refl
  stepped none (acc ac′ _ lt _) _ lst = ⊥-elim (lst (toSc (sval ac′)) tt tt lt)
  stepped (some acs) (acc₀ _ mn) aft _ = ⊥-elim (mn (proj₂ (acc-val acs)) aft)
  stepped (some {q₀} acs) (acc {q₁} ac′ _ lt nx) aft lst =
    cong (λ w → f w _) (acc-func (≼-antisym {q₁} {q₀} (λ h → lst (toSc (sval ac′)) tt h lt) (λ h → nx (proj₂ (acc-val acs)) h aft)) ac′ acs)

  -- The fold at a value met, from the state.
  next : ∀ {c b q a} → St c b → S q (out a) → After c q → (∀ {k e} → S k e → Visible e → After c k → q ≼ k) → Acc q (f b a)
  next none       x _   lst = acc₀ x λ y → lst y tt tt
  next (some acs) x aft lst = acc acs x aft λ y → lst y tt

  out-go : ∀ {c b sc} → St c b → Run Sc c sc
         → Σ _ λ rx → Run S c rx × values sc ≡ scans f b (values rx) × (Ends sc → Ends rx)
  out-go st [] = [] , [] , refl , λ ()
  out-go {c} {b} st (((((sval ac , _) , prop) , _) , _ , aft , lst) ∷ run) with out-go (some ac) run
  ... | rx , run′ , eq , en =
    let ls = least-src {c} lst in
    (_ , out (proj₁ (acc-val ac))) ∷ rx ,
    (((proj₂ (acc-val ac) , λ y → prop (toSc (send y))) , entered-few (⟦ s ⟧ []) root tt (proj₂ (acc-val ac))) , tt , aft , ls) ∷ run′ ,
    cong₂ _∷_ e (trans eq (cong (λ w → scans f w (values rx)) e)) ,
    λ { (here ()) ; (there h) → there (en h) }
    where e = stepped st ac aft lst
  out-go {c} st (((((send y , r) , prop) , _) , _ , aft , lst) ∷ run) with run-past-end {t = Sc} (send y , r) run
  ... | refl =
    (_ , end) ∷ [] ,
    (((y , λ y′ → prop (toSc (send y′))) , entered-few (⟦ s ⟧ []) root tt y) , tt , aft , least-src {c} lst) ∷ [] ,
    refl , λ _ → here refl
  out-go st (((((sstep _ , _) , _) , _) , () , _) ∷ _)
  out-go st (((((spin _ , _) , _) , _) , () , _) ∷ _)

  in-go : ∀ {c b rx} → St c b → Run S c rx
        → Σ _ λ sc → Run Sc c sc × values sc ≡ scans f b (values rx) × (Ends rx → Ends sc)
  in-go st [] = [] , [] , refl , λ ()
  in-go {c} {b} st (_∷_ {e = out a} (((x , prop) , _) , _ , aft , lst) run) with in-go (some (next st x aft lst)) run
  ... | sc , run′ , eq , en =
    (_ , out (f b a)) ∷ sc ,
    (((toSc (sval ac) , λ { (send y , _) → prop y }) , entered-few (⟦ scan f z s ⟧ []) root tt (toSc (sval ac))) , tt , aft , least-scan {c} lst) ∷ run′ ,
    cong (f b a ∷_) eq ,
    λ { (here ()) ; (there h) → there (en h) }
    where ac = next st x aft lst
  in-go {c} st (_∷_ {e = end} (((x , prop) , _) , _ , aft , lst) run) with run-past-end {t = S} x run
  ... | refl =
    (_ , end) ∷ [] ,
    (((toSc (send x) , λ { (send y , _) → prop y }) , entered-few (⟦ scan f z s ⟧ []) root tt (toSc (send x))) , tt , aft , least-scan {c} lst) ∷ [] ,
    refl , λ _ → here refl
  in-go st (_∷_ {e = skip}  (_ , () , _) _)
  in-go st (_∷_ {e = pin _} (_ , () , _) _)

scan-out : ∀ {A B} (f : B → A → B) z (s : Obs Timeline [] A) {sc} → Met (at (scan f z s)) sc
         → Σ _ λ rx → Met (at s) rx × values sc ≡ scans f z (values rx) × (Ends sc → Ends rx)
scan-out f z s = ScanLayer.out-go f z s (ScanLayer.none)

scan-in : ∀ {A B} (f : B → A → B) z (s : Obs Timeline [] A) {rx} → Met (at s) rx
        → Σ _ λ sc → Met (at (scan f z s)) sc × values sc ≡ scans f z (values rx) × (Ends rx → Ends sc)
scan-in f z s = ScanLayer.in-go f z s (ScanLayer.none)

------------------------------------------------------------------------
-- Runs

to≺ : ∀ x y → x <ᵖ y ≡ true → x ≺ y
to≺ _ _ = Equivalence.from T-≡

from≺ : ∀ x y → x ≺ y → x <ᵖ y ≡ true
from≺ _ _ = Equivalence.to T-≡


run-++ : ∀ {A} {t : EmissionSet A} {c xs ys} → Run t c xs → Run t (cursor c xs) ys → Run t c (xs ++ ys)
run-++ []        r = r
run-++ (h ∷ run) r = h ∷ run-++ run r

run-tail : ∀ {A} {t : EmissionSet A} {c} xs {ys} → Run t c (xs ++ ys) → Run t (cursor c xs) ys
run-tail []       r         = r
run-tail (_ ∷ xs) (_ ∷ run) = run-tail xs run

cursor-++ : ∀ {A} c (xs ys : List (Pos × Ev A)) → cursor c (xs ++ ys) ≡ cursor (cursor c xs) ys
cursor-++ c []             ys = refl
cursor-++ c ((q , _) ∷ xs) ys = cursor-++ (just q) xs ys

cursor-snoc : ∀ {A} c (xs : List (Pos × Ev A)) {q e} → cursor c (xs ++ [ (q , e) ]) ≡ just q
cursor-snoc c xs {q} {e} = cursor-++ c xs [ (q , e) ]

after-≺ : ∀ c {k k′} → After c k → k ≺ k′ → After c k′
after-≺ nothing  _ _ = tt
after-≺ (just c) {k} {k′} a b = ≺-trans {c} {k} {k′} a b

-- Every row met past a cursor lies past it.
run-after : ∀ {A} {t : EmissionSet A} {c ys k e} → Run t (just c) ys → (k , e) ∈ ys → c ≺ k
run-after ((_ , _ , aft , _) ∷ _) (here refl) = aft
run-after {c = c} {k = k} ((_ , _ , aft , _) ∷ run) (there m) = ≺-trans {c} {_} {k} aft (run-after run m)

run-row : ∀ {A} {t : EmissionSet A} {c xs k e} → Run t c xs → (k , e) ∈ xs → t k e × Visible e
run-row ((((x , _) , _) , vi , _) ∷ _) (here refl) = x , vi
run-row (_ ∷ run) (there m) = run-row run m

-- A visible row before one met is met.
run-has : ∀ {A} {t : EmissionSet A} → (∀ {y e e′} → t y e → t y e′ → e ≡ e′)
        → ∀ {c rs v e k ek} → Run t c rs → t v e → Visible e → After c v → v ≼ k → (k , ek) ∈ rs → (v , e) ∈ rs
run-has fu {rs = (q , e₁) ∷ _} {v} ((((x₁ , _) , _) , _ , _ , lst) ∷ run) x vi av vk m with ≼-split {q} {v} (lst x vi av)
... | inj₂ refl = here (cong (q ,_) (fu x x₁))
... | inj₁ qv with m
...   | here refl = ⊥-elim (vk qv)
...   | there m′  = there (run-has fu run x vi qv vk m′)

-- Two readers from one cursor meet one run, one a prefix of the other.
run-det : ∀ {A} {t : EmissionSet A} → (∀ {y e e′} → t y e → t y e′ → e ≡ e′)
        → ∀ {c xs ys} → Run t c xs → Run t c ys → Prefix _≡_ xs ys ⊎ Prefix _≡_ ys xs
run-det fu [] _ = inj₁ []
run-det fu (_ ∷ _) [] = inj₂ []
run-det fu (_∷_ {q = q₁} {e = e₁} h₁@(((x₁ , _) , _) , vi₁ , a₁ , l₁) r₁) (_∷_ {q = q₂} h₂@(((x₂ , _) , _) , vi₂ , a₂ , l₂) r₂)
  with ≼-antisym {q₁} {q₂} (l₁ x₂ vi₂ a₂) (l₂ x₁ vi₁ a₁)
... | refl with fu x₁ x₂
...   | refl with run-det fu r₁ r₂
...     | inj₁ p = inj₁ (refl ∷ p)
...     | inj₂ p = inj₂ (refl ∷ p)

-- Nothing is met past an end, so a run that ends is every run it begins.
prefix-end : ∀ {A} {t : EmissionSet A} {c xs ys} → Run t c ys → Prefix _≡_ xs ys → Ends xs → xs ≡ ys
prefix-end _ [] ()
prefix-end ((((x , _) , _) , _) ∷ run) (refl ∷ []) (here refl) with run-past-end x run
... | refl = refl
prefix-end ((((x , _) , _) , _) ∷ run) (refl ∷ (_ ∷ _)) (here refl) with run-past-end x run
... | ()
prefix-end (_ ∷ run) (refl ∷ p) (there h) = cong (_ ∷_) (prefix-end run p h)

ends-last : ∀ {A} {t : EmissionSet A} {c} ys {y} → Run t c (ys ++ [ y ]) → Ends (ys ++ [ y ]) → proj₂ y ≡ end
ends-last []       _ (here eq) = eq
ends-last (_ ∷ ys) ((((x , _) , _) , _) ∷ run) (here refl) = ⊥-elim (snoc-nonempty ys (run-past-end x run))
  where
    snoc-nonempty : ∀ {B : Set} (zs : List B) {z} → zs ++ [ z ] ≡ [] → ⊥
    snoc-nonempty []      ()
    snoc-nonempty (_ ∷ _) ()
ends-last (_ ∷ ys) (_ ∷ run) (there h) = ends-last ys run h

prefix-values : ∀ {A} {xs ys : List (Pos × Ev A)} → Prefix _≡_ xs ys → Prefix _≡_ (values xs) (values ys)
prefix-values [] = []
prefix-values (_∷_ {a = (_ , out _)} refl p) = refl ∷ prefix-values p
prefix-values (_∷_ {a = (_ , skip)}  refl p) = prefix-values p
prefix-values (_∷_ {a = (_ , end)}   refl p) = prefix-values p
prefix-values (_∷_ {a = (_ , pin _)} refl p) = prefix-values p

prefix-split : ∀ {A : Set} {xs ys : List A} → Prefix _≡_ xs ys → xs ≡ ys ⊎ Σ A λ z → Σ (List A) λ zs → ys ≡ xs ++ z ∷ zs
prefix-split {ys = []}     []       = inj₁ refl
prefix-split {ys = z ∷ zs} []       = inj₂ (z , zs , refl)
prefix-split (refl ∷ p) with prefix-split p
... | inj₁ eq            = inj₁ (cong (_ ∷_) eq)
... | inj₂ (z , zs , eq) = inj₂ (z , zs , cong (_ ∷_) eq)

snoc-view : ∀ {A : Set} (xs : List A) → xs ≡ [] ⊎ Σ (List A) λ ys → Σ A λ y → xs ≡ ys ++ [ y ]
snoc-view []       = inj₁ refl
snoc-view (x ∷ xs) with snoc-view xs
... | inj₁ refl           = inj₂ ([] , x , refl)
... | inj₂ (ys , y , refl) = inj₂ (x ∷ ys , y , refl)

last-in : ∀ {A : Set} (ys : List A) {y} xs {z zs} → ys ++ [ y ] ≡ xs ++ z ∷ zs → y ∈ (z ∷ zs)
last-in []       []       refl = here refl
last-in []       (_ ∷ []) ()
last-in []       (_ ∷ _ ∷ _) ()
last-in (_ ∷ ys) []       refl = there (∈-++⁺ʳ ys (here refl))
last-in (_ ∷ ys) (_ ∷ xs) eq   = last-in ys xs (∷-injectiveʳ eq)

------------------------------------------------------------------------
-- An each

-- AN EACH IS ITS SOURCE'S LANES IN TURN: every row told of an `each`
-- hangs under one row told of its source, a value's lane or its end, and
-- falls between its source row and the next.  So a source run read
-- lane by lane is the each's run, and an each's run is one read off the
-- source run reaching its last row's source row.  A merge row's rows
-- before it are finite only through the values before it, which the
-- source run names.
module EachLayer {X Y : Set} (f : X → List Y) (s : Obs Timeline [] X) where
  F : X → Den Y
  F x = Op.of (f x)

  S = at s
  E = at (each f s)

  module M = Merge F S

  IS = inv-⟦⟧ s [] (λ ()) root (tt , λ ())

  ln : Pos → Pos
  ln q = q ⊕ [ ix 1 ]

  -- A row of the source under another is none.
  sole : ∀ {q e zs e′} → S q e → S (q ⊕ zs) e′ → zs ≡ []
  sole {zs = []}    _ _ = refl
  sole {zs = _ ∷ _} x y = ⊥-elim (InvAt.flat IS x y)

  ext-absurd : ∀ {q e y e′ zs} → S q e → S y e′ → q ≺ y → y ≡ q ⊕ zs → ⊥
  ext-absurd {q} x x′ lt eq with sole x (subst (λ w → S w _) eq x′)
  ... | refl = ≺-irrefl {q} (subst (q ≺_) (trans eq (⊕-identityʳ q)) lt)

  -- What lies under a row of the source lies before the rows past it.
  past-under : ∀ {q e q′ e′} → S q e → S q′ e′ → q ≺ q′ → ∀ ys → (q ⊕ ys) ≺ q′
  past-under {q} {q′ = q′} x x′ lt ys = to≺ (q ⊕ ys) q′ (<ᵖ-apart q q′ ys (from≺ q q′ lt) λ zs eq → ext-absurd x x′ lt eq)

  none-under : ∀ {q e y e′} ys → S q e → S y e′ → q ≺ y → y ≼ (q ⊕ ys) → ⊥
  none-under {q} {y = y} ys x x′ lt le with ≼-split {y} {q ⊕ ys} le
  ... | inj₂ eq = ext-absurd x x′ lt eq
  ... | inj₁ lt′ = ext-absurd x x′ lt (proj₂ (<ᵖ-between q y ys (from≺ q y lt) (from≺ y (q ⊕ ys) lt′)))

  vis-end : ∀ {q e c} → S q e → Visible e → S c end → q ≼ c
  vis-end = vis-end-at s

  val-end : ∀ {q a c} → S q (out a) → S c end → q ≺ c
  val-end {q} {c = c} x y with ≼-split {q} {c} (vis-end x tt y)
  ... | inj₁ lt   = lt
  ... | inj₂ refl with (at-func s) x y
  ...   | ()

  seenS : ∀ {q e} → S q e → Visible e → Seen S q e
  seenS = seen-at s

  lane-at : ∀ {q} {xs : List Y} {k} {e : Ev Y} → InE (ofᴱ (ln q) 0 xs) k e → Σ Path λ ys → k ≡ q ⊕ (ix 1 ∷ ys)
  lane-at {q} {xs} y with of-idx (ln q) 0 xs y
  ... | inj₁ (j , _ , eq) = ix j ∷ [] , trans eq (⊕-assoc q [ ix 1 ] [ ix j ])
  ... | inj₂ eq           = last ∷ [] , trans eq (⊕-assoc q [ ix 1 ] [ last ])

  lane-≼ : ∀ {q} {xs : List Y} {k} {e : Ev Y} → InE (ofᴱ (ln q) 0 xs) k e → q ≼ k
  lane-≼ {q} {xs} {k = k} y with lane-at {q} {xs} y
  ... | ys , eq = ≺→≼ {q} {k} (subst (q ≺_) (sym eq) (≺-ext q ys))

  -- A row told of the each, by the source row it hangs under.
  data Vis : Pos → Pos → Ev Y → Set where
    vlane : ∀ {q a k b} → S q (out a) → InE (ofᴱ (ln q) 0 (f a)) k (out b) → Vis k q (out b)
    vend  : ∀ {c} → S c end → Vis c c end

  lend-absurd : ∀ {q a c} → S q (out a) → InE (ofᴱ (ln q) 0 (f a)) c end → M.Done c → ⊥
  lend-absurd {q} {a} x y ((c₀ , y₀ , le) , _) with of-end (ln q) 0 (f a) y
  ... | refl = none-under (ix 1 ∷ last ∷ []) x y₀ (val-end x y₀) (subst (c₀ ≼_) (⊕-assoc q [ ix 1 ] [ last ]) le)

  vis : ∀ {k e} → E k e → Visible e → Σ Pos λ q → Vis k q e
  vis (M.val _ , _) ()
  vis (M.step _ , _) ()
  vis (M.opin _ , _) ()
  vis (M.oend x _ , _) _ = _ , vend x
  vis (M.opass _ _ , _) ()
  vis (M.lane {e = out _} x _ ((y , _) , _) _ _ , _) _ = _ , vlane x y
  vis (M.lane {e = end}   _ _ _ _ () , _) _
  vis (M.lane {e = skip}  _ _ _ _ _ , _) ()
  vis (M.lane {e = pin _} _ _ _ _ _ , _) ()
  vis (M.lend x _ ((y , _) , _) _ _ dn , _) _ = ⊥-elim (lend-absurd x y dn)
  vis (M.lpass _ _ _ _ _ _ , _) ()
  vis (M.hand _ _ _ _ _ , _) ()
  vis (M.left _ _ _ _ _ , _) ()
  vis (M.run () _ , _) _
  vis (M.rend () _ _ , _) _
  vis (M.rpass _ _ _ , _) ()
  vis (M.rhand _ _ , _) ()

  vis-anc : ∀ {k q e} → Vis k q e → Σ (Ev X) λ e₀ → S q e₀ × Visible e₀
  vis-anc (vlane x _) = _ , x , tt
  vis-anc (vend x)    = _ , x , tt

  vend-src : ∀ {k q} → Vis k q end → S q end
  vend-src (vend x) = x

  vis-under : ∀ {k q e} → Vis k q e → q ≼ k
  vis-under (vlane {q} {a} _ y) = lane-≼ {q} {f a} y
  vis-under (vend {c} _)  = ≼-refl {c}

  vis-before : ∀ {k q e q′ e′} → Vis k q e → S q′ e′ → q ≺ q′ → k ≺ q′
  vis-before {q′ = q′} (vlane {q} {a} x y) x′ lt with lane-at {q} {f a} y
  ... | ys , eq = subst (_≺ q′) (sym eq) (past-under x x′ lt (ix 1 ∷ ys))
  vis-before (vend _) _ lt = lt

  -- A row told of the each lies at or before its end.
  e-proper : ∀ {k q e c} → Vis k q e → S c end → k ≼ c
  e-proper (vend x) y = vis-end x tt y
  e-proper {k} {c = c} v@(vlane x _) y = ≺→≼ {k} {c} (vis-before v y (val-end x y))

  end-vend : ∀ {c} → E c end → S c end
  end-vend y with vis y tt
  ... | _ , vend z = z

  seenE : ∀ {k e} → E k e → Visible e → Seen E k e
  seenE {e = out _} x vi = (x , λ y → e-proper (proj₂ (vis x vi)) (end-vend y)) , entered-few (⟦ each f s ⟧ []) root tt x
  seenE {e = end}   x vi = (x , λ y → e-proper (proj₂ (vis x vi)) (end-vend y)) , entered-few (⟦ each f s ⟧ []) root tt x
  seenE {e = skip}  _ ()
  seenE {e = pin _} _ ()

  -- Where each row is anchored in its source, against where the each is read.
  Inv : Maybe Pos → Maybe Pos → Set
  Inv cS cE = ∀ {k q e} → Vis k q e → (After cE k → After cS q) × (After cS q → After cE k)

  -- WHAT A SOURCE RUN REACHES OF THE EACH.
  module Over (whole : List (Pos × Ev X)) (mw : Met S whole) where

    rowsOf : Pos × Ev X → List Pos
    rowsOf (q , out a) = q ∷ (q ⊕ [ ix 0 ]) ∷ of-rows (ln q) 0 (f a)
    rowsOf (q , _)     = q ∷ []

    module _ {q e₀} (qin : (q , e₀) ∈ whole) where
      private
        x₀  = proj₁ (run-row mw qin)
        vi₀ = proj₂ (run-row mw qin)
        ksS = proj₁ (proj₂ (seenS x₀ vi₀))
        hS  = proj₂ (proj₂ (seenS x₀ vi₀))

      ks : List Pos
      ks = concatMap (λ q′ → q′ ∷ (q′ ⊕ [ ix 0 ]) ∷ []) ksS ++ concatMap rowsOf whole

      in-whole : ∀ {r k′} → r ∈ whole → k′ ∈ rowsOf r → k′ ∈ ks
      in-whole m r = ∈-++⁺ʳ (concatMap _ ksS) (∈-concatMap⁺ rowsOf (any-map (λ { refl → r }) m))

      row-in : ∀ {q′ e′} → S q′ e′ → q′ ≼ q → q′ ∈ ks
      row-in {e′ = out _} x le = in-whole (run-has (at-func s) mw x tt tt le qin) (here refl)
      row-in {e′ = end}   x le = in-whole (run-has (at-func s) mw x tt tt le qin) (here refl)
      row-in {q′} {e′ = skip} x le with ≼-split {q′} {q} le
      ... | inj₁ lt = ∈-++⁺ˡ (lift-in (λ q′ → q′ ∷ (q′ ⊕ [ ix 0 ]) ∷ []) (here refl) (hS x lt))
      ... | inj₂ refl = ⊥-elim (skip-vis ((at-func s) x x₀) vi₀)
        where skip-vis : ∀ {e : Ev X} → skip ≡ e → Visible e → ⊥
              skip-vis refl ()
      row-in {q′} {e′ = pin r} x le with ≼-split {q′} {q} le
      ... | inj₁ lt = ∈-++⁺ˡ (lift-in (λ q′ → q′ ∷ (q′ ⊕ [ ix 0 ]) ∷ []) (here refl) (hS x lt))
      ... | inj₂ refl = ⊥-elim (pin-vis ((at-func s) x x₀) vi₀)
        where pin-vis : ∀ {e : Ev X} → pin r ≡ e → Visible e → ⊥
              pin-vis refl ()

      val-in : ∀ {q′ a′} → S q′ (out a′) → q′ ≼ q → (q′ ⊕ [ ix 0 ]) ∈ ks
      val-in x le = in-whole (run-has (at-func s) mw x tt tt le qin) (there (here refl))

      lane-in : ∀ {q′ a′ k′ e′} → S q′ (out a′) → q′ ≼ q → InE (ofᴱ (ln q′) 0 (f a′)) k′ e′ → k′ ∈ ks
      lane-in {q′} {a′} x le y = in-whole (run-has (at-func s) mw x tt tt le qin) (there (there (of-in (ln q′) 0 (f a′) y)))

      -- A merge row before a row anchored at `q` hangs under a source row at or before `q`.
      reachE : ∀ {k e} → Vis k q e → Reach M.JoinT k e
      reachE {k} {e} v = ks , pick
        where
          anc : ∀ {q′ e′ k′} → S q′ e′ → q′ ≼ k′ → k′ ≺ k → q′ ≼ q
          anc {q′} {k′ = k′} x le kk qq = ≺-absurd {k} {k′} (≺-≼-≺ {k} {q′} {k′} (vis-before v x qq) le) kk

          pick : ∀ {k′ e′} → M.JoinT k′ e′ → k′ ≺ k → Dep k e k′ e′ → k′ ∈ ks
          pick {k′} (M.val {q′} x) kk _ = val-in x (anc {k′ = k′} x (≺→≼ {q′} {q′ ⊕ [ ix 0 ]} (≺-ext q′ [])) kk)
          pick {k′} (M.step {q′} x) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.opin {q′} x) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.oend {q′} x _) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.opass {q′} x _) kk _ = row-in x (anc {k′ = k′} x (≼-refl {q′}) kk)
          pick {k′} (M.lane {q′} {a′} x _ ((y , _) , _) _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ {q′} {f a′} y) kk) y
          pick {k′} (M.lend {q′} {a′} x _ ((y , _) , _) _ _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ {q′} {f a′} y) kk) y
          pick {k′} (M.lpass {q′} {a′} x _ ((y , _) , _) _ _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ {q′} {f a′} y) kk) y
          pick (M.hand _ _ _ _ ()) _ _
          pick {k′} (M.left {q′} {a′} x _ ((y , _) , _) _ _) kk _ = lane-in x (anc {k′ = k′} x (lane-≼ {q′} {f a′} y) kk) y
          pick (M.run () _) _ _
          pick (M.rend () _ _) _ _
          pick (M.rpass () _ _) _ _
          pick (M.rhand () _) _ _

    -- A LANE READ IN ORDER: the value at `q`, its lane's rows met one by one.
    module Lane {q a} (sq : S q (out a)) (qin : (q , out a) ∈ whole) where
      p = ln q

      J : Maybe Pos → ℕ → List Y → Set
      J c i xs = (∀ {k q′ e} → Vis k q′ e → After c k → (q′ ≡ q × Σ Y λ b → e ≡ out b × InE (ofᴱ p i xs) k (out b)) ⊎ q ≺ q′)
               × (∀ {k q′ e} → Vis k q′ e → q ≺ q′ → After c k)
               × (∀ {k b} → InE (ofᴱ p i xs) k (out b) → After c k)

      at-i : ∀ i {q′ e′} → S q′ e′ → q ≺ q′ → (p ⊕ [ ix i ]) ≺ q′
      at-i i {q′} x′ lt = subst (_≺ q′) (sym (⊕-assoc q [ ix 1 ] [ ix i ])) (past-under sq x′ lt (ix 1 ∷ ix i ∷ []))

      in-rest : ∀ i (xs : List Y) {k′ e′} → InE (ofᴱ p (suc i) xs) k′ e′ → (p ⊕ [ ix i ]) ≺ k′
      in-rest i xs y with of-idx p (suc i) xs y
      ... | inj₁ (j , le , refl) = to≺ (p ⊕ [ ix i ]) (p ⊕ [ ix j ]) (<ᵖ-part p {ix i} {ix j} [] [] (ix-< le))
      ... | inj₂ refl            = to≺ (p ⊕ [ ix i ]) (p ⊕ [ last ]) (<ᵖ-part p {ix i} {last} [] [] refl)

      go : ∀ {c} i (xs : List Y) → (∀ {k e} → InE (ofᴱ p i xs) k e → InE (ofᴱ p 0 (f a)) k e) → J c i xs
         → Σ _ λ rows → Run E c rows × values rows ≡ xs × Inv (just q) (cursor c rows)
      go {c} i [] _ (j₁ , j₂ , _) = [] , [] , refl , λ v → fin v , j₂ v
        where
          fin : ∀ {k q′ e} → Vis k q′ e → After c k → q ≺ q′
          fin v ak with j₁ v ak
          ... | inj₁ (_ , _ , _ , ())
          ... | inj₂ lt = lt
      go {c} i (x ∷ xs) emb (j₁ , j₂ , j₃) with go (suc i) xs (λ y → emb (on-out y)) (j₁′ , j₂′ , j₃′)
        where
          k = p ⊕ [ ix i ]
          j₁′ : ∀ {k′ q′ e} → Vis k′ q′ e → After (just k) k′ → (q′ ≡ q × Σ Y λ b → e ≡ out b × InE (ofᴱ p (suc i) xs) k′ (out b)) ⊎ q ≺ q′
          j₁′ v ak with j₁ v (after-≺ c (j₃ at-out) ak)
          ... | inj₁ (refl , b , refl , at-out)   = ⊥-elim (≺-irrefl {k} ak)
          ... | inj₁ (refl , b , refl , on-out y) = inj₁ (refl , b , refl , y)
          ... | inj₂ lt                           = inj₂ lt
          j₂′ : ∀ {k′ q′ e} → Vis k′ q′ e → q ≺ q′ → After (just k) k′
          j₂′ {k′} {q′} v lt = ≺-≼-≺ {k} {q′} {k′} (at-i i (proj₁ (proj₂ (vis-anc v))) lt) (vis-under v)
          j₃′ : ∀ {k′ b} → InE (ofᴱ p (suc i) xs) k′ (out b) → After (just k) k′
          j₃′ y = in-rest i xs y
      ... | rows , run , eq , inv = (k , out x) ∷ rows , (seenE row tt , tt , j₃ at-out , mn) ∷ run , cong (x ∷_) eq , inv
        where
          k = p ⊕ [ ix i ]
          v : Vis k q (out x)
          v = vlane sq (emb at-out)
          row : E k (out x)
          row = M.lane sq tt ((emb at-out , of-reach p 0 (f a) {k} {out x}) , ≺-ext p []) (λ ()) tt , reachE qin v
          mn : ∀ {k′ e′} → E k′ e′ → Visible e′ → After c k′ → k ≼ k′
          mn {k′} y vi ak with vis y vi
          ... | q′ , v′ with j₁ v′ ak
          ...   | inj₁ (refl , b , refl , at-out)    = ≼-refl {k}
          ...   | inj₁ (refl , b , refl , on-out y′) = ≺→≼ {k} {k′} (in-rest i xs y′)
          ...   | inj₂ lt = ≺→≼ {k} {k′} (≺-≼-≺ {k} {q′} {k′} (at-i i (proj₁ (proj₂ (vis-anc v′))) lt) (vis-under v′))

    -- The source run read lane by lane.
    each-go : ∀ {cS cE sc} → (∀ {r} → r ∈ sc → r ∈ whole) → Inv cS cE → Run S cS sc
            → Σ _ λ rs → Run E cE rs × values rs ≡ concatMap f (values sc) × (Ends sc → Ends rs) × Inv (cursor cS sc) (cursor cE rs)
    each-go _ inv [] = [] , [] , refl , (λ ()) , inv
    each-go {cS} {cE} sub inv (_∷_ {q = q} {e = out a} {rs = sc′} (((x , _) , _) , _ , aft , lst) run)
      with Lane.go x (sub (here refl)) 0 (f a) (λ y → y) (j₁ , j₂ , j₃)
      where
        j₁ : ∀ {k q′ e} → Vis k q′ e → After cE k → (q′ ≡ q × Σ Y λ b → e ≡ out b × InE (ofᴱ (ln q) 0 (f a)) k (out b)) ⊎ q ≺ q′
        j₁ v ak with ≼-split {q} {_} (lst (proj₁ (proj₂ (vis-anc v))) (proj₂ (proj₂ (vis-anc v))) (proj₁ (inv v) ak))
        ... | inj₁ lt = inj₂ lt
        j₁ (vlane x′ y) ak | inj₂ refl with (at-func s) x′ x
        ... | refl = inj₁ (refl , _ , refl , y)
        j₁ (vend x′) ak | inj₂ refl with (at-func s) x x′
        ... | ()
        j₂ : ∀ {k q′ e} → Vis k q′ e → q ≺ q′ → After cE k
        j₂ v lt = proj₂ (inv v) (after-≺ cS aft lt)
        j₃ : ∀ {k b} → InE (ofᴱ (ln q) 0 (f a)) k (out b) → After cE k
        j₃ y = proj₂ (inv (vlane x y)) aft
    ... | rows , runL , eqL , invL with each-go (λ m → sub (there m)) invL run
    ...   | rs′ , run′ , eq′ , en′ , inv′ =
      rows ++ rs′ , run-++ runL run′ ,
      trans (values-++ rows rs′) (cong₂ _++_ eqL eq′) ,
      (λ { (here ()) ; (there h) → ++⁺ʳ rows (en′ h) }) ,
      subst (Inv (cursor (just q) sc′)) (sym (cursor-++ cE rows rs′)) inv′
    each-go {cS} {cE} sub inv (_∷_ {q = c} {e = end} (((x , _) , _) , _ , aft , lst) run) with run-past-end {t = S} x run
    ... | refl = (c , end) ∷ [] , (seenE row tt , tt , proj₂ (inv (vend x)) aft , mn) ∷ [] , refl , (λ _ → here refl) , inv-end
      where
        lane-ended : ∀ {q′ a′} → S q′ (out a′) → q′ ≺ c → Ended (LaneOf F q′ a′) c
        lane-ended {q′} {a′} x′ lt =
          ln q′ ⊕ [ last ] , ((of-end-row (ln q′) 0 (f a′) , of-reach (ln q′) 0 (f a′) {ln q′ ⊕ [ last ]} {end}) , ≺-ext (ln q′) []) ,
          ≺→≼ {ln q′ ⊕ [ last ]} {c} (subst (_≺ c) (sym (⊕-assoc q′ [ ix 1 ] [ last ])) (past-under x′ x lt (ix 1 ∷ last ∷ [])))
        row : E c end
        row = M.oend x ((c , x , ≼-refl {c}) , λ x′ _ lt _ → lane-ended x′ lt) , reachE (sub (here refl)) (vend x)
        mn : ∀ {k′ e′} → E k′ e′ → Visible e′ → After cE k′ → c ≼ k′
        mn {k′} y vi ak with vis y vi
        ... | q′ , v′ = ≼-trans {c} {q′} {k′} (lst (proj₁ (proj₂ (vis-anc v′))) (proj₂ (proj₂ (vis-anc v′))) (proj₁ (inv v′) ak)) (vis-under v′)
        inv-end : Inv (just c) (just c)
        inv-end {k} {q′} v = fwd v , λ lt → ≺-≼-≺ {c} {q′} {k} lt (vis-under v)
          where
            fwd : ∀ {k q′ e} → Vis k q′ e → c ≺ k → c ≺ q′
            fwd {k} {q′} v ck with ≼-or-≻ q′ c
            ... | inj₂ lt = lt
            ... | inj₁ le with ≼-split {q′} {c} le
            ...   | inj₁ lt = ⊥-elim (≺-absurd {c} {k} ck (vis-before v x lt))
            fwd (vend _)     ck | inj₁ _ | inj₂ refl = ⊥-elim (≺-irrefl {c} ck)
            fwd (vlane x′ _) ck | inj₁ _ | inj₂ refl with (at-func s) x′ x
            ... | ()
    each-go _ _ (_∷_ {e = skip}  (_ , () , _) _)
    each-go _ _ (_∷_ {e = pin _} (_ , () , _) _)

  each-in′ : ∀ {sc} → Met S sc → Σ _ λ rs → Met E rs × values rs ≡ concatMap f (values sc) × (Ends sc → Ends rs)
  each-in′ {sc} m with Over.each-go sc m (λ r → r) (λ _ → (λ _ → tt) , (λ _ → tt)) m
  ... | rs , run , eq , en , _ = rs , run , eq , en

  each-out′ : ∀ {rs} → Met E rs
            → Σ _ λ sc → Met S sc × Prefix _≡_ (values rs) (concatMap f (values sc))
                       × (Ends rs → Ends sc × values rs ≡ concatMap f (values sc))
  each-out′ {rs} m with snoc-view rs
  ... | inj₁ refl = [] , [] , [] , λ ()
  ... | inj₂ (ys , (k , e) , refl) with run-row m (∈-++⁺ʳ ys (here refl))
  ...   | kE , vi with vis kE vi
  ...     | q , v with vis-anc v
  ...       | e₀ , x₀ , vi₀ with reach s (simulated s) [] (seenS x₀ vi₀) vi₀ tt
  ...         | rs″ , mS with Over.each-go (rs″ ++ [ (q , e₀) ]) mS (λ r → r) (λ _ → (λ _ → tt) , (λ _ → tt)) mS
  ...           | rs′ , mE , eq , en , inv = rs″ ++ [ (q , e₀) ] , mS , pre , ends
    where
      sl = rs″ ++ [ (q , e₀) ]
      rl = ys ++ [ (k , e) ]

      longer : Prefix _≡_ rl rs′
      longer with run-det (at-func (each f s)) m mE
      ... | inj₁ pr = pr
      ... | inj₂ pr with prefix-split pr
      ...   | inj₁ eq′ = subst (Prefix _≡_ rl) (sym eq′) (subst (λ w → Prefix _≡_ w rl) eq′ pr)
      ...   | inj₂ ((kz , ez) , zs , eq′) with run-tail rs′ (subst (Run E nothing) eq′ m)
      ...     | tl@((((xz , _) , _) , viz , az , _) ∷ tl′) with vis xz viz
      ...       | qz , vz =
        let qqz : q ≺ qz
            qqz = subst (λ w → After w qz) (cursor-snoc nothing rs″) (proj₁ (inv vz) az)
            kkz : k ≺ kz
            kkz = ≺-≼-≺ {k} {qz} {kz} (vis-before v (proj₁ (proj₂ (vis-anc vz))) qqz) (vis-under vz)
            kzk : kz ≼ k
            kzk = in-tail (last-in ys rs′ eq′)
        in ⊥-elim (kzk kkz)
        where
          in-tail : (k , e) ∈ ((kz , ez) ∷ zs) → kz ≼ k
          in-tail (here refl) = ≼-refl {kz}
          in-tail (there m′)  = ≺→≼ {kz} {k} (run-after tl′ m′)

      pre : Prefix _≡_ (values rl) (concatMap f (values sl))
      pre = subst (Prefix _≡_ (values rl)) eq (prefix-values longer)

      ends : Ends rl → Ends sl × values rl ≡ concatMap f (values sl)
      ends h = ++⁺ʳ rs″ (here ((at-func s) x₀ (vend-src (subst (Vis k q) (ends-last ys m h) v)))) , trans (cong values (prefix-end mE longer h)) eq

each-out : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {rs} → Met (at (each f s)) rs
         → Σ _ λ sc → Met (at s) sc × Prefix _≡_ (values rs) (concatMap f (values sc))
                    × (Ends rs → Ends sc × values rs ≡ concatMap f (values sc))
each-out f s = EachLayer.each-out′ f s

each-in : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {sc} → Met (at s) sc
        → Σ _ λ rs → Met (at (each f s)) rs × values rs ≡ concatMap f (values sc) × (Ends sc → Ends rs)
each-in f s = EachLayer.each-in′ f s

------------------------------------------------------------------------
-- A map

-- A MAP IS ITS SOURCE, ROW FOR ROW: each row met of it is its source's
-- row, the value mapped.
module MapLayer {A B : Set} (g : A → B) (s : Obs Timeline [] A) where
  S  = at s
  Mp = at (map g s)

  toMp : ∀ {y e} → MapT g S y e → Mp y e
  toMp x = x , map-reach (entered-reach (⟦ s ⟧ []) root) x

  least-src : ∀ {c q} → (∀ {k e} → Mp k e → Visible e → After c k → q ≼ k)
            → ∀ {k e} → S k e → Visible e → After c k → q ≼ k
  least-src lst {e = out _} y _ = lst (toMp (map-out y)) tt
  least-src lst {e = end}   y _ = lst (toMp (map-end y)) tt

  out-go : ∀ {c rx} → Run Mp c rx → Σ _ λ sc → Run S c sc × values rx ≡ L.map g (values sc) × (Ends rx → Ends sc)
  out-go [] = [] , [] , refl , λ ()
  out-go {c} (((((map-out y , _) , _) , _) , _ , aft , lst) ∷ run) with out-go run
  ... | sc , run′ , eq , en =
    _ ∷ sc , (seen-at s y tt , tt , aft , least-src {c} lst) ∷ run′ , cong (g _ ∷_) eq , λ { (here ()) ; (there h) → there (en h) }
  out-go {c} (((((map-end y , r) , _) , _) , _ , aft , lst) ∷ run) with run-past-end {t = Mp} (map-end y , r) run
  ... | refl = _ ∷ [] , (seen-at s y tt , tt , aft , least-src {c} lst) ∷ [] , refl , λ _ → here refl
  out-go (((((map-skip _ , _) , _) , _) , () , _) ∷ _)
  out-go (((((map-pin _ , _) , _) , _) , () , _) ∷ _)

map-back : ∀ {A B} (g : A → B) (s : Obs Timeline [] A) {rx} → Met (at (map g s)) rx
         → Σ _ λ sc → Met (at s) sc × values rx ≡ L.map g (values sc) × (Ends rx → Ends sc)
map-back g s = MapLayer.out-go g s

------------------------------------------------------------------------
-- A concat

-- A CONCAT'S LAST VALUE IS ITS SECOND PART'S: a concat of a program
-- with a lone value that completes has met that value last.  It ends
-- only once its second lane has, whose value it has met; the first lane
-- ended before the second started, and shows nothing past its end.
module ConcatLayer {X : Set} (s : Obs Timeline [] X) (c : X) where
  bs : List Bool
  bs = true ∷ false ∷ []

  F : Bool → Den X
  F b = ⟦ if b then s else of [ c ] ⟧ []

  O = enter (Op.of bs) root

  module B = Bounded 1 F O
  module V = Values O
  open Nths O using (nth-val; nth-fun; nth-inj)

  C = at (concatˢ s (of [ c ]))

  q₀ q₁ : Pos
  q₀ = root ⊕ [ ix 0 ]
  q₁ = root ⊕ [ ix 1 ]

  o-val : ∀ {q a} → O q (out a) → (q ≡ q₀ × a ≡ true) ⊎ (q ≡ q₁ × a ≡ false)
  o-val (at-out , _)                 = inj₁ (refl , refl)
  o-val (on-out at-out , _)          = inj₂ (refl , refl)
  o-val (on-out (on-out ()) , _)

  x₀ : O q₀ (out true)
  x₀ = at-out , of-reach root 0 bs {q₀} {out true}

  x₁ : O q₁ (out false)
  x₁ = on-out at-out , of-reach root 0 bs {q₁} {out false}

  nth₀ : V.Nth 0 q₀ true
  nth₀ = V.first x₀ λ y → mn y
    where
      mn : ∀ {k b} → O k (out b) → q₀ ≼ k
      mn y with o-val y
      ... | inj₁ (refl , _) = ≼-refl {q₀}
      ... | inj₂ (refl , _) = ≺→≼ {q₀} {q₁} tt

  nth₁ : V.Nth 1 q₁ false
  nth₁ = V.next nth₀ x₁ tt nx
    where
      nx : ∀ {k b} → O k (out b) → q₀ ≺ k → q₁ ≼ k
      nx y lt with o-val y
      ... | inj₁ (refl , _) = ⊥-elim (≺-irrefl {q₀} lt)
      ... | inj₂ (refl , _) = ≼-refl {q₁}

  IM = inv-⟦⟧ s [] (λ ()) (q₀ ⊕ [ ix 1 ]) (tt , λ ())

  -- The first lane, wherever it runs, shows nothing past an end of it.
  first-quiet : ∀ {i s′ cE k x} → B.Sub i q₀ s′ true → enter (F true) (q₀ ⊕ [ ix 1 ]) cE end → enter (F true) s′ k (out x) → cE ≺ k → ⊥
  first-quiet (nth , st) yE y lt with nth-inj nth nth₀
  first-quiet (nth , B.room _) yE y lt | refl = pinby-vis tt (InvAt.quiet IM yE y lt)
  first-quiet (nth , B.freed () _) yE y lt | refl
  first-quiet (nth , B.queued () _ _ _ _) yE y lt | refl

  -- An end of the first lane, the lane at its value's second child.
  first-end : ∀ {cE} → B.Ends 0 [] cE → enter (F true) (q₀ ⊕ [ ix 1 ]) cE end
  first-end (q , a , s′ , nth , st , (yE , _)) with nth-fun nth nth₀
  ... | refl with o-val (nth-val nth)
  ...   | inj₂ (() , _)
  first-end (q , a , s′ , nth , B.room _ , (yE , _)) | refl | inj₁ (_ , refl) = yE
  first-end (q , a , s′ , nth , B.freed () _ , (yE , _)) | refl | inj₁ (_ , refl)
  first-end (q , a , s′ , nth , B.queued () _ _ _ _ , (yE , _)) | refl | inj₁ (_ , refl)

  -- The second lane starts past an end of the first.
  second-start : ∀ {i s₁} → B.Sub i q₁ s₁ false → Σ Pos λ cE → enter (F true) (q₀ ⊕ [ ix 1 ]) cE end × cE ≺ s₁
  second-start (nth , st) with nth-inj nth nth₁
  second-start (nth , B.room (s≤s ())) | refl
  second-start (nth , B.freed _ (inj₁ (cE , e , lt))) | refl =
    cE , first-end e , ≺-trans {cE} {q₁} {q₁ ⊕ [ ix 1 ]} lt (≺-ext q₁ {ix 1} [])
  second-start (nth , B.queued {c′} _ _ (inj₁ (cE , e , refl)) _ _) | refl = cE , first-end e , ≺-ext cE []

  -- Past the second lane's value, every value met is it.
  past-second : ∀ {i s₁ k x} → B.Sub i q₁ s₁ false → C k (out x) → (s₁ ⊕ [ ix 0 ]) ≺ k → x ≡ c
  past-second {s₁ = s₁} {k} sub (B.lane ox _ (_ , s′ , sub′ , (y , _)) _ _ , _) lt with o-val ox
  ... | inj₂ (refl , refl) with proj₁ y
  ...   | at-out        = refl
  ...   | on-out ()
  past-second {s₁ = s₁} {k} sub (B.lane ox _ (_ , s′ , sub′ , (y , _)) _ _ , _) lt | inj₁ (refl , refl) with second-start sub
  ... | cE , yE , ce = ⊥-elim (first-quiet sub′ yE y (≺-trans {cE} {s₁} {k} ce (≺-trans {s₁} {s₁ ⊕ [ ix 0 ]} {k} (≺-ext s₁ []) lt)))
  past-second _ (B.run () _ , _) _

  done-of : ∀ {k} → C k end → B.Done k
  done-of (B.oend _ d , _)           = d
  done-of (B.lend _ _ _ _ _ d , _)   = d
  done-of (B.lane _ _ _ _ () , _)
  done-of (B.run () _ , _)
  done-of (B.rend () _ _ , _)

  -- The values after a value `c`, each `c`.
  ends-c : ∀ (zs : List (Pos × Ev X)) → (∀ {k x} → (k , out x) ∈ zs → x ≡ c) → Σ (List X) λ vs → c ∷ values zs ≡ vs ++ [ c ]
  ends-c [] _ = [] , refl
  ends-c ((k , out x) ∷ zs) h with h (here refl) | ends-c zs (λ m → h (there m))
  ... | refl | vs , eq = c ∷ vs , cong (c ∷_) eq
  ends-c ((k , skip) ∷ zs) h  = ends-c zs (λ m → h (there m))
  ends-c ((k , end) ∷ zs) h   = ends-c zs (λ m → h (there m))
  ends-c ((k , pin _) ∷ zs) h = ends-c zs (λ m → h (there m))

  concat-last′ : ∀ {sc} → Met C sc → Ends sc → Σ (List X) λ vs → values sc ≡ vs ++ [ c ]
  concat-last′ {sc} m en with snoc-view sc
  ... | inj₁ refl with en
  ...   | ()
  concat-last′ {sc} m en | inj₂ (ys , (qe , e) , refl) with ends-last ys m en
  ... | refl with run-row m (∈-++⁺ʳ ys (here refl))
  ...   | yq@(jq , (ks , rq)) , _ with done-of yq
  ...     | dn@((c₀ , xo , c₀q) , lanes) with lanes x₁ (1 , false , nth₁) q₁q (λ ())
    where
      q₁q : q₁ ≺ qe
      q₁q with of-end root 0 bs (proj₁ xo)
      ... | refl = ≺-≼-≺ {q₁} {root ⊕ [ last ]} {qe} tt c₀q
  ...       | cL , (i , s₁ , sub , ((yL , _) , _)) , cLq with of-end s₁ 0 [ c ] yL
  ...         | refl with ∈-∃++ inRun
    where
      kc = s₁ ⊕ [ ix 0 ]
      kcq : kc ≺ qe
      kcq = ≺-≼-≺ {kc} {s₁ ⊕ [ last ]} {qe} (to≺ kc (s₁ ⊕ [ last ]) (<ᵖ-part s₁ {ix 0} {last} [] [] refl)) cLq
      rowC : C kc (out c)
      rowC = B.lane x₁ (1 , false , nth₁) (i , s₁ , sub , ((at-out , of-reach s₁ 0 [ c ] {kc} {out c}) , ≺-ext s₁ [])) (λ ()) tt ,
             ks , λ {k′} y lt _ → rq y (≺-trans {k′} {kc} {qe} lt kcq) tt
      inRun : (kc , out c) ∈ (ys ++ [ (qe , end) ])
      inRun = run-has (at-func (concatˢ s (of [ c ]))) m rowC tt tt (≺→≼ {kc} {qe} kcq) (∈-++⁺ʳ ys (here refl))
  ...           | as , zs , eq with ends-c zs past
    where
      kc = s₁ ⊕ [ ix 0 ]
      tl : Run C (just kc) zs
      tl = subst (λ w → Run C w zs) (cursor-snoc nothing as)
             (run-tail (as ++ [ (kc , out c) ]) (subst (Run C nothing) (trans eq (sym (++-assoc as [ (kc , out c) ] zs))) m))
      past : ∀ {k x} → (k , out x) ∈ zs → x ≡ c
      past mem = past-second sub (proj₁ (run-row tl mem)) (run-after tl mem)
  ...             | vs , eqv = values as ++ vs ,
    trans (cong values eq) (trans (values-++ as ((s₁ ⊕ [ ix 0 ] , out c) ∷ zs))
      (trans (cong (values as ++_) eqv) (sym (++-assoc (values as) vs [ c ]))))

concat-last : ∀ {X} (s : Obs Timeline [] X) (c : X) {sc} → Met (at (concatˢ s (of [ c ]))) sc → Ends sc
            → Σ (List X) λ vs → values sc ≡ vs ++ [ c ]
concat-last s c = ConcatLayer.concat-last′ s c
