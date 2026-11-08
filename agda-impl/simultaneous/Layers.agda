{-# OPTIONS --guardedness #-}

-- A PROGRAM READ THROUGH THE OPERATOR ON TOP: what a subscriber to a
-- `scan`, or to an `each` (a merge of `of`s), meets, read back as what a
-- subscriber to its source meets.  Generic in the source: nothing here
-- knows the batcher.
module simultaneous.Layers where

open import Data.List using (List; []; _∷_; concatMap; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-concatMap⁺; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Tree using (Obs; scan)
open import denotation.Events using (Timeline; Pos; root; fresh; _≟ᵖ_; _<ᵖ_; ix; last; <ᵖ-apart; <ᵖ-between; <ᵖ-part; ix-<; <ᵖ-split)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; _≺_; _≼_; enter; ⟦_⟧; module Scan; Den; module Op; InE; ofᴱ; at-out; on-out; Seen; Reach; Dep; Ended; LaneOf; module Merge)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Worlds using (InvAt; PinBy)
open import denotation.Laws.Worlds.Leaves using (module AccF; of-end; of-end-row; of-idx; ine-pin)
open import denotation.Laws.Modulus using (≼-antisym; entered-reach; entered-few; ≺-trans; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≺-≼-≺; ≼-trans; ≼-or-≻; ≺-ext)
open import denotation.Laws.Fold using (fold)
open import adequacy.SubOne using (scan-reach; lift-in)
open import adequacy.SubJoin using (of-rows; of-in; of-reach)
open import adequacy.Complete using (reach)
open import adequacy.Simulated using () renaming (cursor to simulated)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met; values; values-++; Ends)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (each)

-- A closed program's emission set, subscribed at the root.
at : ∀ {A} → Obs Timeline [] A → EmissionSet A
at s = enter (⟦ s ⟧ []) root

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

  fu : ∀ {y e e′} → S y e → S y e′ → e ≡ e′
  fu = InvAt.func (inv-⟦⟧ s [] (λ ()) root (tt , λ ()))

  open AccF f z {S} fu using (acc-val; acc-func)

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

to≺ : ∀ {x y} → x <ᵖ y ≡ true → x ≺ y
to≺ = Equivalence.from T-≡

from≺ : ∀ {x y} → x ≺ y → x <ᵖ y ≡ true
from≺ = Equivalence.to T-≡

≼-false : ∀ {x y} → x ≼ y → y <ᵖ x ≡ false
≼-false {x} {y} h with y <ᵖ x
... | true  = ⊥-elim (h tt)
... | false = refl

≼-split : ∀ {x y} → x ≼ y → x ≺ y ⊎ x ≡ y
≼-split {x} {y} h with <ᵖ-split x y (≼-false {x} {y} h)
... | inj₁ lt = inj₁ (to≺ lt)
... | inj₂ eq = inj₂ eq

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
prefix-end (((x , _) , _) ∷ run) (refl ∷ []) (here refl) with run-past-end x run
... | refl = refl
prefix-end (((x , _) , _) ∷ run) (refl ∷ (_ ∷ _)) (here refl) with run-past-end x run
... | ()
prefix-end (_ ∷ run) (refl ∷ p) (there h) = cong (_ ∷_) (prefix-end run p h)

ends-last : ∀ {A} {t : EmissionSet A} {c} ys {y} → Run t c (ys ++ [ y ]) → Ends (ys ++ [ y ]) → proj₂ y ≡ end
ends-last []       _ (here eq) = eq
ends-last (_ ∷ ys) (((x , _) , _) ∷ run) (here refl) with run-past-end x run | ys
... | () | []
... | () | _ ∷ _
ends-last (_ ∷ ys) (_ ∷ run) (there h) = ends-last ys run h

prefix-values : ∀ {A} {xs ys : List (Pos × Ev A)} → Prefix _≡_ xs ys → Prefix _≡_ (values xs) (values ys)
prefix-values [] = []
prefix-values (_∷_ {x = (_ , out _)} refl p) = refl ∷ prefix-values p
prefix-values (_∷_ {x = (_ , skip)}  refl p) = prefix-values p
prefix-values (_∷_ {x = (_ , end)}   refl p) = prefix-values p
prefix-values (_∷_ {x = (_ , pin _)} refl p) = prefix-values p

prefix-refl : ∀ {A : Set} (xs : List A) → Prefix _≡_ xs xs
prefix-refl []       = []
prefix-refl (_ ∷ xs) = refl ∷ prefix-refl xs

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
  IE = inv-⟦⟧ (each f s) [] (λ ()) root (tt , λ ())

  fuS : ∀ {y e e′} → S y e → S y e′ → e ≡ e′
  fuS = InvAt.func IS

  fuE : ∀ {y e e′} → E y e → E y e′ → e ≡ e′
  fuE = InvAt.func IE

  ln : Pos → Pos
  ln q = q ++ [ ix 1 ]

  pinby-vis : ∀ {A c} {e : Ev A} → Visible e → PinBy c e → ⊥
  pinby-vis {e = out _} _ (_ , () , _)
  pinby-vis {e = end}   _ (_ , () , _)
  pinby-vis {e = skip}  ()
  pinby-vis {e = pin _} ()

  -- A row of the source under another is none.
  sole : ∀ {q e zs e′} → S q e → S (q ++ zs) e′ → zs ≡ []
  sole {zs = []}    _ _ = refl
  sole {zs = _ ∷ _} x y = ⊥-elim (InvAt.flat IS x y)

  ext-absurd : ∀ {q e y e′ zs} → S q e → S y e′ → q ≺ y → y ≡ q ++ zs → ⊥
  ext-absurd {q} x x′ lt eq with sole x (subst (λ w → S w _) eq x′)
  ... | refl = ≺-irrefl {q} (subst (q ≺_) (trans eq (++-identityʳ q)) lt)

  -- What lies under a row of the source lies before the rows past it.
  past-under : ∀ {q e q′ e′} → S q e → S q′ e′ → q ≺ q′ → ∀ ys → (q ++ ys) ≺ q′
  past-under {q} {q′ = q′} x x′ lt ys = to≺ (<ᵖ-apart q q′ ys (from≺ lt) λ zs eq → ext-absurd x x′ lt eq)

  none-under : ∀ {q e y e′} ys → S q e → S y e′ → q ≺ y → y ≼ q ++ ys → ⊥
  none-under {q} {y = y} ys x x′ lt le with ≼-split {y} {q ++ ys} le
  ... | inj₂ eq = ext-absurd x x′ lt eq
  ... | inj₁ lt′ = ext-absurd x x′ lt (proj₂ (<ᵖ-between q y ys (from≺ lt) (from≺ lt′)))

  vis-end : ∀ {q e c} → S q e → Visible e → S c end → q ≼ c
  vis-end x vi y cq = pinby-vis vi (InvAt.quiet IS y x cq)

  val-end : ∀ {q a c} → S q (out a) → S c end → q ≺ c
  val-end {q} {c = c} x y with ≼-split {q} {c} (vis-end x tt y)
  ... | inj₁ lt   = lt
  ... | inj₂ refl with fuS x y
  ...   | ()

  seenS : ∀ {q e} → S q e → Visible e → Seen S q e
  seenS {e = out _} x _ = (x , vis-end x tt) , entered-few (⟦ s ⟧ []) root tt x
  seenS {e = end}   x _ = (x , vis-end x tt) , entered-few (⟦ s ⟧ []) root tt x
  seenS {e = skip}  _ ()
  seenS {e = pin _} _ ()

  lane-at : ∀ {q xs k e} → InE (ofᴱ (ln q) 0 xs) k e → Σ Pos λ ys → k ≡ q ++ ix 1 ∷ ys
  lane-at {q} {xs} y with of-idx (ln q) 0 xs y
  ... | inj₁ (j , _ , eq) = ix j ∷ [] , trans eq (++-assoc q [ ix 1 ] [ ix j ])
  ... | inj₂ eq           = last ∷ [] , trans eq (++-assoc q [ ix 1 ] [ last ])

  lane-≼ : ∀ {q xs k e} → InE (ofᴱ (ln q) 0 xs) k e → q ≼ k
  lane-≼ {q} {k = k} y with lane-at y
  ... | ys , eq = ≺→≼ {q} {k} (subst (q ≺_) (sym eq) (≺-ext q ys))

  -- A row told of the each, by the source row it hangs under.
  data Vis : Pos → Pos → Ev Y → Set where
    vlane : ∀ {q a k b} → S q (out a) → InE (ofᴱ (ln q) 0 (f a)) k (out b) → Vis k q (out b)
    vend  : ∀ {c} → S c end → Vis c c end

  lend-absurd : ∀ {q a c} → S q (out a) → InE (ofᴱ (ln q) 0 (f a)) c end → M.Done c → ⊥
  lend-absurd {q} {a} x y ((c₀ , y₀ , le) , _) with of-end (ln q) 0 (f a) y
  ... | refl = none-under (ix 1 ∷ last ∷ []) x y₀ (val-end x y₀) (subst (c₀ ≼_) (++-assoc q [ ix 1 ] [ last ]) le)

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

  vis-under : ∀ {k q e} → Vis k q e → q ≼ k
  vis-under (vlane _ y)   = lane-≼ y
  vis-under (vend {c} _)  = ≼-refl {c}

  vis-before : ∀ {k q e q′ e′} → Vis k q e → S q′ e′ → q ≺ q′ → k ≺ q′
  vis-before {q′ = q′} (vlane x y) x′ lt with lane-at y
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
    rowsOf (q , out a) = q ∷ (q ++ [ ix 0 ]) ∷ of-rows (ln q) 0 (f a)
    rowsOf (q , _)     = q ∷ []

    module _ {q e₀} (qin : (q , e₀) ∈ whole) where
      private
        x₀  = proj₁ (run-row mw qin)
        vi₀ = proj₂ (run-row mw qin)
        ksS = proj₁ (proj₂ (seenS x₀ vi₀))
        hS  = proj₂ (proj₂ (seenS x₀ vi₀))

      ks : List Pos
      ks = concatMap (λ q′ → q′ ∷ (q′ ++ [ ix 0 ]) ∷ []) ksS ++ concatMap rowsOf whole

      in-whole : ∀ {r k′} → r ∈ whole → k′ ∈ rowsOf r → k′ ∈ ks
      in-whole m r = ∈-++⁺ʳ (concatMap _ ksS) (∈-concatMap⁺ rowsOf (any-map (λ { refl → r }) m))

      row-in : ∀ {q′ e′} → S q′ e′ → q′ ≼ q → q′ ∈ ks
      row-in {e′ = out _} x le = in-whole (run-has fuS mw x tt tt le qin) (here refl)
      row-in {e′ = end}   x le = in-whole (run-has fuS mw x tt tt le qin) (here refl)
      row-in {q′} {e′ = skip} x le with ≼-split {q′} {q} le
      ... | inj₁ lt = ∈-++⁺ˡ (lift-in (λ q′ → q′ ∷ (q′ ++ [ ix 0 ]) ∷ []) (here refl) (hS x lt))
      ... | inj₂ refl = ⊥-elim (skip-vis (fuS x x₀) vi₀)
        where skip-vis : ∀ {e : Ev X} → skip ≡ e → Visible e → ⊥
              skip-vis refl ()
      row-in {q′} {e′ = pin r} x le with ≼-split {q′} {q} le
      ... | inj₁ lt = ∈-++⁺ˡ (lift-in (λ q′ → q′ ∷ (q′ ++ [ ix 0 ]) ∷ []) (here refl) (hS x lt))
      ... | inj₂ refl = ⊥-elim (pin-vis (fuS x x₀) vi₀)
        where pin-vis : ∀ {e : Ev X} → pin r ≡ e → Visible e → ⊥
              pin-vis refl ()

      val-in : ∀ {q′ a′} → S q′ (out a′) → q′ ≼ q → (q′ ++ [ ix 0 ]) ∈ ks
      val-in x le = in-whole (run-has fuS mw x tt tt le qin) (there (here refl))

      lane-in : ∀ {q′ a′ k′ e′} → S q′ (out a′) → q′ ≼ q → InE (ofᴱ (ln q′) 0 (f a′)) k′ e′ → k′ ∈ ks
      lane-in {q′} {a′} x le y = in-whole (run-has fuS mw x tt tt le qin) (there (there (of-in (ln q′) 0 (f a′) y)))

      -- A merge row before a row anchored at `q` hangs under a source row at or before `q`.
      reachE : ∀ {k e} → Vis k q e → Reach M.JoinT k e
      reachE {k} v = ks , pick
        where
          anc : ∀ {q′ e′ k′} → S q′ e′ → q′ ≼ k′ → k′ ≺ k → q′ ≼ q
          anc {q′} {k′ = k′} x le kk qq = ≺-absurd {k} {k′} (≺-≼-≺ {k} {q′} {k′} (vis-before v x qq) le) kk

          pick : ∀ {k′ e′} → M.JoinT k′ e′ → k′ ≺ k → Dep k _ k′ e′ → k′ ∈ ks
          pick (M.val {q′} x) kk _ = val-in x (anc x (≺→≼ {q′} {q′ ++ [ ix 0 ]} (≺-ext q′ [])) kk)
          pick (M.step {q′} x) kk _ = row-in x (anc x (≼-refl {q′}) kk)
          pick (M.opin {q′} x) kk _ = row-in x (anc x (≼-refl {q′}) kk)
          pick (M.oend {q′} x _) kk _ = row-in x (anc x (≼-refl {q′}) kk)
          pick (M.opass {q′} x _) kk _ = row-in x (anc x (≼-refl {q′}) kk)
          pick (M.lane x _ ((y , _) , _) _ _) kk _ = lane-in x (anc x (lane-≼ y) kk) y
          pick (M.lend x _ ((y , _) , _) _ _ _) kk _ = lane-in x (anc x (lane-≼ y) kk) y
          pick (M.lpass x _ ((y , _) , _) _ _ _) kk _ = lane-in x (anc x (lane-≼ y) kk) y
          pick (M.hand _ _ _ _ ()) _ _
          pick (M.left x _ ((y , _) , _) _ _) kk _ = lane-in x (anc x (lane-≼ y) kk) y
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

      at-i : ∀ i {q′ e′} → S q′ e′ → q ≺ q′ → (p ++ [ ix i ]) ≺ q′
      at-i i {q′} x′ lt = subst (_≺ q′) (sym (++-assoc q [ ix 1 ] [ ix i ])) (past-under sq x′ lt (ix 1 ∷ ix i ∷ []))

      in-rest : ∀ i xs {k′ e′} → InE (ofᴱ p (suc i) xs) k′ e′ → (p ++ [ ix i ]) ≺ k′
      in-rest i xs y with of-idx p (suc i) xs y
      ... | inj₁ (j , le , refl) = to≺ (<ᵖ-part p {ix i} {ix j} [] [] (ix-< le))
      ... | inj₂ refl            = to≺ (<ᵖ-part p {ix i} {last} [] [] refl)

      go : ∀ {c} i xs → (∀ {k e} → InE (ofᴱ p i xs) k e → InE (ofᴱ p 0 (f a)) k e) → J c i xs
         → Σ _ λ rows → Run E c rows × values rows ≡ xs × Inv (just q) (cursor c rows)
      go {c} i [] _ (j₁ , j₂ , _) = [] , [] , refl , λ v → fin v , j₂ v
        where
          fin : ∀ {k q′ e} → Vis k q′ e → After c k → q ≺ q′
          fin v ak with j₁ v ak
          ... | inj₁ (_ , _ , _ , ())
          ... | inj₂ lt = lt
      go {c} i (x ∷ xs) emb (j₁ , j₂ , j₃) with go (suc i) xs (λ y → emb (on-out y)) (j₁′ , j₂′ , j₃′)
        where
          k = p ++ [ ix i ]
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
          k = p ++ [ ix i ]
          v : Vis k q (out x)
          v = vlane sq (emb at-out)
          row : E k (out x)
          row = M.lane sq tt ((emb at-out , of-reach p 0 (f a)) , ≺-ext p []) (λ ()) tt , reachE qin v
          mn : ∀ {k′ e′} → E k′ e′ → Visible e′ → After c k′ → k ≼ k′
          mn y vi ak with vis y vi
          ... | q′ , v′ with j₁ v′ ak
          ...   | inj₁ (refl , b , refl , at-out)    = ≼-refl {k}
          ...   | inj₁ (refl , b , refl , on-out y′) = ≺→≼ {k} {_} (in-rest i xs y′)
          ...   | inj₂ lt = ≺→≼ {k} {_} (≺-≼-≺ {k} {q′} (at-i i (proj₁ (proj₂ (vis-anc v′))) lt) (vis-under v′))

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
        j₁ (vlane x′ y) ak | inj₂ refl with fuS x′ x
        ... | refl = inj₁ (refl , _ , refl , y)
        j₁ (vend x′) ak | inj₂ refl with fuS x x′
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
          ln q′ ++ [ last ] , ((of-end-row (ln q′) 0 (f a′) , of-reach (ln q′) 0 (f a′)) , ≺-ext (ln q′) []) ,
          ≺→≼ {ln q′ ++ [ last ]} {c} (subst (_≺ c) (sym (++-assoc q′ [ ix 1 ] [ last ])) (past-under x′ x lt (ix 1 ∷ last ∷ [])))
        row : E c end
        row = M.oend x ((c , x , ≼-refl {c}) , λ x′ _ lt _ → lane-ended x′ lt) , reachE (sub (here refl)) (vend x)
        mn : ∀ {k′ e′} → E k′ e′ → Visible e′ → After cE k′ → c ≼ k′
        mn y vi ak with vis y vi
        ... | q′ , v′ = ≼-trans {c} {q′} {_} (lst (proj₁ (proj₂ (vis-anc v′))) (proj₂ (proj₂ (vis-anc v′))) (proj₁ (inv v′) ak)) (vis-under v′)
        inv-end : Inv (just c) (just c)
        inv-end {k} {q′} v = fwd v , λ lt → ≺-≼-≺ {c} {q′} {k} lt (vis-under v)
          where
            fwd : ∀ {k q′ e} → Vis k q′ e → c ≺ k → c ≺ q′
            fwd {k} {q′} v ck with ≼-or-≻ q′ c
            ... | inj₂ lt = lt
            ... | inj₁ le with ≼-split {q′} {c} le
            ...   | inj₁ lt = ⊥-elim (≺-absurd {c} {k} ck (vis-before v x lt))
            fwd (vend _)     ck | inj₁ _ | inj₂ refl = ⊥-elim (≺-irrefl {c} ck)
            fwd (vlane x′ _) ck | inj₁ _ | inj₂ refl with fuS x′ x
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
      sc = rs″ ++ [ (q , e₀) ]
      rs = ys ++ [ (k , e) ]

      longer : Prefix _≡_ rs rs′
      longer with run-det fuE m mE
      ... | inj₁ pr = pr
      ... | inj₂ pr with prefix-split pr
      ...   | inj₁ eq′ = subst (Prefix _≡_ rs) (sym eq′) (prefix-refl rs)
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

      pre : Prefix _≡_ (values rs) (concatMap f (values sc))
      pre = subst (Prefix _≡_ (values rs)) eq (prefix-values longer)

      ends : Ends rs → Ends sc × values rs ≡ concatMap f (values sc)
      ends h with ends-last ys m h | v
      ... | refl | vend _ = ++⁺ʳ rs″ (here refl) , trans (cong values (prefix-end mE longer h)) eq

each-out : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {rs} → Met (at (each f s)) rs
         → Σ _ λ sc → Met (at s) sc × Prefix _≡_ (values rs) (concatMap f (values sc))
                    × (Ends rs → Ends sc × values rs ≡ concatMap f (values sc))
each-out f s = EachLayer.each-out′ f s

each-in : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {sc} → Met (at s) sc
        → Σ _ λ rs → Met (at (each f s)) rs × values rs ≡ concatMap f (values sc) × (Ends sc → Ends rs)
each-in f s = EachLayer.each-in′ f s
