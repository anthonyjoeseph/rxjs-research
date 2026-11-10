{-# OPTIONS --guardedness #-}

-- A READING'S ROWS BEFORE A POSITION, LISTED EXACTLY, wherever finitely
-- many precede (`listed`).  The rows are a cut program's: with `m`
-- positions covering what lies before `q`, the program is within `m` of
-- its `m`-th approximant (`denotation.Laws.from`), and that of the same
-- approximant cut at `m + 2` rows (`denotation.Laws.Cut.cut-ne`), so all
-- three have the same rows up to `q`.  The cut program is finite, and its
-- listing (`listC`, the oracle's `listT` with the cut leaves) is never
-- cut short, so holds exactly its rows.
module simultaneous.Listing where

open import Data.Bool using (Bool; false; _∨_)
open import Data.List using (List; []; _∷_; _++_; [_]; length; applyUpTo; filter) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-applyUpTo⁺; ∈-applyUpTo⁻; ∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup) renaming (map to all-map)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary.Decidable.Core using (T?)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.Events as Ev
open import denotation.Events using (Events; Timeline; timelineAt; start; ofᴱ)
open import denotation.Position using (Pos; _<ᵖ_; ix; last; root; _⊕_)
open import denotation.EmissionSet
  using (out; skip; end; EmissionSet; _≺_; Few; InE; at-out; at-skip; at-end; on-out; on-skip; enter;
  After; DenEnv; ⟦_⟧; Spin; spin)
open import denotation.Laws.Modulus using (AgreeTo; ≺→≼; upto)
open import denotation.Laws.Count using (Cnt; AgC; ag-cnt; AgC-trans; AgC-sym)
open import denotation.Laws.Worlds using (⊑-refl)
open import denotation.Laws using (from)
open import denotation.Laws.ColdInv using (depth)
open import denotation.Laws.Cut using (Deep; spinIx; capprox; cut-ne)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled
  using (Row; _⊣_; rows; short; bind; mapM; mapRows; scanRows; takeRows; mergeRows; switchRows; exhaustRows; connRows;
  rejoin; hotOf; lanes; afterL; past; values; anyᵇ; module BoundedL)
open import quickcheck.Tabled.Exact.Base using (Exact; Exactly; sound; complete; bind⁻; lanes-from; lanes-to; afterL-exact)
open import quickcheck.Tabled.Exact
  using (truncate-exact; map-exact; take-exact; merge-exact; conn-exact; rejoin-exact; proper-exact; defer-exact; EnvRel; []; _∷_; env-lookup)
open import quickcheck.Tabled.Exact.Scan using (scan-exact)
open import quickcheck.Tabled.Exact.Switch using (switch-exact)
open import quickcheck.Tabled.Exact.Exhaust using (exhaust-exact)
open import quickcheck.Tabled.Exact.Bounded using (bounded-exact)

------------------------------------------------------------------------
-- Listed rows

-- The rows before `q`, every one and nothing else.
Listed : ∀ {A} → EmissionSet A → Pos → Set
Listed t q = Σ (List Pos) λ ks → (∀ {k e} → t k e → k ≺ q → k ∈ ks) × (∀ {k} → k ∈ ks → k ≺ q × Σ _ (t k))

-- Wherever finitely many rows precede, they are listed.
Listing : ∀ {A} → EmissionSet A → Set
Listing t = ∀ {q} → Few t q → Listed t q

------------------------------------------------------------------------
-- The cut leaves, listed

-- A stream's first `N` rows.
walkN : ∀ {A} → ℕ → Events A → List (Row A)
walkN zero    _               = []
walkN (suc n) (Ev.out k a r)  = (k , out a) ∷ walkN n (Ev.Events∞.force r)
walkN (suc n) (Ev.skip k r)   = (k , skip) ∷ walkN n (Ev.Events∞.force r)
walkN (suc n) (Ev.end k)      = (k , end) ∷ []
walkN (suc n) Ev.hush         = []

walkN-exact : ∀ {A} N (ev : Events A) → Exact (walkN N ev ⊣ false) (Deep (InE ev) depth N)
walkN-exact N ev = record { sound = s N ev ; complete = c N ev }
  where
    s : ∀ {A} N (ev : Events A) {q e} → (q , e) ∈ walkN N ev → Deep (InE ev) depth N q e
    s zero    _               ()
    s (suc n) (Ev.out k a r)  (here refl) = at-out , s≤s z≤n
    s (suc n) (Ev.out k a r)  (there m)   = let (x , lt) = s n _ m in on-out x , s≤s lt
    s (suc n) (Ev.skip k r)   (here refl) = at-skip , s≤s z≤n
    s (suc n) (Ev.skip k r)   (there m)   = let (x , lt) = s n _ m in on-skip x , s≤s lt
    s (suc n) (Ev.end k)      (here refl) = at-end , s≤s z≤n
    s (suc n) (Ev.end k)      (there ())
    s (suc n) Ev.hush         ()

    c : ∀ {A} N (ev : Events A) {q e} → Deep (InE ev) depth N q e → (q , e) ∈ walkN N ev
    c zero    _ (_ , ())
    c (suc n) _ (at-out , _)            = here refl
    c (suc n) _ (at-skip , _)           = here refl
    c (suc n) _ (at-end , _)            = here refl
    c (suc n) _ (on-out x , s≤s lt)     = there (c n _ (x , lt))
    c (suc n) _ (on-skip x , s≤s lt)    = there (c n _ (x , lt))

-- `of`'s stream is no longer than its values and its end.
private
  of-depth : ∀ {A} p i (xs : List A) {q e} (x : InE (ofᴱ p i xs) q e) → depth x < suc (length xs)
  of-depth p i []       at-end     = s≤s z≤n
  of-depth p i (_ ∷ xs) at-out     = s≤s z≤n
  of-depth p i (_ ∷ xs) (on-out x) = s≤s (of-depth p (suc i) xs x)

of-exact : ∀ {A} p (xs : List A) → Exact (walkN (suc (length xs)) (ofᴱ p 0 xs) ⊣ false) (InE (ofᴱ p 0 xs))
of-exact p xs = record
  { sound    = λ m → proj₁ (sound (walkN-exact (suc (length xs)) (ofᴱ p 0 xs)) m)
  ; complete = λ x → complete (walkN-exact (suc (length xs)) (ofᴱ p 0 xs)) (x , of-depth p 0 xs x) }

-- A spin's first `N` rows.
spinRows : ∀ {A} → ℕ → Pos → List (Row A)
spinRows N p = applyUpTo (λ i → p ⊕ [ ix i ] , skip) N

spin-exact : ∀ {A} N p → Exact {A} (spinRows N p ⊣ false) (Deep (Spin p) spinIx N)
spin-exact N p = record
  { sound    = λ m → let (i , lt , eq) = ∈-applyUpTo⁻ (λ i → p ⊕ [ ix i ] , skip) m in subst (λ r → Deep (Spin p) spinIx N (proj₁ r) (proj₂ r)) (sym eq) (spin i , lt)
  ; complete = λ { (spin i , lt) → ∈-applyUpTo⁺ (λ i → p ⊕ [ ix i ] , skip) lt } }

------------------------------------------------------------------------
-- The cut program, listed

-- `quickcheck.Tabled.listT`, each leaf cut as `capprox` cuts it.
listC : ∀ {Γ A} → ℕ → ℕ → Obs Timeline Γ A → All Tb.Listed Γ → Pos → Maybe (Tb.Listed A)
listC N n       (cold c)          ρ p = just (walkN N (start p (timelineAt c p)) ⊣ false)
listC N n       empty             ρ p = just ([ p ⊕ [ last ] , end ] ⊣ false)
listC N n       (of xs)           ρ p = just (walkN (suc (length xs)) (ofᴱ p 0 xs) ⊣ false)
listC N n       (map f s)         ρ p = bind (listC N n s ρ p) λ l → just (mapRows f l)
listC N n       (scan f z s)      ρ p = bind (listC N n s ρ p) λ l → just (scanRows f z l)
listC N n       (takeWhile i q s) ρ p = bind (listC N n s ρ p) λ l → just (takeRows i q l)
listC N n       (flatMap (mergeᶠ nothing) f s) ρ p =
  bind (listC N n s ρ p) λ o → bind (lanes (afterL (λ a → listC N n (f a) ρ)) (values (rows o))) λ ls → just (mergeRows o ls)
listC N n       (flatMap (mergeᶠ (just k)) f s) ρ p =
  bind (listC N n s ρ p) λ o → BoundedL.listB k (afterL (λ a → listC N n (f a) ρ)) o
listC N n       (flatMap switchᶠ f s) ρ p =
  bind (listC N n s ρ p) λ o → bind (lanes (afterL (λ a → listC N n (f a) ρ)) (values (rows o))) λ ls → just (switchRows o ls)
listC N n       (flatMap exhaustᶠ f s) ρ p =
  bind (listC N n s ρ p) λ o → bind (lanes (afterL (λ a → listC N n (f a) ρ)) (values (rows o))) λ ls → just (exhaustRows o ls)
listC N n       (connect s b)     ρ p =
  bind (listC N n s ρ (p ⊕ [ ix 1 ])) λ σ →
  bind (listC N n b (hotOf σ ∷ ρ) (p ⊕ [ ix 0 ])) λ β →
  just (connRows p σ β)
listC N n       (connected i)     ρ p = just (rejoin p (lookup ρ i))
listC N zero    (defer l)         ρ p = just (spinRows N p ⊣ false)
listC N (suc n) (defer l)         ρ p =
  bind (listC N n (Later.force l) ρ (p ⊕ [ ix 1 ])) λ b → just (((p ⊕ [ ix 0 ] , skip) ∷ rows b) ⊣ short b)

-- WHAT `listC` LISTS UNCUT IS EXACTLY THE CUT PROGRAM'S ROWS.
listC-exact : ∀ {Γ A} N n (o : Obs Timeline Γ A) {ρL : All Tb.Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD
  → ∀ p {l} → listC N n o ρL p ≡ just l → Exactly l (enter (capprox N n o ρD) p)
listC-exact N n (cold c)  ρ p refl = truncate-exact (λ _ → walkN-exact N _)
listC-exact N n empty     ρ p refl = truncate-exact (λ _ → record { sound = λ { (here refl) → at-end ; (there ()) } ; complete = λ { at-end → here refl } })
listC-exact N n (of xs)   ρ p refl = truncate-exact (λ _ → of-exact p xs)
listC-exact N n (map f s) {ρL} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (l₀ , e₀ , refl) = truncate-exact (map-exact f (listC-exact N n s ρ p e₀))
listC-exact N n (scan f z s) {ρL} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (l₀ , e₀ , refl) = truncate-exact (scan-exact f z l₀ (listC-exact N n s ρ p e₀))
listC-exact N n (takeWhile i q s) {ρL} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (l₀ , e₀ , refl) = truncate-exact (take-exact i q l₀ (listC-exact N n s ρ p e₀))
listC-exact N n (flatMap (mergeᶠ nothing) f s) {ρL} {ρD} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (o , eo , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = truncate-exact (merge-exact (λ a → capprox N n (f a) ρD) o ls (listC-exact N n s ρ p eo)
  (lanes-from {ln = afterL (λ a → listC N n (f a) ρL)} {D = λ a → After (capprox N n (f a) ρD)}
    (afterL-exact {ln = λ a → listC N n (f a) ρL} {D = λ a → enter (capprox N n (f a) ρD)} (λ {a} {s′} el → listC-exact N n (f a) ρ s′ el)) els)
  (lanes-to {ln = afterL (λ a → listC N n (f a) ρL)} els))
listC-exact N n (flatMap (mergeᶠ (just k)) f s) {ρL} {ρD} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (o , eo , e₁) =
  truncate-exact (bounded-exact k (λ a → capprox N n (f a) ρD) _ (afterL (λ a → listC N n (f a) ρL)) o (listC-exact N n s ρ p eo)
    (afterL-exact {ln = λ a → listC N n (f a) ρL} {D = λ a → enter (capprox N n (f a) ρD)} (λ {a} {s′} el → listC-exact N n (f a) ρ s′ el)) e₁)
listC-exact N n (flatMap switchᶠ f s) {ρL} {ρD} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (o , eo , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = truncate-exact (switch-exact (λ a → capprox N n (f a) ρD) o ls (listC-exact N n s ρ p eo)
  (lanes-from {ln = afterL (λ a → listC N n (f a) ρL)} {D = λ a → After (capprox N n (f a) ρD)}
    (afterL-exact {ln = λ a → listC N n (f a) ρL} {D = λ a → enter (capprox N n (f a) ρD)} (λ {a} {s′} el → listC-exact N n (f a) ρ s′ el)) els)
  (lanes-to {ln = afterL (λ a → listC N n (f a) ρL)} els))
listC-exact N n (flatMap exhaustᶠ f s) {ρL} {ρD} ρ p e with bind⁻ {m = listC N n s ρL p} e
... | (o , eo , e₁) with bind⁻ {m = lanes (afterL (λ a → listC N n (f a) ρL)) (values (rows o))} e₁
... | (ls , els , refl) = truncate-exact (exhaust-exact (λ a → capprox N n (f a) ρD) o ls (listC-exact N n s ρ p eo)
  (lanes-from {ln = afterL (λ a → listC N n (f a) ρL)} {D = λ a → After (capprox N n (f a) ρD)}
    (afterL-exact {ln = λ a → listC N n (f a) ρL} {D = λ a → enter (capprox N n (f a) ρD)} (λ {a} {s′} el → listC-exact N n (f a) ρ s′ el)) els)
  (lanes-to {ln = afterL (λ a → listC N n (f a) ρL)} els))
listC-exact N n (connect s b) {ρL} {ρD} ρ p e with bind⁻ {m = listC N n s ρL (p ⊕ [ ix 1 ])} e
... | (σl , eσ , e₁) with bind⁻ {m = listC N n b (hotOf σl ∷ ρL) (p ⊕ [ ix 0 ])} e₁
... | (βl , eβ , refl) =
  truncate-exact (conn-exact (capprox N n s ρD) (λ h → capprox N n b (h ∷ ρD)) p σl βl σx
    (listC-exact N n b ((λ p′ → truncate-exact (rejoin-exact (proper-exact σx) p′)) ∷ ρ) (p ⊕ [ ix 0 ]) eβ))
  where
    σx = listC-exact N n s ρ (p ⊕ [ ix 1 ]) eσ
listC-exact N n (connected i) ρ p refl = env-lookup ρ i p
listC-exact N zero    (defer l) ρ p refl = truncate-exact (λ _ → spin-exact N p)
listC-exact N (suc n) (defer l) {ρL} ρ p e with bind⁻ {m = listC N n (Later.force l) ρL (p ⊕ [ ix 1 ])} e
... | (b , eb , refl) = truncate-exact (defer-exact (listC-exact N n (Later.force l) ρ (p ⊕ [ ix 1 ]) eb))

------------------------------------------------------------------------
-- The cut program's listing is never cut short

private
  -- `m` is `just` something with `P`.
  Gets : ∀ {X : Set} → (X → Set) → Maybe X → Set
  Gets {X} P m = Σ X λ x → m ≡ just x × P x

  bind-gets : ∀ {X Y : Set} {P : X → Set} {Q : Y → Set} {m : Maybe X} {k : X → Maybe Y}
            → Gets P m → (∀ x → P x → Gets Q (k x)) → Gets Q (bind m k)
  bind-gets (x , refl , px) h = h x px

  mapM-gets : ∀ {X Y : Set} {P : Y → Set} {f : X → Maybe Y} (xs : List X) → (∀ x → Gets P (f x)) → Gets (All P) (mapM f xs)
  mapM-gets []       h = [] , refl , []
  mapM-gets (x ∷ xs) h = bind-gets (h x) λ y py → bind-gets (mapM-gets xs h) λ ys pys → y ∷ ys , refl , py ∷ pys

  Uncut : ∀ {A} → Tb.Listed A → Set
  Uncut l = short l ≡ false

  UncutEnv : ∀ {Γ} → All Tb.Listed Γ → Set
  UncutEnv []      = ⊤
  UncutEnv (l ∷ ρ) = Uncut l × UncutEnv ρ

  uncut-lookup : ∀ {Γ A} {ρ : All Tb.Listed Γ} → UncutEnv ρ → (i : A ∈ Γ) → Uncut (lookup ρ i)
  uncut-lookup {ρ = l ∷ ρ} (u , _)  (here refl) = u
  uncut-lookup {ρ = l ∷ ρ} (_ , us) (there i)   = uncut-lookup us i

  or-false : ∀ {a b} → a ≡ false → b ≡ false → a ∨ b ≡ false
  or-false refl refl = refl

  none : ∀ {X : Set} {p : X → Bool} {xs} → All (λ x → p x ≡ false) xs → anyᵇ p xs ≡ false
  none []       = refl
  none (px ∷ a) rewrite px = none a

  module Lanes {A B : Set} (ln : A → Pos → Maybe (Tb.Listed B)) (ok : ∀ a s → Gets Uncut (ln a s)) where
    after-ok : ∀ a s → Gets Uncut (afterL ln a s)
    after-ok a s = bind-gets (ok a s) λ l ul → past s l , refl , ul

    lanes-ok : ∀ vs → Gets (All λ x → Uncut (proj₂ (proj₂ x))) (lanes (afterL ln) vs)
    lanes-ok vs = mapM-gets vs λ qa → bind-gets (after-ok (proj₂ qa) (proj₁ qa ⊕ [ ix 1 ])) λ l ul → _ , refl , ul

    module _ (k : ℕ) (o : Tb.Listed A) where
      open BoundedL k (afterL ln) o using (vals; starts; laneAt; entry; levels; boundedRows; listB)

      EntryOk : ℕ × Pos × A × List (Pos × Tb.Listed B) → Set
      EntryOk g = All (λ sl → Uncut (proj₂ sl)) (proj₂ (proj₂ (proj₂ g)))

      entry-ok : ∀ i ess qa → Gets (λ e → All (λ sl → Uncut (proj₂ sl)) (proj₂ (proj₂ e))) (entry i ess qa)
      entry-ok i ess qa =
        bind-gets {m = mapM (laneAt (proj₂ qa)) (starts i (proj₁ qa) ess)}
          (mapM-gets (starts i (proj₁ qa) ess) λ s → bind-gets (after-ok (proj₂ qa) s) λ l ul → (s , l) , refl , ul)
          λ ss ass → (proj₁ qa , proj₂ qa , ss) , refl , ass

      levels-ok : ∀ K i ess vs → Gets (All EntryOk) (levels K i ess vs)
      levels-ok zero    i ess vs = [] , refl , []
      levels-ok (suc K) i ess vs =
        bind-gets (mapM-gets vs (entry-ok i ess)) λ gs ags →
        bind-gets (levels-ok K (suc i) _ _) λ rest arest → _ , refl , AllP.++⁺ (AllP.map⁺ ags) arest

      bounded-ok : Uncut o → Gets Uncut listB
      bounded-ok uo = bind-gets (levels-ok (length vals) 0 [] (Tb.Order.nths vals 0)) λ gs ags →
        boundedRows gs , refl , or-false uo (none (all-map none ags))

-- THE CUT PROGRAM IS LISTED IN FULL: every leaf is finite.
listC-ok : ∀ {Γ A} N n (o : Obs Timeline Γ A) {ρL : All Tb.Listed Γ} → UncutEnv ρL → ∀ p → Gets Uncut (listC N n o ρL p)
listC-ok N n       (cold c)          u p = _ , refl , refl
listC-ok N n       empty             u p = _ , refl , refl
listC-ok N n       (of xs)           u p = _ , refl , refl
listC-ok N n       (map f s)         u p = bind-gets (listC-ok N n s u p) λ l ul → _ , refl , ul
listC-ok N n       (scan f z s)      u p = bind-gets (listC-ok N n s u p) λ l ul → _ , refl , ul
listC-ok N n       (takeWhile i q s) u p = bind-gets (listC-ok N n s u p) λ l ul → _ , refl , ul
listC-ok N n       (flatMap (mergeᶠ nothing) f s) {ρL} u p =
  bind-gets (listC-ok N n s u p) λ o uo → bind-gets (L.lanes-ok (values (rows o))) λ ls uls → _ , refl , or-false uo (none uls)
  where module L = Lanes (λ a → listC N n (f a) ρL) (λ a → listC-ok N n (f a) u)
listC-ok N n       (flatMap (mergeᶠ (just k)) f s) {ρL} u p =
  bind-gets (listC-ok N n s u p) λ o uo → L.bounded-ok k o uo
  where module L = Lanes (λ a → listC N n (f a) ρL) (λ a → listC-ok N n (f a) u)
listC-ok N n       (flatMap switchᶠ f s) {ρL} u p =
  bind-gets (listC-ok N n s u p) λ o uo → bind-gets (L.lanes-ok (values (rows o))) λ ls uls → _ , refl , or-false uo (none uls)
  where module L = Lanes (λ a → listC N n (f a) ρL) (λ a → listC-ok N n (f a) u)
listC-ok N n       (flatMap exhaustᶠ f s) {ρL} u p =
  bind-gets (listC-ok N n s u p) λ o uo → bind-gets (L.lanes-ok (values (rows o))) λ ls uls → _ , refl , or-false uo (none uls)
  where module L = Lanes (λ a → listC N n (f a) ρL) (λ a → listC-ok N n (f a) u)
listC-ok N n       (connect s b)     u p =
  bind-gets (listC-ok N n s u (p ⊕ [ ix 1 ])) λ σ uσ → bind-gets (listC-ok N n b (uσ , u) (p ⊕ [ ix 0 ])) λ β uβ → _ , refl , or-false uσ uβ
listC-ok N n       (connected i)     u p = _ , refl , uncut-lookup u i
listC-ok N zero    (defer l)         u p = _ , refl , refl
listC-ok N (suc n) (defer l)         u p = bind-gets (listC-ok N n (Later.force l) u (p ⊕ [ ix 1 ])) λ b ub → _ , refl , ub

------------------------------------------------------------------------
-- A reading's rows, listed

-- WHEREVER FINITELY MANY ROWS PRECEDE, THEY ARE LISTED: those of the cut
-- program, before the cut.
-- Sealed: consumers read its type, never its body.
opaque
  listed : ∀ {A} (o : Obs Timeline [] A) → Listing (enter (⟦ o ⟧ []) root)
  listed {A} o {q} (ks , few) = ks′ , cover , back
    where
      m : ℕ
      m = length ks
      N : ℕ
      N = suc (suc m)
      t : EmissionSet A
      t = enter (⟦ o ⟧ []) root
      c : EmissionSet A
      c = enter (capprox N m o []) root

      ag : AgC m t c
      ag = AgC-trans (from m o [] (λ ()) root (tt , λ ()))
                     (AgC-sym (cut-ne {m = m} {N} ≤-refl m o [] (λ ()) root (tt , λ ())))

      cnt : Cnt m t q
      cnt = ks , ≤-refl , λ x lt → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (few x lt))

      agq : AgreeTo q t c
      agq = ag-cnt ag q (inj₁ cnt)

      lc : Gets Uncut (listC N m o [] root)
      lc = listC-ok N m o tt root
      L : Tb.Listed A
      L = proj₁ lc

      ex : Exact L c
      ex = listC-exact N m o [] root (proj₁ (proj₂ lc)) (proj₂ (proj₂ lc))

      ks′ : List Pos
      ks′ = filter (λ k → T? (k <ᵖ q)) (mapL proj₁ (rows L))

      cover : ∀ {k e} → t k e → k ≺ q → k ∈ ks′
      cover {k} x kq = ∈-filter⁺ (λ k → T? (k <ᵖ q)) (∈-map⁺ proj₁ (complete ex (proj₁ (upto agq {k} (≺→≼ {k} {q} kq)) x))) kq

      back : ∀ {k} → k ∈ ks′ → k ≺ q × Σ _ (t k)
      back mk with ∈-filter⁻ (λ k → T? (k <ᵖ q)) {xs = mapL proj₁ (rows L)} mk
      ... | mk′ , kq with ∈-map⁻ proj₁ mk′
      ...   | (k , e) , mr , refl = kq , e , proj₂ (upto agq {k} (≺→≼ {k} {q} kq)) (sound ex mr)
