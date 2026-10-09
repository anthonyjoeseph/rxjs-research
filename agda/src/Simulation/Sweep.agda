------------------------------------------------------------------
-- THE SWEEP AS A FILTER, and the counts and guards it reads: what a
-- drop or a cut on both sides needs below every pass that makes one.
------------------------------------------------------------------
module Simulation.Sweep where

open import Data.Bool    using (Bool; true; false; T; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.List    using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_; _<ᵇ_; _≡ᵇ_; _≟_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; <ᵇ⇒<; <⇒<ᵇ; <⇒≢; <-asym; <-trans; <-≤-trans; m≤m+n; +-monoʳ-<; 1+n≢0; +-cancelˡ-≡)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp       using (Ctx; Closed)
open import Rx.Mint      using (counter; sourceᵏ)
open import Rx.Prim      using (Source)
open import Rx.Evaluator using (LiveSource; RegRow; regSource; sameSource; memberSource; sweepLive; Sched; EvalSt; Arrival; cascadeClose)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Schedules using (Sync; ord)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Simulation.Stores using (srcCount; guardOf; aboveᵇ; above-≤; SrcNum; slot~; dyn~; SrcPair; ArrRel; RowRel; hot~; RegRel; []; _∷_; read~; cold~; defer~; mach; Partners; ArrRows; Spent; Named)
  renaming (here to sp-here; there to sp-there)

-- a source number that sits under another is not it
sameSource-lt : ∀ {m k} → k < m → sameSource m k ≡ false
sameSource-lt {m} {k} lt with m ≡ᵇ k in e
... | false = refl
... | true  = ⊥-elim (<⇒≢ lt (sym (≡ᵇ⇒≡ m k (subst T (sym e) tt))))

sameSource-no : ∀ {m k} → m ≢ k → sameSource m k ≡ false
sameSource-no {m} {k} ne with m ≡ᵇ k in e
... | false = refl
... | true  = ⊥-elim (ne (≡ᵇ⇒≡ m k (subst T (sym e) tt)))

-- a source number against itself
same-refl : ∀ x → sameSource x x ≡ true
same-refl zero    = refl
same-refl (suc x) = same-refl x

------------------------------------------------------------------
-- The sweep as a filter, and what a filter does to pointwise lists
------------------------------------------------------------------

sweepL : ∀ {A : Set} → (A → Bool) → List A → List A
sweepL p []       = []
sweepL p (x ∷ xs) = if p x then x ∷ sweepL p xs else sweepL p xs

sweep-eq : ∀ {n} {Γ : Ctx n} {t} (reg : List (RegRow Γ t)) (ls : List (LiveSource Γ)) → sweepLive reg ls ≡ sweepL (guardOf reg) ls
sweep-eq reg []       = refl
sweep-eq reg (l ∷ ls) = cong (λ r → if guardOf reg l then l ∷ r else r) (sweep-eq reg ls)

module _ {A B : Set} {p : A → Bool} {q : B → Bool} where

  -- two lists kept by guards that agree pair up
  sweepL-pw : ∀ {R : A → B → Set} {xs ys} → Pointwise R xs ys → Pointwise (λ x y → p x ≡ q y) xs ys
            → Pointwise R (sweepL p xs) (sweepL q ys)
  sweepL-pw [] [] = []
  sweepL-pw {xs = x ∷ _} {ys = y ∷ _} (r ∷ rs) (g ∷ gs) with p x | q y | g | sweepL-pw rs gs
  ... | true  | .true  | refl | ih = r ∷ ih
  ... | false | .false | refl | ih = ih

module _ {A B : Set} (p : A → Bool) (f : A → B) where

  all-sweep : ∀ {P : B → Set} {xs} → All P (map f xs) → All P (map f (sweepL p xs))
  all-sweep {xs = []}     a        = a
  all-sweep {xs = x ∷ xs} (px ∷ a) with p x
  ... | true  = px ∷ all-sweep a
  ... | false = all-sweep a

  unique-sweep : ∀ {xs} → Unique (map f xs) → Unique (map f (sweepL p xs))
  unique-sweep {xs = []}     u        = u
  unique-sweep {xs = x ∷ xs} (a ∷ u) with p x
  ... | true  = all-sweep a ∷ unique-sweep u
  ... | false = unique-sweep u

module _ {n m} {Γ : Ctx n} {Γ′ : Ctx m} {p : LiveSource Γ → Bool} {q : LiveSource Γ′ → Bool} where

  sync-sweep : ∀ {ls ls′} → Sync ls ls′ → Pointwise (λ x y → p x ≡ q y) ls ls′ → Sync (sweepL p ls) (sweepL q ls′)
  sync-sweep []ˢ []                                       = []ˢ
  sync-sweep {l ∷ ls} {l′ ∷ ls′} ((tk , rk) ∷ˢ sy) (g ∷ gs)
    with p l | q l′ | g | sync-sweep sy gs | sweepL-pw {R = λ x x′ → (ord l <ᵇ ord x) ≡ (ord l′ <ᵇ ord x′)} rk gs
  ... | true  | .true  | refl | ih | rk′ = (tk , rk′) ∷ˢ ih
  ... | false | .false | refl | ih | _   = ih

------------------------------------------------------------------
-- Source numbers
------------------------------------------------------------------

same-yes : ∀ {x y} → x ≡ y → sameSource x y ≡ true
same-yes {x} refl = same-refl x

same-eq : ∀ {x y} → sameSource x y ≡ true → x ≡ y
same-eq {x} {y} e = ≡ᵇ⇒≡ x y (subst T (sym e) tt)

neq-of : ∀ {x y} → sameSource x y ≡ false → x ≢ y
neq-of {x} e refl with trans (sym e) (same-refl x)
... | ()

lt-false : ∀ {n s} → n < s → (s <ᵇ n) ≡ false
lt-false {n} {s} lt with s <ᵇ n in e
... | false = refl
... | true  = ⊥-elim (<-asym lt (<ᵇ⇒< s n (subst T (sym e) tt)))

module _ {m} {Δ : Ctx m} {t} where

  -- a row elsewhere leaves a count alone, a row there raises it
  count-hit : ∀ k (r : RegRow Δ t) K → sameSource k (regSource (proj₁ (proj₂ r))) ≡ true → srcCount k (r ∷ K) ≡ suc (srcCount k K)
  count-hit k (rid , x , c) K e = cong (λ b → if b then suc (srcCount k K) else srcCount k K) e

  count-pass : ∀ k (r : RegRow Δ t) K → sameSource k (regSource (proj₁ (proj₂ r))) ≡ false → srcCount k (r ∷ K) ≡ srcCount k K
  count-pass k (rid , x , c) K e = cong (λ b → if b then suc (srcCount k K) else srcCount k K) e

  -- none at a source, none behind the head either
  count-tail : ∀ {k} (r : RegRow Δ t) K → srcCount k (r ∷ K) ≡ 0 → srcCount k K ≡ 0
  count-tail {k} (rid , s , c) K z = go _ refl
    where
    go : ∀ b → sameSource k (regSource s) ≡ b → srcCount k K ≡ 0
    go true  e = ⊥-elim (1+n≢0 (trans (sym (count-hit k (rid , s , c) K e)) z))
    go false e = trans (sym (count-pass k (rid , s , c) K e)) z

T-true : ∀ {b} → T b → b ≡ true
T-true {true} _ = refl

t≢f : true ≡ false → ⊥
t≢f ()

module _ {n} {Γ : Ctx n} {t} where

  -- whether a registration is at a source
  onSrc : Source → RegRow Γ t → Bool
  onSrc x r = sameSource x (regSource (proj₁ (proj₂ r)))

  -- a registration in a list puts its source's count up
  mem-any : ∀ {r : RegRow Γ t} {K} → r ∈ K → any (onSrc (regSource (proj₁ (proj₂ r)))) K ≡ true
  mem-any {r = r} {K = _ ∷ K} (here refl) = cong (_∨ any (onSrc (regSource (proj₁ (proj₂ r)))) K) (same-refl (regSource (proj₁ (proj₂ r))))
  mem-any {r = r} {K = k ∷ K} (there m)   = trans (cong (onSrc (regSource (proj₁ (proj₂ r))) k ∨_) (mem-any m)) (∨-zeroʳ _)

  -- a live source with a registration is kept
  guard-hit : ∀ (K : List (RegRow Γ t)) (l : LiveSource Γ) → any (onSrc (LiveSource.source l)) K ≡ true → guardOf K l ≡ true
  guard-hit K l cov = trans (cong ((LiveSource.source l <ᵇ n) ∨_) cov) (∨-zeroʳ _)

  -- a slot's live entry is never swept
  guard-low : ∀ (K : List (RegRow Γ t)) (l : LiveSource Γ) → LiveSource.source l < n → guardOf K l ≡ true
  guard-low K l lt = cong (_∨ any (onSrc (LiveSource.source l)) K) (T-true (<⇒<ᵇ lt))

------------------------------------------------------------------
-- Slot numbers and source pairs
------------------------------------------------------------------

module _ {n : ℕ} where

  -- a raw slot's number is no stamped slot's
  raw≢stamped : ∀ (i j : Fin n) → toℕ (i ↑ˡ n) ≢ toℕ (n ↑ʳ j)
  raw≢stamped i j eq = <⇒≢ (<-≤-trans (toℕ<n i) (m≤m+n n (toℕ j))) (trans (sym (toℕ-↑ˡ i n)) (trans eq (toℕ-↑ʳ n j)))

  raw<ₙ : ∀ (i : Fin n) → toℕ (i ↑ˡ n) < n + n
  raw<ₙ i = subst (_< n + n) (sym (toℕ-↑ˡ i n)) (<-≤-trans (toℕ<n i) (m≤m+n n n))

  stamped< : (i : Fin n) → toℕ (n ↑ʳ i) < n + n
  stamped< i = subst (_< n + n) (sym (toℕ-↑ʳ n i)) (+-monoʳ-< n (toℕ<n i))

-- the impl's hot rows sit at slots, under any minted source
mach-lt : ∀ {n s′} (i : Fin n) → n + n < s′ → sameSource s′ (toℕ (i ↑ˡ n)) ≡ false
mach-lt {n} i na′ = sameSource-lt (<-trans (raw<ₙ i) na′)

-- an arrival's pair of sources is a row's pair of sources or neither
arr-dec : ∀ {s s′ src src′ u u′ x x′} → ArrRel s s′ u u′ src src′ x x′
        → (sameSource s src ≡ true × sameSource s′ src′ ≡ true) ⊎ (sameSource s src ≡ false × sameSource s′ src′ ≡ false)
arr-dec {s} {s′} {src} {src′} (f , b) with sameSource s src in e
... | true  = inj₁ (refl , same-yes (proj₁ (f (same-eq e))))
... | false = inj₂ (refl , sameSource-no (λ eq′ → neq-of e (b eq′)))

arr-same : ∀ {s s′ src src′ u u′ x x′} → ArrRel s s′ u u′ src src′ x x′ → sameSource s src ≡ sameSource s′ src′
arr-same ar with arr-dec ar
... | inj₁ (e , e′) = trans e (sym e′)
... | inj₂ (e , e′) = trans e (sym e′)

≡ᵇ-sym : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ (k ≡ᵇ m)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc k) = refl
≡ᵇ-sym (suc m) zero    = refl
≡ᵇ-sym (suc m) (suc k) = ≡ᵇ-sym m k

-- a pair of one-source lists holds a pair of sources alike
member-one : ∀ s s′ x x′ → sameSource s x ≡ sameSource s′ x′ → memberSource x (s ∷ []) ≡ memberSource x′ (s′ ∷ [])
member-one s s′ x x′ e = cong (_∨ false) (trans (≡ᵇ-sym x s) (trans e (≡ᵇ-sym s′ x′)))

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a source the head of a list does not number is apart from the one a pair puts after it
  sp-apart : ∀ {x} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
           → All (x ≢_) (map LiveSource.source LP) → SrcPair κ LP LI s s′ u u′ → x ≢ s
  sp-apart (x≢ ∷ _) sp-here      = x≢
  sp-apart (_ ∷ ap) (sp-there q) = sp-apart ap q

  sp-apart′ : ∀ {x} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
            → All (x ≢_) (map LiveSource.source LI) → SrcPair κ LP LI s s′ u u′ → x ≢ s′
  sp-apart′ (x≢ ∷ _) sp-here      = x≢
  sp-apart′ (_ ∷ ap) (sp-there q) = sp-apart′ ap q

  -- with the sources on each side distinct, two pairs at one source on one side are at the other's
  sp-fun : ∀ {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′ t t′ w w′}
         → Unique (map LiveSource.source LP) → Unique (map LiveSource.source LI)
         → SrcPair κ LP LI s s′ u u′ → SrcPair κ LP LI t t′ w w′
         → (s ≡ t → s′ ≡ t′ × u ≡ w × u′ ≡ w′) × (s′ ≡ t′ → s ≡ t)
  sp-fun (_ ∷ _) (_ ∷ _) sp-here sp-here = (λ _ → refl , refl , refl) , λ _ → refl
  sp-fun (a ∷ _) (a′ ∷ _) sp-here (sp-there q) = (λ e → ⊥-elim (sp-apart a q e)) , λ e′ → ⊥-elim (sp-apart′ a′ q e′)
  sp-fun (a ∷ _) (a′ ∷ _) (sp-there p) sp-here = (λ e → ⊥-elim (sp-apart a p (sym e))) , λ e′ → ⊥-elim (sp-apart′ a′ p (sym e′))
  sp-fun (_ ∷ ul) (_ ∷ ul′) (sp-there p) (sp-there q) = sp-fun ul ul′ p q

  -- what a registry's rows say of a popped pair of sources, from the pair's place in the live lists
  arr-rows : ∀ {RS : List (LiveSource Γ)} {RS′ : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
           → Unique (map LiveSource.source RS) → Unique (map LiveSource.source RS′) → SrcPair κ RS RS′ s s′ u u′
           → ∀ {t π NP NI rg rg′} (rr : RegRel κ π {t} NP NI RS RS′ rg rg′) → ArrRows κ _ _ _ _ _ rr s s′ u u′
  arr-rows ua ua′ pk []                    = tt
  arr-rows ua ua′ pk (read~ _ _ _ ∷ q)     = arr-rows ua ua′ pk q
  arr-rows ua ua′ pk (cold~ sp _ _ _ ∷ q)  = sp-fun ua ua′ pk sp , arr-rows ua ua′ pk q
  arr-rows ua ua′ pk (defer~ sp _ _ _ _ _ ∷ q) = sp-fun ua ua′ pk sp , arr-rows ua ua′ pk q
  arr-rows ua ua′ pk (mach _ q)            = arr-rows ua ua′ pk q

  -- a minted pair of sources has a row on one side exactly when it has one on the other
  any-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′ s s′ u u′} → n < s → n + n < s′
           → (q : RegRel κ π {t} NP NI LP LI rs rs′) → ArrRows κ _ _ _ _ _ q s s′ u u′
           → any (onSrc s) rs ≡ any (onSrc s′) rs′
  any-rows na na′ [] _ = refl
  any-rows na na′ (read~ {i = i} _ _ _ ∷ q) ars =
    cong₂ _∨_ (trans (sameSource-lt (<-trans (toℕ<n i) na)) (sym (sameSource-lt (<-trans (stamped< i) na′)))) (any-rows na na′ q ars)
  any-rows na na′ (cold~ _ _ _ _ ∷ q) (ar , ars) = cong₂ _∨_ (arr-same ar) (any-rows na na′ q ars)
  any-rows na na′ (defer~ _ _ _ _ _ _ ∷ q) (ar , ars) = cong₂ _∨_ (arr-same ar) (any-rows na na′ q ars)
  any-rows {s′ = s′} na na′ (mach {rs′ = rs′} (hot~ {i = i} _ _ _) q) ars =
    trans (any-rows na na′ q ars) (sym (cong (_∨ any (onSrc s′) rs′) (mach-lt i na′)))

  -- and a pair of rows is at it alike
  dies-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′ s s′ u u′} → n < s → n + n < s′
            → (q : RegRel κ π {t} NP NI LP LI rs rs′) → ArrRows κ _ _ _ _ _ q s s′ u u′
            → Spent κ _ _ _ _ _ q (λ r → memberSource (regSource (proj₁ (proj₂ r))) (s ∷ []))
                                  (λ r′ → memberSource (regSource (proj₁ (proj₂ r′))) (s′ ∷ []))
  dies-rows na na′ [] _ = tt
  dies-rows {s = s} {s′ = s′} na na′ (read~ {i = i} _ _ _ ∷ q) ars =
    member-one s s′ (toℕ i) (toℕ (n ↑ʳ i)) (trans (sameSource-lt (<-trans (toℕ<n i) na)) (sym (sameSource-lt (<-trans (stamped< i) na′)))) , dies-rows na na′ q ars
  dies-rows {s = s} {s′ = s′} na na′ (cold~ {src = src} {src′ = src′} _ _ _ _ ∷ q) (ar , ars) = member-one s s′ src src′ (arr-same ar) , dies-rows na na′ q ars
  dies-rows {s = s} {s′ = s′} na na′ (defer~ {src = src} {src′ = src′} _ _ _ _ _ _ ∷ q) (ar , ars) = member-one s s′ src src′ (arr-same ar) , dies-rows na na′ q ars
  dies-rows na na′ (mach _ q) ars = dies-rows na na′ q ars

  -- a slot's number against another's, and their stamps alike
  stamp-same : ∀ (j i : Fin n) → sameSource (toℕ j) (toℕ i) ≡ sameSource (toℕ (n ↑ʳ j)) (toℕ (n ↑ʳ i))
  stamp-same j i with toℕ j ≟ toℕ i
  ... | yes e = trans (same-yes e) (sym (same-yes (trans (toℕ-↑ʳ n j) (trans (cong (n +_) e) (sym (toℕ-↑ʳ n i))))))
  ... | no ne = trans (sameSource-no ne)
                      (sym (sameSource-no (λ x → ne (+-cancelˡ-≡ n (toℕ j) (toℕ i) (trans (sym (toℕ-↑ʳ n j)) (trans x (toℕ-↑ʳ n i)))))))

  -- A PAIR OF ROWS IS AT A SLOT EXACTLY WHEN ITS PARTNER IS AT THE SLOT'S
  -- STAMP: a reader is stamped, and a minted source is above every slot
  stamp-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′} (i : Fin n)
            → (q : RegRel κ π {t} NP NI LP LI rs rs′)
            → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rs → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rs′
            → Spent κ _ _ _ _ _ q (λ r → sameSource (regSource (proj₁ (proj₂ r))) (toℕ i))
                                  (λ r′ → sameSource (regSource (proj₁ (proj₂ r′))) (toℕ (n ↑ʳ i)))
  stamp-rows i [] _ _ = tt
  stamp-rows i (read~ {i = j} _ _ _ ∷ q) (_ ∷ as) (_ ∷ as′) = stamp-same j i , stamp-rows i q as as′
  stamp-rows i (cold~ _ _ _ _ ∷ q) (a ∷ as) (a′ ∷ as′) =
    trans (sameSource-lt (<-≤-trans (toℕ<n i) (above-≤ a))) (sym (sameSource-lt (<-≤-trans (stamped< i) (above-≤ a′)))) , stamp-rows i q as as′
  stamp-rows i (defer~ _ _ _ _ _ _ ∷ q) (a ∷ as) (a′ ∷ as′) =
    trans (sameSource-lt (<-≤-trans (toℕ<n i) (above-≤ a))) (sym (sameSource-lt (<-≤-trans (stamped< i) (above-≤ a′)))) , stamp-rows i q as as′
  stamp-rows i (mach _ q) as (_ ∷ as′) = stamp-rows i q as as′

  -- and no partnered impl row is at a raw slot
  raw-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′} (i : Fin n)
           → (q : RegRel κ π {t} NP NI LP LI rs rs′) → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rs′
           → Spent κ _ _ _ _ _ q (λ _ → false) (λ r′ → sameSource (regSource (proj₁ (proj₂ r′))) (toℕ (i ↑ˡ n)))
  raw-rows i [] _ = tt
  raw-rows i (read~ {i = j} _ _ _ ∷ q) (_ ∷ as′) = sym (sameSource-no (λ x → raw≢stamped i j (sym x))) , raw-rows i q as′
  raw-rows i (cold~ _ _ _ _ ∷ q) (a′ ∷ as′) = sym (sameSource-lt (<-≤-trans (raw<ₙ i) (above-≤ a′))) , raw-rows i q as′
  raw-rows i (defer~ _ _ _ _ _ _ ∷ q) (a′ ∷ as′) = sym (sameSource-lt (<-≤-trans (raw<ₙ i) (above-≤ a′))) , raw-rows i q as′
  raw-rows i (mach _ q) (_ ∷ as′) = raw-rows i q as′

  -- and, with no stamped row, no pair is at the slot nor its raw slot
  close-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′} (i : Fin n)
             → (q : RegRel κ π {t} NP NI LP LI rs rs′)
             → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rs → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rs′
             → srcCount (toℕ (n ↑ʳ i)) rs′ ≡ 0
             → Spent κ _ _ _ _ _ q (λ r → sameSource (regSource (proj₁ (proj₂ r))) (toℕ i))
                                   (λ r′ → sameSource (regSource (proj₁ (proj₂ r′))) (toℕ (i ↑ˡ n)))
  close-rows i [] _ _ _ = tt
  close-rows i (_∷_ {r′ = r′} {rs′ = rs′} (read~ {i = j} _ _ _) q) (_ ∷ as) (_ ∷ as′) z with toℕ j ≟ toℕ i
  ... | yes e = ⊥-elim (1+n≢0 (trans (sym (count-hit (toℕ (n ↑ʳ i)) r′ rs′
                  (same-yes (trans (toℕ-↑ʳ n i) (trans (cong (n +_) (sym e)) (sym (toℕ-↑ʳ n j))))))) z))
  ... | no ne = trans (sameSource-no ne) (sym (sameSource-no (λ x → raw≢stamped i j (sym x)))) , close-rows i q as as′ (count-tail r′ rs′ z)
  close-rows i (_∷_ {r′ = r′} {rs′ = rs′} (cold~ _ _ _ _) q) (a ∷ as) (a′ ∷ as′) z =
    trans (sameSource-lt (<-≤-trans (toℕ<n i) (above-≤ a))) (sym (sameSource-lt (<-≤-trans (raw<ₙ i) (above-≤ a′))))
    , close-rows i q as as′ (count-tail r′ rs′ z)
  close-rows i (_∷_ {r′ = r′} {rs′ = rs′} (defer~ _ _ _ _ _ _) q) (a ∷ as) (a′ ∷ as′) z =
    trans (sameSource-lt (<-≤-trans (toℕ<n i) (above-≤ a))) (sym (sameSource-lt (<-≤-trans (raw<ₙ i) (above-≤ a′))))
    , close-rows i q as as′ (count-tail r′ rs′ z)
  close-rows i (mach {r′ = r′} {rs′ = rs′} _ q) as (_ ∷ as′) z = close-rows i q as as′ (count-tail r′ rs′ z)

  -- SO THE GUARDS OF TWO RELATED REGISTRIES AGREE: a slot's entry is kept on
  -- both sides, and a minted pair of entries is read off the rows alike
  rows-guards : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI K K′} (q : RegRel κ π {t} NP NI LP LI K K′)
              → Unique (map LiveSource.source LP) → Unique (map LiveSource.source LI)
              → Pointwise (λ l l′ → SrcNum κ (LiveSource.source l) (LiveSource.source l′)) LP LI
              → Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI
  rows-guards {LP = LP} {LI} {K} {K′} q ua ua′ = go (λ sp → sp)
    where
      go : ∀ {MP MI} → (∀ {s s′ u u′} → SrcPair κ MP MI s s′ u u′ → SrcPair κ LP LI s s′ u u′)
         → Pointwise (λ l l′ → SrcNum κ (LiveSource.source l) (LiveSource.source l′)) MP MI
         → Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) MP MI
      go f [] = []
      go f (_∷_ {l} {l′} x xs) = at x refl refl ∷ go (λ sp → f (sp-there sp)) xs
        where
          at : ∀ {s s′} → SrcNum κ s s′ → LiveSource.source l ≡ s → LiveSource.source l′ ≡ s′ → guardOf K l ≡ guardOf K′ l′
          at (slot~ j _) e e′ =
            trans (guard-low K l (subst (_< n) (sym e) (toℕ<n j))) (sym (guard-low K′ l′ (subst (_< n + n) (sym e′) (raw<ₙ j))))
          at (dyn~ p p′) refl refl =
            cong₂ _∨_ (trans (lt-false p) (sym (lt-false p′))) (any-rows p p′ q (arr-rows ua ua′ (f sp-here) q))


------------------------------------------------------------------
-- The rows
------------------------------------------------------------------

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a pair of live sources survives the sweep when its guard is up
  pair-sweep : ∀ {t} {K : List (RegRow Γ t)} {K′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))} {LP LI a b u u′}
             → Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI
             → any (onSrc a) K ≡ true
             → SrcPair κ LP LI a b u u′
             → SrcPair κ (sweepL (guardOf K) LP) (sweepL (guardOf K′) LI) a b u u′
  pair-sweep {K = K} {K′ = K′} (_∷_ {l} {l′} g gs) cov sp-here with guardOf K l | guardOf K′ l′ | g | guard-hit K l cov
  ... | true  | .true | refl | _  = sp-here
  ... | false | _     | _    | ()
  pair-sweep {K = K} {K′ = K′} (_∷_ {l} {l′} g gs) cov (sp-there sp) with guardOf K l | guardOf K′ l′ | g
  ... | true  | .true  | refl = sp-there (pair-sweep {K = K} {K′ = K′} gs cov sp)
  ... | false | .false | refl = pair-sweep {K = K} {K′ = K′} gs cov sp

  rowrel-sweep : ∀ {t π NP NI LP LI} {K : List (RegRow Γ t)} {K′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))} {r r′}
               → Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI → r ∈ K
               → RowRel κ π NP NI LP LI r r′
               → RowRel κ π NP NI (sweepL (guardOf K) LP) (sweepL (guardOf K′) LI) r r′
  rowrel-sweep g m (read~ k pr eq)                  = read~ k pr eq
  rowrel-sweep {K = K} {K′ = K′} g m (cold~ sp ib pr eq)          = cold~ (pair-sweep {K = K} {K′ = K′} g (mem-any m) sp) ib pr eq
  rowrel-sweep {K = K} {K′ = K′} g m (defer~ sp pi lnP lnI pr eq) = defer~ (pair-sweep {K = K} {K′ = K′} g (mem-any m) sp) pi lnP lnI pr eq

  regrel-sweep : ∀ {t π NP NI LP LI rs rs′} {K : List (RegRow Γ t)} {K′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))}
               → Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI → rs ⊆ K
               → RegRel κ π NP NI LP LI rs rs′
               → RegRel κ π NP NI (sweepL (guardOf K) LP) (sweepL (guardOf K′) LI) rs rs′
  regrel-sweep g sub []                      = []
  regrel-sweep {K = K} {K′ = K′} g sub (r ∷ q)                 = rowrel-sweep {K = K} {K′ = K′} g (sub (here refl)) r ∷ regrel-sweep {K = K} {K′ = K′} g (λ m → sub (there m)) q
  regrel-sweep {K = K} {K′ = K′} g sub (mach (hot~ h ib eq) q) = mach (hot~ h ib eq) (regrel-sweep {K = K} {K′ = K′} g sub q)

  -- and the sweep keeps every pairing of rows and every arrival's pair against them
  part-sweep : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′} {K : List (RegRow Γ t)} {K′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))}
             → (g : Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI) (sub : rs ⊆ K)
             → (q : RegRel κ π NP NI LP LI rs rs′) → ∀ {x x′} → Partners κ π NP NI LP LI q x x′
             → Partners κ π NP NI _ _ (regrel-sweep {K = K} {K′ = K′} g sub q) x x′
  part-sweep g sub []       ()
  part-sweep g sub (r ∷ q)  (inj₁ e) = inj₁ e
  part-sweep {K = K} {K′ = K′} g sub (r ∷ q) (inj₂ p) = inj₂ (part-sweep {K = K} {K′ = K′} g (λ m → sub (there m)) q p)
  part-sweep {K = K} {K′ = K′} g sub (mach (hot~ h ib eq) q) p = part-sweep {K = K} {K′ = K′} g sub q p

  spent-sweep : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′} {K : List (RegRow Γ t)} {K′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))}
              → (g : Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI) (sub : rs ⊆ K)
              → (q : RegRel κ π NP NI LP LI rs rs′) → ∀ {dP dI} → Spent κ π NP NI LP LI q dP dI
              → Spent κ π NP NI _ _ (regrel-sweep {K = K} {K′ = K′} g sub q) dP dI
  spent-sweep g sub [] s = s
  spent-sweep {K = K} {K′ = K′} g sub (r ∷ q) (e , s) = e , spent-sweep {K = K} {K′ = K′} g (λ m → sub (there m)) q s
  spent-sweep {K = K} {K′ = K′} g sub (mach (hot~ h ib eq) q) s = spent-sweep {K = K} {K′ = K′} g sub q s

  arr-sweep : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI rs rs′} {K : List (RegRow Γ t)} {K′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))}
            → (g : Pointwise (λ l l′ → guardOf K l ≡ guardOf K′ l′) LP LI) (sub : rs ⊆ K)
            → (q : RegRel κ π NP NI LP LI rs rs′) → ∀ {s s′ u u′} → ArrRows κ π NP NI LP LI q s s′ u u′
            → ArrRows κ π NP NI _ _ (regrel-sweep {K = K} {K′ = K′} g sub q) s s′ u u′
  arr-sweep g sub [] a = tt
  arr-sweep {K = K} {K′ = K′} g sub (read~ _ _ _ ∷ q) a = arr-sweep {K = K} {K′ = K′} g (λ m → sub (there m)) q a
  arr-sweep {K = K} {K′ = K′} g sub (cold~ _ _ _ _ ∷ q) (x , a) = x , arr-sweep {K = K} {K′ = K′} g (λ m → sub (there m)) q a
  arr-sweep {K = K} {K′ = K′} g sub (defer~ _ _ _ _ _ _ ∷ q) (x , a) = x , arr-sweep {K = K} {K′ = K′} g (λ m → sub (there m)) q a
  arr-sweep {K = K} {K′ = K′} g sub (mach (hot~ h ib eq) q) a = arr-sweep {K = K} {K′ = K′} g sub q a

-- a close names the closing source and nothing else
close-named : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {f} {sched : Sched Δ} {st : EvalSt e} {a : Arrival Δ}
            → Named f sched st → Arrival.source a < counter (Sched.mint sched) sourceᵏ → Named f sched (cascadeClose a st)
close-named N b = record { slots-below = Named.slots-below N ; ords-below = Named.ords-below N ; srcs-below = Named.srcs-below N
                         ; cut-below = Named.cut-below N ; dlv-below = [] ; dying-below = b ∷ [] }
