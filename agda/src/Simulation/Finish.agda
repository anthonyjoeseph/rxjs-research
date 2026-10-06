------------------------------------------------------------------
-- A MINTED SOURCE'S REGISTRATIONS DROPPED keep the stores related.  The
-- end of a last arrival drops every registration at the spent source and
-- then sweeps the live list down to the sources a registration is still at.
-- The arrival's pair of sources is the rows' partners, so the drop takes
-- the same rows from both registries; the sweep keeps a pair of live
-- sources together because the guard that decides it reads the same on
-- both sides, before the drop (the store's `swept`) and after it.
------------------------------------------------------------------
module Simulation.Finish where

open import Data.Bool    using (Bool; true; false; T; _∨_; _∧_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-zeroʳ; ∧-zeroʳ)
open import Data.Empty   using (⊥-elim)
open import Data.Fin     using (Fin; _↑ˡ_; _↑ʳ_; toℕ) renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective)
open import Data.List    using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_) renaming (map to pw-map)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All using (All; _∷_; []) renaming (map to mapᵃ)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (suc; _+_; _<_; _<ᵇ_; _≟_)
open import Rx.Evaluator.Reducible.Support using (sub-rule)
open import Rx.Evaluator.Reducible.Floor using (drop-sub)
open import Data.Nat.Properties using (≤-refl; 1+n≢0; ≡ᵇ⇒≡; <ᵇ⇒<; <⇒<ᵇ; <⇒≢; <-asym; <-trans; <-≤-trans; +-monoʳ-<; +-cancelˡ-≡; m≤m+n)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Rx.Exp       using (Ctx; Closed)
open import Rx.Prim      using (Source)
open import Rx.Evaluator using (LiveSource; Arrival; Sched; EvalSt; RegRow; regSource; sameSource; memberSource; dropSource; sweepLive; cascadeFinish; cascadeClose; shareFinish; arrSource; arrTy)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ; hotᵏ; sharedᵏ)
open import Data.Vec     using (lookup)
open import Simulation.Chains using (sameSource-lt; sameSource-no; same-refl; count-hit; count-pass)
open import Simulation.Schedules using (Sync; ord)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Simulation.Stores using (srcCount; Census; LatchRel; guardOf; SameAt; SrcNum; slot~; dyn~; SrcPair; RowRel; MachRow; hot~; RegRel; []; _∷_; read~; cold~; defer~; mach; ArrRel; ArrRows; Store; Arr; Owned)
  renaming (here to sp-here; there to sp-there)

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

------------------------------------------------------------------
-- The drop, and the guard after it
------------------------------------------------------------------

module _ {n} {Γ : Ctx n} {t} where

  -- whether a registration is at a source
  onSrc : Source → RegRow Γ t → Bool
  onSrc x r = sameSource x (regSource (proj₁ (proj₂ r)))

  drop-keep : ∀ s (r : RegRow Γ t) K → sameSource s (regSource (proj₁ (proj₂ r))) ≡ false → dropSource s (r ∷ K) ≡ r ∷ dropSource s K
  drop-keep s (rid , x , c) K e = cong (λ b → if b then dropSource s K else (rid , x , c) ∷ dropSource s K) e

  drop-skip : ∀ s (r : RegRow Γ t) K → sameSource s (regSource (proj₁ (proj₂ r))) ≡ true → dropSource s (r ∷ K) ≡ dropSource s K
  drop-skip s (rid , x , c) K e = cong (λ b → if b then dropSource s K else (rid , x , c) ∷ dropSource s K) e

  -- dropping a source's rows leaves every other source's count alone
  drop-other : ∀ x s (K : List (RegRow Γ t)) → sameSource x s ≡ false → any (onSrc x) (dropSource s K) ≡ any (onSrc x) K
  drop-other x s []      ne = refl
  drop-other x s (r ∷ K) ne with sameSource s (regSource (proj₁ (proj₂ r))) in e
  ... | false = cong (onSrc x r ∨_) (drop-other x s K ne)
  ... | true  = trans (drop-other x s K ne)
                  (sym (cong (_∨ any (onSrc x) K)
                             (trans (cong (sameSource x) (sym (same-eq e))) ne)))

  -- and leaves none at the dropped one
  drop-same : ∀ s (K : List (RegRow Γ t)) → any (onSrc s) (dropSource s K) ≡ false
  drop-same s []      = refl
  drop-same s (r ∷ K) with sameSource s (regSource (proj₁ (proj₂ r))) in e
  ... | false = trans (cong (_∨ any (onSrc s) (dropSource s K)) e) (drop-same s K)
  ... | true  = drop-same s K

  all-drop : ∀ {P : RegRow Γ t → Set} s {K} → All P K → All P (dropSource s K)
  all-drop s []                 = []
  all-drop s {r ∷ K} (p ∷ ps) with sameSource s (regSource (proj₁ (proj₂ r)))
  ... | true  = all-drop s ps
  ... | false = p ∷ all-drop s ps

  -- a drop at another source leaves a count alone
  count-drop : ∀ {k} y (K : List (RegRow Γ t)) → sameSource y k ≡ false → srcCount k (dropSource y K) ≡ srcCount k K
  count-drop y [] _ = refl
  count-drop {k} y (r ∷ K) ne = go _ refl _ refl
    where
    go : ∀ b₁ → sameSource y (regSource (proj₁ (proj₂ r))) ≡ b₁ → ∀ b₂ → sameSource k (regSource (proj₁ (proj₂ r))) ≡ b₂
       → srcCount k (dropSource y (r ∷ K)) ≡ srcCount k (r ∷ K)
    go true  e₁ true  e₂ = ⊥-elim (neq-of {y} {k} ne (trans (same-eq e₁) (sym (same-eq e₂))))
    go true  e₁ false e₂ = trans (cong (srcCount k) (drop-skip y r K e₁))
                             (trans (count-drop y K ne) (sym (count-pass k r K e₂)))
    go false e₁ true  e₂ = trans (cong (srcCount k) (drop-keep y r K e₁))
                             (trans (count-hit k r (dropSource y K) e₂)
                               (trans (cong suc (count-drop y K ne)) (sym (count-hit k r K e₂))))
    go false e₁ false e₂ = trans (cong (srcCount k) (drop-keep y r K e₁))
                             (trans (count-pass k r (dropSource y K) e₂)
                               (trans (count-drop y K ne) (sym (count-pass k r K e₂))))

  -- a drop at a source leaves none there
  count-self : ∀ k (K : List (RegRow Γ t)) → srcCount k (dropSource k K) ≡ 0
  count-self k [] = refl
  count-self k (r ∷ K) = go _ refl
    where
    go : ∀ b → sameSource k (regSource (proj₁ (proj₂ r))) ≡ b → srcCount k (dropSource k (r ∷ K)) ≡ 0
    go true  e = trans (cong (srcCount k) (drop-skip k r K e)) (count-self k K)
    go false e = trans (cong (srcCount k) (drop-keep k r K e))
                   (trans (count-pass k r (dropSource k K) e) (count-self k K))

  -- a drop at a source nothing stands at takes nothing
  drop-none : ∀ k (K : List (RegRow Γ t)) → srcCount k K ≡ 0 → dropSource k K ≡ K
  drop-none k [] _ = refl
  drop-none k (r ∷ K) z = go _ refl
    where
    go : ∀ b → sameSource k (regSource (proj₁ (proj₂ r))) ≡ b → dropSource k (r ∷ K) ≡ r ∷ K
    go true  e = ⊥-elim (1+n≢0 (trans (sym (count-hit k r K e)) z))
    go false e = trans (drop-keep k r K e) (cong (r ∷_) (drop-none k K (trans (sym (count-pass k r K e)) z)))

  -- a census holds whatever the raw slot's latch, once that is set
  census-done : ∀ {k₁ k₂ c d} {K : List (RegRow Γ t)} → Census k₁ k₂ K c d → Census k₁ k₂ K c true
  census-done (inj₁ x)              = inj₁ x
  census-done (inj₂ (e₁ , e₂ , _)) = inj₂ (e₁ , e₂ , λ _ → refl)

  -- and so keeps a census at two other sources
  census-drop : ∀ {k₁ k₂ c d} y (K : List (RegRow Γ t)) → sameSource y k₁ ≡ false → sameSource y k₂ ≡ false
              → Census k₁ k₂ K c d → Census k₁ k₂ (dropSource y K) c d
  census-drop y K n₁ n₂ (inj₁ (e , c))         = inj₁ (trans (count-drop y K n₁) e , c)
  census-drop y K n₁ n₂ (inj₂ (e₁ , e₂ , f)) = inj₂ (trans (count-drop y K n₁) e₁ , trans (count-drop y K n₂) e₂ , f)

  -- a registration in a list puts its source's count up
  mem-any : ∀ {r : RegRow Γ t} {K} → r ∈ K → any (onSrc (regSource (proj₁ (proj₂ r)))) K ≡ true
  mem-any {r = r} {K = _ ∷ K} (here refl) = cong (_∨ any (onSrc (regSource (proj₁ (proj₂ r)))) K) (same-refl (regSource (proj₁ (proj₂ r))))
  mem-any {r = r} {K = k ∷ K} (there m)   = trans (cong (onSrc (regSource (proj₁ (proj₂ r))) k ∨_) (mem-any m)) (∨-zeroʳ _)

  -- a live source with a registration is kept
  guard-hit : ∀ (K : List (RegRow Γ t)) (l : LiveSource Γ) → any (onSrc (LiveSource.source l)) K ≡ true → guardOf K l ≡ true
  guard-hit K l cov = trans (cong ((LiveSource.source l <ᵇ n) ∨_) cov) (∨-zeroʳ _)

  -- the dropped source's own live entry is swept
  guard-gone : ∀ (K : List (RegRow Γ t)) {s} (l : LiveSource Γ) → n < s → LiveSource.source l ≡ s → guardOf (dropSource s K) l ≡ false
  guard-gone K {s} l na ℓ =
    trans (cong (λ x → (x <ᵇ n) ∨ any (onSrc x) (dropSource s K)) ℓ) (cong₂ _∨_ (lt-false na) (drop-same s K))

  -- and every other live entry is kept as it was
  guard-other : ∀ (K : List (RegRow Γ t)) {s} (l : LiveSource Γ) → sameSource (LiveSource.source l) s ≡ false → guardOf (dropSource s K) l ≡ guardOf K l
  guard-other K {s} l ne = cong ((LiveSource.source l <ᵇ n) ∨_) (drop-other (LiveSource.source l) s K ne)

-- the guards still agree after the drops
pw-agree : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} {regP : List (RegRow Γ t)} {regI : List (RegRow (plainᵏ Γ κ) (emitᵗ t))} {s s′ LP LI}
         → n < s → n + n < s′
         → Pointwise (λ l l′ → guardOf regP l ≡ guardOf regI l′) LP LI
         → Pointwise (λ l l′ → SameAt s s′ (LiveSource.source l) (LiveSource.source l′)) LP LI
         → Pointwise (λ l l′ → guardOf (dropSource s regP) l ≡ guardOf (dropSource s′ regI) l′) LP LI
pw-agree na na′ [] [] = []
pw-agree {regP = regP} {regI = regI} {s} {s′} na na′ (_∷_ {l} {l′} g gs) ((f , b) ∷ ls) = step ∷ pw-agree {regP = regP} {regI = regI} {s} {s′} na na′ gs ls
  where
    step : guardOf (dropSource s regP) l ≡ guardOf (dropSource s′ regI) l′
    step with sameSource (LiveSource.source l) s in e
    ... | true  = trans (guard-gone regP l na (same-eq e)) (sym (guard-gone regI l′ na′ (f (same-eq e))))
    ... | false = trans (guard-other regP l e)
                    (trans g (sym (guard-other regI l′ (sameSource-no (λ eq′ → neq-of e (b eq′))))))

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

  -- the impl's hot rows sit at slots, under any minted source
  mach-lt : ∀ {s′} (i : Fin n) → n + n < s′ → sameSource s′ (toℕ (i ↑ˡ n)) ≡ false
  mach-lt i na′ = sameSource-lt (<-trans (subst (_< n + n) (sym (toℕ-↑ˡ i n)) (<-≤-trans (toℕ<n i) (m≤m+n n n))) na′)

  keep₂ : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {rs rs′}
            {r : RegRow Γ t} {r′ : RegRow (plainᵏ Γ κ) (emitᵗ t)} s s′
        → RegRel κ π NP NI LP LI (r ∷ dropSource s rs) (r′ ∷ dropSource s′ rs′)
        → sameSource s (regSource (proj₁ (proj₂ r))) ≡ false → sameSource s′ (regSource (proj₁ (proj₂ r′))) ≡ false
        → RegRel κ π NP NI LP LI (dropSource s (r ∷ rs)) (dropSource s′ (r′ ∷ rs′))
  keep₂ {rs = rs} {rs′ = rs′} {r = r} {r′ = r′} s s′ x e e′ =
    subst₂ (RegRel κ _ _ _ _ _) (sym (drop-keep s r rs e)) (sym (drop-keep s′ r′ rs′ e′)) x

  skip₂ : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {rs rs′}
            {r : RegRow Γ t} {r′ : RegRow (plainᵏ Γ κ) (emitᵗ t)} s s′
        → RegRel κ π NP NI LP LI (dropSource s rs) (dropSource s′ rs′)
        → sameSource s (regSource (proj₁ (proj₂ r))) ≡ true → sameSource s′ (regSource (proj₁ (proj₂ r′))) ≡ true
        → RegRel κ π NP NI LP LI (dropSource s (r ∷ rs)) (dropSource s′ (r′ ∷ rs′))
  skip₂ {rs = rs} {rs′ = rs′} {r = r} {r′ = r′} s s′ x e e′ =
    subst₂ (RegRel κ _ _ _ _ _) (sym (drop-skip s r rs e)) (sym (drop-skip s′ r′ rs′ e′)) x

  -- the impl's own row stays
  keepI : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {rs rs′}
            {r′ : RegRow (plainᵏ Γ κ) (emitᵗ t)} s′
        → RegRel κ π NP NI LP LI rs (r′ ∷ dropSource s′ rs′)
        → sameSource s′ (regSource (proj₁ (proj₂ r′))) ≡ false
        → RegRel κ π NP NI LP LI rs (dropSource s′ (r′ ∷ rs′))
  keepI {rs′ = rs′} {r′ = r′} s′ x e′ = subst (RegRel κ _ _ _ _ _ _) (sym (drop-keep s′ r′ rs′ e′)) x

  -- an arrival's pair of sources is a row's pair of sources or neither
  arr-dec : ∀ {s s′ src src′ u u′ x x′} → ArrRel s s′ u u′ src src′ x x′
          → (sameSource s src ≡ true × sameSource s′ src′ ≡ true) ⊎ (sameSource s src ≡ false × sameSource s′ src′ ≡ false)
  arr-dec {s} {s′} {src} {src′} (f , b) with sameSource s src in e
  ... | true  = inj₁ (refl , same-yes (proj₁ (f (same-eq e))))
  ... | false = inj₂ (refl , sameSource-no (λ eq′ → neq-of e (b eq′)))

  -- the registrations at the arrival's source go from both registries together
  drop-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {rs rs′ s s′ u u′} → n < s → n + n < s′
            → (q : RegRel κ π {t} NP NI LP LI rs rs′) → ArrRows κ π NP NI LP LI q s s′ u u′
            → RegRel κ π NP NI LP LI (dropSource s rs) (dropSource s′ rs′)
  drop-rows na na′ [] _ = []
  drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ (_∷_ {rs = rs₀} {rs′ = rs₀′} rr@(read~ {i = i} hk pr refl) q) ars =
    keep₂ {rs = rs₀} {rs′ = rs₀′} s s′ (rr ∷ drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ q ars)
               (sameSource-lt (<-trans (toℕ<n i) na))
               (sameSource-lt (<-trans (subst (_< n + n) (sym (toℕ-↑ʳ n i)) (+-monoʳ-< n (toℕ<n i))) na′))
  drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ (_∷_ {rs = rs₀} {rs′ = rs₀′} rr@(cold~ sp ib pr refl) q) (ar , ars) with arr-dec ar
  ... | inj₁ (e , e′) = skip₂ {rs = rs₀} {rs′ = rs₀′} s s′ (drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ q ars) e e′
  ... | inj₂ (e , e′) = keep₂ {rs = rs₀} {rs′ = rs₀′} s s′ (rr ∷ drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ q ars) e e′
  drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ (_∷_ {rs = rs₀} {rs′ = rs₀′} rr@(defer~ sp pi lnP lnI pr refl) q) (ar , ars) with arr-dec ar
  ... | inj₁ (e , e′) = skip₂ {rs = rs₀} {rs′ = rs₀′} s s′ (drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ q ars) e e′
  ... | inj₂ (e , e′) = keep₂ {rs = rs₀} {rs′ = rs₀′} s s′ (rr ∷ drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ q ars) e e′
  drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ (mach {rs = rs₀} {rs′ = rs₀′} m@(hot~ {i = i} hot ib refl) q) ars =
    keepI {rs = dropSource s rs₀} {rs′ = rs₀′} s′ (mach m (drop-rows {s = s} {s′ = s′} {u = u} {u′ = u′} na na′ q ars))
             (mach-lt i na′)

------------------------------------------------------------------
-- The store
------------------------------------------------------------------

-- a close latches its own arrival's source
close-hit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (a : Arrival Γ) (st : EvalSt e) {k}
          → Arrival.source a ≡ k → memberSource k (EvalSt.completedSources (cascadeClose a st)) ≡ true
close-hit a st {k} refl = cong (_∨ any (sameSource k) (EvalSt.completedSources st)) (same-refl k)

-- a latch list grown by another source reads one apart from it as before
member-no : ∀ {m k} (xs : List Source) → m ≢ k → memberSource m (k ∷ xs) ≡ memberSource m xs
member-no {m} xs ne = cong (_∨ any (sameSource m) xs) (sameSource-no ne)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a drop keeps every surviving block's inner its own row's
  owned-drop : ∀ {t} s {K : List (RegRow (plainᵏ Γ κ) (emitᵗ t))} → Owned {Γ = Γ} κ K → Owned {Γ = Γ} κ (dropSource s K)
  owned-drop s o = all-drop s (mapᵃ (λ f u {j} b → all-drop s (f u {j} b)) o)

  finish-go : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {s s′ u u′}
            → (S : Store κ sP stP sI stI) → n < s → n + n < s′ → Arr S s s′ u u′
            → Store κ (record sP { live = sweepL (guardOf (dropSource s (EvalSt.registry stP))) (Sched.live sP) })
                      (record stP { registry = dropSource s (EvalSt.registry stP) })
                      (record sI { live = sweepL (guardOf (dropSource s′ (EvalSt.registry stI))) (Sched.live sI) })
                      (record stI { registry = dropSource s′ (EvalSt.registry stI) })
  finish-go {t} {stP = stP} {stI = stI} {s} {s′} S na na′ ar = record
    { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
    ; sources = sweepL-pw sources pw
    ; numbers = sweepL-pw numbers pw
    ; distinct = unique-sweep _ LiveSource.source (proj₁ distinct) , unique-sweep _ LiveSource.source (proj₂ distinct)
    ; sync = sync-sweep sync pw
    ; rows = regrel-sweep κ {rs = dropSource s (EvalSt.registry stP)} {rs′ = dropSource s′ (EvalSt.registry stI)}
                            {K = dropSource s (EvalSt.registry stP)} {K′ = dropSource s′ (EvalSt.registry stI)}
                            pw (λ m → m) (drop-rows κ {s = s} {s′ = s′} na na′ rows (Arr.rows ar))
    ; latches = latches
    ; bounded = all-sweep _ LiveSource.source (proj₁ bounded) , all-sweep _ LiveSource.source (proj₂ bounded)
    ; swept = sweepL-pw pw pw
    ; uncut = all-drop s (proj₁ uncut) , all-drop s′ (proj₂ uncut)
    ; above = all-drop s (proj₁ above) , all-drop s′ (proj₂ above)
    ; owned = owned-drop {t = t} s′ {K = EvalSt.registry stI} owned
    ; ruleP = sub-rule (drop-sub s (EvalSt.registry stP)) ≤-refl ruleP
    ; ruleI = sub-rule (drop-sub s′ (EvalSt.registry stI)) ≤-refl ruleI
    ; census = λ i h → census-drop s′ (EvalSt.registry stI) (mach-lt {Γ = Γ} κ i na′)
                         (sameSource-lt (<-trans (subst (_< n + n) (sym (toℕ-↑ʳ n i)) (+-monoʳ-< n (toℕ<n i))) na′))
                         (census i h)
    }
    where
      open Store S
      pw = pw-agree {regP = EvalSt.registry stP} {regI = EvalSt.registry stI} {s} {s′} na na′ swept (Arr.lists ar)

-- THE END OF A LAST ARRIVAL, the drop and the sweep
finish-store : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                 {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {a a′}
  → (s : Store κ sP stP sI stI) → n < Arrival.source a → n + n < Arrival.source a′
  → Arrival.isLast a ≡ true → Arrival.isLast a′ ≡ true
  → Arr s (Arrival.source a) (Arrival.source a′) (arrTy a) (arrTy a′)
  → Store κ (proj₁ (cascadeFinish a sP stP)) (proj₂ (cascadeFinish a sP stP))
            (proj₁ (cascadeFinish a′ sI stI)) (proj₂ (cascadeFinish a′ sI stI))
finish-store {κ = κ} {sP = sP} {stP = stP} {sI = sI} {stI = stI} {a = a} {a′ = a′} S na na′ ll ll′ ar
  with Arrival.isLast a | Arrival.isLast a′ | ll | ll′
... | .true | .true | refl | refl =
  subst₂ (λ x y → Store κ x (record stP { registry = dropSource (arrSource a) (EvalSt.registry stP) })
                          y (record stI { registry = dropSource (arrSource a′) (EvalSt.registry stI) }))
    (cong (λ L → record sP { live = L }) (sym (sweep-eq (dropSource (arrSource a) (EvalSt.registry stP)) (Sched.live sP))))
    (cong (λ L → record sI { live = L }) (sym (sweep-eq (dropSource (arrSource a′) (EvalSt.registry stI)) (Sched.live sI))))
    (finish-go κ S na na′ ar)

------------------------------------------------------------------
-- A hot script's end
------------------------------------------------------------------

-- a filter run twice is run once
sweepL-idem : ∀ {A : Set} (p : A → Bool) xs → sweepL p (sweepL p xs) ≡ sweepL p xs
sweepL-idem p []       = refl
sweepL-idem p (x ∷ xs) with p x in e
... | true  rewrite e = cong (x ∷_) (sweepL-idem p xs)
... | false = sweepL-idem p xs

T-true : ∀ {b} → T b → b ≡ true
T-true {true} _ = refl

module _ {n} {Γ : Ctx n} {t} where

  -- a slot's live entry is never swept
  guard-low : ∀ (K : List (RegRow Γ t)) (l : LiveSource Γ) → LiveSource.source l < n → guardOf K l ≡ true
  guard-low K l lt = cong (_∨ any (onSrc (LiveSource.source l)) K) (T-true (<⇒<ᵇ lt))

  -- the impl's two drops, as one
  drop₂ : Source → Source → List (RegRow Γ t) → List (RegRow Γ t)
  drop₂ y₁ y₂ K = dropSource y₂ (dropSource y₁ K)

  drop₂-keep : ∀ y₁ y₂ (r : RegRow Γ t) K
             → sameSource y₁ (regSource (proj₁ (proj₂ r))) ≡ false → sameSource y₂ (regSource (proj₁ (proj₂ r))) ≡ false
             → drop₂ y₁ y₂ (r ∷ K) ≡ r ∷ drop₂ y₁ y₂ K
  drop₂-keep y₁ y₂ r K e₁ e₂ = trans (cong (dropSource y₂) (drop-keep y₁ r K e₁)) (drop-keep y₂ r (dropSource y₁ K) e₂)

  drop₂-skip₁ : ∀ y₁ y₂ (r : RegRow Γ t) K → sameSource y₁ (regSource (proj₁ (proj₂ r))) ≡ true
              → drop₂ y₁ y₂ (r ∷ K) ≡ drop₂ y₁ y₂ K
  drop₂-skip₁ y₁ y₂ r K e₁ = cong (dropSource y₂) (drop-skip y₁ r K e₁)

  drop₂-skip₂ : ∀ y₁ y₂ (r : RegRow Γ t) K
              → sameSource y₁ (regSource (proj₁ (proj₂ r))) ≡ false → sameSource y₂ (regSource (proj₁ (proj₂ r))) ≡ true
              → drop₂ y₁ y₂ (r ∷ K) ≡ drop₂ y₁ y₂ K
  drop₂-skip₂ y₁ y₂ r K e₁ e₂ = trans (cong (dropSource y₂) (drop-keep y₁ r K e₁)) (drop-skip y₂ r (dropSource y₁ K) e₂)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a partnered pair of sources is numbered as its live entries are
  pair-num : ∀ {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {src src′ u u′}
           → Pointwise (λ l l′ → SrcNum κ (LiveSource.source l) (LiveSource.source l′)) LP LI
           → SrcPair κ LP LI src src′ u u′ → SrcNum κ src src′
  pair-num (x ∷ _)  sp-here       = x
  pair-num (_ ∷ xs) (sp-there sp) = pair-num xs sp

  private
    -- a raw slot's number, and a stamped one's
    raw< : (j : Fin n) → toℕ (j ↑ˡ n) < n + n
    raw< j = subst (_< n + n) (sym (toℕ-↑ˡ j n)) (<-≤-trans (toℕ<n j) (m≤m+n n n))

    raw≢ : (i j : Fin n) → toℕ (j ↑ˡ n) ≢ toℕ (n ↑ʳ i)
    raw≢ i j eq = <⇒≢ (<-≤-trans (toℕ<n j) (m≤m+n n (toℕ i))) (trans (sym (toℕ-↑ˡ j n)) (trans eq (toℕ-↑ʳ n i)))

    stamped≢ : (i j : Fin n) → toℕ i ≢ toℕ j → toℕ (n ↑ʳ i) ≢ toℕ (n ↑ʳ j)
    stamped≢ i j ne eq = ne (+-cancelˡ-≡ n (toℕ i) (toℕ j) (trans (sym (toℕ-↑ʳ n i)) (trans eq (toℕ-↑ʳ n j))))

    stamped≡ : (i j : Fin n) → toℕ j ≡ toℕ i → toℕ (n ↑ʳ i) ≡ toℕ (n ↑ʳ j)
    stamped≡ i j eq = trans (toℕ-↑ʳ n i) (trans (cong (n +_) (sym eq)) (sym (toℕ-↑ʳ n j)))

    raw≡ : (i j : Fin n) → toℕ j ≡ toℕ i → toℕ (i ↑ˡ n) ≡ toℕ (j ↑ˡ n)
    raw≡ i j eq = trans (toℕ-↑ˡ i n) (trans (sym eq) (sym (toℕ-↑ˡ j n)))

    raw≢′ : (i j : Fin n) → toℕ j ≢ toℕ i → toℕ (i ↑ˡ n) ≢ toℕ (j ↑ˡ n)
    raw≢′ i j ne eq = ne (trans (sym (toℕ-↑ˡ j n)) (trans (sym eq) (toℕ-↑ˡ i n)))

    -- a stamped slot's number sits above every raw one
    raw-stamped : (i j : Fin n) → toℕ (i ↑ˡ n) ≢ toℕ (n ↑ʳ j)
    raw-stamped i j = raw≢ j i

    stamped< : (i : Fin n) → toℕ (n ↑ʳ i) < n + n
    stamped< i = subst (_< n + n) (sym (toℕ-↑ʳ n i)) (+-monoʳ-< n (toℕ<n i))

  -- A HOT SLOT'S DROPS TAKE THE SAME ROWS FROM BOTH REGISTRIES: the plain
  -- run drops the slot's, the impl its stamped slot's and then its raw
  -- slot's, and a pair of rows is at the slot on both sides or on neither
  hot-rows : ∀ {t π NP NI} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {rs rs′} (i : Fin n)
           → Pointwise (λ l l′ → SrcNum κ (LiveSource.source l) (LiveSource.source l′)) LP LI
           → RegRel κ π {t} NP NI LP LI rs rs′
           → RegRel κ π NP NI LP LI (dropSource (toℕ i) rs) (drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) rs′)
  hot-rows i nums [] = []
  hot-rows i nums (_∷_ {r = r} {r′ = r′} {rs = rs₀} {rs′ = rs₀′} rr@(read~ {i = j} _ _ refl) q) with toℕ j ≟ toℕ i
  ... | yes eq = subst₂ (RegRel κ _ _ _ _ _) (sym (drop-skip (toℕ i) r rs₀ (same-yes (sym eq))))
                        (sym (drop₂-skip₁ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′ (same-yes (stamped≡ i j eq))))
                        (hot-rows i nums q)
  ... | no ne  = subst₂ (RegRel κ _ _ _ _ _) (sym (drop-keep (toℕ i) r rs₀ (sameSource-no (λ e → ne (sym e)))))
                        (sym (drop₂-keep (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                               (sameSource-no (stamped≢ i j (λ e → ne (sym e)))) (sameSource-no (raw-stamped i j))))
                        (rr ∷ hot-rows i nums q)
  hot-rows i nums (_∷_ {r = r} {r′ = r′} {rs = rs₀} {rs′ = rs₀′} rr@(cold~ sp _ _ refl) q) = at (pair-num nums sp) refl refl
    where
      at : ∀ {x x′} → SrcNum κ x x′ → regSource (proj₁ (proj₂ r)) ≡ x → regSource (proj₁ (proj₂ r′)) ≡ x′
         → RegRel κ _ _ _ _ _ (dropSource (toℕ i) (r ∷ rs₀)) (drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) (r′ ∷ rs₀′))
      at (slot~ j _) e e′ with toℕ j ≟ toℕ i
      ... | yes eq = subst₂ (RegRel κ _ _ _ _ _) (sym (drop-skip (toℕ i) r rs₀ (same-yes (trans (sym eq) (sym e)))))
                            (sym (drop₂-skip₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                                   (sameSource-no (λ x → raw≢ i j (trans (sym e′) (sym x))))
                                   (same-yes (trans (raw≡ i j eq) (sym e′)))))
                            (hot-rows i nums q)
      ... | no ne  = subst₂ (RegRel κ _ _ _ _ _) (sym (drop-keep (toℕ i) r rs₀ (sameSource-no (λ x → ne (sym (trans x e))))))
                            (sym (drop₂-keep (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                                   (sameSource-no (λ x → raw≢ i j (trans (sym e′) (sym x))))
                                   (sameSource-no (λ x → raw≢′ i j ne (trans x e′)))))
                            (rr ∷ hot-rows i nums q)
      at (dyn~ p p′) e e′ =
        subst₂ (RegRel κ _ _ _ _ _) (sym (drop-keep (toℕ i) r rs₀ (sameSource-no (λ x → <⇒≢ (<-trans (toℕ<n i) p) (trans x e)))))
               (sym (drop₂-keep (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                      (sameSource-no (λ x → <⇒≢ (<-trans (stamped< i) p′) (trans x e′)))
                      (sameSource-no (λ x → <⇒≢ (<-trans (raw< i) p′) (trans x e′)))))
               (rr ∷ hot-rows i nums q)
  hot-rows i nums (_∷_ {r = r} {r′ = r′} {rs = rs₀} {rs′ = rs₀′} rr@(defer~ sp _ _ _ _ refl) q) = at (pair-num nums sp) refl refl
    where
      at : ∀ {x x′} → SrcNum κ x x′ → regSource (proj₁ (proj₂ r)) ≡ x → regSource (proj₁ (proj₂ r′)) ≡ x′
         → RegRel κ _ _ _ _ _ (dropSource (toℕ i) (r ∷ rs₀)) (drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) (r′ ∷ rs₀′))
      at (slot~ j _) e e′ with toℕ j ≟ toℕ i
      ... | yes eq = subst₂ (RegRel κ _ _ _ _ _) (sym (drop-skip (toℕ i) r rs₀ (same-yes (trans (sym eq) (sym e)))))
                            (sym (drop₂-skip₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                                   (sameSource-no (λ x → raw≢ i j (trans (sym e′) (sym x))))
                                   (same-yes (trans (raw≡ i j eq) (sym e′)))))
                            (hot-rows i nums q)
      ... | no ne  = subst₂ (RegRel κ _ _ _ _ _) (sym (drop-keep (toℕ i) r rs₀ (sameSource-no (λ x → ne (sym (trans x e))))))
                            (sym (drop₂-keep (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                                   (sameSource-no (λ x → raw≢ i j (trans (sym e′) (sym x))))
                                   (sameSource-no (λ x → raw≢′ i j ne (trans x e′)))))
                            (rr ∷ hot-rows i nums q)
      at (dyn~ p p′) e e′ =
        subst₂ (RegRel κ _ _ _ _ _) (sym (drop-keep (toℕ i) r rs₀ (sameSource-no (λ x → <⇒≢ (<-trans (toℕ<n i) p) (trans x e)))))
               (sym (drop₂-keep (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                      (sameSource-no (λ x → <⇒≢ (<-trans (stamped< i) p′) (trans x e′)))
                      (sameSource-no (λ x → <⇒≢ (<-trans (raw< i) p′) (trans x e′)))))
               (rr ∷ hot-rows i nums q)
  hot-rows i nums (mach {rs = rs₀} {r′ = r′} {rs′ = rs₀′} m@(hot~ {i = j} _ _ refl) q) with toℕ j ≟ toℕ i
  ... | yes eq = subst (RegRel κ _ _ _ _ _ _)
                       (sym (drop₂-skip₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                              (sameSource-no (λ x → raw≢ i j (sym x))) (same-yes (raw≡ i j eq))))
                       (hot-rows i nums q)
  ... | no ne  = subst (RegRel κ _ _ _ _ _ _)
                       (sym (drop₂-keep (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) r′ rs₀′
                              (sameSource-no (λ x → raw≢ i j (sym x))) (sameSource-no (raw≢′ i j ne))))
                       (mach m (hot-rows i nums q))

  -- AND THE GUARDS STILL AGREE, after the impl's first drop and after its
  -- second: a slot's entry is kept on both sides, and a minted one's guard
  -- reads no slot's rows
  hot-guards : ∀ {t} {regP : List (RegRow Γ t)} {regI : List (RegRow (plainᵏ Γ κ) (emitᵗ t))} {LP LI} (i : Fin n)
             → Pointwise (λ l l′ → SrcNum κ (LiveSource.source l) (LiveSource.source l′)) LP LI
             → Pointwise (λ l l′ → guardOf regP l ≡ guardOf regI l′) LP LI
             → Pointwise (λ l l′ → guardOf (dropSource (toℕ i) regP) l ≡ guardOf (dropSource (toℕ (n ↑ʳ i)) regI) l′
                                 × guardOf (dropSource (toℕ i) regP) l ≡ guardOf (drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) regI) l′) LP LI
  hot-guards i [] [] = []
  hot-guards {regP = regP} {regI} i (_∷_ {l} {l′} x xs) (g ∷ gs) = at x refl refl ∷ hot-guards {regP = regP} {regI} i xs gs
    where
      K₁ = dropSource (toℕ (n ↑ʳ i)) regI
      at : ∀ {s s′} → SrcNum κ s s′ → LiveSource.source l ≡ s → LiveSource.source l′ ≡ s′
         → guardOf (dropSource (toℕ i) regP) l ≡ guardOf K₁ l′
         × guardOf (dropSource (toℕ i) regP) l ≡ guardOf (dropSource (toℕ (i ↑ˡ n)) K₁) l′
      at (slot~ j _) e e′ =
          trans (guard-low (dropSource (toℕ i) regP) l (subst (_< n) (sym e) (toℕ<n j))) (sym (guard-low K₁ l′ (subst (_< n + n) (sym e′) (raw< j))))
        , trans (guard-low (dropSource (toℕ i) regP) l (subst (_< n) (sym e) (toℕ<n j)))
                (sym (guard-low (dropSource (toℕ (i ↑ˡ n)) K₁) l′ (subst (_< n + n) (sym e′) (raw< j))))
      at (dyn~ p p′) e e′ =
          trans GP (trans g (sym G₁))
        , trans GP (trans g (sym (trans (guard-other K₁ l′ (sameSource-lt (subst (toℕ (i ↑ˡ n) <_) (sym e′) (<-trans (raw< i) p′)))) G₁)))
        where
          GP = guard-other regP l (sameSource-lt (subst (toℕ i <_) (sym e) (<-trans (toℕ<n i) p)))
          G₁ = guard-other regI l′ (sameSource-lt (subst (toℕ (n ↑ʳ i) <_) (sym e′) (<-trans (stamped< i) p′)))

  -- the store once the plain run drops a slot's rows and the impl drops
  -- its stamped slot's and then its raw slot's, each side sweeping after
  -- each of its drops
  hot-go : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
             {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
         → (S : Store κ sP stP sI stI) (i : Fin n) → memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ true
         → Store κ (record sP { live = sweepL (guardOf (dropSource (toℕ i) (EvalSt.registry stP)))
                                          (sweepL (guardOf (dropSource (toℕ i) (EvalSt.registry stP))) (Sched.live sP)) })
                   (record stP { registry = dropSource (toℕ i) (EvalSt.registry stP) })
                   (record sI { live = sweepL (guardOf (drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) (EvalSt.registry stI)))
                                          (sweepL (guardOf (dropSource (toℕ (n ↑ʳ i)) (EvalSt.registry stI))) (Sched.live sI)) })
                   (record stI { registry = drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) (EvalSt.registry stI) })
  hot-go {t} {stP = stP} {stI = stI} S i dn = record
    { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
    ; sources = sweepL-pw (sweepL-pw sources A) A′
    ; numbers = sweepL-pw (sweepL-pw numbers A) A′
    ; distinct = unique-sweep gP LiveSource.source (unique-sweep gP LiveSource.source (proj₁ distinct))
               , unique-sweep g₂ LiveSource.source (unique-sweep g₁ LiveSource.source (proj₂ distinct))
    ; sync = sync-sweep (sync-sweep sync A) A′
    ; rows = regrel-sweep κ {K = KP} {K′ = K₂} A′ (λ m → m)
               (regrel-sweep κ {K = KP} {K′ = K₁} A (λ m → m) (hot-rows i numbers rows))
    ; latches = latches
    ; bounded = all-sweep gP LiveSource.source (all-sweep gP LiveSource.source (proj₁ bounded))
              , all-sweep g₂ LiveSource.source (all-sweep g₁ LiveSource.source (proj₂ bounded))
    ; swept = sweepL-pw A′ A′
    ; uncut = all-drop (toℕ i) (proj₁ uncut) , all-drop (toℕ (i ↑ˡ n)) (all-drop (toℕ (n ↑ʳ i)) (proj₂ uncut))
    ; above = all-drop (toℕ i) (proj₁ above) , all-drop (toℕ (i ↑ˡ n)) (all-drop (toℕ (n ↑ʳ i)) (proj₂ above))
    ; census = hot-census
    ; owned = owned-drop {Γ = Γ} κ {t = t} (toℕ (i ↑ˡ n)) {K = dropSource (toℕ (n ↑ʳ i)) (EvalSt.registry stI)} (owned-drop {Γ = Γ} κ {t = t} (toℕ (n ↑ʳ i)) {K = EvalSt.registry stI} owned)
    ; ruleP = sub-rule (drop-sub (toℕ i) (EvalSt.registry stP)) ≤-refl ruleP
    ; ruleI = sub-rule (λ r∈ → drop-sub (toℕ (n ↑ʳ i)) (EvalSt.registry stI) (drop-sub (toℕ (i ↑ˡ n)) (dropSource (toℕ (n ↑ʳ i)) (EvalSt.registry stI)) r∈)) ≤-refl ruleI
    }
    where
      open Store S
      KP = dropSource (toℕ i) (EvalSt.registry stP)
      K₁ = dropSource (toℕ (n ↑ʳ i)) (EvalSt.registry stI)
      K₂ = drop₂ (toℕ (n ↑ʳ i)) (toℕ (i ↑ˡ n)) (EvalSt.registry stI)
      gP = guardOf KP
      g₁ = guardOf K₁
      g₂ = guardOf K₂
      G  = hot-guards {regP = EvalSt.registry stP} {regI = EvalSt.registry stI} i numbers swept
      A  = pw-map proj₁ G
      A′ = sweepL-pw (pw-map proj₂ G) A

      -- the slot's own share and raw slot are emptied, every other kept
      hot-census : ∀ j → lookup κ j ≡ hotᵏ → Census (toℕ (j ↑ˡ n)) (toℕ (n ↑ʳ j)) K₂
                                                (memberSource (toℕ (n ↑ʳ j)) (EvalSt.connectedShares stI))
                                                (memberSource (toℕ (j ↑ˡ n)) (EvalSt.completedSources stI))
      hot-census j h with toℕ j ≟ toℕ i
      ... | yes eq = inj₂ ( subst (λ k → srcCount k K₂ ≡ 0) (raw≡ i j eq) (count-self (toℕ (i ↑ˡ n)) K₁)
                          , trans (count-drop (toℕ (i ↑ˡ n)) K₁ (sameSource-no (raw-stamped i j)))
                                  (subst (λ k → srcCount k K₁ ≡ 0) (stamped≡ i j eq) (count-self (toℕ (n ↑ʳ i)) (EvalSt.registry stI)))
                          , λ _ → subst (λ k → memberSource k (EvalSt.completedSources stI) ≡ true) (raw≡ i j eq) dn )
      ... | no ne  = census-drop (toℕ (i ↑ˡ n)) K₁ (sameSource-no (raw≢′ i j ne)) (sameSource-no (raw-stamped i j))
                       (census-drop (toℕ (n ↑ʳ i)) (EvalSt.registry stI) (sameSource-no (λ x → raw≢ i j (sym x)))
                          (sameSource-no (stamped≢ i j (λ x → ne (sym x)))) (census j h))

  -- A HOT SLOT'S END WITH NO RAW ROW: the plain run latches the slot and
  -- the impl the raw slot, and the share stays as it was, spent exactly
  -- if it connected
  hot-close : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
            → (S : Store κ sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
            → lookup κ i ≡ hotᵏ → Arrival.source a ≡ toℕ i → Arrival.source a′ ≡ toℕ (i ↑ˡ n)
            → (memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true
               → memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ true)
            → Store κ sP (cascadeClose a stP) sI (cascadeClose a′ stI)
  hot-close {stP = stP} {stI = stI} S {a} {a′} {i} hk e₁ e₂ cd = record
    { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
    ; sync = sync ; rows = rows ; bounded = bounded ; swept = swept ; uncut = uncut ; above = above
    ; latches = lat ; census = cen ; owned = owned ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI }
    where
      open Store S
      CP = EvalSt.completedSources stP
      CI = EvalSt.completedSources stI
      SI = EvalSt.connectedShares stI

      hitP : memberSource (toℕ i) (Arrival.source a ∷ CP) ≡ true
      hitP = close-hit a stP e₁

      hitI : memberSource (toℕ (i ↑ˡ n)) (Arrival.source a′ ∷ CI) ≡ true
      hitI = close-hit a′ stI e₂

      -- a share's number is no raw slot's
      shr : ∀ j → memberSource (toℕ (n ↑ʳ j)) (Arrival.source a′ ∷ CI) ≡ memberSource (toℕ (n ↑ʳ j)) CI
      shr j = member-no CI (subst (toℕ (n ↑ʳ j) ≢_) (sym e₂) (λ x → raw-stamped i j (sym x)))

      -- the share spent exactly if it connected, once the raw slot is latched
      spent : ∀ d c → (c ≡ true → d ≡ true) → d ∧ c ≡ true ∧ c
      spent d false _ = ∧-zeroʳ d
      spent d true  f = cong (_∧ true) (f refl)

      clash : hotᵏ ≢ sharedᵏ
      clash ()

      lat : LatchRel {Γ = Γ} κ (Arrival.source a ∷ CP) (EvalSt.connectedShares stP) (Arrival.source a′ ∷ CI) SI
      lat j with j ≟ᶠ i
      ... | yes refl =
            (λ _ → let _ , d = proj₁ (latches i) hk
                   in trans hitP (sym hitI)
                    , trans (shr i) (trans d (trans (spent _ _ cd) (cong (_∧ memberSource (toℕ (n ↑ʳ i)) SI) (sym hitI)))))
          , (λ sk → ⊥-elim (clash (trans (sym hk) sk)))
      ... | no ne =
            (λ h → let c , d = proj₁ (latches j) h
                   in trans skP (trans c (sym skR))
                    , trans (shr j) (trans d (cong (_∧ memberSource (toℕ (n ↑ʳ j)) SI) (sym skR))))
          , (λ sk → let c , d = proj₂ (latches j) sk in trans skP (trans c (sym (shr j))) , d)
        where
          ne′ : toℕ j ≢ toℕ i
          ne′ x = ne (toℕ-injective x)
          skP : memberSource (toℕ j) (Arrival.source a ∷ CP) ≡ memberSource (toℕ j) CP
          skP = member-no CP (subst (toℕ j ≢_) (sym e₁) ne′)
          skR : memberSource (toℕ (j ↑ˡ n)) (Arrival.source a′ ∷ CI) ≡ memberSource (toℕ (j ↑ˡ n)) CI
          skR = member-no CI (subst (toℕ (j ↑ˡ n) ≢_) (sym e₂) (λ x → raw≢′ i j ne′ (sym x)))

      cen : ∀ j → lookup κ j ≡ hotᵏ → Census (toℕ (j ↑ˡ n)) (toℕ (n ↑ʳ j)) (EvalSt.registry stI)
                                        (memberSource (toℕ (n ↑ʳ j)) SI) (memberSource (toℕ (j ↑ˡ n)) (Arrival.source a′ ∷ CI))
      cen j h with j ≟ᶠ i
      ... | yes refl = subst (Census (toℕ (i ↑ˡ n)) (toℕ (n ↑ʳ i)) (EvalSt.registry stI) (memberSource (toℕ (n ↑ʳ i)) SI)) (sym hitI)
                             (census-done {k₁ = toℕ (i ↑ˡ n)} {k₂ = toℕ (n ↑ʳ i)} {c = memberSource (toℕ (n ↑ʳ i)) SI}
                                          {d = memberSource (toℕ (i ↑ˡ n)) CI} {K = EvalSt.registry stI} (census i h))
      ... | no ne    = subst (Census (toℕ (j ↑ˡ n)) (toℕ (n ↑ʳ j)) (EvalSt.registry stI) (memberSource (toℕ (n ↑ʳ j)) SI))
                             (sym (member-no CI (subst (toℕ (j ↑ˡ n) ≢_) (sym e₂) (λ x → raw≢′ i j (λ y → ne (toℕ-injective y)) (sym x)))))
                             (census j h)

-- THE END OF A HOT LAST ARRIVAL: the share's registrations and the raw
-- slot's dropped on the impl side, the slot's on the plain side
hot-finish : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
               {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
  → (S : Store κ sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
  → Arrival.source a ≡ toℕ i → Arrival.source a′ ≡ toℕ (i ↑ˡ n)
  → Arrival.isLast a ≡ true → Arrival.isLast a′ ≡ true
  → memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ true
  → ∀ {emits}
  → Store κ (proj₁ (cascadeFinish a sP stP)) (proj₂ (cascadeFinish a sP stP))
      (proj₁ (cascadeFinish a′ (proj₁ (proj₂ (shareFinish (n ↑ʳ i) true (emits , sI , stI))))
                               (proj₂ (proj₂ (shareFinish (n ↑ʳ i) true (emits , sI , stI))))))
      (proj₂ (cascadeFinish a′ (proj₁ (proj₂ (shareFinish (n ↑ʳ i) true (emits , sI , stI))))
                               (proj₂ (proj₂ (shareFinish (n ↑ʳ i) true (emits , sI , stI))))))
hot-finish {n} κ {sP = sP} {stP = stP} {sI = sI} {stI = stI} S {a} {a′} {i} e₁ e₂ ll ll′ dn
  with Arrival.isLast a | Arrival.isLast a′ | ll | ll′
... | .true | .true | refl | refl =
  subst₂ (λ x y → Store κ (record sP { live = x }) (record stP { registry = dropSource (arrSource a) regP })
                          (record sI { live = y }) (record stI { registry = drop₂ (toℕ (n ↑ʳ i)) (arrSource a′) regI }))
    (trans (sweepL-idem (guardOf (dropSource (arrSource a) regP)) (Sched.live sP)) (sym (sweep-eq (dropSource (arrSource a) regP) (Sched.live sP))))
    (sym (trans (sweep-eq (drop₂ (toℕ (n ↑ʳ i)) (arrSource a′) regI) (sweepLive (dropSource (toℕ (n ↑ʳ i)) regI) (Sched.live sI)))
                (cong (sweepL (guardOf (drop₂ (toℕ (n ↑ʳ i)) (arrSource a′) regI))) (sweep-eq (dropSource (toℕ (n ↑ʳ i)) regI) (Sched.live sI)))))
    (subst₂ (λ x y → Store κ (record sP { live = sweepL (guardOf (dropSource x regP)) (sweepL (guardOf (dropSource x regP)) (Sched.live sP)) })
                             (record stP { registry = dropSource x regP })
                             (record sI { live = sweepL (guardOf (drop₂ (toℕ (n ↑ʳ i)) y regI)) (sweepL (guardOf (dropSource (toℕ (n ↑ʳ i)) regI)) (Sched.live sI)) })
                             (record stI { registry = drop₂ (toℕ (n ↑ʳ i)) y regI }))
            (sym e₁) (sym e₂) (hot-go κ S i dn))
  where
    regP = EvalSt.registry stP
    regI = EvalSt.registry stI

-- AND ONE WHOSE SHARE AND RAW SLOT HOLD NO ROW: the impl's drops take
-- nothing but the raw slot's, and that takes nothing either
hot-quiet : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
  → (S : Store κ sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
  → Arrival.source a ≡ toℕ i → Arrival.source a′ ≡ toℕ (i ↑ˡ n)
  → Arrival.isLast a ≡ true → Arrival.isLast a′ ≡ true
  → memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ true
  → srcCount (toℕ (i ↑ˡ n)) (EvalSt.registry stI) ≡ 0 → srcCount (toℕ (n ↑ʳ i)) (EvalSt.registry stI) ≡ 0
  → Store κ (proj₁ (cascadeFinish a sP stP)) (proj₂ (cascadeFinish a sP stP))
            (proj₁ (cascadeFinish a′ sI stI)) (proj₂ (cascadeFinish a′ sI stI))
hot-quiet {n} κ {sP = sP} {stP = stP} {sI = sI} {stI = stI} S {a} {a′} {i} e₁ e₂ ll ll′ dn z₁ z₂
  with Arrival.isLast a | Arrival.isLast a′ | ll | ll′
... | .true | .true | refl | refl =
  subst (λ x → Store κ (record sP { live = x }) (record stP { registry = dropSource (arrSource a) regP })
                       (record sI { live = sweepLive (dropSource (arrSource a′) regI) (Sched.live sI) })
                       (record stI { registry = dropSource (arrSource a′) regI }))
    (trans (sweepL-idem (guardOf (dropSource (arrSource a) regP)) (Sched.live sP)) (sym (sweep-eq (dropSource (arrSource a) regP) (Sched.live sP))))
    (subst₂ (λ x y → Store κ (record sP { live = sweepL (guardOf (dropSource x regP)) (sweepL (guardOf (dropSource x regP)) (Sched.live sP)) })
                             (record stP { registry = dropSource x regP })
                             (record sI { live = sweepLive (dropSource y regI) (Sched.live sI) })
                             (record stI { registry = dropSource y regI }))
            (sym e₁) (sym e₂)
       (subst (λ L → Store κ (record sP { live = sweepL (guardOf (dropSource (toℕ i) regP)) (sweepL (guardOf (dropSource (toℕ i) regP)) (Sched.live sP)) })
                             (record stP { registry = dropSource (toℕ i) regP })
                             (record sI { live = L }) (record stI { registry = dropSource raw regI }))
              live-eq
          (subst (λ K → Store κ (record sP { live = sweepL (guardOf (dropSource (toℕ i) regP)) (sweepL (guardOf (dropSource (toℕ i) regP)) (Sched.live sP)) })
                                (record stP { registry = dropSource (toℕ i) regP })
                                (record sI { live = sweepL (guardOf (dropSource raw K)) (sweepL (guardOf K) (Sched.live sI)) })
                                (record stI { registry = dropSource raw K }))
                 (drop-none (toℕ (n ↑ʳ i)) regI z₂) (hot-go κ S i dn))))
  where
    regP = EvalSt.registry stP
    regI = EvalSt.registry stI
    raw  = toℕ (i ↑ˡ n)
    live-eq : sweepL (guardOf (dropSource raw regI)) (sweepL (guardOf regI) (Sched.live sI)) ≡ sweepLive (dropSource raw regI) (Sched.live sI)
    live-eq = subst (λ K → sweepL (guardOf K) (sweepL (guardOf regI) (Sched.live sI)) ≡ sweepLive K (Sched.live sI))
                    (sym (drop-none raw regI z₁))
                    (trans (sweepL-idem (guardOf regI) (Sched.live sI)) (sym (sweep-eq regI (Sched.live sI))))
