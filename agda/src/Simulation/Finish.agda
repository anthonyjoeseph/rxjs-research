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

open import Data.Bool    using (Bool; true; false; T; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty   using (⊥-elim)
open import Data.Fin     using (Fin; _↑ˡ_; toℕ)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.List    using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (zero; suc; _+_; _<_; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; <ᵇ⇒<; <-asym; <-trans; <-≤-trans; +-monoʳ-<; m≤m+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Rx.Exp       using (Ctx; Closed)
open import Rx.Prim      using (Source)
open import Rx.Evaluator using (LiveSource; Arrival; Sched; EvalSt; RegRow; regSource; sameSource; dropSource; sweepLive; cascadeFinish; arrSource; arrTy)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Chains using (sameSource-lt; sameSource-no)
open import Simulation.Schedules using (Sync; ord)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import Simulation.Stores using (guardOf; SameAt; SrcPair; RowRel; MachRow; hot~; RegRel; []; _∷_; read~; cold~; defer~; mach; ArrRel; ArrRows; Store; Arr)
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

same-refl : ∀ x → sameSource x x ≡ true
same-refl zero    = refl
same-refl (suc x) = same-refl x

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

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  finish-go : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {s s′ u u′}
            → (S : Store κ sP stP sI stI) → n < s → n + n < s′ → Arr S s s′ u u′
            → Store κ (record sP { live = sweepL (guardOf (dropSource s (EvalSt.registry stP))) (Sched.live sP) })
                      (record stP { registry = dropSource s (EvalSt.registry stP) })
                      (record sI { live = sweepL (guardOf (dropSource s′ (EvalSt.registry stI))) (Sched.live sI) })
                      (record stI { registry = dropSource s′ (EvalSt.registry stI) })
  finish-go {stP = stP} {stI = stI} {s} {s′} S na na′ ar = record
    { π = π ; π-keys = π-keys ; π-vals = π-vals
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
