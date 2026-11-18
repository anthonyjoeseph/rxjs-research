{-# OPTIONS --guardedness #-}

-- TRUNCATION ABSORBS THROUGH AN OPERATOR: an operator's rows over a
-- truncated input, truncated, are its rows over the raw input,
-- truncated.  So a stack of nodes is read with ONE truncation, at its
-- top, and a plumbing gadget's meaning is its operators composed over
-- raw rows (`simultaneous.FlatEach` is the first such).
--
-- Both directions move a row's derivation, never decide anything: a row
-- the raw input does not reach waits on infinitely many rows that the
-- operator shows before every row past it.  That holds for `takeWhile`
-- (`TakeAbsorb`), whose conditions read only rows before a reached one.
--
-- It fails for `scan` (`ScanRefuted`): a scanned value exists only
-- through the finite chain of values before it, so an input whose values
-- have no first shows none of them raw, and its end, reached raw, is
-- gone once truncated first.  On a well-founded input it holds
-- classically, but a constructive proof must produce each earlier
-- value's chain, which needs the input's values enumerated: a listing.
-- So a scan over a joiner whose lanes run outside their values keeps
-- the truncation between them.
module simultaneous.Absorb where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; ix; last; inside; _⊕_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; Unpinned; Dep; PDep; Reach; Few; Truncate; _≺_; _≼_;
  module TakeWhile)
open import denotation.Laws.Modulus using (≺-trans; ≺-≼-≺; ≼-≺-≺; ≺→≼; ≼-refl; ≺-ext; reach-few; reach-via)
open import denotation.Laws.Worlds using (⊑-≼; inside-⊑)
open import adequacy.SubOne using (dep-un; below-or-under)

open TakeWhile using (TakeT; Failed; pass; fail; stop; step; tend; left)

------------------------------------------------------------------------
-- Reaching, read off a row reached

module Reached {A : Set} (t : EmissionSet A) where

  -- Below a row with few before it, every row is reached.
  few-down : ∀ {q k} → Few t q → k ≼ q → ∀ {e} → Reach t k e
  few-down {q} {k} (ks , h) kq = ks , λ {j} x jk _ → h x (≺-≼-≺ {j} {k} {q} jk kq)

  few-of : ∀ {q e} → Truncate t q e → Unpinned e → Few t q
  few-of (_ , R) u = reach-few (dep-un u) R

  -- A reached pin has few before its connect.
  pin-few : ∀ {y r} → Reach t y (pin r) → T (inside r y) → Few t r
  pin-few {y} {r} (ks , h) i = ks , λ {j} x jr → h x (≺-≼-≺ {j} {r} {y} jr (⊑-≼ (inside-⊑ r y i))) (λ _ → inj₁ jr)

------------------------------------------------------------------------
-- takeWhile

module TakeAbsorb {A : Set} (incl : Bool) (keep : A → Bool) (t : EmissionSet A)
  (flat : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥)
  (pin-in : ∀ {j r} → t j (pin r) → T (inside r j)) where

  open Reached t

  τ : EmissionSet A
  τ = Truncate t

  Tk : EmissionSet A → EmissionSet A
  Tk = TakeT incl keep

  Fd : EmissionSet A → Pos → Set
  Fd = Failed incl keep

  fd-down : ∀ {q} → Few t q → Fd t q → Fd τ q
  fd-down {q} F (v , a , x , nk , lt) = v , a , (x , few-down {q} {v} F (≺→≼ {v} {q} lt) {out a}) , nk , lt

  fd-up : ∀ {q} → Fd τ q → Fd t q
  fd-up (v , a , x , nk , lt) = v , a , proj₁ x , nk , lt

  fd-≼ : ∀ {j q} → Fd t j → j ≼ q → Fd t q
  fd-≼ {j} {q} (v , a , x , nk , lt) jq = v , a , x , nk , ≺-≼-≺ {v} {j} {q} lt jq

  -- A row over the truncated input is a row over the raw one.
  down : ∀ {y e} → Tk τ y e → Tk t y e
  down (pass x k nf)   = pass (proj₁ x) k (λ g → nf (fd-down (few-of x tt) g))
  down (fail x k nf i) = fail (proj₁ x) k (λ g → nf (fd-down (few-of x tt) g)) i
  down (stop x k nf)   = stop (proj₁ x) k (λ g → nf (fd-down (few-of x tt) g))
  down (step x nf)     = step (proj₁ x) (λ g → nf (fd-down (few-of x tt) g))
  down (tend x nf)     = tend (proj₁ x) (λ g → nf (fd-down (few-of x tt) g))
  down (left {q} {r} x nf i) = left (proj₁ x) (λ g → nf (fd-down (pin-few {q} {r} (proj₂ x) i) g)) i

  -- A row's source.
  srcP : ∀ {k e} → Tk t k e → Pos
  srcP (pass {q} _ _ _)   = q
  srcP (fail {q} _ _ _ _) = q
  srcP (stop {q} _ _ _)   = q
  srcP (step {q} _ _)     = q
  srcP (tend {q} _ _)     = q
  srcP (left {q} _ _ _)   = q

  srcE : ∀ {k e} → Tk t k e → Ev A
  srcE (pass {a = a} _ _ _)   = out a
  srcE (fail {a = a} _ _ _ _) = out a
  srcE (stop {a = a} _ _ _)   = out a
  srcE (step _ _)             = skip
  srcE (tend _ _)             = end
  srcE (left {r = r} _ _ _)   = pin r

  srcT : ∀ {k e} (z : Tk t k e) → t (srcP z) (srcE z)
  srcT (pass x _ _)   = x
  srcT (fail x _ _ _) = x
  srcT (stop x _ _)   = x
  srcT (step x _)     = x
  srcT (tend x _)     = x
  srcT (left x _ _)   = x

  src≼ : ∀ {k e} (z : Tk t k e) → srcP z ≼ k
  src≼ (pass {q} _ _ _)   = ≼-refl {q}
  src≼ (fail {q} _ _ _ _) = ≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q [])
  src≼ (stop {q} _ _ _)   = ≺→≼ {q} {q ⊕ [ last ]} (≺-ext q [])
  src≼ (step {q} _ _)     = ≼-refl {q}
  src≼ (tend {q} _ _)     = ≼-refl {q}
  src≼ (left {q} _ _ _)   = ≼-refl {q}

  -- A row over the raw input, its source reached, is a row over the
  -- truncated one.
  up : ∀ {k e} (z : Tk t k e) → Reach t (srcP z) (srcE z) → Tk τ k e
  up (pass x k nf)   R = pass (x , R) k (λ g → nf (fd-up g))
  up (fail x k nf i) R = fail (x , R) k (λ g → nf (fd-up g)) i
  up (stop x k nf)   R = stop (x , R) k (λ g → nf (fd-up g))
  up (step x nf)     R = step (x , R) (λ g → nf (fd-up g))
  up (tend x nf)     R = tend (x , R) (λ g → nf (fd-up g))
  up (left x nf i)   R = left (x , R) (λ g → nf (fd-up g)) i

  -- Every raw row before a passed point shows.
  img : ∀ {q j e″} → ¬ Fd t q → t j e″ → j ≺ q → Tk t j e″
  img {q} {j} {out a} nf tj jq with keep a in kp
  ... | true  = pass tj (subst T (sym kp) tt) (λ g → nf (fd-≼ g (≺→≼ {j} {q} jq)))
  ... | false = ⊥-elim (nf (j , a , tj , subst (λ b → T (not b)) (sym kp) tt , jq))
  img {q} {j} {skip}  nf tj jq = step tj (λ g → nf (fd-≼ g (≺→≼ {j} {q} jq)))
  img {q} {j} {end}   nf tj jq = tend tj (λ g → nf (fd-≼ g (≺→≼ {j} {q} jq)))
  img {q} {j} {pin r} nf tj jq =
    left tj (λ g → nf (fd-≼ g (≺→≼ {r} {q} (≼-≺-≺ {r} {j} {q} (⊑-≼ (inside-⊑ r j (pin-in tj))) jq)))) (pin-in tj)

  ----------------------------------------------------------------------
  -- Raw to truncated

  -- What the row's source waits on, the row waits on too.
  src-of : ∀ {y e} (x : Tk t y e) → Reach (Tk t) y e → Reach t (srcP x) (srcE x)
  src-of {y} x@(pass {q} _ _ nf)   (L , h) = L , λ {j} tj jq _ → h (img nf tj jq) (≺-≼-≺ {j} {q} {y} jq (src≼ x)) tt
  src-of {y} x@(fail {q} _ _ nf _) (L , h) = L , λ {j} tj jq _ → h (img nf tj jq) (≺-≼-≺ {j} {q} {y} jq (src≼ x)) tt
  src-of {y} x@(stop {q} _ _ nf)   (L , h) = L , λ {j} tj jq _ → h (img nf tj jq) (≺-≼-≺ {j} {q} {y} jq (src≼ x)) tt
  src-of {y} x@(step {q} _ nf)     (L , h) = L , λ {j} tj jq _ → h (img nf tj jq) (≺-≼-≺ {j} {q} {y} jq (src≼ x)) tt
  src-of {y} x@(tend {q} _ nf)     (L , h) = L , λ {j} tj jq _ → h (img nf tj jq) (≺-≼-≺ {j} {q} {y} jq (src≼ x)) tt
  src-of (left {q} {r} _ nf i) (L , h) = L , pick
    where
      pick : ∀ {j e″} → t j e″ → j ≺ q → Dep q (pin r) j e″ → _
      pick {j} {e″} tj jq d with d i
      ... | inj₁ jr   = h (img nf tj jr) jq (λ _ → inj₁ jr)
      ... | inj₂ refl = h (left tj nf (pin-in tj)) jq (λ _ → inj₂ refl)

  raw→ : ∀ {y e} → Truncate (Tk t) y e → Truncate (Tk τ) y e
  raw→ (x , R) = up x (src-of x R) , reach-via (λ z _ d → _ , down z , d) R

  ----------------------------------------------------------------------
  -- Truncated to raw

  -- A reached pin's later pins of its connect are reached.
  pin-reach : ∀ {q r k} → Reach t q (pin r) → (z : Tk t k (pin r)) → k ≺ q → Reach t (srcP z) (srcE z)
  pin-reach {q} {r} {k} (ks , h) (left _ _ ik) kq = ks , λ {j} tj jk d → h tj (≺-trans {j} {k} {q} jk kq) (λ _ → d ik)

  -- Every row a row over the truncated input waits on has its source
  -- reached.
  src-reach : ∀ {y e k e′} → Tk τ y e → (z : Tk t k e′) → k ≺ y → Dep y e k e′ → Reach t (srcP z) (srcE z)
  src-reach {k = k} (pass {q} x _ _) z ky _ = few-down (few-of x tt) (≺→≼ {srcP z} {q} (≼-≺-≺ {srcP z} {k} {q} (src≼ z) ky))
  src-reach {k = k} (step {q} x _)   z ky _ = few-down (few-of x tt) (≺→≼ {srcP z} {q} (≼-≺-≺ {srcP z} {k} {q} (src≼ z) ky))
  src-reach {k = k} (tend {q} x _)   z ky _ = few-down (few-of x tt) (≺→≼ {srcP z} {q} (≼-≺-≺ {srcP z} {k} {q} (src≼ z) ky))
  src-reach {k = k} (fail {q} x _ _ _) z ky _ with below-or-under (srcP z) q (ix 0) (≼-≺-≺ {srcP z} {k} {q ⊕ [ ix 0 ]} (src≼ z) ky)
  ... | inj₁ le             = few-down (few-of x tt) le
  ... | inj₂ (_ , _ , eq) = ⊥-elim (flat (proj₁ x) (subst (λ w → t w (srcE z)) eq (srcT z)))
  src-reach {k = k} (stop {q} x _ _) z ky _ with below-or-under (srcP z) q last (≼-≺-≺ {srcP z} {k} {q ⊕ [ last ]} (src≼ z) ky)
  ... | inj₁ le             = few-down (few-of x tt) le
  ... | inj₂ (_ , _ , eq) = ⊥-elim (flat (proj₁ x) (subst (λ w → t w (srcE z)) eq (srcT z)))
  src-reach {k = k} (left {q} {r} x _ i) z ky d with d i
  ... | inj₁ kr   = few-down (pin-few {q} {r} (proj₂ x) i) (≺→≼ {srcP z} {r} (≼-≺-≺ {srcP z} {k} {r} (src≼ z) kr))
  ... | inj₂ refl = pin-reach {q} {r} (proj₂ x) z ky

  trunc→ : ∀ {y e} → Truncate (Tk τ) y e → Truncate (Tk t) y e
  trunc→ {y} {e} (x , R) = down x , reach-via (λ z ky d → _ , up z (src-reach x z ky d) , d) R

------------------------------------------------------------------------
-- scan: absorption is FALSE without a well-founded input

-- A scan shows a value only through the chain of values before it
-- (`Acc`), so a run whose values descend forever shows none of them,
-- and its end, past them, has nothing before it.  Truncated first, the
-- end is past infinitely many rows and gone.  The input is flat and has
-- no pins, so what `takeWhile` needed does not suffice here.
module ScanRefuted where

  open import Data.List using (replicate; _++_; length)
  open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_)
  open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; n≮n)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Relation.Binary.PropositionalEquality using (cong)
  open import Data.List.Properties using (∷-injectiveʳ)
  open import denotation.Position using (Label; frame; _∙_; path; cmpPath; Cmp; lt; isLt)
  open import denotation.EmissionSet using (module Scan)
  open import denotation.Laws.Modulus using (≺-irrefl)
  open Scan using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)

  rep : ℕ → List Label
  rep n = replicate n (ix 0)

  -- The n-th value, each before the last: [ix 1], [ix 0, ix 1], …
  pt : ℕ → Pos
  pt n = frame ∙ (rep n ++ [ ix 1 ])

  c : Pos
  c = frame ∙ [ ix 2 ]

  data Ch : EmissionSet ℕ where
    v : ∀ {y} n → y ≡ pt n → Ch y (out n)
    e : ∀ {y} → y ≡ c → Ch y end

  cmp-down : ∀ n → cmpPath (ix 0 ∷ rep n ++ [ ix 1 ]) (rep n ++ [ ix 1 ]) ≡ lt
  cmp-down zero    = refl
  cmp-down (suc n) = cmp-down n

  down-lt : ∀ n → pt (suc n) ≺ pt n
  down-lt n = subst (λ x → T (isLt x)) (sym (cmp-down n)) tt

  cmp-c : ∀ n → cmpPath (rep n ++ [ ix 1 ]) [ ix 2 ] ≡ lt
  cmp-c zero    = refl
  cmp-c (suc n) = refl

  before-c : ∀ n → pt n ≺ c
  before-c n = subst (λ x → T (isLt x)) (sym (cmp-c n)) tt

  -- No value has a chain: below each lies another.
  no-acc : ∀ {B} {f : B → ℕ → B} {z q b} → Acc f z Ch q b → ⊥
  no-acc (acc₀ (v n refl) mn) = mn (v (suc n) refl) (down-lt n)
  no-acc (acc ac _ _ _)       = no-acc ac

  -- RAW, THEN TRUNCATED: the end is shown, nothing before it.
  raw-end : ∀ {B} (f : B → ℕ → B) z → Truncate (ScanT f z Ch) c end
  raw-end f z = send (e refl) , [] , λ x kc _ → none x kc
    where
      none : ∀ {k e′} → ScanT f z Ch k e′ → k ≺ c → k ∈ []
      none (sval ac)        _  = ⊥-elim (no-acc ac)
      none (send (e refl))  kc = ⊥-elim (≺-irrefl {c} kc)

  plen : Pos → ℕ
  plen x = length (path x)

  bound : List Pos → ℕ
  bound []       = 0
  bound (x ∷ xs) = plen x ⊔ bound xs

  in-bound : ∀ {x xs} → x ∈ xs → plen x ≤ bound xs
  in-bound {xs = y ∷ ys} (here refl) = m≤m⊔n (plen y) (bound ys)
  in-bound {xs = y ∷ ys} (there m)   = ≤-trans (in-bound m) (m≤n⊔m (plen y) (bound ys))

  len-pt : ∀ n → plen (pt n) ≡ suc n
  len-pt zero    = refl
  len-pt (suc n) = cong suc (len-pt n)

  -- TRUNCATED, THEN SCANNED: the end waits on every value, and no
  -- finite list holds them all.
  trunc-end : ∀ {B} (f : B → ℕ → B) z → ¬ Truncate (ScanT f z (Truncate Ch)) c end
  trunc-end f z (send ((_ , ks , h)) , _) = n≮n n (subst (_≤ n) (len-pt n) (in-bound (h (v n refl) (before-c n) tt)))
    where n = bound ks

  -- The run meets what `TakeAbsorb` asks: no row under a row, no pin.
  fp : ∀ n m {l ys} → (rep n ++ [ ix 1 ]) ++ (l ∷ ys) ≡ rep m ++ [ ix 1 ] → ⊥
  fp zero    zero    ()
  fp zero    (suc m) ()
  fp (suc n) zero    ()
  fp (suc n) (suc m) eq = fp n m (∷-injectiveʳ eq)

  fc : ∀ n {l ys} → (rep n ++ [ ix 1 ]) ++ (l ∷ ys) ≡ ix 2 ∷ [] → ⊥
  fc zero    ()
  fc (suc n) ()

  fe : ∀ m {l ys} → ix 2 ∷ l ∷ ys ≡ rep m ++ [ ix 1 ] → ⊥
  fe zero    ()
  fe (suc m) ()

  ch-flat : ∀ {y ev l ys ev′} → Ch y ev → Ch (y ⊕ (l ∷ ys)) ev′ → ⊥
  ch-flat (v n refl) (v m eq) = fp n m (cong path eq)
  ch-flat (v n refl) (e eq)   = fc n (cong path eq)
  ch-flat (e refl)   (v m eq) = fe m (cong path eq)
  ch-flat (e refl)   (e ())

  ch-pin-in : ∀ {j r} → Ch j (pin r) → T (inside r j)
  ch-pin-in ()

  -- So no lemma moves a scanned row across a truncation of a run whose
  -- values need not have a first, though the run is flat and unpinned.
  scan-absorb-fails : ∀ {B} (f : B → ℕ → B) z
                    → (∀ {y ev l ys ev′} → Ch y ev → Ch (y ⊕ (l ∷ ys)) ev′ → ⊥) × (∀ {j r} → Ch j (pin r) → T (inside r j))
                    × Truncate (ScanT f z Ch) c end × ¬ Truncate (ScanT f z (Truncate Ch)) c end
  scan-absorb-fails f z = ch-flat , ch-pin-in , raw-end f z , trunc-end f z
