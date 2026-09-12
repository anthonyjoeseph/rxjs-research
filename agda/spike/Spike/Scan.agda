------------------------------------------------------------------
-- THE ORDER DISCHARGES THE DOMAIN WITH `scanᵉ` PRESENT, AND THE
-- SYNTACTIC READING OF ITS EXPONENT IS REFUTED.
--
-- `Spike.Total` settled totality for the fragment WITHOUT `scanᵉ`.
-- The refold is what `scanᵉ` adds: the accumulator is re-templated
-- once per arriving value, so an accumulator that nests raises hop
-- depth PER ARRIVAL, and no clause of a depth measure can see how
-- many arrivals there are.  The real development answers that with
-- `(2 + pm)^V`, where `V` is a tower of twos justified by a store
-- invariant — the caps face.
--
-- This module answers it with `blE`, an upper bound on a
-- subscription's synchronous burst LENGTH.  The scan clause reads
--
--   hopD (scanᵉ f z e) = iter (hopDt f) (pm f) (blE e) (hopDv z ⊔ hopD e)
--
-- where `iter c p k` is the k-fold affine map `x ↦ c + p · x`: the
-- refold recurrence written as a recursion instead of solved.  On THIS
-- fragment every `blE` is computed from the expression tree, no cap is
-- computed anywhere and `V` does not appear, which is what the domain
-- result below rests on.
--
-- WHAT IS NOT TRUE IS THAT THE EXPONENT IS CARRIED BY THE PROGRAM
-- TEXT, AND THE GAP BETWEEN THOSE TWO IS THE WHOLE FINDING.  `blE` is
-- not invariant under PLUGGING: a value substituted into an `allᵉ`'s
-- source contributes its own WIDTH to the burst length, so a template
-- plugging into an `allᵉ` that feeds a `scanᵉ` takes its fold count
-- from the plugged VALUE.  The plug lands in `iter`'s EXPONENT and the
-- transport is exponential rather than affine.  No `Tm` here can build
-- such a template; the real `strmᵗ` can, and it is ordinary rxjs —
-- `map(v => v.pipe(mergeAll(), scan(…)))`.  So the reading that would
-- let this fragment's result DELETE `V` does not survive the real
-- language.  What survives is the order itself, which never mentions
-- `blE`.
--
-- `blE` cannot be read off one expression alone — `allᵉ` concatenates
-- the bursts of the observables its source emits — so it comes with a
-- HEREDITARY WIDTH `H`, bounding every emitted value's own width
-- exactly as `emit-hop` bounds every emitted value's own depth.  The
-- two are one mutual induction (`emit-len`/`emit-H`), and the `allᵉ`
-- clause `blE (allᵉ e) = blE e * H e` is where they meet — the same
-- clause the refutation turns on.
--
-- `dupᵗ` IS DELIBERATE AND IS NOT DECORATION.  `Spike.Total` carried
-- no template that could mention its argument twice in ADDED position,
-- so every template there had plug slope 1 and the multiplier in the
-- `mapᵉ` clause was vacuous — which is how a claim that the multiplier
-- is unnecessary survived a green spike and was refuted only in the
-- real tree (`Refuted.Hop-Mul-Clause`).  `dupᵗ t` reifies its argument
-- as both an inner map's template AND that map's source, which is the
-- shape the real refutation uses, so its slope is 2 and a fragment
-- that drops the multiplier now fails here.
--
-- WHAT THE TEMPLATE LAWS REACH, since a fragment's silence is what let
-- the last claim through.  Both laws are AFFINE in the plugged value,
-- and the fragment exercises the three positions a plug can land in.
-- `dupᵗ` puts it in two ADDED positions (slope 2, so the multiplier is
-- not vacuous).  `nestᵗ` puts it under an `allᵉ` that SUBSCRIBES to
-- it, which is the position where the image's own burst length depends
-- on the plugged value — the case `Hv` exists to carry, since
-- `Hv (obsᵛ o)` is the larger of `o`'s two widths and one affine law
-- therefore covers both.
--
-- AND `scnᵗ` PUTS IT INSIDE A `scanᵉ`, which this header once recorded
-- as analysis with nothing instantiating it.  It plugs its argument
-- into the SOURCE of an inner scan whose LENGTH the template's own
-- text writes down, so the plug is transported by that many steps of
-- the recurrence and the slope is the inner step's squared, times the
-- plug's.  The law survives AFFINE here, and `scn-slope` and
-- `scn-image` pin it at a program where composing the slopes once
-- would report 2 against an image of 4.  But that is a fact about the
-- LITERAL SOURCE `scnᵗ` writes down, not about the position: swap that
-- source for the plug itself and the affine law fails outright, which
-- is what the refutation below does.
--
-- IT IS ALSO WHERE THE RECURRENCE'S TWO DIRECTIONS COME APART.  A plug
-- into a scan moves the recurrence's BASE, which the fold's own
-- induction never does, so `iter-mono-x` is needed for this case and
-- for no other.
--
-- WHAT IS STILL NOT REACHED: a plug into the inner scan's SEED, which
-- lands in the same base position through the `⊔` and so takes the
-- same transport, but which no row here instantiates; and a template
-- body of arbitrary shape, which the real `strmᵗ` permits and this
-- `Tm` does not — the gap the refutation walks through.
--
-- `takeᵉ` IS IN THE FRAGMENT AND THE ORDER IS INDIFFERENT TO IT, WHICH
-- IS A WEAKER RESULT THAN IT LOOKS.  Every measure passes it through,
-- mirroring the real tree where no depth or burst family reads the
-- count; the domain gains one clause that descends on `syncSize` and
-- nothing else moves.  What that green does NOT cover is the thing a
-- real `take` actually does: COMPLETE its source, and completion runs
-- teardown, which is a synchronous re-entry edge.  This fragment has no
-- completion at all — every run is a burst and then silence — so the
-- clause cannot fail here whatever teardown does, and reading the green
-- as evidence about `take` would be the same move that let the last two
-- claims through.  It is evidence about the MEASURES and about nothing
-- else.
--
-- REFUTED: `Spike.Wide` — no affine plug law exists for a template
-- plugging into an `allᵉ` that feeds a `scanᵉ`, so this module's
-- exponent cannot be read as syntactic in the real language.  Every
-- `Tm` here does satisfy that law (`template-affine`), which is
-- exactly why the fragment stays green while the reading is false.
------------------------------------------------------------------
module Spike.Scan where

open import Level using (0ℓ)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; _<_; _<?_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using
  ( ≤-refl; ≤-trans; ≤-reflexive; n≤1+n; +-suc
  ; m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m; ⊔-lub
  ; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤; *-monoʳ-≤; *-monoˡ-≤; *-mono-≤; *-identityˡ
  ; m≤n⇒m<n∨m≡n; m<1+n⇒m<n∨m≡n; ≮⇒≥ )
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open +-*-Solver using (solve; _:=_; _:+_; _:*_)

------------------------------------------------------------------
-- THE LANGUAGE — `Spike.Total` plus `scanᵉ`, `accᵗ`, `dupᵗ` and `scnᵗ`.
------------------------------------------------------------------

data Val : Set
data Exp : Set
data Tm  : Set

data Val where
  natᵛ : ℕ → Val
  obsᵛ : Exp → Val

data Tm where
  inᵗ    : Tm
  accᵗ   : Tm
  konstᵗ : Val → Tm
  nestᵗ  : Tm → Tm
  dupᵗ   : Tm → Tm
  scnᵗ   : Tm → Tm → Tm

data Exp where
  ofᵉ    : List Val → Exp
  mapᵉ   : Tm → Exp → Exp
  scanᵉ  : Tm → Val → Exp → Exp
  takeᵉ  : ℕ → Exp → Exp
  allᵉ   : Exp → Exp
  μᵉ     : Exp → Exp
  recᵉ   : Exp
  deferᵉ : Exp → Exp
  slotᵉ  : ℕ → Exp

-- a template reads (accumulator , incoming value)
evalTm : Tm → Val → Val → Val
evalTm inᵗ        a v = v
evalTm accᵗ       a v = a
evalTm (konstᵗ k) a v = k
evalTm (nestᵗ t)  a v = obsᵛ (allᵉ (ofᵉ (evalTm t a v ∷ [])))
evalTm (dupᵗ t)   a v =
  obsᵛ (mapᵉ (konstᵗ (evalTm t a v)) (ofᵉ (evalTm t a v ∷ [])))
evalTm (scnᵗ g t) a v =
  obsᵛ (scanᵉ g (natᵛ 0) (ofᵉ (evalTm t a v ∷ evalTm t a v ∷ [])))

-- `takeᵉ`'s count is a plain ℕ here because the real language's count is
-- a `Tm` that NO depth or burst measure reads — only the frame-width
-- family does — so a term-valued count would add a plug position the
-- measures cannot see, which is a different question from this one.
takeN : ℕ → List Val → List Val
takeN zero    xs       = []
takeN (suc n) []       = []
takeN (suc n) (x ∷ xs) = x ∷ takeN n xs

takeN-length : ∀ n xs → length (takeN n xs) ≤ length xs
takeN-length zero    xs       = z≤n
takeN-length (suc n) []       = z≤n
takeN-length (suc n) (x ∷ xs) = s≤s (takeN-length n xs)

takeN-∈ : ∀ n xs {u} → u ∈ takeN n xs → u ∈ xs
takeN-∈ (suc n) (x ∷ xs) (here p)  = here p
takeN-∈ (suc n) (x ∷ xs) (there p) = there (takeN-∈ n xs p)

mapB : Tm → List Val → List Val
mapB f []       = []
mapB f (v ∷ vs) = evalTm f v v ∷ mapB f vs

foldB : Tm → Val → List Val → List Val
foldB f a []       = []
foldB f a (v ∷ vs) = evalTm f a v ∷ foldB f (evalTm f a v) vs

mapB-length : ∀ f ws → length (mapB f ws) ≡ length ws
mapB-length f []       = refl
mapB-length f (w ∷ ws) = cong suc (mapB-length f ws)

foldB-length : ∀ f a ws → length (foldB f a ws) ≡ length ws
foldB-length f a []       = refl
foldB-length f a (w ∷ ws) = cong suc (foldB-length f (evalTm f a w) ws)

------------------------------------------------------------------
-- THE PLUG SLOPES.  Both are environment-free: they are properties of
-- the template's shape, not of anything it is applied to.  `dupᵗ`
-- doubles both, which is the whole reason it is here.
------------------------------------------------------------------

pm : Tm → ℕ
pm inᵗ        = 1
pm accᵗ       = 1
pm (konstᵗ k) = 1
pm (nestᵗ t)  = pm t
pm (dupᵗ t)   = pm t + pm t
pm (scnᵗ g t) = pm g * (pm g * pm t)

ph : Tm → ℕ
ph inᵗ        = 1
ph accᵗ       = 1
ph (konstᵗ k) = 1
ph (nestᵗ t)  = ph t
ph (dupᵗ t)   = ph t + ph t
ph (scnᵗ g t) = ph g * (ph g * ph t)

one≤* : ∀ {x y} → 1 ≤ x → 1 ≤ y → 1 ≤ x * y
one≤* hx hy = *-mono-≤ hx hy

pm-pos : ∀ f → 1 ≤ pm f
pm-pos inᵗ        = ≤-refl
pm-pos accᵗ       = ≤-refl
pm-pos (konstᵗ k) = ≤-refl
pm-pos (nestᵗ t)  = pm-pos t
pm-pos (dupᵗ t)   = ≤-trans (pm-pos t) (m≤m+n _ _)
pm-pos (scnᵗ g t) = one≤* (pm-pos g) (one≤* (pm-pos g) (pm-pos t))

ph-pos : ∀ f → 1 ≤ ph f
ph-pos inᵗ        = ≤-refl
ph-pos accᵗ       = ≤-refl
ph-pos (konstᵗ k) = ≤-refl
ph-pos (nestᵗ t)  = ph-pos t
ph-pos (dupᵗ t)   = ≤-trans (ph-pos t) (m≤m+n _ _)
ph-pos (scnᵗ g t) = one≤* (ph-pos g) (one≤* (ph-pos g) (ph-pos t))

------------------------------------------------------------------
-- THE REFOLD RECURRENCE, UNSOLVED.  `iter c p k` is the k-fold affine
-- map; every fact below is one of four, and none of them is a closed
-- form.
--
-- THE FOLD ITSELF NEEDS ONLY THREE, AND `iter-mono-x` IS NOT ONE OF
-- THEM: the fold's induction lands on a base that is already one step
-- of the recurrence, so `iter-shift` absorbs it exactly and nothing
-- ever has to widen the starting point.  What needs base monotonicity
-- is a TEMPLATE plugging into a `scanᵉ` (`scnᵗ`), where the plugged
-- value lands in the inner scan's SOURCE and so moves the base rather
-- than the count.  That is the one place the two directions of the
-- recurrence come apart, and it is why the lemma is here and not in
-- `Spike.Total`.
------------------------------------------------------------------

iter : ℕ → ℕ → ℕ → ℕ → ℕ
iter c p zero    x = x
iter c p (suc k) x = c + p * iter c p k x

mul-ge : ∀ {p} y → 1 ≤ p → y ≤ p * y
mul-ge {p} y hp = ≤-trans (≤-reflexive (sym (*-identityˡ y))) (*-monoˡ-≤ y hp)

iter-base : ∀ c {p} k x → 1 ≤ p → x ≤ iter c p k x
iter-base c zero    x hp = ≤-refl
iter-base c (suc k) x hp =
  ≤-trans (iter-base c k x hp)
          (≤-trans (mul-ge _ hp) (m≤n+m _ c))

iter-mono-k : ∀ c {p} x {j k} → 1 ≤ p → j ≤ k →
              iter c p j x ≤ iter c p k x
iter-mono-k c     x {k = k} hp z≤n       = iter-base c k x hp
iter-mono-k c {p} x         hp (s≤s j≤k) =
  +-monoʳ-≤ c (*-monoʳ-≤ p (iter-mono-k c x hp j≤k))

-- the base direction, which only a plug into a `scanᵉ` asks for
iter-mono-x : ∀ c p k {x y} → x ≤ y → iter c p k x ≤ iter c p k y
iter-mono-x c p zero    h = h
iter-mono-x c p (suc k) h = +-monoʳ-≤ c (*-monoʳ-≤ p (iter-mono-x c p k h))

-- one fold step absorbed into the count: this is what turns the
-- fold's induction into an `iter` bound without ever solving it
iter-shift : ∀ c p k x → iter c p k (c + p * x) ≡ iter c p (suc k) x
iter-shift c p zero    x = refl
iter-shift c p (suc k) x = cong (λ y → c + p * y) (iter-shift c p k x)

dup-arith : ∀ c p m → (c + p * m) + (c + p * m) ≡ (c + c) + (p + p) * m
dup-arith =
  solve 3 (λ c p m → (c :+ p :* m) :+ (c :+ p :* m)
                  := (c :+ c) :+ (p :+ p) :* m) refl

-- TWO steps of the recurrence applied to an affine base, re-bracketed
-- as one affine map.  The slope it lands is `p * (p * p₁)` — the plug's
-- own slope times the inner step's, raised to the SOURCE LENGTH the
-- template wrote down.  That is where an exponent in the template's
-- text enters, and it is the whole content of the `scnᵗ` case.
scn-arith : ∀ c p c₁ p₁ m →
            c + p * (c + p * (c₁ + p₁ * m))
            ≡ ((c + p * c) + p * (p * c₁)) + (p * (p * p₁)) * m
scn-arith =
  solve 5 (λ c p c₁ p₁ m →
             c :+ p :* (c :+ p :* (c₁ :+ p₁ :* m))
          := ((c :+ p :* c) :+ p :* (p :* c₁)) :+ (p :* (p :* p₁)) :* m) refl

------------------------------------------------------------------
-- THE UNFOLD.  `recᵉ` becomes a GATED copy, so every measure reads it
-- exactly as it read the `recᵉ`.
------------------------------------------------------------------

substE : Exp → Exp → Exp
substV : Val → Exp → Val
substL : List Val → Exp → List Val
substT : Tm → Exp → Tm

substE (ofᵉ vs)      m = ofᵉ (substL vs m)
substE (mapᵉ f e)    m = mapᵉ (substT f m) (substE e m)
substE (scanᵉ f z e) m = scanᵉ (substT f m) (substV z m) (substE e m)
substE (takeᵉ n e)   m = takeᵉ n (substE e m)
substE (allᵉ e)      m = allᵉ (substE e m)
substE (μᵉ b)        m = μᵉ b
substE recᵉ          m = deferᵉ m
substE (deferᵉ b)    m = deferᵉ b
substE (slotᵉ i)     m = slotᵉ i

substV (natᵛ n) m = natᵛ n
substV (obsᵛ e) m = obsᵛ (substE e m)

substL []       m = []
substL (v ∷ vs) m = substV v m ∷ substL vs m

substT inᵗ        m = inᵗ
substT accᵗ       m = accᵗ
substT (konstᵗ k) m = konstᵗ (substV k m)
substT (nestᵗ t)  m = nestᵗ (substT t m)
substT (dupᵗ t)   m = dupᵗ (substT t m)
substT (scnᵗ g t) m = scnᵗ (substT g m) (substT t m)

unfoldμ : Exp → Exp
unfoldμ b = substE b (μᵉ b)

substL-length : ∀ vs m → length (substL vs m) ≡ length vs
substL-length []       m = refl
substL-length (v ∷ vs) m = cong suc (substL-length vs m)

pm-subst : ∀ f m → pm (substT f m) ≡ pm f
pm-subst inᵗ        m = refl
pm-subst accᵗ       m = refl
pm-subst (konstᵗ k) m = refl
pm-subst (nestᵗ t)  m = pm-subst t m
pm-subst (dupᵗ t)   m = cong₂ _+_ (pm-subst t m) (pm-subst t m)
pm-subst (scnᵗ g t) m =
  cong₂ _*_ (pm-subst g m) (cong₂ _*_ (pm-subst g m) (pm-subst t m))

ph-subst : ∀ f m → ph (substT f m) ≡ ph f
ph-subst inᵗ        m = refl
ph-subst accᵗ       m = refl
ph-subst (konstᵗ k) m = refl
ph-subst (nestᵗ t)  m = ph-subst t m
ph-subst (dupᵗ t)   m = cong₂ _+_ (ph-subst t m) (ph-subst t m)
ph-subst (scnᵗ g t) m =
  cong₂ _*_ (ph-subst g m) (cong₂ _*_ (ph-subst g m) (ph-subst t m))

syncSize : Exp → ℕ
syncSize (ofᵉ vs)      = 1
syncSize (mapᵉ f e)    = suc (syncSize e)
syncSize (scanᵉ f z e) = suc (syncSize e)
syncSize (takeᵉ n e)   = suc (syncSize e)
syncSize (allᵉ e)      = suc (syncSize e)
syncSize (μᵉ b)        = suc (syncSize b)
syncSize recᵉ          = 1
syncSize (deferᵉ b)    = 1
syncSize (slotᵉ i)     = 1

syncSize-subst : ∀ b m → syncSize (substE b m) ≡ syncSize b
syncSize-subst (ofᵉ vs)      m = refl
syncSize-subst (mapᵉ f e)    m = cong suc (syncSize-subst e m)
syncSize-subst (scanᵉ f z e) m = cong suc (syncSize-subst e m)
syncSize-subst (takeᵉ n e)   m = cong suc (syncSize-subst e m)
syncSize-subst (allᵉ e)      m = cong suc (syncSize-subst e m)
syncSize-subst (μᵉ b)        m = refl
syncSize-subst recᵉ          m = refl
syncSize-subst (deferᵉ b)    m = refl
syncSize-subst (slotᵉ i)     m = refl

------------------------------------------------------------------
-- THE MEASURES.  `η` bounds a slot's hop, `ν` a slot's width; both
-- are the spike's stand-in for the real `Rx.Slot-Hop` fixpoint.
------------------------------------------------------------------

module M (η ν : ℕ → ℕ) where

  ----------------------------------------------------------------
  -- WIDTH.  `blE e` bounds the LENGTH of e's synchronous burst; `H e`
  -- bounds every emitted value's own `Hv`, where a value's `Hv` is the
  -- larger of the two for the observable it carries.  `allᵉ` is where
  -- they meet: it emits at most `blE e` inners, each of which emits at
  -- most its own `blE`, which `H e` bounds.
  ----------------------------------------------------------------

  blE : Exp → ℕ
  H   : Exp → ℕ
  Hv  : Val → ℕ
  Hl  : List Val → ℕ
  Ht  : Tm → ℕ

  blE (ofᵉ vs)      = length vs
  blE (mapᵉ f e)    = blE e
  blE (scanᵉ f z e) = blE e
  blE (takeᵉ n e)   = blE e
  blE (allᵉ e)      = blE e * H e
  blE (μᵉ b)        = blE b
  blE recᵉ          = 0
  blE (deferᵉ b)    = 0
  blE (slotᵉ i)     = ν i

  H (ofᵉ vs)      = Hl vs
  H (mapᵉ f e)    = Ht f + ph f * H e
  H (scanᵉ f z e) = iter (Ht f) (ph f) (blE e) (Hv z ⊔ H e)
  H (takeᵉ n e)   = H e
  H (allᵉ e)      = H e
  H (μᵉ b)        = H b
  H recᵉ          = 0
  H (deferᵉ b)    = 0
  H (slotᵉ i)     = ν i

  Hv (natᵛ n) = 0
  Hv (obsᵛ o) = blE o ⊔ H o

  Hl []       = 0
  Hl (v ∷ vs) = Hv v ⊔ Hl vs

  Ht inᵗ        = 0
  Ht accᵗ       = 0
  Ht (konstᵗ k) = Hv k
  Ht (nestᵗ t)  = Ht t
  Ht (dupᵗ t)   = suc (Ht t + Ht t)
  Ht (scnᵗ g t) = 2 + (((Ht g + ph g * Ht g) + ph g * (ph g * Ht t)))

  ----------------------------------------------------------------
  -- DEPTH.  The `mapᵉ` clause multiplies, and `dupᵗ` is what makes
  -- that non-vacuous.  The `scanᵉ` clause is the refold recurrence
  -- iterated `blE e` times — syntax, not a budget.
  ----------------------------------------------------------------

  hopD  : Exp → ℕ
  hopDv : Val → ℕ
  hopDl : List Val → ℕ
  hopDt : Tm → ℕ

  hopD (ofᵉ vs)      = hopDl vs
  hopD (mapᵉ f e)    = hopDt f + pm f * hopD e
  hopD (scanᵉ f z e) = iter (hopDt f) (pm f) (blE e) (hopDv z ⊔ hopD e)
  hopD (takeᵉ n e)   = hopD e
  hopD (allᵉ e)      = suc (hopD e)
  hopD (μᵉ b)        = hopD b
  hopD recᵉ          = 0
  hopD (deferᵉ b)    = 0
  hopD (slotᵉ i)     = η i

  hopDv (natᵛ n) = 0
  hopDv (obsᵛ e) = hopD e

  hopDl []       = 0
  hopDl (v ∷ vs) = hopDv v ⊔ hopDl vs

  hopDt inᵗ        = 0
  hopDt accᵗ       = 0
  hopDt (konstᵗ k) = hopDv k
  hopDt (nestᵗ t)  = suc (hopDt t)
  hopDt (dupᵗ t)   = hopDt t + hopDt t
  hopDt (scnᵗ g t) = (hopDt g + pm g * hopDt g) + pm g * (pm g * hopDt t)

  ----------------------------------------------------------------
  -- THE UNFOLD IS NEUTRAL FOR EVERY MEASURE.
  ----------------------------------------------------------------

  blE-subst : ∀ e m → blE (substE e m) ≡ blE e
  H-subst   : ∀ e m → H (substE e m) ≡ H e
  Hv-subst  : ∀ v m → Hv (substV v m) ≡ Hv v
  Hl-subst  : ∀ vs m → Hl (substL vs m) ≡ Hl vs
  Ht-subst  : ∀ f m → Ht (substT f m) ≡ Ht f

  blE-subst (ofᵉ vs)      m = substL-length vs m
  blE-subst (mapᵉ f e)    m = blE-subst e m
  blE-subst (scanᵉ f z e) m = blE-subst e m
  blE-subst (takeᵉ n e)   m = blE-subst e m
  blE-subst (allᵉ e)      m = cong₂ _*_ (blE-subst e m) (H-subst e m)
  blE-subst (μᵉ b)        m = refl
  blE-subst recᵉ          m = refl
  blE-subst (deferᵉ b)    m = refl
  blE-subst (slotᵉ i)     m = refl

  H-subst (ofᵉ vs)      m = Hl-subst vs m
  H-subst (mapᵉ f e)    m
    rewrite Ht-subst f m | ph-subst f m | H-subst e m = refl
  H-subst (scanᵉ f z e) m
    rewrite Ht-subst f m | ph-subst f m | blE-subst e m
          | Hv-subst z m | H-subst e m = refl
  H-subst (takeᵉ n e)   m = H-subst e m
  H-subst (allᵉ e)      m = H-subst e m
  H-subst (μᵉ b)        m = refl
  H-subst recᵉ          m = refl
  H-subst (deferᵉ b)    m = refl
  H-subst (slotᵉ i)     m = refl

  Hv-subst (natᵛ n) m = refl
  Hv-subst (obsᵛ o) m = cong₂ _⊔_ (blE-subst o m) (H-subst o m)

  Hl-subst []       m = refl
  Hl-subst (v ∷ vs) m = cong₂ _⊔_ (Hv-subst v m) (Hl-subst vs m)

  Ht-subst inᵗ        m = refl
  Ht-subst accᵗ       m = refl
  Ht-subst (konstᵗ k) m = Hv-subst k m
  Ht-subst (nestᵗ t)  m = Ht-subst t m
  Ht-subst (dupᵗ t)   m = cong suc (cong₂ _+_ (Ht-subst t m) (Ht-subst t m))
  Ht-subst (scnᵗ g t) m =
    cong (2 +_)
      (cong₂ _+_ (cong₂ _+_ (Ht-subst g m) (cong₂ _*_ (ph-subst g m) (Ht-subst g m)))
                (cong₂ _*_ (ph-subst g m) (cong₂ _*_ (ph-subst g m) (Ht-subst t m))))

  hopD-subst  : ∀ e m → hopD (substE e m) ≡ hopD e
  hopDv-subst : ∀ v m → hopDv (substV v m) ≡ hopDv v
  hopDl-subst : ∀ vs m → hopDl (substL vs m) ≡ hopDl vs
  hopDt-subst : ∀ f m → hopDt (substT f m) ≡ hopDt f

  hopD-subst (ofᵉ vs)      m = hopDl-subst vs m
  hopD-subst (mapᵉ f e)    m
    rewrite hopDt-subst f m | pm-subst f m | hopD-subst e m = refl
  hopD-subst (scanᵉ f z e) m
    rewrite hopDt-subst f m | pm-subst f m | blE-subst e m
          | hopDv-subst z m | hopD-subst e m = refl
  hopD-subst (takeᵉ n e)   m = hopD-subst e m
  hopD-subst (allᵉ e)      m = cong suc (hopD-subst e m)
  hopD-subst (μᵉ b)        m = refl
  hopD-subst recᵉ          m = refl
  hopD-subst (deferᵉ b)    m = refl
  hopD-subst (slotᵉ i)     m = refl

  hopDv-subst (natᵛ n) m = refl
  hopDv-subst (obsᵛ e) m = hopD-subst e m

  hopDl-subst []       m = refl
  hopDl-subst (v ∷ vs) m = cong₂ _⊔_ (hopDv-subst v m) (hopDl-subst vs m)

  hopDt-subst inᵗ        m = refl
  hopDt-subst accᵗ       m = refl
  hopDt-subst (konstᵗ k) m = hopDv-subst k m
  hopDt-subst (nestᵗ t)  m = cong suc (hopDt-subst t m)
  hopDt-subst (dupᵗ t)   m = cong₂ _+_ (hopDt-subst t m) (hopDt-subst t m)
  hopDt-subst (scnᵗ g t) m =
    cong₂ _+_ (cong₂ _+_ (hopDt-subst g m) (cong₂ _*_ (pm-subst g m) (hopDt-subst g m)))
              (cong₂ _*_ (pm-subst g m) (cong₂ _*_ (pm-subst g m) (hopDt-subst t m)))

  ----------------------------------------------------------------
  -- THE TEMPLATE LAWS — both AFFINE, with the slope the template's
  -- own recursion computes.  `dupᵗ` is the case with slope 2.
  ----------------------------------------------------------------

  evalTm-hop : ∀ f a v → hopDv (evalTm f a v) ≤ hopDt f + pm f * (hopDv a ⊔ hopDv v)
  evalTm-hop inᵗ a v =
    ≤-trans (m≤n⊔m _ _) (≤-reflexive (sym (*-identityˡ _)))
  evalTm-hop accᵗ a v =
    ≤-trans (m≤m⊔n _ _) (≤-reflexive (sym (*-identityˡ _)))
  evalTm-hop (konstᵗ k) a v = m≤m+n _ _
  evalTm-hop (nestᵗ t)  a v = s≤s (⊔-lub (evalTm-hop t a v) z≤n)
  evalTm-hop (dupᵗ t)   a v =
    ≤-trans (+-mono-≤ ih (≤-trans (≤-reflexive (*-identityˡ _))
                                  (≤-trans (⊔-lub ≤-refl z≤n) ih)))
            (≤-reflexive (dup-arith (hopDt t) (pm t) (hopDv a ⊔ hopDv v)))
    where ih = evalTm-hop t a v
  evalTm-hop (scnᵗ g t) a v =
    ≤-trans (iter-mono-x (hopDt g) (pm g) 2
              (≤-trans (⊔-lub ≤-refl (⊔-lub ≤-refl z≤n)) (evalTm-hop t a v)))
            (≤-reflexive
              (scn-arith (hopDt g) (pm g) (hopDt t) (pm t) (hopDv a ⊔ hopDv v)))

  evalTm-wid : ∀ f a v → Hv (evalTm f a v) ≤ Ht f + ph f * (Hv a ⊔ Hv v)
  evalTm-wid inᵗ a v =
    ≤-trans (m≤n⊔m _ _) (≤-reflexive (sym (*-identityˡ _)))
  evalTm-wid accᵗ a v =
    ≤-trans (m≤m⊔n _ _) (≤-reflexive (sym (*-identityˡ _)))
  evalTm-wid (konstᵗ k) a v = m≤m+n _ _
  evalTm-wid (nestᵗ t)  a v =
    ⊔-lub (≤-trans (≤-reflexive (*-identityˡ _)) (⊔-lub ih z≤n))
          (⊔-lub ih z≤n)
    where ih = evalTm-wid t a v
  evalTm-wid (dupᵗ t)   a v =
    ⊔-lub (s≤s z≤n)
          (≤-trans (n≤1+n _)
                   (s≤s (≤-trans
                          (+-mono-≤ ih
                            (≤-trans (≤-reflexive (*-identityˡ _))
                                     (≤-trans (⊔-lub ≤-refl z≤n) ih)))
                          (≤-reflexive (dup-arith (Ht t) (ph t) (Hv a ⊔ Hv v))))))
    where ih = evalTm-wid t a v
  -- `Ht (scnᵗ g t)` leads with a literal 2, which REDUCES — the goal's
  -- right side is headed by `suc`, not by `_+_`, so the two arms weaken
  -- through `n≤1+n` rather than through an addition that is not there.
  evalTm-wid (scnᵗ g t) a v =
    ⊔-lub (s≤s (s≤s z≤n))
          (≤-trans (≤-trans (iter-mono-x (Ht g) (ph g) 2
                              (≤-trans (⊔-lub ≤-refl (⊔-lub ≤-refl z≤n))
                                       (evalTm-wid t a v)))
                            (≤-reflexive
                              (scn-arith (Ht g) (ph g) (Ht t) (ph t)
                                         (Hv a ⊔ Hv v))))
                   (≤-trans (n≤1+n _) (n≤1+n _)))

  ----------------------------------------------------------------
  -- MEMBERSHIP BOUNDS for the two burst constructions.
  ----------------------------------------------------------------

  hopDl-mem : ∀ ws {u} → u ∈ ws → hopDv u ≤ hopDl ws
  hopDl-mem (w ∷ ws) (here refl) = m≤m⊔n _ _
  hopDl-mem (w ∷ ws) (there p)   = ≤-trans (hopDl-mem ws p) (m≤n⊔m _ _)

  Hl-mem : ∀ ws {u} → u ∈ ws → Hv u ≤ Hl ws
  Hl-mem (w ∷ ws) (here refl) = m≤m⊔n _ _
  Hl-mem (w ∷ ws) (there p)   = ≤-trans (Hl-mem ws p) (m≤n⊔m _ _)

  mapB-mem : ∀ f ws {u B} → (∀ {x} → x ∈ ws → hopDv x ≤ B) →
             u ∈ mapB f ws → hopDv u ≤ hopDt f + pm f * B
  mapB-mem f (w ∷ ws) h (here refl) =
    ≤-trans (evalTm-hop f w w)
            (+-monoʳ-≤ (hopDt f)
              (*-monoʳ-≤ (pm f) (⊔-lub (h (here refl)) (h (here refl)))))
  mapB-mem f (w ∷ ws) h (there p) = mapB-mem f ws (λ q → h (there q)) p

  mapB-memH : ∀ f ws {u D} → (∀ {x} → x ∈ ws → Hv x ≤ D) →
              u ∈ mapB f ws → Hv u ≤ Ht f + ph f * D
  mapB-memH f (w ∷ ws) h (here refl) =
    ≤-trans (evalTm-wid f w w)
            (+-monoʳ-≤ (Ht f)
              (*-monoʳ-≤ (ph f) (⊔-lub (h (here refl)) (h (here refl)))))
  mapB-memH f (w ∷ ws) h (there p) = mapB-memH f ws (λ q → h (there q)) p

  -- THE REFOLD BOUND.  The k-th accumulator is the k-fold affine map
  -- applied to the common bound; nothing is solved and nothing is
  -- capped — the count is the burst's ACTUAL length, and the syntactic
  -- `blE` only has to dominate it.
  foldB-mem : ∀ f a ws {u B} → 1 ≤ pm f →
              hopDv a ≤ B → (∀ {x} → x ∈ ws → hopDv x ≤ B) →
              u ∈ foldB f a ws →
              hopDv u ≤ iter (hopDt f) (pm f) (length ws) B
  foldB-mem f a (w ∷ ws) {B = B} hp ha h (here refl) =
    ≤-trans step (iter-mono-k (hopDt f) B {k = length (w ∷ ws)} hp (s≤s z≤n))
    where
      step : hopDv (evalTm f a w) ≤ iter (hopDt f) (pm f) 1 B
      step = ≤-trans (evalTm-hop f a w)
                     (+-monoʳ-≤ (hopDt f)
                       (*-monoʳ-≤ (pm f) (⊔-lub ha (h (here refl)))))
  foldB-mem f a (w ∷ ws) {B = B} hp ha h (there p) =
    ≤-trans (foldB-mem f (evalTm f a w) ws hp step
               (λ q → ≤-trans (h (there q)) (iter-base (hopDt f) 1 B hp)) p)
            (≤-reflexive (iter-shift (hopDt f) (pm f) (length ws) B))
    where
      step : hopDv (evalTm f a w) ≤ hopDt f + pm f * B
      step = ≤-trans (evalTm-hop f a w)
                     (+-monoʳ-≤ (hopDt f)
                       (*-monoʳ-≤ (pm f) (⊔-lub ha (h (here refl)))))

  foldB-memH : ∀ f a ws {u D} → 1 ≤ ph f →
               Hv a ≤ D → (∀ {x} → x ∈ ws → Hv x ≤ D) →
               u ∈ foldB f a ws →
               Hv u ≤ iter (Ht f) (ph f) (length ws) D
  foldB-memH f a (w ∷ ws) {D = D} hp ha h (here refl) =
    ≤-trans step (iter-mono-k (Ht f) D {k = length (w ∷ ws)} hp (s≤s z≤n))
    where
      step : Hv (evalTm f a w) ≤ iter (Ht f) (ph f) 1 D
      step = ≤-trans (evalTm-wid f a w)
                     (+-monoʳ-≤ (Ht f)
                       (*-monoʳ-≤ (ph f) (⊔-lub ha (h (here refl)))))
  foldB-memH f a (w ∷ ws) {D = D} hp ha h (there p) =
    ≤-trans (foldB-memH f (evalTm f a w) ws hp step
               (λ q → ≤-trans (h (there q)) (iter-base (Ht f) 1 D hp)) p)
            (≤-reflexive (iter-shift (Ht f) (ph f) (length ws) D))
    where
      step : Hv (evalTm f a w) ≤ Ht f + ph f * D
      step = ≤-trans (evalTm-wid f a w)
                     (+-monoʳ-≤ (Ht f)
                       (*-monoʳ-≤ (ph f) (⊔-lub ha (h (here refl)))))

  hopD-map-mono : ∀ f e → hopD e ≤ hopD (mapᵉ f e)
  hopD-map-mono f e = ≤-trans (mul-ge _ (pm-pos f)) (m≤n+m _ _)

  hopD-scan-mono : ∀ f z e → hopD e ≤ hopD (scanᵉ f z e)
  hopD-scan-mono f z e =
    ≤-trans (m≤n⊔m _ _) (iter-base (hopDt f) (blE e) _ (pm-pos f))

------------------------------------------------------------------
-- THE OUTERMOST COMPONENT: unconnected slots.
------------------------------------------------------------------

memberℕ : ℕ → List ℕ → Bool
memberℕ i []       = false
memberℕ i (j ∷ js) = if i ≡ᵇ j then true else memberℕ i js

≡ᵇ-refl : ∀ i → (i ≡ᵇ i) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc i) = ≡ᵇ-refl i

idxs : ℕ → List ℕ
idxs zero    = []
idxs (suc n) = n ∷ idxs n

idxs-mem : ∀ n {i} → i < n → i ∈ idxs n
idxs-mem (suc n) i<sn with m<1+n⇒m<n∨m≡n i<sn
... | inj₁ i<n  = there (idxs-mem n i<n)
... | inj₂ refl = here refl

cnt : List ℕ → List ℕ → ℕ
cnt []       cs = 0
cnt (j ∷ js) cs = (if memberℕ j cs then 0 else 1) + cnt js cs

cnt-mono : ∀ js i cs → cnt js (i ∷ cs) ≤ cnt js cs
cnt-mono []       i cs = z≤n
cnt-mono (j ∷ js) i cs with j ≡ᵇ i
... | true  = ≤-trans (cnt-mono js i cs) (m≤n+m _ _)
... | false = +-monoʳ-≤ _ (cnt-mono js i cs)

cnt-drop : ∀ js i cs → i ∈ js → memberℕ i cs ≡ false →
           cnt js (i ∷ cs) < cnt js cs
cnt-drop (j ∷ js) i cs (here refl) nm
  rewrite ≡ᵇ-refl i | nm = s≤s (cnt-mono js i cs)
cnt-drop (j ∷ js) i cs (there p) nm with j ≡ᵇ i
... | true  = ≤-trans (cnt-drop js i cs p nm) (m≤n+m _ _)
... | false = ≤-trans (≤-reflexive (sym (+-suc _ _)))
                      (+-monoʳ-≤ _ (cnt-drop js i cs p nm))

------------------------------------------------------------------
-- THE LEX ORDER.  Three strict components, no carries between them —
-- which is why no second tower appears anywhere in this file.
------------------------------------------------------------------

Meas : Set
Meas = ℕ × ℕ × ℕ

_≺_ : Rel Meas 0ℓ
_≺_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)

≺-wf : WellFounded _≺_
≺-wf = ×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded)

dropU : ∀ {U₁ U₂ r₁ r₂ s₁ s₂} → U₁ < U₂ → (U₁ , r₁ , s₁) ≺ (U₂ , r₂ , s₂)
dropU u = inj₁ u

hopStep : ∀ {U₁ U₂ r₁ r₂ s₁ s₂} → U₁ ≤ U₂ → r₁ < r₂ →
          (U₁ , r₁ , s₁) ≺ (U₂ , r₂ , s₂)
hopStep u≤ r< with m≤n⇒m<n∨m≡n u≤
... | inj₁ u<   = inj₁ u<
... | inj₂ refl = inj₂ (refl , inj₁ r<)

descend : ∀ {U r₁ r₂ s₁ s₂} → r₁ ≤ r₂ → s₁ < s₂ →
          (U , r₁ , s₁) ≺ (U , r₂ , s₂)
descend r≤ s< with m≤n⇒m<n∨m≡n r≤
... | inj₁ r<   = inj₂ (refl , inj₁ r<)
... | inj₂ refl = inj₂ (refl , inj₂ (refl , s<))

------------------------------------------------------------------
-- THE EVALUATOR.
------------------------------------------------------------------

module Run (N : ℕ) (sl : List Exp) (η ν : ℕ → ℕ) where

  open M η ν public

  nth : ℕ → List Exp → Exp
  nth i       []       = ofᵉ []
  nth zero    (e ∷ _)  = e
  nth (suc i) (_ ∷ es) = nth i es

  def : ℕ → Exp
  def i = nth i sl

  unconn : List ℕ → ℕ
  unconn cs = cnt (idxs N) cs

  unconn-insert : ∀ i cs → i < N → memberℕ i cs ≡ false →
                  unconn (i ∷ cs) < unconn cs
  unconn-insert i cs i<N nm = cnt-drop (idxs N) i cs (idxs-mem N i<N) nm

  unconn-keeps : ∀ i cs → unconn (i ∷ cs) ≤ unconn cs
  unconn-keeps i cs = cnt-mono (idxs N) i cs

  data Dom  : Exp → List ℕ → Set
  data DomL : List Val → List ℕ → Set
  run  : ∀ e  cs → Dom  e  cs → List Val × List ℕ
  runL : ∀ vs cs → DomL vs cs → List Val × List ℕ

  data Dom where
    dOf    : ∀ {vs cs} → Dom (ofᵉ vs) cs
    dMap   : ∀ {f e cs} → Dom e cs → Dom (mapᵉ f e) cs
    dScan  : ∀ {f z e cs} → Dom e cs → Dom (scanᵉ f z e) cs
    dTake  : ∀ {n e cs} → Dom e cs → Dom (takeᵉ n e) cs
    dMu    : ∀ {b cs} → Dom (unfoldμ b) cs → Dom (μᵉ b) cs
    dRec   : ∀ {cs} → Dom recᵉ cs
    dDefer : ∀ {b cs} → Dom (deferᵉ b) cs
    dSlotC : ∀ {i cs} → memberℕ i cs ≡ true → Dom (slotᵉ i) cs
    dSlotX : ∀ {i cs} → N ≤ i → Dom (slotᵉ i) cs
    dSlotN : ∀ {i cs} → i < N → memberℕ i cs ≡ false →
             Dom (def i) (i ∷ cs) → Dom (slotᵉ i) cs
    dAll   : ∀ {e cs} (d : Dom e cs) →
             DomL (proj₁ (run e cs d)) (proj₂ (run e cs d)) →
             Dom (allᵉ e) cs

  data DomL where
    dLNil : ∀ {cs} → DomL [] cs
    dLNat : ∀ {n vs cs} → DomL vs cs → DomL (natᵛ n ∷ vs) cs
    dLObs : ∀ {o vs cs} (d : Dom o cs) →
            DomL vs (proj₂ (run o cs d)) → DomL (obsᵛ o ∷ vs) cs

  run (ofᵉ vs)      cs dOf            = vs , cs
  run (mapᵉ f e)    cs (dMap d)       =
    mapB f (proj₁ (run e cs d)) , proj₂ (run e cs d)
  run (scanᵉ f z e) cs (dScan d)      =
    foldB f z (proj₁ (run e cs d)) , proj₂ (run e cs d)
  run (takeᵉ n e)   cs (dTake d)      =
    takeN n (proj₁ (run e cs d)) , proj₂ (run e cs d)
  run (μᵉ b)        cs (dMu d)        = run (unfoldμ b) cs d
  run recᵉ          cs dRec           = [] , cs
  run (deferᵉ b)    cs dDefer         = [] , cs
  run (slotᵉ i)     cs (dSlotC _)     = [] , cs
  run (slotᵉ i)     cs (dSlotX _)     = [] , cs
  run (slotᵉ i)     cs (dSlotN _ _ d) = run (def i) (i ∷ cs) d
  run (allᵉ e)      cs (dAll d ds)    =
    runL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds

  runL []             cs dLNil        = [] , cs
  runL (natᵛ n ∷ vs)  cs (dLNat ds)   = runL vs cs ds
  runL (obsᵛ o ∷ vs)  cs (dLObs d ds) =
    proj₁ (run o cs d) ++ proj₁ (runL vs (proj₂ (run o cs d)) ds)
      , proj₂ (runL vs (proj₂ (run o cs d)) ds)

  ----------------------------------------------------------------
  -- A RUN ONLY CONNECTS.
  ----------------------------------------------------------------

  run-unconn  : ∀ e cs (d : Dom e cs) → unconn (proj₂ (run e cs d)) ≤ unconn cs
  runL-unconn : ∀ vs cs (ds : DomL vs cs) →
                unconn (proj₂ (runL vs cs ds)) ≤ unconn cs

  run-unconn (ofᵉ vs)      cs dOf            = ≤-refl
  run-unconn (mapᵉ f e)    cs (dMap d)       = run-unconn e cs d
  run-unconn (scanᵉ f z e) cs (dScan d)      = run-unconn e cs d
  run-unconn (takeᵉ n e)   cs (dTake d)      = run-unconn e cs d
  run-unconn (μᵉ b)        cs (dMu d)        = run-unconn (unfoldμ b) cs d
  run-unconn recᵉ          cs dRec           = ≤-refl
  run-unconn (deferᵉ b)    cs dDefer         = ≤-refl
  run-unconn (slotᵉ i)     cs (dSlotC _)     = ≤-refl
  run-unconn (slotᵉ i)     cs (dSlotX _)     = ≤-refl
  run-unconn (slotᵉ i)     cs (dSlotN _ _ d) =
    ≤-trans (run-unconn (def i) (i ∷ cs) d) (unconn-keeps i cs)
  run-unconn (allᵉ e)      cs (dAll d ds)    =
    ≤-trans (runL-unconn (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds)
            (run-unconn e cs d)

  runL-unconn []            cs dLNil        = ≤-refl
  runL-unconn (natᵛ n ∷ vs) cs (dLNat ds)   = runL-unconn vs cs ds
  runL-unconn (obsᵛ o ∷ vs) cs (dLObs d ds) =
    ≤-trans (runL-unconn vs (proj₂ (run o cs d)) ds) (run-unconn o cs d)

  ----------------------------------------------------------------
  -- THE INVARIANTS.  Three of them, and every one quantifies over the
  -- ACTUAL burst — the syntactic quantity only has to dominate it.
  ----------------------------------------------------------------

  module _ (η-fix  : ∀ i → hopD (def i) ≤ η i)
           (bl-fix : ∀ i → blE (def i) ≤ ν i)
           (H-fix  : ∀ i → H (def i) ≤ ν i) where

    emit-len  : ∀ e cs (d : Dom e cs) → length (proj₁ (run e cs d)) ≤ blE e
    emit-lenL : ∀ vs cs (ds : DomL vs cs) {D} →
                (∀ {u} → u ∈ vs → Hv u ≤ D) →
                length (proj₁ (runL vs cs ds)) ≤ length vs * D
    emit-H    : ∀ e cs (d : Dom e cs) {v} →
                v ∈ proj₁ (run e cs d) → Hv v ≤ H e
    emit-HL   : ∀ vs cs (ds : DomL vs cs) {w D} →
                (∀ {u} → u ∈ vs → Hv u ≤ D) →
                w ∈ proj₁ (runL vs cs ds) → Hv w ≤ D

    emit-len (ofᵉ vs)      cs dOf       = ≤-refl
    emit-len (mapᵉ f e)    cs (dMap d)  =
      ≤-trans (≤-reflexive (mapB-length f (proj₁ (run e cs d))))
              (emit-len e cs d)
    emit-len (scanᵉ f z e) cs (dScan d) =
      ≤-trans (≤-reflexive (foldB-length f z (proj₁ (run e cs d))))
              (emit-len e cs d)
    emit-len (takeᵉ n e) cs (dTake d) =
      ≤-trans (takeN-length n (proj₁ (run e cs d))) (emit-len e cs d)
    emit-len (μᵉ b) cs (dMu d) =
      ≤-trans (emit-len (unfoldμ b) cs d)
              (≤-reflexive (blE-subst b (μᵉ b)))
    emit-len recᵉ          cs dRec            = z≤n
    emit-len (deferᵉ b)    cs dDefer          = z≤n
    emit-len (slotᵉ i)     cs (dSlotC _)      = z≤n
    emit-len (slotᵉ i)     cs (dSlotX _)      = z≤n
    emit-len (slotᵉ i)     cs (dSlotN _ _ d)  =
      ≤-trans (emit-len (def i) (i ∷ cs) d) (bl-fix i)
    emit-len (allᵉ e) cs (dAll d ds) =
      ≤-trans (emit-lenL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds
                 (λ p → emit-H e cs d p))
              (*-monoˡ-≤ (H e) (emit-len e cs d))

    emit-lenL []            cs dLNil      h = z≤n
    emit-lenL (natᵛ n ∷ vs) cs (dLNat ds) h =
      ≤-trans (emit-lenL vs cs ds (λ p → h (there p))) (m≤n+m _ _)
    emit-lenL (obsᵛ o ∷ vs) cs (dLObs d ds) h =
      ≤-trans (≤-reflexive (length-++ (proj₁ (run o cs d))))
              (+-mono-≤ head-bound
                        (emit-lenL vs (proj₂ (run o cs d)) ds
                                   (λ p → h (there p))))
      where
        head-bound : length (proj₁ (run o cs d)) ≤ _
        head-bound = ≤-trans (emit-len o cs d)
                             (≤-trans (m≤m⊔n (blE o) (H o)) (h (here refl)))

    emit-H (ofᵉ vs)   cs dOf      mem = Hl-mem vs mem
    emit-H (mapᵉ f e) cs (dMap d) mem =
      mapB-memH f (proj₁ (run e cs d)) (λ p → emit-H e cs d p) mem
    emit-H (scanᵉ f z e) cs (dScan d) mem =
      ≤-trans (foldB-memH f z (proj₁ (run e cs d)) (ph-pos f)
                 (m≤m⊔n _ _)
                 (λ p → ≤-trans (emit-H e cs d p) (m≤n⊔m _ _))
                 mem)
              (iter-mono-k (Ht f) _ (ph-pos f) (emit-len e cs d))
    emit-H (takeᵉ n e) cs (dTake d) mem =
      emit-H e cs d (takeN-∈ n (proj₁ (run e cs d)) mem)
    emit-H (μᵉ b) cs (dMu d) mem =
      ≤-trans (emit-H (unfoldμ b) cs d mem)
              (≤-reflexive (H-subst b (μᵉ b)))
    emit-H recᵉ          cs dRec           ()
    emit-H (deferᵉ b)    cs dDefer         ()
    emit-H (slotᵉ i)     cs (dSlotC _)     ()
    emit-H (slotᵉ i)     cs (dSlotX _)     ()
    emit-H (slotᵉ i)     cs (dSlotN _ _ d) mem =
      ≤-trans (emit-H (def i) (i ∷ cs) d mem) (H-fix i)
    emit-H (allᵉ e) cs (dAll d ds) mem =
      emit-HL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds
              (λ p → emit-H e cs d p) mem

    emit-HL []             cs dLNil        h ()
    emit-HL (natᵛ n ∷ vs)  cs (dLNat ds)   h mem =
      emit-HL vs cs ds (λ p → h (there p)) mem
    emit-HL (obsᵛ o ∷ vs)  cs (dLObs d ds) h mem
      with ++⁻ (proj₁ (run o cs d)) mem
    ... | inj₁ p = ≤-trans (emit-H o cs d p)
                           (≤-trans (m≤n⊔m (blE o) (H o)) (h (here refl)))
    ... | inj₂ q = emit-HL vs (proj₂ (run o cs d)) ds (λ r → h (there r)) q

    ----------------------------------------------------------------
    -- THE DEPTH INVARIANT.  Same statement as `Spike.Total`'s, now
    -- with a `scanᵉ` clause whose only extra ingredient is `emit-len`.
    ----------------------------------------------------------------

    emit-hop  : ∀ e cs (d : Dom e cs) {v} →
                v ∈ proj₁ (run e cs d) → hopDv v ≤ hopD e
    emit-hopL : ∀ vs cs (ds : DomL vs cs) {w B} →
                (∀ {u} → u ∈ vs → hopDv u ≤ B) →
                w ∈ proj₁ (runL vs cs ds) → hopDv w ≤ B

    emit-hop (ofᵉ vs)   cs dOf      mem = hopDl-mem vs mem
    emit-hop (mapᵉ f e) cs (dMap d) mem =
      mapB-mem f (proj₁ (run e cs d)) (λ p → emit-hop e cs d p) mem
    emit-hop (scanᵉ f z e) cs (dScan d) mem =
      ≤-trans (foldB-mem f z (proj₁ (run e cs d)) (pm-pos f)
                 (m≤m⊔n _ _)
                 (λ p → ≤-trans (emit-hop e cs d p) (m≤n⊔m _ _))
                 mem)
              (iter-mono-k (hopDt f) _ (pm-pos f) (emit-len e cs d))
    emit-hop (takeᵉ n e) cs (dTake d) mem =
      emit-hop e cs d (takeN-∈ n (proj₁ (run e cs d)) mem)
    emit-hop (μᵉ b) cs (dMu d) mem =
      ≤-trans (emit-hop (unfoldμ b) cs d mem)
              (≤-reflexive (hopD-subst b (μᵉ b)))
    emit-hop recᵉ          cs dRec           ()
    emit-hop (deferᵉ b)    cs dDefer         ()
    emit-hop (slotᵉ i)     cs (dSlotC _)     ()
    emit-hop (slotᵉ i)     cs (dSlotX _)     ()
    emit-hop (slotᵉ i)     cs (dSlotN _ _ d) mem =
      ≤-trans (emit-hop (def i) (i ∷ cs) d mem) (η-fix i)
    emit-hop (allᵉ e) cs (dAll d ds) mem =
      ≤-trans (emit-hopL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds
                (λ p → emit-hop e cs d p) mem)
              (n≤1+n (hopD e))

    emit-hopL []             cs dLNil        h ()
    emit-hopL (natᵛ n ∷ vs)  cs (dLNat ds)   h mem =
      emit-hopL vs cs ds (λ p → h (there p)) mem
    emit-hopL (obsᵛ o ∷ vs)  cs (dLObs d ds) h mem
      with ++⁻ (proj₁ (run o cs d)) mem
    ... | inj₁ p = ≤-trans (emit-hop o cs d p) (h (here refl))
    ... | inj₂ q = emit-hopL vs (proj₂ (run o cs d)) ds (λ r → h (there r)) q

    ----------------------------------------------------------------
    -- TOTALITY.  Nothing here computes a budget.
    ----------------------------------------------------------------

    meas : Exp → List ℕ → Meas
    meas e cs = unconn cs , hopD e , syncSize e

    totalL : ∀ vs cs (U R : ℕ) → unconn cs ≤ U →
             (∀ {u} → u ∈ vs → hopDv u ≤ R) →
             (∀ o cs′ → unconn cs′ ≤ U → hopD o ≤ R → Dom o cs′) →
             DomL vs cs
    totalL []             cs U R hU h rec = dLNil
    totalL (natᵛ n ∷ vs)  cs U R hU h rec =
      dLNat (totalL vs cs U R hU (λ p → h (there p)) rec)
    totalL (obsᵛ o ∷ vs)  cs U R hU h rec =
      dLObs d (totalL vs (proj₂ (run o cs d)) U R
                 (≤-trans (run-unconn o cs d) hU)
                 (λ p → h (there p)) rec)
      where d = rec o cs hU (h (here refl))

    total : ∀ e cs → Acc _≺_ (meas e cs) → Dom e cs
    total (ofᵉ vs)   cs a        = dOf
    total (mapᵉ f e) cs (acc rs) =
      dMap (total e cs (rs (descend (hopD-map-mono f e) ≤-refl)))
    total (scanᵉ f z e) cs (acc rs) =
      dScan (total e cs (rs (descend (hopD-scan-mono f z e) ≤-refl)))
    total (takeᵉ n e) cs (acc rs) =
      dTake (total e cs (rs (descend ≤-refl ≤-refl)))
    total (μᵉ b) cs (acc rs) =
      dMu (total (unfoldμ b) cs
             (rs (descend (≤-reflexive (hopD-subst b (μᵉ b)))
                          (s≤s (≤-reflexive (syncSize-subst b (μᵉ b)))))))
    total recᵉ       cs a = dRec
    total (deferᵉ b) cs a = dDefer
    total (slotᵉ i) cs (acc rs) with memberℕ i cs in mem
    ... | true  = dSlotC mem
    ... | false with i <? N
    ...   | yes i<N =
      dSlotN i<N mem
        (total (def i) (i ∷ cs) (rs (dropU (unconn-insert i cs i<N mem))))
    ...   | no  i≮N = dSlotX (≮⇒≥ i≮N)
    total (allᵉ e) cs (acc rs) =
      dAll d (totalL (proj₁ (run e cs d)) (proj₂ (run e cs d))
                (unconn cs) (hopD e)
                (run-unconn e cs d)
                (λ p → emit-hop e cs d p)
                (λ o cs′ hU hR → total o cs′ (rs (hopStep hU (s≤s hR)))))
      where d = total e cs (rs (descend (n≤1+n (hopD e)) ≤-refl))

    -- THE RESULT: the domain is everything, with `scanᵉ` in the
    -- language, on a lex order with no budget in it anywhere.
    total! : ∀ e cs → Dom e cs
    total! e cs = total e cs (≺-wf (meas e cs))

------------------------------------------------------------------
-- NON-VACUITY.  Two witnesses.
--
-- `witness` is `Spike.Total`'s: all four synchronous re-entry edges at
-- once, and the emitted `natᵛ 7` is reachable ONLY through the inner
-- hop.
--
-- `scan-witness` is the one this module exists for.  Its accumulator
-- REFOLDS: `nestᵗ accᵗ` wraps the previous accumulator in a fresh
-- `allᵉ` per arrival, so the burst's two values have hop depths 1 and
-- 2 while the program's own source is flat.  `allᵉ` then subscribes to
-- both, which is the edge the depth component has to pay for — and it
-- pays for it out of `blE`, which here is the literal length of the
-- source's value list.
------------------------------------------------------------------

module Demo where

  def0 : Exp
  def0 = ofᵉ (obsᵛ (ofᵉ (natᵛ 7 ∷ [])) ∷ [])

  open Run 1 (def0 ∷ []) (λ _ → 0) (λ _ → 1)

  η-fix0 : ∀ i → hopD (def i) ≤ 0
  η-fix0 zero    = z≤n
  η-fix0 (suc i) = z≤n

  bl-fix0 : ∀ i → blE (def i) ≤ 1
  bl-fix0 zero    = ≤-refl
  bl-fix0 (suc i) = z≤n

  H-fix0 : ∀ i → H (def i) ≤ 1
  H-fix0 zero    = ≤-refl
  H-fix0 (suc i) = z≤n

  prog : Exp
  prog = allᵉ (μᵉ (mapᵉ inᵗ (slotᵉ 0)))

  witness : Dom prog []
  witness = total! η-fix0 bl-fix0 H-fix0 prog []

  demo-burst : proj₁ (run prog [] witness) ≡ natᵛ 7 ∷ []
  demo-burst = refl

  demo-connected : proj₂ (run prog [] witness) ≡ 0 ∷ []
  demo-connected = refl

  -- the refold: two arrivals, two accumulators, hop depths 1 and 2
  seed : Val
  seed = obsᵛ (ofᵉ (natᵛ 5 ∷ []))

  scanInner : Exp
  scanInner = scanᵉ (nestᵗ accᵗ) seed (ofᵉ (natᵛ 1 ∷ natᵛ 2 ∷ []))

  scanProg : Exp
  scanProg = allᵉ scanInner

  scan-witness : Dom scanProg []
  scan-witness = total! η-fix0 bl-fix0 H-fix0 scanProg []

  scan-burst : proj₁ (run scanProg [] scan-witness) ≡ natᵛ 5 ∷ natᵛ 5 ∷ []
  scan-burst = refl

  -- LOAD-BEARING, and it is what stops the exponent being decoration:
  -- the clause's number is ATTAINED by an actual emission.  `blE` of
  -- the source is 2, the clause reads `iter 1 1 2 0 = 2`, and the
  -- second accumulator's own hop is 2.  At exponent 1 the clause would
  -- read 1 and `emit-hop` would be FALSE at this very program, so no
  -- smaller count survives.  (At exponent 0 it reads 0 and the FIRST
  -- accumulator already refutes it.)
  scan-bound : hopD scanInner ≡ 2
  scan-bound = refl

  scan-deepest : hopDl (proj₁ (run scanInner [] (dScan dOf))) ≡ 2
  scan-deepest = refl

  -- and the slope-2 template the multiplier is FOR: a value of hop
  -- depth 1 reaches two ADDED positions, so its image has depth 2
  dupProg : Exp
  dupProg = mapᵉ (dupᵗ inᵗ) (ofᵉ (obsᵛ (allᵉ (ofᵉ (natᵛ 3 ∷ []))) ∷ []))

  dup-slope : hopD dupProg ≡ 2
  dup-slope = refl

  -- LOAD-BEARING, and it is the one row that separates a slope
  -- EXPONENTIAL in the template's text from a merely multiplicative
  -- one.  `scnᵗ g t` plugs its argument into the SOURCE of an inner
  -- scan whose length the template itself writes down — two here — so
  -- the plug is transported by two steps of the recurrence and the
  -- slope is `pm g` SQUARED times `pm t`.  With `pm (dupᵗ inᵗ) = 2` and
  -- `pm inᵗ = 1` that reads 4, against the 2 a single step would give;
  -- a clause that composed the slopes ONCE would report 2 and be false
  -- at the image below.  The exponent is the source length, which is
  -- syntax and not a budget — no `V` reaches it.
  scnTm : Tm
  scnTm = scnᵗ (dupᵗ inᵗ) inᵗ

  scn-slope : pm scnTm ≡ 4
  scn-slope = refl

  scn-one-step : pm (dupᵗ inᵗ) * pm inᵗ ≡ 2
  scn-one-step = refl

  -- the image attains it: a plug of hop depth 1 lands at depth 4
  scnCarrier : Val
  scnCarrier = obsᵛ (allᵉ (ofᵉ (natᵛ 3 ∷ [])))

  scn-image : hopDv (evalTm scnTm scnCarrier scnCarrier) ≡ 4
  scn-image = refl

  -- `takeᵉ`.  Every measure passes it straight through, mirroring the
  -- real tree, where no depth or burst family reads the count at all.
  -- The order therefore gets nothing from it and pays nothing for it:
  -- the descent is on `syncSize` alone.
  --
  -- WHAT THE ROWS BUY, since a clause set that cannot fail is not a
  -- test.  `take-slack` is the pass-through made concrete — the source's
  -- deeper value is DROPPED and the clause reports its depth anyway, so
  -- the bound is sound and can never be tight.  `take-witness` puts the
  -- truncation UNDER the re-entry edge: the kept value is the one that
  -- connects a slot, the dropped one is deeper, and the burst and the
  -- connection set are both unchanged from the un-taken program.  That
  -- is the only way this constructor could have touched the order.
  shallowV : Val
  shallowV = obsᵛ (ofᵉ (natᵛ 1 ∷ []))

  deepV : Val
  deepV = obsᵛ (allᵉ (ofᵉ (natᵛ 2 ∷ [])))

  takeInner : Exp
  takeInner = takeᵉ 1 (ofᵉ (shallowV ∷ deepV ∷ []))

  take-drops : proj₁ (run takeInner [] (dTake dOf)) ≡ shallowV ∷ []
  take-drops = refl

  -- LOAD-BEARING: the clause reads 1, the emission reads 0.  A clause
  -- reading the TAKEN prefix would report 0 and still be sound here —
  -- which is exactly why the pass-through costs nothing and buys
  -- nothing.
  take-slack : hopD takeInner ≡ 1
  take-slack = refl

  take-actual : hopDl (proj₁ (run takeInner [] (dTake dOf))) ≡ 0
  take-actual = refl

  takeProg : Exp
  takeProg = allᵉ (takeᵉ 1 (ofᵉ (obsᵛ (μᵉ (mapᵉ inᵗ (slotᵉ 0))) ∷ deepV ∷ [])))

  take-witness : Dom takeProg []
  take-witness = total! η-fix0 bl-fix0 H-fix0 takeProg []

  take-burst : proj₁ (run takeProg [] take-witness)
             ≡ obsᵛ (ofᵉ (natᵛ 7 ∷ [])) ∷ []
  take-burst = refl

  take-connected : proj₂ (run takeProg [] take-witness) ≡ 0 ∷ []
  take-connected = refl
