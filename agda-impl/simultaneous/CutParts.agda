{-# OPTIONS --guardedness #-}

-- A COMPOUND'S CUT IS ITS OPERATOR OVER ITS PARTS' CUTS.  A merge's cut
-- is the join of its outer's cut and its lanes' (`merge-tr→`,
-- `merge-tr←`, and the switch's and exhaust's likewise), a connect's the connect of its source's and its body's
-- (`conn-tr→`, `conn-tr←`), a defer's its marker and its body's
-- (`defer-tr→`, `defer-tr←`).  Each is the listing's exactness read
-- against the parts' own tables as denotations (`simultaneous.ListTR`):
-- a listed table, truncated, holds the same rows.
module simultaneous.CutParts where

open import Data.Empty using (⊥)
open import Data.List using (_∷_; [_])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect; defer)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet; skip; Den; coldAt; Truncate; Ended; LaneOf; At; Superseded; module Joining; module Connecting; module ExhaustOn)
import denotation.EmissionSet as ES
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; bind; rows; short; _⊣_)
open import denotation.Laws.Modulus using (⟨_⟩; upto)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.Horizon using (Tag; module Cuts)
open import quickcheck.Tabled.Exact using (conn-exact; truncate-exact)
open import quickcheck.Tabled.Exact.Base using (Exactly; sound; complete; bind⁻)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv; Uncut)
open import simultaneous.TableKit using (TR)
open import simultaneous.ListTR using (self-exact; ent; laneD; merge-tr; sw-tr; ex-tr; bounded-tr)
open import simultaneous.HorizonTree using (Cut; srcL; bodyρ; bodyU)
open import simultaneous.HorizonJoin using (module MergeJ; module JoinJ; module CcJ)

------------------------------------------------------------------------
-- Tables

private
  tr-≡ : ∀ {X : Set} {m m′ : Maybe (Tb.Listed X)} → m ≡ m′ → ∀ {k e} → TR m k e → TR m′ k e
  tr-≡ refl r = r

  uncut-of : ∀ {X : Set} {m : Maybe (Tb.Listed X)} → Σ (Tb.Listed X) (λ x → m ≡ just x × Uncut x) → ∀ {l} → m ≡ just l → Uncut l
  uncut-of (_ , refl , u) refl = u

  ended-map : ∀ {X : Set} {t t′ : EmissionSet X} → (∀ {k e} → t k e → t′ k e) → ∀ {c} → Ended t c → Ended t′ c
  ended-map f (c₀ , x , cc) = c₀ , f x , cc

------------------------------------------------------------------------
-- Joins and connects over parts holding the same rows

-- An exhaust's cursor over two lane families holding the same rows.
cur-cong : ∀ {A B : Set} {L L′ : Pos → A → EmissionSet B} (o : EmissionSet A)
         → (∀ {q a k e} → L q a k e → L′ q a k e) → (∀ {q a k e} → L′ q a k e → L q a k e)
         → ∀ {q₁ q} → ExhaustOn.Cur L o q₁ q → ExhaustOn.Cur L′ o q₁ q
cur-cong o l→ l← (ExhaustOn.cur₀ x m)            = ExhaustOn.cur₀ x m
cur-cong o l→ l← (ExhaustOn.run c x l cq x₂ qq nx)   = ExhaustOn.run (cur-cong o l→ l← c) x (l→ l) cq x₂ qq nx
cur-cong o l→ l← (ExhaustOn.drop c x nd x₂ qq nx)    = ExhaustOn.drop (cur-cong o l→ l← c) x (λ l → nd (l← l)) x₂ qq nx

module JoinCong {A B : Set} {L L′ : Pos → A → EmissionSet B} {o o′ : EmissionSet A} {Over Over′ : Pos → Set}
  (Bg : EmissionSet B) (Runs Runs′ : Pos → Set) (Cut′ : Pos → Pos → Set) (Hand : Pos → Set)
  (l→ : ∀ {q a k e} → L q a k e → L′ q a k e) (l← : ∀ {q a k e} → L′ q a k e → L q a k e)
  (o→ : ∀ {k e} → o k e → o′ k e) (o← : ∀ {k e} → o′ k e → o k e)
  (ov→ : ∀ {c} → Over c → Over′ c) (ov← : ∀ {c} → Over′ c → Over c)
  (r→ : ∀ {q} → Runs q → Runs′ q) (r← : ∀ {q} → Runs′ q → Runs q) where

  private
    module J  = Joining L  o  Bg Over  Runs  Cut′ Hand
    module J′ = Joining L′ o′ Bg Over′ Runs′ Cut′ Hand

  done→ : ∀ {c} → J.Done c → J′.Done c
  done→ {c} (ov , ls) = ov→ ov , λ {q} {a} x r qc nc → ended-map {t = L q a} {t′ = L′ q a} (λ {k} {e} → l→ {q} {a} {k} {e}) {c} (ls {q} {a} (o← x) (r← r) qc nc)

  done← : ∀ {c} → J′.Done c → J.Done c
  done← {c} (ov , ls) = ov← ov , λ {q} {a} x r qc nc → ended-map {t = L′ q a} {t′ = L q a} (λ {k} {e} → l← {q} {a} {k} {e}) {c} (ls {q} {a} (o→ x) (r→ r) qc nc)

  to : ∀ {k e} → J.JoinT k e → J′.JoinT k e
  to (Joining.val x)                = Joining.val (o→ x)
  to (Joining.step x)               = Joining.step (o→ x)
  to (Joining.opin x)               = Joining.opin (o→ x)
  to (Joining.oend x d)             = Joining.oend (o→ x) (done→ d)
  to (Joining.opass x nd)           = Joining.opass (o→ x) (λ d → nd (done← d))
  to (Joining.lane x r l nc w)      = Joining.lane (o→ x) (r→ r) (l→ l) nc w
  to (Joining.lend x r l nc nh d)   = Joining.lend (o→ x) (r→ r) (l→ l) nc nh (done→ d)
  to (Joining.lpass x r l nc nh nd) = Joining.lpass (o→ x) (r→ r) (l→ l) nc nh (λ d → nd (done← d))
  to (Joining.hand x r l nc h)      = Joining.hand (o→ x) (r→ r) (l→ l) nc h
  to (Joining.left x r l nc ins)    = Joining.left (o→ x) (r→ r) (l→ l) nc ins
  to (Joining.run b w)              = Joining.run b w
  to (Joining.rend b nh d)          = Joining.rend b nh (done→ d)
  to (Joining.rpass b nh nd)        = Joining.rpass b nh (λ d → nd (done← d))
  to (Joining.rhand b h)            = Joining.rhand b h

  from : ∀ {k e} → J′.JoinT k e → J.JoinT k e
  from (Joining.val x)                = Joining.val (o← x)
  from (Joining.step x)               = Joining.step (o← x)
  from (Joining.opin x)               = Joining.opin (o← x)
  from (Joining.oend x d)             = Joining.oend (o← x) (done← d)
  from (Joining.opass x nd)           = Joining.opass (o← x) (λ d → nd (done→ d))
  from (Joining.lane x r l nc w)      = Joining.lane (o← x) (r← r) (l← l) nc w
  from (Joining.lend x r l nc nh d)   = Joining.lend (o← x) (r← r) (l← l) nc nh (done← d)
  from (Joining.lpass x r l nc nh nd) = Joining.lpass (o← x) (r← r) (l← l) nc nh (λ d → nd (done→ d))
  from (Joining.hand x r l nc h)      = Joining.hand (o← x) (r← r) (l← l) nc h
  from (Joining.left x r l nc ins)    = Joining.left (o← x) (r← r) (l← l) nc ins
  from (Joining.run b w)              = Joining.run b w
  from (Joining.rend b nh d)          = Joining.rend b nh (done← d)
  from (Joining.rpass b nh nd)        = Joining.rpass b nh (λ d → nd (done→ d))
  from (Joining.rhand b h)            = Joining.rhand b h

module ConnCong {A B : Set} (p : Pos) {σ σ′ : EmissionSet A} {β β′ : EmissionSet B}
  (s→ : ∀ {k e} → σ k e → σ′ k e) (s← : ∀ {k e} → σ′ k e → σ k e)
  (b→ : ∀ {k e} → β k e → β′ k e) (b← : ∀ {k e} → β′ k e → β k e) where

  private
    module C  = Connecting p σ  β
    module C′ = Connecting p σ′ β′

  to : ∀ {k e} → C.ConnT k e → C′.ConnT k e
  to (Connecting.body x)        = Connecting.body (b→ x)
  to (Connecting.burst x i)     = Connecting.burst (s→ x) i
  to (Connecting.echo x al u n) = Connecting.echo (s→ x) (λ y → al (b← y)) u n
  to (Connecting.kept x al n i) = Connecting.kept (s→ x) (λ y → al (b← y)) n i

  from : ∀ {k e} → C′.ConnT k e → C.ConnT k e
  from (Connecting.body x)        = Connecting.body (b← x)
  from (Connecting.burst x i)     = Connecting.burst (s← x) i
  from (Connecting.echo x al u n) = Connecting.echo (s← x) (λ y → al (b→ y)) u n
  from (Connecting.kept x al n i) = Connecting.kept (s← x) (λ y → al (b→ y)) n i

------------------------------------------------------------------------
-- A join's cut

module _ {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N : ℕ} where
  private
    Lt Lc : Pos → A → EmissionSet B
    Lt = LaneOf (laneD (3 + N) n f (ρ N))
    Lc = JoinJ.Lane (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) (λ _ _ → ⊤) (λ _ _ _ → ⊥) N

    -- A lane read off its listing, truncated, holds that listing's rows.
    lt→ : ∀ {q a k e} → Lt q a k e → Lc q a k e
    lt→ l = proj₁ (proj₁ l) , proj₂ l

    lt← : ∀ {q a k e} → Lc q a k e → Lt q a k e
    lt← {q} {a} l = ent (3 + N) n (f a) (uρ N) (q ⊕ [ ix 1 ]) (proj₁ l) , proj₂ l

    module Cg = JoinCong {L = Lt} {L′ = Lc}
      {o = Cut n s ρ p N} {o′ = Cut n s ρ p N} {Over = Ended (Cut n s ρ p N)} {Over′ = Ended (Cut n s ρ p N)}
      (λ _ _ → ⊥) (λ _ → ⊤) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) lt→ lt←
      (λ x → x) (λ x → x) (λ x → x) (λ x → x) (λ x → x) (λ x → x)

    module Cs = JoinCong {L = Lt} {L′ = Lc}
      {o = Cut n s ρ p N} {o′ = Cut n s ρ p N} {Over = Ended (Cut n s ρ p N)} {Over′ = Ended (Cut n s ρ p N)}
      (λ _ _ → ⊥) (λ _ → ⊤) (λ _ → ⊤) (Superseded (Cut n s ρ p N)) (λ _ → ⊥) lt→ lt←
      (λ x → x) (λ x → x) (λ x → x) (λ x → x) (λ x → x) (λ x → x)

    module Ce = JoinCong {L = Lt} {L′ = Lc}
      {o = Cut n s ρ p N} {o′ = Cut n s ρ p N} {Over = Ended (Cut n s ρ p N)} {Over′ = Ended (Cut n s ρ p N)}
      (λ _ _ → ⊥) (ExhaustOn.Run Lt (Cut n s ρ p N)) (ExhaustOn.Run Lc (Cut n s ρ p N)) (λ _ _ → ⊥) (λ _ → ⊥) lt→ lt←
      (λ x → x) (λ x → x) (λ x → x) (λ x → x)
      (cur-cong (Cut n s ρ p N) (λ {q} {a} {k} {e} → lt→ {q} {a} {k} {e}) (λ {q} {a} {k} {e} → lt← {q} {a} {k} {e}))
      (cur-cong (Cut n s ρ p N) (λ {q} {a} {k} {e} → lt← {q} {a} {k} {e}) (λ {q} {a} {k} {e} → lt→ {q} {a} {k} {e}))

  -- The switch: every lane runs, each cut where the next value arrives.
  SwJ : ℕ → EmissionSet B
  SwJ = JoinJ.Jc (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) (λ _ _ → ⊤) (λ N′ → Superseded (Cut n s ρ p N′))

  -- The exhaust: a lane runs when the last run has ended.
  ExJ : ℕ → EmissionSet B
  ExJ = JoinJ.Jc (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) (λ N′ → ExhaustOn.Run (At (λ a q → Cut n (f a) ρ q N′)) (Cut n s ρ p N′)) (λ _ _ _ → ⊥)

  sw-tr→ : ∀ {y e} → Cut n (flatMap switchᶠ f s) ρ p N y e → SwJ N y e
  sw-tr→ x = Cs.to (Equivalence.to (sw-tr (3 + N) n f s (uρ N) p) x)

  sw-tr← : ∀ {y e} → SwJ N y e → Cut n (flatMap switchᶠ f s) ρ p N y e
  sw-tr← j = Equivalence.from (sw-tr (3 + N) n f s (uρ N) p) (Cs.from j)

  ex-tr→ : ∀ {y e} → Cut n (flatMap exhaustᶠ f s) ρ p N y e → ExJ N y e
  ex-tr→ x = Ce.to (Equivalence.to (ex-tr (3 + N) n f s (uρ N) p) x)

  ex-tr← : ∀ {y e} → ExJ N y e → Cut n (flatMap exhaustᶠ f s) ρ p N y e
  ex-tr← j = Equivalence.from (ex-tr (3 + N) n f s (uρ N) p) (Ce.from j)

  merge-tr→ : ∀ {y e} → Cut n (flatMap (mergeᶠ nothing) f s) ρ p N y e → MergeJ.Jc (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) N y e
  merge-tr→ x = Cg.to (Equivalence.to (merge-tr (3 + N) n f s (uρ N) p) x)

  merge-tr← : ∀ {y e} → MergeJ.Jc (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) N y e → Cut n (flatMap (mergeᶠ nothing) f s) ρ p N y e
  merge-tr← j = Equivalence.from (merge-tr (3 + N) n f s (uρ N) p) (Cg.from j)

  -- The bounded merge: each lane read off its listing, as is.
  cc-tr→ : ∀ k {y e} → Cut n (flatMap (mergeᶠ (just k)) f s) ρ p N y e → CcJ.Jc k (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) N y e
  cc-tr→ k x = Equivalence.to (bounded-tr (3 + N) n k f s (uρ N) p) x

  cc-tr← : ∀ k {y e} → CcJ.Jc k (Cut n s ρ p) (λ a q → Cut n (f a) ρ q) N y e → Cut n (flatMap (mergeᶠ (just k)) f s) ρ p N y e
  cc-tr← k j = Equivalence.from (bounded-tr (3 + N) n k f s (uρ N) p) j

------------------------------------------------------------------------
-- A connect's cut

module _ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N : ℕ} where
  private
    -- The body's table, in the scope a source table's hot extends.
    BodyT : Tb.Listed A → EmissionSet B
    BodyT σl = TR (listC (3 + N) n b (hotOf σl ∷ ρ N) (p ⊕ [ ix 0 ]))

    -- The connect's join over the parts' tables, as the listing read them.
    module P (σl : Tb.Listed A) (βl : Tb.Listed B) (eσ : listC (3 + N) n s (ρ N) (p ⊕ [ ix 1 ]) ≡ just σl)
             (eβ : listC (3 + N) n b (hotOf σl ∷ ρ N) (p ⊕ [ ix 0 ]) ≡ just βl) where

      -- The source the listing read is the one the body's scope lists.
      σ≡ : srcL n s uρ p N ≡ σl
      σ≡ = just-injective (trans (sym (proj₁ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))))) eσ)

      uB : UncutEnv (hotOf σl ∷ ρ N)
      uB = subst (λ x → UncutEnv (hotOf x ∷ ρ N)) σ≡ (bodyU n s uρ p N)

      sD : Den A
      sD = coldAt (λ _ → TR (just σl))

      F : Den A → Den B
      F _ = coldAt (λ _ → TR (just βl))

      module Cg = ConnCong p {σ = ES.Connect.σ sD F p} {σ′ = Cut n s ρ (p ⊕ [ ix 1 ]) N}
        {β = ES.Connect.β sD F p} {β′ = Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N}
        (λ x → tr-≡ (sym eσ) (proj₁ x))
        (λ {k} {e} x → subst (λ m → Truncate (TR m) k e) eσ (ent (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]) x))
        (λ {k} {e} x → subst (λ σ → BodyT σ k e) (sym σ≡) (tr-≡ (sym eβ) (proj₁ x)))
        (λ {k} {e} x → subst (λ m → Truncate (TR m) k e) eβ (ent (3 + N) n b uB (p ⊕ [ ix 0 ]) (subst (λ σ → BodyT σ k e) σ≡ x)))

      exact : Exactly (Tb.connRows p σl βl) (ES.Connect.ConnT sD F p)
      exact = conn-exact sD F p σl βl (truncate-exact (self-exact refl)) (truncate-exact (self-exact refl))

  conn-tr→ : ∀ {y e} → Cut n (connect s b) ρ p N y e
           → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N) y e
  conn-tr→ (l , eq , r) with bind⁻ {m = listC (3 + N) n s (ρ N) (p ⊕ [ ix 1 ])} eq
  ... | (σl , eσ , e₁) with bind⁻ {m = listC (3 + N) n b (hotOf σl ∷ ρ N) (p ⊕ [ ix 0 ])} e₁
  ...   | (βl , eβ , refl) =
    P.Cg.to σl βl eσ eβ (sound (P.exact σl βl eσ eβ (uncut-of (listC-ok (3 + N) n (connect s b) (uρ N) p) eq)) r)

  conn-tr← : ∀ {y e} → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N) y e
           → Cut n (connect s b) ρ p N y e
  conn-tr← j with listC-ok (3 + N) n (connect s b) (uρ N) p
  ... | (l , eq , u) with bind⁻ {m = listC (3 + N) n s (ρ N) (p ⊕ [ ix 1 ])} eq
  ...   | (σl , eσ , e₁) with bind⁻ {m = listC (3 + N) n b (hotOf σl ∷ ρ N) (p ⊕ [ ix 0 ])} e₁
  ...     | (βl , eβ , refl) = _ , eq , complete (P.exact σl βl eσ eβ u) (P.Cg.from σl βl eσ eβ j)

------------------------------------------------------------------------
-- A defer's cut

-- A marker row, then a body's.
Marked : ∀ {A : Set} → Pos → EmissionSet A → EmissionSet A
Marked q t y e = (y ≡ q × e ≡ skip) ⊎ t y e

private
  mk-to : ∀ {A : Set} q {m : Maybe (Tb.Listed A)} {y e} → TR (bind m λ b → just (((q , skip) ∷ rows b) ⊣ short b)) y e → Marked q (TR m) y e
  mk-to q {just b}  (_ , refl , here refl) = inj₁ (refl , refl)
  mk-to q {just b}  (_ , refl , there x)   = inj₂ (b , refl , x)
  mk-to q {nothing} (_ , () , _)

  mk-from : ∀ {A : Set} q {m : Maybe (Tb.Listed A)} → Σ (Tb.Listed A) (λ L → m ≡ just L)
          → ∀ {y e} → Marked q (TR m) y e → TR (bind m λ b → just (((q , skip) ∷ rows b) ⊣ short b)) y e
  mk-from q (L , refl) (inj₁ (refl , refl)) = _ , refl , here refl
  mk-from q (L , refl) (inj₂ (_ , refl , x)) = _ , refl , there x

-- A marker leading no boundary moves nothing.
module MarkB {A : Set} (q : Pos) (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set) (B : Cuts.Bounded c Bd)
  (apart : ∀ {N b g} → Bd N b g → ¬ q ⊑ b) where

  private
    module B = Cuts.Bounded B

  bounded : Cuts.Bounded (λ N → Marked q (c N)) Bd
  bounded = record
    { gap = λ { bd (inj₁ (refl , refl)) → apart bd ; bd (inj₂ x) → B.gap bd x }
    ; held-in = B.held-in ; held-under = B.held-under
    ; fwd = λ {N} {k} cl {N′} le → ⟨ (λ {y} {e} yk →
          (λ { (inj₁ m) → inj₁ m ; (inj₂ x) → inj₂ (proj₁ (upto (B.fwd {N} {k} cl le) {y} {e} yk) x) })
        , (λ { (inj₁ m) → inj₁ m ; (inj₂ x) → inj₂ (proj₂ (upto (B.fwd {N} {k} cl le) {y} {e} yk) x) })) ⟩
    ; fwd-pin = λ {N} {r} {k} cl hc {N′} le {y} yk →
          (λ { (inj₁ (_ , ())) ; (inj₂ x) → inj₂ (proj₁ (B.fwd-pin {N} {r} {k} cl hc le yk) x) })
        , (λ { (inj₁ (_ , ())) ; (inj₂ x) → inj₂ (proj₂ (B.fwd-pin {N} {r} {k} cl hc le yk) x) }) }

module _ {Γ A} n (l : Later Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p where

  -- A DEFER'S TABLE is its marker, then its body's, one label down.
  defer-tr→ : ∀ {N y e} → Cut (suc n) (defer l) ρ p N y e → Marked (p ⊕ [ ix 0 ]) (Cut n (Later.force l) ρ (p ⊕ [ ix 1 ]) N) y e
  defer-tr→ {N} = mk-to (p ⊕ [ ix 0 ]) {m = listC (3 + N) n (Later.force l) (ρ N) (p ⊕ [ ix 1 ])}

  defer-tr← : ∀ {N y e} → Marked (p ⊕ [ ix 0 ]) (Cut n (Later.force l) ρ (p ⊕ [ ix 1 ]) N) y e → Cut (suc n) (defer l) ρ p N y e
  defer-tr← {N} = mk-from (p ⊕ [ ix 0 ]) {m = listC (3 + N) n (Later.force l) (ρ N) (p ⊕ [ ix 1 ])} (proj₁ ok , proj₁ (proj₂ ok))
    where ok = listC-ok (3 + N) n (Later.force l) (uρ N) (p ⊕ [ ix 1 ])
