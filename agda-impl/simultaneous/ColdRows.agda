{-# OPTIONS --guardedness #-}

-- THE ELABORATED COLD'S ROWS, written out.  The elaboration subscribed at
-- `P` runs the cold `J` four steps down, at `c₀`, through a concat with a
-- completion tag, a merge with the tick that closes the subscribe burst,
-- a scan marking every tag past the tick as late, and a render per tag.
-- What it lists is each of the cold's rows on itself, the plumbing's own
-- rows around it, and each tag's render beside it (`CRow`).
--
-- The scan's rows (`SRow`): the merge's and the concat's values, silent;
-- the tick and its lane's end; the cold's values, late past the subscribe
-- burst, and its skips; and the end.  An end in the subscribe burst frees
-- the completion tag at once, in the burst, and the merge ends at its own
-- end.  A later end hands its place to the tag, which ends the merge
-- after it, both in the end's instant.  The concat's own end is never
-- the last part, and neither is the merge's unless the cold ended in the
-- burst.
--
-- A tag's render (`Rend`) is subscribed one step down and ends there,
-- silent: an early value is shown at once; a late value and a late
-- completion mint a name, and the value sits between `begin` and `over`
-- under it.  The last part to end is the scan's, so the end is its end.
module simultaneous.ColdRows where

open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; does)

open import denotation.Position using (Pos; _≟ⁱ_; ix; last; _⊕_; root)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; _≼_)
open import denotation.Laws.Modulus using (≼-trans; ≺→≼; ≺-ext)
open import quickcheck.Tabled using (Row)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; begin; over; valuesOf)
open import simultaneous.SObs using (Tag; val; cdone; tick)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown)
open import simultaneous.TableCorr using (M; m-val; m-ee; m-ss)
open import simultaneous.TakeCut using (inst-⊕)

------------------------------------------------------------------------
-- A row's kind

data Kind : Set where
  kv ks ke : Kind

kind : ∀ {X : Set} → Ev X → Kind
kind (out _) = kv
kind skip    = ks
kind end     = ke
kind (pin _) = ks

module At {A : Set} (P : Pos) where

  IE : Set
  IE = InstEmit Pos A

  -- Where the concat is subscribed, and the cold.
  C₀ : Pos
  C₀ = P ⊕ (ix 0 ∷ ix 1 ∷ [])

  c₀ : Pos
  c₀ = P ⊕ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

  -- In the subscribe burst.
  sync : Pos → Bool
  sync y = does (instantOf y ≟ⁱ instantOf P)

  sync-in : ∀ {y} → sync y ≡ true → instantOf y ≡ instantOf P
  sync-in {y} e with instantOf y ≟ⁱ instantOf P
  sync-in {y} refl | yes i = i

  ------------------------------------------------------------------------
  -- Where each kind of row is shown

  σ : Kind → Bool → Pos → Pos
  σ kv true  y = y ⊕ (ix 1 ∷ ix 0 ∷ [])
  σ kv false y = y ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])
  σ ks _     y = y
  σ ke true  y = P ⊕ [ last ]
  σ ke false y = y ⊕ (ix 1 ∷ last ∷ [])

  im : ∀ {X : Set} → Pos → Ev X → Pos
  im y e = σ (kind e) (sync y) y

  ------------------------------------------------------------------------
  -- The rows

  -- The scan's.
  data SRow (J : List (Row A)) : Pos → Ev (Bool × Tag A) → Set where
    mv₀  : SRow J (P ⊕ (ix 0 ∷ ix 0 ∷ [])) skip
    mv₁  : SRow J (P ⊕ (ix 1 ∷ ix 0 ∷ [])) skip
    cv₀  : SRow J (C₀ ⊕ (ix 0 ∷ ix 0 ∷ [])) skip
    cv₁  : SRow J (C₀ ⊕ (ix 1 ∷ ix 0 ∷ [])) skip
    tk   : SRow J (P ⊕ (ix 1 ∷ ix 1 ∷ ix 0 ∷ [])) (out (true , tick))
    tke  : SRow J (P ⊕ (ix 1 ∷ ix 1 ∷ last ∷ [])) skip
    ce   : SRow J (C₀ ⊕ [ last ]) skip
    cval : ∀ {y a b} → (y , out a) ∈ J → not (sync y) ≡ b → SRow J y (out (b , val a))
    cskp : ∀ {y} → (y , skip) ∈ J → SRow J y skip
    se-c : ∀ {c} → (c , end) ∈ J → sync c ≡ true → SRow J c skip
    se-d : ∀ {c} → (c , end) ∈ J → sync c ≡ true → SRow J (C₀ ⊕ (ix 1 ∷ ix 1 ∷ ix 0 ∷ [])) (out (false , cdone))
    se-k : ∀ {c} → (c , end) ∈ J → sync c ≡ true → SRow J (C₀ ⊕ (ix 1 ∷ ix 1 ∷ last ∷ [])) skip
    se-e : ∀ {c} → (c , end) ∈ J → sync c ≡ true → SRow J (P ⊕ [ last ]) end
    ae-h : ∀ {c} → (c , end) ∈ J → sync c ≡ false → SRow J (c ⊕ [ ix 0 ]) skip
    ae-d : ∀ {c} → (c , end) ∈ J → sync c ≡ false → SRow J (c ⊕ (ix 1 ∷ ix 0 ∷ [])) (out (true , cdone))
    ae-e : ∀ {c} → (c , end) ∈ J → sync c ≡ false → SRow J (c ⊕ (ix 1 ∷ last ∷ [])) end
    me-p : (∀ {c} → (c , end) ∈ J → sync c ≡ false) → SRow J (P ⊕ [ last ]) skip

  -- A tag's render, for the tag at `q`.
  data Rend (q : Pos) : Bool × Tag A → Pos → Ev IE → Set where
    r-end : ∀ {x} → Rend q x (q ⊕ (ix 1 ∷ last ∷ [])) skip
    r-sv  : ∀ {a} → Rend q (false , val a) (q ⊕ (ix 1 ∷ ix 0 ∷ [])) (out (instEmit (value a) root))
    r-mn  : ∀ {a} → Rend q (true , val a) (q ⊕ (ix 1 ∷ ix 0 ∷ ix 0 ∷ [])) skip
    r-mv  : ∀ {a} → Rend q (true , val a) (q ⊕ (ix 1 ∷ ix 1 ∷ [])) skip
    r-mc  : Rend q (true , cdone) (q ⊕ (ix 1 ∷ ix 1 ∷ [])) skip
    r-ab  : ∀ {a} → Rend q (true , val a) (q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (q ⊕ [ ix 1 ])))
    r-av  : ∀ {a} → Rend q (true , val a) (q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])) (out (instEmit (value a) (q ⊕ [ ix 1 ])))
    r-ao  : ∀ {a} → Rend q (true , val a) (q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (q ⊕ [ ix 1 ])))
    r-ae  : ∀ {a} → Rend q (true , val a) (q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])) skip
    r-cb  : Rend q (true , cdone) (q ⊕ (ix 1 ∷ ix 0 ∷ [])) (out (instEmit (mark begin) (q ⊕ [ ix 1 ])))

  -- The elaboration's.
  data CRow (J : List (Row A)) : Pos → Ev IE → Set where
    c-skp  : ∀ {q} → SRow J q skip → CRow J q skip
    c-end  : ∀ {q} → SRow J q end → CRow J q end
    c-val  : ∀ {q x} → SRow J q (out x) → CRow J (q ⊕ [ ix 0 ]) skip
    c-lane : ∀ {q x k e} → SRow J q (out x) → Rend q x k e → CRow J k e

  ------------------------------------------------------------------------
  -- Each row in the subscribe burst's instant or a late row's

  Placed : List (Row A) → Pos → Set
  Placed J l = instantOf l ≡ instantOf P ⊎ Σ Pos λ y → Σ (Ev A) λ e → (y , e) ∈ J × sync y ≡ false × instantOf y ≡ instantOf l

  placed-⊕ : ∀ {J} q → Placed J q → ∀ ys → Placed J (q ⊕ ys)
  placed-⊕ q (inj₁ i) ys = inj₁ (trans (inst-⊕ q ys) i)
  placed-⊕ q (inj₂ (y , e , x , s , i)) ys = inj₂ (y , e , x , s , trans i (sym (inst-⊕ q ys)))

  placed-row : ∀ {J y e} → (y , e) ∈ J → Placed J y
  placed-row {y = y} {e = e} x with sync y in s
  ... | true  = inj₁ (sync-in {y} s)
  ... | false = inj₂ (y , e , x , s , refl)

  placed-P : ∀ {J} ys → Placed J (P ⊕ ys)
  placed-P ys = inj₁ (inst-⊕ P ys)

  placed-C : ∀ {J} ys → Placed J (C₀ ⊕ ys)
  placed-C ys = inj₁ (trans (inst-⊕ C₀ ys) (inst-⊕ P (ix 0 ∷ ix 1 ∷ [])))

  srow-placed : ∀ {J q e} → SRow J q e → Placed J q
  srow-placed mv₀        = placed-P _
  srow-placed mv₁        = placed-P _
  srow-placed cv₀        = placed-C _
  srow-placed cv₁        = placed-C _
  srow-placed tk         = placed-P _
  srow-placed tke        = placed-P _
  srow-placed ce         = placed-C _
  srow-placed (cval x _) = placed-row x
  srow-placed (cskp x)   = placed-row x
  srow-placed (se-c x _) = placed-row x
  srow-placed (se-d _ _) = placed-C _
  srow-placed (se-k _ _) = placed-C _
  srow-placed (se-e _ _) = placed-P _
  srow-placed (ae-h {c = c} x _) = placed-⊕ c (placed-row x) [ ix 0 ]
  srow-placed (ae-d {c = c} x _) = placed-⊕ c (placed-row x) (ix 1 ∷ ix 0 ∷ [])
  srow-placed (ae-e {c = c} x _) = placed-⊕ c (placed-row x) (ix 1 ∷ last ∷ [])
  srow-placed (me-p _)   = placed-P _

  rend-placed : ∀ {J x k e} q → Placed J q → Rend q x k e → Placed J k
  rend-placed q pq r-end = placed-⊕ q pq (ix 1 ∷ last ∷ [])
  rend-placed q pq r-sv  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ [])
  rend-placed q pq r-mn  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ ix 0 ∷ [])
  rend-placed q pq r-mv  = placed-⊕ q pq (ix 1 ∷ ix 1 ∷ [])
  rend-placed q pq r-mc  = placed-⊕ q pq (ix 1 ∷ ix 1 ∷ [])
  rend-placed q pq r-ab  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])
  rend-placed q pq r-av  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])
  rend-placed q pq r-ao  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])
  rend-placed q pq r-ae  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])
  rend-placed q pq r-cb  = placed-⊕ q pq (ix 1 ∷ ix 0 ∷ [])

  crow-placed : ∀ {J l e} → CRow J l e → Placed J l
  crow-placed (c-skp s)    = srow-placed s
  crow-placed (c-end s)    = srow-placed s
  crow-placed (c-val {q = q} s) = placed-⊕ q (srow-placed s) [ ix 0 ]
  crow-placed (c-lane {q = q} s r) = rend-placed q (srow-placed s) r

  ------------------------------------------------------------------------
  -- Each shown row is a cold row's image

  private
    not-f : ∀ {b} → not b ≡ false → b ≡ true
    not-f {true} _ = refl

    not-t : ∀ {b} → not b ≡ true → b ≡ false
    not-t {false} _ = refl

    mark-hid : ∀ {m} {n : Pos} → Shown (One valuesOf) (out (instEmit {Pos} {A} (mark m) n)) → ⊥
    mark-hid (_ , ())

    ke-at : ∀ c b → sync c ≡ b → σ ke b c ≡ im {A} c end
    ke-at c _ s = cong (λ b → σ ke b c) (sym s)

    kv-at : ∀ y {a : A} b → sync y ≡ b → σ kv b y ≡ im y (out a)
    kv-at y _ s = cong (λ b → σ kv b y) (sym s)

  crow-bwd : ∀ {J l e′} → CRow J l e′
           → (Σ Pos λ y → Σ (Ev A) λ e → (y , e) ∈ J × l ≡ im y e × M e e′)
           ⊎ ((Shown (One valuesOf) e′ → ⊥) × Placed J l)
  crow-bwd (c-skp s)                = inj₂ ((λ ()) , srow-placed s)
  crow-bwd (c-end (se-e {c = c} x s)) = inj₁ (c , end , x , ke-at c true s , m-ee)
  crow-bwd (c-end (ae-e {c = c} x s)) = inj₁ (c , end , x , ke-at c false s , m-ee)
  crow-bwd (c-val {q = q} s)        = inj₂ ((λ ()) , placed-⊕ q (srow-placed s) [ ix 0 ])
  crow-bwd (c-lane (cval {y = y} {a = a} x nb) r-sv) = inj₁ (y , out a , x , kv-at y {a} true (not-f nb) , m-val refl)
  crow-bwd (c-lane (cval {y = y} {a = a} x nb) r-av) = inj₁ (y , out a , x , kv-at y {a} false (not-t nb) , m-val refl)
  crow-bwd (c-lane s r-end)         = inj₂ ((λ ()) , crow-placed (c-lane s r-end))
  crow-bwd (c-lane s r-mn)          = inj₂ ((λ ()) , crow-placed (c-lane s r-mn))
  crow-bwd (c-lane s r-mv)          = inj₂ ((λ ()) , crow-placed (c-lane s r-mv))
  crow-bwd (c-lane s r-mc)          = inj₂ ((λ ()) , crow-placed (c-lane s r-mc))
  crow-bwd (c-lane s r-ae)          = inj₂ ((λ ()) , crow-placed (c-lane s r-ae))
  crow-bwd (c-lane {q = q} s r-ab)  = inj₂ (mark-hid {begin} {q ⊕ [ ix 1 ]} , crow-placed (c-lane s r-ab))
  crow-bwd (c-lane {q = q} s r-ao)  = inj₂ (mark-hid {over} {q ⊕ [ ix 1 ]} , crow-placed (c-lane s r-ao))
  crow-bwd (c-lane {q = q} s r-cb)  = inj₂ (mark-hid {begin} {q ⊕ [ ix 1 ]} , crow-placed (c-lane s r-cb))

  ------------------------------------------------------------------------
  -- Each cold row on its image

  crow-fwd : ∀ {J y e} → (∀ {k r} → (k , pin r) ∈ J → ⊥) → (y , e) ∈ J → Σ (Ev IE) λ e′ → CRow J (im y e) e′ × M e e′
  crow-fwd {y = y} {e = out a} _ x with sync y in s
  ... | true  = out (instEmit (value a) root) , c-lane (cval x (cong not s)) r-sv , m-val refl
  ... | false = out (instEmit (value a) (y ⊕ [ ix 1 ])) , c-lane (cval x (cong not s)) r-av , m-val refl
  crow-fwd {e = skip} _ x = skip , c-skp (cskp x) , m-ss {A}
  crow-fwd {y = y} {e = end} _ x with sync y in s
  ... | true  = end , c-end (se-e x s) , m-ee
  ... | false = end , c-end (ae-e x s) , m-ee
  crow-fwd {e = pin _} np x = ⊥-elim (np x)

  ------------------------------------------------------------------------
  -- No pin, and nothing before the subscription

  crow-pin : ∀ {J l r} → CRow J l (pin r) → ⊥
  crow-pin (c-lane _ ())

  private
    ≼-⊕ : ∀ x {l} ys → x ≼ (x ⊕ (l ∷ ys))
    ≼-⊕ x {l} ys = ≺→≼ {x} {x ⊕ (l ∷ ys)} (≺-ext x ys)

    P≼C : ∀ {l} ys → P ≼ (C₀ ⊕ (l ∷ ys))
    P≼C {l} ys = ≼-trans {P} {C₀} {C₀ ⊕ (l ∷ ys)} (≼-⊕ P {ix 0} (ix 1 ∷ [])) (≼-⊕ C₀ {l} ys)

  module _ {J : List (Row A)} (aft : ∀ {y e} → (y , e) ∈ J → P ≼ y) where

    srow-after : ∀ {q e} → SRow J q e → P ≼ q
    srow-after mv₀        = ≼-⊕ P {ix 0} (ix 0 ∷ [])
    srow-after mv₁        = ≼-⊕ P {ix 1} (ix 0 ∷ [])
    srow-after cv₀        = P≼C {ix 0} (ix 0 ∷ [])
    srow-after cv₁        = P≼C {ix 1} (ix 0 ∷ [])
    srow-after tk         = ≼-⊕ P {ix 1} (ix 1 ∷ ix 0 ∷ [])
    srow-after tke        = ≼-⊕ P {ix 1} (ix 1 ∷ last ∷ [])
    srow-after ce         = P≼C {last} []
    srow-after (cval x _) = aft x
    srow-after (cskp x)   = aft x
    srow-after (se-c x _) = aft x
    srow-after (se-d _ _) = P≼C {ix 1} (ix 1 ∷ ix 0 ∷ [])
    srow-after (se-k _ _) = P≼C {ix 1} (ix 1 ∷ last ∷ [])
    srow-after (se-e _ _) = ≼-⊕ P {last} []
    srow-after (ae-h {c = c} x _) = ≼-trans {P} {c} {c ⊕ [ ix 0 ]} (aft x) (≼-⊕ c {ix 0} [])
    srow-after (ae-d {c = c} x _) = ≼-trans {P} {c} {c ⊕ (ix 1 ∷ ix 0 ∷ [])} (aft x) (≼-⊕ c {ix 1} (ix 0 ∷ []))
    srow-after (ae-e {c = c} x _) = ≼-trans {P} {c} {c ⊕ (ix 1 ∷ last ∷ [])} (aft x) (≼-⊕ c {ix 1} (last ∷ []))
    srow-after (me-p _)   = ≼-⊕ P {last} []

    rend-after : ∀ {q x k e} → P ≼ q → Rend q x k e → P ≼ k
    rend-after {q = q} pq r-end = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ last ∷ [])} pq (≼-⊕ q {ix 1} (last ∷ []))
    rend-after {q = q} pq r-sv  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ []))
    rend-after {q = q} pq r-mn  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ ix 0 ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ ix 0 ∷ []))
    rend-after {q = q} pq r-mv  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 1 ∷ [])} pq (≼-⊕ q {ix 1} (ix 1 ∷ []))
    rend-after {q = q} pq r-mc  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 1 ∷ [])} pq (≼-⊕ q {ix 1} (ix 1 ∷ []))
    rend-after {q = q} pq r-ab  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ ix 1 ∷ ix 0 ∷ []))
    rend-after {q = q} pq r-av  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ ix 1 ∷ ix 1 ∷ []))
    rend-after {q = q} pq r-ao  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ ix 1 ∷ ix 2 ∷ []))
    rend-after {q = q} pq r-ae  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ ix 1 ∷ last ∷ []))
    rend-after {q = q} pq r-cb  = ≼-trans {P} {q} {q ⊕ (ix 1 ∷ ix 0 ∷ [])} pq (≼-⊕ q {ix 1} (ix 0 ∷ []))

    crow-after : ∀ {l e} → CRow J l e → P ≼ l
    crow-after (c-skp s)    = srow-after s
    crow-after (c-end s)    = srow-after s
    crow-after (c-val {q = q} s) = ≼-trans {P} {q} {q ⊕ [ ix 0 ]} (srow-after s) (≼-⊕ q {ix 0} [])
    crow-after (c-lane s r) = rend-after (srow-after s) r
