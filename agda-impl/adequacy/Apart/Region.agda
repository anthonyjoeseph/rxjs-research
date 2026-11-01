-- WHAT A NODE CAN STILL MAKE, AND WHAT KEEPS TWO APART.  Every mark
-- owes a REGION: the positions it, and whatever it ever subscribes,
-- can still key (`cn`, `tl`), an after it keys (`pt`), a joiner's live
-- subscription (`bk`), or the run in progress (`cl`).  Two regions are
-- SEPARATE when neither can key inside the other: fresh regions share
-- no position, an after lies outside every fresh region but at its own
-- root, a joiner was joined before every position a region holds, and
-- everything but the run is past the subtree the run is in.
module adequacy.Apart.Region where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import denotation.Events using (Pos; ix; last; _<ᵖ_; _≟ˡ_; <ᵖ-below; <ᵖ-irrefl; <ᵖ-split; <ᵖ-trans)
open import operation.Key using (Key; at; after; _<ᴷ_; at-<ᴷ; <ᴷ-trans; ≮ᴷ-trans; clash; after-past)
open import adequacy.Stamped using (Ix)
open import adequacy.Floor.Keys using (asym; at-after₀)
open import adequacy.Apart.Cone using (Cone; pre; cone-trans; cone-up; cone-low; cone-past)

------------------------------------------------------------------------
-- Keys

-- Below a position, its after is earlier.
after-in : ∀ p l ys → after (p ++ l ∷ ys) <ᴷ after p ≡ true
after-in []      l ys = refl
after-in (a ∷ p) l ys with a ≟ˡ a
... | yes _ rewrite <ᵖ-irrefl [ a ] = after-in p l ys
... | no ¬e = ⊥-elim (¬e refl)

-- No earlier than a position's after: past the position.
past-at : ∀ q y → at y <ᴷ after q ≡ false → q <ᵖ y ≡ true
past-at q y h with q <ᵖ y in e
... | true  = refl
... | false with <ᵖ-split y q e
...   | inj₁ yq   = ⊥-elim (clash (<ᴷ-trans (at y) (at q) (after q) (trans (at-<ᴷ y q) yq) (at-after₀ q)) h)
...   | inj₂ refl = ⊥-elim (clash (at-after₀ q) h)

-- No earlier than a position and outside its cone: past its after.
past-cone : ∀ q y → at y <ᴷ at q ≡ false → (Cone q y → ⊥) → at y <ᴷ after q ≡ false
past-cone q y h ne with <ᵖ-split q y (trans (sym (at-<ᴷ y q)) h)
... | inj₁ qy   = asym (after q) (at y) (cone-past q y qy ne)
... | inj₂ refl = ⊥-elim (ne (subst (Cone q) (++-identityʳ q) (pre [])))

self : ∀ q → Cone q q
self q = subst (Cone q) (++-identityʳ q) (pre [])

------------------------------------------------------------------------
-- Regions

data Rg : Set where
  cn : Pos → Rg
  tl : Pos → ℕ → Rg
  pt : Pos → Rg
  bk : Pos → Rg
  cl : Pos → Rg

-- The positions a region can still make.
In : Rg → Pos → Set
In (cn r)   x = Cone r x
In (tl u i) x = (Σ ℕ λ j → i ≤ j × Cone (u ++ [ ix j ]) x) ⊎ Cone (u ++ [ last ]) x
In (pt _)   x = ⊥
In (bk _)   x = ⊥
In (cl _)   x = ⊥

-- An after at `y` clear of a region.
Out : Rg → Pos → Set
Out (cn r)   y = Cone r y → y ≡ r
Out (tl u i) y = In (tl u i) y → ⊥
Out (pt _)   y = ⊤
Out (bk _)   y = ⊤
Out (cl q)   y = (after y <ᴷ after q ≡ false) × (Cone q y → y ≡ q)

-- A joiner joined at `j` before a region.
Low : Pos → Rg → Set
Low j (cn r)   = ∀ y → In (cn r) y → j <ᵖ y ≡ true
Low j (tl u i) = ∀ y → In (tl u i) y → j <ᵖ y ≡ true
Low j (pt _)   = ⊤
Low j (bk j′)  = j ≡ j′ → ⊥
Low j (cl q)   = j <ᵖ q ≡ true

-- A region past the run at `q`'s subtree.
Far : Pos → Rg → Set
Far q (cn r)   = ∀ y → In (cn r) y → (at y <ᴷ after q ≡ false) × (Cone q y → ⊥)
Far q (tl u i) = ∀ y → In (tl u i) y → (at y <ᴷ after q ≡ false) × (Cone q y → ⊥)
Far q (pt y)   = Out (cl q) y
Far q (bk j)   = j <ᵖ q ≡ true
Far q (cl _)   = ⊤

Dis : Rg → Rg → Set
Dis A B = ∀ y → In A y → In B y → ⊥

-- `A` clear of `B`.
S : Rg → Rg → Set
S A (cn r)   = Dis A (cn r)
S A (tl u i) = Dis A (tl u i)
S A (pt y)   = Out A y
S A (bk j)   = Low j A
S A (cl q)   = Far q A

Sep : Rg → Rg → Set
Sep A B = S A B × S B A

sep-sym : ∀ {A B} → Sep A B → Sep B A
sep-sym (h , h′) = h′ , h

NoCl : Rg → Set
NoCl (cl _) = ⊥
NoCl _      = ⊤

-- Separate from whatever a region is separate from, the run aside.
Sub : Rg → Rg → Set
Sub x z = ∀ B → NoCl B → Sep z B → Sep x B

sub-refl : ∀ x → Sub x x
sub-refl x B _ h = h

------------------------------------------------------------------------
-- Fresh regions

data Fut : Rg → Set where
  f-cn : ∀ r → Fut (cn r)
  f-tl : ∀ u i → Fut (tl u i)

-- An after outside a fresh region is clear of it.
out-not : ∀ {B y} → Fut B → (In B y → ⊥) → Out B y
out-not (f-cn r)   ne c = ⊥-elim (ne c)
out-not (f-tl u i) ne   = ne

low-in : ∀ {B j} → Fut B → (∀ y → In B y → j <ᵖ y ≡ true) → Low j B
low-in (f-cn r)   h = h
low-in (f-tl u i) h = h

low-out : ∀ {B j} → Fut B → Low j B → ∀ y → In B y → j <ᵖ y ≡ true
low-out (f-cn r)   h = h
low-out (f-tl u i) h = h

far-in : ∀ {B q} → Fut B → (∀ y → In B y → (at y <ᴷ after q ≡ false) × (Cone q y → ⊥)) → Far q B
far-in (f-cn r)   h = h
far-in (f-tl u i) h = h

far-out : ∀ {B q} → Fut B → Far q B → ∀ y → In B y → (at y <ᴷ after q ≡ false) × (Cone q y → ⊥)
far-out (f-cn r)   h = h
far-out (f-tl u i) h = h

dis-in : ∀ {A B} → Fut B → Dis A B → S A B
dis-in (f-cn r)   h = h
dis-in (f-tl u i) h = h

dis-out : ∀ {A B} → Fut B → S A B → Dis A B
dis-out (f-cn r)   h = h
dis-out (f-tl u i) h = h

-- Whatever is not fresh holds no position.
none : ∀ {B y} → (Fut B → ⊥) → In B y → ⊥
none {cn r}   nf _ = nf (f-cn r)
none {tl u i} nf _ = nf (f-tl u i)
none {pt _}   nf ()
none {bk _}   nf ()
none {cl _}   nf ()

data Kind (B : Rg) : Set where
  is-fut : Fut B → Kind B
  is-pt  : ∀ y → B ≡ pt y → Kind B
  is-bk  : ∀ j → B ≡ bk j → Kind B

kind : ∀ B → NoCl B → Kind B
kind (cn r)   _ = is-fut (f-cn r)
kind (tl u i) _ = is-fut (f-tl u i)
kind (pt y)   _ = is-pt y refl
kind (bk j)   _ = is-bk j refl
kind (cl _)   ()

------------------------------------------------------------------------
-- What a run's subtree holds

out-sub : ∀ {x p y} → Fut x → (∀ y → In x y → Cone p y) → Out x p → (Cone p y → y ≡ p) → Out x y
out-sub {y = y} (f-cn r)   inc op e c  = trans (e (inc y c)) (op (subst (Cone r) (e (inc y c)) c))
out-sub {y = y} (f-tl u i) inc op e iy = op (subst (In (tl u i)) (e (inc y iy)) iy)

-- A fresh region inside the run's subtree, the run's own root clear.
sub-cl : ∀ {x p} → Ix p → Fut x → (∀ y → In x y → Cone p y) → Out x p → Sub x (cl p)
sub-cl {x} {p} hp fx inc op B nb (_ , fb) with kind B nb
... | is-fut fB = dis-in fB (λ y ix iB → proj₂ (far-out fB fb y iB) (inc y ix))
                , dis-in {B} {x} fx (λ y iB ix → proj₂ (far-out fB fb y iB) (inc y ix))
... | is-pt y refl = out-sub fx inc op (proj₂ fb) , dis-in fx (λ _ ())
... | is-bk j refl = low-in fx (λ y ix → cone-low j hp fb (inc y ix)) , dis-in fx (λ _ ())

-- An after inside the run's subtree.
sub-pt : ∀ {y p} → Cone p y → Sub (pt y) (cl p)
sub-pt {y} c B nb (_ , fb) with kind B nb
... | is-fut fB = dis-in fB (λ _ ()) , out-not fB (λ iB → proj₂ (far-out fB fb y iB) c)
... | is-pt z refl = tt , tt
... | is-bk j refl = tt , tt

-- A joiner joined where the run is.
sub-bk : ∀ {p} → Sub (bk p) (cl p)
sub-bk {p} B nb (_ , fb) with kind B nb
... | is-fut fB = dis-in fB (λ _ ()) , low-in fB (λ y iB → past-at p y (proj₁ (far-out fB fb y iB)))
... | is-pt z refl = tt , tt
... | is-bk j refl = (λ e → ⊥-elim (clash (subst (λ z → z <ᵖ p ≡ true) e fb) (<ᵖ-irrefl p)))
                   , (λ e → ⊥-elim (clash (subst (λ z → z <ᵖ p ≡ true) (sym e) fb) (<ᵖ-irrefl p)))

-- The run a level down.
sub-down : ∀ {p} l → Ix p → Sub (cl (p ++ [ l ])) (cl p)
sub-down {p} l hp B nb (_ , fb) with kind B nb
... | is-fut fB = dis-in fB (λ _ ()) , far-in fB (λ y iB → ≮ᴷ-trans (at y) (after p) (after (p ++ [ l ])) (proj₁ (far-out fB fb y iB)) (asym (after (p ++ [ l ])) (after p) (after-in p l []))
                                                , λ c → proj₂ (far-out fB fb y iB) (cone-trans (pre [ l ]) c))
... | is-pt y refl = out , out
  where
    out : Out (cl (p ++ [ l ])) y
    out = ≮ᴷ-trans (after y) (after p) (after (p ++ [ l ])) (proj₁ fb) (asym (after (p ++ [ l ])) (after p) (after-in p l []))
        , λ c → ⊥-elim (cone-up l [] (subst (Cone (p ++ [ l ])) (proj₂ fb (cone-trans (pre [ l ]) c)) c))
... | is-bk j refl = <ᵖ-trans j p (p ++ [ l ]) fb (<ᵖ-below p []) , <ᵖ-trans j p (p ++ [ l ]) fb (<ᵖ-below p [])

-- A fresh region inside another.
sub-fut : ∀ {x z} → Fut x → Fut z → (∀ y → In x y → In z y) → (∀ y → Out z y → Out x y) → Sub x z
sub-fut {x} {z} fx fz inc out B nb (h , h′) with kind B nb
... | is-fut fB = dis-in fB (λ y ix iB → dis-out fB h y (inc y ix) iB)
                , dis-in {B} fx (λ y iB ix → dis-out {B} fz h′ y iB (inc y ix))
... | is-pt y refl = out y h , dis-in fx (λ _ ())
... | is-bk j refl = low-in fx (λ y ix → low-out fz h y (inc y ix)) , dis-in fx (λ _ ())

-- An after at a position a fresh region holds.
sub-at : ∀ {y z} → Fut z → In z y → Sub (pt y) z
sub-at {y} fz iz B nb (h , h′) with kind B nb
... | is-fut fB = dis-in fB (λ _ ()) , out-not fB (λ iB → dis-out fB h y iz iB)
... | is-pt w refl = tt , tt
... | is-bk j refl = tt , tt

------------------------------------------------------------------------
-- The run begun at the least key

-- Every key a region makes no earlier than `h`.
Keyed : Key → Rg → Set
Keyed h (cn r)   = ∀ y → In (cn r) y → at y <ᴷ h ≡ false
Keyed h (tl u i) = ∀ y → In (tl u i) y → at y <ᴷ h ≡ false
Keyed h (pt y)   = after y <ᴷ h ≡ false
Keyed h (bk _)   = ⊤
Keyed h (cl _)   = ⊤

keyed-out : ∀ {B h} → Fut B → Keyed h B → ∀ y → In B y → at y <ᴷ h ≡ false
keyed-out (f-cn r)   k = k
keyed-out (f-tl u i) k = k

-- A fresh region whose least key runs at `q`, its subtree all
-- the region's: what was separate from it is past the run.
far-of : ∀ {R₀ q} → Ix q → Fut R₀ → (∀ y → Cone q y → In R₀ y) → (∀ y → Out R₀ y → Cone q y → y ≡ q)
       → ∀ B → NoCl B → Keyed (at q) B → Sep R₀ B → Sep (cl q) B
far-of {R₀} {q} hq f₀ inc oq B nb kb (h , h′) with kind B nb
... | is-fut fB = dis-in fB (λ _ ()) , far-in fB (λ y iB → past-cone q y (keyed-out fB kb y iB) (ne y iB) , ne y iB)
  where
    ne : ∀ y → In B y → Cone q y → ⊥
    ne y iB c = dis-out fB h y (inc y c) iB
... | is-pt y refl = out , out
  where
    eq : Cone q y → y ≡ q
    eq = oq y h
    out : Out (cl q) y
    out = after-past y q kb (λ z e → nil z (trans (sym e) (eq (subst (Cone q) (sym e) (pre z)))))
        , eq
      where
        nil : ∀ z → q ++ z ≡ q → z ≡ []
        nil []      _ = refl
        nil (l ∷ z) e = ⊥-elim (cone-up l z (subst (Cone (q ++ l ∷ z)) e (self (q ++ l ∷ z))))
... | is-bk j refl = low-out f₀ h q (inc q (self q)) , low-out f₀ h q (inc q (self q))
