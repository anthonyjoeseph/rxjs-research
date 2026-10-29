{-# OPTIONS --guardedness #-}

-- What exactness means, and the facts every operator's exactness reads a
-- listing's decisions back by: each boolean test the listing makes is its
-- emission set predicate, once the rows it reads are listed exactly.
module quickcheck.Tabled.Exact.Base where

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (T-≡)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; does; yes; no)

open import denotation.Events using (Pos; _<ᵖ_; _≟ᵖ_; ix; <ᵖ-trans; <ᵖ-irrefl)
open import denotation.EmissionSet using (out; skip; end; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Nth using (module Nths)
import denotation.EmissionSet as Tb
open import quickcheck.Tabled
  using (Row; Listed; rows; short; bind; concatMap; mapM; concatMapM; when; anyᵇ; allᵇ; endBy; endBefore; ends;
  properᵇ; values; lanes; pastRows; afterL; module Order)

------------------------------------------------------------------------
-- Exactness

record Exact {A : Set} (l : Listed A) (t : EmissionSet A) : Set where
  field
    sound    : ∀ {q e} → (q , e) ∈ rows l → t q e
    complete : ∀ {q e} → t q e → (q , e) ∈ rows l
open Exact public

Exactly : ∀ {A} → Listed A → EmissionSet A → Set
Exactly l t = short l ≡ false → Exact l t

------------------------------------------------------------------------
-- Booleans

fromT : ∀ {b} → T b → b ≡ true
fromT {true} _ = refl

fromNot : ∀ {b} → ¬ T b → b ≡ false
fromNot {true}  n = ⊥-elim (n tt)
fromNot {false} _ = refl

offT : ∀ {b} → b ≡ false → ¬ T b
offT refl ()

not-T : ∀ {b} → not b ≡ true → ¬ T b
not-T {true}  ()
not-T {false} _ ()

T-not : ∀ {b} → ¬ T b → not b ≡ true
T-not {true}  n = ⊥-elim (n tt)
T-not {false} _ = refl

∨-false : ∀ {a b} → a ∨ b ≡ false → a ≡ false × b ≡ false
∨-false {true}  ()
∨-false {false} e = refl , e

∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-true {true}  e = refl , e
∧-true {false} ()

∧-intro : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-intro refl e = e

-- A test that would hold had its predicate held.
off : ∀ {b} {P : Set} → (b ≡ true → P) → ¬ P → b ≡ false
off {true}  f n = ⊥-elim (n (f refl))
off {false} _ _ = refl

-- An implication, as a disjunction.
or-of : ∀ a {b} → (a ≡ true → b ≡ true) → not a ∨ b ≡ true
or-of true  f = f refl
or-of false f = refl

or-right : ∀ {a b} → a ≡ true → not a ∨ b ≡ true → b ≡ true
or-right refl e = e

≟-refl : ∀ q → does (q ≟ᵖ q) ≡ true
≟-refl q with q ≟ᵖ q
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

≟-true : ∀ {q′ q} → does (q′ ≟ᵖ q) ≡ true → q′ ≡ q
≟-true {q′} {q} e with q′ ≟ᵖ q
≟-true e  | yes eq = eq
≟-true () | no _

------------------------------------------------------------------------
-- Lists

any⁻ : ∀ {X : Set} {p : X → Bool} {xs} → anyᵇ p xs ≡ true → Σ X λ x → x ∈ xs × p x ≡ true
any⁻ {xs = []} ()
any⁻ {p = p} {x ∷ xs} e with p x in px
... | true  = x , here refl , px
... | false = let (y , m , py) = any⁻ {p = p} {xs} e in y , there m , py

any⁺ : ∀ {X : Set} {p : X → Bool} {xs x} → x ∈ xs → p x ≡ true → anyᵇ p xs ≡ true
any⁺ {p = p} {y ∷ xs} (here refl) e rewrite e = refl
any⁺ {p = p} {y ∷ xs} (there m) e with p y
... | true  = refl
... | false = any⁺ {p = p} m e

any-off : ∀ {X : Set} {p : X → Bool} {xs x} → anyᵇ p xs ≡ false → x ∈ xs → p x ≡ false
any-off {p = p} {x = x} e m with p x in px
... | true  = ⊥-elim (offT e (Equivalence.from T-≡ (any⁺ {p = p} m px)))
... | false = refl

all⁻ : ∀ {X : Set} {p : X → Bool} {xs x} → allᵇ p xs ≡ true → x ∈ xs → p x ≡ true
all⁻ {p = p} {y ∷ xs} e (here refl) = proj₁ (∧-true e)
all⁻ {p = p} {y ∷ xs} e (there m)   = all⁻ {p = p} (proj₂ (∧-true {p y} e)) m

all⁺ : ∀ {X : Set} {p : X → Bool} {xs} → (∀ {x} → x ∈ xs → p x ≡ true) → allᵇ p xs ≡ true
all⁺ {xs = []}         f = refl
all⁺ {p = p} {y ∷ xs} f = ∧-intro (f (here refl)) (all⁺ {p = p} (λ m → f (there m)))

single⁻ : ∀ {X : Set} {x y : X} → y ∈ [ x ] → y ≡ x
single⁻ (here e) = e
single⁻ (there ())

when⁻ : ∀ {X : Set} {b} {x y : X} → y ∈ when b x → b ≡ true × y ≡ x
when⁻ {b = true}  m = refl , single⁻ m
when⁻ {b = false} ()

when⁺ : ∀ {X : Set} {b} {x : X} → b ≡ true → x ∈ when b x
when⁺ refl = here refl

if⁻ : ∀ {X : Set} {b} {xs ys : List X} {x} → x ∈ (if b then xs else ys) → (b ≡ true × x ∈ xs) ⊎ (b ≡ false × x ∈ ys)
if⁻ {b = true}  m = inj₁ (refl , m)
if⁻ {b = false} m = inj₂ (refl , m)

if-t : ∀ {X : Set} {b} {xs ys : List X} {x} → b ≡ true → x ∈ xs → x ∈ (if b then xs else ys)
if-t refl m = m

if-f : ∀ {X : Set} {b} {xs ys : List X} {x} → b ≡ false → x ∈ ys → x ∈ (if b then xs else ys)
if-f refl m = m

cm⁻ : ∀ {X Y : Set} {f : X → List Y} {xs : List X} {y} → y ∈ concatMap f xs → Σ X λ x → x ∈ xs × y ∈ f x
cm⁻ {xs = []} ()
cm⁻ {f = f} {x ∷ xs} m with ∈-++⁻ (f x) m
... | inj₁ h = x , here refl , h
... | inj₂ h = let (z , zm , zh) = cm⁻ {f = f} {xs} h in z , there zm , zh

cm⁺ : ∀ {X Y : Set} {f : X → List Y} {xs : List X} {x y} → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
cm⁺ {f = f} {x ∷ xs} (here refl) h = ∈-++⁺ˡ h
cm⁺ {f = f} {x ∷ xs} (there m)   h = ∈-++⁺ʳ (f x) (cm⁺ {f = f} m h)

bind⁻ : ∀ {X Y : Set} {m : Maybe X} {k : X → Maybe Y} {y} → bind m k ≡ just y → Σ X λ x → m ≡ just x × k x ≡ just y
bind⁻ {m = just x} e = x , refl , e
bind⁻ {m = nothing} ()

mapM⁻ : ∀ {X Y : Set} {f : X → Maybe Y} {xs ys y} → mapM f xs ≡ just ys → y ∈ ys → Σ X λ x → x ∈ xs × f x ≡ just y
mapM⁻ {xs = []} refl ()
mapM⁻ {f = f} {x ∷ xs} e m with bind⁻ {m = f x} e
... | (y₀ , fx , e′) with bind⁻ {m = mapM f xs} e′
... | (ys₀ , rest , refl) with m
... | here refl = x , here refl , fx
... | there m′  = let (z , zm , fz) = mapM⁻ {f = f} rest m′ in z , there zm , fz

mapM⁺ : ∀ {X Y : Set} {f : X → Maybe Y} {xs ys x} → mapM f xs ≡ just ys → x ∈ xs → Σ Y λ y → y ∈ ys × f x ≡ just y
mapM⁺ {xs = []} _ ()
mapM⁺ {f = f} {x ∷ xs} e m with bind⁻ {m = f x} e
... | (y₀ , fx , e′) with bind⁻ {m = mapM f xs} e′
... | (ys₀ , rest , refl) with m
... | here refl = y₀ , here refl , fx
... | there m′  = let (z , zm , fz) = mapM⁺ {f = f} rest m′ in z , there zm , fz

cmM⁻ : ∀ {X Y : Set} {f : X → Maybe (List Y)} {xs ys y} → concatMapM f xs ≡ just ys → y ∈ ys
  → Σ X λ x → x ∈ xs × Σ (List Y) λ zs → f x ≡ just zs × y ∈ zs
cmM⁻ {xs = []} refl ()
cmM⁻ {f = f} {x ∷ xs} e m with bind⁻ {m = f x} e
... | (zs , fx , e′) with bind⁻ {m = concatMapM f xs} e′
... | (ws , rest , refl) with ∈-++⁻ zs m
... | inj₁ h = x , here refl , zs , fx , h
... | inj₂ h = let (w , wm , vs , fw , h′) = cmM⁻ {f = f} rest h in w , there wm , vs , fw , h′

cmM⁺ : ∀ {X Y : Set} {f : X → Maybe (List Y)} {xs ys x} → concatMapM f xs ≡ just ys → x ∈ xs
  → Σ (List Y) λ zs → f x ≡ just zs × (∀ {y} → y ∈ zs → y ∈ ys)
cmM⁺ {xs = []} _ ()
cmM⁺ {f = f} {x ∷ xs} e m with bind⁻ {m = f x} e
... | (zs , fx , e′) with bind⁻ {m = concatMapM f xs} e′
... | (ws , rest , refl) with m
... | here refl = zs , fx , ∈-++⁺ˡ
... | there m′  = let (vs , fv , k) = cmM⁺ {f = f} rest m′ in vs , fv , λ h → ∈-++⁺ʳ zs (k h)

------------------------------------------------------------------------
-- Rows

values⁻ : ∀ {A} {rs : List (Row A)} {q a} → (q , a) ∈ values rs → (q , out a) ∈ rs
values⁻ {rs = (k , out b) ∷ rs} (here refl) = here refl
values⁻ {rs = (k , out b) ∷ rs} (there m)   = there (values⁻ m)
values⁻ {rs = (k , skip) ∷ rs}  m           = there (values⁻ m)
values⁻ {rs = (k , end) ∷ rs}   m           = there (values⁻ m)

values⁺ : ∀ {A} {rs : List (Row A)} {q a} → (q , out a) ∈ rs → (q , a) ∈ values rs
values⁺ {rs = (k , out b) ∷ rs} (here refl) = here refl
values⁺ {rs = (k , out b) ∷ rs} (there m)   = there (values⁺ m)
values⁺ {rs = (k , skip) ∷ rs}  (here ())
values⁺ {rs = (k , skip) ∷ rs}  (there m)   = values⁺ m
values⁺ {rs = (k , end) ∷ rs}   (here ())
values⁺ {rs = (k , end) ∷ rs}   (there m)   = values⁺ m

ends⁻ : ∀ {A} {rs : List (Row A)} {c} → c ∈ ends rs → (c , end) ∈ rs
ends⁻ {rs = rs} m with cm⁻ {xs = rs} m
... | ((k , end) , rm , h) with when⁻ h
... | (_ , refl) = rm
ends⁻ {rs = rs} m | ((k , out _) , rm , ())
ends⁻ {rs = rs} m | ((k , skip) , rm , ())

ends⁺ : ∀ {A} {rs : List (Row A)} {c} → (c , end) ∈ rs → c ∈ ends rs
ends⁺ m = cm⁺ m (here refl)

endBy→ : ∀ {X : Set} {u : EmissionSet X} {l : Listed X} → Exact l u → ∀ {c} → endBy (rows l) c ≡ true → Σ Pos λ k → u k end × k ≼ c
endBy→ {l = l} ex e with any⁻ {xs = rows l} e
... | ((k , end) , m , h)   = k , sound ex m , not-T h
... | ((k , out _) , m , ())
... | ((k , skip) , m , ())

→endBy : ∀ {X : Set} {u : EmissionSet X} {l : Listed X} → Exact l u → ∀ {k c} → u k end → k ≼ c → endBy (rows l) c ≡ true
→endBy ex x kc = any⁺ (complete ex x) (T-not kc)

endBefore→ : ∀ {X : Set} {u : EmissionSet X} {l : Listed X} → Exact l u → ∀ {q} → endBefore (rows l) q ≡ true → Σ Pos λ c → u c end × c ≺ q
endBefore→ {l = l} ex e with any⁻ {xs = rows l} e
... | ((c , end) , m , h)   = c , sound ex m , Equivalence.from T-≡ h
... | ((c , out _) , m , ())
... | ((c , skip) , m , ())

→endBefore : ∀ {X : Set} {u : EmissionSet X} {l : Listed X} → Exact l u → ∀ {c q} → u c end → c ≺ q → endBefore (rows l) q ≡ true
→endBefore ex x cq = any⁺ (complete ex x) (fromT cq)

-- `EmissionSet.Proper`'s test: at or before every end.
proper→ : ∀ {X : Set} {u : EmissionSet X} {l : Listed X} → Exact l u → ∀ {q} → properᵇ (rows l) q ≡ true → ∀ {c} → u c end → q ≼ c
proper→ ex e x = not-T (all⁻ e (complete ex x))

→proper : ∀ {X : Set} {u : EmissionSet X} {l : Listed X} → Exact l u → ∀ {q} → (∀ {c} → u c end → q ≼ c) → properᵇ (rows l) q ≡ true
→proper {l = l} ex h = all⁺ {xs = rows l} λ { {k , out _} m → refl ; {k , skip} m → refl ; {k , end} m → T-not (h (sound ex m)) }

-- Each value's lane, listed at its subscription, is exactly its lane.
lanes-from : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} {D : A → Pos → EmissionSet B} {vs ls}
  → (∀ {a s l} → ln a s ≡ just l → Exactly l (D a s)) → lanes ln vs ≡ just ls
  → ∀ {q a l} → (q , a , l) ∈ ls → (q , a) ∈ vs × Exactly l (D a (q ++ [ ix 1 ]))
lanes-from {ln = ln} {vs = vs} ih e m with mapM⁻ {xs = vs} e m
... | ((q′ , a′) , vm , fx) with bind⁻ {m = ln a′ (q′ ++ [ ix 1 ])} fx
... | (l′ , el′ , refl) = vm , ih el′

lanes-to : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} {vs ls} → lanes ln vs ≡ just ls
  → ∀ {q a} → (q , a) ∈ vs → Σ (Listed B) λ l → (q , a , l) ∈ ls
lanes-to {ln = ln} {vs = vs} e {q} {a} vm with mapM⁺ {xs = vs} e vm
... | (y , ym , fx) with bind⁻ {m = ln a (q ++ [ ix 1 ])} fx
... | (l′ , _ , refl) = l′ , ym

-- A lane listing read past its subscription lists the lane's rows past it.
pastRows⁻ : ∀ {A s k e} (rs : List (Row A)) → (k , e) ∈ pastRows s rs → (k , e) ∈ rs × s ≺ k
pastRows⁻ [] ()
pastRows⁻ {s = s} ((k′ , e′) ∷ rs) m with s <ᵖ k′ in h
pastRows⁻ ((k′ , e′) ∷ rs) (here refl) | true  = here refl , subst T (sym h) tt
pastRows⁻ ((k′ , e′) ∷ rs) (there m)   | true  = let (x , y) = pastRows⁻ rs m in there x , y
pastRows⁻ ((k′ , e′) ∷ rs) m           | false = let (x , y) = pastRows⁻ rs m in there x , y

pastRows⁺ : ∀ {A s k e} (rs : List (Row A)) → (k , e) ∈ rs → s ≺ k → (k , e) ∈ pastRows s rs
pastRows⁺ {s = s} ((k′ , e′) ∷ rs) m sk with s <ᵖ k′ in h
pastRows⁺ ((k′ , e′) ∷ rs) (here refl) sk | true  = here refl
pastRows⁺ ((k′ , e′) ∷ rs) (there m)   sk | true  = there (pastRows⁺ rs m sk)
pastRows⁺ ((k′ , e′) ∷ rs) (here refl) sk | false = ⊥-elim (subst T h sk)
pastRows⁺ ((k′ , e′) ∷ rs) (there m)   sk | false = pastRows⁺ rs m sk

afterL-exact : ∀ {A B : Set} {ln : A → Pos → Maybe (Listed B)} {D : A → Pos → EmissionSet B}
  → (∀ {a s l} → ln a s ≡ just l → Exactly l (D a s))
  → ∀ {a s l} → afterL ln a s ≡ just l → Exactly l (λ k e → D a s k e × s ≺ k)
afterL-exact {ln = ln} ih {a} {s} e with bind⁻ {m = ln a s} e
... | (l₀ , e₀ , refl) = λ u → record
  { sound    = λ m → let (x , y) = pastRows⁻ (rows l₀) m in sound (ih e₀ u) x , y
  ; complete = λ { (x , y) → pastRows⁺ (rows l₀) (complete (ih e₀ u) x) y } }

------------------------------------------------------------------------
-- Counting what lies before

-- The values before `q`: what bounds a chain of values ending at `q`.
cnt : ∀ {A : Set} → Pos → List (Pos × A) → ℕ
cnt q []             = 0
cnt q ((k , _) ∷ vs) = if k <ᵖ q then suc (cnt q vs) else cnt q vs

cnt≤ : ∀ {A : Set} {q} (vs : List (Pos × A)) → cnt q vs ≤ length vs
cnt≤ []             = z≤n
cnt≤ {q = q} ((k , _) ∷ vs) with k <ᵖ q
... | true  = s≤s (cnt≤ vs)
... | false = m≤n⇒m≤1+n (cnt≤ vs)

cnt-le : ∀ {A : Set} {q₀ q} (vs : List (Pos × A)) → q₀ <ᵖ q ≡ true → cnt q₀ vs ≤ cnt q vs
cnt-le []             _ = z≤n
cnt-le {q₀ = q₀} {q} ((k , _) ∷ vs) h with k <ᵖ q₀ in e₀ | k <ᵖ q in e₁
... | true  | true  = s≤s (cnt-le vs h)
... | true  | false with () ← trans (sym (<ᵖ-trans k q₀ q e₀ h)) e₁
... | false | true  = m≤n⇒m≤1+n (cnt-le vs h)
... | false | false = cnt-le vs h

-- A value before `q` is one more before it.
cnt-lt : ∀ {A : Set} {vs : List (Pos × A)} {q₀ a₀ q} → (q₀ , a₀) ∈ vs → q₀ <ᵖ q ≡ true → cnt q₀ vs < cnt q vs
cnt-lt {vs = (q₀ , _) ∷ vs} {q = q} (here refl) h rewrite <ᵖ-irrefl q₀ | h = s≤s (cnt-le vs h)
cnt-lt {vs = (k , _) ∷ vs} {q₀} {q = q} (there m) h with k <ᵖ q₀ in e₀ | k <ᵖ q in e₁
... | true  | true  = s≤s (cnt-lt m h)
... | true  | false with () ← trans (sym (<ᵖ-trans k q₀ q e₀ h)) e₁
... | false | true  = m≤n⇒m≤1+n (cnt-lt m h)
... | false | false = cnt-lt m h

-- A value is not before itself.
cnt-in : ∀ {A : Set} {vs : List (Pos × A)} {q a} → (q , a) ∈ vs → cnt q vs < length vs
cnt-in {vs = (q , _) ∷ vs} (here refl) rewrite <ᵖ-irrefl q = s≤s (cnt≤ vs)
cnt-in {vs = (k , _) ∷ vs} {q} (there m) with k <ᵖ q
... | true  = s≤s (cnt-in m)
... | false = m≤n⇒m≤1+n (cnt-in m)

------------------------------------------------------------------------
-- An input's values in order

-- `quickcheck.Tabled.Order`'s tests are `EmissionSet.Values`'s predicates.
module OrderX {A : Set} {t : EmissionSet A} {o : Listed A} (ex : Exact o t) where
  open Nths t using (nth-val)
  open Order (values (rows o)) using (minᵇ; nextᵇ; nths)
  open Tb.Values t using (Next; Nth; first; next)

  min→ : ∀ {q} → minᵇ q ≡ true → ∀ {k b} → t k (out b) → q ≼ k
  min→ e x = not-T (all⁻ e (values⁺ (complete ex x)))

  →min : ∀ {q} → (∀ {k b} → t k (out b) → q ≼ k) → minᵇ q ≡ true
  →min h = all⁺ {xs = values (rows o)} λ { {k , b} m → T-not (h (sound ex (values⁻ m))) }

  next→ : ∀ q q′ → nextᵇ q q′ ≡ true → q ≺ q′ × Next q q′
  next→ q q′ e with ∧-true {q <ᵖ q′} e
  ... | (lt , al) = Equivalence.from T-≡ lt , λ x qk → not-T (or-right (fromT qk) (all⁻ al (values⁺ (complete ex x))))

  →next : ∀ q q′ → q ≺ q′ → Next q q′ → nextᵇ q q′ ≡ true
  →next q q′ lt nx = ∧-intro (fromT lt) (all⁺ {xs = values (rows o)} λ { {k , b} m →
    or-of (q <ᵖ k) λ qk → T-not (nx (sound ex (values⁻ m)) (Equivalence.from T-≡ qk)) })

  nth-s : ∀ i {q a} → (q , a) ∈ nths i → Nth i q a
  nth-s zero m with cm⁻ {xs = values (rows o)} m
  ... | ((q , a) , vm , h) with when⁻ h
  ... | (mn , refl) = first (sound ex (values⁻ vm)) (min→ mn)
  nth-s (suc i) m with cm⁻ {xs = values (rows o)} m
  ... | ((q , a) , vm , h) with when⁻ h
  ... | (an , refl) with any⁻ {xs = nths i} an
  ... | ((q₀ , a₀) , pm , nx) = next (nth-s i pm) (sound ex (values⁻ vm)) (proj₁ (next→ q₀ q nx)) (proj₂ (next→ q₀ q nx))

  nth-c : ∀ {i q a} → Nth i q a → (q , a) ∈ nths i
  nth-c (first x mn)      = cm⁺ (values⁺ (complete ex x)) (when⁺ (→min mn))
  nth-c (next {q = q₀} {q′ = q′} N x lt nx) = cm⁺ (values⁺ (complete ex x)) (when⁺ (any⁺ (nth-c N) (→next q₀ q′ lt nx)))


  -- The i-th value has i values before it.
  nth-cnt : ∀ {i q a} → Nth i q a → i ≤ cnt q (values (rows o))
  nth-cnt (first x _)      = z≤n
  nth-cnt (next N x lt _) = ≤-trans (s≤s (nth-cnt N)) (cnt-lt (values⁺ (complete ex (nth-val N))) (fromT lt))
