{-# OPTIONS --guardedness #-}

-- WHAT IT IS FOR A SUBTERM'S CUTS TO CORRESPOND (`Rel`): the record
-- `simultaneous.TableRel.rel` builds former by former, and the tables'
-- rows (`TR`) and shapes (`Sh`) it is stated over.
module simultaneous.TableCorr where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Bool using (T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; few-ind; ≼-refl; ≺→≼; ≺-≼-≺; ≼-≺-≺; ≼-split)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Every; One; Reads; Match; Shown; Live)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- An event's value mapped, its constructor kept.
ev : ∀ {A B : Set} → (A → B) → Ev A → Ev B
ev f (out a) = out (f a)
ev f skip    = skip
ev f end     = end
ev f (pin r) = pin r

-- A run's shape: where its rows lie, and of what constructor.
Sh : ∀ {X : Set} → EmissionSet X → EmissionSet ⊤
Sh {X} a y e = Σ (Ev X) λ e₀ → a y e₀ × e ≡ ev (λ _ → tt) e₀

-- Agreement between runs carries to runs holding the same rows.
ag-≃ : ∀ {X : Set} {a a′ b b′ : EmissionSet X} {q}
     → (∀ {k e} → a k e → a′ k e) → (∀ {k e} → a′ k e → a k e) → (∀ {k e} → b k e → b′ k e) → (∀ {k e} → b′ k e → b k e)
     → AgreeTo q a b → AgreeTo q a′ b′
ag-≃ f f′ g g′ ⟨ a ⟩ = ⟨ (λ {y} {e} yq → (λ x → g (proj₁ (a {y} {e} yq) (f′ x))) , (λ x → f (proj₂ (a {y} {e} yq) (g′ x)))) ⟩

-- Two runs are truncated before they differ: agreeing below a value of
-- the first, the second holding a row at or past it, the second holds it.
Cons : ∀ {X : Set} → EmissionSet X → EmissionSet X → Set
Cons {X} a b = ∀ {y y′ e′} {v : X} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ a b) → a y (out v) → b y′ e′ → y ≼ y′ → b y (out v)

-- AGREEMENT BY INDUCTION ON ROWS: two runs with few rows below each
-- position agree up to `k` once they agree at each position up to it
-- that everything before agrees below.
ag-ind : ∀ {X : Set} {a b : EmissionSet X} {k} → (∀ q → Few (λ y e → a y e ⊎ b y e) q)
       → (∀ {y} → y ≼ k → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ a b) → ∀ {e} → (a y e → b y e) × (b y e → a y e))
       → AgreeTo k a b
ag-ind {X} {a} {b} {k} fin step = few-ind {t = λ y e → a y e ⊎ b y e} P go (fin k) (≼-refl {k})
  where
    P : Pos → Set
    P w = w ≼ k → AgreeTo w a b

    go : ∀ {w} → Few (λ y e → a y e ⊎ b y e) w → (∀ {v e} → a v e ⊎ b v e → v ≺ w → P v) → P w
    go {w} _ ih wk = ⟨ at ⟩
      where
        before : ∀ {y e} → y ≺ w → (a y e → b y e) × (b y e → a y e)
        before {y} lt = (λ x → proj₁ (upto (ih (inj₁ x) lt yk) (≼-refl {y})) x) , (λ x → proj₂ (upto (ih (inj₂ x) lt yk) (≼-refl {y})) x)
          where yk = ≺→≼ {y} {k} (≺-≼-≺ {y} {w} {k} lt wk)

        below : ∀ {y₀} → y₀ ≺ w → AgreeTo y₀ a b
        below {y₀} lt = ⟨ (λ {y} yy₀ → before (≼-≺-≺ {y} {y₀} {w} yy₀ lt)) ⟩

        at : ∀ {y e} → y ≼ w → (a y e → b y e) × (b y e → a y e)
        at {y} yw with ≼-split {y} {w} yw
        ... | inj₁ lt   = before lt
        ... | inj₂ refl = step wk below

private
  same-sh : ∀ {X : Set} (e e₀ : Ev X) → ev (λ _ → tt) e ≡ ev (λ _ → tt) e₀ → e ≡ e₀ ⊎ Σ X λ v → Σ X λ w → e ≡ out v × e₀ ≡ out w
  same-sh (out v) (out w) _    = inj₂ (v , w , refl , refl)
  same-sh skip    skip    _    = inj₁ refl
  same-sh end     end     _    = inj₁ refl
  same-sh (pin r) (pin .r) refl = inj₁ refl
  same-sh (out _) skip    ()
  same-sh (out _) end     ()
  same-sh (out _) (pin _) ()
  same-sh skip    (out _) ()
  same-sh skip    end     ()
  same-sh skip    (pin _) ()
  same-sh end     (out _) ()
  same-sh end     skip    ()
  same-sh end     (pin _) ()
  same-sh (pin _) (out _) ()
  same-sh (pin _) skip    ()
  same-sh (pin _) end     ()

  half : ∀ {X : Set} {a b : EmissionSet X} {k y} → Cons a b → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ a b) → AgreeTo k (Sh a) (Sh b)
       → y ≼ k → ∀ {e} → a y e → b y e
  half {y = y} cab below sh yk {e} x with proj₁ (upto sh yk) (e , x , refl)
  ... | e₀ , x′ , eq with same-sh e e₀ eq
  ...   | inj₁ refl = x′
  ...   | inj₂ (v , w , refl , refl) = cab below x x′ (≼-refl {y})

-- COHERENCE: two runs truncated before they differ, agreeing in shape,
-- agree outright: a value a truncation changes shows first as a row it
-- removes.
coh-of : ∀ {X : Set} {a b : EmissionSet X} {k} → (∀ q → Few (λ y e → a y e ⊎ b y e) q) → Cons a b → Cons b a
       → AgreeTo k (Sh a) (Sh b) → AgreeTo k a b
coh-of fin cab cba sh = ag-ind fin λ yk below → half cab below sh yk , half cba (λ lt → AgreeTo-sym (below lt)) (AgreeTo-sym sh) yk

-- Rows of a cut program's table.
Rows : ∀ {X : Set} → Tb.Listed X → Pos → Ev X → Set
Rows L k e = (k , e) ∈ rows L

-- A table there is.
Got : ∀ {X : Set} → Maybe (Tb.Listed X) → Set
Got {X} m = Σ (Tb.Listed X) λ L → m ≡ just L

-- A table read on is one.
got-bind : ∀ {X Y : Set} {m : Maybe (Tb.Listed X)} (g : Tb.Listed X → Tb.Listed Y) → Got m → Got (bind m λ l → just (g l))
got-bind g (L , refl) = g L , refl

-- Rows of a table, if there is one.
TR : ∀ {X : Set} → Maybe (Tb.Listed X) → EmissionSet X
TR {X} m k e = Σ (Tb.Listed X) λ L → m ≡ just L × Rows L k e

M : ∀ {A : Set} → Ev A → Ev (IE A) → Set
M = Match Every (One valuesOf) (Reads valuesOf)

-- A matched end is an end.
ends : ∀ {A : Set} {e : Ev A} → Unpinned e → M e end → e ≡ end
ends {e = out a} _ (c , _) with c tt
... | _ , () , _
ends {e = skip} _ (_ , d) = ⊥-elim (d (λ ()) tt)
ends {e = end} _ _ = refl

-- A shown elaborated value is matched by the value it reads.
m-back : ∀ {A : Set} {e : Ev A} {x : IE A} → Unpinned e → M e (out x) → Shown (One valuesOf) (out x)
       → Σ A λ a → e ≡ out a × valuesOf x ≡ a ∷ []
m-back {e = out a} _ (c , _) _ with c tt
... | _ , refl , rd = a , refl , rd
m-back {e = skip} _ (_ , d) sh = ⊥-elim (d (λ ()) sh)
m-back {e = end} _ (c , _) _ with c tt
... | ()

m-val : ∀ {A : Set} {a : A} {x : IE A} → valuesOf x ≡ a ∷ [] → M (out a) (out x)
m-val rd = (λ _ → _ , refl , rd) , (λ n → ⊥-elim (n tt))

m-ee : ∀ {A : Set} → M {A} end end
m-ee = (λ _ → refl) , (λ n → ⊥-elim (n tt))

-- TWO RUNS CORRESPOND along `φ`, subscribed at `s` and `s*`: each
-- unpinned plain row on its image, a skip possibly put late instead, as
-- a live pin is (`put`, homed in the subscription's instant or a carried
-- row's before it); each shown elaborated row back on a plain one; each
-- live elaborated row in the subscription's instant or a carried row's,
-- the image at or before it unless the row leads its instant (an async
-- step's `begin` comes before the step's value); the images keeping the
-- order and the instants of the rows they image.
--
-- A pin is put on an elaborated pin whose connect has no image of a value
-- past the plain connect before it, and a skip no later than the image
-- of any row after it: what a takeWhile keeps of one, it keeps of the
-- other.
record Corr {A : Set} (s s* : Pos) (φ : Pos → Pos) (Put : Pos → Pos → Set) (L : EmissionSet A) (L* : EmissionSet (IE A)) : Set where
  Imaged : Pos → Ev A → Set
  Imaged k e = Σ (Ev (IE A)) λ e′ → L* (φ k) e′ × M e e′

  Homed : Pos → Set
  Homed k = instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → L k₀ e₀ × Unpinned e₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  PutAt : Pos → Set
  PutAt k = (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → L* l e′ × Put k l) × Homed k

  -- No unpinned row of its instant lies before `k`.
  Leads : Pos → Set
  Leads k = ∀ {k′ e′} → L k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  -- A pin put on an elaborated pin, its connect's past the plain one's.
  PinAt : Pos → Pos → Set
  PinAt k p = (Σ Pos λ l → Σ Pos λ p′ → L* l (pin p′) × Put k l
                × (∀ {k₀ a} → L k₀ (out a) → φ k₀ ≺ p′ → k₀ ≺ p))
            × Homed k

  field
    row→   : ∀ {k e} → L k e → Unpinned e → Imaged k e ⊎ (e ≡ skip × PutAt k)
    pin→   : ∀ {k p} → L k (pin p) → Live L k → PinAt k p
    put-before : ∀ {k l k′ e′} → L k skip → Put k l → L k′ e′ → Unpinned e′ → k ≺ k′ → l ≼ φ k′
    shown← : ∀ {l e′} → L* l e′ → Shown (One valuesOf) e′
           → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ k × L k e × Unpinned e × M e e′
    place  : ∀ {m e′} → L* m e′ → Live L* m
           → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev A) λ e → L k e × Unpinned e × Imaged k e × (φ k ≼ m ⊎ Leads k) × instantOf (φ k) ≡ instantOf m
    mono   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ k ≺ φ k′
    inst   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′
           → (instantOf (φ k) ≡ instantOf (φ k′) ⇔ instantOf k ≡ instantOf k′)
    home   : ∀ {k e} → L k e → Unpinned e → (instantOf (φ k) ≡ instantOf s* ⇔ instantOf k ≡ instantOf s)

-- A table's positions.
keys : ∀ {X : Set} → Maybe (Tb.Listed X) → List Pos
keys nothing  = []
keys (just L) = map proj₁ (rows L)

in-keys : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {k e} → TR m k e → k ∈ keys m
in-keys (L , refl , r) = ∈-map⁺ proj₁ r

-- Two tables have few rows together.
tr-few : ∀ {X : Set} (m m′ : Maybe (Tb.Listed X)) q → Few (λ y e → TR m y e ⊎ TR m′ y e) q
tr-few m m′ q = keys m ++ keys m′ , λ { (inj₁ x) _ → ∈-++⁺ˡ (in-keys x) ; (inj₂ x) _ → ∈-++⁺ʳ (keys m) (in-keys x) }

-- A correspondence carries to runs holding the same rows.
corr-≃ : ∀ {A s s* φ Put} {L K : EmissionSet A} {L* K* : EmissionSet (IE A)}
       → (∀ {k e} → L k e → K k e) → (∀ {k e} → K k e → L k e)
       → (∀ {k e} → L* k e → K* k e) → (∀ {k e} → K* k e → L* k e)
       → Corr s s* φ Put L L* → Corr s s* φ Put K K*
corr-≃ {A} {s} {s*} {φ} {Put} {L} {K} {L*} {K*} to from to* from* C = record
  { row→ = λ x un → [ (λ im → inj₁ (imaged im)) , (λ { (eq , pa) → inj₂ (eq , putAt pa) }) ] (C.row→ (from x) un)
  ; pin→ = λ x lv → pinAt (C.pin→ (from x) (λ xc → lv (to xc)))
  ; put-before = λ x pl x′ un′ lt → C.put-before (from x) pl (from x′) un′ lt
  ; shown← = λ y sh → let (k , e , eq , x , un , m) = C.shown← (from* y) sh in k , e , eq , to x , un , m
  ; place = λ {m} y lv → [ inj₁ , (λ { (k , e , x , un , im , le , eq) → inj₂ (k , e , to x , un , imaged im , leadsOr {k} {m} le , eq) }) ] (C.place (from* y) (λ yc → lv (to* yc)))
  ; mono = λ x x′ → C.mono (from x) (from x′)
  ; inst = λ x x′ → C.inst (from x) (from x′)
  ; home = λ x → C.home (from x)
  }
  where
    module C = Corr C

    Imaged : Pos → Ev A → Set
    Imaged k e = Σ (Ev (IE A)) λ e′ → K* (φ k) e′ × M e e′

    imaged : ∀ {k e} → C.Imaged k e → Imaged k e
    imaged (e′ , y , m) = e′ , to* y , m

    Homed : Pos → Set
    Homed k = instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → K k₀ e₀ × Unpinned e₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

    homed : ∀ {k} → C.Homed k → Homed k
    homed (inj₁ eq) = inj₁ eq
    homed (inj₂ (k₀ , e₀ , x , un , im , lt , eq)) = inj₂ (k₀ , e₀ , to x , un , imaged im , lt , eq)

    leadsOr : ∀ {k m} → φ k ≼ m ⊎ C.Leads k → φ k ≼ m ⊎ (∀ {k′ e′} → K k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
    leadsOr (inj₁ le) = inj₁ le
    leadsOr (inj₂ ld) = inj₂ (λ x → ld (from x))

    putAt : ∀ {k} → C.PutAt k → (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → K* l e′ × Put k l) × Homed k
    putAt ((l , e′ , y , pl) , h) = (l , e′ , to* y , pl) , homed h

    pinAt : ∀ {k p} → C.PinAt k p
          → (Σ Pos λ l → Σ Pos λ p′ → K* l (pin p′) × Put k l × (∀ {k₀ a} → K k₀ (out a) → φ k₀ ≺ p′ → k₀ ≺ p)) × Homed k
    pinAt ((l , p′ , y , pl , past) , h) = (l , p′ , to* y , pl , λ x lt → past (from x) lt) , homed h

-- A SUBTERM'S CUTS CORRESPOND, each along its own map and late
-- placement, read off the two families of tables: two cuts agreeing up to
-- a row map it alike; each position is imaged by finitely many, whatever
-- the cut; agreement crosses between cuts along the map, up to an image
-- and back from one the cut holds, up to a late placement, from a row of
-- the instant a row leads to its image, and everywhere.
--
-- Each table is a run's: there is one, of one event per position, none
-- under another's, a pin inside its connect, every row and every image
-- at or past its subscription.  Two cuts are truncated before they
-- differ (`Cons`).
record Rel {A : Set} (P : ℕ → Maybe (Tb.Listed A)) (Q : ℕ → Maybe (Tb.Listed (IE A))) (s s* : Pos) : Set₁ where
  field
    φ           : ℕ → Pos → Pos
    Put         : ℕ → Pos → Pos → Set
    corr        : ∀ N → Corr s s* (φ N) (Put N) (TR (P N)) (TR (Q N))
    φ-agree     : ∀ {N N′ k e} → TR (P N) k e → Unpinned e → AgreeTo k (TR (P N)) (TR (P N′)) → φ N k ≡ φ N′ k
    bk          : Pos → List Pos
    in-bk       : ∀ {N k e} → TR (P N) k e → Unpinned e → k ∈ bk (φ N k)
    pb-few      : ∀ l → Σ (List Pos) λ ks → ∀ {N k} → Put N k l → k ∈ ks
    elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → AgreeTo k (TR (P N′)) (TR (P N))
                → AgreeTo (φ N k) (TR (Q N′)) (TR (Q N))
    stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P N) k e → Unpinned e → TR (Q N) (φ N k) e′
                → AgreeTo (φ N k) (TR (Q N′)) (TR (Q N)) → AgreeTo k (TR (P N′)) (TR (P N))
    stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P N′)) (TR (P N)) → TR (Q N) l e′ → Put N k l
                → AgreeTo l (TR (Q N′)) (TR (Q N))
    stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P N) k e → Unpinned e → TR (Q N) (φ N k) e′ → Corr.Leads (corr N) k
                → TR (Q N) m e* → instantOf m ≡ instantOf (φ N k) → AgreeTo m (TR (Q N′)) (TR (Q N)) → AgreeTo (φ N k) (TR (Q N′)) (TR (Q N))
    elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → ∀ {y e} → TR (Q N′) y e → TR (Q N) y e
    func        : ∀ {N y e e′} → TR (P N) y e → TR (P N) y e′ → e ≡ e′
    func*       : ∀ {N y e e′} → TR (Q N) y e → TR (Q N) y e′ → e ≡ e′
    flat        : ∀ {N y e l ys e′} → TR (P N) y e → TR (P N) (y ⊕ (l ∷ ys)) e′ → ⊥
    flat*       : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
    pin-in      : ∀ {N l r} → TR (P N) l (pin r) → T (inside r l)
    pin-in*     : ∀ {N l r} → TR (Q N) l (pin r) → T (inside r l)
    cons        : ∀ {N N′} → Cons (TR (P N)) (TR (P N′))
    cons*       : ∀ {N N′} → Cons (TR (Q N)) (TR (Q N′))
    got         : ∀ N → Got (P N)
    got*        : ∀ N → Got (Q N)
    after       : ∀ {N k e} → TR (P N) k e → s ≼ k
    after*      : ∀ {N l e} → TR (Q N) l e → s* ≼ l
    after-φ     : ∀ {N k e} → TR (P N) k e → Unpinned e → s* ≼ φ N k
