{-# OPTIONS --guardedness #-}

-- WHAT IT IS FOR A SUBTERM'S CUTS TO CORRESPOND (`Rel`): the record
-- `simultaneous.TableRel.rel` builds former by former, and the tables'
-- rows (`TR`) and shapes (`Sh`) it is stated over.
module simultaneous.TableCorr where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Bool using (T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; pin; Unpinned; EmissionSet; _≺_; _≼_)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)

open import simultaneous.Horizon using (Tag; module Cuts)
open import simultaneous.HorizonCorr using (module Inter; Own; OwnPut)
open import simultaneous.HorizonConn using (Mark)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans)
open import simultaneous.TableKit using (Got; TR; M)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

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
-- past the plain connect before it, and a pin or a skip no later than the
-- image of any row after it: what a takeWhile keeps of one, it keeps of
-- the other.
--
-- A LATE row (`Late`) has no image to speak of, only a late placement: a
-- skip a hot's pin or late row became for its reader, whose image the
-- source never placed.  The order facts are over the rest.
record Corr {A : Set} (s s* : Pos) (φ : Pos → Pos) (Put : Pos → Pos → Set) (Late : Pos → Set) (L : EmissionSet A) (L* : EmissionSet (IE A)) : Set where
  Imaged : Pos → Ev A → Set
  Imaged k e = Σ (Ev (IE A)) λ e′ → L* (φ k) e′ × M e e′

  Homed : Pos → Set
  Homed k = instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → L k₀ e₀ × Unpinned e₀ × ¬ Late k₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

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
    row→   : ∀ {k e} → L k e → Unpinned e → (Imaged k e × ¬ Late k) ⊎ (e ≡ skip × PutAt k)
    late-put : ∀ {k e} → Late k → L k e → e ≡ skip × PutAt k
    pin→   : ∀ {k p} → L k (pin p) → Live L k → PinAt k p
    put-before : ∀ {k l k′ e′} → L k skip → Put k l → L k′ e′ → Unpinned e′ → ¬ Late k′ → k ≺ k′ → l ≼ φ k′
    pin-before : ∀ {k p l k′ e′} → L k (pin p) → Put k l → L k′ e′ → Unpinned e′ → ¬ Late k′ → k ≺ k′ → l ≼ φ k′
    shown← : ∀ {l e′} → L* l e′ → Shown (One valuesOf) e′
           → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ k × L k e × Unpinned e × ¬ Late k × M e e′
    place  : ∀ {m e′} → L* m e′ → Live L* m
           → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev A) λ e → L k e × Unpinned e × ¬ Late k × Imaged k e × (φ k ≼ m ⊎ Leads k) × instantOf (φ k) ≡ instantOf m
    mono   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′ → ¬ Late k → ¬ Late k′ → k ≺ k′ → φ k ≺ φ k′
    inst   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′ → ¬ Late k → ¬ Late k′
           → (instantOf (φ k) ≡ instantOf (φ k′) ⇔ instantOf k ≡ instantOf k′)
    home   : ∀ {k e} → L k e → Unpinned e → ¬ Late k → (instantOf (φ k) ≡ instantOf s* ⇔ instantOf k ≡ instantOf s)

-- A late row is a skip: a row that is not is not late.
nl-ev : ∀ {A s s* φ Put Late} {L : EmissionSet A} {L* : EmissionSet (IE A)} → Corr s s* φ Put Late L L*
      → ∀ {k e} → L k e → ¬ e ≡ skip → ¬ Late k
nl-ev C x ns lt = ns (proj₁ (Corr.late-put C lt x))

-- A table's positions.
keys : ∀ {X : Set} → Maybe (Tb.Listed X) → List Pos
keys nothing  = []
keys (just L) = map proj₁ (rows L)

in-keys : ∀ {X : Set} {m : Maybe (Tb.Listed X)} {k e} → TR m k e → k ∈ keys m
in-keys (L , refl , r) = ∈-map⁺ proj₁ r

-- A correspondence carries to runs holding the same rows.
corr-≃ : ∀ {A s s* φ Put Late} {L K : EmissionSet A} {L* K* : EmissionSet (IE A)}
       → (∀ {k e} → L k e → K k e) → (∀ {k e} → K k e → L k e)
       → (∀ {k e} → L* k e → K* k e) → (∀ {k e} → K* k e → L* k e)
       → Corr s s* φ Put Late L L* → Corr s s* φ Put Late K K*
corr-≃ {A} {s} {s*} {φ} {Put} {Late} {L} {K} {L*} {K*} to from to* from* C = record
  { row→ = λ x un → [ (λ { (im , nl) → inj₁ (imaged im , nl) }) , (λ { (eq , pa) → inj₂ (eq , putAt pa) }) ] (C.row→ (from x) un)
  ; late-put = λ lt x → let (eq , pa) = C.late-put lt (from x) in eq , putAt pa
  ; pin→ = λ x lv → pinAt (C.pin→ (from x) (λ xc → lv (to xc)))
  ; put-before = λ x pl x′ un′ nl lt → C.put-before (from x) pl (from x′) un′ nl lt
  ; pin-before = λ x pl x′ un′ nl lt → C.pin-before (from x) pl (from x′) un′ nl lt
  ; shown← = λ y sh → let (k , e , eq , x , un , nl , m) = C.shown← (from* y) sh in k , e , eq , to x , un , nl , m
  ; place = λ {m} y lv → [ inj₁ , (λ { (k , e , x , un , nl , im , le , eq) → inj₂ (k , e , to x , un , nl , imaged im , leadsOr {k} {m} le , eq) }) ] (C.place (from* y) (λ yc → lv (to* yc)))
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
    Homed k = instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → K k₀ e₀ × Unpinned e₀ × ¬ Late k₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

    homed : ∀ {k} → C.Homed k → Homed k
    homed (inj₁ eq) = inj₁ eq
    homed (inj₂ (k₀ , e₀ , x , un , nl , im , lt , eq)) = inj₂ (k₀ , e₀ , to x , un , nl , imaged im , lt , eq)

    leadsOr : ∀ {k m} → φ k ≼ m ⊎ C.Leads k → φ k ≼ m ⊎ (∀ {k′ e′} → K k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
    leadsOr (inj₁ le) = inj₁ le
    leadsOr (inj₂ ld) = inj₂ (λ x → ld (from x))

    putAt : ∀ {k} → C.PutAt k → (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → K* l e′ × Put k l) × Homed k
    putAt ((l , e′ , y , pl) , h) = (l , e′ , to* y , pl) , homed h

    pinAt : ∀ {k p} → C.PinAt k p
          → (Σ Pos λ l → Σ Pos λ p′ → K* l (pin p′) × Put k l × (∀ {k₀ a} → K k₀ (out a) → φ k₀ ≺ p′ → k₀ ≺ p)) × Homed k
    pinAt ((l , p′ , y , pl , past) , h) = (l , p′ , to* y , pl , λ x lt → past (from x) lt) , homed h

-- THE HANGS ACROSS CUTS.  A shallower cut's plain hangs lie past a
-- deeper cut's own row where its elaborated hangs lie past the row's
-- image (`back-clear`), or past its placement (`put-clear`); and, at one
-- cut, past an instant's leading row where they lie past any elaborated
-- row of its image's instant (`lead-clear`), a mark or pin `bcorr`
-- orders against nothing.  Each is one way: a hang past a cut's first
-- may sit in a lane no deeper cut runs, where no deeper row is ordered
-- against it, but the first hang is real and settles all before it.
record Across {A : Set} (P : ℕ → EmissionSet A) (Q : ℕ → EmissionSet (IE A)) (φ : ℕ → Pos → Pos)
  (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set) (Bd Bd* : ℕ → Pos → Tag → Set) : Set where
  field
    back-clear : ∀ {N N′ k e} → N ≤ N′ → P N′ k e → Unpinned e → ¬ Late N′ k
               → Cuts.Clear Q Bd* N (φ N′ k) → Cuts.Clear P Bd N k
    put-clear  : ∀ {N N′ k e l} → N ≤ N′ → P N′ k e → Put N′ k l → Cuts.Clear Q Bd* N l → Cuts.Clear P Bd N k
    lead-clear : ∀ {N k e m e*} → P N k e → Unpinned e → ¬ Late N k
               → (∀ {k′ e′} → P N k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
               → Q N m e* → instantOf m ≡ instantOf (φ N k) → Cuts.Clear Q Bd* N m → Cuts.Clear P Bd N k

-- A ROW IS CUT-INDEPENDENT BEFORE THE ELABORATED HANGS: a deeper cut's own
-- row whose image lies before a shallower cut's elaborated hangs is a row
-- of the shallower cut, as own and on the same image (`pull`); a late
-- row whose placement lies before them is one of the shallower cut,
-- placed there too (`put-pull`).  No plain hang is mentioned: with one
-- cut's correspondence, ordering rows and placements both ways
-- (`Inter.clear←`, `Inter.clear-put←`), it gives `Across.back-clear`
-- and `Across.put-clear` (`across-of`).
record Stable {A : Set} (P : ℕ → EmissionSet A) (Q : ℕ → EmissionSet (IE A)) (φ : ℕ → Pos → Pos)
  (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set) (Bd Bd* : ℕ → Pos → Tag → Set) : Set where
  field
    pull     : ∀ {N N′ k e} → N ≤ N′ → P N′ k e → Unpinned e → ¬ Late N′ k
             → Cuts.Clear Q Bd* N (φ N′ k) → P N k e × ¬ Late N k × φ N k ≡ φ N′ k
    put-pull : ∀ {N N′ k e l} → N ≤ N′ → P N′ k e → Put N′ k l → Cuts.Clear Q Bd* N l → Σ (Ev A) (P N k) × Put N k l

-- At one cut, a leading row clear where its instant's elaborated rows are.
LeadClear : ∀ {A} → (ℕ → EmissionSet A) → (ℕ → EmissionSet (IE A)) → (ℕ → Pos → Pos) → (ℕ → Pos → Set) → (Bd Bd* : ℕ → Pos → Tag → Set) → Set
LeadClear P Q φ Late Bd Bd* = ∀ {N k e m e*} → P N k e → Unpinned e → ¬ Late N k
  → (∀ {k′ e′} → P N k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
  → Q N m e* → instantOf m ≡ instantOf (φ N k) → Cuts.Clear Q Bd* N m → Cuts.Clear P Bd N k

-- The hangs across cuts, from one cut's correspondence and stability.
across-of : ∀ {A} {P : ℕ → EmissionSet A} {Q : ℕ → EmissionSet (IE A)} {φ : ℕ → Pos → Pos}
            {Put : ℕ → Pos → Pos → Set} {Late : ℕ → Pos → Set} {Bd Bd* : ℕ → Pos → Tag → Set}
          → (∀ N → Inter.BCorr (Own (P N) (Late N)) (φ N) (OwnPut (P N) (Put N)) (Bd N) (Bd* N))
          → Stable P Q φ Put Late Bd Bd*
          → LeadClear P Q φ Late Bd Bd*
          → Across P Q φ Put Late Bd Bd*
across-of {P = P} {Q} {φ} {Put} {Late} {Bd} {Bd*} C S lead = record
  { back-clear = back ; put-clear = put ; lead-clear = lead }
  where
    module I (N : ℕ) = Inter (Own (P N) (Late N)) (φ N) (OwnPut (P N) (Put N)) (Bd N) (Bd* N)

    back : ∀ {N N′ k e} → N ≤ N′ → P N′ k e → Unpinned e → ¬ Late N′ k → Cuts.Clear Q Bd* N (φ N′ k) → Cuts.Clear P Bd N k
    back {N} {N′} {k} {e} le x un nl cl* =
      let (x₀ , nl₀ , eq) = Stable.pull S {N} {N′} {k} {e} le x un nl cl*
      in I.clear← N (C N) {k} (e , x₀ , un , nl₀) (λ {b} {g} bd* → subst (_≺ b) (sym eq) (cl* bd*))

    put : ∀ {N N′ k e l} → N ≤ N′ → P N′ k e → Put N′ k l → Cuts.Clear Q Bd* N l → Cuts.Clear P Bd N k
    put {N} {N′} {k} {e} {l} le x pl cl* = I.clear-put← N (C N) {k} {l} (Stable.put-pull S {N} {N′} {k} {e} {l} le x pl cl*) cl*

-- A SUBTERM'S CUTS CORRESPOND, each along its own map and late
-- placement, read off the two families of tables: each position is
-- imaged by finitely many in each cut.  Each table is a run's: there is
-- one, of one event per position, none under another's, a pin inside its
-- connect, every row and every image at or past its subscription, every
-- elaborated pin's connect too.
--
-- WHERE EACH CUT HANGS: every cut's rows stop at boundaries (`Bd`,
-- `Bd*`), past which a deeper cut may differ and before which none does
-- (`bounded`, `simultaneous.Horizon.Cuts.Bounded`); the plain and the
-- elaborated boundaries correspond at each cut, the same rows before
-- each (`bcorr`).  Two cuts agree up to a row because no boundary lies
-- before it: the subterm never decides where a hang is, only that the
-- two sides hang alike, at one cut and across cuts (`across`).
--
-- LATE ROWS (`Late`) have no image: the order facts are over the rest.
-- A skip put rather than imaged still lies over no elaborated boundary
-- (`skip-off*`), as an image, a row, does not.
record Rel {A : Set} (P : ℕ → Maybe (Tb.Listed A)) (Q : ℕ → Maybe (Tb.Listed (IE A))) (s s* : Pos) : Set₁ where
  field
    φ           : ℕ → Pos → Pos
    Put         : ℕ → Pos → Pos → Set
    Late        : ℕ → Pos → Set
    corr        : ∀ N → Corr s s* (φ N) (Put N) (Late N) (TR (P N)) (TR (Q N))
    bk          : ℕ → Pos → List Pos
    in-bk       : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Late N k → k ∈ bk N (φ N k)
    pb-few      : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put N k l → k ∈ ks
    Bd          : ℕ → Pos → Tag → Set
    Bd*         : ℕ → Pos → Tag → Set
    bounded     : Cuts.Bounded (λ N → TR (P N)) Bd
    bounded*    : Cuts.Bounded (λ N → TR (Q N)) Bd*
    bcorr       : ∀ N → Inter.BCorr (Own (TR (P N)) (Late N)) (φ N) (OwnPut (TR (P N)) (Put N)) (Bd N) (Bd* N)
    across      : Across (λ N → TR (P N)) (λ N → TR (Q N)) φ Put Late Bd Bd*
    skip-off*   : ∀ {N k l b g} → TR (P N) k skip → ¬ Late N k → Put N k l → Bd* N b g → ¬ φ N k ⊑ b
    func        : ∀ {N y e e′} → TR (P N) y e → TR (P N) y e′ → e ≡ e′
    func*       : ∀ {N y e e′} → TR (Q N) y e → TR (Q N) y e′ → e ≡ e′
    flat        : ∀ {N y e l ys e′} → TR (P N) y e → TR (P N) (y ⊕ (l ∷ ys)) e′ → ⊥
    flat*       : ∀ {N y e l ys e′} → TR (Q N) y e → TR (Q N) (y ⊕ (l ∷ ys)) e′ → ⊥
    pin-in      : ∀ {N l r} → TR (P N) l (pin r) → T (inside r l)
    pin-in*     : ∀ {N l r} → TR (Q N) l (pin r) → T (inside r l)
    got         : ∀ N → Got (P N)
    got*        : ∀ N → Got (Q N)
    after       : ∀ {N k e} → TR (P N) k e → s ≼ k
    after*      : ∀ {N l e} → TR (Q N) l e → s* ≼ l
    after-φ     : ∀ {N k e} → TR (P N) k e → Unpinned e → ¬ Late N k → s* ≼ φ N k
    pin-after*  : ∀ {N l r} → TR (Q N) l (pin r) → s* ≼ r

-- NO OWN ROW'S IMAGE LIES OVER AN ELABORATED BOUNDARY: an imaged row's
-- image is a row; a put one's by `skip-off*`.
off* : ∀ {A P Q s s*} (R : Rel {A} P Q s s*) {N k b g} → Own (TR (P N)) (Rel.Late R N) k → Rel.Bd* R N b g → ¬ Rel.φ R N k ⊑ b
off* R {N} (e , x , un , nl) bd with Corr.row→ (Rel.corr R N) x un
... | inj₁ ((_ , y , _) , _)        = Cuts.Bounded.gap (Rel.bounded* R) bd y
... | inj₂ (refl , ((_ , _ , _ , pl) , _)) = Rel.skip-off* R x nl pl bd

-- Nor over a connect a boundary waits on, which lies under it.
off*-mark : ∀ {A P Q s s*} (R : Rel {A} P Q s s*) {N k z*} → Own (TR (P N)) (Rel.Late R N) k → Mark (Rel.Bd* R N) z* → ¬ Rel.φ R N k ⊑ z*
off*-mark R o (_ , _ , bd , inj₁ refl) = off* R o bd
off*-mark R o (_ , _ , bd , inj₂ refl) h = off* R o bd (⊑-trans h (Cuts.Bounded.held-under (Rel.bounded* R) bd))

-- Two records of one stream alike at a row: one image, and the row late
-- in the second only where it is late in the first.
record Same {A} {P P′ : ℕ → Maybe (Tb.Listed A)} {Q Q′ : ℕ → Maybe (Tb.Listed (IE A))} {s s′ s* s*′} (R : Rel P Q s s*) (R′ : Rel P′ Q′ s′ s*′) (N : ℕ) (y : Pos) : Set where
  constructor same
  field
    φ≡  : Rel.φ R N y ≡ Rel.φ R′ N y
    nl→ : ¬ Rel.Late R N y → ¬ Rel.Late R′ N y
open Same public
