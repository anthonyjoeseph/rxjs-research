{-# OPTIONS --guardedness #-}

-- `scan`'S CASE (`scan-tab`): a scan keeps its child's positions and
-- constructors, so the map and the late placement are the child's.  A
-- plain fold and the elaborated one meet at an image (`acc*→`): the
-- elaborated accumulator at any row is the plain fold of the latest value
-- imaged at or before it, a mark folding nothing, and a shown fold is a
-- value's image.  Agreement crosses the scan forward by `scan-ag`, and
-- back through the child's coherence: a scanned table keeps its child's
-- shape, every value of a table having a fold (`fold?`).
module simultaneous.TableScan where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Relation.Unary.Any using (any?; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Bool using (T)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; root; _≟ᵖ_; _<ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_; module Scan; module Values)
open import denotation.Laws using (scan-ag)
open import denotation.Laws.Fold using (Latest)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; few-ind; ≺-irrefl; ≺-absurd; ≼-refl; ≺→≼; ≼-trans; ≼-antisym; ≼-or-≻; ≼-split; ≼-≺-≺)
open import denotation.Laws.Worlds.Leaves using (module AccF)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind; scanRows)
open import quickcheck.Tabled.Exact.Scan using (module ScanX)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.TableCorr using (TR; M; Corr; Rel; module Rel; ev; Sh; ag-≃; coh-of; keys; in-keys; tr-few; ends; m-back; m-val; m-ee; got-bind)
open import simultaneous.TableMap using (Mapped; tr-map→; tr-map←; sh-map→; sh-map←; sh-of; ag-map; func-map; flat-map; pin-in-map)
open import simultaneous.TableTake using (ex-just)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; scanIE; marked)
open import simultaneous.InstEmit using (begin)
open Scan using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)

------------------------------------------------------------------------
-- A table's scan

Scanned : ∀ {X B : Set} → (B → X → B) → B → Maybe (Tb.Listed X) → Maybe (Tb.Listed B)
Scanned f z m = bind m λ l → just (scanRows f z l)

-- The latest position before `w` among `ks` where a decidable `V` holds.
latest? : ∀ (V : Pos → Set) → (∀ k → Dec (V k)) → ∀ w ks → Latest V w ks
latest? V V? w []       = inj₁ λ ()
latest? V V? w (k ∷ ks) with latest? V V? w ks | V? k | T? (k <ᵖ w)
... | inj₁ none | no ¬v | _ = inj₁ λ { {_} (here refl) vk _ → ¬v vk ; {_} (there m) → none m }
... | inj₁ none | yes _ | no ¬kw = inj₁ λ { {_} (here refl) _ kw → ¬kw kw ; {_} (there m) → none m }
... | inj₁ none | yes vk | yes kw =
  inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {_} (there m) vk′ k′w → ⊥-elim (none m vk′ k′w) })
... | inj₂ (v , vv , vw , mx) | no ¬v | _ = inj₂ (v , vv , vw , λ { {_} (here refl) vk _ → ⊥-elim (¬v vk) ; {_} (there m) → mx m })
... | inj₂ (v , vv , vw , mx) | yes _ | no ¬kw = inj₂ (v , vv , vw , λ { {_} (here refl) _ kw → ⊥-elim (¬kw kw) ; {_} (there m) → mx m })
... | inj₂ (v , vv , vw , mx) | yes vk | yes kw with ≼-or-≻ v k
...   | inj₁ vk≼ = inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {k′} (there m) vk′ k′w → ≼-trans {k′} {v} {k} (mx m vk′ k′w) vk≼ })
...   | inj₂ kv  = inj₂ (v , vv , vw , λ { {_} (here refl) _ _ → ≺→≼ {k} {v} kv ; {_} (there m) → mx m })

module _ {X B : Set} (f : B → X → B) (z : B) where
  tr-scan→ : ∀ (m : Maybe (Tb.Listed X)) {k e} → TR (Scanned f z m) k e → ScanT f z (TR m) k e
  tr-scan→ nothing (_ , () , _)
  tr-scan→ (just L) (_ , refl , r) = ScanX.sound-s f z (TR (just L)) L (ex-just L) r

  tr-scan← : ∀ (m : Maybe (Tb.Listed X)) {k e} → ScanT f z (TR m) k e → TR (Scanned f z m) k e
  tr-scan← nothing (sval (acc₀ (_ , () , _) _))
  tr-scan← nothing (sval (acc _ (_ , () , _) _ _))
  tr-scan← nothing (sstep (_ , () , _))
  tr-scan← nothing (spin (_ , () , _))
  tr-scan← nothing (send (_ , () , _))
  tr-scan← (just L) s = scanRows f z L , refl , ScanX.complete-s f z (TR (just L)) L (ex-just L) s

  -- Whether a table holds a value at `k`.
  val? : ∀ (m : Maybe (Tb.Listed X)) k → Dec (Σ X λ a → TR m k (out a))
  val? nothing k = no λ { (_ , _ , () , _) }
  val? (just L) k with any? isval (rows L)
    where
      isval : ∀ (r : Pos × Ev X) → Dec (Σ X λ a → r ≡ (k , out a))
      isval (k′ , out a) with k′ ≟ᵖ k
      ... | yes refl = yes (a , refl)
      ... | no n     = no λ { (_ , refl) → n refl }
      isval (k′ , skip)  = no λ { (_ , ()) }
      isval (k′ , end)   = no λ { (_ , ()) }
      isval (k′ , pin _) = no λ { (_ , ()) }
  ... | yes h with find h
  ...   | _ , mem , (a , refl) = yes (a , L , refl , mem)
  val? (just L) k | no n = no λ { (a , _ , refl , mem) → n (lose mem (a , refl)) }

  -- EVERY VALUE OF A TABLE HAS A FOLD, from the latest value before it.
  fold? : ∀ (m : Maybe (Tb.Listed X)) {w a} → TR m w (out a) → Σ B (Acc f z (TR m) w)
  fold? m {w} = few-ind (λ w → ∀ {a} → TR m w (out a) → Σ B (Acc f z (TR m) w)) step (keys m , λ x _ → in-keys x)
    where
      step : ∀ {w} → Σ (List Pos) (λ ks → ∀ {k e′} → TR m k e′ → k ≺ w → k ∈ ks)
           → (∀ {v e} → TR m v e → v ≺ w → ∀ {a} → TR m v (out a) → Σ B (Acc f z (TR m) v))
           → ∀ {a} → TR m w (out a) → Σ B (Acc f z (TR m) w)
      step {w} (ks , h) ih {a} x with latest? (λ k → Σ X λ a → TR m k (out a)) (val? m) w ks
      ... | inj₁ none = f z a , acc₀ x (λ y kw → none (h y kw) (_ , y) kw)
      ... | inj₂ (v , (_ , xv) , vw , mx) =
        let (b , av) = ih xv vw xv in f b a , acc av x vw (λ y vk kw → mx (h y kw) (_ , y) kw vk)

  -- A scan's row is its child's row at the same position, of the same
  -- constructor; every child row is scanned.
  row-of : ∀ {t : EmissionSet X} {k e} → ScanT f z t k e → Σ (Ev X) (t k)
  row-of (sval (acc₀ x _))    = _ , x
  row-of (sval (acc _ x _ _)) = _ , x
  row-of (sstep x)            = _ , x
  row-of (spin x)             = _ , x
  row-of (send x)             = _ , x

  sh-sc→ : ∀ (m : Maybe (Tb.Listed X)) {k e} → Sh (TR (Scanned f z m)) k e → Sh (TR m) k e
  sh-sc→ m (_ , x , refl) with tr-scan→ m x
  ... | sval (acc₀ y _)    = _ , y , refl
  ... | sval (acc _ y _ _) = _ , y , refl
  ... | sstep y            = _ , y , refl
  ... | spin y             = _ , y , refl
  ... | send y             = _ , y , refl

  row-to : ∀ (m : Maybe (Tb.Listed X)) {k e₀} → TR m k e₀ → Σ (Ev B) λ e → ScanT f z (TR m) k e × ev (λ _ → tt) e ≡ ev (λ _ → tt) e₀
  row-to m {e₀ = out a} x = let (b , ac) = fold? m x in out b , sval ac , refl
  row-to m {e₀ = skip}  x = skip , sstep x , refl
  row-to m {e₀ = end}   x = end , send x , refl
  row-to m {e₀ = pin r} x = pin r , spin x , refl

  sh-sc← : ∀ (m : Maybe (Tb.Listed X)) {k e} → Sh (TR m) k e → Sh (TR (Scanned f z m)) k e
  sh-sc← m (_ , x , refl) = let (e , s , eq) = row-to m x in e , tr-scan← m s , sym eq

  -- Two tables agreeing, scanned, agree.
  ag-sc : ∀ (m m′ : Maybe (Tb.Listed X)) {q} → AgreeTo q (TR m) (TR m′) → AgreeTo q (TR (Scanned f z m)) (TR (Scanned f z m′))
  ag-sc m m′ ag = ag-≃ (tr-scan← m) (tr-scan→ m) (tr-scan← m′) (tr-scan→ m′) (scan-ag f z ag)

  -- A run's scan is a run's.
  func-sc : ∀ {t : EmissionSet X} → (∀ {y e e′} → t y e → t y e′ → e ≡ e′) → ∀ {y e e′} → ScanT f z t y e → ScanT f z t y e′ → e ≡ e′
  func-sc fu (sval a) (sval a′) = cong out (AccF.acc-func f z fu refl a a′)
  func-sc fu (sval a) (sstep x) with fu (proj₂ (AccF.acc-val f z fu a)) x
  ... | ()
  func-sc fu (sval a) (spin x) with fu (proj₂ (AccF.acc-val f z fu a)) x
  ... | ()
  func-sc fu (sval a) (send x) with fu (proj₂ (AccF.acc-val f z fu a)) x
  ... | ()
  func-sc fu (sstep x) (sval a) with fu x (proj₂ (AccF.acc-val f z fu a))
  ... | ()
  func-sc fu (sstep x) (sstep x′) = refl
  func-sc fu (sstep x) (spin x′) with fu x x′
  ... | ()
  func-sc fu (sstep x) (send x′) with fu x x′
  ... | ()
  func-sc fu (spin x) (sval a) with fu x (proj₂ (AccF.acc-val f z fu a))
  ... | ()
  func-sc fu (spin x) (sstep x′) with fu x x′
  ... | ()
  func-sc fu (spin x) (spin x′) with fu x x′
  ... | refl = refl
  func-sc fu (spin x) (send x′) with fu x x′
  ... | ()
  func-sc fu (send x) (sval a) with fu x (proj₂ (AccF.acc-val f z fu a))
  ... | ()
  func-sc fu (send x) (sstep x′) with fu x x′
  ... | ()
  func-sc fu (send x) (spin x′) with fu x x′
  ... | ()
  func-sc fu (send x) (send x′) = refl

  sval-inv : ∀ {t : EmissionSet X} {k b} → ScanT f z t k (out b) → Acc f z t k b
  sval-inv (sval ac) = ac

-- Two rows of one event at `y` and agreement below it: agreement at it.
ag-at : ∀ {X : Set} {a b : EmissionSet X} {y e₀} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ a b)
      → (∀ {k e e′} → a k e → a k e′ → e ≡ e′) → (∀ {k e e′} → b k e → b k e′ → e ≡ e′)
      → a y e₀ → b y e₀ → AgreeTo y a b
ag-at {a = a} {b} {y} below fa fb xa xb = ⟨ (λ {y′} y′y → at y′y) ⟩
  where
    at : ∀ {y′ e} → y′ ≼ y → (a y′ e → b y′ e) × (b y′ e → a y′ e)
    at {y′} y′y with ≼-split {y′} {y} y′y
    ... | inj₁ lt   = upto (below {y′} lt) (≼-refl {y′})
    ... | inj₂ refl = (λ x → subst (b y′) (fa xa x) xb) , (λ x → subst (a y′) (fb xb x) xa)

-- A scanned value shows the fold its value folds.
private
  sv : ∀ {A B : Set} (f : B → A → B) (w₀ : B × IE B) (x₀ : IE A) {a} → valuesOf x₀ ≡ a ∷ []
     → valuesOf (proj₂ (scanIE f w₀ x₀)) ≡ proj₁ (scanIE f w₀ x₀) ∷ []
  sv f w₀ (instEmit (value a) n) refl = refl
  sv f w₀ (instEmit (mark m) n) ()

  uv : ∀ {A B : Set} (f : B → A → B) (w₀ : B × IE B) (x₀ : IE A) {c} → valuesOf (proj₂ (scanIE f w₀ x₀)) ≡ c ∷ []
     → Σ A λ a → valuesOf x₀ ≡ a ∷ []
  uv f w₀ (instEmit (value a) n) _ = a , refl
  uv f w₀ (instEmit (mark m) n) ()

------------------------------------------------------------------------
-- The record, scanned

module ScanTab {A B : Set} (f : B → A → B) (z : B)
  {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {s s* : Pos} (R : Rel P Q s s*) where

  module R = Rel R

  z* : B × IE B
  z* = z , marked begin

  S* : ℕ → Maybe (Tb.Listed (B × IE B))
  S* N = Scanned (scanIE f) z* (Q N)

  P′ : ℕ → Maybe (Tb.Listed B)
  P′ N = Scanned f z (P N)

  Q′ : ℕ → Maybe (Tb.Listed (IE B))
  Q′ N = Mapped proj₂ (S* N)

  q′← : ∀ {N y e₁} → ScanT (scanIE f) z* (TR (Q N)) y e₁ → TR (Q′ N) y (ev proj₂ e₁)
  q′← {N} sc = tr-map← proj₂ (S* N) (tr-scan← (scanIE f) z* (Q N) sc)

  q′→ : ∀ {N y e} → TR (Q′ N) y e → Σ (Ev (B × IE B)) λ e₁ → ScanT (scanIE f) z* (TR (Q N)) y e₁ × e ≡ ev proj₂ e₁
  q′→ {N} y with tr-map→ proj₂ (S* N) y
  ... | e₁ , y₁ , eq = e₁ , tr-scan→ (scanIE f) z* (Q N) y₁ , eq

  -- Agreement back through the scan, by the child's coherence.
  ag← : ∀ {N N′ k} → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → AgreeTo k (TR (P N)) (TR (P N′))
  ag← {N} {N′} ag = coh-of (tr-few (P N) (P N′)) R.cons R.cons
    (ag-≃ (sh-sc→ f z (P N)) (sh-sc← f z (P N)) (sh-sc→ f z (P N′)) (sh-sc← f z (P N′)) (sh-of ag))

  ag←* : ∀ {N N′ k} → AgreeTo k (TR (Q′ N)) (TR (Q′ N′)) → AgreeTo k (TR (Q N)) (TR (Q N′))
  ag←* {N} {N′} ag = coh-of (tr-few (Q N) (Q N′)) R.cons* R.cons*
    (ag-≃ (λ x → sh-sc→ (scanIE f) z* (Q N) (sh-map→ proj₂ (S* N) x)) (λ x → sh-map← proj₂ (S* N) (sh-sc← (scanIE f) z* (Q N) x))
          (λ x → sh-sc→ (scanIE f) z* (Q N′) (sh-map→ proj₂ (S* N′) x)) (λ x → sh-map← proj₂ (S* N′) (sh-sc← (scanIE f) z* (Q N′) x))
          (sh-of ag))

  ag→* : ∀ {N N′ k} → AgreeTo k (TR (Q N)) (TR (Q N′)) → AgreeTo k (TR (Q′ N)) (TR (Q′ N′))
  ag→* {N} {N′} ag = ag-map proj₂ (ag-sc (scanIE f) z* (Q N) (Q N′) ag)

  -- One cut.
  module At (N : ℕ) where
    t : EmissionSet A
    t = TR (P N)

    u : EmissionSet (IE A)
    u = TR (Q N)

    module C = Corr (R.corr N)

    φ : Pos → Pos
    φ = R.φ N

    fu : ∀ {y e e′} → t y e → t y e′ → e ≡ e′
    fu {y} {e} {e′} = R.func {N} {y} {e} {e′}

    fu* : ∀ {y e e′} → u y e → u y e′ → e ≡ e′
    fu* {y} {e} {e′} = R.func* {N} {y} {e} {e′}

    acc-val : ∀ {q b} → Acc f z t q b → Σ A λ a → t q (out a)
    acc-val = AccF.acc-val f z fu

    acc-func : ∀ {q q′ b b′} → q ≡ q′ → Acc f z t q b → Acc f z t q′ b′ → b ≡ b′
    acc-func = AccF.acc-func f z fu

    -- A plain value's image is a shown value.
    img-out : ∀ {k a} → t k (out a) → Σ (IE A) λ x₀ → u (φ k) (out x₀) × valuesOf x₀ ≡ a ∷ []
    img-out x with C.row→ x tt
    ... | inj₁ (e′ , y , mt) with proj₁ mt tt
    ...   | x₀ , refl , rd = x₀ , y , rd
    img-out x | inj₂ (() , _)

    φ-le : ∀ {k k′ e e′} → t k e → t k′ e′ → Unpinned e → Unpinned e′ → φ k′ ≼ φ k → k′ ≼ k
    φ-le x x′ un un′ le lt = le (C.mono x x′ un un′ lt)

    φ-back : ∀ {k₀ k e₀ e} → t k₀ e₀ → t k e → Unpinned e₀ → Unpinned e → φ k₀ ≺ φ k → k₀ ≺ k
    φ-back {k₀} {k} x₀ x u₀ un lt with ≼-or-≻ k k₀
    ... | inj₂ k₀k = k₀k
    ... | inj₁ le with ≼-split {k} {k₀} le
    ...   | inj₁ kk₀  = ⊥-elim (≺-absurd {φ k₀} {φ k} lt (C.mono x x₀ un u₀ kk₀))
    ...   | inj₂ refl = ⊥-elim (≺-irrefl {φ k} lt)

    φ-inj : ∀ {k k′ e e′} → t k e → t k′ e′ → Unpinned e → Unpinned e′ → φ k ≡ φ k′ → k ≡ k′
    φ-inj {k} {k′} x x′ un un′ eq =
      ≼-antisym {k} {k′} (φ-le x′ x un′ un (subst (φ k ≼_) eq (≼-refl {φ k}))) (φ-le x x′ un un′ (subst (_≼ φ k) eq (≼-refl {φ k})))

    -- An image is not a mark.
    mark-img : ∀ {y m n k′ a′} → u y (out (instEmit (mark m) n)) → t k′ (out a′) → φ k′ ≡ y → ⊥
    mark-img xm x′ refl with img-out x′
    ... | x₁ , y₁ , rd with fu* y₁ xm
    ...   | refl with rd
    ...     | ()

    open Values u using (Next)

    -- A value imaged before the next elaborated value is imaged at or
    -- before the previous one.
    below-prev : ∀ {y₀ y k′ a′} → Next y₀ y → t k′ (out a′) → φ k′ ≺ y → φ k′ ≼ y₀
    below-prev {y₀} {y} {k′} nx x′ lt y₀k′ = nx (proj₁ (proj₂ (img-out x′))) y₀k′ lt

    -- THE FOLDS MEET: the elaborated accumulator at `y` is the plain fold
    -- of the latest value imaged at or before it, or `z` if none is; a
    -- shown fold is a value's image, folded alike.
    Latest′ : Pos → Pos → Set
    Latest′ k y = ∀ {k′ a′} → t k′ (out a′) → φ k′ ≼ y → k′ ≼ k

    None : Pos → Set
    None y = ∀ {k′ a′} → t k′ (out a′) → φ k′ ≼ y → ⊥

    Before : Pos → B → Set
    Before y b = (Σ Pos λ k → Acc f z t k b × φ k ≼ y × Latest′ k y) ⊎ (b ≡ z × None y)

    Says : Pos → B × IE B → Set
    Says y w = ∀ {c} → valuesOf (proj₂ w) ≡ c ∷ [] → c ≡ proj₁ w × Σ Pos λ k → y ≡ φ k × Acc f z t k (proj₁ w)

    -- A shown elaborated value read back to its plain value.
    shown-val : ∀ {y a n} → u y (out (instEmit (value a) n)) → Σ Pos λ k → y ≡ φ k × t k (out a)
    shown-val xu with C.shown← xu (_ , refl)
    ... | k , e , eq , x , un , mt with m-back un mt (_ , refl)
    ...   | a′ , refl , refl = k , eq , x

    acc*→ : ∀ {y w} → Acc (scanIE f) z* u y w → Before y (proj₁ w) × Says y w
    acc*→ (acc₀ {a = instEmit (value a) n} xu mn) with shown-val xu
    ... | k , refl , x = inj₁ (k , pac , ≼-refl {φ k} , λ x′ le → φ-le x x′ tt tt le) , λ { refl → refl , k , refl , pac }
      where
        pac : Acc f z t k (f z a)
        pac = acc₀ x λ x′ k′k → mn (proj₁ (proj₂ (img-out x′))) (C.mono x′ x tt tt k′k)
    acc*→ {y} (acc₀ {a = instEmit (mark m) n} xu mn) =
      inj₂ (refl , λ {k′} x′ le → mark-img xu x′ (≼-antisym {φ k′} {y} le (mn (proj₁ (proj₂ (img-out x′)))))) , λ ()
    acc*→ (acc {q = y₀} {b = w₀} {a′ = instEmit (value a) n} ac xu lt nx) with shown-val xu
    ... | k , refl , x = inj₁ (k , pac , ≼-refl {φ k} , λ x′ le → φ-le x x′ tt tt le) , λ { refl → refl , k , refl , pac }
      where
        pac : Acc f z t k (f (proj₁ w₀) a)
        pac with proj₁ (acc*→ ac)
        ... | inj₁ (k₀ , ac₀ , le₀ , lat) =
          acc ac₀ x (φ-back (proj₂ (acc-val ac₀)) x tt tt (≼-≺-≺ {φ k₀} {y₀} {φ k} le₀ lt))
            λ x′ k₀k′ k′k → lat x′ (below-prev {y₀} {φ k} nx x′ (C.mono x′ x tt tt k′k)) k₀k′
        ... | inj₂ (eq , none) =
          subst (λ b → Acc f z t k (f b a)) (sym eq) (acc₀ x λ x′ k′k → none x′ (below-prev {y₀} {φ k} nx x′ (C.mono x′ x tt tt k′k)))
    acc*→ {y} (acc {q = y₀} {b = w₀} {a′ = instEmit (mark m) n} ac xu lt nx) = before (proj₁ (acc*→ ac)) , λ ()
      where
        shift : ∀ {k′ a′} → t k′ (out a′) → φ k′ ≼ y → φ k′ ≼ y₀
        shift {k′} x′ le y₀k′ = mark-img xu x′ (≼-antisym {φ k′} {y} le (nx (proj₁ (proj₂ (img-out x′))) y₀k′))

        before : Before y₀ (proj₁ w₀) → Before y (proj₁ w₀)
        before (inj₁ (k₀ , ac₀ , le₀ , lat)) = inj₁ (k₀ , ac₀ , ≼-trans {φ k₀} {y₀} {y} le₀ (≺→≼ {y₀} {y} lt) , λ x′ le → lat x′ (shift x′ le))
        before (inj₂ (eq , none))            = inj₂ (eq , λ x′ le → none x′ (shift x′ le))

    -- The elaborated value an accumulator folds last.
    last* : ∀ {y w} → Acc (scanIE f) z* u y w → Σ (IE A) λ x₀ → u y (out x₀) × Σ (B × IE B) λ w₀ → w ≡ scanIE f w₀ x₀
    last* (acc₀ xu _)     = _ , xu , z* , refl
    last* (acc _ xu _ _)  = _ , xu , _ , refl

    -- Shown alike.
    shown-w : ∀ {y w x₀ a} → Acc (scanIE f) z* u y w → u y (out x₀) → valuesOf x₀ ≡ a ∷ [] → valuesOf (proj₂ w) ≡ proj₁ w ∷ []
    shown-w ac y rd with last* ac
    ... | x₁ , xu , w₀ , refl with fu* y xu
    ...   | refl = sv f w₀ x₁ rd

    unshown-w : ∀ {y w c} → Acc (scanIE f) z* u y w → valuesOf (proj₂ w) ≡ c ∷ [] → Σ (IE A) λ x₀ → u y (out x₀) × Σ A λ a → valuesOf x₀ ≡ a ∷ []
    unshown-w ac rd with last* ac
    ... | x₁ , xu , w₀ , refl = x₁ , xu , uv f w₀ x₁ rd

    -- A plain fold's image folds it.
    acc-at : ∀ {k b} → Acc f z t k b → Σ (IE B) λ x → Acc (scanIE f) z* u (φ k) (b , x) × valuesOf x ≡ b ∷ []
    acc-at {k} {b} ac with acc-val ac
    ... | a , x with img-out x
    ...   | x₀ , y₀ , rd with fold? (scanIE f) z* (Q N) y₀
    ...     | w , ac* with shown-w ac* y₀ rd
    ...       | sw with proj₂ (acc*→ ac*) sw
    ...         | _ , k″ , eq , ac″ with φ-inj x (proj₂ (acc-val ac″)) tt tt eq
    ...           | refl with acc-func refl ac ac″
    ...             | refl = proj₂ w , ac* , sw

    -- Every elaborated row is scanned; a scanned row is its child's.
    row-to* : ∀ {y e′} → u y e′ → Σ (Ev (B × IE B)) λ e₁ → ScanT (scanIE f) z* u y e₁
    row-to* y = let (e₁ , sc , _) = row-to (scanIE f) z* (Q N) y in e₁ , sc

    shown-back : ∀ {l e′ e₁} → u l e′ → ScanT (scanIE f) z* u l e₁ → Shown (One valuesOf) (ev proj₂ e₁) → Shown (One valuesOf) e′
    shown-back y (sval ac*) sh with unshown-w ac* (proj₂ sh)
    ... | x₀ , xu , shx with fu* y xu
    ...   | refl = shx
    shown-back y (send xe) sh with fu* y xe
    ... | refl = tt

    -- The scanned image of each plain row.
    Imaged′ : Pos → Ev B → Set
    Imaged′ k e = Σ (Ev (IE B)) λ e″ → TR (Q′ N) (φ k) e″ × M e e″

    img-val : ∀ {k b} → Acc f z t k b → Imaged′ k (out b)
    img-val ac = let (x , ac* , rd) = acc-at ac in out x , q′← (sval ac*) , m-val rd

    img-skip : ∀ {k} → C.Imaged k skip → Imaged′ k skip
    img-skip (e′ , y , mt) = let (e₁ , sc) = row-to* y in ev proj₂ e₁ , q′← sc , ((λ ()) , λ _ sh → proj₂ mt (λ ()) (shown-back y sc sh))

    img-end : ∀ {k} → C.Imaged k end → Imaged′ k end
    img-end (e′ , y , mt) with proj₁ mt tt
    ... | refl = end , q′← (send y) , m-ee

    img-of : ∀ {k e₀ e} → t k e₀ → Unpinned e₀ → C.Imaged k e₀ → TR (P′ N) k e → Imaged′ k e
    img-of x₀ u₀ im x with tr-scan→ f z (P N) x
    ... | sval ac   = img-val ac
    ... | sstep xs with fu x₀ xs
    ...   | refl = img-skip im
    img-of x₀ u₀ im x | send xe with fu x₀ xe
    ... | refl = img-end im
    img-of x₀ u₀ im x | spin xp with fu x₀ xp
    ... | refl = ⊥-elim u₀

    back-row : ∀ {k e} → TR (P′ N) k e → Unpinned e → Σ (Ev A) λ e₀ → t k e₀ × Unpinned e₀
    back-row x un with tr-scan→ f z (P N) x
    ... | sval ac = let (_ , x₀) = acc-val ac in _ , x₀ , tt
    ... | sstep x₀ = _ , x₀ , tt
    ... | send x₀  = _ , x₀ , tt
    ... | spin _   = ⊥-elim un

    fwd-row : ∀ {k e₀} → t k e₀ → Unpinned e₀ → Σ (Ev B) λ e → TR (P′ N) k e × Unpinned e
    fwd-row {e₀ = out a} x un = let (b , ac) = fold? f z (P N) x in out b , tr-scan← f z (P N) (sval ac) , tt
    fwd-row {e₀ = skip}  x un = skip , tr-scan← f z (P N) (sstep x) , tt
    fwd-row {e₀ = end}   x un = end , tr-scan← f z (P N) (send x) , tt
    fwd-row {e₀ = pin r} x un = ⊥-elim un

    Homed′ : Pos → Set
    Homed′ k = instantOf k ≡ instantOf s
             ⊎ Σ Pos λ k₀ → Σ (Ev B) λ e₀ → TR (P′ N) k₀ e₀ × Unpinned e₀ × Imaged′ k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

    homed→ : ∀ {k} → C.Homed k → Homed′ k
    homed→ (inj₁ e) = inj₁ e
    homed→ (inj₂ (k₀ , e₀ , x , un , im , lt , ie)) =
      let (e , x′ , un′) = fwd-row x un in inj₂ (k₀ , e , x′ , un′ , img-of x un im x′ , lt , ie)

    PutAt′ : Pos → Set
    PutAt′ k = (Σ Pos λ l → Σ (Ev (IE B)) λ e′ → TR (Q′ N) l e′ × R.Put N k l) × Homed′ k

    put→ : ∀ {k} → C.PutAt k → PutAt′ k
    put→ ((l , e′ , y , pl) , h) = let (e₁ , sc) = row-to* y in (l , ev proj₂ e₁ , q′← sc , pl) , homed→ h

    Leads′ : Pos → Set
    Leads′ k = ∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

    leads→ : ∀ {k} → C.Leads k → Leads′ k
    leads→ ld x′ un′ ie′ = let (_ , x₀ , u₀) = back-row x′ un′ in ld x₀ u₀ ie′

    leads← : ∀ {k} → Leads′ k → C.Leads k
    leads← ld x′ un′ ie′ = let (_ , x₁ , u₁) = fwd-row x′ un′ in ld x₁ u₁ ie′

    row→′ : ∀ {k e} → TR (P′ N) k e → Unpinned e → Imaged′ k e ⊎ (e ≡ skip × PutAt′ k)
    row→′ x un with tr-scan→ f z (P N) x
    ... | sval ac = inj₁ (img-val ac)
    ... | sstep xs with C.row→ xs tt
    ...   | inj₁ im       = inj₁ (img-skip im)
    ...   | inj₂ (_ , pa) = inj₂ (refl , put→ pa)
    row→′ x un | send xe with C.row→ xe tt
    ... | inj₁ im      = inj₁ (img-end im)
    ... | inj₂ (() , _)
    row→′ x un | spin _ = ⊥-elim un

    PinAt′ : Pos → Pos → Set
    PinAt′ k p = (Σ Pos λ l → Σ Pos λ p′ → TR (Q′ N) l (pin p′) × R.Put N k l
                   × (∀ {k₀ b} → TR (P′ N) k₀ (out b) → φ k₀ ≺ p′ → k₀ ≺ p))
               × Homed′ k

    pin→′ : ∀ {k p} → TR (P′ N) k (pin p) → Live (TR (P′ N)) k → PinAt′ k p
    pin→′ x lv with tr-scan→ f z (P N) x
    ... | spin xp with C.pin→ xp (λ xe → lv (tr-scan← f z (P N) (send xe)))
    ...   | (l , p′ , y , pl , past) , h =
      (l , p′ , q′← (spin y) , pl , λ x′ lt → past (proj₂ (acc-val (sval-inv f z (tr-scan→ f z (P N) x′)))) lt) , homed→ h

    put-before′ : ∀ {k l k′ e′} → TR (P′ N) k skip → R.Put N k l → TR (P′ N) k′ e′ → Unpinned e′ → k ≺ k′ → l ≼ φ k′
    put-before′ x pl x′ un′ lt with tr-scan→ f z (P N) x
    ... | sstep xs = let (_ , x₀ , u₀) = back-row x′ un′ in C.put-before xs pl x₀ u₀ lt

    shown←′ : ∀ {l e′} → TR (Q′ N) l e′ → Shown (One valuesOf) e′
            → Σ Pos λ k → Σ (Ev B) λ e → l ≡ φ k × TR (P′ N) k e × Unpinned e × M e e′
    shown←′ y sh with q′→ {N} y
    ... | out w , sval ac* , refl with proj₂ (acc*→ ac*) (proj₂ sh)
    ...   | refl , k , eq , ac = k , out (proj₁ w) , eq , tr-scan← f z (P N) (sval ac) , tt , m-val (proj₂ sh)
    shown←′ y sh | end , send xe , refl with C.shown← xe tt
    ... | k , e , eq , x , un , mt with ends un mt
    ...   | refl = k , end , eq , tr-scan← f z (P N) (send x) , tt , m-ee

    leadsOr : ∀ {k m} → φ k ≼ m ⊎ C.Leads k → φ k ≼ m ⊎ Leads′ k
    leadsOr (inj₁ le) = inj₁ le
    leadsOr (inj₂ ld) = inj₂ (leads→ ld)

    row-of* : ∀ {y e₁} → ScanT (scanIE f) z* u y e₁ → Σ (Ev (IE A)) (u y)
    row-of* = row-of (scanIE f) z*

    place′ : ∀ {m e′} → TR (Q′ N) m e′ → Live (TR (Q′ N)) m
           → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev B) λ e → TR (P′ N) k e × Unpinned e × Imaged′ k e × (φ k ≼ m ⊎ Leads′ k) × instantOf (φ k) ≡ instantOf m
    place′ {m} y lv with q′→ {N} y
    ... | e₁ , sc , _ with C.place (proj₂ (row-of* sc)) (λ xe → lv (q′← (send xe)))
    ...   | inj₁ e = inj₁ e
    ...   | inj₂ (k , e₀ , x , un , im , le , ie) =
      let (e , x′ , un′) = fwd-row x un in inj₂ (k , e , x′ , un′ , img-of x un im x′ , leadsOr {k} {m} le , ie)

    corr′ : Corr s s* φ (R.Put N) (TR (P′ N)) (TR (Q′ N))
    corr′ = record
      { row→ = row→′ ; pin→ = pin→′ ; put-before = put-before′ ; shown← = shown←′ ; place = place′
      ; mono = λ x x′ un un′ lt → let (_ , x₀ , u₀) = back-row x un ; (_ , x₁ , u₁) = back-row x′ un′ in C.mono x₀ x₁ u₀ u₁ lt
      ; inst = λ x x′ un un′ → let (_ , x₀ , u₀) = back-row x un ; (_ , x₁ , u₁) = back-row x′ un′ in C.inst x₀ x₁ u₀ u₁
      ; home = λ x un → let (_ , x₀ , u₀) = back-row x un in C.home x₀ u₀ }

  -- Every elaborated row of the deeper cut, the shallower holds, once the
  -- plain scans agree everywhere: a value's fold is a plain fold both read.
  elab-all′ : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
  elab-all′ {N} {N′} le all y with q′→ {N′} y
  ... | _ , sstep x , refl = q′← (sstep (R.elab-all le (λ q → ag← (all q)) x))
  ... | _ , spin x , refl  = q′← (spin (R.elab-all le (λ q → ag← (all q)) x))
  ... | _ , send x , refl  = q′← (send (R.elab-all le (λ q → ag← (all q)) x))
  ... | out w , sval ac* , refl with At.last* N′ ac*
  ...   | x₀ , xu , w₀ , refl with R.elab-all le (λ q → ag← (all q)) xu
  ...     | xu′ with fold? (scanIE f) z* (Q N) xu′
  ...       | w′ , ac*′ with At.last* N ac*′
  ...         | x₁ , xu″ , w₁ , refl with R.func* xu′ xu″
  ...           | refl = subst (λ v → TR (Q′ N) _ (out v)) (same x₀ refl) (q′← (sval ac*′))
    where
      same : ∀ x → x ≡ x₀ → proj₂ (scanIE f w₁ x) ≡ proj₂ (scanIE f w₀ x)
      same (instEmit (mark m) n)  _    = refl
      same (instEmit (value a) n) refl with proj₂ (At.acc*→ N′ ac*) refl | proj₂ (At.acc*→ N ac*′) refl
      ... | _ , k , eq , pac | _ , k′ , eq′ , pac′ =
        let agk  = ag← {N′} {N} (all k)
            pacN = sval-inv f z (proj₁ (upto (scan-ag f z agk) (≼-refl {k})) (sval pac))
            xk   = proj₂ (At.acc-val N pacN)
            φeq  = R.φ-agree xk tt (AgreeTo-sym agk)
            kk′  = At.φ-inj N xk (proj₂ (At.acc-val N pac′)) tt tt (trans φeq (trans (sym eq) eq′))
        in cong (λ b → instEmit (value b) n) (sym (At.acc-func N kk′ pacN pac′))

  -- Two cuts' scans truncated before they differ.
  cons′ : ∀ {N N′} → (∀ {y y′ e′} {v : B} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ (TR (P′ N)) (TR (P′ N′))) → TR (P′ N) y (out v) → TR (P′ N′) y′ e′ → y ≼ y′ → TR (P′ N′) y (out v))
  cons′ {N} {N′} {y} below x x′ yy with tr-scan→ f z (P N) x
  ... | sval ac =
    let (_ , x₀) = At.acc-val N ac
        x₁ = R.cons (λ lt → ag← (below lt)) x₀ (proj₂ (row-of f z (tr-scan→ f z (P N′) x′))) yy
        agy = ag-at (λ lt → ag← (below lt)) R.func R.func x₀ x₁
    in tr-scan← f z (P N′) (proj₁ (upto (scan-ag f z agy) (≼-refl {y})) (sval ac))

  cons*′ : ∀ {N N′} → (∀ {y y′ e′} {v : IE B} → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ (TR (Q′ N)) (TR (Q′ N′))) → TR (Q′ N) y (out v) → TR (Q′ N′) y′ e′ → y ≼ y′ → TR (Q′ N′) y (out v))
  cons*′ {N} {N′} {y} below x x′ yy with q′→ {N} x
  ... | out w , sval ac* , refl =
    let (_ , xu , _ , _) = At.last* N ac*
        x₁ = R.cons* (λ lt → ag←* (below lt)) xu (proj₂ (At.row-of* N′ (proj₁ (proj₂ (q′→ {N′} x′))))) yy
        agy = ag-at (λ lt → ag←* (below lt)) R.func* R.func* xu x₁
    in q′← (proj₁ (upto (scan-ag (scanIE f) z* agy) (≼-refl {y})) (sval ac*))

  rel′ : Rel P′ Q′ s s*
  rel′ = record
    { φ = R.φ ; Put = R.Put ; corr = At.corr′
    ; φ-agree = λ {N} x un ag → let (_ , x₀ , u₀) = At.back-row N x un in R.φ-agree x₀ u₀ (ag← ag)
    ; bk = R.bk
    ; in-bk = λ {N} x un → let (_ , x₀ , u₀) = At.back-row N x un in R.in-bk x₀ u₀
    ; pb-few = R.pb-few
    ; elab-causal = λ {N} le x un ag → let (_ , x₀ , u₀) = At.back-row N x un in ag→* (R.elab-causal le x₀ u₀ (ag← ag))
    ; stable← = λ {N} {N′} le x un y ag* → let (_ , x₀ , u₀) = At.back-row N x un in
        ag-sc f z (P N′) (P N) (R.stable← le x₀ u₀ (proj₂ (At.row-of* N (proj₁ (proj₂ (q′→ {N} y))))) (ag←* ag*))
    ; stable-put = λ {N} le ag y pl → ag→* (R.stable-put le (ag← ag) (proj₂ (At.row-of* N (proj₁ (proj₂ (q′→ {N} y))))) pl)
    ; stable-lead = λ {N} le x un y ld w ie ag* → let (_ , x₀ , u₀) = At.back-row N x un in
        ag→* (R.stable-lead le x₀ u₀ (proj₂ (At.row-of* N (proj₁ (proj₂ (q′→ {N} y))))) (At.leads← N ld)
                (proj₂ (At.row-of* N (proj₁ (proj₂ (q′→ {N} w))))) ie (ag←* ag*))
    ; elab-all = elab-all′
    ; func = λ {N} x x′ → func-sc f z R.func (tr-scan→ f z (P N) x) (tr-scan→ f z (P N) x′)
    ; func* = λ {N} → func-map proj₂ (S* N) λ x x′ → func-sc (scanIE f) z* R.func* (tr-scan→ (scanIE f) z* (Q N) x) (tr-scan→ (scanIE f) z* (Q N) x′)
    ; flat = λ {N} x x′ → R.flat (proj₂ (row-of f z (tr-scan→ f z (P N) x))) (proj₂ (row-of f z (tr-scan→ f z (P N) x′)))
    ; flat* = λ {N} → flat-map proj₂ (S* N) λ x x′ → R.flat* (proj₂ (At.row-of* N (tr-scan→ (scanIE f) z* (Q N) x))) (proj₂ (At.row-of* N (tr-scan→ (scanIE f) z* (Q N) x′)))
    ; pin-in = λ {N} x → pin-sc (tr-scan→ f z (P N) x) R.pin-in
    ; pin-in* = λ {N} → pin-in-map proj₂ (S* N) λ x → pin-sc (tr-scan→ (scanIE f) z* (Q N) x) R.pin-in*
    ; cons = cons′
    ; cons* = cons*′
    ; got = λ N → got-bind (scanRows f z) (R.got N)
    ; got* = λ N → got-bind (Tb.mapRows proj₂) (got-bind (scanRows (scanIE f) z*) (R.got* N))
    ; after = λ {N} x → R.after (proj₂ (row-of f z (tr-scan→ f z (P N) x)))
    ; after* = λ {N} y → R.after* (proj₂ (At.row-of* N (proj₁ (proj₂ (q′→ {N} y)))))
    ; after-φ = λ {N} x un → let (_ , x₀ , u₀) = At.back-row N x un in R.after-φ x₀ u₀ }
    where
      pin-sc : ∀ {X C : Set} {g : C → X → C} {c : C} {t : EmissionSet X} {l r} → ScanT g c t l (pin r) → (∀ {l r} → t l (pin r) → T (inside r l)) → T (inside r l)
      pin-sc (spin x) pi = pi x

scan-tab : ∀ {A B} (f : B → A → B) (z : B) {P Q s s*} → Rel P Q s s*
         → Rel (λ N → bind (P N) λ l → just (scanRows f z l))
               (λ N → bind (bind (Q N) λ l → just (scanRows (scanIE f) (z , marked begin) l)) λ l → just (Tb.mapRows proj₂ l)) s s*
scan-tab f z R = ScanTab.rel′ f z R
