{-# OPTIONS --guardedness #-}

-- THE ELABORATION CARRIES EVERY SUBTERM.  The elaboration subscribes
-- each node of the plain program deeper, under wrappers of its own, so a
-- plain position and its elaborated counterpart differ by inserted path.
-- A map of positions `M` puts each plain position the run uses on the
-- elaborated subscription of the node it belongs to: step by step, a
-- label on a label of the same kind (a `sub` on the image of the
-- position it names), each after an insertion; an instant on the instant
-- of the image of its creator, at the same tick and label.  Such a map
-- (`Hom`) keeps the order and the instants, and reflects leading.
--
-- A subterm is carried (`CarryAt`) when every row of its plain run is
-- carried by a row of its elaborated run lying under its position's
-- image: the attribution of `simultaneous.Attribution`, read relative to
-- the environment, whose hots may hold rows the subterm only reads.
--
-- By induction on the program (`Carry`), under every environment of
-- carried binders, each subterm extends the map over its own world; the
-- run's map is their union.  A `defer` is reached through its
-- approximants, as in `simultaneous.Held`.
module simultaneous.Carry where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary using (yes; no)
open import denotation.Position using (_<ᵖ_)
open import denotation.Laws.Modulus using (≼-split)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Bool using (T)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; Path; Label; Instant; ix; sub; last; frame; cascade; _∙_; _⊕_; root; _<ˡ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; pin; Unpinned; EmissionSet; Den; hot; enter; Proper; DenEnv; Few; _≺_; ⟦_⟧)
open import denotation.Laws.Modulus using (≺-irrefl)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; W⁼; _⊑_; ⊕-identityʳ)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Spent; events; elaborated)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.HeldComb using (ev)
open import simultaneous.Attribution using (Live; Shown; Match; Attribution; Every; One; Reads)
open import denotation.Position using (_≟ᵖ_)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; annotate)
open Equivalence using (to; from)

------------------------------------------------------------------------
-- Maps of positions

PMap : Set₁
PMap = Pos → Pos → Set

_⊆ᴹ_ : PMap → PMap → Set
M ⊆ᴹ N = ∀ {x y} → M x y → N x y

-- A label on its image: a plain label on itself, a `sub` on the image of
-- the subscription it names.
data LabelAt (M : PMap) : Label → Label → Set where
  ix≈   : ∀ {i} → LabelAt M (ix i) (ix i)
  last≈ : LabelAt M last last
  sub≈  : ∀ {e e′} → M e e′ → LabelAt M (sub e) (sub e′)

-- An instant on its image: a cascade at the same tick and label, created
-- at the image of its creator.
data InstAt (M : PMap) : Instant → Instant → Set where
  frame≈   : InstAt M frame frame
  cascade≈ : ∀ {t e e′ l} → M e e′ → InstAt M (cascade t e l) (cascade t e′ l)

-- Both labels name subscriptions.
Joined : Label → Label → Set
Joined (sub _) (sub _) = ⊤
Joined _       _       = ⊥

-- A HOMOMORPHIC MAP: functional; each instant on its image; each step
-- after its parent's image, past an insertion; two `sub` siblings past
-- one insertion; any other two siblings kept apart, in order.
record Hom (M : PMap) : Set where
  field
    fun   : ∀ {x y y′} → M x y → M x y′ → y ≡ y′
    inst  : ∀ {x y} → M x y → InstAt M (instantOf x) (instantOf y)
    step  : ∀ {z a y} → M (z ⊕ [ a ]) y
          → Σ Pos λ z′ → Σ Path λ w → Σ Label λ a′ → M z z′ × y ≡ z′ ⊕ (w ++ [ a′ ]) × LabelAt M a a′
    joins : ∀ {z e d y y′} → M (z ⊕ [ sub e ]) y → M (z ⊕ [ sub d ]) y′
          → Σ Pos λ v → Σ Label λ a → Σ Label λ b → y ≡ v ⊕ [ a ] × y′ ≡ v ⊕ [ b ]
    split : ∀ {z a b y y′} → ¬ Joined a b → T (a <ˡ b) → M (z ⊕ [ a ]) y → M (z ⊕ [ b ]) y′ → y ≺ y′ × ¬ (y ⊑ y′)

-- THE MAP IS AN ORDER EMBEDDING, keeping instants apart exactly when
-- they were, and a position leads another's image only as it led it.
postulate
  hom-mono   : ∀ {M} → Hom M → ∀ {x x′ y y′} → M x y → M x′ y′ → x ≺ x′ → y ≺ y′
  hom-prefix : ∀ {M} → Hom M → ∀ {x x′ y y′} → M x y → M x′ y′ → y ⊑ y′ → x ⊑ x′
  hom-inst   : ∀ {M} → Hom M → ∀ {x x′ y y′} → M x y → M x′ y′ → (instantOf y ≡ instantOf y′ ⇔ instantOf x ≡ instantOf x′)

-- Two positions apart keep their order below them.
postulate
  apart : ∀ {y y′} → y ≺ y′ → ¬ (y ⊑ y′) → ∀ σ σ′ → (y ⊕ σ) ≺ (y′ ⊕ σ′)

instant-⊕ : ∀ x zs → instantOf (x ⊕ zs) ≡ instantOf x
instant-⊕ (i ∙ p) zs = refl

------------------------------------------------------------------------
-- A subterm carried

-- What an elaborated row is owed to.
data Cause : Set where
  row  : Pos → Cause
  env  : Pos → Cause
  both : Pos → Pos → Cause
  subs : Cause

-- `r` is owed to a plain row, in the image of its instant; to an
-- environment row it lies under; to a plain row and an environment row it
-- lies under; or to the subscribe instant.
Owes : ∀ {A : Set} → PMap → (Pos → Set) → EmissionSet A → Pos → Cause → Pos → Set
Owes {A} M HE t s′ (row k)    r = Σ (Ev A) (t k) × Σ Pos λ y → M k y × instantOf y ≡ instantOf r
Owes {A} M HE t s′ (env h)    r = HE h × h ⊑ r
Owes {A} M HE t s′ (both k h) r = Σ (Ev A) (t k) × HE h × h ⊑ r
Owes {A} M HE t s′ subs       r = instantOf r ≡ instantOf s′

-- Owed through the environment.
Read : Cause → Set
Read (env _)    = ⊤
Read (both _ _) = ⊤
Read (row _)    = ⊥
Read subs       = ⊥

-- `u`, subscribed at `s′`, carries `t`, subscribed at `s`, under the
-- environment hot rows `HP` (plain) and `HE` (elaborated), along `M`:
-- `simultaneous.Attribution.Attribution`'s fields, each carrier lying
-- under the image of the row it carries, a row of `u` placed or a pin of
-- `t` homed also by an instant of an environment row.  Each row of `u` is
-- owed to a cause, each cause owed finitely many, and a row owed through
-- the environment lies at or before every end.
record CarryAt {A Y : Set} (f : Y → List A) (M : PMap) (HP HE : Pos → Set) (t : EmissionSet A) (u : EmissionSet Y) (s s′ : Pos) : Set₁ where
  field
    Img     : Pos → Pos → Set
    ext     : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
    img     : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
            → Σ Pos λ l → Img k l × Σ (Ev Y) λ e′ → u l e′ × Few u l × Match Every (One f) (Reads f) e e′
    shown   : ∀ {l e} → u l e → Shown (One f) e → Live u l → Few u l
            → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → t k e₀ × Match Every (One f) (Reads f) e₀ e
    img-row : ∀ {k l} → Img k l → Σ (Ev A) λ e → t k e × Unpinned e
    img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    place   : ∀ {m e} → u m e → Live u m → Few u m
            → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m)
              ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
    live    : ∀ {k l} → Img k l → Live t k → Live u l
    few     : ∀ {k l} → Img k l → Few t k
    cause   : ∀ {r e} → u r e → Cause
    owes    : ∀ {r e} (ur : u r e) → Owes M HE t s′ (cause ur) r
    fib     : Cause → List Pos
    in-fib  : ∀ {r e} (ur : u r e) → r ∈ fib (cause ur)
    read    : ∀ {r e} (ur : u r e) → Read (cause ur) → Live u r
    bk      : Pos → List Pos
    in-bk   : ∀ {k l} → Img k l → k ∈ bk l
    pbk     : Pos → List Pos
    pinned  : ∀ {k p} → t k (pin p) → Live t k → (Σ Pos λ l → Σ (Ev Y) (u l) × k ∈ pbk l)
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → Σ (Ev A) λ e₀ → t k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

------------------------------------------------------------------------
-- From a carried run to its attribution

-- With no environment, a run carried along an order embedding, from a
-- subscription its map puts under the other's, is attributed: the order,
-- the instants and the home instant come from the map's.
module _ {A : Set} {M : PMap} (hm : Hom M) {t : EmissionSet A} {u : EmissionSet (IE A)} {s s′ : Pos}
         (flat : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥)
         (δ : Path) (at : M s (s′ ⊕ δ)) (c : CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) t u s s′) where
  open CarryAt c

  private
    led-row : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → k ⊑ k′ → ⊥
    led-row {k} i i′ kk ([] , refl) = ≺-irrefl {k} (subst (k ≺_) (⊕-identityʳ k) kk)
    led-row i i′ kk (l ∷ ys , refl) with img-row i | img-row i′
    ... | _ , tk , _ | _ , tk′ , _ = flat tk tk′

    inst-img : ∀ {k l} → Img k l → Σ Pos λ y → M k y × instantOf l ≡ instantOf y
    inst-img i with ext i
    ... | y , my , σ , refl = y , my , instant-⊕ y σ

    gather : (Pos → List Pos) → List Pos → List Pos
    gather g []       = []
    gather g (x ∷ xs) = g x ++ gather g xs

    ∈-gather : ∀ {x y} (g : Pos → List Pos) xs → x ∈ xs → y ∈ g x → y ∈ gather g xs
    ∈-gather g (x ∷ xs) (here refl) m = ∈-++⁺ˡ m
    ∈-gather g (x ∷ xs) (there n)   m = ∈-++⁺ʳ (g x) (∈-gather g xs n m)

    -- Finitely many rows before a carried row and after it: finitely
    -- many in all.
    rows-in : ∀ {k} → Few t k → Spent t (just k) → Σ (List Pos) λ ks → ∀ {k₁ e} → t k₁ e → k₁ ∈ ks
    rows-in {k} (ks₁ , f₁) (ks₂ , f₂) = ks₁ ++ k ∷ ks₂ , go
      where
        go : ∀ {k₁ e} → t k₁ e → k₁ ∈ ks₁ ++ k ∷ ks₂
        go {k₁} tk with T? (k₁ <ᵖ k)
        ... | yes lt = ∈-++⁺ˡ (f₁ tk lt)
        ... | no ge with ≼-split {k} {k₁} ge
        ...   | inj₁ gt   = ∈-++⁺ʳ ks₁ (there (proj₁ (f₂ tk gt)))
        ...   | inj₂ refl = ∈-++⁺ʳ ks₁ (here refl)

    -- Then each row of `u` is owed to one of them or to the subscription.
    every-row : ∀ {k l} → Img k l → Spent t (just k) → Σ (List Pos) λ ls → ∀ {r e} → u r e → r ∈ ls
    every-row i sp with rows-in (few i) sp
    ... | ks , f = gather (λ k₁ → fib (row k₁)) ks ++ fib subs , go
      where
        go : ∀ {r e} → u r e → r ∈ gather (λ k₁ → fib (row k₁)) ks ++ fib subs
        go ur with cause ur | owes ur | in-fib ur
        ... | row k₁   | (_ , tk) , _ | m = ∈-++⁺ˡ (∈-gather (λ k₂ → fib (row k₂)) ks (f tk) m)
        ... | env h    | () , _       | _
        ... | both _ _ | _ , () , _   | _
        ... | subs     | _            | m = ∈-++⁺ʳ (gather (λ k₂ → fib (row k₂)) ks) m

  img-mono′ : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → l ≺ l′
  img-mono′ i i′ kk with ext i | ext i′
  ... | y , my , σ , refl | y′ , my′ , σ′ , refl =
    apart (hom-mono hm my my′ kk) (λ yy → led-row i i′ kk (hom-prefix hm my my′ yy)) σ σ′

  inst′ : ∀ {k k′ l l′} → Img k l → Img k′ l′ → (instantOf l ≡ instantOf l′ ⇔ instantOf k ≡ instantOf k′)
  inst′ i i′ with inst-img i | inst-img i′
  ... | y , my , e | y′ , my′ , e′ = mk⇔
    (λ ll → to (hom-inst hm my my′) (trans (sym e) (trans ll e′)))
    (λ kk → trans e (trans (from (hom-inst hm my my′) kk) (sym e′)))

  home′ : ∀ {k l} → Img k l → (instantOf l ≡ instantOf s′ ⇔ instantOf k ≡ instantOf s)
  home′ i with inst-img i
  ... | y , my , e = mk⇔
    (λ ls → to (hom-inst hm my at) (trans (sym e) (trans ls (sym (instant-⊕ s′ δ)))))
    (λ ks → trans e (trans (from (hom-inst hm my at) ks) (instant-⊕ s′ δ)))

  attributed : Attribution Every (One valuesOf) (Reads valuesOf) t u s s′
  attributed = record
    { Img = Img ; img = img ; shown = shown ; img-row = img-row ; img-fun = img-fun
    ; img-mono = img-mono′ ; inst = inst′ ; home = home′
    ; place = λ {m} um lm fm → placed {m} (place um lm fm)
    ; live = live
    ; spent = λ i sp → let (ls , f) = every-row i sp in ls , λ ur _ → f ur
    ; bk = bk ; in-bk = in-bk ; pbk = pbk
    ; pinned = λ {k} tk lk → let (a , b) = pinned tk lk in a , homed {k} b }
    where
      placed : ∀ {m} → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m) ⊎ Σ Pos (λ h → ⊥ × instantOf h ≡ instantOf m)
             → instantOf m ≡ instantOf s′ ⊎ Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m
      placed (inj₁ e)             = inj₁ e
      placed (inj₂ (inj₁ kl))     = inj₂ kl
      placed (inj₂ (inj₂ (_ , () , _)))
      homed : ∀ {k} → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → Σ (Ev A) λ e₀ → t k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k) ⊎ Σ Pos (λ h → ⊥ × instantOf h ≡ instantOf k)
            → instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → t k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k
      homed (inj₁ e)             = inj₁ e
      homed (inj₂ (inj₁ k₀))     = inj₂ k₀
      homed (inj₂ (inj₂ (_ , () , _)))

------------------------------------------------------------------------
-- The induction

-- What an annotated row shows: the values of the emit it carries.
annValues : ∀ {X} → AIE X → List X
annValues (_ , just x) = valuesOf x
annValues (_ , nothing) = []

-- A connect's binder: the source, read hot past the connect at `at` in
-- the plain run and at `at′` annotated in the elaborated, carried along
-- the map.
record Bound (M₀ : PMap) {X : Set} (d : Den X) (d′ : Den (AIE X)) : Set₁ where
  field
    {Θ Θ′}  : List Set
    m       : Maybe ℕ
    src     : Obs Timeline Θ X
    σ       : ∀ {Y} → Y ∈ L.map AIE Θ → Y ∈ Θ′
    envP    : DenEnv Θ
    envE    : DenEnv Θ′
    at at′  : Pos
    carried : CarryAt annValues M₀ (Hots envP) (Hots envE) (enter (ev m src envP) (at ⊕ [ ix 1 ]))
                (enter (ev m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ])) (at ⊕ [ ix 1 ]) (at′ ⊕ [ ix 1 ])
    isP     : d ≡ hot (Proper (enter (ev m src envP) (at ⊕ [ ix 1 ])))
    isE     : d′ ≡ hot (Proper (enter (ev m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ])))

EnvRel : ∀ {Γ Δ} → PMap → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Γ → DenEnv Δ → Set₁
EnvRel {Γ} M₀ ρ envP envE = ∀ {X} (i : X ∈ Γ) → Bound M₀ (lookup envP i) (lookup envE (ρ (∈-map⁺ AIE i)))

-- The map so far touches neither world.
Fresh : (Pos → Set) → (Pos → Set) → PMap → Pos → Pos → Set
Fresh HP HE M₀ p p′ = ∀ {x y} → M₀ x y → ¬ W⁼ HP p x × ¬ W⁼ HE p′ y

-- What the map adds lies in the two worlds.
Within : (Pos → Set) → (Pos → Set) → PMap → PMap → Pos → Pos → Set
Within HP HE M₀ M p p′ = ∀ {x y} → M x y → M₀ x y ⊎ (W⁼ HP p x × W⁼ HE p′ y)

-- CARRIED under every environment of carried binders: subscribed at
-- admissible positions the map has not touched, the subterm extends the
-- map over its worlds, its subscription under the other's, and carries.
-- A record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record Carry (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor carry
  field carries : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE
                → ∀ M₀ → Hom M₀ → EnvRel M₀ ρ envP envE
                → ∀ p p′ → Ok (Hots envP) p → Ok (Hots envE) p′ → Fresh (Hots envP) (Hots envE) M₀ p p′
                → Σ PMap λ M → M₀ ⊆ᴹ M × Hom M × Within (Hots envP) (Hots envE) M₀ M p p′
                  × (Σ Path λ δ → M p (p′ ⊕ δ))
                  × CarryAt valuesOf M (Hots envP) (Hots envE) (enter (ev m o envP) p) (enter (ev m (elab ρ o) envE) p′) p p′

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER CARRIES its plain counterpart when its children
-- do, under the meaning and under every approximant alike.
postulate
  carry-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → Carry m ρ (cold c)
  carry-empty     : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → Carry m ρ (empty {A = A})
  carry-of        : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → Carry m ρ (of xs)
  carry-map       : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → Carry m ρ s → Carry m ρ (map f s)
  carry-scan      : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → Carry m ρ s → Carry m ρ (scan f z s)
  carry-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → Carry m ρ s → Carry m ρ (takeWhile i p s)
  carry-flatMap   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → Carry m ρ s
                  → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry m ρ′ (f a)) → Carry m ρ (flatMap op f s)
  carry-connect   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                  → Carry m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → Carry m ρ′ b) → Carry m ρ (connect s b)
  carry-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → Carry m ρ (connected i)

-- THE BOTTOM APPROXIMANT shows only skips; each further one is the body
-- under a `defer`'s guard; the meaning is the approximants' limit.
postulate
  carry-⊥    : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → Carry (just zero) ρ (defer l)
  carry-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
             → Carry (just n) ρ (Later.force l) → Carry (just (suc n)) ρ (defer l)
  carry-lim  : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
             → (∀ n → Carry (just n) ρ (defer l)) → Carry nothing ρ (defer l)

carry-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → Carry (just n) ρ o
carry-approx n       ρ (cold c)          = carry-cold (just n) ρ c
carry-approx n       ρ empty             = carry-empty (just n) ρ
carry-approx n       ρ (of xs)           = carry-of (just n) ρ xs
carry-approx n       ρ (map f s)         = carry-map (just n) ρ f s (carry-approx n ρ s)
carry-approx n       ρ (scan f z s)      = carry-scan (just n) ρ f z s (carry-approx n ρ s)
carry-approx n       ρ (takeWhile i p s) = carry-takeWhile (just n) ρ i p s (carry-approx n ρ s)
carry-approx n       ρ (flatMap op f s)  = carry-flatMap (just n) ρ op f s (carry-approx n ρ s) λ a ρ′ → carry-approx n ρ′ (f a)
carry-approx n       ρ (connect s b)     = carry-connect (just n) ρ s b (carry-approx n ρ s) λ ρ′ → carry-approx n ρ′ b
carry-approx n       ρ (connected i)     = carry-connected (just n) ρ i
carry-approx zero    ρ (defer l)         = carry-⊥ ρ l
carry-approx (suc n) ρ (defer l)         = carry-next n ρ l (carry-approx n ρ (Later.force l))

carry-⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → Carry nothing ρ o
carry-⟦⟧ ρ (cold c)          = carry-cold nothing ρ c
carry-⟦⟧ ρ empty             = carry-empty nothing ρ
carry-⟦⟧ ρ (of xs)           = carry-of nothing ρ xs
carry-⟦⟧ ρ (map f s)         = carry-map nothing ρ f s (carry-⟦⟧ ρ s)
carry-⟦⟧ ρ (scan f z s)      = carry-scan nothing ρ f z s (carry-⟦⟧ ρ s)
carry-⟦⟧ ρ (takeWhile i p s) = carry-takeWhile nothing ρ i p s (carry-⟦⟧ ρ s)
carry-⟦⟧ ρ (flatMap op f s)  = carry-flatMap nothing ρ op f s (carry-⟦⟧ ρ s) λ a ρ′ → carry-⟦⟧ ρ′ (f a)
carry-⟦⟧ ρ (connect s b)     = carry-connect nothing ρ s b (carry-⟦⟧ ρ s) λ ρ′ → carry-⟦⟧ ρ′ b
carry-⟦⟧ ρ (connected i)     = carry-connected nothing ρ i
carry-⟦⟧ ρ (defer l)         = carry-lim ρ l λ n → carry-approx n ρ (defer l)

------------------------------------------------------------------------
-- The whole run

-- Where `elaborate` subscribes the elaborated program: past its restamp,
-- the first lane of its concat and the first of its merge.
coreAt : Pos
coreAt = root ⊕ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

-- THE WRAPPER CARRIES THE CORE: the subscribe mark merged in, the
-- completion concatenated, the restamp, each rides in the core's instants
-- and shows nothing, and the whole ends where the core does.
postulate
  carry-wrap : ∀ {A} (o : SObs [] A) {M} → Hom M → ∀ δ → M root (coreAt ⊕ δ)
             → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (events o) (enter (⟦ elab (λ i → i) (plain o) ⟧ []) coreAt) root coreAt
             → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (events o) (elaborated o) root root

-- The empty map.
hom-∅ : Hom (λ _ _ → ⊥)
hom-∅ = record { fun = λ () ; inst = λ () ; step = λ () ; joins = λ () ; split = λ _ _ () }
