{-# OPTIONS --guardedness #-}

-- THE ELABORATION CARRIES EVERY SUBTERM.  The elaboration subscribes
-- each node of the plain program deeper, under wrappers of its own, so a
-- plain position and its elaborated counterpart differ by inserted path.
-- A map of positions `M` puts each plain position the run uses on the
-- elaborated subscription of the node it belongs to, keeping the order
-- and the instants, and reflecting leading (`Emb`).
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

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.All using (lookup; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary using (yes; no; Dec)
open import denotation.Position using (_<ᵖ_)
open import denotation.Laws.Modulus using (≼-split)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import denotation.Laws.Shows using (∈-stable)

open import Tree using (Obs; cold; map; flatMap; connect)
open import denotation.Position using (Pos; Path; Label; Instant; ix; sub; last; _∙_; _⊕_; root; lt; eq; gt; cmpLabel; cmpPath;
  cmpInstant; isLt; inside)
open import Data.List.Properties using (∷-injective)
open import denotation.Simultaneity using (eqˡ; eqⁱ)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; hot; coldAt; enter; Proper; DenEnv; Few;
  _≺_; _≼_; approx; module Op)
import denotation.Events as Evs
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-trans; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; W⁼; here; _⊑_; ⊕-identityʳ; ⊑-refl; ⊑-trans; ⊑-≼; ⊑-cmp; ⊑-inside;
  inside-⊑; ∙-inj; InvAt)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Spent)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.Attribution using (Live; Shown; Match; Attribution; Into; Every; One; Reads)
open import denotation.Position using (_≟ᵖ_)
open import simultaneous.Listing using (Listed; Listing)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; annotate; mapIE; elaborate)
open Equivalence using (to; from)

------------------------------------------------------------------------
-- Maps of positions

PMap : Set₁
PMap = Pos → Pos → Set

_⊆ᴹ_ : PMap → PMap → Set
M ⊆ᴹ N = ∀ {x y} → M x y → N x y

-- AN ORDER EMBEDDING: keeping the order, reflecting leading, and keeping
-- instants apart exactly when they were.  A global law, since the
-- elaboration does not nest as the plain run does.
--
-- DEAD ROUTE: a homomorphic map, each step after its parent's image past
--   an insertion, siblings kept apart, from which these would follow by
--   recursion on positions.  A concat's queued lane hangs, plain, under
--   the previous lane's end; elaborated, under the end of that lane's
--   wrapper, which in a synchronous run is the wrapper's outer end, a
--   sibling branch of the inner lane's end.  No image of the plain end
--   both prefixes the queued lane's and follows the first lane's
--   subscription.
record Emb (M : PMap) : Set where
  field
    fun     : ∀ {x y y′} → M x y → M x y′ → y ≡ y′
    mono    : ∀ {x x′ y y′} → M x y → M x′ y′ → x ≺ x′ → y ≺ y′
    reflect : ∀ {x x′ y y′} → M x y → M x′ y′ → y ⊑ y′ → x ⊑ x′
    inst    : ∀ {x x′ y y′} → M x y → M x′ y′ → (instantOf y ≡ instantOf y′ ⇔ instantOf x ≡ instantOf x′)

private
  lt-of : ∀ {c} → T (isLt c) → c ≡ lt
  lt-of {lt} _ = refl

  path-apart : ∀ p q σ σ′ → cmpPath p q ≡ lt → (∀ zs → q ≡ p ++ zs → ⊥) → cmpPath (p ++ σ) (q ++ σ′) ≡ lt
  path-apart []      q       σ σ′ h  np = ⊥-elim (np q refl)
  path-apart (a ∷ p) (b ∷ q) σ σ′ h  np with cmpLabel a b in c
  ... | lt = refl
  ... | eq with eqˡ a b c
  ...   | refl = path-apart p q σ σ′ h (λ zs e → np zs (cong (a ∷_) e))
  path-apart (a ∷ p) (b ∷ q) σ σ′ () np | gt

-- Two positions apart keep their order below them.
apart : ∀ {y y′} → y ≺ y′ → ¬ (y ⊑ y′) → ∀ σ σ′ → (y ⊕ σ) ≺ (y′ ⊕ σ′)
apart {i ∙ p} {j ∙ q} h np σ σ′ with cmpInstant i j in c
... | lt = tt
... | eq with eqⁱ i j c
...   | refl = subst (λ x → T (isLt x)) (sym (path-apart p q σ σ′ (lt-of h) (λ zs e → np (zs , cong (i ∙_) e)))) tt
apart {i ∙ p} {j ∙ q} () np σ σ′ | gt

instant-⊕ : ∀ x zs → instantOf (x ⊕ zs) ≡ instantOf x
instant-⊕ (i ∙ p) zs = refl

_∪ᴹ_ : PMap → PMap → PMap
(M ∪ᴹ N) x y = M x y ⊎ N x y

-- `x` lies at or under a position of the world with `p`.
Below : (Pos → Set) → Pos → Pos → Set
Below H p x = Σ Pos λ w → W⁼ H p w × w ⊑ x

-- The map so far touches nothing at or under the world but the
-- subscription itself.
Fresh : (Pos → Set) → PMap → Pos → Set
Fresh H M₀ p = ∀ {x y} → M₀ x y → Below H p x → x ≡ p

private
  module Under {M₀ N : PMap} {p p₀ p′ : Pos} (E₀ : Emb M₀) (at : ∀ {x y} → M₀ x y → p ⊑ x → x ≡ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′) (E : Emb N)
               (sh : ∀ {x y} → N x y → Σ Label λ a → Σ Path λ σ → Σ Label λ b → Σ Path λ σ′ → x ≡ p ⊕ (a ∷ σ) × y ≡ p′ ⊕ (b ∷ σ′)) where

    -- What `N` adds lies strictly under the subscription and its image.
    dom : ∀ {x y} → N x y → p ⊑ x × p ≺ x
    dom n with sh n
    ... | a , σ , _ , _ , refl , _ = (a ∷ σ , refl) , ≺-ext p σ

    img : ∀ {x y} → N x y → p₀ ⊑ y × p₀ ≺ y
    img n with sh n
    ... | _ , _ , b , σ′ , _ , refl = ⊑-trans pp (b ∷ σ′ , refl) , ≼-≺-≺ {p₀} {p′} {p′ ⊕ (b ∷ σ′)} (⊑-≼ pp) (≺-ext p′ σ′)

    at-img : ∀ {x y} → M₀ x y → p ⊑ x → y ≡ p₀
    at-img m px with at m px
    ... | refl = Emb.fun E₀ m m₀

    -- An old position not under the subscription is apart from it.
    side : ∀ {x} → ¬ (p ⊑ x) → x ≡ p → ⊥
    side np refl = np (⊑-refl p)

    -- Below an image strictly under `p₀`, an old image before `p₀` stays before.
    before : ∀ {y₀ y} → y₀ ≺ p₀ → p₀ ⊑ y → p₀ ≺ y → y₀ ≺ y
    before {y₀} {y} yp (δ , refl) py with T? (inside y₀ p₀)
    ... | yes i = ≼-≺-≺ {y₀} {p₀} {y} (⊑-≼ (inside-⊑ y₀ p₀ i)) py
    ... | no ni = subst (_≺ (p₀ ⊕ δ)) (⊕-identityʳ y₀) (apart {y₀} {p₀} yp (λ q → ni (⊑-inside q)) [] δ)

    mono₀ : ∀ {x₀ y₀ x y} → M₀ x₀ y₀ → N x y → x₀ ≺ x → y₀ ≺ y
    mono₀ {x₀} {y₀} {x} {y} m n xx with T? (inside p x₀)
    ... | yes i rewrite at-img m (inside-⊑ p x₀ i) = proj₂ (img n)
    ... | no ni with T? (x₀ <ᵖ p)
    ...   | yes xp = before {y₀} {y} (Emb.mono E₀ m m₀ xp) (proj₁ (img n)) (proj₂ (img n))
    ...   | no px with ≼-split {p} {x₀} px
    ...     | inj₂ e = ⊥-elim (side (λ q → ni (⊑-inside q)) (sym e))
    ...     | inj₁ lt′ with dom n
    ...       | (σ , refl) , _ =
      ⊥-elim (≺-irrefl {x₀} (≺-trans {x₀} {p ⊕ σ} {x₀} xx
        (subst ((p ⊕ σ) ≺_) (⊕-identityʳ x₀) (apart {p} {x₀} lt′ (λ q → ni (⊑-inside q)) σ []))))

    mono₁ : ∀ {x y x₀ y₀} → N x y → M₀ x₀ y₀ → x ≺ x₀ → y ≺ y₀
    mono₁ {x} {y} {x₀} {y₀} n m xx with T? (inside p x₀)
    ... | yes i rewrite at m (inside-⊑ p x₀ i) = ⊥-elim (≺-irrefl {x} (≺-trans {x} {p} {x} xx (proj₂ (dom n))))
    ... | no ni with proj₁ (img n)
    ...   | δ , refl =
      subst ((p₀ ⊕ δ) ≺_) (⊕-identityʳ y₀)
        (apart {p₀} {y₀} (Emb.mono E₀ m₀ m (≺-trans {p} {x} {x₀} (proj₂ (dom n)) xx))
               (λ q → ni (⊑-inside (Emb.reflect E₀ m₀ m q))) δ [])

    reflect₀ : ∀ {x₀ y₀ x y} → M₀ x₀ y₀ → N x y → y₀ ⊑ y → x₀ ⊑ x
    reflect₀ {x₀} {y₀} m n yy with ⊑-cmp y₀ p₀ yy (proj₁ (img n))
    ... | inj₁ yp = ⊑-trans (Emb.reflect E₀ m m₀ yp) (proj₁ (dom n))
    ... | inj₂ py rewrite at m (Emb.reflect E₀ m₀ m py) = proj₁ (dom n)

    reflect₁ : ∀ {x y x₀ y₀} → N x y → M₀ x₀ y₀ → y ⊑ y₀ → x ⊑ x₀
    reflect₁ {x} {y} n m yy with Emb.reflect E₀ m₀ m (⊑-trans (proj₁ (img n)) yy)
    ... | px = ⊥-elim (⊑-≼ (subst (y ⊑_) (at-img m px) yy) (proj₂ (img n)))

    inst₀ : ∀ {x₀ y₀ x y} → M₀ x₀ y₀ → N x y → (instantOf y₀ ≡ instantOf y ⇔ instantOf x₀ ≡ instantOf x)
    inst₀ {x₀} {y₀} {x} {y} m n with proj₁ (dom n) | proj₁ (img n)
    ... | σ , refl | δ , refl rewrite instant-⊕ p σ | instant-⊕ p₀ δ = Emb.inst E₀ m m₀

    sym⇔ : ∀ {a b c d : Instant} → (a ≡ b ⇔ c ≡ d) → (b ≡ a ⇔ d ≡ c)
    sym⇔ e = mk⇔ (λ q → sym (to e (sym q))) (λ q → sym (from e (sym q)))

    emb : Emb (M₀ ∪ᴹ N)
    emb = record
      { fun     = λ { (inj₁ m) (inj₁ m′) → Emb.fun E₀ m m′
                    ; (inj₂ n) (inj₂ n′) → Emb.fun E n n′
                    ; (inj₁ m) (inj₂ n) → ⊥-elim (≺-irrefl {p} (subst (p ≺_) (at m (proj₁ (dom n))) (proj₂ (dom n))))
                    ; (inj₂ n) (inj₁ m) → ⊥-elim (≺-irrefl {p} (subst (p ≺_) (at m (proj₁ (dom n))) (proj₂ (dom n)))) }
      ; mono    = λ { (inj₁ m) (inj₁ m′) → Emb.mono E₀ m m′ ; (inj₂ n) (inj₂ n′) → Emb.mono E n n′
                    ; (inj₁ m) (inj₂ n) → mono₀ m n ; (inj₂ n) (inj₁ m) → mono₁ n m }
      ; reflect = λ { (inj₁ m) (inj₁ m′) → Emb.reflect E₀ m m′ ; (inj₂ n) (inj₂ n′) → Emb.reflect E n n′
                    ; (inj₁ m) (inj₂ n) → reflect₀ m n ; (inj₂ n) (inj₁ m) → reflect₁ n m }
      ; inst    = λ { (inj₁ m) (inj₁ m′) → Emb.inst E₀ m m′ ; (inj₂ n) (inj₂ n′) → Emb.inst E n n′
                    ; (inj₁ m) (inj₂ n) → inst₀ m n ; (inj₂ n) (inj₁ m) → sym⇔ (inst₀ m n) }
      }

-- A MAP GROWN UNDER A SUBSCRIPTION it holds fresh, at an image the
-- elaborated subscription extends: what it adds lies strictly under both.
emb-under : ∀ {H M₀ N p p₀ p′} → Emb M₀ → Fresh H M₀ p → M₀ p p₀ → p₀ ⊑ p′ → Emb N
          → (∀ {x y} → N x y → Σ Label λ a → Σ Path λ σ → Σ Label λ b → Σ Path λ σ′ → x ≡ p ⊕ (a ∷ σ) × y ≡ p′ ⊕ (b ∷ σ′))
          → Emb (M₀ ∪ᴹ N)
emb-under E₀ fr m₀ pp E sh = Under.emb E₀ (λ m px → fr m (_ , here , px)) m₀ pp E sh

-- The same, grown under a position the map pairs nothing strictly under.
emb-at : ∀ {M₀ N p p₀ p′} → Emb M₀ → (∀ {x y} → M₀ x y → p ⊑ x → x ≡ p) → M₀ p p₀ → p₀ ⊑ p′ → Emb N
       → (∀ {x y} → N x y → Σ Label λ a → Σ Path λ σ → Σ Label λ b → Σ Path λ σ′ → x ≡ p ⊕ (a ∷ σ) × y ≡ p′ ⊕ (b ∷ σ′))
       → Emb (M₀ ∪ᴹ N)
emb-at E₀ at m₀ pp E sh = Under.emb E₀ at m₀ pp E sh

-- An embedding is pairwise: any two pairs lie in one embedding.
emb-pairs : ∀ {M} → (∀ {x y x′ y′} → M x y → M x′ y′ → Σ PMap λ K → Emb K × K x y × K x′ y′) → Emb M
emb-pairs h = record
  { fun     = λ m m′ → let (_ , E , k , k′) = h m m′ in Emb.fun E k k′
  ; mono    = λ m m′ → let (_ , E , k , k′) = h m m′ in Emb.mono E k k′
  ; reflect = λ m m′ → let (_ , E , k , k′) = h m m′ in Emb.reflect E k k′
  ; inst    = λ m m′ → let (_ , E , k , k′) = h m m′ in Emb.inst E k k′ }

------------------------------------------------------------------------
-- A subterm carried

-- An unpinned row, classically: a pin's home.
Home : ∀ {A : Set} → EmissionSet A → Pos → Set
Home {A} t k = ¬ ¬ Σ (Ev A) λ e → t k e × Unpinned e

-- A carrier near a row: at or before it, or a row listed up to.
Near : ∀ {Y : Set} → EmissionSet Y → Pos → Pos → Set
Near {Y} u m l = l ≼ m ⊎ (Σ (Ev Y) (u l) × Listed u l)

-- Every row, listed exactly.
Whole : ∀ {A : Set} → EmissionSet A → Set
Whole t = Σ (List Pos) λ ks → (∀ {k e} → t k e → k ∈ ks) × (∀ {k} → k ∈ ks → Σ _ (t k))

-- Every row listed: those before any position listed.
whole-listed : ∀ {X : Set} {a : EmissionSet X} → Whole a → ∀ {v} → Listed a v
whole-listed (ks , F , B) {v} =
  filter (λ k → T? (k <ᵖ v)) ks
  , (λ y kv → ∈-filter⁺ (λ k → T? (k <ᵖ v)) (F y) kv)
  , λ m → let (m′ , kv) = ∈-filter⁻ (λ k → T? (k <ᵖ v)) m in kv , B m′

-- The rows listed before a row listed before.
sub-listed : ∀ {X : Set} {a : EmissionSet X} {w v} → Listed a w → v ≺ w → Listed a v
sub-listed {w = w} {v} (ks , F , B) vw =
  filter (λ k → T? (k <ᵖ v)) ks
  , (λ {k} y kv → ∈-filter⁺ (λ k → T? (k <ᵖ v)) (F y (≺-trans {k} {v} {w} kv vw)) kv)
  , λ m → let (m′ , kv) = ∈-filter⁻ (λ k → T? (k <ᵖ v)) m in kv , proj₂ (B m′)

listed-≼ : ∀ {X : Set} {a : EmissionSet X} {w v} → Listed a w → v ≼ w → Listed a v
listed-≼ {w = w} {v} L vw with ≼-split {v} {w} vw
... | inj₁ v≺w  = sub-listed L v≺w
... | inj₂ refl = L

few-sub : ∀ {X : Set} {a : EmissionSet X} {w v} → Few a w → v ≺ w → Few a v
few-sub {w = w} {v} (ks , F) vw = ks , λ {k} y kv → F y (≺-trans {k} {v} {w} kv vw)

-- The plain row a carrier shows a value of is that value.
match-val : ∀ {A : Set} {e₀ : Ev A} {a} {n : Pos} → Match Every (One valuesOf) (Reads valuesOf) e₀ (out (instEmit (value a) n)) → e₀ ≡ out a
match-val {e₀ = out _} (cr , _) with cr tt
... | _ , refl , refl = refl
match-val {e₀ = end}   (cr , _) with cr tt
... | ()
match-val {e₀ = skip}  (_ , ns) = ⊥-elim (ns (λ ()) (_ , refl))
match-val {e₀ = pin _} (_ , ns) = ⊥-elim (ns (λ ()) (_ , refl))

-- The carrier of a plain value shows it.
carried-val : ∀ {A : Set} {a : A} {e₁ : Ev (IE A)} → Match Every (One valuesOf) (Reads valuesOf) (out a) e₁
            → Σ Pos λ n → e₁ ≡ out (instEmit (value a) n)
carried-val (cr , _) with cr tt
... | instEmit (value _) n , refl , refl = n , refl
... | instEmit (mark _) _  , refl , ()

-- The plain row carried by an end is an end.
match-end : ∀ {A : Set} {e₀ : Ev A} → Match Every (One {X = IE A} valuesOf) (Reads valuesOf) e₀ end → e₀ ≡ end
match-end {e₀ = out _} (cr , _) with cr tt
... | _ , () , _
match-end {e₀ = end}   _        = refl
match-end {e₀ = skip}  (_ , ns) = ⊥-elim (ns (λ ()) tt)
match-end {e₀ = pin _} (_ , ns) = ⊥-elim (ns (λ ()) tt)

-- CARRIED INTO ITS INSTANT, along `Img`: put by `PB` on a row of `u`
-- with finitely many before it, and in the subscription's instant, a
-- carried row's before it, or an environment row's.  A pin, and a skip
-- a reader hears from one, is carried so: pins are not carried in order.
IntoAt : ∀ {Y : Set} → (Pos → Pos → Set) → EmissionSet Y → (Pos → Pos → Set) → (Pos → Set) → Pos → Pos → Set
IntoAt {Y} Img u PB HP s k =
  (Σ Pos λ l → Σ (Ev Y) (u l) × Listed u l × PB k l)
  × (instantOf k ≡ instantOf s
     ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ (Ev Y) (u l₀) × Listed u l₀)
     ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

-- `u`, subscribed at `s′`, carries `t`, subscribed at `s`, under the
-- environment hot rows `HP` (plain) and `HE` (elaborated), along `M`:
-- `simultaneous.Attribution.Attribution`'s fields, each carrier lying
-- under the image of the row it carries, a row of `u` placed or a pin of
-- `t` homed also by an instant of an environment row.
--
-- A ROW IS CARRIED FROM ITS LISTING, onto a carrier listed too, a pin's
-- included: under its environment's listing too, since pins are carried
-- out of order (a queued lane's subscribe pin falls past values the plain
-- run puts after it), so the pin's own listing does not reach the rows
-- before its carrier.  A row only witnessed to exist (the carried row, a pin's home) is so
-- classically, and a pin's home lies before its connect, as does whatever
-- a carrier before the elaborated connect carries.  A closed run is
-- listed wherever few rows precede (`simultaneous.Listing.listed`), and
-- there each classical row is found among the listed ones (`attributed`).
--
-- A ROW IS CARRIED UNDER ITS ENVIRONMENT'S LISTING (`LP`): a reader's
-- carrier is its hot's, and the hot's carry asks the rows before the
-- reader's subscription listed, which only the connect's echoes list.
-- Without it a reader's image would decide which of finitely many
-- positions before its subscription hold the hot's rows.  Carried
-- classically (`img¬¬`), a row needs only few rows before it: what
-- reading back past a carrier asks of each earlier row.
--
-- A ROW OF `u` IS PLACED FROM ITS LISTING, by a carrier near it: at or
-- before it, or listed up to.  `u` HAS FEW ROWS IN ALL when `t` and the
-- environment do and `t` has no end: a row past a carrier is not listed
-- from the rows past the row it carries, which a former hiding rows past
-- a failure need not have; and a run with an end has its exit.  Each
-- names a position from listings alone, so such a former decides where
-- the failure lies.
--
-- DEAD ROUTE: each row from finitely many before it, outright.  A scan's
--   row needs its source's values before it listed, and a subterm's run is
--   not listed from few rows: a lane reading a hot past an accumulation of
--   its rows (hidden from the subterm by a takeWhile failed early) meets a
--   later row iff the accumulation is finite, so a scan over that lane and
--   a timer has a row at the timer whose state decides it.
--
-- DEAD ROUTE: `whole` for a run with an end.  A takeWhile keeps its
--   source's pins past its failure whose connect lies before it; no field
--   lists the elaborated ones, the elaborated hot bursting for its marks
--   too.
record CarryAt {A Y : Set} (f : Y → List A) (M : PMap) (HP HE LP : Pos → Set) (t : EmissionSet A) (u : EmissionSet Y) (s s′ : Pos) : Set₁ where
  field
    Img     : Pos → Pos → Set
    ext     : ∀ {k l} → Img k l → Σ Pos λ y → M k y × y ⊑ l
    PB      : Pos → Pos → Set
    pb-few  : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB k l → k ∈ ks
    img     : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
            → (Σ Pos λ l → Img k l × Σ (Ev Y) λ e′ → u l e′ × Listed u l × Match Every (One f) (Reads f) e e′)
              ⊎ (e ≡ skip × IntoAt Img u PB HP s k)
    img¬¬   : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
            → ¬ ¬ ((Σ Pos λ l → Img k l × Σ (Ev Y) λ e′ → u l e′ × Match Every (One f) (Reads f) e e′) ⊎ e ≡ skip)
    shown   : ∀ {l e} → u l e → Shown (One f) e → Live u l → Few u l
            → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → t k e₀ × Match Every (One f) (Reads f) e₀ e
    img-row : ∀ {k l} → Img k l → ¬ ¬ Σ (Ev A) λ e → t k e × Unpinned e
    img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    place   : ∀ {m e} → u m e → Live u m → Listed u m
            → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u m l)
              ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
    live    : ∀ {k l} → Img k l → Live t k → Live u l
    few     : ∀ {k l} → Img k l → Few t k
    whole   : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Whole u
    bk      : Pos → List Pos
    in-bk   : ∀ {k l} → Img k l → k ∈ bk l
    pinned  : ∀ {k p} → t k (pin p) → Live t k
            → (Σ Pos λ l → Σ Pos λ p′ → u l (pin p′) × PB k l × (∀ {k′ l′} → Img k′ l′ → l′ ≺ p′ → k′ ≺ p)
                × (Listed t k → LP k → Listed u l))
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)

------------------------------------------------------------------------
-- Relabelled rows

-- An event and its relabelling: the same kind, a pin of the same.
data Kin {A B : Set} : Ev A → Ev B → Set where
  k-out  : ∀ {a b} → Kin (out a) (out b)
  k-skip : Kin skip skip
  k-pin  : ∀ {r} → Kin (pin r) (pin r)
  k-end  : Kin end end

kin-refl : ∀ {X : Set} (e : Ev X) → Kin e e
kin-refl (out _) = k-out
kin-refl skip    = k-skip
kin-refl (pin _) = k-pin
kin-refl end     = k-end

private
  module Rows {X Z : Set} {a : EmissionSet X} {b : EmissionSet Z} {Rel : Pos → Ev X → Ev Z → Set}
              (kn : ∀ {k e e′} → Rel k e e′ → Kin e e′)
              (to : ∀ {k e} → a k e → Σ (Ev Z) λ e′ → b k e′ × Rel k e e′)
              (fro : ∀ {k e′} → b k e′ → Σ (Ev X) λ e → a k e × Rel k e e′) where
    live← : ∀ {k} → Live b k → Live a k
    live← {k} lb {c} ac with to ac
    ... | _ , bc , r with kn r
    ...   | k-end = lb {c} bc

    few→ : ∀ {k} → Few a k → Few b k
    few→ (ks , F) = ks , λ bk kk → F (proj₁ (proj₂ (fro bk))) kk

    few← : ∀ {k} → Few b k → Few a k
    few← (ks , F) = ks , λ ak kk → F (proj₁ (proj₂ (to ak))) kk

    lst← : ∀ {k} → Listed b k → Listed a k
    lst← (ks , F , B) = ks , (λ ak kk → F (proj₁ (proj₂ (to ak))) kk) , λ m → proj₁ (B m) , proj₁ (fro (proj₂ (proj₂ (B m)))) , proj₁ (proj₂ (fro (proj₂ (proj₂ (B m)))))

    ended← : (∀ {c} → b c end → ⊥) → ∀ {c} → a c end → ⊥
    ended← ne ac with to ac
    ... | _ , bc , r with kn r
    ...   | k-end = ne bc

    whole← : Whole b → Whole a
    whole← (ks , F , B) = ks , (λ ak → F (proj₁ (proj₂ (to ak)))) , λ m → proj₁ (fro (proj₂ (B m))) , proj₁ (proj₂ (fro (proj₂ (B m))))

-- A RELABELLING LIFTED ONLY AT A LISTED ROW, and refutably elsewhere: a
-- scan's, whose state folds the rows before.
module Lifts {X Z : Set} {a : EmissionSet X} {b : EmissionSet Z} {Rel : Pos → Ev X → Ev Z → Set}
             (kn : ∀ {k e e′} → Rel k e e′ → Kin e e′)
             (toL : ∀ {k e} → Listed a k → a k e → Σ (Ev Z) λ e′ → b k e′ × Rel k e e′)
             (to¬¬ : ∀ {k e} → a k e → ¬ ¬ Σ (Ev Z) λ e′ → b k e′ × Rel k e e′)
             (to-end : ∀ {k} → a k end → b k end)
             (fro : ∀ {k e′} → b k e′ → Σ (Ev X) λ e → a k e × Rel k e e′) where
  live→ : ∀ {k} → Live a k → Live b k
  live→ {k} la {c} bc with fro bc
  ... | _ , ac , r with kn r
  ...   | k-end = la {c} ac

  live← : ∀ {k} → Live b k → Live a k
  live← lb ac = lb (to-end ac)

  few← : ∀ {k} → Few b k → Few a k
  few← (ks , F) = ks , λ ak kk → ∈-stable λ ni → to¬¬ ak λ { (_ , bk , _) → ni (F bk kk) }

  lst→ : ∀ {k} → Listed a k → Listed b k
  lst→ (ks , F , B) = ks , (λ bk kk → F (proj₁ (proj₂ (fro bk))) kk)
                    , λ m → proj₁ (B m) , _ , proj₁ (proj₂ (toL (sub-listed (ks , F , B) (proj₁ (B m))) (proj₂ (proj₂ (B m)))))

  lst← : ∀ {k} → Listed b k → Listed a k
  lst← (ks , F , B) = ks , (λ ak kk → ∈-stable λ ni → to¬¬ ak λ { (_ , bk , _) → ni (F bk kk) })
                    , λ m → proj₁ (B m) , _ , proj₁ (proj₂ (fro (proj₂ (proj₂ (B m)))))

  whole→ : Whole a → Whole b
  whole→ W = proj₁ W , (λ bk → proj₁ (proj₂ W) (proj₁ (proj₂ (fro bk))))
           , λ m → let (_ , al) = proj₂ (proj₂ W) m in _ , proj₁ (proj₂ (toL (whole-listed W) al))

  near→ : ∀ {m l} → Near a m l → Near b m l
  near→ (inj₁ lm)             = inj₁ lm
  near→ (inj₂ ((_ , al) , L)) = inj₂ ((_ , proj₁ (proj₂ (toL L al))) , lst→ L)

unp← : ∀ {X Z} {e : Ev X} {e′ : Ev Z} → Kin e e′ → Unpinned e′ → Unpinned e
unp← k-out  _ = tt
unp← k-skip _ = tt
unp← k-end  _ = tt

unp→ : ∀ {X Z} {e : Ev X} {e′ : Ev Z} → Kin e e′ → Unpinned e → Unpinned e′
unp→ k-out  _ = tt
unp→ k-skip _ = tt
unp→ k-end  _ = tt

-- A CARRIED RUN RELABELLED ROW FOR ROW stays carried, when the labels
-- carry what they carried.
module Relabel {A A′ Y Y′ : Set} {f : Y → List A} {f′ : Y′ → List A′} {M : PMap} {HP HE LP : Pos → Set}
  {t : EmissionSet A} {t′ : EmissionSet A′} {u : EmissionSet Y} {u′ : EmissionSet Y′} {s s′ : Pos}
  (R : Pos → Ev A → Ev A′ → Set) (R′ : Pos → Ev Y → Ev Y′ → Set)
  (kin : ∀ {k e e′} → R k e e′ → Kin e e′) (kin′ : ∀ {l e e′} → R′ l e e′ → Kin e e′)
  (up : ∀ {k e} → t k e → Σ (Ev A′) λ e′ → t′ k e′ × R k e e′)
  (down : ∀ {k e′} → t′ k e′ → Σ (Ev A) λ e → t k e × R k e e′)
  (upL′ : ∀ {l e} → Listed u l → u l e → Σ (Ev Y′) λ e′ → u′ l e′ × R′ l e e′)
  (up¬¬′ : ∀ {l e} → u l e → ¬ ¬ Σ (Ev Y′) λ e′ → u′ l e′ × R′ l e e′)
  (up-end′ : ∀ {l} → u l end → u′ l end) (up-pin′ : ∀ {l r} → u l (pin r) → u′ l (pin r))
  (down′ : ∀ {l e′} → u′ l e′ → Σ (Ev Y) λ e → u l e × R′ l e e′)
  (c : CarryAt f M HP HE LP t u s s′)
  (sh : ∀ {l e e′} → R′ l e e′ → Shown (One f′) e′ → Shown (One f) e)
  (mt : ∀ {k l e₀ e₁ e₀′ e₁′} → CarryAt.Img c k l → R k e₀ e₀′ → R′ l e₁ e₁′
      → Match Every (One f) (Reads f) e₀ e₁ → Match Every (One f′) (Reads f′) e₀′ e₁′) where
  open CarryAt c
  private
    module T = Rows {a = t} {b = t′} {Rel = R} kin up down
    module U = Lifts {a = u} {b = u′} {Rel = R′} kin′ upL′ up¬¬′ up-end′ down′

    into′ : ∀ {k} → IntoAt Img u PB HP s k → IntoAt Img u′ PB HP s k
    into′ ((l , (e , ul) , L , m) , h) = (l , (proj₁ (upL′ L ul) , proj₁ (proj₂ (upL′ L ul))) , U.lst→ {l} L , m) , home h
      where
        home : _ → _
        home (inj₁ e) = inj₁ e
        home (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (e₀ , ul₀) , L))) =
          inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (proj₁ (upL′ L ul₀) , proj₁ (proj₂ (upL′ L ul₀))) , U.lst→ {l₀} L))
        home (inj₂ (inj₂ h)) = inj₂ (inj₂ h)

    skip-up : ∀ {k e e′} → R k e e′ → e ≡ skip → e′ ≡ skip
    skip-up r refl with kin r
    ... | k-skip = refl

    img′ : ∀ {k e′} → t′ k e′ → Unpinned e′ → Live t′ k → Listed t′ k → LP k
         → (Σ Pos λ l → Img k l × Σ (Ev Y′) λ e₁′ → u′ l e₁′ × Listed u′ l × Match Every (One f′) (Reads f′) e′ e₁′)
           ⊎ (e′ ≡ skip × IntoAt Img u′ PB HP s k)
    img′ {k} tk un lv fw lp with down tk
    ... | e , tk₀ , r with img tk₀ (unp← (kin r) un) (T.live← {k} (λ {c} → lv {c})) (T.lst← {k} fw) lp
    ...   | inj₂ (es , h) = inj₂ (skip-up r es , into′ h)
    ...   | inj₁ (l , i , e₁ , ul , fu , m) with upL′ fu ul
    ...     | e₁′ , ul′ , r′ = inj₁ (l , i , e₁′ , ul′ , U.lst→ {l} fu , mt i r r′ m)

    img¬¬′ : ∀ {k e′} → t′ k e′ → Unpinned e′ → Live t′ k → Few t′ k
           → ¬ ¬ ((Σ Pos λ l → Img k l × Σ (Ev Y′) λ e₁′ → u′ l e₁′ × Match Every (One f′) (Reads f′) e′ e₁′) ⊎ e′ ≡ skip)
    img¬¬′ {k} tk un lv fw n with down tk
    ... | e , tk₀ , r = img¬¬ tk₀ (unp← (kin r) un) (T.live← {k} (λ {c} → lv {c})) (T.few← {k} fw)
      λ { (inj₁ (l , i , e₁ , ul , m)) → up¬¬′ ul λ { (e₁′ , ul′ , r′) → n (inj₁ (l , i , e₁′ , ul′ , mt i r r′ m)) }
        ; (inj₂ es) → n (inj₂ (skip-up r es)) }

    shown′ : ∀ {l e₁′} → u′ l e₁′ → Shown (One f′) e₁′ → Live u′ l → Few u′ l
           → Σ Pos λ k → Img k l × Σ (Ev A′) λ e₀′ → t′ k e₀′ × Match Every (One f′) (Reads f′) e₀′ e₁′
    shown′ {l} ul sw lv fw with down′ ul
    ... | e₁ , ul₀ , r′ with shown ul₀ (sh r′ sw) (U.live← {l} (λ {c} → lv {c})) (U.few← {l} fw)
    ...   | k , i , e₀ , tk , m with up tk
    ...     | e₀′ , tk′ , r = k , i , e₀′ , tk′ , mt i r r′ m

    up-row : ∀ {k} → Σ (Ev A) (λ e → t k e × Unpinned e) → Σ (Ev A′) λ e → t′ k e × Unpinned e
    up-row (e , tk , un) = proj₁ (up tk) , proj₁ (proj₂ (up tk)) , unp→ (kin (proj₂ (proj₂ (up tk)))) un

    img-row′ : ∀ {k l} → Img k l → ¬ ¬ Σ (Ev A′) λ e → t′ k e × Unpinned e
    img-row′ i n = img-row i λ r → n (up-row r)

    placed′ : ∀ {m} → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u m l)
                ⊎ Σ Pos (λ h → HE h × instantOf h ≡ instantOf m)
            → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u′ m l)
                ⊎ Σ Pos (λ h → HE h × instantOf h ≡ instantOf m)
    placed′ (inj₁ e)                          = inj₁ e
    placed′ {m} (inj₂ (inj₁ (k , l , i , e , n))) = inj₂ (inj₁ (k , l , i , e , U.near→ {m} {l} n))
    placed′ (inj₂ (inj₂ h))                   = inj₂ (inj₂ h)

    pinned′ : ∀ {k p} → t′ k (pin p) → Live t′ k
              → (Σ Pos λ l → Σ Pos λ p′ → u′ l (pin p′) × PB k l × (∀ {k′ l′} → Img k′ l′ → l′ ≺ p′ → k′ ≺ p)
                  × (Listed t′ k → LP k → Listed u′ l))
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t′ k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ {k} {p} tk lv with down tk
    ... | _ , tk₀ , r with kin r
    ...   | k-pin with pinned tk₀ (T.live← {k} (λ {c} → lv {c}))
    ...     | (l , p′ , ul , m , b , ls) , h = (l , p′ , up-pin′ ul , m , b , λ L lp → U.lst→ {l} (ls (T.lst← {k} L) lp)) , homed′ {k} {p} h
      where
        homed′ : ∀ {k p} → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t k₀ × instantOf k₀ ≡ instantOf k)
                   ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
               → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t′ k₀ × instantOf k₀ ≡ instantOf k)
                   ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
        homed′ (inj₁ e)                         = inj₁ e
        homed′ (inj₂ (inj₁ (k₀ , kp , hm , ek))) = inj₂ (inj₁ (k₀ , kp , (λ n → hm λ r → n (up-row r)) , ek))
        homed′ (inj₂ (inj₂ h))                  = inj₂ (inj₂ h)

  carried : CarryAt f′ M HP HE LP t′ u′ s s′
  carried = record
    { Img = Img ; ext = ext ; img = img′ ; img¬¬ = img¬¬′ ; shown = shown′ ; img-row = img-row′ ; img-fun = img-fun
    ; place = λ {m} um lv lm → placed′ {m} (place (proj₁ (proj₂ (down′ um))) (U.live← {m} (λ {c} → lv {c})) (U.lst← {m} lm))
    ; live = λ {k} {l} i lv → U.live→ {l} (λ {c} → live i (T.live← {k} (λ {c′} → lv {c′})) {c})
    ; few = λ {k} i → T.few→ {k} (few i)
    ; whole = λ wt ne lp → U.whole→ (whole (T.whole← wt) (T.ended← ne) lp)
    ; bk = bk ; in-bk = in-bk ; PB = PB ; pb-few = λ ul → pb-few (proj₁ (proj₂ (down′ ul))) ; pinned = pinned′ }

------------------------------------------------------------------------
-- A map

kin-map : ∀ {A B} {g : A → B} (e : Ev A) → Kin e (mapEv g e)
kin-map (out _) = k-out
kin-map skip    = k-skip
kin-map (pin _) = k-pin
kin-map end     = k-end

private
  sh-map : ∀ {A B} {g : A → B} (e : Ev (IE A)) → Shown (One valuesOf) (mapEv (mapIE g) e) → Shown (One valuesOf) e
  sh-map (out (instEmit (value a) _)) _       = a , refl
  sh-map (out (instEmit (mark _) _))  (_ , ())
  sh-map end                          _       = tt

  match-map : ∀ {A B} {g : A → B} (e₀ : Ev A) (e₁ : Ev (IE A)) → Match Every (One valuesOf) (Reads valuesOf) e₀ e₁
            → Match Every (One valuesOf) (Reads valuesOf) (mapEv g e₀) (mapEv (mapIE g) e₁)
  match-map {g = g} (out a) e₁ (cr , _) with cr tt
  ... | instEmit (value _) n , refl , refl = (λ _ → instEmit (value (g a)) n , refl , refl) , λ ns → ⊥-elim (ns tt)
  ... | instEmit (mark _) n  , refl , ()
  match-map end     e₁ (cr , _) with cr tt
  ... | refl = (λ _ → refl) , λ ns → ⊥-elim (ns tt)
  match-map {g = g} skip    e₁ (_ , ns) = (λ ()) , λ _ sw → ns (λ ()) (sh-map {g = g} e₁ sw)
  match-map {g = g} (pin _) e₁ (_ , ns) = (λ ()) , λ _ sw → ns (λ ()) (sh-map {g = g} e₁ sw)

-- A MAP CARRIES what its source did: it relabels each row on both sides
-- by the function, a value's carrier carrying its image.
map-carry : ∀ {A B} (g : A → B) (d : Den A) (d′ : Den (IE A)) {M HP HE LP} p p′
          → CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′
          → CarryAt valuesOf M HP HE LP (enter (Op.map g d) p) (enter (Op.map (mapIE g) d′) p′) p p′
map-carry g d d′ p p′ c =
  Relabel.carried (λ _ e e′ → e′ ≡ mapEv g e) (λ _ e e′ → e′ ≡ mapEv (mapIE g) e)
    (λ { {e = e} refl → kin-map e }) (λ { {e = e} refl → kin-map e })
    (λ tk → _ , P.lift tk , refl) P.unmap (λ _ ul → _ , E.lift ul , refl) (λ ul n → n (_ , E.lift ul , refl)) E.lift E.lift E.unmap c
    (λ { {e = e} refl sw → sh-map {g = g} e sw }) (λ { {e₀ = e₀} {e₁ = e₁} _ refl refl m → match-map {g = g} e₀ e₁ m })
  where
    module P = MapRun g d p
    module E = MapRun (mapIE g) d′ p′

------------------------------------------------------------------------
-- Carriers in order

-- Along an order embedding, carriers keep the order of the rows they
-- carry: no row lies strictly under another, so their images are apart.
module Mono {A Y : Set} {f : Y → List A} {M : PMap} {HP HE LP : Pos → Set} {t : EmissionSet A} {u : EmissionSet Y} {s s′ : Pos}
            (hm : Emb M) (flat : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥) (c : CarryAt f M HP HE LP t u s s′) where
  open CarryAt c

  private
    led-row : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → k ⊑ k′ → ⊥
    led-row {k} i i′ kk ([] , refl) = ≺-irrefl {k} (subst (k ≺_) (⊕-identityʳ k) kk)
    led-row i i′ kk (l ∷ ys , refl) = img-row i λ { (_ , tk , _) → img-row i′ λ { (_ , tk′ , _) → flat tk tk′ } }

  img-mono : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → l ≺ l′
  img-mono i i′ kk with ext i | ext i′
  ... | y , my , σ , refl | y′ , my′ , σ′ , refl =
    apart (Emb.mono hm my my′ kk) (λ yy → led-row i i′ kk (Emb.reflect hm my my′ yy)) σ σ′

------------------------------------------------------------------------
-- From a carried run to its attribution

-- With no environment, a listed run carried along an order embedding,
-- from a subscription its map puts under the other's, is attributed: the
-- order, the instants and the home instant come from the map's, and each
-- row it holds classically is found among those its listing holds.
module _ {A : Set} {M : PMap} (hm : Emb M) {t : EmissionSet A} {u : EmissionSet (IE A)} {s s′ : Pos}
         (flat : ∀ {y e l ys e′} → t y e → t (y ⊕ (l ∷ ys)) e′ → ⊥) (func : ∀ {y e e′} → t y e → t y e′ → e ≡ e′)
         (lst : Listing t) (lstU : Listing u) (pin-few : ∀ {k p} → t k (pin p) → Few t p)
         (liveT′ : ∀ {k e} → t k e → Unpinned e → Live t k) (δ : Path) (at : M s (s′ ⊕ δ)) (c : CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) t u s s′) where
  open CarryAt c

  private
    unpinned : ∀ {k e} → t k e → Home t k → Unpinned e
    unpinned {e = out _} _ _ = tt
    unpinned {e = skip}  _ _ = tt
    unpinned {e = end}   _ _ = tt
    unpinned {e = pin _} tk h = ⊥-elim (h λ { (_ , tk₀ , un) → subst Unpinned (func tk₀ tk) un })

    -- Past a row it holds, `t`'s next rows lie past that row's path.
    past : ∀ {k x e} → Home t k → t x e → x ≺ (k ⊕ [ last ]) → ¬ (x ≡ k) → ¬ (x ≺ k) → ⊥
    past {k} {x} h tx xl x≠k nxk with T? (inside k x)
    ... | yes i with inside-⊑ k x i
    ...   | [] , e = x≠k (trans e (⊕-identityʳ k))
    ...   | _ ∷ _ , refl = h λ { (_ , tk , _) → flat tk tx }
    past {k} {x} h tx xl x≠k nxk | no ni with ≼-split {k} {x} nxk
    ...   | inj₂ e = x≠k (sym e)
    ...   | inj₁ kx = ≺-irrefl {x} (≺-trans {x} {k ⊕ [ last ]} {x} xl
                         (subst ((k ⊕ [ last ]) ≺_) (⊕-identityʳ x) (apart {k} {x} kx (λ q → ni (⊑-inside q)) [ last ] [])))

    -- A row held classically, with few rows before it, is listed.
    row-at : ∀ {k} → Few t k → Home t k → Σ (Ev A) λ e → t k e × Unpinned e
    row-at {k} (ks , F) h with lst {k ⊕ [ last ]} (k ∷ ks , cov)
      where
        cov : ∀ {x e} → t x e → x ≺ (k ⊕ [ last ]) → x ∈ k ∷ ks
        cov {x} tx xl with x ≟ᵖ k
        ... | yes refl = here refl
        ... | no x≠k with T? (x <ᵖ k)
        ...   | yes xk = there (F tx xk)
        ...   | no nxk = ⊥-elim (past h tx xl x≠k nxk)
    ... | ls , G , B with any? (k ≟ᵖ_) ls
    ...   | yes m = proj₁ (proj₂ (B m)) , proj₂ (proj₂ (B m)) , unpinned (proj₂ (proj₂ (B m))) h
    ...   | no ¬m = ⊥-elim (h λ { (_ , tk , _) → ¬m (G tk (≺-ext k [])) })

    inst-img : ∀ {k l} → Img k l → Σ Pos λ y → M k y × instantOf l ≡ instantOf y
    inst-img i with ext i
    ... | y , my , σ , refl = y , my , instant-⊕ y σ

    -- Finitely many rows before a carried row and after it: finitely
    -- many in all.
    rows-in : ∀ {k} → Few t k → Spent t (just k) → Σ (List Pos) λ ks → ∀ {k₁ e} → t k₁ e → k₁ ∈ ks
    rows-in {k} (ks₁ , f₁) (ks₂ , f₂) = ks₁ ++ k ∷ ks₂ , go
      where
        go : ∀ {k₁ e} → t k₁ e → k₁ ∈ ks₁ ++ k ∷ ks₂
        go {k₁} tk with T? (k₁ <ᵖ k)
        ... | yes kk = ∈-++⁺ˡ (f₁ tk kk)
        ... | no ge with ≼-split {k} {k₁} ge
        ...   | inj₁ kk   = ∈-++⁺ʳ ks₁ (there (proj₁ (f₂ tk kk)))
        ...   | inj₂ refl = ∈-++⁺ʳ ks₁ (here refl)

    -- With finitely many rows in all, whether a position holds one is
    -- decided by the listing just past it.
    row? : (Σ (List Pos) λ ks → ∀ {k₁ e} → t k₁ e → k₁ ∈ ks) → ∀ x → Dec (Σ (Ev A) (t x))
    row? (ks , f) x with lst {x ⊕ [ last ]} (ks , λ tx _ → f tx)
    ... | ls , G , B with any? (x ≟ᵖ_) ls
    ...   | yes m = yes (proj₂ (B m))
    ...   | no ¬m = no λ { (_ , tx) → ¬m (G tx (≺-ext x [])) }

    -- Finitely many rows before a carried row and past it: every row,
    -- listed exactly.
    whole-of : ∀ {k} → Few t k → Spent t (just k) → Whole t
    whole-of fw sp = filter (row? R) (proj₁ R) , cov , back
      where
        R = rows-in fw sp

        cov : ∀ {k′ e} → t k′ e → k′ ∈ filter (row? R) (proj₁ R)
        cov tk = ∈-filter⁺ (row? R) (proj₂ R tk) (_ , tk)

        back : ∀ {k′} → k′ ∈ filter (row? R) (proj₁ R) → Σ _ (t k′)
        back m = proj₂ (∈-filter⁻ (row? R) {xs = proj₁ R} m)

  inst′ : ∀ {k k′ l l′} → Img k l → Img k′ l′ → (instantOf l ≡ instantOf l′ ⇔ instantOf k ≡ instantOf k′)
  inst′ i i′ with inst-img i | inst-img i′
  ... | y , my , e | y′ , my′ , e′ = mk⇔
    (λ ll → to (Emb.inst hm my my′) (trans (sym e) (trans ll e′)))
    (λ kk → trans e (trans (from (Emb.inst hm my my′) kk) (sym e′)))

  home′ : ∀ {k l} → Img k l → (instantOf l ≡ instantOf s′ ⇔ instantOf k ≡ instantOf s)
  home′ i with inst-img i
  ... | y , my , e = mk⇔
    (λ ls → to (Emb.inst hm my at) (trans (sym e) (trans ls (sym (instant-⊕ s′ δ)))))
    (λ ks → trans e (trans (from (Emb.inst hm my at) ks) (instant-⊕ s′ δ)))

  attributed : Attribution Every (One valuesOf) (Reads valuesOf) t u s s′
  attributed = record
    { Img = Img ; img = img′ ; shown = shown ; img-row = λ i → row-at (few i) (img-row i) ; img-fun = img-fun
    ; img-mono = Mono.img-mono hm flat c ; inst = inst′ ; home = home′
    ; place = λ {m} um lm fm → placed {m} (place um lm (lstU fm))
    ; live = live
    ; spent = λ i sp ne → let (ls , F , _) = whole (whole-of (few i) sp) ne tt in ls , λ ur _ → F ur
    ; bk = bk ; in-bk = in-bk ; PB = PB ; pb-few = pb-few
    ; pinned = pinned′ }
    where
      few-of : ∀ {l} → Listed u l → Few u l
      few-of (ls , F , _) = ls , F

      -- A carried row's instant, as the attribution reads it.
      home-at : ∀ {k} → instantOf k ≡ instantOf s
                ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ (Ev (IE A)) (u l₀) × Listed u l₀)
                ⊎ Σ Pos (λ h → ⊥ × instantOf h ≡ instantOf k)
              → instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × Σ (Ev (IE A)) (u l₀) × Few u l₀ × instantOf k₀ ≡ instantOf k
      home-at (inj₁ e)                                  = inj₁ e
      home-at (inj₂ (inj₁ (k₀ , l₀ , i , _ , ek , r , L))) = inj₂ (k₀ , l₀ , i , r , few-of L , ek)
      home-at (inj₂ (inj₂ (_ , () , _)))

      into-at : ∀ {k} → IntoAt Img u PB (λ _ → ⊥) s k → Into Img u PB s k
      into-at ((l , r , _ , m) , h) = (l , r , m) , home-at h

      img′ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
           → (Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Few u l × Match Every (One valuesOf) (Reads valuesOf) e e′)
             ⊎ (e ≡ skip × Into Img u PB s k)
      img′ tk un lv fw with img tk un lv (lst fw) tt
      ... | inj₁ (l , i , e′ , ul , L , m) = inj₁ (l , i , e′ , ul , few-of L , m)
      ... | inj₂ (es , h)                  = inj₂ (es , into-at h)

      pinned′ : ∀ {k p} → t k (pin p) → Live t k → Into Img u PB s k
      pinned′ {k} {p} tk lk with pinned tk lk
      ... | (l , p′ , ul , m , _) , inj₁ e = (l , (pin p′ , ul) , m) , inj₁ e
      ... | (l , p′ , ul , m , _) , inj₂ (inj₂ (_ , () , _))
      ... | (l , p′ , ul , m , _) , inj₂ (inj₁ (k₀ , kp , h , ek)) with pin-few tk
      ...   | ks , F with row-at {k₀} (ks , λ {x} tx xk → F tx (≺-trans {x} {k₀} {p} xk kp)) h
      ...     | e₀ , tk₀ , un with img tk₀ un (liveT′ tk₀ un) (lst (ks , λ {x} tx xk → F tx (≺-trans {x} {k₀} {p} xk kp))) tt
      ...       | inj₁ (l₀ , i , e′ , ul₀ , L , _) = (l , (pin p′ , ul) , m) , inj₂ (k₀ , l₀ , i , (e′ , ul₀) , few-of L , ek)
      ...       | inj₂ (_ , _ , h₀) with home-at h₀
      ...         | inj₁ e₀s = (l , (pin p′ , ul) , m) , inj₁ (trans (sym ek) e₀s)
      ...         | inj₂ (k₁ , l₁ , i₁ , r₁ , f₁ , e₁) = (l , (pin p′ , ul) , m) , inj₂ (k₁ , l₁ , i₁ , r₁ , f₁ , trans e₁ ek)

      placed : ∀ {m} → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u m l)
               ⊎ Σ Pos (λ h → ⊥ × instantOf h ≡ instantOf m)
             → instantOf m ≡ instantOf s′ ⊎ Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m
      placed (inj₁ e)                          = inj₁ e
      placed (inj₂ (inj₁ (k , l , i , e , _))) = inj₂ (k , l , i , e)
      placed (inj₂ (inj₂ (_ , () , _)))

------------------------------------------------------------------------
-- The induction

-- What an annotated row shows: the values of the emit it carries.
annValues : ∀ {X} → AIE X → List X
annValues (_ , just x) = valuesOf x
annValues (_ , nothing) = []

-- EVERY HOT OF AN ENVIRONMENT LISTED before a position.
HotsListed : ∀ {Γ} → DenEnv Γ → Pos → Set
HotsListed []              q = ⊤
HotsListed (hot t ∷ ρ)     q = Listed t q × HotsListed ρ q
HotsListed (coldAt _ ∷ ρ)  q = HotsListed ρ q

listed↓ : ∀ {Γ} (ρ : DenEnv Γ) {x y} → x ≼ y → HotsListed ρ y → HotsListed ρ x
listed↓ []             _  _       = tt
listed↓ (hot t ∷ ρ)    xy (L , R) = listed-≼ L xy , listed↓ ρ xy R
listed↓ (coldAt _ ∷ ρ) xy R       = listed↓ ρ xy R

-- A connect's binder: the source, read hot past the connect at `at` in
-- the plain run and at `at′` annotated in the elaborated, carried along
-- the map, each reading keeping the invariant.
record Bound (M₀ : PMap) (LP : Pos → Set) {X : Set} (d : Den X) (d′ : Den (AIE X)) : Set₁ where
  field
    {Θ Θ′}  : List Set
    m       : ℕ
    src     : Obs Timeline Θ X
    σ       : ∀ {Y} → Y ∈ L.map AIE Θ → Y ∈ Θ′
    envP    : DenEnv Θ
    envE    : DenEnv Θ′
    at at′  : Pos
    lists   : ∀ {q} → LP q → HotsListed envP q
    carried : CarryAt annValues M₀ (Hots envP) (Hots envE) (HotsListed envP) (enter (approx m src envP) (at ⊕ [ ix 1 ]))
                (enter (approx m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ])) (at ⊕ [ ix 1 ]) (at′ ⊕ [ ix 1 ])
    invP    : InvAt (Hots envP) (at ⊕ [ ix 1 ]) (enter (approx m src envP) (at ⊕ [ ix 1 ]))
    invE    : InvAt (Hots envE) (at′ ⊕ [ ix 1 ]) (enter (approx m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ]))
    isP     : d ≡ hot (Proper (enter (approx m src envP) (at ⊕ [ ix 1 ])))
    isE     : d′ ≡ hot (Proper (enter (approx m (annotate (elab σ src)) envE) (at′ ⊕ [ ix 1 ])))

EnvRel : ∀ {Γ Δ} → PMap → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Γ → DenEnv Δ → Set₁
EnvRel {Γ} M₀ ρ envP envE = ∀ {X} (i : X ∈ Γ) → Bound M₀ (HotsListed envP) (lookup envP i) (lookup envE (ρ (∈-map⁺ AIE i)))

-- What the map adds lies in the world with the subscription.
Within : (Pos → Set) → PMap → PMap → Pos → Set
Within H M₀ M p = ∀ {x y} → M x y → M₀ x y ⊎ W⁼ H p x

-- The map pairs nothing strictly under a row: what a former putting a
-- row under another's position grows the map by.
Bare : ∀ {A : Set} → PMap → EmissionSet A → Set
Bare M t = ∀ {k e x y} → t k e → M x y → k ⊑ x → x ≡ k

-- No hot row at or under a position.
NotHot : (Pos → Set) → Pos → Set
NotHot H p = ∀ {q} → H q → p ⊑ q → ⊥

-- A row of a bound hot.
BoundRow : ∀ {M₀ LP X} {d : Den X} {d′ : Den (AIE X)} → Bound M₀ LP d d′ → Pos → Set
BoundRow {X = X} b q = Σ (Ev X) (Proper (enter (approx (Bound.m b) (Bound.src b) (Bound.envP b)) (Bound.at b ⊕ [ ix 1 ])) q)

hots-at : ∀ {Γ} (envP : DenEnv Γ) {X} (i : X ∈ Γ) {t : EmissionSet X} → lookup envP i ≡ hot t → ∀ {q e} → t q e → Hots envP q
hots-at (hot _ ∷ _)    (here refl) refl tq = inj₁ (_ , tq)
hots-at (coldAt _ ∷ _) (here refl) ()   _
hots-at (hot _ ∷ ρ)    (there i)   e    tq = inj₂ (hots-at ρ i e tq)
hots-at (coldAt _ ∷ ρ) (there i)   e    tq = hots-at ρ i e tq

bound-hot : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} (envP : DenEnv Γ) {envE : DenEnv Δ}
            (er : EnvRel M₀ ρ envP envE) {X} (i : X ∈ Γ) {q} → BoundRow (er i) q → Hots envP q
bound-hot envP er i (_ , x) = hots-at envP i (Bound.isP (er i)) x

-- UNDER A HOT ROW, ONLY A READER'S JOIN: a point the map puts strictly
-- under a row of a bound hot lies under the row joined at a subscription
-- `e`, its image under the row's carrier joined at `e`'s image.  Two
-- readers' rows of one hot row keep their subscriptions' order so.
Joins : ∀ {Γ Δ} {M₀ : PMap} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (envP : DenEnv Γ) (envE : DenEnv Δ)
      → EnvRel M₀ ρ envP envE → PMap → Set₁
Joins {Γ} _ _ _ er M = ∀ {X} (i : X ∈ Γ) {x y q a σ} → M x y → BoundRow (er i) q → x ≡ q ⊕ (a ∷ σ)
  → Σ Pos λ e → a ≡ sub e × Σ Pos λ e′ → M e e′ × Σ Pos λ L → CarryAt.Img (Bound.carried (er i)) q L × (L ⊕ [ sub e′ ]) ⊑ y

-- NO POSITION HOLDS ROWS OF TWO HOTS: a hot's rows lie in its source's
-- world, which holds no row of a hot already bound.
Apart : ∀ {Γ} → DenEnv Γ → Set
Apart []             = ⊤
Apart (hot t ∷ ρ)    = (∀ {q e} → t q e → Hots ρ q → ⊥) × Apart ρ
Apart (coldAt _ ∷ ρ) = Apart ρ

-- One label under a point of the map, imaged under its image, the point
-- holding no hot row at or under it.
Grown : PMap → (Pos → Set) → PMap
Grown M H x y = Σ Pos λ r → Σ Pos λ r₀ → Σ Label λ a → M r r₀ × r₀ ⊑ y × x ≡ r ⊕ [ a ] × NotHot H r

private
  snoc-split : ∀ (ps qs : Path) {a a′ σ} → ps ++ [ a ] ≡ qs ++ a′ ∷ σ → (ps ≡ qs × a ≡ a′) ⊎ Σ Path λ σ′ → ps ≡ qs ++ a′ ∷ σ′
  snoc-split []       []            refl = inj₁ (refl , refl)
  snoc-split (_ ∷ ps) []            refl = inj₂ (ps , refl)
  snoc-split []       (_ ∷ [])      ()
  snoc-split []       (_ ∷ _ ∷ _)   ()
  snoc-split (_ ∷ ps) (_ ∷ qs)      e with ∷-injective e
  ... | refl , e′ with snoc-split ps qs e′
  ...   | inj₁ (refl , refl) = inj₁ (refl , refl)
  ...   | inj₂ (σ′ , refl)   = inj₂ (σ′ , refl)

  -- One label under `r`, read under `q`: `r` is `q`, or lies under `q`'s step.
  pos-split : ∀ r q {a a′ σ} → r ⊕ [ a ] ≡ q ⊕ (a′ ∷ σ) → (r ≡ q × a ≡ a′) ⊎ Σ Path λ σ′ → r ≡ q ⊕ (a′ ∷ σ′)
  pos-split (i ∙ ps) (j ∙ qs) e with ∙-inj e
  ... | refl , e′ with snoc-split ps qs e′
  ...   | inj₁ (refl , refl) = inj₁ (refl , refl)
  ...   | inj₂ (σ′ , refl)   = inj₂ (σ′ , refl)

-- THE JOINS KEPT by a map growing by points one label under points of
-- the map.
joins-grow : ∀ {Γ Δ} {M₀ : PMap} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {envP : DenEnv Γ} {envE : DenEnv Δ}
             {er : EnvRel M₀ ρ envP envE} {M N : PMap}
           → M ⊆ᴹ N → Joins ρ envP envE er M → (∀ {x y} → N x y → M x y ⊎ Grown M (Hots envP) x y) → Joins ρ envP envE er N
joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} ms jn gr i n row xe with gr n
... | inj₁ m with jn i m row xe
...   | e , ae , e′ , me , L , il , Ly = e , ae , e′ , ms me , L , il , Ly
joins-grow {ρ = ρ} {envP = envP} {envE = envE} {er = er} ms jn gr i n row xe | inj₂ (r , r₀ , a , m , ry , refl , nh) with pos-split r _ xe
... | inj₁ (refl , refl) = ⊥-elim (nh (bound-hot {ρ = ρ} envP {envE = envE} er i row) (⊑-refl r))
... | inj₂ (σ′ , refl) with jn i m row refl
...   | e , ae , e′ , me , L , il , Ly = e , ae , e′ , ms me , L , il , ⊑-trans Ly ry

-- CARRIED under every environment of carried binders: subscribed at
-- admissible positions the map pairs, holding no hot row, its worlds
-- untouched, the subterm extends the map over its worlds, keeping the
-- joins, and carries.
-- A record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record Carry (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor carry
  field carries : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE
                → ∀ M₀ → Emb M₀ → (er : EnvRel M₀ ρ envP envE) → Joins ρ envP envE er M₀ → Apart envP
                → ∀ p p′ → M₀ p p′ → Ok (Hots envP) p → Ok (Hots envE) p′ → NotHot (Hots envP) p → Fresh (Hots envP) M₀ p
                → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (enter (approx n o envP) p) × Joins ρ envP envE er M
                  × CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter (approx n o envP) p) (enter (approx n (elab ρ o) envE) p′) p p′

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER CARRIES its plain counterpart when its children
-- do, under every approximant.
postulate
  carry-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → Carry m ρ (cold c)
  carry-flatMap   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → Carry m ρ s
                  → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry m ρ′ (f a)) → Carry m ρ (flatMap op f s)
  carry-connect   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                  → Carry m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → Carry m ρ′ b) → Carry m ρ (connect s b)

carry-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → Carry m ρ s → Carry m ρ (map f s)
carry-map n ρ f s (carry h) = carry λ envP envE gP gE M₀ hm er jn ap p p′ m₀ okP okE nh fr →
  let (M , ms , hm′ , wi , br , jn′ , c) = h envP envE gP gE M₀ hm er jn ap p p′ m₀ okP okE nh fr
  in M , ms , hm′ , wi , (λ tk → br (proj₁ (proj₂ (MapRun.unmap f (approx n s envP) p tk)))) , jn′ , map-carry f (approx n s envP) (approx n (elab ρ s) envE) p p′ c
