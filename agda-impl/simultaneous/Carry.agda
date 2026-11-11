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
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Properties using (++-assoc; ++-cancelˡ; ∷-injectiveˡ)
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

open import Tree using (Obs; cold; empty; of; map; flatMap; connect; connected)
open import denotation.Position using (Pos; Path; Label; Instant; ix; last; _∙_; _⊕_; root; lt; eq; gt; cmpLabel; cmpPath; cmpInstant; cmpPos; isLt; inside)
open import denotation.Simultaneity using (eqˡ; eqⁱ; reflˡ; reflⁱ)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; hot; coldAt; enter; Proper; DenEnv; Few; _≺_; _≼_;
  approx; module Op; Truncate; Reach; InE; at-end; at-out; on-out)
import denotation.Events as Evs
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-trans; ≼-≺-≺; ≺-ext)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; W⁼; here; inW; step; Plain; plain-ix; plain-last; _⊑_; ⊕-identityʳ; ⊑-refl; ⊑-trans; ⊑-≼;
  ⊑-cmp; ⊑-inside; inside-⊑)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Spent)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.Attribution using (Live; Shown; Match; Attribution; Every; One; Reads)
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

-- `u`, subscribed at `s′`, carries `t`, subscribed at `s`, under the
-- environment hot rows `HP` (plain) and `HE` (elaborated), along `M`:
-- `simultaneous.Attribution.Attribution`'s fields, each carrier lying
-- under the image of the row it carries, a row of `u` placed or a pin of
-- `t` homed also by an instant of an environment row.
--
-- A ROW IS CARRIED FROM ITS LISTING, onto a carrier listed too; a row
-- only witnessed to exist (the carried row, a pin's home) is so
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
    img     : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
            → Σ Pos λ l → Img k l × Σ (Ev Y) λ e′ → u l e′ × Listed u l × Match Every (One f) (Reads f) e e′
    img¬¬   : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
            → ¬ ¬ Σ Pos λ l → Img k l × Σ (Ev Y) λ e′ → u l e′ × Match Every (One f) (Reads f) e e′
    shown   : ∀ {l e} → u l e → Shown (One f) e → Live u l → Few u l
            → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → t k e₀ × Match Every (One f) (Reads f) e₀ e
    img-row : ∀ {k l} → Img k l → ¬ ¬ Σ (Ev A) λ e → t k e × Unpinned e
    img-fun : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    place   : ∀ {m e} → u m e → Live u m → Listed u m
            → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u m l)
              ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
    live    : ∀ {k l} → Img k l → Live t k → Live u l
    few     : ∀ {k l} → Img k l → Few t k
    whole   : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Σ (List Pos) λ ls → ∀ {r e} → u r e → r ∈ ls
    bk      : Pos → List Pos
    in-bk   : ∀ {k l} → Img k l → k ∈ bk l
    pbk     : Pos → List Pos
    pinned  : ∀ {k p} → t k (pin p) → Live t k
            → (Σ Pos λ l → Σ Pos λ p′ → u l (pin p′) × k ∈ pbk l × (∀ {k′ l′} → Img k′ l′ → l′ ≺ p′ → k′ ≺ p))
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

private
  module Rows {X Z : Set} {a : EmissionSet X} {b : EmissionSet Z} {Rel : Pos → Ev X → Ev Z → Set}
              (kn : ∀ {k e e′} → Rel k e e′ → Kin e e′)
              (to : ∀ {k e} → a k e → Σ (Ev Z) λ e′ → b k e′ × Rel k e e′)
              (fro : ∀ {k e′} → b k e′ → Σ (Ev X) λ e → a k e × Rel k e e′) where
    live→ : ∀ {k} → Live a k → Live b k
    live→ {k} la {c} bc with fro bc
    ... | _ , ac , r with kn r
    ...   | k-end = la {c} ac

    live← : ∀ {k} → Live b k → Live a k
    live← {k} lb {c} ac with to ac
    ... | _ , bc , r with kn r
    ...   | k-end = lb {c} bc

    few→ : ∀ {k} → Few a k → Few b k
    few→ (ks , F) = ks , λ bk kk → F (proj₁ (proj₂ (fro bk))) kk

    few← : ∀ {k} → Few b k → Few a k
    few← (ks , F) = ks , λ ak kk → F (proj₁ (proj₂ (to ak))) kk

    lst→ : ∀ {k} → Listed a k → Listed b k
    lst→ (ks , F , B) = ks , (λ bk kk → F (proj₁ (proj₂ (fro bk))) kk) , λ m → proj₁ (B m) , proj₁ (to (proj₂ (proj₂ (B m)))) , proj₁ (proj₂ (to (proj₂ (proj₂ (B m)))))

    lst← : ∀ {k} → Listed b k → Listed a k
    lst← (ks , F , B) = ks , (λ ak kk → F (proj₁ (proj₂ (to ak))) kk) , λ m → proj₁ (B m) , proj₁ (fro (proj₂ (proj₂ (B m)))) , proj₁ (proj₂ (fro (proj₂ (proj₂ (B m)))))

    ended← : (∀ {c} → b c end → ⊥) → ∀ {c} → a c end → ⊥
    ended← ne ac with to ac
    ... | _ , bc , r with kn r
    ...   | k-end = ne bc

    whole← : Whole b → Whole a
    whole← (ks , F , B) = ks , (λ ak → F (proj₁ (proj₂ (to ak)))) , λ m → proj₁ (fro (proj₂ (B m))) , proj₁ (proj₂ (fro (proj₂ (B m))))

    near→ : ∀ {m l} → Near a m l → Near b m l
    near→ (inj₁ lm)             = inj₁ lm
    near→ (inj₂ ((_ , al) , L)) = inj₂ ((_ , proj₁ (proj₂ (to al))) , lst→ L)

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
  (up′ : ∀ {l e} → u l e → Σ (Ev Y′) λ e′ → u′ l e′ × R′ l e e′)
  (down′ : ∀ {l e′} → u′ l e′ → Σ (Ev Y) λ e → u l e × R′ l e e′)
  (c : CarryAt f M HP HE LP t u s s′)
  (sh : ∀ {l e e′} → R′ l e e′ → Shown (One f′) e′ → Shown (One f) e)
  (mt : ∀ {k l e₀ e₁ e₀′ e₁′} → CarryAt.Img c k l → R k e₀ e₀′ → R′ l e₁ e₁′
      → Match Every (One f) (Reads f) e₀ e₁ → Match Every (One f′) (Reads f′) e₀′ e₁′) where
  open CarryAt c
  private
    module T = Rows {a = t} {b = t′} {Rel = R} kin up down
    module U = Rows {a = u} {b = u′} {Rel = R′} kin′ up′ down′

    img′ : ∀ {k e′} → t′ k e′ → Unpinned e′ → Live t′ k → Listed t′ k → LP k
         → Σ Pos λ l → Img k l × Σ (Ev Y′) λ e₁′ → u′ l e₁′ × Listed u′ l × Match Every (One f′) (Reads f′) e′ e₁′
    img′ {k} tk un lv fw lp with down tk
    ... | e , tk₀ , r with img tk₀ (unp← (kin r) un) (T.live← {k} (λ {c} → lv {c})) (T.lst← {k} fw) lp
    ...   | l , i , e₁ , ul , fu , m with up′ ul
    ...     | e₁′ , ul′ , r′ = l , i , e₁′ , ul′ , U.lst→ {l} fu , mt i r r′ m

    img¬¬′ : ∀ {k e′} → t′ k e′ → Unpinned e′ → Live t′ k → Few t′ k
           → ¬ ¬ Σ Pos λ l → Img k l × Σ (Ev Y′) λ e₁′ → u′ l e₁′ × Match Every (One f′) (Reads f′) e′ e₁′
    img¬¬′ {k} tk un lv fw n with down tk
    ... | e , tk₀ , r = img¬¬ tk₀ (unp← (kin r) un) (T.live← {k} (λ {c} → lv {c})) (T.few← {k} fw)
      λ { (l , i , e₁ , ul , m) → let (e₁′ , ul′ , r′) = up′ ul in n (l , i , e₁′ , ul′ , mt i r r′ m) }

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
              → (Σ Pos λ l → Σ Pos λ p′ → u′ l (pin p′) × k ∈ pbk l × (∀ {k′ l′} → Img k′ l′ → l′ ≺ p′ → k′ ≺ p))
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t′ k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ {k} {p} tk lv with down tk
    ... | _ , tk₀ , r with kin r
    ...   | k-pin with pinned tk₀ (T.live← {k} (λ {c} → lv {c}))
    ...     | (l , p′ , ul , m , b) , h = (l , p′ , pin-up ul , m , b) , homed′ {k} {p} h
      where
        pin-up : ∀ {l p′} → u l (pin p′) → u′ l (pin p′)
        pin-up ul with up′ ul
        ... | _ , ul′ , r′ with kin′ r′
        ...   | k-pin = ul′

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
    ; whole = λ wt ne lp → let (ls , F) = whole (T.whole← wt) (T.ended← ne) lp in ls , λ ur → F (proj₁ (proj₂ (down′ ur)))
    ; bk = bk ; in-bk = in-bk ; pbk = pbk ; pinned = pinned′ }

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
    (λ tk → _ , P.lift tk , refl) P.unmap (λ ul → _ , E.lift ul , refl) E.unmap c
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
         (δ : Path) (at : M s (s′ ⊕ δ)) (c : CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) t u s s′) where
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
    ; spent = λ i sp ne → let (ls , F) = whole (whole-of (few i) sp) ne tt in ls , λ ur _ → F ur
    ; bk = bk ; in-bk = in-bk ; pbk = pbk
    ; pinned = pinned′ }
    where
      img′ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
           → Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Few u l × Match Every (One valuesOf) (Reads valuesOf) e e′
      img′ tk un lv fw with img tk un lv (lst fw) tt
      ... | l , i , e′ , ul , (ls , F , _) , m = l , i , e′ , ul , (ls , F) , m

      pinned′ : ∀ {k p} → t k (pin p) → Live t k → (Σ Pos λ l → Σ (Ev (IE A)) (u l) × k ∈ pbk l)
                × (instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → t k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k)
      pinned′ {k} {p} tk lk with pinned tk lk
      ... | (l , p′ , ul , m , _) , inj₁ e = (l , (pin p′ , ul) , m) , inj₁ e
      ... | (l , p′ , ul , m , _) , inj₂ (inj₁ (k₀ , kp , h , ek)) with pin-few tk
      ...   | ks , F with row-at {k₀} (ks , λ {x} tx xk → F tx (≺-trans {x} {k₀} {p} xk kp)) h
      ...     | e₀ , tk₀ , un = (l , (pin p′ , ul) , m) , inj₂ (k₀ , e₀ , tk₀ , un , ek)
      pinned′ {k} {p} tk lk | (l , p′ , ul , m , _) , inj₂ (inj₂ (_ , () , _))

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
-- the map.
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

-- CARRIED under every environment of carried binders: subscribed at
-- admissible positions the map pairs, its worlds untouched, the subterm
-- extends the map over its worlds and carries.
-- A record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record Carry (n : ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor carry
  field carries : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE
                → ∀ M₀ → Emb M₀ → EnvRel M₀ ρ envP envE
                → ∀ p p′ → (Σ Pos λ p₀ → M₀ p p₀ × p₀ ⊑ p′) → Ok (Hots envP) p → Ok (Hots envE) p′ → Fresh (Hots envP) M₀ p
                → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) M₀ M p × Bare M (enter (approx n o envP) p)
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
  carry-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → Carry m ρ (connected i)

carry-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → Carry m ρ s → Carry m ρ (map f s)
carry-map n ρ f s (carry h) = carry λ envP envE gP gE M₀ hm er p p′ m₀ okP okE fr →
  let (M , ms , hm′ , wi , br , c) = h envP envE gP gE M₀ hm er p p′ m₀ okP okE fr
  in M , ms , hm′ , wi , (λ tk → br (proj₁ (proj₂ (MapRun.unmap f (approx n s envP) p tk)))) , map-carry f (approx n s envP) (approx n (elab ρ s) envE) p p′ c

-- Positions one label under a common prefix.
private
  path-under : ∀ ps σ τ → cmpPath (ps ++ σ) (ps ++ τ) ≡ cmpPath σ τ
  path-under []       σ τ = refl
  path-under (a ∷ ps) σ τ rewrite reflˡ a = path-under ps σ τ

  cmp-under : ∀ q σ τ → cmpPos (q ⊕ σ) (q ⊕ τ) ≡ cmpPath σ τ
  cmp-under (i ∙ ps) σ τ rewrite reflⁱ i = path-under ps σ τ

  ≺-shift : ∀ q q′ σ τ → (q ⊕ σ) ≺ (q ⊕ τ) → (q′ ⊕ σ) ≺ (q′ ⊕ τ)
  ≺-shift q q′ σ τ h = subst (λ c → T (isLt c)) (trans (cmp-under q σ τ) (sym (cmp-under q′ σ τ))) h

  path-of : Pos → Path
  path-of (_ ∙ ps) = ps

  ⊑-one : ∀ q {a b} → (q ⊕ [ a ]) ⊑ (q ⊕ [ b ]) → b ≡ a
  ⊑-one (i ∙ ps) {a} {b} (zs , e) = ∷-injectiveˡ (++-cancelˡ ps [ b ] (a ∷ zs) (trans (cong path-of e) (++-assoc ps [ a ] zs)))

  drop-len : ∀ (ps σ : Path) → L.drop (L.length ps) (ps ++ σ) ≡ σ
  drop-len []       σ = refl
  drop-len (_ ∷ ps) σ = drop-len ps σ

  drop-under : ∀ q σ → L.drop (L.length (path-of q)) (path-of (q ⊕ σ)) ≡ σ
  drop-under (i ∙ ps) σ = drop-len ps σ

-- Each plain label under one position, put on the same label under another.
module OneAt (p p′ : Pos) where
  N : PMap
  N x y = Σ Label λ a → Plain a × x ≡ p ⊕ [ a ] × y ≡ p′ ⊕ [ a ]

  embN : Emb N
  embN = record
    { fun     = λ { (a , _ , refl , refl) (b , _ , e , refl) →
                    cong (λ c → p′ ⊕ [ c ]) (⊑-one p ([] , trans e (sym (⊕-identityʳ (p ⊕ [ b ]))))) }
    ; mono    = λ { (a , _ , refl , refl) (b , _ , refl , refl) h → ≺-shift p p′ [ a ] [ b ] h }
    ; reflect = λ { (a , _ , refl , refl) (b , _ , refl , refl) h → subst (λ c → (p ⊕ [ a ]) ⊑ (p ⊕ [ c ])) (sym (⊑-one p′ h)) (⊑-refl (p ⊕ [ a ])) }
    ; inst    = λ { (a , _ , refl , refl) (b , _ , refl , refl) →
                    mk⇔ (λ _ → trans (instant-⊕ p [ a ]) (sym (instant-⊕ p [ b ])))
                        (λ _ → trans (instant-⊕ p′ [ a ]) (sym (instant-⊕ p′ [ b ]))) } }

-- ONE LABEL UNDER EACH SUBSCRIPTION: a map held fresh grown by each
-- plain label under the plain subscription, put on the same label under
-- the elaborated one.
module OneUnder {HP : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos}
                (E₀ : Emb M₀) (fr : Fresh HP M₀ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′) where
  open OneAt p p′ public

  M : PMap
  M = M₀ ∪ᴹ N

  emb : Emb M
  emb = emb-under {N = N} E₀ fr m₀ pp embN λ { (a , _ , refl , refl) → a , [] , a , [] , refl , refl }

  within : Within HP M₀ M p
  within (inj₁ m)                  = inj₁ m
  within (inj₂ (_ , pl , refl , _)) = inj₂ (inW (step here pl))

  -- Rows one label under the subscription have nothing paired under them.
  bare : ∀ {X : Set} {t : EmissionSet X} → (∀ {k e} → t k e → Σ Label λ a → Plain a × k ≡ p ⊕ [ a ]) → Bare M t
  bare sh tk (inj₁ m) kx with sh tk
  ... | a , pl , refl = ⊥-elim (⊑-≼ (subst ((p ⊕ [ a ]) ⊑_) (fr m (p ⊕ [ a ] , inW (step here pl) , kx)) kx) (≺-ext p []))
  bare sh tk (inj₂ (b , _ , refl , _)) kx with sh tk
  ... | a , pl , refl = cong (λ c → p ⊕ [ c ]) (⊑-one p kx)

  -- A position's path past one subscription, put under the other.
  up : Pos → Pos
  up k = p′ ⊕ L.drop (L.length (path-of p)) (path-of k)

  up-⊕ : ∀ σ → up (p ⊕ σ) ≡ p′ ⊕ σ
  up-⊕ σ = cong (p′ ⊕_) (drop-under p σ)

  down : Pos → Pos
  down l = p ⊕ L.drop (L.length (path-of p′)) (path-of l)

  down-⊕ : ∀ σ → down (p′ ⊕ σ) ≡ p ⊕ σ
  down-⊕ σ = cong (p ⊕_) (drop-under p′ σ)

-- An end one label under `q` comes after every row so labelled.
last-max : ∀ q {a} → Plain a → (q ⊕ [ last ]) ≺ (q ⊕ [ a ]) → ⊥
last-max q (plain-ix {i}) h = subst (λ c → T (isLt c)) (cmp-under q [ last ] [ ix i ]) h
last-max q plain-last     h = subst (λ c → T (isLt c)) (cmp-under q [ last ] [ last ]) h

ix-last : ∀ q → (q ⊕ [ ix 0 ]) ≺ (q ⊕ [ last ])
ix-last q = subst (λ c → T (isLt c)) (sym (cmp-under q [ ix 0 ] [ last ])) tt

private
  unp-pin : ∀ {X : Set} {r} → Unpinned {X} (pin r) → ⊥
  unp-pin ()

  -- What an elaborated `of` emits for a value.
  V : ∀ {A : Set} → A → IE A
  V x = instEmit (value x) root

  -- A run with a complete list of its rows, each a row, is listed
  -- before every position.
  fin-listed : ∀ {X : Set} {t : EmissionSet X} (ks : List Pos) → (∀ {k e} → t k e → k ∈ ks) → (∀ {k} → k ∈ ks → Σ (Ev X) (t k))
             → ∀ q → Listed t q
  fin-listed ks F B q =
    filter (λ k → T? (k <ᵖ q)) ks
    , (λ tk kq → ∈-filter⁺ (λ k → T? (k <ᵖ q)) (F tk) kq)
    , λ m → let (n , kq) = ∈-filter⁻ (λ k → T? (k <ᵖ q)) m in kq , B n

  -- The rows of an `of`: one label under its subscription, finitely
  -- many, none pinned, the end last.
  of-pos : ∀ {A : Set} → Pos → ℕ → List A → List Pos
  of-pos p i []       = [ p ⊕ [ last ] ]
  of-pos p i (_ ∷ xs) = (p ⊕ [ ix i ]) ∷ of-pos p (suc i) xs

  of-in : ∀ {A : Set} p i (xs : List A) {k e} → InE (Evs.ofᴱ p i xs) k e → k ∈ of-pos p i xs
  of-in p i []       at-end     = here refl
  of-in p i (x ∷ xs) at-out     = here refl
  of-in p i (x ∷ xs) (on-out r) = there (of-in p (suc i) xs r)

  of-row : ∀ {A : Set} p i (xs : List A) {k} → k ∈ of-pos p i xs → Σ (Ev A) (InE (Evs.ofᴱ p i xs) k)
  of-row p i []       (here refl) = end , at-end
  of-row p i (x ∷ xs) (here refl) = out x , at-out
  of-row p i (x ∷ xs) (there m)   = let (e , r) = of-row p (suc i) xs m in e , on-out r

  of-unp : ∀ {A : Set} p i (xs : List A) {k e} → InE (Evs.ofᴱ p i xs) k e → Unpinned e
  of-unp p i []       at-end     = tt
  of-unp p i (x ∷ xs) at-out     = tt
  of-unp p i (x ∷ xs) (on-out r) = of-unp p (suc i) xs r

  of-end : ∀ {A : Set} p i (xs : List A) {c} → InE (Evs.ofᴱ p i xs) c end → c ≡ p ⊕ [ last ]
  of-end p i []       at-end     = refl
  of-end p i (x ∷ xs) (on-out r) = of-end p (suc i) xs r

  -- Each row of the plain `of`, and of the elaborated, has its fellow
  -- under the other subscription.
  of-up : ∀ {A : Set} p p′ i (xs : List A) {k e} → InE (Evs.ofᴱ p i xs) k e
        → Σ Label λ a → Plain a × k ≡ p ⊕ [ a ] × InE (Evs.ofᴱ p′ i (L.map V xs)) (p′ ⊕ [ a ]) (mapEv V e)
  of-up p p′ i []       at-end     = last , plain-last , refl , at-end
  of-up p p′ i (x ∷ xs) at-out     = ix i , plain-ix , refl , at-out
  of-up p p′ i (x ∷ xs) (on-out r) with of-up p p′ (suc i) xs r
  ... | a , pl , e , r′ = a , pl , e , on-out r′

  of-down : ∀ {A : Set} p p′ i (xs : List A) {l e′} → InE (Evs.ofᴱ p′ i (L.map V xs)) l e′
          → Σ Label λ a → Plain a × l ≡ p′ ⊕ [ a ] × Σ (Ev A) λ e → InE (Evs.ofᴱ p i xs) (p ⊕ [ a ]) e × e′ ≡ mapEv V e
  of-down p p′ i []       at-end     = last , plain-last , refl , end , at-end , refl
  of-down p p′ i (x ∷ xs) at-out     = ix i , plain-ix , refl , out x , at-out , refl
  of-down p p′ i (x ∷ xs) (on-out r) with of-down p p′ (suc i) xs r
  ... | a , pl , e , e₀ , r₀ , ee = a , pl , e , e₀ , on-out r₀ , ee

  match-V : ∀ {A : Set} (e : Ev A) → Match Every (One valuesOf) (Reads valuesOf) e (mapEv V e)
  match-V (out x) = (λ _ → V x , refl , refl) , λ ns → ⊥-elim (ns tt)
  match-V end     = (λ _ → refl) , λ ns → ⊥-elim (ns tt)
  match-V skip    = (λ ()) , λ _ ()
  match-V (pin _) = (λ ()) , λ _ ()

  -- The values listed, carried row for row one label under each side.
  module OfRows {A : Set} {HP HE LP : Pos → Set} {M₀ : PMap} {p p₀ p′ : Pos} (xs : List A)
                (E₀ : Emb M₀) (fr : Fresh HP M₀ p) (m₀ : M₀ p p₀) (pp : p₀ ⊑ p′) where
    open OneUnder E₀ fr m₀ pp using (N; embN; M; emb; within)

    t : EmissionSet A
    t = Truncate (InE (Evs.ofᴱ p 0 xs))

    u : EmissionSet (IE A)
    u = Truncate (InE (Evs.ofᴱ p′ 0 (L.map V xs)))

    allT : Σ (List Pos) λ ks → ∀ {k e} → InE (Evs.ofᴱ p 0 xs) k e → k ∈ ks
    allT = of-pos p 0 xs , of-in p 0 xs

    allU : Σ (List Pos) λ ks → ∀ {k e} → InE (Evs.ofᴱ p′ 0 (L.map V xs)) k e → k ∈ ks
    allU = of-pos p′ 0 (L.map V xs) , of-in p′ 0 (L.map V xs)

    reachT : ∀ {q e} → Reach (InE (Evs.ofᴱ p 0 xs)) q e
    reachT = proj₁ allT , λ r _ _ → proj₂ allT r

    reachU : ∀ {q e} → Reach (InE (Evs.ofᴱ p′ 0 (L.map V xs))) q e
    reachU = proj₁ allU , λ r _ _ → proj₂ allU r

    fewT : ∀ {k} → Few t k
    fewT = proj₁ allT , λ r _ → proj₂ allT (proj₁ r)

    lstU : ∀ {l} → Listed u l
    lstU {l} = fin-listed (proj₁ allU) (λ r → proj₂ allU (proj₁ r)) (λ m → let (e , r) = of-row p′ 0 (L.map V xs) m in e , r , reachU) l

    Img : Pos → Pos → Set
    Img k l = N k l × Σ (Ev A) (t k)

    img : ∀ {k e} → t k e → Σ Pos λ l → Img k l × Σ (Ev (IE A)) λ e′ → u l e′ × Listed u l × Match Every (One valuesOf) (Reads valuesOf) e e′
    img {k} {e} tk with of-up p p′ 0 xs (proj₁ tk)
    ... | a , pl , refl , r′ = p′ ⊕ [ a ] , ((a , pl , refl , refl) , e , tk) , mapEv V e , (r′ , reachU) , lstU , match-V e

    shown : ∀ {l e′} → u l e′ → Shown (One valuesOf) e′ → Live u l → Few u l
          → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → t k e₀ × Match Every (One valuesOf) (Reads valuesOf) e₀ e′
    shown ul _ _ _ with of-down p p′ 0 xs (proj₁ ul)
    ... | a , pl , refl , e , r₀ , refl = p ⊕ [ a ] , ((a , pl , refl , refl) , e , r₀ , reachT) , e , (r₀ , reachT) , match-V e

    place : ∀ {m e} → u m e → instantOf m ≡ instantOf p′
    place um with of-down p p′ 0 xs (proj₁ um)
    ... | a , _ , refl , _ = instant-⊕ p′ [ a ]

    live : ∀ {k l} → Img k l → ∀ {c} → u c end → c ≺ l → ⊥
    live ((a , pl , _ , refl) , _) uc with of-end p′ 0 (L.map V xs) (proj₁ uc)
    ... | refl = last-max p′ pl

    carried : CarryAt valuesOf M HP HE LP t u p p′
    carried = record
      { Img     = Img
      ; ext     = λ { (n , _) → _ , inj₂ n , ⊑-refl _ }
      ; img     = λ tk _ _ _ _ → img tk
      ; img¬¬   = λ tk _ _ _ n → let (l , i , e′ , ul , _ , m) = img tk in n (l , i , e′ , ul , m)
      ; shown   = shown
      ; img-row = λ { (_ , e , tk) n → n (e , tk , of-unp p 0 xs (proj₁ tk)) }
      ; img-fun = λ { (n , _) (n′ , _) → Emb.fun embN n n′ }
      ; place   = λ um _ _ → inj₁ (place um)
      ; live    = λ i _ → live i
      ; few     = λ _ → fewT
      ; whole   = λ _ _ _ → proj₁ allU , λ ur → proj₂ allU (proj₁ ur)
      ; bk      = λ _ → proj₁ allT
      ; in-bk   = λ { (_ , _ , tk) → proj₂ allT (proj₁ tk) }
      ; pbk     = λ _ → []
      ; pinned  = λ {_} {r} tk _ → ⊥-elim (unp-pin {A} {r} (of-unp p 0 xs (proj₁ tk)))
      }

  of-carried : ∀ {A HP HE LP M₀ p p₀ p′} (xs : List A) → Emb M₀ → Fresh HP M₀ p → M₀ p p₀ → p₀ ⊑ p′
             → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within HP M₀ M p × Bare M (Truncate (InE (Evs.ofᴱ p 0 xs)))
               × CarryAt valuesOf M HP HE LP (Truncate (InE (Evs.ofᴱ p 0 xs))) (Truncate (InE (Evs.ofᴱ p′ 0 (L.map V xs)))) p p′
  of-carried {A} {HP} {HE} {LP} {p = p} xs E₀ fr m₀ pp = O.M , inj₁ , O.emb , O.within , O.bare {t = Truncate (InE (Evs.ofᴱ p 0 xs))} (λ {k} {e} tk → of-shape {k} {e} (proj₁ tk)) , X.carried
    where module X = OfRows {A} {HP} {HE} {LP} xs E₀ fr m₀ pp
          module O = OneUnder E₀ fr m₀ pp
          of-shape : ∀ {k e} → InE (Evs.ofᴱ p 0 xs) k e → Σ Label λ a → Plain a × k ≡ p ⊕ [ a ]
          of-shape r = let (a , pl , e , _) = of-up p p 0 xs r in a , pl , e

-- AN `of` lists its values one label under each subscription.
carry-of : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : List A) → Carry m ρ (of xs)
carry-of n ρ xs = carry λ _ _ _ _ _ e₀ _ p p′ (_ , m₀ , pp) _ _ fr → of-carried xs e₀ fr m₀ pp

-- THE EMPTY PROGRAM ends at once, on both sides: the empty listing.
carry-empty : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → Carry m ρ (empty {A = A})
carry-empty n ρ = carry λ _ _ _ _ _ e₀ _ p p′ (_ , m₀ , pp) _ _ fr → of-carried [] e₀ fr m₀ pp

------------------------------------------------------------------------
-- The whole run

-- Where `elaborate` subscribes the elaborated program: past its restamp,
-- the first lane of its concat and the first of its merge.
coreAt : Pos
coreAt = root ⊕ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

-- THE WRAPPER CARRIES THE CORE, at each approximant: the subscribe mark merged in, the
-- completion concatenated, the restamp, each rides in the core's instants
-- and shows nothing, and the whole ends where the core does.
postulate
  carry-wrap : ∀ n {A} (o : SObs [] A) {M} → Emb M → M root coreAt
             → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root)
                 (enter (approx n (elab (λ i → i) (plain o)) []) coreAt) root coreAt
             → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root)
                 (enter (approx n (elaborate (plain o)) []) root) root root

-- The plain run's subscription paired with the core's: one pair, in
-- neither world.
At₀ : PMap
At₀ x y = x ≡ root × y ≡ coreAt

emb-At₀ : Emb At₀
emb-At₀ = record
  { fun     = λ { (refl , refl) (refl , refl) → refl }
  ; mono    = λ { (refl , refl) (refl , refl) rr → ⊥-elim (≺-irrefl {root} rr) }
  ; reflect = λ { (refl , refl) (refl , refl) _ → [] , refl }
  ; inst    = λ { (refl , refl) (refl , refl) → mk⇔ (λ _ → refl) (λ _ → refl) }
  }

fresh-At₀ : Fresh (λ _ → ⊥) At₀ root
fresh-At₀ (refl , refl) _ = refl
