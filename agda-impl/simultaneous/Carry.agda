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
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary using (yes; no)
open import denotation.Position using (_<ᵖ_)
open import denotation.Laws.Modulus using (≼-split)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; Path; ix; _∙_; _⊕_; root; lt; eq; gt; cmpLabel; cmpPath; cmpInstant; isLt)
open import denotation.Simultaneity using (eqˡ; eqⁱ)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; hot; enter; Proper; DenEnv; Few; _≺_; ⟦_⟧; approx; module Op)
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import denotation.Laws.Modulus using (≺-irrefl)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; W; _⊑_; ⊕-identityʳ; world-after)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Spent; events; elaborated)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark)
open import simultaneous.HeldComb using (ev)
open import simultaneous.Attribution using (Live; Shown; Match; Attribution; Every; One; Reads)
open import denotation.Position using (_≟ᵖ_)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; annotate; mapIE)
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
module Relabel {A A′ Y Y′ : Set} {f : Y → List A} {f′ : Y′ → List A′} {M : PMap} {HP HE : Pos → Set}
  {t : EmissionSet A} {t′ : EmissionSet A′} {u : EmissionSet Y} {u′ : EmissionSet Y′} {s s′ : Pos}
  (R : Pos → Ev A → Ev A′ → Set) (R′ : Pos → Ev Y → Ev Y′ → Set)
  (kin : ∀ {k e e′} → R k e e′ → Kin e e′) (kin′ : ∀ {l e e′} → R′ l e e′ → Kin e e′)
  (up : ∀ {k e} → t k e → Σ (Ev A′) λ e′ → t′ k e′ × R k e e′)
  (down : ∀ {k e′} → t′ k e′ → Σ (Ev A) λ e → t k e × R k e e′)
  (up′ : ∀ {l e} → u l e → Σ (Ev Y′) λ e′ → u′ l e′ × R′ l e e′)
  (down′ : ∀ {l e′} → u′ l e′ → Σ (Ev Y) λ e → u l e × R′ l e e′)
  (c : CarryAt f M HP HE t u s s′)
  (sh : ∀ {l e e′} → R′ l e e′ → Shown (One f′) e′ → Shown (One f) e)
  (mt : ∀ {k l e₀ e₁ e₀′ e₁′} → CarryAt.Img c k l → R k e₀ e₀′ → R′ l e₁ e₁′
      → Match Every (One f) (Reads f) e₀ e₁ → Match Every (One f′) (Reads f′) e₀′ e₁′) where
  open CarryAt c
  private
    module T = Rows {a = t} {b = t′} {Rel = R} kin up down
    module U = Rows {a = u} {b = u′} {Rel = R′} kin′ up′ down′

    img′ : ∀ {k e′} → t′ k e′ → Unpinned e′ → Live t′ k → Few t′ k
         → Σ Pos λ l → Img k l × Σ (Ev Y′) λ e₁′ → u′ l e₁′ × Few u′ l × Match Every (One f′) (Reads f′) e′ e₁′
    img′ {k} tk un lv fw with down tk
    ... | e , tk₀ , r with img tk₀ (unp← (kin r) un) (T.live← {k} (λ {c} → lv {c})) (T.few← {k} fw)
    ...   | l , i , e₁ , ul , fu , m with up′ ul
    ...     | e₁′ , ul′ , r′ = l , i , e₁′ , ul′ , U.few→ {l} fu , mt i r r′ m

    shown′ : ∀ {l e₁′} → u′ l e₁′ → Shown (One f′) e₁′ → Live u′ l → Few u′ l
           → Σ Pos λ k → Img k l × Σ (Ev A′) λ e₀′ → t′ k e₀′ × Match Every (One f′) (Reads f′) e₀′ e₁′
    shown′ {l} ul sw lv fw with down′ ul
    ... | e₁ , ul₀ , r′ with shown ul₀ (sh r′ sw) (U.live← {l} (λ {c} → lv {c})) (U.few← {l} fw)
    ...   | k , i , e₀ , tk , m with up tk
    ...     | e₀′ , tk′ , r = k , i , e₀′ , tk′ , mt i r r′ m

    img-row′ : ∀ {k l} → Img k l → Σ (Ev A′) λ e → t′ k e × Unpinned e
    img-row′ i with img-row i
    ... | e , tk , un with up tk
    ...   | e′ , tk′ , r = e′ , tk′ , unp→ (kin r) un

    owes′ : ∀ {c r} → Owes M HE t s′ c r → Owes M HE t′ s′ c r
    owes′ {row k}    ((_ , tk) , y)  = (_ , proj₁ (proj₂ (up tk))) , y
    owes′ {env h}    o               = o
    owes′ {both k h} ((_ , tk) , hy) = (_ , proj₁ (proj₂ (up tk))) , hy
    owes′ {subs}     o               = o

    homed′ : ∀ {k} → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → Σ (Ev A) λ e₀ → t k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k)
               ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
           → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → Σ (Ev A′) λ e₀ → t′ k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k)
               ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
    homed′ (inj₁ e)                          = inj₁ e
    homed′ (inj₂ (inj₁ (k₀ , e₀ , tk , un , ek))) with up tk
    ... | e₀′ , tk′ , r = inj₂ (inj₁ (k₀ , e₀′ , tk′ , unp→ (kin r) un , ek))
    homed′ (inj₂ (inj₂ h))                   = inj₂ (inj₂ h)

    pinned′ : ∀ {k p} → t′ k (pin p) → Live t′ k → (Σ Pos λ l → Σ (Ev Y′) (u′ l) × k ∈ pbk l)
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → Σ (Ev A′) λ e₀ → t′ k₀ e₀ × Unpinned e₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ {k} tk lv with down tk
    ... | _ , tk₀ , r with kin r
    ...   | k-pin with pinned tk₀ (T.live← {k} (λ {c} → lv {c}))
    ...     | (l , (_ , ul) , m) , h = (l , (proj₁ (up′ ul) , proj₁ (proj₂ (up′ ul))) , m) , homed′ {k} h

  carried : CarryAt f′ M HP HE t′ u′ s s′
  carried = record
    { Img = Img ; ext = ext ; img = img′ ; shown = shown′ ; img-row = img-row′ ; img-fun = img-fun
    ; place = λ {m} um lv fw → place (proj₁ (proj₂ (down′ um))) (U.live← {m} (λ {c} → lv {c})) (U.few← {m} fw)
    ; live = λ {k} {l} i lv → U.live→ {l} (λ {c} → live i (T.live← {k} (λ {c′} → lv {c′})) {c})
    ; few = λ {k} i → T.few→ {k} (few i)
    ; cause = λ ur → cause (proj₁ (proj₂ (down′ ur)))
    ; owes = λ ur → owes′ (owes (proj₁ (proj₂ (down′ ur))))
    ; fib = fib
    ; in-fib = λ ur → in-fib (proj₁ (proj₂ (down′ ur)))
    ; read = λ {r} ur rd → U.live→ {r} (λ {c} → read (proj₁ (proj₂ (down′ ur))) rd {c})
    ; bk = bk ; in-bk = in-bk ; pbk = pbk ; pinned = pinned′ }

------------------------------------------------------------------------
-- A map

private
  kin-map : ∀ {A B} {g : A → B} (e : Ev A) → Kin e (mapEv g e)
  kin-map (out _) = k-out
  kin-map skip    = k-skip
  kin-map (pin _) = k-pin
  kin-map end     = k-end

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
map-carry : ∀ {A B} (g : A → B) (d : Den A) (d′ : Den (IE A)) {M HP HE} p p′
          → CarryAt valuesOf M HP HE (enter d p) (enter d′ p′) p p′
          → CarryAt valuesOf M HP HE (enter (Op.map g d) p) (enter (Op.map (mapIE g) d′) p′) p p′
map-carry g d d′ p p′ c =
  Relabel.carried (λ _ e e′ → e′ ≡ mapEv g e) (λ _ e e′ → e′ ≡ mapEv (mapIE g) e)
    (λ { {e = e} refl → kin-map e }) (λ { {e = e} refl → kin-map e })
    (λ tk → _ , P.lift tk , refl) P.unmap (λ ul → _ , E.lift ul , refl) E.unmap c
    (λ { {e = e} refl sw → sh-map {g = g} e sw }) (λ { {e₀ = e₀} {e₁ = e₁} _ refl refl m → match-map {g = g} e₀ e₁ m })
  where
    module P = MapRun g d p
    module E = MapRun (mapIE g) d′ p′

------------------------------------------------------------------------
-- From a carried run to its attribution

-- With no environment, a run carried along an order embedding, from a
-- subscription its map puts under the other's, is attributed: the order,
-- the instants and the home instant come from the map's.
module _ {A : Set} {M : PMap} (hm : Emb M) {t : EmissionSet A} {u : EmissionSet (IE A)} {s s′ : Pos}
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
        ... | yes kk = ∈-++⁺ˡ (f₁ tk kk)
        ... | no ge with ≼-split {k} {k₁} ge
        ...   | inj₁ kk   = ∈-++⁺ʳ ks₁ (there (proj₁ (f₂ tk kk)))
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
    apart (Emb.mono hm my my′ kk) (λ yy → led-row i i′ kk (Emb.reflect hm my my′ yy)) σ σ′

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
Fresh HP HE M₀ p p′ = ∀ {x y} → M₀ x y → ¬ W HP p x × ¬ W HE p′ y

-- What the map adds lies in the two worlds.
Within : (Pos → Set) → (Pos → Set) → PMap → PMap → Pos → Pos → Set
Within HP HE M₀ M p p′ = ∀ {x y} → M x y → M₀ x y ⊎ (W HP p x × W HE p′ y)

-- CARRIED under every environment of carried binders: subscribed at
-- admissible positions the map pairs, its worlds untouched, the subterm
-- extends the map over its worlds and carries.
-- A record, so that a statement about a former is compared by its
-- arguments, never by the elaborated tree its meaning unfolds to.
record Carry (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor carry
  field carries : ∀ (envP : DenEnv Γ) (envE : DenEnv Δ) → GoodEnv envP → GoodEnv envE
                → ∀ M₀ → Emb M₀ → EnvRel M₀ ρ envP envE
                → ∀ p p′ → M₀ p p′ → Ok (Hots envP) p → Ok (Hots envE) p′ → Fresh (Hots envP) (Hots envE) M₀ p p′
                → Σ PMap λ M → M₀ ⊆ᴹ M × Emb M × Within (Hots envP) (Hots envE) M₀ M p p′
                  × CarryAt valuesOf M (Hots envP) (Hots envE) (enter (ev m o envP) p) (enter (ev m (elab ρ o) envE) p′) p p′

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER CARRIES its plain counterpart when its children
-- do, under the meaning and under every approximant alike.
postulate
  carry-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → Carry m ρ (cold c)
  carry-empty     : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → Carry m ρ (empty {A = A})
  carry-of        : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → Carry m ρ (of xs)
  carry-scan      : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → Carry m ρ s → Carry m ρ (scan f z s)
  carry-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → Carry m ρ s → Carry m ρ (takeWhile i p s)
  carry-flatMap   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → Carry m ρ s
                  → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → Carry m ρ′ (f a)) → Carry m ρ (flatMap op f s)
  carry-connect   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                  → Carry m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → Carry m ρ′ b) → Carry m ρ (connect s b)
  carry-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → Carry m ρ (connected i)

carry-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → Carry m ρ s → Carry m ρ (map f s)
carry-map nothing ρ f s (carry h) = carry λ envP envE gP gE M₀ hm er p p′ m₀ okP okE fr →
  let (M , ms , hm′ , wi , c) = h envP envE gP gE M₀ hm er p p′ m₀ okP okE fr
  in M , ms , hm′ , wi , map-carry f (⟦ s ⟧ envP) (⟦ elab ρ s ⟧ envE) p p′ c
carry-map (just n) ρ f s (carry h) = carry λ envP envE gP gE M₀ hm er p p′ m₀ okP okE fr →
  let (M , ms , hm′ , wi , c) = h envP envE gP gE M₀ hm er p p′ m₀ okP okE fr
  in M , ms , hm′ , wi , map-carry f (approx n s envP) (approx n (elab ρ s) envE) p p′ c

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
  carry-wrap : ∀ {A} (o : SObs [] A) {M} → Emb M → M root coreAt
             → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (events o) (enter (⟦ elab (λ i → i) (plain o) ⟧ []) coreAt) root coreAt
             → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (events o) (elaborated o) root root

-- The plain run's subscription paired with the core's: one pair, in
-- neither world.
At₀ : PMap
At₀ x y = x ≡ root × y ≡ coreAt

emb-At₀ : Emb At₀
emb-At₀ = record
  { mono    = λ { (refl , refl) (refl , refl) rr → ⊥-elim (≺-irrefl {root} rr) }
  ; reflect = λ { (refl , refl) (refl , refl) _ → [] , refl }
  ; inst    = λ { (refl , refl) (refl , refl) → mk⇔ (λ _ → refl) (λ _ → refl) }
  }

fresh-At₀ : Fresh (λ _ → ⊥) (λ _ → ⊥) At₀ root coreAt
fresh-At₀ (refl , refl) = (λ w → ≺-irrefl {root} (world-after w tt)) , (λ w → ≺-irrefl {coreAt} (world-after w tt))
