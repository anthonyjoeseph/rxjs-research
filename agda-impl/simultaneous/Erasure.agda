{-# OPTIONS --guardedness #-}

-- THE ERASURE, READ OFF THE VALUES IN ORDER.  A met run's values are a
-- stream's first values in order (`Enumerate`), each before every end;
-- past an ended run no value is left.  Wherever finitely many rows
-- precede and they are listed, a visible row before every end is met at
-- the end of a run (`Reaching`).
--
-- So the elaborated run and the plain one are matched value by value:
-- each side's last value has a counterpart of the same index on the
-- other, met at the end of a run there, and two runs whose values run to
-- the same index carry the same values with the same stamps, their last
-- instants over together.  An ended run is matched by the other side's
-- end: each side's values, all of them, have counterparts on the other.
-- What is left is a fact of rows, not runs.
module simultaneous.Erasure where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
import Data.List as L
open import Data.List.Properties using (length-++; length-map; map-++; ++-identityʳ; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([])
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _+_; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; ≤-antisym; ≤-pred; n<1+n; _<?_; ≮⇒≥; m≤n⇒m<n∨m≡n; suc-injective)
open import Data.Bool using (true; false)
open import Data.Bool.Properties using (T?)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import denotation.Position using (Pos; root; _≟ᵖ_; _<ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; module Values; ⟦_⟧)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Modulus using (≼-split; ≼-antisym; ≼-refl; ≺→≼; ≼-trans; ≼-≺-≺; ≺-trans; few-ind)
open import denotation.Laws.Nth using (module Nths)
open import simultaneous.InstEmit using (instEmit; value; mark; valuesOf)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.Readings using (stamped)
open import simultaneous.Relations using (Met; ranked; Rank; values; outs; vals; stampedᴮ; stampedᴰ; carried; Over; Closes; Ends; Erases;
  elaborated; events)
open import simultaneous.Ranks using (unrank; ranks-x; ranks-e; instant-rank; enter-few; visible-unpinned)
open import simultaneous.Listing using (Listing; listed)
open import simultaneous.Layers using (at-func; run-tail; run-++; cursor-snoc; ends-last; snoc-view)
open import simultaneous.Project using (run-prefix)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Worlds using (InvAt)
open import simultaneous.Reach using (module Reached)
open import simultaneous.Attribution using (Live; Single; V; vrow; Attribution; Every; One; Reads; module Attributed)
open import simultaneous.Carry using (Carry; carry-⟦⟧; hom-∅; coreAt; attributed; carry-wrap)
open import denotation.Laws.Worlds using (⊕-assoc)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; elaborate)
open Values using (Nth; Next; first; next)
open Equivalence using (to; from)

------------------------------------------------------------------------
-- A stream's values, one row at a time

-- A run's values through `f`, each at its row.
picks : ∀ {X A : Set} → (X → List A) → List (Pos × Ev X) → List (Pos × A)
picks f []                 = []
picks f ((q , out x) ∷ rs) = L.map (q ,_) (f x) ++ picks f rs
picks f ((_ , skip) ∷ rs)  = picks f rs
picks f ((_ , end) ∷ rs)   = picks f rs
picks f ((_ , pin _) ∷ rs) = picks f rs

picks-++ : ∀ {X A : Set} (f : X → List A) xs ys → picks f (xs ++ ys) ≡ picks f xs ++ picks f ys
picks-++ f []                 ys = refl
picks-++ f ((q , out x) ∷ xs) ys = trans (cong (L.map (q ,_) (f x) ++_) (picks-++ f xs ys)) (sym (++-assoc (L.map (q ,_) (f x)) (picks f xs) (picks f ys)))
picks-++ f ((_ , skip) ∷ xs)  ys = picks-++ f xs ys
picks-++ f ((_ , end) ∷ xs)   ys = picks-++ f xs ys
picks-++ f ((_ , pin _) ∷ xs) ys = picks-++ f xs ys

-- The i-th, (i+1)-th, ... values of `t` through `f`, each before every end.
data Enum {X A : Set} (f : X → List A) (t : EmissionSet X) : ℕ → List (Pos × A) → Set where
  []  : ∀ {i} → Enum f t i []
  _∷_ : ∀ {i q a vs} → Nth (V f t) i q a × Live t q → Enum f t (suc i) vs → Enum f t i ((q , a) ∷ vs)

-- The last of them is the (i + its place)-th.
enum-snoc : ∀ {X A : Set} {f : X → List A} {t i} xs {k a} → Enum f t i (xs ++ [ (k , a) ]) → Nth (V f t) (i + length xs) k a × Live t k
enum-snoc {f = f} {t} {i} []       {k} {a} ((n , l) ∷ []) = subst (λ j → Nth (V f t) j k a) (sym (+-identityʳ i)) n , l
enum-snoc {f = f} {t} {i} (_ ∷ xs) {k} {a} (_ ∷ en) with enum-snoc xs en
... | n , l = subst (λ j → Nth (V f t) j k a) (sym (+-suc i (length xs))) n , l

-- Where a reader at `c` stands among the values: `i` of them met, every
-- later one past `c`.
data Prev {X A : Set} (f : X → List A) (t : EmissionSet X) : Maybe Pos → ℕ → Set where
  pre₀ : ∀ {c} → (∀ {k a} → V f t k (out a) → After c k) → Prev f t c 0
  pre  : ∀ {c₀ i q a} → Nth (V f t) i q a → q ≼ c₀ → (∀ {k b} → V f t k (out b) → q ≺ k → c₀ ≺ k) → Prev f t (just c₀) (suc i)

module Enumerate {X A : Set} {f : X → List A} (sv : Single f) {t : EmissionSet X}
                 (func : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) where
  private
    module N = Nths (V f t)

    vrow-row : ∀ {k a} → V f t k (out a) → Σ X λ x → t k (out x)
    vrow-row (vrow r _) = _ , r

    -- A row carrying no value is no value row.
    no-val : ∀ {q e a} → t q e → (∀ {x} → e ≡ out x → f x ≡ []) → V f t q (out a) → ⊥
    no-val r nv (vrow r′ fx) with func r r′
    ... | refl with () ← trans (sym (nv refl)) fx

    -- Past a row carrying no value, a value met no earlier lies strictly after.
    past : ∀ {c q e} → t q e → (∀ {x} → e ≡ out x → f x ≡ []) → (∀ {k e′} → t k e′ → Visible e′ → After c k → q ≼ k)
         → ∀ {k b} → V f t k (out b) → After c k → q ≺ k
    past {q = q} r nv least {k} vk ak with ≼-split {q} {k} (least (proj₂ (vrow-row vk)) tt ak)
    ... | inj₁ lt   = lt
    ... | inj₂ refl = ⊥-elim (no-val r nv vk)

    -- The reader moves past a row carrying no value.
    skip-prev : ∀ {c q e i} → t q e → (∀ {x} → e ≡ out x → f x ≡ []) → After c q
              → (∀ {k e′} → t k e′ → Visible e′ → After c k → q ≼ k) → Prev f t c i → Prev f t (just q) i
    skip-prev {c} {q} r nv aq least (pre₀ all) =
      pre₀ λ {k} vk → past {c = c} {q = q} r nv least {k} vk (all vk)
    skip-prev {q = q} r nv aq least (pre {c₀} {q = q₀} n q₀c₀ later) =
      pre n (≺→≼ {q₀} {q} (≼-≺-≺ {q₀} {c₀} {q} q₀c₀ aq)) λ {k} vk q₀k → past {c = just c₀} {q = q} r nv least {k} vk (later vk q₀k)

    -- The value met next is the next value.
    nth-of : ∀ {c q i a} → V f t q (out a) → After c q → (∀ {k e′} → t k e′ → Visible e′ → After c k → q ≼ k)
           → Prev f t c i → Nth (V f t) i q a
    nth-of vq aq least (pre₀ all) = first vq λ vk → least (proj₂ (vrow-row vk)) tt (all vk)
    nth-of {q = q} vq aq least (pre {c₀} {q = q₀} n q₀c₀ later) =
      next n vq (≼-≺-≺ {q₀} {c₀} {q} q₀c₀ aq) λ vk q₀k → least (proj₂ (vrow-row vk)) tt (later vk q₀k)

  enum-go : ∀ {c rs i} → Run t c rs → Prev f t c i → Enum f t i (picks f rs) × Prev f t (cursor c rs) (i + length (picks f rs))
  enum-go {i = i} [] p = [] , subst (Prev f t _) (sym (+-identityʳ i)) p
  enum-go {rs = (q , out x) ∷ rs} {i} ((((r , live) , _) , _ , aq , least) ∷ run) p with sv x
  ... | inj₁ fx rewrite fx = enum-go run (skip-prev {q = q} r (λ { refl → fx }) aq least p)
  ... | inj₂ (a , fx) rewrite fx with nth-of {q = q} (vrow r fx) aq least p
  ...   | n with enum-go run (pre n (≼-refl {q}) λ _ qk → qk)
  ...     | en , pv = ((n , live) ∷ en) , subst (Prev f t _) (sym (+-suc i (length (picks f rs)))) pv
  enum-go {rs = (q , end) ∷ rs} ((((r , _) , _) , _ , aq , least) ∷ run) p = enum-go run (skip-prev {q = q} r (λ ()) aq least p)
  enum-go {rs = (q , skip) ∷ rs}  ((_ , () , _) ∷ _) _
  enum-go {rs = (q , pin _) ∷ rs} ((_ , () , _) ∷ _) _

  -- A run met lists the first values in order.
  run-enum : ∀ {rs} → Met t rs → Enum f t 0 (picks f rs) × Prev f t (cursor nothing rs) (length (picks f rs))
  run-enum m = enum-go m (pre₀ λ _ → tt)

  private
    nth-down : ∀ {i j k a} → i ≤ j → Nth (V f t) j k a → Σ Pos λ q → Σ A λ b → Nth (V f t) i q b × q ≼ k
    nth-down {k = k} z≤n n@(first _ _) = k , _ , n , ≼-refl {k}
    nth-down {i} {suc j} {k} le n@(next {q = q₀} n₀ _ lt _) with m≤n⇒m<n∨m≡n le
    ... | inj₂ refl = k , _ , n , ≼-refl {k}
    ... | inj₁ lt′ with nth-down (≤-pred lt′) n₀
    ...   | q , b , nq , qp = q , b , nq , ≺→≼ {q} {k} (≼-≺-≺ {q} {q₀} {k} qp lt)

    after-nth : ∀ {c n k b} → Prev f t c n → Nth (V f t) n k b → After c k
    after-nth (pre₀ all)       n₁ = all (N.nth-val n₁)
    after-nth (pre n₀ _ later) n₁ = later (N.nth-val n₁) (N.nth-lt (n<1+n _) n₀ n₁)

  -- Past an ended run, no value is left before its end.
  beyond : ∀ rs {c} → Met t (rs ++ [ (c , end) ]) → ∀ {j k a} → Nth (V f t) j k a → Live t k → j < length (picks f rs)
  beyond rs {c} m {j} {k} n lk with j <? length (picks f rs)
  ... | yes lt = lt
  ... | no ge with nth-down (≮⇒≥ ge) n | proj₂ (run-enum (run-prefix rs m)) | run-tail rs m
  ...   | k₁ , b , n₁ , k₁k | pv | ((((xc , _) , _) , _ , _ , least) ∷ []) with vrow-row (N.nth-val n₁)
  ...     | x , r₁ with ≼-antisym {c} {k₁} (least r₁ tt (after-nth pv n₁)) (≼-trans {k₁} {k} {c} k₁k (lk xc))
  ...       | refl with () ← func xc r₁

module Reaching {X : Set} {t : EmissionSet X} (func : ∀ {y e e′} → t y e → t y e′ → e ≡ e′)
                (few : ∀ {q e} → t q e → Visible e → Few t q) (listing : Listing t) where
  private
    vis? : (e : Ev X) → Dec (Visible e)
    vis? (out _) = yes tt
    vis? end     = yes tt
    vis? skip    = no λ ()
    vis? (pin _) = no λ ()

    Latest : List Pos → Set
    Latest ks = (∀ {k e} → k ∈ ks → t k e → Visible e → ⊥)
              ⊎ Σ Pos λ v → Σ (Ev X) λ ev → v ∈ ks × t v ev × Visible ev × (∀ {k e} → k ∈ ks → t k e → Visible e → k ≼ v)

    -- The last visible row of a listing, if any.
    latest : (ks : List Pos) → (∀ {k} → k ∈ ks → Σ (Ev X) (t k)) → Latest ks
    latest []       _ = inj₁ λ ()
    latest (k ∷ ks) s with latest ks (λ m → s (there m)) | s (here refl)
    ... | r | e₁ , x₁ with vis? e₁
    ...   | no nv with r
    ...     | inj₁ none = inj₁ λ { (here refl) x v → nv (subst Visible (sym (func x₁ x)) v) ; (there m) x v → none m x v }
    ...     | inj₂ (v , ev , m , xv , vv , all) =
      inj₂ (v , ev , there m , xv , vv , λ { (here refl) x vi → ⊥-elim (nv (subst Visible (sym (func x₁ x)) vi)) ; (there m′) x vi → all m′ x vi })
    latest (k ∷ ks) s | inj₁ none | e₁ , x₁ | yes v₁ =
      inj₂ (k , e₁ , here refl , x₁ , v₁ , λ { (here refl) _ _ → ≼-refl {k} ; (there m) x vi → ⊥-elim (none m x vi) })
    latest (k ∷ ks) s | inj₂ (v , ev , m , xv , vv , all) | e₁ , x₁ | yes v₁ with T? (v <ᵖ k)
    ... | yes vk = inj₂ (k , e₁ , here refl , x₁ , v₁ , λ { (here refl) _ _ → ≼-refl {k} ; {k′} (there m′) x vi → ≼-trans {k′} {v} {k} (all m′ x vi) (≺→≼ {v} {k} vk) })
    ... | no kv  = inj₂ (v , ev , there m , xv , vv , λ { (here refl) _ _ → kv ; (there m′) x vi → all m′ x vi })

    Reaches : Pos → Set
    Reaches w = ∀ {e} → t w e → Live t w → Visible e → Σ _ λ rs → Met t (rs ++ [ (w , e) ])

    step : ∀ {w} → Few t w → (∀ {u e} → t u e → u ≺ w → Reaches u) → Reaches w
    step {w} F ih {e} x lw vi with listing F
    ... | ks , cover , sound with latest ks (λ m → proj₂ (sound m))
    ...   | inj₁ none = [] , (((x , lw) , F) , vi , tt , λ y vy _ yw → none (cover y yw) y vy) ∷ []
    ...   | inj₂ (u , eu , m , xu , vu , all) with ih xu (proj₁ (sound m)) xu (λ {c} ce cu → lw ce (≺-trans {c} {u} {w} cu (proj₁ (sound m)))) vu
    ...     | rs , run = rs ++ [ (u , eu) ] ,
      run-++ run (subst (λ c → Run t c [ (w , e) ]) (sym (cursor-snoc nothing rs))
        ((((x , lw) , F) , vi , proj₁ (sound m) , λ y vy uy yw → all (cover y yw) y vy uy) ∷ []))

  -- A visible row before every end is met at the end of a run.
  reach : ∀ {w e} → t w e → Live t w → Visible e → Σ _ λ rs → Met t (rs ++ [ (w , e) ])
  reach x lw vi = few-ind Reaches step (few x vi) x lw vi

------------------------------------------------------------------------
-- A ranked run's values

-- Each carried value indexed, before every end, with its rank.
data SEnum {X A : Set} (f : X → List A) (t : EmissionSet X) : ℕ → List (Pos × ℕ × A) → Set where
  []  : ∀ {i} → SEnum f t i []
  _∷_ : ∀ {i q n a vs} → Nth (V f t) i q a × Live t q × Rank t q n → SEnum f t (suc i) vs → SEnum f t i ((q , n , a) ∷ vs)

carried-enum : ∀ {X A : Set} {f : X → List A} (sv : Single f) {t c rs i} → Run (ranked t) c rs → Enum f t i (picks f (unrank rs))
             → SEnum f t i (carried f rs)
carried-enum sv [] [] = []
carried-enum sv {rs = (q , out (n , x)) ∷ rs} ((((r , _) , _) , _) ∷ run) en with sv x
... | inj₁ fx rewrite fx = carried-enum sv run en
... | inj₂ (a , fx) rewrite fx with en
...   | (nth , live) ∷ en′ = (nth , live , proj₂ r) ∷ carried-enum sv run en′
carried-enum sv {rs = (q , skip) ∷ rs}  (_ ∷ run) en = carried-enum sv run en
carried-enum sv {rs = (q , end) ∷ rs}   (_ ∷ run) en = carried-enum sv run en
carried-enum sv {rs = (q , pin _) ∷ rs} (_ ∷ run) en = carried-enum sv run en

carried-length : ∀ {X A : Set} (f : X → List A) rs → length (carried f rs) ≡ length (picks f (unrank rs))
carried-length f []                       = refl
carried-length f ((q , out (n , x)) ∷ rs) =
  trans (length-++ (L.map (λ b → q , n , b) (f x)))
    (trans (cong₂ _+_ (trans (length-map _ (f x)) (sym (length-map _ (f x)))) (carried-length f rs))
      (sym (length-++ (L.map (q ,_) (f x)))))
carried-length f ((q , skip) ∷ rs)  = carried-length f rs
carried-length f ((q , end) ∷ rs)   = carried-length f rs
carried-length f ((q , pin _) ∷ rs) = carried-length f rs

-- An elaborated run's values and a plain run's, through their readers.
private
  pairs : ∀ {B C : Set} (c : C) (ys : List B) → L.map proj₂ (L.map (c ,_) ys) ≡ ys
  pairs c []       = refl
  pairs c (y ∷ ys) = cong (y ∷_) (pairs c ys)

vals-picks : ∀ {A : Set} (rs : List (Pos × Ev (IE A))) → vals rs ≡ L.map proj₂ (picks valuesOf rs)
vals-picks []                 = refl
vals-picks ((q , out x) ∷ rs) =
  trans (map-++ proj₂ (L.map (λ a → _ , a) (valuesOf x)) (stamped (values rs)))
    (trans (cong₂ _++_ (trans (pairs _ (valuesOf x)) (sym (pairs q (valuesOf x)))) (vals-picks rs))
      (sym (map-++ proj₂ (L.map (q ,_) (valuesOf x)) (picks valuesOf rs))))
vals-picks ((q , skip) ∷ rs)  = vals-picks rs
vals-picks ((q , end) ∷ rs)   = vals-picks rs
vals-picks ((q , pin _) ∷ rs) = vals-picks rs

outs-picks : ∀ {A : Set} (rs : List (Pos × Ev A)) → outs rs ≡ picks [_] rs
outs-picks []                 = refl
outs-picks ((q , out a) ∷ rs) = cong ((q , a) ∷_) (outs-picks rs)
outs-picks ((q , skip) ∷ rs)  = outs-picks rs
outs-picks ((q , end) ∷ rs)   = outs-picks rs
outs-picks ((q , pin _) ∷ rs) = outs-picks rs

------------------------------------------------------------------------
-- The elaborated values and the plain ones, by index

-- An elaborated program's values, and its plain program's.
VX : ∀ {A} → SObs [] A → EmissionSet A
VX o = V valuesOf (elaborated o)

VE : ∀ {A} → SObs [] A → EmissionSet A
VE o = V [_] (events o)

-- One value or none off each elaborated emit.
single-values : ∀ {A} → Single {IE A} valuesOf
single-values (instEmit (value a) _) = inj₂ (a , refl)
single-values (instEmit (mark _) _)  = inj₁ refl

-- THE ELABORATION CARRIES THE PLAIN RUN: each unpinned plain row at or
-- before the end is carried by the elaborated row elaborating it, a
-- value by its value and the end by the end, in order, instant for
-- instant.  The elaboration adds no instant and holds no value; switch,
-- exhaust and the bounded queue are the real cases.
--
-- REFUTED: e10449e the ranks agreeing, with a rank counting only instants
--   holding rows: a run with no row in the subscribe frame ranks its
--   values one below its elaboration, whose subscribed mark lies there.
-- DEAD ROUTE: carrying every row, past the ends too.  A connect whose
--   body ends at once puts its source's burst pins past its end in the
--   subscribe frame, and the elaboration's end is that frame's last row:
--   no elaborated row lies past it to carry them in order.
-- DEAD ROUTE: carrying the pins in order.  Concat's elaboration
--   subscribes a queued lane under its own readers, so a pin of a later
--   lane's subscribe can fall past a value the plain run puts after it:
--   no elaborated row carries it in order.  A pin is carried only into
--   its instant, which is all a rank or an exit reads of it.
-- REFUTED: 711567f3 finitely many elaborated rows past every plain row's
--   carrier, outright: a connect whose source is an endless synchronous
--   burst under a silent body leaves endlessly many elaborated rows past
--   each; finitely many follow only a plain row past which finitely many
--   do.
-- REFUTED: 711567f3 every elaborated row put on a plain row or ahead of
--   all: under `connect (of [1]) (λ _ → ones)` a pin lies past endlessly
--   many carriers, so no reader reaches it to put it anywhere; only rows
--   a reader reaches are placed, each in the instant of a carrier.
erasing : ∀ {A} (o : SObs [] A) → Attribution Every (One valuesOf) (Reads valuesOf) (events o) (elaborated o) root root
erasing o with Carry.carries (carry-⟦⟧ (λ i → i) (plain o)) [] [] (λ ()) (λ ()) (λ _ _ → ⊥) hom-∅ (λ ())
                 root coreAt (tt , λ ()) (tt , λ ()) (λ ())
... | M , _ , hm , _ , (δ , at) , c =
  attributed hm (InvAt.flat (inv-⟦⟧ (plain o) [] (λ ()) root (tt , λ ()))) (_ ++ δ) (subst (M root) (⊕-assoc root _ δ) at)
    (carry-wrap o hm δ at c)

-- A plain row that is not a pin is at or before every end.
unpinned-live : ∀ {A} (o : SObs [] A) {k e} → events o k e → Unpinned e → Live (events o) k
unpinned-live o tk up {c} tc ck with InvAt.quiet (inv-⟦⟧ (plain o) [] (λ ()) root (tt , λ ())) tc tk ck
... | r , refl , _ = up

private
  module Er {A : Set} (o : SObs [] A) =
    Attributed {A} {IE A} {valuesOf} single-values {events o} {elaborated o}
      (λ {y} {e} {e′} → at-func (plain o) {y} {e} {e′}) (λ {y} {e} {e′} → at-func (elaborate (plain o)) {y} {e} {e′})
      (λ {k} {e} → Reached.seen (⟦ plain o ⟧ []) root (inv-⟦⟧ (plain o) [] (λ ()) root (tt , λ ())) {k} {e})
      (λ {k} {e} → Reached.seen (⟦ elaborate (plain o) ⟧ []) root (inv-⟦⟧ (elaborate (plain o)) [] (λ ()) root (tt , λ ())) {k} {e})
      (λ {k} {e} → enter-few (⟦ plain o ⟧ []) root {k} {e}) (λ {k} {e} → unpinned-live o {k} {e})
      (λ {q} → listed (plain o) {q}) (λ {q} → listed (elaborate (plain o)) {q})
      (erasing o)

-- THE I-TH VALUE IS THE I-TH: before each side's end, the elaborated
-- program's i-th value is its plain program's, at the same rank, its
-- instant over exactly when the other's is; and each side reaches an end
-- exactly when the other does.
erase-x : ∀ {A} (o : SObs [] A) {i k a} → Nth (VX o) i k a → Live (elaborated o) k
        → Σ Pos λ k′ → Nth (VE o) i k′ a × Live (events o) k′
erase-x o = Er.values-ut o

erase-e : ∀ {A} (o : SObs [] A) {i k′ a} → Nth (VE o) i k′ a → Live (events o) k′
        → Σ Pos λ k → Nth (VX o) i k a × Live (elaborated o) k
erase-e o = Er.values-tu o

erase-rank : ∀ {A} (o : SObs [] A) {i k k′ a b n} → Nth (VX o) i k a → Live (elaborated o) k → Nth (VE o) i k′ b → Live (events o) k′
           → Rank (elaborated o) k n → Rank (events o) k′ n
erase-rank o {n = n} nx lx ne _ r with Er.nth-ut o nx
... | k₀ , ak , nk = subst (λ q → Rank (events o) q n) (Nths.nth-fun (VE o) nk ne) (Er.rank-v o nx ak r)

erase-over : ∀ {A} (o : SObs [] A) {i k k′ a b} → Nth (VX o) i k a → Live (elaborated o) k → Nth (VE o) i k′ b → Live (events o) k′
           → Over valuesOf (elaborated o) (just k) ⇔ Over [_] (events o) (just k′)
erase-over o nx _ ne _ with Er.nth-ut o nx | Nths.nth-val (VX o) nx | Nths.nth-val (VE o) ne
... | k₀ , ak , nk | vrow ul fx | vrow tk refl with Nths.nth-fun (VE o) nk ne
...   | refl = Er.over-ut o ak ul (_ , fx) tk

erase-end : ∀ {A} (o : SObs [] A)
          → (Σ Pos λ c → elaborated o c end × Live (elaborated o) c) ⇔ (Σ Pos λ c′ → events o c′ end × Live (events o) c′)
erase-end o = Er.ends o

-- The last values of two runs, of one index.
data LastRel {A : Set} (o : SObs [] A) : Maybe Pos → Maybe Pos → Set where
  none : LastRel o nothing nothing
  both : ∀ {j k k′ a b} → Nth (VX o) j k a → Live (elaborated o) k → Nth (VE o) j k′ b → Live (events o) k′ → LastRel o (just k) (just k′)

module Erasing {A : Set} (o : SObs [] A) where
  private
    X = elaborated o
    E = events o

    funcX : ∀ {y e e′} → X y e → X y e′ → e ≡ e′
    funcX = at-func (elaborate (plain o))

    funcE : ∀ {y e e′} → E y e → E y e′ → e ≡ e′
    funcE = at-func (plain o)

    svE : Single {A} [_]
    svE x = inj₂ (x , refl)

    module EX = Enumerate {IE A} {A} {valuesOf} single-values {X} funcX
    module EE = Enumerate {A} {A} {[_]} svE {E} funcE
    module RX = Reaching {IE A} {X} funcX (λ {q} {e} r v → enter-few (⟦ elaborate (plain o) ⟧ []) root {q} {e} r (visible-unpinned v)) (λ {q} → listed (elaborate (plain o)) {q})
    module RE = Reaching {A} {E} funcE (λ {q} {e} r v → enter-few (⟦ plain o ⟧ []) root {q} {e} r (visible-unpinned v)) (λ {q} → listed (plain o) {q})
    module NX = Nths (VX o)
    module NE = Nths (VE o)

    -- One index, one plain value.
    same-val : ∀ {i q a b} → Nth (VE o) i q a → Nth (VE o) i q b → a ≡ b
    same-val n₁ n₂ with NE.nth-val n₁ | NE.nth-val n₂
    ... | vrow r₁ refl | vrow r₂ refl with funcE r₁ r₂
    ... | refl = refl

    -- The heads of two runs' values of one index.
    head-eq : ∀ {i q q′ n n′ a b} → Nth (VX o) i q a → Live X q → Rank X q n → Nth (VE o) i q′ b → Live E q′ → Rank E q′ n′
            → (n , a) ≡ (n′ , b)
    head-eq nx lx rx ne le re with erase-x o nx lx
    ... | k′ , ne′ , _ with NE.nth-fun ne′ ne
    ...   | refl = cong₂ _,_ (instant-rank (erase-rank o nx lx ne le rx) re refl) (same-val ne′ ne)

    -- Two runs' values to one index: one stamped list, the last values of one index.
    core : ∀ {i L L′} → SEnum valuesOf X i L → SEnum [_] E i L′ → length L ≡ length L′
         → L.map proj₂ L ≡ L.map proj₂ L′ × LastRel o (L.last (L.map proj₁ L)) (L.last (L.map proj₁ L′))
    core [] [] _ = refl , none
    core ((nx , lx , rx) ∷ []) ((ne , le , re) ∷ []) _ = cong (_∷ []) (head-eq nx lx rx ne le re) , both nx lx ne le
    core ((nx , lx , rx) ∷ sx@(_ ∷ _)) ((ne , le , re) ∷ se@(_ ∷ _)) len with core sx se (suc-injective len)
    ... | eq , lr = cong₂ _∷_ (head-eq nx lx rx ne le re) eq , lr
    core (_ ∷ []) (_ ∷ _ ∷ _) ()
    core (_ ∷ _ ∷ _) (_ ∷ []) ()

    -- Two runs' values to one index, unstamped.
    vmatch : ∀ {i xs ys} → Enum valuesOf X i xs → Enum [_] E i ys → length xs ≡ length ys → L.map proj₂ xs ≡ L.map proj₂ ys
    vmatch [] [] _ = refl
    vmatch ((nx , lx) ∷ ex) ((ne , le) ∷ ee) len with erase-x o nx lx
    ... | k′ , ne′ , _ with NE.nth-fun ne′ ne
    ...   | refl = cong₂ _∷_ (same-val ne′ ne) (vmatch ex ee (suc-injective len))

    over-x : ∀ {l l′} → LastRel o l l′ → Over valuesOf X l → Over [_] E l′
    over-x none               _  = tt
    over-x (both nx lx ne le) ov = to (erase-over o nx lx ne le) ov

    over-e : ∀ {l l′} → LastRel o l l′ → Over [_] E l′ → Over valuesOf X l
    over-e none               _  = tt
    over-e (both nx lx ne le) ov = from (erase-over o nx lx ne le) ov

    closes-x : ∀ ov {rx rs′} → LastRel o (L.last (L.map proj₁ (carried valuesOf rx))) (L.last (L.map proj₁ (carried [_] rs′)))
             → Closes valuesOf X rx ov → Closes [_] E rs′ ov
    closes-x false _  _ = tt
    closes-x true  lr c = over-x lr c

    closes-e : ∀ ov {rx rs′} → LastRel o (L.last (L.map proj₁ (carried valuesOf rx))) (L.last (L.map proj₁ (carried [_] rs′)))
             → Closes [_] E rs′ ov → Closes valuesOf X rx ov
    closes-e false _  _ = tt
    closes-e true  lr c = over-e lr c

    -- A plain value, as a row.
    e-row : ∀ {k a} → VE o k (out a) → E k (out a)
    e-row (vrow r refl) = r

    -- The last value of a run, reached on the other side: a ranked run
    -- there whose values run to the same index.
    to-e : ∀ xs {k a} → Enum valuesOf X 0 (xs ++ [ (k , a) ])
         → Σ _ λ rs′ → Met (ranked E) rs′ × length (picks [_] (unrank rs′)) ≡ length (xs ++ [ (k , a) ])
    to-e xs {k} {a} en with enum-snoc xs en
    ... | nx , lx with erase-x o nx lx
    ...   | k′ , ne , le with RE.reach (e-row (NE.nth-val ne)) le tt
    ...     | rs₀ , mE with proj₁ (ranks-e o) mE
    ...       | rs′ , mr′ , eq = rs′ , mr′ ,
      trans (cong (λ r → length (picks [_] r)) eq)
        (trans (cong length (picks-++ [_] rs₀ [ (k′ , out a) ]))
          (trans (length-++ (picks [_] rs₀)) (trans (cong (_+ 1) idx) (sym (length-++ xs)))))
      where
        en′ : Enum [_] E 0 (picks [_] rs₀ ++ [ (k′ , a) ])
        en′ = subst (Enum [_] E 0) (picks-++ [_] rs₀ [ (k′ , out a) ]) (proj₁ (EE.run-enum mE))

        idx : length (picks [_] rs₀) ≡ length xs
        idx = NE.nth-inj (proj₁ (enum-snoc (picks [_] rs₀) en′)) ne

    to-x : ∀ ys {k′ a} → Enum [_] E 0 (ys ++ [ (k′ , a) ])
         → Σ _ λ rx → Met (ranked X) rx × length (picks valuesOf (unrank rx)) ≡ length (ys ++ [ (k′ , a) ])
    to-x ys {k′} {a} en with enum-snoc ys en
    ... | ne , le with erase-e o ne le
    ...   | k , nx , lx with NX.nth-val nx
    ...     | vrow {x = x} r fx with RX.reach r lx tt
    ...       | rs₀ , mX with proj₁ (ranks-x o) mX
    ...         | rx , mr , eq = rx , mr ,
      trans (cong (λ r → length (picks valuesOf r)) eq)
        (trans (cong length (trans (picks-++ valuesOf rs₀ [ (k , out x) ]) (cong (picks valuesOf rs₀ ++_) tail)))
          (trans (length-++ (picks valuesOf rs₀)) (trans (cong (_+ 1) idx) (sym (length-++ ys)))))
      where
        tail : picks valuesOf [ (k , out x) ] ≡ [ (k , a) ]
        tail = trans (++-identityʳ (L.map (k ,_) (valuesOf x))) (cong (L.map (k ,_)) fx)

        en′ : Enum valuesOf X 0 (picks valuesOf rs₀ ++ [ (k , a) ])
        en′ = subst (Enum valuesOf X 0) (trans (picks-++ valuesOf rs₀ [ (k , out x) ]) (cong (picks valuesOf rs₀ ++_) tail))
                (proj₁ (EX.run-enum mX))

        idx : length (picks valuesOf rs₀) ≡ length ys
        idx = NX.nth-inj (proj₁ (enum-snoc (picks valuesOf rs₀) en′)) nx

  dir₁ : ∀ {rx ov} → Met (ranked X) rx → Closes valuesOf X rx ov
       → Σ _ λ rs′ → Met (ranked E) rs′ × Closes [_] E rs′ ov × stampedᴮ rx ≡ stampedᴰ rs′
  dir₁ {rx} {ov} mr cl = finish (snoc-view (picks valuesOf (unrank rx)))
    where
      ex : Enum valuesOf X 0 (picks valuesOf (unrank rx))
      ex = proj₁ (EX.run-enum {unrank rx} (proj₂ (ranks-x o) {rx} mr))

      sx : SEnum valuesOf X 0 (carried valuesOf rx)
      sx = carried-enum single-values {t = X} {nothing} {rx} {0} mr ex

      matched : ∀ {rs′} → Met (ranked E) rs′ → length (carried valuesOf rx) ≡ length (carried [_] rs′)
              → Σ _ λ rs″ → Met (ranked E) rs″ × Closes [_] E rs″ ov × stampedᴮ rx ≡ stampedᴰ rs″
      matched {rs′} mr′ len =
        rs′ , mr′ , closes-x ov {rx} {rs′} (proj₂ (core sx se len)) cl , proj₁ (core sx se len)
        where
          se : SEnum [_] E 0 (carried [_] rs′)
          se = carried-enum svE {t = E} {nothing} {rs′} {0} mr′ (proj₁ (EE.run-enum {unrank rs′} (proj₂ (ranks-e o) {rs′} mr′)))

      finish : picks valuesOf (unrank rx) ≡ [] ⊎ Σ _ (λ xs → Σ _ λ p → picks valuesOf (unrank rx) ≡ xs ++ [ p ])
             → Σ _ λ rs′ → Met (ranked E) rs′ × Closes [_] E rs′ ov × stampedᴮ rx ≡ stampedᴰ rs′
      finish (inj₁ e₀) = matched {[]} [] (trans (carried-length valuesOf rx) (cong length e₀))
      finish (inj₂ (xs , (k , a) , e₁)) = use e₁ (to-e xs (subst (Enum valuesOf X 0) e₁ ex))
        where
          use : ∀ {ps} → picks valuesOf (unrank rx) ≡ ps → (Σ _ λ rs′ → Met (ranked E) rs′ × length (picks [_] (unrank rs′)) ≡ length ps)
              → Σ _ λ rs′ → Met (ranked E) rs′ × Closes [_] E rs′ ov × stampedᴮ rx ≡ stampedᴰ rs′
          use e (rs′ , mr′ , len) =
            matched mr′ (trans (carried-length valuesOf rx) (trans (cong length e) (trans (sym len) (sym (carried-length [_] rs′)))))

  dir₂ : ∀ {rs′ ov} → Met (ranked E) rs′ → Closes [_] E rs′ ov
       → Σ _ λ rx → Met (ranked X) rx × Closes valuesOf X rx ov × stampedᴰ rs′ ≡ stampedᴮ rx
  dir₂ {rs′} {ov} mr′ cl = finish (snoc-view (picks [_] (unrank rs′)))
    where
      ee : Enum [_] E 0 (picks [_] (unrank rs′))
      ee = proj₁ (EE.run-enum {unrank rs′} (proj₂ (ranks-e o) {rs′} mr′))

      se : SEnum [_] E 0 (carried [_] rs′)
      se = carried-enum svE {t = E} {nothing} {rs′} {0} mr′ ee

      matched : ∀ {rx} → Met (ranked X) rx → length (carried valuesOf rx) ≡ length (carried [_] rs′)
              → Σ _ λ rx′ → Met (ranked X) rx′ × Closes valuesOf X rx′ ov × stampedᴰ rs′ ≡ stampedᴮ rx′
      matched {rx} mr len =
        rx , mr , closes-e ov {rx} {rs′} (proj₂ (core sx se len)) cl , sym (proj₁ (core sx se len))
        where
          sx : SEnum valuesOf X 0 (carried valuesOf rx)
          sx = carried-enum single-values {t = X} {nothing} {rx} {0} mr (proj₁ (EX.run-enum {unrank rx} (proj₂ (ranks-x o) {rx} mr)))

      finish : picks [_] (unrank rs′) ≡ [] ⊎ Σ _ (λ ys → Σ _ λ p → picks [_] (unrank rs′) ≡ ys ++ [ p ])
             → Σ _ λ rx → Met (ranked X) rx × Closes valuesOf X rx ov × stampedᴰ rs′ ≡ stampedᴮ rx
      finish (inj₁ e₀) = matched {[]} [] (sym (trans (carried-length [_] rs′) (cong length e₀)))
      finish (inj₂ (ys , (k′ , a) , e₁)) = use e₁ (to-x ys (subst (Enum [_] E 0) e₁ ee))
        where
          use : ∀ {ps} → picks [_] (unrank rs′) ≡ ps → (Σ _ λ rx → Met (ranked X) rx × length (picks valuesOf (unrank rx)) ≡ length ps)
              → Σ _ λ rx → Met (ranked X) rx × Closes valuesOf X rx ov × stampedᴰ rs′ ≡ stampedᴮ rx
          use e (rx , mr , len) =
            matched mr (trans (carried-length valuesOf rx) (trans len (trans (sym (cong length e)) (sym (carried-length [_] rs′)))))

  private
    -- An ended run's last row is its end, at or before every end.
    ended : ∀ {B : Set} {t : EmissionSet B} {rs} → Met t rs → Ends rs
          → Σ _ λ rs₀ → Σ Pos λ c → rs ≡ rs₀ ++ [ (c , end) ] × t c end × Live t c
    ended {rs = rs} m en with snoc-view rs
    ended {rs = .[]} m () | inj₁ refl
    ... | inj₂ (rs₀ , (c , ec) , refl) with ends-last rs₀ m en
    ...   | refl with run-tail rs₀ m
    ...     | ((((xc , lc) , _) , _) ∷ []) = rs₀ , c , refl , xc , lc

    -- Two ended runs' values to one count.
    counts : ∀ xs ys {cx ce} → Met X (xs ++ [ (cx , end) ]) → Met E (ys ++ [ (ce , end) ])
           → length (picks valuesOf xs) ≡ length (picks [_] ys)
    counts xs ys mx me = ≤-antisym (bound-x (snoc-view (picks valuesOf xs)) (proj₁ (EX.run-enum (run-prefix xs mx))))
                                   (bound-e (snoc-view (picks [_] ys)) (proj₁ (EE.run-enum (run-prefix ys me))))
      where
        bound-x : ∀ {ps} → ps ≡ [] ⊎ Σ _ (λ ps₀ → Σ _ λ p → ps ≡ ps₀ ++ [ p ]) → Enum valuesOf X 0 ps → length ps ≤ length (picks [_] ys)
        bound-x (inj₁ refl) _ = z≤n
        bound-x (inj₂ (ps₀ , (k , a) , refl)) en with enum-snoc ps₀ en
        ... | nx , lx with erase-x o nx lx
        ...   | _ , ne , le = subst (_≤ _) (trans (sym (+-comm (length ps₀) 1)) (sym (length-++ ps₀))) (EE.beyond ys me ne le)

        bound-e : ∀ {ps} → ps ≡ [] ⊎ Σ _ (λ ps₀ → Σ _ λ p → ps ≡ ps₀ ++ [ p ]) → Enum [_] E 0 ps → length ps ≤ length (picks valuesOf xs)
        bound-e (inj₁ refl) _ = z≤n
        bound-e (inj₂ (ps₀ , (k , a) , refl)) en with enum-snoc ps₀ en
        ... | ne , le with erase-e o ne le
        ...   | _ , nx , lx = subst (_≤ _) (trans (sym (+-comm (length ps₀) 1)) (sym (length-++ ps₀))) (EX.beyond xs mx nx lx)

    end-picks : ∀ {B C : Set} (f : B → List C) xs c → picks f (xs ++ [ (c , end) ]) ≡ picks f xs
    end-picks f xs c = trans (picks-++ f xs [ (c , end) ]) (++-identityʳ (picks f xs))

    ends-at : ∀ {B : Set} (rs : List (Pos × Ev B)) c → Ends (rs ++ [ (c , end) ])
    ends-at rs c = AnyP.++⁺ʳ rs (here refl)

  dir₃ : ∀ {rx} → Met X rx → Ends rx → Σ _ λ rs′ → Met E rs′ × Ends rs′ × vals rx ≡ values rs′
  dir₃ mx en with ended mx en
  ... | xs , c , refl , xc , lc with to (erase-end o) (c , xc , lc)
  ...   | c′ , ec′ , lc′ with RE.reach ec′ lc′ tt
  ...     | ys , me = ys ++ [ (c′ , end) ] , me , ends-at ys c′ ,
    trans (vals-picks (xs ++ [ (c , end) ]))
      (trans (cong (L.map proj₂) (end-picks valuesOf xs c))
        (trans (vmatch (proj₁ (EX.run-enum (run-prefix xs mx))) (proj₁ (EE.run-enum (run-prefix ys me))) (counts xs ys mx me))
          (sym (trans (cong (L.map proj₂) (outs-picks (ys ++ [ (c′ , end) ]))) (cong (L.map proj₂) (end-picks [_] ys c′))))))

  dir₄ : ∀ {rs′} → Met E rs′ → Ends rs′ → Σ _ λ rx → Met X rx × Ends rx × values rs′ ≡ vals rx
  dir₄ me en with ended me en
  ... | ys , c′ , refl , ec′ , lc′ with from (erase-end o) (c′ , ec′ , lc′)
  ...   | c , xc , lc with RX.reach xc lc tt
  ...     | xs , mx = xs ++ [ (c , end) ] , mx , ends-at xs c ,
    sym (trans (vals-picks (xs ++ [ (c , end) ]))
      (trans (cong (L.map proj₂) (end-picks valuesOf xs c))
        (trans (vmatch (proj₁ (EX.run-enum (run-prefix xs mx))) (proj₁ (EE.run-enum (run-prefix ys me))) (counts xs ys mx me))
          (sym (trans (cong (L.map proj₂) (outs-picks (ys ++ [ (c′ , end) ]))) (cong (L.map proj₂) (end-picks [_] ys c′)))))))

-- THE ERASURE: the elaborated run, marks dropped, is the plain run stamp
-- for stamp, value by value.
erases : ∀ {A} (o : SObs [] A) → Erases (elaborated o) (events o)
erases o = (λ {rx} {ov} → dir₁ {rx} {ov}) , (λ {rs′} {ov} → dir₂ {rs′} {ov}) , (λ {rx} → dir₃ {rx}) , (λ {rs′} → dir₄ {rs′})
  where open Erasing o
