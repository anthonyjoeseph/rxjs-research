{-# OPTIONS --guardedness #-}

-- ROWS ATTRIBUTED.  An emission set `u` carries another, `t`, when each
-- of `u`'s rows at or before its end is attributed to one of `t`'s
-- unpinned rows, or to none, ahead of every one of them: in order,
-- instant for instant, finitely many to each, and each of `t`'s unpinned
-- rows at or before its end is carried by one of `u`'s, a value by a
-- value of the same, an end by an end.  A pin is carried only into its
-- instant: by a row of `u` put on a row of that instant at or before it,
-- or put ahead of every row when the pin lies in the subscribe frame.
-- What `u` adds shows nothing, and lies in an instant `t` passes through
-- or in the subscribe frame.  Past the ends nothing is carried: a reader
-- is shown nothing there.
--
-- So `u`'s values are `t`'s, index for index, each before every end
-- exactly when its counterpart is (`values-ut`, `values-tu`); an instant
-- before a value of `u` is one before its counterpart, so the two share a
-- rank (`rank-ut`); and an instant is over on one side exactly when it is
-- on the other (`over-ut`), since what `u` adds after a value is a finite
-- tail of rows already attributed, never a value or an end of its own.
-- Whether a run has ended past a value is decided by listing its rows
-- (`simultaneous.Listing`): past it, finitely many.
module simultaneous.Attribution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool.Properties using (T?)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; Instant; root; frame; _<ᵖ_; _⊕_; ix)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_; Few; Seen; module Values)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≼-split; ≼-antisym; ≼-refl; ≼-trans; ≼-≺-≺; ≺→≼; ≺-irrefl; ≺-absurd; ≺-ext)
open import denotation.Laws.Nth using (module Nths)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; irrⁱ; triⁱ; frame-least; ≺-instant; instant-≺)
open import simultaneous.Relations using (Rank; Before; Left; Exits; Over)
open import simultaneous.Listing using (Listing)

open Values using (Nth; Next; first; next)
open Equivalence using (to; from)

------------------------------------------------------------------------
-- A stream's values, one row at a time

-- At or before every end.
Live : ∀ {X : Set} → EmissionSet X → Pos → Set
Live t k = ∀ {c} → t c end → k ≼ c

-- `f` reads one value or none off each element.
Single : ∀ {X A : Set} → (X → List A) → Set
Single {A = A} f = ∀ x → f x ≡ [] ⊎ Σ A λ a → f x ≡ a ∷ []

-- The rows carrying one value through `f`.
data V {X A : Set} (f : X → List A) (t : EmissionSet X) : EmissionSet A where
  vrow : ∀ {k x a} → t k (out x) → f x ≡ a ∷ [] → V f t k (out a)

------------------------------------------------------------------------
-- Lists built along membership

private
  module _ {X Y : Set} where
    mapWith : (xs : List X) → (∀ {x} → x ∈ xs → Y) → List Y
    mapWith []       g = []
    mapWith (x ∷ xs) g = g (here refl) ∷ mapWith xs (λ m → g (there m))

    length-mapWith : ∀ xs (g : ∀ {x} → x ∈ xs → Y) → length (mapWith xs g) ≡ length xs
    length-mapWith []       g = refl
    length-mapWith (x ∷ xs) g = cong suc (length-mapWith xs (λ m → g (there m)))

    ∈-mapWith⁺ : ∀ {x} xs (g : ∀ {x} → x ∈ xs → Y) (m : x ∈ xs) → g m ∈ mapWith xs g
    ∈-mapWith⁺ (x ∷ xs) g (here refl) = here refl
    ∈-mapWith⁺ (x ∷ xs) g (there m)   = there (∈-mapWith⁺ xs (λ m′ → g (there m′)) m)

    ∈-mapWith⁻ : ∀ {y} xs (g : ∀ {x} → x ∈ xs → Y) → y ∈ mapWith xs g → Σ X λ x → Σ (x ∈ xs) λ m → y ≡ g m
    ∈-mapWith⁻ (x ∷ xs) g (here refl) = x , here refl , refl
    ∈-mapWith⁻ (x ∷ xs) g (there n) with ∈-mapWith⁻ xs (λ m → g (there m)) n
    ... | x′ , m , eq = x′ , there m , eq

    allWith : ∀ {P : Y → Set} {Q : X → Set} xs (g : ∀ {x} → x ∈ xs → Y)
            → (∀ {x} (m : x ∈ xs) → Q x → P (g m)) → All Q xs → All P (mapWith xs g)
    allWith []       g h []       = []
    allWith (x ∷ xs) g h (q ∷ qs) = h (here refl) q ∷ allWith xs (λ m → g (there m)) (λ m → h (there m)) qs

    pairsWith : ∀ {R : X → X → Set} {S : Y → Y → Set} xs (g : ∀ {x} → x ∈ xs → Y)
              → (∀ {x y} (m : x ∈ xs) (n : y ∈ xs) → R x y → S (g m) (g n)) → AllPairs R xs → AllPairs S (mapWith xs g)
    pairsWith []       g h []       = []
    pairsWith (x ∷ xs) g h (a ∷ ps) =
      allWith xs (λ m → g (there m)) (λ m r → h (here refl) (there m) r) a ∷ pairsWith xs (λ m → g (there m)) (λ m n → h (there m) (there n)) ps

    -- Each element's list, in turn.
    every : (X → List Y) → List X → List Y
    every g []       = []
    every g (x ∷ xs) = g x ++ every g xs

    ∈-every : ∀ {x y} (g : X → List Y) xs → x ∈ xs → y ∈ g x → y ∈ every g xs
    ∈-every g (x ∷ xs) (here refl) yg = ∈-++⁺ˡ yg
    ∈-every g (x ∷ xs) (there m)   yg = ∈-++⁺ʳ (g x) (∈-every g xs m yg)

------------------------------------------------------------------------
-- Attribution

-- `nothing` lies ahead of every row; `just k` where `k` does.
data _≤ₘ_ : Maybe Pos → Maybe Pos → Set where
  none : ∀ {y} → nothing ≤ₘ y
  some : ∀ {k m} → k ≼ m → just k ≤ₘ just m

-- A row a reader is told of through `Sh`: a value it shows, or the end.
Shown : ∀ {X : Set} → (X → Set) → Ev X → Set
Shown Sh (out x) = Sh x
Shown Sh end     = ⊤
Shown Sh skip    = ⊥
Shown Sh (pin _) = ⊥

-- A shown row, carried on the other side.
Carried : ∀ {A B : Set} → (A → B → Set) → Ev A → Ev B → Set
Carried Val (out a) e′ = Σ _ λ x → e′ ≡ out x × Val a x
Carried Val end     e′ = e′ ≡ end
Carried Val skip    e′ = ⊥
Carried Val (pin _) e′ = ⊥

-- A row and its carrier: shown by one exactly as by the other.
Match : ∀ {A B : Set} → (A → Set) → (B → Set) → (A → B → Set) → Ev A → Ev B → Set
Match ShA ShB Val e e′ = (Shown ShA e → Carried Val e e′) × (¬ Shown ShA e → ¬ Shown ShB e′)

-- `u`, subscribed at `s′`, carries `t`, subscribed at `s`: `At l x` puts
-- `u`'s row at `l` on `t`'s at `k` (`x = just k`), or ahead of all of
-- them (`x = nothing`).  `pre`, `fib` and `bk` over-approximate, as
-- lists, the rows ahead, the rows put on `k`, and the row `l` is put on;
-- `pbk`, the pins `l` carries into their instant.
record Attribution {A B : Set} (ShA : A → Set) (ShB : B → Set) (Val : A → B → Set)
                   (t : EmissionSet A) (u : EmissionSet B) (s s′ : Pos) : Set₁ where
  field
    At     : Pos → Maybe Pos → Set
    att    : ∀ {l e} → u l e → Live u l → Σ (Maybe Pos) (At l)
    at-fun : ∀ {l x y} → At l x → At l y → x ≡ y
    at-row : ∀ {l k} → At l (just k) → Σ (Ev A) λ e → t k e × Unpinned e
    img    : ∀ {k e} → t k e → Unpinned e → Live t k → Σ Pos λ l → At l (just k) × Σ (Ev B) λ e′ → u l e′ × Match ShA ShB Val e e′
    shown  : ∀ {l e} → u l e → Shown ShB e → Live u l → Σ Pos λ k → At l (just k) × Σ (Ev A) λ e₀ → t k e₀ × Match ShA ShB Val e₀ e
    uniq   : ∀ {l m k e e′} → At l (just k) → At m (just k) → u l e → u m e′ → Shown ShB e → Shown ShB e′ → l ≡ m
    mono   : ∀ {l m x y} → At l x → At m y → l ≺ m → x ≤ₘ y
    inst   : ∀ {l m k n} → At l (just k) → At m (just n) → (instantOf l ≡ instantOf m ⇔ instantOf k ≡ instantOf n)
    home   : ∀ {l k} → At l (just k) → (instantOf l ≡ instantOf s′ ⇔ instantOf k ≡ instantOf s)
    early  : ∀ {l} → At l nothing → instantOf l ≡ instantOf s′
    live   : ∀ {l k} → At l (just k) → Live t k → Live u l
    pre    : List Pos
    in-pre : ∀ {l} → At l nothing → l ∈ pre
    fib    : Pos → List Pos
    in-fib : ∀ {l k} → At l (just k) → l ∈ fib k
    bk     : Pos → List Pos
    in-bk  : ∀ {l k} → At l (just k) → k ∈ bk l
    pbk    : Pos → List Pos
    pinned : ∀ {k p} → t k (pin p) → Live t k → Σ Pos λ l → Σ (Ev B) (u l) × k ∈ pbk l
             × ((At l nothing × instantOf k ≡ instantOf s) ⊎ Σ Pos λ k₀ → At l (just k₀) × instantOf k₀ ≡ instantOf k × k₀ ≼ k)

-- A plain run shows every value; an elaborated one, those `f` reads one
-- value off, and carries the value it reads.
Every : ∀ {A : Set} → A → Set
Every _ = ⊤

One : ∀ {X A : Set} → (X → List A) → X → Set
One {A = A} f x = Σ A λ a → f x ≡ a ∷ []

Reads : ∀ {X A : Set} → (X → List A) → A → X → Set
Reads f a x = f x ≡ a ∷ []

------------------------------------------------------------------------
-- Whether a run ends past a row

private
  module Past {X : Set} {t : EmissionSet X} (func : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) (listing : Listing t) where

    -- The latest of a position and a list.
    top : Pos → List Pos → Pos
    top m []       = m
    top m (k ∷ ks) with T? (m <ᵖ k)
    ... | yes _ = top k ks
    ... | no  _ = top m ks

    top-≥ : ∀ m ks {k} → k ∈ m ∷ ks → k ≼ top m ks
    top-≥ m []       (here refl) = ≼-refl {m}
    top-≥ m (k ∷ ks) mem with T? (m <ᵖ k)
    top-≥ m (k ∷ ks) (here refl)         | yes mk = ≼-trans {m} {k} {top k ks} (≺→≼ {m} {k} mk) (top-≥ k ks (here refl))
    top-≥ m (k ∷ ks) (there (here refl)) | yes _  = top-≥ k ks (here refl)
    top-≥ m (k ∷ ks) (there (there x))   | yes _  = top-≥ k ks (there x)
    top-≥ m (k ∷ ks) (here refl)         | no _   = top-≥ m ks (here refl)
    top-≥ m (k ∷ ks) (there (here refl)) | no km  = ≼-trans {k} {m} {top m ks} km (top-≥ m ks (here refl))
    top-≥ m (k ∷ ks) (there (there x))   | no _   = top-≥ m ks (there x)

    endOr : (e : Ev X) → e ≡ end ⊎ (e ≡ end → ⊥)
    endOr end     = inj₁ refl
    endOr (out _) = inj₂ λ ()
    endOr skip    = inj₂ λ ()
    endOr (pin _) = inj₂ λ ()

    -- An end among rows listed, or none.
    hunt : (ks : List Pos) → (∀ {k} → k ∈ ks → Σ _ (t k)) → (Σ Pos λ c → t c end) ⊎ (∀ {c} → c ∈ ks → t c end → ⊥)
    hunt []       b = inj₂ λ ()
    hunt (k ∷ ks) b with b (here refl)
    ... | e , tk with endOr e
    ...   | inj₁ refl = inj₁ (k , tk)
    ...   | inj₂ ne with hunt ks (λ m → b (there m))
    ...     | inj₁ c  = inj₁ c
    ...     | inj₂ absent = inj₂ λ { (here refl) tc → ne (func tk tc) ; (there m) tc → absent m tc }

    -- Past a row with finitely many rows before it, finitely many.
    bound : ∀ {l} ks → Few t l → (∀ {r e} → t r e → l ≺ r → r ∈ ks) → Few t (top l ks ⊕ [ ix 0 ])
    bound {l} ks (fs , few) after = fs ++ l ∷ ks , cover
      where
        cover : ∀ {r e} → t r e → r ≺ (top l ks ⊕ [ ix 0 ]) → r ∈ fs ++ l ∷ ks
        cover {r} tr _ with T? (r <ᵖ l)
        ... | yes rl = ∈-++⁺ˡ (few tr rl)
        ... | no lr with ≼-split {l} {r} lr
        ...   | inj₁ lr′ = ∈-++⁺ʳ fs (there (after tr lr′))
        ...   | inj₂ refl = ∈-++⁺ʳ fs (here refl)

    -- So the run ends or it does not past the row.
    ends? : ∀ {l} ks → Few t l → (∀ {r e} → t r e → l ≺ r → r ∈ ks) → (Σ Pos λ c → t c end) ⊎ (∀ {c} → t c end → l ≺ c → ⊥)
    ends? {l} ks fl after with listing (bound ks fl after)
    ... | ks′ , has , back with hunt ks′ (λ m → proj₂ (back m))
    ...   | inj₁ c  = inj₁ c
    ...   | inj₂ absent = inj₂ λ {c} tc lc →
      absent (has tc (≼-≺-≺ {c} {top l ks} {top l ks ⊕ [ ix 0 ]} (top-≥ l ks (there (after tc lc))) (≺-ext (top l ks) []))) tc

------------------------------------------------------------------------
-- What an attribution at the root carries over

-- `t` and `u` are readings: one event at a position, every value and end
-- reached and at or before every end, finitely many rows before each of
-- `t`'s unpinned ones, and the rows before any position listed where
-- finitely many precede it.
module Attributed {A X : Set} {f : X → List A} (sv : Single f) {t : EmissionSet A} {u : EmissionSet X}
                  (funcT : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) (funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′)
                  (seenT : ∀ {k e} → t k e → Visible e → Seen t k e) (seenU : ∀ {l e} → u l e → Visible e → Seen u l e)
                  (fewT : ∀ {k e} → t k e → Unpinned e → Few t k)
                  (listT : Listing t) (listU : Listing u)
                  (R : Attribution Every (One f) (Reads f) t u root root) where
  open Attribution R

  private
    module PT = Past funcT listT
    module PU = Past funcU listU

    liveT : ∀ {k e} → t k e → Visible e → Live t k
    liveT tk v = proj₂ (proj₁ (seenT tk v))

    liveU : ∀ {l e} → u l e → Visible e → Live u l
    liveU ul v = proj₂ (proj₁ (seenU ul v))

    -- Before a row at or before every end, a row is too.
    live-≺ : ∀ {Y : Set} {w : EmissionSet Y} {r m} → r ≺ m → Live w m → Live w r
    live-≺ {r = r} {m} rm lm {c} wc = ≼-trans {r} {m} {c} (≺→≼ {r} {m} rm) (lm wc)

    module NU = Nths (V f u)

    pinOr : ∀ {Y : Set} (e : Ev Y) → Unpinned e ⊎ Σ Pos λ p → e ≡ pin p
    pinOr (out _) = inj₁ tt
    pinOr skip    = inj₁ tt
    pinOr end     = inj₁ tt
    pinOr (pin p) = inj₂ (p , refl)

    unsome : ∀ {k m} → just k ≤ₘ just m → k ≼ m
    unsome (some h) = h

    -- Attribution keeps the order, and reflects it.
    mono≼ : ∀ {l m k n} → At l (just k) → At m (just n) → l ≼ m → k ≼ n
    mono≼ {l} {m} {k} al am lm with ≼-split {l} {m} lm
    ... | inj₁ lt   = unsome (mono al am lt)
    ... | inj₂ refl with at-fun al am
    ...   | refl = ≼-refl {k}

    strict : ∀ {l m k n} → At l (just k) → At m (just n) → k ≺ n → l ≺ m
    strict {l} {m} al am kn with T? (l <ᵖ m)
    ... | yes lm = lm
    ... | no ml  = ⊥-elim (mono≼ am al ml kn)

    -- Before a row put on `k₀`, the rows put ahead of every row or on
    -- one before `k₀` or on `k₀` itself.
    few-u : ∀ {m k₀} → At m (just k₀) → Live u m → Few t k₀ → Few u m
    few-u {m} {k₀} am lm (fs , few) = pre ++ every fib (k₀ ∷ fs) , cov
      where
        cov : ∀ {r e} → u r e → r ≺ m → r ∈ pre ++ every fib (k₀ ∷ fs)
        cov {r} ur rm with att ur (live-≺ {w = u} rm lm)
        ... | nothing , a₀ = ∈-++⁺ˡ (in-pre a₀)
        ... | just r₁ , ar with ≼-split {r₁} {k₀} (mono≼ ar am (≺→≼ {r} {m} rm))
        ...   | inj₁ lt   = ∈-++⁺ʳ pre (∈-every fib (k₀ ∷ fs) (there (few (proj₁ (proj₂ (at-row ar))) lt)) (in-fib ar))
        ...   | inj₂ refl = ∈-++⁺ʳ pre (∈-every fib (k₀ ∷ fs) (here refl) (in-fib ar))

    -- A row put ahead of every row lies before each one put on a row.
    none-first : ∀ {l m n} → At l nothing → At m (just n) → l ≺ m
    none-first {l} {m} al am with T? (l <ᵖ m)
    ... | yes lm = lm
    ... | no ml with ≼-split {m} {l} ml
    ...   | inj₁ ml′ with mono am al ml′
    ...     | ()
    none-first al am | no ml | inj₂ refl with at-fun al am
    ... | ()

    -- A shown row of `u` is put on a row of `t` of its kind.
    end-of : ∀ {k e₀} → t k e₀ → Match Every (One f) (Reads f) e₀ end → t k end
    end-of {e₀ = out _} tk (c , q) with c tt
    ... | _ , () , _
    end-of {e₀ = end}   tk m       = tk
    end-of {e₀ = skip}  tk (c , q) = ⊥-elim (q (λ ()) tt)
    end-of {e₀ = pin _} tk (c , q) = ⊥-elim (q (λ ()) tt)

    end-back : ∀ {l} → u l end → Σ Pos λ k → At l (just k) × t k end
    end-back ul with shown ul tt (liveU ul tt)
    ... | k , ak , e₀ , tk , m = k , ak , end-of tk m

    val-of : ∀ {k x e₀ a} → t k e₀ → Match Every (One f) (Reads f) e₀ (out x) → f x ≡ a ∷ [] → t k (out a)
    val-of {k} {e₀ = out b} tk (c , q) fx with c tt
    ... | _ , refl , fb = subst (λ z → t k (out z)) (∷-injectiveˡ (trans (sym fb) fx)) tk
    val-of {e₀ = end}   tk (c , q) fx with c tt
    ... | ()
    val-of {e₀ = skip}  tk (c , q) fx = ⊥-elim (q (λ ()) (_ , fx))
    val-of {e₀ = pin _} tk (c , q) fx = ⊥-elim (q (λ ()) (_ , fx))

    -- A carried end, and a carried value.
    end-img : ∀ {k} → t k end → Σ Pos λ l → At l (just k) × u l end
    end-img tk with img tk tt (liveT tk tt)
    ... | l , al , e′ , ul , (c , _) with c tt
    ...   | refl = l , al , ul

    vt : ∀ {k a} → V [_] t k (out a) → t k (out a)
    vt (vrow tk refl) = tk

    vback : ∀ {l a} → V f u l (out a) → Σ Pos λ k → At l (just k) × t k (out a)
    vback (vrow ul fx) with shown ul (_ , fx) (liveU ul tt)
    ... | k , ak , e₀ , tk , m = k , ak , val-of tk m fx

    vimg : ∀ {k a} → t k (out a) → Σ Pos λ l → At l (just k) × V f u l (out a)
    vimg tk with img tk tt (liveT tk tt)
    ... | l , al , e′ , ul , (c , _) with c tt
    ...   | x , refl , fx = l , al , vrow ul fx

    vuniq : ∀ {l m k a b} → At l (just k) → At m (just k) → V f u l (out a) → V f u m (out b) → l ≡ m
    vuniq al am (vrow ul fx) (vrow um fy) = uniq al am ul um (_ , fx) (_ , fy)

    -- Of two values of `u`, the earlier is put on the earlier.
    vstrict : ∀ {l m k n a b} → At l (just k) → At m (just n) → V f u l (out a) → V f u m (out b) → l ≺ m → k ≺ n
    vstrict {l} {m} {k} {n} al am vl vm lm with ≼-split {k} {n} (mono≼ al am (≺→≼ {l} {m} lm))
    ... | inj₁ kn   = kn
    ... | inj₂ refl = ⊥-elim (≺-irrefl {l} (subst (l ≺_) (sym (vuniq al am vl vm)) lm))

    vfwd : ∀ {l m k n a b} → At l (just k) → At m (just n) → V f u l (out a) → V f u m (out b) → k ≼ n → l ≼ m
    vfwd {l} {m} {k} {n} al am vl vm kn ml with ≼-antisym {n} {k} (unsome (mono am al ml)) kn
    ... | refl = ≺-irrefl {m} (subst (m ≺_) (vuniq al am vl vm) ml)

  ------------------------------------------------------------------------
  -- Values, index for index

  nth-ut : ∀ {i l a} → Nth (V f u) i l a → Σ Pos λ k → At l (just k) × Nth (V [_] t) i k a
  nth-ut (first v least) with vback v
  ... | k , ak , tk = k , ak , first (vrow tk refl) λ vm → back vm
    where
      back : ∀ {m b} → V [_] t m (out b) → k ≼ m
      back vm with vimg (vt vm)
      ... | m′ , am , vm′ = mono≼ ak am (least vm′)
  nth-ut (next n v lt nx) with nth-ut n | vback v
  ... | k , ak , nk | k′ , ak′ , tk′ = k′ , ak′ , next nk (vrow tk′ refl) (vstrict ak ak′ (NU.nth-val n) v lt) λ vm km → fwd vm km
    where
      fwd : ∀ {m b} → V [_] t m (out b) → k ≺ m → k′ ≼ m
      fwd vm km with vimg (vt vm)
      ... | m′ , am , vm′ = mono≼ ak′ am (nx vm′ (strict ak am km))

  nth-tu : ∀ {i k a} → Nth (V [_] t) i k a → Σ Pos λ l → At l (just k) × Nth (V f u) i l a
  nth-tu (first v least) with vimg (vt v)
  ... | l , al , vl = l , al , first vl λ vm → back vm
    where
      back : ∀ {m b} → V f u m (out b) → l ≼ m
      back vm with vback vm
      ... | m₁ , am , tm = vfwd al am vl vm (least (vrow tm refl))
  nth-tu (next n v lt nx) with nth-tu n | vimg (vt v)
  ... | l , al , nl | l′ , al′ , vl′ = l′ , al′ , next nl vl′ (strict al al′ lt) λ vm lm → fwd vm lm
    where
      fwd : ∀ {m b} → V f u m (out b) → l ≺ m → l′ ≼ m
      fwd vm lm with vback vm
      ... | m₁ , am , tm = vfwd al′ am vl′ vm (nx (vrow tm refl) (vstrict al am (NU.nth-val nl) vm lm))

  live-ut : ∀ {l k} → At l (just k) → Live u l → Live t k
  live-ut al lu tc with end-img tc
  ... | c , ac , uc = mono≼ al ac (lu uc)

  values-ut : ∀ {i l a} → Nth (V f u) i l a → Live u l → Σ Pos λ k → Nth (V [_] t) i k a × Live t k
  values-ut n lu with nth-ut n
  ... | k , ak , nk = k , nk , live-ut ak lu

  values-tu : ∀ {i k a} → Nth (V [_] t) i k a → Live t k → Σ Pos λ l → Nth (V f u) i l a × Live u l
  values-tu n lt with nth-tu n
  ... | l , al , nl = l , nl , live al lt

  ends : (Σ Pos λ c → u c end × Live u c) ⇔ (Σ Pos λ c′ → t c′ end × Live t c′)
  ends = mk⇔ to′ from′
    where
      to′ : (Σ Pos λ c → u c end × Live u c) → Σ Pos λ c′ → t c′ end × Live t c′
      to′ (c , uc , lc) with end-back uc
      ... | c′ , ac , tc = c′ , tc , live-ut ac lc
      from′ : (Σ Pos λ c′ → t c′ end × Live t c′) → Σ Pos λ c → u c end × Live u c
      from′ (c′ , tc , lc) with end-img tc
      ... | c , ac , uc = c , uc , live ac lc

  ------------------------------------------------------------------------
  -- Ranks

  private
    -- `u`'s instant `J` is `t`'s `I`: the subscribe frame, or the instant
    -- of a row of `u` and that of the row it is put on.
    Lands : Instant → Instant → Set
    Lands J I = (J ≡ frame × I ≡ frame)
              ⊎ Σ Pos λ m → Σ Pos λ m₁ → Σ (Ev X) λ e → u m e × At m (just m₁) × instantOf m ≡ J × instantOf m₁ ≡ I

    lands-fun : ∀ {J I I′} → Lands J I → Lands J I′ → I ≡ I′
    lands-fun (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
    lands-fun (inj₁ (refl , refl)) (inj₂ (m , m₁ , e , um , am , mJ , refl)) = sym (to (home am) mJ)
    lands-fun (inj₂ (m , m₁ , e , um , am , mJ , refl)) (inj₁ (refl , refl)) = to (home am) mJ
    lands-fun (inj₂ (m , m₁ , _ , _ , am , mJ , refl)) (inj₂ (n , n₁ , _ , _ , an , nJ , refl)) = to (inst am an) (trans mJ (sym nJ))

    above-frame : ∀ {i} → i ≢ frame → frame ≺ⁱ i
    above-frame {i} ne with triⁱ frame i
    ... | inj₁ lt          = lt
    ... | inj₂ (inj₁ eq)   = ⊥-elim (ne (sym eq))
    ... | inj₂ (inj₂ lt)   = ⊥-elim (frame-least lt)

    lands-mono : ∀ {J₁ J₂ I₁ I₂} → Lands J₁ I₁ → Lands J₂ I₂ → J₁ ≺ⁱ J₂ → I₁ ≺ⁱ I₂
    lands-mono _ (inj₁ (refl , _)) lt = ⊥-elim (frame-least lt)
    lands-mono (inj₁ (refl , refl)) (inj₂ (m , m₁ , _ , _ , am , refl , refl)) lt =
      above-frame λ e → irrⁱ (subst (frame ≺ⁱ_) (from (home am) e) lt)
    lands-mono (inj₂ (m , m₁ , _ , _ , am , refl , refl)) (inj₂ (n , n₁ , _ , _ , an , refl , refl)) lt
      with ≼-split {m₁} {n₁} (mono≼ am an (≺→≼ {m} {n} (instant-≺ m n lt)))
    ... | inj₁ lt₁  = ≺-instant m₁ n₁ lt₁ λ e → irrⁱ (subst (instantOf m ≺ⁱ_) (sym (from (inst am an) e)) lt)
    ... | inj₂ refl = ⊥-elim (irrⁱ (subst (instantOf m ≺ⁱ_) (sym (from (inst am an) refl)) lt))

    below-of : ∀ {m l m₁ k} → At m (just m₁) → At l (just k) → m ≺ l → instantOf m ≢ instantOf l → m₁ ≺ k
    below-of {m} {l} {m₁} {k} am al ml ne with ≼-split {m₁} {k} (mono≼ am al (≺→≼ {m} {l} ml))
    ... | inj₁ lt   = lt
    ... | inj₂ refl = ⊥-elim (ne (from (inst am al) refl))

    frame-before : ∀ {l k} → At l (just k) → frame ≢ instantOf l → Before t k frame
    frame-before al ne = (λ eq → ne (sym (from (home al) (sym eq)))) , inj₁ refl

    -- An instant before a row of `u`, as `t` passes it, and back.
    fwd : ∀ {l k J} → At l (just k) → Live u l → Before u l J → Σ Instant λ I → Lands J I × Before t k I
    fwd al lu (ne , inj₁ refl) = frame , inj₁ (refl , refl) , frame-before al ne
    fwd al lu (ne , inj₂ (m , e , um , ml , refl)) with att um (live-≺ {w = u} ml lu)
    ... | nothing , a₀ = frame , inj₁ (early a₀ , refl) , frame-before al λ eq → ne (trans (early a₀) eq)
    ... | just m₁ , am with at-row am
    ...   | e₁ , tm₁ , _ =
      instantOf m₁ , inj₂ (m , m₁ , e , um , am , refl , refl) ,
      ((λ eq → ne (from (inst am al) eq)) , inj₂ (m₁ , e₁ , tm₁ , below-of am al ml ne , refl))

    bwd : ∀ {l k I} → At l (just k) → Live t k → Before t k I → Σ Instant λ J → Before u l J × Lands J I
    bwd al lk (ne , inj₁ refl) = frame , ((λ eq → ne (sym (to (home al) (sym eq)))) , inj₁ refl) , inj₁ (refl , refl)
    bwd al lk (ne , inj₂ (m₁ , e₁ , tm₁ , m₁k , refl)) with pinOr e₁
    ... | inj₁ up with img tm₁ up (live-≺ {w = t} m₁k lk)
    ...   | m , am , e′ , um , _ =
      instantOf m , ((λ eq → ne (to (inst am al) eq)) , inj₂ (m , e′ , um , strict am al m₁k , refl)) ,
      inj₂ (m , m₁ , e′ , um , am , refl , refl)
    bwd {k = k} al lk (ne , inj₂ (m₁ , e₁ , tm₁ , m₁k , refl)) | inj₂ (p , eq) with pinned (subst (t m₁) eq tm₁) (live-≺ {w = t} m₁k lk)
    ... | m , (e′ , um) , _ , inj₁ (_ , ef) =
      frame , ((λ eq′ → ne (trans ef (sym (to (home al) (sym eq′))))) , inj₁ refl) , inj₁ (refl , ef)
    ... | m , (e′ , um) , _ , inj₂ (k₀ , a₀ , ek , k₀m₁) =
      instantOf m , ((λ eq′ → ne (trans (sym ek) (to (inst a₀ al) eq′))) , inj₂ (m , e′ , um , strict a₀ al (≼-≺-≺ {k₀} {m₁} {k} k₀m₁ m₁k) , refl)) ,
      inj₂ (m , k₀ , e′ , um , a₀ , refl , ek)

  -- A row of `u` is ranked as the row it is put on.
  rank-ut : ∀ {l k r} → At l (just k) → Live u l → Rank u l r → Rank t k r
  rank-ut {l} {k} al lu (is , sorted , len , iff) =
    mapWith is g , pairsWith is g (λ m n lt → lands-mono (L m) (L n) lt) sorted , trans (length-mapWith is g) len ,
    mk⇔ fwd′ bwd′
    where
      g : ∀ {J} → J ∈ is → Instant
      g m = proj₁ (fwd al lu (to iff m))

      L : ∀ {J} (m : J ∈ is) → Lands J (g m)
      L m = proj₁ (proj₂ (fwd al lu (to iff m)))

      fwd′ : ∀ {I} → I ∈ mapWith is g → Before t k I
      fwd′ mem with ∈-mapWith⁻ is g mem
      ... | J , m , refl = proj₂ (proj₂ (fwd al lu (to iff m)))

      bwd′ : ∀ {I} → Before t k I → I ∈ mapWith is g
      bwd′ b with bwd al (live-ut al lu) b
      ... | J , bJ , lJ = subst (_∈ mapWith is g) (lands-fun (L (from iff bJ)) lJ) (∈-mapWith⁺ is g (from iff bJ))

  ------------------------------------------------------------------------
  -- An instant over

  private
    left-ut : ∀ {l k} → At l (just k) → Left f u l → Left [_] t k
    left-ut al lu {m} {a} tm km same with vimg tm
    ... | m′ , am , vrow um fx with trans (sym (lu um (strict al am km) (from (inst am al) same))) fx
    ...   | ()

    left-tu : ∀ {l k x} → At l (just k) → u l (out x) → One f x → Left [_] t k → Left f u l
    left-tu al ul (_ , fl) lt {m} {x} um lm same with sv x
    ... | inj₁ f0       = f0
    ... | inj₂ (a , fx) with shown um (a , fx) (liveU um tt)
    ...   | m₁ , am , e₀ , tm₁ , mt with lt (val-of tm₁ mt fx) (vstrict al am (vrow ul fl) (vrow um fx) lm) (to (inst am al) same)
    ...     | ()

    after-of : ∀ {l m k m₁ e b} → At l (just k) → At m (just m₁) → t k (out b) → u m e → l ≺ m
             → (instantOf m ≢ instantOf l ⊎ e ≡ end) → k ≺ m₁
    after-of {l} {m} {k} {m₁} al am tk um lm cond with ≼-split {k} {m₁} (mono≼ al am (≺→≼ {l} {m} lm))
    ... | inj₁ lt = lt
    ... | inj₂ refl with cond
    ...   | inj₁ ne   = ⊥-elim (ne (from (inst am al) refl))
    ...   | inj₂ refl with end-back um
    ...     | c , ac , tc with at-fun am ac
    ...       | refl with funcT tk tc
    ...         | ()

    cond-ut : ∀ {l m k m₁ e e₁} → At l (just k) → At m (just m₁) → u m e → t m₁ e₁
            → (instantOf m ≢ instantOf l ⊎ e ≡ end) → (instantOf m₁ ≢ instantOf k ⊎ e₁ ≡ end)
    cond-ut al am um tm₁ (inj₁ ne)   = inj₁ λ eq → ne (from (inst am al) eq)
    cond-ut al am um tm₁ (inj₂ refl) with end-back um
    ... | c , ac , tc with at-fun am ac
    ...   | refl = inj₂ (funcT tm₁ tc)

    cond-tu : ∀ {l m k m₁ e₁ e′} → At l (just k) → At m (just m₁) → (Shown Every e₁ → Carried (Reads f) e₁ e′)
            → (instantOf m₁ ≢ instantOf k ⊎ e₁ ≡ end) → (instantOf m ≢ instantOf l ⊎ e′ ≡ end)
    cond-tu al am c (inj₁ ne)   = inj₁ λ eq → ne (to (inst am al) eq)
    cond-tu al am c (inj₂ refl) = inj₂ (c tt)

    -- A value of each, and an end of the other past it.
    past-u : ∀ {l x c} → u l (out x) → u c end → l ≺ c
    past-u {l} {x} {c} ul uc with ≼-split {l} {c} (liveU ul tt uc)
    ... | inj₁ lc = lc
    ... | inj₂ refl with funcU ul uc
    ...   | ()

    past-t : ∀ {k b c} → t k (out b) → t c end → k ≺ c
    past-t {k} {b} {c} tk tc with ≼-split {k} {c} (liveT tk tt tc)
    ... | inj₁ kc = kc
    ... | inj₂ refl with funcT tk tc
    ...   | ()

    -- Past a value, a pin of another instant lies in a later one.
    later : ∀ {k m₁} {e₁ : Ev A} {p} → k ≺ m₁ → e₁ ≡ pin p → (instantOf m₁ ≢ instantOf k ⊎ e₁ ≡ end) → instantOf k ≺ⁱ instantOf m₁
    later {k} {m₁} km₁ _ (inj₁ ne) = ≺-instant k m₁ km₁ (λ e → ne (sym e))
    later km₁ refl (inj₂ ())

    exits-ut : ∀ {l k x b} → At l (just k) → u l (out x) → t k (out b) → Exits u l → Exits t k
    exits-ut {l} al ul tk (inj₁ (m , e , ((um , pu) , _) , lm , cond)) with att um pu
    ... | nothing , a₀ = ⊥-elim (≺-absurd {m} {l} (none-first a₀ al) lm)
    ... | just m₁ , am with at-row am
    ...   | e₁ , tm₁ , up₁ = inj₁ (m₁ , e₁ , ((tm₁ , live-ut am pu) , fewT tm₁ up₁) , after-of al am tk um lm cond , cond-ut al am um tm₁ cond)
    exits-ut al ul tk (inj₂ (ks , sp)) with PU.ends? ks (proj₂ (seenU ul tt)) (λ ur lr → proj₁ (sp ur lr))
    ... | inj₁ (c , uc) with end-back uc
    ...   | c′ , ac , tc = inj₁ (c′ , end , seenT tc tt , after-of al ac tk uc (past-u ul uc) (inj₂ refl) , inj₂ refl)
    exits-ut {l} {k} al ul tk (inj₂ (ks , sp)) | inj₂ absent = inj₂ (every bk ks ++ every pbk (l ∷ fs ++ ks) , row)
      where
        fs : List Pos
        fs = proj₁ (proj₂ (seenU ul tt))

        unended : ∀ {c} → t c end → ⊥
        unended tc with end-img tc
        ... | c₁ , _ , uc₁ = absent uc₁ (past-u ul uc₁)

        -- Every row of `u` is before `l`, at it, or after it.
        near : ∀ {m e′} → u m e′ → m ∈ l ∷ fs ++ ks
        near {m} um with T? (m <ᵖ l)
        ... | yes ml = there (∈-++⁺ˡ (proj₂ (proj₂ (seenU ul tt)) um ml))
        ... | no lm with ≼-split {l} {m} lm
        ...   | inj₁ lm′  = there (∈-++⁺ʳ fs (proj₁ (sp um lm′)))
        ...   | inj₂ refl = here refl

        place : ∀ {r e} → t r e → k ≺ r → (Unpinned e ⊎ Σ Pos λ p → e ≡ pin p) → r ∈ every bk ks ++ every pbk (l ∷ fs ++ ks)
        place tr kr (inj₁ up) with img tr up (λ tc → ⊥-elim (unended tc))
        ... | r′ , ar , _ , ur , _ = ∈-++⁺ˡ (∈-every bk ks (proj₁ (sp ur (strict al ar kr))) (in-bk ar))
        place {r} tr kr (inj₂ (p , eq)) with pinned (subst (t r) eq tr) (λ tc → ⊥-elim (unended tc))
        ... | m , (e′ , um) , rm , _ = ∈-++⁺ʳ (every bk ks) (∈-every pbk (l ∷ fs ++ ks) (near um) rm)

        row : ∀ {r e} → t r e → k ≺ r → r ∈ every bk ks ++ every pbk (l ∷ fs ++ ks) × (t r e × (∀ {c} → t c end → r ≼ c))
        row {e = e} tr kr = place tr kr (pinOr e) , tr , (λ tc → ⊥-elim (unended tc))

    exits-tu : ∀ {l k x b} → At l (just k) → u l (out x) → t k (out b) → Exits t k → Exits u l
    exits-tu al ul tk (inj₁ (m₁ , e₁ , ((tm₁ , pt) , ft) , km₁ , cond)) with pinOr e₁
    ... | inj₁ up with img tm₁ up pt
    ...   | m , am , e′ , um , (c , _) = inj₁ (m , e′ , ((um , live am pt) , few-u am (live am pt) ft) , strict al am km₁ , cond-tu al am c cond)
    exits-tu {l} {k} al ul tk (inj₁ (m₁ , e₁ , ((tm₁ , pt) , _) , km₁ , cond)) | inj₂ (p , eq) with pinned (subst (t m₁) eq tm₁) pt
    ... | m , (e′ , um) , _ , inj₁ (_ , ef) = ⊥-elim (frame-least (subst (instantOf k ≺ⁱ_) ef (later {k} {m₁} km₁ eq cond)))
    ... | m , (e′ , um) , _ , inj₂ (k₀ , a₀ , ek , k₀m₁) with at-row a₀
    ...   | e₀ , tk₀ , up₀ =
      inj₁ (m , e′ , ((um , live a₀ lk₀) , few-u a₀ (live a₀ lk₀) (fewT tk₀ up₀)) , strict al a₀ (instant-≺ k k₀ kk₀) ,
            inj₁ λ eq′ → irrⁱ (subst (instantOf k ≺ⁱ_) (to (inst a₀ al) eq′) kk₀))
      where
        kk₀ : instantOf k ≺ⁱ instantOf k₀
        kk₀ = subst (instantOf k ≺ⁱ_) (sym ek) (later {k} {m₁} km₁ eq cond)

        lk₀ : Live t k₀
        lk₀ {c} tc = ≼-trans {k₀} {m₁} {c} k₀m₁ (pt tc)
    exits-tu al ul tk (inj₂ (ks , sp)) with PT.ends? ks (proj₂ (seenT tk tt)) (λ tr kr → proj₁ (sp tr kr))
    ... | inj₁ (c , tc) with end-img tc
    ...   | c₁ , ac , uc = inj₁ (c₁ , end , seenU uc tt , strict al ac (past-t tk tc) , inj₂ refl)
    exits-tu {l} {k} al ul tk (inj₂ (ks , sp)) | inj₂ absent = inj₂ (every fib (k ∷ ks) , row)
      where
        unended : ∀ {c} → u c end → ⊥
        unended uc with end-back uc
        ... | c′ , _ , tc = absent tc (past-t tk tc)

        row : ∀ {r e} → u r e → l ≺ r → r ∈ every fib (k ∷ ks) × (u r e × (∀ {c} → u c end → r ≼ c))
        row {r} ur lr with att ur (λ uc → ⊥-elim (unended uc))
        ... | nothing , a₀ = ⊥-elim (≺-absurd {r} {l} (none-first a₀ al) lr)
        ... | just r₁ , ar with ≼-split {k} {r₁} (mono≼ al ar (≺→≼ {l} {r} lr))
        ...   | inj₂ refl = ∈-every fib (k ∷ ks) (here refl) (in-fib ar) , ur , (λ uc → ⊥-elim (unended uc))
        ...   | inj₁ lt   = ∈-every fib (k ∷ ks) (there (proj₁ (sp (proj₁ (proj₂ (at-row ar))) lt))) (in-fib ar) , ur , (λ uc → ⊥-elim (unended uc))

  -- A value's instant is over on one side exactly when its counterpart's
  -- is on the other.
  over-ut : ∀ {l k x b} → At l (just k) → u l (out x) → One f x → t k (out b)
          → Over f u (just l) ⇔ Over [_] t (just k)
  over-ut {l} {k} {x} {b} al ul ox tk =
    mk⇔ (λ { (lu , eu) → left-ut {l} {k} al lu , exits-ut {l} {k} {x} {b} al ul tk eu })
        (λ { (lt , et) → left-tu {l} {k} {x} al ul ox lt , exits-tu {l} {k} {x} {b} al ul tk et })
