{-# OPTIONS --guardedness #-}

-- ROWS ATTRIBUTED.  An emission set `u` carries another, `t`, when each
-- of `t`'s unpinned rows a reader can reach, at or before its end, is
-- carried by one of `u`'s, in order, instant for instant, a value by a
-- value of the same, an end by an end; each of `u`'s rows that shows
-- anything carries one, and every other row of `u` a reader can reach
-- lies in the subscribe frame or in an instant some carrier lies in.
-- Past a carrier of a row past which `t` has finitely many rows, `u` has
-- finitely many too.  A pin, and any skip not carried in order, is
-- carried into its instant: listed by some row of `u`, each listing
-- finitely many, and in the subscribe frame or in a carried row's instant.
-- Past the ends nothing is carried: a reader is shown nothing there.
--
-- So `u`'s values are `t`'s, index for index, each before every end
-- exactly when its counterpart is (`values-ut`, `values-tu`); an instant
-- before a value of `u` is one before its counterpart, so the two share a
-- rank (`rank-ut`); and an instant is over on one side exactly when it is
-- on the other (`over-ut`), since what `u` adds after a value is a finite
-- tail of rows in instants already carried, never a value or an end of
-- its own.
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
open import Data.Maybe using (just)
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
open import denotation.Laws.Modulus using (≼-split; ≼-refl; ≼-trans; ≼-≺-≺; ≺→≼; ≺-irrefl; ≺-absurd; ≺-ext; ≺-trans)
open import denotation.Laws.Nth using (module Nths)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; irrⁱ; triⁱ; frame-least; ≺-instant; instant-≺)
open import simultaneous.Relations using (Rank; Before; Left; Exits; Over; Spent)
open import simultaneous.Listing using (Listing)
open import denotation.Laws.Worlds using (Shows)
open import denotation.Position using (_≟ᵖ_)
open import Data.List.Relation.Unary.Any using (any?)
open import Relation.Nullary.Decidable using (decidable-stable)

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

-- CARRIED INTO ITS INSTANT, along `Img`: listed by some row of `u`, and in
-- the subscribe frame or in the instant of a carried row.
Into : ∀ {B : Set} → (Pos → Pos → Set) → EmissionSet B → (Pos → Pos → Set) → Pos → Pos → Set
Into {B} Img u PB s k =
  (Σ Pos λ l → Σ (Ev B) (u l) × PB k l)
  × (instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × Σ (Ev B) (u l₀) × Few u l₀ × instantOf k₀ ≡ instantOf k)

-- `u`, subscribed at `s′`, carries `t`, subscribed at `s`: `Img k l`
-- puts `t`'s unpinned row at `k` on `u`'s at `l`.  Only rows with
-- finitely many rows before them are carried or placed: a reader reaches
-- no other.  A row of `u` that shows anything carries one; any other lies
-- in the subscribe frame or in the instant of one that carries.  Past a
-- row carrying a `k` past which `t` has finitely many rows and no end,
-- `u` has finitely many: what a run left without exiting asks.  `bk`
-- over-approximates, as a list, the rows `l` carries; `PB`, finitely
-- many per row, those it carries into their instant: the pins, and the
-- skips a reader hears from them.
record Attribution {A B : Set} (ShA : A → Set) (ShB : B → Set) (Val : A → B → Set)
                   (t : EmissionSet A) (u : EmissionSet B) (s s′ : Pos) : Set₁ where
  field
    Img      : Pos → Pos → Set
    PB       : Pos → Pos → Set
    pb-few   : ∀ {l e} → u l e → Σ (List Pos) λ ks → ∀ {k} → PB k l → k ∈ ks
    img      : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
             → (Σ Pos λ l → Img k l × Σ (Ev B) λ e′ → u l e′ × Few u l × Match ShA ShB Val e e′) ⊎ (e ≡ skip × Into Img u PB s k)
    shown    : ∀ {l e} → u l e → Shown ShB e → Live u l → Few u l → Σ Pos λ k → Img k l × Σ (Ev A) λ e₀ → t k e₀ × Match ShA ShB Val e₀ e
    img-row  : ∀ {k l} → Img k l → Σ (Ev A) λ e → t k e × Unpinned e
    img-fun  : ∀ {k l l′} → Img k l → Img k l′ → l ≡ l′
    img-mono : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → l ≺ l′
    inst     : ∀ {k k′ l l′} → Img k l → Img k′ l′ → (instantOf l ≡ instantOf l′ ⇔ instantOf k ≡ instantOf k′)
    home     : ∀ {k l} → Img k l → (instantOf l ≡ instantOf s′ ⇔ instantOf k ≡ instantOf s)
    place    : ∀ {m e} → u m e → Live u m → Few u m → instantOf m ≡ instantOf s′ ⊎ Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m
    live     : ∀ {k l} → Img k l → Live t k → Live u l
    spent    : ∀ {k l} → Img k l → Spent t (just k) → (∀ {c} → t c end → ⊥) → Σ (List Pos) λ ls → ∀ {r e} → u r e → l ≺ r → r ∈ ls
    bk       : Pos → List Pos
    in-bk    : ∀ {k l} → Img k l → k ∈ bk l
    pinned   : ∀ {k p} → t k (pin p) → Live t k → Few t k → Into Img u PB s k

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
-- `t`'s unpinned ones, each of those at or before every end, and the
-- rows before any position listed where finitely many precede it.
module Attributed {A X : Set} {f : X → List A} (sv : Single f) {t : EmissionSet A} {u : EmissionSet X}
                  (funcT : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) (funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′)
                  (seenT : ∀ {k e} → t k e → Visible e → Seen t k e) (seenU : ∀ {l e} → u l e → Visible e → Seen u l e)
                  (fewT : ∀ {k e} → t k e → Unpinned e → Few t k) (liveT′ : ∀ {k e} → t k e → Unpinned e → Live t k)
                  (listT : Listing t) (listU : Listing u) (showsT : Shows t)
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

    -- Before a row with finitely many before it, finitely many.
    few-≺ : ∀ {Y : Set} {w : EmissionSet Y} {r m} → Few w m → r ≺ m → Few w r
    few-≺ {r = r} {m} (ks , h) rm = ks , λ {k} x lt → h x (≺-trans {k} {r} {m} lt rm)

    module NU = Nths (V f u)

    -- A row is carried in order, or into its instant.
    carried? : ∀ {k e} → t k e → Live t k → Few t k
             → (Σ Pos λ l → Img k l × Σ (Ev X) λ e′ → u l e′ × Few u l × Match Every (One f) (Reads f) e e′)
               ⊎ ((e ≡ end → ⊥) × Into Img u PB root k)
    carried? {e = out _} tk lk fk with img tk tt lk fk
    ... | inj₁ c        = inj₁ c
    ... | inj₂ (() , _)
    carried? {e = end}   tk lk fk with img tk tt lk fk
    ... | inj₁ c        = inj₁ c
    ... | inj₂ (() , _)
    carried? {e = skip}  tk lk fk with img tk tt lk fk
    ... | inj₁ c        = inj₁ c
    ... | inj₂ (_ , h)  = inj₂ ((λ ()) , h)
    carried? {e = pin _} tk lk fk = inj₂ ((λ ()) , pinned tk lk fk)

    -- Carrying keeps the order, and reflects it.
    reflect : ∀ {k k′ l l′} → Img k l → Img k′ l′ → l ≺ l′ → k ≺ k′
    reflect {k} {k′} {l} {l′} a b ll with T? (k <ᵖ k′)
    ... | yes lt = lt
    ... | no nlt with ≼-split {k′} {k} nlt
    ...   | inj₁ lt   = ⊥-elim (≺-absurd {l} {l′} ll (img-mono b a lt))
    ...   | inj₂ refl with img-fun a b
    ...     | refl = ⊥-elim (≺-irrefl {l} ll)

    reflect≼ : ∀ {k k′ l l′} → Img k l → Img k′ l′ → l ≼ l′ → k ≼ k′
    reflect≼ a b ll k′k = ll (img-mono b a k′k)

    -- A shown row of `u` is carrying a row of `t` of its kind.
    end-of : ∀ {k e₀} → t k e₀ → Match Every (One f) (Reads f) e₀ end → t k end
    end-of {e₀ = out _} tk (c , q) with c tt
    ... | _ , () , _
    end-of {e₀ = end}   tk m       = tk
    end-of {e₀ = skip}  tk (c , q) = ⊥-elim (q (λ ()) tt)
    end-of {e₀ = pin _} tk (c , q) = ⊥-elim (q (λ ()) tt)

    end-back : ∀ {l} → u l end → Σ Pos λ k → Img k l × t k end
    end-back ul with shown ul tt (liveU ul tt) (proj₂ (seenU ul tt))
    ... | k , ik , e₀ , tk , m = k , ik , end-of tk m

    val-of : ∀ {k x e₀ a} → t k e₀ → Match Every (One f) (Reads f) e₀ (out x) → f x ≡ a ∷ [] → t k (out a)
    val-of {k} {e₀ = out b} tk (c , q) fx with c tt
    ... | _ , refl , fb = subst (λ z → t k (out z)) (∷-injectiveˡ (trans (sym fb) fx)) tk
    val-of {e₀ = end}   tk (c , q) fx with c tt
    ... | ()
    val-of {e₀ = skip}  tk (c , q) fx = ⊥-elim (q (λ ()) (_ , fx))
    val-of {e₀ = pin _} tk (c , q) fx = ⊥-elim (q (λ ()) (_ , fx))

    -- A carried end, and a carried value.
    end-img : ∀ {k} → t k end → Σ Pos λ l → Img k l × u l end
    end-img tk with img tk tt (liveT tk tt) (proj₂ (seenT tk tt))
    ... | inj₂ (() , _)
    ... | inj₁ (l , ik , e′ , ul , _ , (c , _)) with c tt
    ...   | refl = l , ik , ul

    vt : ∀ {k a} → V [_] t k (out a) → t k (out a)
    vt (vrow tk refl) = tk

    vback : ∀ {l a} → V f u l (out a) → Σ Pos λ k → Img k l × t k (out a)
    vback (vrow ul fx) with shown ul (_ , fx) (liveU ul tt) (proj₂ (seenU ul tt))
    ... | k , ik , e₀ , tk , m = k , ik , val-of tk m fx

    vimg : ∀ {k a} → t k (out a) → Σ Pos λ l → Img k l × V f u l (out a)
    vimg tk with img tk tt (liveT tk tt) (proj₂ (seenT tk tt))
    ... | inj₂ (() , _)
    ... | inj₁ (l , ik , e′ , ul , _ , (c , _)) with c tt
    ...   | x , refl , fx = l , ik , vrow ul fx

    vfwd : ∀ {k n l m} → Img k l → Img n m → k ≼ n → l ≼ m
    vfwd al am kn ml = kn (reflect am al ml)

  ------------------------------------------------------------------------
  -- Values, index for index

  nth-ut : ∀ {i l a} → Nth (V f u) i l a → Σ Pos λ k → Img k l × Nth (V [_] t) i k a
  nth-ut (first v least) with vback v
  ... | k , ak , tk = k , ak , first (vrow tk refl) λ vm → back vm
    where
      back : ∀ {m b} → V [_] t m (out b) → k ≼ m
      back vm with vimg (vt vm)
      ... | m′ , am , vm′ = reflect≼ ak am (least vm′)
  nth-ut (next n v lt nx) with nth-ut n | vback v
  ... | k , ak , nk | k′ , ak′ , tk′ = k′ , ak′ , next nk (vrow tk′ refl) (reflect ak ak′ lt) λ vm km → fwd vm km
    where
      fwd : ∀ {m b} → V [_] t m (out b) → k ≺ m → k′ ≼ m
      fwd vm km with vimg (vt vm)
      ... | m′ , am , vm′ = reflect≼ ak′ am (nx vm′ (img-mono ak am km))

  nth-tu : ∀ {i k a} → Nth (V [_] t) i k a → Σ Pos λ l → Img k l × Nth (V f u) i l a
  nth-tu (first v least) with vimg (vt v)
  ... | l , al , vl = l , al , first vl λ vm → back vm
    where
      back : ∀ {m b} → V f u m (out b) → l ≼ m
      back vm with vback vm
      ... | m₁ , am , tm = vfwd al am (least (vrow tm refl))
  nth-tu (next n v lt nx) with nth-tu n | vimg (vt v)
  ... | l , al , nl | l′ , al′ , vl′ = l′ , al′ , next nl vl′ (img-mono al al′ lt) λ vm lm → fwd vm lm
    where
      fwd : ∀ {m b} → V f u m (out b) → l ≺ m → l′ ≼ m
      fwd vm lm with vback vm
      ... | m₁ , am , tm = vfwd al′ am (nx (vrow tm refl) (reflect al am lm))

  live-ut : ∀ {k l} → Img k l → Live u l → Live t k
  live-ut al lu tc with end-img tc
  ... | c , ac , uc = reflect≼ al ac (lu uc)

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
    -- of a carrying row and that of the row it carries.
    Lands : Instant → Instant → Set
    Lands J I = (J ≡ frame × I ≡ frame)
              ⊎ Σ Pos λ m → Σ Pos λ m₁ → Img m₁ m × instantOf m ≡ J × instantOf m₁ ≡ I

    lands-fun : ∀ {J I I′} → Lands J I → Lands J I′ → I ≡ I′
    lands-fun (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
    lands-fun (inj₁ (refl , refl)) (inj₂ (m , m₁ , am , mJ , refl)) = sym (to (home am) mJ)
    lands-fun (inj₂ (m , m₁ , am , mJ , refl)) (inj₁ (refl , refl)) = to (home am) mJ
    lands-fun (inj₂ (m , m₁ , am , mJ , refl)) (inj₂ (n , n₁ , an , nJ , refl)) = to (inst am an) (trans mJ (sym nJ))

    above-frame : ∀ {i} → i ≢ frame → frame ≺ⁱ i
    above-frame {i} ne with triⁱ frame i
    ... | inj₁ lt          = lt
    ... | inj₂ (inj₁ eq)   = ⊥-elim (ne (sym eq))
    ... | inj₂ (inj₂ lt)   = ⊥-elim (frame-least lt)

    lands-mono : ∀ {J₁ J₂ I₁ I₂} → Lands J₁ I₁ → Lands J₂ I₂ → J₁ ≺ⁱ J₂ → I₁ ≺ⁱ I₂
    lands-mono _ (inj₁ (refl , _)) lt = ⊥-elim (frame-least lt)
    lands-mono (inj₁ (refl , refl)) (inj₂ (m , m₁ , am , refl , refl)) lt =
      above-frame λ e → irrⁱ (subst (frame ≺ⁱ_) (from (home am) e) lt)
    lands-mono (inj₂ (m , m₁ , am , refl , refl)) (inj₂ (n , n₁ , an , refl , refl)) lt =
      ≺-instant m₁ n₁ (reflect am an (instant-≺ m n lt)) λ e → irrⁱ (subst (instantOf m ≺ⁱ_) (sym (from (inst am an) e)) lt)

    frame-before : ∀ {k l} → Img k l → frame ≢ instantOf l → Before t k frame
    frame-before al ne = (λ eq → ne (sym (from (home al) (sym eq)))) , inj₁ refl

    -- A row of an instant before a row's lies before it.
    earlier : ∀ {k k₀ m₁} → m₁ ≺ k → instantOf m₁ ≢ instantOf k → instantOf k₀ ≡ instantOf m₁ → k₀ ≺ k
    earlier {k} {k₀} {m₁} m₁k ne ek = instant-≺ k₀ k (subst (_≺ⁱ instantOf k) (sym ek) (≺-instant m₁ k m₁k ne))

    -- An instant before a row of `u`, as `t` passes it, and back.
    fwd : ∀ {k l J} → Img k l → Live u l → Few u l → Before u l J → Σ Instant λ I → Lands J I × Before t k I
    fwd al lu fu (ne , inj₁ refl) = frame , inj₁ (refl , refl) , frame-before al ne
    fwd {k} {l} al lu fu (ne , inj₂ (m , e , um , ml , refl)) with place um (live-≺ {w = u} ml lu) (few-≺ {w = u} fu ml)
    ... | inj₁ ef = frame , inj₁ (ef , refl) , frame-before al λ eq → ne (trans ef eq)
    ... | inj₂ (m₁ , l₀ , il₀ , el₀) =
      instantOf m₁ , inj₂ (l₀ , m₁ , il₀ , el₀ , refl) ,
      ((λ eq → ne (trans (sym el₀) (from (inst il₀ al) eq))) ,
       inj₂ (m₁ , proj₁ (img-row il₀) , proj₁ (proj₂ (img-row il₀)) , reflect il₀ al l₀l , refl))
      where
        l₀l : l₀ ≺ l
        l₀l = instant-≺ l₀ l (subst (_≺ⁱ instantOf l) (sym el₀) (≺-instant m l ml ne))

    bwd : ∀ {k l I} → Img k l → Live t k → Few t k → Before t k I → Σ Instant λ J → Before u l J × Lands J I
    bwd al lk fk (ne , inj₁ refl) = frame , ((λ eq → ne (sym (to (home al) (sym eq)))) , inj₁ refl) , inj₁ (refl , refl)
    bwd {k} al lk fk (ne , inj₂ (m₁ , e₁ , tm₁ , m₁k , refl)) with carried? tm₁ (live-≺ {w = t} m₁k lk) (few-≺ {w = t} fk m₁k)
    ... | inj₁ (m , am , e′ , um , _ , _) =
      instantOf m , ((λ eq → ne (to (inst am al) eq)) , inj₂ (m , e′ , um , img-mono am al m₁k , refl)) ,
      inj₂ (m , m₁ , am , refl , refl)
    ... | inj₂ (_ , _ , inj₁ ef) =
      frame , ((λ eq′ → ne (trans ef (sym (to (home al) (sym eq′))))) , inj₁ refl) , inj₁ (refl , ef)
    ... | inj₂ (_ , _ , inj₂ (k₀ , m , a₀ , (e′ , um) , _ , ek)) =
      instantOf m , ((λ eq′ → ne (trans (sym ek) (to (inst a₀ al) eq′))) ,
                     inj₂ (m , e′ , um , img-mono a₀ al (earlier {k} {k₀} {m₁} m₁k ne ek) , refl)) ,
      inj₂ (m , k₀ , a₀ , refl , ek)

  -- A row of `u` is ranked as the row it carries.
  rank-ut : ∀ {k l r} → Img k l → Live u l → Few u l → Rank u l r → Rank t k r
  rank-ut {k} {l} al lu fu (is , sorted , len , iff) =
    mapWith is g , pairsWith is g (λ m n lt → lands-mono (L m) (L n) lt) sorted , trans (length-mapWith is g) len ,
    mk⇔ fwd′ bwd′
    where
      g : ∀ {J} → J ∈ is → Instant
      g m = proj₁ (fwd al lu fu (to iff m))

      L : ∀ {J} (m : J ∈ is) → Lands J (g m)
      L m = proj₁ (proj₂ (fwd al lu fu (to iff m)))

      fwd′ : ∀ {I} → I ∈ mapWith is g → Before t k I
      fwd′ mem with ∈-mapWith⁻ is g mem
      ... | J , m , refl = proj₂ (proj₂ (fwd al lu fu (to iff m)))

      bwd′ : ∀ {I} → Before t k I → I ∈ mapWith is g
      bwd′ b with bwd al (live-ut al lu) (fewT (proj₁ (proj₂ (img-row al))) (proj₂ (proj₂ (img-row al)))) b
      ... | J , bJ , lJ = subst (_∈ mapWith is g) (lands-fun (L (from iff bJ)) lJ) (∈-mapWith⁺ is g (from iff bJ))

  -- A value of `u` is ranked as the row it carries.
  rank-v : ∀ {i l a k r} → Nth (V f u) i l a → Img k l → Rank u l r → Rank t k r
  rank-v n al with NU.nth-val n
  ... | vrow ul _ = rank-ut al (liveU ul tt) (proj₂ (seenU ul tt))

  ------------------------------------------------------------------------
  -- An instant over

  private
    left-ut : ∀ {k l} → Img k l → Left f u l → Left [_] t k
    left-ut al lu {m} {a} tm km same with vimg tm
    ... | m′ , am , vrow um fx with trans (sym (lu um (img-mono al am km) (from (inst am al) same))) fx
    ...   | ()

    left-tu : ∀ {k l x} → Img k l → u l (out x) → One f x → Left [_] t k → Left f u l
    left-tu al ul (_ , fl) lt {m} {x} um lm same with sv x
    ... | inj₁ f0       = f0
    ... | inj₂ (a , fx) with shown um (a , fx) (liveU um tt) (proj₂ (seenU um tt))
    ...   | m₁ , am , e₀ , tm₁ , mt with lt (val-of tm₁ mt fx) (reflect al am lm) (to (inst am al) same)
    ...     | ()

    cond-tu : ∀ {k l m₁ m e₁ e′} → Img k l → Img m₁ m → (Shown Every e₁ → Carried (Reads f) e₁ e′)
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

    -- Past a value, a row other than an end of another instant lies in a
    -- later one.
    later : ∀ {k m₁} {e₁ : Ev A} → k ≺ m₁ → (e₁ ≡ end → ⊥) → (instantOf m₁ ≢ instantOf k ⊎ e₁ ≡ end) → instantOf k ≺ⁱ instantOf m₁
    later {k} {m₁} km₁ _  (inj₁ ne) = ≺-instant k m₁ km₁ (λ e → ne (sym e))
    later          km₁ ne (inj₂ e)  = ⊥-elim (ne e)

    exits-ut : ∀ {k l x b} → Img k l → u l (out x) → t k (out b) → Exits u l → Exits t k
    exits-ut al ul tk (inj₁ (m , e , ((um , _) , _) , lm , inj₂ refl)) with end-back um
    ... | c′ , _ , tc = inj₁ (c′ , end , seenT tc tt , past-t tk tc , inj₂ refl)
    exits-ut {k} {l} al ul tk (inj₁ (m , e , ((um , pu) , fu) , lm , inj₁ ne)) with place um pu fu
    ... | inj₁ ef = ⊥-elim (frame-least (subst (instantOf l ≺ⁱ_) ef (≺-instant l m lm (λ eq → ne (sym eq)))))
    ... | inj₂ (k₁ , l₁ , a₁ , el₁) with img-row a₁
    ...   | e₁ , tk₁ , up₁ = inj₁ (k₁ , e₁ , ((tk₁ , liveT′ tk₁ up₁) , fewT tk₁ up₁) , reflect al a₁ (instant-≺ l l₁ lJ) , inj₁ ne₁)
      where
        lJ : instantOf l ≺ⁱ instantOf l₁
        lJ = subst (instantOf l ≺ⁱ_) (sym el₁) (≺-instant l m lm (λ eq → ne (sym eq)))

        ne₁ : instantOf k₁ ≢ instantOf k
        ne₁ eq = irrⁱ (subst (instantOf l ≺ⁱ_) (sym (from (inst al a₁) (sym eq))) lJ)
    exits-ut al ul tk (inj₂ (ks , sp)) with PU.ends? ks (proj₂ (seenU ul tt)) (λ ur lr → proj₁ (sp ur lr))
    ... | inj₁ (c , uc) with end-back uc
    ...   | c′ , _ , tc = inj₁ (c′ , end , seenT tc tt , past-t tk tc , inj₂ refl)
    exits-ut {k} {l} al ul tk (inj₂ (ks , sp)) | inj₂ absent = inj₂ (every bk ks ++ pbs , row)
      where
        unended : ∀ {c} → t c end → ⊥
        unended tc with end-img tc
        ... | c₁ , _ , uc₁ = absent uc₁ (past-u ul uc₁)

        after : ∀ {r e} → u r e → l ≺ r → r ∈ ks
        after ur lr = proj₁ (sp ur lr)

        -- Every row of `u`, listed: none lies past `ks`.
        q : Pos
        q = PU.top l ks ⊕ [ ix 0 ]

        lq : l ≺ q
        lq = ≼-≺-≺ {l} {PU.top l ks} {q} (PU.top-≥ l ks (here refl)) (≺-ext (PU.top l ks) [])

        within : ∀ {m e} → u m e → m ≺ q
        within {m} um with T? (m <ᵖ l)
        ... | yes ml = ≺-trans {m} {l} {q} ml lq
        ... | no lm with ≼-split {l} {m} lm
        ...   | inj₁ lm′  = ≼-≺-≺ {m} {PU.top l ks} {q} (PU.top-≥ l ks (there (after um lm′))) (≺-ext (PU.top l ks) [])
        ...   | inj₂ refl = lq

        W = listU (PU.bound ks (proj₂ (seenU ul tt)) after)

        -- What each row carries into its instant.
        pb : ∀ {m} → m ∈ proj₁ W → List Pos
        pb m = proj₁ (pb-few (proj₂ (proj₂ (proj₂ (proj₂ W) m))))

        pbs : List Pos
        pbs = every (λ z → z) (mapWith (proj₁ W) pb)

        put-few : ∀ {r e} → t r e → k ≺ r → Few t r → r ∈ every bk ks ++ pbs
        put-few tr kr fr with carried? tr (λ tc → ⊥-elim (unended tc)) fr
        ... | inj₁ (r′ , ar , _ , ur , _ , _) = ∈-++⁺ˡ (∈-every bk ks (proj₁ (sp ur (img-mono al ar kr))) (in-bk ar))
        ... | inj₂ (_ , (m , (e′ , um) , rm) , _) =
          let mw = proj₁ (proj₂ W) um (within um) in
          ∈-++⁺ʳ (every bk ks) (∈-every (λ z → z) (mapWith (proj₁ W) pb) (∈-mapWith⁺ (proj₁ W) pb mw)
                                  (proj₂ (pb-few (proj₂ (proj₂ (proj₂ (proj₂ W) mw)))) rm))

        -- Every row past `k`: those with few rows before them are listed,
        -- so a hang shows, and each has few before it.
        put : ∀ {r e} → t r e → k ≺ r → r ∈ every bk ks ++ pbs
        put {r} tr kr = decidable-stable (any? (r ≟ᵖ_) (every bk ks ++ pbs)) λ n → showsT cover λ fr → n (put-few tr kr fr)
          where
            fk : Few t k
            fk = fewT tk tt

            cover : Σ (List Pos) λ js → ∀ {k′ e′} → t k′ e′ → Few t k′ → k′ ≺ r → k′ ∈ js
            cover = proj₁ fk ++ k ∷ every bk ks ++ pbs , pick
              where
                pick : ∀ {k′ e′} → t k′ e′ → Few t k′ → k′ ≺ r → k′ ∈ proj₁ fk ++ k ∷ every bk ks ++ pbs
                pick {k′} tk′ fk′ _ with T? (k′ <ᵖ k)
                ... | yes kk = ∈-++⁺ˡ (proj₂ fk tk′ kk)
                ... | no nkk with ≼-split {k} {k′} nkk
                ...   | inj₁ kk′  = ∈-++⁺ʳ (proj₁ fk) (there (put-few tk′ kk′ fk′))
                ...   | inj₂ refl = ∈-++⁺ʳ (proj₁ fk) (here refl)

        row : ∀ {r e} → t r e → k ≺ r → r ∈ every bk ks ++ pbs × (t r e × (∀ {c} → t c end → r ≼ c))
        row tr kr = put tr kr , tr , (λ tc → ⊥-elim (unended tc))

    exits-tu : ∀ {k l x b} → Img k l → u l (out x) → t k (out b) → Exits t k → Exits u l
    exits-tu {k} al ul tk (inj₁ (m₁ , e₁ , ((tm₁ , pt) , ft) , km₁ , cond)) with carried? tm₁ pt ft
    ... | inj₁ (m , am , e′ , um , fm , (c , _)) = inj₁ (m , e′ , ((um , live am pt) , fm) , img-mono al am km₁ , cond-tu al am c cond)
    ... | inj₂ (ne , _ , inj₁ ef) = ⊥-elim (frame-least (subst (instantOf k ≺ⁱ_) ef (later {k} {m₁} km₁ ne cond)))
    ... | inj₂ (ne , _ , inj₂ (k₀ , m , a₀ , (e′ , um) , fm , ek)) with img-row a₀
    ...   | _ , tk₀ , up₀ =
      inj₁ (m , e′ , ((um , live a₀ (liveT′ tk₀ up₀)) , fm) , img-mono al a₀ (instant-≺ k k₀ kk₀) ,
            inj₁ λ eq′ → irrⁱ (subst (instantOf k ≺ⁱ_) (to (inst a₀ al) eq′) kk₀))
      where
        kk₀ : instantOf k ≺ⁱ instantOf k₀
        kk₀ = subst (instantOf k ≺ⁱ_) (sym ek) (later {k} {m₁} km₁ ne cond)
    exits-tu al ul tk (inj₂ (ks , sp)) with PT.ends? ks (proj₂ (seenT tk tt)) (λ tr kr → proj₁ (sp tr kr))
    ... | inj₁ (c , tc) with end-img tc
    ...   | c₁ , ac , uc = inj₁ (c₁ , end , seenU uc tt , img-mono al ac (past-t tk tc) , inj₂ refl)
    exits-tu {k} {l} al ul tk (inj₂ (ks , sp)) | inj₂ absent = inj₂ (proj₁ (spent al (ks , sp) endless) , row)
      where
        endless : ∀ {c} → t c end → ⊥
        endless tc = absent tc (past-t tk tc)

        unended : ∀ {c} → u c end → ⊥
        unended uc with end-back uc
        ... | c′ , _ , tc = endless tc

        row : ∀ {r e} → u r e → l ≺ r → r ∈ proj₁ (spent al (ks , sp) endless) × (u r e × (∀ {c} → u c end → r ≼ c))
        row ur lr = proj₂ (spent al (ks , sp) endless) ur lr , ur , (λ uc → ⊥-elim (unended uc))

  -- A value's instant is over on one side exactly when its counterpart's
  -- is on the other.
  over-ut : ∀ {k l x b} → Img k l → u l (out x) → One f x → t k (out b)
          → Over f u (just l) ⇔ Over [_] t (just k)
  over-ut {k} {l} {x} {b} al ul ox tk =
    mk⇔ (λ { (lu , eu) → left-ut {k} {l} al lu , exits-ut {k} {l} {x} {b} al ul tk eu })
        (λ { (lt , et) → left-tu {k} {l} {x} al ul ox lt , exits-tu {k} {l} {x} {b} al ul tk et })
