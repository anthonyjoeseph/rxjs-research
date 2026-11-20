{-# OPTIONS --guardedness #-}

-- THE PLAIN PROGRAM'S BOUNDARIES AND THE ELABORATION'S, AT ONE CUT.  Two
-- boundaries correspond when the same plain rows lie before each: before
-- the plain one exactly when their images lie before the elaborated one
-- (`Btw`).  The rows are a term's own and its environment's, each read
-- through one map, so a body sees its connect's source as rows too.
-- Every boundary has a partner on the other side (`Inter.BCorr`), and a
-- held one has a held partner, waiting on a connect with the same rows
-- before it (`Inter.TagTo`, `Inter.TagFrom`); the elaborated side may
-- hold free what the plain side holds, never the reverse.  Then a plain
-- row and its image are clear together (`Inter.clear→`, `Inter.clear←`),
-- so settled together (`Root`).
--
-- A FORMER KEEPS THE CORRESPONDENCE: a take keeps a boundary where its
-- partner's take does, since a failing value lies before the one exactly
-- when its image lies before the other (`TakePair`).  A layer that wraps
-- the elaborated side alone keeps every boundary in place, and its rows
-- keep their order against them (`Wrap`), as a hot row read past a
-- subscription does (`ReaderMove`).  Two spins cut alike correspond, the
-- environment cut alike at their positions (`SpinPair`).  The connect is
-- in `simultaneous.HorizonConn`.
--
-- A RELOCATED SUBTERM NEEDS NO MORE: a correspondence is stated at a pair
-- of subscriptions, so a source the elaboration subscribes inside a lane
-- is the same pair entered there, its boundaries already in the lane.
module simultaneous.HorizonCorr where

open import Data.Bool using (Bool; T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-part)
open import denotation.EmissionSet using (Ev; out; Unpinned; EmissionSet; _≺_; module TakeWhile)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-irrefl; ≺→≼; ≼-or-≻)
open import denotation.Laws.Worlds using (_⊑_; ⊕-assoc; ⊕-identityʳ; ⊑-snoc⁺; ⊑-inside; inside-⊑)
open import denotation.Laws.Cut using (ix-asc)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.TableKit using (TR)
open import simultaneous.SpinKit using (S; sp→)
open import simultaneous.TakeKit using (Run; module Take)
open import simultaneous.Horizon using (Tag; free; held; module Cuts; module Settle; module SpinB; past-child; sub-between)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- Order against a pair of positions

-- The rows `R` lie before `z` exactly when their images lie before `z*`.
Btw : (Pos → Set) → (Pos → Pos) → Pos → Pos → Set
Btw R φ z z* = ∀ {k} → R k → (k ≺ z → φ k ≺ z*) × (φ k ≺ z* → k ≺ z)

-- A late row before `z` has its placement before `z*`.
PB : (Pos → Pos → Set) → Pos → Pos → Set
PB P z z* = ∀ {k l} → P k l → k ≺ z → l ≺ z*

-- A term's own rows: unpinned and not late.
Own : ∀ {A} → EmissionSet A → (Pos → Set) → Pos → Set
Own {A} L Late k = Σ (Ev A) λ e → L k e × Unpinned e × ¬ Late k

OwnPut : ∀ {A} → EmissionSet A → (Pos → Pos → Set) → Pos → Pos → Set
OwnPut {A} L Put k l = Σ (Ev A) (L k) × Put k l

infixr 4 _∪_ _∪²_
_∪_ : (Pos → Set) → (Pos → Set) → Pos → Set
(R ∪ R′) k = R k ⊎ R′ k

_∪²_ : (Pos → Pos → Set) → (Pos → Pos → Set) → Pos → Pos → Set
(P ∪² P′) k l = P k l ⊎ P′ k l

pb-∪ : ∀ {P P′ z z*} → PB P z z* → PB P′ z z* → PB (P ∪² P′) z z*
pb-∪ b b′ (inj₁ x) = b x
pb-∪ b b′ (inj₂ x) = b′ x

-- Past a position: past its first child, unless over that.
ix0-first : ∀ {j z} → j ≺ z → ¬ (j ⊕ [ ix 0 ]) ⊑ z → (j ⊕ [ ix 0 ]) ≺ z
ix0-first {j} {z} lt nj with T? (inside j z)
... | no ni = past-child {j} {z} (ix 0) lt (λ h → ni (⊑-inside h))
... | yes ins with inside-⊑ j z ins
...   | [] , refl                  = ⊥-elim (≺-irrefl {j} (subst (j ≺_) (⊕-identityʳ j) lt))
...   | (ix zero ∷ ys) , refl      = ⊥-elim (nj (ys , sym (⊕-assoc j [ ix 0 ] ys)))
...   | (ix (suc _) ∷ ys) , refl   = Equivalence.from T-≡ (<ᵖ-part j [] ys refl)
...   | (sub _ ∷ ys) , refl        = Equivalence.from T-≡ (<ᵖ-part j [] ys refl)
...   | (last ∷ ys) , refl         = Equivalence.from T-≡ (<ᵖ-part j [] ys refl)

-- A row made at a row's first child keeps that row's order against a pair
-- no made row lies over.
first-child : ∀ {j j* z z*} → (j ≺ z → j* ≺ z*) × (j* ≺ z* → j ≺ z)
            → ¬ (j ⊕ [ ix 0 ]) ⊑ z → ¬ (j* ⊕ [ ix 0 ]) ⊑ z*
            → ((j ⊕ [ ix 0 ]) ≺ z → (j* ⊕ [ ix 0 ]) ≺ z*) × ((j* ⊕ [ ix 0 ]) ≺ z* → (j ⊕ [ ix 0 ]) ≺ z)
first-child {j} {j*} {z} {z*} (f , b) n n* =
  (λ lt → ix0-first (f (≺-trans {j} {j ⊕ [ ix 0 ]} {z} (≺-ext j []) lt)) n*)
  , (λ lt → ix0-first (b (≺-trans {j*} {j* ⊕ [ ix 0 ]} {z*} (≺-ext j* []) lt)) n)

-- A position not under `p`: before `p`'s child exactly when before `p`.
off-child : ∀ {p k} l → ¬ p ⊑ k → (k ≺ p → k ≺ (p ⊕ [ l ])) × (k ≺ (p ⊕ [ l ]) → k ≺ p)
off-child {p} {k} l np = (λ lt → ≺-trans {k} {p} {p ⊕ [ l ]} lt (≺-ext p [])) , back
  where
    back : k ≺ (p ⊕ [ l ]) → k ≺ p
    back lt with ≼-or-≻ p k
    ... | inj₂ kp = kp
    ... | inj₁ pk = ⊥-elim (np (sub-between {p} {p ⊕ [ l ]} {k} (⊑-snoc⁺ p) pk (≺→≼ {k} {p ⊕ [ l ]} lt)))

------------------------------------------------------------------------
-- Boundaries corresponding at one cut

module Inter (Row : Pos → Set) (φ : Pos → Pos) (Puts : Pos → Pos → Set) (Bd Bd* : Pos → Tag → Set) where

  Between : Pos → Pos → Set
  Between = Btw Row φ

  PutBefore : Pos → Pos → Set
  PutBefore = PB Puts

  -- A plain held boundary has a held partner.
  data TagTo : Tag → Tag → Set where
    plain-free : ∀ {g*} → TagTo free g*
    both-held  : ∀ {q q*} → Between q q* → TagTo (held q) (held q*)

  -- An elaborated held boundary has a held partner.
  data TagFrom : Tag → Tag → Set where
    elab-free : ∀ {g} → TagFrom g free
    both-held : ∀ {q q*} → Between q q* → TagFrom (held q) (held q*)

  record BCorr : Set where
    field
      to   : ∀ {b g} → Bd b g → Σ Pos λ b* → Σ Tag λ g* → Bd* b* g* × Between b b* × TagTo g g*
      from : ∀ {b* g*} → Bd* b* g* → Σ Pos λ b → Σ Tag λ g → Bd b g × Between b b* × PutBefore b b* × TagFrom g g*

  -- A correspondence whose pairs, held ones too, cut more alike (`X`):
  -- rows read along maps of their own, as an environment's are.
  data TagToX (X : Pos → Pos → Set) : Tag → Tag → Set where
    plain-free : ∀ {g*} → TagToX X free g*
    both-held  : ∀ {q q*} → Between q q* → X q q* → TagToX X (held q) (held q*)

  data TagFromX (X : Pos → Pos → Set) : Tag → Tag → Set where
    elab-free : ∀ {g} → TagFromX X g free
    both-held : ∀ {q q*} → Between q q* → X q q* → TagFromX X (held q) (held q*)

  record BCorrX (X : Pos → Pos → Set) : Set where
    field
      to   : ∀ {b g} → Bd b g → Σ Pos λ b* → Σ Tag λ g* → Bd* b* g* × Between b b* × X b b* × TagToX X g g*
      from : ∀ {b* g*} → Bd* b* g* → Σ Pos λ b → Σ Tag λ g → Bd b g × Between b b* × PutBefore b b* × X b b* × TagFromX X g g*

  -- What is cut alike carries to what that implies.
  weakenX : ∀ {X X′ : Pos → Pos → Set} → (∀ {z z*} → X z z* → X′ z z*) → BCorrX X → BCorrX X′
  weakenX {X} {X′} w C = record
    { to   = λ bd → let (b* , g* , bd* , btw , x , tg) = BCorrX.to C bd in b* , g* , bd* , btw , w x , tagTo tg
    ; from = λ bd* → let (b , g , bd , btw , pb , x , tg) = BCorrX.from C bd* in b , g , bd , btw , pb , w x , tagFrom tg }
    where
      tagTo : ∀ {g g*} → TagToX X g g* → TagToX X′ g g*
      tagTo plain-free         = plain-free
      tagTo (both-held btw x)  = both-held btw (w x)

      tagFrom : ∀ {g g*} → TagFromX X g g* → TagFromX X′ g g*
      tagFrom elab-free        = elab-free
      tagFrom (both-held btw x) = both-held btw (w x)

  -- Forgetting what more is cut alike.
  forget : ∀ {X} → BCorrX X → BCorr
  forget {X} C = record
    { to   = λ bd → let (b* , g* , bd* , btw , _ , tg) = BCorrX.to C bd in b* , g* , bd* , btw , tagTo tg
    ; from = λ bd* → let (b , g , bd , btw , pb , _ , tg) = BCorrX.from C bd* in b , g , bd , btw , pb , tagFrom tg }
    where
      tagTo : ∀ {g g*} → TagToX X g g* → TagTo g g*
      tagTo plain-free        = plain-free
      tagTo (both-held btw _) = both-held btw

      tagFrom : ∀ {g g*} → TagFromX X g g* → TagFrom g g*
      tagFrom elab-free         = elab-free
      tagFrom (both-held btw _) = both-held btw

  Clear Clear* : Pos → Set
  Clear k  = ∀ {b g} → Bd b g → k ≺ b
  Clear* l = ∀ {b g} → Bd* b g → l ≺ b

  module _ (C : BCorr) where
    open BCorr C

    clear→ : ∀ {k} → Row k → Clear k → Clear* (φ k)
    clear→ r cl bd* with from bd*
    ... | _ , _ , bd , btw , _ = proj₁ (btw r) (cl bd)

    clear← : ∀ {k} → Row k → Clear* (φ k) → Clear k
    clear← r cl* bd with to bd
    ... | _ , _ , bd* , btw , _ = proj₂ (btw r) (cl* bd*)

    clear-put : ∀ {k l} → Puts k l → Clear k → Clear* l
    clear-put x cl bd* with from bd*
    ... | _ , _ , bd , _ , pb , _ = pb x (cl bd)

-- No boundary on either side corresponds trivially.
none-corr : ∀ {Row φ Puts} → Inter.BCorr Row φ Puts (λ _ _ → ⊥) (λ _ _ → ⊥)
none-corr = record { to = λ () ; from = λ () }

-- A correspondence over more rows and placements holds over fewer.
module Sub {Row Row′ : Pos → Set} {φ : Pos → Pos} {Puts Puts′ : Pos → Pos → Set} {Bd Bd* : Pos → Tag → Set}
  (r : ∀ {k} → Row k → Row′ k) (pt : ∀ {k l} → Puts k l → Puts′ k l) where
  module I  = Inter Row φ Puts Bd Bd*
  module I′ = Inter Row′ φ Puts′ Bd Bd*

  tagTo : ∀ {g g*} → I′.TagTo g g* → I.TagTo g g*
  tagTo I′.plain-free       = I.plain-free
  tagTo (I′.both-held btw)  = I.both-held (λ x → btw (r x))

  tagFrom : ∀ {g g*} → I′.TagFrom g g* → I.TagFrom g g*
  tagFrom I′.elab-free      = I.elab-free
  tagFrom (I′.both-held btw) = I.both-held (λ x → btw (r x))

  restrict : I′.BCorr → I.BCorr
  restrict C = record
    { to   = λ bd → let (b* , g* , bd* , btw , tg) = I′.BCorr.to C bd in b* , g* , bd* , (λ x → btw (r x)) , tagTo tg
    ; from = λ bd* → let (b , g , bd , btw , pb , tg) = I′.BCorr.from C bd* in b , g , bd , (λ x → btw (r x)) , (λ x → pb (pt x)) , tagFrom tg }

------------------------------------------------------------------------
-- At the root: settled together

module Root {A : Set}
  (c : ℕ → EmissionSet A) (d : ℕ → EmissionSet (IE A)) (Bd Bd* : ℕ → Pos → Tag → Set)
  (B : Cuts.Bounded c Bd) (B* : Cuts.Bounded d Bd*)
  (off : ∀ {N k e} → c N k e → Cuts.Off c Bd N k) (off* : ∀ {N k e} → d N k e → Cuts.Off d Bd* N k)
  (R : Cuts.Real c Bd) (R* : Cuts.Real d Bd*)
  (φ : ℕ → Pos → Pos) (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set)
  (C : ∀ N → Inter.BCorr (Own (c N) (Late N)) (φ N) (OwnPut (c N) (Put N)) (Bd N) (Bd* N))
  where
  module I (N : ℕ) = Inter (Own (c N) (Late N)) (φ N) (OwnPut (c N) (Put N)) (Bd N) (Bd* N)

  open Settle c d Bd Bd* B B* R R* off off* φ Put Late
    (λ {N} x un nl → I.clear→ N (C N) (_ , x , un , nl))
    (λ {N} x un nl → I.clear← N (C N) (_ , x , un , nl))
    (λ {N} x pl → I.clear-put N (C N) ((_ , x) , pl))
    public using (settle→; settle←; settle-put)

------------------------------------------------------------------------
-- Two spins cut alike

-- Every own row lies before the spin's boundary, on both sides; the
-- environment lies before it as before the spin's subscription.
module SpinPair {X Y : Set} (p p* : Pos) (N : ℕ) (φ : Pos → Pos)
  (Env : Pos → Set) (EnvPut : Pos → Pos → Set)
  (rows* : ∀ {k e} → SpinB.c {X} p N k e → Σ (Ev Y) (SpinB.c {Y} p* N (φ k)))
  (env-at : Btw Env φ p p*) (env-off : ∀ {k} → Env k → ¬ p ⊑ k) (env-off* : ∀ {k} → Env k → ¬ p* ⊑ φ k)
  (put-at : PB EnvPut p p*) (put-off : ∀ {k l} → EnvPut k l → ¬ p ⊑ k)
  where
  module P = SpinB {X} p
  module E = SpinB {Y} p*

  b b* : Pos
  b  = p ⊕ [ ix (3 + N) ]
  b* = p* ⊕ [ ix (3 + N) ]

  module I = Inter (Own (P.c N) (λ _ → ⊥) ∪ Env) φ ((λ _ _ → ⊥) ∪² EnvPut) (P.Bd N) (E.Bd N)

  before : ∀ {Z} (q : Pos) {k e} → TR {Z} (S (3 + N) q) k e → k ≺ (q ⊕ [ ix (3 + N) ])
  before q x with sp→ x
  ... | i , lt , refl , _ = ix-asc q lt

  between : I.Between b b*
  between (inj₁ (_ , x , _ , _)) = (λ _ → before p* (proj₂ (rows* x))) , (λ _ → before p x)
  between {k} (inj₂ en) =
    (λ lt → proj₁ (off-child {p*} {φ k} (ix (3 + N)) (env-off* en)) (proj₁ (env-at en) (proj₂ (off-child {p} {k} (ix (3 + N)) (env-off en)) lt)))
    , (λ lt → proj₁ (off-child {p} {k} (ix (3 + N)) (env-off en)) (proj₂ (env-at en) (proj₂ (off-child {p*} {φ k} (ix (3 + N)) (env-off* en)) lt)))

  put-before : I.PutBefore b b*
  put-before (inj₁ ())
  put-before {k} {l} (inj₂ x) lt =
    ≺-trans {l} {p*} {b*} (put-at x (proj₂ (off-child {p} {k} (ix (3 + N)) (put-off x)) lt)) (≺-ext p* [])

  corr : I.BCorr
  corr = record
    { to   = λ { {g = .free} (refl , refl) → b* , free , (refl , refl) , between , I.plain-free }
    ; from = λ { {g* = .free} (refl , refl) → b , free , (refl , refl) , between , put-before , I.elab-free } }

------------------------------------------------------------------------
-- A take over corresponding sources

module TakePair {A X : Set} (incl : Bool) (keep : A → Bool) (keep* : X → Bool)
  (c : EmissionSet A) (d : EmissionSet X) (φ : Pos → Pos) (Put : Pos → Pos → Set) (Late : Pos → Set)
  (Env : Pos → Set) (EnvPut : Pos → Pos → Set)
  (Bd Bd* : Pos → Tag → Set)
  (R : Run c)
  (gap  : ∀ {b g y e} → Bd b g → c y e → ¬ y ⊑ b)
  (gap* : ∀ {b g y e} → Bd* b g → d y e → ¬ y ⊑ b)
  (held-in  : ∀ {b q} → Bd b (held q) → q ≺ b)
  (held-in* : ∀ {b q} → Bd* b (held q) → q ≺ b)
  -- no row lies over a connect a boundary waits on
  (held-gap  : ∀ {b q y e} → Bd b (held q) → c y e → ¬ y ⊑ q)
  (held-gap* : ∀ {b q y e} → Bd* b (held q) → d y e → ¬ y ⊑ q)
  (C : Inter.BCorr (Own c Late ∪ Env) φ (OwnPut c Put ∪² EnvPut) Bd Bd*)
  -- a failing value's image fails, and an elaborated failing value is one's image
  (nl-out : ∀ {o a} → c o (out a) → ¬ Late o)
  (fail→ : ∀ {f a} → c f (out a) → T (not (keep a)) → Σ X λ x → d (φ f) (out x) × T (not (keep* x)))
  (fail← : ∀ {f* x} → d f* (out x) → T (not (keep* x)) → Σ Pos λ f → Σ A λ a → c f (out a) × T (not (keep a)) × f* ≡ φ f)
  -- the take's images: a kept row's its source row's, a made row's under its value's
  (φ′ : Pos → Pos)
  (φ′-self : ∀ {k e} → c k e → φ′ k ≡ φ k)
  (φ′-new : ∀ {o a l} → c o (out a) → φ′ (o ⊕ [ l ]) ≡ φ o ⊕ [ l ])
  (φ′-env : ∀ {k} → Env k → φ′ k ≡ φ k)
  where
  open Take incl keep using (module One)
  module I = Inter (Own c Late ∪ Env) φ (OwnPut c Put ∪² EnvPut) Bd Bd*
  open Inter.BCorr C

  Fl : Pos → Set
  Fl = TakeWhile.Failed incl keep c

  Fl* : Pos → Set
  Fl* = TakeWhile.Failed incl keep* d

  Keep : Pos → Tag → Set
  Keep b free     = ¬ Fl b
  Keep b (held q) = ¬ Fl q

  Keep* : Pos → Tag → Set
  Keep* b free     = ¬ Fl* b
  Keep* b (held q) = ¬ Fl* q

  Tk  = TakeWhile.TakeT incl keep c

  Bd′ : Pos → Tag → Set
  Bd′ b g = Bd b g × Keep b g

  Bd*′ : Pos → Tag → Set
  Bd*′ b g = Bd* b g × Keep* b g

  -- A late row of the take is its source's, placed as there.
  Put′ : Pos → Pos → Set
  Put′ k l = Σ (Ev A) (c k) × Put k l

  module I′ = Inter (Own Tk Late ∪ Env) φ′ (OwnPut Tk Put′ ∪² EnvPut) Bd′ Bd*′

  -- A failure before a position carries to its partner, and back.
  fail-to : ∀ {z z*} → I.Between z z* → Fl z → Fl* z*
  fail-to btw (f , a , x , nk , fz) with fail→ x nk
  ... | x* , y , nk* = φ _ , x* , y , nk* , proj₁ (btw (inj₁ (out a , x , _ , nl-out x))) fz

  fail-from : ∀ {z z*} → I.Between z z* → Fl* z* → Fl z
  fail-from {z* = z*} btw (f* , x , y , nk* , fz*) with fail← y nk*
  ... | f , a , xf , nk , refl = f , a , xf , nk , proj₂ (btw (inj₁ (out a , xf , _ , nl-out xf))) fz*

  either : ∀ (B : Pos → Tag → Set) {b} {Z : Set} → B b free ⊎ Σ Pos (λ q → B b (held q)) → (∀ {g} → B b g → Z) → Z
  either _ (inj₁ bd) k = k bd
  either _ (inj₂ (_ , bd)) k = k bd

  -- The take's rows keep the order against partners no row lies over.
  between-at : ∀ {b b*} → (∀ {y e} → c y e → ¬ y ⊑ b) → (∀ {y e} → d y e → ¬ y ⊑ b*)
             → I.Between b b* → I′.Between b b*
  between-at {b} {b*} ng ng* btw {k} (inj₂ en) =
    subst (λ w → (k ≺ b → w ≺ b*) × (w ≺ b* → k ≺ b)) (sym (φ′-env en)) (btw (inj₂ en))
  between-at {b} {b*} ng ng* btw {k} (inj₁ (e , tk , un , nl)) with One.from R tk
  ... | One.self x _ = subst (λ w → (k ≺ b → w ≺ b*) × (w ≺ b* → k ≺ b)) (sym (φ′-self x)) (btw (inj₁ (e , x , un , nl)))
  ... | One.new {o} {a} x nk _ (l , refl , _) = subst (λ w → (k ≺ b → w ≺ b*) × (w ≺ b* → k ≺ b)) (sym (φ′-new x)) (fw , bw)
    where
      ob = btw (inj₁ (out a , x , _ , nl-out x))
      img = proj₁ (proj₂ (fail→ x nk))

      fw : (o ⊕ [ l ]) ≺ b → (φ o ⊕ [ l ]) ≺ b*
      fw lt = past-child l (proj₁ ob (≺-trans {o} {o ⊕ [ l ]} {b} (≺-ext o []) lt)) (ng* img)

      bw : (φ o ⊕ [ l ]) ≺ b* → (o ⊕ [ l ]) ≺ b
      bw lt = past-child l (proj₂ ob (≺-trans {φ o} {φ o ⊕ [ l ]} {b*} (≺-ext (φ o) []) lt)) (ng x)

  between′ : ∀ {b b*} → Bd b free ⊎ Σ Pos (λ q → Bd b (held q)) → Bd* b* free ⊎ Σ Pos (λ q → Bd* b* (held q))
           → I.Between b b* → I′.Between b b*
  between′ bdp bde = between-at (λ x → either Bd bdp (λ bd → gap bd x)) (λ y → either Bd* bde (λ bd* → gap* bd* y))

  tagged : ∀ (B : Pos → Tag → Set) {b} g → B b g → B b free ⊎ Σ Pos (λ q → B b (held q))
  tagged _ free     bd = inj₁ bd
  tagged _ (held q) bd = inj₂ (q , bd)

  -- A KEPT BOUNDARY'S PARTNER IS KEPT, each way.
  keep→ : ∀ {b b* g g*} → Bd* b* g* → I.Between b b* → I.TagTo g g* → Keep b g → Keep* b* g*
  keep→ {g* = free}   _   btw I.plain-free kp F* = kp (fail-from btw F*)
  keep→ {b* = b*} {g* = held q*} bd* btw I.plain-free kp (f* , x , y , nk* , fq*) =
    kp (fail-from btw (f* , x , y , nk* , ≺-trans {f*} {q*} {b*} fq* (held-in* bd*)))
  keep→ _ _ (I.both-held btwq) kp F* = kp (fail-from btwq F*)

  keep← : ∀ {b b* g g*} → Bd b g → I.Between b b* → I.TagFrom g g* → Keep* b* g* → Keep b g
  keep← {g = free}   _   btw I.elab-free kp F = kp (fail-to btw F)
  keep← {b = b} {g = held q} bd btw I.elab-free kp (f , a , x , nk , fq) =
    kp (fail-to btw (f , a , x , nk , ≺-trans {f} {q} {b} fq (held-in bd)))
  keep← _ _ (I.both-held btwq) kp F = kp (fail-to btwq F)

  tag→ : ∀ {b b* g g*} → Bd b g → Bd* b* g* → I.TagTo g g* → I′.TagTo g g*
  tag→ _  _   I.plain-free      = I′.plain-free
  tag→ bd bd* (I.both-held btw) = I′.both-held (between-at (held-gap bd) (held-gap* bd*) btw)

  tag← : ∀ {b b* g g*} → Bd b g → Bd* b* g* → I.TagFrom g g* → I′.TagFrom g g*
  tag← _  _   I.elab-free       = I′.elab-free
  tag← bd bd* (I.both-held btw) = I′.both-held (between-at (held-gap bd) (held-gap* bd*) btw)

  corr′ : I′.BCorr
  corr′ = record
    { to = λ { {g = g} (bd , kp) → case-to g bd kp }
    ; from = λ { {g* = g*} (bd* , kp*) → case-from g* bd* kp* } }
    where
      case-to : ∀ {b} g → Bd b g → Keep b g → Σ Pos λ b* → Σ Tag λ g* → Bd*′ b* g* × I′.Between b b* × I′.TagTo g g*
      case-to g bd kp with to bd
      ... | b* , g* , bd* , btw , tt = b* , g* , (bd* , keep→ bd* btw tt kp) , between′ (tagged Bd g bd) (tagged Bd* g* bd*) btw , tag→ bd bd* tt

      case-from : ∀ {b*} g* → Bd* b* g* → Keep* b* g* → Σ Pos λ b → Σ Tag λ g → Bd′ b g × I′.Between b b* × I′.PutBefore b b* × I′.TagFrom g g*
      case-from g* bd* kp* with from bd*
      ... | b , g , bd , btw , pb , tf =
        b , g , (bd , keep← bd btw tf kp*) , between′ (tagged Bd g bd) (tagged Bd* g* bd*) btw
        , pb-∪ {OwnPut Tk Put′} {EnvPut} (λ {k} {l} → λ { (_ , (x , pl)) kb → pb {k} {l} (inj₁ (x , pl)) kb }) (λ {k} {l} x kb → pb {k} {l} (inj₂ x) kb) , tag← bd bd* tf

------------------------------------------------------------------------
-- A layer wrapping the elaborated side alone

-- The wrapper holds the wrapped boundaries a plain one partners, in place
-- with their tags; it holds no other, save freed; and its rows keep the
-- wrapped rows' order against those boundaries and the connects they
-- wait on.
module Wrap (Row : Pos → Set) (φ φw : Pos → Pos) (Puts Putsw : Pos → Pos → Set) (Bd Bd* Bdw : Pos → Tag → Set)
  (C : Inter.BCorr Row φ Puts Bd Bd*)
  (keeps : ∀ {b b* g g*} → Bd b g → Bd* b* g* → Btw Row φ b b* → Bdw b* g*)
  (only : ∀ {b g} → Bdw b g → Σ Tag λ g₀ → Bd* b g₀ × (g ≡ g₀ ⊎ g ≡ free))
  (moved : ∀ {k b g} → Row k → Bd* b g → (φ k ≺ b → φw k ≺ b) × (φw k ≺ b → φ k ≺ b))
  (moved-q : ∀ {k b q} → Row k → Bd* b (held q) → (φ k ≺ q → φw k ≺ q) × (φw k ≺ q → φ k ≺ q))
  (putw : ∀ {b b* g*} → Bd* b* g* → PB Puts b b* → PB Putsw b b*)
  where
  module I  = Inter Row φ Puts Bd Bd*
  module Iw = Inter Row φw Putsw Bd Bdw
  open Inter.BCorr C

  between-at : ∀ {b b*} → (∀ {k} → Row k → (φ k ≺ b* → φw k ≺ b*) × (φw k ≺ b* → φ k ≺ b*))
             → I.Between b b* → Iw.Between b b*
  between-at mv btw r = (λ lt → proj₁ (mv r) (proj₁ (btw r) lt)) , (λ lt → proj₂ (btw r) (proj₂ (mv r) lt))

  tag→ : ∀ {b* g g*} → Bd* b* g* → I.TagTo g g* → Iw.TagTo g g*
  tag→ _   I.plain-free       = Iw.plain-free
  tag→ bd* (I.both-held btw)  = Iw.both-held (between-at (λ r → moved-q r bd*) btw)

  tag← : ∀ {b* g g* g′} → Bd* b* g* → I.TagFrom g g* → (g′ ≡ g* ⊎ g′ ≡ free) → Iw.TagFrom g g′
  tag← _ _ (inj₂ refl)                     = Iw.elab-free
  tag← _ I.elab-free (inj₁ refl)           = Iw.elab-free
  tag← bd* (I.both-held btw) (inj₁ refl)   = Iw.both-held (between-at (λ r → moved-q r bd*) btw)

  corr : Iw.BCorr
  corr = record
    { to = λ bd → case-to bd
    ; from = λ bdw → case-from bdw }
    where
      case-to : ∀ {b g} → Bd b g → Σ Pos λ b* → Σ Tag λ g* → Bdw b* g* × Iw.Between b b* × Iw.TagTo g g*
      case-to bd with to bd
      ... | b* , g* , bd* , btw , tt = b* , g* , keeps bd bd* btw , between-at (λ r → moved r bd*) btw , tag→ bd* tt

      case-from : ∀ {b* g′} → Bdw b* g′ → Σ Pos λ b → Σ Tag λ g → Bd b g × Iw.Between b b* × Iw.PutBefore b b* × Iw.TagFrom g g′
      case-from bdw with only bdw
      ... | g* , bd* , eq with from bd*
      ...   | b , g , bd , btw , pb , tf = b , g , bd , between-at (λ r → moved r bd*) btw , putw bd* pb , tag← bd* tf eq

-- A hot row read past a reader's subscription keeps its order against
-- every position no hot row lies over.
module ReaderMove {X : Set} (s : Pos) (h : EmissionSet X)
  where

  moved : ∀ {y e b} → h y e → ¬ y ⊑ b → (y ≺ b → (y ⊕ [ sub s ]) ≺ b) × ((y ⊕ [ sub s ]) ≺ b → y ≺ b)
  moved {y} {b = b} x ng = (λ lt → past-child (sub s) lt ng) , (λ lt → ≺-trans {y} {y ⊕ [ sub s ]} {b} (≺-ext y []) lt)
