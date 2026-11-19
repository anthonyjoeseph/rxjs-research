{-# OPTIONS --guardedness #-}

-- THE PLAIN PROGRAM'S BOUNDARIES AND THE ELABORATION'S, AT ONE CUT.  Two
-- boundaries correspond when the same plain rows lie before each: before
-- the plain one exactly when their images lie before the elaborated one
-- (`Inter.Between`).  Every boundary has a partner on the other side
-- (`Inter.BCorr`), and a held one has a held partner, waiting on a
-- connect with the same rows before it (`Inter.TagTo`, `Inter.TagFrom`);
-- the elaborated side may hold free what the plain side holds, never the
-- reverse.  Then a plain row and its image are clear together
-- (`Inter.clear→`, `Inter.clear←`), so settled together (`Root`).
--
-- A FORMER KEEPS THE CORRESPONDENCE: a take keeps a boundary where its
-- partner's take does, since a failing value lies before the one exactly
-- when its image lies before the other (`TakePair`).  A layer that wraps
-- the elaborated side alone keeps every boundary in place, and its rows
-- keep their order against them (`Wrap`), as a hot row read past a
-- subscription does (`ReaderMove`).
-- Two spins cut alike correspond (`SpinPair`).
--
-- A BOUNDARY A LANE INHERITS FROM A HOT IS REAL AT THE CONNECT OWNING IT.
-- A lane's boundary is real, or the hot's (`RealEnv.RealRel`); the
-- connect holds its source's rows as its own, so it discharges its
-- source's, wherever its body met them (`ConnReal`).  Closed, every
-- boundary is real (`RealEnv.closed`).
module simultaneous.HorizonCorr where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Nat using (ℕ; _<_; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; pin; Unpinned; EmissionSet; _≺_; _≼_; Rejoin; shown; heard; ended; late;
  module TakeWhile)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_)
open import denotation.Laws.Cut using (ix-asc)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.TableCorr using (TR)
open import simultaneous.TableSpin using (S; sp→)
open import simultaneous.TakeKit using (Run; module Take)
open import simultaneous.Horizon using (Tag; free; held; module Cuts; module Settle; module SpinB; module ConnB; past-child)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- Boundaries corresponding at one cut

module Inter {A X : Set} (L : EmissionSet A) (L* : EmissionSet X) (φ : Pos → Pos) (Put : Pos → Pos → Set) (Late : Pos → Set)
  (Bd Bd* : Pos → Tag → Set) where

  Row : Pos → Set
  Row k = Σ (Ev A) λ e → L k e × Unpinned e × ¬ Late k

  -- The same plain rows before each.
  Between : Pos → Pos → Set
  Between b b* = ∀ {k} → Row k → (k ≺ b → φ k ≺ b*) × (φ k ≺ b* → k ≺ b)

  -- A late placement of a row before the plain one lies before the other.
  PutBefore : Pos → Pos → Set
  PutBefore b b* = ∀ {k e l} → L k e → Put k l → k ≺ b → l ≺ b*

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

    clear-put : ∀ {k e l} → L k e → Put k l → Clear k → Clear* l
    clear-put x pl cl bd* with from bd*
    ... | _ , _ , bd , _ , pb , _ = pb x pl (cl bd)

------------------------------------------------------------------------
-- At the root: settled together

module Root {A : Set}
  (c : ℕ → EmissionSet A) (d : ℕ → EmissionSet (IE A)) (Bd Bd* : ℕ → Pos → Tag → Set)
  (B : Cuts.Bounded c Bd) (B* : Cuts.Bounded d Bd*) (R : Cuts.Real c Bd) (R* : Cuts.Real d Bd*)
  (φ : ℕ → Pos → Pos) (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set)
  (C : ∀ N → Inter.BCorr (c N) (d N) (φ N) (Put N) (Late N) (Bd N) (Bd* N))
  where
  module I (N : ℕ) = Inter (c N) (d N) (φ N) (Put N) (Late N) (Bd N) (Bd* N)

  open Settle c d Bd Bd* B B* R R* φ Put Late
    (λ {N} x un nl → I.clear→ N (C N) (_ , x , un , nl))
    (λ {N} x un nl → I.clear← N (C N) (_ , x , un , nl))
    (λ {N} x pl → I.clear-put N (C N) x pl)
    public using (settle→; settle←; settle-put)

------------------------------------------------------------------------
-- Two spins cut alike

module SpinPair {X Y : Set} (p p* : Pos) (N : ℕ) where
  module P = SpinB {X} p
  module E = SpinB {Y} p*

  φ : Pos → Pos
  φ k = k

  -- Each row lies before each boundary, on both sides.
  module I = Inter (P.c N) (E.c N) (λ k → k) (λ _ _ → ⊥) (λ _ → ⊥) (P.Bd N) (E.Bd N)

  before : ∀ {Z} (q : Pos) {k e} → TR {Z} (S (3 + N) q) k e → k ≺ (q ⊕ [ ix (3 + N) ])
  before q x with sp→ x
  ... | i , lt , refl , _ = ix-asc q lt

  -- Each spin's rows, read at the other's position.
  module Moved (rows* : ∀ {k e} → P.c N k e → Σ (Ev Y) (E.c N k)) where
    corr : I.BCorr
    corr = record
      { to   = λ { {g = .free} (refl , refl) → p* ⊕ [ ix (3 + N) ] , free , (refl , refl)
                 , (λ { (_ , x , _ , _) → (λ _ → before p* (proj₂ (rows* x))) , (λ _ → before p x) }) , I.plain-free }
      ; from = λ { {g* = .free} (refl , refl) → p ⊕ [ ix (3 + N) ] , free , (refl , refl)
                 , (λ { (_ , x , _ , _) → (λ _ → before p* (proj₂ (rows* x))) , (λ _ → before p x) }) , (λ _ ()) , I.elab-free } }

------------------------------------------------------------------------
-- A take over corresponding sources

module TakePair {A X : Set} (incl : Bool) (keep : A → Bool) (keep* : X → Bool)
  (c : EmissionSet A) (d : EmissionSet X) (φ : Pos → Pos) (Put : Pos → Pos → Set) (Late : Pos → Set)
  (Bd Bd* : Pos → Tag → Set)
  (R : Run c)
  (gap  : ∀ {b g y e} → Bd b g → c y e → ¬ b ⊑ y × ¬ y ⊑ b)
  (gap* : ∀ {b g y e} → Bd* b g → d y e → ¬ b ⊑ y × ¬ y ⊑ b)
  (held-in  : ∀ {b q} → Bd b (held q) → q ≺ b)
  (held-in* : ∀ {b q} → Bd* b (held q) → q ≺ b)
  -- no row lies over a connect a boundary waits on
  (held-gap  : ∀ {b q y e} → Bd b (held q) → c y e → ¬ y ⊑ q)
  (held-gap* : ∀ {b q y e} → Bd* b (held q) → d y e → ¬ y ⊑ q)
  (C : Inter.BCorr c d φ Put Late Bd Bd*)
  -- a failing value's image fails, and an elaborated failing value is one's image
  (nl-out : ∀ {o a} → c o (out a) → ¬ Late o)
  (fail→ : ∀ {f a} → c f (out a) → T (not (keep a)) → Σ X λ x → d (φ f) (out x) × T (not (keep* x)))
  (fail← : ∀ {f* x} → d f* (out x) → T (not (keep* x)) → Σ Pos λ f → Σ A λ a → c f (out a) × T (not (keep a)) × f* ≡ φ f)
  -- the take's images: a kept row's its source row's, a made row's under its value's
  (φ′ : Pos → Pos)
  (φ′-self : ∀ {k e} → c k e → φ′ k ≡ φ k)
  (φ′-new : ∀ {o a l} → c o (out a) → φ′ (o ⊕ [ l ]) ≡ φ o ⊕ [ l ])
  where
  open Take incl keep using (module One)
  module I = Inter c d φ Put Late Bd Bd*
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
  Tk* = TakeWhile.TakeT incl keep* d

  Bd′ : Pos → Tag → Set
  Bd′ b g = Bd b g × Keep b g

  Bd*′ : Pos → Tag → Set
  Bd*′ b g = Bd* b g × Keep* b g

  Put′ : Pos → Pos → Set
  Put′ k l = Σ (Ev A) (c k) × Put k l

  module I′ = Inter Tk Tk* φ′ Put′ Late Bd′ Bd*′

  -- A failure before a position carries to its partner, and back.
  fail-to : ∀ {z z*} → I.Between z z* → Fl z → Fl* z*
  fail-to btw (f , a , x , nk , fz) with fail→ x nk
  ... | x* , y , nk* = φ _ , x* , y , nk* , proj₁ (btw (out a , x , _ , nl-out x)) fz

  fail-from : ∀ {z z*} → I.Between z z* → Fl* z* → Fl z
  fail-from {z* = z*} btw (f* , x , y , nk* , fz*) with fail← y nk*
  ... | f , a , xf , nk , refl = f , a , xf , nk , proj₂ (btw (out a , xf , _ , nl-out xf)) fz*

  either : ∀ (B : Pos → Tag → Set) {b} {Z : Set} → B b free ⊎ Σ Pos (λ q → B b (held q)) → (∀ {g} → B b g → Z) → Z
  either _ (inj₁ bd) k = k bd
  either _ (inj₂ (_ , bd)) k = k bd

  -- The take's rows keep the order against partners no row lies over.
  between-at : ∀ {b b*} → (∀ {y e} → c y e → ¬ y ⊑ b) → (∀ {y e} → d y e → ¬ y ⊑ b*)
             → I.Between b b* → I′.Between b b*
  between-at {b} {b*} ng ng* btw {k} (e , tk , un , nl) with One.from R tk
  ... | One.self x _ = subst (λ w → (k ≺ b → w ≺ b*) × (w ≺ b* → k ≺ b)) (sym (φ′-self x)) (btw (e , x , un , nl))
  ... | One.new {o} {a} x nk _ (l , refl , _) = subst (λ w → (k ≺ b → w ≺ b*) × (w ≺ b* → k ≺ b)) (sym (φ′-new x)) (fw , bw)
    where
      ob = btw (out a , x , _ , nl-out x)
      img = proj₁ (proj₂ (fail→ x nk))

      ngap : ¬ o ⊑ b
      ngap = ng x

      ngap* : ¬ φ o ⊑ b*
      ngap* = ng* img

      fw : (o ⊕ [ l ]) ≺ b → (φ o ⊕ [ l ]) ≺ b*
      fw lt = past-child l (proj₁ ob (≺-trans {o} {o ⊕ [ l ]} {b} (≺-ext o []) lt)) ngap*

      bw : (φ o ⊕ [ l ]) ≺ b* → (o ⊕ [ l ]) ≺ b
      bw lt = past-child l (proj₂ ob (≺-trans {φ o} {φ o ⊕ [ l ]} {b*} (≺-ext (φ o) []) lt)) ngap

  between′ : ∀ {b b*} → Bd b free ⊎ Σ Pos (λ q → Bd b (held q)) → Bd* b* free ⊎ Σ Pos (λ q → Bd* b* (held q))
           → I.Between b b* → I′.Between b b*
  between′ bdp bde = between-at (λ x → either Bd bdp (λ bd → proj₂ (gap bd x))) (λ y → either Bd* bde (λ bd* → proj₂ (gap* bd* y)))

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
        b , g , (bd , keep← bd btw tf kp*) , between′ (tagged Bd g bd) (tagged Bd* g* bd*) btw , (λ { _ ((_ , x) , pl) kb → pb x pl kb }) , tag← bd bd* tf

------------------------------------------------------------------------
-- A layer wrapping the elaborated side alone

-- The wrapper holds every boundary of what it wraps, in place, with its
-- tag or free; it holds no other; and its rows read off the wrapped rows
-- keep their order against those boundaries.
module Wrap {A X Y : Set} (L : EmissionSet A) (L* : EmissionSet X) (W : EmissionSet Y)
  (φ : Pos → Pos) (Put : Pos → Pos → Set) (Late : Pos → Set) (Bd Bd* Bdw : Pos → Tag → Set)
  (C : Inter.BCorr L L* φ Put Late Bd Bd*)
  (move : Pos → Pos)
  (keeps : ∀ {b g} → Bd* b g → Bdw b g)
  (only : ∀ {b g} → Bdw b g → Σ Tag λ g₀ → Bd* b g₀ × (g ≡ g₀ ⊎ g ≡ free))
  (moved : ∀ {k e b g} → L* (φ k) e → Bd* b g → (φ k ≺ b → move (φ k) ≺ b) × (move (φ k) ≺ b → φ k ≺ b))
  (moved-q : ∀ {k e b q} → L* (φ k) e → Bd* b (held q) → (φ k ≺ q → move (φ k) ≺ q) × (move (φ k) ≺ q → φ k ≺ q))
  (img : ∀ {k} → Inter.Row L L* φ Put Late Bd Bd* k → Σ (Ev X) λ e* → L* (φ k) e*)
  (Putw : Pos → Pos → Set)
  (putw : ∀ {k e l b b*} → L k e → Putw k l → Inter.PutBefore L L* φ Put Late Bd Bd* b b* → k ≺ b → l ≺ b*)
  where
  module I  = Inter L L* φ Put Late Bd Bd*
  module Iw = Inter L W (λ k → move (φ k)) Putw Late Bd Bdw
  open Inter.BCorr C

  between-at : ∀ {b b*} → (∀ {k e} → L* (φ k) e → (φ k ≺ b* → move (φ k) ≺ b*) × (move (φ k) ≺ b* → φ k ≺ b*))
             → I.Between b b* → Iw.Between b b*
  between-at mv btw r with img r
  ... | _ , y = (λ lt → proj₁ (mv y) (proj₁ (btw r) lt)) , (λ lt → proj₂ (btw r) (proj₂ (mv y) lt))

  between : ∀ {b b* g*} → Bd* b* g* → I.Between b b* → Iw.Between b b*
  between bd* = between-at (λ y → moved y bd*)

  tag→ : ∀ {b* g g*} → Bd* b* g* → I.TagTo g g* → Iw.TagTo g g*
  tag→ _   I.plain-free       = Iw.plain-free
  tag→ bd* (I.both-held btw)  = Iw.both-held (between-at (λ y → moved-q y bd*) btw)

  tag← : ∀ {b* g g* g′} → Bd* b* g* → I.TagFrom g g* → (g′ ≡ g* ⊎ g′ ≡ free) → Iw.TagFrom g g′
  tag← _ _ (inj₂ refl)                     = Iw.elab-free
  tag← _ I.elab-free (inj₁ refl)           = Iw.elab-free
  tag← bd* (I.both-held btw) (inj₁ refl)   = Iw.both-held (between-at (λ y → moved-q y bd*) btw)

  corr : Iw.BCorr
  corr = record
    { to = λ bd → case-to bd
    ; from = λ bdw → case-from bdw }
    where
      case-to : ∀ {b g} → Bd b g → Σ Pos λ b* → Σ Tag λ g* → Bdw b* g* × Iw.Between b b* × Iw.TagTo g g*
      case-to bd with to bd
      ... | b* , g* , bd* , btw , tt = b* , g* , keeps bd* , between bd* btw , tag→ bd* tt

      case-from : ∀ {b* g′} → Bdw b* g′ → Σ Pos λ b → Σ Tag λ g → Bd b g × Iw.Between b b* × Iw.PutBefore b b* × Iw.TagFrom g g′
      case-from bdw with only bdw
      ... | g* , bd* , eq with from bd*
      ...   | b , g , bd , btw , pb , tf = b , g , bd , between bd* btw , (λ x pl kb → putw x pl pb kb) , tag← bd* tf eq

-- A hot row read past a reader's subscription keeps its order against
-- every position no hot row lies over.
module ReaderMove {X : Set} (s : Pos) (h : EmissionSet X)
  where

  moved : ∀ {y e b} → h y e → ¬ y ⊑ b → (y ≺ b → (y ⊕ [ sub s ]) ≺ b) × ((y ⊕ [ sub s ]) ≺ b → y ≺ b)
  moved {y} {b = b} x ng = (λ lt → past-child (sub s) lt ng) , (λ lt → ≺-trans {y} {y ⊕ [ sub s ]} {b} (≺-ext y []) lt)

------------------------------------------------------------------------
-- Real, or the environment's

module RealEnv {A : Set} (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set) where
  open Cuts c Bd

  -- Each boundary is real, or borne by the environment.
  RealRel : (ℕ → Pos → Set) → Set
  RealRel Ext = ∀ {N b g} → Bd N b g → (Σ Pos λ y → Near b y × Diff N y) ⊎ Ext N b

  -- With nothing in the environment, real.
  closed : RealRel (λ _ _ → ⊥) → Real
  closed rr bd with rr bd
  ... | inj₁ r = r
  ... | inj₂ ()

-- A reader's boundaries are all the hot's.
module ReaderReal {X : Set} (s : Pos) (h : ℕ → EmissionSet X) (Bdh : ℕ → Pos → Tag → Set) where
  J : ℕ → EmissionSet X
  J N = Rejoin s (h N)

  JBd : ℕ → Pos → Tag → Set
  JBd N b free     = Σ Tag (Bdh N b)
  JBd N b (held _) = ⊥

  real-j : RealEnv.RealRel J JBd (λ N b → Σ Tag (Bdh N b))
  real-j {g = free} bd = inj₂ bd
  real-j {g = held _} ()

-- THE CONNECT OWNING A HOT DISCHARGES ITS BODY'S DEBTS TO IT: a body
-- boundary borne by the hot is a boundary of the source, which the
-- connect holds, and a source row that differs near it shows.
module ConnReal {A B : Set} (p : Pos) (σ : ℕ → EmissionSet A) (β : ℕ → EmissionSet B) (Bdσ Bdβ : ℕ → Pos → Tag → Set)
  (Bσ : Cuts.Bounded σ Bdσ) (Bβ : Cuts.Bounded β Bdβ)
  (σ-after : ∀ {N b g} → Bdσ N b g → (p ⊕ [ ix 1 ]) ≺ b)
  (σ-held : ∀ {N b q} → Bdσ N b (held q) → (p ⊕ [ ix 1 ]) ≼ q)
  (Ext : ℕ → Pos → Set)
  (Rσ : RealEnv.RealRel σ Bdσ Ext)
  (Rβ : RealEnv.RealRel β Bdβ (λ N b → Σ Tag (Bdσ N b) ⊎ Ext N b))
  where
  open ConnB p σ β Bdσ Bdβ Bσ Bβ σ-after σ-held
  module Sσ′ = Cuts σ Bdσ
  module Sβ′ = Cuts β Bdβ

  postulate
    -- A body row that differs is the connect's.
    body-diff : ∀ {N y} → Sβ′.Diff N y → SC.Diff N y
    -- A source row differing near a boundary the connect holds shows,
    -- or the body's end moved before it.
    shows : ∀ {N b g g₀ y} → CBd N b g → Bdσ N b g₀ → Sσ′.Near b y → Sσ′.Diff N y → Σ Pos λ y′ → SC.Near b y′ × SC.Diff N y′

  src : ∀ {N b g g₀} → CBd N b g → Bdσ N b g₀ → (Σ Pos λ y → SC.Near b y × SC.Diff N y) ⊎ Ext N b
  src cb bd with Rσ bd
  ... | inj₁ (y , near , d) = inj₁ (shows cb bd near d)
  ... | inj₂ e = inj₂ e

  real-c : RealEnv.RealRel Cc CBd Ext
  real-c (bodyB bd) with Rβ bd
  ... | inj₁ (y , near , d)    = inj₁ (y , near , body-diff d)
  ... | inj₂ (inj₁ (_ , bdσ))  = src (bodyB bd) bdσ
  ... | inj₂ (inj₂ e)          = inj₂ e
  real-c cb@(burstB bd _)  = src cb bd
  real-c cb@(echoB bd _ _) = src cb bd
  real-c cb@(keptB bd _ _) = src cb bd
