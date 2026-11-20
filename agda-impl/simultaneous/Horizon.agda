{-# OPTIONS --guardedness #-}

-- WHERE A CUT STOPS BEING THE RUN, READ OFF ONE CUT.  Each former's cut
-- at `N` has BOUNDARIES (`Bd N`): positions where a hang's rows were cut
-- short, kept only while the former still reads past them.  A cut is
-- settled up to `k` (agrees with every deeper cut) when `k` lies before
-- every boundary (`Cuts.Bounded.fwd`).  For a closed program, only then
-- (`Cuts.clear`), off the boundaries: there each one has a row one cut
-- deeper at or before its last descendant (`Cuts.Real`).
--
-- THE ELABORATION HANGS WHERE THE PLAIN PROGRAM DOES (`Settle`): a plain
-- row and its image are settled together once their CLEARNESS
-- corresponds at one cut (`Settle.settle→`, `Settle.settle←`).  Nothing
-- decides where a hang is; clearness is `≺` against each boundary.
--
-- A HANG HIDDEN BEHIND A TAKEWHILE.  A take keeps its source's
-- boundaries only where no failing value precedes them (`TakeClear.Keep`),
-- so a hang past the failure makes no row of anything above it
-- unsettled.
--
-- A HANG IN A SUBSCRIBE BURST OUTLIVES THE READER.  A boundary is `held q`
-- when its hang's rows are pins of the connect at `q`, and every former
-- keeps a held boundary exactly where it keeps those pins: a take while
-- no failure precedes `q` (`TakeClear.Keep`), a connect while its body is
-- alive at `q` (`ConnB.CBd.keptB`).  A connect makes every boundary of
-- its source's burst held by itself (`ConnB.CBd.burstB`); a lane reading
-- a hot keeps each boundary's tag (`RejoinB`), since a hang in the burst
-- is a call still executing when the lane's reader unsubscribes.
-- As a pin waits only on what came before its connect and the burst,
-- pins of `q` settle past an unrelated hang, once every boundary is past
-- `q` and every one held by `q` past the row (`Cuts.Bounded.fwd-pin`); a
-- take reads its pins past the failure by that (`TakeB.fwd′`), a connect
-- its kept pins (`ConnB.fwd`).
--
-- A spin's last row is short of the next cut's (`SpinB`).
--
-- A lane reading a hot keeps the hot's hangs before its subscription,
-- before all its rows, and its cuts never differ near them; so `Real`
-- fails of an open term, and holds of a closed one through the connect
-- whose source the hang is in.
module simultaneous.Horizon where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_])
open import Data.Nat using (ℕ; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties using (n≤1+n; n<1+n; <-irrefl; +-monoʳ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; Rejoin; shown; heard; ended; late; module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; ≺-ext; ≺-trans; ≺-absurd; ≼-refl; ≺→≼; ≼-split;
  ≼-or-≻; ≼-≺-≺; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊑-≼; ⊑-snoc; ⊑-inside; inside-⊑)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.TableKit using (TR; ag-≃)
open import simultaneous.SpinKit using (S; sp→; sp←; step-inj; ix-inj; widen)
open import simultaneous.TakeKit using (Run; ≼-last; module Take)
open import denotation.Laws.Cut using (ix-back)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- Positions under a position

-- Past a position and not under it: past everything under it.
past-sub : ∀ {b y k} → b ⊑ y → b ≼ k → ¬ b ⊑ k → y ≺ k
past-sub {b} {k = k} (zs , refl) bk nb with ≼-split {b} {k} bk
... | inj₂ refl = ⊥-elim (nb (⊑-refl b))
... | inj₁ lt   = Equivalence.from T-≡ (<ᵖ-apart b k zs (Equivalence.to T-≡ lt) (λ ys eq → nb (ys , eq)))

-- Between a position and one under it: under it too.
sub-between : ∀ {b y q} → b ⊑ y → b ≼ q → q ≼ y → b ⊑ q
sub-between {b} {y} {q} by bq qy with T? (inside b q)
... | yes ins = inside-⊑ b q ins
... | no nins = ⊥-elim (qy (past-sub by bq (λ h → nins (⊑-inside h))))

-- Past a position not under it: past its children.
past-child : ∀ {o b} l → o ≺ b → ¬ o ⊑ b → (o ⊕ [ l ]) ≺ b
past-child {o} {b} l lt nsub = Equivalence.from T-≡ (<ᵖ-apart o b [ l ] (Equivalence.to T-≡ lt) (λ ys eq → nsub (ys , eq)))

-- Leading no position: nor do its children.
under-child : ∀ {b q} l → ¬ q ⊑ b → ¬ (q ⊕ [ l ]) ⊑ b
under-child {b} {q} l nqb h = nqb (⊑-trans (⊑-snoc⁺ q) h)

not-T : ∀ {x} → ¬ T x → T (not x)
not-T {false} _ = tt
not-T {true}  n = ⊥-elim (n tt)

T-not : ∀ {x} → T (not x) → ¬ T x
T-not {false} _ ()
T-not {true}  ()

------------------------------------------------------------------------
-- One program's cuts

-- A boundary's hang: free, or the subscribe burst of the connect at `q`.
data Tag : Set where
  free : Tag
  held : Pos → Tag

module Cuts {A : Set} (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set) where

  -- Every deeper cut agrees up to `k`.
  Settled : ℕ → Pos → Set
  Settled N k = ∀ {N′} → N ≤ N′ → AgreeTo k (c N) (c N′)

  -- Before every boundary.
  Clear : ℕ → Pos → Set
  Clear N k = ∀ {b g} → Bd N b g → k ≺ b

  -- Under no boundary.
  Off : ℕ → Pos → Set
  Off N k = ∀ {b g} → Bd N b g → ¬ b ⊑ k

  -- Two emission sets hold the same pins of the connect at `q` up to `k`.
  PinAgree : Pos → Pos → EmissionSet A → EmissionSet A → Set
  PinAgree q k t t′ = ∀ {y} → y ≼ k → (t y (pin q) → t′ y (pin q)) × (t′ y (pin q) → t y (pin q))

  PinSettled : ℕ → Pos → Pos → Set
  PinSettled N q k = ∀ {N′} → N ≤ N′ → PinAgree q k (c N) (c N′)

  -- Before every boundary held by the connect at `q`.
  HeldClear : ℕ → Pos → Pos → Set
  HeldClear N q k = ∀ {b} → Bd N b (held q) → k ≺ b

  -- A row one of two consecutive cuts holds and the other does not.
  Diff : ℕ → Pos → Set
  Diff N y = Σ (Ev A) λ e → (c N y e × ¬ c (suc N) y e) ⊎ (c (suc N) y e × ¬ c N y e)

  -- At or before a boundary's last descendant.
  Near : Pos → Pos → Set
  Near b y = y ≼ b ⊎ b ⊑ y

  -- Every boundary has a row one cut deeper at or before its last
  -- descendant.
  Real : Set
  Real = ∀ {N b g} → Bd N b g → Σ Pos λ y → Near b y × Diff N y

  near-≼ : ∀ {b k y} → Near b y → b ≼ k → ¬ b ⊑ k → y ≼ k
  near-≼ {b} {k} {y} (inj₁ yb) bk _  = λ ky → bk (≺-≼-≺ {k} {y} {b} ky yb)
  near-≼ {b} {k} {y} (inj₂ by) bk nb = ≺→≼ {y} {k} (past-sub by bk nb)

  -- SETTLED, SO CLEAR: a boundary at or before `k` has a row one cut
  -- deeper before `k`, which a settled cut would hold.
  clear : Real → ∀ {N k} → Off N k → Settled N k → Clear N k
  clear real {N} {k} off st {b} bd with ≼-or-≻ b k
  ... | inj₂ kb = kb
  ... | inj₁ bk with real bd
  ...   | y , near , e , d = ⊥-elim (gone d)
    where
      yk : y ≼ k
      yk = near-≼ near bk (off bd)

      gone : (c N y e × ¬ c (suc N) y e) ⊎ (c (suc N) y e × ¬ c N y e) → ⊥
      gone (inj₁ (x , nx)) = nx (proj₁ (upto (st (n≤1+n N)) {y} {e} yk) x)
      gone (inj₂ (x , nx)) = nx (proj₂ (upto (st (n≤1+n N)) {y} {e} yk) x)

  record Bounded : Set where
    field
      -- a row leads no boundary
      gap     : ∀ {N b g y e} → Bd N b g → c N y e → ¬ y ⊑ b
      held-in : ∀ {N b q} → Bd N b (held q) → q ≺ b
      -- a held boundary lies under the connect holding it
      held-under : ∀ {N b q} → Bd N b (held q) → q ⊑ b
      fwd     : ∀ {N k} → Clear N k → Settled N k
      fwd-pin : ∀ {N q k} → Clear N q → HeldClear N q k → PinSettled N q k

-- A cut that never moves hangs nowhere.
const-bounded : ∀ {A} (t : EmissionSet A) → Cuts.Bounded (λ _ → t) (λ _ _ _ → ⊥)
const-bounded t = record
  { gap = λ () ; held-in = λ () ; held-under = λ ()
  ; fwd = λ _ _ → ⟨ (λ _ → (λ x → x) , (λ x → x)) ⟩
  ; fwd-pin = λ _ _ _ _ → (λ x → x) , (λ x → x) }

-- Cuts holding the same rows hang at the same boundaries.
bounded-≃ : ∀ {A} {c c′ : ℕ → EmissionSet A} {Bd : ℕ → Pos → Tag → Set}
          → (∀ {N k e} → c N k e → c′ N k e) → (∀ {N k e} → c′ N k e → c N k e)
          → Cuts.Bounded c Bd → Cuts.Bounded c′ Bd
bounded-≃ {c = c} {c′} to from B = record
  { gap = λ bd x → B.gap bd (from x) ; held-in = B.held-in ; held-under = B.held-under
  ; fwd = λ {N} {k} cl le → ag-≃ to from to from (B.fwd {N} {k} cl le)
  ; fwd-pin = λ {N} {q} {k} cl hc le yk → let (f , g) = B.fwd-pin {N} {q} {k} cl hc le yk in (λ x → to (f (from x))) , (λ x → to (g (from x))) }
  where module B = Cuts.Bounded B

------------------------------------------------------------------------
-- The plain program and the elaboration, settled together

module Settle {A : Set}
  (c : ℕ → EmissionSet A) (d : ℕ → EmissionSet (IE A)) (Bd Bd* : ℕ → Pos → Tag → Set)
  (B : Cuts.Bounded c Bd) (B* : Cuts.Bounded d Bd*)
  -- the closed programs' boundaries are real, and over no row
  (R : Cuts.Real c Bd) (R* : Cuts.Real d Bd*)
  (off : ∀ {N k e} → c N k e → Cuts.Off c Bd N k) (off* : ∀ {N k e} → d N k e → Cuts.Off d Bd* N k)
  (φ : ℕ → Pos → Pos) (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set)
  -- clearness corresponds at one cut
  (clear→ : ∀ {N k e} → c N k e → Unpinned e → ¬ Late N k → Cuts.Clear c Bd N k → Cuts.Clear d Bd* N (φ N k))
  (clear← : ∀ {N k e} → c N k e → Unpinned e → ¬ Late N k → Cuts.Clear d Bd* N (φ N k) → Cuts.Clear c Bd N k)
  (clear-put : ∀ {N k e l} → c N k e → Put N k l → Cuts.Clear c Bd N k → Cuts.Clear d Bd* N l)
  where
  module P = Cuts c Bd
  module E = Cuts d Bd*
  module PB = P.Bounded B
  module EB = E.Bounded B*

  settle→ : ∀ {N k e} → c N k e → Unpinned e → ¬ Late N k → P.Settled N k → E.Settled N (φ N k)
  settle→ x un nl st = EB.fwd (clear→ x un nl (P.clear R (off x) st))

  settle← : ∀ {N k e e′} → c N k e → Unpinned e → ¬ Late N k → d N (φ N k) e′ → E.Settled N (φ N k) → P.Settled N k
  settle← x un nl y st = PB.fwd (clear← x un nl (E.clear R* (off* y) st))

  -- A late skip or a pin, on its placement.
  settle-put : ∀ {N k e l} → c N k e → Put N k l → P.Settled N k → E.Settled N l
  settle-put x pl st = EB.fwd (clear-put x pl (P.clear R (off x) st))

------------------------------------------------------------------------
-- A spin

module SpinB {X : Set} (p : Pos) where

  c : ℕ → EmissionSet X
  c N = TR (S (3 + N) p)

  Bd : ℕ → Pos → Tag → Set
  Bd N b g = g ≡ free × b ≡ p ⊕ [ ix (3 + N) ]

  open Cuts c Bd

  private
    no-up : ∀ {x l} → (x ⊕ [ l ]) ⊑ x → ⊥
    no-up {x} h = ⊑-≼ h (≺-ext x [])

    tick-ne : ∀ {N i} → i < 3 + N → ¬ (p ⊕ [ ix (3 + N) ]) ≡ p ⊕ [ ix i ]
    tick-ne lt eq = <-irrefl (sym (ix-inj (step-inj p eq))) lt

  gap : ∀ {N b g y e} → Bd N b g → c N y e → ¬ y ⊑ b
  gap {N} (refl , refl) x with sp→ x
  ... | i , lt , refl , refl = down
    where
      down : ¬ (p ⊕ [ ix i ]) ⊑ (p ⊕ [ ix (3 + N) ])
      down h with ⊑-snoc p h
      ... | inj₁ h′ = no-up h′
      ... | inj₂ eq = tick-ne lt (sym eq)

  held-in : ∀ {N b q} → Bd N b (held q) → q ≺ b
  held-in (() , _)

  held-under : ∀ {N b q} → Bd N b (held q) → q ⊑ b
  held-under (() , _)

  real : Real
  real {N} (refl , refl) = p ⊕ [ ix (3 + N) ] , inj₂ (⊑-refl _) , skip , inj₂ (sp← (n<1+n (3 + N)) , nope)
    where
      nope : ¬ c N (p ⊕ [ ix (3 + N) ]) skip
      nope x with sp→ x
      ... | _ , lt , eq , _ = tick-ne lt eq

  fwd : ∀ {N k} → Clear N k → Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} yk → widen (+-monoʳ-≤ 3 le) , back yk) ⟩
    where
      back : ∀ {y e} → y ≼ k → c N′ y e → c N y e
      back yk x with sp→ x
      ... | j , _ , refl , refl = sp← (ix-back p (≼-≺-≺ {p ⊕ [ ix j ]} {k} {p ⊕ [ ix (3 + N) ]} yk (cl (refl , refl))))

  -- A spin holds no pin.
  fwd-pin : ∀ {N q k} → Clear N q → HeldClear N q k → PinSettled N q k
  fwd-pin {N} {q} {k} _ _ {N′} _ {y} _ = (λ x → none {N} {y} {q} x) , (λ x → none {N′} {y} {q} x)
    where
      none : ∀ {M y q} {Z : Set} → c M y (pin q) → Z
      none x with sp→ x
      ... | _ , _ , _ , ()

  bounded : Bounded
  bounded = record { gap = gap ; held-in = held-in ; held-under = held-under ; fwd = fwd ; fwd-pin = λ {N} {q} {k} → fwd-pin {N} {q} {k} }

------------------------------------------------------------------------
-- A takeWhile's clearness at a row, its source's at the row read

module TakeBd {A : Set} (incl : Bool) (keep : A → Bool) (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set) where

  Fl : ℕ → Pos → Set
  Fl N = TakeWhile.Failed incl keep (c N)

  -- A take keeps a boundary as it keeps the rows of its hang: a free one
  -- while no failing value precedes it, a held one while none precedes
  -- the connect.
  Keep : ℕ → Pos → Tag → Set
  Keep N b free     = ¬ Fl N b
  Keep N b (held q) = ¬ Fl N q

  Bd′ : ℕ → Pos → Tag → Set
  Bd′ N b g = Bd N b g × Keep N b g

module TakeClear {A : Set} (incl : Bool) (keep : A → Bool) (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set)
  (held-in : ∀ {N b q} → Bd N b (held q) → q ≺ b) where

  open TakeBd incl keep c Bd public

  module C = Cuts c Bd

  Clear′ : ℕ → Pos → Set
  Clear′ N k = ∀ {b g} → Bd′ N b g → k ≺ b

  failed-≼ : ∀ {N y z} → y ≼ z → Fl N y → Fl N z
  failed-≼ {y = y} {z} yz (q , a , x , nk , qy) = q , a , x , nk , ≺-≼-≺ {q} {y} {z} qy yz

  -- A boundary no failure precedes is kept.
  keep-≼ : ∀ {N b z} g → Bd N b g → ¬ Fl N z → b ≼ z → Keep N b g
  keep-≼ free     _  nF bz = λ F → nF (failed-≼ bz F)
  keep-≼ {N} {b} {z} (held q) bd nF bz = λ F → nF (failed-≼ {N} {q} {z} (≺→≼ {q} {z} (≺-≼-≺ {q} {b} {z} (held-in bd) bz)) F)

  -- At a position no failure precedes, the take's clearness is its source's.
  clear-kept : ∀ {N k} → ¬ Fl N k → Clear′ N k → C.Clear N k
  clear-kept {N} {k} nF cl {b} {g} bd with ≼-or-≻ b k
  ... | inj₂ kb = kb
  ... | inj₁ bk = cl (bd , keep-≼ g bd nF bk)

  -- Before a position past the first failing value, the source is clear
  -- at that value.
  clear-first : ∀ {N z f} → Clear′ N z → ¬ Fl N f → f ≺ z → C.Clear N f
  clear-first {N} {z} {f} cl nF fz {b} {g} bd with ≼-or-≻ b f
  ... | inj₂ fb = fb
  ... | inj₁ bf = ⊥-elim (≺-absurd {z} {b} (cl (bd , keep-≼ g bd nF bf)) (≼-≺-≺ {b} {f} {z} bf fz))

------------------------------------------------------------------------
-- A takeWhile's cuts

module TakeB {A : Set} (incl : Bool) (keep : A → Bool) (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set)
  (run : ∀ N → Run (c N))
  (failed? : ∀ N w → Dec (TakeWhile.Failed incl keep (c N) w))
  (fin : ∀ N w → Few (c N) w)
  (B : Cuts.Bounded c Bd) where

  open Take incl keep
  module CB = Cuts.Bounded B
  open TakeClear incl keep c Bd CB.held-in public

  Tk : ℕ → EmissionSet A
  Tk N = TakeWhile.TakeT incl keep (c N)

  module T = Cuts Tk Bd′

  -- Past the first failing value's completion, a take holds only pins
  -- whose connect no failure precedes.
  module Past {t : EmissionSet A} (R : Run t) where
    module W = TakeWhile incl keep t

    only-left : ∀ {y e f a} → t f (out a) → T (not (keep a)) → ¬ W.Failed f → (f ⊕ [ last ]) ≺ y → W.TakeT y e
              → Σ Pos λ q → e ≡ pin q × t y (pin q) × ¬ W.Failed q
    only-left {y} {f = f} {a} xf nk nF ly (W.pass _ _ nFy) = ⊥-elim (nFy (f , a , xf , nk , ≺-trans {f} {f ⊕ [ last ]} {y} (≺-ext f []) ly))
    only-left {y} {f = f} {a} xf nk nF ly (W.step _ nFy)   = ⊥-elim (nFy (f , a , xf , nk , ≺-trans {f} {f ⊕ [ last ]} {y} (≺-ext f []) ly))
    only-left {y} {f = f} {a} xf nk nF ly (W.tend _ nFy)   = ⊥-elim (nFy (f , a , xf , nk , ≺-trans {f} {f ⊕ [ last ]} {y} (≺-ext f []) ly))
    only-left xf nk nF ly (W.left {r = q} x nFq _) = q , refl , x , nFq
    only-left {f = f} xf nk nF ly (W.fail xo nko nFo _) with One.first-uniq R xf nk nF xo nko nFo
    ... | refl = ⊥-elim (≼-last {f} (inj₁ refl) ly)
    only-left {f = f} xf nk nF ly (W.stop xo nko nFo) with One.first-uniq R xf nk nF xo nko nFo
    ... | refl = ⊥-elim (≼-last {f} (inj₂ refl) ly)

  gap′ : ∀ {N b g y e} → Bd′ N b g → Tk N y e → ¬ y ⊑ b
  gap′ {N} {b} (bd , _) tk with One.from (run N) tk
  ... | One.self x _ = CB.gap bd x
  ... | One.new {o} x _ _ (l , refl , _) = under-child l (CB.gap bd x)

  held-in′ : ∀ {N b q} → Bd′ N b (held q) → q ≺ b
  held-in′ (bd , _) = CB.held-in bd

  held-under′ : ∀ {N b q} → Bd′ N b (held q) → q ⊑ b
  held-under′ (bd , _) = CB.held-under bd

  -- CLEAR, SO SETTLED: the source settles up to `k`, or up to the first
  -- failing value; past its completion each cut holds only pins of
  -- connects before it, which the source holds alike.
  fwd′ : ∀ {N k} → T.Clear N k → T.Settled N k
  fwd′ {N} {k} cl {N′} le with failed? N k
  ... | no nF = ⟨ (λ {y} yk → D.push1 {k} ag yk , D′.push1 {k} (AgreeTo-sym ag) yk) ⟩
    where
      module D  = Dir (run N) (run N′)
      module D′ = Dir (run N′) (run N)
      ag : AgreeTo k (c N) (c N′)
      ag = CB.fwd {N} {k} (clear-kept {N} {k} nF cl) le
  ... | yes (q , a , xq , nk , qk) with One.first (run N) (failed? N) (fin N) {q} {a} xq nk
  ...   | f , a′ , xf , nkf , nFf , fq = ⟨ at ⟩
    where
      module D  = Dir (run N) (run N′)
      module D′ = Dir (run N′) (run N)
      module P  = Past (run N)
      module P′ = Past (run N′)

      fk : f ≺ k
      fk = ≼-≺-≺ {f} {q} {k} fq qk

      cf : Cuts.Clear c Bd N f
      cf = clear-first {N} {k} {f} cl nFf fk

      ag : AgreeTo f (c N) (c N′)
      ag = CB.fwd {N} {f} cf le
      xf′ = proj₁ (upto ag (≼-refl {f})) xf
      nFf′ = D.unfail ag (≼-refl {f}) nFf

      -- The source's pins of a connect no failure precedes, up to `k`.
      pins : ∀ {r} → ¬ Fl N r → r ≼ f → C.PinSettled N r k
      pins {r} nFr rf = CB.fwd-pin {N} {r} {k} (λ {b} bd → ≼-≺-≺ {r} {f} {b} rf (cf bd)) (λ bd → cl (bd , nFr))

      past→ : ∀ {y e} → y ≼ k → (f ⊕ [ last ]) ≺ y → Tk N y e → Tk N′ y e
      past→ {y} yk ly tk with P.only-left xf nkf nFf ly tk
      ... | r , refl , x , nFr = D.W′.left x′ (D.unfail ag rf nFr) (Run.pin-in (run N′) x′)
        where
          rf : r ≼ f
          rf fr = nFr (f , a′ , xf , nkf , fr)
          x′ = proj₁ (pins nFr rf le {y} yk) x

      past← : ∀ {y e} → y ≼ k → (f ⊕ [ last ]) ≺ y → Tk N′ y e → Tk N y e
      past← {y} yk ly tk with P′.only-left xf′ nkf nFf′ ly tk
      ... | r , refl , x′ , nFr′ = D.W.left x nFr (Run.pin-in (run N) x)
        where
          rf : r ≼ f
          rf fr = nFr′ (f , a′ , xf′ , nkf , fr)
          nFr = D′.unfail (AgreeTo-sym ag) rf nFr′
          x = proj₂ (pins nFr rf le {y} yk) x′

      at : ∀ {y e} → y ≼ k → (Tk N y e → Tk N′ y e) × (Tk N′ y e → Tk N y e)
      at {y} yk with ≼-or-≻ y (f ⊕ [ last ])
      ... | inj₁ yl = D.push-fail1 ag xf nkf nFf yl , D′.push-fail1 (AgreeTo-sym ag) xf′ nkf nFf′ yl
      ... | inj₂ ly = past→ yk ly , past← yk ly

  -- A take's pins are its source's while no failure precedes their
  -- connect, and none otherwise.
  fwd-pin′ : ∀ {N q k} → T.Clear N q → T.HeldClear N q k → T.PinSettled N q k
  fwd-pin′ {N} {q} {k} cq hq {N′} le {y} yk with failed? N q
  ... | no nFq = (λ { (D.W.left x _ ins) → D.W′.left (proj₁ (ps {y} yk) x) nF′ ins })
               , (λ { (D.W′.left x′ _ ins) → D.W.left (proj₂ (ps {y} yk) x′) nFq ins })
    where
      module D = Dir (run N) (run N′)
      cs : C.Clear N q
      cs = clear-kept {N} {q} nFq cq
      ps = CB.fwd-pin {N} {q} {k} cs (λ bd → hq (bd , nFq)) le
      nF′ = D.unfail (CB.fwd {N} {q} cs le) (≼-refl {q}) nFq
  ... | yes (q₀ , a , xq , nk , q₀q) with One.first (run N) (failed? N) (fin N) {q₀} {a} xq nk
  ...   | f , a′ , xf , nkf , nFf , fq₀ = (λ { (D.W.left x nF _) → ⊥-elim (nF (q₀ , a , xq , nk , q₀q)) })
                                        , (λ { (D.W′.left x′ nF′ _) → ⊥-elim (nF′ (f , a′ , xf′ , nkf , fq)) })
    where
      module D = Dir (run N) (run N′)
      fq : f ≺ q
      fq = ≼-≺-≺ {f} {q₀} {q} fq₀ q₀q
      xf′ = proj₁ (upto (CB.fwd {N} {f} (clear-first {N} {q} {f} cq nFf fq) le) (≼-refl {f})) xf

  bounded′ : T.Bounded
  bounded′ = record { gap = gap′ ; held-in = held-in′ ; held-under = held-under′ ; fwd = fwd′ ; fwd-pin = λ {N} {q} {k} → fwd-pin′ {N} {q} {k} }

------------------------------------------------------------------------
-- A connect's cuts

-- A connect keeps a boundary as it keeps its hang's rows.
module ConnBd {A B : Set} (p : Pos) (σ : ℕ → EmissionSet A) (β : ℕ → EmissionSet B) (Bdσ Bdβ : ℕ → Pos → Tag → Set) where

  r : Pos
  r = p ⊕ [ ix 1 ]

  Cc : ℕ → EmissionSet B
  Cc N = Connecting.ConnT p (σ N) (β N)

  Al : ℕ → Pos → Set
  Al N = Connecting.Alive p (σ N) (β N)

  -- A connect keeps a boundary as it keeps its hang's rows: the body's;
  -- its source's burst, held by itself; past the burst, a free one while
  -- the body is alive there, a held one while it is alive at the connect.
  data CBd (N : ℕ) : Pos → Tag → Set where
    bodyB  : ∀ {b g} → Bdβ N b g → CBd N b g
    burstB : ∀ {b g} → Bdσ N b g → T (inside r b) → CBd N b (held p)
    echoB  : ∀ {b} → Bdσ N b free → T (not (inside r b)) → Al N b → CBd N b free
    keptB  : ∀ {b q} → Bdσ N b (held q) → T (not (inside r b)) → Al N q → CBd N b (held q)

module ConnB {A B : Set} (p : Pos) (σ : ℕ → EmissionSet A) (β : ℕ → EmissionSet B) (Bdσ Bdβ : ℕ → Pos → Tag → Set)
  (Bσ : Cuts.Bounded σ Bdσ) (Bβ : Cuts.Bounded β Bdβ)
  (σ-out : ∀ {N b g} → Bdσ N b g → b ≺ p ⊎ (p ⊕ [ ix 1 ]) ≺ b)
  (σ-held : ∀ {N b q} → Bdσ N b (held q) → T (inside (p ⊕ [ ix 1 ]) b) → (p ⊕ [ ix 1 ]) ≼ q)
  (β-after : ∀ {N c} → β N c end → p ≺ c)
  where

  open ConnBd p σ β Bdσ Bdβ public

  module Sσ = Cuts σ Bdσ
  module Sβ = Cuts β Bdβ
  module SC = Cuts Cc CBd
  module BS = Sσ.Bounded Bσ
  module BB = Sβ.Bounded Bβ

  held-in : ∀ {N b q} → CBd N b (held q) → q ≺ b
  held-in {N} {b} (bodyB bd)       = BB.held-in {N} {b} bd
  held-in {N} {b} (burstB _ ins)   = ≺-≼-≺ {p} {r} {b} (≺-ext p []) (⊑-≼ (inside-⊑ r b ins))
  held-in {N} {b} (keptB bd _ _)   = BS.held-in {N} {b} bd

  held-under : ∀ {N b q} → CBd N b (held q) → q ⊑ b
  held-under {N} {b} (bodyB bd)       = BB.held-under {N} {b} bd
  held-under {N} {b} (burstB _ ins)   = ⊑-trans {p} {r} {b} ([ ix 1 ] , refl) (inside-⊑ r b ins)
  held-under {N} {b} (keptB bd _ _)   = BS.held-under {N} {b} bd

  alive-down : ∀ {N z w} → w ≼ z → Al N z → Al N w
  alive-down {z = z} {w = w} wz al {c} x = ≼-≺-≺ {w} {z} {c} wz (al x)

  -- Two cuts whose bodies agree up to `w` find the body alive alike.
  alive→ : ∀ {N N′ w z} → AgreeTo w (β N) (β N′) → z ≼ w → Al N z → Al N′ z
  alive→ {w = w} {z} ag zw al {c} x with ≼-or-≻ c w
  ... | inj₁ cw = al (proj₂ (upto ag {c} {end} cw) x)
  ... | inj₂ wc = ≼-≺-≺ {z} {w} {c} zw wc

  alive← : ∀ {N N′ w z} → AgreeTo w (β N) (β N′) → z ≼ w → Al N′ z → Al N z
  alive← {w = w} {z} ag zw al {c} x with ≼-or-≻ c w
  ... | inj₁ cw = al (proj₁ (upto ag {c} {end} cw) x)
  ... | inj₂ wc = ≼-≺-≺ {z} {w} {c} zw wc

  not-burst : ∀ {b} → b ≺ p → T (not (inside r b))
  not-burst {b} bp = not-T (λ ins → ≺-absurd {b} {p} bp (≺-≼-≺ {p} {r} {b} (≺-ext p []) (⊑-≼ (inside-⊑ r b ins))))

  alive-early : ∀ {N z} → z ≺ p → Al N z
  alive-early {N} {z} zp x = ≺-trans {z} {p} zp (β-after x)

  -- A source boundary before the connect is the connect's: the body,
  -- subscribed past it, is alive there.
  early : ∀ {N b g} → Bdσ N b g → b ≺ p → Σ Tag (CBd N b)
  early {N} {b} {free}   bd bp = free , echoB bd (not-burst bp) (alive-early {N} {b} bp)
  early {N} {b} {held q} bd bp = held q , keptB bd (not-burst bp) (alive-early {N} {q} (≺-trans {q} {b} {p} (BS.held-in {N} {b} {q} bd) bp))

  -- Where the body is alive, the source is clear wherever the connect is.
  src-clear : ∀ {N z} → (∀ {b g} → CBd N b g → z ≺ b) → Al N z → Sσ.Clear N z
  src-clear {N} {z} H al {b} {g} bd with ≼-or-≻ b z
  ... | inj₂ zb = zb
  ... | inj₁ bz = ⊥-elim (bz (H (proj₂ (lift g bd))))
    where
      lift : ∀ g → Bdσ N b g → Σ Tag (CBd N b)
      lift free bd′ with T? (inside r b)
      ... | yes ins  = held p , burstB bd′ ins
      ... | no nins  = free , echoB bd′ (not-T nins) (alive-down {N} {z} {b} bz al)
      lift (held q) bd′ with T? (inside r b)
      ... | yes ins  = held p , burstB bd′ ins
      ... | no nins  = held q , keptB bd′ (not-T nins) (alive-down {N} {z} {q} (≺→≼ {q} {z} (≺-≼-≺ {q} {b} {z} (BS.held-in {N} {b} {q} bd′) bz)) al)

  -- In the burst, the source is clear wherever no burst boundary is and
  -- no boundary before the connect.
  src-burst : ∀ {N z} → (∀ {b g} → Bdσ N b g → T (inside r b) → z ≺ b) → (∀ {b g} → Bdσ N b g → b ≺ p → z ≺ b) → T (inside r z) → Sσ.Clear N z
  src-burst {N} {z} H E insz {b} {g} bd with ≼-or-≻ b z
  ... | inj₂ zb = zb
  ... | inj₁ bz with T? (inside r b)
  ...   | yes ins = ⊥-elim (bz (H {b} {g} bd ins))
  ...   | no nins with σ-out {N} {b} {g} bd
  ...     | inj₁ bp = ⊥-elim (bz (E {b} {g} bd bp))
  ...     | inj₂ rb = past-sub (inside-⊑ r z insz) (≺→≼ {r} {b} rb) (λ h → nins (⊑-inside h))

  -- CLEAR, SO SETTLED: the body by its own; each source row shown by the
  -- source clear there, or its pins clear.
  fwd : ∀ {N k} → SC.Clear N k → SC.Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} yk → to yk , from yk) ⟩
    where
      agβ : AgreeTo k (β N) (β N′)
      agβ = BB.fwd {N} {k} (λ bd → cl (bodyB bd)) le

      below : ∀ {z} → z ≺ k → ∀ {b g} → CBd N b g → z ≺ b
      below {z} zk {b} bd = ≺-trans {z} {k} {b} zk (cl bd)

      burst-ag : ∀ {k₀} → k₀ ≺ k → T (inside r k₀) → AgreeTo k₀ (σ N) (σ N′)
      burst-ag {k₀} k0k ins = BS.fwd {N} {k₀} (src-burst {N} {k₀} (λ {b} bd ins′ → ≺-trans {k₀} {k} {b} k0k (cl (burstB bd ins′)))
        (λ {b} {g} bd bp → ≺-trans {k₀} {k} {b} k0k (cl (proj₂ (early {N} {b} {g} bd bp)))) ins) le

      held-all : ∀ {q} → Al N q → Sσ.HeldClear N q k
      held-all al {b} bd with T? (inside r b)
      ... | yes ins = cl (burstB bd ins)
      ... | no nins = cl (keptB bd (not-T nins) al)

      kept-ag : ∀ {q} → q ≺ k → Al N q → Sσ.PinAgree q k (σ N) (σ N′)
      kept-ag {q} qk al = BS.fwd-pin {N} {q} {k} (src-clear {N} {q} (below {q} qk) al) (held-all {q} al) le

      src-ag : ∀ {k₀} → k₀ ≺ k → Al N k₀ → AgreeTo k₀ (σ N) (σ N′)
      src-ag {k₀} k0k al = BS.fwd {N} {k₀} (src-clear {N} {k₀} (below {k₀} k0k) al) le

      step : ∀ {k₀} → (k₀ ⊕ [ ix 0 ]) ≼ k → k₀ ≺ k
      step {k₀} yk = ≺-≼-≺ {k₀} {k₀ ⊕ [ ix 0 ]} {k} (≺-ext k₀ []) yk

      to : ∀ {y e} → y ≼ k → Cc N y e → Cc N′ y e
      to yk (Connecting.body x) = Connecting.body (proj₁ (upto agβ yk) x)
      to yk (Connecting.burst {k₀} x ins) = Connecting.burst (proj₁ (upto (burst-ag {k₀} (step {k₀} yk) ins) (≼-refl {k₀})) x) ins
      to yk (Connecting.echo {k₀} x al un nins) =
        Connecting.echo (proj₁ (upto (src-ag {k₀} (step {k₀} yk) al) (≼-refl {k₀})) x) (alive→ {N} {N′} {k} {k₀} agβ (≺→≼ {k₀} {k} (step {k₀} yk)) al) un nins
      to yk (Connecting.kept {k₀} {q} x al nins ins) =
        Connecting.kept (proj₁ (kept-ag {q} qk al {k₀} (≺→≼ {k₀} {k} (step {k₀} yk))) x) (alive→ {N} {N′} {k} {q} agβ (≺→≼ {q} {k} qk) al) nins ins
        where
          qk : q ≺ k
          qk = ≼-≺-≺ {q} {k₀} {k} (⊑-≼ (inside-⊑ q k₀ ins)) (step {k₀} yk)

      from : ∀ {y e} → y ≼ k → Cc N′ y e → Cc N y e
      from yk (Connecting.body x) = Connecting.body (proj₂ (upto agβ yk) x)
      from yk (Connecting.burst {k₀} x ins) = Connecting.burst (proj₂ (upto (burst-ag {k₀} (step {k₀} yk) ins) (≼-refl {k₀})) x) ins
      from yk (Connecting.echo {k₀} x al′ un nins) =
        Connecting.echo (proj₂ (upto (src-ag {k₀} (step {k₀} yk) al) (≼-refl {k₀})) x) al un nins
        where
          al = alive← {N} {N′} {k} {k₀} agβ (≺→≼ {k₀} {k} (step {k₀} yk)) al′
      from yk (Connecting.kept {k₀} {q} x al′ nins ins) =
        Connecting.kept (proj₂ (kept-ag {q} qk al {k₀} (≺→≼ {k₀} {k} (step {k₀} yk))) x) al nins ins
        where
          qk : q ≺ k
          qk = ≼-≺-≺ {q} {k₀} {k} (⊑-≼ (inside-⊑ q k₀ ins)) (step {k₀} yk)
          al = alive← {N} {N′} {k} {q} agβ (≺→≼ {q} {k} qk) al′

  -- A held source boundary in the burst waits on a connect in the burst,
  -- whose pins the connect shows as its own.
  src-held : ∀ {N q k k₀} → SC.HeldClear N q k → Al N q → T (not (inside r k₀)) → T (inside q k₀) → Sσ.HeldClear N q k
  src-held {N} {q} {k} {k₀} hq al nins ins {b} bd with T? (inside r b)
  ... | no nins′ = hq (keptB bd (not-T nins′) al)
  ... | yes insb = ⊥-elim (T-not nins (⊑-inside (⊑-trans rq (inside-⊑ q k₀ ins))))
    where
      rq : r ⊑ q
      rq = sub-between (inside-⊑ r b insb) (σ-held {N} {b} {q} bd insb) (≺→≼ {q} {b} (BS.held-in {N} {b} {q} bd))

  -- PINS OF `q` SETTLE: the body's by its own, the burst's by the source
  -- clear there, a kept one by the source's pins of `q`.
  module PinStep {N N′ : ℕ} (le : N ≤ N′) where
    burst-ag : ∀ {k k₀} → SC.Clear N p → SC.HeldClear N p k → (k₀ ⊕ [ ix 0 ]) ≼ k → T (inside r k₀) → AgreeTo k₀ (σ N) (σ N′)
    burst-ag {k} {k₀} cp hq yk ins = BS.fwd {N} {k₀} (src-burst {N} {k₀} (λ {b} bd ins′ → ≺-trans {k₀} {k} {b} k0k (hq (burstB bd ins′)))
      (λ {b} {g} bd bp → ⊥-elim (≺-absurd {b} {p} bp (cp (proj₂ (early {N} {b} {g} bd bp))))) ins) le
      where
        k0k : k₀ ≺ k
        k0k = ≺-≼-≺ {k₀} {k₀ ⊕ [ ix 0 ]} {k} (≺-ext k₀ []) yk

    kept-ag : ∀ {q k k₀} → SC.Clear N q → SC.HeldClear N q k → Al N q → T (not (inside r k₀)) → T (inside q k₀) → Sσ.PinAgree q k (σ N) (σ N′)
    kept-ag {q} {k} {k₀} cq hq al nins ins = BS.fwd-pin {N} {q} {k} (src-clear {N} {q} cq al) (src-held {N} {q} {k} {k₀} hq al nins ins) le

    body-ag : ∀ {q k} → SC.Clear N q → SC.HeldClear N q k → Sβ.PinAgree q k (β N) (β N′)
    body-ag {q} {k} cq hq = BB.fwd-pin {N} {q} {k} (λ bd → cq (bodyB bd)) (λ bd → hq (bodyB bd)) le

    agβq : ∀ {q} → SC.Clear N q → AgreeTo q (β N) (β N′)
    agβq {q} cq = BB.fwd {N} {q} (λ bd → cq (bodyB bd)) le

    pin-to : ∀ {q k y} → SC.Clear N q → SC.HeldClear N q k → y ≼ k → Cc N y (pin q) → Cc N′ y (pin q)
    pin-to {q} {k} cq hq yk (Connecting.body x) = Connecting.body (proj₁ (body-ag {q} {k} cq hq yk) x)
    pin-to {k = k} cq hq yk (Connecting.burst {k₀} x ins) = Connecting.burst (proj₁ (upto (burst-ag {k} {k₀} cq hq yk ins) (≼-refl {k₀})) x) ins
    pin-to {q} {k} cq hq yk (Connecting.kept {k₀} x al nins ins) =
      Connecting.kept (proj₁ (kept-ag {q} {k} {k₀} cq hq al nins ins {k₀} (≺→≼ {k₀} {k} (≺-≼-≺ {k₀} {k₀ ⊕ [ ix 0 ]} {k} (≺-ext k₀ []) yk))) x)
        (alive→ {N} {N′} {q} {q} (agβq {q} cq) (≼-refl {q}) al) nins ins

    pin-from : ∀ {q k y} → SC.Clear N q → SC.HeldClear N q k → y ≼ k → Cc N′ y (pin q) → Cc N y (pin q)
    pin-from {q} {k} cq hq yk (Connecting.body x) = Connecting.body (proj₂ (body-ag {q} {k} cq hq yk) x)
    pin-from {k = k} cq hq yk (Connecting.burst {k₀} x ins) = Connecting.burst (proj₂ (upto (burst-ag {k} {k₀} cq hq yk ins) (≼-refl {k₀})) x) ins
    pin-from {q} {k} cq hq yk (Connecting.kept {k₀} x al′ nins ins) =
      Connecting.kept (proj₂ (kept-ag {q} {k} {k₀} cq hq al nins ins {k₀} (≺→≼ {k₀} {k} (≺-≼-≺ {k₀} {k₀ ⊕ [ ix 0 ]} {k} (≺-ext k₀ []) yk))) x) al nins ins
      where
        al = alive← {N} {N′} {q} {q} (agβq {q} cq) (≼-refl {q}) al′

  fwd-pin : ∀ {N q k} → SC.Clear N q → SC.HeldClear N q k → SC.PinSettled N q k
  fwd-pin {N} {q} {k} cq hq {N′} le {y} yk = PinStep.pin-to le {q} {k} {y} cq hq yk , PinStep.pin-from le {q} {k} {y} cq hq yk

  postulate
    gap-c  : ∀ {N b g y e} → CBd N b g → Cc N y e → ¬ y ⊑ b

  bounded : SC.Bounded
  bounded = record { gap = gap-c ; held-in = held-in ; held-under = held-under ; fwd = fwd ; fwd-pin = λ {N} {q} {k} → fwd-pin {N} {q} {k} }

------------------------------------------------------------------------
-- A lane reading a hot

-- A reader subscribed at `s` keeps every boundary of the hot with its
-- tag: the hot's pins are skips to it, but a held hang sits in a call
-- the reader cannot interrupt.  The hot's boundaries lie in its own
-- world, led by no reader's late end.
module RejoinB {A : Set} (s : Pos) (h : ℕ → EmissionSet A) (Bdh : ℕ → Pos → Tag → Set) (Bh : Cuts.Bounded h Bdh)
  (apart-s : ∀ {N b g} → Bdh N b g → ¬ (s ⊕ [ last ]) ⊑ b)
  where

  J : ℕ → EmissionSet A
  J N = Rejoin s (h N)

  JBd : ℕ → Pos → Tag → Set
  JBd = Bdh

  under : ∀ {b q} → ¬ q ⊑ b → ¬ (q ⊕ [ sub s ]) ⊑ b
  under = under-child (sub s)

  module H  = Cuts h Bdh
  module SJ = Cuts J JBd
  module BH = H.Bounded Bh

  -- A hot row leads no boundary.
  gap-j : ∀ {N b g y e} → JBd N b g → J N y e → ¬ y ⊑ b
  gap-j bd (shown x _ _) = under (BH.gap bd x)
  gap-j bd (heard x _)   = under (BH.gap bd x)
  gap-j bd (ended x _)   = under (BH.gap bd x)
  gap-j bd (late _ _)    = apart-s bd

  held-in-j : ∀ {N b q} → JBd N b (held q) → q ≺ b
  held-in-j {N} {b} {q} = BH.held-in {N} {b} {q}

  held-under-j : ∀ {N b q} → JBd N b (held q) → q ⊑ b
  held-under-j {N} {b} {q} = BH.held-under {N} {b} {q}

  -- CLEAR, SO SETTLED: a row shown at `q ⊕ [ sub s ]` reads the hot up to
  -- `q`, and a late end up to `s`; every hot boundary lies past both.
  fwd-j : ∀ {N k} → SJ.Clear N k → SJ.Settled N k
  fwd-j {N} {k} cl {N′} le = ⟨ (λ {y} yk → to yk , from yk) ⟩
    where
      hot-clear : ∀ {z} → z ≺ k → H.Clear N z
      hot-clear {z} zk {b} {g} bd with ≼-or-≻ b z
      ... | inj₂ zb = zb
      ... | inj₁ bz = ⊥-elim (≺-absurd {k} {b} (cl {b} {g} bd) (≼-≺-≺ {b} {z} {k} bz zk))

      ag : ∀ {z} → z ≺ k → AgreeTo z (h N) (h N′)
      ag {z} zk = BH.fwd {N} {z} (hot-clear {z} zk) le

      sub≺ : ∀ {q} → (q ⊕ [ sub s ]) ≼ k → q ≺ k
      sub≺ {q} yk = ≺-≼-≺ {q} {q ⊕ [ sub s ]} {k} (≺-ext q []) yk

      last≺ : (s ⊕ [ last ]) ≼ k → s ≺ k
      last≺ yk = ≺-≼-≺ {s} {s ⊕ [ last ]} {k} (≺-ext s []) yk

      to : ∀ {y e} → y ≼ k → J N y e → J N′ y e
      to yk (shown {q} x bare sq) = shown (proj₁ (upto (ag {q} (sub≺ {q} yk)) (≼-refl {q})) x) bare sq
      to yk (heard {q} x sq)      = heard (proj₁ (upto (ag {q} (sub≺ {q} yk)) (≼-refl {q})) x) sq
      to yk (ended {c} x sc)      = ended (proj₁ (upto (ag {c} (sub≺ {c} yk)) (≼-refl {c})) x) sc
      to yk (late {c} x cs)       = late (proj₁ (upto (ag {s} (last≺ yk)) {c} {end} cs) x) cs

      from : ∀ {y e} → y ≼ k → J N′ y e → J N y e
      from yk (shown {q} x bare sq) = shown (proj₂ (upto (ag {q} (sub≺ {q} yk)) (≼-refl {q})) x) bare sq
      from yk (heard {q} x sq)      = heard (proj₂ (upto (ag {q} (sub≺ {q} yk)) (≼-refl {q})) x) sq
      from yk (ended {c} x sc)      = ended (proj₂ (upto (ag {c} (sub≺ {c} yk)) (≼-refl {c})) x) sc
      from yk (late {c} x cs)       = late (proj₂ (upto (ag {s} (last≺ yk)) {c} {end} cs) x) cs

  -- A reader holds no pin.
  fwd-pin-j : ∀ {N q k} → SJ.Clear N q → SJ.HeldClear N q k → SJ.PinSettled N q k
  fwd-pin-j {N} {q} {k} _ _ {N′} _ {y} _ = none {N} {N′} , none {N′} {N}
    where
      none : ∀ {M M′} → J M y (pin q) → J M′ y (pin q)
      none (shown _ () _)

  bounded-j : SJ.Bounded
  bounded-j = record { gap = gap-j ; held-in = λ {N} {b} {q} → held-in-j {N} {b} {q} ; held-under = λ {N} {b} {q} → held-under-j {N} {b} {q} ; fwd = fwd-j ; fwd-pin = λ {N} {q} {k} → fwd-pin-j {N} {q} {k} }
