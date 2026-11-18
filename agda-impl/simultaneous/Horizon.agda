{-# OPTIONS --guardedness #-}

-- WHERE A CUT STOPS BEING THE RUN, READ OFF ONE CUT.  Each former's cut
-- at `N` has BOUNDARIES (`Bd N`): positions where a hang's rows were cut
-- short, kept only while the former still reads past them.  A cut is
-- settled up to `k` (agrees with every deeper cut) when `k` lies before
-- every boundary (`Cuts.Bounded.fwd`), and only then, off them
-- (`Cuts.Bounded.clear`): a boundary has a row one cut deeper at or
-- before its last descendant (`Cuts.Bounded.real`), and no row of its own
-- cut at or under it (`Cuts.Bounded.gap`).  All three are facts of one
-- program's cuts, so the plain program and the elaboration share them.
--
-- THE ELABORATION HANGS WHERE THE PLAIN PROGRAM DOES (`Settle`): a plain
-- row and its image are settled together once their CLEARNESS
-- corresponds at one cut (`Settle.settle→`, `Settle.settle←`).  Nothing
-- decides where a hang is; clearness is `≺` against each boundary.
--
-- A HANG HIDDEN BEHIND A TAKEWHILE.  A take keeps its source's
-- boundaries only where no failing value precedes them (`TakeB.Bd′`), so
-- a hang past the failure makes no row of anything above it unsettled.
-- The take's cuts settle by its source's (`TakeB.fwd′`), and its
-- clearness at a row is its source's at the row read (`TakeClear`).  So
-- a take's correspondence is its source's (`TakeLayer`), at one cut.
--
-- A spin's last row is short of the next cut's (`SpinB`).
module simultaneous.Horizon where

open import Data.Bool using (Bool; T; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Nat using (ℕ; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties using (n≤1+n; n<1+n; <-irrefl; +-monoʳ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import denotation.Position using (Pos; root; _≟ᵖ_; inside; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; skip; pin; Unpinned; EmissionSet; Few; _≺_; _≼_; module TakeWhile)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; ≺-ext; ≺-trans; ≺-absurd; ≼-refl; ≺→≼; ≼-trans; ≼-split;
  ≼-or-≻; ≼-≺-≺; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_; ⊑-refl; ⊑-snoc⁺; ⊑-trans; ⊑-≼; ⊑-snoc; ⊑-inside; inside-⊑)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.TableCorr using (TR)
open import simultaneous.TableSpin using (S; sp→; sp←; step-inj; ix-inj; widen)
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

------------------------------------------------------------------------
-- One program's cuts

module Cuts {A : Set} (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Set) where

  -- Every deeper cut agrees up to `k`.
  Settled : ℕ → Pos → Set
  Settled N k = ∀ {N′} → N ≤ N′ → AgreeTo k (c N) (c N′)

  -- Before every boundary.
  Clear : ℕ → Pos → Set
  Clear N k = ∀ {b} → Bd N b → k ≺ b

  -- Under no boundary.
  Off : ℕ → Pos → Set
  Off N k = ∀ {b} → Bd N b → ¬ b ⊑ k

  -- A row one of two consecutive cuts holds and the other does not.
  Diff : ℕ → Pos → Set
  Diff N y = Σ (Ev A) λ e → (c N y e × ¬ c (suc N) y e) ⊎ (c (suc N) y e × ¬ c N y e)

  -- At or before a boundary's last descendant.
  Near : Pos → Pos → Set
  Near b y = y ≼ b ⊎ b ⊑ y

  record Bounded : Set where
    field
      gap  : ∀ {N b y e} → Bd N b → c N y e → ¬ b ⊑ y × ¬ y ⊑ b
      real : ∀ {N b} → Bd N b → Σ Pos λ y → Near b y × Diff N y
      fwd  : ∀ {N k} → Clear N k → Settled N k

    off-row : ∀ {N k e} → c N k e → Off N k
    off-row x bd = proj₁ (gap bd x)

    -- SETTLED, SO CLEAR: a boundary at or before `k` has a row one cut
    -- deeper before `k`, which a settled cut would hold.
    near-≼ : ∀ {b k y} → Near b y → b ≼ k → ¬ b ⊑ k → y ≼ k
    near-≼ {b} {k} {y} (inj₁ yb) bk _  = ≼-trans {y} {b} {k} yb bk
    near-≼ {b} {k} {y} (inj₂ by) bk nb = ≺→≼ {y} {k} (past-sub by bk nb)

    clear : ∀ {N k} → Off N k → Settled N k → Clear N k
    clear {N} {k} off st {b} bd with ≼-or-≻ b k
    ... | inj₂ kb = kb
    ... | inj₁ bk with real bd
    ...   | y , near , e , d = ⊥-elim (gone d)
      where
        yk : y ≼ k
        yk = near-≼ near bk (off bd)

        gone : (c N y e × ¬ c (suc N) y e) ⊎ (c (suc N) y e × ¬ c N y e) → ⊥
        gone (inj₁ (x , nx)) = nx (proj₁ (upto (st (n≤1+n N)) {y} {e} yk) x)
        gone (inj₂ (x , nx)) = nx (proj₂ (upto (st (n≤1+n N)) {y} {e} yk) x)

------------------------------------------------------------------------
-- The plain program and the elaboration, settled together

module Settle {A : Set}
  (c : ℕ → EmissionSet A) (d : ℕ → EmissionSet (IE A)) (Bd Bd* : ℕ → Pos → Set)
  (B : Cuts.Bounded c Bd) (B* : Cuts.Bounded d Bd*)
  (φ : ℕ → Pos → Pos) (Put : ℕ → Pos → Pos → Set) (Late : ℕ → Pos → Set)
  -- clearness corresponds at one cut
  (clear→ : ∀ {N k e} → c N k e → Unpinned e → ¬ Late N k → Cuts.Clear c Bd N k → Cuts.Clear d Bd* N (φ N k))
  (clear← : ∀ {N k e} → c N k e → Unpinned e → ¬ Late N k → Cuts.Clear d Bd* N (φ N k) → Cuts.Clear c Bd N k)
  (clear-put : ∀ {N k l} → c N k skip → Put N k l → Cuts.Clear c Bd N k → Cuts.Clear d Bd* N l)
  where
  module P = Cuts c Bd
  module E = Cuts d Bd*
  module PB = P.Bounded B
  module EB = E.Bounded B*

  settle→ : ∀ {N k e} → c N k e → Unpinned e → ¬ Late N k → P.Settled N k → E.Settled N (φ N k)
  settle→ x un nl st = EB.fwd (clear→ x un nl (PB.clear (PB.off-row x) st))

  settle← : ∀ {N k e e′} → c N k e → Unpinned e → ¬ Late N k → d N (φ N k) e′ → E.Settled N (φ N k) → P.Settled N k
  settle← x un nl y st = PB.fwd (clear← x un nl (EB.clear (EB.off-row y) st))

  settle-put : ∀ {N k l} → c N k skip → Put N k l → P.Settled N k → E.Settled N l
  settle-put x pl st = EB.fwd (clear-put x pl (PB.clear (PB.off-row x) st))

------------------------------------------------------------------------
-- A spin

module SpinB {X : Set} (p : Pos) where

  c : ℕ → EmissionSet X
  c N = TR (S (3 + N) p)

  Bd : ℕ → Pos → Set
  Bd N b = b ≡ p ⊕ [ ix (3 + N) ]

  open Cuts c Bd

  private
    no-up : ∀ {x l} → (x ⊕ [ l ]) ⊑ x → ⊥
    no-up {x} h = ⊑-≼ h (≺-ext x [])

    tick-ne : ∀ {N i} → i < 3 + N → ¬ (p ⊕ [ ix (3 + N) ]) ≡ p ⊕ [ ix i ]
    tick-ne lt eq = <-irrefl (sym (ix-inj (step-inj p eq))) lt

  gap : ∀ {N b y e} → Bd N b → c N y e → ¬ b ⊑ y × ¬ y ⊑ b
  gap {N} refl x with sp→ x
  ... | i , lt , refl , refl = up , down
    where
      up : ¬ (p ⊕ [ ix (3 + N) ]) ⊑ (p ⊕ [ ix i ])
      up h with ⊑-snoc p h
      ... | inj₁ h′ = no-up h′
      ... | inj₂ eq = tick-ne lt eq

      down : ¬ (p ⊕ [ ix i ]) ⊑ (p ⊕ [ ix (3 + N) ])
      down h with ⊑-snoc p h
      ... | inj₁ h′ = no-up h′
      ... | inj₂ eq = tick-ne lt (sym eq)

  real : ∀ {N b} → Bd N b → Σ Pos λ y → Near b y × Diff N y
  real {N} refl = p ⊕ [ ix (3 + N) ] , inj₂ (⊑-refl _) , skip , inj₂ (sp← (n<1+n (3 + N)) , nope)
    where
      nope : ¬ c N (p ⊕ [ ix (3 + N) ]) skip
      nope x with sp→ x
      ... | _ , lt , eq , _ = tick-ne lt eq

  fwd : ∀ {N k} → Clear N k → Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} yk → widen (+-monoʳ-≤ 3 le) , back yk) ⟩
    where
      back : ∀ {y e} → y ≼ k → c N′ y e → c N y e
      back yk x with sp→ x
      ... | j , _ , refl , refl = sp← (ix-back p (≼-≺-≺ {p ⊕ [ ix j ]} {k} {p ⊕ [ ix (3 + N) ]} yk (cl refl)))

  bounded : Bounded
  bounded = record { gap = gap ; real = real ; fwd = fwd }

------------------------------------------------------------------------
-- A takeWhile's clearness at a row, its source's at the row read

module TakeClear {A : Set} (incl : Bool) (keep : A → Bool) (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Set)
  (gap : ∀ {N b y e} → Bd N b → c N y e → ¬ b ⊑ y × ¬ y ⊑ b) where

  Fl : ℕ → Pos → Set
  Fl N = TakeWhile.Failed incl keep (c N)

  -- A source boundary no failing value precedes.
  Bd′ : ℕ → Pos → Set
  Bd′ N b = Bd N b × ¬ Fl N b

  module C = Cuts c Bd

  Clear′ : ℕ → Pos → Set
  Clear′ N k = ∀ {b} → Bd′ N b → k ≺ b

  failed-≼ : ∀ {N y z} → y ≼ z → Fl N y → Fl N z
  failed-≼ {y = y} {z} yz (q , a , x , nk , qy) = q , a , x , nk , ≺-≼-≺ {q} {y} {z} qy yz

  -- At a position no failure precedes, the take's clearness is its source's.
  clear-kept : ∀ {N k} → ¬ Fl N k → Clear′ N k → C.Clear N k
  clear-kept {N} {k} nF cl {b} bd with ≼-or-≻ b k
  ... | inj₂ kb = kb
  ... | inj₁ bk = cl (bd , λ F → nF (failed-≼ bk F))

  kept-clear : ∀ {N k} → C.Clear N k → Clear′ N k
  kept-clear cl (bd , _) = cl bd

  -- Under the first failing value, the take's clearness is its source's there.
  clear-made : ∀ {N o} l → ¬ Fl N o → Clear′ N (o ⊕ [ l ]) → C.Clear N o
  clear-made {N} {o} l nF cl {b} bd with ≼-or-≻ b o
  ... | inj₂ ob = ob
  ... | inj₁ bo = ⊥-elim (≺-absurd {o ⊕ [ l ]} {b} (cl (bd , λ F → nF (failed-≼ bo F))) (≼-≺-≺ {b} {o} {o ⊕ [ l ]} bo (≺-ext o [])))

  made-clear : ∀ {N o e} l → c N o e → C.Clear N o → Clear′ N (o ⊕ [ l ])
  made-clear l x cl (bd , _) = past-child l (cl bd) (proj₂ (gap bd x))

------------------------------------------------------------------------
-- A takeWhile's cuts

module TakeB {A : Set} (incl : Bool) (keep : A → Bool) (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Set)
  (run : ∀ N → Run (c N))
  (nopin : ∀ {N y r} → ¬ c N y (pin r))
  (failed? : ∀ N w → Dec (TakeWhile.Failed incl keep (c N) w))
  (fin : ∀ N w → Few (c N) w)
  (B : Cuts.Bounded c Bd) where

  open Take incl keep
  module CB = Cuts.Bounded B
  open TakeClear incl keep c Bd CB.gap public

  Tk : ℕ → EmissionSet A
  Tk N = TakeWhile.TakeT incl keep (c N)

  module T = Cuts Tk Bd′

  -- Past the first failing value's completion, a take holds nothing.
  module Past {t : EmissionSet A} (R : Run t) (nopin′ : ∀ {y r} → ¬ t y (pin r)) where
    module W = TakeWhile incl keep t

    none-past : ∀ {y e f a} → t f (out a) → T (not (keep a)) → ¬ W.Failed f → (f ⊕ [ last ]) ≺ y → ¬ W.TakeT y e
    none-past {y} {f = f} {a} xf nk nF ly (W.pass _ _ nFy) = nFy (f , a , xf , nk , ≺-trans {f} {f ⊕ [ last ]} {y} (≺-ext f []) ly)
    none-past {y} {f = f} {a} xf nk nF ly (W.step _ nFy)   = nFy (f , a , xf , nk , ≺-trans {f} {f ⊕ [ last ]} {y} (≺-ext f []) ly)
    none-past {y} {f = f} {a} xf nk nF ly (W.tend _ nFy)   = nFy (f , a , xf , nk , ≺-trans {f} {f ⊕ [ last ]} {y} (≺-ext f []) ly)
    none-past xf nk nF ly (W.left x _ _) = nopin′ x
    none-past {f = f} xf nk nF ly (W.fail xo nko nFo _) with One.first-uniq R xf nk nF xo nko nFo
    ... | refl = ≼-last {f} (inj₁ refl) ly
    none-past {f = f} xf nk nF ly (W.stop xo nko nFo) with One.first-uniq R xf nk nF xo nko nFo
    ... | refl = ≼-last {f} (inj₂ refl) ly

  gap′ : ∀ {N b y e} → Bd′ N b → Tk N y e → ¬ b ⊑ y × ¬ y ⊑ b
  gap′ {N} {b} (bd , _) tk with One.from (run N) tk
  ... | One.self x _ = CB.gap bd x
  ... | One.new {o} x _ _ (l , refl , _) = up , down
    where
      up : ¬ b ⊑ (o ⊕ [ l ])
      up h with ⊑-snoc o h
      ... | inj₁ h′ = proj₁ (CB.gap bd x) h′
      ... | inj₂ eq = proj₂ (CB.gap bd x) (subst (o ⊑_) (sym eq) (⊑-snoc⁺ o))

      down : ¬ (o ⊕ [ l ]) ⊑ b
      down h = proj₂ (CB.gap bd x) (⊑-trans (⊑-snoc⁺ o) h)

  -- CLEAR, SO SETTLED: the source settles up to `k`, or up to the first
  -- failing value, past whose completion neither cut holds anything.
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
      module P  = Past (run N) nopin
      module P′ = Past (run N′) nopin

      fk : f ≺ k
      fk = ≼-≺-≺ {f} {q} {k} fq qk

      cf : Cuts.Clear c Bd N f
      cf {b} bd with ≼-or-≻ b f
      ... | inj₂ fb = fb
      ... | inj₁ bf = ⊥-elim (≺-absurd {k} {b} (cl (bd , λ F → nFf (failed-≼ {N} {b} {f} bf F))) (≼-≺-≺ {b} {f} {k} bf fk))

      ag = CB.fwd cf le
      xf′ = proj₁ (upto ag (≼-refl {f})) xf
      nFf′ = D.unfail ag (≼-refl {f}) nFf

      at : ∀ {y e} → y ≼ k → (Tk N y e → Tk N′ y e) × (Tk N′ y e → Tk N y e)
      at {y} yk with ≼-or-≻ y (f ⊕ [ last ])
      ... | inj₁ yl = D.push-fail1 ag xf nkf nFf yl , D′.push-fail1 (AgreeTo-sym ag) xf′ nkf nFf′ yl
      ... | inj₂ ly = (λ tk → ⊥-elim (P.none-past xf nkf nFf ly tk)) , (λ tk → ⊥-elim (P′.none-past xf′ nkf nFf′ ly tk))

  postulate
    real′ : ∀ {N b} → Bd′ N b → Σ Pos λ y → T.Near b y × T.Diff N y

  bounded′ : T.Bounded
  bounded′ = record { gap = gap′ ; real = real′ ; fwd = fwd′ }

------------------------------------------------------------------------
-- A takeWhile's correspondence is its source's

module TakeLayer {A X : Set} (incl : Bool) (keep : A → Bool) (keep* : X → Bool)
  (c : ℕ → EmissionSet A) (d : ℕ → EmissionSet X) (Bd Bd* : ℕ → Pos → Set)
  (gap : ∀ {N b y e} → Bd N b → c N y e → ¬ b ⊑ y × ¬ y ⊑ b)
  (gap* : ∀ {N b y e} → Bd* N b → d N y e → ¬ b ⊑ y × ¬ y ⊑ b)
  (φ : ℕ → Pos → Pos)
  -- the source's correspondence, at its rows
  (ch→ : ∀ {N k e} → c N k e → Cuts.Clear c Bd N k → Cuts.Clear d Bd* N (φ N k))
  (ch← : ∀ {N k e} → c N k e → Cuts.Clear d Bd* N (φ N k) → Cuts.Clear c Bd N k)
  -- one cut's facts of it: a row is imaged, and no failure precedes the
  -- image of a row no failure precedes
  (img : ∀ {N k e} → c N k e → Σ (Ev X) (d N (φ N k)))
  (unfail : ∀ {N k e} → c N k e → ¬ TakeWhile.Failed incl keep (c N) k → ¬ TakeWhile.Failed incl keep* (d N) (φ N k))
  where
  module P = TakeClear incl keep c Bd gap
  module E = TakeClear incl keep* d Bd* gap*

  -- A row the take keeps sits on its source row's image.
  kept→ : ∀ {N k e} → c N k e → ¬ P.Fl N k → P.Clear′ N k → E.Clear′ N (φ N k)
  kept→ {N} {k} x nF cl = E.kept-clear {N} {φ N k} (ch→ x (P.clear-kept {N} {k} nF cl))

  kept← : ∀ {N k e} → c N k e → ¬ P.Fl N k → E.Clear′ N (φ N k) → P.Clear′ N k
  kept← {N} {k} x nF cl = P.kept-clear {N} {k} (ch← x (E.clear-kept {N} {φ N k} (unfail x nF) cl))

  -- A row under the first failing value sits under its image.
  made→ : ∀ {N o a} l → c N o (out a) → ¬ P.Fl N o → P.Clear′ N (o ⊕ [ l ]) → E.Clear′ N (φ N o ⊕ [ l ])
  made→ {N} {o} l x nF cl = E.made-clear {N} {φ N o} l (proj₂ (img x)) (ch→ x (P.clear-made {N} {o} l nF cl))

  made← : ∀ {N o a} l → c N o (out a) → ¬ P.Fl N o → E.Clear′ N (φ N o ⊕ [ l ]) → P.Clear′ N (o ⊕ [ l ])
  made← {N} {o} l x nF cl = P.made-clear {N} {o} l x (ch← x (E.clear-made {N} {φ N o} l (unfail x nF) cl))
