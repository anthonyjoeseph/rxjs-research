{-# OPTIONS --guardedness #-}

-- A SIMULATION OF A PROGRAM'S RUN BY ITS ROWS: a carrier on the run's
-- configurations, each read as the rows still owed the root, starting
-- at the program's own rows; a silent step keeps what is owed, a value
-- shows the least row owed and drops it, the end shows the least, and a
-- drained run owes nothing.  The sound half follows from any.
module adequacy.Simulation where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import denotation.Events using (Pos; root)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; enter; ⟦_⟧; Den; _≺_; _≼_; Dep; Silent; Seen)
open import denotation.Laws.Modulus using (≼-or-≻; entered-few)
open import denotation.Laws.Worlds using (InvAt)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Read using (Meets; Run; Visible; loud; cursor; []; _∷_)
import denotation.Read as Read
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Conf; load)
open import adequacy.Rows using (Steps; conv; Vis; Past; Lowest; Shows*; Shows*-≃; Beyond; into; back; narrow; past-≃; _≃_; ≃-sym; ≃-trans;
  []; _∷_) renaming (tau to τˢ; val to valˢ; fin to finˢ)
open import adequacy.Path using (Path)
import adequacy.Path as P
open _≃_

record Simulation {R : Set} (o : PureObs [] R) : Set₂ where
  field
    I   : Conf R → Set₁
    T   : ∀ {k} → I k → EmissionSet R
    i₀  : I (load o)
    t₀  : Vis (T i₀) ≃ Vis (enter (⟦ o ⟧ []ᴬ) root)
    tau : ∀ {k k′ t} (i : I k) → Driver.step R k ≡ Driver.silent t k′ → Σ (I k′) λ i′ → Vis (T i) ≃ Vis (T i′)
    val : ∀ {k k′ t p a} (i : I k) → Driver.step R k ≡ Driver.value t p a k′
        → Σ (I k′) λ i′ → Lowest (T i) p (out a) × Vis (Past p (T i)) ≃ Vis (T i′)
    fin : ∀ {k p} (i : I k) → Driver.step R k ≡ Driver.complete p → Lowest (T i) p end
    dry : ∀ {k} (i : I k) → Driver.step R k ≡ Driver.drained → ∀ {q e} → Vis (T i) q e → ⊥

module Sound {R : Set} {o : PureObs [] R} (S : Simulation o) where
  open Simulation S

  -- Whatever a run from `k` shows, a reader of its rows is shown.
  sound-from : ∀ {k} (i : I k) → ∀ {rs} → Steps k rs → Shows* (T i) (conv rs)
  sound-from i []          = []
  sound-from i (τˢ e st)  = let (i′ , q) = tau i e in Shows*-≃ (≃-sym q) (sound-from i′ st)
  sound-from i (valˢ e st)  = let (i′ , l , q) = val i e in l ∷ Shows*-≃ (≃-sym q) (sound-from i′ st)
  sound-from i (finˢ e)     = fin i e ∷ []

-- THE SKIPS BETWEEN: least visible rows shown in turn are a reader's run.
-- Each has few rows before it, as it is entered, and no end before it,
-- since only silent rows follow an end.
module _ {A} (d : Den A) (p₀ : Pos) (quiet : ∀ {c y e} → enter d p₀ c end → enter d p₀ y e → c ≺ y → Silent e) where
  private
    t : EmissionSet A
    t = enter d p₀

    dep : ∀ {q} {e : Ev A} {k e′} → Visible e → Dep q e k e′
    dep {e = out _} _ = tt
    dep {e = end}   _ = tt

  run-of : ∀ c {vs} → Shows* (Beyond t c) vs → Run t c vs
  run-of c [] = []
  run-of c (_∷_ {p = p} ((x , vi) , lt) rest) =
    (((tp , proper) , entered-few d p₀ (λ {k} {e′} → dep {p} {_} {k} {e′} vi) tp) , vi , cq , λ tk vk ck → lt (back c tk ck , vk))
    ∷ run-of (just p) (Shows*-≃ (narrow c cq) rest)
    where
      tp = proj₁ (into c x)
      cq = proj₂ (into c x)
      proper : ∀ {k} → t k end → p ≼ k
      proper {k} tk with ≼-or-≻ p k
      ... | inj₁ le = le
      ... | inj₂ kp = ⊥-elim (loud vi (quiet tk tp kp))

-- Only silent rows follow a program's end.
quiet-root : ∀ {R} (o : PureObs [] R) {c y e} → enter (⟦ o ⟧ []ᴬ) root c end → enter (⟦ o ⟧ []ᴬ) root y e → c ≺ y → Silent e
quiet-root o = InvAt.quiet (inv-⟦⟧ o []ᴬ (λ ()) root (tt , λ ()))

met-of-shown : ∀ {R} {o : PureObs [] R} {vs} → Shows* (enter (⟦ o ⟧ []ᴬ) root) vs → Meets (enter (⟦ o ⟧ []ᴬ) root) vs
met-of-shown {o = o} = run-of (⟦ o ⟧ []ᴬ) root (quiet-root o) nothing

-- THE SOUND HALF: what the engine shows, a subscriber to the program's
-- rows is shown.
sound : ∀ {R} {o : PureObs [] R} → Simulation o → ∀ {rs} → Steps (load o) rs → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs)
sound {o = o} S st = met-of-shown {o = o} (Shows*-≃ (Simulation.t₀ S) (Sound.sound-from S (Simulation.i₀ S) st))

-- ALONG A RUN: the carrier on the conf reached, and the visible rows it
-- owes the program's rows past what the run has shown.
module Along {R : Set} {o : PureObs [] R} (S : Simulation o) where
  open Simulation S using (I; T) renaming (tau to simτ; val to simval)

  private
    t : EmissionSet R
    t = enter (⟦ o ⟧ []ᴬ) root

  along : ∀ {k₀ rs k} c → Path k₀ rs k → (i : I k₀) → Vis (T i) ≃ Vis (Beyond t c)
        → Σ (I k) λ i′ → Vis (T i′) ≃ Vis (Beyond t (cursor c (conv rs)))
  along c P.[]        i r = i , r
  along c (P.tau e pth) i r =
    let (i′ , q) = simτ i e
    in along c pth i′ (≃-trans {t = Vis (T i′)} {u = Vis (T i)} {v = Vis (Beyond t c)} (≃-sym q) r)
  along c (P.val {p = p} e pth) i r =
    let (i′ , (v , _) , q) = simval i e
        cq = proj₂ (into c (proj₁ (to r v)))
    in along (just p) pth i′
         (≃-trans {t = Vis (T i′)} {u = Vis (Past p (T i))} {v = Vis (Beyond t (just p))} (≃-sym q)
           (≃-trans {u = Vis (Past p (Beyond t c))} (past-≃ {t = T i} {u = Beyond t c} {p = p} r) (narrow {t = t} c cq)))

  -- The row met next past `c`.
  Owed : Maybe Pos → Pos → Ev R → Set
  Owed c p e = Seen t p e × Visible e × Read.Least t c p

  -- The last row met.
  met-next : ∀ {c} xs {p e} → Run t c (xs ++ [ (p , e) ]) → Owed (cursor c xs) p e
  met-next []       (h ∷ []) = h
  met-next (_ ∷ xs) (_ ∷ m)  = met-next xs m
