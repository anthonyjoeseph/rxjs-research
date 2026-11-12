{-# OPTIONS --guardedness #-}

-- A RUN TOLD ITS END CARRIES THE RUN.  `completing` and `annotate` each
-- read a run through its own subject by a concat queueing one more row,
-- which shows nothing, at the run's end: one connect, two uses.  Around
-- it, rows relabelled one for one: a map, and a scan projected, whose
-- rows show what the rows they relabel showed.
module simultaneous.CarryTold where

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; connect; connected; of)
open import denotation.Position using (_≟ᵖ_; Pos; ix; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Reach; Den; DenEnv; enter; approx; module Scan; module Op)
open import denotation.Laws.Modulus using (entered-reach; reach-few)
open import denotation.Laws.Worlds using (InvAt; Ok; Hots; GoodEnv; full; _⊑_)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import simultaneous.Attribution using (Shown; Match; Every; One; Reads; Carried; Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.Folds using (reach-kin; few-¬¬listed; module ListedFold)
open import simultaneous.CarryBase using (CarryAt; Kin; k-out; k-skip; k-pin; k-end; kin-refl; module Relabel)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; concatˢ)

------------------------------------------------------------------------
-- Rows showing alike

-- Two events alike but for their labels, each label showing what the
-- other does.
data Same {X Y Z : Set} (f₁ : Y → List X) (f₂ : Z → List X) : Ev Y → Ev Z → Set where
  same-out  : ∀ {x y} → f₁ x ≡ f₂ y → Same f₁ f₂ (out x) (out y)
  same-skip : Same f₁ f₂ skip skip
  same-pin  : ∀ {r} → Same f₁ f₂ (pin r) (pin r)
  same-end  : Same f₁ f₂ end end

private
  module Alike {X Y Z : Set} {f₁ : Y → List X} {f₂ : Z → List X} where
    kin : ∀ {e e′} → Same f₁ f₂ e e′ → Kin e e′
    kin (same-out _) = k-out
    kin same-skip    = k-skip
    kin same-pin     = k-pin
    kin same-end     = k-end

    shown : ∀ {e e′} → Same f₁ f₂ e e′ → Shown (One f₂) e′ → Shown (One f₁) e
    shown (same-out eq) (a , r) = a , trans eq r
    shown same-end      _       = tt
    shown same-skip     ()
    shown same-pin      ()

    carried : ∀ {e₀ : Ev X} {e e′} → Carried (Reads f₁) e₀ e → Same f₁ f₂ e e′ → Carried (Reads f₂) e₀ e′
    carried {e₀ = out _} (_ , refl , r) (same-out eq) = _ , refl , trans (sym eq) r
    carried {e₀ = end}   refl           same-end      = refl
    carried {e₀ = skip}  ()             _
    carried {e₀ = pin _} ()             _

    match : ∀ {e₀ : Ev X} {e e′} → Same f₁ f₂ e e′
          → Match Every (One f₁) (Reads f₁) e₀ e → Match Every (One f₂) (Reads f₂) e₀ e′
    match sv (cr , ns) = (λ s₀ → carried (cr s₀) sv) , λ n sw → ns n (shown sv sw)

  -- A carry relabelled on the elaborated side alone, row for row.
  module OneSide {X Y Z : Set} {f₁ : Y → List X} {f₂ : Z → List X} {u : EmissionSet Y} {u′ : EmissionSet Z}
    (upL′ : ∀ {l e} → Listed u l → u l e → Σ (Ev Z) λ e′ → u′ l e′ × Same f₁ f₂ e e′)
    (up¬¬′ : ∀ {l e} → u l e → ¬ ¬ Σ (Ev Z) λ e′ → u′ l e′ × Same f₁ f₂ e e′)
    (up-end′ : ∀ {l} → u l end → u′ l end) (up-pin′ : ∀ {l r} → u l (pin r) → u′ l (pin r))
    (down′ : ∀ {l e′} → u′ l e′ → Σ (Ev Y) λ e → u l e × Same f₁ f₂ e e′) where

    carried : ∀ {M HP HE LP} {t : EmissionSet X} {s s′} → CarryAt f₁ M HP HE LP t u s s′ → CarryAt f₂ M HP HE LP t u′ s s′
    carried {t = t} c =
      Relabel.carried {t = t} {t′ = t} (λ _ e e′ → e′ ≡ e) (λ _ → Same f₁ f₂) (λ { {e = e} refl → kin-refl e })
        (λ {l} {e} {e′} → Alike.kin {e = e} {e′ = e′})
        (λ tk → _ , tk , refl) (λ tk → _ , tk , refl) (λ {l} {e} → upL′ {l} {e}) (λ {l} {e} → up¬¬′ {l} {e}) (λ {l} → up-end′ {l})
        (λ {l} {r} → up-pin′ {l} {r}) (λ {l} {e′} → down′ {l} {e′}) c
        (λ {l} {e} {e′} → Alike.shown {e = e} {e′ = e′}) (λ { _ refl sv m → Alike.match sv m })

------------------------------------------------------------------------
-- A map

-- A MAP RELABELS: each row keeps its place, its label mapped, showing
-- what it showed.
module Mapped {X Y Z : Set} {f₁ : Y → List X} {f₂ : Z → List X} (g : Y → Z) (law : ∀ y → f₁ y ≡ f₂ (g y)) (d : Den Y) (p′ : Pos) where
  private
    module E = MapRun g d p′

    same : ∀ (e : Ev Y) → Same f₁ f₂ e (mapEv g e)
    same (out y) = same-out (law y)
    same skip    = same-skip
    same (pin _) = same-pin
    same end     = same-end

    down : ∀ {l e′} → E.M l e′ → Σ (Ev Y) λ e → E.S l e × Same f₁ f₂ e e′
    down m with E.unmap m
    ... | e , x , refl = e , x , same e

  carried : ∀ {M HP HE LP} {t : EmissionSet X} {s} → CarryAt f₁ M HP HE LP t E.S s p′ → CarryAt f₂ M HP HE LP t E.M s p′
  carried = OneSide.carried (λ {_} {e} _ x → _ , E.lift x , same e) (λ {_} {e} x n → n (_ , E.lift x , same e)) E.lift E.lift
              (λ {l} {e′} → down {l} {e′})

------------------------------------------------------------------------
-- A scan projected

-- A SCAN PROJECTED RELABELS when each step's projection shows what its
-- row did: its state folds the rows before, so it is built only from a
-- listing, and refutably elsewhere.
module Folded {X Y Z B : Set} {f₁ : Y → List X} {f₂ : Z → List X} (g : B → Y → B) (z : B) (π : B → Z)
  (law : ∀ b y → f₂ (π (g b y)) ≡ f₁ y) (d : Den Y) (p′ : Pos) {H : Pos → Set} (Iu : InvAt H p′ (enter d p′)) where
  private
    u : EmissionSet Y
    u = enter d p′

    funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′
    funcU {y} {e} {e′} = InvAt.func Iu {y} {e} {e′}

    module RS = Scan g z u
    module AF = AccF g z {t = u} (λ {y} {e} {e′} → funcU {y} {e} {e′})
    module RL = ListedFold g z {t = u} (λ {y} {e} {e′} → funcU {y} {e} {e′})
    module W = MapRun π (Op.scan g z d) p′

    down₀ : ∀ {l e′} → RS.ScanT l e′ → Σ (Ev Y) λ e → u l e × Kin e e′
    down₀ (RS.sval a)  = _ , proj₂ (AF.acc-val a) , k-out
    down₀ (RS.sstep x) = _ , x , k-skip
    down₀ (RS.spin x)  = _ , x , k-pin
    down₀ (RS.send x)  = _ , x , k-end

    vals-acc : ∀ {l st y} → RS.Acc l st → u l (out y) → f₂ (π st) ≡ f₁ y
    vals-acc (RS.acc₀ {a = a} x _) ux with funcU x ux
    ... | refl = law z a
    vals-acc (RS.acc {b = b} {a′ = a′} _ x _ _) ux with funcU x ux
    ... | refl = law b a′

    rch : ∀ {q e} → u q e → Reach u q e
    rch {q} {e} = entered-reach d p′ {q} {e}

    upL : ∀ {l e} → Listed u l → u l e → Σ (Ev Z) λ e′ → W.M l e′ × Same f₁ f₂ e e′
    upL {e = out y} L uy with RL.fold-listed L uy
    ... | st , ac = out (π st) , W.lift (RS.sval ac , reach-kin down₀ (k-out {a = y} {b = st}) (rch uy)) , same-out (sym (vals-acc ac uy))
    upL {e = skip}  _ x = skip , W.lift (RS.sstep x , reach-kin down₀ k-skip (rch x)) , same-skip
    upL {e = pin r} _ x = pin r , W.lift (RS.spin x , reach-kin down₀ k-pin (rch x)) , same-pin
    upL {e = end}   _ x = end , W.lift (RS.send x , reach-kin down₀ k-end (rch x)) , same-end

    up-pin : ∀ {l r} → u l (pin r) → W.M l (pin r)
    up-pin x = W.lift (RS.spin x , reach-kin down₀ k-pin (rch x))

    up-end : ∀ {l} → u l end → W.M l end
    up-end x = W.lift (RS.send x , reach-kin down₀ k-end (rch x))

    up¬¬ : ∀ {l e} → u l e → ¬ ¬ Σ (Ev Z) λ e′ → W.M l e′ × Same f₁ f₂ e e′
    up¬¬ {l} {e = out y} uy n = few-¬¬listed (reach-few {e = out y} (λ {k} {e′} → full {q = l} {e = out y} tt {k} {e′}) (rch uy)) λ L → n (upL L uy)
    up¬¬ {e = skip}  x  n = n (skip , W.lift (RS.sstep x , reach-kin down₀ k-skip (rch x)) , same-skip)
    up¬¬ {e = pin r} x  n = n (pin r , up-pin x , same-pin)
    up¬¬ {e = end}   x  n = n (end , up-end x , same-end)

    back : ∀ {l e₀} → RS.ScanT l e₀ → Σ (Ev Y) λ e → u l e × Same f₁ f₂ e (mapEv π e₀)
    back (RS.sval a)  = let (y , uy) = AF.acc-val a in out y , uy , same-out (sym (vals-acc a uy))
    back (RS.sstep x) = skip , x , same-skip
    back (RS.spin x)  = _ , x , same-pin
    back (RS.send x)  = end , x , same-end

    down : ∀ {l e′} → W.M l e′ → Σ (Ev Y) λ e → u l e × Same f₁ f₂ e e′
    down m with W.unmap m
    ... | _ , (sc , _) , refl = back sc

  carried : ∀ {M HP HE LP} {t : EmissionSet X} {s} → CarryAt f₁ M HP HE LP t u s p′ → CarryAt f₂ M HP HE LP t W.M s p′
  carried = OneSide.carried (λ {l} {e} → upL {l} {e}) (λ {l} {e} → up¬¬ {l} {e}) (λ {l} → up-end {l}) (λ {l} {r} → up-pin {l} {r})
              (λ {l} {e′} → down {l} {e′})

------------------------------------------------------------------------
-- The told run

-- A run read through its own subject by a concat queueing one more row.
told : ∀ {Γ Y} → Y → Obs Timeline Γ Y → Obs Timeline Γ Y
told x s = connect s (concatˢ (connected (here refl)) (of (x ∷ [])))

-- THE TOLD RUN CARRIES THE RUN, where the queued row shows nothing: the
-- subject shows the run's rows again in the concat's first lane, under
-- their own, and only the end moves, past the queued row; the run's own
-- rows show again only as the connect's pins and skips.  Each late
-- carrier lies under one of the run's.
postulate
  told-carry : ∀ {Γ X Y} {f : Y → List X} {M HP HE LP} {t : EmissionSet X} {s} n (S : Obs Timeline Γ Y) (x : Y) → f x ≡ []
             → (env : DenEnv Γ) → GoodEnv env → ∀ q → Ok (Hots env) q
             → (c : CarryAt f M HP HE LP t (enter (approx n S env) (q ⊕ [ ix 1 ])) s (q ⊕ [ ix 1 ]))
             → Σ (CarryAt f M HP HE LP t (enter (approx n (told x S) env) q) s q)
                 λ c′ → ∀ {k l e₀} → CarryAt.PB c′ k l → t k e₀ → Live t k → Σ Pos λ l₀ → CarryAt.PB c k l₀ × l₀ ⊑ l

-- What a row of a run read as maybe-emits shows.
justValues : ∀ {X} → Maybe (IE X) → List X
justValues (just x) = valuesOf x
justValues nothing  = []
