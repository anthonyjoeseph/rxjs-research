{-# OPTIONS --guardedness #-}

-- THE WRAPPER CARRIES THE CORE.  `elaborate` subscribes the elaborated
-- core as the first lane of a merge with the subscribe mark, that merge
-- as the first lane of a concat with the completion mark, and restamps
-- and projects the whole.  Each stage carries the plain run on its own:
-- a mark shows nothing, so only the end moves, past the stage's other
-- lane, and the stage's carry has an embedding of its own.
module simultaneous.CarryWrap where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (of)
open import denotation.Position using (_≟ᵖ_; Pos; Path; ix; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Reach; Den; enter; approx; module Scan; module Op)
open import denotation.Laws.Modulus using (entered-reach; reach-few)
open import denotation.Laws.Worlds using (InvAt; Ok; Hots; full; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import denotation.Laws using (inv-approx)
open import simultaneous.SObs using (SObs; plain; module Elaborate)
open import simultaneous.InstEmit using (instEmit; valuesOf; value; mark; begin; over; stop; outerOpen; outerClose; laneStart;
  laneDone; burstEnd; outerDone; subscribed; completed)
import simultaneous.InstEmit as Marks
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import simultaneous.Attribution using (Shown; Match; Every; One; Reads; Carried)
open import simultaneous.Listing using (Listed)
open import simultaneous.Folds using (reach-kin; few-¬¬listed; module ListedFold)
open import simultaneous.Relations using (stamp₀; sourced)
open import simultaneous.Carry using (PMap; Emb; CarryAt; Kin; k-out; k-skip; k-pin; k-end; kin-refl; module Relabel)
open import simultaneous.CarryLeaves using (coreAt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; elab; elaborate; marked; concatˢ; restamp)

-- A stage of the wrapper over `u`, subscribed at `s′`: the plain run
-- carried along an embedding of the stage's own, the plain subscription
-- put at or under the stage's.
Wrapped : ∀ {A} → ℕ → SObs [] A → EmissionSet (IE A) → Pos → Set₁
Wrapped n o u s′ = Σ PMap λ M → Emb M × Σ Path λ δ → M root (s′ ⊕ δ)
                 × CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root) u root s′

-- Where the concat subscribes its first lane, the merge: the second
-- child of the concat's first outer value.
mAt : Pos
mAt = root ⊕ (ix 0 ∷ ix 1 ∷ [])

------------------------------------------------------------------------
-- The restamp

private
  -- Two events alike but for their stamps.
  data SameVals {X : Set} : Ev (IE X) → Ev (IE X) → Set where
    sv-out  : ∀ {x y} → valuesOf x ≡ valuesOf y → SameVals (out x) (out y)
    sv-skip : SameVals skip skip
    sv-pin  : ∀ {r} → SameVals (pin r) (pin r)
    sv-end  : SameVals end end

  sv-kin : ∀ {X : Set} {e e′ : Ev (IE X)} → SameVals e e′ → Kin e e′
  sv-kin (sv-out _) = k-out
  sv-kin sv-skip    = k-skip
  sv-kin sv-pin     = k-pin
  sv-kin sv-end     = k-end

  sv-shown : ∀ {X : Set} {e e′ : Ev (IE X)} → SameVals e e′ → Shown (One valuesOf) e′ → Shown (One valuesOf) e
  sv-shown (sv-out eq) (a , r) = a , trans eq r
  sv-shown sv-end      _       = tt
  sv-shown sv-skip     ()
  sv-shown sv-pin      ()

  sv-carried : ∀ {X : Set} {e₀ : Ev X} {e₁ e₁′ : Ev (IE X)} → Carried (Reads valuesOf) e₀ e₁ → SameVals e₁ e₁′
             → Carried (Reads valuesOf) e₀ e₁′
  sv-carried {e₀ = out _} (_ , refl , r) (sv-out eq) = _ , refl , trans (sym eq) r
  sv-carried {e₀ = end}   refl           sv-end      = refl
  sv-carried {e₀ = skip}  ()             _
  sv-carried {e₀ = pin _} ()             _

  sv-match : ∀ {X : Set} {e₀ : Ev X} {e₁ e₁′ : Ev (IE X)} → SameVals e₁ e₁′
           → Match Every (One valuesOf) (Reads valuesOf) e₀ e₁ → Match Every (One valuesOf) (Reads valuesOf) e₀ e₁′
  sv-match sv (cr , ns) = (λ s₀ → sv-carried (cr s₀) sv) , λ n sw → ns n (sv-shown sv sw)

  -- A restamp keeps the event, so the values.
  restamp-vals : ∀ {X : Set} (st : Pos × IE X) x → valuesOf (proj₂ (restamp st x)) ≡ valuesOf x
  restamp-vals (_ , _) (instEmit (value _) _)            = refl
  restamp-vals (_ , _) (instEmit (mark begin) _)         = refl
  restamp-vals (_ , _) (instEmit (mark over) _)          = refl
  restamp-vals (_ , _) (instEmit (mark stop) _)          = refl
  restamp-vals (_ , _) (instEmit (mark outerOpen) _)     = refl
  restamp-vals (_ , _) (instEmit (mark outerClose) _)    = refl
  restamp-vals (_ , _) (instEmit (mark laneStart) _)     = refl
  restamp-vals (_ , _) (instEmit (mark Marks.carry) _)   = refl
  restamp-vals (_ , _) (instEmit (mark laneDone) _)      = refl
  restamp-vals (_ , _) (instEmit (mark burstEnd) _)      = refl
  restamp-vals (_ , _) (instEmit (mark outerDone) _)     = refl
  restamp-vals (_ , _) (instEmit (mark subscribed) _)    = refl
  restamp-vals (_ , _) (instEmit (mark completed) _)     = refl

-- THE RESTAMP RELABELS: each emit keeps its event under a new stamp, so
-- a carry passes through the scan and the projection row for row.  The
-- scan's state folds the rows before, so it is built only from a listing,
-- and refutably elsewhere.
module Restamp {X : Set} (d : Den (IE X)) (p′ : Pos) {H : Pos → Set} (Iu : InvAt H p′ (enter d p′)) where
  private
    u : EmissionSet (IE X)
    u = enter d p′

    funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′
    funcU {y} {e} {e′} = InvAt.func Iu {y} {e} {e′}

    module RS = Scan restamp stamp₀ u
    module AF = AccF restamp stamp₀ {t = u} (λ {y} {e} {e′} → funcU {y} {e} {e′})
    module RL = ListedFold restamp stamp₀ {t = u} (λ {y} {e} {e′} → funcU {y} {e} {e′})
    module W = MapRun proj₂ (Op.scan restamp stamp₀ d) p′

    down₀ : ∀ {l e′} → RS.ScanT l e′ → Σ (Ev (IE X)) λ e → u l e × Kin e e′
    down₀ (RS.sval a)  = _ , proj₂ (AF.acc-val a) , k-out
    down₀ (RS.sstep x) = _ , x , k-skip
    down₀ (RS.spin x)  = _ , x , k-pin
    down₀ (RS.send x)  = _ , x , k-end

    vals-acc : ∀ {l st x} → RS.Acc l st → u l (out x) → valuesOf (proj₂ st) ≡ valuesOf x
    vals-acc (RS.acc₀ {a = a} y _) ux with funcU y ux
    ... | refl = restamp-vals stamp₀ a
    vals-acc (RS.acc {b = b} {a′ = a′} _ y _ _) ux with funcU y ux
    ... | refl = restamp-vals b a′

    rch : ∀ {q e} → u q e → Reach u q e
    rch {q} {e} = entered-reach d p′ {q} {e}

    upL : ∀ {l e} → Listed u l → u l e → Σ (Ev (IE X)) λ e′ → W.M l e′ × SameVals e e′
    upL {e = out x} L ux with RL.fold-listed L ux
    ... | st , ac = out (proj₂ st) , W.lift (RS.sval ac , reach-kin down₀ (k-out {a = x} {b = st}) (rch ux)) , sv-out (sym (vals-acc ac ux))
    upL {e = skip}  _ x = skip , W.lift (RS.sstep x , reach-kin down₀ k-skip (rch x)) , sv-skip
    upL {e = pin r} _ x = pin r , W.lift (RS.spin x , reach-kin down₀ k-pin (rch x)) , sv-pin
    upL {e = end}   _ x = end , W.lift (RS.send x , reach-kin down₀ k-end (rch x)) , sv-end

    up-pin : ∀ {l r} → u l (pin r) → W.M l (pin r)
    up-pin x = W.lift (RS.spin x , reach-kin down₀ k-pin (rch x))

    up-end : ∀ {l} → u l end → W.M l end
    up-end x = W.lift (RS.send x , reach-kin down₀ k-end (rch x))

    up¬¬ : ∀ {l e} → u l e → ¬ ¬ Σ (Ev (IE X)) λ e′ → W.M l e′ × SameVals e e′
    up¬¬ {l} {e = out x} ux n = few-¬¬listed (reach-few {e = out x} (λ {k} {e′} → full {q = l} {e = out x} tt {k} {e′}) (rch ux)) λ L → n (upL L ux)
    up¬¬ {e = skip}  x  n = n (skip , W.lift (RS.sstep x , reach-kin down₀ k-skip (rch x)) , sv-skip)
    up¬¬ {e = pin r} x  n = n (pin r , up-pin x , sv-pin)
    up¬¬ {e = end}   x  n = n (end , up-end x , sv-end)

    back : ∀ {l e₀} → RS.ScanT l e₀ → Σ (Ev (IE X)) λ e → u l e × SameVals e (mapEv proj₂ e₀)
    back (RS.sval a)  = let (x , ux) = AF.acc-val a in out x , ux , sv-out (sym (vals-acc a ux))
    back (RS.sstep x) = skip , x , sv-skip
    back (RS.spin x)  = _ , x , sv-pin
    back (RS.send x)  = end , x , sv-end

    down : ∀ {l e′} → W.M l e′ → Σ (Ev (IE X)) λ e → u l e × SameVals e e′
    down m with W.unmap m
    ... | _ , (sc , _) , refl = back sc

  carried : ∀ {M HP HE LP} {t : EmissionSet X} {s} → CarryAt valuesOf M HP HE LP t u s p′ → CarryAt valuesOf M HP HE LP t W.M s p′
  carried c =
    Relabel.carried (λ _ e e′ → e′ ≡ e) (λ _ → SameVals) (λ { {e = e} refl → kin-refl e }) (λ {l} {e} {e′} → sv-kin {X} {e} {e′})
      (λ tk → _ , tk , refl) (λ tk → _ , tk , refl) (λ {l} {e} → upL {l} {e}) (λ {l} {e} → up¬¬ {l} {e}) (λ {l} → up-end {l})
      (λ {l} {r} → up-pin {l} {r}) (λ {l} {e′} → down {l} {e′}) c
      (λ {l} {e} {e′} → sv-shown {X} {e} {e′}) (λ { _ refl sv m → sv-match sv m })

------------------------------------------------------------------------
-- The stages

-- THE MERGE CARRIES THE CORE: the subscribe mark, a lone lane emitting at
-- once, shows nothing, and the merge ends where the later of its lanes
-- does, so the core's end, if any, moves to the merge's.
-- THE CONCAT CARRIES THE MERGE: the completion mark's lane is queued
-- until the merge ends and subscribed past it, so the end moves past the
-- mark; every other row stays where the merge's was.
postulate
  wrap-merge  : ∀ n {A} (o : SObs [] A) → Wrapped n o (enter (approx n (elab (λ i → i) (plain o)) []) coreAt) coreAt
              → Wrapped n o (enter (approx n (sourced o) []) mAt) mAt
  wrap-concat : ∀ n {A} (o : SObs [] A) → Wrapped n o (enter (approx n (sourced o) []) mAt) mAt
              → Wrapped n o (enter (approx n (concatˢ (sourced o) (of (marked completed ∷ []))) []) root) root

-- The restamp and projection, over the concat.
wrap-restamp : ∀ n {A} (o : SObs [] A) → Wrapped n o (enter (approx n (concatˢ (sourced o) (of (marked completed ∷ []))) []) root) root
             → Wrapped n o (enter (approx n (elaborate (plain o)) []) root) root
wrap-restamp n o (M , hm , δ , at , c) =
  M , hm , δ , at , Restamp.carried (approx n (concatˢ (sourced o) (of (marked completed ∷ []))) []) root
                      (inv-approx n (concatˢ (sourced o) (of (marked completed ∷ []))) [] (λ ()) root ok₀) c
  where
    ok₀ : Ok (Hots []) root
    ok₀ = tt , λ ()

-- THE WRAPPER CARRIES THE CORE, at each approximant, stage by stage.
carry-wrap : ∀ n {A} (o : SObs [] A) {M} → Emb M → M root coreAt
           → CarryAt valuesOf M (λ _ → ⊥) (λ _ → ⊥) (λ _ → ⊤) (enter (approx n (plain o) []) root)
               (enter (approx n (elab (λ i → i) (plain o)) []) coreAt) root coreAt
           → Wrapped n o (enter (approx n (elaborate (plain o)) []) root) root
carry-wrap n o {M} hm m c =
  wrap-restamp n o (wrap-concat n o (wrap-merge n o (M , hm , [] , subst (M root) (sym (⊕-identityʳ coreAt)) m , c)))
