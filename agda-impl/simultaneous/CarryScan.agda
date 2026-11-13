{-# OPTIONS --guardedness #-}

-- A SCAN CARRIES what its source did.  The plain scan's value at a row
-- folds every plain value up to it; the elaborated scan's state at the
-- row's carrier folds every elaborated value up to the carrier, marks
-- passing the state through.  The carried values are the elaborated
-- values, in order and none skipped, so the two folds agree.
--
-- The elaborated fold is built from the carrier's listing, which names
-- every row before it with its event, so the latest value before a row
-- is decided.  The plain fold is only witnessed: the plain run is listed
-- only at the closed top (`simultaneous.Carry`'s DEAD ROUTE), so a fold
-- read off the elaborated one (`Back`) is compared with the plain row's
-- own, and every negative fact about the plain values (none before the
-- first, none between two) is found classically, from carriers in order.
module simultaneous.CarryScan where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (T)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Tree using (scan)
open import denotation.Position using (Pos; _<ᵖ_; root; _≟ᵖ_; inside)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; enter; Truncate; Reach; Few; _≺_; _≼_; Unpinned;
  module Scan; module Op; approx)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split; reach-few; entered-reach)
open import denotation.Laws.Worlds using (InvAt; full; GoodEnv; Ok; Hots)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Shows using (∈-stable)
open import denotation.Laws using (inv-approx)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark; begin)
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Folds using (reach-kin; few-¬¬listed; module ListedFold)
open import simultaneous.CarryBase using (PMap; Emb; CarryAt; Narrow; PinList; pins-map; Encl; encl-map; Targeted; Kin; k-out; k-skip; k-pin; k-end; unp→; kin-map; kin-refl; module Relabel; module Lifts; module Mono; Home; Near; Whole; IntoAt; few-sub; match-val; carried-val; match-end)
open import simultaneous.Carry using (Carry; carry; nest-via; CarriesAt; EnvRel; HotsListed)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; scanIE; marked)

-- The label of an elaborated scan: the values of the emit it passes.
stateValues : ∀ {B : Set} → B × IE B → List B
stateValues x = valuesOf (proj₂ x)

------------------------------------------------------------------------
-- Rows of a set and of an operator over it

private
  -- The carrier of a plain value is unpinned.
  carried-unp : ∀ {A : Set} {a : A} {e₁ : Ev (IE A)} → Match Every (One valuesOf) (Reads valuesOf) (out a) e₁ → Unpinned e₁
  carried-unp mt with carried-val mt
  ... | _ , refl = tt

  -- A step shows a value exactly when the emit it reads does.
  shown-ie : ∀ {A B : Set} {f : B → A → B} st (y : IE A) → Shown (One stateValues) (out (scanIE f st y))
           → Shown (One valuesOf) (out y)
  shown-ie st (instEmit (value a) _) _ = a , refl
  shown-ie st (instEmit (mark _) _)  (_ , ())

------------------------------------------------------------------------
-- The scan's carrier

module Core {A B : Set} (f : B → A → B) (z : B) {M : PMap} {HP HE LP H₁ H₂ : Pos → Set}
  {t : EmissionSet A} {u : EmissionSet (IE A)} {s s′ : Pos} (hm : Emb M)
  (rch : ∀ {q e} → t q e → Reach t q e) (rchU : ∀ {q e} → u q e → Reach u q e)
  (It : InvAt H₁ s t) (Iu : InvAt H₂ s′ u)
  (c : CarryAt valuesOf M HP HE LP t u s s′) where
  open CarryAt c

  private
    module P = Scan f z t
    module E = Scan (scanIE f) (z , marked begin) u
    module PF = AccF f z (λ {y} {e} {e′} → InvAt.func It {y} {e} {e′})
    module EF = AccF (scanIE f) (z , marked begin) (λ {y} {e} {e′} → InvAt.func Iu {y} {e} {e′})
    module EL = ListedFold (scanIE f) (z , marked begin) (λ {y} {e} {e′} → InvAt.func Iu {y} {e} {e′})

  img-mono : ∀ {k k′ l l′} → Img k l → Img k′ l′ → k ≺ k′ → l ≺ l′
  img-mono = Mono.img-mono hm (λ {y} {e} {l} {ys} {e′} → InvAt.flat It {y} {e} {l} {ys} {e′}) c

  S : EmissionSet B
  S = Truncate P.ScanT

  S′ : EmissionSet (B × IE B)
  S′ = Truncate E.ScanT

  private
    funcU : ∀ {y e e′} → u y e → u y e′ → e ≡ e′
    funcU {y} {e} {e′} = InvAt.func Iu {y} {e} {e′}

    ----------------------------------------------------------------------
    -- Down, constructively; up, classically or from a listing

    down₀ : ∀ {k e′} → P.ScanT k e′ → Σ (Ev A) λ e → t k e × Kin e e′
    down₀ (P.sval a)  = _ , proj₂ (PF.acc-val a) , k-out
    down₀ (P.sstep x) = _ , x , k-skip
    down₀ (P.spin x)  = _ , x , k-pin
    down₀ (P.send x)  = _ , x , k-end

    down : ∀ {k e′} → S k e′ → Σ (Ev A) λ e → t k e × Kin e e′
    down x = down₀ (proj₁ x)

    downU₀ : ∀ {l e′} → E.ScanT l e′ → Σ (Ev (IE A)) λ e → u l e × Kin e e′
    downU₀ (E.sval a)  = _ , proj₂ (EF.acc-val a) , k-out
    downU₀ (E.sstep x) = _ , x , k-skip
    downU₀ (E.spin x)  = _ , x , k-pin
    downU₀ (E.send x)  = _ , x , k-end

    downU : ∀ {l e′} → S′ l e′ → Σ (Ev (IE A)) λ e → u l e × Kin e e′
    downU x = downU₀ (proj₁ x)

    few-of : ∀ {q e} → Unpinned e → t q e → Few t q
    few-of un x = reach-few (full un) (rch x)

    few-ofU : ∀ {q e} → Unpinned e → u q e → Few u q
    few-ofU un x = reach-few (full un) (rchU x)

    up : ∀ {k e} → t k e → ¬ ¬ Σ (Ev B) λ e′ → S k e′ × Kin e e′
    up {e = out a} x n = fold f z t (few-of tt x) x λ { (b , ac) → n (out b , (P.sval ac , reach-kin down₀ (k-out {a = a} {b = b}) (rch x)) , k-out) }
    up {e = skip}  x n = n (skip , (P.sstep x , reach-kin down₀ k-skip (rch x)) , k-skip)
    up {e = pin r} x n = n (pin r , (P.spin x , reach-kin down₀ k-pin (rch x)) , k-pin)
    up {e = end}   x n = n (end , (P.send x , reach-kin down₀ k-end (rch x)) , k-end)

    upU : ∀ {l e} → u l e → ¬ ¬ Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Kin e e′
    upU {e = out a} x n = fold (scanIE f) (z , marked begin) u (few-ofU tt x) x
      λ { (b , ac) → n (out b , (E.sval ac , reach-kin downU₀ (k-out {a = a} {b = b}) (rchU x)) , k-out) }
    upU {e = skip}  x n = n (skip , (E.sstep x , reach-kin downU₀ k-skip (rchU x)) , k-skip)
    upU {e = pin r} x n = n (pin r , (E.spin x , reach-kin downU₀ k-pin (rchU x)) , k-pin)
    upU {e = end}   x n = n (end , (E.send x , reach-kin downU₀ k-end (rchU x)) , k-end)

    upL : ∀ {l e} → Listed u l → u l e → Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Kin e e′
    upL {e = out y} L x = out _ , (E.sval (proj₂ (EL.fold-listed L x)) , reach-kin downU₀ (k-out {a = y} {b = proj₁ (EL.fold-listed L x)}) (rchU x)) , k-out
    upL {e = skip}  L x = skip , (E.sstep x , reach-kin downU₀ k-skip (rchU x)) , k-skip
    upL {e = pin r} L x = pin r , (E.spin x , reach-kin downU₀ k-pin (rchU x)) , k-pin
    upL {e = end}   L x = end , (E.send x , reach-kin downU₀ k-end (rchU x)) , k-end

    ----------------------------------------------------------------------
    -- Ends, few rows and listings across the scan

    liveS← : ∀ {k} → Live S k → Live t k
    liveS← lv tc = lv (P.send tc , reach-kin down₀ k-end (rch tc))

    liveS→ : ∀ {k} → Live t k → Live S k
    liveS→ lv sc with down sc
    ... | _ , tc , k-end = lv tc

    module UL = Lifts {a = u} {b = S′} {Rel = λ _ e e′ → Kin e e′} (λ k → k) upL upU (λ uc → E.send uc , reach-kin downU₀ k-end (rchU uc)) downU

    fewS→ : ∀ {k} → Few t k → Few S k
    fewS→ (ks , F) = ks , λ y kk → F (proj₁ (proj₂ (down y))) kk

    lstS← : ∀ {k} → Listed S k → Listed t k
    lstS← (ks , F , B) = ks , (λ y kk → ∈-stable λ ni → up y λ { (_ , y′ , _) → ni (F y′ kk) })
                       , λ m → proj₁ (B m) , _ , proj₁ (proj₂ (down (proj₂ (proj₂ (B m)))))

    endedS← : (∀ {c} → S c end → ⊥) → ∀ {c} → t c end → ⊥
    endedS← ne tc = up tc λ { (_ , sc , k-end) → ne sc }

    wholeS← : Whole S → Whole t
    wholeS← (ks , F , B) = ks , (λ y → ∈-stable λ ni → up y λ { (_ , y′ , _) → ni (F y′) })
                         , λ m → _ , proj₁ (proj₂ (down (proj₂ (B m))))

    live-out : ∀ {y a} → t y (out a) → Live t y
    live-out ty tc cy with InvAt.quiet It tc ty cy
    ... | _ , () , _

    ----------------------------------------------------------------------
    -- The plain values, classically carried

    img-val : ∀ {x a l e₁} → Img x l → u l e₁ → Match Every (One valuesOf) (Reads valuesOf) (out a) e₁
            → Σ Pos λ l′ → Img x l′ × Σ (IE A) λ y → u l′ (out y) × Reads valuesOf a y
    img-val i ul mt with carried-val mt
    ... | n , refl = _ , i , instEmit (value _) n , ul , refl

    img-out : ∀ {x a} → t x (out a) → ¬ ¬ Σ Pos λ l′ → Img x l′ × Σ (IE A) λ y → u l′ (out y) × Reads valuesOf a y
    img-out tx n = img¬¬ tx tt (live-out tx) (few-of tt tx) λ { (inj₁ (_ , i , _ , ul , mt)) → n (img-val i ul mt) ; (inj₂ ()) }

    img-at : ∀ {x a l′} → t x (out a) → Img x l′ → ¬ ¬ Σ (IE A) λ y → u l′ (out y) × Reads valuesOf a y
    img-at tx i′ n = img-out tx λ { (l″ , i″ , y , ul , r) → n (y , subst (λ l → u l (out y)) (img-fun i″ i′) ul , r) }

    -- A mark is no plain value's carrier.
    same-mark : ∀ {m l′ μ n y a} → u m (out (instEmit (mark μ) n)) → u l′ (out y) → Reads valuesOf a y → m ≼ l′ → ¬ (m ≺ l′) → ⊥
    same-mark {m} {l′} um ul r ml nml with ≼-split {m} {l′} ml
    ... | inj₁ l = nml l
    ... | inj₂ refl with funcU um ul
    ...   | refl with r
    ...     | ()

    -- Every carrier of a plain value at or past a mark lies past it.
    at-mark : ∀ {m μ n x a l′} → u m (out (instEmit (mark μ) n)) → t x (out a) → Img x l′ → (∀ {y} → u l′ (out y) → m ≼ l′) → m ≺ l′
    at-mark {m} {l′ = l′} um tx i′ h = decidable-stable (T? (m <ᵖ l′)) λ nml → img-at tx i′ λ { (y , ul′ , r) → same-mark um ul′ r (h ul′) nml }

    live-before : ∀ {m₀ m} → Live u m → m₀ ≺ m → Live u m₀
    live-before {m₀} {m} lv mm {c} uc = ≼-trans {m₀} {m} {c} (≺→≼ {m₀} {m} mm) (lv uc)

  ------------------------------------------------------------------------
  -- THE FOLD READ BACK: at an elaborated row, either no plain value is
  -- carried at or before it and the state is the seed, or the latest that
  -- is folds to the state, and every later one is carried past the row.
  Back : Pos → B → Set
  Back m b = (b ≡ z × (∀ {x a l′} → t x (out a) → Img x l′ → m ≺ l′))
           ⊎ Σ Pos λ k → Σ Pos λ lk → Img k lk × lk ≼ m × P.Acc k b × (∀ {x a l′} → t x (out a) → k ≺ x → Img x l′ → m ≺ l′)

  back : ∀ {m st} → E.Acc m st → Live u m → Few u m → Back m (proj₁ st)
  back {m} (E.acc₀ {a = instEmit (value a) n} y mn) lv fw with shown y (a , refl) lv fw
  ... | k , i , e₀ , tk , mt with match-val mt
  ...   | refl = inj₂ (k , m , i , ≼-refl {m} , P.acc₀ tk (λ tx xk → img-out tx λ { (l′ , i′ , _ , ul′ , _) → mn ul′ (img-mono i′ i xk) })
                      , λ _ kx i′ → img-mono i i′ kx)
  back {m} (E.acc₀ {a = instEmit (mark _) n} y mn) lv fw = inj₁ (refl , λ tx i′ → at-mark y tx i′ λ ul′ → mn ul′)
  back {m} (E.acc {q = m₀} {a′ = instEmit (mark _) n} a₀ y mm nx) lv fw with back a₀ (live-before {m₀} {m} lv mm) (few-sub fw mm)
  ... | inj₁ (eq , none) = inj₁ (eq , λ tx i′ → at-mark y tx i′ λ ul′ → nx ul′ (none tx i′))
  ... | inj₂ (k , lk , i , lkm , ac , lat) =
    inj₂ (k , lk , i , ≼-trans {lk} {m₀} {m} lkm (≺→≼ {m₀} {m} mm) , ac , λ tx kx i′ → at-mark y tx i′ λ ul′ → nx ul′ (lat tx kx i′))
  back {m} (E.acc {q = m₀} {b = st₀} {a′ = instEmit (value a) n} a₀ y mm nx) lv fw with shown y (a , refl) lv fw
  ... | k , i , e₀ , tk , mt with match-val mt
  ...   | refl = inj₂ (k , m , i , ≼-refl {m} , pacc (back a₀ (live-before {m₀} {m} lv mm) (few-sub fw mm)) , λ _ kx i′ → img-mono i i′ kx)
    where
      pacc : Back m₀ (proj₁ st₀) → P.Acc k (f (proj₁ st₀) a)
      pacc (inj₁ (eq , none)) =
        subst (λ b → P.Acc k (f b a)) (sym eq) (P.acc₀ tk λ tx xk → img-out tx λ { (l′ , i′ , _ , ul′ , _) → nx ul′ (none tx i′) (img-mono i′ i xk) })
      pacc (inj₂ (k₀ , lk , i₀ , lkm , ac , lat)) =
        P.acc ac tk k₀k (λ tx k₀x xk → img-out tx λ { (l′ , i′ , _ , ul′ , _) → nx ul′ (lat tx k₀x i′) (img-mono i′ i xk) })
        where
          k₀k : k₀ ≺ k
          k₀k with ≼-or-≻ k k₀
          ... | inj₂ kk = kk
          ... | inj₁ kk with ≼-split {k} {k₀} kk
          ...   | inj₁ lt   = ⊥-elim (lkm (≺-trans {m₀} {m} {lk} mm (img-mono i i₀ lt)))
          ...   | inj₂ refl = ⊥-elim (lkm (subst (m₀ ≺_) (img-fun i i₀) mm))

  -- Read back at a carrier, the fold is the carried row's.
  back-at : ∀ {k l b a} → Back l b → t k (out a) → Img k l → P.Acc k b
  back-at {l = l} (inj₁ (_ , none)) tk i = ⊥-elim (≺-irrefl {l} (none tk i))
  back-at {k} {l} (inj₂ (k′ , lk , i′ , lkl , ac , lat)) tk i with ≼-or-≻ k k′
  ... | inj₂ k′k = ⊥-elim (≺-irrefl {l} (lat tk k′k i))
  ... | inj₁ kk with ≼-split {k} {k′} kk
  ...   | inj₁ lt   = ⊥-elim (lkl (img-mono i i′ lt))
  ...   | inj₂ refl = ac

  private
    -- The state at a value's row is one step past the state before it.
    out-at : ∀ {l st y} → E.Acc l st → u l (out y) → Σ (B × IE B) λ st₀ → st ≡ scanIE f st₀ y
    out-at (E.acc₀ y′ _) ul with funcU y′ ul
    ... | refl = _ , refl
    out-at (E.acc _ y′ _ _) ul with funcU y′ ul
    ... | refl = _ , refl

    shownU : ∀ {l e₁ e₁′} → u l e₁ → S′ l e₁′ → Shown (One stateValues) e₁′ → Shown (One valuesOf) e₁
    shownU ul (E.sval ac , _) sw with EF.acc-val ac
    ... | y , uy with funcU ul uy
    ...   | refl with out-at ac uy
    ...     | st₀ , refl = shown-ie {f = f} st₀ y sw
    shownU ul (E.send ue , _) _ with funcU ul ue
    ... | refl = tt
    shownU ul (E.sstep _ , _) ()
    shownU ul (E.spin _ , _)  ()

    -- A fold's row, carried at its value's carrier: the elaborated fold
    -- there, from a listing before it.
    sval-at : ∀ {k l b a e₁} → P.Acc k b → Live t k → t k (out a) → Img k l → u l e₁ → Listed u l
            → Match Every (One valuesOf) (Reads valuesOf) (out a) e₁
            → Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Listed S′ l × Match Every (One stateValues) (Reads stateValues) (out b) e′
    sval-at {a = a} ac lv tk i ul Lu mt with carried-val mt
    ... | n , refl with EL.fold-listed Lu ul
    ...   | st , eac with out-at eac ul
    ...     | st₀ , refl =
      out _ , (E.sval eac , reach-kin downU₀ (k-out {a = instEmit (value a) n} {b = scanIE f st₀ (instEmit (value a) n)}) (rchU ul)) , UL.lst→ Lu
      , (λ _ → _ , refl , cong (_∷ []) (sym (PF.acc-func refl ac (back-at (back eac (live i lv) (proj₁ Lu , proj₁ (proj₂ Lu))) tk i))))
      , λ ns → ⊥-elim (ns tt)

    send-at : ∀ {l e₁} → u l e₁ → Match Every (One valuesOf) (Reads valuesOf) end e₁
            → Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Match Every (One stateValues) (Reads stateValues) end e′
    send-at ul (cr , _) with cr tt
    ... | refl = end , (E.send ul , reach-kin downU₀ k-end (rchU ul)) , (λ _ → refl) , λ ns → ⊥-elim (ns tt)

    -- A skip carried into its instant, on the fold's rows.
    into : ∀ {k} → IntoAt Img u PB HP s k → IntoAt Img S′ PB HP s k
    into ((l , (_ , ul) , L , m) , h) = (l , (proj₁ (upL L ul) , proj₁ (proj₂ (upL L ul))) , UL.lst→ L , m) , at h
      where
        at : _ → _
        at (inj₁ e) = inj₁ e
        at (inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (_ , ul₀) , L₀))) =
          inj₂ (inj₁ (k₀ , l₀ , i , kk , ek , (proj₁ (upL L₀ ul₀) , proj₁ (proj₂ (upL L₀ ul₀))) , UL.lst→ L₀))
        at (inj₂ (inj₂ h)) = inj₂ (inj₂ h)

    img′ : ∀ {k e} → S k e → Unpinned e → Live S k → Listed S k → LP k
         → (Σ Pos λ l → Img k l × Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Listed S′ l × Match Every (One stateValues) (Reads stateValues) e e′)
           ⊎ (e ≡ skip × IntoAt Img S′ PB HP s k)
    img′ (P.sval ac , _) _ lv L lp with PF.acc-val ac
    ... | a , tk with img tk tt (liveS← lv) (lstS← L) lp
    ...   | inj₁ (l , i , e₁ , ul , Lu , mt) = inj₁ (l , i , sval-at ac (liveS← lv) tk i ul Lu mt)
    ...   | inj₂ (() , _)
    img′ (P.sstep x , _) _ lv L lp with img x tt (liveS← lv) (lstS← L) lp
    ... | inj₂ (_ , h) = inj₂ (refl , into h)
    ... | inj₁ (l , i , e₁ , ul , Lu , (_ , ns)) with upL Lu ul
    ...   | e₁′ , s₁ , _ = inj₁ (l , i , e₁′ , s₁ , UL.lst→ Lu , (λ ()) , λ _ sw → ns (λ ()) (shownU ul s₁ sw))
    img′ (P.send x , _) _ lv L lp with img x tt (liveS← lv) (lstS← L) lp
    ... | inj₂ (() , _)
    ... | inj₁ (l , i , e₁ , ul , Lu , (cr , _)) with cr tt
    ...   | refl = inj₁ (l , i , end , (E.send ul , reach-kin downU₀ k-end (rchU ul)) , UL.lst→ Lu , (λ _ → refl) , λ ns → ⊥-elim (ns tt))
    img′ (P.spin _ , _) () _ _ _

    img¬¬′ : ∀ {k e} → S k e → Unpinned e → Live S k → Few S k
           → ¬ ¬ ((Σ Pos λ l → Img k l × Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Match Every (One stateValues) (Reads stateValues) e e′) ⊎ e ≡ skip)
    img¬¬′ (P.sval ac , _) _ lv _ n with PF.acc-val ac
    ... | a , tk = img¬¬ tk tt (liveS← lv) (few-of tt tk) λ { (inj₁ (l , i , e₁ , ul , mt)) →
      few-¬¬listed (few-ofU (carried-unp mt) ul) λ Lu → let (e′ , s₁ , _ , m) = sval-at ac (liveS← lv) tk i ul Lu mt in n (inj₁ (l , i , e′ , s₁ , m))
      ; (inj₂ ()) }
    img¬¬′ (P.sstep x , _) _ lv _ n = img¬¬ x tt (liveS← lv) (few-of tt x) λ { (inj₁ (l , i , e₁ , ul , (_ , ns))) →
      upU ul λ { (e₁′ , s₁ , _) → n (inj₁ (l , i , e₁′ , s₁ , (λ ()) , λ _ sw → ns (λ ()) (shownU ul s₁ sw))) }
      ; (inj₂ _) → n (inj₂ refl) }
    img¬¬′ (P.send x , _) _ lv _ n = img¬¬ x tt (liveS← lv) (few-of tt x) λ { (inj₁ (l , i , e₁ , ul , m)) →
      let (e′ , s₁ , m′) = send-at ul m in n (inj₁ (l , i , e′ , s₁ , m′))
      ; (inj₂ ()) }
    img¬¬′ (P.spin _ , _) () _ _

    shown′ : ∀ {l e} → S′ l e → Shown (One stateValues) e → Live S′ l → Few S′ l
           → Σ Pos λ k → Img k l × Σ (Ev B) λ e₀ → S k e₀ × Match Every (One stateValues) (Reads stateValues) e₀ e
    shown′ (E.sval ac , _) sw lv fw with EF.acc-val ac
    ... | instEmit (value a) n , uy with out-at ac uy
    ...   | st₀ , refl with shown uy (a , refl) (UL.live← lv) (UL.few← fw)
    ...     | k , i , e₀ , tk , mt with match-val mt
    ...       | refl = k , i , out _ , (P.sval (back-at (back ac (UL.live← lv) (UL.few← fw)) tk i) , reach-kin down₀ (k-out {a = a} {b = f (proj₁ st₀) a}) (rch tk))
                       , (λ _ → _ , refl , refl) , λ ns → ⊥-elim (ns tt)
    shown′ (E.sval ac , _) sw lv fw | instEmit (mark _) n , uy with out-at ac uy
    ...   | st₀ , refl with sw
    ...     | _ , ()
    shown′ (E.send ue , _) _ lv fw with shown ue tt (UL.live← lv) (UL.few← fw)
    ... | k , i , e₀ , tk , mt with match-end mt
    ...   | refl = k , i , end , (P.send tk , reach-kin down₀ k-end (rch tk)) , (λ _ → refl) , λ ns → ⊥-elim (ns tt)
    shown′ (E.sstep _ , _) () _ _
    shown′ (E.spin _ , _)  () _ _

    placed′ : ∀ {m} → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near u m l)
                ⊎ Σ Pos (λ h → HE h × instantOf h ≡ instantOf m)
            → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l → Img k l × instantOf l ≡ instantOf m × Near S′ m l)
                ⊎ Σ Pos (λ h → HE h × instantOf h ≡ instantOf m)
    placed′ (inj₁ e)                                          = inj₁ e
    placed′ {m} (inj₂ (inj₁ (k , l , i , e , n))) = inj₂ (inj₁ (k , l , i , e , UL.near→ {m} {l} n))
    placed′ (inj₂ (inj₂ h))                       = inj₂ (inj₂ h)

    home′ : ∀ {k} → Home t k → Home S k
    home′ h n = h λ { (_ , tk , un) → up tk λ { (e′ , sk , kn) → n (e′ , sk , unp→ kn un) } }

    homed : ∀ {k p} → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home t k₀ × instantOf k₀ ≡ instantOf k) ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
          → instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home S k₀ × instantOf k₀ ≡ instantOf k) ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
    homed (inj₁ e)                        = inj₁ e
    homed (inj₂ (inj₁ (k₀ , kp , h , ek))) = inj₂ (inj₁ (k₀ , kp , home′ h , ek))
    homed (inj₂ (inj₂ hh))                = inj₂ (inj₂ hh)

    -- A pin of the scan is its source's, on both sides.
    spinS : ∀ {k r} → t k (pin r) → S k (pin r)
    spinS x = P.spin x , reach-kin down₀ k-pin (rch x)

    pinS↓ : ∀ {k r} → S k (pin r) → t k (pin r)
    pinS↓ (P.spin x , _) = x

    spinU : ∀ {l r} → u l (pin r) → S′ l (pin r)
    spinU x = E.spin x , reach-kin downU₀ k-pin (rchU x)

    pinU↓ : ∀ {l r} → S′ l (pin r) → u l (pin r)
    pinU↓ (E.spin x , _) = x

    pinned′ : ∀ {k p} → S k (pin p) → Listed S k → LP k
              → (Σ Pos λ l → Σ Pos λ p′ → S′ l (pin p′) × PB k l × Targeted M p p′ × Listed S′ l)
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home S k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ {k} {p} (P.spin x , _) L lp with pinned x (lstS← L) lp
    ... | (l , p′ , ul , m , b , ls) , h = (l , p′ , spinU ul , m , b , UL.lst→ {l} ls) , homed {k} {p} h


  scanned : CarryAt stateValues M HP HE LP S S′ s s′
  scanned = record
    { Img = Img ; ext = ext ; img = img′ ; img¬¬ = img¬¬′ ; shown = shown′
    ; img-row = λ i n → img-row i λ { (_ , tk , un) → up tk λ { (e′ , sk , kn) → n (e′ , sk , unp→ kn un) } }
    ; img-fun = img-fun
    ; place = λ {m} s₁ lv lm → placed′ {m} (place (proj₁ (proj₂ (downU s₁))) (UL.live← {m} (λ {c} → lv {c})) (UL.lst← {m} lm))
    ; live = λ {k} {l} i lv → UL.live→ {l} (λ {c} → live i (liveS← {k} (λ {c′} → lv {c′})) {c})
    ; few = λ i → fewS→ (few i)
    ; whole = λ wt ne lp → UL.whole→ (whole (wholeS← wt) (endedS← ne) lp)
    ; cover = λ {v} {w} L lp lv F → UL.lst→ {w} (cover (lstS← L) lp (liveS← {v} (λ {c} → lv {c}))
                λ tk lk vk m ul lw → up tk λ { (_ , sk , _) → upU ul λ { (_ , su , _) → F sk (liveS→ lk) vk m su lw } })
    ; bk = bk ; in-bk = in-bk ; PB = PB ; pb-few = λ s₁ → pb-few (proj₁ (proj₂ (downU s₁))) ; pinned = pinned′
    ; pb-img = pb-img
    ; pb-past = λ {k} pb sk lv s₁ → pb-past pb (proj₁ (proj₂ (down sk))) (λ un → liveS← {k} (λ {c} → lv (unp→ (proj₂ (proj₂ (down sk))) un) {c})) (proj₁ (proj₂ (downU s₁))) }

  -- A PIN IS CARRIED FROM ITS OWN PAST as its source's: a scan keeps
  -- every pin.
  narrowed : Narrow c → Narrow scanned
  narrowed nc = record { pinned↓ = pinned↓′ ; encl↓ = encl↓′ }
    where
      encl↓′ : ∀ {x x′ k l p p′} → Img x x′ → Listed S x → LP k → S k (pin p) → T (inside p x) → x ≺ k
             → S′ l (pin p′) → PB k l → Encl S x k → Encl S′ x′ l
      encl↓′ i L lp sk ix xk sl pb E =
        encl-map {a = u} {b = S′} (λ {l′} {r} → spinU {l′} {r}) (λ {l′} {r} → pinU↓ {l′} {r})
          (Narrow.encl↓ nc i (lstS← L) lp (pinS↓ sk) ix xk (pinU↓ sl) pb
            (encl-map {a = S} {b = t} (λ {k′} {r} → pinS↓ {k′} {r}) (λ {k′} {r} → spinS {k′} {r}) E))

      pinned↓′ : ∀ {k p} → S k (pin p) → Listed S p → PinList S p k → LP p
               → (Σ Pos λ l → Σ Pos λ p′ → S′ l (pin p′) × PB k l × Targeted M p p′ × PinList S′ p′ l)
                 × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home S k₀ × instantOf k₀ ≡ instantOf k)
                    ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
      pinned↓′ {k} {p} (P.spin x , _) L Pk lp
        with Narrow.pinned↓ nc x (lstS← L) (pins-map {a = S} {b = t} (λ {k′} → pinS↓ {k′}) (λ {k′} → spinS {k′}) Pk) lp
      ... | (l , p′ , ul , m , b , Pu) , h =
        (l , p′ , spinU ul , m , b , pins-map {a = u} {b = S′} (λ {l′} → spinU {l′}) (λ {l′} → pinU↓ {l′}) Pu) , homed {k} {p} h

  -- Its rows carried into their instant are its source's.
  pb-down : ∀ {k l e₀} → PB k l → S k e₀ → (Unpinned e₀ → Live S k) → PB k l × Σ (Ev A) λ e → t k e × (Unpinned e → Live t k)
  pb-down {k} pb sk lv = pb , _ , proj₁ (proj₂ (down sk)) , λ un → liveS← {k} (λ {c₁} → lv (unp→ (proj₂ (proj₂ (down sk))) un) {c₁})

------------------------------------------------------------------------
-- The former

private
  -- A scan's row is its source's.
  scan-row : ∀ {A B : Set} {f : B → A → B} {z : B} {t : EmissionSet A} {q e} → Scan.ScanT f z t q e → Σ (Ev A) (t q)
  scan-row (Scan.sval (Scan.acc₀ x _))    = _ , x
  scan-row (Scan.sval (Scan.acc _ x _ _)) = _ , x
  scan-row (Scan.sstep x)                 = _ , x
  scan-row (Scan.spin x)                  = _ , x
  scan-row (Scan.send x)                  = _ , x

  sh-proj : ∀ {B : Set} (e : Ev (B × IE B)) → Shown (One valuesOf) (mapEv proj₂ e) → Shown (One stateValues) e
  sh-proj (out _) sw = sw
  sh-proj end     _  = tt
  sh-proj skip    ()
  sh-proj (pin _) ()

  match-proj : ∀ {B : Set} {e₀ : Ev B} (e₁ : Ev (B × IE B)) → Match Every (One stateValues) (Reads stateValues) e₀ e₁
             → Match Every (One valuesOf) (Reads valuesOf) e₀ (mapEv proj₂ e₁)
  match-proj {e₀ = out _} e₁ (cr , ns) = (λ sh → let (x , eq , r) = cr sh in proj₂ x , cong (mapEv proj₂) eq , r) , λ n sw → ns n (sh-proj e₁ sw)
  match-proj {e₀ = end}   e₁ (cr , ns) = (λ sh → cong (mapEv proj₂) (cr sh)) , λ n sw → ns n (sh-proj e₁ sw)
  match-proj {e₀ = skip}  e₁ (_ , ns)  = (λ ()) , λ n sw → ns n (sh-proj e₁ sw)
  match-proj {e₀ = pin _} e₁ (_ , ns)  = (λ ()) , λ n sw → ns n (sh-proj e₁ sw)

module ScanCarry {A B} (f : B → A → B) z (d : Den A) (d′ : Den (IE A)) {M HP HE LP H₁ H₂} p p′ (hm : Emb M)
                 (It : InvAt H₁ p (enter d p)) (Iu : InvAt H₂ p′ (enter d′ p′))
                 (c : CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′) where
  private
    module W = MapRun proj₂ (Op.scan (scanIE f) (z , marked begin) d′) p′
    module K = Core f z hm (λ {q} {e} → entered-reach d p {q} {e}) (λ {q} {e} → entered-reach d′ p′ {q} {e}) It Iu c
    module R = Relabel (λ _ e e′ → e′ ≡ e) (λ _ e e′ → e′ ≡ mapEv proj₂ e)
      (λ { {e = e} refl → kin-refl e }) (λ { {e = e} refl → kin-map e })
      (λ tk → _ , tk , refl) (λ tk → _ , tk , refl) (λ _ ul → _ , W.lift ul , refl) (λ ul n → n (_ , W.lift ul , refl)) W.lift W.lift W.unmap
      K.scanned
      (λ { {e = e} refl sw → sh-proj e sw }) (λ { {e₁ = e₁} _ refl refl m → match-proj e₁ m })

  carried : CarryAt valuesOf M HP HE LP (enter (Op.scan f z d) p) (enter (Op.map proj₂ (Op.scan (scanIE f) (z , marked begin) d′)) p′) p p′
  carried = R.carried

  narrowed : Narrow c → Narrow carried
  narrowed nc = R.narrowed (K.narrowed nc)

-- THE ELABORATED SCAN CARRIES the plain one: its state's emit, projected,
-- carries the plain fold.
scan-carry : ∀ {A B} (f : B → A → B) z (d : Den A) (d′ : Den (IE A)) {M HP HE LP H₁ H₂} p p′ → Emb M
           → InvAt H₁ p (enter d p) → InvAt H₂ p′ (enter d′ p′)
           → CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′
           → CarryAt valuesOf M HP HE LP (enter (Op.scan f z d) p) (enter (Op.map proj₂ (Op.scan (scanIE f) (z , marked begin) d′)) p′) p p′
scan-carry f z d d′ p p′ hm It Iu c = ScanCarry.carried f z d d′ p p′ hm It Iu c

scan-narrow : ∀ {A B} (f : B → A → B) z (d : Den A) (d′ : Den (IE A)) {M HP HE LP H₁ H₂} p p′ (hm : Emb M)
            → (It : InvAt H₁ p (enter d p)) (Iu : InvAt H₂ p′ (enter d′ p′))
            → (c : CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′)
            → Narrow c → Narrow (scan-carry f z d d′ p p′ hm It Iu c)
scan-narrow f z d d′ p p′ hm It Iu c = ScanCarry.narrowed f z d d′ p p′ hm It Iu c

carry-scan : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → Carry m ρ s → Carry m ρ (scan f z s)
carry-scan n ρ f z s (carry h) = carry λ envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr →
  scanned envP envE gP gE M₀ er p p′ okP okE (h envP envE gP gE M₀ hm er jn ns ap p p′ m₀ okP okE nh fr)
  where
    scanned : ∀ envP envE → GoodEnv envP → GoodEnv envE → ∀ M₀ (er : EnvRel M₀ ρ envP envE) p p′ → Ok (Hots envP) p → Ok (Hots envE) p′
            → CarriesAt n ρ s envP envE M₀ er p p′ → CarriesAt n ρ (scan f z s) envP envE M₀ er p p′
    scanned envP envE gP gE M₀ er p p′ okP okE (M , ms , hm′ , wi , br , jn′ , ep , c , nc , nr) =
      M , ms , hm′ , wi , (λ tk → br (proj₂ (scan-row (proj₁ tk)))) , jn′ , ep , c′
      , nest-via {er = er} {c = c} {c′ = c′} (λ m → m)
          (λ {k} {l} {e₀} → Core.pb-down f z hm′ (λ {q} {e} → entered-reach (approx n s envP) p {q} {e})
             (λ {q} {e} → entered-reach (approx n (elab ρ s) envE) p′ {q} {e}) (inv-approx n s envP gP p okP) (inv-approx n (elab ρ s) envE gE p′ okE) c {k} {l} {e₀})
          nc
      , scan-narrow f z (approx n s envP) (approx n (elab ρ s) envE) p p′ hm′ (inv-approx n s envP gP p okP) (inv-approx n (elab ρ s) envE gE p′ okE) c nr
      where
        c′ : CarryAt valuesOf M (Hots envP) (Hots envE) (HotsListed envP) (enter (approx n (scan f z s) envP) p) (enter (approx n (elab ρ (scan f z s)) envE) p′) p p′
        c′ = scan-carry f z (approx n s envP) (approx n (elab ρ s) envE) p p′ hm′ (inv-approx n s envP gP p okP) (inv-approx n (elab ρ s) envE gE p′ okE) c
