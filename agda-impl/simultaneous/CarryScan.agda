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
open import Data.List using (List; []; _∷_; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Relation.Nullary.Decidable.Core using (¬¬-excluded-middle)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Tree using (scan)
open import denotation.Position using (Pos; _<ᵖ_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; enter; Truncate; Reach; Dep; Few; _≺_; _≼_;
  Unpinned; module Scan; module Op; approx)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≼-split; reach-via; reach-few; few-ind;
  entered-reach)
open import denotation.Laws.Worlds using (InvAt; full)
open import denotation.Laws.Worlds.Leaves using (module AccF)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Shows using (∈-stable)
open import denotation.Laws using (inv-approx)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.InstEmit using (valuesOf; instEmit; value; mark; begin)
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Carry using (PMap; Emb; CarryAt; Carry; carry; Kin; k-out; k-skip; k-pin; k-end; unp→; kin-map;
  module Relabel; module Mono; Owes; Home; row; env; both; subs)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; AIE; elab; scanIE; marked)

-- The label of an elaborated scan: the values of the emit it passes.
stateValues : ∀ {B : Set} → B × IE B → List B
stateValues x = valuesOf (proj₂ x)

------------------------------------------------------------------------
-- Rows of a set and of an operator over it

private
  -- What a row of `b` waits on, a row of `a` it came from waits on.
  dep : ∀ {X Y : Set} {q k} {e₀ e : Ev X} {e₀′ e′ : Ev Y} → Kin e₀ e₀′ → Kin e e′ → Dep q e₀′ k e′ → Dep q e₀ k e
  dep k-out  _ _ = tt
  dep k-skip _ _ = tt
  dep k-end  _ _ = tt
  dep k-pin  kn d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ refl with kn
  ...   | k-pin = inj₂ refl

  -- Each row of `b` from a row of `a` of its kind: what a row of `b`
  -- waits on is as few as what its row of `a` does.
  reach-kin : ∀ {X Y : Set} {a : EmissionSet X} {b : EmissionSet Y} → (∀ {k e′} → b k e′ → Σ (Ev X) λ e → a k e × Kin e e′)
            → ∀ {q e e′} → Kin e e′ → Reach a q e → Reach b q e′
  reach-kin dn kq = reach-via (λ y _ d → let (e , x , kn) = dn y in e , x , dep kq kn d)

  -- Few rows before a row, classically listed.
  few-¬¬listed : ∀ {X : Set} {a : EmissionSet X} {q} → Few a q → ¬ ¬ Listed a q
  few-¬¬listed {X} {a} {q} (ks , F) n = go ks λ ls G B → n (ls , (λ y kq → G (F y kq) kq (_ , y)) , B)
    where
      go : ∀ ks → (∀ ls → (∀ {k} → k ∈ ks → k ≺ q → Σ (Ev X) (a k) → k ∈ ls) → (∀ {k} → k ∈ ls → k ≺ q × Σ (Ev X) (a k)) → ⊥) → ⊥
      go []       κ = κ [] (λ ()) (λ ())
      go (k ∷ ks) κ = go ks λ ls G B → ¬¬-excluded-middle {A = k ≺ q × Σ (Ev X) (a k)} λ
        { (yes h) → κ (k ∷ ls) (λ { (here refl) _ _ → here refl ; (there m) kq r → there (G m kq r) }) (λ { (here refl) → h ; (there m) → B m })
        ; (no ¬h) → κ ls (λ { (here refl) kq r → ⊥-elim (¬h (kq , r)) ; (there m) → G m }) B }

  -- The rows listed before a row listed before.
  sub-listed : ∀ {X : Set} {a : EmissionSet X} {w v} → Listed a w → v ≺ w → Listed a v
  sub-listed {w = w} {v} (ks , F , B) vw =
    filter (λ k → T? (k <ᵖ v)) ks
    , (λ {k} y kv → ∈-filter⁺ (λ k → T? (k <ᵖ v)) (F y (≺-trans {k} {v} {w} kv vw)) kv)
    , λ m → let (m′ , kv) = ∈-filter⁻ (λ k → T? (k <ᵖ v)) m in kv , proj₂ (B m′)

  -- The plain row a carrier shows a value of is that value.
  match-val : ∀ {A : Set} {e₀ : Ev A} {a} {n : Pos} → Match Every (One valuesOf) (Reads valuesOf) e₀ (out (instEmit (value a) n)) → e₀ ≡ out a
  match-val {e₀ = out _} (cr , _) with cr tt
  ... | _ , refl , refl = refl
  match-val {e₀ = end}   (cr , _) with cr tt
  ... | ()
  match-val {e₀ = skip}  (_ , ns) = ⊥-elim (ns (λ ()) (_ , refl))
  match-val {e₀ = pin _} (_ , ns) = ⊥-elim (ns (λ ()) (_ , refl))

  -- The carrier of a plain value shows it.
  carried-val : ∀ {A : Set} {a : A} {e₁ : Ev (IE A)} → Match Every (One valuesOf) (Reads valuesOf) (out a) e₁
              → Σ Pos λ n → e₁ ≡ out (instEmit (value a) n)
  carried-val (cr , _) with cr tt
  ... | instEmit (value _) n , refl , refl = n , refl
  ... | instEmit (mark _) _  , refl , ()

  -- The carrier of a plain value is unpinned.
  carried-unp : ∀ {A : Set} {a : A} {e₁ : Ev (IE A)} → Match Every (One valuesOf) (Reads valuesOf) (out a) e₁ → Unpinned e₁
  carried-unp mt with carried-val mt
  ... | _ , refl = tt

  -- The plain row carried by an end is an end.
  match-end : ∀ {A : Set} {e₀ : Ev A} → Match Every (One {X = IE A} valuesOf) (Reads valuesOf) e₀ end → e₀ ≡ end
  match-end {e₀ = out _} (cr , _) with cr tt
  ... | _ , () , _
  match-end {e₀ = end}   _        = refl
  match-end {e₀ = skip}  (_ , ns) = ⊥-elim (ns (λ ()) tt)
  match-end {e₀ = pin _} (_ , ns) = ⊥-elim (ns (λ ()) tt)

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

    -- The latest value among rows listed before `w`, decided: each comes
    -- with its event, which is the only one there.
    Latest : Pos → List Pos → Set
    Latest w ks = (∀ {k y} → k ∈ ks → u k (out y) → ⊥)
                ⊎ Σ Pos λ v → Σ (IE A) (λ y → u v (out y)) × v ≺ w × (∀ {k y} → k ∈ ks → u k (out y) → k ≼ v)

    keep : ∀ {w k ks} → Latest w ks → (∀ {y} → u k (out y) → ⊥) → Latest w (k ∷ ks)
    keep (inj₁ none) nk = inj₁ λ { (here refl) uy → nk uy ; (there m) → none m }
    keep (inj₂ (v , vy , vw , mx)) nk = inj₂ (v , vy , vw , λ { (here refl) uy → ⊥-elim (nk uy) ; (there m) → mx m })

    latest : ∀ {w} ks → (∀ {k} → k ∈ ks → k ≺ w × Σ (Ev (IE A)) (u k)) → Latest w ks
    latest []       B = inj₁ λ ()
    latest (k ∷ ks) B with latest ks (λ m → B (there m)) | B (here refl)
    ... | inj₁ none | kw , out y , uk =
      inj₂ (k , (y , uk) , kw , λ { (here refl) _ → ≼-refl {k} ; (there m) uy → ⊥-elim (none m uy) })
    ... | inj₂ (v , vy , vw , mx) | kw , out y , uk with ≼-or-≻ v k
    ...   | inj₁ vk = inj₂ (k , (y , uk) , kw , λ { (here refl) _ → ≼-refl {k} ; {k′} (there m) uy → ≼-trans {k′} {v} {k} (mx m uy) vk })
    ...   | inj₂ kv = inj₂ (v , vy , vw , λ { (here refl) _ → ≺→≼ {k} {v} kv ; (there m) → mx m })
    latest (k ∷ ks) B | L | kw , skip , uk = keep L λ uy → not-out (funcU uk uy)
      where not-out : ∀ {y} → skip ≡ out y → ⊥
            not-out ()
    latest (k ∷ ks) B | L | kw , end , uk = keep L λ uy → not-out (funcU uk uy)
      where not-out : ∀ {y} → end ≡ out y → ⊥
            not-out ()
    latest (k ∷ ks) B | L | kw , pin _ , uk = keep L λ uy → not-out (funcU uk uy)
      where not-out : ∀ {r y} → pin r ≡ out y → ⊥
            not-out ()

    -- THE ELABORATED FOLD, from a listing: from the latest value before
    -- the row, or from none.
    eacc : ∀ {w} → Listed u w → ∀ {x} → u w (out x) → Σ (B × IE B) (E.Acc w)
    eacc L = few-ind {t = u} (λ w → Listed u w → ∀ {x} → u w (out x) → Σ (B × IE B) (E.Acc w)) step (proj₁ L , proj₁ (proj₂ L)) L
      where
        step : ∀ {w} → Few u w → (∀ {v e} → u v e → v ≺ w → Listed u v → ∀ {x} → u v (out x) → Σ (B × IE B) (E.Acc v))
             → Listed u w → ∀ {x} → u w (out x) → Σ (B × IE B) (E.Acc w)
        step {w} _ ih (ks , F , B) {x} ux with latest ks B
        ... | inj₁ none = _ , E.acc₀ ux (λ uy kw → none (F uy kw) uy)
        ... | inj₂ (v , (y , uv) , vw , mx) with ih uv vw (sub-listed (ks , F , B) vw) uv
        ...   | st , av = _ , E.acc av ux vw (λ uy vk kw → mx (F uy kw) uy vk)

    upL : ∀ {l e} → Listed u l → u l e → Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Kin e e′
    upL {e = out y} L x = out _ , (E.sval (proj₂ (eacc L x)) , reach-kin downU₀ (k-out {a = y} {b = proj₁ (eacc L x)}) (rchU x)) , k-out
    upL {e = skip}  L x = skip , (E.sstep x , reach-kin downU₀ k-skip (rchU x)) , k-skip
    upL {e = pin r} L x = pin r , (E.spin x , reach-kin downU₀ k-pin (rchU x)) , k-pin
    upL {e = end}   L x = end , (E.send x , reach-kin downU₀ k-end (rchU x)) , k-end

    ----------------------------------------------------------------------
    -- Ends, few rows and listings across the scan

    liveS← : ∀ {k} → Live S k → Live t k
    liveS← lv tc = lv (P.send tc , reach-kin down₀ k-end (rch tc))

    liveU← : ∀ {l} → Live S′ l → Live u l
    liveU← lv uc = lv (E.send uc , reach-kin downU₀ k-end (rchU uc))

    liveU→ : ∀ {l} → Live u l → Live S′ l
    liveU→ lv (E.send uc , _) = lv uc

    fewS→ : ∀ {k} → Few t k → Few S k
    fewS→ (ks , F) = ks , λ y kk → F (proj₁ (proj₂ (down y))) kk

    fewU← : ∀ {l} → Few S′ l → Few u l
    fewU← (ks , F) = ks , λ y kk → ∈-stable λ ni → upU y λ { (_ , y′ , _) → ni (F y′ kk) }

    lstS← : ∀ {k} → Listed S k → Listed t k
    lstS← (ks , F , B) = ks , (λ y kk → ∈-stable λ ni → up y λ { (_ , y′ , _) → ni (F y′ kk) })
                       , λ m → proj₁ (B m) , _ , proj₁ (proj₂ (down (proj₂ (proj₂ (B m)))))

    lstU→ : ∀ {l} → Listed u l → Listed S′ l
    lstU→ (ks , F , B) = ks , (λ y kk → F (proj₁ (proj₂ (downU y))) kk)
                       , λ m → proj₁ (B m) , _ , proj₁ (proj₂ (upL (sub-listed (ks , F , B) (proj₁ (B m))) (proj₂ (proj₂ (B m)))))

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
    img-out tx n = img¬¬ tx tt (live-out tx) (few-of tt tx) λ { (_ , i , _ , ul , mt) → n (img-val i ul mt) }

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

    few-before : ∀ {m₀ m} → Few u m → m₀ ≺ m → Few u m₀
    few-before {m₀} {m} (ks , F) mm = ks , λ {k} y km → F y (≺-trans {k} {m₀} {m} km mm)

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
  back {m} (E.acc {q = m₀} {a′ = instEmit (mark _) n} a₀ y mm nx) lv fw with back a₀ (live-before {m₀} {m} lv mm) (few-before fw mm)
  ... | inj₁ (eq , none) = inj₁ (eq , λ tx i′ → at-mark y tx i′ λ ul′ → nx ul′ (none tx i′))
  ... | inj₂ (k , lk , i , lkm , ac , lat) =
    inj₂ (k , lk , i , ≼-trans {lk} {m₀} {m} lkm (≺→≼ {m₀} {m} mm) , ac , λ tx kx i′ → at-mark y tx i′ λ ul′ → nx ul′ (lat tx kx i′))
  back {m} (E.acc {q = m₀} {b = st₀} {a′ = instEmit (value a) n} a₀ y mm nx) lv fw with shown y (a , refl) lv fw
  ... | k , i , e₀ , tk , mt with match-val mt
  ...   | refl = inj₂ (k , m , i , ≼-refl {m} , pacc (back a₀ (live-before {m₀} {m} lv mm) (few-before fw mm)) , λ _ kx i′ → img-mono i i′ kx)
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
    ... | n , refl with eacc Lu ul
    ...   | st , eac with out-at eac ul
    ...     | st₀ , refl =
      out _ , (E.sval eac , reach-kin downU₀ (k-out {a = instEmit (value a) n} {b = scanIE f st₀ (instEmit (value a) n)}) (rchU ul)) , lstU→ Lu
      , (λ _ → _ , refl , cong (_∷ []) (sym (PF.acc-func refl ac (back-at (back eac (live i lv) (proj₁ Lu , proj₁ (proj₂ Lu))) tk i))))
      , λ ns → ⊥-elim (ns tt)

    send-at : ∀ {l e₁} → u l e₁ → Match Every (One valuesOf) (Reads valuesOf) end e₁
            → Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Match Every (One stateValues) (Reads stateValues) end e′
    send-at ul (cr , _) with cr tt
    ... | refl = end , (E.send ul , reach-kin downU₀ k-end (rchU ul)) , (λ _ → refl) , λ ns → ⊥-elim (ns tt)

    img′ : ∀ {k e} → S k e → Unpinned e → Live S k → Listed S k → LP k
         → Σ Pos λ l → Img k l × Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Listed S′ l × Match Every (One stateValues) (Reads stateValues) e e′
    img′ (P.sval ac , _) _ lv L lp with PF.acc-val ac
    ... | a , tk with img tk tt (liveS← lv) (lstS← L) lp
    ...   | l , i , e₁ , ul , Lu , mt = l , i , sval-at ac (liveS← lv) tk i ul Lu mt
    img′ (P.sstep x , _) _ lv L lp with img x tt (liveS← lv) (lstS← L) lp
    ... | l , i , e₁ , ul , Lu , (_ , ns) with upL Lu ul
    ...   | e₁′ , s₁ , _ = l , i , e₁′ , s₁ , lstU→ Lu , (λ ()) , λ _ sw → ns (λ ()) (shownU ul s₁ sw)
    img′ (P.send x , _) _ lv L lp with img x tt (liveS← lv) (lstS← L) lp
    ... | l , i , e₁ , ul , Lu , (cr , _) with cr tt
    ...   | refl = l , i , end , (E.send ul , reach-kin downU₀ k-end (rchU ul)) , lstU→ Lu , (λ _ → refl) , λ ns → ⊥-elim (ns tt)
    img′ (P.spin _ , _) () _ _ _

    img¬¬′ : ∀ {k e} → S k e → Unpinned e → Live S k → Few S k
           → ¬ ¬ Σ Pos λ l → Img k l × Σ (Ev (B × IE B)) λ e′ → S′ l e′ × Match Every (One stateValues) (Reads stateValues) e e′
    img¬¬′ (P.sval ac , _) _ lv _ n with PF.acc-val ac
    ... | a , tk = img¬¬ tk tt (liveS← lv) (few-of tt tk) λ { (l , i , e₁ , ul , mt) →
      few-¬¬listed (few-ofU (carried-unp mt) ul) λ Lu → let (e′ , s₁ , _ , m) = sval-at ac (liveS← lv) tk i ul Lu mt in n (l , i , e′ , s₁ , m) }
    img¬¬′ (P.sstep x , _) _ lv _ n = img¬¬ x tt (liveS← lv) (few-of tt x) λ { (l , i , e₁ , ul , (_ , ns)) →
      upU ul λ { (e₁′ , s₁ , _) → n (l , i , e₁′ , s₁ , (λ ()) , λ _ sw → ns (λ ()) (shownU ul s₁ sw)) } }
    img¬¬′ (P.send x , _) _ lv _ n = img¬¬ x tt (liveS← lv) (few-of tt x) λ { (l , i , e₁ , ul , m) →
      let (e′ , s₁ , m′) = send-at ul m in n (l , i , e′ , s₁ , m′) }
    img¬¬′ (P.spin _ , _) () _ _

    shown′ : ∀ {l e} → S′ l e → Shown (One stateValues) e → Live S′ l → Few S′ l
           → Σ Pos λ k → Img k l × Σ (Ev B) λ e₀ → S k e₀ × Match Every (One stateValues) (Reads stateValues) e₀ e
    shown′ (E.sval ac , _) sw lv fw with EF.acc-val ac
    ... | instEmit (value a) n , uy with out-at ac uy
    ...   | st₀ , refl with shown uy (a , refl) (liveU← lv) (fewU← fw)
    ...     | k , i , e₀ , tk , mt with match-val mt
    ...       | refl = k , i , out _ , (P.sval (back-at (back ac (liveU← lv) (fewU← fw)) tk i) , reach-kin down₀ (k-out {a = a} {b = f (proj₁ st₀) a}) (rch tk))
                       , (λ _ → _ , refl , refl) , λ ns → ⊥-elim (ns tt)
    shown′ (E.sval ac , _) sw lv fw | instEmit (mark _) n , uy with out-at ac uy
    ...   | st₀ , refl with sw
    ...     | _ , ()
    shown′ (E.send ue , _) _ lv fw with shown ue tt (liveU← lv) (fewU← fw)
    ... | k , i , e₀ , tk , mt with match-end mt
    ...   | refl = k , i , end , (P.send tk , reach-kin down₀ k-end (rch tk)) , (λ _ → refl) , λ ns → ⊥-elim (ns tt)
    shown′ (E.sstep _ , _) () _ _
    shown′ (E.spin _ , _)  () _ _

    owes′ : ∀ {c r} → Owes M HE t s′ c r → Owes M HE S s′ c r
    owes′ {row k}    (nr , y)  = (λ n → nr λ { (_ , tk) → up tk λ { (_ , sk , _) → n (_ , sk) } }) , y
    owes′ {env h}    o         = o
    owes′ {both k h} (nr , hy) = (λ n → nr λ { (_ , tk) → up tk λ { (_ , sk , _) → n (_ , sk) } }) , hy
    owes′ {subs}     o         = o

    home′ : ∀ {k} → Home t k → Home S k
    home′ h n = h λ { (_ , tk , un) → up tk λ { (e′ , sk , kn) → n (e′ , sk , unp→ kn un) } }

    pinned′ : ∀ {k p} → S k (pin p) → Live S k → (Σ Pos λ l → Σ Pos λ p′ → S′ l (pin p′) × k ∈ pbk l)
              × (instantOf k ≡ instantOf s ⊎ (Σ Pos λ k₀ → k₀ ≺ p × Home S k₀ × instantOf k₀ ≡ instantOf k)
                 ⊎ Σ Pos λ h → HP h × instantOf h ≡ instantOf k)
    pinned′ {k} {p} (P.spin x , _) lv with pinned x (liveS← lv)
    ... | (l , p′ , ul , m) , inj₁ e                          = (l , p′ , (E.spin ul , reach-kin downU₀ k-pin (rchU ul)) , m) , inj₁ e
    ... | (l , p′ , ul , m) , inj₂ (inj₁ (k₀ , kp , h , ek)) = (l , p′ , (E.spin ul , reach-kin downU₀ k-pin (rchU ul)) , m) , inj₂ (inj₁ (k₀ , kp , home′ h , ek))
    ... | (l , p′ , ul , m) , inj₂ (inj₂ hh)                 = (l , p′ , (E.spin ul , reach-kin downU₀ k-pin (rchU ul)) , m) , inj₂ (inj₂ hh)

  scanned : CarryAt stateValues M HP HE LP S S′ s s′
  scanned = record
    { Img = Img ; ext = ext ; img = img′ ; img¬¬ = img¬¬′ ; shown = shown′
    ; img-row = λ i n → img-row i λ { (_ , tk , un) → up tk λ { (e′ , sk , kn) → n (e′ , sk , unp→ kn un) } }
    ; img-fun = img-fun
    ; place = λ {m} s₁ lv fw → place (proj₁ (proj₂ (downU s₁))) (liveU← {m} (λ {c} → lv {c})) (fewU← fw)
    ; live = λ {k} {l} i lv → liveU→ {l} (λ {c} → live i (liveS← {k} (λ {c′} → lv {c′})) {c})
    ; few = λ i → fewS→ (few i)
    ; cause = λ s₁ → cause (proj₁ (proj₂ (downU s₁)))
    ; owes = λ s₁ → owes′ (owes (proj₁ (proj₂ (downU s₁))))
    ; fib = fib
    ; in-fib = λ s₁ → in-fib (proj₁ (proj₂ (downU s₁)))
    ; read = λ {r} s₁ rd → liveU→ {r} (λ {c} → read (proj₁ (proj₂ (downU s₁))) rd {c})
    ; bk = bk ; in-bk = in-bk ; pbk = pbk ; pinned = pinned′ }

------------------------------------------------------------------------
-- The former

private
  kin-refl : ∀ {X : Set} (e : Ev X) → Kin e e
  kin-refl (out _) = k-out
  kin-refl skip    = k-skip
  kin-refl (pin _) = k-pin
  kin-refl end     = k-end

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

-- THE ELABORATED SCAN CARRIES the plain one: its state's emit, projected,
-- carries the plain fold.
scan-carry : ∀ {A B} (f : B → A → B) z (d : Den A) (d′ : Den (IE A)) {M HP HE LP H₁ H₂} p p′ → Emb M
           → InvAt H₁ p (enter d p) → InvAt H₂ p′ (enter d′ p′)
           → CarryAt valuesOf M HP HE LP (enter d p) (enter d′ p′) p p′
           → CarryAt valuesOf M HP HE LP (enter (Op.scan f z d) p) (enter (Op.map proj₂ (Op.scan (scanIE f) (z , marked begin) d′)) p′) p p′
scan-carry f z d d′ p p′ hm It Iu c =
  Relabel.carried (λ _ e e′ → e′ ≡ e) (λ _ e e′ → e′ ≡ mapEv proj₂ e)
    (λ { {e = e} refl → kin-refl e }) (λ { {e = e} refl → kin-map e })
    (λ tk → _ , tk , refl) (λ tk → _ , tk , refl) (λ ul → _ , W.lift ul , refl) W.unmap
    (Core.scanned f z hm (λ {q} {e} → entered-reach d p {q} {e}) (λ {q} {e} → entered-reach d′ p′ {q} {e}) It Iu c)
    (λ { {e = e} refl sw → sh-proj e sw }) (λ { {e₁ = e₁} _ refl refl m → match-proj e₁ m })
  where
    module W = MapRun proj₂ (Op.scan (scanIE f) (z , marked begin) d′) p′

carry-scan : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → Carry m ρ s → Carry m ρ (scan f z s)
carry-scan n ρ f z s (carry h) = carry λ envP envE gP gE M₀ hm er p p′ m₀ okP okE fr →
  let (M , ms , hm′ , wi , c) = h envP envE gP gE M₀ hm er p p′ m₀ okP okE fr
  in M , ms , hm′ , wi , scan-carry f z (approx n s envP) (approx n (elab ρ s) envE) p p′ hm′
       (inv-approx n s envP gP p okP) (inv-approx n (elab ρ s) envE gE p′ okE) c
