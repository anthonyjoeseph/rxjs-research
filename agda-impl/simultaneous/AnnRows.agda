{-# OPTIONS --guardedness #-}

-- THE ANNOTATED SOURCE'S ROWS, against the source's.  `annotate S` at
-- `q` maps `S` at `q ⊕ [ ix 1 ]` (`σₑ`) to maybe-emits, tells its end by
-- `nothing` (`simultaneous.ToldRows`), folds routes over the told run and
-- keeps each step's emit beside the routes before it.  A value of `σₑ` at
-- `l` shows again at `l ⊕ [ sub w ]`, its end at `c₁ l`; every other
-- annotated row shows nothing, and lies in the subscribe instant or under
-- a row of `σₑ`.
module simultaneous.AnnRows where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; all?; tabulate; lookup)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (T?; ¬?)

open import Tree using (Obs; map)
open import denotation.Position using (_≟ᵖ_; _<ᵖ_; Pos; ix; sub; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Few; Proper; Den; DenEnv; enter; approx; _≺_;
  module Op; module Scan)
open import denotation.Laws using (inv-approx)
open import denotation.Laws.Modulus using (≺-trans; ≼-split)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; InvAt; _⊑_; ⊑-≼; ok-step)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Listing using (Listed)
open import simultaneous.HeldMap using (mapEv; module MapRun)
open import simultaneous.HeldScan using (module ScanRun)
open import simultaneous.ReadFold using (foldᵈ)
open import simultaneous.Sim using (annValues)
open import simultaneous.ToldRows using (told; module Told)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; annStep; annotate)

module Ann {Γ A} n (S : Obs Timeline Γ (IE A)) (env : DenEnv Γ) (genv : GoodEnv env) (q : Pos) (ok : Ok (Hots env) q) where
  module Tl = Told n (map just S) nothing env genv q ok
  open Tl public using (w; c₁; fixedL; imgs; imgs-⊑; img-≺; img-≼; fixed-≺)

  -- The source, and the source annotated.
  σₑ : EmissionSet (IE A)
  σₑ = enter (approx n S env) (q ⊕ [ ix 1 ])

  σ′ : EmissionSet (AIE A)
  σ′ = enter (approx n (annotate S) env) q

  private
    module Mj = MapRun just (approx n S env) (q ⊕ [ ix 1 ])

    z₀ : Routes × AIE A
    z₀ = (root , 0) , ((root , 0) , nothing)

    D : Den (Maybe (IE A))
    D = approx n (told nothing (map just S)) env

    module Sr = ScanRun annStep z₀ D q
    module Mr = MapRun proj₂ (Op.scan annStep z₀ D) q

    Iτ : InvAt (Hots env) q Tl.τ
    Iτ = inv-approx n (told nothing (map just S)) env genv q ok

    τ-func : ∀ {y e e′} → Tl.τ y e → Tl.τ y e′ → e ≡ e′
    τ-func {y} {e} {e′} = InvAt.func Iτ {y} {e} {e′}

  -- The source's invariant.
  Iₑ : InvAt (Hots env) (q ⊕ [ ix 1 ]) σₑ
  Iₑ = inv-approx n S env genv (q ⊕ [ ix 1 ]) (ok-step q ok)

  -- The annotated source's invariant.
  Iσ′ : InvAt (Hots env) q σ′
  Iσ′ = inv-approx n (annotate S) env genv q ok

  ------------------------------------------------------------------------
  -- The source and the told run's source

  -- A row of the told run's source is a row of the source, mapped.
  down-j : ∀ {k e′} → Tl.σ k e′ → Σ (Ev (IE A)) λ e → σₑ k e × e′ ≡ mapEv just e
  down-j y = Mj.unmap y

  up-j : ∀ {k e} → σₑ k e → Tl.σ k (mapEv just e)
  up-j y = Mj.lift y

  out-j : ∀ {k b} → Tl.σ k (out (just b)) → σₑ k (out b)
  out-j y with down-j y
  ... | out _ , y′ , refl = y′
  ... | skip , _ , ()
  ... | end , _ , ()
  ... | pin _ , _ , ()

  end-j : ∀ {k} → Tl.σ k end → σₑ k end
  end-j y with down-j y
  ... | end , y′ , refl = y′
  ... | out _ , _ , ()
  ... | skip , _ , ()
  ... | pin _ , _ , ()

  listed-j : ∀ {l} → Listed σₑ l → Listed Tl.σ l
  listed-j (ks , cov , bk) = ks , (λ y lt → cov (proj₁ (proj₂ (down-j y))) lt) , λ m → proj₁ (bk m) , _ , up-j (proj₂ (proj₂ (bk m)))

  ------------------------------------------------------------------------
  -- A told row annotated

  -- A told value, every told row before it listed: its fold, the
  -- annotated row its step leaves.
  out-row : ∀ {m a} → Tl.τ m (out a) → Listed Tl.τ m → Σ (Routes × AIE A) λ c → σ′ m (out (proj₂ (annStep c a)))
  out-row {m} {a} t (ks , cov , bk) = c , subst (λ st → σ′ m (out (proj₂ st))) eq′ (Mr.lift (Sr.toSc (Scan.sval ac)))
    where
      fd = foldᵈ annStep z₀ Tl.τ (λ {y} {e} {e′} → τ-func {y} {e} {e′}) ks (λ mm → proj₂ (bk mm)) cov t
      ac = proj₂ fd
      av = Sr.accv ac
      c = proj₁ av
      eq′ : proj₁ fd ≡ annStep c a
      eq′ = subst (λ a′ → proj₁ fd ≡ annStep c a′) (lemma (τ-func (proj₁ (proj₂ (proj₂ av))) t)) (proj₂ (proj₂ (proj₂ av)))
        where
          lemma : ∀ {a′} → out a′ ≡ out a → a′ ≡ a
          lemma refl = refl

  -- A told row other than a value: annotated as it is.
  skip-row : ∀ {m} → Tl.τ m skip → σ′ m skip
  skip-row t = Mr.lift (Sr.toSc (Scan.sstep t))

  pin-row : ∀ {m r} → Tl.τ m (pin r) → σ′ m (pin r)
  pin-row t = Mr.lift (Sr.toSc (Scan.spin t))

  end-row : ∀ {m} → Tl.τ m end → σ′ m end
  end-row t = Mr.lift (Sr.toSc (Scan.send t))

  -- An annotated row: a told row, a value folded.
  data Up : Ev (Maybe (IE A)) → Ev (AIE A) → Set where
    up-out  : ∀ {a c} → Up (out a) (out (proj₂ (annStep c a)))
    up-skip : Up skip skip
    up-pin  : ∀ {r} → Up (pin r) (pin r)
    up-end  : Up end end

  told-of : ∀ {m e′} → σ′ m e′ → Σ (Ev (Maybe (IE A))) λ e → Tl.τ m e × Up e e′
  told-of x with Mr.unmap x
  ... | out _ , (Scan.sval ac , _) , refl with Sr.accv ac
  ...   | c , a , t , refl = out a , t , up-out
  told-of x | skip , (Scan.sstep t , _) , refl = skip , t , up-skip
  told-of x | pin _ , (Scan.spin t , _) , refl = pin _ , t , up-pin
  told-of x | end , (Scan.send t , _) , refl = end , t , up-end

  ------------------------------------------------------------------------
  -- Values and ends, both ways

  -- A shown annotated value: a value of the source, at its image.
  val← : ∀ {m b′} → σ′ m (out b′) → ¬ (annValues b′ ≡ []) → Σ Pos λ l → Σ (IE A) λ b → σₑ l (out b) × m ≡ l ⊕ [ sub w ] × annValues b′ ≡ valuesOf b
  val← x sh with told-of x
  ... | out nothing , _ , up-out = ⊥-elim (sh refl)
  ... | out (just b) , t , up-out with Tl.raw t
  ...   | Tl.r-shown {k} p _ = k , b , out-j (proj₁ p) , refl , refl

  -- An annotated end: the source's end, at its image.
  end← : ∀ {m} → σ′ m end → Σ Pos λ l → σₑ l end × m ≡ c₁ l
  end← x with told-of x
  ... | end , t , up-end with Tl.raw t
  ...   | Tl.r-end {k} y = k , end-j y , refl
  ...   | Tl.r-shown _ ()

  -- Before a told row, every told row listed: its value annotated,
  -- showing what the source's did.
  val→ : ∀ {l b} → σₑ l (out b) → Listed σₑ l → Σ (AIE A) λ b′ → σ′ (l ⊕ [ sub w ]) (out b′) × annValues b′ ≡ valuesOf b
  val→ {l} {b} y L = proj₂ (annStep c (just b)) , x , refl
    where
      yj = up-j y
      Lj = listed-j L
      tr = Tl.told-row yj (Tl.few-of Lj)
      t : Tl.τ (l ⊕ [ sub w ]) (out (just b))
      t with tr
      ... | _ , t′ , Tl.t-out = t′
      c = proj₁ (out-row t (Tl.told-listed yj Lj))
      x = proj₂ (out-row t (Tl.told-listed yj Lj))

  end→ : ∀ {l} → σₑ l end → Listed σₑ l → σ′ (c₁ l) end
  end→ {l} y L = end-row (Tl.τ-under yj (Tl.few-of (listed-j L)) (Tl.under-c₁ l) (Tl.j-end yj))
    where yj = up-j y

  ------------------------------------------------------------------------
  -- Where the annotated rows lie

  -- Every annotated row: in the subscribe instant, or at an image of a
  -- source row.
  owner : ∀ {m e′} → σ′ m e′ → m ∈ fixedL ⊎ Σ Pos λ l → Σ (Ev (IE A)) λ e → σₑ l e × m ∈ imgs l
  owner x with Tl.owner (Tl.raw (proj₁ (proj₂ (told-of x))))
  ... | Tl.o-fix f   = inj₁ f
  ... | Tl.o-row y i = inj₂ (_ , proj₁ (down-j y) , proj₁ (proj₂ (down-j y)) , i)

  ------------------------------------------------------------------------
  -- The annotated rows over a downward-closed set of source rows, listed

  -- Every source row leading `v` is in the set.
  module Over (P : Pos → Set) (P? : ∀ l → Dec (P l)) (down : ∀ {k k′} → k′ ≺ k → P k → P k′)
              (ks : List Pos) (cov : ∀ {l e} → σₑ l e → P l → l ∈ ks) (bk : ∀ {l} → l ∈ ks → P l × Σ (Ev (IE A)) (σₑ l)) where

    Led : Pos → Set
    Led v = ∀ {k e} → σₑ k e → k ⊑ v → P k

    private
      few : ∀ {l} → P l → Few Tl.σ l
      few pl = ks , λ y lt → cov (proj₁ (proj₂ (down-j y))) (down lt pl)

      es : List Tl.Entry
      es = Tl.ents ks (λ m → (_ , up-j (proj₂ (proj₂ (bk m)))) , few (proj₁ (bk m)))

      clo : ∀ {en} → en ∈ es → Tl.Image.Clo es (proj₁ en)
      clo m yc ck = Tl.ents-at (cov (end-j yc) (down ck (proj₁ (bk (Tl.ents-in m)))))

      module C = Tl.Image.Cover es clo

      led-at : ∀ {v} → Led v → ∀ {k e} → Tl.σ k e → k ⊑ v → Tl.At es k
      led-at ld y kv = Tl.ents-at (cov (proj₁ (proj₂ (down-j y))) (ld (proj₁ (proj₂ (down-j y))) kv))

      -- A told row's owner in the set.
      OwnO : ∀ {u} → Tl.Owner u → Set
      OwnO (Tl.o-fix _)       = ⊤
      OwnO (Tl.o-row {k} _ _) = P k

      own? : ∀ {u} (o : Tl.Owner u) → Dec (OwnO o)
      own? (Tl.o-fix _)       = yes tt
      own? (Tl.o-row {k} _ _) = P? k

      own-led : ∀ {u} (o : Tl.Owner u) → Led u → OwnO o
      own-led (Tl.o-fix _)        _  = tt
      own-led (Tl.o-row {k} y i)  ld = ld (proj₁ (proj₂ (down-j y))) (imgs-⊑ k i)

      -- Before a told row owned in the set, every row is led in it.
      led-before : ∀ {v} (o : Tl.Owner v) → OwnO o → ∀ {v′} → v′ ≺ v → Led v′
      led-before {v} (Tl.o-fix f) _ {v′} vv {k} y kv =
        ⊥-elim (⊑-≼ {k} {v′} kv (≺-trans {v′} {v} {k} vv (≺-trans {v} {Tl.r} {k} (fixed-≺ f) (Tl.r≺ (up-j y)))))
      led-before {v} (Tl.o-row {l} yl i) pl {v′} vv {k} y kv = at (≼-split {k} {l} (img-≼ (up-j y) yl kv (imgs-⊑ l i) vv))
        where
          at : k ≺ l ⊎ k ≡ l → P k
          at (inj₁ kl)   = down kl pl
          at (inj₂ refl) = pl

      Keep : Tl.Row → Set
      Keep (_ , _ , t) = OwnO (Tl.owner (Tl.raw t))

      keep? : ∀ rw → Dec (Keep rw)
      keep? (_ , _ , t) = own? (Tl.owner (Tl.raw t))


    -- The told rows before a told row owned in the set: listed.
    listedτ : ∀ {v e} (t : Tl.τ v e) → Keep (v , e , t) → Listed Tl.τ v
    listedτ {v} t o = filter (λ u → T? (u <ᵖ v)) (L.map proj₁ C.all) , cov′ , back′
      where
        cov′ : ∀ {u e′} → Tl.τ u e′ → u ≺ v → u ∈ filter (λ u → T? (u <ᵖ v)) (L.map proj₁ C.all)
        cov′ t′ uv = ∈-filter⁺ (λ u → T? (u <ᵖ v)) (AnyP.map⁺ (C.cover t′ (led-at (led-before (Tl.owner (Tl.raw t)) o uv)))) uv

        back′ : ∀ {u} → u ∈ filter (λ u → T? (u <ᵖ v)) (L.map proj₁ C.all) → u ≺ v × Σ _ (Tl.τ u)
        back′ m = proj₂ (∈-filter⁻ (λ u → T? (u <ᵖ v)) {xs = L.map proj₁ C.all} m) , C.back (proj₁ (∈-filter⁻ (λ u → T? (u <ᵖ v)) {xs = L.map proj₁ C.all} m))

    -- A told row owned in the set, annotated.
    ann-row : ∀ {v e} (t : Tl.τ v e) → Keep (v , e , t) → Σ (Ev (AIE A)) (σ′ v)
    ann-row {e = out a}  t o = _ , proj₂ (out-row t (listedτ t o))
    ann-row {e = skip}   t _ = skip , skip-row t
    ann-row {e = pin r}  t _ = pin r , pin-row t
    ann-row {e = end}    t _ = end , end-row t

    -- A told row owned in the set, with its annotation.
    private
      KRow : Set
      KRow = Σ Tl.Row Keep

      keptK : List Tl.Row → List KRow
      keptK []         = []
      keptK (rw ∷ rs) with keep? rw
      ... | yes k = (rw , k) ∷ keptK rs
      ... | no _  = keptK rs

      ∈-keptK : ∀ {rw rs} → rw ∈ rs → Keep rw → Σ (Keep rw) λ k → (rw , k) ∈ keptK rs
      ∈-keptK {rw} {rw′ ∷ rs} (here refl) k with keep? rw′
      ... | yes k′ = k′ , here refl
      ... | no nk  = ⊥-elim (nk k)
      ∈-keptK {rw} {rw′ ∷ rs} (there m) k with keep? rw′
      ... | yes _ = proj₁ (∈-keptK m k) , there (proj₂ (∈-keptK m k))
      ... | no _  = ∈-keptK m k

      pos : KRow → Pos
      pos r = proj₁ (proj₁ r)

      annOf : (r : KRow) → Σ (Ev (AIE A)) (σ′ (pos r))
      annOf ((_ , _ , t) , k) = ann-row t k

      isEnd? : (e : Ev (AIE A)) → Dec (e ≡ end)
      isEnd? end     = yes refl
      isEnd? (out _) = no λ ()
      isEnd? skip    = no λ ()
      isEnd? (pin _) = no λ ()

      endK? : ∀ r → Dec (proj₁ (annOf r) ≡ end)
      endK? r = isEnd? (proj₁ (annOf r))

      ks₀ : List KRow
      ks₀ = keptK C.all

      endsP : List Pos
      endsP = L.map pos (filter endK? ks₀)

      Before : Pos → Set
      Before m = All (λ c → ¬ (c ≺ m)) endsP

      before? : ∀ r → Dec (Before (pos r))
      before? r = all? (λ c → ¬? (T? (c <ᵖ pos r))) endsP

      fin : List KRow
      fin = filter before? ks₀

      keep-led : ∀ rw → Led (proj₁ rw) → Keep rw
      keep-led (_ , _ , t) ld = own-led (Tl.owner (Tl.raw t)) ld

      has→ : ∀ {rs v} → Tl.Has rs v → Σ Tl.Row λ rw → rw ∈ rs × v ≡ proj₁ rw
      has→ (here p)  = _ , here refl , p
      has→ (there h) = let (rw , m , p) = has→ h in rw , there m , p

      -- An annotated row led in the set: a kept row.
      led-kept : ∀ {m e′} → σ′ m e′ → Led m → Σ KRow λ r → r ∈ ks₀ × m ≡ pos r
      led-kept x ld with has→ (C.cover (proj₁ (proj₂ (told-of x))) (led-at ld))
      ... | rw , mi , refl = (rw , proj₁ (∈-keptK mi (keep-led rw ld))) , proj₂ (∈-keptK mi (keep-led rw ld)) , refl

      -- Before a kept row, led in the set.
      led-past : ∀ (r : KRow) {c} → c ≺ pos r → Led c
      led-past ((_ , _ , t) , k) = led-before (Tl.owner (Tl.raw t)) k

      end-in : ∀ {c} → σ′ c end → Led c → c ∈ endsP
      end-in x ld with led-kept x ld
      ... | r , mi , refl = ∈-map⁺ pos (∈-filter⁺ endK? mi (InvAt.func Iσ′ (proj₂ (annOf r)) x))

      ends-end : ∀ {c} → c ∈ endsP → σ′ c end
      ends-end ci with ∈-map⁻ pos ci
      ... | r , ri , refl = subst (σ′ (pos r)) (proj₂ (∈-filter⁻ endK? {xs = ks₀} ri)) (proj₂ (annOf r))

    -- EVERY PROPER ANNOTATED ROW LED IN THE SET, LISTED: the kept rows
    -- past no kept end.  An end before a kept row is led, so kept.
    listing : Σ (List Pos) λ ls → (∀ {m e′} → Proper σ′ m e′ → Led m → m ∈ ls) × (∀ {m} → m ∈ ls → Σ (Ev (AIE A)) (Proper σ′ m))
    listing = L.map pos fin , cov′ , back′
      where
        cov′ : ∀ {m e′} → Proper σ′ m e′ → Led m → m ∈ L.map pos fin
        cov′ (x , pr) ld with led-kept x ld
        ... | r , mi , refl = ∈-map⁺ pos (∈-filter⁺ before? mi (tabulate λ ci → pr (ends-end ci)))

        back′ : ∀ {m} → m ∈ L.map pos fin → Σ (Ev (AIE A)) (Proper σ′ m)
        back′ mi with ∈-map⁻ pos mi
        ... | r , ri , refl = proj₁ (annOf r) , proj₂ (annOf r)
                            , λ x cm → lookup (proj₂ (∈-filter⁻ before? {xs = ks₀} ri)) (end-in x (led-past r cm)) cm
