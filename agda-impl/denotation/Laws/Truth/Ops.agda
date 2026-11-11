{-# OPTIONS --guardedness #-}

-- EACH UNARY OPERATOR KEEPS THE TRUTH: over a child read against its
-- next, `map`, `defer`, `scan` and `takeWhile` are read against theirs.
module denotation.Laws.Truth.Ops where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (suc; z≤n; s≤s)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import Data.Bool using (Bool; true; false; not) renaming (T to Tr)
open import Tree using (map; scan; takeWhile; defer)
open import denotation.Position using (Pos; ix; last; inside; _⊕_)
open import denotation.Events using (ix-<; <ᵖ-part)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; Few; Dep; Reach; Truncate; Silent; hush; held;
  spin; DeferT; guard; body; MapT; map-out; map-skip; map-pin; map-end; module Scan;
  module TakeWhile; PDep; _≺_; _≼_; enter; module Op)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺→≼; ≼-refl; ≼-trans; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≼-split; ≺-irrefl; ≺-trans;
  reach-via; entered-reach; entered-few; few-ind; ≺-ext)
open import denotation.Laws.Count using (Cov; cov-down; cov-stable; em)
open import denotation.Laws.Worlds using (ok-step; InvD; _⊑_; ⊑-refl; ⊑-≼; ⊕-assoc; ⊕-identityʳ; inside-⊑; ⊑-trans; ⊑-cmp; ⊑-snoc;
  ⊑-snoc⁺; conv; InvAt)
open import denotation.Laws using (from; scan-ag)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Truth using (Before; Clean; Lie; Rel; Spun; Truth; before-down; before-of; clean-down; clean-of; guarded; lie-up; pull; where?)

------------------------------------------------------------------------
-- Operators that relabel rows where they lie

private
  -- The same kind of row, values aside.
  data Lbl {A B : Set} : Ev A → Ev B → Set where
    l-out  : ∀ {a b} → Lbl (out a) (out b)
    l-skip : Lbl skip skip
    l-pin  : ∀ {r} → Lbl (pin r) (pin r)
    l-end  : Lbl end end

  lbl-sym : ∀ {A B} {e₀ : Ev A} {e : Ev B} → Lbl e₀ e → Lbl e e₀
  lbl-sym l-out  = l-out
  lbl-sym l-skip = l-skip
  lbl-sym l-pin  = l-pin
  lbl-sym l-end  = l-end

  -- What a row waits on is read off the kinds alone.
  dep-lbl : ∀ {A B q k} {e₀ e₀′ : Ev A} {e e′ : Ev B} → Lbl e₀ e → Lbl e₀′ e′ → Dep q e₀ k e₀′ → Dep q e k e′
  dep-lbl l-out  _ _ = tt
  dep-lbl l-skip _ _ = tt
  dep-lbl l-end  _ _ = tt
  dep-lbl l-pin l-out d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ ()
  dep-lbl l-pin l-skip d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ ()
  dep-lbl l-pin l-end d i with d i
  ... | inj₁ kr = inj₁ kr
  ... | inj₂ ()
  dep-lbl l-pin l-pin d i with d i
  ... | inj₁ kr   = inj₁ kr
  ... | inj₂ refl = inj₂ refl

  lbl-silent : ∀ {A B} {e₀ : Ev A} {e : Ev B} → Lbl e₀ e → Silent e₀ → Silent e
  lbl-silent l-skip hush = hush
  lbl-silent l-pin  held = held

  -- Rows each on a reached row of the same kind are reached.
  lifted : ∀ {A B} {u : EmissionSet A} {v : EmissionSet B}
         → (src : ∀ {q e} → v q e → Ev A) → (∀ {q e} (x : v q e) → u q (src x)) → (∀ {q e} (x : v q e) → Lbl (src x) e)
         → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : v q e) → Reach v q e
  lifted src row lbl re x = reach-via (λ y _ d → src y , row y , dep-lbl (lbl-sym (lbl x)) (lbl-sym (lbl y)) d) (re (row x))

  -- A map's row, the row it lies on, and that row's image.
  module Mapped {A B : Set} (f : A → B) where
    src : ∀ {u : EmissionSet A} {q e} → MapT f u q e → Ev A
    src (map-out {a = a} _) = out a
    src (map-skip _)        = skip
    src (map-pin {r = r} _) = pin r
    src (map-end _)         = end

    row : ∀ {u : EmissionSet A} {q e} (x : MapT f u q e) → u q (src x)
    row (map-out x)  = x
    row (map-skip x) = x
    row (map-pin x)  = x
    row (map-end x)  = x

    lbl : ∀ {u : EmissionSet A} {q e} (x : MapT f u q e) → Lbl (src x) e
    lbl (map-out _)  = l-out
    lbl (map-skip _) = l-skip
    lbl (map-pin _)  = l-pin
    lbl (map-end _)  = l-end

    via : ∀ {u u′ : EmissionSet A} {q e} (x : MapT f u q e) → (u q (src x) → u′ q (src x)) → MapT f u′ q e
    via (map-out x)  h = map-out (h x)
    via (map-skip x) h = map-skip (h x)
    via (map-pin x)  h = map-pin (h x)
    via (map-end x)  h = map-end (h x)

    up : ∀ {u : EmissionSet A} {q e₀} → u q e₀ → Σ (Ev B) λ e → MapT f u q e × Lbl e₀ e
    up {e₀ = out _} x = _ , map-out x , l-out
    up {e₀ = skip}  x = _ , map-skip x , l-skip
    up {e₀ = pin _} x = _ , map-pin x , l-pin
    up {e₀ = end}   x = _ , map-end x , l-end

    lift : ∀ {u : EmissionSet A} → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : MapT f u q e) → Reach (MapT f u) q e
    lift {u} = lifted (λ {q} {e} → src {u} {q} {e}) (λ {q} {e} → row {u} {q} {e}) (λ {q} {e} → lbl {u} {q} {e})

  -- A scan's row, the row it lies on, a value on the one it folds in.
  module Scanned {A B : Set} (f : B → A → B) (z : B) where
    final : ∀ {u : EmissionSet A} {q b} → Scan.Acc f z u q b → Σ A λ a → u q (out a)
    final (Scan.acc₀ x _)    = _ , x
    final (Scan.acc _ x _ _) = _ , x

    src : ∀ {u : EmissionSet A} {q e} → Scan.ScanT f z u q e → Ev A
    src (Scan.sval ac)         = out (proj₁ (final ac))
    src (Scan.sstep _)         = skip
    src (Scan.spin {r = r} _)  = pin r
    src (Scan.send _)          = end

    row : ∀ {u : EmissionSet A} {q e} (x : Scan.ScanT f z u q e) → u q (src x)
    row (Scan.sval ac) = proj₂ (final ac)
    row (Scan.sstep x) = x
    row (Scan.spin x)  = x
    row (Scan.send x)  = x

    lbl : ∀ {u : EmissionSet A} {q e} (x : Scan.ScanT f z u q e) → Lbl (src x) e
    lbl (Scan.sval _)  = l-out
    lbl (Scan.sstep _) = l-skip
    lbl (Scan.spin _)  = l-pin
    lbl (Scan.send _)  = l-end

    lift : ∀ {u : EmissionSet A} → (∀ {k e₀} → u k e₀ → Reach u k e₀) → ∀ {q e} (x : Scan.ScanT f z u q e) → Reach (Scan.ScanT f z u) q e
    lift {u} = lifted (λ {q} {e} → src {u} {q} {e}) (λ {q} {e} → row {u} {q} {e}) (λ {q} {e} → lbl {u} {q} {e})

  -- A takeWhile's row, the row it lies on, and the point before which
  -- no value failed.
  module Taken {A : Set} (incl : Bool) (keep : A → Bool) where
    open TakeWhile incl keep using (TakeT; Failed; pass; fail; stop; step; tend; left)

    spos : ∀ {u q e} → TakeT u q e → Pos
    spos (pass {q} _ _ _)   = q
    spos (fail {q} _ _ _ _) = q
    spos (stop {q} _ _ _)   = q
    spos (step {q} _ _)     = q
    spos (tend {q} _ _)     = q
    spos (left {q} _ _ _)   = q

    sev : ∀ {u q e} → TakeT u q e → Ev A
    sev (pass {a = a} _ _ _)   = out a
    sev (fail {a = a} _ _ _ _) = out a
    sev (stop {a = a} _ _ _)   = out a
    sev (step _ _)             = skip
    sev (tend _ _)             = end
    sev (left {r = r} _ _ _)   = pin r

    srow : ∀ {u q e} (x : TakeT u q e) → u (spos x) (sev x)
    srow (pass y _ _)   = y
    srow (fail y _ _ _) = y
    srow (stop y _ _)   = y
    srow (step y _)     = y
    srow (tend y _)     = y
    srow (left y _ _)   = y

    bound : ∀ {u q e} → TakeT u q e → Pos
    bound (pass {q} _ _ _)   = q
    bound (fail {q} _ _ _ _) = q
    bound (stop {q} _ _ _)   = q
    bound (step {q} _ _)     = q
    bound (tend {q} _ _)     = q
    bound (left {r = r} _ _ _) = r

    unf : ∀ {u q e} (x : TakeT u q e) → ¬ Failed u (bound x)
    unf (pass _ _ nf)   = nf
    unf (fail _ _ nf _) = nf
    unf (stop _ _ nf)   = nf
    unf (step _ nf)     = nf
    unf (tend _ nf)     = nf
    unf (left _ nf _)   = nf

    -- The same row over another source.
    move : ∀ {u u′ q e} (x : TakeT u q e) → u′ (spos x) (sev x) → ¬ Failed u′ (bound x) → TakeT u′ q e
    move (pass _ k _)   y nf = pass y k nf
    move (fail _ k _ i) y nf = fail y k nf i
    move (stop _ k _)   y nf = stop y k nf
    move (step _ _)     y nf = step y nf
    move (tend _ _)     y nf = tend y nf
    move (left _ _ i)   y nf = left y nf i

    under : ∀ {u q e} (x : TakeT u q e) → spos x ⊑ q
    under (pass _ _ _)       = ⊑-refl _
    under (fail {q} _ _ _ _) = ⊑-snoc⁺ q
    under (stop {q} _ _ _)   = ⊑-snoc⁺ q
    under (step _ _)         = ⊑-refl _
    under (tend _ _)         = ⊑-refl _
    under (left _ _ _)       = ⊑-refl _

    -- What lies before the bound, the source waits on.
    bounded : ∀ {u q e g e″} (x : TakeT u q e) → g ≺ bound x → g ≺ spos x × Dep (spos x) (sev x) g e″
    bounded (pass _ _ _)   gb = gb , tt
    bounded (fail _ _ _ _) gb = gb , tt
    bounded (stop _ _ _)   gb = gb , tt
    bounded (step _ _)     gb = gb , tt
    bounded (tend _ _)     gb = gb , tt
    bounded {g = g} (left {q} {r} _ _ i) gb = ≺-≼-≺ {g} {r} {q} gb (⊑-≼ (inside-⊑ r q i)) , λ _ → inj₁ gb

    -- ... and so does the row.
    bound-dep : ∀ {u q e} (x : TakeT u q e) → ∀ {k e₀} → k ≺ bound x → Dep q e k e₀
    bound-dep (pass _ _ _)   _  = tt
    bound-dep (fail _ _ _ _) _  = tt
    bound-dep (stop _ _ _)   _  = tt
    bound-dep (step _ _)     _  = tt
    bound-dep (tend _ _)     _  = tt
    bound-dep (left _ _ _)   kr = λ _ → inj₁ kr

    bound-≼ : ∀ {u q e} (x : TakeT u q e) → bound x ≼ q
    bound-≼ (pass {q} _ _ _)       = ≼-refl {q}
    bound-≼ (fail {q} _ _ _ _)     = ⊑-≼ (⊑-snoc⁺ q)
    bound-≼ (stop {q} _ _ _)       = ⊑-≼ (⊑-snoc⁺ q)
    bound-≼ (step {q} _ _)         = ≼-refl {q}
    bound-≼ (tend {q} _ _)         = ≼-refl {q}
    bound-≼ (left {q} {r} _ _ i)   = ⊑-≼ (inside-⊑ r q i)

    ext : List Pos → List Pos
    ext []       = []
    ext (k ∷ ks) = k ∷ (k ⊕ [ ix 0 ]) ∷ (k ⊕ [ last ]) ∷ ext ks

    ext-∈ : ∀ {u q e ks} (x : TakeT u q e) → spos x ∈ ks → q ∈ ext ks
    ext-∈ (pass _ _ _)   (here refl) = here refl
    ext-∈ (fail _ _ _ _) (here refl) = there (here refl)
    ext-∈ (stop _ _ _)   (here refl) = there (there (here refl))
    ext-∈ (step _ _)     (here refl) = here refl
    ext-∈ (tend _ _)     (here refl) = here refl
    ext-∈ (left _ _ _)   (here refl) = here refl
    ext-∈ x (there m) = there (there (there (ext-∈ x m)))

    -- With no source row under another, a row before another lies on a
    -- source at or before the other's.
    order : ∀ {u q e k e′} → (∀ {y e l ys e′} → u y e → u (y ⊕ (l ∷ ys)) e′ → ⊥)
          → (x : TakeT u q e) (y : TakeT u k e′) → k ≺ q → spos y ≺ spos x ⊎ spos y ≡ spos x
    order {u} {q} {k = k} fl x y kq with ≼-or-≻ (spos x) (spos y)
    ... | inj₂ lt = inj₁ lt
    ... | inj₁ xy with ≼-split {spos x} {spos y} xy
    ...   | inj₂ eq = inj₂ (sym eq)
    ...   | inj₁ lt with conv (⊑-refl (spos x)) xy (≼-≺-≺ {spos y} {k} {q} (⊑-≼ (under y)) kq) (under x)
    ...     | [] , eq = ⊥-elim (≺-irrefl {spos x} (subst (spos x ≺_) (trans eq (⊕-identityʳ (spos x))) lt))
    ...     | l ∷ ys , eq = ⊥-elim (fl (srow x) (subst (λ v → u v (sev y)) eq (srow y)))

    pin-dep : ∀ {u k r} (y : TakeT u k (pin r)) → PDep r (spos y) (sev y)
    pin-dep (left _ _ _) = inj₂ refl

    dep-src : ∀ {u q e k e′} (x : TakeT u q e) (y : TakeT u k e′) → Dep q e k e′ → Dep (spos x) (sev x) (spos y) (sev y)
    dep-src (pass _ _ _)   _ _ = tt
    dep-src (fail _ _ _ _) _ _ = tt
    dep-src (stop _ _ _)   _ _ = tt
    dep-src (step _ _)     _ _ = tt
    dep-src (tend _ _)     _ _ = tt
    dep-src {k = k} (left {r = r} _ _ _) y d ins with d ins
    ... | inj₁ kr   = inj₁ (≼-≺-≺ {spos y} {k} {r} (⊑-≼ (under y)) kr)
    ... | inj₂ refl = pin-dep y

    -- With no source row under another, over reached rows, every row is reached.
    lift : ∀ {u} → (∀ {y e l ys e′} → u y e → u (y ⊕ (l ∷ ys)) e′ → ⊥) → (∀ {k e₀} → u k e₀ → Reach u k e₀)
         → ∀ {q e} (x : TakeT u q e) → Reach (TakeT u) q e
    lift {u} fl re {q} {e} x with re (srow x)
    ... | ks , h = ext (spos x ∷ ks) , λ y kq d → ext-∈ y (src y kq d)
      where
        src : ∀ {k e′} (y : TakeT u k e′) → k ≺ q → Dep q e k e′ → spos y ∈ (spos x ∷ ks)
        src y kq d with order fl x y kq
        ... | inj₂ eq = here eq
        ... | inj₁ lt = there (h (srow y) lt (dep-src x y d))

-- A MAP KEEPS THE TRUTH: each row lies on its input's, and is reached
-- once that one is, so a clean row lies on a clean one.
map-truth : ∀ {A B H} (f : A → B) {s s′ : Den A} → Rel H s s′ → Rel H (Op.map f s) (Op.map f s′)
map-truth {A} {B} f {s} {s′} R p ok = record
  { Cut     = Cut
  ; silent  = λ c sp x → lbl-silent (lbl (proj₁ x)) (silent c sp (row (proj₁ x)))
  ; shows   = λ c i → shown (shows c i)
  ; again   = λ { c (map-pin y , _) l rs i → shade (again c y l rs i) }
  ; shadow  = λ { c (map-pin y , _) l rs bf → shade (shadow c y l rs (before bf)) }
  ; agree   = λ q e cl → (λ { (x , _) → let v = via x (proj₁ (agree q (src x) (clean cl (lbl x)))) in v , lift re′ v })
                       , (λ { (x , _) → let v = via x (proj₂ (agree q (src x) (clean cl (lbl x)))) in v , lift re v })
  }
  where
    open Truth (R p ok)
    open Mapped f

    t t′ : EmissionSet A
    t  = enter s p
    t′ = enter s′ p

    re : ∀ {k e} → t k e → Reach t k e
    re = entered-reach s p

    re′ : ∀ {k e} → t′ k e → Reach t′ k e
    re′ = entered-reach s′ p

    image : ∀ {k e₀} → t k e₀ → Σ (Ev B) λ e → Truncate (MapT f t) k e × Lbl e₀ e
    image y with up y
    ... | e , m , l = e , (m , lift re m) , l

    shown : ∀ {c i} → (Σ Pos λ z → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × t z e₀)
          → Σ Pos λ z → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ z × Truncate (MapT f t) z e
    shown (z , _ , z0 , tz) with image tz
    ... | e , m , _ = z , e , z0 , m

    shade : ∀ {c i r} → (Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × t z (pin r)) → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Truncate (MapT f t) z (pin r)
    shade (z , z1 , tz) = z , z1 , map-pin tz , lift re (map-pin tz)

    before : ∀ {r} → Before Cut (Truncate (MapT f t)) r → Before Cut t r
    before (ks , h) = ks , λ y kr → h (proj₁ (proj₂ (image y))) kr

    clean : ∀ {q e e₀} → Clean Cut (Truncate (MapT f t)) q e → Lbl e₀ e → Clean Cut t q e₀
    clean (nl , ks , h) l = nl , ks , λ y kq d → h (proj₁ (proj₂ (image y))) kq (dep-lbl l (proj₂ (proj₂ (image y))) d)

-- A DEFER KEEPS THE TRUTH: its body's cuts are its own, and its guard
-- is the same row either way.
defer-truth : ∀ {A H} {d d′ : Den A} → InvD H d → InvD H d′ → Rel H d d′ → Rel H (Op.defer d) (Op.defer d′)
defer-truth {A} {H} {d} {d′} inv inv′ R p ok = record
  { Cut     = Cut
  ; silent  = λ { _ _ (guard , _) → hush ; c sp (body x , _) → silent c sp x }
  ; shows   = λ c i → shown (shows c i)
  ; again   = λ { c (body y , _) l rs i → shade (again c y l rs i) }
  ; shadow  = λ { c (body y , _) l rs bf → shade (shadow c y l rs (before bf)) }
  ; agree   = λ q e cl → fwd cl , bwd cl
  }
  where
    open Truth (R (p ⊕ [ ix 1 ]) (ok-step p ok))

    -- A body row waits on the guard and on body rows.
    in-body : ∀ (e : Den A) {k e₀} → enter e (p ⊕ [ ix 1 ]) k e₀ → Reach (DeferT e p) k e₀
    in-body e x with entered-reach e (p ⊕ [ ix 1 ]) x
    ... | ks , h = (p ⊕ [ ix 0 ]) ∷ ks , λ { guard _ _ → here refl ; (body y) kq dd → there (h y kq dd) }

    shown : ∀ {c i} → (Σ Pos λ z → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × enter d (p ⊕ [ ix 1 ]) z e₀)
          → Σ Pos λ z → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ z × Truncate (DeferT d p) z e₀
    shown (z , e₀ , z0 , tz) = z , e₀ , z0 , body tz , in-body d tz

    shade : ∀ {c i r} → (Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × enter d (p ⊕ [ ix 1 ]) z (pin r)) → Σ Pos λ z → (c ⊕ [ ix i ]) ⊑ z × Truncate (DeferT d p) z (pin r)
    shade (z , z1 , tz) = z , z1 , body tz , in-body d tz

    before : ∀ {r} → Before Cut (Truncate (DeferT d p)) r → Before Cut (enter d (p ⊕ [ ix 1 ])) r
    before (ks , h) = ks , λ y kr → h (body y , in-body d y) kr

    clean : ∀ {q e} → Clean Cut (Truncate (DeferT d p)) q e → Clean Cut (enter d (p ⊕ [ ix 1 ])) q e
    clean (nl , ks , h) = nl , ks , λ y kq dd → h (body y , in-body d y) kq dd

    fwd : ∀ {q e} → Clean Cut (Truncate (DeferT d p)) q e → Truncate (DeferT d p) q e → Truncate (DeferT d′ p) q e
    fwd _  (guard , _)  = guard , guarded d′ inv′ p ok
    fwd {q} {e} cl (body x , _) = body y , in-body d′ y
      where y = proj₁ (agree q e (clean cl)) x

    bwd : ∀ {q e} → Clean Cut (Truncate (DeferT d p)) q e → Truncate (DeferT d′ p) q e → Truncate (DeferT d p) q e
    bwd _  (guard , _)  = guard , guarded d inv p ok
    bwd {q} {e} cl (body x , _) = body y , in-body d y
      where y = proj₂ (agree q e (clean cl)) x

-- A SCAN KEEPS THE TRUTH: each row lies on its input's, a value on the
-- one it folds in.  A value reads every value before it, so the input
-- agrees up to a clean value, whose past is all clean.  A value's fold is
-- classical, but what it is needed for is decidable or a negation.
scan-truth : ∀ {A B H} (f : B → A → B) z {s s′ : Den A} → Rel H s s′ → Rel H (Op.scan f z s) (Op.scan f z s′)
scan-truth {A} {B} f z {s} {s′} R p ok = record
  { Cut     = Cut
  ; silent  = λ c sp x → lbl-silent (lbl (proj₁ x)) (silent c sp (row (proj₁ x)))
  ; shows   = λ c i → shown c (shows c i)
  ; again   = λ { c (Scan.spin y , _) l rs i → shade (again c y l rs i) }
  ; shadow  = λ { c (Scan.spin y , _) l rs bf → shade (shadow c y l rs (before bf)) }
  ; agree   = λ q e cl → fwd cl , bwd cl
  }
  where
    tr = R p ok
    open Truth tr
    open Scanned f z

    t t′ : EmissionSet A
    t  = enter s p
    t′ = enter s′ p

    S S′ : EmissionSet B
    S  = Scan.ScanT f z t
    S′ = Scan.ScanT f z t′

    re : ∀ {k e} → t k e → Reach t k e
    re = entered-reach s p

    re′ : ∀ {k e} → t′ k e → Reach t′ k e
    re′ = entered-reach s′ p

    -- Each input row shows, a value classically.
    image : ∀ {k e₀} → t k e₀ → ¬ ¬ (Σ (Ev B) λ e → Truncate S k e × Lbl e₀ e)
    image {e₀ = out a} y n = fold f z t (entered-few s p tt y) y λ { (b , ac) → n (out b , (Scan.sval ac , lift re (Scan.sval ac)) , l-out) }
    image {e₀ = skip}  y n = n (skip , (Scan.sstep y , lift re (Scan.sstep y)) , l-skip)
    image {e₀ = pin r} y n = n (pin r , (Scan.spin y , lift re (Scan.spin y)) , l-pin)
    image {e₀ = end}   y n = n (end , (Scan.send y , lift re (Scan.send y)) , l-end)

    quiet : ∀ {k e₀} → t k e₀ → Silent e₀ → Σ (Ev B) λ e → Truncate S k e
    quiet y hush = skip , Scan.sstep y , lift re (Scan.sstep y)
    quiet y held = _ , Scan.spin y , lift re (Scan.spin y)

    shown : ∀ {c i} → Cut c → (Σ Pos λ w → Σ (Ev A) λ e₀ → (c ⊕ [ ix i ]) ⊑ w × t w e₀)
          → Σ Pos λ w → Σ (Ev B) λ e → (c ⊕ [ ix i ]) ⊑ w × Truncate S w e
    shown {i = i} c (w , _ , w0 , tw) with quiet tw (silent c (i , w0) tw)
    ... | e , m = w , e , w0 , m

    shade : ∀ {c i r} → (Σ Pos λ w → (c ⊕ [ ix i ]) ⊑ w × t w (pin r)) → Σ Pos λ w → (c ⊕ [ ix i ]) ⊑ w × Truncate S w (pin r)
    shade (w , w1 , tw) = w , w1 , Scan.spin tw , lift re (Scan.spin tw)

    firm : ∀ {q ks k} → ¬ ¬ (Cov q ks k × ¬ Lie Cut k) → Cov q ks k × ¬ Lie Cut k
    firm nn = cov-stable (λ n → nn λ c → n (proj₁ c)) , λ l → nn λ c → proj₂ c l

    before : ∀ {r} → Before Cut (Truncate S) r → Before Cut t r
    before (ks , h) = ks , λ y kr → firm λ n → image y λ { (_ , m , _) → n (h m kr) }

    clean : ∀ {q e e₀} → Clean Cut (Truncate S) q e → Lbl e₀ e → Clean Cut t q e₀
    clean (nl , ks , h) l = nl , ks , λ y kq d → firm λ n → image y λ { (_ , m , l′) → n (h m kq (dep-lbl l l′ d)) }

    -- Up to a clean value, the input agrees.
    upto-clean : ∀ {q a} → Clean Cut t q (out a) → AgreeTo q t t′
    upto-clean {q} {a} cl@(nl , ks , h) = ⟨ (λ {y} {e₀} yq → at (≼-split {y} {q} yq)) ⟩
      where
        at : ∀ {y e₀} → y ≺ q ⊎ y ≡ q → (t y e₀ → t′ y e₀) × (t′ y e₀ → t y e₀)
        at {y} {e₀} (inj₁ yq) = (λ x → proj₁ (agree y e₀ (clean-down tr {q} {out a} {y} {e₀} cl yq tt (proj₂ (h x yq tt)))) x) , (λ x → pull tr {q} {out a} {y} {e₀} cl x yq tt)
        at {e₀ = e₀} (inj₂ refl) = agree q e₀ (nl , ks , λ x kq _ → h x kq tt)

    fwd : ∀ {q e} → Clean Cut (Truncate S) q e → Truncate S q e → Truncate S′ q e
    fwd {q} cl (Scan.sval {b = b} ac , _) =
      let v = proj₁ (upto (scan-ag f z (upto-clean {a = proj₁ (final ac)} (clean {e = out b} {e₀ = out (proj₁ (final ac))} cl l-out))) {q} (≼-refl {q})) (Scan.sval ac) in v , lift re′ v
    fwd {q} cl (Scan.sstep x , _) = let v = Scan.sstep (proj₁ (agree q skip (clean cl l-skip)) x) in v , lift re′ v
    fwd {q} cl (Scan.spin {r = r} x , _) = let v = Scan.spin (proj₁ (agree q (pin r) (clean cl l-pin)) x) in v , lift re′ v
    fwd {q} cl (Scan.send x , _) = let v = Scan.send (proj₁ (agree q end (clean cl l-end)) x) in v , lift re′ v

    bwd : ∀ {q e} → Clean Cut (Truncate S) q e → Truncate S′ q e → Truncate S q e
    bwd {q} cl (Scan.sval {b = b} ac , _) =
      let v = proj₂ (upto (scan-ag f z (upto-clean {a = proj₁ (final ac)} (clean {e = out b} {e₀ = out (proj₁ (final ac))} cl l-out))) {q} (≼-refl {q})) (Scan.sval ac) in v , lift re v
    bwd {q} cl (Scan.sstep x , _) = let v = Scan.sstep (proj₂ (agree q skip (clean cl l-skip)) x) in v , lift re v
    bwd {q} cl (Scan.spin {r = r} x , _) = let v = Scan.spin (proj₂ (agree q (pin r) (clean cl l-pin)) x) in v , lift re v
    bwd {q} cl (Scan.send x , _) = let v = Scan.send (proj₂ (agree q end (clean cl l-end)) x) in v , lift re v

-- A TAKEWHILE KEEPS THE TRUTH: each row lies on its source's, unfailed
-- before it.  A cut stays a cut while unfailed before its spin, or while
-- it keeps the pins of a connect leading it; a cut it hides holds no row
-- of either side where a row is clean.  Which failure is the earliest is
-- not decidable, but what it is needed for is a negation.
take-truth : ∀ {A H} (i : Bool) (keep : A → Bool) {s s′ : Den A} → InvD H s → InvD H s′
           → Rel H s s′ → Rel H (Op.takeWhile i keep s) (Op.takeWhile i keep s′)
take-truth {A} {H} i keep {s} {s′} Is Is′ R p ok = record
  { Cut     = Cut′
  ; silent  = λ c sp x → quiet (proj₁ c) sp (proj₁ x)
  ; shows   = shown
  ; again   = λ { c (left x nf _ , _) l rc j → kept-at nf (again (proj₁ c) x l rc j) }
  ; shadow  = λ { c (left x′ nf′ _ , _) l rc bf → kept-at (unfailed bf nf′) (shadow (proj₁ c) x′ l rc (before-in bf (unfailed bf nf′))) }
  ; agree   = λ q e cl → fwd cl , bwd cl
  }
  where
    tr = R p ok
    open Truth tr
    open Taken i keep
    open TakeWhile i keep using (TakeT; Failed; pass; fail; stop; step; tend; left)

    t t′ : EmissionSet A
    t  = enter s p
    t′ = enter s′ p

    O : EmissionSet A
    O = Truncate (TakeT t)

    I  = Is p ok
    I′ = Is′ p ok

    rows : ∀ {q e} → TakeT t q e → O q e
    rows x = x , lift (InvAt.flat I) (entered-reach s p) x

    rows′ : ∀ {q e} → TakeT t′ q e → Truncate (TakeT t′) q e
    rows′ x = x , lift (InvAt.flat I′) (entered-reach s′ p) x

    pinned-in : ∀ {z r} → t z (pin r) → Tr (inside r z)
    pinned-in x = proj₂ (InvAt.pinned I x)

    -- The pins of a connect leading the cut, kept.
    Kept : Pos → Set
    Kept c = Σ Pos λ r → r ⊑ c × ¬ Failed t r × Σ Pos λ z → (c ⊕ [ ix 1 ]) ⊑ z × t z (pin r)

    Cut′ : Pos → Set
    Cut′ c = Cut c × (¬ Failed t (c ⊕ [ ix 0 ]) ⊎ Kept c)

    fd-up : ∀ {w z} → Failed t w → w ≼ z → Failed t z
    fd-up {w} {z} (g , a , x , nk , gw) wz = g , a , x , nk , ≺-≼-≺ {g} {w} {z} gw wz

    past-first : ∀ c j {y} → (c ⊕ [ ix (suc j) ]) ⊑ y → Failed t (c ⊕ [ ix 0 ]) → Failed t y
    past-first c j {y} l f = fd-up {c ⊕ [ ix 0 ]} {y} f (≺→≼ {c ⊕ [ ix 0 ]} {y}
      (≺-≼-≺ {c ⊕ [ ix 0 ]} {c ⊕ [ ix (suc j) ]} {y} (Equivalence.from T-≡ (<ᵖ-part c [] [] (ix-< {0} {suc j} (s≤s z≤n)))) (⊑-≼ l)))

    -- A row one step under a source's position: the source is under the spin.
    snoc-spun : ∀ {c j q l e₀} → Cut c → (c ⊕ [ ix j ]) ⊑ (q ⊕ [ l ]) → t q e₀ → Spun c q
    snoc-spun {c} {j} {q} {l} cc sq x with ⊑-snoc q sq
    ... | inj₁ le = j , le
    ... | inj₂ eq with shows cc j
    ...   | _ , _ , (zs , refl) , tz = ⊥-elim (InvAt.flat I x (subst (λ v → t v _) (trans (cong (_⊕ zs) eq) (⊕-assoc q [ l ] zs)) tz))

    quiet : ∀ {c y e} → Cut c → Spun c y → TakeT t y e → Silent e
    quiet cc sp (pass x _ _) with silent cc sp x
    ... | ()
    quiet cc (_ , l) (fail x _ _ _) with silent cc (snoc-spun cc l x) x
    ... | ()
    quiet cc (_ , l) (stop x _ _) with silent cc (snoc-spun cc l x) x
    ... | ()
    quiet cc sp (step x _) = hush
    quiet cc sp (tend x _) with silent cc sp x
    ... | ()
    quiet cc sp (left x _ _) = held

    -- Unfailed before the spin, unfailed under it.
    unfailed-under : ∀ {c j z} → Cut c → ¬ Failed t (c ⊕ [ ix 0 ]) → (c ⊕ [ ix j ]) ⊑ z → ¬ Failed t z
    unfailed-under {c} {j} {z} cc nf sz (g , a , x , nk , gz) with where? c g
    ... | inj₁ g0 = nf (g , a , x , nk , g0)
    ... | inj₂ (inj₁ sp) with silent cc sp x
    ...   | ()
    unfailed-under {c} {j} {z} cc nf sz (g , a , x , nk , gz) | inj₂ (inj₂ after)
      with silent cc (j , conv (⊑-refl (c ⊕ [ ix j ])) (≺→≼ {c ⊕ [ ix j ]} {g} (after j)) gz sz) x
    ... | ()

    kept-at : ∀ {c j r} → ¬ Failed t r → (Σ Pos λ z → (c ⊕ [ ix j ]) ⊑ z × t z (pin r)) → Σ Pos λ z → (c ⊕ [ ix j ]) ⊑ z × O z (pin r)
    kept-at nf (z , sz , x) = z , sz , rows (left x nf (pinned-in x))

    shown : ∀ {c} → Cut′ c → ∀ j → Σ Pos λ z → Σ (Ev A) λ e → (c ⊕ [ ix j ]) ⊑ z × O z e
    shown (cc , inj₁ nf) j with shows cc j
    ... | z , e₀ , sz , x with silent cc (j , sz) x
    ...   | hush = z , skip , sz , rows (step x (unfailed-under cc nf sz))
    ...   | held {r} = z , pin r , sz , rows (left x (λ g → unfailed-under cc nf sz (fd-up {r} {z} g (⊑-≼ (inside-⊑ r z (pinned-in x))))) (pinned-in x))
    shown (cc , inj₂ (r , rc , nf , z₁ , s1 , x₁)) j with kept-at nf (again cc x₁ (0 , s1) rc j)
    ... | z , sz , o = z , pin r , sz , o

    -- A row past a cut's first, failed before the spin: the cut keeps
    -- the pins of a connect leading it.
    hidden : ∀ {c j q e} → Cut c → TakeT t q e → (c ⊕ [ ix (suc j) ]) ⊑ q → Failed t (c ⊕ [ ix 0 ]) → Kept c
    hidden {j = j} cc (pass y _ _) l _ with silent cc (suc j , l) y
    ... | ()
    hidden cc (fail y _ _ _) l _ with silent cc (snoc-spun cc l y) y
    ... | ()
    hidden cc (stop y _ _) l _ with silent cc (snoc-spun cc l y) y
    ... | ()
    hidden {c} {j} cc (step _ nf) l f = ⊥-elim (nf (past-first c j l f))
    hidden {j = j} cc (tend y _) l _ with silent cc (suc j , l) y
    ... | ()
    hidden {c} {j} cc (left {q} {r} y nf ins) l f with ⊑-cmp r (c ⊕ [ ix (suc j) ]) (inside-⊑ r q ins) l
    ... | inj₂ Sr = ⊥-elim (nf (past-first c j Sr f))
    ... | inj₁ rS with ⊑-snoc c rS
    ...   | inj₂ refl = ⊥-elim (nf (past-first c j (⊑-refl _) f))
    ...   | inj₁ rc with again cc y (j , l) rc 1
    ...     | z , z1 , tz = r , rc , nf , z , z1 , tz

    -- A row not past a cut's first it shows is past none.
    honest : ∀ {q e} → TakeT t q e → ¬ Lie Cut′ q → ¬ Lie Cut q
    honest x nl (c , cc , j , l) = nl (c , (cc , inj₁ λ f → nl (c , (cc , inj₂ (hidden cc x l f)) , j , l)) , j , l)

    -- A value is not past a cut's first.
    honest-val : ∀ {g a} → t g (out a) → ¬ Lie Cut g
    honest-val x (c , cc , j , l) with silent cc (suc j , l) x
    ... | ()

    -- An unfailed row shows where it is.
    img : ∀ {b k e₀} → ¬ Failed t b → t k e₀ → k ≺ b → TakeT t k e₀
    img {b} {k} {out a} nf x kb with keep a in eq
    ... | true  = pass x (subst Tr (sym eq) tt) (λ g → nf (fd-up {k} {b} g (≺→≼ {k} {b} kb)))
    ... | false = ⊥-elim (nf (k , a , x , subst (λ v → Tr (not v)) (sym eq) tt , kb))
    img {b} {k} {skip}  nf x kb = step x (λ g → nf (fd-up {k} {b} g (≺→≼ {k} {b} kb)))
    img {b} {k} {end}   nf x kb = tend x (λ g → nf (fd-up {k} {b} g (≺→≼ {k} {b} kb)))
    img {b} {k} {pin r} nf x kb =
      left x (λ g → nf (fd-up {r} {b} g (≼-trans {r} {k} {b} (⊑-≼ (inside-⊑ r k (pinned-in x))) (≺→≼ {k} {b} kb)))) (pinned-in x)

    before-in : ∀ {b} → Before Cut′ O b → ¬ Failed t b → Before Cut t b
    before-in (ks , h) nf = ks , λ x kb → let o = img nf x kb ; a = h (rows o) kb in proj₁ a , honest o (proj₂ a)

    -- To refute a failure, refute the earliest.
    firstfail : ∀ {b} → (∀ {g a} → ¬ Failed t g → t g (out a) → Tr (not (keep a)) → g ≺ b → ⊥) → ¬ Failed t b
    firstfail {b} refute (g , a , x , nk , gb) = few-ind P stp (entered-few s p tt x) x nk gb
      where
        P : Pos → Set
        P g = ∀ {a} → t g (out a) → Tr (not (keep a)) → g ≺ b → ⊥

        stp : ∀ {g} → Few t g → (∀ {v e} → t v e → v ≺ g → P v) → P g
        stp {g} _ ih x nk gb =
          em {P = Failed t g} {G = ⊥}
             (λ { (g′ , a′ , x′ , nk′ , g′g) _ → ih x′ g′g x′ nk′ (≺-trans {g′} {g} {b} g′g gb) })
             (λ nf _ → refute nf x nk gb)
             (λ z → z)

    -- Clean before a point, the next has failed there only if this has.
    unfailed : ∀ {b} → Before Cut′ O b → ¬ Failed t′ b → ¬ Failed t b
    unfailed {b} bf nf′ = firstfail λ {g} {a} nfg x nk gb →
      nf′ (g , a , proj₁ (agree g (out a) (clean-of {e = out a} (before-in (before-down bf (≺→≼ {g} {b} gb)) nfg) (honest-val x))) x , nk , gb)

    -- A source row of the next past a cut's first, failed before the
    -- spin: the cut keeps the pins of a connect leading it.
    hidden′ : ∀ {c j q e} → Cut c → (x′ : TakeT t′ q e) → ¬ Failed t (bound x′) → Before Cut′ O (bound x′)
            → (c ⊕ [ ix (suc j) ]) ⊑ spos x′ → Failed t (c ⊕ [ ix 0 ]) → Kept c
    hidden′ {c} {j} _ (pass _ _ _)   nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (fail _ _ _ _) nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (stop _ _ _)   nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (step _ _)     nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} _ (tend _ _)     nf _ l f = ⊥-elim (nf (past-first c j l f))
    hidden′ {c} {j} cc (left {q} {r} y′ _ ins) nf bf l f with ⊑-cmp r (c ⊕ [ ix (suc j) ]) (inside-⊑ r q ins) l
    ... | inj₂ Sr = ⊥-elim (nf (past-first c j Sr f))
    ... | inj₁ rS with ⊑-snoc c rS
    ...   | inj₂ refl = ⊥-elim (nf (past-first c j (⊑-refl _) f))
    ...   | inj₁ rc with shadow cc y′ (j , l) rc (before-in bf nf)
    ...     | z , z1 , tz = r , rc , nf , z , z1 , tz

    honest′ : ∀ {q e} (x′ : TakeT t′ q e) → ¬ Failed t (bound x′) → Before Cut′ O (bound x′) → ¬ Lie Cut′ q → ¬ Lie Cut (spos x′)
    honest′ x′ nf bf nl (c , cc , j , l) = nl (c , (cc , inj₁ λ f → nl (c , (cc , inj₂ (hidden′ cc x′ nf bf l f)) , j , lq)) , j , lq)
      where lq = ⊑-trans l (under x′)

    seen-at : ∀ {q e ks k e₀} → (∀ {k′ e′} → O k′ e′ → k′ ≺ q → Dep q e k′ e′ → Cov q ks k′ × ¬ Lie Cut′ k′)
            → TakeT t k e₀ → k ≺ q → Dep q e k e₀ → Cov q ks k × ¬ Lie Cut k
    seen-at h o kq d = let a = h (rows o) kq d in proj₁ a , honest o (proj₂ a)

    down : ∀ {q′ q ks k} → Cov q′ ks k × ¬ Lie Cut k → k ≺ q → q ≼ q′ → Cov q ks k × ¬ Lie Cut k
    down (cv , nl) kq qq′ = cov-down cv kq qq′ , nl

    -- Unfailed to its bound, a source waits only on clean rows.
    deps : ∀ {u q e} (x : TakeT u q e) → ¬ Failed t (bound x) → Clean Cut′ O q e
         → Σ (List Pos) λ ks → ∀ {k e₀} → t k e₀ → k ≺ spos x → Dep (spos x) (sev x) k e₀ → Cov (spos x) ks k × ¬ Lie Cut k
    deps (pass {a = a} _ _ _) nf (_ , ks , h) = ks , λ y kq _ → seen-at {e = out a} h (img nf y kq) kq tt
    deps (step _ _)   nf (_ , ks , h) = ks , λ y kq _ → seen-at {e = skip} h (img nf y kq) kq tt
    deps (tend _ _)   nf (_ , ks , h) = ks , λ y kq _ → seen-at {e = end} h (img nf y kq) kq tt
    deps (fail {q} {a} _ _ _ _) nf (_ , ks , h) = ks , λ {k} y kq _ →
      down (seen-at {e = out a} h (img nf y kq) (≺-trans {k} {q} {q ⊕ [ ix 0 ]} kq (≺-ext q [])) tt) kq (≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q []))
    deps (stop {q} _ _ _) nf (_ , ks , h) = ks , λ {k} y kq _ →
      down (seen-at {e = end} h (img nf y kq) (≺-trans {k} {q} {q ⊕ [ last ]} kq (≺-ext q [])) tt) kq (≺→≼ {q} {q ⊕ [ last ]} (≺-ext q []))
    deps (left {q} {r} _ _ ins) nf (_ , ks , h) = ks , λ y kq d → by (d ins) y kq
      where
        by : ∀ {k e₀} → PDep r k e₀ → t k e₀ → k ≺ q → Cov q ks k × ¬ Lie Cut k
        by (inj₁ kr)   y kq = seen-at h (img nf y kr) kq (λ _ → inj₁ kr)
        by (inj₂ refl) y kq = seen-at h (left y nf (pinned-in y)) kq (λ _ → inj₂ refl)

    src-clean : ∀ {q e} (x : TakeT t q e) → Clean Cut′ O q e → Clean Cut t (spos x) (sev x)
    src-clean x cl@(nl , _) = (λ l → honest x nl (lie-up l (under x))) , deps x (unf x) cl

    src-clean′ : ∀ {q e} (x′ : TakeT t′ q e) → Clean Cut′ O q e → ¬ Failed t (bound x′) × Clean Cut t (spos x′) (sev x′)
    src-clean′ x′ cl@(nl , _) = nfb , honest′ x′ nfb bf nl , deps x′ nfb cl
      where
        bf  = before-of cl (bound-≼ x′) (bound-dep x′)
        nfb = unfailed bf (unf x′)

    fwd : ∀ {q e} → Clean Cut′ O q e → O q e → Truncate (TakeT t′) q e
    fwd cl (x , _) = rows′ (move x (proj₁ (agree (spos x) (sev x) sc) (srow x)) nf′)
      where
        sc = src-clean x cl

        nf′ : ¬ Failed t′ (bound x)
        nf′ (g , a , y′ , nk , gb) with bounded {e″ = out a} x gb
        ... | gs , d = unf x (g , a , pull tr sc y′ gs d , nk , gb)

    bwd : ∀ {q e} → Clean Cut′ O q e → Truncate (TakeT t′) q e → O q e
    bwd cl (x′ , _) with src-clean′ x′ cl
    ... | nfb , sc = rows (move x′ (proj₂ (agree (spos x′) (sev x′) sc) (srow x′)) nfb)
