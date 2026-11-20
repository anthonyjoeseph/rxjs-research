{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S OUTER LAYERS: the lanes' flatMap's record carried out
-- through the combined scan, the closer and the share to the flatMap's
-- elaboration; and the flatMap's case, assembled from its source's and
-- lanes' records.
module simultaneous.TableLayers where

open import Data.Bool using (T; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
import Data.Maybe as M
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; flatMap)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; _<ᵖ_; ix; sub; last; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; Unpinned; pin; skip; _≺_; _≼_)
open import denotation.Laws.Worlds using (_⊑_; ⊑-trans)
open import denotation.Laws.Modulus using (≼-trans; ≺→≼; ≺-ext)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; rows; ends)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.TableCorr using (Same; same; φ≡; nl→; Rel; Corr; Across; Stable; LeadClear; across-of; module Across)
open import simultaneous.TableKit using (TR; Got)
open import simultaneous.Horizon using (Tag; free; held; module Cuts)
open import simultaneous.Readings using (instantOf)
open import simultaneous.HorizonCorr using (module Inter; module Wrap; Own; OwnPut; Btw; PB)
open import simultaneous.TableEnv using (Ren; wk; got-ok; pin-ok; after-ok; pin-after-ok; Tab; Tab*; up; up-⊕; _⊕ˡ_; ⊑-⊕ˡ; Linked; linked-r*;
  Aligned; aligned-r*; Rest; Out; out; same-bd; EnvR; maps; lw; lw*; hot-coh; env-wk; env-wk-eq; EnvEq; Full; Coh; Admits; dbd; tab-func; tab-flat)
open import simultaneous.TreeBounded using (admits-trig; tree-bounded)
open import simultaneous.HorizonTree using (bd)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

open import simultaneous.TableFlat using (module Flat; in-if; max-ge; ≼-ˡ; any-≟; if-≡)
open import simultaneous.TableJoin using (module Joiners)
open import simultaneous.TableCoh using (module Two)

module Layers {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (ad : Admits (lw env) p) (ad* : Admits (lw* env) p*) where

  open Flat n f s ρ uρ ρι ρ* uρ* env p p* ad ad*
  open Joiners n f s ρ uρ ρι ρ* uρ* env p p* ad ad* using (flat-core)

  ----------------------------------------------------------------------
  -- THE COMBINED SCAN: each row of the lanes' flatMap read by the scan's
  -- lane branch and re-emitted by `each` as it is, the scan's other emits
  -- all marks; the flatMap's end at the `nothing` the scan's concat sends
  -- past the last of its three branches' ends.
  module CombTab (op : FlatOp) (R : Rel (Pd op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁) where
    P′ Q′ : ℕ → _
    P′ = Pd op
    Q′ = λ N → listC (3 + N) n (inner op) (ρ*c N) c₂

    -- The scan's three branches, under its concat's first lane: the
    -- outer, the lanes and the closer, each read at `rB`.
    cA : Pos
    cA = c₂ ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])

    rB : ℕ → Pos
    rB i = cA ⊕ˡ (ix i ∷ ix 1 ∷ [])

    readEnd : Pos → List Pos → List Pos
    readEnd r = L.map (λ e → if r <ᵖ e then e ⊕ [ sub r ] else r ⊕ [ last ])

    core-hot : ℕ → Tb.Listed (IE B)
    core-hot N = hotOf (proj₁ (listC-ok (3 + N) n (core op) {ρ*c N} (uρ*c N) c₁))

    -- The last of the branches' ends, as the merge over them ends.
    aEnds : ℕ → List Pos
    aEnds N = readEnd (rB 0) (ends (rows (sh-tab N))) ++ readEnd (rB 1) (ends (rows (core-hot N)))
              ++ readEnd (rB 2) (ends (rows (cl-tab N)))

    aEnd : ℕ → Pos
    aEnd N = L.foldr (λ x y → if x <ᵖ y then y else x) (cA ⊕ [ last ]) (aEnds N)

    reEmit : Pos → Pos
    reEmit l = l ⊕ˡ (sub (rB 1) ∷ ix 1 ∷ ix 0 ∷ [])

    φ′ : ℕ → Pos → Pos
    φ′ N k = if endAt (P′ N) k then aEnd N ⊕ˡ (ix 1 ∷ ix 0 ∷ last ∷ []) else reEmit (Rel.φ R N k)

    Put′ : ℕ → Pos → Pos → Set
    Put′ N k l = Σ Pos λ l′ → Rel.Put R N k l′ × (l ≡ reEmit l′ ⊎ l ≡ l′ ⊕ [ ix 0 ])

    bk′ : ℕ → Pos → List Pos
    bk′ N l = Rel.bk R N (ups 3 l) ++ endsOf (P′ N)

    Late′ : ℕ → Pos → Set
    Late′ = Rel.Late R

    postulate
      cb-corr        : ∀ N → Corr p c₂ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))

    -- Three labels up undo the re-emit.
    ups-re : ∀ l → ups 3 (reEmit l) ≡ l
    ups-re l = trans (cong (ups 2) (up-⊕ _ _)) (trans (cong (ups 1) (up-⊕ _ _)) (up-⊕ _ _))

    -- A put's preimages are the lanes' flatMap's at the image re-emitted,
    -- or shown by the combined connect.
    cb-pb-few : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
    cb-pb-few N l = proj₁ (Rel.pb-few R N (ups 3 l)) ++ proj₁ (Rel.pb-few R N (up l)) , go
      where
        go : ∀ {k} → Put′ N k l → k ∈ proj₁ (Rel.pb-few R N (ups 3 l)) ++ proj₁ (Rel.pb-few R N (up l))
        go (l′ , pt , inj₁ e) = ∈-++⁺ˡ (proj₂ (Rel.pb-few R N (ups 3 l)) (subst (Rel.Put R N _) (trans (sym (ups-re l′)) (cong (ups 3) (sym e))) pt))
        go (l′ , pt , inj₂ e) = ∈-++⁺ʳ (proj₁ (Rel.pb-few R N (ups 3 l))) (proj₂ (Rel.pb-few R N (up l)) (subst (Rel.Put R N _) (sym (trans (cong up e) (up-⊕ l′ _))) pt))

    -- A value's preimage is listed at its re-emit, an end among the ends.
    cb-in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
    cb-in-bk {N} {k} x u nl = in-if (endAt (P′ N) k) (λ l → k ∈ bk′ N l)
      (λ eq → ∈-++⁺ʳ (Rel.bk R N _) (any-≟ eq))
      (λ _ → ∈-++⁺ˡ (subst (λ y → k ∈ Rel.bk R N y) (sym (ups-re (Rel.φ R N k))) (Rel.in-bk R x u nl)))

    -- A put is the lanes' flatMap's, re-emitted.
    cb-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₂ ≼ φ′ N k
    cb-after-φ {N} {k} x u nl = in-if (endAt (P′ N) k) (λ l → c₂ ≼ l)
      (λ _ → ≼-trans {c₂} {aEnd N} {aEnd N ⊕ˡ (ix 1 ∷ ix 0 ∷ last ∷ [])}
               (≼-trans {c₂} {cA ⊕ [ last ]} {aEnd N} (≼-ˡ c₂ (ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])) (max-ge (cA ⊕ [ last ]) (aEnds N)))
               (≼-ˡ (aEnd N) (ix 1 ∷ ix 0 ∷ last ∷ [])))
      (λ _ → ≼-trans {c₂} {c₁} {reEmit (Rel.φ R N k)} (≺→≼ {c₂} {c₁} (≺-ext c₂ []))
               (≼-trans {c₁} {Rel.φ R N k} {reEmit (Rel.φ R N k)} (Rel.after-φ R x u nl) (≼-ˡ (Rel.φ R N k) (sub (rB 1) ∷ ix 1 ∷ ix 0 ∷ []))))

    -- THE COMBINED SCAN'S HANGS: the scan wraps the lanes' flatMap alone,
    -- re-emitting each of its rows; it keeps the boundaries a plain one
    -- partners, moving no row across one.
    cb-bd* : ℕ → Pos → Tag → Set
    cb-bd* = bd n (inner op) ρ*c uρ*c (dbd Dc) c₂

    cb-bounded* : Cuts.Bounded (λ N → TR (Q′ N)) cb-bd*
    cb-bounded* = tree-bounded n (inner op) ρ*c uρ*c Dc c₂ ad₂

    postulate
      cb-keeps    : ∀ N {b b* g g*} → Rel.Bd R N b g → Rel.Bd* R N b* g* → Btw (Own (TR (P′ N)) (Late′ N)) (Rel.φ R N) b b* → cb-bd* N b* g*
      cb-only     : ∀ N {b g} → cb-bd* N b g → Σ Tag λ g₀ → Rel.Bd* R N b g₀ × (g ≡ g₀ ⊎ g ≡ free)
      cb-moved    : ∀ N {k b g} → Own (TR (P′ N)) (Late′ N) k → Rel.Bd* R N b g → (Rel.φ R N k ≺ b → φ′ N k ≺ b) × (φ′ N k ≺ b → Rel.φ R N k ≺ b)
      cb-moved-q  : ∀ N {k b q} → Own (TR (P′ N)) (Late′ N) k → Rel.Bd* R N b (held q) → (Rel.φ R N k ≺ q → φ′ N k ≺ q) × (φ′ N k ≺ q → Rel.φ R N k ≺ q)
      cb-putw     : ∀ N {b b* g*} → Rel.Bd* R N b* g* → PB (OwnPut (TR (P′ N)) (Rel.Put R N)) b b* → PB (OwnPut (TR (P′ N)) (Put′ N)) b b*
      cb-stable : Stable (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Put′ Late′ (Rel.Bd R) cb-bd*
      cb-lead   : LeadClear (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Late′ (Rel.Bd R) cb-bd*

    -- A put skip is no end: re-emitted, its image lies under the lanes'
    -- flatMap's, over no boundary of the flatMap's, which the scan's are.
    cb-put-off* : ∀ {N k l b g} → TR (P′ N) k skip → ¬ Late′ N k → Put′ N k l → cb-bd* N b g → ¬ φ′ N k ⊑ b
    cb-put-off* {N} {k} {b = b} x nl (_ , pl , _) bd = go (endAt (P′ N) k) refl
      where
        go : ∀ c → endAt (P′ N) k ≡ c → ¬ (if c then aEnd N ⊕ˡ (ix 1 ∷ ix 0 ∷ last ∷ []) else reEmit (Rel.φ R N k)) ⊑ b
        go true  eq _ = skip≢end (Rel.func R x (endAt-E (P′ N) eq))
        go false _  h = Rel.skip-off* R x nl pl (proj₁ (proj₂ (cb-only N bd)))
                          (⊑-trans (⊑-⊕ˡ (Rel.φ R N k) (sub (rB 1) ∷ ix 1 ∷ ix 0 ∷ [])) h)

    cb-bcorr : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (Rel.Bd R N) (cb-bd* N)
    cb-bcorr N = Wrap.corr (Own (TR (P′ N)) (Late′ N)) (Rel.φ R N) (φ′ N) (OwnPut (TR (P′ N)) (Rel.Put R N)) (OwnPut (TR (P′ N)) (Put′ N))
      (Rel.Bd R N) (Rel.Bd* R N) (cb-bd* N) (Rel.bcorr R N)
      (cb-keeps N) (cb-only N) (λ {k} {b} {g} → cb-moved N {k} {b} {g}) (λ {k} {b} {q} → cb-moved-q N {k} {b} {q}) (cb-putw N)

    cb-got* : ∀ N → Got (Q′ N)
    cb-got* N = got-ok (3 + N) n (inner op) {ρ*c N} (uρ*c N) c₂

    cb-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    cb-pin-in* {N} = pin-ok (3 + N) n (inner op) {ρ*c N} c₂

    cb-after* : ∀ {N l e} → TR (Q′ N) l e → c₂ ≼ l
    cb-after* {N} = after-ok (3 + N) n (inner op) {ρ*c N} c₂

    cb-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₂ ≼ r
    cb-pin-after* {N} = pin-after-ok (3 + N) n (inner op) {ρ*c N} c₂

    rel′ : Rel P′ Q′ p c₂
    rel′ = record
      { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = cb-corr ; bk = bk′ ; in-bk = cb-in-bk ; pb-few = cb-pb-few
      ; func = Rel.func R ; func* = tab-func n (inner op) uρ*c Dc ad₂ ; flat = Rel.flat R ; flat* = tab-flat n (inner op) uρ*c Dc ad₂
      ; pin-in = Rel.pin-in R ; pin-in* = cb-pin-in* ; got = Rel.got R ; got* = cb-got*
      ; after = Rel.after R ; after* = cb-after* ; after-φ = cb-after-φ ; pin-after* = cb-pin-after*
      ; Bd = Rel.Bd R ; Bd* = cb-bd* ; bounded = Rel.bounded R ; bounded* = cb-bounded* ; bcorr = cb-bcorr ; across = across-of (λ N → cb-bcorr N) (cb-stable) (λ {N} → cb-lead {N}) ; skip-off* = cb-put-off* }

  ----------------------------------------------------------------------
  -- THE CLOSER: the combined run is the closer's connect's body, its rows
  -- shown as they are; the closer, that connect's source, shows only
  -- pins and skips.
  module CloseTab (op : FlatOp) (R : Rel (Pd op) (λ N → listC (3 + N) n (inner op) (ρ*c N) c₂) p c₂) where
    P′ Q′ : ℕ → _
    P′ = Pd op
    Q′ = λ N → listC (3 + N) n (body op) (ρ*h N) c₃

    φ′ : ℕ → Pos → Pos
    φ′ = Rel.φ R

    Put′ : ℕ → Pos → Pos → Set
    Put′ = Rel.Put R

    bk′ : ℕ → Pos → List Pos
    bk′ = Rel.bk R

    Late′ : ℕ → Pos → Set
    Late′ = Rel.Late R

    postulate
      cz-corr        : ∀ N → Corr p c₃ (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))

    -- THE CLOSER'S HANGS: the closer wraps the combined run alone, its
    -- rows where they were; it keeps the boundaries a plain one partners.
    cz-bd* : ℕ → Pos → Tag → Set
    cz-bd* = bd n (body op) ρ*h uρ*h (dbd Dh) c₃

    cz-bounded* : Cuts.Bounded (λ N → TR (Q′ N)) cz-bd*
    cz-bounded* = tree-bounded n (body op) ρ*h uρ*h Dh c₃ ad₃

    postulate
      cz-keeps    : ∀ N {b b* g g*} → Rel.Bd R N b g → Rel.Bd* R N b* g* → Btw (Own (TR (P′ N)) (Late′ N)) (Rel.φ R N) b b* → cz-bd* N b* g*
      cz-only     : ∀ N {b g} → cz-bd* N b g → Σ Tag λ g₀ → Rel.Bd* R N b g₀ × (g ≡ g₀ ⊎ g ≡ free)
      -- An instant's leading row lies before the plain hangs where a row
      -- of the combined run's, in its image's instant, lies before the
      -- closer's.
      cz-lead-clear : ∀ {N k e m e*} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k
                    → (∀ {k′ e′} → TR (P′ N) k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′)
                    → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → Cuts.Clear (λ N → TR (Q′ N)) cz-bd* N m
                    → Cuts.Clear (λ N → TR (P′ N)) (Rel.Bd R) N k

    -- Every hang of the combined run is the closer's, partnered as it is:
    -- what lies before the closer's lies before the combined run's.
    cz-clear : ∀ {N l} → Cuts.Clear (λ N → TR (Q′ N)) cz-bd* N l → Cuts.Clear (λ N → TR (listC (3 + N) n (inner op) (ρ*c N) c₂)) (Rel.Bd* R) N l
    cz-clear {N} {l} cl {b} {g} bd* = cl {b} {g} (cz-keeps N {_} {b} {_} {g} (proj₁ (proj₂ (proj₂ fr))) bd* (proj₁ (proj₂ (proj₂ (proj₂ fr)))))
      where fr = Inter.BCorr.from (Rel.bcorr R N) bd*

    cz-bcorr : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (Rel.Bd R N) (cz-bd* N)
    cz-bcorr N = Wrap.corr (Own (TR (P′ N)) (Late′ N)) (Rel.φ R N) (φ′ N) (OwnPut (TR (P′ N)) (Rel.Put R N)) (OwnPut (TR (P′ N)) (Put′ N))
      (Rel.Bd R N) (Rel.Bd* R N) (cz-bd* N) (Rel.bcorr R N)
      (cz-keeps N) (cz-only N) (λ _ _ → (λ x → x) , (λ x → x)) (λ _ _ → (λ x → x) , (λ x → x)) (λ _ pb → pb)

    cz-got* : ∀ N → Got (Q′ N)
    cz-got* N = got-ok (3 + N) n (body op) {ρ*h N} (uρ*h N) c₃

    cz-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    cz-pin-in* {N} = pin-ok (3 + N) n (body op) {ρ*h N} c₃

    -- The body's images lie past the closer's body, one label up.
    cz-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → c₃ ≼ φ′ N k
    cz-after-φ {N} {k} x u nl = ≼-trans {c₃} {c₂} {φ′ N k} (≼-ˡ c₃ (ix 0 ∷ [])) (Rel.after-φ R x u nl)

    cz-after* : ∀ {N l e} → TR (Q′ N) l e → c₃ ≼ l
    cz-after* {N} = after-ok (3 + N) n (body op) {ρ*h N} c₃

    cz-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₃ ≼ r
    cz-pin-after* {N} = pin-after-ok (3 + N) n (body op) {ρ*h N} c₃

    rel′ : Rel P′ Q′ p c₃
    rel′ = record
      { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = cz-corr ; bk = bk′ ; in-bk = Rel.in-bk R ; pb-few = Rel.pb-few R
      ; func = Rel.func R ; func* = tab-func n (body op) uρ*h Dh ad₃ ; flat = Rel.flat R ; flat* = tab-flat n (body op) uρ*h Dh ad₃
      ; pin-in = Rel.pin-in R ; pin-in* = cz-pin-in* ; got = Rel.got R ; got* = cz-got*
      ; after = Rel.after R ; after* = cz-after* ; after-φ = cz-after-φ ; pin-after* = cz-pin-after*
      ; Bd = Rel.Bd R ; Bd* = cz-bd* ; bounded = Rel.bounded R ; bounded* = cz-bounded* ; bcorr = cz-bcorr
      ; across = record
        { back-clear = λ {N} {N′} {k} {e} le x un nl cl* → Across.back-clear (Rel.across R) {N} {N′} {k} {e} le x un nl (cz-clear {N} {φ′ N′ k} cl*)
        ; put-clear = λ {N} {N′} {k} {e} {l} le x pl cl* → Across.put-clear (Rel.across R) {N} {N′} {k} {e} {l} le x pl (cz-clear {N} {l} cl*)
        ; lead-clear = λ {N} {k} {e} {m} {e*} → cz-lead-clear {N} {k} {e} {m} {e*} }
      ; skip-off* = λ {N} x nl pl bd → Rel.skip-off* R x nl pl (proj₁ (proj₂ (cz-only N bd))) }

  ----------------------------------------------------------------------
  -- THE SHARE: the body is the share's two connects' body, its rows shown
  -- as they are; the trigger's are pins, the shared run's are shown one
  -- label down, so the source's pins return, the layers inside lacking
  -- them.
  module ShareTab (op : FlatOp) (Os : Src) (R : Rel (Pd op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃)
    (sr-bounded : Cuts.Bounded (λ N → TR (P op N)) (Rel.Bd R)) where
    P′ Q′ : ℕ → _
    P′ = P op
    Q′ = Tab* n ρι (flatMap op f s) ρ* p*

    φ′ : ℕ → Pos → Pos
    φ′ = Rel.φ R

    -- The body's puts, and a source's pin put where the share's connect
    -- shows the source's row.
    Put′ : ℕ → Pos → Pos → Set
    Put′ N k l = Rel.Put R N k l
               ⊎ (Σ Pos λ r → TR (Tab n s ρ p N) k (pin r)) × (Σ Pos λ l′ → Rel.Put (Out.rel Os) N k l′ × l ≡ l′ ⊕ [ ix 0 ])

    bk′ : ℕ → Pos → List Pos
    bk′ = Rel.bk R

    -- The body's late rows, the source's pins never late.
    Late′ : ℕ → Pos → Set
    Late′ N k = (Σ (Ev B) λ e → TR (Pd op N) k e) × Rel.Late R N k

    -- A row the body shows is late here as there.
    nl-pd : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → ¬ Rel.Late R N k
    nl-pd {N} x u nl lt = nl ((_ , pd-keep {op} {N} x u) , lt)

    postulate
      sr-corr        : ∀ N → Corr p p* (φ′ N) (Put′ N) (Late′ N) (TR (P′ N)) (TR (Q′ N))

    -- A put's preimages are the body's, or the source's one label up.
    sr-pb-few : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
    sr-pb-few N l = proj₁ (Rel.pb-few R N l) ++ proj₁ (Rel.pb-few (Out.rel Os) N (up l)) , go
      where
        go : ∀ {k} → Put′ N k l → k ∈ proj₁ (Rel.pb-few R N l) ++ proj₁ (Rel.pb-few (Out.rel Os) N (up l))
        go (inj₁ pt) = ∈-++⁺ˡ (proj₂ (Rel.pb-few R N l) pt)
        go (inj₂ (_ , l′ , pt , e)) = ∈-++⁺ʳ (proj₁ (Rel.pb-few R N l))
          (proj₂ (Rel.pb-few (Out.rel Os) N (up l)) (subst (Rel.Put (Out.rel Os) N _) (sym (trans (cong up e) (up-⊕ l′ _))) pt))

    sr-in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → k ∈ bk′ N (φ′ N k)
    sr-in-bk {N} x u nl = Rel.in-bk R (pd-keep {op} {N} x u) u (nl-pd x u nl)

    -- THE SHARE'S HANGS: the share returns the source's pins the layers
    -- inside lack, so its plain side is the flatMap itself, hanging as
    -- its tree does; its elaborated side wraps the body and the trigger.
    sr-bd* : ℕ → Pos → Tag → Set
    sr-bd* = bd n (elab ρι (flatMap op f s)) ρ* uρ* (dbd (lw* env)) p*

    sr-bounded* : Cuts.Bounded (λ N → TR (Q′ N)) sr-bd*
    sr-bounded* = tree-bounded n (elab _ (flatMap op f s)) ρ* uρ* (lw* env) p* ad*

    postulate
      sr-bcorr    : ∀ N → Inter.BCorr (Own (TR (P′ N)) (Late′ N)) (φ′ N) (OwnPut (TR (P′ N)) (Put′ N)) (Rel.Bd R N) (sr-bd* N)
      sr-stable : Stable (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Put′ Late′ (Rel.Bd R) sr-bd*
      sr-lead   : LeadClear (λ N → TR (P′ N)) (λ N → TR (Q′ N)) φ′ Late′ (Rel.Bd R) sr-bd*
      -- every row not late imaged at a row of the elaborated flatMap
      sr-img      : ∀ N {k} → Own (TR (P′ N)) (Late′ N) k → Σ (Ev (IE B)) (TR (Q′ N) (φ′ N k))

    -- A put skip is imaged as any row is, so over no boundary.
    sr-put-off* : ∀ {N k l b g} → TR (P′ N) k skip → ¬ Late′ N k → Put′ N k l → sr-bd* N b g → ¬ φ′ N k ⊑ b
    sr-put-off* x nl _ b₀ = proj₂ (Cuts.Bounded.gap sr-bounded* b₀ (proj₂ (sr-img _ (skip , x , tt , nl))))

    sr-got : ∀ N → Got (P′ N)
    sr-got N = got-ok (3 + N) n (flatMap op f s) {ρ N} (uρ N) p

    sr-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
    sr-pin-in {N} = pin-ok (3 + N) n (flatMap op f s) {ρ N} p

    sr-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
    sr-after {N} = after-ok (3 + N) n (flatMap op f s) {ρ N} p

    sr-got* : ∀ N → Got (Q′ N)
    sr-got* N = got-ok (3 + N) n (elab _ (flatMap op f s)) {ρ* N} (uρ* N) p*

    sr-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    sr-pin-in* {N} = pin-ok (3 + N) n (elab _ (flatMap op f s)) {ρ* N} p*

    -- The closer's images lie past the share, two labels up.
    sr-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → p* ≼ φ′ N k
    sr-after-φ {N} {k} x u nl = ≼-trans {p*} {c₃} {φ′ N k} (≼-ˡ p* (ix 0 ∷ ix 0 ∷ [])) (Rel.after-φ R (pd-keep {op} {N} x u) u (nl-pd x u nl))

    sr-after* : ∀ {N l e} → TR (Q′ N) l e → p* ≼ l
    sr-after* {N} = after-ok (3 + N) n (elab _ (flatMap op f s)) {ρ* N} p*

    sr-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → p* ≼ r
    sr-pin-after* {N} = pin-after-ok (3 + N) n (elab _ (flatMap op f s)) {ρ* N} p*

    rel′ : Rel P′ Q′ p p*
    rel′ = record
      { φ = φ′ ; Put = Put′ ; Late = Late′ ; corr = sr-corr ; bk = bk′ ; in-bk = sr-in-bk ; pb-few = sr-pb-few
      ; func = tab-func n (flatMap op f s) uρ (lw env) ad ; func* = tab-func n (elab _ (flatMap op f s)) uρ* (lw* env) ad*
      ; flat = tab-flat n (flatMap op f s) uρ (lw env) ad ; flat* = tab-flat n (elab _ (flatMap op f s)) uρ* (lw* env) ad*
      ; pin-in = sr-pin-in ; pin-in* = sr-pin-in* ; got = sr-got ; got* = sr-got*
      ; after = sr-after ; after* = sr-after* ; after-φ = sr-after-φ ; pin-after* = sr-pin-after*
      ; Bd = Rel.Bd R ; Bd* = sr-bd* ; bounded = sr-bounded ; bounded* = sr-bounded* ; bcorr = sr-bcorr ; across = across-of (λ N → sr-bcorr N) (sr-stable) (λ {N} → sr-lead {N}) ; skip-off* = sr-put-off* }

  -- The layers pass the core's boundaries through: the flatMap's own.
  flat-hangs : ∀ op (Os : Src) (Ls : Lanes) (Lc : LanesCoh Ls) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*)
             → Cuts.Bounded (λ N → TR (P op N)) (Rel.Bd (CloseTab.rel′ op (CombTab.rel′ op (flat-core op Os Ls Lc al lk))))
  flat-hangs (mergeᶠ M.nothing)  Os Ls Lc al lk = jtree (mergeᶠ M.nothing)
  flat-hangs (mergeᶠ (M.just k)) Os Ls Lc al lk = jtree (mergeᶠ (M.just k))
  flat-hangs switchᶠ           Os Ls Lc al lk = jtree switchᶠ
  flat-hangs exhaustᶠ          Os Ls Lc al lk = jtree exhaustᶠ

  flat-tab : ∀ op → Src → (Ls : Lanes) → LanesCoh Ls → Aligned (maps env) ρ p p* → Linked p p* → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*
  flat-tab op Os Ls Lc al lk = ShareTab.rel′ op Os (CloseTab.rel′ op (CombTab.rel′ op (flat-core op Os Ls Lc al lk))) (flat-hangs op Os Ls Lc al lk)

  postulate
    -- THE FLATMAP'S ORDER FACTS: each row is a source row or a lane row
    -- at its own position, imaged along its stream's map, so each fact is
    -- the source's or the lane's; a lane's subscription is past every
    -- earlier pair that cuts the flatMap alike.
    flatmap-order : ∀ op (Os : Src) (Ls : Lanes) (Lc : LanesCoh Ls) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) → Rest (maps env) ρ (flat-tab op Os Ls Lc al lk)

-- THE FLATMAP'S PARTS: its source's record, under the trigger's hot, and
-- each lane's, under the hots the lane's elaboration subscribes.
module FlatRel {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (Fs : Full n s) (Ff : ∀ a → Full n (f a)) (Ffc : ∀ a → Coh n (f a) (Ff a))
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) (ad : Admits (lw env) p) (ad* : Admits (lw* env) p*) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) where
  module F = Flat n f s ρ uρ ρι ρ* uρ* env p p* ad ad*
  module G = Layers n f s ρ uρ ρι ρ* uρ* env p p* ad ad*

  path : List Label
  path = ix 1 ∷ last ∷ sub (p* ⊕ˡ (ix 0 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ [])) ∷ ix 1 ∷ []

  Os : F.Src
  Os = Fs ρ uρ (wk ρι) F.ρ*s F.uρ*s (env-wk F.ttD env) p F.sp* ad (admits-trig n uρ* (lw* env) p* ad*)
         (aligned-r* {Ψ = maps env} {ρ = ρ} al path) (linked-r* lk path)

  Ls : F.Lanes
  Ls a t₁ t₂ t₃ t₄ u h₁ h₂ h₃ h₄ = Ff a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk h₁ (env-wk h₂ (env-wk h₃ (env-wk h₄ env))))

  Lc : F.LanesCoh Ls
  Lc a t₁ t₂ t₃ t₄ u h₁ h₁′ h₂ h₃ h₄ =
    Ffc a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk h₁ E₄) (env-wk h₁′ E₄) (env-wk-eq h₁ h₁′ {E₄} {E₄} (hot-coh E₄))
    where E₄ = env-wk h₂ (env-wk h₃ (env-wk h₄ env))

  -- The lanes' flatMap's record.
  Rc : Rel (F.Pd op) (λ N → listC (3 + N) n (F.core op) (F.ρ*c N) F.c₁) p F.c₁
  Rc = Joiners.flat-core n f s ρ uρ ρι ρ* uρ* env p p* ad ad* op Os Ls Lc al lk

flat-rel : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
         → Full n s → (Ff : ∀ a → Full n (f a)) → (∀ a → Coh n (f a) (Ff a)) → Full n (flatMap op f s)
flat-rel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* env p p* ad ad* al lk =
  out (G.flat-tab op Os Ls Lc al lk) (G.flatmap-order op Os Ls Lc al lk) (Joiners.flat-core-pin n f s ρ uρ ρι ρ* uρ* env p p* ad ad* op Os Ls Lc al lk) same-bd
  where open FlatRel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* env p p* ad ad* al lk

-- THE LANES' MAP IS THE SUBSCRIPTIONS': two environments whose hots map
-- alike give the lanes' flatMap one map and late rows, the source's map alike by the
-- source's coherence and each lane's by the lane's.
core-coh : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
           (Fs : Full n s) (Ff : ∀ a → Full n (f a)) (Ffc : ∀ a → Coh n (f a) (Ff a)) → Coh n s Fs
         → ∀ (ρ : ℕ → All Tb.Listed Γ) uρ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) uρ* (E E′ : EnvR ρ ρι ρ*) → EnvEq E E′
         → ∀ p p* (a : Admits (lw E) p) (a′ : Admits (lw E′) p) (a* : Admits (lw* E) p*) (a*′ : Admits (lw* E′) p*)
             (al : Aligned (maps E) ρ p p*) (al′ : Aligned (maps E′) ρ p p*) (lk lk′ : Linked p p*) N y
         → Same (FlatRel.Rc n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* E p p* a a* al lk) (FlatRel.Rc n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′) N y
core-coh n op f s Fs Ff Ffc cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ =
  Two.joiners-coh n f s ρ uρ ρι ρ* uρ* E E′ p p* a a′ a* a*′ X.Os X′.Os X.Ls X′.Ls X.Lc X′.Lc os≡ ls≡ op al al′ lk lk′
  where
    module X  = FlatRel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* E  p p* a  a*  al  lk
    module X′ = FlatRel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′
    os≡ : ∀ N y → Same (Out.rel X.Os) (Out.rel X′.Os) N y
    os≡ = cs ρ uρ (wk ρι) X.F.ρ*s X.F.uρ*s (env-wk X.F.ttD E) (env-wk X′.F.ttD E′) (env-wk-eq X.F.ttD X′.F.ttD {E} {E′} ee) p X.F.sp* a a′
             (admits-trig n uρ* (lw* E) p* a*) (admits-trig n uρ* (lw* E′) p* a*′)
             (aligned-r* {Ψ = maps E} {ρ = ρ} al X.path) (aligned-r* {Ψ = maps E′} {ρ = ρ} al′ X.path) (linked-r* lk X.path) (linked-r* lk′ X.path)
    ls≡ : Two.LanesX n f s ρ uρ ρι ρ* uρ* E E′ p p* a a′ a* a*′ X.Ls X′.Ls
    ls≡ b t₁ t₂ t₃ t₄ u h₁ h₁′ h₂ h₂′ h₃ h₃′ h₄ h₄′ =
      Ffc b ρ uρ X.F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk h₁ E₂) (env-wk h₁′ E₂′)
          (env-wk-eq h₁ h₁′ {E₂} {E₂′} (env-wk-eq h₂ h₂′ {E₃} {E₃′} (env-wk-eq h₃ h₃′ {E₄} {E₄′} (env-wk-eq h₄ h₄′ {E} {E′} ee))))
      where
        E₄  = env-wk h₄ E
        E₄′ = env-wk h₄′ E′
        E₃  = env-wk h₃ E₄
        E₃′ = env-wk h₃′ E₄′
        E₂  = env-wk h₂ E₃
        E₂′ = env-wk h₂′ E₃′

-- A flatMap's map is its lanes' flatMap's, re-emitted by the combined
-- scan: coherent where the lanes' flatMap is.
flat-coh : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
           (Fs : Full n s) (Ff : ∀ a → Full n (f a)) (Ffc : ∀ a → Coh n (f a) (Ff a))
         → Coh n s Fs → Coh n (flatMap op f s) (flat-rel n op f s Fs Ff Ffc)
flat-coh n op f s Fs Ff Ffc cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y =
  same (if-≡ {b = X.F.endAt (X.G.CombTab.P′ op X.Rc N) y} {b′ = X.F.endAt (X′.G.CombTab.P′ op X′.Rc N) y} refl (λ _ → refl)
          (λ _ → cong (X.G.CombTab.reEmit op X.Rc) (φ≡ cc)))
       (λ { nl (r , lt) → nl→ cc (λ lt₀ → nl (r , lt₀)) lt })
  where module X  = FlatRel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* E  p p* a  a*  al  lk
        module X′ = FlatRel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′
        cc = core-coh n op f s Fs Ff Ffc cs ρ uρ ρι ρ* uρ* E E′ ee p p* a a′ a* a*′ al al′ lk lk′ N y
