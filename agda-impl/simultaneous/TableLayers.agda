{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S OUTER LAYERS: the lanes' flatMap's record carried out
-- through the combined scan, the closer and the share to the flatMap's
-- elaboration; and the flatMap's case, assembled from its source's and
-- lanes' records.
module simultaneous.TableLayers where


open import Data.Bool using (T; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
import Data.Maybe as M
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

open import Tree using (Obs; FlatOp; flatMap)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; _<ᵖ_; ix; sub; last; inside; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Unpinned; pin; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ≼-trans; ≺→≼; ≺-ext)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; rows; ends)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.TableCorr using (Rel; TR; Corr; Cons; Got)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TableEnv using (Ren; wk; got-ok; pin-ok; after-ok; pin-after-ok; Tab; Tab*; up; up-⊕; _⊕ˡ_; Linked; linked-r*;
  Aligned; aligned-r*; Rest; Out; _⊢_; EnvR; maps; lw; lw*; env-wk; env-wk-eq; Full; Coh; Admits; admits-trig; tab-func; tab-flat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

open import simultaneous.TableFlat using (module Flat; in-if; max-ge; ≼-ˡ; any-≟)
open import simultaneous.TableJoin using (module Joiners)

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

    postulate
      cb-corr        : ∀ N → Corr p c₂ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
      cb-φ-agree     : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
      cb-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                     → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cb-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
      cb-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cb-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cb-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      cb-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (cb-corr N) k
                     → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cb-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      cb-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
      cb-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

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
    cb-in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
    cb-in-bk {N} {k} x u = in-if (endAt (P′ N) k) (λ l → k ∈ bk′ N l)
      (λ eq → ∈-++⁺ʳ (Rel.bk R N _) (any-≟ eq))
      (λ _ → ∈-++⁺ˡ (subst (λ y → k ∈ Rel.bk R N y) (sym (ups-re (Rel.φ R N k))) (Rel.in-bk R x u)))

    -- A put is the lanes' flatMap's, re-emitted.
    cb-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₂ ≼ φ′ N k
    cb-after-φ {N} {k} x u = in-if (endAt (P′ N) k) (λ l → c₂ ≼ l)
      (λ _ → ≼-trans {c₂} {aEnd N} {aEnd N ⊕ˡ (ix 1 ∷ ix 0 ∷ last ∷ [])}
               (≼-trans {c₂} {cA ⊕ [ last ]} {aEnd N} (≼-ˡ c₂ (ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ last ∷ [])) (max-ge (cA ⊕ [ last ]) (aEnds N)))
               (≼-ˡ (aEnd N) (ix 1 ∷ ix 0 ∷ last ∷ [])))
      (λ _ → ≼-trans {c₂} {c₁} {reEmit (Rel.φ R N k)} (≺→≼ {c₂} {c₁} (≺-ext c₂ []))
               (≼-trans {c₁} {Rel.φ R N k} {reEmit (Rel.φ R N k)} (Rel.after-φ R x u) (≼-ˡ (Rel.φ R N k) (sub (rB 1) ∷ ix 1 ∷ ix 0 ∷ []))))

    cb-put-up : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
    cb-put-up le ag (l′ , pt , eq) = l′ , Rel.put-up R le ag pt , eq

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
      { φ = φ′ ; Put = Put′ ; corr = cb-corr ; φ-agree = cb-φ-agree ; bk = bk′ ; in-bk = cb-in-bk ; pb-few = cb-pb-few
      ; back = cb-back ; put-up = cb-put-up ; back-put = cb-back-put
      ; elab-causal = cb-elab-causal ; stable← = cb-stable← ; stable-put = cb-stable-put ; stable-lead = cb-stable-lead
      ; elab-all = cb-elab-all ; func = Rel.func R ; func* = tab-func n (inner op) uρ*c Dc ad₂ ; flat = Rel.flat R ; flat* = tab-flat n (inner op) uρ*c Dc ad₂
      ; pin-in = Rel.pin-in R ; pin-in* = cb-pin-in* ; cons = Rel.cons R ; cons* = cb-cons* ; got = Rel.got R ; got* = cb-got*
      ; after = Rel.after R ; after* = cb-after* ; after-φ = cb-after-φ ; pin-after* = cb-pin-after* ; pin-stable = cb-pin-stable }

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

    postulate
      cz-corr        : ∀ N → Corr p c₃ (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
      cz-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                     → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cz-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
      cz-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cz-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      cz-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      cz-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (cz-corr N) k
                     → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      cz-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      cz-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
      cz-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

    cz-got* : ∀ N → Got (Q′ N)
    cz-got* N = got-ok (3 + N) n (body op) {ρ*h N} (uρ*h N) c₃

    cz-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    cz-pin-in* {N} = pin-ok (3 + N) n (body op) {ρ*h N} c₃

    -- The body's images lie past the closer's body, one label up.
    cz-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → c₃ ≼ φ′ N k
    cz-after-φ {N} {k} x u = ≼-trans {c₃} {c₂} {φ′ N k} (≼-ˡ c₃ (ix 0 ∷ [])) (Rel.after-φ R x u)

    cz-after* : ∀ {N l e} → TR (Q′ N) l e → c₃ ≼ l
    cz-after* {N} = after-ok (3 + N) n (body op) {ρ*h N} c₃

    cz-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → c₃ ≼ r
    cz-pin-after* {N} = pin-after-ok (3 + N) n (body op) {ρ*h N} c₃

    rel′ : Rel P′ Q′ p c₃
    rel′ = record
      { φ = φ′ ; Put = Put′ ; corr = cz-corr ; φ-agree = Rel.φ-agree R ; bk = bk′ ; in-bk = Rel.in-bk R ; pb-few = Rel.pb-few R
      ; back = cz-back ; put-up = Rel.put-up R ; back-put = cz-back-put
      ; elab-causal = cz-elab-causal ; stable← = cz-stable← ; stable-put = cz-stable-put ; stable-lead = cz-stable-lead
      ; elab-all = cz-elab-all ; func = Rel.func R ; func* = tab-func n (body op) uρ*h Dh ad₃ ; flat = Rel.flat R ; flat* = tab-flat n (body op) uρ*h Dh ad₃
      ; pin-in = Rel.pin-in R ; pin-in* = cz-pin-in* ; cons = Rel.cons R ; cons* = cz-cons* ; got = Rel.got R ; got* = cz-got*
      ; after = Rel.after R ; after* = cz-after* ; after-φ = cz-after-φ ; pin-after* = cz-pin-after* ; pin-stable = cz-pin-stable }

  ----------------------------------------------------------------------
  -- THE SHARE: the body is the share's two connects' body, its rows shown
  -- as they are; the trigger's are pins, the shared run's are shown one
  -- label down, so the source's pins return, the layers inside lacking
  -- them.
  module ShareTab (op : FlatOp) (Os : Src) (R : Rel (Pd op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃) where
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

    postulate
      sr-corr        : ∀ N → Corr p p* (φ′ N) (Put′ N) (TR (P′ N)) (TR (Q′ N))
      sr-back        : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N′) k e → Unpinned e → AgreeTo (φ′ N′ k) (TR (Q′ N′)) (TR (Q′ N))
                     → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      sr-put-up      : ∀ {N N′ k l} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → Put′ N k l → Put′ N′ k l
      sr-back-put    : ∀ {N N′ k l} → N ≤ N′ → Put′ N′ k l → AgreeTo l (TR (Q′ N′)) (TR (Q′ N)) → Put′ N k l
      sr-elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      sr-stable←     : ∀ {N N′ k e e′} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′
                     → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo k (TR (P′ N′)) (TR (P′ N))
      sr-stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P′ N′)) (TR (P′ N)) → TR (Q′ N) l e′ → Put′ N k l
                     → AgreeTo l (TR (Q′ N′)) (TR (Q′ N))
      sr-stable-lead : ∀ {N N′ k e e′ m e*} → N ≤ N′ → TR (P′ N) k e → Unpinned e → TR (Q′ N) (φ′ N k) e′ → Corr.Leads (sr-corr N) k
                     → TR (Q′ N) m e* → instantOf m ≡ instantOf (φ′ N k) → AgreeTo m (TR (Q′ N′)) (TR (Q′ N)) → AgreeTo (φ′ N k) (TR (Q′ N′)) (TR (Q′ N))
      sr-elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P′ N′)) (TR (P′ N))) → ∀ {y e} → TR (Q′ N′) y e → TR (Q′ N) y e
      sr-cons        : ∀ {N N′} → Cons (TR (P′ N)) (TR (P′ N′))
      sr-cons*       : ∀ {N N′} → Cons (TR (Q′ N)) (TR (Q′ N′))
      sr-pin-stable  : ∀ {N N′ k e} → N ≤ N′ → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N′)) (TR (P′ N))
                     → (∀ {y r} → r ≼ k → TR (P′ N′) y (pin r) → TR (P′ N) y (pin r))
                     → ∀ {y r} → r ≼ φ′ N k → TR (Q′ N′) y (pin r) → TR (Q′ N) y (pin r)

    -- A put's preimages are the body's, or the source's one label up.
    sr-pb-few : ∀ N l → Σ (List Pos) λ ks → ∀ {k} → Put′ N k l → k ∈ ks
    sr-pb-few N l = proj₁ (Rel.pb-few R N l) ++ proj₁ (Rel.pb-few (Out.rel Os) N (up l)) , go
      where
        go : ∀ {k} → Put′ N k l → k ∈ proj₁ (Rel.pb-few R N l) ++ proj₁ (Rel.pb-few (Out.rel Os) N (up l))
        go (inj₁ pt) = ∈-++⁺ˡ (proj₂ (Rel.pb-few R N l) pt)
        go (inj₂ (_ , l′ , pt , e)) = ∈-++⁺ʳ (proj₁ (Rel.pb-few R N l))
          (proj₂ (Rel.pb-few (Out.rel Os) N (up l)) (subst (Rel.Put (Out.rel Os) N _) (sym (trans (cong up e) (up-⊕ l′ _))) pt))

    sr-φ-agree : ∀ {N N′ k e} → TR (P′ N) k e → Unpinned e → AgreeTo k (TR (P′ N)) (TR (P′ N′)) → φ′ N k ≡ φ′ N′ k
    sr-φ-agree {N} {N′} x u ag = Rel.φ-agree R (pd-keep {op} {N} x u) u (pd-agree {op} {N} {N′} ag)

    sr-in-bk : ∀ {N k e} → TR (P′ N) k e → Unpinned e → k ∈ bk′ N (φ′ N k)
    sr-in-bk {N} x u = Rel.in-bk R (pd-keep {op} {N} x u) u

    sr-got : ∀ N → Got (P′ N)
    sr-got N = got-ok (3 + N) n (flatMap op f s) {ρ N} (uρ N) p

    sr-pin-in : ∀ {N l r} → TR (P′ N) l (pin r) → T (inside r l)
    sr-pin-in {N} = pin-ok (3 + N) n (flatMap op f s) {ρ N} p

    sr-after : ∀ {N k e} → TR (P′ N) k e → p ≼ k
    sr-after {N} = after-ok (3 + N) n (flatMap op f s) {ρ N} p

    sr-got* : ∀ N → Got (Q′ N)
    sr-got* N = got-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} (uρ* N) p*

    sr-pin-in* : ∀ {N l r} → TR (Q′ N) l (pin r) → T (inside r l)
    sr-pin-in* {N} = pin-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} p*

    -- The closer's images lie past the share, two labels up.
    sr-after-φ : ∀ {N k e} → TR (P′ N) k e → Unpinned e → p* ≼ φ′ N k
    sr-after-φ {N} {k} x u = ≼-trans {p*} {c₃} {φ′ N k} (≼-ˡ p* (ix 0 ∷ ix 0 ∷ [])) (Rel.after-φ R (pd-keep {op} {N} x u) u)

    sr-after* : ∀ {N l e} → TR (Q′ N) l e → p* ≼ l
    sr-after* {N} = after-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} p*

    sr-pin-after* : ∀ {N l r} → TR (Q′ N) l (pin r) → p* ≼ r
    sr-pin-after* {N} = pin-after-ok (3 + N) n (elab ρι (flatMap op f s)) {ρ* N} p*

    rel′ : Rel P′ Q′ p p*
    rel′ = record
      { φ = φ′ ; Put = Put′ ; corr = sr-corr ; φ-agree = sr-φ-agree ; bk = bk′ ; in-bk = sr-in-bk ; pb-few = sr-pb-few
      ; back = sr-back ; put-up = sr-put-up ; back-put = sr-back-put
      ; elab-causal = sr-elab-causal ; stable← = sr-stable← ; stable-put = sr-stable-put ; stable-lead = sr-stable-lead
      ; elab-all = sr-elab-all ; func = tab-func n (flatMap op f s) uρ (lw env) ad ; func* = tab-func n (elab ρι (flatMap op f s)) uρ* (lw* env) ad*
      ; flat = tab-flat n (flatMap op f s) uρ (lw env) ad ; flat* = tab-flat n (elab ρι (flatMap op f s)) uρ* (lw* env) ad*
      ; pin-in = sr-pin-in ; pin-in* = sr-pin-in* ; cons = sr-cons ; cons* = sr-cons* ; got = sr-got ; got* = sr-got*
      ; after = sr-after ; after* = sr-after* ; after-φ = sr-after-φ ; pin-after* = sr-pin-after* ; pin-stable = sr-pin-stable }

  flat-tab : ∀ op → Src → (Ls : Lanes) → LanesCoh Ls → Aligned (maps env) ρ p p* → Linked p p* → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*
  flat-tab op Os Ls Lc al lk = ShareTab.rel′ op Os (CloseTab.rel′ op (CombTab.rel′ op (flat-core op Os Ls Lc al lk)))

  postulate
    -- THE FLATMAP'S ORDER FACTS: each row is a source row or a lane row
    -- at its own position, imaged along its stream's map, so each fact is
    -- the source's or the lane's; a lane's subscription is past every
    -- earlier pair that cuts the flatMap alike.
    flatmap-order : ∀ op (Os : Src) (Ls : Lanes) (Lc : LanesCoh Ls) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) → Rest (maps env) ρ (flat-tab op Os Ls Lc al lk)

flat-rel : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
         → Full n s → (Ff : ∀ a → Full n (f a)) → (∀ a → Coh n (f a) (Ff a)) → Full n (flatMap op f s)
flat-rel n op f s Fs Ff Ffc ρ uρ ρι ρ* uρ* env p p* ad ad* al lk = G.flat-tab op Os Ls Lc al lk ⊢ G.flatmap-order op Os Ls Lc al lk
  where
    module F = Flat n f s ρ uρ ρι ρ* uρ* env p p* ad ad*
    module G = Layers n f s ρ uρ ρι ρ* uρ* env p p* ad ad*

    path : List Label
    path = ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ []

    Os : F.Src
    Os = Fs ρ uρ (wk ρι) F.ρ*s F.uρ*s (env-wk F.ttD env) p F.sp* ad (admits-trig n uρ* (lw* env) p* ad*)
           (aligned-r* {Ψ = maps env} {ρ = ρ} al path) (linked-r* lk path)

    Ls : F.Lanes
    Ls a t₁ t₂ t₃ t₄ u h₁ h₂ h₃ h₄ = Ff a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk h₁ (env-wk h₂ (env-wk h₃ (env-wk h₄ env))))

    Lc : F.LanesCoh Ls
    Lc a t₁ t₂ t₃ t₄ u h₁ h₁′ h₂ h₃ h₄ =
      Ffc a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk h₁ E) (env-wk h₁′ E) (env-wk-eq h₁ h₁′ E)
      where E = env-wk h₂ (env-wk h₃ (env-wk h₄ env))
