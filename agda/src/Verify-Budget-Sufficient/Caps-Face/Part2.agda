-- Verify-Budget-Sufficient.Caps-Face.Part2
-- ONE foldStep PER SYNTAX NODE … END OF PLUG SECTION
module Verify-Budget-Sufficient.Caps-Face.Part2 where

open import Data.Bool    using (true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _⊔_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-refl; ≤-reflexive; +-identityʳ; ⊔-mono-≤; m≤m+n; m≤n+m; n≤1+n; +-mono-≤;
  ^-monoˡ-≤; *-mono-≤; m≤m⊔n; m≤n⊔m; ⊔-lub; *-zeroʳ)
open import Data.Empty   using (⊥)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Prim      using (_at_from_as_; after_,_)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Ctx; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; varIx; renExp;
  renTm; renTms; Ren∈; ext∈; ++Ren; wkTm; reify; Exp; Tm; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
  fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; lookupEnv)
open import Rx.Frame-Width using (pWᵉ; pWᵛ; dWᵉ; dWᵗ; dWᵗˢ; dWᵛ; outWᵛ; outWᵉ; innWᵉ; innWᵗ; innWᵗˢ; pmOᵉ; pmOᵗ; pmIᵉ; pmIᵗ;
  pmIᵗˢ; _∈ᵇ_; outWⱽ; innWⱽ; innWᵗⱽ; innWᵗˢⱽ; pmOⱽ; pmOᵗⱽ; pmIⱽ; pmIᵗⱽ; pmIᵗˢⱽ; dWⱽ; dWᵗⱽ;
  dWᵗˢⱽ)
open import Rx.Evaluator using (foldStep; iterFold)
open import Rx.Slots using (scripted; shared; Slots)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Measures using
  (ext-≢; len-renTms; sizeᵉ-pos;
                                                      sizeᵗ-pos; ∧-true)
open import Verify-Budget-Sufficient.Caps using
  (foldStep-infl; iterFold-mono-count)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over (see below, ~6307).  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (4≤iterFold; k≤iterFold;
                                                             len≤sizeᵗˢ; max3-suc; node1;
                                                             node2; one-fits; powʳ1;
                                                             module Red; slotsCaps?;
                                                             slotsCaps?-lookup; SlotWid; Sub;
                                                             Sub-[]; Sub-∷; thr; thr3;
                                                             two-folds; T≤TT; Wᴱ; Wᴱ-mono;
                                                             Wᴸ; Wᴸ-mono; Wᵀ; Wᵀ-mono)
open import Decide using (T-to; ifNeq; ite≤)

------------------------------------------------------------------
-- ONE foldStep PER SYNTAX NODE, TWO AT scanᵉ.
------------------------------------------------------------------

module _ (S M : ℕ) (hS : 2 ≤ S) (hM : 1 ≤ M) where

  mutual
    widᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ t) → Wᴱ sl (iterFold S (sizeᵉ e) M) e
    widᵉ {n = n} sl hI (input i) =
      ≤-trans (proj₁ (hI i)) INFL , ≤-trans (proj₁ (proj₂ (hI i))) INFL
      , (λ k → z≤n) , (λ k → z≤n)
      where INFL = foldStep-infl S M hS
    widᵉ {n = n} sl hI emptyᵉ =
      ≤-trans (≤-reflexive (Red.oW-empty n sl)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-empty n sl)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵉ {n = n} sl hI (varᵉ x) =
      ≤-trans (≤-reflexive (Red.oW-var n sl x)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-var n sl x)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵉ {n = n} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} sl hI (deferᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-defer n sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-defer n sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    widᵉ {n = n} sl hI (ofᵉ ts) =
      ≤-trans (≤-reflexive (Red.oW-of n sl ts))
              (up (≤-trans (len≤sizeᵗˢ ts) (k≤iterFold S (sizeᵗˢ ts) M hS)))
      , ≤-trans (≤-reflexive (Red.iW-of n sl ts)) (up (proj₁ IH))
      , (λ k → z≤n) , (λ k → up (proj₂ IH k))
      where
      IH = widᵗˢ sl hI ts
      up : ∀ {x} → x ≤ iterFold S (sizeᵗˢ ts) M → x ≤ iterFold S (suc (sizeᵗˢ ts)) M
      up h = ≤-trans (≤-trans h (foldStep-infl S _ hS))
                     (node1 S M (sizeᵗˢ ts) (suc (sizeᵗˢ ts)) hS ≤-refl)
    widᵉ {n = n} sl hI (mapᵉ f e) =
      ≤-trans (≤-reflexive (Red.oW-map n sl f e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-map n sl f e)) (FIT INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → FIT (PMI k))
      where
      m   = sizeᵗ f ⊔ sizeᵉ e
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM (≤-trans (sizeᵗ-pos f) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ f) (sizeᵉ e)))
              (widᵗ sl hI f)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ f) (sizeᵉ e)))
              (widᵉ sl hI e)
      step = node1 S M m (suc (sizeᵗ f + sizeᵉ e)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ f) (sizeᵉ e)) (m≤n+m (sizeᵉ e) (sizeᵗ f))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ f + sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc (sizeᵗ f + sizeᵉ e)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      INN : innWᵗ n sl f + (pmIᵗ n sl 0 f ⊔ 1) * innWᵉ n sl e ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (proj₁ IHf) (T≤TT Tb 1≤T))
                     (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T) (proj₁ (proj₂ IHe)))
      PMI : ∀ k → pmIᵗ n sl (suc k) f + (pmIᵗ n sl 0 f ⊔ 1) * pmIᵉ n sl k e
                    ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (proj₂ (proj₂ IHf) (suc k)) (T≤TT Tb 1≤T))
                       (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T)
                                 (proj₂ (proj₂ (proj₂ IHe)) k))
    widᵉ {n = n} sl hI (takeᵉ c e) =
      ≤-trans (≤-reflexive (Red.oW-take n sl c e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-take n sl c e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      Tb    = iterFold S (sizeᵉ e) M
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵗ c + sizeᵉ e)) hS
               (s≤s (m≤n+m (sizeᵉ e) (sizeᵗ c)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c + sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵉ {n = n} sl hI (mergeAllᵉ lim e) =
      allClause sl hI e (mergeAllᵉ lim e) (Red.oW-mergeAll n sl lim e) (Red.iW-mergeAll n sl lim e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (switchAllᵉ e) =
      allClause sl hI e (switchAllᵉ e) (Red.oW-switch n sl e) (Red.iW-switch n sl e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (exhaustAllᵉ e) =
      allClause sl hI e (exhaustAllᵉ e) (Red.oW-exhaust n sl e) (Red.iW-exhaust n sl e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (μᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-μ n sl e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-μ n sl e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      Tb    = iterFold S (sizeᵉ e) M
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵉ {n = n} sl hI (scanᵉ f z e) =
      ≤-trans (≤-reflexive (Red.oW-scan n sl f z e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-scan n sl f z e)) (FIT2 INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k)) , (λ k → FIT2 (PMI k))
      where
      m   = sizeᵗ f ⊔ sizeᵗ z ⊔ sizeᵉ e
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos f) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e)))) (widᵗ sl hI f)
      IHz = Wᵀ-mono sl z (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e)))) (widᵗ sl hI z)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ f ⊔ sizeᵗ z) (sizeᵉ e))) (widᵉ sl hI e)
      Σ3    = sizeᵗ f + sizeᵗ z + sizeᵉ e
      step2 = node2 S M m (suc Σ3) hS
                (s≤s (max3-suc (sizeᵗ f) (sizeᵗ z) (sizeᵉ e)
                        (sizeᵗ-pos f) (sizeᵗ-pos z) (sizeᵉ-pos e)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc Σ3) M
      up0 h = ≤-trans (≤-trans (≤-trans h (foldStep-infl S Tb hS))
                               (foldStep-infl S (foldStep S Tb) hS)) step2
      FIT2 : ∀ {x} → x ≤ Tb ^ Tb * (3 * Tb + 1) → x ≤ iterFold S (suc Σ3) M
      FIT2 h = ≤-trans (≤-trans h (two-folds S Tb hS hT)) step2
      base≤ : pmIᵗ n sl 0 f ⊔ 1 ≤ Tb
      base≤ = ⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T
      pw : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e ≤ Tb ^ Tb
      pw = ≤-trans (^-monoˡ-≤ (outWᵉ n sl e) base≤) (powʳ1 Tb 1≤T (proj₁ IHe))
      INN : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
              * (innWᵗ n sl f + innWᵗ n sl z + innWᵉ n sl e + 1)
            ≤ Tb ^ Tb * (3 * Tb + 1)
      INN = *-mono-≤ pw
              (≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ (proj₁ IHf) (proj₁ IHz))
                                           (proj₁ (proj₂ IHe)))
                                 (≤-refl {1}))
                       (≤-reflexive (thr Tb)))
      PMI : ∀ k → (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
                    * (pmIᵗ n sl (suc k) f + pmIᵗ n sl k z + pmIᵉ n sl k e)
                  ≤ Tb ^ Tb * (3 * Tb + 1)
      PMI k = *-mono-≤ pw
                (≤-trans (+-mono-≤ (+-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                                             (proj₂ (proj₂ IHz) k))
                                   (proj₂ (proj₂ (proj₂ IHe)) k))
                         (≤-trans (≤-reflexive (thr3 Tb)) (m≤m+n (3 * Tb) 1)))

    -- the four *All nodes, which share a clause: the reduction
    -- equations come in as arguments so the four differ only in which
    -- constructor they name
    allClause : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ (obs t)) (E : Exp Γ Δᵍ Δ Θ t) →
      outWᵉ n sl E ≡ outWᵉ n sl e * innWᵉ n sl e →
      innWᵉ n sl E ≡ innWᵉ n sl e →
      ((k : ℕ) → pmOᵉ n sl k E
                   ≡ outWᵉ n sl e * pmIᵉ n sl k e + pmOᵉ n sl k e * innWᵉ n sl e) →
      ((k : ℕ) → pmIᵉ n sl k E ≡ pmIᵉ n sl k e) →
      Wᴱ sl (iterFold S (suc (sizeᵉ e)) M) E
    allClause {n = n} sl hI e E eo ei ep eq =
      ≤-trans (≤-reflexive eo)
              (FIT (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                            (m≤m+n (Tb * Tb) (Tb * Tb))))
      , ≤-trans (≤-reflexive ei) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → ≤-trans (≤-reflexive (ep k))
                 (FIT (+-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                                (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                          (proj₁ (proj₂ IHe))))))
      , (λ k → ≤-trans (≤-reflexive (eq k)) (up0 (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      Tb    = iterFold S (sizeᵉ e) M
      hT   = 4≤iterFold S M (sizeᵉ e) hS hM (sizeᵉ-pos e)
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step

    widᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (tm : Tm Γ Δᵍ Δ Θ t) → Wᵀ sl (iterFold S (sizeᵗ tm) M) tm
    widᵗ sl hI (varᵗ x) =
      z≤n , (λ k → z≤n)
      , (λ k → ite≤ _ (≤-trans (≤ᵇ⇒≤ 1 4 tt) (4≤iterFold S M 1 hS hM ≤-refl)))
    widᵗ sl hI unit̂        = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (bool̂ _)    = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (nat̂ _)     = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (primᵗ _ a) = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (pairᵗ a b) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      m   = sizeᵗ a ⊔ sizeᵗ b
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI a)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI b)
      step = node1 S M m (suc (sizeᵗ a + sizeᵗ b)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ a) (sizeᵗ b)) (m≤n+m (sizeᵗ b) (sizeᵗ a))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ a + sizeᵗ b)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵗ sl hI (fstᵗ p) = unary sl hI p
    widᵗ sl hI (sndᵗ p) = unary sl hI p
    widᵗ sl hI (inlᵗ p) = unary sl hI p
    widᵗ sl hI (inrᵗ p) = unary sl hI p
    widᵗ sl hI (strmᵗ e) =
      up0 (proj₁ IHe) , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      where
      Tb    = iterFold S (sizeᵉ e) M
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵗ sl hI (ifᵗ c a b) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      m   = sizeᵗ a ⊔ sizeᵗ b
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI a)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI b)
      step = node1 S M m (suc (sizeᵗ c + sizeᵗ a + sizeᵗ b)) hS
               (s≤s (⊔-lub (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                    (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))
                           (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c + sizeᵗ a + sizeᵗ b)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵗ {n = n} sl hI (caseᵗ s l r) =
      FIT INN , (λ k → FIT (PMO k)) , (λ k → FIT (PMI k))
      where
      m   = sizeᵗ s ⊔ sizeᵗ l ⊔ sizeᵗ r
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos s) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHs = Wᵀ-mono sl s (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ s) (sizeᵗ l)) (m≤m⊔n _ (sizeᵗ r)))) (widᵗ sl hI s)
      IHl = Wᵀ-mono sl l (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ s) (sizeᵗ l)) (m≤m⊔n _ (sizeᵗ r)))) (widᵗ sl hI l)
      IHr = Wᵀ-mono sl r (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ s ⊔ sizeᵗ l) (sizeᵗ r))) (widᵗ sl hI r)
      step = node1 S M m (suc (sizeᵗ s + sizeᵗ l + sizeᵗ r)) hS
               (s≤s (⊔-lub (⊔-lub (≤-trans (m≤m+n (sizeᵗ s) (sizeᵗ l))
                                           (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r)))
                                  (≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ s))
                                           (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))))
                           (m≤n+m (sizeᵗ r) (sizeᵗ s + sizeᵗ l))))
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb →
            x ≤ iterFold S (suc (sizeᵗ s + sizeᵗ l + sizeᵗ r)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      C≤ : pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1 ≤ Tb
      C≤ = ⊔-lub (⊔-lub (proj₂ (proj₂ IHl) 0) (proj₂ (proj₂ IHr) 0)) 1≤T
      INN : (innWᵗ n sl l ⊔ innWᵗ n sl r)
              + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * innWᵗ n sl s
            ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (⊔-lub (proj₁ IHl) (proj₁ IHr)) (T≤TT Tb 1≤T))
                     (*-mono-≤ C≤ (proj₁ IHs))
      PMO : ∀ k → pmOᵗ n sl (suc k) l ⊔ pmOᵗ n sl (suc k) r
                    ⊔ (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmOᵗ n sl k s
                  ≤ Tb * Tb + Tb * Tb
      PMO k = ⊔-lub (≤-trans (⊔-lub (proj₁ (proj₂ IHl) (suc k))
                                    (proj₁ (proj₂ IHr) (suc k)))
                             (≤-trans (T≤TT Tb 1≤T) (m≤m+n _ _)))
                    (≤-trans (*-mono-≤ C≤ (proj₁ (proj₂ IHs) k)) (m≤m+n _ _))
      PMI : ∀ k → (pmIᵗ n sl (suc k) l ⊔ pmIᵗ n sl (suc k) r)
                    + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmIᵗ n sl k s
                  ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (⊔-lub (proj₂ (proj₂ IHl) (suc k))
                                       (proj₂ (proj₂ IHr) (suc k)))
                                (T≤TT Tb 1≤T))
                       (*-mono-≤ C≤ (proj₂ (proj₂ IHs) k))

    unary : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (p : Tm Γ Δᵍ Δ Θ t) →
      (innWᵗ n sl p ≤ iterFold S (suc (sizeᵗ p)) M)
      × ((k : ℕ) → pmOᵗ n sl k p ≤ iterFold S (suc (sizeᵗ p)) M)
      × ((k : ℕ) → pmIᵗ n sl k p ≤ iterFold S (suc (sizeᵗ p)) M)
    unary sl hI p =
      up0 (proj₁ IH) , (λ k → up0 (proj₁ (proj₂ IH) k))
      , (λ k → up0 (proj₂ (proj₂ IH) k))
      where
      Tb    = iterFold S (sizeᵗ p) M
      IH   = widᵗ sl hI p
      step = node1 S M (sizeᵗ p) (suc (sizeᵗ p)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ p)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step

    widᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (ts : List (Tm Γ Δᵍ Δ Θ t)) → Wᴸ sl (iterFold S (sizeᵗˢ ts) M) ts
    widᵗˢ sl hI []       = z≤n , (λ k → z≤n)
    widᵗˢ sl hI (y ∷ ys) =
      ⊔-lub (proj₁ IHy) (proj₁ IHys)
      , (λ k → ⊔-lub (proj₂ (proj₂ IHy) k) (proj₂ IHys k))
      where
      IHy  = Wᵀ-mono sl y (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
               (widᵗ sl hI y)
      IHys = Wᴸ-mono sl ys (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))
               (widᵗˢ sl hI ys)

  -- THE PARKED HALF.  dW is a plain ⊔-collect with one exception —
  -- `dWᵉ (deferᵉ e) = outWᵉ e ⊔ dWᵉ e`, the clause the family exists for
  -- — so it costs no fold anywhere and reads the delivered half above
  -- at the defer
  mutual
    wdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ t) → dWᵉ n sl e ≤ iterFold S (sizeᵉ e) M
    wdᵉ sl hI (input i) = ≤-trans (proj₂ (proj₂ (hI i))) (foldStep-infl S M hS)
    wdᵉ sl hI emptyᵉ    = z≤n
    wdᵉ sl hI (varᵉ x)  = z≤n
    wdᵉ sl hI (ofᵉ ts)  =
      ≤-trans (wdᵗˢ sl hI ts)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗˢ ts) (suc (sizeᵗˢ ts)) hS ≤-refl))
    wdᵉ sl hI (deferᵉ e) =
      ≤-trans (⊔-lub (proj₁ (widᵉ sl hI e)) (wdᵉ sl hI e))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl))
    wdᵉ sl hI (mapᵉ f e) =
      ≤-trans (⊔-lub (≤-trans (wdᵗ sl hI f) (mono (m≤m⊔n (sizeᵗ f) (sizeᵉ e))))
                     (≤-trans (wdᵉ sl hI e) (mono (m≤n⊔m (sizeᵗ f) (sizeᵉ e)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ f ⊔ sizeᵉ e) (suc (sizeᵗ f + sizeᵉ e)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ f) (sizeᵉ e))
                                     (m≤n+m (sizeᵉ e) (sizeᵗ f))))))
      where mono = iterFold-mono-count S M hS
    wdᵉ sl hI (takeᵉ c e) =
      ≤-trans (⊔-lub (≤-trans (wdᵗ sl hI c) (mono (m≤m⊔n (sizeᵗ c) (sizeᵉ e))))
                     (≤-trans (wdᵉ sl hI e) (mono (m≤n⊔m (sizeᵗ c) (sizeᵉ e)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ c ⊔ sizeᵉ e) (suc (sizeᵗ c + sizeᵉ e)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ c) (sizeᵉ e))
                                     (m≤n+m (sizeᵉ e) (sizeᵗ c))))))
      where mono = iterFold-mono-count S M hS
    wdᵉ sl hI (scanᵉ f z e) =
      ≤-trans (⊔-lub (⊔-lub (≤-trans (wdᵗ sl hI f) (mono up-f))
                            (≤-trans (wdᵗ sl hI z) (mono up-z)))
                     (≤-trans (wdᵉ sl hI e) (mono up-e)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (sizeᵗ f + sizeᵗ z + sizeᵉ e)) hS
                         (≤-trans (max3-suc (sizeᵗ f) (sizeᵗ z) (sizeᵉ e)
                                     (sizeᵗ-pos f) (sizeᵗ-pos z) (sizeᵉ-pos e))
                                  (n≤1+n _))))
      where
      m    = sizeᵗ f ⊔ sizeᵗ z ⊔ sizeᵉ e
      mono = iterFold-mono-count S M hS
      up-f = ≤-trans (m≤m⊔n (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e))
      up-z = ≤-trans (m≤n⊔m (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e))
      up-e = m≤n⊔m (sizeᵗ f ⊔ sizeᵗ z) (sizeᵉ e)
    wdᵉ sl hI (mergeAllᵉ _ e)   = pass sl hI e
    wdᵉ sl hI (switchAllᵉ e)  = pass sl hI e
    wdᵉ sl hI (exhaustAllᵉ e) = pass sl hI e
    wdᵉ sl hI (μᵉ e)          = pass sl hI e

    pass : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ t) → dWᵉ n sl e ≤ iterFold S (suc (sizeᵉ e)) M
    pass sl hI e =
      ≤-trans (wdᵉ sl hI e)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl))

    wdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (tm : Tm Γ Δᵍ Δ Θ t) → dWᵗ n sl tm ≤ iterFold S (sizeᵗ tm) M
    wdᵗ sl hI (varᵗ x)  = z≤n
    wdᵗ sl hI unit̂      = z≤n
    wdᵗ sl hI (bool̂ _)  = z≤n
    wdᵗ sl hI (nat̂ _)   = z≤n
    wdᵗ sl hI (strmᵗ e) = pass sl hI e
    wdᵗ sl hI (fstᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (sndᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (inlᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (inrᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (primᵗ _ p) = passᵗ sl hI p
    wdᵗ sl hI (pairᵗ a b) =
      ≤-trans (⊔-lub (≤-trans (wdᵗ sl hI a) (mono (m≤m⊔n (sizeᵗ a) (sizeᵗ b))))
                     (≤-trans (wdᵗ sl hI b) (mono (m≤n⊔m (sizeᵗ a) (sizeᵗ b)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ a ⊔ sizeᵗ b) (suc (sizeᵗ a + sizeᵗ b)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ a) (sizeᵗ b))
                                     (m≤n+m (sizeᵗ b) (sizeᵗ a))))))
      where mono = iterFold-mono-count S M hS
    wdᵗ sl hI (caseᵗ s l r) = three sl hI s l r
    wdᵗ sl hI (ifᵗ c a b)   = three sl hI c a b

    passᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (p : Tm Γ Δᵍ Δ Θ t) → dWᵗ n sl p ≤ iterFold S (suc (sizeᵗ p)) M
    passᵗ sl hI p =
      ≤-trans (wdᵗ sl hI p)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ p) (suc (sizeᵗ p)) hS ≤-refl))

    three : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ₁ Θ₂ Θ₃ t u v} (sl : Slots Γ) → SlotWid sl M →
      (a : Tm Γ Δᵍ Δ Θ₁ t) (b : Tm Γ Δᵍ Δ Θ₂ u) (c : Tm Γ Δᵍ Δ Θ₃ v) →
      dWᵗ n sl a ⊔ dWᵗ n sl b ⊔ dWᵗ n sl c
        ≤ iterFold S (suc (sizeᵗ a + sizeᵗ b + sizeᵗ c)) M
    three sl hI a b c =
      ≤-trans (⊔-lub (⊔-lub (≤-trans (wdᵗ sl hI a) (mono up-a))
                            (≤-trans (wdᵗ sl hI b) (mono up-b)))
                     (≤-trans (wdᵗ sl hI c) (mono up-c)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (sizeᵗ a + sizeᵗ b + sizeᵗ c)) hS
                         (≤-trans (max3-suc (sizeᵗ a) (sizeᵗ b) (sizeᵗ c)
                                     (sizeᵗ-pos a) (sizeᵗ-pos b) (sizeᵗ-pos c))
                                  (n≤1+n _))))
      where
      m    = sizeᵗ a ⊔ sizeᵗ b ⊔ sizeᵗ c
      mono = iterFold-mono-count S M hS
      up-a = ≤-trans (m≤m⊔n (sizeᵗ a) (sizeᵗ b)) (m≤m⊔n _ (sizeᵗ c))
      up-b = ≤-trans (m≤n⊔m (sizeᵗ a) (sizeᵗ b)) (m≤m⊔n _ (sizeᵗ c))
      up-c = m≤n⊔m (sizeᵗ a ⊔ sizeᵗ b) (sizeᵗ c)

    wdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (ts : List (Tm Γ Δᵍ Δ Θ t)) → dWᵗˢ n sl ts ≤ iterFold S (sizeᵗˢ ts) M
    wdᵗˢ sl hI []       = z≤n
    wdᵗˢ sl hI (y ∷ ys) =
      ⊔-lub (≤-trans (wdᵗ sl hI y)
                     (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y) (sizeᵗˢ ys))))
            (≤-trans (wdᵗˢ sl hI ys)
                     (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys) (sizeᵗ y))))

-- THE LEMMA, assembled
wid-iterFold : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M → (e : Exp Γ Δᵍ Δ Θ t) →
  (outWᵉ n sl e ≤ iterFold S (sizeᵉ e) M)
  × (innWᵉ n sl e ≤ iterFold S (sizeᵉ e) M)
  × (dWᵉ n sl e ≤ iterFold S (sizeᵉ e) M)
wid-iterFold S M hS hM sl hI e =
  proj₁ (widᵉ S M hS hM sl hI e)
  , proj₁ (proj₂ (widᵉ S M hS hM sl hI e))
  , wdᵉ S M hS hM sl hI e

------------------------------------------------------------------
-- AND THE TELESCOPE SUPPLIES THE LEAF, at ONE above the width cap.
-- The shared branch is slotCaps?'s pW and innW conjuncts read one
-- CONNECT down — `outWᵉ (suc j) sl (input i)` is `outWᵉ j sl d`, one
-- fuel below what the conjunct states — and the scripted branch is the
-- constant 1 that outWᵉ / innWᵉ hand back for a data payload, which is
-- what the `suc` pays for.
------------------------------------------------------------------

-- THE MEASURES ARE MONOTONE IN THE SLOT FUEL AND ANTITONE IN THE
-- VISITED SET, and it is ONE induction because only the `input` clauses
-- read either.  More fuel means a deeper descent into the slot
-- telescope; a bigger visited set means a shorter one, since a revisit
-- hands back 0.  Every other clause is a ⊔, a sum, a product or an
-- exponential of the children, all monotone in all of them.
--
-- BOTH AXES AT ONCE is what the leaf needs.  The slot side condition is
-- stated at the ENTRY form (`vs = []`, since capsOK? bounds a STORED
-- value and a stored value carries no record of which connect put it
-- there), while the width induction meets an `input` leaf one CONNECT
-- below it AND with that slot's own index already marked.  The bridge
-- is therefore `q ≤ q′` together with `Sub vs′ vs`, and `Sub [] _` is
-- vacuous — which is exactly the instance slotsCaps?-slotWid uses.
module _ {n} {Γ : Ctx n} (sl : Slots Γ) where

  MonoE : ∀ {Δᵍ Δ Θ t} → ℕ → List (Fin n) → ℕ → List (Fin n) → Exp Γ Δᵍ Δ Θ t → Set
  MonoE q vs q′ vs′ e = (outWⱽ q vs sl e ≤ outWⱽ q′ vs′ sl e)
               × (innWⱽ q vs sl e ≤ innWⱽ q′ vs′ sl e)
               × ((k : ℕ) → pmOⱽ q vs sl k e ≤ pmOⱽ q′ vs′ sl k e)
               × ((k : ℕ) → pmIⱽ q vs sl k e ≤ pmIⱽ q′ vs′ sl k e)

  MonoT : ∀ {Δᵍ Δ Θ t} → ℕ → List (Fin n) → ℕ → List (Fin n) → Tm Γ Δᵍ Δ Θ t → Set
  MonoT q vs q′ vs′ tm = (innWᵗⱽ q vs sl tm ≤ innWᵗⱽ q′ vs′ sl tm)
                × ((k : ℕ) → pmOᵗⱽ q vs sl k tm ≤ pmOᵗⱽ q′ vs′ sl k tm)
                × ((k : ℕ) → pmIᵗⱽ q vs sl k tm ≤ pmIᵗⱽ q′ vs′ sl k tm)

  MonoL : ∀ {Δᵍ Δ Θ t} → ℕ → List (Fin n) → ℕ → List (Fin n) → List (Tm Γ Δᵍ Δ Θ t) → Set
  MonoL q vs q′ vs′ ts = (innWᵗˢⱽ q vs sl ts ≤ innWᵗˢⱽ q′ vs′ sl ts)
                × ((k : ℕ) → pmIᵗˢⱽ q vs sl k ts ≤ pmIᵗˢⱽ q′ vs′ sl k ts)

  mutual
    monoᵉ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → MonoE q vs q′ vs′ e
    monoᵉ q {q′} le hv (ofᵉ ts) =
      ≤-reflexive (trans (Red.oW-of q sl ts) (sym (Red.oW-of q′ sl ts)))
      , ≤-trans (≤-reflexive (Red.iW-of q sl ts))
                (≤-trans (proj₁ (monoᵗˢ q le hv ts))
                         (≤-reflexive (sym (Red.iW-of q′ sl ts))))
      , (λ k → z≤n)
      , (λ k → proj₂ (monoᵗˢ q le hv ts) k)
    monoᵉ q {q′} le hv emptyᵉ =
      ≤-trans (≤-reflexive (Red.oW-empty q sl)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-empty q sl)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ q {q′} le hv (varᵉ x) =
      ≤-trans (≤-reflexive (Red.oW-var q sl x)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-var q sl x)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ q {q′} le hv {Δᵍ} {Δ} {Θ} (deferᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-defer q sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-defer q sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ q {q′} le hv (mapᵉ f e) =
      ≤-trans (≤-reflexive (Red.oW-map q sl f e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-map q′ sl f e))))
      , ≤-trans (≤-reflexive (Red.iW-map q sl f e))
                (≤-trans (+-mono-≤ (proj₁ IHf)
                            (*-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHf) 0) ≤-refl)
                                      (proj₁ (proj₂ IHe))))
                         (≤-reflexive (sym (Red.iW-map q′ sl f e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → +-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                 (*-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHf) 0) ≤-refl)
                           (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      IHf = monoᵗ q le hv f
      IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (takeᵉ c e) =
      ≤-trans (≤-reflexive (Red.oW-take q sl c e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-take q′ sl c e))))
      , ≤-trans (≤-reflexive (Red.iW-take q sl c e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-take q′ sl c e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le {vs} {vs′} hv (scanᵉ f z e) =
      ≤-trans (≤-reflexive (Red.oW-scan q sl f z e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-scan q′ sl f z e))))
      , ≤-trans (≤-reflexive (Red.iW-scan q sl f z e))
                (≤-trans (*-mono-≤ POW
                            (+-mono-≤ (+-mono-≤ (+-mono-≤ (proj₁ IHf) (proj₁ IHz))
                                                (proj₁ (proj₂ IHe)))
                                      ≤-refl))
                         (≤-reflexive (sym (Red.iW-scan q′ sl f z e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → *-mono-≤ POW
                 (+-mono-≤ (+-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                                     (proj₂ (proj₂ IHz) k))
                           (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      IHf = monoᵗ q le hv f
      IHz = monoᵗ q le hv z
      IHe = monoᵉ q le hv e
      POW : (pmIᵗⱽ q vs sl 0 f ⊔ 1) ^ outWⱽ q vs sl e
              ≤ (pmIᵗⱽ q′ vs′ sl 0 f ⊔ 1) ^ outWⱽ q′ vs′ sl e
      POW = ≤-trans (^-monoˡ-≤ (outWⱽ q vs sl e)
                      (⊔-mono-≤ (proj₂ (proj₂ IHf) 0) ≤-refl))
                    (powʳ1 (pmIᵗⱽ q′ vs′ sl 0 f ⊔ 1)
                           (m≤n⊔m (pmIᵗⱽ q′ vs′ sl 0 f) 1) (proj₁ IHe))
    monoᵉ q {q′} le hv (mergeAllᵉ lim e) =
      ≤-trans (≤-reflexive (Red.oW-mergeAll q sl lim e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-mergeAll q′ sl lim e))))
      , ≤-trans (≤-reflexive (Red.iW-mergeAll q sl lim e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-mergeAll q′ sl lim e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (switchAllᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-switch q sl e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-switch q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-switch q sl e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-switch q′ sl e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (exhaustAllᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-exhaust q sl e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-exhaust q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-exhaust q sl e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-exhaust q′ sl e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (μᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-μ q sl e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-μ q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-μ q sl e))
                (≤-trans (proj₁ (proj₂ IHe)) (≤-reflexive (sym (Red.iW-μ q′ sl e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    -- THE ONLY CLAUSE THAT READS THE FUEL, and the only place the
    -- induction descends on it rather than on the syntax
    monoᵉ zero {q′} le hv (input i) = z≤n , z≤n , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ (suc q) {suc q′} (s≤s le) {vs} {vs′} hv (input i) with i ∈ᵇ vs′ in eq′
    -- the RIGHT side has already entered this slot, so the left has too
    ... | true rewrite hv i eq′ = z≤n , z≤n , (λ k → z≤n) , (λ k → z≤n)
    ... | false with i ∈ᵇ vs
    -- only the LEFT has: a revisit delivers nothing, and 0 bounds all
    ...   | true  = z≤n , z≤n , (λ k → z≤n) , (λ k → z≤n)
    ...   | false with sl i
    ...     | scripted _ = ≤-refl , ≤-refl , (λ k → z≤n) , (λ k → z≤n)
    ...     | shared d   = proj₁ IH , proj₁ (proj₂ IH) , (λ k → z≤n) , (λ k → z≤n)
      where IH = monoᵉ q le {i ∷ vs} {i ∷ vs′} (Sub-∷ i {vs′} {vs} hv) d

    monoᵗ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → MonoT q vs q′ vs′ tm
    monoᵗ q {q′} le hv (varᵗ x)   = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv unit̂       = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (bool̂ _)   = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (nat̂ _)    = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (primᵗ _ a) = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (pairᵗ a b) =
      ⊔-mono-≤ (proj₁ IHa) (proj₁ IHb)
      , (λ k → ⊔-mono-≤ (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k))
      , (λ k → ⊔-mono-≤ (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k))
      where
      IHa = monoᵗ q le hv a
      IHb = monoᵗ q le hv b
    monoᵗ q {q′} le hv (fstᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (sndᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (inlᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (inrᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (ifᵗ c a b) =
      ⊔-mono-≤ (proj₁ IHa) (proj₁ IHb)
      , (λ k → ⊔-mono-≤ (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k))
      , (λ k → ⊔-mono-≤ (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k))
      where
      IHa = monoᵗ q le hv a
      IHb = monoᵗ q le hv b
    monoᵗ q {q′} le hv (strmᵗ e) =
      proj₁ IHe , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵗ q {q′} le hv (caseᵗ s l r) =
      +-mono-≤ (⊔-mono-≤ (proj₁ IHl) (proj₁ IHr)) (*-mono-≤ C≤ (proj₁ IHs))
      , (λ k → ⊔-mono-≤ (⊔-mono-≤ (proj₁ (proj₂ IHl) (suc k))
                                  (proj₁ (proj₂ IHr) (suc k)))
                        (*-mono-≤ C≤ (proj₁ (proj₂ IHs) k)))
      , (λ k → +-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHl) (suc k))
                                  (proj₂ (proj₂ IHr) (suc k)))
                        (*-mono-≤ C≤ (proj₂ (proj₂ IHs) k)))
      where
      IHs = monoᵗ q le hv s
      IHl = monoᵗ q le hv l
      IHr = monoᵗ q le hv r
      C≤ = ⊔-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHl) 0) (proj₂ (proj₂ IHr) 0)) ≤-refl

    monoᵗˢ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → MonoL q vs q′ vs′ ts
    monoᵗˢ q {q′} le hv []       = ≤-refl , (λ k → ≤-refl)
    monoᵗˢ q {q′} le hv (y ∷ ys) =
      ⊔-mono-≤ (proj₁ IHy) (proj₁ IHys)
      , (λ k → ⊔-mono-≤ (proj₂ (proj₂ IHy) k) (proj₂ IHys k))
      where
      IHy  = monoᵗ q le hv y
      IHys = monoᵗˢ q le hv ys

  -- and the parked half, which reads the delivered one at a defer
  mutual
    monoᴰᵉ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → dWⱽ q vs sl e ≤ dWⱽ q′ vs′ sl e
    monoᴰᵉ q le hv (ofᵉ ts)        = monoᴰᵗˢ q le hv ts
    monoᴰᵉ q le hv emptyᵉ          = z≤n
    monoᴰᵉ q le hv (varᵉ x)        = z≤n
    monoᴰᵉ q le hv (mapᵉ f e)      = ⊔-mono-≤ (monoᴰᵗ q le hv f) (monoᴰᵉ q le hv e)
    monoᴰᵉ q le hv (takeᵉ c e)     = ⊔-mono-≤ (monoᴰᵗ q le hv c) (monoᴰᵉ q le hv e)
    monoᴰᵉ q le hv (scanᵉ f z e)   =
      ⊔-mono-≤ (⊔-mono-≤ (monoᴰᵗ q le hv f) (monoᴰᵗ q le hv z)) (monoᴰᵉ q le hv e)
    monoᴰᵉ q le hv (mergeAllᵉ _ e)   = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (switchAllᵉ e)  = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (exhaustAllᵉ e) = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (μᵉ e)          = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (deferᵉ e)      =
      ⊔-mono-≤ (proj₁ (monoᵉ q le hv e)) (monoᴰᵉ q le hv e)
    monoᴰᵉ zero    le hv (input i) = z≤n
    monoᴰᵉ (suc q) (s≤s le) {vs} {vs′} hv (input i) with i ∈ᵇ vs′ in eq′
    ... | true rewrite hv i eq′ = z≤n
    ... | false with i ∈ᵇ vs
    ...   | true  = z≤n
    ...   | false with sl i
    ...     | scripted _ = z≤n
    ...     | shared d   = monoᴰᵉ q le {i ∷ vs} {i ∷ vs′} (Sub-∷ i {vs′} {vs} hv) d

    monoᴰᵗ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → dWᵗⱽ q vs sl tm ≤ dWᵗⱽ q′ vs′ sl tm
    monoᴰᵗ q le hv (varᵗ x)     = z≤n
    monoᴰᵗ q le hv unit̂         = z≤n
    monoᴰᵗ q le hv (bool̂ _)     = z≤n
    monoᴰᵗ q le hv (nat̂ _)      = z≤n
    monoᴰᵗ q le hv (pairᵗ a b)  = ⊔-mono-≤ (monoᴰᵗ q le hv a) (monoᴰᵗ q le hv b)
    monoᴰᵗ q le hv (fstᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (sndᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (inlᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (inrᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (primᵗ _ a)  = monoᴰᵗ q le hv a
    monoᴰᵗ q le hv (strmᵗ e)    = monoᴰᵉ q le hv e
    monoᴰᵗ q le hv (caseᵗ s l r) =
      ⊔-mono-≤ (⊔-mono-≤ (monoᴰᵗ q le hv s) (monoᴰᵗ q le hv l)) (monoᴰᵗ q le hv r)
    monoᴰᵗ q le hv (ifᵗ c a b) =
      ⊔-mono-≤ (⊔-mono-≤ (monoᴰᵗ q le hv c) (monoᴰᵗ q le hv a)) (monoᴰᵗ q le hv b)

    monoᴰᵗˢ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → dWᵗˢⱽ q vs sl ts ≤ dWᵗˢⱽ q′ vs′ sl ts
    monoᴰᵗˢ q le hv []       = z≤n
    monoᴰᵗˢ q le hv (y ∷ ys) = ⊔-mono-≤ (monoᴰᵗ q le hv y) (monoᴰᵗˢ q le hv ys)

------------------------------------------------------------------
-- THE LEAF, off the slot side condition.
------------------------------------------------------------------

slotsCaps?-slotWid : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) →
  slotsCaps? B W sl ≡ true → SlotWid sl (suc W)
slotsCaps?-slotWid {n = suc m} B W sl h i
  with sl i | slotsCaps?-lookup B W sl i h
... | scripted _ | _  = s≤s z≤n , s≤s z≤n , z≤n
... | shared d   | sd =
  ≤-trans (≤-trans (proj₁ (monoᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d))
                   (≤-trans (m≤m⊔n (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw))
          (n≤1+n W)
  , ≤-trans (≤-trans (proj₁ (proj₂ (monoᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d))) iw)
            (n≤1+n W)
  , ≤-trans (≤-trans (monoᴰᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d)
                     (≤-trans (m≤n⊔m (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw))
            (n≤1+n W)
  where
  split₁ = ∧-true (sizeᵉ d ≤ᵇ B)
             ((pWᵉ (suc m) sl d ≤ᵇ W) ∧ (innWᵉ (suc m) sl d ≤ᵇ W)) sd
  split₂ = ∧-true (pWᵉ (suc m) sl d ≤ᵇ W) (innWᵉ (suc m) sl d ≤ᵇ W)
             (proj₂ split₁)
  pw : pWᵉ (suc m) sl d ≤ W
  pw = ≤ᵇ⇒≤ (pWᵉ (suc m) sl d) W (T-to (proj₁ split₂))
  iw : innWᵉ (suc m) sl d ≤ W
  iw = ≤ᵇ⇒≤ (innWᵉ (suc m) sl d) W (T-to (proj₂ split₂))

------------------------------------------------------------------
-- THE WIDTH FACE OF THE EVALUATOR — the piece that makes every
-- receipt in the cluster SYNTAX-COUNTED.
--
-- The five members all have to bound the width of a value the
-- evaluator just built.  Reading that width off the value's SIZE
-- (which is what the first landing did) costs a fold count equal to
-- that size — iterFold is a TOWER in its count, so nothing smaller
-- dominates it — and the only bound on an evaluated value's size is
-- the RUNNING size cap.  That is where the old `+ suc K` came from,
-- and it made an instant's total j self-referential.
--
-- The route that is syntax-counted reads the width off the WIDTH: an
-- evaluated value's obs components are the term's own obs subterms
-- with the environment plugged in, so their widths come from the
-- term's syntax with the plugged widths as the SEED — one foldStep
-- per syntax node of the TERM, exactly wid-iterFold's count, with the
-- environment entering the seed and never the count.
--
-- FOUR PIECES, all ground: the plug's own measures (a reified value,
-- weakened in — renaming invariance plus the two slopes vanishing
-- because it is Θ-closed), wid-subΘ (wid-iterFold's induction on a
-- substitution instance), evalWith-iterFold (the evaluator's own
-- recursion over it), and wid-lift (the seed lift the members spend
-- their one extra fold on).
------------------------------------------------------------------

-- what an environment presents to the induction: every plugged value
-- is under the same leaf bound the slot telescope is under
EnvW : ∀ {n} {Γ : Ctx n} {Θ} → Slots Γ → ℕ → All (Val Γ) Θ → Set
EnvW sl M []ᵃ                        = ⊤
EnvW {n = n} sl M (_∷ᵃ_ {x = t} v σ) = (pWᵛ n sl t v ≤ M) × EnvW sl M σ

envW-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (M : ℕ) (sl : Slots Γ)
  (σ : All (Val Γ) Θ) → EnvW sl M σ → (z : t ∈ Θ) →
  pWᵛ n sl t (lookupEnv σ z) ≤ M
envW-lookup M sl (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envW-lookup M sl (v ∷ᵃ σ) (hv , hσ) (there z)   = envW-lookup M sl σ hσ z

envW-mono : ∀ {n} {Γ : Ctx n} {Θ} {M M′ : ℕ} (sl : Slots Γ)
  (σ : All (Val Γ) Θ) → M ≤ M′ → EnvW sl M σ → EnvW sl M′ σ
envW-mono sl []ᵃ      le hσ         = tt
envW-mono sl (v ∷ᵃ σ) le (hv , hσ) = ≤-trans hv le , envW-mono sl σ le hσ

-- the leaf bound only ever needs widening, which is all the seed
-- juggling below does
SlotWid-mono : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) {M M′ : ℕ} → M ≤ M′ →
  SlotWid sl M → SlotWid sl M′
SlotWid-mono sl le hI i = ≤-trans (proj₁ (hI i)) le
                        , ≤-trans (proj₁ (proj₂ (hI i))) le
                        , ≤-trans (proj₂ (proj₂ (hI i))) le

-- a pair's parked width is its components', which is what a scan rung
-- hands the step function and what the projections read back
pWᵛ-pair : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (s u : Ty)
  (a : Val Γ s) (b : Val Γ u) →
  pWᵛ n sl (s ×ᵗ u) (a , b) ≤ pWᵛ n sl s a ⊔ pWᵛ n sl u b
pWᵛ-pair {n = n} sl s u a b =
  ⊔-lub (⊔-lub (≤-trans (m≤m⊔n (outWᵛ n sl s a) (dWᵛ n sl s a)) (m≤m⊔n P Q))
               (≤-trans (m≤m⊔n (outWᵛ n sl u b) (dWᵛ n sl u b)) (m≤n⊔m P Q)))
        (⊔-lub (≤-trans (m≤n⊔m (outWᵛ n sl s a) (dWᵛ n sl s a)) (m≤m⊔n P Q))
               (≤-trans (m≤n⊔m (outWᵛ n sl u b) (dWᵛ n sl u b)) (m≤n⊔m P Q)))
  where
  P = pWᵛ n sl s a
  Q = pWᵛ n sl u b

pWᵛ-fst : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (s u : Ty)
  (a : Val Γ s) (b : Val Γ u) → pWᵛ n sl s a ≤ pWᵛ n sl (s ×ᵗ u) (a , b)
pWᵛ-fst {n = n} sl s u a b =
  ⊔-lub (≤-trans (m≤m⊔n (outWᵛ n sl s a) (outWᵛ n sl u b))
                 (m≤m⊔n (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))
        (≤-trans (m≤m⊔n (dWᵛ n sl s a) (dWᵛ n sl u b))
                 (m≤n⊔m (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))

pWᵛ-snd : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (s u : Ty)
  (a : Val Γ s) (b : Val Γ u) → pWᵛ n sl u b ≤ pWᵛ n sl (s ×ᵗ u) (a , b)
pWᵛ-snd {n = n} sl s u a b =
  ⊔-lub (≤-trans (m≤n⊔m (outWᵛ n sl s a) (outWᵛ n sl u b))
                 (m≤m⊔n (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))
        (≤-trans (m≤n⊔m (dWᵛ n sl s a) (dWᵛ n sl u b))
                 (m≤n⊔m (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))

-- a renaming the width slopes can see through: it moves a Θ variable
-- without moving its de Bruijn INDEX, which is what pmI reads
IxPres : ∀ {Θ Θ′ : List Ty} → Ren∈ Θ Θ′ → Set
IxPres {Θ} ρ = ∀ {u} (x : u ∈ Θ) → varIx (ρ x) ≡ varIx x

ext∈-IxPres : ∀ {Θ Θ′ s} {ρ : Ren∈ Θ Θ′} → IxPres ρ → IxPres (ext∈ {s = s} ρ)
ext∈-IxPres hp (here refl) = refl
ext∈-IxPres hp (there x)   = cong suc (hp x)

∅-IxPres : ∀ {Θ : List Ty} → IxPres {[]} {Θ} (λ ())
∅-IxPres ()

-- the shape every outW / innW clause lands in, since those two split on
-- the slot fuel and do not reduce at a variable one
bridge : ∀ {A : Set} {x y u v : A} → x ≡ u → y ≡ v → u ≡ v → x ≡ y
bridge p q r = trans p (trans r (sym q))

-- and a slot leaf weighs the same in any binder context: the measures
-- read the slot, never the telescope it sits under
module Irr {n} {Γ : Ctx n} where
  oW-input : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ Δᵍ′ Δ′ Θ′ : List Ty} (i : Fin n) →
    outWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i)
      ≡ outWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ′} {Δ = Δ′} {Θ = Θ′} i)
  oW-input zero    sl i = refl
  oW-input (suc q) sl i with sl i
  ... | scripted _ = refl
  ... | shared d   = refl

  iW-input : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ Δᵍ′ Δ′ Θ′ : List Ty} (i : Fin n) →
    innWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i)
      ≡ innWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ′} {Δ = Δ′} {Θ = Θ′} i)
  iW-input zero    sl i = refl
  iW-input (suc q) sl i with sl i
  ... | scripted _ = refl
  ... | shared d   = refl

  dW-input : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ Δᵍ′ Δ′ Θ′ : List Ty} (i : Fin n) →
    dWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i)
      ≡ dWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ′} {Δ = Δ′} {Θ = Θ′} i)
  dW-input zero    sl i = refl
  dW-input (suc q) sl i with sl i
  ... | scripted _ = refl
  ... | shared d   = refl

------------------------------------------------------------------
-- THE FIVE WIDTH MEASURES ARE RENAMING-INVARIANT, at an
-- index-preserving Θ renaming.  Renaming maps every constructor 1-1
-- and only `pmIᵗ`'s varᵗ clause reads an index at all — the caseW-ren /
-- shellSize-ren shape, four measures at once because they cross-refer
------------------------------------------------------------------

mutual
  ren-oWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (e : Exp Γ Δᵍ Δ Θ t) →
    outWᵉ q sl (renExp ρg ρd ρt e) ≡ outWᵉ q sl e
  ren-oWᵉ q sl ρg ρd ρt hp (input i)   = Irr.oW-input q sl i
  ren-oWᵉ q sl ρg ρd ρt hp (varᵉ x)    = bridge (Red.oW-var q sl _) (Red.oW-var q sl x) refl
  ren-oWᵉ q sl ρg ρd ρt hp emptyᵉ      = bridge (Red.oW-empty q sl) (Red.oW-empty q sl) refl
  ren-oWᵉ q sl ρg ρd ρt hp (deferᵉ e)  =
    bridge (Red.oW-defer q sl _) (Red.oW-defer q sl e) refl
  ren-oWᵉ q sl ρg ρd ρt hp (ofᵉ ts)    =
    bridge (Red.oW-of q sl _) (Red.oW-of q sl ts) (len-renTms ρg ρd ρt ts)
  ren-oWᵉ q sl ρg ρd ρt hp (mapᵉ f e)  =
    bridge (Red.oW-map q sl _ _) (Red.oW-map q sl f e)
           (ren-oWᵉ q sl ρg ρd ρt hp e)
  ren-oWᵉ q sl ρg ρd ρt hp (takeᵉ c e) =
    bridge (Red.oW-take q sl _ _) (Red.oW-take q sl c e)
           (ren-oWᵉ q sl ρg ρd ρt hp e)
  ren-oWᵉ q sl ρg ρd ρt hp (scanᵉ f z e) =
    bridge (Red.oW-scan q sl _ _ _) (Red.oW-scan q sl f z e)
           (ren-oWᵉ q sl ρg ρd ρt hp e)
  ren-oWᵉ q sl ρg ρd ρt hp (mergeAllᵉ lim e) =
    bridge (Red.oW-mergeAll q sl lim _) (Red.oW-mergeAll q sl lim e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (switchAllᵉ e) =
    bridge (Red.oW-switch q sl _) (Red.oW-switch q sl e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (exhaustAllᵉ e) =
    bridge (Red.oW-exhaust q sl _) (Red.oW-exhaust q sl e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (μᵉ e) =
    bridge (Red.oW-μ q sl _) (Red.oW-μ q sl e)
           (ren-oWᵉ q sl (ext∈ ρg) ρd ρt hp e)

  ren-iWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (e : Exp Γ Δᵍ Δ Θ t) →
    innWᵉ q sl (renExp ρg ρd ρt e) ≡ innWᵉ q sl e
  ren-iWᵉ q sl ρg ρd ρt hp (input i)  = Irr.iW-input q sl i
  ren-iWᵉ q sl ρg ρd ρt hp (varᵉ x)   = bridge (Red.iW-var q sl _) (Red.iW-var q sl x) refl
  ren-iWᵉ q sl ρg ρd ρt hp emptyᵉ     = bridge (Red.iW-empty q sl) (Red.iW-empty q sl) refl
  ren-iWᵉ q sl ρg ρd ρt hp (deferᵉ e) =
    bridge (Red.iW-defer q sl _) (Red.iW-defer q sl e) refl
  ren-iWᵉ q sl ρg ρd ρt hp (ofᵉ ts)   =
    bridge (Red.iW-of q sl _) (Red.iW-of q sl ts) (ren-iWᵗˢ q sl ρg ρd ρt hp ts)
  ren-iWᵉ q sl ρg ρd ρt hp (mapᵉ f e) =
    bridge (Red.iW-map q sl _ _) (Red.iW-map q sl f e)
           (cong₂ _+_ (ren-iWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) f)
                      (cong₂ _*_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                                 (ext∈-IxPres hp) 0 f))
                                 (ren-iWᵉ q sl ρg ρd ρt hp e)))
  ren-iWᵉ q sl ρg ρd ρt hp (takeᵉ c e) =
    bridge (Red.iW-take q sl _ _) (Red.iW-take q sl c e)
           (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (scanᵉ f z e) =
    bridge (Red.iW-scan q sl _ _ _) (Red.iW-scan q sl f z e)
           (cong₂ _*_ (cong₂ _^_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                                 (ext∈-IxPres hp) 0 f))
                                 (ren-oWᵉ q sl ρg ρd ρt hp e))
                      (cong (_+ 1)
                        (cong₂ _+_ (cong₂ _+_ (ren-iWᵗ q sl ρg ρd (ext∈ ρt)
                                                 (ext∈-IxPres hp) f)
                                              (ren-iWᵗ q sl ρg ρd ρt hp z))
                                   (ren-iWᵉ q sl ρg ρd ρt hp e))))
  ren-iWᵉ q sl ρg ρd ρt hp (mergeAllᵉ lim e) =
    bridge (Red.iW-mergeAll q sl lim _) (Red.iW-mergeAll q sl lim e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (switchAllᵉ e) =
    bridge (Red.iW-switch q sl _) (Red.iW-switch q sl e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (exhaustAllᵉ e) =
    bridge (Red.iW-exhaust q sl _) (Red.iW-exhaust q sl e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (μᵉ e) =
    bridge (Red.iW-μ q sl _) (Red.iW-μ q sl e) (ren-iWᵉ q sl (ext∈ ρg) ρd ρt hp e)

  ren-pOᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    pmOᵉ q sl k (renExp ρg ρd ρt e) ≡ pmOᵉ q sl k e
  ren-pOᵉ q sl ρg ρd ρt hp k (input i)  = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (varᵉ x)   = refl
  ren-pOᵉ q sl ρg ρd ρt hp k emptyᵉ     = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (deferᵉ e) = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (ofᵉ ts)   = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (mapᵉ f e)   = ren-pOᵉ q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (takeᵉ c e)  = ren-pOᵉ q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (scanᵉ f z e) = ren-pOᵉ q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (mergeAllᵉ _ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (switchAllᵉ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (exhaustAllᵉ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (μᵉ e) = ren-pOᵉ q sl (ext∈ ρg) ρd ρt hp k e

  allPO : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWᵉ q sl (renExp ρg ρd ρt e) * pmIᵉ q sl k (renExp ρg ρd ρt e)
      + pmOᵉ q sl k (renExp ρg ρd ρt e) * innWᵉ q sl (renExp ρg ρd ρt e)
    ≡ outWᵉ q sl e * pmIᵉ q sl k e + pmOᵉ q sl k e * innWᵉ q sl e
  allPO q sl ρg ρd ρt hp k e =
    cong₂ _+_ (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-pIᵉ q sl ρg ρd ρt hp k e))
              (cong₂ _*_ (ren-pOᵉ q sl ρg ρd ρt hp k e) (ren-iWᵉ q sl ρg ρd ρt hp e))

  ren-pIᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    pmIᵉ q sl k (renExp ρg ρd ρt e) ≡ pmIᵉ q sl k e
  ren-pIᵉ q sl ρg ρd ρt hp k (input i)  = refl
  ren-pIᵉ q sl ρg ρd ρt hp k (varᵉ x)   = refl
  ren-pIᵉ q sl ρg ρd ρt hp k emptyᵉ     = refl
  ren-pIᵉ q sl ρg ρd ρt hp k (deferᵉ e) = refl
  ren-pIᵉ q sl ρg ρd ρt hp k (ofᵉ ts)   = ren-pIᵗˢ q sl ρg ρd ρt hp k ts
  ren-pIᵉ q sl ρg ρd ρt hp k (mapᵉ f e) =
    cong₂ _+_ (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) f)
              (cong₂ _*_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                         (ext∈-IxPres hp) 0 f))
                         (ren-pIᵉ q sl ρg ρd ρt hp k e))
  ren-pIᵉ q sl ρg ρd ρt hp k (takeᵉ c e) = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (scanᵉ f z e) =
    cong₂ _*_ (cong₂ _^_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                         (ext∈-IxPres hp) 0 f))
                         (ren-oWᵉ q sl ρg ρd ρt hp e))
              (cong₂ _+_ (cong₂ _+_ (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                       (ext∈-IxPres hp) (suc k) f)
                                    (ren-pIᵗ q sl ρg ρd ρt hp k z))
                         (ren-pIᵉ q sl ρg ρd ρt hp k e))
  ren-pIᵉ q sl ρg ρd ρt hp k (mergeAllᵉ _ e)   = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (switchAllᵉ e)  = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (exhaustAllᵉ e) = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (μᵉ e) = ren-pIᵉ q sl (ext∈ ρg) ρd ρt hp k e

  ren-iWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (tm : Tm Γ Δᵍ Δ Θ t) → innWᵗ q sl (renTm ρg ρd ρt tm) ≡ innWᵗ q sl tm
  ren-iWᵗ q sl ρg ρd ρt hp (varᵗ x)    = refl
  ren-iWᵗ q sl ρg ρd ρt hp unit̂        = refl
  ren-iWᵗ q sl ρg ρd ρt hp (bool̂ _)    = refl
  ren-iWᵗ q sl ρg ρd ρt hp (nat̂ _)     = refl
  ren-iWᵗ q sl ρg ρd ρt hp (primᵗ _ a) = refl
  ren-iWᵗ q sl ρg ρd ρt hp (pairᵗ a b) =
    cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd ρt hp a) (ren-iWᵗ q sl ρg ρd ρt hp b)
  ren-iWᵗ q sl ρg ρd ρt hp (fstᵗ p) = ren-iWᵗ q sl ρg ρd ρt hp p
  ren-iWᵗ q sl ρg ρd ρt hp (sndᵗ p) = ren-iWᵗ q sl ρg ρd ρt hp p
  ren-iWᵗ q sl ρg ρd ρt hp (inlᵗ a) = ren-iWᵗ q sl ρg ρd ρt hp a
  ren-iWᵗ q sl ρg ρd ρt hp (inrᵗ a) = ren-iWᵗ q sl ρg ρd ρt hp a
  ren-iWᵗ q sl ρg ρd ρt hp (ifᵗ c a b) =
    cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd ρt hp a) (ren-iWᵗ q sl ρg ρd ρt hp b)
  ren-iWᵗ q sl ρg ρd ρt hp (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) l)
                         (ren-iWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 l)
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 r))
                            refl)
                         (ren-iWᵗ q sl ρg ρd ρt hp s))
  ren-iWᵗ q sl ρg ρd ρt hp (strmᵗ e) = ren-oWᵉ q sl ρg ρd ρt hp e


  ren-pIᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (tm : Tm Γ Δᵍ Δ Θ t) → pmIᵗ q sl k (renTm ρg ρd ρt tm) ≡ pmIᵗ q sl k tm
  ren-pIᵗ q sl ρg ρd ρt hp k (varᵗ x) =
    cong (λ i → if i ≡ᵇ k then 1 else 0) (hp x)
  ren-pIᵗ q sl ρg ρd ρt hp k unit̂        = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (bool̂ _)    = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (nat̂ _)     = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (primᵗ _ a) = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (pairᵗ a b) =
    cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd ρt hp k a) (ren-pIᵗ q sl ρg ρd ρt hp k b)
  ren-pIᵗ q sl ρg ρd ρt hp k (fstᵗ p) = ren-pIᵗ q sl ρg ρd ρt hp k p
  ren-pIᵗ q sl ρg ρd ρt hp k (sndᵗ p) = ren-pIᵗ q sl ρg ρd ρt hp k p
  ren-pIᵗ q sl ρg ρd ρt hp k (inlᵗ a) = ren-pIᵗ q sl ρg ρd ρt hp k a
  ren-pIᵗ q sl ρg ρd ρt hp k (inrᵗ a) = ren-pIᵗ q sl ρg ρd ρt hp k a
  ren-pIᵗ q sl ρg ρd ρt hp k (ifᵗ c a b) =
    cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd ρt hp k a) (ren-pIᵗ q sl ρg ρd ρt hp k b)
  ren-pIᵗ q sl ρg ρd ρt hp k (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) l)
                         (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 l)
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 r))
                            refl)
                         (ren-pIᵗ q sl ρg ρd ρt hp k s))
  ren-pIᵗ q sl ρg ρd ρt hp k (strmᵗ e) = ren-pOᵉ q sl ρg ρd ρt hp k e

  ren-iWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → innWᵗˢ q sl (renTms ρg ρd ρt ts) ≡ innWᵗˢ q sl ts
  ren-iWᵗˢ q sl ρg ρd ρt hp []       = refl
  ren-iWᵗˢ q sl ρg ρd ρt hp (y ∷ ys) =
    cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd ρt hp y) (ren-iWᵗˢ q sl ρg ρd ρt hp ys)

  ren-pIᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    pmIᵗˢ q sl k (renTms ρg ρd ρt ts) ≡ pmIᵗˢ q sl k ts
  ren-pIᵗˢ q sl ρg ρd ρt hp k []       = refl
  ren-pIᵗˢ q sl ρg ρd ρt hp k (y ∷ ys) =
    cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd ρt hp k y) (ren-pIᵗˢ q sl ρg ρd ρt hp k ys)

------------------------------------------------------------------
-- AND A RENAMING THAT REACHES NO INDEX `k` KILLS BOTH SLOPES — the
-- pm-ren0 shape, for the two width slopes.  A plug is Θ-closed, so it
-- is renamed in by `(λ ())` and every k is unreached
------------------------------------------------------------------

zeroSum : ∀ (a b : ℕ) → a * 0 + 0 * b ≡ 0
zeroSum a b = trans (+-identityʳ (a * 0)) (*-zeroʳ a)

mutual
  pO-ren0ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (e : Exp Γ Δᵍ Δ Θ t) → pmOᵉ q sl k (renExp ρg ρd ρt e) ≡ 0
  pO-ren0ᵉ q k sl ρg ρd ρt h (input i)  = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (varᵉ x)   = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h emptyᵉ     = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (deferᵉ e) = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (ofᵉ ts)   = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (mapᵉ f e)    = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (takeᵉ c e)   = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (scanᵉ f z e) = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (μᵉ e) = pO-ren0ᵉ q k sl (ext∈ ρg) ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (mergeAllᵉ _ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))
  pO-ren0ᵉ q k sl ρg ρd ρt h (switchAllᵉ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))
  pO-ren0ᵉ q k sl ρg ρd ρt h (exhaustAllᵉ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))

  pI-ren0ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (e : Exp Γ Δᵍ Δ Θ t) → pmIᵉ q sl k (renExp ρg ρd ρt e) ≡ 0
  pI-ren0ᵉ q k sl ρg ρd ρt h (input i)  = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h (varᵉ x)   = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h emptyᵉ     = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h (deferᵉ e) = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h (ofᵉ ts)   = pI-ren0ᵗˢ q k sl ρg ρd ρt h ts
  pI-ren0ᵉ q k sl ρg ρd ρt h (takeᵉ c e)   = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (mergeAllᵉ _ e)   = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (switchAllᵉ e)  = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (exhaustAllᵉ e) = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (μᵉ e) = pI-ren0ᵉ q k sl (ext∈ ρg) ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (mapᵉ f e)
    rewrite pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) f
          | pI-ren0ᵉ q k sl ρg ρd ρt h e =
    *-zeroʳ (pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) f) ⊔ 1)
  pI-ren0ᵉ q k sl ρg ρd ρt h (scanᵉ f z e)
    rewrite pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) f
          | pI-ren0ᵗ q k sl ρg ρd ρt h z
          | pI-ren0ᵉ q k sl ρg ρd ρt h e =
    *-zeroʳ ((pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) f) ⊔ 1)
               ^ outWᵉ q sl (renExp ρg ρd ρt e))

  pO-ren0ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (tm : Tm Γ Δᵍ Δ Θ t) → pmOᵗ q sl k (renTm ρg ρd ρt tm) ≡ 0
  pO-ren0ᵗ q k sl ρg ρd ρt h (varᵗ x)    = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h unit̂        = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (bool̂ _)    = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (nat̂ _)     = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (primᵗ _ a) = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (fstᵗ p)    = pO-ren0ᵗ q k sl ρg ρd ρt h p
  pO-ren0ᵗ q k sl ρg ρd ρt h (sndᵗ p)    = pO-ren0ᵗ q k sl ρg ρd ρt h p
  pO-ren0ᵗ q k sl ρg ρd ρt h (inlᵗ a)    = pO-ren0ᵗ q k sl ρg ρd ρt h a
  pO-ren0ᵗ q k sl ρg ρd ρt h (inrᵗ a)    = pO-ren0ᵗ q k sl ρg ρd ρt h a
  pO-ren0ᵗ q k sl ρg ρd ρt h (strmᵗ e)   = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵗ q k sl ρg ρd ρt h (pairᵗ a b)
    rewrite pO-ren0ᵗ q k sl ρg ρd ρt h a | pO-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (ifᵗ c a b)
    rewrite pO-ren0ᵗ q k sl ρg ρd ρt h a | pO-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (caseᵗ s l r)
    rewrite pO-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) l
          | pO-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) r
          | pO-ren0ᵗ q k sl ρg ρd ρt h s =
    *-zeroʳ (pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) l)
             ⊔ pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) r) ⊔ 1)

  pI-ren0ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (tm : Tm Γ Δᵍ Δ Θ t) → pmIᵗ q sl k (renTm ρg ρd ρt tm) ≡ 0
  pI-ren0ᵗ q k sl ρg ρd ρt h (varᵗ x)    = ifNeq (varIx (ρt x)) k (h x)
  pI-ren0ᵗ q k sl ρg ρd ρt h unit̂        = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (bool̂ _)    = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (nat̂ _)     = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (primᵗ _ a) = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (fstᵗ p)    = pI-ren0ᵗ q k sl ρg ρd ρt h p
  pI-ren0ᵗ q k sl ρg ρd ρt h (sndᵗ p)    = pI-ren0ᵗ q k sl ρg ρd ρt h p
  pI-ren0ᵗ q k sl ρg ρd ρt h (inlᵗ a)    = pI-ren0ᵗ q k sl ρg ρd ρt h a
  pI-ren0ᵗ q k sl ρg ρd ρt h (inrᵗ a)    = pI-ren0ᵗ q k sl ρg ρd ρt h a
  pI-ren0ᵗ q k sl ρg ρd ρt h (strmᵗ e)   = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵗ q k sl ρg ρd ρt h (pairᵗ a b)
    rewrite pI-ren0ᵗ q k sl ρg ρd ρt h a | pI-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (ifᵗ c a b)
    rewrite pI-ren0ᵗ q k sl ρg ρd ρt h a | pI-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (caseᵗ s l r)
    rewrite pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) l
          | pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) r
          | pI-ren0ᵗ q k sl ρg ρd ρt h s =
    *-zeroʳ (pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) l)
             ⊔ pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) r) ⊔ 1)

  pI-ren0ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → pmIᵗˢ q sl k (renTms ρg ρd ρt ts) ≡ 0
  pI-ren0ᵗˢ q k sl ρg ρd ρt h []       = refl
  pI-ren0ᵗˢ q k sl ρg ρd ρt h (y ∷ ys)
    rewrite pI-ren0ᵗ q k sl ρg ρd ρt h y | pI-ren0ᵗˢ q k sl ρg ρd ρt h ys = refl

-- the parked half of the same fact
mutual
  ren-dWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (e : Exp Γ Δᵍ Δ Θ t) → dWᵉ q sl (renExp ρg ρd ρt e) ≡ dWᵉ q sl e
  ren-dWᵉ q sl ρg ρd ρt hp (input i)  = Irr.dW-input q sl i
  ren-dWᵉ q sl ρg ρd ρt hp emptyᵉ     = refl
  ren-dWᵉ q sl ρg ρd ρt hp (varᵉ x)   = refl
  ren-dWᵉ q sl ρg ρd ρt hp (ofᵉ ts)   = ren-dWᵗˢ q sl ρg ρd ρt hp ts
  ren-dWᵉ q sl ρg ρd ρt hp (mapᵉ f e) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) f)
              (ren-dWᵉ q sl ρg ρd ρt hp e)
  ren-dWᵉ q sl ρg ρd ρt hp (takeᵉ c e) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp c) (ren-dWᵉ q sl ρg ρd ρt hp e)
  ren-dWᵉ q sl ρg ρd ρt hp (scanᵉ f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) f)
                         (ren-dWᵗ q sl ρg ρd ρt hp z))
              (ren-dWᵉ q sl ρg ρd ρt hp e)
  ren-dWᵉ q sl ρg ρd ρt hp (mergeAllᵉ _ e)   = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (switchAllᵉ e)  = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (exhaustAllᵉ e) = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (μᵉ e) = ren-dWᵉ q sl (ext∈ ρg) ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (deferᵉ e) =
    cong₂ _⊔_ (ren-oWᵉ q sl (λ ()) (++Ren ρg ρd) ρt hp e)
              (ren-dWᵉ q sl (λ ()) (++Ren ρg ρd) ρt hp e)

  ren-dWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (tm : Tm Γ Δᵍ Δ Θ t) → dWᵗ q sl (renTm ρg ρd ρt tm) ≡ dWᵗ q sl tm
  ren-dWᵗ q sl ρg ρd ρt hp (varᵗ x) = refl
  ren-dWᵗ q sl ρg ρd ρt hp unit̂     = refl
  ren-dWᵗ q sl ρg ρd ρt hp (bool̂ _) = refl
  ren-dWᵗ q sl ρg ρd ρt hp (nat̂ _)  = refl
  ren-dWᵗ q sl ρg ρd ρt hp (pairᵗ a b) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp a) (ren-dWᵗ q sl ρg ρd ρt hp b)
  ren-dWᵗ q sl ρg ρd ρt hp (fstᵗ p)    = ren-dWᵗ q sl ρg ρd ρt hp p
  ren-dWᵗ q sl ρg ρd ρt hp (sndᵗ p)    = ren-dWᵗ q sl ρg ρd ρt hp p
  ren-dWᵗ q sl ρg ρd ρt hp (inlᵗ a)    = ren-dWᵗ q sl ρg ρd ρt hp a
  ren-dWᵗ q sl ρg ρd ρt hp (inrᵗ a)    = ren-dWᵗ q sl ρg ρd ρt hp a
  ren-dWᵗ q sl ρg ρd ρt hp (primᵗ _ a) = ren-dWᵗ q sl ρg ρd ρt hp a
  ren-dWᵗ q sl ρg ρd ρt hp (ifᵗ c a b) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp c) (ren-dWᵗ q sl ρg ρd ρt hp a))
              (ren-dWᵗ q sl ρg ρd ρt hp b)
  ren-dWᵗ q sl ρg ρd ρt hp (caseᵗ s l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp s)
                         (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) l))
              (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) r)
  ren-dWᵗ q sl ρg ρd ρt hp (strmᵗ e) = ren-dWᵉ q sl ρg ρd ρt hp e

  ren-dWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → dWᵗˢ q sl (renTms ρg ρd ρt ts) ≡ dWᵗˢ q sl ts
  ren-dWᵗˢ q sl ρg ρd ρt hp []       = refl
  ren-dWᵗˢ q sl ρg ρd ρt hp (y ∷ ys) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp y) (ren-dWᵗˢ q sl ρg ρd ρt hp ys)

------------------------------------------------------------------
-- THE PLUG.  A substituted variable becomes the reified value, weakened
-- in: its two width faces are the VALUE's, and both its slopes vanish
-- because it is Θ-closed
------------------------------------------------------------------

plug-iW : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) →
  innWᵗ n sl (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≤ pWᵛ n sl t v
plug-iW {n = n} sl unitᵗ v = z≤n
plug-iW {n = n} sl boolᵗ v = z≤n
plug-iW {n = n} sl natᵗ  v = z≤n
plug-iW {n = n} sl (s ×ᵗ u) (a , b) =
  ⊔-lub (≤-trans (plug-iW {n = n} sl s a) (pWᵛ-fst sl s u a b))
        (≤-trans (plug-iW {n = n} sl u b) (pWᵛ-snd sl s u a b))
plug-iW {n = n} sl (s +ᵗ u) (inj₁ a) = plug-iW {n = n} sl s a
plug-iW {n = n} sl (s +ᵗ u) (inj₂ b) = plug-iW {n = n} sl u b
plug-iW {n = n} sl (obs u)  e =
  ≤-trans (≤-reflexive (ren-oWᵉ n sl (λ ()) (λ ()) (λ ()) ∅-IxPres e))
          (m≤m⊔n (outWᵉ n sl e) (dWᵉ n sl e))

plug-dW : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) →
  dWᵗ n sl (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≤ pWᵛ n sl t v
plug-dW {n = n} sl unitᵗ v = z≤n
plug-dW {n = n} sl boolᵗ v = z≤n
plug-dW {n = n} sl natᵗ  v = z≤n
plug-dW {n = n} sl (s ×ᵗ u) (a , b) =
  ⊔-lub (≤-trans (plug-dW {n = n} sl s a) (pWᵛ-fst sl s u a b))
        (≤-trans (plug-dW {n = n} sl u b) (pWᵛ-snd sl s u a b))
plug-dW {n = n} sl (s +ᵗ u) (inj₁ a) = plug-dW {n = n} sl s a
plug-dW {n = n} sl (s +ᵗ u) (inj₂ b) = plug-dW {n = n} sl u b
plug-dW {n = n} sl (obs u)  e =
  ≤-trans (≤-reflexive (ren-dWᵉ n sl (λ ()) (λ ()) (λ ()) ∅-IxPres e))
          (m≤n⊔m (outWᵉ n sl e) (dWᵉ n sl e))

plug-pO : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (k : ℕ) (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) → pmOᵗ n sl k (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≡ 0
plug-pO {n = n} k sl t v = pO-ren0ᵗ n k sl (λ ()) (λ ()) (λ ()) (λ ()) (reify v)

plug-pI : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (k : ℕ) (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) → pmIᵗ n sl k (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≡ 0
plug-pI {n = n} k sl t v = pI-ren0ᵗ n k sl (λ ()) (λ ()) (λ ()) (λ ()) (reify v)

