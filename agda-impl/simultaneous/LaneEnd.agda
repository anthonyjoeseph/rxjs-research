-- A LANE'S END, AS `laneˢ` SHOWS IT.  The elaborated lane, ending at `e`
-- under its trigger's lane, ends the share at the later of `e` and the
-- trigger's own end; the reader of the share ends one label under that,
-- which frees the `laneDone` lane; the `counted` scan sends that
-- `laneDone` on, and the take stops one label past it (`lane-end`).
--
-- Nothing ends the take sooner: the burst's frame sends no `laneDone`,
-- the elaborated lane none (`Undone`), and the lane's frame only the one
-- its third part sends, which the schedule puts where the reader ends.
module simultaneous.LaneEnd where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Nat using (ℕ; _+_; s≤s; z≤n)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Tree using (Obs; mergeᶠ; of; flatMap; takeWhile; scan; connect)
open import denotation.Position using (Pos; ix; sub; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; out; end; DenEnv; enter; Proper; ended; late; at-out; on-out; _≺_; _≼_; Few;
  module Op; module Joining; module Connecting; module Scan; module TakeWhile)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≼-refl; ≺→≼; ≺-≼-≺; ≼-or-≻; ≺-ext)
open import denotation.Laws.Worlds using (InvAt; world-after)
open import denotation.Laws.Worlds.Leaves using (out-inj)
open import denotation.Laws.Cut using (capprox; inv-capprox)
open import denotation.Laws.BoundedInv using (end-uniq)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Nth using (module Nths)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows)
open import quickcheck.Tabled.Exact.Base using (complete)
open import quickcheck.Tabled.Exact using (EnvRel)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; listC-exact; Raw; Uncut; UncutEnv)
open import simultaneous.TableCorr using (Corr)
open import simultaneous.TableKit using (TR)
open import simultaneous.TableEnv using (_⊕ˡ_; Tab; DenOf; den; den-ex; den-ok; Admits; admits-ix; admits-step; admits-at)
open import simultaneous.TreeBounded using (admits-trig)
open import simultaneous.DenRows using (merge-out)
open import simultaneous.ElabUndone using (Undone)
open import simultaneous.InstEmit using (stop)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; laneˢ; shareˢ; counted; framed; piece; laneStep; undone; marked)

open import simultaneous.LaneEndSched using (laneX; readerR; emitAt; later; later-cases; ≺-ˡ; raw-in; hot-in; tr-in; dec-end; acc-last;
  module Ending)

------------------------------------------------------------------------
-- One layer's row, read forward

-- A plain end's image, an end.
corr-end : ∀ {A s s* φ Put Late L L*} → Corr {A} s s* φ Put Late L L* → ∀ {k} → L k end → L* (φ k) end
corr-end C x with Corr.row→ C x tt
... | inj₂ (() , _)
... | inj₁ ((_ , y , m) , _) with proj₁ m tt
...   | refl = y

-- A connect's row, its body's.
conn-raw : ∀ {Γ X Y} K n (s : Obs Timeline Γ X) (b : Obs Timeline (X ∷ Γ) Y) (ρ : DenEnv Γ) p {k e}
         → enter (capprox K n b (ES.hot (Proper (enter (capprox K n s ρ) (p ⊕ [ ix 1 ]))) ∷ ρ)) (p ⊕ [ ix 0 ]) k e
         → Raw (capprox K n (connect s b) ρ) p k e
conn-raw K n s b ρ p x = Connecting.body x

-- A merge's value, a lane's.
merge-raw : ∀ {Γ X Y} K n (f : X → Obs Timeline Γ Y) (s : Obs Timeline Γ X) (ρ : DenEnv Γ) p {q a k y}
          → enter (capprox K n s ρ) p q (out a) → enter (capprox K n (f a) ρ) (q ⊕ [ ix 1 ]) k (out y) → (q ⊕ [ ix 1 ]) ≺ k
          → Raw (capprox K n (flatMap (mergeᶠ nothing) f s) ρ) p k (out y)
merge-raw K n f s ρ p oq l lt = Joining.lane oq tt (l , lt) (λ ()) tt

-- A scan's value, its fold.
scan-raw : ∀ {Γ X Y} K n (f : Y → X → Y) (z : Y) (s : Obs Timeline Γ X) (ρ : DenEnv Γ) p {q c}
         → Scan.Acc f z (enter (capprox K n s ρ) p) q c → Raw (capprox K n (scan f z s) ρ) p q (out c)
scan-raw K n f z s ρ p ac = Scan.sval ac

-- An inclusive take's end, at its first failing value.
stop-raw : ∀ {Γ X} K n (keep : X → Bool) (s : Obs Timeline Γ X) (ρ : DenEnv Γ) p {q a}
         → enter (capprox K n s ρ) p q (out a) → T (not (keep a)) → ¬ TakeWhile.Failed true keep (enter (capprox K n s ρ) p) q
         → Raw (capprox K n (takeWhile true keep s) ρ) p (q ⊕ [ last ]) end
stop-raw K n keep s ρ p r nk nf = TakeWhile.stop r nk nf

-- A ROW KEPT FOLDED.  An application whose type is a row of a large
-- program has that type reduced to its head, which runs the program's
-- denotation; a `Row` stops there, and two of them compare as programs.
-- Each step below is checked once, over a variable program.
opaque
  Row : ∀ {Γ X} (K n : ℕ) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) → Pos → Pos → ES.Ev X → Set
  Row K n o ρ p q e = enter (capprox K n o ρ) p q e

opaque
  unfolding Row

  toRow : ∀ {Γ X} (K n : ℕ) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) p q e → enter (capprox K n o ρ) p q e → Row K n o ρ p q e
  toRow K n o ρ p q e x = x

  connR : ∀ {Γ X Y} (K n : ℕ) (s : Obs Timeline Γ X) (b : Obs Timeline (X ∷ Γ) Y) {ρL ρD} → EnvRel ρL ρD → UncutEnv ρL → ∀ p q e
        → Row K n b (ES.hot (Proper (enter (capprox K n s ρD) (p ⊕ [ ix 1 ]))) ∷ ρD) (p ⊕ [ ix 0 ]) q e → Row K n (connect s b) ρD p q e
  connR K n s b ex u p q e r = raw-in K n (connect s b) tt ex u p (conn-raw K n s b _ p r)

  mergeR : ∀ {Γ X Y} (K n : ℕ) (f : X → Obs Timeline Γ Y) (s : Obs Timeline Γ X) {ρL ρD} → EnvRel ρL ρD → UncutEnv ρL → ∀ p q a k y
         → Row K n s ρD p q (out a) → Row K n (f a) ρD (q ⊕ [ ix 1 ]) k (out y) → (q ⊕ [ ix 1 ]) ≺ k
         → Row K n (flatMap (mergeᶠ nothing) f s) ρD p k (out y)
  mergeR K n f s ex u p q a k y oq l lt = raw-in K n (flatMap (mergeᶠ nothing) f s) tt ex u p (merge-raw K n f s _ p oq l lt)

  stopR : ∀ {Γ X} (K n : ℕ) (keep : X → Bool) (s : Obs Timeline Γ X) {ρL ρD} → EnvRel ρL ρD → UncutEnv ρL → ∀ p q a
        → Row K n s ρD p q (out a) → T (not (keep a)) → ¬ TakeWhile.Failed true keep (Row K n s ρD p) q
        → Row K n (takeWhile true keep s) ρD p (q ⊕ [ last ]) end
  stopR K n keep s ex u p q a r nk nf = raw-in K n (takeWhile true keep s) tt ex u p (stop-raw K n keep s _ p r nk nf)

  -- A row of a listed program, listed.
  rowIn : ∀ {Γ A} (K n : ℕ) (o : Obs Timeline Γ A) {ρL ρD} → EnvRel ρL ρD → ∀ p {l} → listC K n o ρL p ≡ just l → Uncut l → ∀ q e
        → Row K n o ρD p q e → (q , e) ∈ rows l
  rowIn K n o ex p eq ul q e r = complete (listC-exact K n o ex p eq ul) r

  -- A merge's row, a lane's under a value of its source.
  backR : ∀ {Γ X Y} (K n : ℕ) (o : Obs Timeline Γ Y) (f : X → Obs Timeline Γ Y) (s : Obs Timeline Γ X) (ρ : DenEnv Γ) → o ≡ flatMap (mergeᶠ nothing) f s → ∀ p k y
        → Row K n o ρ p k (out y)
        → Σ Pos λ q → Σ X λ a → enter (capprox K n s ρ) p q (out a) × enter (capprox K n (f a) ρ) (q ⊕ [ ix 1 ]) k (out y) × (q ⊕ [ ix 1 ]) ≺ k
  backR K n o f s ρ refl p k y x = merge-out (λ a → capprox K n (f a) ρ) (capprox K n s ρ) p x


------------------------------------------------------------------------
-- The lane's end

module Lane {Θ : List Set} {B : Set} n (x : Obs Timeline (⊤ ∷ Θ) (IE B)) {ρ : ℕ → All Tb.Listed Θ} (u : ∀ N → UncutEnv (ρ N))
            (D : DenOf ρ) (st : Pos) (ad : Admits D st) (N : ℕ) (ux : ∀ h → Undone (capprox (3 + N) n x (h ∷ den D N))) where
  open Ending n x {ρ} u D st ad N ux
  open Nths Ob using (nth-inj)

  ----------------------------------------------------------------------
  -- Past the elaborated lane's end at `e`

  module At {e : Pos} (xt : TR (listC K n x (trig N ∷ ρ N) (laneX st)) e end) where

    xe : enter (capprox K n x ρ₁) (laneX st) e end
    xe = tr-in K n x {ℓ₁ N} (den-ex D₁ N) (u₁ N) (laneX st) xt

    Ix : InvAt _ (laneX st) (enter (capprox K n x ρ₁) (laneX st))
    Ix = inv-capprox K n x ρ₁ (den-ok D₁ N) (laneX st) (admits-at D₁ (admits-ix D₁ 1 (admits-ix D₁ 0 (admits-trig n u D L aL))) N)

    lx : laneX st ≺ e
    lx = world-after (InvAt.world Ix xe) (InvAt.real Ix xe)

    -- The gated lane ends at the later of `e` and the gate's end.
    g-ended : ∀ {c} → e ≼ c → ∀ {q a} → tw q (out a) → ⊤ → q ≺ c → ¬ ⊥ → ES.Ended (ES.LaneOf (λ _ → capprox K n x ρ₁) q a) c
    g-ended le tq _ _ _ with tg-out⁻ tq
    ... | refl = e , (xe , lx) , le

    g-at : (sp ⊕ [ last ]) ≺ e → enter Gd sp e end
    g-at lt = raw-in K n (G lanePart) tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) sp
      (Joining.lend tg-val tt (xe , lx) (λ ()) (λ ()) ((sp ⊕ [ last ] , tg-end , ≺→≼ {sp ⊕ [ last ]} {e} lt) , g-ended (≼-refl {e})))

    g-in : e ≼ (sp ⊕ [ last ]) → enter Gd sp (sp ⊕ [ last ]) end
    g-in le = raw-in K n (G lanePart) tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) sp
      (Joining.oend tg-end ((sp ⊕ [ last ] , tg-end , ≼-refl {sp ⊕ [ last ]}) , g-ended le))

    sp-sl : sp ≺ (sp ⊕ [ last ])
    sp-sl = ≺-ext sp []

    g-by : ∀ {c} → e ≼ c → (sp ⊕ [ last ]) ≼ c → Σ Pos λ c₁ → (enter Gd sp c₁ end × sp ≺ c₁) × c₁ ≼ c
    g-by le le′ with ≼-or-≻ e (sp ⊕ [ last ])
    ... | inj₁ e≼ = sp ⊕ [ last ] , (g-in e≼ , sp-sl) , le′
    ... | inj₂ lt = e , (g-at lt , ≺-trans {sp} {sp ⊕ [ last ]} {e} sp-sl lt) , le

    -- The share ends at the later of `e` and the trigger's end.
    E : Pos
    E = later e T′

    s-ended : ∀ {c} → e ≼ c → T′ ≼ c → ∀ {q a} → enter (ES.hot (Proper σ₁)) S q (out a) → ⊤ → q ≺ c → ¬ ⊥
            → ES.Ended (ES.LaneOf (λ _ → Gd) q a) c
    s-ended {c} le lT tq _ _ _ with r₁-out⁻ tq
    ... | refl = g-by {c} le (≺→≼ {sp ⊕ [ last ]} {c} (≺-≼-≺ {sp ⊕ [ last ]} {T′} {c} sl-T lT))

    σ₂-end : σ₂ E end
    σ₂-end with later-cases e T′
    ... | inj₁ (eq , Te) = subst (λ c → σ₂ c end) (sym eq) (raw-in K n (Sh lanePart) tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) S
            (Joining.lend r₁-val tt (g-at sl-e , ≺-trans {sp} {sp ⊕ [ last ]} {e} sp-sl sl-e) (λ ()) (λ ())
              ((T′ , r₁-end , Te) , s-ended (≼-refl {e}) Te)))
      where
        sl-e : (sp ⊕ [ last ]) ≺ e
        sl-e = ≺-≼-≺ {sp ⊕ [ last ]} {T′} {e} sl-T Te
    ... | inj₂ (eq , eT) = subst (λ c → σ₂ c end) (sym eq) (raw-in K n (Sh lanePart) tt {ℓ₁ N} (den-ex D₁ N) (u₁ N) S
            (Joining.oend r₁-end ((T′ , r₁-end , ≼-refl {T′}) , s-ended (≺→≼ {e} {T′} eT) (≼-refl {T′}))))

    T-E : T′ ≼ E
    T-E with later-cases e T′
    ... | inj₁ (eq , Te) = subst (T′ ≼_) (sym eq) Te
    ... | inj₂ (eq , _)  = subst (T′ ≼_) (sym eq) (≼-refl {T′})

    I₂ : InvAt _ S σ₂
    I₂ = inv-capprox K n (Sh lanePart) ρ₁ (den-ok D₁ N) S (admits-at D₁ (admits-step D₁ a₁) N)

    H₂-end : Proper σ₂ E end
    H₂-end = σ₂-end , λ c → subst (E ≼_) (end-uniq I₂ σ₂-end c) (≼-refl {E})

    H₂-end⁻ : ∀ {c} → Proper σ₂ c end → c ≡ E
    H₂-end⁻ (c , _) = end-uniq I₂ c σ₂-end

    R-E : R ≺ E
    R-E = ≺-≼-≺ {R} {T′} {E} R-T T-E

    -- The reader ends one label under the share's end.
    E₁ : Pos
    E₁ = E ⊕ [ sub R ]

    E-E₁ : E ≺ E₁
    E-E₁ = ≺-ext E []

    l₁-end : enter (ES.hot (Proper σ₂)) R E₁ end
    l₁-end = hot-in n (Sh lanePart) {ℓ₁} u₁ D₁ B₀ N R (ended H₂-end R-E)

    l₁-end⁻ : ∀ {c} → enter (ES.hot (Proper σ₂)) R c end → c ≡ E₁
    l₁-end⁻ (ended h _ , _) = cong (λ c′ → c′ ⊕ [ sub R ]) (H₂-end⁻ h)
    l₁-end⁻ (late h le , _) = ⊥-elim (le (subst (R ≺_) (sym (H₂-end⁻ h)) R-E))

    l₁-ends : Bd.Ends 1 (Bd.Sched 1) E₁
    l₁-ends = Bc ⊕ [ ix 1 ] , 1 , R , nth₁ , fr₁ , (l₁-end , ≺-trans {R} {E} {E₁} R-E E-E₁)

    l₁-uniq : ∀ {c} → Bd.Ends 1 (Bd.Sched 1) c → c ≡ E₁
    l₁-uniq (_ , _ , _ , nq , sq , af) with BI.sub-fun (nq , sq) sb₁
    ... | refl , refl , refl = l₁-end⁻ (proj₁ af)

    -- The third part, queued where the reader ends.
    B2-E₁ : (Bc ⊕ [ ix 2 ]) ≺ E₁
    B2-E₁ = ≺-trans {Bc ⊕ [ ix 2 ]} {E} {E₁} (≺-≼-≺ {Bc ⊕ [ ix 2 ]} {T′} {E} B2-T T-E) E-E₁

    c₀-E₁ : c₀ ≼ E₁
    c₀-E₁ = ≺→≼ {c₀} {E₁} (≺-trans {c₀} {E} {E₁} (≺-≼-≺ {c₀} {T′} {E} c₀-T T-E) E-E₁)

    nK : ¬ Bd.Kth (_≺ E₁) (Bd.Sched 2) 1
    nK (inj₁ ((c , ec , lt) , _)) = ≺-irrefl {E₁} (subst (_≺ E₁) (l₁-uniq ec) lt)
    nK (inj₂ (inj₁ (_ , ())))
    nK (inj₂ (inj₂ ()))

    sb₂ : Bd.Sub 2 (Bc ⊕ [ ix 2 ]) (E₁ ⊕ [ ix 1 ]) 2
    sb₂ = nth₂ , Bd.queued (s≤s z≤n) B2-E₁ (inj₁ (E₁ , l₁-ends , refl))
                   (inj₁ ((E₁ , l₁-ends , ≼-refl {E₁}) , inj₁ (c₀ , l₀-end , c₀-E₁))) nK

    V Q : Pos
    V = (E₁ ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
    Q = emitAt V

    Fr : EmissionSet (IE B)
    Fr = enter (capprox K n (framed lanePart) ρ₂) Bc

    fr-val : Fr V (out ld)
    fr-val = raw-in K n (framed lanePart) tt {ℓ₂ N} (den-ex D₂ N) (u₂ N) Bc
      (Joining.lane ob₂ (2 , 2 , nth₂)
        (2 , E₁ ⊕ [ ix 1 ] , sb₂ , (raw-in K n (of (ld ∷ [])) tt {ℓ₂ N} (den-ex D₂ N) (u₂ N) (E₁ ⊕ [ ix 1 ]) at-out , ≺-ext (E₁ ⊕ [ ix 1 ]) []))
        (λ ()) tt)

    few-fr : Few Fr V
    few-fr =
      let (l , eq , ul) = listC-ok K n (framed lanePart) {ℓ₂ N} (u₂ N) Bc
      in L.map proj₁ (rows l) , λ y _ → ∈-map⁺ proj₁ (complete (listC-exact K n (framed lanePart) {ℓ₂ N} (den-ex D₂ N) Bc eq ul) y)

    IFr : InvAt _ Bc Fr
    IFr = inv-capprox K n (framed lanePart) ρ₂ (den-ok D₂ N) Bc okB

    -- The scan's state there folds the third part's mark.
    acc-at : ∀ {y} → Scan.Acc laneStep z₀ Fr V y → Σ (Routes × (List (IE B) × List (IE B))) λ b → y ≡ laneStep b ld
    acc-at = acc-last (λ r → out-inj (InvAt.func IFr r fr-val))

    W : Pos
    W = V ⊕ [ ix 1 ]

    lane-s : ∀ {i s} → i ≡ 2 → Bd.Sub i (Bc ⊕ [ ix 2 ]) s 2 → emitAt (s ⊕ [ ix 0 ]) ≡ Q
    lane-s refl sb = cong (λ s′ → emitAt (s′ ⊕ [ ix 0 ])) (proj₂ (proj₂ (BI.sub-fun sb sb₂)))

    -- The lane part's `laneDone` is the third part's, at `Q`.
    lane-q : ∀ {q v} → q ≡ emitAt v
           → lanePart ≡ lanePart × Σ ℕ (λ i → Σ Pos λ s → Bd.Sub i (Bc ⊕ [ ix 2 ]) s 2 × v ≡ s ⊕ [ ix 0 ]) → q ≡ Q
    lane-q refl (_ , i , s , sb , refl) = lane-s (nth-inj (proj₁ sb) nth₂) sb


    burst-no : burstPart ≡ lanePart → ⊥
    burst-no ()


    lane-p : ∀ {q P} → P ≡ L → (Σ Pos λ v → Σ (IE B) λ a₀ → q ≡ emitAt v × Peel.FrP lanePart P v (out a₀) × T (not (undone a₀))) → q ≡ Q
    lane-p refl (v , a₀ , eq , fr , nu₀) = lane-q eq (Peel.fr-back lanePart L fr nu₀)

    burst-p : ∀ {q P} → (Σ Pos λ v → Σ (IE B) λ a₀ → q ≡ emitAt v × Peel.FrP burstPart P v (out a₀) × T (not (undone a₀))) → q ≡ Q
    burst-p {P = P} (v , a₀ , eq , fr , nu₀) = ⊥-elim (burst-no (proj₁ (Peel.fr-back burstPart P fr nu₀)))

    back-v : ∀ {q₁ k q} → enter (Op.of (lanePart ∷ burstPart ∷ [])) st q₁ (out k)
           → (Σ Pos λ v → Σ (IE B) λ a₀ → q ≡ emitAt v × Peel.FrP k (q₁ ⊕ [ ix 1 ]) v (out a₀) × T (not (undone a₀))) → q ≡ Q
    back-v (at-out , _)        pr = lane-p refl pr
    back-v (on-out at-out , _) pr = burst-p pr
    back-v (on-out (on-out ()) , _) _

    back-k : ∀ {q₁ k q a} → enter (Op.of (lanePart ∷ burstPart ∷ [])) st q₁ (out k)
           → enter (capprox K n (shareˢ (G k) (counted (framed k))) ρ₀) (q₁ ⊕ [ ix 1 ]) q (out a) → T (not (undone a)) → q ≡ Q
    back-k {q₁} {k} {q} {a} oq l nu = back-v oq (Peel.peel k (q₁ ⊕ [ ix 1 ]) {q} {a} l nu)

    back-m : ∀ {q a} → (Σ Pos λ q₁ → Σ Part λ k → enter (Op.of (lanePart ∷ burstPart ∷ [])) st q₁ (out k)
                        × enter (capprox K n (shareˢ (G k) (counted (framed k))) ρ₀) (q₁ ⊕ [ ix 1 ]) q (out a) × (q₁ ⊕ [ ix 1 ]) ≺ q)
           → T (not (undone a)) → q ≡ Q
    back-m {q} {a} (q₁ , k , oq , l , _) nu = back-k {q₁} {k} {q} {a} oq l nu

    -- No earlier `laneDone` reaches the take.
    back : ∀ {q a} → Row K n M ρ₀ st q (out a) → T (not (undone a)) → q ≡ Q
    back {q} {a} r = back-m {q} {a} (backR K n M (λ k → shareˢ (G k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ [])) ρ₀ refl st q a r)

    nf-at : ∀ {q} → q ≡ Q → q ≺ Q → ⊥
    nf-at refl lt = ≺-irrefl {Q} lt

    nf : ¬ TakeWhile.Failed true undone (Row K n M ρ₀ st) Q
    nf (q , a , mq , nu , lt) = nf-at {q} (back {q} {a} mq nu) lt

    -- Forward: the mark through `counted`, both connects, the merge and
    -- the take.
    module Fwd (b : Routes × (List (IE B) × List (IE B))) (ac : Scan.Acc laneStep z₀ Fr V (laneStep b ld)) where
      y : Routes × (List (IE B) × List (IE B))
      y = laneStep b ld

      -- Every position and environment below is spelled as the
      -- operator above it computes it.
      P₀ : Pos
      P₀ = (st ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

      ccf : Obs Timeline (IE B ∷ ⊤ ∷ Θ) (IE B)
      ccf = counted (framed lanePart)

      env₁ : DenEnv (⊤ ∷ Θ)
      env₁ = ES.hot (Proper (enter (capprox K n (of (tt ∷ [])) ρ₀) (P₀ ⊕ [ ix 1 ]))) ∷ ρ₀

      env₂ : DenEnv (IE B ∷ ⊤ ∷ Θ)
      env₂ = ES.hot (Proper (enter (capprox K n (Sh lanePart) env₁) ((P₀ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))) ∷ env₁

      Bp : Pos
      Bp = (P₀ ⊕ [ ix 0 ]) ⊕ [ ix 0 ]

      o-false : enter (capprox K n (of (true ∷ false ∷ [])) env₂) (V ⊕ [ ix 1 ]) ((V ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) (out false)
      o-false = raw-in K n (of (true ∷ false ∷ [])) tt {ℓ₂ N} {env₂} (den-ex D₂ N) (u₂ N) (V ⊕ [ ix 1 ]) (on-out at-out)

      o-ld : enter (capprox K n (of (if false then proj₁ (proj₂ y) else proj₂ (proj₂ y))) env₂) (((V ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) Q (out ld)
      o-ld = raw-in K n (of (if false then proj₁ (proj₂ y) else proj₂ (proj₂ y))) tt {ℓ₂ N} {env₂} (den-ex D₂ N) (u₂ N)
        (((V ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) at-out

      in-val : enter (capprox K n (inner y) env₂) (V ⊕ [ ix 1 ]) Q (out ld)
      in-val = raw-in K n (inner y) tt {ℓ₂ N} {env₂} (den-ex D₂ N) (u₂ N) (V ⊕ [ ix 1 ])
        (merge-raw K n (λ c → of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (of (true ∷ false ∷ [])) env₂ (V ⊕ [ ix 1 ])
          o-false o-ld (≺-ext (((V ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) []))

      sv : enter (capprox K n (scan laneStep z₀ (framed lanePart)) env₂) Bp V (out y)
      sv = raw-in K n (scan laneStep z₀ (framed lanePart)) tt {ℓ₂ N} {env₂} (den-ex D₂ N) (u₂ N) Bp
        (scan-raw K n laneStep z₀ (framed lanePart) env₂ Bp ac)

      ct-val : enter (capprox K n ccf env₂) Bp Q (out ld)
      ct-val = raw-in K n ccf tt {ℓ₂ N} {env₂} (den-ex D₂ N) (u₂ N) Bp
        (merge-raw K n inner (scan laneStep z₀ (framed lanePart)) env₂ Bp sv in-val (≺-ˡ (V ⊕ [ ix 1 ]) (ix 1) (ix 1 ∷ ix 0 ∷ [])))

      c₁-val : enter (capprox K n (connect (Sh lanePart) ccf) env₁) (P₀ ⊕ [ ix 0 ]) Q (out ld)
      c₁-val = raw-in K n (connect (Sh lanePart) ccf) tt {ℓ₁ N} {env₁} (den-ex D₁ N) (u₁ N) (P₀ ⊕ [ ix 0 ])
        (conn-raw K n (Sh lanePart) ccf env₁ (P₀ ⊕ [ ix 0 ]) ct-val)

      c₀-val : Row K n (shareˢ (G lanePart) ccf) ρ₀ P₀ Q (out ld)
      c₀-val = connR K n (of (tt ∷ [])) (connect (Sh lanePart) ccf) {ρ N} {ρ₀} (den-ex D N) (u N) P₀ Q (out ld)
        (toRow K n (connect (Sh lanePart) ccf) env₁ (P₀ ⊕ [ ix 0 ]) Q (out ld) c₁-val)

      L-Q : P₀ ≺ Q
      L-Q = ≺-trans {L} {E} {Q} (≺-≼-≺ {L} {T′} {E} L-T T-E) (≺-ˡ E (sub R) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 1 ∷ ix 1 ∷ ix 0 ∷ []))

      oq : enter (capprox K n (of (lanePart ∷ burstPart ∷ [])) ρ₀) st (st ⊕ [ ix 0 ]) (out lanePart)
      oq = raw-in K n (of (lanePart ∷ burstPart ∷ [])) tt {ρ N} {ρ₀} (den-ex D N) (u N) st at-out

      m-val : Row K n M ρ₀ st Q (out ld)
      m-val = mergeR K n (λ k → shareˢ (G k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ [])) {ρ N} {ρ₀} (den-ex D N) (u N) st (st ⊕ [ ix 0 ]) lanePart Q ld
        (toRow K n (of (lanePart ∷ burstPart ∷ [])) ρ₀ st (st ⊕ [ ix 0 ]) (out lanePart) oq) c₀-val L-Q

      final : Row K n (laneˢ x) ρ₀ st (Q ⊕ [ last ]) end
      final = stopR K n undone M {ρ N} {ρ₀} (den-ex D N) (u N) st Q ld m-val tt nf

    end-row : ¬ ¬ Row K n (laneˢ x) ρ₀ st (Q ⊕ [ last ]) end
    end-row ¬r = fold laneStep z₀ Fr few-fr fr-val λ { (_ , ac) → go ac }
      where
        go′ : ∀ {y} → Scan.Acc laneStep z₀ Fr V y → (Σ (Routes × (List (IE B) × List (IE B))) λ b → y ≡ laneStep b ld) → ⊥
        go′ ac (b , refl) = ¬r (Fwd.final b ac)

        go : ∀ {y} → Scan.Acc laneStep z₀ Fr V y → ⊥
        go ac = go′ ac (acc-at ac)

    row-of : ∀ {l} → listC K n (laneˢ x) (ρ N) st ≡ just l → Uncut l → Dec ((Q ⊕ [ last ] , end) ∈ rows l)
           → TR (listC K n (laneˢ x) (ρ N) st) (Q ⊕ [ last ]) end
    row-of eq ul (yes m) = _ , eq , m
    row-of eq ul (no ¬m) = ⊥-elim (end-row λ r → ¬m (rowIn K n (laneˢ x) (den-ex D N) st eq ul (Q ⊕ [ last ]) end r))

    row-at : (Σ (Tb.Listed (IE B)) λ l → listC K n (laneˢ x) (ρ N) st ≡ just l × Uncut l) → TR (listC K n (laneˢ x) (ρ N) st) (Q ⊕ [ last ]) end
    row-at (l , eq , ul) = row-of eq ul (dec-end (rows l) (Q ⊕ [ last ]))

    row : TR (listC K n (laneˢ x) (ρ N) st) (Q ⊕ [ last ]) end
    row = row-at (listC-ok K n (laneˢ x) (u N) st)

  -- The plain table, at a program not yet known: no listing is read.
  tr-tab : ∀ {X} {o : Obs Timeline Θ X} {q e} → TR (listC K n o (ρ N) st) q e → TR (Tab n o ρ st N) q e
  tr-tab t = t

  -- THE ELABORATED LANE'S END, AS `laneˢ` SHOWS IT, at the caller's own
  -- spelling of the trigger, the lane and the row: each equation is
  -- checked on its own small term, never under a listing.
  lane-end : ∀ {t o q e} → t ≡ trig N → o ≡ laneˢ x → q ≡ emitAt (later e T′ ⊕ˡ (sub (readerR st) ∷ ix 1 ∷ ix 0 ∷ [])) ⊕ [ last ]
           → TR (listC K n x (t ∷ ρ N) (laneX st)) e end → TR (Tab n o ρ st N) q end
  lane-end refl refl refl xt = tr-tab {o = laneˢ x} (At.row xt)
