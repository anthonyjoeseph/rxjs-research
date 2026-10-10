------------------------------------------------------------------
-- AN EXPLODE'S ONE CARRYING EMIT: the impl's merge subscribes the
-- run the explode cuts as an inner at the counter's next node, which
-- finishes at once, its element walked beside the plain outer's walk
------------------------------------------------------------------
module Simulation.Pass.Explode where

open import Data.Bool    using (T; true; false)
open import Data.Empty   using (⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; reverseAcc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (nothing; just)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; n<1+n)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using ([_,_]; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Exp       using (Ctx; Closed; Val; Ty; Env; ofᵉ; evalWith; obs; applyClo; Tm; foldᵗ; consᵗ; nilᵗ; strmᵗ; emptyᵉ;
  _∷ᵉ_; renTm; ext∈; unitᵗ; _+ᵗ_; _×ᵗ_; fstᵗ; varᵗ; foldVals; uniqᵗ)
open import SExp.InstEmit using (splitAccᵗ; splitEventsᵛ; instEventᵗ)
open import Rx.Evaluator using (EvalSt; Path; _↠[_]_; thru-outer; from-inner; mergeAllᵒ; lookupNode; echoᵗ; thruEvents;
  Sched; mergeAll-st; setNode)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-step; step-from-inner; react-alive; react-dead; finish-nil;
  finish-all-drain; drain-spent; subscribeInner⇓; thruWalk⇓; subs-of; inner; subscribeE⇓; innerFinish⇓)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ; plainᵗ)
open import SExp.Elaborate using (explodeᵛ; elemᵛ; elemBodyᵛ)
open import Simulation.Elem using (pw-one; paysOf; values-decode; split-eval; fold-rev; revStep)
open import Simulation.Stores using (EmitRel; Flattener; V; PathRel; []; _∷_; Store; MergeAt; LiveIf; live-if-under)
open import Simulation.After using (module Kept; readᴾ; readᴵ)
open import Simulation.Arm using (Out; out-++; Clear; fold-clear; reclear; thru)
open import Simulation.Sweep using (t≢f)
open import Rx.Evaluator.Reducible.Support using (Sound; sub-ot; sub-on)
open import Rx.Evaluator.Unconn-Arith using (keeps-refl)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set)
open import Rx.Mint using (nodeᵏ; setAt)
open import Rx.Evaluator.Reducible.Rule-Kept using (Thru; thruWalk-rule)
open import Simulation.Pass.Quiet using (module PassQ; usable-self; fresh-dead; nil-all)
open import Simulation.Walks using (module Walkers)
open import Simulation.Size using (sz-thruWalk)

-- a walk through a flattener keeps its node off the path below it
walk-clear : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo w} {k} {κ : Path Δ lo w u} {op now xs}
               {sched sched′ st st′ out}
           → thruWalk⇓ {e = e} op k κ now xs sched st (out , sched′ , st′)
           → Clear k κ sched st → Clear k κ sched′ st′
walk-clear {e = e} {k = k} {κ = κ} d c = reclear {π = Thru {e = e} k κ} refl c (thruWalk-rule d (thru c))

-- a `letᵗ` read apart: the term it binds, its default, and the body
-- under both
data LetOf {m} {Δ : Ctx m} {Θ s u} : Tm Δ [] [] Θ u → Set where
  letOf : ∀ (x : Tm Δ [] [] Θ s) d (b : Tm Δ [] [] (s ∷ u ∷ Θ) u) → LetOf (foldᵗ (consᵗ x nilᵗ) d b)

letBody : ∀ {m} {Δ : Ctx m} {Θ s u} {x : Tm Δ [] [] Θ u} → LetOf {s = s} x → Tm Δ [] [] (s ∷ u ∷ Θ) u
letBody (letOf _ _ b) = b

-- WHAT `explodeᵛ` MAKES OF AN EMIT CARRYING ONE PAYLOAD: an `of` of one
-- element, the one `elemᵛ` makes of the same emit.  Both are stuck only
-- on the emit's split, so each is read over a split carrying that one
-- payload; the two then differ only in the environment their
-- bookkeeping's reversals fold under, which no reversal reads.
module _ {m} {Δ : Ctx m} {t : Ty} {Θ} (ρ : Env Δ Θ) (e′ : Val Δ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)))) where

  private
    P : Ty
    P = plainᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))

    Elm : Ty
    Elm = (unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t))

    E : Ty
    E = emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))

    SP : Ty
    SP = splitAccᵗ uniqᵗ P (plainᵗ t)

    env₀ : Env Δ (E ∷ Θ)
    env₀ = e′ ∷ᵉ ρ

    -- `explodeᵛ`'s body under its split
    ex-body : Val Δ SP → Val Δ (obs Elm)
    ex-body sp = evalWith (letBody {x = explodeᵛ {Δᵍ = []} {Δ = []} {Θ = Θ} {t = t}} (letOf _ _ _))
                          (_∷ᵉ_ {s = SP} sp (_∷ᵉ_ {s = obs Elm} (evalWith {t = obs Elm} (strmᵗ emptyᵉ) env₀) env₀))

    -- `elemᵛ`'s
    el-body : Val Δ SP → Val Δ Elm
    el-body sp = evalWith (renTm (λ x → x) (λ x → x) (ext∈ (there {x = Elm})) (elemBodyᵛ {t = t}))
                          (_∷ᵉ_ {s = SP} sp (_∷ᵉ_ {s = Elm} (inj₁ tt , inj₁ tt) env₀))

    -- `appendᵗ`'s two reversals of the bookkeeping, under any environment
    rev-rev : ∀ {Θ′ s} (env : Env Δ Θ′) (xs : List (Val Δ s)) R
            → foldVals (revStep {Θ = Θ′} {s = s}) env (foldVals (revStep {Θ = Θ′} {s = s}) env xs []) R ≡ reverseAcc R (reverseAcc [] xs)
    rev-rev {Θ′} {s} env xs R =
      trans (fold-rev {Θ = Θ′} {s = s} env (foldVals (revStep {Θ = Θ′} {s = s}) env xs []) R)
            (cong (reverseAcc R) (fold-rev {Θ = Θ′} {s = s} env xs []))

    -- an element carrying an echo of the emit's instant, beside a lane
    Ev : Ty
    Ev = instEventᵗ uniqᵗ (plainᵗ t)

    K : Val Δ (unitᵗ +ᵗ obs (emitᵗ t)) → List (Val Δ Ev) → Val Δ Elm
    K ln z = inj₂ (z , proj₁ (proj₂ e′) , proj₁ (proj₂ (proj₂ e′)) , proj₂ (proj₂ (proj₂ e′))) , ln

    one-run : ∀ bk ps f ech ln → ps ≡ (ech , ln) ∷ []
            → Σ (List Ty) λ Θ′ → Σ (Tm Δ [] [] Θ′ Elm) λ tm → Σ (Env Δ Θ′) λ ρ′
                → ex-body (bk , ps , f) ≡ (Θ′ , ofᵉ (tm ∷ []) , ρ′) × evalWith tm ρ′ ≡ el-body (bk , ps , f)
    one-run bk _ f (inj₁ _) ln@(inj₁ _) refl =
      _ , _ , _ , refl , trans (cong (K ln) (rev-rev {s = Ev} _ bk _)) (sym (cong (K ln) (rev-rev {s = Ev} _ bk _)))
    one-run bk _ f (inj₁ _) ln@(inj₂ _) refl =
      _ , _ , _ , refl , trans (cong (K ln) (rev-rev {s = Ev} _ bk _)) (sym (cong (K ln) (rev-rev {s = Ev} _ bk _)))
    one-run bk _ f (inj₂ _) ln@(inj₁ _) refl =
      _ , _ , _ , refl , trans (cong (K ln) (rev-rev {s = Ev} _ bk _)) (sym (cong (K ln) (rev-rev {s = Ev} _ bk _)))
    one-run bk _ f (inj₂ _) ln@(inj₂ _) refl =
      _ , _ , _ , refl , trans (cong (K ln) (rev-rev {s = Ev} _ bk _)) (sym (cong (K ln) (rev-rev {s = Ev} _ bk _)))

  explode-one-run : ∀ ech ln → paysOf {a = P} (proj₁ e′) ≡ (ech , ln) ∷ []
                  → Σ (List Ty) λ Θ′ → Σ (Tm Δ [] [] Θ′ Elm) λ tm → Σ (Env Δ Θ′) λ ρ′
                      → applyClo (Θ , explodeᵛ {t = t} , ρ) e′ ≡ (Θ′ , ofᵉ (tm ∷ []) , ρ′)
                        × evalWith tm ρ′ ≡ applyClo (Θ , elemᵛ {t = t} , ρ) e′
  explode-one-run ech ln eq = one-run (proj₁ S) (proj₁ (proj₂ S)) (proj₂ (proj₂ S)) ech ln (trans (proj₁ sv) eq)
    where
    S : Val Δ SP
    S = evalWith (splitEventsᵛ {b = plainᵗ t} (fstᵗ (varᵗ (here refl)))) env₀

    sv = split-eval {a = P} {b = plainᵗ t} (fstᵗ (varᵗ (here refl))) env₀

module PassE {n} {Γ : Ctx n} (κ : Kinds n) where

  open PassQ {Γ = Γ} κ
  open Walkers {Γ = Γ} κ using (Walker)

  module InE {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open InQ {t} {ep} {ei}
    open Kept {Γ = Γ} κ {t} {ep} {ei}

    -- AN EMIT CARRYING ONE VALUE, EXPLODED: one element, the one `elemᵛ`
    -- reads off the same emit, as an `of` of that element alone.  A lone
    -- payload echoes before its own inner, so the run the explode cuts
    -- is one element and no tail
    explode-run-one : ∀ {u Θ ρ} e′ {w} → EmitRel {Γ = Γ} κ (echoᵗ u) e′ (w ∷ [])
                    → Σ (List Ty) λ Θ′ → Σ (Tm (plainᵏ Γ κ) [] [] Θ′ (echoᵗ (emitᵗ u))) λ tm → Σ (Env (plainᵏ Γ κ) Θ′) λ ρ′
                        → applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ , explodeᵛ , ρ) e′ ≡ (Θ′ , ofᵉ (tm ∷ []) , ρ′)
                          × evalWith tm ρ′ ≡ applyClo {s = emitᵗ (echoᵗ u)} {t = echoᵗ (emitᵗ u)} (Θ , elemᵛ , ρ) e′
    explode-run-one {u} {ρ = ρ} e′ {w} r = explode-one-run {t = u} ρ e′ (proj₁ (proj₁ pw)) (proj₂ (proj₁ pw)) (proj₁ (proj₂ pw))
      where
      pw = pw-one (paysOf {Γ = plainᵏ Γ κ} {a = plainᵗ (echoᵗ u)} (proj₁ e′))
                  (subst (λ l → Pointwise (λ x v → V κ (echoᵗ u) (proj₂ x) v) l (w ∷ []))
                         (values-decode {Γ = plainᵏ Γ κ} {a = plainᵗ (echoᵗ u)} (proj₁ e′) (proj₁ (proj₂ e′)) (proj₁ (proj₂ (proj₂ e′))) (proj₂ (proj₂ (proj₂ e′)))) r)

    -- AN EXPLODE'S CARRYING ELEMENT WALKED WHILE ITS MERGE COUNTS IT:
    -- the flattener's fold of the one element runs over the merge's
    -- node holding the inner in flight, the plain outer's walk hands the
    -- value on, and with that node set back to what it held, the stores
    -- and the walk are related where the two leave them.  The carrying
    -- twin of `inner-over`, under a bound on the plain walk: the walk is
    -- the pass's, above the explode, so it is handed in
    IOO-at : ℕ → Set
    IOO-at K = ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂ x₀ y w z}
                 {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {rP r}
             → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
             → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
             → lookupNode mX (EvalSt.nodes stI) ≡ just x₀
             → LiveIf (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (EvalSt.nodes stI)
             → ∀ e′ → EmitRel κ (echoᵗ u) e′ (w ∷ [])
             → (W : thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP)
             → z ≡ applyClo {s = emitᵗ (echoᵗ u)} {t = echoᵗ (emitᵗ u)} (Θ₀ , elemᵛ , ρ₀) e′
             → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (z ∷ []) false sI
                 (record stI { nodes = setNode mX y (EvalSt.nodes stI) }) r
             → sz-thruWalk W < K
             → Σ (After S rP (proj₁ r , proj₁ (proj₂ r) , record (proj₂ (proj₂ r)) { nodes = setNode mX x₀ (EvalSt.nodes (proj₂ (proj₂ r))) })) λ A
                 → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP)))
                     (setNode mX x₀ (EvalSt.nodes (proj₂ (proj₂ r))))
                   × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I (proj₁ r))

    -- the same at every bound below `N`
    IOO< : ℕ → Set
    IOO< N = ∀ {K} → K < N → IOO-at K

    -- A WALKER THE EXPLODE CAN USE: the walk at every former, and the
    -- carrying element's walk, both under `N`.  A record, so that two
    -- modules' copies of it compare by their arguments.
    record Walker′ (N : ℕ) : Set where
      field
        walks : Walker ep ei N
        ones  : IOO< N

    postulate
      -- AN OUTER'S EMIT CARRYING ONE VALUE, EXPLODED AND SUBSCRIBED AT A
      -- MERGE WHOSE OUTER HAS ENDED: `MergeAt` admits the merge done; the
      -- `of` inner's finish would end it again, that end reach the
      -- flattener's wrap, and an idle flattener send a second end down
      -- `q`: two where the plain flattener, its inner ending inside its
      -- subscribe, sends one, and one where `explode-quiet-ended`'s sends
      -- none.  The `LiveIf` on the merge's path rules that out unless a
      -- cut below has spent the path, where it says nothing.
      --
      -- DEAD ROUTE: a wrap that is a no-op on a node already done, rxjs's
      --   idempotent `complete`, makes both leaves true once `od` at `mX`
      --   forces it at `m′`, and moves the falsity to `Simulation.Hot-End`'s
      --   `block-end`: `InputBlock` admits its merge done too, where the
      --   plain slot's second end reaches its share and the impl's wrap now
      --   sends nothing.  Each relation is closed under its own end so a
      --   store holds between an end and the finish that drops its row, so
      --   no evaluator repair alone serves both.
      explode-one-ended : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                          {rP o inst out sched₁ st₁}
                      → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                      → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                      → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                      → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true)
                      → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                      → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP
                      → o ≡ applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′
                      → subscribeInner⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now o sI
                          (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] true) (EvalSt.nodes stI) })
                          (inst , out , sched₁ , st₁)
                      → Σ (After S rP (out , sched₁ , st₁)) λ A
                          → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁)
                              u op m m′ ks (mX ∷ [])
                            × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁) p q
                            × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
                            × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I out)

    -- an arm's plain output, read as an equal one
    after-in : ∀ {sP stP sI stI} {S : St sP stP sI stI} {o o′ rI} {x : Sched Γ × EvalSt ep}
             → o ≡ o′ → After S (o , x) rI → After S (o′ , x) rI
    after-in {rI = rI} e A =
      after (After.store A) (After.keeps A) (After.persists A)
        (subst (λ o → Pointwise (λ x w → V κ t (proj₂ x) w) (readᴵ (proj₁ rI)) (readᴾ o)) e (After.values A))
        (After.grows A)

    -- an inner run at the counter's next node, then a tail sent from where
    -- it left the plain side, as one arm from where the plain side started
    after-fresh : ∀ {sP stP sI stI} {S : St sP stP sI stI} {rP oV x rI}
                → (A : After (mint-impl S) rP (oV , x)) → After (After.store A) ([] , proj₂ rP) rI
                → After S rP ((oV ++ []) ++ proj₁ rI , proj₂ rI)
    after-fresh {rP = rP} {oV = oV} A T =
      after-in (++-identityʳ (proj₁ rP)) (after-out (cong (_++ _) (sym (++-identityʳ oV))) (unmintI A ⨾ T))

    -- and what it sends at an instant is the inner's, the tail sending none
    out-fresh : ∀ {sP stP sI stI} {S : St sP stP sI stI} {I y oV rI}
              → Out I oV → After S ([] , y) rI → Out I ((oV ++ []) ++ proj₁ rI)
    out-fresh {oV = oV} {rI = rI} o T =
      out-++ (oV ++ []) (proj₁ rI) (subst (Out _) (sym (++-identityʳ oV)) o) (nil-all (After.values T))

    -- THE EXPLODE'S INNER ENDED, ITS ELEMENT WALKED: the merge back at no
    -- inner, the empty group its finish leaves folds the tail, and the
    -- two runs are one arm from where the plain outer's walk began
    explode-one-close : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                          {e′ : Val (plainᵏ Γ κ) (emitᵗ (echoᵗ u))} {rP oV sJ stJ r₂}
                      → (A : After (mint-impl S) rP (oV , sJ , stJ))
                      → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes stJ)
                      → (∀ {I} → DelAt {echoᵗ u} I e′ → Out I oV)
                      → Sound p (proj₁ (proj₂ rP)) (proj₂ (proj₂ rP))
                      → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sJ stJ
                      → lookupNode mX (EvalSt.nodes stJ) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] false)
                      → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) [] false sJ stJ r₂
                      → Σ (After S rP ((oV ++ []) ++ proj₁ r₂ , proj₂ r₂)) λ B
                          → Flattener {Γ = Γ} κ (Store.π (After.store B)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r₂)))
                              u op m m′ ks (mX ∷ [])
                            × PathRel κ (Store.π (After.store B)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r₂))) p q
                            × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ r₂))) u mX
                            × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I ((oV ++ []) ++ proj₁ r₂))
    explode-one-close S {op = op} {oV = oV} A W o sp c lk F =
      let (T , fl , r , x) = explode-tail (After.store A) {op = op} sp c (proj₁ W) (proj₂ W) (false , lk) F
      in after-fresh {oV = oV} A T , fl , r , x , λ d → out-fresh {oV = oV} (o d) T

    -- the inner's finish read at the node it set, so its arms match
    -- with no with-abstraction over the subscribe's context
    explode-one-drain : ∀ {N} (io : IOO< N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                          {Θ′ ρ′} {tm : Tm (plainᵏ Γ κ) [] [] Θ′ (echoᵗ (emitᵗ u))} {w rP r₁ out₂ sched₂ st₂}
                      → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                      → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                      → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] false)
                      → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                      → ∀ e′ → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                      → (W : thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP)
                      → suc (sz-thruWalk W) < N
                      → evalWith tm ρ′ ≡ applyClo {s = emitᵗ (echoᵗ u)} {t = echoᵗ (emitᵗ u)} (Θ₀ , elemᵛ , ρ₀) e′
                      → innerFinish⇓ mergeAllᵒ mX (nodeCt sI) (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now (evalWith tm ρ′ ∷ [])
                          (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) })
                          (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] false) (EvalSt.nodes stI) })
                          (just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] false)) r₁
                      → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (proj₁ (proj₂ r₁)) (proj₁ (proj₂ (proj₂ r₁)))
                          (proj₁ (proj₂ (proj₂ (proj₂ r₁)))) (proj₂ (proj₂ (proj₂ (proj₂ r₁)))) (out₂ , sched₂ , st₂)
                      → Σ (After S rP (proj₁ r₁ ++ out₂ , sched₂ , st₂)) λ A
                          → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₂)
                              u op m m′ ks (mX ∷ [])
                            × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₂) p q
                            × MergeAt {Γ = Γ} κ (EvalSt.nodes st₂) u mX
                            × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I (proj₁ r₁ ++ out₂))
    explode-one-drain _ S cp ci fl r lX lv e′ rel W _ ez (finish-nil e) _ = ⊥-elim (t≢f (trans (sym (usable-self _)) e))
    explode-one-drain io {sI = sI} {stI = stI} S {u = u} {op = op} {mX = mX} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {rP = rP} cp ci fl r lX lv e′ rel W lt ez (finish-all-drain {outV = outV} {st₁ = st₁′} fd drain-spent) F₂ =
      let ci′ = sub-on (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₁ ci) , sub-ot (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (keeps-refl _ _) (proj₂ ci)
          (A₁ , W₁ , o₁) = io lt (mint-impl S) {u = u} {Θ₀ = Θ₀} {ρ₀ = ρ₀} cp ci′ (fl , r) lX (live-if-under _ _ lv) e′ rel W ez fd (n<1+n _)
          c₁ = fold-clear fd (sub-ot (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (keeps-refl _ _) (proj₂ ci)) refl
                 (sub-on (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (proj₁ ci) , sub-ot (λ r∈ → r∈) (n≤1+n (nodeCt sI)) (keeps-refl _ _) (proj₂ ci))
      in explode-one-close S {u = u} {op = op} {mX = mX} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {e′ = e′} {oV = outV} A₁ W₁ o₁ (proj₂ (walk-clear W cp))
           (sub-on (λ r∈ → r∈) ≤-refl (proj₁ c₁) , sub-ot (λ r∈ → r∈) ≤-refl (keeps-refl _ _) (proj₂ c₁))
           (lookup-set mX _ (EvalSt.nodes st₁′)) F₂

    -- THE EXPLODE'S INNER, ITS ONE CARRYING ELEMENT IN HAND: the
    -- counter's next node, so no row keeps it alive and it finishes at
    -- once; its element walks the flattener beside the plain outer's
    -- walk, the merge's count falls back, and the empty group the finish
    -- leaves folds the tail
    explode-one-fresh : ∀ {N} (io : IOO< N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                          {Θ′ ρ′} {tm : Tm (plainᵏ Γ κ) [] [] Θ′ (echoᵗ (emitᵗ u))} {w rP o out sched₁ st₁}
                      → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                      → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                      → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] false)
                      → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                      → ∀ e′ → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                      → (W : thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP)
                      → suc (sz-thruWalk W) < N
                      → evalWith tm ρ′ ≡ applyClo {s = emitᵗ (echoᵗ u)} {t = echoᵗ (emitᵗ u)} (Θ₀ , elemᵛ , ρ₀) e′
                      → o ≡ (Θ′ , ofᵉ (tm ∷ []) , ρ′)
                      → subscribeE⇓ o (from-inner mergeAllᵒ mX (nodeCt sI) ↠[ ≤-refl ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) now
                          (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) })
                          (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 1 [] false) (EvalSt.nodes stI) })
                          (out , sched₁ , st₁)
                      → Σ (After S rP (out , sched₁ , st₁)) λ A
                          → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁)
                              u op m m′ ks (mX ∷ [])
                            × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁) p q
                            × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
                            × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I out)
    explode-one-fresh _ S cp ci fl r lX lv e′ rel W _ ez refl (subs-of (fold-step (step-from-inner (react-alive al)) _)) =
      ⊥-elim (t≢f (trans (sym al) (fresh-dead (Store.ruleI S))))
    explode-one-fresh io {sI = sI} {stI = stI} S {u = u} {op = op} {mX = mX} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ′ = Θ′} {ρ′ = ρ′} {tm = tm} {rP = rP} cp ci fl r lX lv e′ rel W lt ez refl
                      (subs-of (fold-step (step-from-inner (react-dead _ F′)) F₂)) =
      explode-one-drain io S {u = u} {op = op} {mX = mX} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ′ = Θ′} {ρ′ = ρ′} {tm = tm} {rP = rP} cp ci fl r lX lv e′ rel W lt ez
        (finish-at (lookup-set mX _ (EvalSt.nodes stI)) F′) F₂

    -- `explode-one-sub` over its subscribe at a value only EQUAL to the
    -- explode's application, so no clause unifies under that application
    explode-one-at : ∀ {N} (io : IOO< N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                        {rP lim a qs od o inst out sched₁ st₁}
                    → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                    → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → (mg : MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX)
                    → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                    → just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] (proj₁ mg)) ≡ just (mergeAll-st lim a qs od)
                    → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                    → (W : thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP)
                    → suc (sz-thruWalk W) < N
                    → o ≡ applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′
                    → subscribeInner⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now o sI
                        (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} lim (suc a) qs od) (EvalSt.nodes stI) })
                        (inst , out , sched₁ , st₁)
                    → Σ (After S rP (out , sched₁ , st₁)) λ A
                        → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁)
                            u op m m′ ks (mX ∷ [])
                          × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁) p q
                          × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
                          × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I out)
    explode-one-at _ S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r (true , lX) lv refl e′ rel W _ ho c =
      explode-one-ended S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r lv lX e′ rel W ho c
    explode-one-at io S {u = u} {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r (false , lX) lv refl e′ rel W lt ho (inner refl sub) =
      let (_ , _ , _ , eq , ez) = explode-run-one {u = u} {Θ = Θ₀} {ρ = ρ₀} e′ rel
      in explode-one-fresh io S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r lX lv e′ rel W lt ez (trans ho eq) sub

    -- AN OUTER'S EMIT CARRYING ONE VALUE, EXPLODED, SUBSCRIBED: the
    -- impl's merge takes its run of elements as an inner, they walk into
    -- the flattener where the plain outer's walk hands the value's
    -- events on, and the merge stays unbounded at the echo's type.  What
    -- it sends, it sends at the emit's own delivery: the echo crosses
    -- the restamp first and sets its cell to that delivery
    explode-one-sub : ∀ {N} (io : IOO< N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                        {rP lim a qs od inst out sched₁ st₁}
                    → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                    → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                    → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                    → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} lim a qs od)
                    → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                    → (W : thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP)
                    → suc (sz-thruWalk W) < N
                    → subscribeInner⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                        (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI
                        (record stI { nodes = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} lim (suc a) qs od) (EvalSt.nodes stI) })
                        (inst , out , sched₁ , st₁)
                    → Σ (After S rP (out , sched₁ , st₁)) λ A
                        → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁)
                            u op m m′ ks (mX ∷ [])
                          × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes st₁) p q
                          × MergeAt {Γ = Γ} κ (EvalSt.nodes st₁) u mX
                          × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I out)
    explode-one-sub io S {u = u} {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r mg lv l e′ rel W lt c =
      explode-one-at io S {u = u} {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r mg lv (trans (sym (proj₂ mg)) l) e′ rel W lt refl c
