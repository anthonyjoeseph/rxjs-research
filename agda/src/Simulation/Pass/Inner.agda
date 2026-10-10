------------------------------------------------------------------
-- AN INNER'S ARMS: the pass's type, the leaves per plain frame, and
-- an inner's step by the rule its react takes, over the quiet arms
------------------------------------------------------------------
module Simulation.Pass.Inner where

open import Data.Bool    using (T; true; false; not; _∧_; _∨_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; suc; pred; _+_; _≤_; _<_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; pred[n]≤n)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec     using (lookup)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong; cong₂)

open import Rx.Exp       using (Ctx; Closed; Val; Ty; _≟ᵗ_; mergeᶠ; switchᶠ; exhaustᶠ; uniqᵗ; obs; applyClo; Tm; varᵗ; unit̂; pairᵗ;
  inlᵗ; inrᵗ; sndᵗ)
open import Rx.Evaluator using (EvalSt; NodeId; shareSpend; shareDying; Path; _↠[_]_; scan-f; map-f; thru-outer; from-inner;
  mergeAllᵒ; lookupNode; echoᵗ; thruEvents; thruWrap; switchᵒ; exhaustᵒ; shareFinish;
  aliveThroughᶠ; Sched; pathHasNode; NodeState; mergeAll-st; cell-st; take-st; switch-st;
  exhaust-st; batchSync-st; setNode; drainSt; hasRoom)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-step; stepFrame⇓; step-map; step-scan; step-thru-outer;
  step-from-inner; react-false; react-alive; react-dead; innerFinish⇓; finish-switch-clear;
  finish-exhaust-clear; finish-nil; finish-all-drain; mergeAllDrain⇓; drain-spent; drain-nil;
  drain-no-room; drain-room; subscribeInner⇓; thruWalk⇓; thruConsume⇓; walk-nil; walk-echo;
  walk-cons; consume-all-sub; consume-all-enqueue; consume-all-nil)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ; hotᵏ; sharedᵏ)
open import SExp.Elaborate using (restampᵛ; subscribeᵛ; deliveryᵛ; flatStepᵛ; explodeᵛ; elemᵛ)
open import Simulation.Stores using (Inv; EmitRel; Flattener; FlatNodes; switch~; exhaust~; merge~; ObsRel; V; PathRel; inner~;
  deferInner~; []; _∷_; Store; Partners; RegRel; RowRel; MachRow; mach; Spent; dlvᵇ; dyingᵇ;
  MergeAt; outerDoneᵇ; live-mono; live-set; od-back; LiveIf; LiveFor; live-for; live-if-drop; live-if-set)
open import Simulation.Cut using (module At; module Third)
open import Simulation.Walks using (module Walkers)
open import Simulation.Size using (sz-foldPath; sz-mergeAllDrain; sz-innerFinish; sz-l; sz-r)
open import Simulation.After using (module Kept; readᴾ; readᴵ-++)
open import Simulation.Take using (module Takes)
open import Simulation.Scan using (module Scans)
open import Simulation.Arm using (Out; out-quiet; out-++; Clear; missed; fold-unmoved; on-drop; unthru; step-clear; consume-clear; reclear; thru; NoBatch; rel-unbatched; Gone; gone-nodes)
open import Simulation.Sweep using (t≢f)
open import Rx.Evaluator.Reducible.Support using (Sound; sub-ot; drop-ot; head-on; self-node; off-path; ∨-Tˡ; ∨-Tʳ; distinct; fresh-path)
open import Rx.Evaluator.Reducible.Dead-Kept using (fold-dead; off-T)
open import Rx.Evaluator.Freshness using (lookup-set; set-above)
open import Simulation.Write using (module HopWrite; apart)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept; fold-kept; Thru; thruWalk-rule; subscribeInner-rule)
open import Simulation.Pass.Quiet using (module PassQ; cur-here; cur-there; delivered; delivered-arr; dying; dying-arr; tail-of;
  usable-self; unusable; no-queue; pw-null)

-- A WALK OVER TWO RUNS OF EVENTS IS THE FIRST WALK, THEN THE SECOND
-- from where it left the state
walk-split : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {w lo op nid} {κ : Path Δ lo w u} {now} xs ys {sched st r}
           → thruWalk⇓ {e = e} op nid κ now (xs ++ ys) sched st r
           → Σ _ λ r₁ → thruWalk⇓ op nid κ now xs sched st r₁
               × Σ _ λ r₂ → thruWalk⇓ op nid κ now ys (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) r₂
               × r ≡ (proj₁ r₁ ++ proj₁ r₂ , proj₂ r₂)
walk-split [] ys W = _ , walk-nil , _ , W , refl
walk-split (inj₁ v ∷ xs) ys (walk-echo {out₁ = o} F W) with walk-split xs ys W
... | r₁ , W₁ , r₂ , W₂ , refl = _ , walk-echo F W₁ , _ , W₂ , cong (_, proj₂ r₂) (sym (++-assoc o (proj₁ r₁) (proj₁ r₂)))
walk-split (inj₂ x ∷ xs) ys (walk-cons {out₁ = o} C W) with walk-split xs ys W
... | r₁ , W₁ , r₂ , W₂ , refl = _ , walk-cons C W₁ , _ , W₂ , cong (_, proj₂ r₂) (sym (++-assoc o (proj₁ r₁) (proj₁ r₂)))

-- an echo's events, ahead of the rest
events-cons : ∀ {m} {Δ : Ctx m} {u} (x : Val Δ (echoᵗ u)) xs → thruEvents (x ∷ xs) ≡ thruEvents (x ∷ []) ++ thruEvents xs
events-cons (inj₁ _ , inj₁ _) xs = refl
events-cons (inj₁ _ , inj₂ _) xs = refl
events-cons (inj₂ _ , inj₁ _) xs = refl
events-cons (inj₂ _ , inj₂ _) xs = refl

walk-head : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {w lo op nid} {κ : Path Δ lo w u} {now} (x : Val Δ (echoᵗ w)) xs {sched st r}
          → thruWalk⇓ {e = e} op nid κ now (thruEvents (x ∷ xs)) sched st r
          → Σ _ λ r₁ → thruWalk⇓ op nid κ now (thruEvents (x ∷ [])) sched st r₁
              × Σ _ λ r₂ → thruWalk⇓ op nid κ now (thruEvents xs) (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) r₂
              × r ≡ (proj₁ r₁ ++ proj₁ r₂ , proj₂ r₂)
walk-head x xs W = walk-split (thruEvents (x ∷ [])) (thruEvents xs) (subst (λ ys → thruWalk⇓ _ _ _ _ ys _ _ _) (events-cons x xs) W)

-- a walk through a flattener keeps its node off the path below it
walk-clear : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo w} {k} {κ : Path Δ lo w u} {op now xs}
               {sched sched′ st st′ out}
           → thruWalk⇓ {e = e} op k κ now xs sched st (out , sched′ , st′)
           → Clear k κ sched st → Clear k κ sched′ st′
walk-clear {e = e} {k = k} {κ = κ} d c = reclear {π = Thru {e = e} k κ} refl c (thruWalk-rule d (thru c))

-- a one-lane merge's count drops to none
pred-one : ∀ {a} → a ≤ 1 → (pred a ≡ᵇ 0) ≡ true
pred-one z≤n       = refl
pred-one (s≤s z≤n) = refl

-- a fold at an end known otherwise
fin-at : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo w now} {p : Path Δ lo w u} {vals c c′ sched st r}
       → c ≡ c′ → foldPath⇓ {e = e} now p vals c sched st r → foldPath⇓ now p vals c′ sched st r
fin-at refl f = f

-- and so does a subscribe through it, from the node it writes
sub-clear : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo w} {k} {κ : Path Δ lo w u} {op now o y}
              {sched sched′ st st′ inst out}
          → subscribeInner⇓ {e = e} op k κ now o sched (record st { nodes = setNode k y (EvalSt.nodes st) }) (inst , out , sched′ , st′)
          → Clear k κ sched st → Clear k κ sched′ st′
sub-clear {e = e} {k = k} {κ = κ} {y = y} {sched = sched} {st = st} d c = unthru (subscribeInner-rule d so (Thru {e = e} k κ) so (λ _ _ _ → refl))
  where
  so : Sound (Thru {e = e} k κ) sched (record st { nodes = setNode k y (EvalSt.nodes st) })
  so = sub-ot (λ r∈ → r∈) ≤-refl (thru c)

-- a merge's node, as a drain re-reads it
drain-self : ∀ {m} {Δ : Ctx m} u {l a od} {q : List (Val Δ (obs u))} → drainSt {Γ = Δ} u (just (mergeAll-st {t = u} l a q od)) ≡ (l , a , q , od)
drain-self u with u ≟ᵗ u
... | yes refl = refl
... | no ¬e    = ⊥-elim (¬e refl)

-- and the end it re-reads is the node's own
drain-od : ∀ {m} {Δ : Ctx m} (s : Ty) (x : Maybe (NodeState Δ)) {l a q od₂} → drainSt s x ≡ (l , a , q , od₂) → outerDoneᵇ x ≡ false → od₂ ≡ false
drain-od s (just (mergeAll-st {w} lim act q od)) e h with w ≟ᵗ s
... | yes refl = trans (cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)) h
... | no _     = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)
drain-od s nothing e _ = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)
drain-od s (just (cell-st _)) e _ = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)
drain-od s (just (take-st _)) e _ = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)
drain-od s (just (switch-st _ _)) e _ = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)
drain-od s (just (exhaust-st _ _)) e _ = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)
drain-od s (just (batchSync-st _ _ _)) e _ = cong (λ z → proj₂ (proj₂ (proj₂ z))) (sym e)

postulate
  -- A QUIET FOLD RIDES PAST A WRITE OFF ITS PATH: run from a store with
  -- that node written, it is the fold from the store without it, the
  -- write laid over where that fold leaves the store.  Every frame
  -- handed nothing writes only its own node, back to what it held.
  --
  -- TWIN: `quiet-fold` -- the same induction over a bracket-free path,
  --   a clause per frame `step-quiet` reads.
  fold-past : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} {κ : Path Δ lo s t} {k y now sched st r}
            → NoBatch κ → Clear k κ sched st
            → foldPath⇓ {e = e} now κ [] false sched (record st { nodes = setNode k y (EvalSt.nodes st) }) r
            → Σ _ λ r′ → foldPath⇓ now κ [] false sched st r′
                × r ≡ (proj₁ r′ , proj₁ (proj₂ r′) , record (proj₂ (proj₂ r′)) { nodes = setNode k y (EvalSt.nodes (proj₂ (proj₂ r′))) })

module PassI {n} {Γ : Ctx n} (κ : Kinds n) where

  open PassQ {Γ = Γ} κ public
  open Walkers {Γ = Γ} κ using (Walker)
  open Takes {Γ = Γ} κ using (module While)
  open Scans {Γ = Γ} κ using (module Cells)

  module InI {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open InQ {t} {ep} {ei} public
    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open While {t} {ep} {ei} using (takeWhile-arm)
    open Cells {t} {ep} {ei} using (scan-arm)

    -- TWO RELATED PATHS KEEP THE PASS, AND ARE RELATED AGAIN WHERE IT
    -- LEAVES THEM: a flattener's outer folds its tail once per emit.  The
    -- plain fold sits below `N`, the bound the walker it is handed walks
    -- under.
    Pass : ∀ {lo lo′ s} → ℕ → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Pass N p q =
      ∀ {now vs es fin sP stP sI stI rP rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es vs
      → Sound p sP stP → Sound q sI stI → (fin ≡ true → Gone q stI) → LiveFor es q (EvalSt.nodes stI)
      → (dP : foldPath⇓ now p vs fin sP stP rP) → foldPath⇓ now q es fin sI stI rI
      → sz-foldPath dP < N
      → Σ (After S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
          × (∀ {I} → Dlv I fin es → Out I (proj₁ rI))

    -- THE PASS AT ONE PLAIN FOLD: what a finish hands its arm for the
    -- fold it runs down its own tail, so the pass recurses on that fold
    PassAt : ∀ {lo lo′ s now vs fin sP rP} {stP : EvalSt ep} {p : Path Γ lo s t} → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)
           → foldPath⇓ now p vs fin sP stP rP → Set
    PassAt {now = now} {vs = vs} {fin = fin} {sP = sP} {rP = rP} {stP = stP} {p = p} q _ =
      ∀ {es sI stI rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es vs
      → Sound p sP stP → Sound q sI stI → (fin ≡ true → Gone q stI) → LiveFor es q (EvalSt.nodes stI)
      → foldPath⇓ now q es fin sI stI rI
      → Σ (After S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    -- only a merge's finish folds its tail
    TailAt : ∀ {lo lo′ s op m j now vs sP mx r} {stP : EvalSt ep} {p : Path Γ lo s t} → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)
           → innerFinish⇓ op m j p now vs sP stP mx r → Set
    TailAt q (finish-all-drain fP _) = PassAt q fP
    TailAt q (finish-switch-clear _) = ⊤
    TailAt q finish-exhaust-clear    = ⊤
    TailAt q (finish-nil _)          = ⊤


    -- ONE LEAF PER PLAIN FRAME A CONSTRUCTOR STARTS WITH.  An outer's
    -- two constructors and an inner's three are split once their arm is
    -- the riskiest.
    postulate
      -- A SHARE CLOSED ON BOTH SIDES, before its end is delivered
      share-spend  : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} → lookup κ i ≡ sharedᵏ
                   → After S ([] , sP , shareSpend i stP) ([] , sI , shareSpend (n ↑ʳ i) stI)
      -- A SHARE'S READERS DROPPED ON BOTH SIDES, once its end is delivered
      share-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} → lookup κ i ≡ sharedᵏ
                   → After S ([] , proj₂ (shareFinish i true ([] , sP , stP))) ([] , proj₂ (shareFinish (n ↑ʳ i) true ([] , sI , stI)))
      -- AN OUTER'S EMIT CARRYING ONE VALUE, EXPLODED, SUBSCRIBED: the
      -- impl's merge takes its run of elements as an inner, they walk into
      -- the flattener where the plain outer's walk hands the value's
      -- events on, and the merge stays unbounded at the echo's type.  What
      -- it sends, it sends at the emit's own delivery: the echo crosses
      -- the restamp first and sets its cell to that delivery
      --
      -- OPEN WHERE THE MERGE'S PATH IS SPENT.  `MergeAt` admits the merge
      -- done; an ended merge would let the `of` inner's finish end it
      -- again, that end reach the flattener's wrap, and an idle flattener
      -- send a second end down `q`: two where the plain flattener, its
      -- inner ending inside its subscribe, sends one, and one where
      -- `explode-quiet-sub`'s sends none.  The `LiveIf` on the merge's path
      -- rules that out unless a cut below has spent the path, where it says
      -- nothing.
      --
      -- DEAD ROUTE: a wrap that is a no-op on a node already done, rxjs's
      --   idempotent `complete`, makes both leaves true once `od` at `mX`
      --   forces it at `m′`, and moves the falsity to `Simulation.Hot-End`'s
      --   `block-end`: `InputBlock` admits its merge done too, where the
      --   plain slot's second end reaches its share and the impl's wrap now
      --   sends nothing.  Each relation is closed under its own end so a
      --   store holds between an end and the finish that drops its row, so
      --   no evaluator repair alone serves both.
      -- DEAD ROUTE: walking the inner's element into the flattener over the
      --   pass's own steps needs a `Store` while the merge counts that
      --   inner, where `MergeAt` reads count zero; `explode-quiet-sub`
      --   meets the same wall.
      explode-one-sub : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                          {rP lim a qs od inst out sched₁ st₁}
                      → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                      → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                      → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                      → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                      → lookupNode mX (EvalSt.nodes stI) ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} lim a qs od)
                      → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                      → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP
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
      -- AN OUTER'S GROUP ALL DELIVERED AT ONE INSTANT, ITS ELEMENTS
      -- WALKED, SENDS AT IT: each element's echo crosses the restamp, so
      -- its lane is subscribed at that delivery.  The route is through the
      -- walk's echo and lane, a consume carrying the instant its echo set.
      --
      elem-out : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es vs rI}
               → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
               → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → Carries {echoᵗ u} es vs
               → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                   (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
               → ∀ {I} → All (DelAt {echoᵗ u} I) es → Out I (proj₁ rI)
    -- A DEFERRED BODY'S THREE COUNTS WRITTEN: the plain merge's and the
    -- impl's hop node, alike, and the marker merge's, each one lower.  π
    -- pairs the marker once and the hop's two nodes only with each other,
    -- so a row's facts at the three are the written ones or are kept
    defer-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₃ u nid nid′ j j′ m2 j2 a b}
                    {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                → (nid , nid′ ∷ []) ∈ Store.π S → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ Store.π S
                → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing a [] true)
                → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
                → lookupNode m2 (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing b [] true)
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → Σ (After S ([] , sP , record stP { nodes = setNode nid (mergeAll-st {t = u} nothing (pred a) [] true) (EvalSt.nodes stP) })
                             ([] , sI , record stI { nodes = setNode nid′ (mergeAll-st {t = emitᵗ u} nothing (pred a) [] true)
                                                               (setNode m2 (mergeAll-st {t = emitᵗ u} nothing (pred b) [] true) (EvalSt.nodes stI)) }))
                    λ A → PathRel κ (Store.π (After.store A))
                            (setNode nid (mergeAll-st {t = u} nothing (pred a) [] true) (EvalSt.nodes stP))
                            (setNode nid′ (mergeAll-st {t = emitᵗ u} nothing (pred a) [] true)
                              (setNode m2 (mergeAll-st {t = emitᵗ u} nothing (pred b) [] true) (EvalSt.nodes stI))) p q
    defer-write {sP} {stP} {sI} {stI} S e₁ e₂ lP lI l2 r =
      node-write S W.M.moved (live-mono {st = stI} {st′ = record stI { nodes = W.NI′ }} (λ r∈ → r∈) (λ _ _ h → h)
            (λ {_} {_} {q} l → live-set {q = q} _ W.yI W.NI₂
                (λ h → trans (sym (cong outerDoneᵇ lI)) (od-back _ _ W.y2 (EvalSt.nodes stI) (λ ()) h))
                (live-set {q = q} _ W.y2 (EvalSt.nodes stI) (λ h → trans (sym (cong outerDoneᵇ l2)) h) l))
            (Inv.live-outer (Store.inv S)))
      , W.M.pathW r
      where
      module W = HopWrite κ (Store.π-keys S) (Store.π-vals S) {t = t} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} e₁ e₂ lP lI l2

    -- AN INNER NO LIVE CHAIN RUNS THROUGH STAYS SO while the group it
    -- left folds down the tail below it: its node is off the tail, which
    -- the path's distinctness says, and below the counter, which its
    -- freshness says, so every row the fold registers misses it
    still-dead : ∀ {sP} {stP : EvalSt ep} {now lo ℓ u op m j} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {vs rP}
               → Sound (from-inner op m j ↠[ h ] p) sP stP
               → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
               → foldPath⇓ now p vs false sP stP rP
               → any (aliveThroughᶠ j (proj₂ (proj₂ rP))) (EvalSt.registry (proj₂ (proj₂ rP))) ≡ false
    still-dead {m = m} {j} {p = p} so dd f =
      fold-dead j f (off-T (λ hp → proj₁ (distinct so) j on hp)) (fresh-path so j (∨-Tˡ {b = pathHasNode j p} on)) dd
      where on = ∨-Tʳ {a = m ≡ᵇ j} (self-node j [])

    -- A DEAD DEFERRED BODY'S END, ONCE ITS GROUP HAS FOLDED: the plain
    -- merge's count falls, against the hop's marker merge's, the empty
    -- group the marker hands the hop's node, and that node's own fall.
    -- The fold runs below both impl nodes, so the marker's write rides
    -- past it and the three counts fall together
    defer-end : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀ a b}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {rQ}
              → (nid , nid′ ∷ []) ∈ Store.π S → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ Store.π S
              → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing a [] true)
              → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
              → lookupNode m2 (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing b [] true)
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
              → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                       (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                        (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
              → foldPath⇓ now q [] false sI
                  (record stI { nodes = setNode m2 (mergeAll-st {t = emitᵗ u} nothing (pred b) [] true) (EvalSt.nodes stI) }) rQ
              → Σ (After S ([] , sP , record stP { nodes = setNode nid (mergeAll-st {t = u} nothing (pred a) [] true) (EvalSt.nodes stP) })
                           (proj₁ rQ ++ [] , proj₁ (proj₂ rQ)
                           , record (proj₂ (proj₂ rQ))
                               { nodes = setNode nid′ (mergeAll-st {t = emitᵗ u} nothing (pred a) [] true) (EvalSt.nodes (proj₂ (proj₂ rQ))) }))
                  λ A → PathRel κ (Store.π (After.store A))
                          (setNode nid (mergeAll-st {t = u} nothing (pred a) [] true) (EvalSt.nodes stP))
                          (setNode nid′ (mergeAll-st {t = emitᵗ u} nothing (pred a) [] true) (EvalSt.nodes (proj₂ (proj₂ rQ)))) p q
    defer-end S {nid′ = nid′} {j′ = j′} {m2 = m2} {j2} ip₁ ip₂ lP lI l2 pr sp si dq
      with fold-past (rel-unbatched pr) (on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) ,
                                         drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))) dq
    ... | _ , d′ , refl
      with quiet-pass S pr [] refl (drop-ot _ _ _ sp) (drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))) (inj₁ refl) d′
    ...   | A₁ , pr₁
      with defer-write (After.store A₁) (After.grows A₁ ip₁) (After.grows A₁ ip₂) lP
             (trans (fold-unmoved d′ (head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) (drop-ot _ _ _ (drop-ot _ _ _ si)) ,
                                      drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si)))) lI)
             (trans (fold-unmoved d′ (on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) ,
                                      drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si)))) l2)
             pr₁
    ...     | A₂ , pr₂ = A₁ ⨾ A₂ , pr₂

    -- A PAIR OF NODES EVERY PAIR OF ROWS NAMES ALIKE, AND THE IMPL'S OWN
    -- ROWS NEVER THE IMPL ONE, HAS A CHAIN RUNNING THROUGH IT ON BOTH SIDES
    -- OR ON NEITHER: neither row of a pair is cancelled, and the two are
    -- delivered and dying alike
    alive-by : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′}
             → (∀ {x x′} → RowRel κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) x x′
                         → pathHasNode j (proj₂ (proj₂ (proj₂ x))) ≡ pathHasNode j′ (proj₂ (proj₂ (proj₂ x′))))
             → (∀ {x′} → MachRow κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) x′
                         → pathHasNode j′ (proj₂ (proj₂ (proj₂ x′))) ≡ false)
             → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j′ stI) (EvalSt.registry stI)
    alive-by {sP} {stP} {sI} {stI} S {j} {j′} rc mc = go rows (proj₁ uncut) (proj₂ uncut) dlv-alike dying-alike
      where
        open Store S

        off : ∀ {a} b c → a ≡ false → (a ∧ b) ∨ c ≡ c
        off b c refl = refl

        go : ∀ {rs rs′} (q : RegRel κ π {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) rs rs′)
           → All (λ r → any (_≡ᵇ proj₁ r) (EvalSt.cancelled stP) ≡ false) rs
           → All (λ r → any (_≡ᵇ proj₁ r) (EvalSt.cancelled stI) ≡ false) rs′
           → Spent κ π (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) q (dlvᵇ stP) (dlvᵇ stI)
           → Spent κ π (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI) q (dyingᵇ stP) (dyingᵇ stI)
           → any (aliveThroughᶠ j stP) rs ≡ any (aliveThroughᶠ j′ stI) rs′
        go [] _ _ _ _ = refl
        go (rr ∷ q) (u ∷ us) (u′ ∷ us′) (d , ds) (y , ys) =
          cong₂ _∨_ (cong₂ _∧_ (rc rr) (cong₂ _∧_ (cong not (trans u (sym u′))) (cong₂ _∨_ (cong not y) (cong not d))))
                    (go q us us′ ds ys)
        go (mach m q) us (_ ∷ us′) ds ys = trans (go q us us′ ds ys) (sym (off _ _ (mc m)))

    -- AN INNER HAS A CHAIN RUNNING THROUGH IT ON THE PLAIN SIDE EXACTLY
    -- WHEN ITS PAIR DOES ON THE IMPL'S: a pair of rows names the pair of
    -- nodes alike, and the impl's own rows name no paired node
    inner-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′ cs}
                → (j , j′ ∷ cs) ∈ Store.π S
                → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j′ stI) (EvalSt.registry stI)
    inner-alive S ce = alive-by S (λ rr → C.row-cut rr) (λ m → C.mach-cut m)
      where module C = At {Γ = Γ} κ (Store.π-keys S) (Store.π-vals S) ce (here refl)

    -- A DEFERRED BODY'S INNER IS LIVE ON THE PLAIN SIDE EXACTLY WHEN THE
    -- HOP'S MARKER MERGE'S INNER IS ON THE IMPL'S: that inner is the third
    -- of the run `π` pairs the body's inner with, and the marker merge
    -- being a merge tells the run from an exploding flattener's
    defer-alive : ∀ {sP stP sI stI} (S : St sP stP sI stI) {j j′ m2 j2 u a}
                → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ Store.π S
                → lookupNode m2 (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
                → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ any (aliveThroughᶠ j2 stI) (EvalSt.registry stI)
    defer-alive {stI = stI} S {m2 = m2} ce l2 = alive-by S (λ rr → D.row-cut ly rr) (λ m → D.mach-cut m)
      where
        module D = Third {Γ = Γ} κ (Store.π-keys S) (Store.π-vals S) ce
        ly : ∀ {w} {v : Val (plainᵏ Γ κ) w} → lookupNode m2 (EvalSt.nodes stI) ≢ just (cell-st v)
        ly lk with trans (sym l2) lk
        ... | ()

    -- a scan's step sends nothing itself
    scan-quiet : ∀ {lo s u fn nid} {q : Path (plainᵏ Γ κ) lo u (emitᵗ t)} {now} {vals : List (Val (plainᵏ Γ κ) s)} {fin sched}
                   {st : EvalSt ei} {o r I}
               → stepFrame⇓ now (scan-f fn nid) q vals fin sched st (o , r) → Out I o
    scan-quiet step-scan = out-quiet [] refl

    -- AN INNER LEFT OPEN: the impl's lets the group past as the plain one
    -- does, its restamp moves the cell alone, and the tails are related
    inner-on : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {stP₁ stI₁ vs es fin rI}
             → (A₀ : After S ([] , sP , stP₁) ([] , sI , stI₁))
             → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ (Store.π (After.store A₀)) {t} (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) u op m m′ ks xs)
               × (j , j′ ∷ []) ∈ Store.π (After.store A₀) × PathRel κ (Store.π (After.store A₀)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
             → Carries es vs
             → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP₁
             → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI₁
             → (fin ≡ true → Gone (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) stI₁)
             → LiveFor es (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) (EvalSt.nodes stI₁)
             → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es fin sI stI₁ rI
             → Arm S now [] sP stP₁ p vs fin
                 (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                    (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) (λ I → Dlv I fin es) rI
    inner-on {op = op} {m = m} {m′} {ks = ks} {j = j} {j′} {Θ₁} {ρ₁} {Θ₂} {ρ₂} {h₂ = h₂} {h₃} {q = q} {stP₁ = stP₁} A₀ ((xs , f) , ip , pr) b sp si g lv (fold-step d₁ (fold-step step-map dq))
      with restamp-echo (After.store A₀) f pr b d₁
    ... | A , f′ , pr′ , c′ , refl , dl =
      arm (A₀ ⨾ A) pr′ c′ (proj₂ (proj₁ cI)) (λ e → gone-echo {π = Store.π (After.store A₀)} {NP = EvalSt.nodes stP₁} {op = op} {m = m} {m′ = m′} {xs = xs} f d₁ (gone-restamp (After.store A₀) {Θ₁ = Θ₁} {ρ₁} {ks} {Θ₂} {ρ₂} {h₂} {h₃} {q} (g e)))
        (live-echo {π = Store.π (After.store A₀)} {NP = EvalSt.nodes stP₁} {h₃ = h₂} {h₄ = h₃} {q = q} f d₁ lv) dq (λ {rP} dP B rel′ →
        inner~ refl (flat-move (EvalSt.nodes stP₁) _ (EvalSt.nodes (proj₂ (proj₂ rP))) _ (After.grows B)
                       (missed dP (head-on _ _ _ m (self-node m (j ∷ [])) sp , drop-ot _ _ _ sp))
                       (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) f′)
               (After.grows B (After.grows A ip)) rel′)
        λ { (f , ds) → scan-quiet d₁ , inj₂ (f , dl ds) }
      where
      cI = tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))

    -- leaving an inner: the flattener's lane, then its restamp
    inner-pass : ∀ {lo lo′ ℓ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
               → InnerPasses (flatOp op) m j h p
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
    inner-pass {op = op} S R b sp si lv _ (fold-step (step-from-inner react-false) dR) =
      inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) (leave op R) b sp si (λ ())
        (live-for (λ x → x) (λ l → inj₂ (live-if-drop _ _ _ refl refl l)) lv) dR
    inner-pass {op = op} S R b sp si lv _ (fold-step (step-from-inner (react-alive _)) dR) =
      arm-weaken (λ { (() , _) }) (inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) (leave op R) b sp si (λ ())
        (live-for (λ x → x) (λ l → inj₂ (live-if-drop _ _ _ refl refl l)) lv) dR)
    inner-pass S R b sp si _ (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    inner-pass {op = op} S R b sp si _ (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (inner-alive S (proj₁ (proj₂ (leave op R))))) al)) dd))

    postulate
      -- A FINISH THAT ENDS ITS FLATTENER LEFT NOTHING AT ITS TAIL: an
      -- end leaves a finish only once the outer has ended and no inner is
      -- alive, and every row through the tail's head came through the
      -- outer or one of the inners.  A restamp's tail and a nested
      -- merge's are both instances.  The store is the one the finish
      -- leaves: a nested merge's finish writes its node before it starts,
      -- and only the drain after it hands a store back.
      gone-finish : ∀ {sP stP sI₁ stI₁} (S : St sP stP sI₁ stI₁) {now ℓ s op m′ j′ x}
                      {q : Path (plainᵏ Γ κ) ℓ s (emitᵗ t)} {es sI stI o₁ es₁ f₁}
                  → innerFinish⇓ op m′ j′ q now es sI stI x (o₁ , es₁ , f₁ , sI₁ , stI₁)
                  → f₁ ≡ true → Gone q stI₁

    -- A SWITCH'S INNER ENDED: both sides clear their current inner and let
    -- the group on, or neither does -- `CurRel` pairs the two currents,
    -- so the dying inner is current on both sides or on neither
    switch-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
               → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u switchᶠ m m′ ks xs
               → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u switchᶠ x x′
               → lookupNode m′ (EvalSt.nodes stI) ≡ just x′
               → Carries es vs
               → LiveFor es (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) (EvalSt.nodes stI)
               → Sound (from-inner switchᵒ m j ↠[ h ] p) sP₁ stP₁
               → Sound (from-inner switchᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
               → innerFinish⇓ switchᵒ m j p now vs sP stP (just x) (oP , vs₁ , fin₁ , sP₁ , stP₁)
               → innerFinish⇓ switchᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′) (o₁ , es₁ , f₁ , sI₁ , stI₁)
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner switchᵒ m j ↠[ h ] p)
                     (from-inner switchᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) Never (o₁ ++ proj₁ rI , proj₂ rI)
    switch-finish S f ip pr (switch~ _) lI b lv sp si (finish-switch-clear _) F′@(finish-switch-clear _) dR =
      let W = flat-write S (f , pr) (switch~ tt) (keep-live S _ lI refl) in arm-weaken (λ ()) (inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , ip , proj₂ (proj₂ W)) b sp si (gone-finish (After.store (proj₁ W)) F′)
        (live-for (λ x → x) (λ l → inj₂ (flat-live-if _ _ lI refl refl l)) lv) dR)
    switch-finish S f ip pr (switch~ {cur′ = nothing} ()) lI b _ sp si (finish-switch-clear _) (finish-nil _) dR
    switch-finish S f ip pr (switch~ {cur′ = just _} c) lI b _ sp si (finish-switch-clear e) (finish-nil e′) dR =
      ⊥-elim (t≢f (trans (sym (cur-here (Store.π-keys S) c ip e)) e′))
    switch-finish S f ip pr (switch~ {cur = nothing} ()) lI b _ sp si (finish-nil _) (finish-switch-clear _) dR
    switch-finish S f ip pr (switch~ {cur = just _} c) lI b _ sp si (finish-nil e) (finish-switch-clear e′) dR =
      ⊥-elim (t≢f (trans (sym (cur-there (Store.π-vals S) c ip e′)) e))
    switch-finish S f ip pr (switch~ _) lI b lv sp si (finish-nil _) F′@(finish-nil _) dR =
      arm-weaken (λ ()) (inner-on (after S (λ x → x) (λ x → x) [] (λ x → x)) ((_ , f) , ip , pr) b sp si (gone-finish S F′) lv dR)

    -- AN EXHAUST'S INNER ENDED: both sides clear their lane and let the
    -- group on
    exhaust-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
               → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u exhaustᶠ m m′ ks xs
               → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
               → FlatNodes {Γ = Γ} κ (Store.π S) u exhaustᶠ x x′
               → lookupNode m′ (EvalSt.nodes stI) ≡ just x′
               → Carries es vs
               → LiveFor es (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) (EvalSt.nodes stI)
               → Sound (from-inner exhaustᵒ m j ↠[ h ] p) sP₁ stP₁
               → Sound (from-inner exhaustᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
               → innerFinish⇓ exhaustᵒ m j p now vs sP stP (just x) (oP , vs₁ , fin₁ , sP₁ , stP₁)
               → innerFinish⇓ exhaustᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′) (o₁ , es₁ , f₁ , sI₁ , stI₁)
               → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner exhaustᵒ m j ↠[ h ] p)
                     (from-inner exhaustᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) Never (o₁ ++ proj₁ rI , proj₂ rI)
    exhaust-finish S f ip pr exhaust~ lI b lv sp si finish-exhaust-clear F′@finish-exhaust-clear dR =
      let W = flat-write S (f , pr) (exhaust~ {ia = false}) (keep-live S _ lI refl) in arm-weaken (λ ()) (inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , ip , proj₂ (proj₂ W)) b sp si (gone-finish (After.store (proj₁ W)) F′)
        (live-for (λ x → x) (λ l → inj₂ (flat-live-if _ _ lI refl refl l)) lv) dR)
    exhaust-finish S f ip pr exhaust~ lI b _ sp si (finish-nil ()) _ dR
    exhaust-finish S f ip pr exhaust~ lI b _ sp si finish-exhaust-clear (finish-nil ()) dR

    -- AN ARM AFTER A PASS: the pass's output ahead of the arm's
    arm-after : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now o sP₀ stP₀ sP₁ stP₁ i sI₀ stI₀ ℓ u} {p : Path Γ ℓ u t} {vs fin G H rI}
              → (A : After S (o , sP₀ , stP₀) (i , sI₀ , stI₀)) → (∀ {I} → H I → Out I i)
              → Arm (After.store A) now [] sP₁ stP₁ p vs fin G H rI
              → Arm S now o sP₁ stP₁ p vs fin G H (i ++ proj₁ rI , proj₂ rI)
    arm-after {S = S} {now = now} {o = o} {sP₁ = sP₁} {stP₁ = stP₁} {i = i} {p = p} {vs} {fin} {G} {H} A oi (arm {oI = oI} {rI = rI} A′ r b si g lv dI k ok) =
      subst (λ z → Arm S now o sP₁ stP₁ p vs fin G H (z , proj₂ rI)) (++-assoc i oI (proj₁ rI))
        (arm (after (After.store A′) (λ {a} {a′} x → After.keeps A′ {a} {a′} (After.keeps A {a} {a′} x))
                (λ ar → After.persists A′ (After.persists A ar))
                (subst₂ (Pointwise (λ x w → V κ t (proj₂ x) w)) (sym (readᴵ-++ i oI)) (++-identityʳ (readᴾ o))
                   (++⁺ (After.values A) (After.values A′)))
                (λ x → After.grows A′ (After.grows A x)))
             r b si g lv dI k λ h → out-++ i oI (oi h) (proj₁ (ok h)) , proj₂ (ok h))

    -- and its first part's own empty end, regrouped
    arm-shift : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now o sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin G H} xs ys {r}
              → Arm S now o sP₁ stP₁ p vs fin G H ((xs ++ ys) ++ proj₁ r , proj₂ r)
              → Arm S now o sP₁ stP₁ p vs fin G H ((xs ++ []) ++ (ys ++ proj₁ r) , proj₂ r)
    arm-shift {S = S} {now = now} {o = o} {sP₁ = sP₁} {stP₁ = stP₁} {p = p} {vs} {fin} {G} {H} xs ys {r} =
      subst (λ z → Arm S now o sP₁ stP₁ p vs fin G H (z , proj₂ r))
        (trans (++-assoc xs ys (proj₁ r)) (cong (_++ (ys ++ proj₁ r)) (sym (++-identityʳ xs))))

    -- a merge's pair as a drain re-reads it: one bound, one count, one
    -- end, and the queues related
    drain-read : ∀ {π NP NI u lim m m′ ks xs l₂ a₂ q₂ od₂ l₂′ a₂′ q₂′ od₂′}
               → Flattener {Γ = Γ} κ π {t} NP NI u (mergeᶠ lim) m m′ ks xs
               → drainSt u (lookupNode m NP) ≡ (l₂ , a₂ , q₂ , od₂)
               → drainSt (emitᵗ u) (lookupNode m′ NI) ≡ (l₂′ , a₂′ , q₂′ , od₂′)
               → l₂ ≡ l₂′ × a₂ ≡ a₂′ × od₂ ≡ od₂′ × Pointwise (λ x′ x → ObsRel κ u x′ x) q₂′ q₂
    drain-read {u = u} (_ , _ , _ , lP , lI , merge~ qs , _) eP eI
      with trans (sym (drain-self u)) (trans (sym (cong (drainSt u) lP)) eP)
         | trans (sym (drain-self (emitᵗ u))) (trans (sym (cong (drainSt (emitᵗ u)) lI)) eI)
    ... | refl | refl = refl , refl , refl , qs

    postulate
      -- A FOLD NEVER UN-ENDS AN OUTER: a node whose done flag is up stays
      -- up.  The risk is a nested merge's finish, which writes back the
      -- flag it read BEFORE folding its group: if that fold ended the
      -- merge's own outer, the write lowers the flag again
      -- An outer ends at most once, so a flag lowered inside a fold stays
      -- down to the next boundary, where a revert is counted.
      fold-keeps-od : ∀ {k now lo s} {p : Path (plainᵏ Γ κ) lo s (emitᵗ t)} {vs f sched} {st : EvalSt ei} {r}
                    → foldPath⇓ now p vs f sched st r
                    → outerDoneᵇ (lookupNode k (EvalSt.nodes (proj₂ (proj₂ r)))) ≡ false
                    → outerDoneᵇ (lookupNode k (EvalSt.nodes st)) ≡ false

      -- A DRAIN WRITES BACK NO END ITS NODE HAS SINCE LOST: the flag it
      -- carries is down wherever the node's flag is down when it stops.
      -- Each spend writes the carried flag, then subscribes, and a
      -- subscribe can reach the same stale write as a fold
      -- An outer ends at most once, so a flag lowered inside a fold stays
      -- down to the next boundary, where a revert is counted.
      drain-keeps-od : ∀ {k lo s} {p : Path (plainᵏ Γ κ) lo s (emitᵗ t)} {now fs l a od qs sched} {st : EvalSt ei} {out a′ q′ sched₂ st₂}
                     → mergeAllDrain⇓ k p now fs l a od qs sched st (out , a′ , q′ , sched₂ , st₂)
                     → (outerDoneᵇ (lookupNode k (EvalSt.nodes st)) ≡ false → od ≡ false)
                     → outerDoneᵇ (lookupNode k (EvalSt.nodes st₂)) ≡ false → od ≡ false

      -- A DRAIN ABOUT TO SPEND A QUEUED INNER FINDS ITS TAIL LIVE UNLESS
      -- SPENT: a merge holding a queue has not ended, so no outer its
      -- output walks into has, though the inners the drain already spent
      -- may have run the tail and the merge's own outer may be done
      -- A fact about the STATE the drain starts in, not about a run: what
      -- it owes is an invariant tying a merge's queue to its tail.
      -- DEAD ROUTE: threading the tail's liveness through the drain's
      --   spends, each over `inner-spares` -- that leaf's head is the
      --   merge's outer frame, live, and a drain runs under an outer that
      --   may already be done.
      drain-live : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u lim m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                     {f fs l a od o qs r}
                 → Walkedˣ xs (mergeᶠ lim) m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → hasRoom l a ≡ true
                 → mergeAllDrain⇓ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now (f ∷ fs) l a od (o ∷ qs) sI stI r
                 → LiveIf (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (EvalSt.nodes stI)

    -- A MERGE'S QUEUE DRAINED ON BOTH SIDES: while a lane is free each
    -- side spends its queue's head through the flattener's mint, and the
    -- node each re-reads is the pair the mint left
    drain-pair : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u lim m m′ ks xs Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : n + ℓ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                   {fs fs′ l a od qs qs′ out act qr sP₂ stP₂ out′ act′ qr′ sI₂ stI₂}
               → Walkedˣ xs (mergeᶠ lim) m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
               → Pointwise (λ x′ x → ObsRel κ u x′ x) fs′ fs → Pointwise (λ x′ x → ObsRel κ u x′ x) qs′ qs
               → (outerDoneᵇ (lookupNode m′ (EvalSt.nodes stI)) ≡ false → od ≡ false)
               → (dP : mergeAllDrain⇓ m p now fs l a od qs sP stP (out , act , qr , sP₂ , stP₂))
               → mergeAllDrain⇓ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now fs′ l a od qs′ sI stI (out′ , act′ , qr′ , sI₂ , stI₂)
               → sz-mergeAllDrain dP < N
               → Σ (After S (out , sP₂ , stP₂) (out′ , sI₂ , stI₂)) λ A
                   → act ≡ act′ × Pointwise (λ x′ x → ObsRel κ u x′ x) qr′ qr
                     × Walkedˣ xs (mergeᶠ lim) m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP₂) (EvalSt.nodes stI₂)
    drain-pair _ S W _ _ [] qw _ drain-spent drain-spent _ = after S (λ x → x) (λ x → x) [] (λ x → x) , refl , qw , W
    drain-pair _ S W _ _ (_ ∷ _) [] _ drain-nil drain-nil _ = after S (λ x → x) (λ x → x) [] (λ x → x) , refl , [] , W
    drain-pair _ S W _ _ (_ ∷ _) qw@(_ ∷ _) _ (drain-no-room _) (drain-no-room _) _ = after S (λ x → x) (λ x → x) [] (λ x → x) , refl , qw , W
    drain-pair _ S W _ _ (_ ∷ _) (_ ∷ _) _ (drain-no-room eP) (drain-room eI _ _ _) _ = ⊥-elim (t≢f (trans (sym eI) eP))
    drain-pair _ S W _ _ (_ ∷ _) (_ ∷ _) _ (drain-room eP _ _ _) (drain-no-room eI) _ = ⊥-elim (t≢f (trans (sym eP) eI))
    drain-pair wk {stP = stP} {stI = stI} S {m′ = m′} W cP cI (_ ∷ fw) (ob ∷ qw) H (drain-room {st₁ = s₁} _ c rP dr) dI@(drain-room {st₁ = s₁′} eI c′ rI dr′) lt
      with flat-mint wk S W cP cI (merge~ qw) (write-live S m′ H)
             (live-if-set _ m′ _ _ H (λ _ → flat-unspent {π = Store.π S} {NP = EvalSt.nodes stP} {NI = EvalSt.nodes stI} (proj₁ W)) (drain-live S W eI dI)) ob c c′ (sz-l lt)
    ... | A₁ , W₁ with drain-read {NP = EvalSt.nodes s₁} {NI = EvalSt.nodes s₁′} (proj₁ W₁) rP rI
    ...   | refl , refl , refl , qw₁ with drain-pair wk (After.store A₁) W₁ (sub-clear c cP) (sub-clear c′ cI) fw qw₁ (drain-od _ (lookupNode m′ (EvalSt.nodes s₁′)) rI) dr dr′ (sz-r lt)
    ...     | A₂ , e , qr , W₂ = A₁ ⨾ A₂ , e , qr , W₂

    -- A MERGE'S QUEUE DRAINED ON BOTH SIDES once its dying inner's group
    -- has folded, from the queue its node holds
    merge-drain : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u lim lim′ a q q′ od m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                    {p : Path Γ ℓ u t} {q̂ : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    {out act qr sP₂ stP₂ out′ act′ qr′ sI₂ stI₂}
                → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u (mergeᶠ lim) m m′ ks xs
                → Pointwise (λ x′ x → ObsRel κ u x′ x) q′ q
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q̂
                → Sound (from-inner mergeAllᵒ m j ↠[ h ] p) sP stP
                → Sound (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q̂) sI stI
                → (outerDoneᵇ (lookupNode m′ (EvalSt.nodes stI)) ≡ false → od ≡ false)
                → (dP : mergeAllDrain⇓ m p now q lim′ a od q sP stP (out , act , qr , sP₂ , stP₂))
                → mergeAllDrain⇓ m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q̂) now q′ lim′ a od q′ sI stI
                    (out′ , act′ , qr′ , sI₂ , stI₂)
                → sz-mergeAllDrain dP < N
                → Σ (After S (out , sP₂ , stP₂) (out′ , sI₂ , stI₂)) λ A
                    → act ≡ act′ × Pointwise (λ x′ x → ObsRel κ u x′ x) qr′ qr
                      × Flattener {Γ = Γ} κ (Store.π (After.store A)) {t} (EvalSt.nodes stP₂) (EvalSt.nodes stI₂) u (mergeᶠ lim) m m′ ks xs
                      × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP₂) (EvalSt.nodes stI₂) p q̂
    merge-drain wk S {m = m} {m′} {j = j} {j′} f qs pr sp si H dP dI lt =
      drain-pair wk S (f , pr) (head-on _ _ _ m (self-node m (j ∷ [])) sp , drop-ot _ _ _ sp)
        (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si) qs qs H dP dI lt

    -- A MERGE'S INNER ENDED ON BOTH SIDES: each finish folds the group
    -- down its tail, drains the queue its node holds, and writes the
    -- count and queue the drain left; the end then crosses the restamp
    merge-finish : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u lim m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂ x x′ mx}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                     {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                 → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u (mergeᶠ lim) m m′ ks xs
                 → (j , j′ ∷ []) ∈ Store.π S → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → lookupNode m (EvalSt.nodes stP) ≡ just x → lookupNode m′ (EvalSt.nodes stI) ≡ just x′
                 → FlatNodes {Γ = Γ} κ (Store.π S) u (mergeᶠ lim) x x′
                 → Carries es vs
                 → LiveFor es (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) (EvalSt.nodes stI)
                 → Sound (from-inner mergeAllᵒ m j ↠[ h ] p) sP stP
                 → Sound (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI
                 → Sound (from-inner mergeAllᵒ m j ↠[ h ] p) sP₁ stP₁
                 → Sound (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
                 → (F : innerFinish⇓ mergeAllᵒ m j p now vs sP stP mx (oP , vs₁ , fin₁ , sP₁ , stP₁)) → TailAt q F → mx ≡ just x
                 → innerFinish⇓ mergeAllᵒ m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (just x′)
                     (o₁ , es₁ , f₁ , sI₁ , stI₁)
                 → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
                 → sz-innerFinish F < N
                 → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                     (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ m j ↠[ h ] p)
                        (from-inner mergeAllᵒ m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) Never (o₁ ++ proj₁ rI , proj₂ rI)
    merge-finish _ S f ip pr lP lI (merge~ _) b _ sp si _ _ (finish-nil e) _ refl _ _ _ =
      ⊥-elim (t≢f (trans (sym (usable-self _)) e))
    merge-finish _ S f ip pr lP lI (merge~ _) b _ sp si _ _ (finish-all-drain _ _) _ refl (finish-nil e) _ _ =
      ⊥-elim (t≢f (trans (sym (usable-self _)) e))
    merge-finish wk {stP = stP} S {m = m} {m′} {j = j} {j′} {h₂ = h₂} {h₃} {q = q} f ip pr _ lI (merge~ qs) b lv sp si sp′ si′
        (finish-all-drain fP dP) tail refl F′@(finish-all-drain fI@(fold-step d₁ (fold-step step-map dq)) dI) dR lt
      with restamp-echo S f pr b d₁
    ... | A , f′ , pr′ , c′ , refl , _
      with tail (After.store A) pr′ c′ (drop-ot _ _ _ sp)
             (proj₂ (proj₁ (tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))))) (λ ())
             (live-echo {π = Store.π S} {NP = EvalSt.nodes stP} {h₃ = h₂} {h₄ = h₃} {q = q} f d₁ lv) dq
    ...   | A₁ , pr₁
      with merge-drain wk (After.store A₁)
             (flat-move _ _ _ _ (After.grows A₁)
               (missed fP (head-on _ _ _ m (self-node m (j ∷ [])) sp , drop-ot _ _ _ sp))
               (missed dq (proj₁ (tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si)))))
               (missed dq (proj₂ (tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))) ,
                           proj₂ (proj₁ (tail-of (step-clear d₁ (head-on _ _ _ m′ (self-node m′ (j′ ∷ [])) si , drop-ot _ _ _ si))))))
               f′)
             qs pr₁
             (fold-kept fP (drop-ot _ _ _ sp) _ sp (λ _ _ _ → refl))
             (fold-kept fI (drop-ot _ _ _ si) _ si (λ _ _ _ → refl))
             (λ h → trans (sym (cong outerDoneᵇ lI)) (fold-keeps-od fI h)) dP dI (sz-r lt)
    ...     | D , refl , qs′ , f₂ , pr₂ =
      arm-after ((A ⨾ A₁) ⨾ D) (λ ()) (arm-weaken (λ ())
        (inner-on (proj₁ W) ((_ , proj₁ (proj₂ W)) , After.grows (proj₁ W) (After.grows D (After.grows A₁ (After.grows A ip))) , proj₂ (proj₂ W))
           [] sp′ si′ (λ e → gone-finish (After.store (proj₁ W)) F′ (trans (cong (λ z → z ∧ _) (pw-null qs)) e)) (inj₁ refl) (subst (λ z → foldPath⇓ _ _ [] z _ _ _) (cong (λ z → z ∧ _) (pw-null qs)) dR)))
      where W = flat-write (After.store D) (f₂ , pr₂) (merge~ qs′)
                  (write-live (After.store D) m′ (drain-keeps-od dI (λ h → trans (sym (cong outerDoneᵇ lI)) (fold-keeps-od fI h))))

    -- AN INNER ENDED ON BOTH SIDES, by its flattener's operator
    finish-by : ∀ {N} (wk : Walker ep ei N) {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                  {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
              → Σ (List NodeId) (λ xs → Flattener {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks xs)
                × (j , j′ ∷ []) ∈ Store.π S × PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Carries es vs
              → LiveFor es (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) (EvalSt.nodes stI)
              → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP
              → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI stI
              → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP₁ stP₁
              → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) sI₁ stI₁
              → (F : innerFinish⇓ (flatOp op) m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁))
              → TailAt q F
              → innerFinish⇓ (flatOp op) m′ j′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) now es sI stI (lookupNode m′ (EvalSt.nodes stI))
                  (o₁ , es₁ , f₁ , sI₁ , stI₁)
              → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q) es₁ f₁ sI₁ stI₁ rI
              → sz-innerFinish F < N
              → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                  (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                     (from-inner (flatOp op) m′ j′ ↠[ h₁ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₂ h₃ q)) Never (o₁ ++ proj₁ rI , proj₂ rI)
    finish-by wk S {op = mergeᶠ _} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b lv sp si sp′ si′ F tail F′ dR lt =
      merge-finish wk S f ip pr lP lI fn b lv sp si sp′ si′ F tail lP
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR lt
    finish-by _ S {op = switchᶠ} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b lv _ _ sp si F _ F′ dR _ =
      switch-finish S f ip pr fn lI b lv sp si (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lP F)
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR
    finish-by _ S {op = exhaustᶠ} ((_ , f@(_ , _ , _ , lP , lI , fn , _)) , ip , pr) b lv _ _ sp si F _ F′ dR _ =
      exhaust-finish S f ip pr fn lI b lv sp si (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lP F)
        (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) lI F′) dR

    -- AN INNER NO LIVE CHAIN RUNS THROUGH: its pair is dead too, and
    -- both sides finish it
    inner-dies : ∀ {N} (wk : Walker ep ei N) {lo lo′ ℓ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                   {now vs es sP stP sI stI oP vs₁ fin₁ sP₁ stP₁ rI} (S : St sP stP sI stI)
               → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner (flatOp op) m j ↠[ h ] p)
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
               → Carries es vs
               → LiveFor es (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q))) (EvalSt.nodes stI)
               → Sound (from-inner (flatOp op) m j ↠[ h ] p) sP stP
               → Sound (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q))) sI stI
               → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
               → (F : innerFinish⇓ (flatOp op) m j p now vs sP stP (lookupNode m (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁))
               → TailAt q F
               → foldPath⇓ now
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q))) es true sI stI rI
               → sz-innerFinish F < N
               → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                   (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                      (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                       (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                        (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))) Never rI
    inner-dies _ {op = op} S R b _ sp si dd F _ (fold-step (step-from-inner (react-alive al′)) _) _ =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (inner-alive S (proj₁ (proj₂ (leave op R))))) dd)))
    inner-dies wk {op = op} S R b lv sp si dd F tail (fold-step d′@(step-from-inner (react-dead _ F′)) dR) lt =
      finish-by wk S (leave op R) b (live-for (λ x → x) (λ l → inj₂ (live-if-drop _ _ _ refl refl l)) lv) sp si (step-kept _ (step-from-inner (react-dead dd F)) sp) (step-kept _ d′ si) F tail F′ dR lt

    -- a delivery keeps its stamp through the hop's restamp, which moves
    -- only a subscribe
    delivery-del : ∀ {u Θx ρ₀} {I} {es : List (Val (plainᵏ Γ κ) (emitᵗ u))}
                 → All (DelAt I) es
                 → All (DelAt I) (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es)
    delivery-del {es = []} [] = []
    delivery-del {es = (_ , _ , _ , inj₁ _) ∷ _} (() ∷ _)
    delivery-del {Θx = Θx} {ρ₀} {es = (_ , _ , _ , inj₂ _) ∷ _} (d ∷ ds) = d ∷ delivery-del {Θx = Θx} {ρ₀} ds

    -- the hop's marker merge is not the hop's node: both are on the
    -- impl's path, and a path names each node once
    hop-apart : ∀ {sI} {stI : EvalSt ei} {lo′ ℓ₁ ℓ₂ ℓ₃ u nid′ j′ m2 j2 Θx ρ₀}
                  {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
              → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                       (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                        (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
              → m2 ≡ nid′ → ⊥
    hop-apart {nid′ = nid′} {j′} {m2} {j2} {Θx} {ρ₀} {h₂ = h₂} {h₃} {q} si eq =
      off-path (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)
        (subst (λ x → T (pathHasNode m2
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ x j′ ↠[ h₃ ] q))))
               eq (∨-Tˡ (self-node m2 (j′ ∷ []))))

    -- an impl finish at an index known otherwise
    finish-at : ∀ {lo s op m j} {q : Path (plainᵏ Γ κ) lo s (emitᵗ t)} {now vals sched} {st : EvalSt ei} {mx my r}
              → mx ≡ my → innerFinish⇓ op m j q now vals sched st mx r → innerFinish⇓ op m j q now vals sched st my r
    finish-at refl F = F

    -- a deferred body's liveness, past the marker merge, its restamp and
    -- the hop's node, none of which walks an outer or spends
    defer-live : ∀ {lo′ ℓ₁ ℓ₂ ℓ₃ u nid′ j′ m2 j2 Θx ρ₀} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {es : List (Val (plainᵏ Γ κ) (emitᵗ u))} {N}
               → LiveFor es (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) N
               → LiveFor (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es) q N
    defer-live = live-for (λ { refl → refl })
                   (λ l → inj₂ (live-if-drop _ _ _ refl refl (live-if-drop _ _ _ refl refl (live-if-drop _ _ _ refl refl l))))

    -- A DEAD DEFERRED BODY FINISHES ON BOTH SIDES: the plain merge folds
    -- the group down its tail, as the hop's marker merge does through its
    -- restamp and the hop's node; the counts fall, the marker's end
    -- reaches the hop's node, whose inner is dead as the body's is, and
    -- that node's finish hands the tail the end
    defer-finish : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀ a b mx}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                     {vs es oP vs₁ fin₁ sP₁ stP₁ o₁ es₁ f₁ sI₁ stI₁ rI}
                 → (nid , nid′ ∷ []) ∈ Store.π S → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ Store.π S
                 → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing a [] true)
                 → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
                 → lookupNode m2 (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing b [] true) → a ≤ 1 → b ≤ 1
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Carries es vs
                 → LiveFor es (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) (EvalSt.nodes stI)
                 → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
                 → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
                 → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP₁ stP₁
                 → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI₁ stI₁
                 → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
                 → (F : innerFinish⇓ mergeAllᵒ nid j p now vs sP stP mx (oP , vs₁ , fin₁ , sP₁ , stP₁)) → TailAt q F
                 → mx ≡ just (mergeAll-st {t = u} nothing a [] true)
                 → innerFinish⇓ mergeAllᵒ m2 j2
                     (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                      (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)) now es sI stI (just (mergeAll-st {t = emitᵗ u} nothing b [] true))
                     (o₁ , es₁ , f₁ , sI₁ , stI₁)
                 → foldPath⇓ now (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                     (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)) es₁ f₁ sI₁ stI₁ rI
                 → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                     (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) Never (o₁ ++ proj₁ rI , proj₂ rI)
    defer-finish S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (finish-nil e) _ refl _ _ =
      ⊥-elim (t≢f (trans (sym (usable-self _)) e))
    defer-finish S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (finish-all-drain _ _) _ refl (finish-nil e) _ =
      ⊥-elim (t≢f (trans (sym (usable-self _)) e))
    defer-finish S {now} {u = u} {nid = nid} {nid′} {j} {j′} {m2} {j2} {a = a} {b = b₀}
        ip₁ ip₂ lP lI l2 a1 b1 pr b lv sp si sp′ si′ dd (finish-all-drain {st₁ = stPf} fP drain-spent) tail refl
        (finish-all-drain (fold-step step-map (fold-step {out₂ = oI₁} {sched₂ = sIq} {st₂ = stIq} (step-from-inner react-false) dq))
          drain-spent) dR
      with tail S pr (delivery-carries b) (drop-ot _ _ _ sp) (drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))) (λ ()) (defer-live lv) dq
    ... | A₁ , pr₁
      with fin-at (pred-one b1) dR
    ...   | fold-step step-map (fold-step (step-from-inner (react-alive al)) _) =
      ⊥-elim (t≢f (trans (sym al) (trans (sym (inner-alive (After.store A₁) (After.grows A₁ ip₂))) (still-dead sp dd fP))))
    ...   | fold-step step-map (fold-step d₂@(step-from-inner (react-dead _ F″)) dq₂)
      with finish-at
             (trans (set-above m2 nid′ (mergeAll-st {t = emitᵗ u} nothing (pred b₀) [] true) (EvalSt.nodes stIq)
                      (apart m2 nid′ (λ e → hop-apart si (sym e))))
                    (trans (fold-unmoved dq (head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) (drop-ot _ _ _ (drop-ot _ _ _ si)) ,
                                             drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))))
                           lI))
             F″
    ...     | finish-nil e = ⊥-elim (t≢f (trans (sym (usable-self _)) e))
    ...     | finish-all-drain {outV = oQ} {st₁ = stQ} fq₀ drain-spent
      with defer-end (After.store A₁) (After.grows A₁ ip₁) (After.grows A₁ ip₂)
             (trans (fold-unmoved fP (head-on _ _ _ nid (self-node nid (j ∷ [])) sp , drop-ot _ _ _ sp)) lP)
             (trans (fold-unmoved dq (head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) (drop-ot _ _ _ (drop-ot _ _ _ si)) ,
                                      drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))))
                    lI)
             (trans (fold-unmoved dq (on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) ,
                                      drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))))
                    l2)
             pr₁
             (fold-kept fP (drop-ot _ _ _ sp) _ sp (λ _ _ _ → refl))
             (fold-kept dq (drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si))) _ si (λ _ _ _ → refl))
             fq₀
    ...       | A₂ , pr₂ =
      arm-shift oI₁ (oQ ++ [])
        (arm-after (A₁ ⨾ A₂) (λ ())
          (arm (after (After.store A₂) (λ x → x) (λ x → x) [] (λ x → x)) pr₂ [] (drop-ot _ _ _ sN) (gone-finish (After.store A₂) F″) (inj₁ refl) dq₂
             (λ {rP} dP B rel′ →
               deferInner~ (After.grows B (After.grows A₂ (After.grows A₁ ip₁))) (After.grows B (After.grows A₂ (After.grows A₁ ip₂)))
                 (trans (fold-unmoved dP (head-on _ _ _ nid (self-node nid (j ∷ [])) sp′ , drop-ot _ _ _ sp′)) (lookup-set nid (mergeAll-st {t = u} nothing (pred a) [] true) (EvalSt.nodes stPf)))
                 (trans (fold-unmoved dq₂ (head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) sN , drop-ot _ _ _ sN)) (lookup-set nid′ (mergeAll-st {t = emitᵗ u} nothing (pred a) [] true) (EvalSt.nodes stQ)))
                 (trans (fold-unmoved dq₂ (on-drop (proj₁ cM) , drop-ot _ _ _ (proj₂ cM)))
                   (trans (set-above nid′ m2 (mergeAll-st {t = emitᵗ u} nothing (pred a) [] true) (EvalSt.nodes stQ) (apart nid′ m2 (hop-apart si)))
                     (trans (fold-unmoved fq₀ (on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si′)) ,
                                               drop-ot _ _ _ (drop-ot _ _ _ (drop-ot _ _ _ si′))))
                            (lookup-set m2 (mergeAll-st {t = emitᵗ u} nothing (pred b₀) [] true) (EvalSt.nodes stIq)))))
                 (≤-trans pred[n]≤n a1) (≤-trans pred[n]≤n b1) rel′) λ ()))
      where
      sN = step-kept _ d₂ (drop-ot _ _ _ (drop-ot _ _ _ si′))
      cM = step-clear d₂ (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si′) , drop-ot _ _ _ (drop-ot _ _ _ si′))

    -- A DEFERRED BODY NO LIVE CHAIN RUNS THROUGH: the hop's marker
    -- merge's inner is dead too, and both sides finish it
    deferInner-dies : ∀ {lo lo′ ℓ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                        {now vs es sP stP sI stI oP vs₁ fin₁ sP₁ stP₁ rI} (S : St sP stP sI stI)
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
                    → Carries es vs
                    → LiveFor es (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) (EvalSt.nodes stI)
                    → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
                    → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                             (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                              (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
                    → any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ false
                    → (F : innerFinish⇓ mergeAllᵒ nid j p now vs sP stP (lookupNode nid (EvalSt.nodes stP)) (oP , vs₁ , fin₁ , sP₁ , stP₁))
                    → TailAt q F
                    → foldPath⇓ now
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) es true sI stI rI
                    → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                        (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                           (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                            (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                             (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) Never rI
    deferInner-dies S R@(deferInner~ _ ip₂ _ _ l2 _ _ _) b _ sp si dd F _ (fold-step (step-from-inner (react-alive al′)) _) =
      ⊥-elim (t≢f (trans (sym al′) (trans (sym (defer-alive S ip₂ l2)) dd)))
    deferInner-dies S (deferInner~ ip₁ ip₂ lP lI l2 a1 b1 pr) b lv sp si dd F tail (fold-step d′@(step-from-inner (react-dead _ F′)) dR) =
      defer-finish S ip₁ ip₂ lP lI l2 a1 b1 pr b lv sp si (step-kept _ (step-from-inner (react-dead dd F)) sp) (step-kept _ d′ si) dd
        F tail lP (subst (λ ns → innerFinish⇓ _ _ _ _ _ _ _ _ ns _) l2 F′) dR

    -- A DEFERRED BODY'S INNER LEFT OPEN: the hop's marker merge and its
    -- node let the group past, and the restamp between moves no node
    defer-on : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)} {vs es rI}
             → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                 (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                  (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                   (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
             → Carries es vs
             → LiveFor es (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) (EvalSt.nodes stI)
             → Sound (from-inner mergeAllᵒ nid j ↠[ h ] p) sP stP
             → Sound (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                      (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                       (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))) sI stI
             → foldPath⇓ now q (map (applyClo (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀)) es)
                 false sI stI rI
             → Arm S now [] sP stP p vs false
                 (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                    (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                     (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                      (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))) (λ I → Dlv I false es) rI
    defer-on S {nid = nid} {nid′} {j} {j′} {m2} {j2} (deferInner~ ip₁ ip₂ lP lI l2 a1 b1 pr) b lv sp si dq =
      arm (after S (λ x → x) (λ x → x) [] (λ x → x)) pr (delivery-carries b) s3 (λ ()) (defer-live lv) dq (λ {rP} dP B rel′ →
        deferInner~ (After.grows B ip₁) (After.grows B ip₂) (trans (fold-unmoved dP cP) lP)
                    (trans (fold-unmoved dq c′) lI) (trans (fold-unmoved dq c2) l2) a1 b1 rel′)
        λ { (_ , ds) → out-quiet [] refl , inj₂ (refl , delivery-del ds) }
      where
      s2 = drop-ot _ _ _ (drop-ot _ _ _ si)
      s3 = drop-ot _ _ _ s2
      cP = head-on _ _ _ nid (self-node nid (j ∷ [])) sp , drop-ot _ _ _ sp
      c′ = head-on _ _ _ nid′ (self-node nid′ (j′ ∷ [])) s2 , s3
      c2 = on-drop (on-drop (head-on _ _ _ m2 (self-node m2 (j2 ∷ [])) si)) , s3

    -- a deferred body: the hop's marker merge, its restamp, the hop's node
    deferInner-pass : ∀ {lo lo′ ℓ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ n + ℓ} {h₂ : n + ℓ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → InnerPasses mergeAllᵒ nid j h p
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
    deferInner-pass S R b sp si lv _
      (fold-step (step-from-inner react-false) (fold-step step-map (fold-step (step-from-inner react-false) dq))) =
      defer-on S R b lv sp si dq
    deferInner-pass S R b sp si lv _
      (fold-step (step-from-inner (react-alive _)) (fold-step step-map (fold-step (step-from-inner react-false) dq))) =
      arm-weaken (λ { (() , _) }) (defer-on S R b lv sp si dq)
    deferInner-pass S R b sp si _ (inj₁ ()) (fold-step (step-from-inner (react-dead _ _)) _)
    deferInner-pass S R@(deferInner~ _ ip₂ _ _ l2 _ _ _) b sp si _ (inj₂ al) (fold-step (step-from-inner (react-dead dd _)) _) =
      ⊥-elim (t≢f (trans (sym (trans (sym (defer-alive S ip₂ l2)) al)) dd))

    -- AN OUTER'S EMIT CARRYING ONE VALUE, EXPLODED: the merge is
    -- unbounded, so its consume neither queues nor finds the node
    -- unusable, and subscribes
    explode-one : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                    {rP rI}
                → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ [])
                → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP rP
                → thruConsume⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                    (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀) e′) sI stI rI
                → Σ (After S rP rI) λ A
                    → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                        u op m m′ ks (mX ∷ [])
                      × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                      × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ rI))) u mX
                      × (∀ {I} → DelAt {echoᵗ u} I e′ → Out I (proj₁ rI))
    explode-one S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x lv e′ rel W
                (consume-all-sub l _ c) =
      explode-one-sub S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x lv l e′ rel W c
    explode-one S cp ci fl r (_ , lX) _ e′ rel W (consume-all-enqueue l h) = ⊥-elim (no-queue (trans (sym lX) l) h)
    explode-one S {u = u} cp ci fl r (_ , lX) _ e′ rel W (consume-all-nil e) =
      ⊥-elim (unusable mergeAllᵒ (echoᵗ (emitᵗ u)) lX e (usable-self (echoᵗ (emitᵗ u))))

    -- AN OUTER'S ELEMENTS EXPLODED: each emit's run of elements is an
    -- inner the impl's merge subscribes, and its elements walk into the
    -- flattener where the plain outer's walk hands them on.  One emit at
    -- a time, in the order the impl walks them
    explode-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                     {es vs rP rI}
                 → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                 → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                 → LiveFor es (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                 → Carries {echoᵗ u} es vs
                 → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                 → thruWalk⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                     (thruEvents (map (applyClo {s = obs (echoᵗ (emitᵗ u))} {t = echoᵗ (echoᵗ (emitᵗ u))}
                                                (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅))
                                      (map (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀)) es))) sI stI rI
                 → Σ (After S rP rI) λ A
                     → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                         u op m m′ ks (mX ∷ [])
                       × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                       × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ rI))) u mX
                       × (∀ {I} → All (DelAt {echoᵗ u} I) es → Out I (proj₁ rI))
    -- one emit carrying a value: the plain walk already split at it
    explode-cons : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                     {es vs rP rI r₁ r₂}
                 → Clear m p sP stP → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) sI stI
                 → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                 → LiveIf (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) (EvalSt.nodes stI)
                 → ∀ e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ []) → Carries {echoᵗ u} es vs
                 → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ [])) sP stP r₁
                 → thruWalk⇓ (flatOp op) m p now (thruEvents vs) (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) r₂
                 → rP ≡ (proj₁ r₁ ++ proj₁ r₂ , proj₂ r₂)
                 → thruWalk⇓ mergeAllᵒ mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) now
                     (thruEvents (map (applyClo {s = obs (echoᵗ (emitᵗ u))} {t = echoᵗ (echoᵗ (emitᵗ u))}
                                                (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅))
                                      (map (applyClo {s = emitᵗ (echoᵗ u)} {t = obs (echoᵗ (emitᵗ u))} (Θ₀ , explodeᵛ , ρ₀)) (e′ ∷ es)))) sI stI rI
                 → Σ (After S rP rI) λ A
                     → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
                         u op m m′ ks (mX ∷ [])
                       × PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
                       × MergeAt {Γ = Γ} κ (EvalSt.nodes (proj₂ (proj₂ rI))) u mX
                       × (∀ {I} → All (DelAt {echoᵗ u} I) (e′ ∷ es) → Out I (proj₁ rI))
    explode-walk S cp ci fl r x _ [] walk-nil walk-nil = after S (λ y → y) (λ y → y) [] (λ y → y) , fl , r , x , λ _ → out-quiet [] refl
    explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                 cp ci fl r x lv (quiet e′ bare b) W (walk-cons {out₁ = oa} {out₂ = ob} C W′) =
      let l = live-cons lv
          (X , fl′ , r′ , x′ , o₁) = explode-quiet S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x l e′ bare C
          (Y , fl″ , r″ , x″ , o₂) = explode-walk (After.store X) {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                         cp (consume-clear C ci) fl′ r′ x′ (inj₂ (consume-spares C l)) b W W′
      in (X ⨾ Y) , fl″ , r″ , x″ , λ { (d ∷ ds) → out-++ oa ob (o₁ d) (o₂ ds) }
    explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                 cp ci fl r x lv (one e′ {w = w} {vs = vs} rel b) W WI =
      let H = walk-head w vs W
      in explode-cons S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
           cp ci fl r x (live-cons lv) e′ rel b (proj₁ (proj₂ H)) (proj₁ (proj₂ (proj₂ (proj₂ H)))) (proj₂ (proj₂ (proj₂ (proj₂ H)))) WI
    explode-cons S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                 cp ci fl r x l e′ rel b W₁ W₂ refl (walk-cons {out₁ = oa} {out₂ = ob} C W′) =
      let (X , fl′ , r′ , x′ , o₁) = explode-one S {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂} cp ci fl r x l e′ rel W₁ C
          (Y , fl″ , r″ , x″ , o₂) = explode-walk (After.store X) {op = op} {Θ₀ = Θ₀} {ρ₀ = ρ₀} {Θ₅ = Θ₅} {ρ₅ = ρ₅} {Θ₁ = Θ₁} {ρ₁ = ρ₁} {Θ₂ = Θ₂} {ρ₂ = ρ₂}
                         (walk-clear W₁ cp) (consume-clear C ci) fl′ r′ x′ (inj₂ (consume-spares C l)) b W₂ W′
      in (X ⨾ Y) , fl″ , r″ , x″ , λ { (d ∷ ds) → out-++ oa ob (o₁ d) (o₂ ds) }

    -- the same, once the merge's end is read off
    explode-wrapped : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI″ stI″ fin r T} {H : ℕ → Set}
                    → (fin , sI″ , stI″) ≡ T
                    → (A : After S (oP , sP′ , stP′) (oI , sI″ , stI″))
                    → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                    → Walkedˣ (mX ∷ []) op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI″)
                    → MergeAt {Γ = Γ} κ (EvalSt.nodes stI″) u mX
                    → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) (proj₁ (proj₂ T)) (proj₂ (proj₂ T))
                    → (fin ≡ true → Gone (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) stI″)
                    → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) [] (proj₁ T) (proj₁ (proj₂ T)) (proj₂ (proj₂ T)) r
                    → (∀ {I} → H I → Out I oI × fin ≡ false)
                    → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                        (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                        p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                        (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                           (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                            (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                             (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                              (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q))))) H
                        (oI ++ proj₁ r , proj₂ r)
    explode-wrapped {op = op} {h₄ = h₄} {fin = fin} refl A cP W x cI gw (fold-step d@(step-thru-outer walk-nil) dR) g =
      explode-arm A cP (outer-wrap (After.store A) {op = op} {h₂ = h₄} {fin = fin} W gw (unthru (step-kept _ d (proj₂ cI))) dR)
        (merge-moved (missed (fold-step d dR) cI) x) g

    -- THE EXPLODED OUTER'S END: the impl's merge is idle, so it ends
    -- where the plain outer does, and the flattener's end follows on
    -- both sides
    explode-end : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ} {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                    {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r} {H : ℕ → Set}
                → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
                → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                → Flattener {Γ = Γ} κ (Store.π (After.store A)) {t = t} (EvalSt.nodes stP′) (EvalSt.nodes stI′) u op m m′ ks (mX ∷ [])
                  × PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI′) p q
                  × MergeAt {Γ = Γ} κ (EvalSt.nodes stI′) u mX
                → Clear mX (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)
                    (proj₁ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′))))
                → (fin ≡ true → Gone (thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)) stI′)
                → foldPath⇓ now (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q) []
                    (proj₁ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))
                    (proj₁ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ mX fin (sI′ , stI′)))) r
                → (∀ {I} → H I → Out I oI × fin ≡ false)
                → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                    (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                    p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                    (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                       (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                        (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                         (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                          (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q))))) H
                    (oI ++ proj₁ r , proj₂ r)
    explode-end {fin = false} A cP (fl , r , x) cI _ dI g = explode-wrapped refl A cP (fl , r) x cI (λ ()) dI g
    explode-end {op = op} {m′ = m′} {ks = ks} {mX = mX} {Θ₁ = Θ₁} {ρ₁} {Θ₂} {ρ₂} {h₃ = h₃} {h₄} {h₅} {h₆} {q = q} {sI′ = sI′} {stI′ = stI′} {fin = true} A cP (fl , r , (_ , lX)) cI gm dI g =
      let (B , W , x′) = merge-done (After.store A) fl r lX
                           (live-spent mX _ (gone-thru {st = stI′} {q = thru-outer mergeAllᵒ mX ↠[ h₃ ] (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)} refl (gm refl))
                              (Inv.live-outer (Store.inv (After.store A))))
      in explode-wrapped {T = thruWrap mergeAllᵒ mX true (sI′ , stI′)} (sym (merge-wrap lX)) (A ⨾∅ B) cP W x′ cI
           (λ _ → gone-nodes {q = thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q} {st = stI′}
                    (gone-wrap (After.store A) {o = mergeAllᵒ} {k = mX} {h = h₃} {q = thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q}
                       (gm refl) (cong proj₁ (merge-wrap {s = sI′} {st = stI′} lX)))) dI g

    -- an outer's elements, each inner a sync outer hands the flattener
    -- subscribed before the step returns: the explode and its merge
    outerExplode-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                         {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ n + ℓ}
                         {h₅ : n + ℓ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                         {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                         {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                     → Flattener {Γ = Γ} κ (Store.π S) {t = t} (EvalSt.nodes stP) (EvalSt.nodes stI) u op m m′ ks (mX ∷ [])
                       × MergeAt {Γ = Γ} κ (EvalSt.nodes stI) u mX
                       × PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                     → Carries {echoᵗ u} es vs
                     → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                     → Sound (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) sI stI
                     → (fin ≡ true → Gone (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) stI)
                     → LiveFor es (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) (EvalSt.nodes stI)
                     → stepFrame⇓ now (thru-outer (flatOp op) m) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                     → foldPath⇓ now (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                               (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                                (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                                 (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q)))) es fin sI stI rI
                     → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                         (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                            (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                             (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                              (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                               (thru-outer (flatOp op) m′ ↠[ h₄ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₅ h₆ q))))) (λ I → Dlv {echoᵗ u} I fin es) rI
    outerExplode-arm S {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} {h₃ = h₃} {fin = fin} (fl , x , r) b sp si gn lv dW@(step-thru-outer W)
                     (fold-step step-map (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR))) =
      let si′ = drop-ot _ _ _ (drop-ot _ _ _ si)
          X   = explode-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} (unthru sp) (unthru si′) fl r x
                  (live-for (λ e → e) (λ l → inj₂ (live-if-drop _ _ _ refl refl (live-if-drop _ _ _ refl refl l))) lv) b W W′
          F   = proj₂ X
      in explode-end {op = op} {Θ₀ = Θ₀} {ρ₀} {Θ₅ = Θ₅} {ρ₅} {fin = fin} (proj₁ X) (unthru (step-kept _ dW sp))
           (proj₁ F , proj₁ (proj₂ F) , proj₁ (proj₂ (proj₂ F)))
           (unthru (step-kept _ dW′ si′)) (λ e → gone-walk S {h = h₃} W′ (gn e)) dR
           λ { (f , ds) → proj₂ (proj₂ (proj₂ F)) ds , f }

    -- and a read's restamp keeps a delivery's
    restamp-del : ∀ {i : Fin n} {Θ₀ ρ₀} {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {I}
                    {es : List (Val (plainᵏ Γ κ) (emitᵗ (lookup Γ i)))}
                → All (DelAt I) es → All (DelAt I) (map (applyClo (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀)) es)
    restamp-del {es = []} [] = []
    restamp-del {es = (_ , _ , _ , inj₁ _) ∷ _} (() ∷ _)
    restamp-del {i = i} {ρ₀ = ρ₀} {X = X} {es = (_ , _ , _ , inj₂ _) ∷ _} (d ∷ ds) = d ∷ restamp-del {i = i} {ρ₀ = ρ₀} {X = X} ds

    -- A SLOT'S READER: the impl runs the restamp where the plain path runs
    -- on, so the arm is the one frame the impl moves alone, and the plain
    -- side has not moved
    read-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {Θ₀ ρ₀ ℓ′}
                   {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {h : suc (toℕ (n ↑ʳ i)) ≤ ℓ′}
                   {p : Path Γ (suc (toℕ i)) (lookup Γ i) t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ (lookup Γ i)) (emitᵗ t)}
                 → lookup κ i ≡ hotᵏ ⊎ lookup κ i ≡ sharedᵏ
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → ∀ {now vs es fin rI} → Carries es vs
                 → Sound (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) sI stI
                 → (fin ≡ true → Gone (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) stI)
                 → LiveIf (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) (EvalSt.nodes stI)
                 → foldPath⇓ now (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) es fin sI stI rI
                 → Arm S now [] sP stP p vs fin none (λ I → Dlv I fin es) rI
    read-arm S {i = i} {ρ₀ = ρ₀} {X = X} _ r c si g l (fold-step step-map dq) =
      arm (after S (λ x → x) (λ x → x) [] (λ x → x)) r (restamp-carries {i = i} {X = X} c) (drop-ot _ _ _ si) g
        (inj₂ (live-if-drop _ _ _ refl refl l)) dq (λ _ _ _ → tt)
        λ { (f , ds) → out-quiet [] refl , inj₂ (f , restamp-del {i = i} {ρ₀ = ρ₀} {X = X} ds) }

    -- the same pass, started from the store as it stood before the row was marked
    rebase : ∀ {sP stP sI stI fin x x′ rP rI} {S : St sP stP sI stI} {pr : Partners κ _ _ _ _ _ (Store.rows S) x x′}
           → After (delivered S {fin} pr) rP rI → After S rP rI
    rebase {fin = fin} (after s k q v g) = after s k (λ ar → q (delivered-arr {fin = fin} ar)) v g

    -- a share marked dying on both sides
    dying-after : ∀ {sP stP sI stI} (S : St sP stP sI stI) (i : Fin n) → lookup κ i ≡ sharedᵏ
                → After S ([] , sP , shareDying i true stP) ([] , sI , shareDying (n ↑ʳ i) true stI)
    dying-after S i sh = after (dying S i sh) (λ x → x) (dying-arr {S = S} {i = i} {sh = sh}) [] (λ x → x)
