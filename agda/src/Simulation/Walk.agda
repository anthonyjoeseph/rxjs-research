------------------------------------------------------------------
-- THE ROOT SUBSCRIBES, WALKED ONE FORMER AT A TIME.  Both runs open by
-- subscribing their program at the root, and each subscribe is a
-- derivation the builder hands back: the plain one over `plainExp`, the
-- impl's over the elaboration under its mint.  A walk over the author's
-- program reads the two together, one former's frames per step, and
-- what it keeps is `Simulation.Stores`'s relation and the values the
-- two send to the root.
--
-- A FORMER'S ARM SEES BOTH DERIVATIONS AT ITS OWN TERM.  The plain
-- closure is the former's `plainExp`, the impl's its elaboration
-- renamed into whatever telescope the impl closed it in, over
-- environments related slot for slot -- `ObsRel`'s shape, so the walk
-- reaches a flattener's inner on the same terms as the root.
------------------------------------------------------------------
module Simulation.Walk where

open import Data.List    using (List; []; _∷_; map)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Relation.Unary.All using (All; _∷_; []) renaming (map to mapᵃ)
open import Data.List.Relation.Unary.All.Properties using (map⁺; concat⁺; tabulate⁺)
open import Data.Bool    using (Bool; T; true; false; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Unit    using (tt)
open import Data.Nat     using (ℕ; suc; _+_; _<_; _≤_; s≤s; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsize-unfoldμ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Properties using (<-trans; n<1+n; m≤n+m; ≤-trans; ≤-reflexive; ≤-refl; <⇒<ᵇ; <⇒≢; 1+n≢n)
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)

open import Rx.Prim      using (hot; cold)
open import Rx.Exp       using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import Rx.Exp       using (Ctx; Val; Closed; Exp; unfoldμ; obs; ofᵉ; Ren∈; ext∈; renExp; renTm; applyClo; []ᵉ; _∷ᵉ_; uniqᵗ; unitᵗ; boolᵗ; _×ᵗ_; evalWith; input; mintᵉ; deferᵉ; mapᵉ; scanᵉ; takeWhileᵉ; flattenᵉ; sndᵗ; varᵗ; pairᵗ; inlᵗ; inrᵗ; unit̂; Fn; FnClo; Tm)
open import Rx.Mint      using (Mint; setAt; sourceᵏ; nodeᵏ; ordinalᵏ; regᵏ; counter; freshId)
open import Rx.Evaluator using (Sched; EvalSt; LiveSource; Path; root; map-f; scan-f; take-f; _↠[_]_; NodeId; NodeState; sched-init; st-init;
  Frame; frameNodes; mkHot; installNode; setNode; cell-st; take-st; lookupNode; echoᵗ; thru-outer; register; atDyn; mergeAll-st; mergeAllᵒ)
open import Rx.Slots     using (Slots; scripted; shared)
open import Rx.Evaluator.Domain using (subscribeE⇓; foldPath⇓; subs-map; subs-mint; subs-of; subs-empty; subs-scan; subs-takeWhile; subs-flatten; subs-defer; subs-μ; sub-all; flatSt)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set; set-above)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; rule; Sound; sound; fresh-sound; push-sound; sub-ot; node-eq)
open import Data.Fin     using (Fin; _↑ʳ_)
open import Data.Vec     using (lookup)
open import SExp.Syntax  using (SExp; STm; SFn; Kind; Kinds; hotᵏ; coldᵏ; sharedᵏ; plainᵏ; plainᵗ; emitᵗ; inputˢ; ofˢ; emptyˢ; takeWhileˢ; mapˢ; scanˢ;
  flattenˢ; μˢ; varˢ; deferˢ)
open import SExp.Plain   using (plainExp; plainTm; plainTms)
open import Simulation.Arm using (module Arms)
open import SExp.Elaborate using (toInstEmit; toInstEmitTm; plainᶜ⁺; mapStepᵖ; ScanAᵗ; CutS; cutOpenᵛ; cutOutᵛ;
  FlatSᵗ; flatStepᵛ; elemᵛ; explodeᵛ; flattenᵖ; perInnerˢ; frameᵛ; stampedSlot; restampᵛ; subscribeᵛ; inputᵖ)
open import SExp.InstEmit using (machineEmitᵗ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Schedules using (Sync)
open import Simulation.After using (readᴾ; readᴵ; module Kept)
open import Simulation.Write using (apart)
open Kept using (After; module After; _⨾_)
open import Simulation.Stores using (guardOf; V; EnvRel; Lifts; ScanLifts; CutLifts; PathRel; root~; map~; scan~; takeWhile~;
  spentWhile~; FlatNodes; merge~; switch~; exhaust~; outerElem~; outerExplode~; Store; Src;
  SrcNum; [])


-- TWIN: `ib-renᵉ` -- the same walk over `renExp`'s clauses, a binder's
--   `ext∈` over the composite agreeing with the composite of the two
--   `ext∈`s pointwise, not definitionally.
postulate
  renExp-fuse : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ₁ Θ₂ Θ₃ t} (σ : Ren∈ Θ₁ Θ₂) (ρ : Ren∈ Θ₂ Θ₃) (x : Exp Γ Δᵍ Δ Θ₁ t)
              → renExp (λ y → y) (λ y → y) ρ (renExp (λ y → y) (λ y → y) σ x) ≡ renExp (λ y → y) (λ y → y) (λ y → ρ (σ y)) x

-- a read through a transported slot is a read of the slot, down the
-- path transported back
read-input : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {Θ Θ′} (w : Ren∈ Θ Θ′) {j : Fin m} {B} (eq : lookup Δ j ≡ B)
               {ρ lo} {κq : Path Δ lo B t} {now s st r}
           → subscribeE⇓ {e = e} (Θ′ , renExp (λ x → x) (λ x → x) w (subst (Exp Δ [] [] Θ) eq (input j)) , ρ) κq now s st r
           → subscribeE⇓ {e = e} (Θ′ , input j , ρ) (subst (λ u → Path Δ lo u t) (sym eq) κq) now s st r
read-input w refl d = d

-- the same, for a term whose type the transport reaches through
read-machine : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {Θ Θ′} (w : Ren∈ Θ Θ′) {A B} (eq : A ≡ B) (X : Exp Δ [] [] Θ (machineEmitᵗ A))
                 {ρ lo} {κq : Path Δ lo (machineEmitᵗ B) t} {now s st r}
             → subscribeE⇓ {e = e} (Θ′ , renExp (λ x → x) (λ x → x) w (subst (λ u → Exp Δ [] [] Θ (machineEmitᵗ u)) eq X) , ρ) κq now s st r
             → subscribeE⇓ {e = e} (Θ′ , renExp (λ x → x) (λ x → x) w X , ρ) (subst (λ u → Path Δ lo (machineEmitᵗ u) t) (sym eq) κq) now s st r
read-machine w refl X d = d

-- A ONE-NODE FRAME MINTED AT THE COUNTER, its node installed, over a
-- sound path: the path through it is sound
fresh-at : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s u} {f : Frame Δ s u} {κ : Path Δ lo u t} {ns : NodeState Δ}
             {sched : Sched Δ} {st : EvalSt e} {k}
         → frameNodes f ≡ k ∷ [] → nodeCt sched ≡ k → Sound κ sched st
         → Sound (f ↠[ ≤-refl ] κ) (record sched { mint = setAt nodeᵏ (suc k) (Sched.mint sched) }) (installNode k ns st)
fresh-at {f = f} {κ} {ns} e refl so = fresh-sound f κ ns (λ j a → node-eq (subst (λ xs → T (any (_≡ᵇ j) xs)) e a)) so

-- a map's frame names no node
bare : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s u} {F : FnClo Δ s u} {κ : Path Δ lo u t} {sched : Sched Δ} {st : EvalSt e}
     → Sound κ sched st → Sound (map-f F ↠[ ≤-refl ] κ) sched st
bare {F = F} {κ} so = push-sound (map-f F) ≤-refl κ so (λ k ())

-- a minted source moves no node counter
resrc : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo u} {κ : Path Δ lo u t} {sched : Sched Δ} {st : EvalSt e} {v}
      → Sound κ sched st → Sound κ (record sched { mint = setAt sourceᵏ v (Sched.mint sched) }) st
resrc = sub-ot (λ r∈ → r∈) ≤-refl

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- WHERE IT CAN STILL FAIL: A STEP THAT DOES NOT KEEP AN EMIT'S INSTANT,
  -- or reads the author's variables at slots the renaming moved.  The
  -- map's step splits each emit and applies the author's function to
  -- every payload, renamed under one more binder.
  -- PROBED: `Probed.Map-Step` -- `x + 1` over one hand-built emit, an
  --   `init` then two payloads, under no binder: both payloads mapped,
  --   the instant kept.  Not an emit the impl produced, not a function
  --   reading the author's variables.
  postulate
    lifts-map : ∀ {Θ s u} (f : SFn Γ [] [] Θ s u) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ}
              → EnvRel κ Θ w ρ′ ρ
              → Lifts κ s u (applyClo (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w) (mapStepᵖ (toInstEmitTm κ f)) , ρ′))
                            (map (applyClo (Θ , plainTm f , ρ)))

    -- WHERE IT CAN STILL FAIL: A SEED OR A STEP READING THE AUTHOR'S
    -- VARIABLES AT SLOTS THE MINT'S BINDER MOVED.  The scan's elaboration,
    -- read off by its shape: its step against the author's, its seed's
    -- state against the author's seed.
    lifts-scan : ∀ {Θ s u} (f : SFn Γ [] [] Θ (u ×ᵗ s) u) (z : STm Γ [] [] Θ u) (b : SExp Γ [] [] Θ s)
                   {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} (src : ℕ)
                   {g : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (ScanAᵗ u) (emitᵗ u)}
                   {F : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u)}
                   {i : Tm (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (ScanAᵗ u)} {e″ : Exp (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (emitᵗ s)}
               → EnvRel κ Θ w ρ′ ρ
               → renExp (λ x → x) (λ x → x) w (toInstEmit κ (scanˢ f z b)) ≡ mintᵉ (mapᵉ g (scanᵉ F i e″))
               → ScanLifts κ s u (uniqᵗ ∷ Θ′ , F , src ∷ᵉ ρ′) (Θ , plainTm f , ρ)
                 × V κ u (proj₁ (evalWith i (src ∷ᵉ ρ′))) (evalWith (plainTm z) ρ)

    -- WHERE IT CAN STILL FAIL: THE AUTHOR'S TEST READ AT SLOTS THE MINT'S
    -- BINDER MOVED, or a cut the scan's step decides apart from the plain
    -- test's.  The elaborated takeWhile, read off by its shape: its
    -- cutter's step against the plain test at a budget of one.
    lifts-while : ∀ {Θ s} (f : SFn Γ [] [] Θ s boolᵗ) (b : SExp Γ [] [] Θ s)
                    {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} (src : ℕ)
                    {g : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s) (emitᵗ s)}
                    {c : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s) boolᵗ}
                    {F : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                    {i : Tm (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s)} {e″ : Exp (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (emitᵗ s)}
                → EnvRel κ Θ w ρ′ ρ
                → renExp (λ x → x) (λ x → x) w (toInstEmit κ (takeWhileˢ f b)) ≡ mintᵉ (mapᵉ g (takeWhileᵉ c (scanᵉ F i e″)))
                → CutLifts κ unitᵗ s (λ _ n → n ≡ 1) (uniqᵗ ∷ Θ′ , F , src ∷ᵉ ρ′) (just (Θ , plainTm f , ρ))

    -- AN UNROLLING IS AN AUTHOR'S PROGRAM: some tree whose plain form is
    -- the plain unrolling and whose elaboration, at every renaming, is
    -- the elaborated one.  The equations pin the tree.  Where it can
    -- fail: a μ-var read under a defer under value binders, where the
    -- elaboration's frame term reads the value telescope the unrolling's
    -- weakening moved, and the defer's context transport.
    -- PROBED: `Probed.Unfold` -- both equations by `refl`, the elaborated
    --   one at an abstract renaming, at a μ-var straight under a defer and
    --   at one under a defer under a map's binder.  Not a μ inside a μ,
    --   not a var under a scan's or a test's binder, not a nonempty
    --   outer telescope.
    μ-unfolds : ∀ {Θ u} (b : SExp Γ (u ∷ []) [] Θ u)
              → Σ (SExp Γ [] [] Θ u) λ s′ → plainExp s′ ≡ unfoldμ (plainExp b)
                  × (∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′)
                     → renExp (λ x → x) (λ x → x) w (toInstEmit κ s′)
                       ≡ unfoldμ (renExp (ext∈ (λ x → x)) (λ x → x) w (toInstEmit κ b)))

  open Arms {Γ = Γ} κ using (Carries)

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    -- WHAT ONE SUBSCRIBE KEEPS: what a pass keeps, from related stores
    -- and related sound paths, and the paths related again after.
    Walks : ∀ {u} → Val (plainᵏ Γ κ) (obs (emitᵗ u)) → Val Γ (obs u) → Set
    Walks {u} x′ x =
      ∀ {lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now}
        {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
      → Sound p sP stP → Sound q sI stI
      → subscribeE⇓ {e = ep} x p now sP stP rP → subscribeE⇓ {e = ei} x′ q now sI stI rI
      → Σ (After κ S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    -- the walk at one former, over any related environment
    Elab-Walks : ∀ {Θ u} → SExp Γ [] [] Θ u → Set
    Elab-Walks {Θ} s =
      ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → Walks (Θ′ , renExp (λ x → x) (λ x → x) w (toInstEmit κ s) , ρ′) (Θ , plainExp s , ρ)

    -- A READ OF A SLOT THE IMPL STAMPED: both subscribes at the slot, the
    -- impl's down the restamp
    StampedRead : ∀ {Θ} (i : Fin n) → Set
    StampedRead {Θ} i =
      ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
      → ∀ {lo lo′} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
          {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
      → subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP
      → subscribeE⇓ {e = ei} (Θ′ , input (n ↑ʳ i) , ρ′)
          (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sym eq)
            (map-f (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w)
                           (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ Θ)) subscribeᵛ (varᵗ (here refl))) , ρ′) ↠[ ≤-refl ] q))
          now sI stI rI
      → Σ (After κ S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    -- ONE LEAF PER FORMER WHOSE ELABORATION INSTALLS MORE THAN IT READS.
    -- Each names the run of impl frames `PathRel` pairs with its plain
    -- frame, and the sources and nodes it registers.
    postulate
      -- A COLD SLOT'S READ, AGAINST ITS STAMPED SLOT'S BLOCK: the plain
      -- subscribe at the slot, the impl's at the marked, batched and
      -- stamped read of the script under its mint
      --
      -- THE TWO SCRIPTS AT THE SLOT ARE ONE, read off `Store.scripts`: both
      -- schedules' tables are one author's, the impl's embedded.  The hot
      -- and shared reads stand on it too.
      -- PROBED: `Probed.Stores` -- the STORE conjunct alone, at the root
      --   from empty stores: a cold script, its block run straight to the
      --   root (`cold~`).  Not under a binder, not the values conjunct.
      -- RECOVERY: git show ae5fd17e:agda/evidence/refuted/Refuted/Slot-Scripts.agda
      --   restores the opening store at two cold tables, which refuted this
      --   read over a store blind to the slots.
      cold-read      : ∀ {Θ} (i : Fin n) → lookup κ i ≡ coldᵏ
                     → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                     → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ plainᵗ (lookup Γ i))
                     → ∀ {lo lo′} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                         {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
                     → (S : Store κ sP stP sI stI)
                     → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                     → subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP
                     → subscribeE⇓ {e = ei} (Θ′ , renExp (λ x → x) (λ x → x) w (inputᵖ (n ↑ʳ i) (frameᵛ Θ)) , ρ′)
                         (subst (λ u → Path (plainᵏ Γ κ) lo′ (machineEmitᵗ u) (emitᵗ t)) (sym eq) q) now sI stI rI
                     → Σ (After κ S rP rI) λ A
                         → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
      -- A HOT SLOT'S READ, AGAINST ITS STAMPED SLOT'S: the plain
      -- subscribe at the slot, the impl's at the share wrapping it, under
      -- the restamp handing its subscribe-kind emits this program's frame
      -- PROBED: `Probed.Stores` -- the STORE conjunct alone, at the root
      --   from empty stores: a hot read of two arrivals, its share's
      --   `read~` and `hot~` machine row.  Not under a binder, not the
      --   values conjunct.
      hot-read       : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ → StampedRead {Θ} i
      -- a shared slot's read, against its stamped slot's
      shared-read    : ∀ {Θ} (i : Fin n) → lookup κ i ≡ sharedᵏ → StampedRead {Θ} i
      -- AN `of`'S EMITS CARRY ITS VALUES: the impl's list under its mint,
      -- one emit per value, the last also carrying the end, against the
      -- plain values over related environments
      of-carries     : ∀ {Θ u} (ts : List (STm Γ [] [] Θ u)) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                     → ∀ {L} → renExp (λ x → x) (λ x → x) w (toInstEmit κ (ofˢ ts)) ≡ mintᵉ (ofᵉ L)
                     → ∀ src → Carries {u} (map (λ tm → evalWith tm (src ∷ᵉ ρ′)) L) (map (λ tm → evalWith tm ρ) (plainTms ts))
      -- THE GROUP FOLDED DOWN RELATED PATHS, ENDED, the impl's under its
      -- new source.  A body is `path-pass`, and `walk` would join its
      -- cycle through `inner-walk`, terminating on the plain derivation,
      -- so its helpers would call it rather than take it.  The cycle is
      -- genuine: an `of` under a flattener's outer folds its inners into
      -- the consume, which walks them.  The new source moves only
      -- `Store.bounded`, which a larger counter keeps.
      --
      -- `Sound` OF BOTH PATHS, AS `Pass` CARRIES IT: without it a related
      -- path may pass one merge twice, and a lane subscribed through it
      -- registers a row `Rule.distinct-rows` refuses.
      -- REFUTED: `Refuted.Of-Fold-Sound` -- a path through one merge as
      --   outer and as its own lane, one emit carrying one lane.
      -- DEAD ROUTE: `Sound` from `Store` and `PathRel`.  The store holds
      --   the rule and `π`'s keys below the counter, which gives a
      --   pinned node's freshness, but neither record says where a
      --   path's nodes' rows end, nor that its nodes are distinct.
      of-fold       : ∀ {u lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now}
                         {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI src es vs}
                     → (S : Store κ sP stP sI stI)
                     → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                     → Sound p sP stP → Sound q sI stI
                     → freshId sourceᵏ (Sched.mint sI) ≡ src
                     → Carries {u} es vs
                     → foldPath⇓ now p vs true sP stP rP
                     → foldPath⇓ now q es true (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) stI rI
                     → Σ (After κ S rP rI) λ A
                         → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    postulate
      -- A CELL INSTALLED ON BOTH SIDES, the impl's under its mint: the
      -- pair joins `π` and the tails stay related
      scan-install : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) {lo lo′ u} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)}
                       {k k′ src} (a : Val Γ u) (aI : Val (plainᵏ Γ κ) (ScanAᵗ u))
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → freshId nodeᵏ (Sched.mint sP) ≡ k
                   → freshId sourceᵏ (Sched.mint sI) ≡ src
                   → freshId nodeᵏ (setAt sourceᵏ (suc src) (Sched.mint sI)) ≡ k′
                   → Σ (After κ S ([] , record sP { mint = setAt nodeᵏ (suc k) (Sched.mint sP) } , installNode k (cell-st {t = u} a) stP)
                                  ([] , record sI { mint = setAt nodeᵏ (suc k′) (setAt sourceᵏ (suc src) (Sched.mint sI)) }
                                      , installNode k′ (cell-st {t = ScanAᵗ u} aI) stI)) λ A
                       → (k , k′ ∷ []) ∈ Store.π (After.store A)
                       × PathRel κ (Store.π (After.store A)) (setNode k (cell-st {t = u} a) (EvalSt.nodes stP))
                           (setNode k′ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI)) p q

      -- A TEST INSTALLED ON BOTH SIDES, the impl's test and cell under
      -- its mint: the triple joins `π` and the tails stay related
      while-install : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                        {lo lo′ u} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)}
                        {k k₁ k₂ src} (c : Val (plainᵏ Γ κ) (CutS unitᵗ u))
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → freshId nodeᵏ (Sched.mint sP) ≡ k
                    → freshId sourceᵏ (Sched.mint sI) ≡ src
                    → freshId nodeᵏ (setAt sourceᵏ (suc src) (Sched.mint sI)) ≡ k₂
                    → suc k₂ ≡ k₁
                    → Σ (After κ S ([] , record sP { mint = setAt nodeᵏ (suc k) (Sched.mint sP) } , installNode k (take-st 1) stP)
                                   ([] , record sI { mint = setAt nodeᵏ (suc k₁) (setAt nodeᵏ (suc k₂) (setAt sourceᵏ (suc src) (Sched.mint sI))) }
                                       , installNode k₁ (cell-st {t = CutS unitᵗ u} c) (installNode k₂ (take-st 1) stI))) λ A
                        → (k , k₁ ∷ k₂ ∷ []) ∈ Store.π (After.store A)
                        × PathRel κ (Store.π (After.store A)) (setNode k (take-st 1) (EvalSt.nodes stP))
                            (setNode k₁ (cell-st {t = CutS unitᵗ u} c) (setNode k₂ (take-st 1) (EvalSt.nodes stI))) p q

      -- A FLATTENER INSTALLED ON BOTH SIDES, the impl's restamping cell
      -- under it: the triple joins `π` and the tails stay related.
      -- Read off normal forms, not instantiated: a one-lane merge of the
      -- hot read installs what the relation says -- `π` pairing the plain
      -- merge node with the impl's lane node and cell -- and the
      -- typechecked row of the merge does not finish, the coverage
      -- boundary of `Probed.Stores`.
      flat-install : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                       {lo lo′ u} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)}
                       (op : FlatOp) {m m′ ks} (c : Val (plainᵏ Γ κ) (FlatSᵗ u))
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → freshId nodeᵏ (Sched.mint sP) ≡ m
                   → freshId nodeᵏ (Sched.mint sI) ≡ ks
                   → suc ks ≡ m′
                   → Σ (After κ S ([] , record sP { mint = setAt nodeᵏ (suc m) (Sched.mint sP) } , installNode m (flatSt u op) stP)
                                  ([] , record sI { mint = setAt nodeᵏ (suc m′) (setAt nodeᵏ (suc ks) (Sched.mint sI)) }
                                      , installNode m′ (flatSt (emitᵗ u) op) (installNode ks (cell-st {t = FlatSᵗ u} c) stI))) λ A
                       → (m , m′ ∷ ks ∷ []) ∈ Store.π (After.store A)
                       × PathRel κ (Store.π (After.store A)) (setNode m (flatSt u op) (EvalSt.nodes stP))
                           (setNode m′ (flatSt (emitᵗ u) op) (setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI))) p q

      -- the same with the impl's per-inner merge under the flattener:
      -- the merge's node rides the quadruple
      flat-install-explode : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                               {lo lo′ u} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)}
                               (op : FlatOp) {m m′ ks mX} (c : Val (plainᵏ Γ κ) (FlatSᵗ u))
                           → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                           → freshId nodeᵏ (Sched.mint sP) ≡ m
                           → freshId nodeᵏ (Sched.mint sI) ≡ ks
                           → suc ks ≡ m′
                           → suc m′ ≡ mX
                           → Σ (After κ S ([] , record sP { mint = setAt nodeᵏ (suc m) (Sched.mint sP) } , installNode m (flatSt u op) stP)
                                          ([] , record sI { mint = setAt nodeᵏ (suc mX) (setAt nodeᵏ (suc m′) (setAt nodeᵏ (suc ks) (Sched.mint sI))) }
                                              , installNode mX (flatSt (echoᵗ (emitᵗ u)) (mergeᶠ nothing))
                                                  (installNode m′ (flatSt (emitᵗ u) op) (installNode ks (cell-st {t = FlatSᵗ u} c) stI)))) λ A
                               → (m , m′ ∷ ks ∷ mX ∷ []) ∈ Store.π (After.store A)
                               × PathRel κ (Store.π (After.store A)) (setNode m (flatSt u op) (EvalSt.nodes stP))
                                   (setNode mX (flatSt (echoᵗ (emitᵗ u)) (mergeᶠ nothing))
                                     (setNode m′ (flatSt (emitᵗ u) op) (setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)))) p q

    postulate
      -- A HOP INSTALLED ON BOTH SIDES, the body pending: the merge pair
      -- joins `π`, the sources and rows pair as `defer~`, and the tails
      -- stay related
      -- PROBED: `Probed.Stores` -- the STORE conjunct alone, at the root
      --   from empty stores: a deferred hot read, its hop pending as a
      --   `defer~` source and row and its body not yet subscribed.  Not
      --   a defer under a flattener, not the values conjunct.
      defer-install : ∀ {Θ u} (b : SExp Γ [] [] Θ u) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} {bI}
                    → EnvRel κ Θ w ρ′ ρ
                    → renExp (λ x → x) (λ x → x) w (toInstEmit κ {[]} {[]} (deferˢ b)) ≡ deferᵉ bI
                    → ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                        {lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now nid src ord rid nid′ src′ ord′ rid′}
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → freshId nodeᵏ (Sched.mint sP) ≡ nid → freshId sourceᵏ (Sched.mint sP) ≡ src
                    → freshId ordinalᵏ (Sched.mint sP) ≡ ord → freshId regᵏ (Sched.mint sP) ≡ rid
                    → freshId nodeᵏ (Sched.mint sI) ≡ nid′ → freshId sourceᵏ (Sched.mint sI) ≡ src′
                    → freshId ordinalᵏ (Sched.mint sI) ≡ ord′ → freshId regᵏ (Sched.mint sI) ≡ rid′
                    → let stP′ = register rid (atDyn src lo) (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] p)
                                   (installNode nid (mergeAll-st {t = u} nothing 0 [] false) stP)
                          stI′ = register rid′ (atDyn src′ lo′) (thru-outer mergeAllᵒ nid′ ↠[ ≤-refl ] q)
                                   (installNode nid′ (mergeAll-st {t = emitᵗ u} nothing 0 [] false) stI)
                      in Σ (After κ S
                             ( [] , record sP { mint = setAt regᵏ (suc rid) (setAt nodeᵏ (suc nid) (setAt sourceᵏ (suc src)
                                                         (setAt ordinalᵏ (suc ord) (Sched.mint sP))))
                                              ; live = record { source = src ; ordinal = ord ; elemTy = echoᵗ u
                                                              ; pending = (suc now , (inj₁ tt , inj₂ (Θ , plainExp b , ρ))) ∷ [] }
                                                       ∷ Sched.live sP }
                             , stP′ )
                             ( [] , record sI { mint = setAt regᵏ (suc rid′) (setAt nodeᵏ (suc nid′) (setAt sourceᵏ (suc src′)
                                                         (setAt ordinalᵏ (suc ord′) (Sched.mint sI))))
                                              ; live = record { source = src′ ; ordinal = ord′ ; elemTy = echoᵗ (emitᵗ u)
                                                              ; pending = (suc now , (inj₁ tt , inj₂ (Θ′ , bI , ρ′))) ∷ [] }
                                                       ∷ Sched.live sI }
                             , stI′ )) λ A
                         → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP′) (EvalSt.nodes stI′) p q

    -- a fresh flattener's nodes, related
    flat-init : ∀ {π} u op → FlatNodes {Γ = Γ} κ π u op (flatSt u op) (flatSt (emitᵗ u) op)
    flat-init u (mergeᶠ _) = merge~ []ᵖ
    flat-init u switchᶠ    = switch~ tt
    flat-init u exhaustᶠ   = exhaust~

    -- a flattener's frames walked, one element per emit: the tail related again
    unflat : ∀ {X : Set} {π : X → List (NodeId × List NodeId)} {NP : X → List (NodeId × NodeState Γ)}
               {NI : X → List (NodeId × NodeState (plainᵏ Γ κ))} {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u x y o o′ m m′ ks}
               {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) (echoᵗ x)} {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y}
               {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
               {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
               {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
           → Σ X (λ A → PathRel κ (π A) {t} (NP A) (NI A) (thru-outer o m ↠[ h ] p)
                          (map-f G₀ ↠[ h₁ ] (thru-outer o′ m′ ↠[ h₂ ] (scan-f G₁ ks ↠[ h₃ ] (map-f G₂ ↠[ h₄ ] q)))))
           → Σ X (λ A → PathRel κ (π A) (NP A) (NI A) p q)
    unflat (A , outerElem~ _ pr) = A , pr

    -- the same, one element per inner
    unexplode : ∀ {X : Set} {π : X → List (NodeId × List NodeId)} {NP : X → List (NodeId × NodeState Γ)}
                  {NI : X → List (NodeId × NodeState (plainᵏ Γ κ))} {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u w x y o o′ o″ m m′ ks mX}
                  {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) w} {G₅ : FnClo (plainᵏ Γ κ) w (echoᵗ (echoᵗ x))}
                  {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y} {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
              → Σ X (λ A → PathRel κ (π A) {t} (NP A) (NI A) (thru-outer o m ↠[ h ] p)
                             (map-f G₀ ↠[ h₁ ] (map-f G₅ ↠[ h₂ ] (thru-outer o″ mX ↠[ h₃ ]
                               (thru-outer o′ m′ ↠[ h₄ ] (scan-f G₁ ks ↠[ h₅ ] (map-f G₂ ↠[ h₆ ] q)))))))
              → Σ X (λ A → PathRel κ (π A) (NP A) (NI A) p q)
    unexplode (A , outerExplode~ _ pr) = A , pr

    -- a test's frames walked: the tail related again
    unwhile : ∀ {X : Set} {π : X → List (NodeId × List NodeId)} {NP : X → List (NodeId × NodeState Γ)}
                {NI : X → List (NodeId × NodeState (plainᵏ Γ κ))} {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s k k₁ k₂ G₂ G₃}
                {P : FnClo Γ s boolᵗ} {F₁ : FnClo (plainᵏ Γ κ) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
            → Σ X (λ A → PathRel κ (π A) {t} (NP A) (NI A) (take-f (just P) k ↠[ h ] p)
                           (scan-f F₁ k₁ ↠[ h₁ ] (take-f (just G₂) k₂ ↠[ h₂ ] (map-f G₃ ↠[ h₃ ] q))))
            → Σ X (λ A → PathRel κ (π A) (NP A) (NI A) p q)
    unwhile (A , takeWhile~ _ _ _ _ _ pr) = A , pr
    unwhile (A , spentWhile~ _ _ _ pr)    = A , pr

    -- a scan's frames walked: the tail related again
    unscan : ∀ {X : Set} {π : X → List (NodeId × List NodeId)} {NP : X → List (NodeId × NodeState Γ)}
               {NI : X → List (NodeId × NodeState (plainᵏ Γ κ))} {lo lo′ ℓ ℓ₁ ℓ₂ s u k k′ G}
               {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u)}
               {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂}
               {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)}
           → Σ X (λ A → PathRel κ (π A) {t} (NP A) (NI A) {s = s} (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q)))
           → Σ X (λ A → PathRel κ (π A) (NP A) (NI A) p q)
    unscan (A , scan~ _ _ _ _ _ pr) = A , pr

    -- a subscription at an expression is one at any equal one
    reExp : ∀ {Θ u lo} {ρ} {E E′ : Exp (plainᵏ Γ κ) [] [] Θ u} {q : Path (plainᵏ Γ κ) lo u (emitᵗ t)} {now s st r}
          → E ≡ E′ → subscribeE⇓ {e = ei} (Θ , E , ρ) q now s st r → subscribeE⇓ {e = ei} (Θ , E′ , ρ) q now s st r
    reExp refl d = d

    -- and the plain side's
    reExpᴾ : ∀ {Θ u lo} {ρ} {E E′ : Exp Γ [] [] Θ u} {p : Path Γ lo u t} {now s st r}
           → E ≡ E′ → subscribeE⇓ {e = ep} (Θ , E , ρ) p now s st r → subscribeE⇓ {e = ep} (Θ , E′ , ρ) p now s st r
    reExpᴾ refl d = d

    -- a map's frames walked: the tail related again
    unmap : ∀ {X : Set} {π : X → List (NodeId × List NodeId)} {NP : X → List (NodeId × NodeState Γ)}
              {NI : X → List (NodeId × NodeState (plainᵏ Γ κ))} {lo lo′ ℓ ℓ′ s u F G} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
              {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
          → Σ X (λ A → PathRel κ (π A) {t} (NP A) (NI A) {s = s} (map-f F ↠[ h ] p) (map-f G ↠[ h′ ] q))
          → Σ X (λ A → PathRel κ (π A) (NP A) (NI A) p q)
    unmap (A , map~ _ pr) = A , pr

    -- a takeWhile's walk, at its elaboration's shape: the plain test
    -- installed, the impl's source minted and its test and cell installed,
    -- and the body walked under them
    walk-while : ∀ {Θ s} (f : SFn Γ [] [] Θ s boolᵗ) (b : SExp Γ [] [] Θ s) → Elab-Walks b
               → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
               → ∀ {F : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                   {i : Tm (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s)} {e″ : Exp (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (emitᵗ s)}
               → renExp (λ x → x) (λ x → x) w (toInstEmit κ (takeWhileˢ f b)) ≡ mintᵉ (mapᵉ cutOutᵛ (takeWhileᵉ cutOpenᵛ (scanᵉ F i e″)))
               → e″ ≡ renExp (λ x → x) (λ x → x) (λ y → there (w y)) (toInstEmit κ b)
               → (∀ ρ″ → proj₁ (proj₂ (evalWith i ρ″)) ≡ false)
               → Walks (Θ′ , mintᵉ (mapᵉ cutOutᵛ (takeWhileᵉ cutOpenᵛ (scanᵉ F i e″))) , ρ′) (Θ , plainExp (takeWhileˢ f b) , ρ)
    walk-while f b wb w {ρ′} {ρ} r {F} {i} {e″} eq fu op {stP = stP} {stI = stI} S pr oP oI (subs-takeWhile {nid = k} frP dP)
      (subs-mint {src = src} frS (subs-map (subs-takeWhile {nid = k₂} fr₂ (subs-scan {nid = k₁} fr₁ dI)))) =
      let I = while-install S (evalWith i (src ∷ᵉ ρ′)) pr frP frS fr₂ fr₁
          N₂ = setNode k₂ (take-st 1) (EvalSt.nodes stI)
          v  = evalWith i (src ∷ᵉ ρ′)
          k₁-set : lookupNode k₁ (setNode k₁ (cell-st v) N₂) ≡ just (cell-st {t = CutS unitᵗ _} (tt , (false , proj₂ (proj₂ v))))
          k₁-set = trans (lookup-set k₁ (cell-st v) N₂) (cong (λ x → just (cell-st {t = CutS unitᵗ _} (tt , (x , proj₂ (proj₂ v))))) (op (src ∷ᵉ ρ′)))
          k₂-set : lookupNode k₂ (setNode k₁ (cell-st (evalWith i (src ∷ᵉ ρ′))) N₂) ≡ just (take-st 1)
          k₂-set = trans (set-above k₁ k₂ (cell-st (evalWith i (src ∷ᵉ ρ′))) N₂ (apart k₁ k₂ (λ e → 1+n≢n (trans fr₁ (sym e)))))
                         (lookup-set k₂ (take-st 1) (EvalSt.nodes stI))
          X = wb (λ y → there (w y)) r (After.store (proj₁ I))
                (takeWhile~ (proj₁ (proj₂ I)) (lookup-set k (take-st 1) (EvalSt.nodes stP))
                  k₁-set k₂-set
                  (lifts-while f b w src r eq) (proj₂ (proj₂ I)))
                (fresh-at refl frP oP) (fresh-at refl fr₁ (fresh-at refl fr₂ (bare (resrc oI))))
                dP (reExp fu dI)
      in unwhile (_⨾_ κ (proj₁ I) (proj₁ X) , proj₂ X)

    -- a flattener's walk, one element per emit: the plain node
    -- installed, the impl's cell and node installed, and the body walked
    -- under them
    walk-flat-elem : ∀ {Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ (echoᵗ u)) → Elab-Walks b
                   → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                   → ∀ {i : Tm (plainᵏ Γ κ) [] [] Θ′ (FlatSᵗ u)}
                   → Walks (Θ′ , mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ flatStepᵛ i
                                   (flattenᵉ op (mapᵉ elemᵛ (renExp (λ x → x) (λ x → x) w (toInstEmit κ b))))) , ρ′)
                           (Θ , plainExp (flattenˢ op b) , ρ)
    walk-flat-elem {u = u} op b wb w {ρ′} r {i} {stP = stP} {stI = stI} S pr oP oI (subs-flatten (sub-all {nid = m} frP dP))
      (subs-map (subs-scan {nid = ks} frK (subs-flatten (sub-all {nid = m′} frM (subs-map dI))))) =
      let c  = evalWith i ρ′
          N  = setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)
          I  = flat-install S op c pr frP frK frM
          F  = proj₁ (proj₂ I) , flatSt u op , flatSt (emitᵗ u) op
             , lookup-set m (flatSt u op) (EvalSt.nodes stP) , lookup-set m′ (flatSt (emitᵗ u) op) N , flat-init u op
             , c , trans (set-above m′ ks (flatSt (emitᵗ u) op) N (apart m′ ks (λ e → 1+n≢n (trans frM (sym e)))))
                         (lookup-set ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI))
          X  = wb w r (After.store (proj₁ I)) (outerElem~ {op = op} F (proj₂ (proj₂ I)))
                 (fresh-at refl frP oP) (bare (fresh-at refl frM (fresh-at refl frK (bare oI)))) dP dI
      in unflat (_⨾_ κ (proj₁ I) (proj₁ X) , proj₂ X)

    -- the same, one element per inner: the impl's per-inner merge
    -- installed between its flattener and the body
    walk-flat-explode : ∀ {Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ (echoᵗ u)) → Elab-Walks b
                      → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                      → ∀ {i : Tm (plainᵏ Γ κ) [] [] Θ′ (FlatSᵗ u)}
                      → Walks (Θ′ , mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ flatStepᵛ i
                                      (flattenᵉ op (flattenᵉ (mergeᶠ nothing) (mapᵉ (pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))))
                                        (mapᵉ explodeᵛ (renExp (λ x → x) (λ x → x) w (toInstEmit κ b))))))) , ρ′)
                              (Θ , plainExp (flattenˢ op b) , ρ)
    walk-flat-explode {u = u} op b wb w {ρ′} r {i} {stP = stP} {stI = stI} S pr oP oI (subs-flatten (sub-all {nid = m} frP dP))
      (subs-map (subs-scan {nid = ks} frK (subs-flatten (sub-all {nid = m′} frM (subs-flatten (sub-all {nid = mX} frX (subs-map (subs-map dI)))))))) =
      let c  = evalWith i ρ′
          N  = setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)
          xX = flatSt (echoᵗ (emitᵗ u)) (mergeᶠ nothing)
          x′ = flatSt (emitᵗ u) op
          I  = flat-install-explode S op c pr frP frK frM frX
          F  = proj₁ (proj₂ I) , flatSt u op , x′
             , lookup-set m (flatSt u op) (EvalSt.nodes stP)
             , trans (set-above mX m′ xX (setNode m′ x′ N) (apart mX m′ (λ e → 1+n≢n (trans frX (sym e)))))
                     (lookup-set m′ x′ N)
             , flat-init u op
             , c , trans (set-above mX ks xX (setNode m′ x′ N)
                           (apart mX ks (λ e → <⇒≢ (<-trans (n<1+n ks) (n<1+n (suc ks))) (trans e (sym (trans (cong suc frM) frX))))))
                         (trans (set-above m′ ks x′ N (apart m′ ks (λ e → 1+n≢n (trans frM (sym e)))))
                                (lookup-set ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)))
          X  = wb w r (After.store (proj₁ I)) (outerExplode~ {op = op} F (proj₂ (proj₂ I)))
                 (fresh-at refl frP oP) (bare (bare (fresh-at refl frX (fresh-at refl frM (fresh-at refl frK (bare oI)))))) dP dI
      in unexplode (_⨾_ κ (proj₁ I) (proj₁ X) , proj₂ X)


    -- a defer's walk: the hop's node, source and row on both sides
    walk-defer : ∀ {Θ u} (b : SExp Γ [] [] Θ u) → Elab-Walks (deferˢ b)
    walk-defer b w r S pr _ _ (subs-defer f₁ f₂ f₃ f₄) (subs-defer g₁ g₂ g₃ g₄) = defer-install b w r refl S pr f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄

    -- a flattener's walk at either elaboration
    walk-flat : ∀ {Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ (echoᵗ u)) → Elab-Walks b → (pi : Bool)
              → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
              → Walks (Θ′ , renExp (λ x → x) (λ x → x) w (flattenᵖ op pi (frameᵛ Θ) (toInstEmit κ b)) , ρ′)
                      (Θ , plainExp (flattenˢ op b) , ρ)
    walk-flat op b wb false w r = walk-flat-elem op b wb w r
    walk-flat op b wb true  w r = walk-flat-explode op b wb w r

    -- an `of`'s walk: the impl mints its source, and both fold the
    -- group and end
    walk-of : ∀ {Θ u} (ts : List (STm Γ [] [] Θ u)) → Elab-Walks (ofˢ ts)
    walk-of ts w r S pr oP oI (subs-of dP) (subs-mint {src = src} fr (subs-of dI)) = of-fold S pr oP oI fr (of-carries ts w r refl src) dP dI

    -- a cold slot's walk: the impl's read past the transport
    walk-cold : ∀ {Θ} (i : Fin n) → lookup κ i ≡ coldᵏ → Elab-Walks {Θ} (inputˢ i)
    walk-cold i e w r S pr _ _ dP dI with lookup κ i in ek | stampedSlot Γ κ i
    walk-cold i e w r S pr _ _ dP dI | coldᵏ | eq = cold-read i ek w r eq S pr dP (read-machine w eq _ dI)
    walk-cold i () w r S pr _ _ dP dI | hotᵏ | _
    walk-cold i () w r S pr _ _ dP dI | sharedᵏ | _

    -- a hot slot's walk: the impl's read peeled to its stamped slot
    walk-hot : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ → Elab-Walks {Θ} (inputˢ i)
    walk-hot i e w r S pr _ _ dP dI with lookup κ i in ek | stampedSlot Γ κ i
    walk-hot i e w r S pr _ _ dP (subs-map dJ) | hotᵏ | eq = hot-read i ek w r eq S pr dP (read-input _ eq dJ)
    walk-hot i () w r S pr _ _ dP dI | coldᵏ | _
    walk-hot i () w r S pr _ _ dP dI | sharedᵏ | _

    -- a shared slot's walk, the same
    walk-shared : ∀ {Θ} (i : Fin n) → lookup κ i ≡ sharedᵏ → Elab-Walks {Θ} (inputˢ i)
    walk-shared i e w r S pr _ _ dP dI with lookup κ i in ek | stampedSlot Γ κ i
    walk-shared i e w r S pr _ _ dP (subs-map dJ) | sharedᵏ | eq = shared-read i ek w r eq S pr dP (read-input _ eq dJ)
    walk-shared i () w r S pr _ _ dP dI | coldᵏ | _
    walk-shared i () w r S pr _ _ dP dI | hotᵏ | _

    -- the one arm that reads `κ`, one leaf per kind
    walk-input : ∀ {Θ} (i : Fin n) (k : Kind) → lookup κ i ≡ k → Elab-Walks {Θ} (inputˢ i)
    walk-input i coldᵏ   e = walk-cold i e
    walk-input i hotᵏ    e = walk-hot i e
    walk-input i sharedᵏ e = walk-shared i e

    -- THE WALK DESCENDS THE PLAIN TREE'S GUARDED SIZE, not the tree: an
    -- unrolling is no smaller, but it reads its μ-var only past a defer,
    -- which the size does not count and the walk does not enter.
    walk< : ∀ {Θ u} (s : SExp Γ [] [] Θ u) → Acc _<_ (gsizeᵉ (plainExp s)) → Elab-Walks s
    walk< (inputˢ i) _     = walk-input i (lookup κ i) refl
    walk< (ofˢ ts) _       = walk-of ts
    walk< {Θ} {u} emptyˢ _ w {ρ′} {ρ} r S pr oP oI (subs-empty f) dI = walk-of {Θ} {u} [] w {ρ′} {ρ} r S pr oP oI (subs-of {ts = []} f) dI
    walk< (takeWhileˢ f b) (acc rs) w r = walk-while f b (walk< b (rs (s≤s (m≤n+m _ _)))) w r refl (renExp-fuse there (ext∈ w) (toInstEmit κ b)) (λ _ → refl)
    walk< (mapˢ f b) (acc rs) w r S pr oP oI (subs-map dP) (subs-map dI) = unmap (walk< b (rs (s≤s (m≤n+m _ _))) w r S (map~ (lifts-map f w r) pr) (bare oP) (bare oI) dP dI)
    walk< (scanˢ f z b) (acc rs) w {ρ′} {ρ} r {stP = stP} {stI = stI} S pr oP oI (subs-scan {nid = k} frP dP) (subs-mint {src = src} frS (subs-map (subs-scan {i = iI} {nid = k′} frI dI))) =
      let L = lifts-scan f z b w src {i = iI} r refl
          I = scan-install S (evalWith (plainTm z) ρ) (evalWith iI (src ∷ᵉ ρ′)) pr frP frS frI
          X = walk< b (rs (s≤s (≤-trans (m≤n+m _ (gsizeᵗ (plainTm z))) (m≤n+m (gsizeᵗ (plainTm z) + gsizeᵉ (plainExp b)) (gsizeᵗ (plainTm f)))))) (λ y → there (w y)) r (After.store (proj₁ I))
                (scan~ (proj₁ (proj₂ I)) (lookup-set k (cell-st (evalWith (plainTm z) ρ)) (EvalSt.nodes stP))
                  (lookup-set k′ (cell-st (evalWith iI (src ∷ᵉ ρ′))) (EvalSt.nodes stI)) (proj₂ L) (proj₁ L) (proj₂ (proj₂ I)))
                (fresh-at refl frP oP) (fresh-at refl frI (bare (resrc oI)))
                dP (reExp (renExp-fuse there (ext∈ w) (toInstEmit κ b)) dI)
      in unscan (_⨾_ κ (proj₁ I) (proj₁ X) , proj₂ X)
    walk< (flattenˢ op b) (acc rs) w r = walk-flat op b (walk< b (rs (n<1+n _))) (perInnerˢ op b) w r
    walk< (μˢ b) (acc rs) w r S pr oP oI (subs-μ dP) (subs-μ dI) =
      let (s′ , pe , ie) = μ-unfolds b
      in walk< s′ (rs (s≤s (≤-reflexive (trans (cong gsizeᵉ pe) (gsize-unfoldμ (plainExp b))))))
           w r S pr oP oI (reExpᴾ (sym pe) dP) (reExp (sym (ie w)) dI)
    walk< (varˢ ()) _
    walk< (deferˢ b) _     = walk-defer b

    walk : ∀ {Θ u} (s : SExp Γ [] [] Θ u) → Elab-Walks s
    walk s = walk< s (<-wellFounded _)

-- WHERE IT CAN STILL FAIL: A HOT SCRIPT LIVE ON ONE SIDE ONLY, or two
-- live at different places.  Both lists are the slots' hot scripts in
-- slot order, the impl's read off its raw half.
-- PROBED: `Probed.Opening` -- one hot script of two arrivals, both
--   payloads left on each side.  Not two hot slots, not a shared slot.
postulate
  init-sources : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
               → Pointwise (Src κ) (Sched.live (sched-init (plainExp e) (plainSlots ins)))
                                    (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)))

-- WHERE IT CAN STILL FAIL: A HOT SCRIPT AT A DIFFERENT TICK OR RANK ON
-- ONE SIDE.  Both lists are the slots' hot scripts in slot order.
-- PROBED: `Probed.Opening` -- one hot script of two arrivals.  Not two
--   hot slots, so no rank was compared.
postulate
  init-sync : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
            → Sync (Sched.live (sched-init (plainExp e) (plainSlots ins)))
                   (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)))

-- WHERE IT CAN STILL FAIL: A HOT SCRIPT NUMBERED APART FROM ITS RAW
-- READ.  Both lists are the slots' hot scripts, numbered by slot.
postulate
  init-numbers : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
               → Pointwise (λ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) → SrcNum κ (LiveSource.source l) (LiveSource.source l′))
                           (Sched.live (sched-init (plainExp e) (plainSlots ins)))
                           (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)))

-- the hot scripts live before anything is subscribed, one per slot
postulate
  init-distinct : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
                → Unique (map LiveSource.source (Sched.live (sched-init (plainExp e) (plainSlots ins))))
                × Unique (map LiveSource.source (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins))))

-- TWIN: `ib-renᵉ` -- the same walk over `renExp`'s clauses, a binder's
--   `ext∈` the one place the identity is not definitional.
postulate
  renExp-id : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (x : Exp Γ Δᵍ Δ Θ t) → renExp (λ y → y) (λ y → y) (λ y → y) x ≡ x

-- the hot scripts a slot table starts live are numbered by their slots
mkHot-below : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (i : Fin n) → All (λ l → LiveSource.source l < n) (mkHot ins i)
mkHot-below ins i with ins i
... | scripted (hot async) = toℕ<n i ∷ []
... | scripted (cold _ _)  = []
... | shared _             = []

init-below : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → All (_< n) (map LiveSource.source (Sched.live (sched-init e ins)))
init-below e ins = map⁺ (concat⁺ (tabulate⁺ (mkHot-below ins)))

-- no registration yet, so the sweep keeps the slots alone: and both lists hold slots only
guard-slot : ∀ {n} {Γ : Ctx n} {t} {l : LiveSource Γ} → LiveSource.source l < n → guardOf {t = t} [] l ≡ true
guard-slot lt = ∨-true _ _ (<⇒<ᵇ lt)
  where
    ∨-true : ∀ a b → T a → (a ∨ b) ≡ true
    ∨-true true b _ = refl

init-swept : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} {t t′} {R : LiveSource Γ → LiveSource Γ′ → Set} {ls ls′}
           → Pointwise R ls ls′ → All (_< n) (map LiveSource.source ls) → All (_< m) (map LiveSource.source ls′)
           → Pointwise (λ l l′ → guardOf {t = t} [] l ≡ guardOf {t = t′} [] l′) ls ls′
init-swept []ᵖ        []         []           = []ᵖ
init-swept {t = t} {t′} (_∷ᵖ_ {l} {l′} _ rs) (lt ∷ lts) (lt′ ∷ lts′) = trans (guard-slot {t = t} {l = l} lt) (sym (guard-slot {t = t′} {l = l′} lt′)) ∷ᵖ init-swept {t = t} {t′ = t′} rs lts lts′

-- BEFORE ANYTHING IS SUBSCRIBED THE STORES ARE EMPTY, and the impl's
-- mint touches only the counter, which the relation does not read.
init-store : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) (μ : Mint)
           → n + n < counter μ sourceᵏ
           → Store κ (sched-init (plainExp e) (plainSlots ins)) (st-init (plainExp e))
                     (record (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)) { mint = μ })
                     (st-init (elaborateImpl κ e))
init-store κ {t} e ins μ big = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; pairs-below = [] , []
  ; sources = init-sources κ e ins
  ; numbers = init-numbers κ e ins
  ; distinct = init-distinct κ e ins
  ; sync    = init-sync κ e ins
  ; rows    = []
  ; dlv-alike = tt
  ; dying-alike = tt
  ; latches = λ _ → (λ _ → refl , refl) , (λ _ → refl , refl)
  ; bounded = mapᵃ (λ lt → <-trans lt (n<1+n _)) (init-below (plainExp e) (plainSlots ins))
            , mapᵃ (λ lt → <-trans lt big) (init-below (elaborateImpl κ e) (embedSlotsImpl ins))
  ; swept   = init-swept {t = t} {t′ = emitᵗ t} (init-sources κ e ins) (init-below (plainExp e) (plainSlots ins)) (init-below (elaborateImpl κ e) (embedSlotsImpl ins))
  ; uncut   = [] , []
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = ins , refl , refl
  }

-- THE IMPL'S ROOT SUBSCRIBE IS ITS MINT'S BODY'S, at the token the mint
-- drew: the frame the elaboration closes over.
minted : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
       → Σ ℕ λ src → n + n < src ×
         subscribeE⇓ {e = elaborateImpl κ e}
           (uniqᵗ ∷ [] , renExp (λ x → x) (λ x → x) (λ x → x) (toInstEmit κ e) , src ∷ᵉ []ᵉ) (root {lo = n + n}) 0
           (record (sched-init (elaborateImpl κ e) (embedSlotsImpl ins))
              { mint = setAt sourceᵏ (suc src) (Sched.mint (sched-init (elaborateImpl κ e) (embedSlotsImpl ins))) })
           (st-init (elaborateImpl κ e)) (Σ⁰.fst⁰ (subscribe! (elaborateImpl κ e) (embedSlotsImpl ins)))
minted {n} κ e ins = go (proj₁ (Σ⁰.snd⁰ (subscribe! (elaborateImpl κ e) (embedSlotsImpl ins))))
  where
  sI = sched-init (elaborateImpl κ e) (embedSlotsImpl ins)

  go : ∀ {rI} → subscribeE⇓ {e = elaborateImpl κ e} ([] , elaborateImpl κ e , []ᵉ) (root {lo = n + n}) 0
                    sI (st-init (elaborateImpl κ e)) rI
     → Σ ℕ λ src → n + n < src ×
       subscribeE⇓ {e = elaborateImpl κ e}
         (uniqᵗ ∷ [] , renExp (λ x → x) (λ x → x) (λ x → x) (toInstEmit κ e) , src ∷ᵉ []ᵉ) (root {lo = n + n}) 0
         (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) (st-init (elaborateImpl κ e)) rI
  go {rI} (subs-mint {src = src} fresh dI) =
    src , ≤-reflexive fresh , subst (λ E → subscribeE⇓ {e = elaborateImpl κ e} (uniqᵗ ∷ [] , E , src ∷ᵉ []ᵉ) (root {lo = n + n}) 0
                         (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) (st-init (elaborateImpl κ e)) rI)
                (sym (renExp-id (toInstEmit κ e))) dI

-- THE ROOT SUBSCRIBES ARE THE WALK AT THE PROGRAM, from empty stores
root-walk : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
          → Store κ (proj₁ (proj₂ (Σ⁰.fst⁰ (subscribe! (plainExp e) (plainSlots ins)))))
                    (proj₂ (proj₂ (Σ⁰.fst⁰ (subscribe! (plainExp e) (plainSlots ins)))))
                    (proj₁ (proj₂ (Σ⁰.fst⁰ (subscribe! (elaborateImpl κ e) (embedSlotsImpl ins)))))
                    (proj₂ (proj₂ (Σ⁰.fst⁰ (subscribe! (elaborateImpl κ e) (embedSlotsImpl ins)))))
          × Pointwise (λ a w → V κ t (proj₂ a) w)
                      (readᴵ (proj₁ (Σ⁰.fst⁰ (subscribe! (elaborateImpl κ e) (embedSlotsImpl ins)))))
                      (readᴾ (proj₁ (Σ⁰.fst⁰ (subscribe! (plainExp e) (plainSlots ins)))))
root-walk κ e ins = After.store (proj₁ W) , After.values (proj₁ W)
  where
  S₀ = init-store κ e ins _ (<-trans (proj₁ (proj₂ (minted κ e ins))) (n<1+n _))
  W = walk κ e (λ x → x) (λ ()) S₀ root~ (sound (Store.ruleP S₀) (λ k ()) (λ k ()) _) (sound (Store.ruleI S₀) (λ k ()) (λ k ()) _)
       (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp e) (plainSlots ins)))) (proj₂ (proj₂ (minted κ e ins)))
