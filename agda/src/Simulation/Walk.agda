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
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ʳ; splitAt-↑ʳ; splitAt⁻¹-↑ʳ)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.List.Relation.Unary.All using (All; _∷_; []) renaming (map to mapᵃ)
open import Data.List.Relation.Unary.All.Properties using (map⁺; concat⁺; tabulate⁺)
open import Data.Bool    using (Bool; T; true; false; _∨_; _∧_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Bool.ListAction using (any)
open import Data.Unit    using (tt)
open import Rx.Evaluator.Reducible.Support using (fresh-path)
open import Data.Nat     using (ℕ; suc; _+_; _<_; _≤_; s<s⁻¹; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Properties using (≤⇒≯; +-cancelˡ-≤; +-cancelˡ-<; <-trans; n<1+n; n≤1+n; ≤-trans; ≤-reflexive; ≤-refl; <⇒<ᵇ; <⇒≢; 1+n≢n; m<n⇒m<1+n)
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just; nothing)

open import Rx.Prim      using (hot; cold)
open import Rx.Exp       using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import Rx.Exp       using (Ctx; Val; Closed; Exp; unfoldμ; ofᵉ; Ren∈; ext∈; renExp; renTm; applyClo; []ᵉ; _∷ᵉ_; uniqᵗ;
  unitᵗ; boolᵗ; _×ᵗ_; evalWith; input; mintᵉ; deferᵉ; mapᵉ; scanᵉ; takeWhileᵉ; flattenᵉ; sndᵗ;
  varᵗ; pairᵗ; inlᵗ; inrᵗ; unit̂; Fn; FnClo; Tm; Env)
open import Rx.Mint      using (Mint; setAt; sourceᵏ; nodeᵏ; ordinalᵏ; regᵏ; counter; freshId)
open import Rx.Evaluator using (Sched; EvalSt; LiveSource; Path; root; map-f; scan-f; take-f; _↠[_]_; NodeId; NodeState; sched-init; st-init;
  Frame; frameNodes; mkHot; memoᶠ; Stream; resolve; memberSource; atSlot; lowerFloor; installNode; setNode; cell-st; take-st; lookupNode; echoᵗ; thru-outer; register; atDyn; mergeAll-st; mergeAllᵒ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import Rx.Evaluator.Domain using (subscribeE⇓; foldPath⇓; fold-step; step-map; sharedConnect⇓; subs-floor; subs-shared; subs-hot-done; subs-hot-live;
  subs-cold-sync; subs-cold-async; slot-spent; slot-join; slot-connect; subs-map; subs-mint; subs-of; subs-empty; subs-scan; subs-takeWhile; subs-flatten; subs-defer; subs-μ; sub-all; flatSt)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set; set-above)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; rule; Sound; sound; fresh-sound; push-sound; sub-ot; node-eq; sub-rule)
open import Data.Fin     using (Fin; zero; suc; toℕ; splitAt; _↑ʳ_)
open import Data.Vec     using (lookup)
open import SExp.Syntax  using (SExp; STm; SFn; Kind; Kinds; hotᵏ; coldᵏ; sharedᵏ; plainᵏ; plainᵗ; emitᵗ; inputˢ; ofˢ; emptyˢ; takeWhileˢ; mapˢ; scanˢ;
  flattenˢ; μˢ; varˢ; deferˢ)
open import SExp.Plain   using (plainExp; plainTm; plainTms)
open import Simulation.Arm using (module Arms; Gone)
open import SExp.Elaborate using (toInstEmit; toInstEmitTm; plainᶜ⁺; mapStepᵖ; ScanAᵗ; CutS; cutOpenᵛ; cutOutᵛ;
  FlatSᵗ; flatStepᵛ; elemᵛ; explodeᵛ; flattenᵖ; perInnerˢ; frameᵛ; stampedSlot; restampᵛ; subscribeᵛ; inputᵖ)
open import SExp.InstEmit using (machineEmitᵗ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl; embedAt; stampedSlotᵏ; hotSlotAt)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; plainSlots)
open import Simulation.Schedules using (Sync)
open import Simulation.After using (readᴾ; readᴵ; module Kept)
open import Simulation.Write using (apart)
open import Simulation.Install using (install; fresh-set; weak; named-mint)
open import Simulation.Hop using (hop-register)
open import Simulation.Cold using (ColdBlock; cold-register)
open import Simulation.Slot-Join using (join-read)
open import Simulation.Catch using (Kept; Stamps; AtFrame; OnPath; on-path; catch-same; kept-same; kept-trans; kept-catch;
  kept-unmoved; unmoved-set; by-sub; by-sub⁻)
open Kept using (After; module After; _⨾_; after)
open import Simulation.Walks using (module Walkers)
open import Simulation.Size using (sz-subscribeE; sz-foldPath; sz-1)
open import Simulation.Pass.Path using (module PassP)
open import Simulation.Stores using (live; guardOf; V; EnvRel; Lifts; ScanLifts; CutLifts; PathRel; root~; map~; scan~; takeWhile~;
  spentWhile~; FlatNodes; merge~; switch~; exhaust~; outerElem~; outerExplode~; Store; Src; Arr;
  SrcNum; []; elab; LiveIf; live-if; live-if-above; live-if-cons; live-if-thru; flat-live; outerDoneᵇ)


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

-- a fold of nothing through a read's restamp is the fold past it
peel-read : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {A B u lo} (eq : A ≡ B) {F : FnClo Δ B u} {q : Path Δ lo u t}
              {now fin sched st out sched′ st′}
          → foldPath⇓ {e = e} now (subst (λ v → Path Δ lo v t) (sym eq) (map-f F ↠[ ≤-refl ] q)) [] fin sched st (out , sched′ , st′)
          → foldPath⇓ now q [] fin sched st (out , sched′ , st′)
peel-read refl (fold-step step-map f) = f

-- a table read at a slot is the slot
memoᶠ-at : ∀ {m} {P : Fin m → Set} (f : ∀ j → P j) j → memoᶠ f j ≡ f j
memoᶠ-at f zero    = refl
memoᶠ-at f (suc j) = memoᶠ-at (λ j → f (suc j)) j

-- A HOT SLOT READ PLAIN IS ITS SCRIPT, READ IMPL AT ITS STAMPED SLOT A
-- SHARE: neither run's read of it takes the other kinds' rules
plain-hot-slot : ∀ {m} {Δ : Ctx m} {κ : Kinds m} (ins : SimulSlots Δ κ) (j : Fin m) → lookup κ j ≡ hotᵏ
               → Σ _ λ ok → Σ _ λ as → plainSlots ins j ≡ scripted {ok = ok} (hot as)
plain-hot-slot {κ = κ} ins j ek with lookup κ j | ins j
plain-hot-slot ins j refl | hotᵏ | hotˢ _ = _ , _ , refl

-- A COLD SLOT READ PLAIN IS ITS SCRIPT, COLD
plain-cold-slot : ∀ {m} {Δ : Ctx m} {κ : Kinds m} (ins : SimulSlots Δ κ) (j : Fin m) → lookup κ j ≡ coldᵏ
                → Σ _ λ ok → Σ _ λ ss → Σ _ λ as → plainSlots ins j ≡ scripted {ok = ok} (cold ss as)
plain-cold-slot {κ = κ} ins j ek with lookup κ j | ins j
plain-cold-slot ins j refl | coldᵏ | coldˢ _ _ = _ , _ , _ , refl

scriptedᵇ : ∀ {m} {Δ : Ctx m} {k u} → Slot Δ k u → Bool
scriptedᵇ (scripted _) = true
scriptedᵇ (shared _)   = false

impl-hot-slot : ∀ {m} {Δ : Ctx m} {κ : Kinds m} (ins : SimulSlots Δ κ) (j : Fin m) → lookup κ j ≡ hotᵏ
              → scriptedᵇ (embedSlotsImpl ins (m ↑ʳ j)) ≡ false
impl-hot-slot {m} {Δ} {κ} ins j ek = at (splitAt m (m ↑ʳ j)) refl
  where
    at-fin : ∀ {x y : Fin (m + m)} (p : x ≡ y) (s : Slot (plainᵏ Δ κ) (toℕ x) (lookup (plainᵏ Δ κ) x))
           → scriptedᵇ s ≡ false → scriptedᵇ (subst (λ x′ → Slot (plainᵏ Δ κ) (toℕ x′) (lookup (plainᵏ Δ κ) x′)) p s) ≡ false
    at-fin refl s f = f
    at-ty : ∀ {k u u′} (p : u ≡ u′) (s : Slot (plainᵏ Δ κ) k u) → scriptedᵇ s ≡ false → scriptedᵇ (subst (Slot (plainᵏ Δ κ) k) p s) ≡ false
    at-ty refl s f = f
    hot-at : ∀ {j′} (k≡ : lookup κ j′ ≡ hotᵏ) b e → scriptedᵇ (hotSlotAt {Γ = Δ} κ j′ k≡ b e) ≡ false
    hot-at k≡ true  _ = refl
    hot-at k≡ false _ = refl
    by-kind : ∀ {j′} kd (k≡ : lookup κ j′ ≡ kd) (s : SimulSlot Δ κ (toℕ j′) (lookup Δ j′) kd) → kd ≡ hotᵏ
            → scriptedᵇ (stampedSlotᵏ κ j′ kd k≡ s) ≡ false
    by-kind hotᵏ    k≡ (hotˢ _) _ = hot-at k≡ _ refl
    by-kind coldᵏ   _ _ ()
    by-kind sharedᵏ _ _ ()
    at : ∀ s (e : splitAt m (m ↑ʳ j) ≡ s) → scriptedᵇ (embedAt ins (m ↑ʳ j) s e) ≡ false
    at (inj₁ _) e with trans (sym e) (splitAt-↑ʳ m m j)
    ... | ()
    at (inj₂ j′) e =
      at-fin (splitAt⁻¹-↑ʳ e) _
        (at-ty (sym (stampedSlot Δ κ j′)) _
          (by-kind (lookup κ j′) refl (ins j′) (subst (λ x → lookup κ x ≡ hotᵏ) (sym (inj₂-injective (trans (sym e) (splitAt-↑ʳ m m j)))) ek)))

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- WHERE IT CAN STILL FAIL: A STEP THAT DOES NOT KEEP AN EMIT'S STAMP,
  -- or reads the author's variables at slots the renaming moved.  The
  -- map's step splits each emit and applies the author's function to
  -- every payload, renamed under one more binder.
  -- PROBED: `Probed.Map-Step` -- `x + 1` over one hand-built emit, an
  --   `init` then two payloads, under no binder: both payloads mapped,
  --   the stamp kept; and `x + y` reading the author's variable 4 past
  --   the step's binder, once at the identity renaming and once at one
  --   moving it a slot out past a value 8 it does not own, or past a
  --   mint's token.  Not an emit the impl produced.
  -- PROBED: make qc-store QC='16 200 3' QC_BUDGET=900 QC_DRAW='{"exp":[1,1,6,1,1,0,2,1,0,0,0,2,2],"fan":[1,1,1,1,1,0,1,1,1,0],"leaf":[3,1,1],"script":[1,1,1,1,1,1],"slot":[2,1,1,1,0,0],"reach":["map"]}'
  --   decided by `CLI.Store-Check`'s `lifts?` at every map on a related
  --   path: 200 agree, every case a map, drawn steps under binders, fan
  --   lanes and cuts.  Emits: every word of up to three events over
  --   inits and closes at two tokens, each close reason, a handoff, a
  --   complete and two payloads, at every kind, plus three longer
  --   samples; not the run's own emits.  Fails when `lifts?` refuses
  --   the plumbing kind, and when the enumerated emits' plain values
  --   drop one.
  postulate
    lifts-map : ∀ {Θ s u} (f : SFn Γ [] [] Θ s u) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ}
              → EnvRel κ Θ w ρ′ ρ
              → Lifts κ s u (applyClo (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w) (mapStepᵖ (toInstEmitTm κ f)) , ρ′))
                            (map (applyClo (Θ , plainTm f , ρ)))

    -- WHERE IT CAN STILL FAIL: A SEED OR A STEP READING THE AUTHOR'S
    -- VARIABLES AT SLOTS THE MINT'S BINDER MOVED.  The scan's elaboration,
    -- read off by its shape: its step against the author's, its seed's
    -- state against the author's seed.
    -- PROBED: `Probed.Walk-Leaves` -- a running sum plus the author's
    --   variable, seeded by it, past the mint's binder: the seed, and the
    --   step over one payload.  Two payloads in one emit do not finish
    --   in the typechecker, a coverage boundary.
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
    -- PROBED: `Probed.Walk-Leaves` -- a test below the author's variable,
    --   past the mint's binder, at one payload it fails and one it
    --   passes.  A cut inside a two-payload emit does not finish in the
    --   typechecker, a coverage boundary.
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
    --   one at an abstract renaming, at a μ-var straight under a defer,
    --   under a defer under a map's, a scan step's and a test's binder,
    --   past an inner μ's binder, and under a map's at a nonempty outer
    --   telescope, and read twice, at the root and under a map's binder.
    --   Not a μ-var under a flattener's inner literal.
    μ-unfolds : ∀ {Θ u} (b : SExp Γ (u ∷ []) [] Θ u)
              → Σ (SExp Γ [] [] Θ u) λ s′ → plainExp s′ ≡ unfoldμ (plainExp b)
                  × (∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′)
                     → renExp (λ x → x) (λ x → x) w (toInstEmit κ s′)
                       ≡ unfoldμ (renExp (ext∈ (λ x → x)) (λ x → x) w (toInstEmit κ b)))

  open Arms {Γ = Γ} κ using (Carries) renaming ([] to []ᶜ)

  open Walkers {Γ = Γ} κ using (frameAt; Walker)

  postulate
    -- AN `of`'S EMITS STAND AT ITS PROGRAM'S FRAME, subscribe-kind
    -- PROBED: `Probed.Opening` -- two values at the root, and one under a
    --   value binder, the frame apart from the `of`'s source and from the
    --   bound value; both again at a renaming moving the telescope a slot
    --   out past a value 8 or 5 it does not own, and the root's past a
    --   mint's token.  Not a `ofˢ` whose terms read a variable.
    of-emits : ∀ {Θ u} (ts : List (STm Γ [] [] Θ u)) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′}
             → ∀ {L} → renExp (λ x → x) (λ x → x) w (toInstEmit κ (ofˢ ts)) ≡ mintᵉ (ofᵉ L)
             → ∀ src → All (AtFrame {Γ = Γ} κ (frameAt w ρ′)) (map (λ tm → evalWith tm (src ∷ᵉ ρ′)) L)

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open Walkers.On {Γ = Γ} κ ep ei using (Walks; Walks<; Elab-Walks; Elab-Walks<)
    open PassP.InP {Γ = Γ} κ {t} {ep} {ei} using (path-pass)

    -- the impl read's path: the restamp handing a read's emits its frame
    readPath : ∀ Θ {Θ′} (i : Fin n) (w : Ren∈ (plainᶜ⁺ Θ) Θ′) (ρ′ : Env (plainᵏ Γ κ) Θ′)
               (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)) {lo}
             → Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)
             → Path (plainᵏ Γ κ) (n + lo) (lookup (plainᵏ Γ κ) (n ↑ʳ i)) (emitᵗ t)
    readPath Θ {Θ′} i w ρ′ eq {lo} q =
      subst (λ u → Path (plainᵏ Γ κ) (n + lo) u (emitᵗ t)) (sym eq)
        (map-f (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w)
                       (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ Θ)) subscribeᵛ (varᵗ (here refl))) , ρ′) ↠[ ≤-refl ] q)

    -- what a read leaves: the stores related again, and the paths
    ReadAfter : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                  (rP : Stream Γ t × Sched Γ × EvalSt ep) (rI : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei)
                  {lo lo′ u} → Path Γ lo u t → Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t) → Set
    ReadAfter S rP rI p q =
      Σ (After κ S rP rI) λ A → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    postulate
      -- A PATH BEING SUBSCRIBED HAS NO ROW AT ITS FIRST NODE YET: a row is
      -- registered only once its subscribe has run, and no two rows start
      -- at one node.
      gone-subscribed : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                          {lo u X} {q : Path (plainᵏ Γ κ) lo u (emitᵗ t)} {now rI}
                      → subscribeE⇓ {e = ei} X q now sI stI rI → Gone q stI

    -- the same, read through the read's cast and its transparent restamp
    gone-cast : ∀ {u u′} (e : u′ ≡ u) {lo} {q : Path (plainᵏ Γ κ) lo u (emitᵗ t)} {st : EvalSt ei}
              → Gone (subst (λ v → Path (plainᵏ Γ κ) lo v (emitᵗ t)) (sym e) q) st → Gone q st
    gone-cast refl g = g

    gone-read : ∀ Θ {Θ′} (i : Fin n) (w : Ren∈ (plainᶜ⁺ Θ) Θ′) (ρ′ : Env (plainᵏ Γ κ) Θ′)
                  (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)) {lo}
                  {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {st : EvalSt ei}
              → Gone (readPath Θ i w ρ′ eq q) st → Gone q st
    gone-read Θ {Θ′} i w ρ′ eq {q = q} {st} =
      gone-cast eq {q = map-f (Θ′ , renTm (λ x → x) (λ x → x) (ext∈ w)
                                     (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ Θ)) subscribeᵛ (varᵗ (here refl))) , ρ′) ↠[ ≤-refl ] q} {st = st}

    -- A READ OF A SLOT THE IMPL STAMPED: both subscribes at the slot, the
    -- impl's down the restamp.  `Sound` of both paths for the reason
    -- `of-fold` takes it: the read registers its path as a row.  And the
    -- impl's path live unless spent, for the same reason: a registered
    -- row walks live outers, and only the walk knows its own are.
    -- REFUTED: `Refuted.Shared-Read-Sound` -- a path through one merge as
    --   two lanes, the read joining a connected share.
    -- REFUTED: `Refuted.Hot-Read-Sound` -- the same path, the read of a
    --   live hot joining its connected share.
    StampedRead : ∀ {Θ} (i : Fin n) → Set
    StampedRead {Θ} i =
      ∀ {M} → Walker ep ei M → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
      → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
          {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
      → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
      → (dP : subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP)
      → subscribeE⇓ {e = ei} (Θ′ , input (n ↑ʳ i) , ρ′) (readPath Θ i w ρ′ eq q) now sI stI rI
      → sz-subscribeE dP < suc M
      → ReadAfter S rP rI p q

    -- WHERE THE SAME READ'S EMITS LAND
    StampedReadStamps : ∀ {Θ} (i : Fin n) → Set
    StampedReadStamps {Θ} i =
      ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
      → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
          {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
      → Sound p sP stP → Sound q sI stI
      → subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP
      → subscribeE⇓ {e = ei} (Θ′ , input (n ↑ʳ i) , ρ′) (readPath Θ i w ρ′ eq q) now sI stI rI
      → Stamps κ (frameAt w ρ′) pr stI rI

    -- ONE LEAF PER FORMER WHOSE ELABORATION INSTALLS MORE THAN IT READS.
    -- Each names the run of impl frames `PathRel` pairs with its plain
    -- frame, and the sources and nodes it registers.
    postulate
      -- A COLD READ'S INPUT BLOCK UP TO ITS FLUSH, at a script with an
      -- asynchronous tail: the impl's subscribe of the marked, batched and
      -- stamped read leaves the block's nodes at or above the counter, a
      -- source partnered with the plain read's, and the flush one fold
      -- down the tail of a group carrying the plain prefix.  What
      -- `Simulation.Cold`'s `cold-register` needs to register both rows.
      --
      -- THE TWO SCRIPTS AT THE SLOT ARE ONE, read off `Store.scripts`: both
      -- schedules' tables are one author's, the impl's embedded.  The hot
      -- and shared reads stand on it too.
      --
      -- WHERE IT CAN FAIL: the flush as ONE fold of ONE group from the
      -- state the registration leaves.  The stamp, the pairing and the
      -- flattening merge sit between the batch and the tail, and the merge
      -- subscribes an inner, which mints and installs; each is a state
      -- the field quantifies past.
      -- PROBED: make qc-store QC='6 200 4' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,0,1,1,1,0,0,0,0,5],"fan":[0,2,2,1,2,0,1,2,1,0],"leaf":[4,0,1],"script":[0,0,1,1,2,0],"slot":[2,0,0,0,1,0],"reach":["flatten","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 200 agree.  Every case
      --   flattens a fan step over a cold read with an asynchronous tail,
      --   so the flushed values each subscribe a lane inner mid-flush; 42
      --   finish one at a merge, 190 group values.  Not inside a μ.
      -- PROBED: make qc-same-clock QC='6 150 2' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,0,1,1,1,0,0,0,0,5],"fan":[0,2,2,1,2,0,1,2,1,0],"leaf":[4,0,1],"script":[0,0,1,1,2,0],"slot":[2,0,0,0,1,0],"reach":["flatten","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 96
      --   agree, 0 fail, 18 undecided: the same flushes' values, each
      --   through a lane inner, against the plain run's instants.
      -- PROBED: git show 11e23e3e:agda/evidence/probed/Probed/Stores.agda
      --   -- the STORE conjunct alone, at the root from empty stores, before
      --   the `Sound` pair was a hypothesis: a cold script, its block run
      --   straight to the root (`cold~`).  Not under a binder, not the
      --   values conjunct.
      -- PROBED: make qc-store QC='12 200 3' QC_BUDGET=900 QC_DRAW='{"exp":[1,0,1,0,1,1,1,1,0,0,0,0,4],"fan":[0,0,0,0,0,0,0,0,0,1],"leaf":[3,0,0],"script":[0,0,1,1,1,1],"slot":[1,0,0,0,0,1],"reach":["flatten","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 200 agree.  Cold
      --   scripts only, every fan step a lane reading a slot under the
      --   map's binder, slot one a share of slot zero or a second cold
      --   script; per-case reads are not counted.
      -- PROBED: make qc-same-clock QC='12 150 2' QC_BUDGET=900 QC_DRAW='{"exp":[1,0,1,0,1,1,1,1,0,0,0,0,4],"fan":[0,0,0,0,0,0,0,0,0,1],"leaf":[3,0,0],"script":[0,0,1,1,1,1],"slot":[1,0,0,0,0,1],"reach":["flatten","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 37
      --   agree, 0 fail, 37 undecided: the same draw's values.
      -- PROBED: make qc-store QC='15 100 3' QC_FUEL=20 QC_BUDGET=900 QC_DRAW='{"exp":[1,0,1,0,1,0,0,0,4,0,0,0,1],"spineD":[0,0,0,3,0,0,3,0,0,0],"spineG":[3,3,0,0,1,0,1,0,0,0],"fan":[0,0,0,0,0,0,0,0,0,1],"leaf":[4,0,1],"script":[0,0,1,1,1,1],"slot":[1,0,0,0,0,1],"reach":["mu","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`, over budget at 63 agree,
      --   0 fail: cold scripts only, every case inside a μ whose spine
      --   merges or flattens over lanes reading a slot; 39 subscribe an
      --   input, 23 finish an inner at a merge, 10 join a connected share.
      -- PROBED: make qc-same-clock QC='15 100 2' QC_FUEL=20 QC_BUDGET=900 QC_DRAW='{"exp":[1,0,1,0,1,0,0,0,4,0,0,0,1],"spineD":[0,0,0,3,0,0,3,0,0,0],"spineG":[3,3,0,0,1,0,1,0,0,0],"fan":[0,0,0,0,0,0,0,0,0,1],"leaf":[4,0,1],"script":[0,0,1,1,1,1],"slot":[1,0,0,0,0,1],"reach":["mu","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 65 agree, 0 fail,
      --   35 undecided: the same draw's values.
      -- RECOVERY: git show ae5fd17e:agda/evidence/refuted/Refuted/Slot-Scripts.agda
      --   restores the opening store at two cold tables, which refuted this
      --   read over a store blind to the slots.
      cold-block : ∀ {Θ} (i : Fin n) → lookup κ i ≡ coldᵏ
                 → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′}
                 → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ plainᵗ (lookup Γ i))
                 → ∀ {lo} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                     {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rI}
                 → (S : Store κ sP stP sI stI)
                 → ∀ {ok sync d ds} → toℕ i < lo → Sched.slots sP i ≡ scripted {ok = ok} (cold sync (d ∷ ds))
                 → subscribeE⇓ {e = ei} (Θ′ , renExp (λ x → x) (λ x → x) w (inputᵖ (n ↑ʳ i) (frameᵛ Θ)) , ρ′)
                     (subst (λ u → Path (plainᵏ Γ κ) (n + lo) (machineEmitᵗ u) (emitᵗ t)) (sym eq) q) now sI stI rI
                 → ColdBlock κ S q now (record { source = freshId sourceᵏ (Sched.mint sP) ; ordinal = freshId ordinalᵏ (Sched.mint sP)
                                               ; elemTy = lookup Γ i ; pending = resolve now (d ∷ ds) }) sync rI
      -- A COLD READ WITH NOTHING TO REGISTER: below the floor, or a script
      -- whose values are all synchronous.  Each run folds its prefix and
      -- the end at once, the impl's through its block
      --
      -- THE BELOW-FLOOR DISJUNCT NEEDS TWO SCRIPTED SLOTS: a registration on
      -- slot `k` lowers a path's floor to `suc k` and no further, so a read
      -- reaches it only at a cold slot above the source it registered on.
      -- PROBED: make qc-store QC='5 200 4' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[0,0,0,0,0,1],"slot":[2,0,0,0,2,0],"reach":["input"]}'
      --   decided by `CLI.Store-Check`'s `store?`, the store conjunct
      --   alone: 196 agree, 0 fail, 4 undecided.  Every case reads a cold
      --   script of two synchronous values and no arrival, under maps,
      --   scans, every flattener and μ.  Not the below-floor disjunct.
      -- PROBED: make qc-same-clock QC='5 150 2' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[0,0,0,0,0,1],"slot":[2,0,0,0,2,0],"reach":["input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 73
      --   agree, 0 fail, 23 undecided: the same scripts' values against
      --   the plain run's instants.
      -- PROBED: make qc-store QC='8 200 3' QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,1,2,2,0,0,0,0,0],"leaf":[3,0,0],"script":[0,0,1,1,1,1],"slot":[0,0,0,0,0,1],"reach":["flatten","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 200 agree, 0 fail, 0
      --   undecided.  Both slots cold scripts in every program; 17 read
      --   slot one in an inner over slot zero, the below-floor shape,
      --   counted off the program rather than the derivation.
      cold-read-end : ∀ {Θ} (i : Fin n) → lookup κ i ≡ coldᵏ
                    → ∀ {M} → Walker ep ei M → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ : Env (plainᵏ Γ κ) Θ′} {ρ : Env Γ Θ} → EnvRel κ Θ w ρ′ ρ
                    → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ plainᵗ (lookup Γ i))
                    → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                        {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
                    → (S : Store κ sP stP sI stI)
                    → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                    → Sound p sP stP → Sound q sI stI
                    → ∀ {vs} → (lo ≤ toℕ i × vs ≡ []) ⊎ (toℕ i < lo × Σ _ λ ok → Sched.slots sP i ≡ scripted {ok = ok} (cold vs []))
                    → (fP : foldPath⇓ now p vs true sP stP rP)
                    → subscribeE⇓ {e = ei} (Θ′ , renExp (λ x → x) (λ x → x) w (inputᵖ (n ↑ʳ i) (frameᵛ Θ)) , ρ′)
                        (subst (λ u → Path (plainᵏ Γ κ) (n + lo) (machineEmitᵗ u) (emitᵗ t)) (sym eq) q) now sI stI rI
                    → sz-foldPath fP < M
                    → ReadAfter S rP rI p q
      -- WHERE A COLD READ'S EMITS LAND: its block stamps every one at
      -- the program's frame, subscribe-kind, and the path catches it.
      -- Decoding what the block sends exhausted the checker's memory at a
      -- one-value cold script, so this region is the compiled sweep's.
      -- PROBED: make qc-same-clock QC='47 200 1' QC_DRAW='{"exp":[0,0,0,0,1,0,0,0,0,0,0,0,0],"obs":[1,0,0,0],"leaf":[1,0,0],"slot":[1,0,1,1,0,0],"script":[0,0,1,0,1,0],"reach":["flatten","scan"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 12
      --   agree, 0 fail.  Cases 2 to 4 read a cold script of one or two
      --   synchronous values under a scan the merge above subscribes.
      cold-read-stamps : ∀ {Θ} (i : Fin n) → lookup κ i ≡ coldᵏ
                       → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                       → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ plainᵗ (lookup Γ i))
                       → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                           {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
                       → (S : Store κ sP stP sI stI)
                       → (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
                       → subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP
                       → subscribeE⇓ {e = ei} (Θ′ , renExp (λ x → x) (λ x → x) w (inputᵖ (n ↑ʳ i) (frameᵛ Θ)) , ρ′)
                           (subst (λ u → Path (plainᵏ Γ κ) (n + lo) (machineEmitᵗ u) (emitᵗ t)) (sym eq) q) now sI stI rI
                       → Stamps κ (frameAt w ρ′) pr stI rI
      -- AN ENDED SCRIPT'S READ CONNECTING ITS SHARE: the plain read folds
      -- the end, the impl's runs the share's definition, whose read of
      -- the raw slot folds it
      -- PROBED: make qc-store QC='3 200 4' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,0,2,2,2,4,0,0,0],"leaf":[3,1,1],"script":[1,1,0,0,0,0],"slot":[2,0,0,0,2,0],"reach":["defer","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`, the store conjunct
      --   alone: 199 agree, 0 fail, 1 undecided.  39 cases connect slot
      --   zero's share after its hot script completed, reads deferred
      --   past the end.
      -- PROBED: make qc-same-clock QC='3 150 2' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,0,2,2,2,4,0,0,0],"leaf":[3,1,1],"script":[1,1,0,0,0,0],"slot":[2,0,0,0,2,0],"reach":["defer","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 132 agree, 0 fail,
      --   18 undecided.  Read against `make qc-store` on the same line,
      --   20 of the 20 cases connecting an ended script's share agree.
      hot-read-connect-done : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ
                   → ∀ {M} → Walker ep ei M → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ : Env (plainᵏ Γ κ) Θ′} {ρ : Env Γ Θ} → EnvRel κ Θ w ρ′ ρ
                   → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
                   → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                       {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI d ok}
                       {below′ : toℕ (n ↑ʳ i) < n + lo}
                   → (S : Store κ sP stP sI stI)
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Sound p sP stP → Sound q sI stI
                   → memberSource (toℕ i) (EvalSt.completedSources stP) ≡ true
                   → (fP : foldPath⇓ now p [] true sP stP rP)
                   → Sched.slots sI (n ↑ʳ i) ≡ shared d {ok = ok}
                   → memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ false
                   → sharedConnect⇓ (n ↑ʳ i) d (readPath Θ i w ρ′ eq q) below′ now sI stI rI
                   → sz-foldPath fP < M
                   → ReadAfter S rP rI p q
      -- A LIVE SCRIPT'S READ CONNECTING ITS SHARE: the plain read
      -- registers at the slot, the impl's runs the share's definition,
      -- whose read of the raw slot registers there; the reader's path
      -- live unless spent, as `StampedRead` takes it
      -- PROBED: make qc-store QC='3 200 4' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,0,2,2,2,4,0,0,0],"leaf":[3,1,1],"script":[1,1,0,0,0,0],"slot":[2,0,0,0,2,0],"reach":["defer","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`, the store conjunct
      --   alone: 199 agree, 0 fail, 1 undecided.  76 cases connect a share
      --   at the subscribe, where the hot script is still live; which
      --   slot's share is not counted apart.
      -- PROBED: make qc-same-clock QC='3 150 2' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,0,2,2,2,4,0,0,0],"leaf":[3,1,1],"script":[1,1,0,0,0,0],"slot":[2,0,0,0,2,0],"reach":["defer","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 132 agree, 0 fail,
      --   18 undecided.  Read against `make qc-store` on the same line,
      --   47 of the 54 cases connecting a share at the subscribe agree.
      -- PROBED: make qc-store QC='7 200 4' QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[1,1,1,1,0,1],"slot":[0,0,0,0,0,1],"reach":["input"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 132 agree, 0 fail, 1
      --   undecided.  Slot one a script in every program; 38 connect slot
      --   one's hot share, 14 of them beside a hot slot zero.
      -- PROBED: make qc-store QC='13 200 3' QC_BUDGET=900 QC_DRAW='{"exp":[1,0,1,0,1,1,1,1,0,0,0,0,4],"fan":[0,0,0,0,0,0,0,0,0,1],"leaf":[3,0,0],"script":[1,1,0,0,0,0],"slot":[1,0,0,0,0,1],"reach":["flatten","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 200 agree.  Hot
      --   scripts only, every fan step a lane reading a slot under the
      --   map's binder, slot one a share of slot zero or a second hot
      --   script.  Its connects are not counted.
      -- PROBED: make qc-same-clock QC='13 150 2' QC_BUDGET=900 QC_DRAW='{"exp":[1,0,1,0,1,1,1,1,0,0,0,0,4],"fan":[0,0,0,0,0,0,0,0,0,1],"leaf":[3,0,0],"script":[1,1,0,0,0,0],"slot":[1,0,0,0,0,1],"reach":["flatten","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 148 agree, 0 fail,
      --   2 undecided, the same draw's values.
      hot-read-connect-live : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ
                   → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ : Env (plainᵏ Γ κ) Θ′} {ρ : Env Γ Θ} → EnvRel κ Θ w ρ′ ρ
                   → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
                   → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                       {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rI rid d ok}
                       {below : toℕ i < lo} {below′ : toℕ (n ↑ʳ i) < n + lo}
                   → (S : Store κ sP stP sI stI)
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
                   → memberSource (toℕ i) (EvalSt.completedSources stP) ≡ false
                   → freshId regᵏ (Sched.mint sP) ≡ rid
                   → Sched.slots sI (n ↑ʳ i) ≡ shared d {ok = ok}
                   → memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ false
                   → sharedConnect⇓ (n ↑ʳ i) d (readPath Θ i w ρ′ eq q) below′ now sI stI rI
                   → ReadAfter S ([] , record sP { mint = setAt regᵏ (suc rid) (Sched.mint sP) } , register rid (atSlot i) (lowerFloor below p) stP) rI p q
      -- a shared slot's read, against its stamped slot's
      -- PROBED: make qc-store QC='3 200 4' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,0,2,2,2,4,0,0,0],"leaf":[3,1,1],"script":[1,1,0,0,0,0],"slot":[2,0,0,0,2,0],"reach":["defer","input"]}'
      --   decided by `CLI.Store-Check`'s `store?`, the store conjunct
      --   alone: 199 agree, 0 fail, 1 undecided.  106 cases connect slot
      --   one's share, a definition forwarding slot zero's or a program over
      --   it, at the subscribe and deferred past it.
      -- PROBED: make qc-same-clock QC='3 150 2' QC_FUEL=30 QC_BUDGET=600 QC_DRAW='{"exp":[1,1,1,0,2,0,2,2,2,4,0,0,0],"leaf":[3,1,1],"script":[1,1,0,0,0,0],"slot":[2,0,0,0,2,0],"reach":["defer","input"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 132 agree, 0 fail,
      --   18 undecided.  Read against `make qc-store` on the same line,
      --   59 of the 65 cases connecting slot one's share agree.
      shared-read    : ∀ {Θ} (i : Fin n) → lookup κ i ≡ sharedᵏ → StampedRead {Θ} i
      -- WHERE A HOT READ'S EMITS LAND: the restamp hands its own a frame
      -- and the path catches it; a live script joined sends nothing yet
      -- PROBED: make qc-same-clock QC='49 150 2' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,0,2,1,1,1,0,0,0,0,1],"leaf":[3,0,1],"slot":[1,1,1,1,0,0],"script":[1,1,0,0,0,0]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 145 agree, 0 fail,
      --   5 undecided.  Cases 73 and 104 read the hot input twice under
      --   one merge, the second read joining the share the first
      --   connected; case 55 reads it under an exhaust.
      hot-read-stamps    : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ → StampedReadStamps {Θ} i
      -- WHERE A SHARED READ'S EMITS LAND.  WHERE IT CAN STILL FAIL: a
      -- connect the read starts runs the share's definition to every row
      -- on its subject, joiners a value made mid-burst included, and what
      -- reaches a joiner leaves down the joiner's path, not this one
      -- PROBED: make qc-same-clock QC='48 200 1' QC_BUDGET=500 QC_DRAW='{"exp":[0,0,0,0,1,0,0,0,0,0,0,0,0],"obs":[1,0,0,0],"leaf":[1,0,0],"slot":[0,0,0,1,0,0],"script":[0,0,1,0,1,0],"reach":["flatten","scan"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 34
      --   agree, 0 fail, 20 undecided.  Case 45 merges a scan whose seed
      --   and source both read a shared slot of two values and whose step
      --   hands on its accumulator: the connect's first value hands the
      --   share to the merge, which joins it mid-burst, and the second
      --   value reaches both rows.
      -- PROBED: make qc-same-clock QC='47 200 1' QC_DRAW='{"exp":[0,0,0,0,1,0,0,0,0,0,0,0,0],"obs":[1,0,0,0],"leaf":[1,0,0],"slot":[1,0,1,1,0,0],"script":[0,0,1,0,1,0],"reach":["flatten","scan"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 12
      --   agree, 0 fail, 4 undecided.  Cases 13 and 15: a joiner made
      --   mid-burst by a one-value connect, reached by its end alone.
      shared-read-stamps : ∀ {Θ} (i : Fin n) → lookup κ i ≡ sharedᵏ → StampedReadStamps {Θ} i
      -- AN `of`'S EMITS CARRY ITS VALUES: the impl's list under its mint,
      -- one emit per value, the last also carrying the end, against the
      -- plain values over related environments
      -- PROBED: `Probed.Walk-Leaves` -- no values, and two with the first
      --   read off a binder through the mint's renaming: one emit per
      --   value, the end on the last; and a pair of the variable and a
      --   right sum at a renaming moving the variable past a value it
      --   does not own; and a pair reading an outer binder before an
      --   inner one, under the same renaming.
      of-carries     : ∀ {Θ u} (ts : List (STm Γ [] [] Θ u)) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                     → ∀ {L} → renExp (λ x → x) (λ x → x) w (toInstEmit κ (ofˢ ts)) ≡ mintᵉ (ofᵉ L)
                     → ∀ src → Carries {u} (map (λ tm → evalWith tm (src ∷ᵉ ρ′)) L) (map (λ tm → evalWith tm ρ) (plainTms ts))
      -- WHERE A GROUP AT ONE FRAME LANDS, folded down the path: below the
      -- catch every restamp cell is subscribe-kind and hands the group
      -- its own instant, and the catch's cell hands the group the catch
      -- PROBED: make qc-same-clock QC='49 150 2' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,0,2,1,1,1,0,0,0,0,1],"leaf":[3,0,1],"slot":[1,1,1,1,0,0],"script":[1,1,0,0,0,0]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 145 agree, 0 fail.
      --   Cases 55 and 73 subscribe a lane's two-value `of` at a hot
      --   arrival, its group folded down a flattener's restamp.
      of-fold-stamps : ∀ {u lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now}
                         {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI src es vs f}
                     → (S : Store κ sP stP sI stI)
                     → (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
                     → Sound p sP stP → Sound q sI stI
                     → freshId sourceᵏ (Sched.mint sI) ≡ src
                     → Carries {u} es vs → All (AtFrame {Γ = Γ} κ f) es
                     → foldPath⇓ now p vs true sP stP rP
                     → foldPath⇓ now q es true (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) stI rI
                     → Stamps κ f pr stI rI

    -- NEITHER RUN READS A HOT SLOT BY ANOTHER KIND'S RULE
    plain-no-shared : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ hotᵏ
                    → ∀ {d ok} → Sched.slots sP i ≡ shared d {ok = ok} → ⊥
    plain-no-shared S i ek x with Store.scripts S
    ... | ins , eP , _ with plain-hot-slot ins i ek
    ...   | _ , _ , s with trans (sym s) (trans (sym (memoᶠ-at (plainSlots ins) i)) (trans (sym (cong (λ f → f i) eP)) x))
    ...     | ()

    plain-no-cold : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ hotᵏ
                  → ∀ {ok ss as} → Sched.slots sP i ≡ scripted {ok = ok} (cold ss as) → ⊥
    plain-no-cold S i ek x with Store.scripts S
    ... | ins , eP , _ with plain-hot-slot ins i ek
    ...   | _ , _ , s with trans (sym s) (trans (sym (memoᶠ-at (plainSlots ins) i)) (trans (sym (cong (λ f → f i) eP)) x))
    ...     | ()

    impl-no-script : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ hotᵏ
                   → ∀ {ok sc} → Sched.slots sI (n ↑ʳ i) ≡ scripted {ok = ok} sc → ⊥
    impl-no-script S i ek x with Store.scripts S
    ... | ins , _ , eI with trans (cong scriptedᵇ (trans (sym x) (trans (cong (λ f → f (n ↑ʳ i)) eI) (memoᶠ-at (embedSlotsImpl ins) (n ↑ʳ i)))))
                                  (impl-hot-slot ins i ek)
    ...   | ()

    -- NOR A COLD SLOT
    cold-no-shared : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ coldᵏ
                   → ∀ {d ok} → Sched.slots sP i ≡ shared d {ok = ok} → ⊥
    cold-no-shared S i ek x with Store.scripts S
    ... | ins , eP , _ with plain-cold-slot ins i ek
    ...   | _ , _ , _ , s with trans (sym s) (trans (sym (memoᶠ-at (plainSlots ins) i)) (trans (sym (cong (λ f → f i) eP)) x))
    ...     | ()

    cold-no-hot : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ coldᵏ
                → ∀ {ok as} → Sched.slots sP i ≡ scripted {ok = ok} (hot as) → ⊥
    cold-no-hot S i ek x with Store.scripts S
    ... | ins , eP , _ with plain-cold-slot ins i ek
    ...   | _ , _ , _ , s with trans (sym s) (trans (sym (memoᶠ-at (plainSlots ins) i)) (trans (sym (cong (λ f → f i) eP)) x))
    ...     | ()

    -- AN ENDED SCRIPT'S SHARE IS NOT JOINED, A LIVE ONE'S NOT SPENT: the
    -- stamped slot's latch is its raw slot's and its connection's
    done-unjoined : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ hotᵏ
                  → memberSource (toℕ i) (EvalSt.completedSources stP) ≡ true
                  → memberSource (toℕ (n ↑ʳ i)) (EvalSt.completedSources stI) ≡ false
                  → memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true → ⊥
    done-unjoined S i ek c cI sI with proj₁ (Store.latches S i) ek
    ... | L₁ , L₂ with trans (sym cI) (trans L₂ (cong₂ _∧_ (trans (sym L₁) c) sI))
    ...   | ()

    live-unspent : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI) (i : Fin n) → lookup κ i ≡ hotᵏ
                 → memberSource (toℕ i) (EvalSt.completedSources stP) ≡ false
                 → memberSource (toℕ (n ↑ʳ i)) (EvalSt.completedSources stI) ≡ true → ⊥
    live-unspent {stI = stI} S i ek c s with proj₁ (Store.latches S i) ek
    ... | L₁ , L₂ with trans (sym s) (trans L₂ (cong (λ b → b ∧ memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI)) (trans (sym L₁) c)))
    ...   | ()

    -- A LIVE SCRIPT'S READ JOINING ITS CONNECTED SHARE: each run
    -- registers one row at the slot, the impl's down the restamp
    hot-read-join : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ
                 → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ : Env (plainᵏ Γ κ) Θ′} {ρ : Env Γ Θ} → EnvRel κ Θ w ρ′ ρ
                 → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (lookup Γ i))
                 → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)}
                     {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rid rid′}
                     {below : toℕ i < lo} {below′ : toℕ (n ↑ʳ i) < n + lo}
                 → (S : Store κ sP stP sI stI)
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
                 → memberSource (toℕ i) (EvalSt.completedSources stP) ≡ false
                 → memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true
                 → freshId regᵏ (Sched.mint sP) ≡ rid → freshId regᵏ (Sched.mint sI) ≡ rid′
                 → ReadAfter S ([] , record sP { mint = setAt regᵏ (suc rid) (Sched.mint sP) } , register rid (atSlot i) (lowerFloor below p) stP)
                               ([] , record sI { mint = setAt regᵏ (suc rid′) (Sched.mint sI) }
                                   , register rid′ (atSlot (n ↑ʳ i)) (lowerFloor below′ (readPath Θ i w ρ′ eq q)) stI) p q
    hot-read-join i ek w r eq {below = below} {below′ = below′} S pr oP oI lv cP conn refl refl =
      join-read κ S i ek cP conn below below′ eq pr oP oI lv

    -- A HOT SLOT'S READ, AGAINST ITS STAMPED SLOT'S: the plain
    -- subscribe at the slot, the impl's at the share wrapping it, under
    -- the restamp handing its subscribe-kind emits this program's frame.
    -- The floors are aligned, so the two runs read below the floor
    -- together; above it the latches pair the script's rule with the
    -- share's.
    --
    -- THE `Sound` PAIR AT A CONCRETE STORE IS PAST THE TYPECHECKER: the
    -- row below, given `sound` over the opening store's two root
    -- derivations, held a flat 6 GB for two hours in CI without a
    -- verdict.  A coverage boundary; the compiled sweep covers it.
    -- REFUTED: `Refuted.Read-Floor` -- the plain read above the slot, the
    --   impl's at its stamped one's floor.
    hot-read : ∀ {Θ} (i : Fin n) → lookup κ i ≡ hotᵏ → StampedRead {Θ} i
    hot-read {Θ} i ek wk w {ρ′} r eq {q = q} {stI = stI} S pr oP oI lv (subs-floor _ fP) dI@(subs-floor _ fI) lt =
      let X = path-pass wk S pr []ᶜ oP oI (λ _ → gone-read Θ i w ρ′ eq {q = q} {st = stI} (gone-subscribed S dI)) fP (peel-read eq fI) (s<s⁻¹ lt) in proj₁ X , proj₁ (proj₂ X)
    hot-read i ek wk w r eq S pr oP oI lv (subs-floor h _) (subs-shared {below = b} _ _) _ =
      ⊥-elim (≤⇒≯ h (+-cancelˡ-< n _ _ (subst (_< n + _) (toℕ-↑ʳ n i) b)))
    hot-read i ek wk w r eq S pr oP oI lv _ (subs-hot-done _ x _ _) _          = ⊥-elim (impl-no-script S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv _ (subs-hot-live _ x _ _) _          = ⊥-elim (impl-no-script S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv _ (subs-cold-sync _ x _) _           = ⊥-elim (impl-no-script S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv _ (subs-cold-async _ x _ _ _ _) _    = ⊥-elim (impl-no-script S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv (subs-shared x _) _ _                = ⊥-elim (plain-no-shared S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv (subs-cold-sync _ x _) _ _           = ⊥-elim (plain-no-cold S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv (subs-cold-async _ x _ _ _ _) _ _    = ⊥-elim (plain-no-cold S i ek x)
    hot-read i ek wk w r eq S pr oP oI lv (subs-hot-done b _ _ _) (subs-floor h _) _ =
      ⊥-elim (≤⇒≯ (+-cancelˡ-≤ n _ _ (subst (n + _ ≤_) (toℕ-↑ʳ n i) h)) b)
    hot-read i ek wk w r eq S pr oP oI lv (subs-hot-live b _ _ _) (subs-floor h _) _ =
      ⊥-elim (≤⇒≯ (+-cancelˡ-≤ n _ _ (subst (n + _ ≤_) (toℕ-↑ʳ n i) h)) b)
    hot-read {Θ} i ek wk w {ρ′} r eq {q = q} {stI = stI} S pr oP oI lv (subs-hot-done _ _ _ fP) dI@(subs-shared _ (slot-spent _ fI)) lt =
      let X = path-pass wk S pr []ᶜ oP oI (λ _ → gone-read Θ i w ρ′ eq {q = q} {st = stI} (gone-subscribed S dI)) fP (peel-read eq fI) (s<s⁻¹ lt) in proj₁ X , proj₁ (proj₂ X)
    hot-read i ek wk w r eq S pr oP oI lv (subs-hot-done _ _ c _) (subs-shared _ (slot-join cI sI _)) _ =
      ⊥-elim (done-unjoined S i ek c cI sI)
    hot-read i ek wk w {ρ′} {ρ} r eq S pr oP oI lv (subs-hot-done _ _ c fP) (subs-shared x (slot-connect _ sI dc)) lt =
      hot-read-connect-done i ek wk w {ρ′} {ρ} r eq S pr oP oI c fP x sI dc (s<s⁻¹ lt)
    hot-read i ek wk w r eq S pr oP oI lv (subs-hot-live _ _ c _) (subs-shared _ (slot-spent s _)) _ =
      ⊥-elim (live-unspent S i ek c s)
    hot-read i ek wk w {ρ′} {ρ} r eq S pr oP oI lv (subs-hot-live _ _ c fr) (subs-shared _ (slot-join _ sI fr′)) _ =
      hot-read-join i ek w {ρ′} {ρ} r eq S pr oP oI lv c sI fr fr′
    hot-read i ek wk w {ρ′} {ρ} r eq S pr oP oI lv (subs-hot-live _ _ c fr) (subs-shared x (slot-connect _ sI dc)) _ =
      hot-read-connect-live i ek w {ρ′} {ρ} r eq S pr oP oI lv c fr x sI dc

    -- A COLD SLOT'S READ, AGAINST ITS STAMPED SLOT'S BLOCK: the plain
    -- subscribe at the slot, the impl's at the marked, batched and
    -- stamped read of the script under its mint.  With an asynchronous
    -- tail both runs register a row, the block's flush folds what the
    -- plain prefix folds, and the pass carries the stores past it.
    cold-read : ∀ {Θ} (i : Fin n) → lookup κ i ≡ coldᵏ
              → ∀ {M} → Walker ep ei M → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
              → (eq : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ plainᵗ (lookup Γ i))
              → ∀ {lo} {p : Path Γ lo (lookup Γ i) t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ (lookup Γ i)) (emitᵗ t)} {now}
                  {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
              → (S : Store κ sP stP sI stI)
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
              → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
              → (dP : subscribeE⇓ {e = ep} (Θ , input i , ρ) p now sP stP rP)
              → subscribeE⇓ {e = ei} (Θ′ , renExp (λ x → x) (λ x → x) w (inputᵖ (n ↑ʳ i) (frameᵛ Θ)) , ρ′)
                  (subst (λ u → Path (plainᵏ Γ κ) (n + lo) (machineEmitᵗ u) (emitᵗ t)) (sym eq) q) now sI stI rI
              → sz-subscribeE dP < suc M
              → ReadAfter S rP rI p q
    cold-read i ek wk w {ρ′} {ρ} r eq S pr oP oI lv (subs-floor h fP) dI lt =
      cold-read-end i ek wk w {ρ′} {ρ} r eq S pr oP oI (inj₁ (h , refl)) fP dI (s<s⁻¹ lt)
    cold-read i ek wk w {ρ′} {ρ} r eq S pr oP oI lv (subs-cold-sync b x fP) dI lt =
      cold-read-end i ek wk w {ρ′} {ρ} r eq S pr oP oI (inj₂ (b , _ , x)) fP dI (s<s⁻¹ lt)
    cold-read i ek wk w r eq S pr oP oI lv (subs-cold-async b x refl refl refl fP) dI lt =
      let B = cold-block i ek w eq S b x dI
          C = cold-register κ S pr oP oI lv _ B
          X = path-pass wk (After.store (proj₁ C)) (proj₁ (proj₂ C)) (ColdBlock.carries B)
                (proj₁ (proj₂ (proj₂ C))) (proj₂ (proj₂ (proj₂ C))) (λ ()) fP (ColdBlock.fold B) (s<s⁻¹ lt)
      in _⨾_ κ (proj₁ C) (proj₁ X) , proj₁ (proj₂ X)
    cold-read i ek wk w r eq S pr oP oI lv (subs-shared x _) _ _        = ⊥-elim (cold-no-shared S i ek x)
    cold-read i ek wk w r eq S pr oP oI lv (subs-hot-done _ x _ _) _ _  = ⊥-elim (cold-no-hot S i ek x)
    cold-read i ek wk w r eq S pr oP oI lv (subs-hot-live _ x _ _) _ _  = ⊥-elim (cold-no-hot S i ek x)

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
    scan-install {stP = stP} {stI = stI} S {u = u} a aI pr refl refl refl =
      install κ S ≤-refl (n≤1+n _) (≤-refl ∷ []) (≤-refl ∷ []) ([] ∷ []) ≤-refl ≤-refl (n≤1+n _) ≤-refl ≤-refl ≤-refl
        (fresh-set _ (cell-st {t = u} a) (EvalSt.nodes stP) ≤-refl) (fresh-set _ (cell-st {t = ScanAᵗ u} aI) (EvalSt.nodes stI) ≤-refl) pr

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
    while-install {stP = stP} {stI = stI} S {u = u} c pr refl refl refl refl =
      install κ S ≤-refl (≤-trans (n≤1+n _) (n≤1+n _)) (n≤1+n _ ∷ ≤-refl ∷ []) (≤-refl ∷ n≤1+n _ ∷ []) ((1+n≢n ∷ []) ∷ [] ∷ [])
        ≤-refl ≤-refl (n≤1+n _) ≤-refl ≤-refl ≤-refl
        (fresh-set _ (take-st 1) (EvalSt.nodes stP) ≤-refl)
        (λ j lt → trans (fresh-set _ (cell-st {t = CutS unitᵗ u} c) (setNode _ (take-st 1) (EvalSt.nodes stI)) (n≤1+n _) j lt) (fresh-set _ (take-st 1) (EvalSt.nodes stI) ≤-refl j lt)) pr

    -- A FLATTENER INSTALLED ON BOTH SIDES, the impl's restamping cell
    -- under it: the triple joins `π` and the tails stay related
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
    flat-install {stP = stP} {stI = stI} S {u = u} op c pr refl refl refl =
      install κ S ≤-refl (≤-trans (n≤1+n _) (n≤1+n _)) (n≤1+n _ ∷ ≤-refl ∷ []) (≤-refl ∷ n≤1+n _ ∷ []) ((1+n≢n ∷ []) ∷ [] ∷ [])
        ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
        (fresh-set _ (flatSt u op) (EvalSt.nodes stP) ≤-refl)
        (λ j lt → trans (fresh-set _ (flatSt (emitᵗ u) op) (setNode _ (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)) (n≤1+n _) j lt) (fresh-set _ (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI) ≤-refl j lt)) pr

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
    flat-install-explode {stP = stP} {stI = stI} S {u = u} op c pr refl refl refl refl =
      install κ S ≤-refl (≤-trans (n≤1+n _) (≤-trans (n≤1+n _) (n≤1+n _)))
        (n≤1+n _ ∷ ≤-refl ∷ ≤-trans (n≤1+n _) (n≤1+n _) ∷ []) (n≤1+n _ ∷ ≤-trans (n≤1+n _) (n≤1+n _) ∷ ≤-refl ∷ [])
        ((1+n≢n ∷ <⇒≢ ≤-refl ∷ []) ∷ (<⇒≢ (n≤1+n _) ∷ []) ∷ [] ∷ [])
        ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
        (fresh-set _ (flatSt u op) (EvalSt.nodes stP) ≤-refl)
        (λ j lt → trans (fresh-set _ (flatSt (echoᵗ (emitᵗ u)) (mergeᶠ nothing)) (setNode _ (flatSt (emitᵗ u) op) (setNode _ (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI))) (≤-trans (n≤1+n _) (n≤1+n _)) j lt)
                 (trans (fresh-set _ (flatSt (emitᵗ u) op) (setNode _ (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)) (n≤1+n _) j lt) (fresh-set _ (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI) ≤-refl j lt))) pr

    -- A HOP INSTALLED ON BOTH SIDES, the body pending: the merge pair
    -- joins `π`, the sources and rows pair as `defer~`, and the tails
    -- stay related.  The merges go in first, then the hop's source and
    -- row.
    --
    -- `Sound` OF BOTH PATHS, AS EVERY WALK CARRIES IT: the hop's row
    -- runs through the path, and only a distinct path whose rows end
    -- where it does pays the rule for it.
    -- REFUTED: `Refuted.Defer-Install-Sound` -- a path through one
    --   merge as two of its lanes.
    defer-install : ∀ {Θ u} (b : SExp Γ [] [] Θ u) {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} {bI}
                  → EnvRel κ Θ w ρ′ ρ
                  → renExp (λ x → x) (λ x → x) w (toInstEmit κ {[]} {[]} (deferˢ b)) ≡ deferᵉ bI
                  → ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : Store κ sP stP sI stI)
                      {lo} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ u) (emitᵗ t)} {now nid src ord rid nid′ src′ ord′ rid′}
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                  → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
                  → freshId nodeᵏ (Sched.mint sP) ≡ nid → freshId sourceᵏ (Sched.mint sP) ≡ src
                  → freshId ordinalᵏ (Sched.mint sP) ≡ ord → freshId regᵏ (Sched.mint sP) ≡ rid
                  → freshId nodeᵏ (Sched.mint sI) ≡ nid′ → freshId sourceᵏ (Sched.mint sI) ≡ src′
                  → freshId ordinalᵏ (Sched.mint sI) ≡ ord′ → freshId regᵏ (Sched.mint sI) ≡ rid′
                  → let stP′ = register rid (atDyn src lo) (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] p)
                                 (installNode nid (mergeAll-st {t = u} nothing 0 [] false) stP)
                        stI′ = register rid′ (atDyn src′ (n + lo)) (thru-outer mergeAllᵒ nid′ ↠[ ≤-refl ] q)
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
    defer-install {u = u} b w r refl {sP} {stP} {sI} {stI} S pr soP soI lv refl refl refl refl refl refl refl refl =
      let A = install κ S {mP = setAt nodeᵏ (suc (nodeCt sP)) (Sched.mint sP)} {mI = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI)}
                {NP = setNode (nodeCt sP) (mergeAll-st {t = u} nothing 0 [] false) (EvalSt.nodes stP)}
                {NI = setNode (nodeCt sI) (mergeAll-st {t = emitᵗ u} nothing 0 [] false) (EvalSt.nodes stI)} {xs = nodeCt sI ∷ []}
                ≤-refl (n≤1+n _) (≤-refl ∷ []) (≤-refl ∷ []) ([] ∷ [])
                ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                (fresh-set _ (mergeAll-st {t = u} nothing 0 [] false) (EvalSt.nodes stP) ≤-refl)
                (fresh-set _ (mergeAll-st {t = emitᵗ u} nothing 0 [] false) (EvalSt.nodes stI) ≤-refl) pr
          B = hop-register κ (After.store (proj₁ A)) (proj₁ (proj₂ A)) (proj₂ (proj₂ A)) soP soI lv (elab b w r)
      in _⨾_ κ (proj₁ A) (proj₁ B) , proj₂ B

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
    unexplode (A , outerExplode~ _ _ pr) = A , pr

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

    -- a walked tail's relation, with what its subscribe sends beside it
    pairS : ∀ {X : Set} {P : X → Set} {Z : Set} → Σ X P → Z → Σ X (λ A → P A × Z)
    pairS (a , pr) z = a , pr , z

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
    walk-while : ∀ {M Θ s} (f : SFn Γ [] [] Θ s boolᵗ) (b : SExp Γ [] [] Θ s) → Elab-Walks< M b
               → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
               → ∀ {F : Fn (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                   {i : Tm (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (CutS unitᵗ s)} {e″ : Exp (plainᵏ Γ κ) [] [] (uniqᵗ ∷ Θ′) (emitᵗ s)}
               → renExp (λ x → x) (λ x → x) w (toInstEmit κ (takeWhileˢ f b)) ≡ mintᵉ (mapᵉ cutOutᵛ (takeWhileᵉ cutOpenᵛ (scanᵉ F i e″)))
               → e″ ≡ renExp (λ x → x) (λ x → x) (λ y → there (w y)) (toInstEmit κ b)
               → (∀ ρ″ → proj₁ (proj₂ (evalWith i ρ″)) ≡ false)
               → Walks< (suc M) (frameAt w ρ′) (Θ′ , mintᵉ (mapᵉ cutOutᵛ (takeWhileᵉ cutOpenᵛ (scanᵉ F i e″))) , ρ′) (Θ , plainExp (takeWhileˢ f b) , ρ)
    walk-while f b wb w {ρ′} {ρ} r {F} {i} {e″} eq fu op {q = q} {stP = stP} {stI = stI} S pr oP oI lv (subs-takeWhile {nid = k} frP dP)
      (subs-mint {src = src} frS (subs-map (subs-takeWhile {nid = k₂} fr₂ (subs-scan {nid = k₁} fr₁ dI)))) lt =
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
                (live-if-cons _ _ _ refl (live-if-cons _ _ _ refl (live-if-cons _ _ q refl
                  (live-if-above q k₁ (cell-st v) N₂ (λ j h → ≤-trans (subst (j <_) fr₂ (fresh-path oI j h)) (subst (k₂ ≤_) fr₁ (n≤1+n k₂)))
                    (live-if-above q k₂ (take-st 1) (EvalSt.nodes stI) (λ j h → subst (j <_) fr₂ (fresh-path oI j h)) lv)))))
                dP (reExp fu dI) (s<s⁻¹ lt)
          pr₁ = proj₂ (proj₂ I)
          fr : ∀ j → OnPath j q → j < k₂
          fr j o = subst (j <_) fr₂ (fresh-path oI j (on-path o))
          K  = kept-unmoved κ pr₁ (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = N₂} {m = k₁} (cell-st v) fr
                   (subst (k₂ ≤_) fr₁ (n≤1+n k₂))
                 (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = EvalSt.nodes stI} {m = k₂} (take-st 1) fr ≤-refl (λ _ _ → refl)))
      in pairS (unwhile (_⨾_ κ (proj₁ I) (proj₁ X) , proj₁ (proj₂ X))) λ C →
           let (al , ke) = proj₂ (proj₂ X) (kept-catch κ pr₁ (catch-same κ pr pr₁ C) K)
           in al , kept-same κ pr₁ pr (kept-trans κ pr₁ K ke)

    -- a scan's walk: the plain cell installed, the impl's source minted
    -- and its cell installed, and the body walked under them
    walk-scan : ∀ {Θ s u} (f : SFn Γ [] [] Θ (u ×ᵗ s) u) (z : STm Γ [] [] Θ u) (b : SExp Γ [] [] Θ s)
              → ∀ {M} → Elab-Walks< M b → Elab-Walks< (suc M) (scanˢ f z b)
    walk-scan f z b wb w {ρ′} {ρ} r {q = q} {stP = stP} {stI = stI} S pr oP oI lv (subs-scan {nid = k} frP dP) (subs-mint {src = src} frS (subs-map (subs-scan {i = iI} {nid = k′} frI dI))) lt =
      let L = lifts-scan f z b w src {i = iI} r refl
          I = scan-install S (evalWith (plainTm z) ρ) (evalWith iI (src ∷ᵉ ρ′)) pr frP frS frI
          X = wb (λ y → there (w y)) r (After.store (proj₁ I))
                (scan~ (proj₁ (proj₂ I)) (lookup-set k (cell-st (evalWith (plainTm z) ρ)) (EvalSt.nodes stP))
                  (lookup-set k′ (cell-st (evalWith iI (src ∷ᵉ ρ′))) (EvalSt.nodes stI)) (proj₂ L) (proj₁ L) (proj₂ (proj₂ I)))
                (fresh-at refl frP oP) (fresh-at refl frI (bare (resrc oI)))
                (live-if-cons _ _ _ refl (live-if-cons _ _ q refl
                  (live-if-above q k′ (cell-st (evalWith iI (src ∷ᵉ ρ′))) (EvalSt.nodes stI) (λ j h → subst (j <_) frI (fresh-path oI j h)) lv)))
                dP (reExp (renExp-fuse there (ext∈ w) (toInstEmit κ b)) dI) (s<s⁻¹ lt)
          pr₁ = proj₂ (proj₂ I)
          fr : ∀ j → OnPath j q → j < k′
          fr j o = subst (j <_) frI (fresh-path oI j (on-path o))
          K  = kept-unmoved κ pr₁ (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = EvalSt.nodes stI} {m = k′}
                 (cell-st (evalWith iI (src ∷ᵉ ρ′))) fr ≤-refl (λ _ _ → refl))
      in pairS (unscan (_⨾_ κ (proj₁ I) (proj₁ X) , proj₁ (proj₂ X))) λ C →
           let (al , ke) = proj₂ (proj₂ X) (kept-catch κ pr₁ (catch-same κ pr pr₁ C) K)
           in al , kept-same κ pr₁ pr (kept-trans κ pr₁ K ke)

    -- a flattener's walk, one element per emit: the plain node
    -- installed, the impl's cell and node installed, and the body walked
    -- under them
    walk-flat-elem : ∀ {M Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ (echoᵗ u)) → Elab-Walks< M b
                   → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                   → ∀ {i : Tm (plainᵏ Γ κ) [] [] Θ′ (FlatSᵗ u)} → proj₁ (evalWith i ρ′) ≡ (frameAt w ρ′ , inj₁ tt)
                   → Walks< (suc M) (frameAt w ρ′) (Θ′ , mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ flatStepᵛ i
                                   (flattenᵉ op (mapᵉ elemᵛ (renExp (λ x → x) (λ x → x) w (toInstEmit κ b))))) , ρ′)
                           (Θ , plainExp (flattenˢ op b) , ρ)
    walk-flat-elem {u = u} op b wb w {ρ′} r {i} seed {q = q} {stP = stP} {stI = stI} S pr oP oI lv (subs-flatten (sub-all {nid = m} frP dP))
      (subs-map (subs-scan {nid = ks} frK (subs-flatten (sub-all {nid = m′} frM (subs-map dI))))) lt =
      let c  = evalWith i ρ′
          N  = setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)
          I  = flat-install S op c pr frP frK frM
          lk = trans (set-above m′ ks (flatSt (emitᵗ u) op) N (apart m′ ks (λ e → 1+n≢n (trans frM (sym e)))))
                     (lookup-set ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI))
          F  = proj₁ (proj₂ I) , flatSt u op , flatSt (emitᵗ u) op
             , lookup-set m (flatSt u op) (EvalSt.nodes stP) , lookup-set m′ (flatSt (emitᵗ u) op) N , flat-init u op
             , c , lk
          X  = wb w r (After.store (proj₁ I)) (outerElem~ {op = op} F (proj₂ (proj₂ I)))
                 (fresh-at refl frP oP) (bare (fresh-at refl frM (fresh-at refl frK (bare oI))))
                 (live-if-cons _ _ _ refl (live-if-thru _ _ (trans (cong outerDoneᵇ (lookup-set m′ (flatSt (emitᵗ u) op) N)) (flat-live (emitᵗ u) op))
                   (live-if-cons _ _ _ refl (live-if-cons _ _ q refl
                     (live-if-above q m′ (flatSt (emitᵗ u) op) N (λ j h → ≤-trans (subst (j <_) frK (fresh-path oI j h)) (subst (ks ≤_) frM (n≤1+n ks)))
                       (live-if-above q ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI) (λ j h → subst (j <_) frK (fresh-path oI j h)) lv))))))
                 dP dI (sz-1 (s<s⁻¹ lt))
          pr₁ = proj₂ (proj₂ I)
          fr : ∀ j → OnPath j q → j < ks
          fr j o = subst (j <_) frK (fresh-path oI j (on-path o))
          K  = kept-unmoved κ pr₁ (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = N} {m = m′} (flatSt (emitᵗ u) op) fr
                   (subst (ks ≤_) frM (n≤1+n ks))
                 (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = EvalSt.nodes stI} {m = ks} (cell-st {t = FlatSᵗ u} c) fr ≤-refl (λ _ _ → refl)))
      in pairS (unflat (_⨾_ κ (proj₁ I) (proj₁ X) , proj₁ (proj₂ X))) λ C →
           let (al , ke) = proj₂ (proj₂ X) (c , lk , by-sub {Γ = Γ} κ {c = c} seed (kept-catch κ pr₁ (catch-same κ pr pr₁ C) K))
               (_ , _ , _ , kb) = ke c lk
           in al , kept-same κ pr₁ pr (kept-trans κ pr₁ K (by-sub⁻ {Γ = Γ} κ {c = c} seed kb))

    -- the same, one element per inner: the impl's per-inner merge
    -- installed between its flattener and the body
    walk-flat-explode : ∀ {M Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ (echoᵗ u)) → Elab-Walks< M b
                      → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
                      → ∀ {i : Tm (plainᵏ Γ κ) [] [] Θ′ (FlatSᵗ u)} → proj₁ (evalWith i ρ′) ≡ (frameAt w ρ′ , inj₁ tt)
                      → Walks< (suc M) (frameAt w ρ′) (Θ′ , mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ flatStepᵛ i
                                      (flattenᵉ op (flattenᵉ (mergeᶠ nothing) (mapᵉ (pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))))
                                        (mapᵉ explodeᵛ (renExp (λ x → x) (λ x → x) w (toInstEmit κ b))))))) , ρ′)
                              (Θ , plainExp (flattenˢ op b) , ρ)
    walk-flat-explode {u = u} op b wb w {ρ′} r {i} seed {q = q} {stP = stP} {stI = stI} S pr oP oI lv (subs-flatten (sub-all {nid = m} frP dP))
      (subs-map (subs-scan {nid = ks} frK (subs-flatten (sub-all {nid = m′} frM (subs-flatten (sub-all {nid = mX} frX (subs-map (subs-map dI)))))))) lt =
      let c  = evalWith i ρ′
          N  = setNode ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)
          xX = flatSt (echoᵗ (emitᵗ u)) (mergeᶠ nothing)
          x′ = flatSt (emitᵗ u) op
          lk = trans (set-above mX ks xX (setNode m′ x′ N)
                       (apart mX ks (λ e → <⇒≢ (<-trans (n<1+n ks) (n<1+n (suc ks))) (trans e (sym (trans (cong suc frM) frX))))))
                     (trans (set-above m′ ks x′ N (apart m′ ks (λ e → 1+n≢n (trans frM (sym e)))))
                            (lookup-set ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI)))
          I  = flat-install-explode S op c pr frP frK frM frX
          lm = trans (set-above mX m′ xX (setNode m′ x′ N) (apart mX m′ (λ e → 1+n≢n (trans frX (sym e)))))
                     (lookup-set m′ x′ N)
          F  = proj₁ (proj₂ I) , flatSt u op , x′
             , lookup-set m (flatSt u op) (EvalSt.nodes stP)
             , lm
             , flat-init u op
             , c , lk
          X  = wb w r (After.store (proj₁ I)) (outerExplode~ {op = op} F (false , lookup-set mX xX (setNode m′ x′ N)) (proj₂ (proj₂ I)))
                 (fresh-at refl frP oP) (bare (bare (fresh-at refl frX (fresh-at refl frM (fresh-at refl frK (bare oI))))))
                 (live-if-cons _ _ _ refl (live-if-cons _ _ _ refl
                   (live-if-thru _ _ (cong outerDoneᵇ (lookup-set mX xX (setNode m′ x′ N)))
                     (live-if-thru _ _ (trans (cong outerDoneᵇ lm) (flat-live (emitᵗ u) op))
                       (live-if-cons _ _ _ refl (live-if-cons _ _ q refl
                         (live-if-above q mX xX (setNode m′ x′ N)
                            (λ j h → ≤-trans (subst (j <_) frK (fresh-path oI j h))
                                       (subst (ks ≤_) (trans (cong suc frM) frX) (≤-trans (n≤1+n ks) (n≤1+n (suc ks)))))
                           (live-if-above q m′ x′ N (λ j h → ≤-trans (subst (j <_) frK (fresh-path oI j h)) (subst (ks ≤_) frM (n≤1+n ks)))
                             (live-if-above q ks (cell-st {t = FlatSᵗ u} c) (EvalSt.nodes stI) (λ j h → subst (j <_) frK (fresh-path oI j h)) lv)))))))))
                 dP dI (sz-1 (s<s⁻¹ lt))
          pr₁ = proj₂ (proj₂ I)
          fr : ∀ j → OnPath j q → j < ks
          fr j o = subst (j <_) frK (fresh-path oI j (on-path o))
          K  = kept-unmoved κ pr₁
                 (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = setNode m′ x′ N} {m = mX} xX fr
                     (subst (ks ≤_) (trans (cong suc frM) frX) (≤-trans (n≤1+n ks) (n≤1+n (suc ks))))
                   (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = N} {m = m′} x′ fr (subst (ks ≤_) frM (n≤1+n ks))
                     (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = EvalSt.nodes stI} {m = ks} (cell-st {t = FlatSᵗ u} c) fr
                       ≤-refl (λ _ _ → refl))))
      in pairS (unexplode (_⨾_ κ (proj₁ I) (proj₁ X) , proj₁ (proj₂ X))) λ C →
           let (al , ke) = proj₂ (proj₂ X) (c , lk , by-sub {Γ = Γ} κ {c = c} seed (kept-catch κ pr₁ (catch-same κ pr pr₁ C) K))
               (_ , _ , _ , kb) = ke c lk
           in al , kept-same κ pr₁ pr (kept-trans κ pr₁ K (by-sub⁻ {Γ = Γ} κ {c = c} seed kb))


    -- a defer's walk: the hop's node, source and row on both sides
    walk-defer : ∀ {Θ u} (b : SExp Γ [] [] Θ u) → Elab-Walks (deferˢ b)
    walk-defer b w r {q = q} {stI = stI} S pr oP oI lv (subs-defer f₁ f₂ f₃ f₄) (subs-defer g₁ g₂ g₃ g₄) =
      let A = defer-install b w r refl S pr oP oI lv f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄
          fr : ∀ j → OnPath j q → j < _
          fr j o = subst (j <_) g₁ (fresh-path oI j (on-path o))
      in proj₁ A , proj₂ A , λ C → [] , kept-unmoved κ pr
           (unmoved-set {Γ = Γ} κ {Q = λ j → OnPath j q} {N = EvalSt.nodes stI} {N′ = EvalSt.nodes stI} _ fr ≤-refl (λ _ _ → refl))

    -- a flattener's walk at either elaboration
    walk-flat : ∀ {M Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ (echoᵗ u)) → Elab-Walks< M b → (pi : Bool)
              → ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
              → Walks< (suc M) (frameAt w ρ′) (Θ′ , renExp (λ x → x) (λ x → x) w (flattenᵖ op pi (frameᵛ Θ) (toInstEmit κ b)) , ρ′)
                      (Θ , plainExp (flattenˢ op b) , ρ)
    walk-flat op b wb false w r = walk-flat-elem op b wb w r refl
    walk-flat op b wb true  w r = walk-flat-explode op b wb w r refl

    -- A SOURCE MINTED ON THE IMPL SIDE ALONE moves no store field: the
    -- plain counter bounds the live sources, and the impl's node counter
    -- stands
    src-bump : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} → Store κ sP stP sI stI
             → Store κ sP stP (record sI { mint = setAt sourceᵏ (suc (freshId sourceᵏ (Sched.mint sI))) (Sched.mint sI) }) stI
    src-bump S = record
      { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below
      ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync
      ; rows = rows ; dlv-alike = dlv-alike ; dying-alike = dying-alike
      ; latches = latches ; dying-done = dying-done ; bounded = proj₁ bounded , mapᵃ m<n⇒m<1+n (proj₂ bounded)
      ; swept = swept ; uncut = uncut ; named = proj₁ named , named-mint (n≤1+n _) ≤-refl ≤-refl (proj₂ named) ; rids = rids ; fresh-ids = fresh-ids ; above = above
      ; census = census ; owned = owned
      ; ruleP = ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI
      ; scripts = scripts ; live-outer = live-outer
      }
      where open Store S

    -- and a pass from the bumped store is one from the store
    unsrc : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {S : Store κ sP stP sI stI} {rP rI} → After κ (src-bump S) rP rI → After κ S rP rI
    unsrc A =
      after (After.store A) (After.keeps A)
            (λ ar → After.persists A (record { boundP = Arr.boundP ar ; boundI = m<n⇒m<1+n (Arr.boundI ar)
                                               ; rows = Arr.rows ar ; lists = Arr.lists ar }))
            (After.values A) (After.grows A)

    -- THE GROUP FOLDED DOWN RELATED PATHS, ENDED, the impl's under its
    -- new source.  The cycle is genuine: an `of` under a flattener's
    -- outer folds its inners into the consume, which walks them, so
    -- the pass is handed a walker under the fold's own size.
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
    of-fold : ∀ {N} (wk : Walker ep ei N) {u lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now}
                       {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI src es vs}
                   → (S : Store κ sP stP sI stI)
                   → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                   → Sound p sP stP → Sound q sI stI
                   → freshId sourceᵏ (Sched.mint sI) ≡ src
                   → Carries {u} es vs
                   → Gone q stI
                   → (dP : foldPath⇓ now p vs true sP stP rP)
                   → foldPath⇓ now q es true (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) stI rI
                   → sz-foldPath dP < N
                   → Σ (After κ S rP rI) λ A
                       → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
    of-fold wk S pr oP oI refl c g dP dI lt =
      let X = path-pass wk (src-bump S) pr c oP (resrc oI) (λ _ → g) dP dI lt
      in unsrc (proj₁ X) , proj₁ (proj₂ X)

    -- an `of`'s walk: the impl mints its source, and both fold the
    -- group and end
    walk-of : ∀ {M Θ u} (ts : List (STm Γ [] [] Θ u)) → Walker ep ei M → Elab-Walks< (suc M) (ofˢ ts)
    walk-of ts wk w r S pr oP oI lv (subs-of dP) dS@(subs-mint {src = src} fr (subs-of dI)) lt =
      let A = of-fold wk S pr oP oI fr (of-carries ts w r refl src) (gone-subscribed S dS) dP dI (s<s⁻¹ lt)
      in proj₁ A , proj₂ A , of-fold-stamps S pr oP oI fr (of-carries ts w r refl src) (of-emits ts w refl src) dP dI

    -- a cold slot's walk: the impl's read past the transport
    walk-cold : ∀ {M Θ} (i : Fin n) → lookup κ i ≡ coldᵏ → Walker ep ei M → Elab-Walks< {Θ} (suc M) (inputˢ i)
    walk-cold i e wk w r S pr oP oI lv dP dI lt with lookup κ i in ek | stampedSlot Γ κ i
    walk-cold i e wk w r S pr oP oI lv dP dI lt | coldᵏ | eq =
      let A = cold-read i ek wk w r eq S pr oP oI lv dP (read-machine w eq _ dI) lt
      in proj₁ A , proj₂ A , cold-read-stamps i ek w r eq S pr dP (read-machine w eq _ dI)
    walk-cold i () wk w r S pr _ _ _ dP dI lt | hotᵏ | _
    walk-cold i () wk w r S pr _ _ _ dP dI lt | sharedᵏ | _

    -- a hot slot's walk: the impl's read peeled to its stamped slot
    walk-hot : ∀ {M Θ} (i : Fin n) → lookup κ i ≡ hotᵏ → Walker ep ei M → Elab-Walks< {Θ} (suc M) (inputˢ i)
    walk-hot i e wk w r S pr _ _ _ dP dI lt with lookup κ i in ek | stampedSlot Γ κ i
    walk-hot i e wk w r S pr oP oI lv dP (subs-map dJ) lt | hotᵏ | eq =
      let A = hot-read i ek wk w r eq S pr oP oI lv dP (read-input _ eq dJ) lt
      in proj₁ A , proj₂ A , hot-read-stamps i ek w r eq S pr oP oI dP (read-input _ eq dJ)
    walk-hot i () wk w r S pr _ _ _ dP dI lt | coldᵏ | _
    walk-hot i () wk w r S pr _ _ _ dP dI lt | sharedᵏ | _

    -- a shared slot's walk, the same
    walk-shared : ∀ {M Θ} (i : Fin n) → lookup κ i ≡ sharedᵏ → Walker ep ei M → Elab-Walks< {Θ} (suc M) (inputˢ i)
    walk-shared i e wk w r S pr _ _ _ dP dI lt with lookup κ i in ek | stampedSlot Γ κ i
    walk-shared i e wk w r S pr oP oI lv dP (subs-map dJ) lt | sharedᵏ | eq =
      let A = shared-read i ek wk w r eq S pr oP oI lv dP (read-input _ eq dJ) lt
      in proj₁ A , proj₂ A , shared-read-stamps i ek w r eq S pr oP oI dP (read-input _ eq dJ)
    walk-shared i () wk w r S pr _ _ _ dP dI lt | coldᵏ | _
    walk-shared i () wk w r S pr _ _ _ dP dI lt | hotᵏ | _

    -- the one arm that reads `κ`, one leaf per kind
    walk-input : ∀ {M Θ} (i : Fin n) (k : Kind) → lookup κ i ≡ k → Walker ep ei M → Elab-Walks< {Θ} (suc M) (inputˢ i)
    walk-input i coldᵏ   e wk = walk-cold i e wk
    walk-input i hotᵏ    e wk = walk-hot i e wk
    walk-input i sharedᵏ e wk = walk-shared i e wk

    -- a renamed expression's derivation is the derivation
    sz-reExpᴾ : ∀ {Θ u lo} {ρ} {E E′ : Exp Γ [] [] Θ u} {p : Path Γ lo u t} {now s st r} {M}
                (eq : E ≡ E′) (d : subscribeE⇓ {e = ep} (Θ , E , ρ) p now s st r)
              → sz-subscribeE d < M → sz-subscribeE (reExpᴾ eq d) < M
    sz-reExpᴾ refl d lt = lt

    -- ONE FORMER'S WALK, its sub-walks handed a walker under the
    -- former's own plain size.  A μ's unrolling is no smaller a tree,
    -- but its subscribe is a premise of the μ's.
    at : ∀ {M Θ u} (s : SExp Γ [] [] Θ u) → Walker ep ei M → Elab-Walks< (suc M) s
    at (inputˢ i) wk = walk-input i (lookup κ i) refl wk
    at (ofˢ ts) wk         = walk-of ts wk
    at {Θ = Θ} {u} emptyˢ wk w {ρ′} {ρ} r S pr oP oI lv (subs-empty f) dI lt = walk-of {Θ = Θ} {u} [] wk w {ρ′} {ρ} r S pr oP oI lv (subs-of {ts = []} f) dI lt
    at (takeWhileˢ f b) wk w r = walk-while f b (wk b) w r refl (renExp-fuse there (ext∈ w) (toInstEmit κ b)) (λ _ → refl)
    at (mapˢ f b) wk w r S pr oP oI lv (subs-map dP) (subs-map dI) lt =
      let X = wk b w r S (map~ (lifts-map f w r) pr) (bare oP) (bare oI) (live-if-cons _ _ _ refl lv) dP dI (s<s⁻¹ lt)
      in pairS (unmap (proj₁ X , proj₁ (proj₂ X))) (proj₂ (proj₂ X))
    at (scanˢ f z b) wk    = walk-scan f z b (wk b)
    at (flattenˢ op b) wk w r = walk-flat op b (wk b) (perInnerˢ op b) w r
    at (μˢ b) wk w r S pr oP oI lv (subs-μ dP) (subs-μ dI) lt =
      let (s′ , pe , ie) = μ-unfolds b
      in wk s′ w r S pr oP oI lv (reExpᴾ (sym pe) dP) (reExp (sym (ie w)) dI) (sz-reExpᴾ (sym pe) dP (s<s⁻¹ lt))
    at (varˢ ()) _
    at (deferˢ b) _ w r S pr oP oI lv dP dI _ = walk-defer b w r S pr oP oI lv dP dI

    -- THE WALK DESCENDS THE PLAIN DERIVATION'S SIZE
    walk< : ∀ {N} → Acc _<_ N → Walker ep ei N
    walk< (acc rs) s w r S pr oP oI lv dP dI lt = at s (walk< (rs lt)) w r S pr oP oI lv dP dI (n<1+n _)

    walk : ∀ {Θ u} (s : SExp Γ [] [] Θ u) → Elab-Walks s
    walk s w r S pr oP oI lv dP dI = walk< (<-wellFounded _) s w r S pr oP oI lv dP dI (n<1+n _)

    -- a walker under any bound, for a pass outside the cycle
    walker : ∀ {N} → Walker ep ei N
    walker s w r S pr oP oI lv dP dI _ = walk s w r S pr oP oI lv dP dI

-- WHERE IT CAN STILL FAIL: A HOT SCRIPT LIVE ON ONE SIDE ONLY, or two
-- live at different places.  Both lists are the slots' hot scripts in
-- slot order, the impl's read off its raw half.
-- PROBED: `Probed.Opening` -- one hot script of two arrivals, both
--   payloads left on each side.  Not two hot slots, not a shared slot.
-- PROBED: make qc-store QC='7 200 4' QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[1,1,1,1,0,1],"slot":[0,0,0,0,0,1],"reach":["input"]}'
--   decided by `CLI.Store-Check`'s `store?`, its `sources` field at the
--   first traced state, the live lists after the subscribe: 132 agree,
--   0 fail, 1 undecided, killed at case 134.  Slot one a script in every
--   program, 23 with two hot slots.
postulate
  init-sources : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
               → Pointwise (Src κ) (Sched.live (sched-init (plainExp e) (plainSlots ins)))
                                    (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)))

-- WHERE IT CAN STILL FAIL: A HOT SCRIPT AT A DIFFERENT TICK OR RANK ON
-- ONE SIDE.  Both lists are the slots' hot scripts in slot order.
-- PROBED: `Probed.Opening` -- one hot script of two arrivals.  Not two
--   hot slots, so no rank was compared.
-- PROBED: make qc-store QC='7 200 4' QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[1,1,1,1,0,1],"slot":[0,0,0,0,0,1],"reach":["input"]}'
--   decided by `CLI.Store-Check`'s `store?`, its `sync` field at the
--   first traced state, the live lists after the subscribe: 132 agree,
--   0 fail, 1 undecided, killed at case 134.  Slot one a script in every
--   program, 23 with two hot slots.
postulate
  init-sync : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
            → Sync (Sched.live (sched-init (plainExp e) (plainSlots ins)))
                   (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)))

-- WHERE IT CAN STILL FAIL: A HOT SCRIPT NUMBERED APART FROM ITS RAW
-- READ.  Both lists are the slots' hot scripts, numbered by slot.
-- PROBED: `Probed.Walk-Leaves` -- one hot script, so no two slots
--   compared.
-- PROBED: make qc-store QC='7 200 4' QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[1,1,1,1,0,1],"slot":[0,0,0,0,0,1],"reach":["input"]}'
--   decided by `CLI.Store-Check`'s `store?`, its `numbers` field at the
--   first traced state, the live lists after the subscribe: 132 agree,
--   0 fail, 1 undecided, killed at case 134.  Slot one a script in every
--   program, 23 with two hot slots.
postulate
  init-numbers : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
               → Pointwise (λ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) → SrcNum κ (LiveSource.source l) (LiveSource.source l′))
                           (Sched.live (sched-init (plainExp e) (plainSlots ins)))
                           (Sched.live (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)))

-- the hot scripts live before anything is subscribed, one per slot
-- PROBED: `Probed.Walk-Leaves` -- one hot script, so no two compared.
-- PROBED: make qc-store QC='7 200 4' QC_BUDGET=600 QC_DRAW='{"exp":[2,2,1,1,2,1,2,2,1,1,0,1,1],"leaf":[3,1,1],"script":[1,1,1,1,0,1],"slot":[0,0,0,0,0,1],"reach":["input"]}'
--   decided by `CLI.Store-Check`'s `store?`, its `distinct` field at
--   the first traced state, the live lists after the subscribe: 132
--   agree, 0 fail, 1 undecided, killed at case 134.  Slot one a script
--   in every program, 23 with two hot slots.
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

-- and ordered by them
mkHot-ords : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (i : Fin n) → All (λ l → LiveSource.ordinal l < n) (mkHot ins i)
mkHot-ords ins i with ins i
... | scripted (hot async) = toℕ<n i ∷ []
... | scripted (cold _ _)  = []
... | shared _             = []

init-ords : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → All (_< n) (map LiveSource.ordinal (Sched.live (sched-init e ins)))
init-ords e ins = map⁺ (concat⁺ (tabulate⁺ (mkHot-ords ins)))

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
           → n + n < counter μ sourceᵏ → n + n ≤ counter μ ordinalᵏ
           → Store κ (sched-init (plainExp e) (plainSlots ins)) (st-init (plainExp e))
                     (record (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)) { mint = μ })
                     (st-init (elaborateImpl κ e))
init-store κ {t} e ins μ big ord = record
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
  ; dying-done = λ _ _ → (λ ()) , (λ ())
  ; bounded = mapᵃ (λ lt → <-trans lt (n<1+n _)) (init-below (plainExp e) (plainSlots ins))
            , mapᵃ (λ lt → <-trans lt big) (init-below (elaborateImpl κ e) (embedSlotsImpl ins))
  ; swept   = init-swept {t = t} {t′ = emitᵗ t} (init-sources κ e ins) (init-below (plainExp e) (plainSlots ins)) (init-below (elaborateImpl κ e) (embedSlotsImpl ins))
  ; uncut   = [] , []
  ; named   = record { slots-below = n<1+n _ ; ords-below = init-ords (plainExp e) (plainSlots ins)
                     ; srcs-below = [] ; cut-below = [] ; dlv-below = [] ; dying-below = [] }
            , record { slots-below = big ; ords-below = weak {f = λ x → x} ord (init-ords (elaborateImpl κ e) (embedSlotsImpl ins))
                     ; srcs-below = [] ; cut-below = [] ; dlv-below = [] ; dying-below = [] }
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = ins , refl , refl
  ; live-outer = live (λ ())
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
          × All (λ y → proj₁ y ≡ proj₁ (minted κ e ins)) (readᴵ (proj₁ (Σ⁰.fst⁰ (subscribe! (elaborateImpl κ e) (embedSlotsImpl ins)))))
root-walk κ e ins = After.store (proj₁ W) , After.values (proj₁ W) , proj₁ (proj₂ (proj₂ W) refl)
  where
  S₀ = init-store κ e ins _ (<-trans (proj₁ (proj₂ (minted κ e ins))) (n<1+n _)) ≤-refl
  W = walk κ e (λ x → x) (λ ()) S₀ root~ (sound (Store.ruleP S₀) (λ k ()) (λ k ()) _) (sound (Store.ruleI S₀) (λ k ()) (λ k ()) _) (live-if (λ _ → []))
       (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp e) (plainSlots ins)))) (proj₂ (proj₂ (minted κ e ins)))
