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

open import Data.List    using (List; []; _∷_; map; concat)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Nat     using (ℕ; suc; _+_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim      using (Id)
open import Rx.Exp       using (FlatOp)
open import Rx.Exp       using (Ctx; Val; Closed; Exp; obs; Ren∈; ext∈; renExp; renTm; applyClo; []ᵉ; _∷ᵉ_; uniqᵗ)
open import Rx.Mint      using (Mint; setAt; sourceᵏ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; LiveSource; Path; root; sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-map; subs-mint)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰)
open import Data.Fin     using (Fin)
open import SExp.Syntax  using (SExp; STm; SFn; Kinds; plainᵏ; emitᵗ; inputˢ; ofˢ; emptyˢ; takeˢ; takeWhileˢ; mapˢ; scanˢ;
  flattenˢ; μˢ; varˢ; deferˢ)
open import SExp.Plain   using (plainExp; plainTm; plainValues)
open import SExp.Elaborate using (toInstEmit; toInstEmitTm; plainᶜ⁺; mapStepᵖ)
open import SExp.Pipeline using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Schedules using (Sync)
open import Simulation.Stores using (V; EnvRel; Lifts; PathRel; root~; map~; Store; Src; SrcNum; [])

-- what a run sends to its root, read as values: the plain run's in
-- order, the impl's decoded and each paired with its instant
readᴾ : ∀ {n} {Γ : Ctx n} {t} → Stream Γ t → List (Val Γ t)
readᴾ s = plainValues (concat s)

readᴵ : ∀ {m} {Γ′ : Ctx m} {t} → Stream Γ′ (instEmitᵗ uniqᵗ t) → List (Id × Val Γ′ t)
readᴵ s = instExtract (decodeEmits (concat s))

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

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    -- WHAT ONE SUBSCRIBE KEEPS: from related stores and a related path,
    -- the two derivations end in related stores, having sent the root
    -- related values.
    Walks : ∀ {u} → Val (plainᵏ Γ κ) (obs (emitᵗ u)) → Val Γ (obs u) → Set
    Walks {u} x′ x =
      ∀ {lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now}
        {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
      → subscribeE⇓ {e = ep} x p now sP stP rP → subscribeE⇓ {e = ei} x′ q now sI stI rI
      → Store κ (proj₁ (proj₂ rP)) (proj₂ (proj₂ rP)) (proj₁ (proj₂ rI)) (proj₂ (proj₂ rI))
      × Pointwise (λ a w → V κ t (proj₂ a) w) (readᴵ (proj₁ rI)) (readᴾ (proj₁ rP))

    -- the walk at one former, over any related environment
    Elab-Walks : ∀ {Θ u} → SExp Γ [] [] Θ u → Set
    Elab-Walks {Θ} s =
      ∀ {Θ′} (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ ρ} → EnvRel κ Θ w ρ′ ρ
      → Walks (Θ′ , renExp (λ x → x) (λ x → x) w (toInstEmit κ s) , ρ′) (Θ , plainExp s , ρ)

    -- ONE LEAF PER FORMER WHOSE ELABORATION INSTALLS MORE THAN IT READS.
    -- Each names the run of impl frames `PathRel` pairs with its plain
    -- frame, and the sources and nodes it registers.
    postulate
      -- the one arm that reads `κ`: a cold's block, a hot's share
      -- connect and machine row, a shared slot's stamped read
      -- PROBED: `Probed.Stores` -- the STORE conjunct alone, at the root
      --   from empty stores: a hot read of two arrivals (its share's
      --   `read~` and `hot~` machine row) and a cold script (its block
      --   run straight to the root, `cold~`).  Not a shared slot's read,
      --   not under a binder, not the values conjunct.
      walk-input     : ∀ {Θ} (i : Fin n) → Elab-Walks {Θ} (inputˢ i)
      walk-of        : ∀ {Θ u} (ts : List (STm Γ [] [] Θ u)) → Elab-Walks (ofˢ ts)
      walk-empty     : ∀ {Θ u} → Elab-Walks {Θ} {u} emptyˢ
      walk-take      : ∀ {Θ u} (k : STm Γ [] [] Θ _) (b : SExp Γ [] [] Θ u) → Elab-Walks (takeˢ k b)
      walk-takeWhile : ∀ {Θ u} (f : SFn Γ [] [] Θ u _) (b : SExp Γ [] [] Θ u) → Elab-Walks (takeWhileˢ f b)
      walk-scan      : ∀ {Θ s u} (f : SFn Γ [] [] Θ _ u) (z : STm Γ [] [] Θ u) (b : SExp Γ [] [] Θ s)
                     → Elab-Walks (scanˢ f z b)
      -- the riskiest arm: the outer's frames, and every inner a sync
      -- outer hands the flattener subscribed before the arm returns.
      -- Read off normal forms, not instantiated: a one-lane merge of the
      -- hot read installs what the relation says -- `read~` through
      -- `inner~` and `merge~`, `π` pairing the plain merge node with the
      -- impl's lane node and cell -- and a literal `of` outer installs
      -- nothing on either side.  The typechecked row of the merge does
      -- not finish: the coverage boundary of `Probed.Stores`.
      walk-flatten   : ∀ {Θ u} (op : FlatOp) (b : SExp Γ [] [] Θ _) → Elab-Walks {Θ} {u} (flattenˢ op b)
      -- an unrolling: the body under the substitution, on both sides
      walk-μ         : ∀ {Θ u} (b : SExp Γ (u ∷ []) [] Θ u) → Elab-Walks (μˢ b)
      -- PROBED: `Probed.Stores` -- the STORE conjunct alone, at the root
      --   from empty stores: a deferred hot read, its hop pending as a
      --   `defer~` source and row and its body not yet subscribed.  Not
      --   a defer under a flattener, not the values conjunct.
      walk-defer     : ∀ {Θ u} (b : SExp Γ [] [] Θ u) → Elab-Walks (deferˢ b)

    walk : ∀ {Θ u} (s : SExp Γ [] [] Θ u) → Elab-Walks s
    walk (inputˢ i)       = walk-input i
    walk (ofˢ ts)         = walk-of ts
    walk emptyˢ           = walk-empty
    walk (takeˢ k b)      = walk-take k b
    walk (takeWhileˢ f b) = walk-takeWhile f b
    walk (mapˢ f b) w r S pr (subs-map dP) (subs-map dI) = walk b w r S (map~ (lifts-map f w r) pr) dP dI
    walk (scanˢ f z b)    = walk-scan f z b
    walk (flattenˢ op b)  = walk-flatten op b
    walk (μˢ b)           = walk-μ b
    walk (varˢ ())
    walk (deferˢ b)       = walk-defer b

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

-- BEFORE ANYTHING IS SUBSCRIBED THE STORES ARE EMPTY, and the impl's
-- mint touches only the counter, which the relation does not read.
init-store : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) (μ : Mint)
           → Store κ (sched-init (plainExp e) (plainSlots ins)) (st-init (plainExp e))
                     (record (sched-init (elaborateImpl κ e) (embedSlotsImpl ins)) { mint = μ })
                     (st-init (elaborateImpl κ e))
init-store κ e ins μ = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; sources = init-sources κ e ins
  ; numbers = init-numbers κ e ins
  ; distinct = init-distinct κ e ins
  ; sync    = init-sync κ e ins
  ; rows    = []
  ; latches = λ _ → (λ _ → refl) , (λ _ → refl , refl)
  ; wfᴾ     = λ _ ()
  ; wfᴵ     = λ _ ()
  }

-- THE IMPL'S ROOT SUBSCRIBE IS ITS MINT'S BODY'S, at the token the mint
-- drew: the frame the elaboration closes over.
minted : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ)
       → Σ ℕ λ src →
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
     → Σ ℕ λ src →
       subscribeE⇓ {e = elaborateImpl κ e}
         (uniqᵗ ∷ [] , renExp (λ x → x) (λ x → x) (λ x → x) (toInstEmit κ e) , src ∷ᵉ []ᵉ) (root {lo = n + n}) 0
         (record sI { mint = setAt sourceᵏ (suc src) (Sched.mint sI) }) (st-init (elaborateImpl κ e)) rI
  go {rI} (subs-mint {src = src} _ dI) =
    src , subst (λ E → subscribeE⇓ {e = elaborateImpl κ e} (uniqᵗ ∷ [] , E , src ∷ᵉ []ᵉ) (root {lo = n + n}) 0
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
root-walk κ e ins =
  walk κ e (λ x → x) (λ ()) (init-store κ e ins _) root~
       (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp e) (plainSlots ins)))) (proj₂ (minted κ e ins))
