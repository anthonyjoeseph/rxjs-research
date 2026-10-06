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
open import Data.Bool    using (T; true; _∨_)
open import Data.Nat     using (ℕ; suc; _+_; _<_; _≤_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat.Properties using (<-trans; n<1+n; ≤-reflexive; <⇒<ᵇ)
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.Sum using (inj₂)

open import Rx.Prim      using (hot; cold)
open import Rx.Exp       using (FlatOp)
open import Rx.Exp       using (Ctx; Val; Closed; Exp; obs; Ren∈; ext∈; renExp; renTm; applyClo; []ᵉ; _∷ᵉ_; uniqᵗ; _×ᵗ_; evalWith; mintᵉ; mapᵉ; scanᵉ; Fn; FnClo; Tm)
open import Rx.Mint      using (Mint; setAt; sourceᵏ; nodeᵏ; counter; freshId)
open import Rx.Evaluator using (Sched; EvalSt; LiveSource; Path; root; map-f; scan-f; _↠[_]_; NodeId; NodeState; sched-init; st-init;
  mkHot; installNode; setNode; cell-st)
open import Rx.Slots     using (Slots; scripted; shared)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-map; subs-mint; subs-scan)
open import Rx.Evaluator.Freshness using (lookup-set)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; rule)
open import Data.Fin     using (Fin)
open import SExp.Syntax  using (SExp; STm; SFn; Kinds; plainᵏ; emitᵗ; inputˢ; ofˢ; emptyˢ; takeˢ; takeWhileˢ; mapˢ; scanˢ;
  flattenˢ; μˢ; varˢ; deferˢ)
open import SExp.Plain   using (plainExp; plainTm)
open import SExp.Elaborate using (toInstEmit; toInstEmitTm; plainᶜ⁺; mapStepᵖ; ScanAᵗ)
open import SExp.Pipeline using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Schedules using (Sync)
open import Simulation.After using (readᴾ; readᴵ; module Kept)
open Kept using (After; module After; _⨾_)
open import Simulation.Stores using (guardOf; V; EnvRel; Lifts; ScanLifts; PathRel; root~; map~; scan~; Store; Src; SrcNum; [])


-- TWIN: `ib-renᵉ` -- the same walk over `renExp`'s clauses, a binder's
--   `ext∈` over the composite agreeing with the composite of the two
--   `ext∈`s pointwise, not definitionally.
postulate
  renExp-fuse : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ₁ Θ₂ Θ₃ t} (σ : Ren∈ Θ₁ Θ₂) (ρ : Ren∈ Θ₂ Θ₃) (x : Exp Γ Δᵍ Δ Θ₁ t)
              → renExp (λ y → y) (λ y → y) ρ (renExp (λ y → y) (λ y → y) σ x) ≡ renExp (λ y → y) (λ y → y) (λ y → ρ (σ y)) x

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

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    -- WHAT ONE SUBSCRIBE KEEPS: what a pass keeps, from related stores
    -- and a related path, and the path related again after.
    Walks : ∀ {u} → Val (plainᵏ Γ κ) (obs (emitᵗ u)) → Val Γ (obs u) → Set
    Walks {u} x′ x =
      ∀ {lo lo′} {p : Path Γ lo u t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t)} {now}
        {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {rP rI}
      → (S : Store κ sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
      → subscribeE⇓ {e = ep} x p now sP stP rP → subscribeE⇓ {e = ei} x′ q now sI stI rI
      → Σ (After κ S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

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

    -- a map's frames walked: the tail related again
    unmap : ∀ {X : Set} {π : X → List (NodeId × List NodeId)} {NP : X → List (NodeId × NodeState Γ)}
              {NI : X → List (NodeId × NodeState (plainᵏ Γ κ))} {lo lo′ ℓ ℓ′ s u F G} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
              {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
          → Σ X (λ A → PathRel κ (π A) {t} (NP A) (NI A) {s = s} (map-f F ↠[ h ] p) (map-f G ↠[ h′ ] q))
          → Σ X (λ A → PathRel κ (π A) (NP A) (NI A) p q)
    unmap (A , map~ _ pr) = A , pr

    walk : ∀ {Θ u} (s : SExp Γ [] [] Θ u) → Elab-Walks s
    walk (inputˢ i)       = walk-input i
    walk (ofˢ ts)         = walk-of ts
    walk emptyˢ           = walk-empty
    walk (takeˢ k b)      = walk-take k b
    walk (takeWhileˢ f b) = walk-takeWhile f b
    walk (mapˢ f b) w r S pr (subs-map dP) (subs-map dI) = unmap (walk b w r S (map~ (lifts-map f w r) pr) dP dI)
    walk (scanˢ f z b) w {ρ′} {ρ} r {stP = stP} {stI = stI} S pr (subs-scan {nid = k} frP dP) (subs-mint {src = src} frS (subs-map (subs-scan {i = iI} {nid = k′} frI dI))) =
      let L = lifts-scan f z b w src {i = iI} r refl
          I = scan-install S (evalWith (plainTm z) ρ) (evalWith iI (src ∷ᵉ ρ′)) pr frP frS frI
          X = walk b (λ y → there (w y)) r (After.store (proj₁ I))
                (scan~ (proj₁ (proj₂ I)) (lookup-set k (cell-st (evalWith (plainTm z) ρ)) (EvalSt.nodes stP))
                  (lookup-set k′ (cell-st (evalWith iI (src ∷ᵉ ρ′))) (EvalSt.nodes stI)) (proj₂ L) (proj₁ L) (proj₂ (proj₂ I)))
                dP (reExp (renExp-fuse there (ext∈ w) (toInstEmit κ b)) dI)
      in unscan (_⨾_ κ (proj₁ I) (proj₁ X) , proj₂ X)
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
  W = walk κ e (λ x → x) (λ ()) (init-store κ e ins _ (<-trans (proj₁ (proj₂ (minted κ e ins))) (n<1+n _))) root~
       (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp e) (plainSlots ins)))) (proj₂ (proj₂ (minted κ e ins)))
