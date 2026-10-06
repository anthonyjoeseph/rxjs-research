------------------------------------------------------------------
-- THE TWO STORES, RELATED.  The plain run and the elaborated run hold
-- a registry, a node table, live sources and two latches each; this is
-- what makes one a picture of the other, former by former, so that
-- each arrival's leaf is the cascade through one former's frames.
--
-- A VALUE IS RELATED AT DATA BY BEING THE SAME AND AT `obs` BY BEING
-- ITS ELABORATION.  An observable is a closure, and the impl's is the
-- plain one's program run through `toInstEmit`, renamed into whatever
-- telescope the impl closed it in, over an environment related slot
-- for slot.  The frame token rides at the far end of the telescope and
-- is constrained by nothing: no value of the plain run stands for it.
--
-- A FRAME IS RELATED BY WHAT IT DOES TO ONE EMIT, NOT BY ITS TERM.  A
-- step the impl closed over a renamed elaboration is not syntactically
-- the elaboration of anything; what the cascade needs is that it lifts
-- the plain step to emits, keeping the emit's instant, and that is
-- stated once per kind of step (`Lifts`, `ScanLifts`, `CutLifts`).
--
-- STRUCTURE IS RELATED SYNTACTICALLY, BECAUSE THE CASCADE READS IT.
-- Each former's elaboration installs a fixed run of frames and nodes
-- for one plain frame; `PathRel` names that run, and `π` pairs each
-- plain node with the impl nodes the elaboration installed for it, so
-- every registration through one plain node agrees on the impl nodes.
------------------------------------------------------------------
module Simulation.Stores where

open import Data.Bool    using (Bool; true; false; _∨_; _∧_; T; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Empty   using (⊥)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_; _↑ˡ_)
open import Data.List    using (List; []; _∷_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-map⁺)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _<_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Rx.Evaluator.Reducible.Support using (Rule)
open import Rx.Evaluator.Freshness using (nodeCt)

open import Rx.Mint      using (counter; sourceᵏ)
open import Rx.Prim      using (InstEmit; Tick; Source)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Val; Env; Closed; lookupEnv;
  Ren∈; renExp; FnClo; applyClo; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; varᵗ; unit̂; pairᵗ; inlᵗ;
  inrᵗ; sndᵗ; Tm)
open import Rx.Evaluator using (LiveSource; Sched; EvalSt; NodeState; NodeId; Path; RegRow; RegSrc; atSlot; atDyn; root; share-sink;
  _↠[_]_; map-f; scan-f; take-f; batchSync-f; from-inner; thru-outer; mergeAllᵒ; cell-st;
  take-st; mergeAll-st; switch-st; exhaust-st; batchSync-st; echoᵗ; lookupNode; memberSource;
  takeVals; scanVals; regSource; sameSource; pathHasNode)
open import Rx.Evaluator.Domain using (flatOp)
open import SExp.Syntax  using (SExp; Kinds; plainᵏ; plainᵗ; emitᵗ; slotTy; hotᵏ; sharedᵏ)
open import SExp.Plain   using (plainExp)
open import Simulation.Schedules using (Sync)
open import SExp.Elaborate using (toInstEmit; plainᶜ⁺; deferBodyᵖ; stampedSlot; restampᵛ; subscribeᵛ; deliveryᵛ; inputStampᵖ;
  ScanAᵗ; CutS; cutOpenᵛ; cutOutᵛ; flatStepᵛ; elemᵛ; explodeᵛ; FlatSᵗ)
open import SExp.InstEmit using (machineEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmit)
open import Batchable.Inst-Extract using (emitValues)

-- A LIVE SOURCE'S NUMBER AGAINST ITS PARTNER'S.  The only slots live
-- on either side are the hot scripts, the impl's read off its raw
-- half under the same number, and every other source is minted above
-- the slots: the plain run's above `n`, the impl's above `n + n`.
data SrcNum {n} (κ : Kinds n) : Source → Source → Set where
  slot~ : ∀ i → lookup κ i ≡ hotᵏ → SrcNum κ (toℕ i) (toℕ (i ↑ˡ n))
  dyn~  : ∀ {s s′} → n < s → n + n < s′ → SrcNum κ s s′

-- WHETHER THE SWEEP KEEPS A LIVE SOURCE: a slot's, or one some registration
-- is still at
guardOf : ∀ {n} {Γ : Ctx n} {t} → List (RegRow Γ t) → LiveSource Γ → Bool
guardOf {n = n} reg l = (LiveSource.source l <ᵇ n) ∨ any (λ p → sameSource (LiveSource.source l) (regSource (proj₁ (proj₂ p)))) reg

-- WHETHER A REGISTRATION SITS WHERE ITS SOURCE WAS MINTED: a slot's at its
-- slot, a minted source's above every slot
aboveᵇ : ∀ {n} {Γ : Ctx n} → RegSrc Γ → Bool
aboveᵇ (atSlot _)        = true
aboveᵇ {n} (atDyn s _)   = n ≤ᵇ s

above-≤ : ∀ {n s} → (n ≤ᵇ s) ≡ true → n ≤ s
above-≤ {n} {s} e = ≤ᵇ⇒≤ n s (subst T (sym e) tt)

-- HOW MANY REGISTRATIONS STAND AT ONE SOURCE
srcCount : ∀ {n} {Γ : Ctx n} {t} → Source → List (RegRow Γ t) → ℕ
srcCount k []              = 0
srcCount k ((_ , s , _) ∷ r) = if sameSource k (regSource s) then suc (srcCount k r) else srcCount k r

-- A HOT SLOT'S SHARE HAS CONNECTED ONCE OR NOT AT ALL.  The connect
-- subscribes the raw slot once and never again, so one row stands at it;
-- before the connect nothing reads the share, and once the share is spent
-- both are dropped and a later reader registers nothing.  The input block
-- holds no cut, so a connected share loses its raw row only to the raw
-- slot's own end: a connected share with no raw row has a latched one.
Census : ∀ {n} {Γ : Ctx n} {t} → Source → Source → List (RegRow Γ t) → Bool → Bool → Set
Census raw stamped reg conn done =
  (srcCount raw reg ≡ 1 × conn ≡ true) ⊎ (srcCount raw reg ≡ 0 × srcCount stamped reg ≡ 0 × (conn ≡ true → done ≡ true))

-- the sweep reads a source's number alone
guard-src : ∀ {n} {Γ : Ctx n} {t} (reg : List (RegRow Γ t)) {l l₂ : LiveSource Γ}
          → LiveSource.source l₂ ≡ LiveSource.source l → guardOf reg l₂ ≡ guardOf reg l
guard-src {n = n} reg {l} {l₂} e = cong (λ x → (x <ᵇ n) ∨ any (λ p → sameSource x (regSource (proj₁ (proj₂ p)))) reg) e

-- two sources' numbers against the arrival's pair: one is the arrival's exactly when the other is
SameAt : Source → Source → Source → Source → Set
SameAt s s′ x x′ = (x ≡ s → x′ ≡ s′) × (x′ ≡ s′ → x ≡ s)

-- an arrival's pair of sources against one pair of rows' sources: the
-- arrival is the row's exactly when it is the partner's, and then the
-- element types are the rows'
ArrRel : Source → Source → Ty → Ty → Source → Source → Ty → Ty → Set
ArrRel s s′ u u′ src src′ x x′ = (s ≡ src → s′ ≡ src′ × u ≡ x × u′ ≡ x′) × (s′ ≡ src′ → s ≡ src)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  Γ′ : Ctx (n + n)
  Γ′ = plainᵏ Γ κ

  ----------------------------------------------------------------
  -- Values
  ----------------------------------------------------------------

  mutual

    -- the impl's value against the plain run's
    V : ∀ t → Val Γ′ (plainᵗ t) → Val Γ t → Set
    V unitᵗ     v        w        = v ≡ w
    V boolᵗ     v        w        = v ≡ w
    V natᵗ      v        w        = v ≡ w
    V uniqᵗ     v        w        = v ≡ w
    V (s ×ᵗ t)  (a , b)  (c , d)  = V s a c × V t b d
    V (s +ᵗ t)  (inj₁ a) (inj₁ c) = V s a c
    V (s +ᵗ t)  (inj₂ b) (inj₂ d) = V t b d
    V (s +ᵗ t)  (inj₁ _) (inj₂ _) = ⊥
    V (s +ᵗ t)  (inj₂ _) (inj₁ _) = ⊥
    V (listᵗ t) vs       ws       = Pointwise (V t) vs ws
    V (obs t)   x        y        = ObsRel t x y

    -- an observable is its elaboration, renamed, over a related env
    data ObsRel (t : Ty) : Val Γ′ (obs (emitᵗ t)) → Val Γ (obs t) → Set where
      elab : ∀ {Θ Θ′} (s : SExp Γ [] [] Θ t) (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ : Env Γ′ Θ′} {ρ : Env Γ Θ}
           → EnvRel Θ w ρ′ ρ
           → ObsRel t (Θ′ , renExp (λ x → x) (λ x → x) w (toInstEmit κ s) , ρ′) (Θ , plainExp s , ρ)

    -- slot for slot, the author's variables where `toInstEmitTm` reads them
    EnvRel : ∀ Θ {Θ′} → Ren∈ (plainᶜ⁺ Θ) Θ′ → Env Γ′ Θ′ → Env Γ Θ → Set
    EnvRel Θ w ρ′ ρ = ∀ {u} (x : u ∈ Θ) → V u (lookupEnv ρ′ (w (∈-++⁺ˡ (∈-map⁺ plainᵗ x)))) (lookupEnv ρ x)

  -- a deferred body: the plain body against its elaboration's hop
  data DeferRel (u : Ty) : Val Γ′ (obs (emitᵗ u)) → Val Γ (obs u) → Set where
    elab : ∀ {Θ Θ′} (s : SExp Γ [] [] Θ u) (w : Ren∈ (plainᶜ⁺ Θ) Θ′) {ρ′ : Env Γ′ Θ′} {ρ : Env Γ Θ}
         → EnvRel Θ w ρ′ ρ
         → DeferRel u (Θ′ , renExp (λ x → x) (λ x → x) w (deferBodyᵖ (toInstEmit κ s)) , ρ′) (Θ , plainExp s , ρ)

  -- one impl emit against the plain values it carries
  EmitRel : ∀ t → Val Γ′ (emitᵗ t) → List (Val Γ t) → Set
  EmitRel t e′ vs = Pointwise (λ x w → V t (proj₂ x) w) (emitValues (decodeEmit e′)) vs

  instantOf : ∀ {t} → Val Γ′ (emitᵗ t) → ℕ
  instantOf e′ = InstEmit.instant (decodeEmit e′)

  -- an impl step on emits lifting a plain step on the values one carries
  Lifts : ∀ s u → (Val Γ′ (emitᵗ s) → Val Γ′ (emitᵗ u)) → (List (Val Γ s) → List (Val Γ u)) → Set
  Lifts s u G′ G = ∀ e′ vs → EmitRel s e′ vs → EmitRel u (G′ e′) (G vs) × instantOf (G′ e′) ≡ instantOf e′

  -- the elaborated scan's step against the plain one: a related cell
  -- goes to a related cell, and the emit it carries holds the outputs
  ScanLifts : ∀ s u → FnClo Γ′ (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u) → FnClo Γ (u ×ᵗ s) u → Set
  ScanLifts s u F′ F =
    ∀ a′ em a e′ vs → V u a′ a → EmitRel s e′ vs →
      V u (proj₁ (applyClo F′ ((a′ , em) , e′))) (proj₂ (scanVals F a vs))
    × EmitRel u (proj₂ (applyClo F′ ((a′ , em) , e′))) (proj₁ (scanVals F a vs))
    × instantOf {u} (proj₂ (applyClo F′ ((a′ , em) , e′))) ≡ instantOf e′

  -- the elaborated cut's step against the plain take: the budget kept
  -- related while nothing cuts, the cut decided alike, and the prefix
  -- taken carried
  --
  -- `Bud` RELATES ONLY THE PLAIN BUDGETS A ROW CAN CARRY, WHICH ARE
  -- POSITIVE.  A plain take is installed at a positive count and a cut
  -- clears the row, so zero is never one; a test's cell holds `tt`, so
  -- its plain budget is pinned at one.  A cut leaves the plain budget at
  -- zero, so the budget after is owed only on a step that does not cut.
  -- REFUTED: `Refuted.Cut-Budget` -- a test's `Bud` at `⊤`: one impl
  --   step owes the plain step at budget zero and at budget one; and a
  --   count's at `_≡_`, where the elaborated cutter cuts at zero on an
  --   emit carrying nothing.
  CutLifts : ∀ B s → (Val Γ′ B → ℕ → Set) → FnClo Γ′ (CutS B s ×ᵗ emitᵗ s) (CutS B s)
           → Maybe (FnClo Γ s boolᵗ) → Set
  CutLifts B s Bud F′ P =
    ∀ b′ b os em e′ vs → Bud b′ b → EmitRel s e′ vs →
      (proj₂ (proj₂ (takeVals P b vs)) ≡ false
        → Bud (proj₁ (applyClo F′ ((b′ , (false , (os , em))) , e′))) (proj₁ (proj₂ (takeVals P b vs))))
    × proj₁ (proj₂ (applyClo F′ ((b′ , (false , (os , em))) , e′))) ≡ proj₂ (proj₂ (takeVals P b vs))
    × EmitRel s (proj₂ (proj₂ (proj₂ (applyClo F′ ((b′ , (false , (os , em))) , e′))))) (proj₁ (takeVals P b vs))
    × instantOf {s} (proj₂ (proj₂ (proj₂ (applyClo F′ ((b′ , (false , (os , em))) , e′))))) ≡ instantOf e′

  ----------------------------------------------------------------
  -- Live sources
  ----------------------------------------------------------------

  -- a deferred hop, pending: the body it will subscribe
  data DeferPend (u : Ty) : Tick × Val Γ′ (echoᵗ (emitᵗ u)) → Tick × Val Γ (echoᵗ u) → Set where
    hop : ∀ {k k′ x x′} → DeferRel u x′ x → DeferPend u (k′ , (inj₁ tt , inj₂ x′)) (k , (inj₁ tt , inj₂ x))

  -- a live source of the plain run against its partner: a script's
  -- values related at the plain type, or a deferred hop's body
  data Src : LiveSource Γ → LiveSource Γ′ → Set where
    data~  : ∀ {l l′} (eq : LiveSource.elemTy l′ ≡ plainᵗ (LiveSource.elemTy l))
           → Pointwise (λ p′ p → V (LiveSource.elemTy l) (subst (Val Γ′) eq (proj₂ p′)) (proj₂ p))
                       (LiveSource.pending l′) (LiveSource.pending l)
           -- a slot's source holds its slot's type
           → (∀ (i : Fin n) → LiveSource.source l ≡ toℕ i → LiveSource.elemTy l ≡ lookup Γ i)
           → Src l l′
    defer~ : ∀ {u src src′ o o′ ps ps′} → n < src → Pointwise (DeferPend u) ps′ ps
           → Src (record { source = src ; ordinal = o ; elemTy = echoᵗ u ; pending = ps })
                 (record { source = src′ ; ordinal = o′ ; elemTy = echoᵗ (emitᵗ u) ; pending = ps′ })

  -- two sources standing at the same place in the two live lists, and the
  -- element types they hold
  data SrcPair : List (LiveSource Γ) → List (LiveSource Γ′) → Source → Source → Ty → Ty → Set where
    here  : ∀ {l l′ LP LI} → SrcPair (l ∷ LP) (l′ ∷ LI) (LiveSource.source l) (LiveSource.source l′) (LiveSource.elemTy l) (LiveSource.elemTy l′)
    there : ∀ {l l′ LP LI s s′ u u′} → SrcPair LP LI s s′ u u′ → SrcPair (l ∷ LP) (l′ ∷ LI) s s′ u u′

  ----------------------------------------------------------------
  -- Paths
  ----------------------------------------------------------------

  -- the impl's shared slot i stands at the plain slot's emit
  sharedEq : ∀ i → lookup κ i ≡ sharedᵏ → lookup Γ′ (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)
  sharedEq i sh = trans (stampedSlot Γ κ i) (cong (slotTy (lookup Γ i)) sh)

  hotEq : ∀ i → lookup κ i ≡ hotᵏ → lookup Γ′ (n ↑ʳ i) ≡ emitᵗ (lookup Γ i)
  hotEq i h = trans (stampedSlot Γ κ i) (cong (slotTy (lookup Γ i)) h)

  module _ (π : List (NodeId × List NodeId)) where

    -- AN IMPL-ONLY NODE A ROW READS IS NONE OF `π`'S: a write to a paired
    -- node then reaches it only where the pairing does
    Unpaired : NodeId → Set
    Unpaired k = k ∈ concatMap proj₂ π → ⊥

    -- the switch's current inner, paired through `π`
    CurRel : Maybe NodeId → Maybe NodeId → Set
    CurRel nothing  nothing   = ⊤
    CurRel (just j) (just j′) = (j , j′ ∷ []) ∈ π
    CurRel _        _         = ⊥

    -- a flattener's own node against the impl's
    data FlatNodes (u : Ty) : FlatOp → NodeState Γ → NodeState Γ′ → Set where
      -- one count on both sides: an emit carries one payload at most, so
      -- every lane, bounded or not, is one inner; the completion flags
      -- read off the count agree
      merge~   : ∀ {lim a q q′ od} → Pointwise (λ x′ x → ObsRel u x′ x) q′ q
               → FlatNodes u (mergeᶠ lim) (mergeAll-st {t = u} lim a q od) (mergeAll-st {t = emitᵗ u} lim a q′ od)
      switch~  : ∀ {cur cur′ od} → CurRel cur cur′
               → FlatNodes u switchᶠ (switch-st cur od) (switch-st cur′ od)
      exhaust~ : ∀ {ia od} → FlatNodes u exhaustᶠ (exhaust-st ia od) (exhaust-st ia od)

    -- a switch pairs its inner instances, which its current one names
    InnerPair : FlatOp → NodeId → NodeId → Set
    InnerPair switchᶠ    j j′ = (j , j′ ∷ []) ∈ π
    InnerPair (mergeᶠ _) _ _  = ⊤
    InnerPair exhaustᶠ   _ _  = ⊤

    module _ {t : Ty} (NP : List (NodeId × NodeState Γ)) (NI : List (NodeId × NodeState Γ′)) where

      -- a flattener's node pair, and the scan the elaboration restamps
      -- through, holding a cell of its own type: a scan finding anything
      -- else puts out nothing, so without the cell the relation admits
      -- an impl dropping every echo and lane emit the plain side delivers
      Flattener : ∀ u → FlatOp → NodeId → NodeId → NodeId → List NodeId → Set
      Flattener u op m m′ ks xs =
        (m , m′ ∷ ks ∷ xs) ∈ π
        × Σ (NodeState Γ) λ x → Σ (NodeState Γ′) λ x′ →
            lookupNode m NP ≡ just x × lookupNode m′ NI ≡ just x′ × FlatNodes u op x x′
            × Σ (Val Γ′ (FlatSᵗ u)) λ c → lookupNode ks NI ≡ just (cell-st {t = FlatSᵗ u} c)

      -- WHAT ONE FORMER'S FRAMES ARE ON THE IMPL SIDE.  A plain frame
      -- and the run of impl frames its former's elaboration installs,
      -- then the rest of both paths related again.
      data PathRel : ∀ {lo lo′ s} → Path Γ lo s t → Path Γ′ lo′ (emitᵗ s) (emitᵗ t) → Set where
        root~ : ∀ {lo lo′} → PathRel {lo} {lo′} root root

        -- a share's subject: the plain slot's and the impl's stamped one
        sink~ : ∀ {lo lo′ i} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
              → PathRel (share-sink i h)
                        (subst (λ u → Path Γ′ lo′ u (emitᵗ t)) (sharedEq i sh) (share-sink (n ↑ʳ i) h′))

        map~ : ∀ {lo lo′ ℓ ℓ′ s u} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                 {F : FnClo Γ s u} {F′ : FnClo Γ′ (emitᵗ s) (emitᵗ u)}
                 {p : Path Γ ℓ u t} {q : Path Γ′ ℓ′ (emitᵗ u) (emitᵗ t)}
             → Lifts s u (applyClo F′) (map (applyClo F)) → PathRel p q
             → PathRel (map-f F ↠[ h ] p) (map-f F′ ↠[ h′ ] q)

        -- the scan carries the author's state beside the emit, and a map projects
        scan~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ s u k k′ a a′ em Θ₀ ρ₀}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂}
                  {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo Γ′ (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u)}
                  {p : Path Γ ℓ u t} {q : Path Γ′ ℓ₂ (emitᵗ u) (emitᵗ t)}
              → (k , k′ ∷ []) ∈ π
              → lookupNode k NP ≡ just (cell-st {t = u} a)
              → lookupNode k′ NI ≡ just (cell-st {t = ScanAᵗ u} (a′ , em))
              → V u a′ a → ScanLifts s u F′ F → PathRel p q
              → PathRel (scan-f F k ↠[ h ] p)
                        (scan-f F′ k′ ↠[ h₁ ] (map-f (Θ₀ , sndᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ] q))

        -- a count: the cut's scan, its test, its projection, and the
        -- one-lane merge that decided zero at subscribe
        take~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ s k k₁ k₂ m j b b′ os em Θ₂ ρ₂ Θ₃ ρ₃ aₘ}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                  {F₁ : FnClo Γ′ (CutS natᵗ s ×ᵗ emitᵗ s) (CutS natᵗ s)}
                  {p : Path Γ ℓ s t} {q : Path Γ′ ℓ₄ (emitᵗ s) (emitᵗ t)}
              → (k , k₁ ∷ k₂ ∷ m ∷ j ∷ []) ∈ π
              → lookupNode k NP ≡ just (take-st b)
              → lookupNode k₁ NI ≡ just (cell-st {t = CutS natᵗ s} (b′ , (false , (os , em))))
              → lookupNode k₂ NI ≡ just (take-st 1)
              → lookupNode m NI ≡ just (mergeAll-st {t = emitᵗ s} nothing aₘ [] true) → aₘ ≤ 1
              → b′ ≡ b → CutLifts natᵗ s (λ b′ b → b′ ≡ b × 0 < b) F₁ nothing → PathRel p q
              → PathRel (take-f nothing k ↠[ h ] p)
                  (scan-f F₁ k₁ ↠[ h₁ ]
                   (take-f (just (Θ₂ , cutOpenᵛ , ρ₂)) k₂ ↠[ h₂ ]
                    (map-f (Θ₃ , cutOutᵛ , ρ₃) ↠[ h₃ ]
                     (from-inner mergeAllᵒ m j ↠[ h₄ ] q))))

        -- a test: the same run, with no merge, since nothing is decided at subscribe
        takeWhile~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s k k₁ k₂ os em Θ₂ ρ₂ Θ₃ ρ₃}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                       {P : FnClo Γ s boolᵗ} {F₁ : FnClo Γ′ (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                       {p : Path Γ ℓ s t} {q : Path Γ′ ℓ₃ (emitᵗ s) (emitᵗ t)}
                   → (k , k₁ ∷ k₂ ∷ []) ∈ π
                   → lookupNode k NP ≡ just (take-st 1)
                   → lookupNode k₁ NI ≡ just (cell-st {t = CutS unitᵗ s} (tt , (false , (os , em))))
                   → lookupNode k₂ NI ≡ just (take-st 1)
                   → CutLifts unitᵗ s (λ _ b → b ≡ 1) F₁ (just P) → PathRel p q
                   → PathRel (take-f (just P) k ↠[ h ] p)
                       (scan-f F₁ k₁ ↠[ h₁ ]
                        (take-f (just (Θ₂ , cutOpenᵛ , ρ₂)) k₂ ↠[ h₂ ]
                         (map-f (Θ₃ , cutOutᵛ , ρ₃) ↠[ h₃ ] q)))

        -- a flattener's outer, one element per emit: `elemᵛ`, the
        -- flattener, and the scan that restamps what it puts out
        outerElem~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                       {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                       {p : Path Γ ℓ u t} {q : Path Γ′ ℓ₄ (emitᵗ u) (emitᵗ t)}
                   → Flattener u op m m′ ks [] → PathRel p q
                   → PathRel (thru-outer (flatOp op) m ↠[ h ] p)
                       (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ]
                        (thru-outer (flatOp op) m′ ↠[ h₂ ]
                         (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₃ ]
                          (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q))))

        -- one element per inner: `explodeᵛ`'s run of elements, merged
        -- into one outer for the flattener
        outerExplode~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                          {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                          {p : Path Γ ℓ u t} {q : Path Γ′ ℓ₆ (emitᵗ u) (emitᵗ t)}
                      → Flattener u op m m′ ks (mX ∷ []) → PathRel p q
                      → PathRel (thru-outer (flatOp op) m ↠[ h ] p)
                          (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                           (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                            (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                             (thru-outer (flatOp op) m′ ↠[ h₄ ]
                              (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                               (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q))))))

        -- leaving an inner: the flattener's lane, then its restamp
        inner~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks xs j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                   {p : Path Γ ℓ u t} {q : Path Γ′ ℓ₃ (emitᵗ u) (emitᵗ t)}
               → Flattener u op m m′ ks xs → InnerPair op j j′ → PathRel p q
               → PathRel (from-inner (flatOp op) m j ↠[ h ] p)
                   (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                    (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                     (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))

        -- an inner the elaboration led with its echo: one more merge,
        -- impl only, in front of the lane it rides
        lane~ : ∀ {lo lo′ ℓ ℓ′ u op m j mL jL aL} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                  {p : Path Γ ℓ u t} {Q : Path Γ′ ℓ′ (emitᵗ u) (emitᵗ t)}
              → lookupNode mL NI ≡ just (mergeAll-st {t = emitᵗ u} nothing aL [] true) → Unpaired mL
              → PathRel (from-inner (flatOp op) m j ↠[ h ] p) Q
              → PathRel (from-inner (flatOp op) m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)

        -- a deferred body: the hop's marker merge, its restamp, the hop's node
        deferInner~ : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀ a}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path Γ′ ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → (nid , nid′ ∷ []) ∈ π → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ π
                    → lookupNode nid NP ≡ just (mergeAll-st {t = u} nothing a [] true)
                    → lookupNode nid′ NI ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
                    → lookupNode m2 NI ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true) → a ≤ 1
                    → PathRel p q
                    → PathRel (from-inner mergeAllᵒ nid j ↠[ h ] p)
                        (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                         (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                          (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))

      -- WHAT A SCRIPT READ BY THE ELABORATION RUNS THROUGH, `inputᵖ`:
      -- the marked merge, the subscribe bracket, the stamp, and the
      -- merge that flattens the stamped emits.  The block, then its tail
      --
      -- A ONE-LANE MERGE'S COUNT IS ONE OR ZERO, NEVER A LITERAL ONE, here
      -- and at a count's and a deferred body's merges.  A source's close
      -- cascade ends the inner its rows ride, and the inner's finish finds
      -- no live row through it (the rows are dying and delivered), so the
      -- merge drops to zero and its outer's bit goes up; the rows stay
      -- registered until the finish drops them, and the stores must hold in
      -- between.  Zero is also where an end leaves the merge again, so the
      -- relation is closed under it
      data InputBlock (a : Ty) : ∀ {lo ℓ} → Path Γ′ lo a (emitᵗ t) → Path Γ′ ℓ (machineEmitᵗ a) (emitᵗ t) → Set where
        block : ∀ {lo ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ m1 j1 b m2 Θ₀ ρ₀ Θ₃ fr ρ₃ Θ₄ ρ₄ a₁ d₂}
                  {h₁ : lo ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                  {q : Path Γ′ ℓ₆ (machineEmitᵗ a) (emitᵗ t)}
              → lookupNode m1 NI ≡ just (mergeAll-st {t = unitᵗ +ᵗ a} nothing a₁ [] true) → a₁ ≤ 1
              → lookupNode b NI ≡ just (batchSync-st {s = unitᵗ +ᵗ a} false [] false)
              → lookupNode m2 NI ≡ just (mergeAll-st {t = machineEmitᵗ a} nothing 0 [] d₂)
              → Unpaired m1 → Unpaired b → Unpaired m2
              → InputBlock a
                  (map-f (Θ₀ , inrᵗ (varᵗ (here refl)) , ρ₀) ↠[ h₁ ]
                   (from-inner mergeAllᵒ m1 j1 ↠[ h₂ ]
                    (batchSync-f b ↠[ h₃ ]
                     (map-f (uniqᵗ ∷ Θ₃ , inputStampᵖ fr , ρ₃) ↠[ h₄ ]
                      (map-f (Θ₄ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₄) ↠[ h₅ ]
                       (thru-outer mergeAllᵒ m2 ↠[ h₆ ] q))))))
                  q

      module _ (LP : List (LiveSource Γ)) (LI : List (LiveSource Γ′)) where

        -- a plain registration against the impl's that the elaboration made for it
        data RowRel : RegRow Γ t → RegRow Γ′ (emitᵗ t) → Set where
          -- a hot or shared slot, read through the share at its stamped slot
          read~ : ∀ {rid rid′ i Θ₀ ρ₀ ℓ′} {X : Tm Γ′ [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ}
                    {h : suc (toℕ (n ↑ʳ i)) ≤ ℓ′}
                    {p : Path Γ (suc (toℕ i)) (lookup Γ i) t} {q : Path Γ′ ℓ′ (emitᵗ (lookup Γ i)) (emitᵗ t)} {c′}
                → lookup κ i ≡ hotᵏ ⊎ lookup κ i ≡ sharedᵏ
                → PathRel p q
                → c′ ≡ (emitᵗ (lookup Γ i) , (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q))
                → RowRel (rid , atSlot i , (lookup Γ i , p)) (rid′ , atSlot (n ↑ʳ i) , c′)
          -- a cold's asynchronous tail, at partnered sources
          cold~ : ∀ {rid rid′ src src′ lo lo′ s ℓ} {p : Path Γ lo s t}
                    {full : Path Γ′ lo′ (plainᵗ s) (emitᵗ t)} {q : Path Γ′ ℓ (emitᵗ s) (emitᵗ t)} {c′}
                → SrcPair LP LI src src′ s (plainᵗ s) → InputBlock (plainᵗ s) full q → PathRel p q
                → c′ ≡ (plainᵗ s , full)
                → RowRel (rid , atDyn src lo , (s , p)) (rid′ , atDyn src′ lo′ , c′)
          -- a deferred hop, not yet fired, at partnered sources
          defer~ : ∀ {rid rid′ src src′ lo lo′ ℓ ℓ′ u nid nid′} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                     {p : Path Γ ℓ u t} {q : Path Γ′ ℓ′ (emitᵗ u) (emitᵗ t)} {c′}
                 → SrcPair LP LI src src′ (echoᵗ u) (echoᵗ (emitᵗ u)) → (nid , nid′ ∷ []) ∈ π
                 → lookupNode nid NP ≡ just (mergeAll-st {t = u} nothing 0 [] false)
                 → lookupNode nid′ NI ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
                 → PathRel p q
                 → c′ ≡ (echoᵗ (emitᵗ u) , (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q))
                 → RowRel (rid , atDyn src lo , (echoᵗ u , (thru-outer mergeAllᵒ nid ↠[ h ] p)))
                          (rid′ , atDyn src′ lo′ , c′)

        -- the impl's own registration: a hot script's raw slot, wrapped
        -- once into the share every reader reads
        data MachRow : RegRow Γ′ (emitᵗ t) → Set where
          hot~ : ∀ {rid i ℓ} (hot : lookup κ i ≡ hotᵏ) {h : ℓ ≤ toℕ (n ↑ʳ i)}
                   {full : Path Γ′ (suc (toℕ (i ↑ˡ n))) (plainᵗ (lookup Γ i)) (emitᵗ t)} {c′}
               → InputBlock (plainᵗ (lookup Γ i)) full
                   (subst (λ u → Path Γ′ ℓ u (emitᵗ t)) (hotEq i hot) (share-sink (n ↑ʳ i) h))
               → c′ ≡ (plainᵗ (lookup Γ i) , full)
               → MachRow (rid , atSlot (i ↑ˡ n) , c′)

        -- the registries in subscription order, the impl's own rows between
        data RegRel : List (RegRow Γ t) → List (RegRow Γ′ (emitᵗ t)) → Set where
          []   : RegRel [] []
          _∷_  : ∀ {r r′ rs rs′} → RowRel r r′ → RegRel rs rs′ → RegRel (r ∷ rs) (r′ ∷ rs′)
          mach : ∀ {rs r′ rs′} → MachRow r′ → RegRel rs rs′ → RegRel rs (r′ ∷ rs′)

        -- two registrations the relation pairs
        Partners : ∀ {rs rs′} → RegRel rs rs′ → RegRow Γ t → RegRow Γ′ (emitᵗ t) → Set
        Partners []                          x x′ = ⊥
        Partners (_∷_ {r = r} {r′ = r′} _ q) x x′ = (x ≡ r × x′ ≡ r′) ⊎ Partners q x x′
        Partners (mach _ q)                  x x′ = Partners q x x′

        partner-row : ∀ {rs rs′} (q : RegRel rs rs′) {x x′} → Partners q x x′ → RowRel x x′
        partner-row (r ∷ q)    (inj₁ (refl , refl)) = r
        partner-row (r ∷ q)    (inj₂ p)             = partner-row q p
        partner-row (mach _ q) p                    = partner-row q p

        -- the same, at every minted source's row the registries pair
        ArrRows : ∀ {rs rs′} → RegRel rs rs′ → Source → Source → Ty → Ty → Set
        ArrRows []                                                                  s s′ u u′ = ⊤
        ArrRows (read~ _ _ _ ∷ q)                                                   s s′ u u′ = ArrRows q s s′ u u′
        ArrRows (cold~ {src = src} {src′ = src′} {s = x} _ _ _ _ ∷ q)               s s′ u u′ =
          ArrRel s s′ u u′ src src′ x (plainᵗ x) × ArrRows q s s′ u u′
        ArrRows (defer~ {src = src} {src′ = src′} {u = x} _ _ _ _ _ _ ∷ q)          s s′ u u′ =
          ArrRel s s′ u u′ src src′ (echoᵗ x) (echoᵗ (emitᵗ x)) × ArrRows q s s′ u u′
        ArrRows (mach _ q)                                                          s s′ u u′ = ArrRows q s s′ u u′

  -- the completion and connection latches, slot for stamped slot.  A hot
  -- slot's latch is its raw slot's, since the raw slot ends whether or not
  -- its share ever connected, and the share is spent exactly when it did
  LatchRel : (CP SP CI SI : List Source) → Set
  LatchRel CP SP CI SI =
    ∀ i → (lookup κ i ≡ hotᵏ → memberSource (toℕ i) CP ≡ memberSource (toℕ (i ↑ˡ n)) CI
                              × memberSource (toℕ (n ↑ʳ i)) CI ≡ memberSource (toℕ (i ↑ˡ n)) CI ∧ memberSource (toℕ (n ↑ʳ i)) SI)
        × (lookup κ i ≡ sharedᵏ → memberSource (toℕ i) CP ≡ memberSource (toℕ (n ↑ʳ i)) CI
                                 × memberSource (toℕ i) SP ≡ memberSource (toℕ (n ↑ʳ i)) SI)

-- the nodes a path's input block installs, if it starts with one: the
-- marked merge, its inner, the bracket and the flattening merge
-- (one frame per clause, so no split is at a computed element type)
blockNodes : ∀ {m} {Δ : Ctx m} {lo s u} → Path Δ lo s u → List NodeId
blockNodes = λ p → atInr p
  where
    atM2 atStamp atPair atB atM1 atInr : ∀ {m} {Δ : Ctx m} {lo s u} → Path Δ lo s u → List NodeId
    atM2 (thru-outer mergeAllᵒ m2 ↠[ _ ] _) = m2 ∷ []
    atM2 _                                  = []
    atPair (map-f _ ↠[ _ ] p) = atM2 p
    atPair _                  = []
    atStamp (map-f _ ↠[ _ ] p) = atPair p
    atStamp _                  = []
    atB (batchSync-f b ↠[ _ ] p) = b ∷ atStamp p
    atB _                        = []
    atM1 (from-inner mergeAllᵒ m1 j ↠[ _ ] p) = m1 ∷ j ∷ atB p
    atM1 _                                    = []
    atInr (map-f _ ↠[ _ ] p) = atM1 p
    atInr _                  = []

-- AN INPUT BLOCK'S NODES ARE ITS OWN ROW'S, AND NO OTHER ROW THREADS
-- THEM.  The block is minted at the read's subscribe, which registers the
-- one row of the script it reads, and a row registered later starts at
-- its own source, below the block; the flattening merge never subscribes
-- an inner.  It is what lets the row's end leave the block: the inner's
-- finish finds nothing alive through it, and what the end writes to the
-- block's nodes no other row reads.  Stamped slots are exempt, since a
-- reader's path is a restamp, and one inside a deferred body leads with
-- the hop's merge, which many rows thread
Owned : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} → List (RegRow (plainᵏ Γ κ) (emitᵗ t)) → Set
Owned {n} κ K =
  All (λ r → (∀ (k : Fin n) → proj₁ (proj₂ r) ≡ atSlot (n ↑ʳ k) → ⊥)
           → ∀ {j} → j ∈ blockNodes (proj₂ (proj₂ (proj₂ r)))
           → All (λ r′ → pathHasNode j (proj₂ (proj₂ (proj₂ r′))) ≡ true → r′ ≡ r) K) K

------------------------------------------------------------------
-- The stores
------------------------------------------------------------------

-- over the raw schedules and states, since a subscribe walks through
-- states no configuration names
--
-- DEAD ROUTE: a field counting a merge's lanes exactly against the
--   registry.  The end walk decrements a merge's active count once no
--   registration is alive through the inner, while the dying source's rows
--   stay registered until the end's drop, so the field fails between the walk
--   and the drop on any program that ends an inner.
record Store {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
             (sP : Sched Γ) (stP : EvalSt ep) (sI : Sched (plainᵏ Γ κ)) (stI : EvalSt ei) : Set where
  field
    π       : List (NodeId × List NodeId)
    π-keys  : Unique (map proj₁ π)
    π-vals  : Unique (concatMap proj₂ π)
    -- every node `π` pairs was minted: below its run's node counter, so
    -- a node the counter hands out next pairs apart from all of them
    pairs-below : All (λ e → proj₁ e < nodeCt sP) π × All (λ e → All (_< nodeCt sI) (proj₂ e)) π
    sources : Pointwise (Src κ) (Sched.live sP) (Sched.live sI)
    numbers : Pointwise (λ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) → SrcNum κ (LiveSource.source l) (LiveSource.source l′)) (Sched.live sP) (Sched.live sI)
    distinct : Unique (map LiveSource.source (Sched.live sP)) × Unique (map LiveSource.source (Sched.live sI))
    sync    : Sync (Sched.live sP) (Sched.live sI)
    rows    : RegRel κ π (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                (EvalSt.registry stP) (EvalSt.registry stI)
    latches : LatchRel {Γ = Γ} κ (EvalSt.completedSources stP) (EvalSt.connectedShares stP)
                                     (EvalSt.completedSources stI) (EvalSt.connectedShares stI)
    -- every live source was minted: below its run's counter
    bounded : All (_< counter (Sched.mint sP) sourceᵏ) (map LiveSource.source (Sched.live sP))
            × All (_< counter (Sched.mint sI) sourceᵏ) (map LiveSource.source (Sched.live sI))
    -- a pair of live sources is swept alike
    swept   : Pointwise (λ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) → guardOf (EvalSt.registry stP) l ≡ guardOf (EvalSt.registry stI) l′)
                (Sched.live sP) (Sched.live sI)
    -- a registration still in the registry is not a cascade's victim
    uncut   : All (λ r → any (_≡ᵇ proj₁ r) (EvalSt.cancelled stP) ≡ false) (EvalSt.registry stP)
            × All (λ r → any (_≡ᵇ proj₁ r) (EvalSt.cancelled stI) ≡ false) (EvalSt.registry stI)
    -- a registration at a minted source is above every slot
    above   : All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) (EvalSt.registry stP)
            × All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) (EvalSt.registry stI)
    -- each hot slot's raw row, and its readers only behind one
    census  : ∀ i → lookup κ i ≡ hotᵏ → Census (toℕ (i ↑ˡ n)) (toℕ (n ↑ʳ i)) (EvalSt.registry stI)
                                          (memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI))
                                          (memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI))
    -- each input block's inner, its own row's
    owned   : Owned {Γ = Γ} κ (EvalSt.registry stI)
    -- each run keeps the evaluator's rule
    ruleP   : Rule sP stP
    ruleI   : Rule sI stI

-- A POPPED ARRIVAL'S PAIR OF SOURCES AGAINST THE ROWS: every minted
-- source's row is the arrival's exactly when its partner is the other
-- arrival's, and both sources were minted before the stores' counters.
-- It is the pairing a cascade's second walk needs, and it is not part of
-- a store: it names an arrival.
record Arr {n} {Γ : Ctx n} {κ : Kinds n} {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
           {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
           (S : Store κ sP stP sI stI) (s s′ : Source) (u u′ : Ty) : Set where
  field
    boundP : s < counter (Sched.mint sP) sourceᵏ
    boundI : s′ < counter (Sched.mint sI) sourceᵏ
    rows   : ArrRows κ (Store.π S) _ _ _ _ (Store.rows S) s s′ u u′
    lists  : Pointwise (λ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) → SameAt s s′ (LiveSource.source l) (LiveSource.source l′))
               (Sched.live sP) (Sched.live sI)
