------------------------------------------------------------------
-- A CASCADE'S VALUE PASS, ONE PATH CONSTRUCTOR AT A TIME.  A related
-- chain hands its values down two related paths, and the fold reads
-- both derivations together: one `PathRel` constructor's frames per
-- step, the stores kept related, the values each sends rootward
-- related, and the chains the pass has not reached kept paired.
--
-- A STEP'S ARM SEES THE PLAIN FRAME'S STEP AND THE IMPL'S WHOLE FOLD.
-- The impl runs a former's frames where the plain run steps once, so an
-- arm takes the impl fold from the top of that run and hands back what
-- is left of it below the run: the tail the plain path continues on,
-- related again, and the group that reaches it.  The plain fold is the
-- descent; an impl-only lane is the one step that moves the impl alone.
------------------------------------------------------------------
module Simulation.Pass where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_; _↑ˡ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool.ListAction using (any)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; map; concat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺)
open import Data.Maybe   using (nothing; just)
open import Data.Nat     using (ℕ; suc; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Data.Vec     using (lookup)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Prim      using (Tick; valueᵖ; completeᵖ)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; Env; FlatOp; uniqᵗ; unitᵗ; _×ᵗ_; _+ᵗ_; obs; FnClo; applyClo; Tm; varᵗ; unit̂; pairᵗ; inlᵗ; inrᵗ; sndᵗ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState; Arrival; arrVal; arrTy; arrTick; cascadeClose; shareSpend; shareDying; memberSource; Path; Frame; share-sink;
  _↠[_]_; scan-f; take-f; map-f; thru-outer; from-inner; mergeAllᵒ; lookupNode; mergeAll-st; echoᵗ; thruEvents; thruWrap; RegId; RegRow; AtFloor; atDyn; atSlot; chainsOf)
open import Rx.Evaluator.Domain using (flatOp; foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; step-thru-outer; thruWalk⇓; walk-nil; walk-echo; walk-cons;
  thruConsume⇓; chainStep⇓; chain-step;
  cascadeGo⇓; casc-nil; casc-cut; casc-live; shareGo⇓; go-nil; go-cut; go-live; dispatchShare⇓)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; hotᵏ; sharedᵏ)
open import SExp.Elaborate using (restampᵛ; subscribeᵛ; deliveryᵛ; flatStepᵛ; elemᵛ; explodeᵛ; FlatSᵗ)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import SExp.Plain   using (plainValues)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Lockstep using (concat-++; values-++; decode-++; extract-++)
open import Simulation.Schedules using (HeadOf)
open import Simulation.Stores using (srcCount; V; EmitRel; ObsRel; Lifts; Flattener; FlatNodes; merge~; switch~; exhaust~; CurRel; Src; SrcPair; sharedEq; PathRel; root~; sink~; map~; scan~; take~; takeWhile~;
  outerElem~; outerExplode~; inner~; lane~; deferInner~; InputBlock; hotEq; RowRel; read~; cold~; defer~; RegRel; Partners; partner-row; Store; Arr)
open import Simulation.Walk using (readᴾ; readᴵ)
open import Rx.Evaluator.Reducible.Support using (Sound; sub-rule; NodeOn; node-on; drop-ot; head-on; self-node; push-thru; sub-ot; Agree; endOf; ∨-Tʳ)
open import Rx.Evaluator.Reducible.Rule-Kept using (Thru; RuleKept; step-kept; fold-kept; stepFrame-rule; thruConsume-rule)

readᴾ-++ : ∀ {n} {Γ : Ctx n} {t} (xs ys : Stream Γ t) → readᴾ (xs ++ ys) ≡ readᴾ xs ++ readᴾ ys
readᴾ-++ xs ys = trans (cong plainValues (concat-++ xs ys)) (values-++ (concat xs) (concat ys))

readᴵ-++ : ∀ {m} {Γ′ : Ctx m} {t} (xs ys : Stream Γ′ (instEmitᵗ uniqᵗ t)) → readᴵ (xs ++ ys) ≡ readᴵ xs ++ readᴵ ys
readᴵ-++ xs ys =
  trans (cong (λ z → instExtract (decodeEmits z)) (concat-++ xs ys))
 (trans (cong instExtract (decode-++ (concat xs) (concat ys)))
        (extract-++ (decodeEmits (concat xs)) (decodeEmits (concat ys))))

-- a minted source's chain, as the registration it was read from
dynRow : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ) → RegId × AtFloor Γ (arrTy a) t → RegRow Γ t
dynRow a (rid , lo , p) = rid , atDyn (Arrival.source a) lo , (arrTy a , p)

-- A CHAIN PAIR THE PASS HAS NOT REACHED: cut on both sides, or on
-- neither and partnered by the registries' relation
PairedR : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
        → RegRel κ π {t} NP NI LP LI rs rs′ → List RegId → List RegId
        → RegRow Γ t → RegRow (plainᵏ Γ κ) (emitᵗ t) → Set
PairedR {κ = κ} rr CP CI x x′ =
    (any (_≡ᵇ proj₁ x) CP ≡ true × any (_≡ᵇ proj₁ x′) CI ≡ true)
  ⊎ (any (_≡ᵇ proj₁ x) CP ≡ false × any (_≡ᵇ proj₁ x′) CI ≡ false
     × Partners κ _ _ _ _ _ rr x x′)

-- the same, for a minted source's chains
Paired : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
       → RegRel κ π {t} NP NI LP LI rs rs′ → List RegId → List RegId → (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ))
       → RegId × AtFloor Γ (arrTy a) t → RegId × AtFloor (plainᵏ Γ κ) (arrTy a′) (emitᵗ t) → Set
Paired rr CP CI a a′ c c′ = PairedR rr CP CI (dynRow a c) (dynRow a′ c′)

clash : true ≡ false → ⊥
clash ()

-- the fold a chain step runs
unchain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ} {vs fin x sched st r}
        → chainStep⇓ {e = e} a vs fin x sched st r → foldPath⇓ (arrTick a) (proj₂ x) vs fin sched st r
unchain (chain-step d) = d

-- a chain step marks its row delivered, which no relation reads
delivered : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
          → Store κ sP stP sI stI → ∀ {x y}
          → Store κ sP (record stP { delivered = x }) sI (record stI { delivered = y })
delivered s = record
  { π = π ; π-keys = π-keys ; π-vals = π-vals ; sources = sources ; numbers = numbers ; distinct = distinct
  ; sync = sync ; rows = rows ; latches = latches ; bounded = bounded ; swept = swept ; uncut = uncut ; above = above ; census = census ; owned = owned
  ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI }
  where open Store s

-- the arrival's pair against the rows is as it was, since the rows are
delivered-arr : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                  {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
                  {S : Store κ sP stP sI stI} {x y s s′ u u′}
              → Arr S s s′ u u′ → Arr (delivered S {x} {y}) s s′ u u′
delivered-arr ar = record { boundP = boundP ; boundI = boundI ; rows = rows ; lists = lists } where open Arr ar

-- A PLAIN CHAIN AT A SLOT AND THE REGISTRATION THE ELABORATION READ IT THROUGH:
-- the stamped slot's share fans out to exactly the rows the plain run walks
data SlotPair {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
              (rr : RegRel κ π {t} NP NI LP LI rs rs′) (CP CI : List RegId) (i : Fin n) {u : Ty}
            : RegId × AtFloor Γ u t
            → RegId × Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) (lookup (plainᵏ Γ κ) (n ↑ʳ i)) (emitᵗ t) → Set where
  slotpair : ∀ {rid rid′ p p′}
           → PairedR rr CP CI (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (lookup (plainᵏ Γ κ) (n ↑ʳ i) , p′))
           → SlotPair rr CP CI i (rid , suc (toℕ i) , p) (rid′ , p′)

-- a node a run left as it found it
data Unmoved {n} {Γ : Ctx n} (k : NodeId) (N′ N : List (NodeId × NodeState Γ)) : Set where
  unmoved : lookupNode k N′ ≡ lookupNode k N → Unmoved k N′ N

-- A NODE OFF A PATH THE RULE HOLDS FOR, which is what a fold down the
-- path needs to leave the node as it found it
Clear : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} → NodeId → Path Γ lo s t → Sched Γ → EvalSt e → Set
Clear k p sched st = NodeOn k p sched st × Sound p sched st

-- the impl's tail below a flattener: the flattener's node and its
-- restamp's cell both off it
ClearI : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} → NodeId → NodeId → Path Γ lo s t → Sched Γ → EvalSt e → Set
ClearI k ks q sched st = Clear k q sched st × NodeOn ks q sched st

postulate
  -- A FOLD LEAVES A NODE OFF ITS PATH AS IT FOUND IT, the node below
  -- the counter and its rows ending where the path does.  The
  -- candidate's `Kept` is this clause, proven of the evaluator's own
  -- fold on standing ground; this owes it of every derivation.
  --
  -- TWIN: `foldPath-rule` -- the same induction, a clause per
  --   constructor, there keeping the rule where this keeps the node.
  fold-unmoved : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {κ : Path Γ lo s t} {k now vals fin sched st r}
               → foldPath⇓ {e = e} now κ vals fin sched st r → Clear k κ sched st
               → lookupNode k (EvalSt.nodes (proj₂ (proj₂ r))) ≡ lookupNode k (EvalSt.nodes st)

-- so a fold misses it
missed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {κ : Path Γ lo s t} {k now vals fin sched st r}
       → foldPath⇓ {e = e} now κ vals fin sched st r → Clear k κ sched st
       → Unmoved k (EvalSt.nodes (proj₂ (proj₂ r))) (EvalSt.nodes st)
missed d c = unmoved (fold-unmoved d c)

-- a node off a path is off the path below its head frame
on-drop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u} {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
            {k sched} {st : EvalSt e}
        → NodeOn k (f ↠[ le ] κ) sched st → NodeOn k κ sched st
on-drop (node-on ea lt op) = node-on ea lt (λ h → op (∨-Tʳ h))

-- a flattener's frame on a path, as its node off the path below
unthru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ u} {op k} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
           {sched} {st : EvalSt e}
       → Sound (thru-outer op k ↠[ le ] κ) sched st → Clear k κ sched st
unthru {k = k} so = head-on _ _ _ k (self-node k []) so , drop-ot _ _ _ so

-- and back, as the flattener's own path
thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} {k} {κ : Path Γ lo u t} {sched} {st : EvalSt e}
     → Clear k κ sched st → Sound (Thru {e = e} k κ) sched st
thru {k = k} {κ = κ} (on , so) = push-thru mergeAllᵒ k ≤-refl κ so on

-- A RUN KEEPING THE RULE FOR EVERY PATH AGREEING WITH ONE THAT ENDS
-- WHERE `κ` DOES keeps a node off `κ`
reclear : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo lo′ u s′} {k} {κ : Path Γ lo u t} {π : Path Γ lo′ s′ t}
            {sched sched′} {st st′ : EvalSt e}
        → endOf π ≡ endOf κ → Clear k κ sched st → RuleKept π sched st sched′ st′ → Clear k κ sched′ st′
reclear {e = e} {k = k} {κ = κ} eq c rk = unthru (rk (Thru {e = e} k κ) (thru c) (λ _ _ _ → eq))

-- a step keeps a node off its own path
step-clear : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u} {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
               {k now vals fin sched st out vals′ fin′ sched′ st′}
           → stepFrame⇓ {e = e} now f κ vals fin sched st (out , vals′ , fin′ , sched′ , st′)
           → Clear k (f ↠[ le ] κ) sched st → Clear k (f ↠[ le ] κ) sched′ st′
step-clear {f = f} {le = le} {κ = κ} d c = reclear {π = f ↠[ le ] κ} refl c (stepFrame-rule le d (proj₂ c))

-- a fold down a sound path of the same end keeps it too
fold-clear : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo lo′ u s′} {k} {κ : Path Γ lo u t} {π : Path Γ lo′ s′ t}
               {now vals fin sched st r}
           → foldPath⇓ {e = e} now π vals fin sched st r → Sound π sched st → endOf π ≡ endOf κ
           → Clear k κ sched st → Clear k κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
fold-clear {π = π} d so eq c = reclear {π = π} eq c (fold-kept d so)

-- and so does consuming an inner through it
consume-clear : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} {k} {κ : Path Γ lo u t} {op now} {o : Val Γ (obs u)}
                  {sched sched′ st st′ out}
              → thruConsume⇓ {e = e} op k κ now o sched st (out , sched′ , st′)
              → Clear k κ sched st → Clear k κ sched′ st′
consume-clear {e = e} {k = k} {κ = κ} d c = reclear {π = Thru {e = e} k κ} refl c (thruConsume-rule d (thru c))

-- and the rule follows a step down its path
adv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u} {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
        {now vals fin sched st out vals′ fin′ sched′ st′}
    → stepFrame⇓ {e = e} now f κ vals fin sched st (out , vals′ , fin′ , sched′ , st′)
    → Sound (f ↠[ le ] κ) sched st → Sound κ sched′ st′
adv {le = le} d so = drop-ot _ _ _ (step-kept le d so)

-- the impl's tail below a restamp, read off the restamp's path
tail-of : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {ℓ₂ ℓ₃ ℓ₄ s u w} {C : FnClo Γ (u ×ᵗ s) u} {D : FnClo Γ u w} {ks k}
            {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {q : Path Γ ℓ₄ w t} {sched} {st : EvalSt e}
        → Clear k (scan-f C ks ↠[ h₃ ] (map-f D ↠[ h₄ ] q)) sched st → ClearI k ks q sched st
tail-of {ks = ks} (on , so) =
  (on-drop (on-drop on) , drop-ot _ _ _ (drop-ot _ _ _ so)) , on-drop (head-on _ _ _ ks (self-node ks []) so)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- WHAT A GROUP OF EMITS CARRIES: each emit's value, if it has one,
  -- in turn -- the plain group they make joined.
  --
  -- AN EMIT CARRIES AT MOST ONE VALUE, and the relation has to say so
  -- because a share tells one emit of two values from two emits of one.
  -- Its fan-out is value-major, so a plain group reaches every reader
  -- value by value, while the impl's share, running the same loop at the
  -- emit type, hands each reader a whole emit before the next reader
  -- sees it: past two readers, a two-value emit reorders the root.  A
  -- flattener's echo segment is the same gap from the other side -- the
  -- plain walk folds an echo run one value at a time where the segment
  -- folds once.  Read off the elaboration rather than instantiated:
  -- every source puts out one value per emit (an arrival is one value,
  -- `ofᵖ` splits its list), and every former keeps the count, a
  -- flattener's echo and segment holding more only where its outer emit
  -- already did.
  Bare : ∀ {s} → Val (plainᵏ Γ κ) (emitᵗ s) → Set
  Bare {s} e′ = EmitRel {Γ = Γ} κ s e′ []

  data Carries {s} : List (Val (plainᵏ Γ κ) (emitᵗ s)) → List (Val Γ s) → Set where
    []    : Carries [] []
    quiet : ∀ (e′ : Val (plainᵏ Γ κ) (emitᵗ s)) {es′ vs} → Bare {s} e′ → Carries es′ vs → Carries (e′ ∷ es′) vs
    one   : ∀ (e′ : Val (plainᵏ Γ κ) (emitᵗ s)) {es′ w vs} → EmitRel κ s e′ (w ∷ []) → Carries es′ vs
          → Carries (e′ ∷ es′) (w ∷ vs)

  quiet-lift : ∀ {s u} {G′ : Val (plainᵏ Γ κ) (emitᵗ s) → Val (plainᵏ Γ κ) (emitᵗ u)} {f : Val Γ s → Val Γ u}
             → Lifts κ s u G′ (map f) → ∀ e′ → Bare {s} e′ → Bare {u} (G′ e′)
  quiet-lift L e′ r = proj₁ (L e′ [] r)

  one-lift : ∀ {s u} {G′ : Val (plainᵏ Γ κ) (emitᵗ s) → Val (plainᵏ Γ κ) (emitᵗ u)} {f : Val Γ s → Val Γ u}
           → Lifts κ s u G′ (map f) → ∀ e′ {w} → EmitRel κ s e′ (w ∷ []) → EmitRel κ u (G′ e′) (f w ∷ [])
  one-lift L e′ {w} r = proj₁ (L e′ (w ∷ []) r)

  carries-map : ∀ {s u} {G′ : Val (plainᵏ Γ κ) (emitᵗ s) → Val (plainᵏ Γ κ) (emitᵗ u)} {f : Val Γ s → Val Γ u}
              → Lifts κ s u G′ (map f) → ∀ {es vs} → Carries es vs → Carries (map G′ es) (map f vs)
  carries-map L []                      = []
  carries-map {G′ = G′} {f} L (quiet e′ r b) = quiet (G′ e′) (quiet-lift {G′ = G′} {f} L e′ r) (carries-map L b)
  carries-map {G′ = G′} {f} L (one e′ r b) = one (G′ e′) (one-lift {G′ = G′} {f} L e′ r) (carries-map L b)


  -- WHAT `elemᵛ` MAKES OF AN OUTER EMIT CARRYING ONE ELEMENT: an echo
  -- always, carrying the element's echoed value if it has one, beside
  -- the element's inner as the lane if it has one
  echoOf : ∀ {u} → Val Γ (unitᵗ +ᵗ u) → List (Val Γ u)
  echoOf (inj₁ _) = []
  echoOf (inj₂ v) = v ∷ []

  data LaneRel {u} : Val (plainᵏ Γ κ) (unitᵗ +ᵗ obs (emitᵗ u)) → Val Γ (unitᵗ +ᵗ obs u) → Set where
    no-lane : ∀ {a b} → LaneRel (inj₁ a) (inj₁ b)
    a-lane  : ∀ {o′ o} → ObsRel κ u o′ o → LaneRel (inj₂ o′) (inj₂ o)

  data Elem {u} : Val Γ (echoᵗ u) → Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)) → Set where
    elem : ∀ {w l x l′} → EmitRel κ u x (echoOf w) → LaneRel l′ l → Elem (w , l) (inj₂ x , l′)

  -- and of one carrying none: an echo carrying nothing, and no lane
  data QuietElem {u} : Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)) → Set where
    quiet-elem : ∀ {x a} → Bare {u} x → QuietElem (inj₂ x , inj₁ a)

  postulate
    elem-one   : ∀ {u Θ ρ} e′ {w} → EmitRel κ (echoᵗ u) e′ (w ∷ []) → Elem w (applyClo (Θ , elemᵛ , ρ) e′)
    elem-quiet : ∀ {u Θ ρ} e′ → Bare {echoᵗ u} e′ → QuietElem {u} (applyClo (Θ , elemᵛ , ρ) e′)

  -- THE VALUE A POPPED SOURCE HANDS ITS CHAINS, on both sides: the head
  -- of each partnered source's pending list, at the row's source
  data Head (src src′ : ℕ) : ∀ {u u′} → List (Val Γ u) → List (Val (plainᵏ Γ κ) u′) → Set where
    head : ∀ {l l′ a a′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′
         → Arrival.source a ≡ src → Arrival.source a′ ≡ src′
         → Head src src′ (arrVal a ∷ []) (arrVal a′ ∷ [])
    nohead : ∀ {u u′} → Head src src′ {u} {u′} [] []

  -- the related values at the root: the emits' payloads in order
  postulate
    root-values : ∀ {t es vs} → Carries {t} es vs → ∀ fin
      → Pointwise (λ x w → V κ t (proj₂ x) w)
          (readᴵ ((map valueᵖ es ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))
          (readᴾ ((map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    St : Sched Γ → EvalSt ep → Sched (plainᵏ Γ κ) → EvalSt ei → Set
    St = Store κ

    -- the chains not reached stay paired
    Keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁}
          → St sP stP sI stI → St sP₁ stP₁ sI₁ stI₁ → Set
    Keeps {stP = stP} {stI = stI} {stP₁ = stP₁} {stI₁ = stI₁} S S₁ =
      ∀ {x x′}
      → PairedR (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) x x′
      → PairedR (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) x x′

    -- the popped arrival's pair against the rows stays as it was
    Persists : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁}
             → St sP stP sI stI → St sP₁ stP₁ sI₁ stI₁ → Set
    Persists S S₁ = ∀ {s s′ u u′} → Arr S s s′ u u′ → Arr S₁ s s′ u u′

    -- WHAT A PASS KEEPS: related stores after, the unreached chains
    -- paired, the arrival's pair against the rows, related values sent
    -- rootward, and every node pairing it found
    record After {sP stP sI stI} (S : St sP stP sI stI)
                 (rP : Stream Γ t × Sched Γ × EvalSt ep)
                 (rI : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei) : Set where
      constructor after
      field
        store  : Store κ (proj₁ (proj₂ rP)) (proj₂ (proj₂ rP)) (proj₁ (proj₂ rI)) (proj₂ (proj₂ rI))
        keeps  : Keeps S store
        persists : Persists S store
        values : Pointwise (λ x w → V κ t (proj₂ x) w) (readᴵ (proj₁ rI)) (readᴾ (proj₁ rP))
        grows  : ∀ {x} → x ∈ Store.π S → x ∈ Store.π store

    -- one pass, then another from where it left the stores
    _⨾_ : ∀ {sP stP sI stI} {S : St sP stP sI stI} {o₁ sP₁ stP₁ i₁ sI₁ stI₁ rP rI}
        → (A : After S (o₁ , sP₁ , stP₁) (i₁ , sI₁ , stI₁)) → After (After.store A) rP rI
        → After S (o₁ ++ proj₁ rP , proj₂ rP) (i₁ ++ proj₁ rI , proj₂ rI)
    -- by projection, so that the two together leave the second's store
    _⨾_ {o₁ = o₁} {i₁ = i₁} {rP = rP} {rI = rI} A B =
      after (After.store B) (λ {a} {a′} x → After.keeps B {a} {a′} (After.keeps A {a} {a′} x))
        (λ ar → After.persists B (After.persists A ar))
        (subst₂ (Pointwise (λ x w → V κ t (proj₂ x) w)) (sym (readᴵ-++ i₁ (proj₁ rI))) (sym (readᴾ-++ o₁ (proj₁ rP)))
                (++⁺ (After.values A) (After.values B)))
        (λ x → After.grows B (After.grows A x))

    -- what a relation over the whole path reads: the node pairing and
    -- the two node tables a pass leaves
    Goal : Set₁
    Goal = List (NodeId × List NodeId) → List (NodeId × NodeState Γ) → List (NodeId × NodeState (plainᵏ Γ κ)) → Set

    -- WHAT AN ARM HANDS BACK: the pass so far, the rest of the impl
    -- fold standing on a sound tail related to the plain one's, and the whole
    -- related again once the tails have folded -- the arm's own frames
    -- being nodes a tail's fold does not write
    data Arm {sP stP sI stI} (S : St sP stP sI stI) (now : Tick) (oP : Stream Γ t) (sP₁ : Sched Γ) (stP₁ : EvalSt ep)
             {ℓ u} (p : Path Γ ℓ u t) (vs : List (Val Γ u)) (fin : Bool) (G : Goal)
           : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set where
      arm : ∀ {ℓ′} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {oI es sI₁ stI₁ rI}
          → (A : After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁))
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
          → Carries es vs
          → Sound q sI₁ stI₁
          → foldPath⇓ now q es fin sI₁ stI₁ rI
          → (∀ {rP} → foldPath⇓ now p vs fin sP₁ stP₁ rP → (B : After (After.store A) rP rI)
             → PathRel κ (Store.π (After.store B)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
             → G (Store.π (After.store B)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))))
          → Arm S now oP sP₁ stP₁ p vs fin G (oI ++ proj₁ rI , proj₂ rI)

    -- nothing asked of the whole
    none : Goal
    none _ _ _ = ⊤

    -- one pass, then another sending nothing more
    _⨾∅_ : ∀ {sP stP sI stI} {S : St sP stP sI stI} {o₁ i₁ sP₁ stP₁ sI₁ stI₁ sP₂ stP₂ sI₂ stI₂}
         → (A : After S (o₁ , sP₁ , stP₁) (i₁ , sI₁ , stI₁)) → After (After.store A) ([] , sP₂ , stP₂) ([] , sI₂ , stI₂)
         → After S (o₁ , sP₂ , stP₂) (i₁ , sI₂ , stI₂)
    A ⨾∅ B =
      after (After.store B) (λ {a} {a′} x → After.keeps B {a} {a′} (After.keeps A {a} {a′} x))
        (λ ar → After.persists B (After.persists A ar)) (After.values A) (λ x → After.grows B (After.grows A x))

    ----------------------------------------------------------------
    -- AN OUTER'S WALK
    ----------------------------------------------------------------

    -- the impl's tail below a flattener: the restamp's scan and projection
    Restamp : ∀ {ℓ₂ ℓ₃ ℓ₄ u} Θ₁ → Env (plainᵏ Γ κ) Θ₁ → NodeId → ∀ Θ₂ → Env (plainᵏ Γ κ) Θ₂ → ℓ₂ ≤ ℓ₃ → ℓ₃ ≤ ℓ₄
            → Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t) → Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)
    Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q =
      scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₃ ] (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)

    -- where the walk has got to: the flattener, and the tails it hands to
    Walked : ∀ {ℓ ℓ₄ u} → FlatOp → NodeId → NodeId → NodeId
           → Path Γ ℓ u t → Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t) → Goal
    Walked {u = u} op m m′ ks p q π NP NI = Flattener κ π {t = t} NP NI u op m m′ ks [] × PathRel κ π NP NI p q

    cur-grow : ∀ {π π′} → (∀ {x} → x ∈ π → x ∈ π′) → ∀ {cur cur′} → CurRel {Γ = Γ} κ π cur cur′ → CurRel {Γ = Γ} κ π′ cur cur′
    cur-grow g {nothing} {nothing} c = c
    cur-grow g {just _}  {just _}  c = g c

    nodes-grow : ∀ {π π′} → (∀ {x} → x ∈ π → x ∈ π′) → ∀ {u op x x′} → FlatNodes {Γ = Γ} κ π u op x x′ → FlatNodes {Γ = Γ} κ π′ u op x x′
    nodes-grow g (merge~ ps) = merge~ ps
    nodes-grow g (switch~ c) = switch~ (cur-grow g c)
    nodes-grow g exhaust~    = exhaust~

    -- a flattener stays one where its nodes do and the pairing grows
    flat-move : ∀ {π π′ u op m m′ ks} (NP : List (NodeId × NodeState Γ)) (NI : List (NodeId × NodeState (plainᵏ Γ κ)))
                  (NP′ : List (NodeId × NodeState Γ)) (NI′ : List (NodeId × NodeState (plainᵏ Γ κ)))
              → (∀ {x} → x ∈ π → x ∈ π′) → Unmoved m NP′ NP → Unmoved m′ NI′ NI → Unmoved ks NI′ NI
              → Flattener κ π {t = t} NP NI u op m m′ ks [] → Flattener κ π′ {t = t} NP′ NI′ u op m m′ ks []
    flat-move _ _ _ _ g (unmoved eP) (unmoved eI) (unmoved eK) (pm , x , x′ , lP , lI , fn , c , lk) =
      g pm , x , x′ , trans eP lP , trans eI lI , nodes-grow g fn , c , trans eK lk

    -- an echo through the restamp's scan, on the impl side alone: the
    -- flattener kept, and the group the scan hands its projection
    data Restamped {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u} (op : FlatOp) (m m′ ks : NodeId)
                   (p : Path Γ ℓ u t) (q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)) (ws : List (Val Γ u))
                   (es : List (Val (plainᵏ Γ κ) (emitᵗ u))) (fin : Bool)
                   (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      restamped : (A : After S ([] , sP , stP) (oI , sI₁ , stI₁))
                → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁)
                → Carries es ws → fin ≡ false
                → Restamped S op m m′ ks p q ws es fin oI sI₁ stI₁

    -- the outer's end on both sides, as far as the impl's tail
    data Wrapped {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ₄ u} (op : FlatOp) (m m′ ks : NodeId)
                 (p : Path Γ ℓ u t) (q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)) (fin : Bool) (now : Tick)
               : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set where
      wrapped : ∀ {sI₁ stI₁ r} (A : After S ([] , proj₂ (thruWrap (flatOp op) m fin (sP , stP))) ([] , sI₁ , stI₁))
              → Walked op m m′ ks p q (Store.π (After.store A))
                  (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP , stP))))) (EvalSt.nodes stI₁)
              → ClearI m′ ks q sI₁ stI₁
              → foldPath⇓ now q [] (proj₁ (thruWrap (flatOp op) m fin (sP , stP))) sI₁ stI₁ r
              → Wrapped S op m m′ ks p q fin now r

    postulate
      -- AN ECHO THROUGH THE RESTAMP: the scan's cell restamps it and
      -- keeps its payloads, and writes nothing but the cell, so the
      -- flattener and the tails stay related with the cell moved on; the
      -- group it hands on stays open
      flat-echo : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                    {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {xs ws o₁ fin₁ sI₁ stI₁}
                    {ys : List (Val (plainᵏ Γ κ) (FlatSᵗ u))}
                → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                → Carries xs ws
                → stepFrame⇓ now (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks) (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₄ ] q)
                    xs false sI stI (o₁ , ys , fin₁ , sI₁ , stI₁)
                → Restamped S op m m′ ks p q ws (map (applyClo {s = FlatSᵗ u} (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂)) ys) fin₁ o₁ sI₁ stI₁

      -- AN OUTER'S INNER HANDED THE FLATTENER ON BOTH SIDES, its lane on
      -- the impl's: the policy reads related nodes and decides alike
      consume-pair : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                       {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {o o′ rP rI}
                   → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                   → ObsRel κ u o′ o
                   → thruConsume⇓ (flatOp op) m p now o sP stP rP
                   → thruConsume⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now o′ sI stI rI
                   → Σ (After S rP rI) λ A
                       → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))

      -- THE OUTER'S END ON BOTH SIDES: a flattener completes once its
      -- outer has and no lane is open or queued, read off related nodes,
      -- so the two ends agree; the restamp passes the empty group on
      outer-wrap : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {fin r}
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) (proj₁ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                     (proj₂ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                 → foldPath⇓ now (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) []
                     (proj₁ (thruWrap (flatOp op) m′ fin (sI , stI)))
                     (proj₁ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI))))
                     (proj₂ (proj₂ (thruWrap (flatOp op) m′ fin (sI , stI)))) r
                 → Wrapped S op m m′ ks p q fin now r


    ----------------------------------------------------------------
    -- A VALUELESS GROUP, ON THE IMPL SIDE ALONE.  An outer's emit whose
    -- element echoes nothing is restamped and folded rootward by the
    -- impl, and the plain run has nothing to fold.  The impl's frames
    -- step on it one constructor at a time, the plain side still, and
    -- the descent is the impl's fold.
    ----------------------------------------------------------------

    -- a pass's impl output, regrouped as the fold lays it down
    after-out : ∀ {sP stP sI stI} {S : St sP stP sI stI} {rP o o′} {x : Sched (plainᵏ Γ κ) × EvalSt ei}
              → o ≡ o′ → After S rP (o , x) → After S rP (o′ , x)
    after-out {rP = rP} e A =
      after (After.store A) (After.keeps A) (After.persists A)
        (subst (λ o → Pointwise (λ x w → V κ t (proj₂ x) w) (readᴵ o) (readᴾ (proj₁ rP))) e (After.values A))
        (After.grows A)

    regroup₂ : (o₁ o₂ y : Stream (plainᵏ Γ κ) (emitᵗ t)) → (o₁ ++ o₂) ++ y ≡ o₁ ++ (o₂ ++ y)
    regroup₂ o₁ o₂ y = ++-assoc o₁ o₂ y

    regroup₃ : (o₁ o₂ o₃ y : Stream (plainᵏ Γ κ) (emitᵗ t)) → (o₁ ++ (o₂ ++ o₃)) ++ y ≡ o₁ ++ (o₂ ++ (o₃ ++ y))
    regroup₃ o₁ o₂ o₃ y = trans (++-assoc o₁ (o₂ ++ o₃) y) (cong (o₁ ++_) (++-assoc o₂ o₃ y))

    -- A VALUELESS GROUP KEEPS THE PASS WITH THE PLAIN SIDE STILL, and
    -- the two paths related where the impl's fold leaves them
    Quiet : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Quiet p q =
      ∀ {now es fin sP stP sI stI rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es [] → fin ≡ false
      → Sound q sI stI
      → foldPath⇓ now q es fin sI stI rI
      → Σ (After S ([] , sP , stP) rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    -- WHAT A QUIET ARM HANDS BACK: the impl's run for one constructor
    -- stepped, the plain side still, the group reaching the tail still
    -- valueless and open, and the whole related again once the tail has
    -- folded
    data QArm {sP stP sI stI} (S : St sP stP sI stI) (now : Tick) {ℓ u} (p : Path Γ ℓ u t) (G : Goal)
              {ℓ′} (q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)) (es : List (Val (plainᵏ Γ κ) (emitᵗ u))) (fin : Bool)
              (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      qarm : (A : After S ([] , sP , stP) (oI , sI₁ , stI₁))
           → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes stI₁) p q
           → Carries es [] → fin ≡ false
           → (∀ {rI} → foldPath⇓ now q es fin sI₁ stI₁ rI → (B : After (After.store A) ([] , sP , stP) rI)
              → PathRel κ (Store.π (After.store B)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
              → G (Store.π (After.store B)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI))))
           → QArm S now p G q es fin oI sI₁ stI₁

    -- ONE LEAF PER CONSTRUCTOR, OVER THE IMPL'S OWN STEPS.  Each is
    -- handed the steps of its constructor's run and not the tail's fold,
    -- which its caller keeps, so the descent stays on the impl's fold.
    postulate
      -- A SHARE'S SUBJECT FANS A VALUELESS GROUP OUT TO EVERY READER, and
      -- every reader's chain folds it on the impl side alone
      quiet-sink : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                 → Quiet (share-sink i h)
                     (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))

      -- A SCAN'S CELL STEPPED ON EMITS CARRYING NOTHING stays related to
      -- the plain cell, which the plain scan's empty step leaves alone
      quiet-scan : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ s u C k k′}
                     {F : FnClo Γ (u ×ᵗ s) u} {F′ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ u)}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₂ (emitᵗ u) (emitᵗ t)}
                     {es fin o₁ y₁ f₁ s₁ st₁}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q))
                 → Carries es [] → fin ≡ false
                 → stepFrame⇓ now (scan-f F′ k′) (map-f G ↠[ h₂ ] q) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                 → QArm S now p (λ π NP NI → PathRel κ π NP NI (scan-f F k ↠[ h ] p) (scan-f F′ k′ ↠[ h₁ ] (map-f G ↠[ h₂ ] q)))
                     q (map (applyClo G) y₁) f₁ o₁ s₁ st₁

      -- A COUNT'S CUT NEVER FIRES ON NOTHING: the cut's scan, its test,
      -- its projection and the one-lane merge all pass the group on open
      quiet-take : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ s C k k₁ k₂ m j w}
                     {F₁ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ s)}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ s) (emitᵗ t)}
                     {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂ o₄ y₄ f₄ s₄ st₄}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f nothing k ↠[ h ] p)
                     (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q))))
                 → Carries es [] → fin ≡ false
                 → stepFrame⇓ now (scan-f F₁ k₁) (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q)))
                     es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                 → stepFrame⇓ now (take-f w k₂) (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q)) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                 → stepFrame⇓ now (from-inner mergeAllᵒ m j) q (map (applyClo G) y₂) f₂ s₂ st₂ (o₄ , y₄ , f₄ , s₄ , st₄)
                 → QArm S now p (λ π NP NI → PathRel κ π NP NI (take-f nothing k ↠[ h ] p)
                       (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] (from-inner mergeAllᵒ m j ↠[ h₄ ] q)))))
                     q y₄ f₄ (o₁ ++ (o₂ ++ o₄)) s₄ st₄

      -- A TEST'S CUT NEVER FIRES ON NOTHING: no value to test
      quiet-takeWhile : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s C P k k₁ k₂ w}
                          {F₁ : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ s) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ s)}
                          {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                          {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                          {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂}
                      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p)
                          (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q)))
                      → Carries es [] → fin ≡ false
                      → stepFrame⇓ now (scan-f F₁ k₁) (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q)) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                      → stepFrame⇓ now (take-f w k₂) (map-f G ↠[ h₃ ] q) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                      → QArm S now p (λ π NP NI → PathRel κ π NP NI (take-f (just P) k ↠[ h ] p)
                            (scan-f F₁ k₁ ↠[ h₁ ] (take-f w k₂ ↠[ h₂ ] (map-f G ↠[ h₃ ] q))))
                          q (map (applyClo G) y₂) f₂ (o₁ ++ o₂) s₂ st₂

      -- AN EXPLODED OUTER'S EMIT CARRYING NOTHING explodes into no
      -- inner, and its echo is restamped on the impl side alone
      quiet-explode : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                        {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                    → Quiet (thru-outer (flatOp op) m ↠[ h ] p)
                        (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                         (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                          (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                           (thru-outer (flatOp op) m′ ↠[ h₄ ]
                            (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                             (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q))))))

      -- AN INNER'S EMITS CARRYING NOTHING leave its lane as they came,
      -- the flattener's node unwritten, and are restamped
      quiet-inner : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u C op m m′ j j′ k}
                      {F : FnClo (plainᵏ Γ κ) (C ×ᵗ emitᵗ u) C} {G : FnClo (plainᵏ Γ κ) C (emitᵗ u)}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                      {es fin o₁ y₁ f₁ s₁ st₁ o₂ y₂ f₂ s₂ st₂}
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner (flatOp op) m j ↠[ h ] p)
                      (from-inner (flatOp op) m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q)))
                  → Carries es [] → fin ≡ false
                  → stepFrame⇓ now (from-inner (flatOp op) m′ j′) (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q)) es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                  → stepFrame⇓ now (scan-f F k) (map-f G ↠[ h₃ ] q) y₁ f₁ s₁ st₁ (o₂ , y₂ , f₂ , s₂ , st₂)
                  → QArm S now p (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p)
                        (from-inner (flatOp op) m′ j′ ↠[ h₁ ] (scan-f F k ↠[ h₂ ] (map-f G ↠[ h₃ ] q))))
                      q (map (applyClo G) y₂) f₂ (o₁ ++ o₂) s₂ st₂

      -- THE IMPL-ONLY MERGE IN FRONT OF A LANE passes emits carrying
      -- nothing on as they came
      quiet-lane : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ′ u op m j mL jL}
                     {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                     {es fin o₁ y₁ f₁ s₁ st₁}
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner (flatOp op) m j ↠[ h ] p)
                     (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
                 → Carries es [] → fin ≡ false
                 → stepFrame⇓ now (from-inner mergeAllᵒ mL jL) Q es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                 → QArm S now (from-inner (flatOp op) m j ↠[ h ] p)
                     (λ π NP NI → PathRel κ π NP NI (from-inner (flatOp op) m j ↠[ h ] p) (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q))
                     Q y₁ f₁ o₁ s₁ st₁

      -- A DEFERRED BODY'S EMITS CARRYING NOTHING pass the hop's marker
      -- merge, its restamp and the hop's node as they came
      quiet-deferInner : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2}
                           {G : FnClo (plainᵏ Γ κ) (emitᵗ u) (emitᵗ u)}
                           {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                           {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                           {es fin o₁ y₁ f₁ s₁ st₁ o₃ y₃ f₃ s₃ st₃}
                       → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner mergeAllᵒ nid j ↠[ h ] p)
                           (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))
                       → Carries es [] → fin ≡ false
                       → stepFrame⇓ now (from-inner mergeAllᵒ m2 j2) (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))
                           es fin sI stI (o₁ , y₁ , f₁ , s₁ , st₁)
                       → stepFrame⇓ now (from-inner mergeAllᵒ nid′ j′) q (map (applyClo G) y₁) f₁ s₁ st₁ (o₃ , y₃ , f₃ , s₃ , st₃)
                       → QArm S now p (λ π NP NI → PathRel κ π NP NI (from-inner mergeAllᵒ nid j ↠[ h ] p)
                             (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ] (map-f G ↠[ h₂ ] (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q))))
                           q y₃ f₃ (o₁ ++ o₃) s₃ st₃

    mutual
      quiet-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Quiet p q
      quiet-pass S root~ b refl _ fold-root = after S (λ x → x) (λ x → x) (root-values b false) (λ x → x) , root~
      quiet-pass S r@(sink~ sh) b e si dI = quiet-sink sh S r b e si dI
      quiet-pass S (map~ L r) b e si (fold-step step-map dI) =
        let X = quiet-pass S r (carries-map L b) e (drop-ot _ _ _ si) dI in proj₁ X , map~ L (proj₂ X)
      quiet-pass S r@(scan~ _ _ _ _ _ _) b e si (fold-step d₁ (fold-step step-map dq)) =
        quiet-resume (quiet-scan S r b e d₁) (drop-ot _ _ _ (adv d₁ si)) dq
      quiet-pass S r@(take~ _ _ _ _ _ _ _ _ _) b e si
                 (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map (fold-step {out₁ = o₄} d₄ dq)))) =
        let X = quiet-resume (quiet-take S r b e d₁ d₂ d₄) (adv d₄ (drop-ot _ _ _ (adv d₂ (adv d₁ si)))) dq
        in after-out (regroup₃ o₁ o₂ o₄ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(takeWhile~ _ _ _ _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-takeWhile S r b e d₁ d₂) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S (outerElem~ fl r) b e si dI = quiet-outer S (fl , r) b e si dI
      quiet-pass S r@(outerExplode~ _ _) b e si dI = quiet-explode S r b e si dI
      quiet-pass S r@(inner~ _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step {out₁ = o₂} d₂ (fold-step step-map dq))) =
        let X = quiet-resume (quiet-inner S r b e d₁ d₂) (drop-ot _ _ _ (adv d₂ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₂ _) (proj₁ X) , proj₂ X
      quiet-pass S r@(lane~ _ _) b e si (fold-step d₁ dq) = quiet-resume (quiet-lane S r b e d₁) (adv d₁ si) dq
      quiet-pass S r@(deferInner~ _ _ _ _ _ _ _) b e si (fold-step {out₁ = o₁} d₁ (fold-step step-map (fold-step {out₁ = o₃} d₃ dq))) =
        let X = quiet-resume (quiet-deferInner S r b e d₁ d₃) (adv d₃ (drop-ot _ _ _ (adv d₁ si))) dq
        in after-out (regroup₂ o₁ o₃ _) (proj₁ X) , proj₂ X

      quiet-resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ′ u} {p : Path Γ ℓ u t} {G : Goal}
                       {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {es fin oI sI₁ stI₁ rI}
                   → QArm S now p G q es fin oI sI₁ stI₁ → Sound q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ rI
                   → Σ (After S ([] , sP , stP) (oI ++ proj₁ rI , proj₂ rI)) λ A
                       → G (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-resume (qarm A r b e rb) si dq = let X = quiet-pass (After.store A) r b e si dq in A ⨾ proj₁ X , rb dq (proj₁ X) (proj₂ X)

      -- AN OUTER'S EMITS CARRYING NOTHING, HANDED THE FLATTENER: every
      -- element a bare echo, restamped, then the open end restamped too
      quiet-outer : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin rI}
                  → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) → Carries es [] → fin ≡ false
                  → Sound (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) sI stI
                  → foldPath⇓ now (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
                      es fin sI stI rI
                  → Σ (After S ([] , sP , stP) rI) λ A
                      → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
                          (thru-outer (flatOp op) m ↠[ h ] p)
                          (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
      quiet-outer S {op = op} {Θ₀ = Θ₀} {ρ₀} w b refl si
                  (fold-step step-map (fold-step dW@(step-thru-outer W) (fold-step d₁ (fold-step step-map dq)))) =
        let si′ = drop-ot _ _ _ si
            X  = quiet-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru si′) w b W
            c₁ = step-clear d₁ (unthru (step-kept _ dW si′))
            T  = quiet-tail (flat-echo (After.store (proj₁ X)) (proj₂ X) [] d₁) (tail-of c₁) dq
        in proj₁ X ⨾ proj₁ T , outerElem~ (proj₁ (proj₂ T)) (proj₂ (proj₂ T))

      -- THE OUTER'S WALK, every element a bare echo
      quiet-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es rI}
                 → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → Carries {echoᵗ u} es []
                 → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                     (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                 → Σ (After S ([] , sP , stP) rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-walk S cI w [] walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , w
      quiet-walk S {Θ₀ = Θ₀} {ρ₀} cI w (quiet e′ bq b) W = quiet-elem-step S cI w (elem-quiet {Θ = Θ₀} {ρ₀} e′ bq) b W

      quiet-elem-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                          {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {z es rI}
                      → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                      → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                      → QuietElem {u} z → Carries {echoᵗ u} es []
                      → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                          (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                      → Σ (After S ([] , sP , stP) rI) λ A
                          → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-elem-step S cI w (quiet-elem bx) b (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ bx []) d₁) (tail-of c₁) dq
            X  = quiet-walk (After.store (proj₁ E)) (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W′
        in proj₁ E ⨾ proj₁ X , proj₂ X

      -- a bare echo, restamped: down the impl's tail alone
      quiet-tail : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₄ u op m m′ ks}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es fin oI sI₁ stI₁ r}
                 → Restamped S op m m′ ks p q [] es fin oI sI₁ stI₁ → ClearI m′ ks q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ r
                 → Σ (After S ([] , sP , stP) (oI ++ proj₁ r , proj₂ r)) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ r)))
      quiet-tail {stP = stP} {stI₁ = stI₁} {r = r} (restamped A (fl , rel) c e) cI dq =
        let X  = quiet-pass (After.store A) rel c e (proj₂ (proj₁ cI)) dq
            F  = flat-move (EvalSt.nodes stP) (EvalSt.nodes stI₁) (EvalSt.nodes stP) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows (proj₁ X)) (unmoved refl) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in A ⨾ proj₁ X , F , proj₂ X

    -- THE OUTER'S END, AS THE ARM ITS TAIL RESUMES: the flattener's
    -- nodes are below the tail, so its fold leaves them where they were
    wrap-arm : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                 {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                 {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {oP sP′ stP′ oI sI′ stI′ fin r}
             → (A : After S (oP , sP′ , stP′) (oI , sI′ , stI′))
             → Clear m p (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′)))) (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
             → Wrapped (After.store A) op m m′ ks p q fin now r
             → Arm S now oP (proj₁ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                 (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))
                 p [] (proj₁ (thruWrap (flatOp op) m fin (sP′ , stP′)))
                 (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                    (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)))
                 (oI ++ proj₁ r , proj₂ r)
    wrap-arm {op = op} {m = m} {sP′ = sP′} {stP′ = stP′} {fin = fin} {r = r} A cP (wrapped {stI₁ = stI₁} A′ (fl , rel) cI dq) =
      arm (A ⨾∅ A′) rel [] (proj₂ (proj₁ cI)) dq λ {rP} dP B rel′ →
        let F  = flat-move (EvalSt.nodes (proj₂ (proj₂ (thruWrap (flatOp op) m fin (sP′ , stP′))))) (EvalSt.nodes stI₁)
                   (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows B) (missed dP cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in outerElem~ F rel′

    -- TWO RELATED PATHS KEEP THE PASS, AND ARE RELATED AGAIN WHERE IT
    -- LEAVES THEM: a flattener's outer folds its tail once per emit
    Pass : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Pass p q =
      ∀ {now vs es fin sP stP sI stI rP rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es vs
      → Sound p sP stP → Sound q sI stI
      → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now q es fin sI stI rI
      → Σ (After S rP rI) λ A
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q

    -- one plain frame and the impl run its constructor pairs it with
    Steps : ∀ {lo lo′ ℓ s u} → Frame Γ s u → lo ≤ ℓ → Path Γ ℓ u t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Steps f h p Q =
      ∀ {now vs es fin sP stP sI stI oP vs₁ fin₁ sP₁ stP₁ rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (f ↠[ h ] p) Q → Carries es vs
      → Sound (f ↠[ h ] p) sP stP → Sound Q sI stI
      → stepFrame⇓ now f p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
      → foldPath⇓ now Q es fin sI stI rI
      → Arm S now oP sP₁ stP₁ p vs₁ fin₁ (λ π NP NI → PathRel κ π NP NI (f ↠[ h ] p) Q) rI

    -- ONE LEAF PER PLAIN FRAME A CONSTRUCTOR STARTS WITH.  A count and a
    -- test are one frame apart in what they cut on; an outer's two
    -- constructors and an inner's three are split once their arm is the
    -- riskiest.
    postulate
      -- a share's subject, fanning the group out to every reader
      sink-pass     : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                    → Pass (share-sink i h)
                           (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))
      scan-arm      : ∀ {lo lo′ ℓ s u} {F : FnClo Γ (u ×ᵗ s) u} {k} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (scan-f F k) h p Q
      take-arm      : ∀ {lo lo′ ℓ s} {k} {h : lo ≤ ℓ} {p : Path Γ ℓ s t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (take-f nothing k) h p Q
      takeWhile-arm : ∀ {lo lo′ ℓ s} {P k} {h : lo ≤ ℓ} {p : Path Γ ℓ s t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (take-f (just P) k) h p Q
      -- an outer's elements, each inner a sync outer hands the flattener
      -- subscribed before the step returns: the explode and its merge
      outerExplode-arm : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u op m m′ ks mX Θ₀ ρ₀ Θ₅ ρ₅ Θ₁ ρ₁ Θ₂ ρ₂}
                           {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                           {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                           {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                       → Steps (thru-outer (flatOp op) m) h p
                           (map-f (Θ₀ , explodeᵛ , ρ₀) ↠[ h₁ ]
                            (map-f (Θ₅ , pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl))) , ρ₅) ↠[ h₂ ]
                             (thru-outer mergeAllᵒ mX ↠[ h₃ ]
                              (thru-outer (flatOp op) m′ ↠[ h₄ ]
                               (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₅ ]
                                (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₆ ] q))))))
      -- leaving an inner: the flattener's lane, then its restamp
      inner-arm     : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u op m m′ ks j j′ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                    → Steps (from-inner (flatOp op) m j) h p
                        (from-inner (flatOp op) m′ j′ ↠[ h₁ ]
                         (scan-f (Θ₁ , flatStepᵛ , ρ₁) ks ↠[ h₂ ]
                          (map-f (Θ₂ , sndᵗ (varᵗ (here refl)) , ρ₂) ↠[ h₃ ] q)))
      -- an inner led with its echo: one more merge, impl only, in front of its lane
      lane-arm      : ∀ {lo lo′ ℓ ℓ′ u op m j mL jL} {h : lo ≤ ℓ} {h′ : lo′ ≤ ℓ′}
                        {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                    → Steps (from-inner (flatOp op) m j) h p (from-inner mergeAllᵒ mL jL ↠[ h′ ] Q)
      -- a deferred body: the hop's marker merge, its restamp, the hop's node
      deferInner-arm : ∀ {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ u nid nid′ j j′ m2 j2 Θx ρ₀}
                         {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                         {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ u) (emitᵗ t)}
                     → Steps (from-inner mergeAllᵒ nid j) h p
                         (from-inner mergeAllᵒ m2 j2 ↠[ h₁ ]
                          (map-f (uniqᵗ ∷ Θx , restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)) , ρ₀) ↠[ h₂ ]
                           (from-inner mergeAllᵒ nid′ j′ ↠[ h₃ ] q)))

    mutual
      path-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Pass p q
      path-pass S root~ b _ _ (fold-root {fin = fin}) fold-root = after S (λ x → x) (λ x → x) (root-values b fin) (λ x → x) , root~
      path-pass S r@(sink~ sh) b sp si dP dI = sink-pass sh S r b sp si dP dI
      path-pass S (map~ L r) b sp si (fold-step step-map dP) (fold-step step-map dI) =
        let X = path-pass S r (carries-map L b) (drop-ot _ _ _ sp) (drop-ot _ _ _ si) dP dI in proj₁ X , map~ L (proj₂ X)
      path-pass S r@(scan~ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (scan-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(take~ _ _ _ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (take-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(takeWhile~ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (takeWhile-arm S r b sp si d dI) (adv d sp) dP
      path-pass S (outerElem~ fl r) b sp si (fold-step d dP) dI = resume (outerElem-arm S (fl , r) b sp si d dI) (adv d sp) dP
      path-pass S r@(outerExplode~ _ _) b sp si (fold-step d dP) dI = resume (outerExplode-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(inner~ _ _ _) b sp si (fold-step d dP) dI = resume (inner-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(lane~ _ _) b sp si (fold-step d dP) dI = resume (lane-arm S r b sp si d dI) (adv d sp) dP
      path-pass S r@(deferInner~ _ _ _ _ _ _ _) b sp si (fold-step d dP) dI = resume (deferInner-arm S r b sp si d dI) (adv d sp) dP

      resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now oP sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin G rP rI}
             → Arm S now oP sP₁ stP₁ p vs fin G rI → Sound p sP₁ stP₁ → foldPath⇓ now p vs fin sP₁ stP₁ rP
             → Σ (After S (oP ++ proj₁ rP , proj₂ rP) rI) λ A
                 → G (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      resume (arm A r b si dI rb) sp dP = let X = path-pass (After.store A) r b sp si dP dI in A ⨾ proj₁ X , rb dP (proj₁ X) (proj₂ X)

      -- AN OUTER'S ELEMENT, ONE PER EMIT, HANDED THE FLATTENER: the
      -- walk, then the outer's end, then the tail resumed on the empty
      -- group.  Handed the flattener and the tails apart, since the frame's
      -- relation does not invert at a variable policy.
      outerElem-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                        {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                        {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
                        {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                    → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) → Carries es vs
                    → Sound (thru-outer (flatOp op) m ↠[ h ] p) sP stP
                    → Sound (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q)) sI stI
                    → stepFrame⇓ now (thru-outer (flatOp op) m) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                    → foldPath⇓ now (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))
                        es fin sI stI rI
                    → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                        (λ π NP NI → PathRel κ π NP NI (thru-outer (flatOp op) m ↠[ h ] p)
                           (map-f (Θ₀ , elemᵛ , ρ₀) ↠[ h₁ ] (thru-outer (flatOp op) m′ ↠[ h₂ ] Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q))) rI
      outerElem-arm S {op = op} {Θ₀ = Θ₀} {ρ₀} {fin = fin} w b sp si dW@(step-thru-outer W) (fold-step step-map (fold-step dW′@(step-thru-outer W′) dR)) =
        let si′ = drop-ot _ _ _ si
            X   = elem-walk S {op = op} {Θ₀ = Θ₀} {ρ₀} (unthru sp) (unthru si′) w b W W′
        in wrap-arm (proj₁ X) (unthru (step-kept _ dW sp))
             (outer-wrap (After.store (proj₁ X)) {op = op} {fin = fin} (proj₂ X) (unthru (step-kept _ dW′ si′)) dR)

      -- THE OUTER'S WALK, an element at a time
      elem-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                    {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {es vs rP rI}
                → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                → Carries {echoᵗ u} es vs
                → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                    (thruEvents (map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                → Σ (After S rP rI) λ A
                    → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      elem-walk S cP cI w [] walk-nil walk-nil = after S (λ x → x) (λ x → x) [] (λ x → x) , w
      elem-walk S {Θ₀ = Θ₀} {ρ₀} cP cI w (quiet e′ bq b) W W′ = quiet-step S cP cI w (elem-quiet {Θ = Θ₀} {ρ₀} e′ bq) b W W′
      elem-walk S {Θ₀ = Θ₀} {ρ₀} cP cI w (one e′ r b) W W′ = one-step S cP cI w (elem-one {Θ = Θ₀} {ρ₀} e′ r) b W W′

      -- an emit with no element: its bare echo, on the impl side alone
      quiet-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                     {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {z es vs rP rI}
                 → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
                 → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
                 → QuietElem {u} z → Carries {echoᵗ u} es vs
                 → thruWalk⇓ (flatOp op) m p now (thruEvents vs) sP stP rP
                 → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                     (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
                 → Σ (After S rP rI) λ A
                     → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      quiet-step S cP cI w (quiet-elem bx) b W (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ bx []) d₁) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X

      -- an emit with one element: its echo, then its lane
      one-step : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ₂ ℓ₃ ℓ₄ u op m m′ ks Θ₀ ρ₀ Θ₁ ρ₁ Θ₂ ρ₂}
                   {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {w z es vs rP rI}
               → Clear m p sP stP → Clear m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) sI stI
               → Walked op m m′ ks p q (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI)
               → Elem {u} w z → Carries {echoᵗ u} es vs
               → thruWalk⇓ (flatOp op) m p now (thruEvents (w ∷ vs)) sP stP rP
               → thruWalk⇓ (flatOp op) m′ (Restamp Θ₁ ρ₁ ks Θ₂ ρ₂ h₃ h₄ q) now
                   (thruEvents (z ∷ map (applyClo (Θ₀ , elemᵛ , ρ₀)) es)) sI stI rI
               → Σ (After S rP rI) λ A
                   → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI)))
      one-step S cP cI w (elem {w = inj₁ _} r no-lane) b W (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) cP (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step S cP cI w (elem {w = inj₁ _} r (a-lane ob)) b (walk-cons c W) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) =
        let c₁ = step-clear d₁ cI
            E  = quiet-tail (flat-echo S w (quiet _ r []) d₁) (tail-of c₁) dq
            c₂ = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C  = consume-pair (After.store (proj₁ E)) (proj₂ E) ob c c′
            X  = elem-walk (After.store (proj₁ C)) (consume-clear c cP)
                   (consume-clear c′ c₂) (proj₂ C) b W W′
        in proj₁ E ⨾ (proj₁ C ⨾ proj₁ X) , proj₂ X
      one-step S cP cI w (elem {w = inj₂ _} r no-lane) b (walk-echo dv W) (walk-echo (fold-step d₁ (fold-step step-map dq)) W′) =
        let c₁ = step-clear d₁ cI
            E  = echo-go dv cP (flat-echo S w (one _ r []) d₁) (tail-of c₁) dq
            X  = elem-walk (After.store (proj₁ E)) (fold-clear dv (proj₂ cP) refl cP)
                   (fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁) (proj₂ E) b W W′
        in proj₁ E ⨾ proj₁ X , proj₂ X
      one-step S cP cI w (elem {w = inj₂ _} r (a-lane ob)) b (walk-echo dv (walk-cons c W)) (walk-echo (fold-step d₁ (fold-step step-map dq)) (walk-cons c′ W′)) =
        let c₁  = step-clear d₁ cI
            E   = echo-go dv cP (flat-echo S w (one _ r []) d₁) (tail-of c₁) dq
            cP₂ = fold-clear dv (proj₂ cP) refl cP
            c₂  = fold-clear dq (proj₂ (proj₁ (tail-of c₁))) refl c₁
            C   = consume-pair (After.store (proj₁ E)) (proj₂ E) ob c c′
            X   = elem-walk (After.store (proj₁ C)) (consume-clear c cP₂)
                    (consume-clear c′ c₂) (proj₂ C) b W W′
        in proj₁ E ⨾ (proj₁ C ⨾ proj₁ X) , proj₂ X

      -- a valued echo, restamped: down both tails
      echo-go : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now ℓ ℓ₄ u op m m′ ks}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)} {v rP es fin oI sI₁ stI₁ r}
              → foldPath⇓ now p (v ∷ []) false sP stP rP → Clear m p sP stP
              → Restamped S op m m′ ks p q (v ∷ []) es fin oI sI₁ stI₁ → ClearI m′ ks q sI₁ stI₁ → foldPath⇓ now q es fin sI₁ stI₁ r
              → Σ (After S rP (oI ++ proj₁ r , proj₂ r)) λ A
                  → Walked op m m′ ks p q (Store.π (After.store A)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
      echo-go {stP = stP} {rP = rP} {stI₁ = stI₁} {r = r} dv cP (restamped A (fl , rel) c refl) cI dq =
        let X  = path-pass (After.store A) rel c (proj₂ cP) (proj₂ (proj₁ cI)) dv dq
            F  = flat-move (EvalSt.nodes stP) (EvalSt.nodes stI₁) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ r)))
                   (After.grows (proj₁ X)) (missed dv cP) (missed dq (proj₁ cI)) (missed dq (proj₂ cI , proj₂ (proj₁ cI))) fl
        in A ⨾ proj₁ X , F , proj₂ X

    -- THE TWO ROWS A MINTED SOURCE'S CHAINS CAN BE.  A cold read's impl
    -- chain runs its input block before the path its partner runs; a
    -- deferred hop's subscribes the body on both sides.
    postulate
      block-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
                → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ s (plainᵗ s)
                → ∀ {lo′ ℓ ℓ′} {p : Path Γ ℓ s t} {full : Path (plainᵏ Γ κ) lo′ (plainᵗ s) (emitᵗ t)}
                    {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ s) (emitᵗ t)}
                → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) full q
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → Sound full sI stI
                → ∀ {now fin rI} → foldPath⇓ now full vs′ fin sI stI rI
                → Arm S now [] sP stP p vs fin none rI
      hop-arm   : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u} {vs : List (Val Γ (echoᵗ u))} {vs′ : List (Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)))}
                → Head src src′ {echoᵗ u} {echoᵗ (emitᵗ u)} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′ (echoᵗ u) (echoᵗ (emitᵗ u))
                → ∀ {nid nid′} → (nid , nid′ ∷ []) ∈ Store.π S
                → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing 0 [] false)
                → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
                → ∀ {ℓ ℓ′ lo′} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → Sound (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q) sI stI
                → ∀ {now fin oP vs₁ fin₁ sP₁ stP₁ rI}
                → stepFrame⇓ now (thru-outer mergeAllᵒ nid) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                → foldPath⇓ now (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q) vs′ fin sI stI rI
                → Arm S now oP sP₁ stP₁ p vs₁ fin₁ none rI

    -- A SLOT'S READER: the impl runs the restamp where the plain path runs
    -- on, so the arm is the one frame the impl moves alone
    postulate
      read-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {Θ₀ ρ₀ ℓ′}
                   {X : Tm (plainᵏ Γ κ) [] [] (emitᵗ (lookup Γ i) ∷ Θ₀) uniqᵗ} {h : suc (toℕ (n ↑ʳ i)) ≤ ℓ′}
                   {p : Path Γ (suc (toℕ i)) (lookup Γ i) t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ (lookup Γ i)) (emitᵗ t)}
                 → lookup κ i ≡ hotᵏ ⊎ lookup κ i ≡ sharedᵏ
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                 → ∀ {now vs es fin rI} → Carries es vs
                 → Sound (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) sI stI
                 → foldPath⇓ now (map-f (Θ₀ , restampᵛ X subscribeᵛ (varᵗ (here refl)) , ρ₀) ↠[ h ] q) es fin sI stI rI
                 → Arm S now [] sP stP p vs fin none rI

    -- the emits of a stamped slot against the plain values, at types the
    -- share's own is only propositionally the emit of
    CarriesU : ∀ {u u′} → u′ ≡ emitᵗ u → List (Val (plainᵏ Γ κ) u′) → List (Val Γ u) → Set
    CarriesU refl = Carries

    -- a slot's partnered reader, by the row the store pairs it with
    slot-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {u u′ rid rid′}
                  {p : Path Γ (suc (toℕ i)) u t} {p′ : Path (plainᵏ Γ κ) (suc (toℕ (n ↑ʳ i))) u′ (emitᵗ t)}
                  {vs es} (εI : u′ ≡ emitᵗ u)
              → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                  (rid , atSlot i , (u , p)) (rid′ , atSlot (n ↑ʳ i) , (u′ , p′))
              → CarriesU εI es vs
              → Sound p sP stP → Sound p′ sI stI
              → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ es fin sI stI rI
              → After S rP rI
    slot-pass S refl (read~ hk r refl) c sp si dP dI = proj₁ (resume (read-arm S hk r c si dI) sp dP)

    -- a partnered pair stays partnered once the store moves
    slot-keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {u}
                   {c : RegId × AtFloor Γ u t} {d}
               → Keeps S S₁
               → SlotPair (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i c d
               → SlotPair (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i c d
    slot-keeps K (slotpair x) = slotpair (K x)

    -- the same pass, started from the store as it stood before the row was marked
    rebase : ∀ {sP stP sI stI x y rP rI} {S : St sP stP sI stI}
           → After (delivered S {x} {y}) rP rI → After S rP rI
    rebase (after s k q v g) = after s k (λ ar → q (delivered-arr ar)) v g

    -- A SHARE'S FAN-OUT AGAINST THE PLAIN CASCADE OVER THE SAME READERS,
    -- one reader at a time: the plain chain and the admitted row it is
    -- partnered with, a cut one on both sides skipped
    fan-go : ∀ {sP stP sI stI} (S : St sP stP sI stI) {i : Fin n} {a : Arrival Γ}
               (εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)) {es now vs fin}
           → CarriesU εI es vs → arrTick a ≡ now
           → ∀ {chs adm}
           → Pointwise (SlotPair (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) chs adm
           → (∀ {x} → x ∈ chs → Sound (proj₂ (proj₂ x)) sP stP)
           → (∀ {x y} → x ∈ chs → y ∈ chs → Agree (proj₂ (proj₂ x)) (proj₂ (proj₂ y)))
           → (∀ {x} → x ∈ adm → Sound (proj₂ x) sI stI)
           → (∀ {x y} → x ∈ adm → y ∈ adm → Agree (proj₂ x) (proj₂ y))
           → ∀ {oP sP₁ stP₁ oI sI₁ stI₁}
           → cascadeGo⇓ a vs fin chs sP stP (oP , sP₁ , stP₁)
           → shareGo⇓ now (n ↑ʳ i) es fin adm sI stI (oI , sI₁ , stI₁)
           → After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁)
    fan-go S εI c ta [] _ _ _ _ casc-nil go-nil = after S (λ x → x) (λ x → x) [] (λ x → x)
    fan-go S εI c ta (slotpair (inj₁ _) ∷ ps) hP aP hI aI (casc-cut _ g) (go-cut _ g′) =
      fan-go S εI c ta ps (λ m → hP (there m)) (λ m m′ → aP (there m) (there m′)) (λ m → hI (there m)) (λ m m′ → aI (there m) (there m′)) g g′
    fan-go S εI c ta (slotpair (inj₁ (x , _)) ∷ _) _ _ _ _ (casc-live y _ _) _ = ⊥-elim (clash (trans (sym x) y))
    fan-go S εI c ta (slotpair (inj₁ (_ , x)) ∷ _) _ _ _ _ (casc-cut _ _) (go-live y _ _) = ⊥-elim (clash (trans (sym x) y))
    fan-go S εI c ta (slotpair (inj₂ (x , _)) ∷ _) _ _ _ _ (casc-cut y _) _ = ⊥-elim (clash (trans (sym y) x))
    fan-go S εI c ta (slotpair (inj₂ (_ , x , _)) ∷ _) _ _ _ _ (casc-live _ _ _) (go-cut y _) = ⊥-elim (clash (trans (sym y) x))
    fan-go S εI c refl (slotpair (inj₂ (_ , _ , pr)) ∷ ps) hP aP hI aI (casc-live _ dP g) (go-live _ dI g′) =
      rebase (A ⨾ fan-go (After.store A) εI c refl (map-slot {S₀ = S} {S₁ = After.store A} (After.keeps A) ps)
                (λ m → fold-kept (unchain dP) sP₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hP (there m))) (aP (here refl) (there m)))
                (λ m m′ → aP (there m) (there m′))
                (λ m → fold-kept dI sI₀ _ (sub-ot (λ r∈ → r∈) ≤-refl (hI (there m))) (aI (here refl) (there m)))
                (λ m m′ → aI (there m) (there m′)) g g′)
      where
        sP₀ = sub-ot (λ r∈ → r∈) ≤-refl (hP (here refl))
        sI₀ = sub-ot (λ r∈ → r∈) ≤-refl (hI (here refl))
        A = slot-pass (delivered S) εI (partner-row κ _ _ _ _ _ (Store.rows S) pr) c sP₀ sI₀ (unchain dP) dI

        map-slot : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁} {S₀ : St sP stP sI stI} {S₁ : St sP₁ stP₁ sI₁ stI₁} {i : Fin n} {u}
                     {cs : List (RegId × AtFloor Γ u t)} {ds}
                 → Keeps S₀ S₁
                 → Pointwise (SlotPair (Store.rows S₀) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i) cs ds
                 → Pointwise (SlotPair (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) i) cs ds
        map-slot K []       = []
        map-slot {S₀ = S₀} {S₁ = S₁} K (r ∷ rs) = slot-keeps {S = S₀} {S₁ = S₁} K r ∷ map-slot {S₀ = S₀} {S₁ = S₁} K rs

    -- WHAT A HOT ARRIVAL'S IMPL CHAIN DOES BEFORE THE SHARE: its input block
    -- runs alone, the plain side not moving, and hands the share the one emit
    -- that carries the arrival's value
    data HotStart {sP stP sI stI} (S : St sP stP sI stI) (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) (i : Fin n)
                  (oI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₁ : Sched (plainᵏ Γ κ)) (stI₁ : EvalSt ei) : Set where
      hot-start-at : ∀ {oB sI₂ stI₂ e lo rD} {below : lo ≤ toℕ (n ↑ʳ i)}
                       {εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)} {ty : arrTy a ≡ lookup Γ i}
                   → (A : After S ([] , sP , stP) (oB , sI₂ , stI₂))
                   → CarriesU εI (e ∷ []) (arrVal a ∷ [])
                   → dispatchShare⇓ (arrTick a′) (n ↑ʳ i) below (e ∷ []) false sI₂ stI₂ rD
                   → (oI , sI₁ , stI₁) ≡ (oB ++ proj₁ rD , proj₂ rD)
                   → HotStart S a a′ i oI sI₁ stI₁
      -- or no reader on either side, and the impl not moving
      hot-idle : chainsOf a stP ≡ [] → (oI , sI₁ , stI₁) ≡ ([] , sI , stI)
               → HotStart S a a′ i oI sI₁ stI₁

    -- WHAT A HOT ARRIVAL'S IMPL CHAIN DOES AT THE END: the same block runs
    -- alone, the share is spent, and the end it hands the share is
    -- dispatched.  The plain side has latched the slot and the impl the share,
    -- which is where the latches meet again
    data HotEnd {sP stP sI stI} (S : St sP stP sI stI) (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) (i : Fin n)
                (eI : Stream (plainᵏ Γ κ) (emitᵗ t)) (sI₃ : Sched (plainᵏ Γ κ)) (stI₃ : EvalSt ei) : Set where
      hot-end-at : ∀ {oB sI₂ stI₂ lo rD} {below : lo ≤ toℕ (n ↑ʳ i)}
                     {εI : lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ emitᵗ (arrTy a)} {ty : arrTy a ≡ lookup Γ i}
                 → (A : After S ([] , sP , cascadeClose a stP)
                              (oB , sI₂ , shareSpend (n ↑ʳ i) (shareDying (n ↑ʳ i) true stI₂)))
                 → CarriesU εI [] []
                 → dispatchShare⇓ (arrTick a′) (n ↑ʳ i) below [] true sI₂ stI₂ rD
                 → (eI , sI₃ , stI₃) ≡ (oB ++ proj₁ rD , proj₂ rD)
                 → HotEnd S a a′ i eI sI₃ stI₃
      -- or no row at the raw slot or the share, no plain reader, and the
      -- impl only latching the raw slot; a share that connected is spent
      hot-end-idle : chainsOf a stP ≡ []
                   → srcCount (toℕ (i ↑ˡ n)) (EvalSt.registry stI) ≡ 0 → srcCount (toℕ (n ↑ʳ i)) (EvalSt.registry stI) ≡ 0
                   → (memberSource (toℕ (n ↑ʳ i)) (EvalSt.connectedShares stI) ≡ true
                      → memberSource (toℕ (i ↑ˡ n)) (EvalSt.completedSources stI) ≡ true)
                   → (eI , sI₃ , stI₃) ≡ ([] , sI , cascadeClose a′ stI)
                   → HotEnd S a a′ i eI sI₃ stI₃

    postulate
      -- THE IMPL'S ONE CHAIN AT A HOT ARRIVAL'S RAW SLOT, ONCE ITS SHARE HAS
      -- CONNECTED: the raw row's step over the arrival's value, its input
      -- block run alone into the share.  What it owes is the block's run:
      -- the one stamped emit carrying the value, the plain side not moving
      hot-block : ∀ {sP stP sI stI} (S : St sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
                → (hot : lookup κ i ≡ hotᵏ)
                → Head (toℕ i) (toℕ (i ↑ˡ n)) {arrTy a} {arrTy a′} (arrVal a ∷ []) (arrVal a′ ∷ [])
                → arrTy a ≡ lookup Γ i
                → ∀ {rid q ℓ full} {h : ℓ ≤ toℕ (n ↑ʳ i)}
                → _≡_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (arrTy a′ , q)) (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full))
                → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ (lookup Γ i)) full
                    (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
                → ∀ {oI sI₁ stI₁}
                → chainStep⇓ a′ (arrVal a′ ∷ []) false (suc (toℕ (i ↑ˡ n)) , q) sI
                    (record stI { delivered = rid ∷ EvalSt.delivered stI }) (oI , sI₁ , stI₁)
                → HotStart S a a′ i oI sI₁ stI₁

    -- a minted source's partnered chain, by the row the store pairs it with
    row-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u u′} {vs : List (Val Γ u)} {vs′ : List (Val (plainᵏ Γ κ) u′)}
             → Head src src′ {u} {u′} vs vs′
             → ∀ {rid rid′ lo lo′} {p : Path Γ lo u t} {p′ : Path (plainᵏ Γ κ) lo′ u′ (emitᵗ t)}
             → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                 (rid , atDyn src lo , (u , p)) (rid′ , atDyn src′ lo′ , (u′ , p′))
             → Sound p sP stP → Sound p′ sI stI
             → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ vs′ fin sI stI rI
             → After S rP rI
    row-pass S hd (cold~ sp blk r refl) soP soI dP dI = proj₁ (resume (block-arm S hd sp blk r soI dI) soP dP)
    row-pass S hd (defer~ sp k nP nI r refl) soP soI (fold-step d dP) dI = proj₁ (resume (hop-arm S hd sp k nP nI r soI d dI) (adv d soP) dP)
