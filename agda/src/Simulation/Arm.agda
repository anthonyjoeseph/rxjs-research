-- THE VOCABULARY A CASCADE'S PASS IS STATED IN: what a group of emits
-- carries, and what one path constructor's arm hands back.  Below the
-- pass so each arm's body can live in a module of its own.
module Simulation.Arm where

open import Data.Bool    using (Bool)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Nat     using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Tick)
open import Rx.Exp       using (Ctx; Closed; Val; obs)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState; Path; Frame; _↠[_]_; thru-outer; mergeAllᵒ; lookupNode)
open import Rx.Evaluator.Domain using (foldPath⇓; stepFrame⇓; thruConsume⇓)
open import Rx.Evaluator.Reducible.Support using (Sound; NodeOn; node-on; drop-ot; head-on; self-node; push-thru; endOf; ∨-Tʳ)
open import Rx.Evaluator.Reducible.Rule-Kept using (Thru; RuleKept; step-kept; fold-kept; stepFrame-rule; thruConsume-rule)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Stores using (EmitRel; Lifts; PathRel; Store)
open import Simulation.After using (module Kept)

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

module Arms {n} {Γ : Ctx n} (κ : Kinds n) where

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

  module Run {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open Kept {Γ = Γ} κ {t} {ep} {ei}

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

    -- one plain frame and the impl run its constructor pairs it with
    Steps : ∀ {lo lo′ ℓ s u} → Frame Γ s u → lo ≤ ℓ → Path Γ ℓ u t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Steps f h p Q =
      ∀ {now vs es fin sP stP sI stI oP vs₁ fin₁ sP₁ stP₁ rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (f ↠[ h ] p) Q → Carries es vs
      → Sound (f ↠[ h ] p) sP stP → Sound Q sI stI
      → stepFrame⇓ now f p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
      → foldPath⇓ now Q es fin sI stI rI
      → Arm S now oP sP₁ stP₁ p vs₁ fin₁ (λ π NP NI → PathRel κ π NP NI (f ↠[ h ] p) Q) rI
