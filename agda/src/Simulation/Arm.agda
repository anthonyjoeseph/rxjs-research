-- THE VOCABULARY A CASCADE'S PASS IS STATED IN: what a group of emits
-- carries, and what one path constructor's arm hands back.  Below the
-- pass so each arm's body can live in a module of its own.
module Simulation.Arm where

open import Data.Bool    using (Bool; false; true)
open import Data.Empty   using (⊥)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.Bool.ListAction using (any)
open import Data.Nat     using (ℕ; _≤_; zero; suc)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim      using (Tick; EmitKind; subscribe; delivery; plumbing)
open import Rx.Exp       using (Ctx; Closed; Val; obs; uniqᵗ; FnClo; boolᵗ; _×ᵗ_; _≟ᵗ_)
open import Rx.Mint      using (counter; sourceᵏ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState; Path; Frame; _↠[_]_; thru-outer; thruWrap; mergeAllᵒ; lookupNode; AllOp; from-inner; aliveThroughᶠ;
  root; share-sink; map-f; scan-f; take-f; batchSync-f; frameNodes; skipᵇ; regSource; scanDispatch; takeDispatch; cell-st; take-st; mergeAll-st; switch-st; exhaust-st; batchSync-st)
open import Rx.Evaluator.Domain using (foldPath⇓; stepFrame⇓; thruConsume⇓; thruWalk⇓; fold-root; fold-sink; fold-step; step-map; step-scan; step-take;
  step-batchSync; step-from-inner; step-thru-outer; react-false; walk-nil; disp)
open import Rx.Evaluator.Reducible.Support using (Sound; NodeOn; node-on; drop-ot; head-on; self-node; push-thru; endOf; ∨-Tʳ)
open import Rx.Evaluator.Reducible.Rule-Kept using (Thru; RuleKept; step-kept; fold-kept; stepFrame-rule; thruConsume-rule)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.InstEmit using (instEmitᵗ)
open import Simulation.Stores using (EmitRel; Lifts; PathRel; Store; stampOf; sharedEq; root~; sink~; map~; scan~; takeWhile~; spentWhile~;
  outerElem~; outerExplode~; inner~; deferInner~; LiveFor)
open import Simulation.After using (module Kept; readᴵ; readᴵ-++)

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
  -- fold on standing ground; this owes it of every derivation.  A
  -- share the fold connects has no reader but the one the connect
  -- registers, which is the rule's `linked`.
  --
  -- TWIN: `foldPath-rule` -- the same induction, a clause per
  --   constructor, there keeping the rule where this keeps the node.
  fold-unmoved : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {κ : Path Γ lo s t} {k now vals fin sched st r}
               → foldPath⇓ {e = e} now κ vals fin sched st r → Clear k κ sched st
               → lookupNode k (EvalSt.nodes (proj₂ (proj₂ r))) ≡ lookupNode k (EvalSt.nodes st)

-- A TAIL HANDED NOTHING, AND NO END, SENDS NOTHING and runs no clock back
QuietTail : ∀ {m} {Δ : Ctx m} {t} (e : Closed Δ (instEmitᵗ uniqᵗ t)) {ℓ u} → Path Δ ℓ u (instEmitᵗ uniqᵗ t) → Set
QuietTail e q = ∀ {now sched st o sched′ st′} → foldPath⇓ {e = e} now q [] false sched st (o , sched′ , st′)
              → readᴵ o ≡ [] × counter (Sched.mint sched) sourceᵏ ≤ counter (Sched.mint sched′) sourceᵏ

-- A PATH WITH NO BRACKET ON IT.  A lowered bracket flushes its buffer
-- on the first fold through it, whatever it is handed, so it is the one
-- frame a fold handed nothing can make speak.
--
-- REFUTED: `Refuted.Quiet-Fold-Batch`, read with
--   `git show c2e60cb8:agda/evidence/refuted/Refuted/Quiet-Fold-Batch.agda`
--   -- quiet over every path, a
--   lowered bracket holding a value sends it.
NoBatch : ∀ {m} {Δ : Ctx m} {lo s u} → Path Δ lo s u → Set
NoBatch root                        = ⊤
NoBatch (share-sink _ _)            = ⊤
NoBatch (batchSync-f _ ↠[ _ ] _)    = ⊥
NoBatch (map-f _ ↠[ _ ] p)          = NoBatch p
NoBatch (scan-f _ _ ↠[ _ ] p)       = NoBatch p
NoBatch (take-f _ _ ↠[ _ ] p)       = NoBatch p
NoBatch (from-inner _ _ _ ↠[ _ ] p) = NoBatch p
NoBatch (thru-outer _ _ ↠[ _ ] p)   = NoBatch p

unbatched-subst : ∀ {m} {Δ : Ctx m} {lo s s′ u} (eq : s ≡ s′) {p : Path Δ lo s u}
                → NoBatch p → NoBatch (subst (λ w → Path Δ lo w u) eq p)
unbatched-subst refl b = b

-- the elaboration installs a bracket only in a read's input block, and
-- a block is a row's, never a related path's
rel-unbatched : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {π t NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
              → PathRel κ π {t} NP NI p q → NoBatch q
rel-unbatched root~                          = tt
rel-unbatched {Γ = Γ} {κ = κ} (sink~ {i = i} sh) = unbatched-subst (sharedEq {Γ = Γ} κ i sh) tt
rel-unbatched (map~ _ r)                     = rel-unbatched r
rel-unbatched (scan~ _ _ _ _ _ r)            = rel-unbatched r
rel-unbatched (takeWhile~ _ _ _ _ _ r)       = rel-unbatched r
rel-unbatched (spentWhile~ _ _ _ r)          = rel-unbatched r
rel-unbatched (outerElem~ _ r)               = rel-unbatched r
rel-unbatched (outerExplode~ _ _ r)          = rel-unbatched r
rel-unbatched (inner~ _ _ _ r)               = rel-unbatched r
rel-unbatched (deferInner~ _ _ _ _ _ _ _ r)  = rel-unbatched r

-- the numbers naming a node frame: an inner's lane names its inner too
frameKey : ∀ {m} {Δ : Ctx m} {s u} → Frame Δ s u → List ℕ
frameKey (from-inner _ k j) = 1 ∷ k ∷ j ∷ []
frameKey (thru-outer _ k)   = 2 ∷ k ∷ []
frameKey f                  = 3 ∷ frameNodes f

-- the first node frame a path reaches
headKey : ∀ {m} {Δ : Ctx m} {lo s u} → Path Δ lo s u → List ℕ
headKey (map-f _ ↠[ _ ] q) = headKey q
headKey (f ↠[ _ ] q)       = frameKey f
headKey _                  = []

Passes : ∀ {m} {Δ : Ctx m} {lo s u} → List ℕ → Path Δ lo s u → Set
Passes key (f ↠[ _ ] q) = frameKey f ≡ key ⊎ Passes key q
Passes key _            = ⊥

-- no row a dispatch would walk passes the path's first node frame
Clean : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} → Path Δ lo s t → EvalSt e → Set
Clean q st = ∀ {r} → r ∈ EvalSt.registry st → skipᵇ (regSource (proj₁ (proj₂ r))) (proj₁ r) st ≡ false
           → ¬ Passes (headKey q) (proj₂ (proj₂ (proj₂ r)))

-- a path came down a node frame: a flattener's by its outer or by any
-- of its inner lanes
Through : ∀ {m} {Δ : Ctx m} {lo s u s′ u′} → Frame Δ s u → Path Δ lo s′ u′ → Set
Through (from-inner _ k _) p = Passes (2 ∷ k ∷ []) p ⊎ Σ ℕ λ j → Passes (1 ∷ k ∷ j ∷ []) p
Through (thru-outer _ k)   p = Passes (2 ∷ k ∷ []) p ⊎ Σ ℕ λ j → Passes (1 ∷ k ∷ j ∷ []) p
Through f                  p = Passes (frameKey f) p

-- EVERY ROW BELOW A NODE FRAME CAME DOWN IT: a row a dispatch would walk
-- through the first node frame past one reached it through that one.
-- A frame an end left can say nothing of a row that joined below it,
-- so this is what an end's absence is handed on by.
Fed : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} → Path Δ lo s t → EvalSt e → Set
Fed (map-f _ ↠[ _ ] q) st = Fed q st
Fed (f ↠[ _ ] q)       st = (∀ {r} → r ∈ EvalSt.registry st → skipᵇ (regSource (proj₁ (proj₂ r))) (proj₁ r) st ≡ false
                             → Passes (headKey q) (proj₂ (proj₂ (proj₂ r))) → Through f (proj₂ (proj₂ (proj₂ r))))
                           × Fed q st
Fed _                  st = ⊤

-- AN END THE WALK CARRIES HAS LEFT NOTHING AT THE FRAME IT REACHES, and
-- every row below came down the path.  What a flattener's outer needs to
-- end with every row still walking its outer live.
--
-- WITHOUT `Fed` NO STEP HANDS IT ON: a frame's absence says nothing of
-- the tail's first node, false at a frame whose node no row passes
-- above a tail an alive row walks.
Gone : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} → Path Δ lo s t → EvalSt e → Set
Gone q st = Clean q st × Fed q st

-- neither reads a node, so a table rewritten under them keeps both
fed-nodes : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} (q : Path Δ lo s t) {st : EvalSt e} {N}
          → Fed q st → Fed q (record st { nodes = N })
fed-nodes (map-f _ ↠[ _ ] q) fd        = fed-nodes q fd
fed-nodes (scan-f _ _ ↠[ _ ] q)      (fd , fq) = fd , fed-nodes q fq
fed-nodes (take-f _ _ ↠[ _ ] q)      (fd , fq) = fd , fed-nodes q fq
fed-nodes (batchSync-f _ ↠[ _ ] q)   (fd , fq) = fd , fed-nodes q fq
fed-nodes (from-inner _ _ _ ↠[ _ ] q) (fd , fq) = fd , fed-nodes q fq
fed-nodes (thru-outer _ _ ↠[ _ ] q)  (fd , fq) = fd , fed-nodes q fq
fed-nodes root               _         = tt
fed-nodes (share-sink _ _)   _         = tt

gone-nodes : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} {q : Path Δ lo s t} {st : EvalSt e} {N}
           → Gone q st → Gone q (record st { nodes = N })
gone-nodes {q = q} (c , fd) = c , fed-nodes q fd

-- a frame whose step writes its own cell and nothing else a row reads
data Cell {m} {Δ : Ctx m} : ∀ {s u} → Frame Δ s u → Set where
  scan-c : ∀ {s u} {F : FnClo Δ (u ×ᵗ s) u} {k} → Cell (scan-f F k)
  take-c : ∀ {s} {w : Maybe (FnClo Δ s boolᵗ)} {k} → Cell (take-f w k)

-- a frame's dispatch handed nothing, and no end, hands on nothing
Hushed : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {u} → Sched Δ → List (Val Δ u) × Bool × Sched Δ × EvalSt e → Set
Hushed sched r = proj₁ r ≡ [] × proj₁ (proj₂ r) ≡ false × proj₁ (proj₂ (proj₂ r)) ≡ sched

scan-hush : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s u} (fn : FnClo Δ (u ×ᵗ s) u) nid sched (st : EvalSt e) x
          → Hushed sched (scanDispatch fn nid [] false sched st x)
scan-hush {u = u} fn nid sched st (just (cell-st {w} a)) with w ≟ᵗ u
... | no  _    = refl , refl , refl
... | yes refl = refl , refl , refl
scan-hush fn nid sched st nothing                         = refl , refl , refl
scan-hush fn nid sched st (just (take-st _))              = refl , refl , refl
scan-hush fn nid sched st (just (mergeAll-st _ _ _ _))    = refl , refl , refl
scan-hush fn nid sched st (just (switch-st _ _))          = refl , refl , refl
scan-hush fn nid sched st (just (exhaust-st _ _))         = refl , refl , refl
scan-hush fn nid sched st (just (batchSync-st _ _ _))     = refl , refl , refl

take-hush : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s} (w : Maybe (FnClo Δ s boolᵗ)) nid sched (st : EvalSt e) x
          → Hushed sched (takeDispatch w nid [] false sched st x)
take-hush w nid sched st (just (take-st zero))            = refl , refl , refl
take-hush w nid sched st (just (take-st (suc _)))         = refl , refl , refl
take-hush w nid sched st nothing                          = refl , refl , refl
take-hush w nid sched st (just (cell-st _))               = refl , refl , refl
take-hush w nid sched st (just (mergeAll-st _ _ _ _))     = refl , refl , refl
take-hush w nid sched st (just (switch-st _ _))           = refl , refl , refl
take-hush w nid sched st (just (exhaust-st _ _))          = refl , refl , refl
take-hush w nid sched st (just (batchSync-st _ _ _))      = refl , refl , refl

-- one frame off a bracket-free path, handed nothing and no end
step-quiet : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo ℓ s u} {f : Frame Δ s u} {le : lo ≤ ℓ} {q : Path Δ ℓ u t} {now sched st r}
           → NoBatch (f ↠[ le ] q) → stepFrame⇓ {e = e} now f q [] false sched st r
           → proj₁ r ≡ [] × proj₁ (proj₂ r) ≡ [] × proj₁ (proj₂ (proj₂ r)) ≡ false
             × proj₁ (proj₂ (proj₂ (proj₂ r))) ≡ sched × NoBatch q
step-quiet b step-map = refl , refl , refl , refl , b
step-quiet b (step-scan {fn = fn} {nid = nid} {sched = sched} {st = st}) =
  refl , proj₁ h , proj₁ (proj₂ h) , proj₂ (proj₂ h) , b
  where h = scan-hush fn nid sched st (lookupNode nid (EvalSt.nodes st))
step-quiet b (step-take {w = w} {nid = nid} {sched = sched} {st = st}) =
  refl , proj₁ h , proj₁ (proj₂ h) , proj₂ (proj₂ h) , b
  where h = take-hush w nid sched st (lookupNode nid (EvalSt.nodes st))
step-quiet () step-batchSync
step-quiet b (step-from-inner react-false) = refl , refl , refl , refl , b
step-quiet b (step-thru-outer walk-nil)    = refl , refl , refl , refl , b

-- ANY BRACKET-FREE TAIL IS QUIET HANDED NOTHING.
quiet-fold : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ (instEmitᵗ uniqᵗ t)} {ℓ u} {q : Path Δ ℓ u (instEmitᵗ uniqᵗ t)}
           → NoBatch q → QuietTail e q
quiet-fold _ fold-root                   = refl , ≤-refl
quiet-fold _ (fold-sink (disp walk-nil)) = refl , ≤-refl
quiet-fold b (fold-step s d) with step-quiet b s
... | refl , refl , refl , refl , b′ = quiet-fold b′ d

-- WHAT A RUN SENDS AT ONE INSTANT: every value it puts out read at `I`
Out : ∀ {m} {Δ : Ctx m} {t} → ℕ → Stream Δ (instEmitᵗ uniqᵗ t) → Set
Out I o = All (λ y → proj₁ y ≡ I) (readᴵ o)

out-++ : ∀ {m} {Δ : Ctx m} {t} {I} (xs ys : Stream Δ (instEmitᵗ uniqᵗ t)) → Out I xs → Out I ys → Out I (xs ++ ys)
out-++ {I = I} xs ys a b = subst (All (λ y → proj₁ y ≡ I)) (sym (readᴵ-++ xs ys)) (++⁺ᵃ a b)

-- a tail read at `I`, once whatever else it might be is ruled out
out-tail : ∀ {m} {Δ : Ctx m} {t} {I} {o : Stream Δ (instEmitᵗ uniqᵗ t)} {D : Set} → Out I o ⊎ D → (D → Out I o) → Out I o
out-tail (inj₁ x) _ = x
out-tail (inj₂ d) f = f d

-- a quiet run is at every instant
out-quiet : ∀ {m} {Δ : Ctx m} {t} {I} (o : Stream Δ (instEmitᵗ uniqᵗ t)) → readᴵ o ≡ [] → Out I o
out-quiet {I = I} o e = subst (All (λ y → proj₁ y ≡ I)) (sym e) []

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

  -- AN EMIT DELIVERED AT `I`: any kind but a subscribe's, which the
  -- frame it lands at restamps
  Del : ℕ → ℕ × EmitKind → Set
  Del I (_ , subscribe) = ⊥
  Del I (i , delivery)  = i ≡ I
  Del I (i , plumbing)  = i ≡ I

  DelAt : ∀ {s} → ℕ → Val (plainᵏ Γ κ) (emitᵗ s) → Set
  DelAt {s} I e′ = Del I (stampOf {Γ = Γ} κ {s} e′)

  -- A GROUP ALL DELIVERED AT `I` AND NOT THE END: what a pass reads its
  -- output's instant off
  Dlv : ∀ {s} → ℕ → Bool → List (Val (plainᵏ Γ κ) (emitᵗ s)) → Set
  Dlv I fin es = fin ≡ false × All (DelAt I) es

  -- no instant asked of an arm whose tail ends
  Never : ℕ → Set
  Never _ = ⊥

  -- a stamp kept is a delivery kept
  del-keep : ∀ {s u} {I} (x : Val (plainᵏ Γ κ) (emitᵗ u)) (y : Val (plainᵏ Γ κ) (emitᵗ s))
           → stampOf {Γ = Γ} κ {u} x ≡ stampOf {Γ = Γ} κ {s} y → DelAt I y → DelAt I x
  del-keep {I = I} _ _ eq d = subst (Del I) (sym eq) d

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
    --
    -- AN END IT HANDS THE TAIL HAS LEFT NOTHING at the tail's first node
    -- frame
    --
    -- AND, AT EVERY INSTANT `H` NAMES, the arm's own output read there and
    -- either the tail's or the group it hands the tail delivered there
    data Arm {sP stP sI stI} (S : St sP stP sI stI) (now : Tick) (oP : Stream Γ t) (sP₁ : Sched Γ) (stP₁ : EvalSt ep)
             {ℓ u} (p : Path Γ ℓ u t) (vs : List (Val Γ u)) (fin : Bool) (G : Goal) (H : ℕ → Set)
           : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set where
      arm : ∀ {ℓ′} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {oI es sI₁ stI₁ rI}
          → (A : After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁))
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
          → Carries es vs
          → Sound q sI₁ stI₁
          → (fin ≡ true → Gone q stI₁)
          → LiveFor es q (EvalSt.nodes stI₁)
          → foldPath⇓ now q es fin sI₁ stI₁ rI
          → (∀ {rP} → foldPath⇓ now p vs fin sP₁ stP₁ rP → (B : After (After.store A) rP rI)
             → PathRel κ (Store.π (After.store B)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))) p q
             → G (Store.π (After.store B)) (EvalSt.nodes (proj₂ (proj₂ rP))) (EvalSt.nodes (proj₂ (proj₂ rI))))
          → (∀ {I} → H I → Out I oI × (Out I (proj₁ rI) ⊎ Dlv I fin es))
          → Arm S now oP sP₁ stP₁ p vs fin G H (oI ++ proj₁ rI , proj₂ rI)

    -- an arm read at fewer instants
    arm-weaken : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now oP sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin G H H′ r}
               → (∀ {I} → H′ I → H I) → Arm S now oP sP₁ stP₁ p vs fin G H r → Arm S now oP sP₁ stP₁ p vs fin G H′ r
    arm-weaken w (arm A r b si g lv dI rb o) = arm A r b si g lv dI rb (λ h → o (w h))

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

    -- A CELL'S FRAME HANDS AN END'S GONE ON: every row past the cell came
    -- down it, and none is left there.  A cell writes no registry, so the
    -- tail's state reads as the frame's.
    gone-cell : ∀ {sP stP sI stI} (S : St sP stP sI stI) {ℓ ℓ′ s u} {f : Frame (plainᵏ Γ κ) s u} {h : ℓ ≤ ℓ′}
                  {q : Path (plainᵏ Γ κ) ℓ′ u (emitᵗ t)}
              → Cell f → Gone (f ↠[ h ] q) stI → Gone q stI
    gone-cell _ scan-c (c , fd , fq) = (λ r∈ sk ps → c r∈ sk (fd r∈ sk ps)) , fq
    gone-cell _ take-c (c , fd , fq) = (λ r∈ sk ps → c r∈ sk (fd r∈ sk ps)) , fq

    postulate
      -- AN IDLE FLATTENER HAS NO ROW DOWN AN INNER LANE: its counters
      -- cover its alive inners, so a merge with none active or queued, a
      -- switch with no current inner and an exhaust not active have none.
      -- The harness's `accounts` decides the counters' half at a boundary;
      -- no `Store` field carries it.
      idle-lanes : ∀ {sP stP sI stI} (S : St sP stP sI stI) {o k}
                 → proj₁ (thruWrap o k true (sI , stI)) ≡ true
                 → ∀ {r j} → r ∈ EvalSt.registry stI → skipᵇ (regSource (proj₁ (proj₂ r))) (proj₁ r) stI ≡ false
                 → ¬ Passes (1 ∷ k ∷ j ∷ []) (proj₂ (proj₂ (proj₂ r)))
      -- AN OUTER'S WALK LEAVES ITS GONE AS IT FOUND IT: every row the walk
      -- registers comes through an inner it subscribes, never through the
      -- outer, and a row it cuts or ends is skipped from then on
      gone-walk : ∀ {sP stP sI stI} (S : St sP stP sI stI) {o k ℓ ℓ′ u now evs r} {h : ℓ ≤ ℓ′}
                    {q : Path (plainᵏ Γ κ) ℓ′ u (emitᵗ t)}
                → thruWalk⇓ o k q now evs sI stI r
                → Gone (thru-outer o k ↠[ h ] q) stI → Gone (thru-outer o k ↠[ h ] q) (proj₂ (proj₂ r))

    -- AN OUTER'S END THAT LEAVES ITS FLATTENER IDLE HANDS ITS GONE ON: a
    -- row past the flattener came down its outer, which the end left, or
    -- down a lane, and an idle flattener has none.  The write marks the
    -- outer done and touches no registry, so it is read where it starts.
    gone-wrap : ∀ {sP stP sI stI} (S : St sP stP sI stI) {o k ℓ ℓ′ u} {h : ℓ ≤ ℓ′}
                  {q : Path (plainᵏ Γ κ) ℓ′ u (emitᵗ t)}
              → Gone (thru-outer o k ↠[ h ] q) stI → proj₁ (thruWrap o k true (sI , stI)) ≡ true → Gone q stI
    gone-wrap S {o} {k} (c , fd , fq) w =
      (λ r∈ sk ps → [ c r∈ sk , (λ (_ , p) → idle-lanes S {o} {k} w r∈ sk p) ] (fd r∈ sk ps)) , fq

    -- one plain frame and the impl run its constructor pairs it with
    Steps : ∀ {lo lo′ ℓ s u} → Frame Γ s u → lo ≤ ℓ → Path Γ ℓ u t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Steps f h p Q =
      ∀ {now vs es fin sP stP sI stI oP vs₁ fin₁ sP₁ stP₁ rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (f ↠[ h ] p) Q → Carries es vs
      → Sound (f ↠[ h ] p) sP stP → Sound Q sI stI → (fin ≡ true → Gone Q stI) → LiveFor es Q (EvalSt.nodes stI)
      → stepFrame⇓ now f p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
      → foldPath⇓ now Q es fin sI stI rI
      → Arm S now oP sP₁ stP₁ p vs₁ fin₁ (λ π NP NI → PathRel κ π NP NI (f ↠[ h ] p) Q) (λ I → Dlv I fin es) rI

    -- AN INNER'S STEP THAT LEAVES IT OPEN: the group passed on as it came
    InnerPasses : ∀ {lo lo′ ℓ u} → AllOp → NodeId → NodeId → lo ≤ ℓ → Path Γ ℓ u t → Path (plainᵏ Γ κ) lo′ (emitᵗ u) (emitᵗ t) → Set
    InnerPasses a m j h p Q =
      ∀ {now vs es fin sP stP sI stI rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (from-inner a m j ↠[ h ] p) Q → Carries es vs
      → Sound (from-inner a m j ↠[ h ] p) sP stP → Sound Q sI stI → LiveFor es Q (EvalSt.nodes stI)
      → fin ≡ false ⊎ any (aliveThroughᶠ j stP) (EvalSt.registry stP) ≡ true
      → foldPath⇓ now Q es fin sI stI rI
      → Arm S now [] sP stP p vs false (λ π NP NI → PathRel κ π NP NI (from-inner a m j ↠[ h ] p) Q) (λ I → Dlv I fin es) rI
