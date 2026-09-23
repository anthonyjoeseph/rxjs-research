-- WHAT A WRITE AT A FRESH IDENTIFIER LEAVES ALONE.  A frame's
-- continuation stands on the store holding what it closed over, and a
-- write to another identifier is the one thing a step may do to the
-- table without moving it.  The bound is a FLOOR taken as an argument
-- rather than read off the mint, so the fact is one family and the
-- counter's monotonicity is re-established separately, where a premise
-- ran at an advanced mint.
--
-- DEAD ROUTE: proving preservation over the SUBSCRIBE RELATION -- "a
--   subscription never writes below the counter it began at".  The
--   connect makes it false: a frame over a share registers the caller's
--   own continuation and folds the definition's synchronous values back
--   down it, so the caller's own node is written at an identifier
--   minted before the subscription began.  Preservation is carried by
--   each ANSWER instead (`Rx.Evaluator.Reducible`'s ground), and the
--   connect answers that the room fell.
-- RECOVERY: git show 33078215:agda/src/Rx/Evaluator/Freshness.agda
--   holds `lookup-set`, `FrameAbove`, `pres-same` and `pres-trans`,
--   which the frame arms spend; the two relation-level families beside
--   it are the dead route above.
module Rx.Evaluator.Freshness where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool.ListAction using (any)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Decide using (≡ᵇ→≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Mint using (nodeᵏ; freshId)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; lookupNode; setNode;
  Path; root; share-sink; _↠[_]_; frameNodes; pathHasNode; RegRow; RegSrc; atSlot; atDyn)

-- where the node counter sits, named once
nodeCt : ∀ {n} {Γ : Ctx n} → Sched Γ → ℕ
nodeCt sched = freshId nodeᵏ (Sched.mint sched)

-- EVERY NODE STRICTLY BELOW THE FLOOR READS BACK EXACTLY AS IT DID.  A
-- record rather than the function it wraps, because both states appear
-- in that type only under a projection, and a transparent alias would
-- leave every composition asking Agda to invert `EvalSt.nodes`.
record PreservedBelow {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                      (f : ℕ) (st st′ : EvalSt e) : Set where
  constructor pres
  field below : ∀ k → k < f
              → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st)

open PreservedBelow public using (below)

-- every node other than the written one reads back as it did.  The
-- table is an association list, so the two clauses are the two ways a
-- write can miss: past the end, where the write lands as a fresh head
-- the reader walks past, and at a row whose key is the written one,
-- where the reader's own test already answered.
set-above : ∀ {n} {Γ : Ctx n} (nid k : NodeId) (ns : NodeState Γ)
              (ts : List (NodeId × NodeState Γ))
          → (nid ≡ᵇ k) ≡ false
          → lookupNode k (setNode nid ns ts) ≡ lookupNode k ts
set-above nid k ns []            ne rewrite ne = refl
set-above nid k ns ((j , s) ∷ r) ne with j ≡ᵇ nid in eq
... | true  rewrite ≡ᵇ→≡ j nid eq | ne = refl
... | false with j ≡ᵇ k
...   | true  = refl
...   | false = set-above nid k ns r ne

-- a key below a bound is not that bound
<→≢ᵇ : ∀ {k m} → k < m → (m ≡ᵇ k) ≡ false
<→≢ᵇ {zero}  {suc m} _       = refl
<→≢ᵇ {suc k} {suc m} (s≤s p) = <→≢ᵇ p

-- a write at or above the floor preserves everything below it.  Stated
-- over an equation on the table rather than the states, because a step
-- that leaves the table alone rarely leaves the state alone.
pres-write : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f nid}
               (st st′ : EvalSt e) (ns : NodeState Γ)
             → EvalSt.nodes st′ ≡ setNode nid ns (EvalSt.nodes st)
             → f ≤ nid
             → PreservedBelow f st st′
pres-write {nid = nid} st st′ ns eq f≤nid =
  pres λ k k<f → trans (cong (lookupNode k) eq)
                       (set-above nid k ns (EvalSt.nodes st)
                         (<→≢ᵇ (≤-trans k<f f≤nid)))

-- THE SINK A PATH ENDS IN, if it ends in one rather than at the root.
sinkOf : ∀ {n} {Γ : Ctx n} {lo u t} → Path Γ lo u t → Maybe (Fin n)
sinkOf root             = nothing
sinkOf (share-sink i _) = just i
sinkOf (_ ↠[ _ ] κ)     = sinkOf κ

-- THE SLOT A ROW WAS REGISTERED AT, if it was registered at one.  A
-- share's fan-out matches rows by NUMBER, and a row registered at a
-- minted dynamic source carries a number no slot has in any state the
-- evaluator reaches; reading the registration's own shape here is what
-- lets a step that registers a dynamic row move the ground without
-- that invariant, and leaves the invariant to be spent once, where the
-- fan-out's own writes are accounted for.
slotOf : ∀ {n} {Γ : Ctx n} → RegSrc Γ → Maybe (Fin n)
slotOf (atSlot i)  = just i
slotOf (atDyn _ _) = nothing

rowSlot : ∀ {n} {Γ : Ctx n} {t} → RegRow Γ t → Maybe (Fin n)
rowSlot row = slotOf (proj₁ (proj₂ row))

rowHasNode : ∀ {n} {Γ : Ctx n} {t} → NodeId → RegRow Γ t → Bool
rowHasNode k row = pathHasNode k (proj₂ (proj₂ (proj₂ row)))

rowSink : ∀ {n} {Γ : Ctx n} {t} → RegRow Γ t → Maybe (Fin n)
rowSink row = sinkOf (proj₂ (proj₂ (proj₂ row)))

-- A NODE THE REGISTRY REACHES FROM A SOURCE: it sits on a row
-- registered there, or a row registered there ends in a sink whose
-- own rows reach it.  A share's fan-out folds the rows of its source
-- and every sink those rows end in, so this is the whole of what it
-- may write below the counter -- and a frame standing above such a
-- sink stands on its own node being OUTSIDE it.
data Reaches {n} {Γ : Ctx n} {t} (reg : List (RegRow Γ t)) : Fin n → NodeId → Set where
  on-row  : ∀ {i k}
          → Any (λ row → rowSlot row ≡ just i × rowHasNode k row ≡ true) reg
          → Reaches reg i k
  via-row : ∀ {i k j}
          → Any (λ row → rowSlot row ≡ just i × rowSink row ≡ just j) reg
          → Reaches reg j k
          → Reaches reg i k

-- WHAT A FOLD OF A PATH MAY WRITE BELOW THE COUNTER: its own frames'
-- nodes, and past a sink whatever the registry reaches from it.  The
-- root writes nothing.
Exempt : ∀ {n} {Γ : Ctx n} {lo u t} → Path Γ lo u t → NodeId → List (RegRow Γ t) → Set
Exempt root             k reg = ⊥
Exempt (share-sink i _) k reg = Reaches reg i k
Exempt (f ↠[ _ ] κ)     k reg = T (any (_≡ᵇ k) (frameNodes f)) ⊎ Exempt κ k reg

-- a node on the path is exempt on any registry
onPath-exempt : ∀ {n} {Γ : Ctx n} {lo u t} (κ : Path Γ lo u t) (k : NodeId)
                (reg : List (RegRow Γ t)) → T (pathHasNode k κ) → Exempt κ k reg
onPath-exempt (f ↠[ _ ] κ) k reg on with any (_≡ᵇ k) (frameNodes f)
... | true  = inj₁ _
... | false = inj₂ (onPath-exempt κ k reg on)

-- A REGISTRY THAT REACHES NO MORE THAN ANOTHER: every row of it is a
-- row of the other, or was registered at no slot.
RegSub : ∀ {n} {Γ : Ctx n} {t} → List (RegRow Γ t) → List (RegRow Γ t) → Set
RegSub reg′ reg = ∀ {row} → row ∈ reg′ → row ∈ reg ⊎ rowSlot row ≡ nothing

regsub-refl : ∀ {n} {Γ : Ctx n} {t} {reg : List (RegRow Γ t)} → RegSub reg reg
regsub-refl mem = inj₁ mem

-- one dynamic row appended
regsub-snoc : ∀ {n} {Γ : Ctx n} {t} {reg : List (RegRow Γ t)} {row : RegRow Γ t}
            → rowSlot row ≡ nothing → RegSub (reg ++ row ∷ []) reg
regsub-snoc {reg = reg} dyn mem with ∈-++⁻ reg mem
... | inj₁ old         = inj₁ old
... | inj₂ (here refl) = inj₂ dyn
... | inj₂ (there ())

reaches-sub : ∀ {n} {Γ : Ctx n} {t} {reg reg′ : List (RegRow Γ t)} {i k}
            → RegSub reg′ reg → Reaches reg′ i k → Reaches reg i k
reaches-sub sub (on-row a) with find a
... | row , mem , (sl , p) with sub mem
...   | inj₁ mem′ = on-row (lose mem′ (sl , p))
...   | inj₂ dyn with trans (sym sl) dyn
...     | ()
reaches-sub sub (via-row a r) with find a
... | row , mem , (sl , p) with sub mem
...   | inj₁ mem′ = via-row (lose mem′ (sl , p)) (reaches-sub sub r)
...   | inj₂ dyn with trans (sym sl) dyn
...     | ()

exempt-sub : ∀ {n} {Γ : Ctx n} {lo u t} (κ : Path Γ lo u t) (k : NodeId)
             {reg reg′ : List (RegRow Γ t)}
           → RegSub reg′ reg → Exempt κ k reg′ → Exempt κ k reg
exempt-sub (share-sink i _) k sub r        = reaches-sub sub r
exempt-sub (f ↠[ _ ] κ)     k sub (inj₁ h) = inj₁ h
exempt-sub (f ↠[ _ ] κ)     k sub (inj₂ r) = inj₂ (exempt-sub κ k sub r)
