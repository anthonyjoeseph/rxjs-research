-- `quiet-sink` IS FALSE OF EVERY STORE PAIRING A SHARE'S READER.  An
-- emit carrying nothing reaches the impl's share and its walk delivers
-- it to every reader, marking each one delivered; the plain side does
-- not move, so its partner stays undelivered.  `Store.dlv-alike` asks a
-- pair of rows to be delivered alike, and the only relation between the
-- two one-row registries pairs exactly these two.
--
-- THE STATES ARE BUILT, NOT REACHED, and that is the claim: the
-- statement quantified over every store relating a share's sink.
module Refuted.Quiet-Sink-Delivered where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc; _↑ʳ_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Closed; Val; FnClo; natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_; varᵗ)
open import Rx.Mint using (setAt; regᵏ)
open import Rx.Evaluator using (Sched; EvalSt; Path; RegRow; root; map-f; share-sink; _↠[_]_; atSlot; sched-init; st-init)
open import Rx.Evaluator.Domain using (fold-root; fold-step; step-map; fold-sink; disp; walk-more; walk-nil; go-live; go-nil)
open import Rx.Evaluator.Reducible.Support using (rule; sink-sound)
open import SExp.Syntax using (Kinds; plainᵏ; emitᵗ; inputˢ; emptyˢ)
open import SExp.Plain using (plainExp)
open import SExp.Elaborate using (restampᵛ; subscribeᵛ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import Simulation.Stores using (Store; RegRel; Spent; sharedEq; root~; sink~; read~; mach; []; _∷_)
open import Simulation.Schedules using ([])
open import Simulation.After using (module Kept)
open Kept using (module After)
open import Simulation.Pass.Quiet using (module PassQ; sink-intro; sink-ok)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots)
open import Rx.Prim using (hot)

κ₀ : Kinds 2
κ₀ = κOf (hot [])

ins : SimulSlots Γ₂ κ₀
ins = mkSlots (hot []) emptyˢ

Γ′ = plainᵏ Γ₂ κ₀

ep : Closed Γ₂ natᵗ
ep = plainExp (inputˢ zero)

ei : Closed Γ′ (emitᵗ natᵗ)
ei = elaborateImpl {Γ = Γ₂} κ₀ (inputˢ zero)

open PassQ κ₀ using (Carries; quiet; [])
open PassQ.InQ κ₀ {natᵗ} {ep} {ei} using (Quiet)

-- one reader on each side, registered on the share and not yet delivered
rowP : RegRow Γ₂ natᵗ
rowP = 0 , atSlot (suc zero) , (natᵗ , root)

rowI : RegRow Γ′ (emitᵗ natᵗ)
rowI = 0 , atSlot (2 ↑ʳ suc zero)
         , (emitᵗ natᵗ , (map-f (uniqᵗ ∷ [] , restampᵛ (varᵗ (there (here refl))) subscribeᵛ (varᵗ (here refl)) , 0 ∷ᵉ []ᵉ) ↠[ ≤-refl ] root))

sP : Sched Γ₂
sP = record (sched-init ep (plainSlots ins)) { mint = setAt regᵏ 1 (Sched.mint (sched-init ep (plainSlots ins))) ; live = [] }

stP : EvalSt ep
stP = record (st-init ep) { registry = rowP ∷ [] ; connectedShares = 1 ∷ [] }

sI : Sched Γ′
sI = record (sched-init ei (embedSlotsImpl ins)) { mint = setAt regᵏ 1 (Sched.mint (sched-init ei (embedSlotsImpl ins))) ; live = [] }

stI : EvalSt ei
stI = record (st-init ei) { registry = rowI ∷ [] ; connectedShares = 3 ∷ [] }

S : Store {Γ = Γ₂} κ₀ sP stP sI stI
S = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; pairs-below = [] , []
  ; sources = []
  ; numbers = []
  ; distinct = [] , []
  ; sync    = []
  ; rows    = read~ (inj₂ refl) root~ refl ∷ []
  ; dlv-alike = refl , tt
  ; dying-alike = refl , tt
  ; latches = λ { zero → (λ _ → refl , refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; bounded = [] , []
  ; swept   = []
  ; uncut   = (refl ∷ []) , (refl ∷ [])
  ; rids    = ([] ∷ []) , ([] ∷ [])
  ; fresh-ids = (s≤s z≤n ∷ []) , (s≤s z≤n ∷ [])
  ; above   = (refl ∷ []) , (refl ∷ [])
  ; census  = λ { zero _ → inj₂ (refl , refl , λ ()) ; (suc zero) () }
  ; owned   = (λ ns → ⊥-elim (ns (suc zero) refl)) ∷ []
  ; ruleP   = rule (λ { k (here refl) _ () _ ; k (there ()) _ _ _ }) (λ { (here refl) k () ; (there ()) }) (λ { (here refl) → lift tt ; (there ()) })
  ; ruleI   = rule (λ { k (here refl) _ () _ ; k (there ()) _ _ _ }) (λ { (here refl) k () ; (there ()) })
                   (λ { (here refl) → (λ k ()) , lift tt ; (there ()) })
  ; scripts = ins , refl , refl
  }

-- an emit carrying no value and no end
e₀ : Val Γ′ (emitᵗ natᵗ)
e₀ = [] , 0 , 0 , inj₁ tt

ε = sharedEq {Γ = Γ₂} κ₀ (suc zero) refl

QuietSink : Set
QuietSink = ∀ {lo lo′} {h : lo ≤ 1} {h′ : lo′ ≤ 3}
          → Quiet (share-sink (suc zero) h) (subst (λ u → Path Γ′ lo′ u (emitᵗ natᵗ)) ε (share-sink (2 ↑ʳ suc zero) h′))

-- the only relation between two one-row registries pairs the rows, and
-- a pair delivered on one side alone is not spent alike
unpaired : ∀ {π NP NI LP LI} {r r′} (q : RegRel κ₀ π NP NI LP LI (r ∷ []) (r′ ∷ [])) {dP dI}
         → dP r ≡ false → dI r′ ≡ true → Spent κ₀ π NP NI LP LI q dP dI → ⊥
unpaired (_ ∷ []) f t (d , _) with trans (sym f) (trans d t)
... | ()
unpaired (mach _ ()) _ _ _

-- the impl's share walks the one emit to its one reader
quiet-sink-false : ¬ QuietSink
quiet-sink-false QS = unpaired (Store.rows S′) refl refl (Store.dlv-alike S′)
  where
  S′ = After.store (proj₁ (QS {h = z≤n} {h′ = z≤n} S (sink~ refl) (quiet e₀ [] []) refl
         (sink-sound (suc zero) z≤n (Store.ruleP S)) (sink-ok ε (Store.ruleI S))
         (sink-intro ε (fold-sink (disp (walk-more (go-live refl (fold-step step-map fold-root) go-nil) walk-nil))))))
