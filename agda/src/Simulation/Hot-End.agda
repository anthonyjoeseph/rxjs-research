------------------------------------------------------------------
-- A HOT SLOT'S END ONCE ITS SHARE HAS CONNECTED.  The impl's one chain
-- at the raw slot is the raw row's, and its end step runs the row's input
-- block alone into the share: the block's own nodes are written and
-- nothing else, the share is spent, and the bare end is dispatched.  The
-- plain side latches the slot and does not otherwise move.
--
-- THE RAW ROW IS IN THE REGISTRY, and that is what the end store stands
-- on: the census then has the share connected, which is the latch the
-- spent share meets, and the store's ownership has no other row threading
-- the block's nodes, so every other row reads its nodes as it did.  A
-- block handed in without its row says neither: another connected slot's
-- block run for an unconnected one leaves the share spent and unconnected.
------------------------------------------------------------------
module Simulation.Hot-End where

open import Data.Bool    using (Bool; true; false; not; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (∧-zeroʳ; ∨-zeroʳ)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_; _↑ˡ_) renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-injective; ↑ʳ-injective)
open import Data.List    using (List; []; _∷_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using ([])
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookupᵃ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (suc; pred; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (1+n≢0; ≤-refl; ≤-trans; pred[n]≤n)
open import Rx.Evaluator.Reducible.Support using (sub-rule)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Rx.Exp       using (Ctx; Closed; Ty; _≟ᵗ_; listᵗ; _×ᵗ_; unitᵗ; _+ᵗ_)
open import SExp.InstEmit using (machineEmitᵗ)
open import Decide       using (≡ᵇ→≡)
open import Rx.Prim      using (Source)
open import Rx.Evaluator using (Arrival; Sched; EvalSt; RegRow; atSlot; regSource; sameSource; memberSource; cascadeClose; shareSpend; shareDying;
  share-sink; Path; lookupNode; pathHasNode; aliveThroughᶠ; arrTy; arrTick; chainsOf; NodeId; NodeState; setNode; thruWrap;
  mergeAllᵒ; map-f; batchSync-f; thru-outer; _↠[_]_; mergeAll-st; batchSync-st)
open import Rx.Evaluator.Domain using (chainStep⇓; dispatchShare⇓; cascadeGo⇓; casc-cut; casc-live; casc-nil; foldPath⇓; fold-step; fold-sink;
  step-map; step-batchSync; step-from-inner; step-thru-outer; react-alive; react-dead; finish-all-drain; finish-nil; drain-spent; walk-nil;
  disp; chain-step)
open import Rx.Evaluator.Freshness using (lookup-set; set-above)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; hotᵏ; sharedᵏ)
open import Simulation.Stores using (srcCount; Census; LatchRel; Src; InputBlock; block; MachRow; hot~; RowRel; read~; cold~; defer~; hotEq; blockNodes; Store; Arr)
open import Simulation.Frame using (Agree; agree; first; mach-frame; reg-frame; partners-frame; arr-frame)
open import Simulation.Pass using (CarriesU; []; HotEnd; hot-end-at; hot-end-idle; usable-self)
open import Simulation.After using (module Kept)
open Kept using (after; Keeps; Persists)
open import Simulation.Sweep using (t≢f; same-refl; count-hit; raw≢stamped)
open import Simulation.Chains using (count-tail; raw-mistyped; raw-at; raw-one; raw-none;
  plain-none; head-ety; slot-ty; plainᵗ-inj; casc-empty)
open import Simulation.Finish using (close-hit; member-no)
open import Simulation.Schedules using (HeadOf)

-- a test true somewhere along a list, and false all along it
any-in : ∀ {A : Set} (f : A → Bool) (xs : List A) → any f xs ≡ true → Σ A λ x → x ∈ xs × f x ≡ true
any-in f []       ()
any-in f (x ∷ xs) e with f x in fx
... | true  = x , here refl , fx
... | false with any-in f xs e
...   | y , m , fy = y , there m , fy

any-out : ∀ {A : Set} (f : A → Bool) {xs : List A} {x} → x ∈ xs → f x ≡ true → any f xs ≡ true
any-out f {x ∷ xs} (here refl) e = cong (_∨ any f xs) e
any-out f {y ∷ xs} (there m)   e = trans (cong (f y ∨_) (any-out f m e)) (∨-zeroʳ (f y))

all-false : ∀ {A : Set} (f : A → Bool) {xs : List A} → All (λ x → f x ≡ false) xs → any f xs ≡ false
all-false f []       = refl
all-false f (e ∷ es) = cong₂ _∨_ e (all-false f es)

-- a member at a source counts there
count-mem : ∀ {m} {Δ : Ctx m} {t} {k} {r : RegRow Δ t} {K} → r ∈ K
          → sameSource k (regSource (proj₁ (proj₂ r))) ≡ true → srcCount k K ≡ 0 → ⊥
count-mem {k = k} {K = r ∷ K} (here refl) e z = 1+n≢0 (trans (sym (count-hit k r K e)) z)
count-mem {K = r′ ∷ K} (there m) e z = count-mem m e (count-tail r′ K z)

-- two nodes holding different states are two nodes
node-apart : ∀ {m} {Δ : Ctx m} (x y : NodeId) {NI} {A B : NodeState Δ}
           → lookupNode x NI ≡ just A → lookupNode y NI ≡ just B → (A ≡ B → ⊥) → (x ≡ᵇ y) ≡ false
node-apart x y ea eb ne with x ≡ᵇ y in xy
... | false = refl
... | true with ≡ᵇ→≡ x y xy
...   | refl = ⊥-elim (ne (just-injective (trans (sym ea) eb)))

-- a node of a list is not a key off it
apart-off : ∀ (x k : NodeId) {xs} → x ∈ xs → (k ∈ xs → ⊥) → (x ≡ᵇ k) ≡ false
apart-off x k m out with x ≡ᵇ k in xk
... | false = refl
... | true with ≡ᵇ→≡ x k xk
...   | refl = ⊥-elim (out m)

-- a one-lane merge's count drops to none
pred-one : ∀ {a} → a ≤ 1 → (pred a ≡ᵇ 0) ≡ true
pred-one z≤n       = refl
pred-one (s≤s z≤n) = refl

-- THE FRAMES OF AN INPUT BLOCK, FOLDED WITH NO VALUES.  A map hands the
-- empty group on; an empty bracket flushes nothing and rewrites its own
-- node as it was; a merge's outer walks nothing and only its end bit
-- moves; the sink hands the share what it was given
map-nil : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo ℓ s w now fn} {le : lo ≤ ℓ} {p : Path Δ ℓ w u} {fin sched st out sched′ st′}
        → foldPath⇓ {e = e} now (map-f {s = s} fn ↠[ le ] p) [] fin sched st (out , sched′ , st′)
        → foldPath⇓ now p [] fin sched st (out , sched′ , st′)
map-nil (fold-step step-map f) = f

batch-nil : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo ℓ s now nid} {le : lo ≤ ℓ} {p : Path Δ ℓ (s ×ᵗ listᵗ s) u}
              {fin sched} {st : EvalSt e} {out sched′ st′}
          → foldPath⇓ now (batchSync-f nid ↠[ le ] p) [] fin sched st (out , sched′ , st′)
          → lookupNode nid (EvalSt.nodes st) ≡ just (batchSync-st {s = s} false [] false)
          → foldPath⇓ now p [] fin sched (record st { nodes = setNode nid (batchSync-st {s = s} false [] false) (EvalSt.nodes st) })
              (out , sched′ , st′)
batch-nil {s = s} {nid = nid} {st = st} (fold-step step-batchSync f) e with lookupNode nid (EvalSt.nodes st) | e | f
... | _ | refl | f′ with s ≟ᵗ s | f′
...   | yes refl | f″ = f″
...   | no ne    | _  = ⊥-elim (ne refl)

outer-nil : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo ℓ w now nid} {le : lo ≤ ℓ} {p : Path Δ ℓ w u} {fin sched st out sched′ st′}
          → foldPath⇓ {e = e} now (thru-outer mergeAllᵒ nid ↠[ le ] p) [] fin sched st (out , sched′ , st′)
          → foldPath⇓ now p [] (proj₁ (thruWrap mergeAllᵒ nid fin (sched , st)))
              (proj₁ (proj₂ (thruWrap mergeAllᵒ nid fin (sched , st)))) (proj₂ (proj₂ (thruWrap mergeAllᵒ nid fin (sched , st))))
              (out , sched′ , st′)
outer-nil (fold-step (step-thru-outer walk-nil) f) = f

outer-end : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo ℓ w now nid} {le : lo ≤ ℓ} {p : Path Δ ℓ w u}
              {sched} {st : EvalSt e} {lim od} {v : Ty} {out sched′ st′}
          → foldPath⇓ now (thru-outer mergeAllᵒ nid ↠[ le ] p) [] true sched st (out , sched′ , st′)
          → lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = v} lim 0 [] od)
          → foldPath⇓ now p [] true sched (record st { nodes = setNode nid (mergeAll-st {t = v} lim 0 [] true) (EvalSt.nodes st) })
              (out , sched′ , st′)
outer-end {nid = nid} {st = st} fp e with lookupNode nid (EvalSt.nodes st) | e | outer-nil fp
... | _ | refl | f = f

sink-at : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {ℓ now} {k : Fin m} {h : ℓ ≤ toℕ k} {w} (eq : lookup Δ k ≡ w) {fin sched st r}
        → foldPath⇓ {e = e} now (subst (λ w → Path Δ ℓ w u) eq (share-sink k h)) [] fin sched st r
        → dispatchShare⇓ now k h [] fin sched st r
sink-at refl (fold-sink d) = d

fin-at : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {lo w now} {p : Path Δ lo w u} {vals c c′ sched st r}
       → c ≡ c′ → foldPath⇓ {e = e} now p vals c sched st r → foldPath⇓ now p vals c′ sched st r
fin-at refl f = f

-- the share handed nothing, and no end, does nothing
disp-quiet : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {ℓ now} {k : Fin m} {h : ℓ ≤ toℕ k} {sched st r}
           → dispatchShare⇓ {e = e} now k h [] false sched st r → r ≡ ([] , sched , st)
disp-quiet (disp walk-nil) = refl

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  -- a plain registration's partner is at a stamped slot or a minted
  -- source, never at a raw slot
  row-src : ∀ {π NP NI LP LI r r′} → RowRel {Γ = Γ} κ π {t} NP NI LP LI r r′
          → ∀ (k : Fin n) → proj₁ (proj₂ r′) ≡ atSlot (k ↑ˡ n) → ⊥
  row-src (read~ {i = j} _ _ _) k e = raw≢stamped k j (sym (cong regSource e))
  row-src (cold~ _ _ _ _) k ()
  row-src (defer~ _ _ _ _ _ _) k ()

  -- THE INPUT BLOCK'S RUN TO ITS END, WITH NO LIVE ROW THROUGH ITS NODES.
  -- The inner reacts dead, the drain is spent, the bracket hands on a
  -- bare end, the flattening merge ends, and the share is handed the end
  -- with no values.  Only the block's own nodes are written, and they are
  -- a block again; the schedule and every other part of the state stand.
  -- The inner's finish folds the rest of the block once with no end
  -- before its own end goes down, and that pass is quiet: an empty
  -- bracket flushes nothing and the share is handed nothing
  block-end : ∀ {i : Fin n} (hot : lookup κ i ≡ hotᵏ) {π NP} {sI : Sched (plainᵏ Γ κ)} {st : EvalSt ei} {now}
                {rid u ℓ full} {q : Path (plainᵏ Γ κ) (suc (toℕ (i ↑ˡ n))) u (emitᵗ t)} {h : ℓ ≤ toℕ (n ↑ʳ i)}
            → _≡_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (u , q)) (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full))
            → InputBlock {Γ = Γ} κ π {t} NP (EvalSt.nodes st) (plainᵗ (lookup Γ i)) full
                (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
            → (∀ {j} → j ∈ blockNodes full → any (aliveThroughᶠ j st) (EvalSt.registry st) ≡ false)
            → ∀ {r} → foldPath⇓ now q [] true sI st r
            → Σ _ λ NI′ → InputBlock {Γ = Γ} κ π {t} NP NI′ (plainᵗ (lookup Γ i)) full
                              (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
                        × (∀ k → (k ∈ blockNodes full → ⊥) → lookupNode k NI′ ≡ lookupNode k (EvalSt.nodes st))
                        × dispatchShare⇓ now (n ↑ʳ i) h [] true sI (record st { nodes = NI′ }) r
  block-end {i = i} hot {sI = sI} {st = st} refl (block {m1 = m1} {j1 = j1} {b = b} {m2 = m2} {a₁ = a₁} {d₂ = d₂} e₁ a≤ eb e₂ u₁ uj ub u₂) alive fp
    with map-nil fp
  ... | fold-step (step-from-inner (react-alive x)) _ = ⊥-elim (t≢f (trans (sym x) (alive (there (here refl)))))
  ... | fold-step (step-from-inner (react-dead _ F)) f
    with lookupNode m1 (EvalSt.nodes st) | e₁ | F
  ...   | _ | refl | finish-nil x = ⊥-elim (t≢f (trans (sym (usable-self _)) x))
  ...   | _ | refl | finish-all-drain fv drain-spent
    with disp-quiet (sink-at (hotEq {Γ = Γ} κ i hot) (outer-nil (map-nil (map-nil (batch-nil fv eb)))))
  ...     | refl =
    NI′ , block e₁′ (≤-trans pred[n]≤n a≤) eb′ (lookup-set m2 M2 N₂) u₁ uj ub u₂ , fr ,
    sink-at (hotEq {Γ = Γ} κ i hot)
      (outer-end (map-nil (map-nil (batch-nil (fin-at (pred-one a≤) f) eb₁))) e₂′)
    where
      A = plainᵗ (lookup Γ i)
      M1 M2 B : NodeState (plainᵏ Γ κ)
      M1 = mergeAll-st {t = unitᵗ +ᵗ A} nothing (pred a₁) [] true
      M2 = mergeAll-st {t = machineEmitᵗ A} nothing 0 [] true
      B  = batchSync-st {s = unitᵗ +ᵗ A} false [] false
      NI N₀ N₁ N₂ NI′ : List (NodeId × NodeState (plainᵏ Γ κ))
      NI  = EvalSt.nodes st
      N₀  = setNode b B NI
      N₁  = setNode m1 M1 N₀
      N₂  = setNode b B N₁
      NI′ = setNode m2 M2 N₂
      eb₁ : lookupNode b N₁ ≡ just B
      eb₁ = trans (set-above m1 b M1 N₀ (node-apart m1 b {NI = NI} e₁ eb (λ ()))) (lookup-set b B NI)
      e₂′ : lookupNode m2 N₂ ≡ just (mergeAll-st {t = machineEmitᵗ A} nothing 0 [] d₂)
      e₂′ = trans (set-above b m2 B N₁ (node-apart b m2 {NI = NI} eb e₂ (λ ())))
              (trans (set-above m1 m2 M1 N₀ (node-apart m1 m2 {NI = NI} e₁ e₂ (λ ())))
                (trans (set-above b m2 B NI (node-apart b m2 {NI = NI} eb e₂ (λ ()))) e₂))
      e₁′ : lookupNode m1 NI′ ≡ just M1
      e₁′ = trans (set-above m2 m1 M2 N₂ (node-apart m2 m1 {NI = NI} e₂ e₁ (λ ())))
              (trans (set-above b m1 B N₁ (node-apart b m1 {NI = NI} eb e₁ (λ ()))) (lookup-set m1 M1 N₀))
      eb′ : lookupNode b NI′ ≡ just B
      eb′ = trans (set-above m2 b M2 N₂ (node-apart m2 b {NI = NI} e₂ eb (λ ()))) (lookup-set b B N₁)
      fr : ∀ k → (k ∈ m1 ∷ j1 ∷ b ∷ m2 ∷ [] → ⊥) → lookupNode k NI′ ≡ lookupNode k NI
      fr k out =
        trans (set-above m2 k M2 N₂ (apart-off m2 k (there (there (there (here refl)))) out))
          (trans (set-above b k B N₁ (apart-off b k (there (there (here refl))) out))
            (trans (set-above m1 k M1 N₀ (apart-off m1 k (here refl) out))
              (set-above b k B NI (apart-off b k (there (there (here refl))) out))))

  hot-block-end : ∀ {i : Fin n} (hot : lookup κ i ≡ hotᵏ) {π NP} {sI : Sched (plainᵏ Γ κ)} {st : EvalSt ei} {a′ : Arrival (plainᵏ Γ κ)}
                    {rid q ℓ full} {h : ℓ ≤ toℕ (n ↑ʳ i)}
                → _≡_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (arrTy a′ , q)) (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full))
                → InputBlock {Γ = Γ} κ π {t} NP (EvalSt.nodes st) (plainᵗ (lookup Γ i)) full
                    (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
                → (∀ {j} → j ∈ blockNodes full → any (aliveThroughᶠ j st) (EvalSt.registry st) ≡ false)
                → ∀ {r} → chainStep⇓ a′ [] true (suc (toℕ (i ↑ˡ n)) , q) sI st r
                → Σ _ λ NI′ → InputBlock {Γ = Γ} κ π {t} NP NI′ (plainᵗ (lookup Γ i)) full
                                  (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
                            × (∀ k → (k ∈ blockNodes full → ⊥) → lookupNode k NI′ ≡ lookupNode k (EvalSt.nodes st))
                            × dispatchShare⇓ (arrTick a′) (n ↑ʳ i) h [] true sI (record st { nodes = NI′ }) r
  hot-block-end hot d ib alive (chain-step fp) = block-end hot d ib alive fp

  -- the emits of no values carry none
  carriesU-nil : ∀ {u u′} (e : u′ ≡ emitᵗ u) → CarriesU κ {t} {ep} {ei} e [] []
  carriesU-nil refl = []

  module _ {sP stP sI stI} (S : Store κ {t} {ep} {ei} sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
           (hot : lookup κ i ≡ hotᵏ) (e₁ : Arrival.source a ≡ toℕ i) (e₂ : Arrival.source a′ ≡ toℕ (i ↑ˡ n))
           {rid ℓ} {full : Path (plainᵏ Γ κ) (suc (toℕ (i ↑ˡ n))) (plainᵗ (lookup Γ i)) (emitᵗ t)} {h : ℓ ≤ toℕ (n ↑ʳ i)}
           (mem : _∈_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full)) (EvalSt.registry stI)) where

    open Store S

    private
      K     = EvalSt.registry stI
      NI    = EvalSt.nodes stI
      CP    = EvalSt.completedSources stP
      CI    = EvalSt.completedSources stI
      SI    = EvalSt.connectedShares stI
      raw   = toℕ (i ↑ˡ n)
      shr   = toℕ (n ↑ʳ i)
      rawRow : RegRow (plainᵏ Γ κ) (emitᵗ t)
      rawRow = rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full)
      St₀ : EvalSt ei
      St₀ = record (cascadeClose a′ stI) { delivered = rid ∷ EvalSt.delivered (cascadeClose a′ stI) }

    -- the raw row's block nodes are threaded by it alone
    own-raw : ∀ {j} → j ∈ blockNodes full → All (λ r′ → pathHasNode j (proj₂ (proj₂ (proj₂ r′))) ≡ true → r′ ≡ rawRow) K
    own-raw = lookupᵃ owned mem (λ k e → raw≢stamped i k (cong regSource e))

    -- the raw row's count is one, so the share has connected
    live : srcCount raw K ≡ 1 × memberSource shr SI ≡ true
    live with census i hot
    ... | inj₁ x       = x
    ... | inj₂ (z , _) = ⊥-elim (count-mem mem (same-refl raw) z)

    -- THE END FINDS NO LIVE ROW THROUGH THE BLOCK: the raw row is dying and
    -- delivered, and no other row threads its nodes
    dead-raw : ∀ j → aliveThroughᶠ j St₀ rawRow ≡ false
    dead-raw j = trans (cong (λ z → pathHasNode j full ∧ not (any (_≡ᵇ rid) (EvalSt.cancelled stI)) ∧ z)
                             (cong₂ (λ x y → not x ∨ not y) dy (first rid [])))
                       (trans (cong (pathHasNode j full ∧_) (∧-zeroʳ _)) (∧-zeroʳ _))
      where
        dy : memberSource raw (Arrival.source a′ ∷ []) ≡ true
        dy = subst (λ s → memberSource raw (s ∷ []) ≡ true) (sym e₂) (cong (_∨ false) (same-refl raw))

    alive : ∀ {j} → j ∈ blockNodes full → any (aliveThroughᶠ j St₀) K ≡ false
    alive {j} jm = all-false (aliveThroughᶠ j St₀) (go (own-raw jm))
      where
        one : ∀ r′ → (pathHasNode j (proj₂ (proj₂ (proj₂ r′))) ≡ true → r′ ≡ rawRow) → ∀ b → pathHasNode j (proj₂ (proj₂ (proj₂ r′))) ≡ b → aliveThroughᶠ j St₀ r′ ≡ false
        one r′ o false e = cong (_∧ _) e
        one r′ o true  e = subst (λ r → aliveThroughᶠ j St₀ r ≡ false) (sym (o e)) (dead-raw j)
        go : ∀ {K′} → All (λ r′ → pathHasNode j (proj₂ (proj₂ (proj₂ r′))) ≡ true → r′ ≡ rawRow) K′ → All (λ r′ → aliveThroughᶠ j St₀ r′ ≡ false) K′
        go []                  = []
        go {r′ ∷ _} (o ∷ os) = one r′ o _ refl ∷ go os

    module _ {NI′} (ib′ : InputBlock {Γ = Γ} κ π {t} (EvalSt.nodes stP) NI′ (plainᵗ (lookup Γ i)) full
                            (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h)))
                   (fr : ∀ k → (k ∈ blockNodes full → ⊥) → lookupNode k NI′ ≡ lookupNode k NI) where

      -- A ROW IS THE RAW ROW, OR READS ITS NODES AS IT DID
      touch : ∀ {r′} → r′ ∈ K → (r′ ≡ rawRow) ⊎ Agree {Γ = Γ} κ NI′ NI (proj₂ (proj₂ (proj₂ r′)))
      touch {r′} m′ = go (any (λ j → pathHasNode j (proj₂ (proj₂ (proj₂ r′)))) (blockNodes full)) refl
        where
          go : ∀ b → any (λ j → pathHasNode j (proj₂ (proj₂ (proj₂ r′)))) (blockNodes full) ≡ b → (r′ ≡ rawRow) ⊎ Agree {Γ = Γ} κ NI′ NI (proj₂ (proj₂ (proj₂ r′)))
          go true  e with any-in (λ j → pathHasNode j (proj₂ (proj₂ (proj₂ r′)))) (blockNodes full) e
          ... | j , jm , hj = inj₁ (lookupᵃ (own-raw jm) m′ hj)
          go false e = inj₂ (agree (λ k hk → fr k (λ km → t≢f (trans (sym (any-out (λ j → pathHasNode j (proj₂ (proj₂ (proj₂ r′)))) km hk)) e))))

      rows-ob : ∀ {r r′} → r′ ∈ K → RowRel {Γ = Γ} κ π {t} (EvalSt.nodes stP) NI (Sched.live sP) (Sched.live sI) r r′ → Agree {Γ = Γ} κ NI′ NI (proj₂ (proj₂ (proj₂ r′)))
      rows-ob m′ x with touch m′
      ... | inj₂ ag = ag
      ... | inj₁ e  = ⊥-elim (row-src x i (cong (λ r → proj₁ (proj₂ r)) e))

      machs-ob : ∀ {r′} → r′ ∈ K → MachRow {Γ = Γ} κ π {t} (EvalSt.nodes stP) NI (Sched.live sP) (Sched.live sI) r′
               → MachRow {Γ = Γ} κ π {t} (EvalSt.nodes stP) NI′ (Sched.live sP) (Sched.live sI) r′
      machs-ob m′ x with touch m′
      ... | inj₂ ag = mach-frame {Γ = Γ} κ ag x
      ... | inj₁ e  = subst (MachRow {Γ = Γ} κ π {t} (EvalSt.nodes stP) NI′ (Sched.live sP) (Sched.live sI)) (sym e) (hot~ hot ib′ refl)

      private
        CI′ : List Source
        CI′ = shr ∷ Arrival.source a′ ∷ CI

        -- a raw slot is no share
        skI : ∀ (j : Fin n) → memberSource (toℕ (j ↑ˡ n)) CI′ ≡ memberSource (toℕ (j ↑ˡ n)) (Arrival.source a′ ∷ CI)
        skI j = member-no (Arrival.source a′ ∷ CI) (raw≢stamped j i)

        rawI : memberSource raw CI′ ≡ true
        rawI = trans (skI i) (close-hit a′ stI e₂)

        shareI : memberSource shr CI′ ≡ true
        shareI = cong (_∨ memberSource shr (Arrival.source a′ ∷ CI)) (same-refl shr)

        -- another slot's latches read as they did
        skR : ∀ (j : Fin n) → toℕ j ≢ toℕ i → memberSource (toℕ (j ↑ˡ n)) CI′ ≡ memberSource (toℕ (j ↑ˡ n)) CI
        skR j ne = trans (skI j) (member-no CI (subst (toℕ (j ↑ˡ n) ≢_) (sym e₂)
                                                       (λ x → ne (trans (sym (toℕ-↑ˡ j n)) (trans x (toℕ-↑ˡ i n))))))

        shJ : ∀ (j : Fin n) → toℕ j ≢ toℕ i → memberSource (toℕ (n ↑ʳ j)) CI′ ≡ memberSource (toℕ (n ↑ʳ j)) CI
        shJ j ne = trans (member-no (Arrival.source a′ ∷ CI) (λ x → ne (cong toℕ (↑ʳ-injective n j i (toℕ-injective x)))))
                         (member-no CI (subst (toℕ (n ↑ʳ j) ≢_) (sym e₂) (λ x → raw≢stamped i j (sym x))))

        skP : ∀ (j : Fin n) → toℕ j ≢ toℕ i → memberSource (toℕ j) (Arrival.source a ∷ CP) ≡ memberSource (toℕ j) CP
        skP j ne = member-no CP (subst (toℕ j ≢_) (sym e₁) ne)

      -- THE END STORE: the plain side latched, the impl's raw slot latched
      -- and its share spent, and the block's nodes rewritten under the rows
      end-store : Store κ sP (cascadeClose a stP) sI (shareSpend (n ↑ʳ i) (shareDying (n ↑ʳ i) true (record St₀ { nodes = NI′ })))
      end-store = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals ; pairs-below = pairs-below ; sources = sources ; numbers = numbers ; distinct = distinct
        ; sync = sync ; rows = reg-frame {Γ = Γ} κ rows-ob machs-ob (λ m → m) rows ; bounded = bounded ; swept = swept
        ; uncut = uncut ; rids = rids ; fresh-ids = fresh-ids ; above = above ; latches = lat ; census = cen ; owned = owned
        ; ruleP = sub-rule (λ r∈ → r∈) ≤-refl ruleP ; ruleI = sub-rule (λ r∈ → r∈) ≤-refl ruleI }
        where
          lat : LatchRel {Γ = Γ} κ (Arrival.source a ∷ CP) (EvalSt.connectedShares stP) CI′ SI
          lat j with j ≟ᶠ i
          ... | yes refl =
                (λ _ → trans (close-hit a stP e₁) (sym rawI) , trans shareI (sym (cong₂ _∧_ rawI (proj₂ live))))
              , (λ sk → ⊥-elim (hs (trans (sym hot) sk)))
            where
              hs : hotᵏ ≡ sharedᵏ → ⊥
              hs ()
          ... | no ne =
                (λ hj → let c , d = proj₁ (latches j) hj
                        in trans (skP j ne′) (trans c (sym (skR j ne′)))
                         , trans (shJ j ne′) (trans d (cong (_∧ memberSource (toℕ (n ↑ʳ j)) SI) (sym (skR j ne′)))))
              , (λ sk → let c , d = proj₂ (latches j) sk in trans (skP j ne′) (trans c (sym (shJ j ne′))) , d)
            where
              ne′ : toℕ j ≢ toℕ i
              ne′ x = ne (toℕ-injective x)

          cen : ∀ j → lookup κ j ≡ hotᵏ → Census (toℕ (j ↑ˡ n)) (toℕ (n ↑ʳ j)) K (memberSource (toℕ (n ↑ʳ j)) SI) (memberSource (toℕ (j ↑ˡ n)) CI′)
          cen j hj with j ≟ᶠ i
          ... | yes refl = inj₁ live
          ... | no ne    = subst (Census (toℕ (j ↑ˡ n)) (toℕ (n ↑ʳ j)) K (memberSource (toℕ (n ↑ʳ j)) SI))
                                 (sym (skR j (λ x → ne (toℕ-injective x)))) (census j hj)

      end-keeps : Keeps κ S end-store
      end-keeps (inj₁ x)             = inj₁ x
      end-keeps (inj₂ (x , y , p))   = inj₂ (x , y , partners-frame {Γ = Γ} κ rows-ob machs-ob (λ m → m) rows p)

      end-persists : Persists κ S end-store
      end-persists ar = record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar
                               ; rows = arr-frame {Γ = Γ} κ rows-ob machs-ob (λ m → m) rows (Arr.rows ar) ; lists = Arr.lists ar }

  -- THE IMPL'S ONE CHAIN AT A HOT ARRIVAL'S RAW SLOT, CLOSING, ONCE ITS
  -- SHARE HAS CONNECTED: the block runs to the share's end over the end
  -- store, and the end it hands the share is dispatched
  hot-end-block : ∀ {sP stP sI stI} (S : Store κ {t} {ep} {ei} sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
                → (hot : lookup κ i ≡ hotᵏ) → Arrival.source a ≡ toℕ i → Arrival.source a′ ≡ toℕ (i ↑ˡ n)
                → arrTy a ≡ lookup Γ i
                → ∀ {rid q ℓ full} {h : ℓ ≤ toℕ (n ↑ʳ i)}
                → _≡_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (arrTy a′ , q)) (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full))
                → _∈_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full)) (EvalSt.registry stI)
                → InputBlock {Γ = Γ} κ (Store.π S) {t} (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ (lookup Γ i)) full
                    (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
                → ∀ {eI sI₃ stI₃}
                → chainStep⇓ a′ [] true (suc (toℕ (i ↑ˡ n)) , q) sI
                    (record (cascadeClose a′ stI) { delivered = rid ∷ EvalSt.delivered (cascadeClose a′ stI) }) (eI , sI₃ , stI₃)
                → HotEnd κ S a a′ i eI sI₃ stI₃
  hot-end-block S {a} {a′} {i} hot e₁ e₂ ety {h = h} d mem ib step
    with hot-block-end hot d ib (alive S {a} {a′} {i} hot e₁ e₂ {h = h} mem) step
  ... | NI′ , ib′ , fr , dsp =
    hot-end-at {below = h} {εI = trans (hotEq {Γ = Γ} κ i hot) (cong emitᵗ (sym ety))} {ty = ety}
      (after (end-store S {a} {a′} {i} hot e₁ e₂ mem ib′ fr) (end-keeps S {a} {a′} {i} hot e₁ e₂ mem ib′ fr) (end-persists S {a} {a′} {i} hot e₁ e₂ mem ib′ fr) [] (λ x → x))
      (carriesU-nil _) dsp refl

-- AND AT ITS END: none, and no plain reader, until the share has
-- connected; then the one raw row's, whose end step is the input block's
-- run.  A raw row at another type than the arrival's is not there, since
-- a slot's source holds its slot's type
hot-end-start : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                  {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
              → (S : Store κ sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
              → lookup κ i ≡ hotᵏ
              → ∀ {l l′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′
              → Arrival.source a ≡ toℕ i → Arrival.source a′ ≡ toℕ (i ↑ˡ n)
              → ∀ {eI sI₃ stI₃}
              → cascadeGo⇓ a′ [] true (chainsOf a′ stI) sI (cascadeClose a′ stI) (eI , sI₃ , stI₃)
              → HotEnd κ S a a′ i eI sI₃ stI₃
hot-end-start {n} {Γ} κ {stP = stP} {sI = sI} {stI = stI} S {a} {a′} {i} hk src h h′ e₁ e₂ {eI} {sI₃} {stI₃} go
  with Store.census S i hk
... | inj₂ (z₁ , z₂ , cd) =
  hot-end-idle (plain-none {Γ = Γ} κ e₁ (Store.rows S) (proj₁ (Store.above S)) z₂) z₁ z₂ cd
    (casc-empty (subst (λ c → cascadeGo⇓ a′ [] true c sI (cascadeClose a′ stI) (eI , sI₃ , stI₃))
                       (raw-none a′ (EvalSt.registry stI) (subst (λ k → srcCount k (EvalSt.registry stI) ≡ 0) (sym e₂) z₁)) go))
... | inj₁ (c , _) with raw-one {Γ = Γ} κ {CI = EvalSt.cancelled stI} e₂ (Store.rows S) (proj₂ (Store.above S)) (proj₂ (Store.uncut S)) c
...   | raw-mistyped ne _ = ⊥-elim (ne (trans (head-ety {Γ = Γ} κ src h h′ e₁) (cong plainᵗ (slot-ty {Γ = Γ} κ src h e₁))))
...   | raw-at hot ch d ib u mem
  with subst (λ c → cascadeGo⇓ a′ [] true c sI (cascadeClose a′ stI) (eI , sI₃ , stI₃)) ch go
...     | casc-cut y _ = ⊥-elim (t≢f (trans (sym y) u))
...     | casc-live _ d′ casc-nil =
  subst (λ o → HotEnd κ S a a′ i o sI₃ stI₃) (sym (++-identityʳ _))
        (hot-end-block κ S hot e₁ e₂
                       (plainᵗ-inj (trans (sym (head-ety {Γ = Γ} κ src h h′ e₁)) (cong (λ r → proj₁ (proj₂ (proj₂ r))) d)))
                       d mem ib d′)
