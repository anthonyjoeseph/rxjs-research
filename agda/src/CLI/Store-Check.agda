------------------------------------------------------------------
-- THE STORES, DECIDED, AT EVERY ARRIVAL BOUNDARY OF BOTH RUNS.  The
-- correspondence `Simulation.Stores.Store` claims is lockstep: the two
-- runs' states after the subscribe, and after each arrival, related
-- field by field.  Every unprobed leaf of the simulation claims one
-- step keeps it, so a compiled sweep of this decider over a leaf's
-- region is the evidence a leaf's row is lowered on, and a red names
-- the field, the row and the clause a program breaks it at.
--
-- `π` IS INFERRED, NOT GIVEN.  The record holds it existentially, so
-- each clause returns the pairings it needs as constraints, every way
-- it can be met, and the store holds when one combination of the
-- rows' constraints is one pairing with distinct values that no
-- impl-only node a row reads is among.  A flattener's inner reads a
-- PREFIX of its node's entry, since `Flattener` leaves the tail free.
--
-- WHAT IS DECIDED IS EVERY STRUCTURAL CLAUSE AND EVERY FRAME'S STEP ON
-- SAMPLES; WHAT IS NOT IS A TERM.  `Lifts`, `ScanLifts` and `CutLifts`
-- are read by applying both live steps to a few related inputs per
-- type, so a green covers those inputs and a red is a counterexample.
-- `ObsRel`/`DeferRel`/`EnvRel` relate terms, and an `obs` value is
-- related to anything here.  `ruleP`/`ruleI` are the evaluator's own
-- rule, which its builders already carry.  A red is a candidate until
-- a probe pins it.
--
-- A COMBINATION SET IS CAPPED, so a red reading "no pairing fits" with
-- the set at its cap is not yet a red.  The report says when it was.
------------------------------------------------------------------
module CLI.Store-Check where

open import Data.Bool    using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.ListAction using (any; all)
open import Data.Fin     using (Fin; toℕ)
open import Data.List    using (List; []; _∷_; map; length; take; concatMap; _++_; allFin)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing; maybe′) renaming (map to mapᴹ)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.String  using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (lookup)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Prim      using (Source; Fuel)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Val; Closed; _≟ᵗ_;
  FnClo; applyClo; emptyᵉ; []ᵉ)
open import Rx.Slots     using (Slots)
open import Rx.Mint      using (counter; sourceᵏ; regᵏ)
open import Rx.Evaluator using (LiveSource; Sched; EvalSt; Stream; Arrival; sched-next; NodeState; NodeId; Path; RegRow;
  atSlot; atDyn; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f; batchSync-f; from-inner; thru-outer;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st; mergeAll-st; switch-st; exhaust-st; batchSync-st;
  echoᵗ; lookupNode; memberSource; pathHasNode; takeVals; scanVals)
open import Rx.Evaluator.Builder using (cascade!; pop-rule; subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; _,_; Rule)
open import SExp.Syntax  using (SExp; Kind; hotᵏ; coldᵏ; sharedᵏ; Kinds; plainᵏ; plainᵗ; emitᵗ)
open import SExp.InstEmit using (machineEmitᵗ; instEventᵗ)
open import SExp.InstEmit.Decode using (decodeEmit)
open import Batchable.Inst-Extract using (emitValues)
open import SExp.Elaborate using (ScanAᵗ; CutS; FlatSᵗ)
open import SExp.Plain   using (plainExp)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import Simulation.Stores using (guardOf; aboveᵇ; srcCount; blockNodes)
open import Simulation.Schedules using (ticks)
open import CLI.Emit-Eq  using (eqListℕ; prefixListℕ)

------------------------------------------------------------------
-- Small decisions
------------------------------------------------------------------

eqB : Bool → Bool → Bool
eqB true  b = b
eqB false b = not b

eqMb : Maybe ℕ → Maybe ℕ → Bool
eqMb nothing  nothing  = true
eqMb (just a) (just b) = a ≡ᵇ b
eqMb _        _        = false

is : Maybe ℕ → ℕ → Bool
is (just a) b = a ≡ᵇ b
is nothing  _ = false

eqOp : AllOp → AllOp → Bool
eqOp mergeAllᵒ mergeAllᵒ = true
eqOp switchᵒ   switchᵒ   = true
eqOp exhaustᵒ  exhaustᵒ  = true
eqOp _         _         = false

isHot isShared : Kind → Bool
isHot hotᵏ = true
isHot _    = false
isShared sharedᵏ = true
isShared _       = false

_≈_ : Ty → Ty → Bool
s ≈ t = does (s ≟ᵗ t)

unique : List ℕ → Bool
unique []       = true
unique (x ∷ xs) = not (any (_≡ᵇ x) xs) ∧ unique xs

castV : ∀ {m} {Δ : Ctx m} s t → Val Δ s → Maybe (Val Δ t)
castV {Δ = Δ} s t v with s ≟ᵗ t
... | yes eq = just (subst (Val Δ) eq v)
... | no _   = nothing

-- an echo's lane type, read off the element type
echoOf : Ty → Maybe Ty
echoOf ((unitᵗ +ᵗ u) ×ᵗ (unitᵗ +ᵗ obs u′)) = if u ≈ u′ then just u else nothing
echoOf _                                   = nothing

indexed : ∀ {A : Set} → ℕ → List A → List (ℕ × A)
indexed k []       = []
indexed k (x ∷ xs) = (k , x) ∷ indexed (suc k) xs

-- a node, read at the shape a clause names, its element type checked
module _ {m} {Δ : Ctx m} where

  cellOf : (ty : Ty) → Maybe (NodeState Δ) → Maybe (Val Δ ty)
  cellOf ty (just (cell-st {t = s} v)) = castV s ty v
  cellOf ty _                          = nothing

  takeOf : Maybe (NodeState Δ) → Maybe ℕ
  takeOf (just (take-st b)) = just b
  takeOf _                  = nothing

  -- limit, active count, queue length, outer done
  mergeOf : Ty → Maybe (NodeState Δ) → Maybe (Maybe ℕ × ℕ × ℕ × Bool)
  mergeOf ty (just (mergeAll-st {t = s} lim a q od)) = if s ≈ ty then just (lim , a , length q , od) else nothing
  mergeOf ty _                                       = nothing

  -- the bit, the buffer's length, the held completion
  batchOf : Ty → Maybe (NodeState Δ) → Maybe (Bool × ℕ × Bool)
  batchOf ty (just (batchSync-st {s = s} y b d)) = if s ≈ ty then just (y , length b , d) else nothing
  batchOf ty _                                   = nothing

  opName : AllOp → String
  opName mergeAllᵒ = "merge"
  opName switchᵒ   = "switch"
  opName exhaustᵒ  = "exhaust"

  frameName : ∀ {s u} → Frame Δ s u → String
  frameName (map-f _)            = "map"
  frameName (scan-f _ k)         = "scan#" ++ˢ show k
  frameName (take-f nothing k)   = "take#" ++ˢ show k
  frameName (take-f (just _) k)  = "takeWhile#" ++ˢ show k
  frameName (batchSync-f k)      = "batch#" ++ˢ show k
  frameName (from-inner o k j)   = "from-" ++ˢ opName o ++ˢ "#" ++ˢ show k ++ˢ "/" ++ˢ show j
  frameName (thru-outer o k)     = "thru-" ++ˢ opName o ++ˢ "#" ++ˢ show k

  -- a path's frames, for a report
  skel : ∀ {lo s t} → Path Δ lo s t → String
  skel root             = "root"
  skel (share-sink i _) = "sink" ++ˢ show (toℕ i)
  skel (f ↠[ _ ] p)     = frameName f ++ˢ " " ++ˢ skel p

------------------------------------------------------------------
-- Pairings: every way a clause can be met, as constraints on `π`
------------------------------------------------------------------

-- a key's entry, exactly or as a prefix
Con : Set
Con = NodeId × List NodeId × Bool

-- the entries, and the impl-only nodes no entry may name
Req : Set
Req = List Con × List NodeId

data Res : Set where
  holds  : List Req → Res
  breaks : String → Res

cap : ℕ
cap = 64

ok : Res
ok = holds (([] , []) ∷ [])

pairs pairsFrom : NodeId → List NodeId → Res
pairs     k xs = holds (((k , xs , true) ∷ [] , []) ∷ [])
pairsFrom k xs = holds (((k , xs , false) ∷ [] , []) ∷ [])

apart : NodeId → Res
apart k = holds (([] , k ∷ []) ∷ [])

infixr 6 _⊗_
infixr 5 _⊕_

-- both, every combination
_⊗_ : Res → Res → Res
breaks w ⊗ _         = breaks w
holds as ⊗ breaks w  = breaks w
holds as ⊗ holds bs  =
  holds (take cap (concatMap (λ a → map (λ b → (proj₁ a ++ proj₁ b) , (proj₂ a ++ proj₂ b)) bs) as))

-- either, every way; the first failure is the one reported
_⊕_ : Res → Res → Res
holds as ⊕ holds bs  = holds (take cap (as ++ bs))
holds as ⊕ breaks _  = holds as
breaks _ ⊕ holds bs  = holds bs
breaks w ⊕ breaks _  = breaks w

-- either, both failures reported
_⊘_ : Res → Res → Res
breaks w ⊘ breaks w′ = breaks (w ++ˢ " / " ++ˢ w′)
r        ⊘ r′        = r ⊕ r′

when : Bool → String → Res → Res
when b w r = if b then r else breaks w

on : ∀ {A : Set} → Maybe A → String → (A → Res) → Res
on (just a) w k = k a
on nothing  w k = breaks w

fails : String → Maybe String → Res
fails w (just x) = breaks (w ++ˢ x)
fails w nothing  = ok

anyR : String → List Res → Res
anyR w []       = breaks w
anyR w (r ∷ rs) = r ⊕ anyR w rs

aparts : List NodeId → Res
aparts []       = ok
aparts (k ∷ ks) = apart k ⊗ aparts ks

tag : String → Res → Res
tag p (breaks w) = breaks (p ++ˢ w)
tag p r          = r

-- two constraints on one key, as one
merge : List NodeId × Bool → List NodeId × Bool → Maybe (List NodeId × Bool)
merge (xs , true)  (ys , true)  = if eqListℕ xs ys then just (xs , true) else nothing
merge (xs , true)  (ys , false) = if prefixListℕ ys xs then just (xs , true) else nothing
merge (xs , false) (ys , true)  = if prefixListℕ xs ys then just (ys , true) else nothing
merge (xs , false) (ys , false) =
  if prefixListℕ xs ys then just (ys , false) else if prefixListℕ ys xs then just (xs , false) else nothing

insert : Con → List Con → Maybe (List Con)
insert c [] = just (c ∷ [])
insert (k , x) ((k′ , y) ∷ cs) with k ≡ᵇ k′
... | true  = mapᴹ (λ z → (k , z) ∷ cs) (merge x y)
... | false = mapᴹ ((k′ , y) ∷_) (insert (k , x) cs)

build : List Con → Maybe (List Con)
build []       = just []
build (c ∷ cs) with build cs
... | nothing = nothing
... | just π  = insert c π

-- THE MINIMAL PAIRING IS COMPLETE: `π` is existential, so an entry no
-- clause needs only adds values, and a prefix closed at its shortest
-- is the one that collides with nothing
fits : Req → Bool
fits (cs , us) with build cs
... | nothing = false
... | just π  = unique (concatMap (λ c → proj₁ (proj₂ c)) π)
              ∧ all (λ u → not (any (_≡ᵇ u) (concatMap (λ c → proj₁ (proj₂ c)) π))) us

settle : Res → Maybe String
settle (breaks w) = just w
settle (holds rs) =
  if any fits rs then nothing
  else just ("pi: no pairing fits every row's constraints (" ++ˢ show (length rs) ++ˢ " combinations"
             ++ˢ (if cap ≤ᵇ length rs then ", AT THE CAP)" else ")"))

------------------------------------------------------------------
-- The decider, one store pair
------------------------------------------------------------------

module Decide {n} {Γ : Ctx n} (κ : Kinds n) where

  Γ′ : Ctx (n + n)
  Γ′ = plainᵏ Γ κ

  -- an impl path, its indices packed: the plain path is what recursion
  -- descends, so the impl side is read through views
  IP : Set
  IP = Σ ℕ λ l → Σ Ty λ a → Σ Ty λ b → Path Γ′ l a b

  pk : ∀ {l a b} → Path Γ′ l a b → IP
  pk q = _ , _ , _ , q

  srcTy : IP → Ty
  srcTy (_ , a , _) = a

  vRoot : IP → Bool
  vRoot (_ , _ , _ , root) = true
  vRoot _                  = false

  vSink : IP → Maybe ℕ
  vSink (_ , _ , _ , share-sink j _) = just (toℕ j)
  vSink _                            = nothing

  vMap : IP → Maybe IP
  vMap (_ , _ , _ , (map-f _ ↠[ _ ] q)) = just (pk q)
  vMap _                                = nothing

  -- a frame's step, with the types it was installed at
  Step : Set
  Step = Σ Ty λ a → Σ Ty λ b → FnClo Γ′ a b

  vMapF : IP → Maybe (Step × IP)
  vMapF (_ , _ , _ , (map-f F ↠[ _ ] q)) = just ((_ , _ , F) , pk q)
  vMapF _                                = nothing

  vScanF : IP → Maybe (Step × NodeId × IP)
  vScanF (_ , _ , _ , (scan-f F k ↠[ _ ] q)) = just ((_ , _ , F) , k , pk q)
  vScanF _                                   = nothing

  stepAt : ∀ a′ b′ → Step → Maybe (FnClo Γ′ a′ b′)
  stepAt a′ b′ (a , b , F) with a ≟ᵗ a′ | b ≟ᵗ b′
  ... | yes refl | yes refl = just F
  ... | _        | _        = nothing

  vScan : IP → Maybe (NodeId × IP)
  vScan (_ , _ , _ , (scan-f _ k ↠[ _ ] q)) = just (k , pk q)
  vScan _                                   = nothing

  vTake : IP → Maybe (NodeId × IP)
  vTake (_ , _ , _ , (take-f (just _) k ↠[ _ ] q)) = just (k , pk q)
  vTake _                                          = nothing

  vBatch : IP → Maybe (NodeId × IP)
  vBatch (_ , _ , _ , (batchSync-f k ↠[ _ ] q)) = just (k , pk q)
  vBatch _                                      = nothing

  vFrom : IP → Maybe (AllOp × NodeId × NodeId × IP)
  vFrom (_ , _ , _ , (from-inner o m j ↠[ _ ] q)) = just (o , m , j , pk q)
  vFrom _                                         = nothing

  vThru : IP → Maybe (AllOp × NodeId × IP)
  vThru (_ , _ , _ , (thru-outer o m ↠[ _ ] q)) = just (o , m , pk q)
  vThru _                                       = nothing

  finOf : ℕ → Maybe (Fin n)
  finOf k = go (allFin n)
    where
      go : List (Fin n) → Maybe (Fin n)
      go []       = nothing
      go (i ∷ is) = if toℕ i ≡ᵇ k then just i else go is

  -- `V`, with an observable related to anything
  V? : ∀ t → Val Γ′ (plainᵗ t) → Val Γ t → Bool
  V? unitᵗ     _        _        = true
  V? boolᵗ     v        w        = eqB v w
  V? natᵗ      v        w        = v ≡ᵇ w
  V? uniqᵗ     v        w        = v ≡ᵇ w
  V? (s ×ᵗ t)  (a , b)  (c , d)  = V? s a c ∧ V? t b d
  V? (s +ᵗ t)  (inj₁ a) (inj₁ c) = V? s a c
  V? (s +ᵗ t)  (inj₂ b) (inj₂ d) = V? t b d
  V? (s +ᵗ t)  _        _        = false
  V? (listᵗ t) []       []       = true
  V? (listᵗ t) (v ∷ vs) (w ∷ ws) = V? t v w ∧ V? (listᵗ t) vs ws
  V? (listᵗ t) _        _        = false
  V? (obs t)   _        _        = true

  ----------------------------------------------------------------
  -- THE CLOSURE RELATIONS, DECIDED ON SAMPLES.  `Lifts`, `ScanLifts`
  -- and `CutLifts` quantify over every related input; these read the
  -- two live steps at a few related values per type, so a red is a
  -- counterexample and a green covers the samples.  An observable
  -- sample is `emptyᵉ` on both sides, related only as `V?` relates one.
  ----------------------------------------------------------------

  samp : ∀ t → List (Val Γ′ (plainᵗ t) × Val Γ t)
  samp unitᵗ     = (tt , tt) ∷ []
  samp boolᵗ     = (true , true) ∷ (false , false) ∷ []
  samp natᵗ      = (0 , 0) ∷ (1 , 1) ∷ (3 , 3) ∷ []
  samp uniqᵗ     = (0 , 0) ∷ (2 , 2) ∷ []
  samp (s ×ᵗ t)  =
    take 4 (concatMap (λ a → map (λ b → (proj₁ a , proj₁ b) , (proj₂ a , proj₂ b)) (samp t)) (samp s))
  samp (s +ᵗ t)  = map (λ a → inj₁ (proj₁ a) , inj₁ (proj₂ a)) (take 2 (samp s))
                ++ map (λ b → inj₂ (proj₁ b) , inj₂ (proj₂ b)) (take 2 (samp t))
  samp (listᵗ t) = ([] , []) ∷ map (λ xs → map proj₁ xs , map proj₂ xs) (take 1 (samp t) ∷ take 2 (samp t) ∷ [])
  samp (obs t)   = (([] , emptyᵉ , []ᵉ) , ([] , emptyᵉ , []ᵉ)) ∷ []

  valEv : ∀ {a} → Val Γ′ a → Val Γ′ (instEventᵗ uniqᵗ a)
  valEv v = inj₂ (inj₁ v)

  -- an emit carrying values, bare and between an init and a close
  bare wrapped : ∀ t → List (Val Γ′ (plainᵗ t)) → Val Γ′ (emitᵗ t)
  bare    t vs = map valEv vs , 7 , 9 , inj₂ (inj₁ tt)
  wrapped t vs = (inj₁ 7 ∷ map valEv vs ++ inj₂ (inj₂ (inj₁ (7 , inj₂ (inj₂ tt)))) ∷ []) , 7 , 9 , inj₁ tt

  emits : ∀ t → List (Val Γ′ (emitᵗ t) × List (Val Γ t))
  emits t = concatMap (λ xs → (bare t (map proj₁ xs) , map proj₂ xs) ∷ (wrapped t (map proj₁ xs) , map proj₂ xs) ∷ [])
                      ([] ∷ take 1 (samp t) ∷ take 2 (samp t) ∷ [])

  instE : ∀ t → Val Γ′ (emitᵗ t) → ℕ
  instE t e = proj₁ (proj₂ e)

  emitRel? : ∀ t → Val Γ′ (emitᵗ t) → List (Val Γ t) → Bool
  emitRel? t e′ = pw (map proj₂ (emitValues (decodeEmit {Γ = Γ′} {a = plainᵗ t} e′)))
    where
      pw : List (Val Γ′ (plainᵗ t)) → List (Val Γ t) → Bool
      pw []       []       = true
      pw (x ∷ xs) (y ∷ ys) = V? t x y ∧ pw xs ys
      pw _        _        = false

  lifts? : ∀ s u → FnClo Γ′ (emitᵗ s) (emitᵗ u) → FnClo Γ s u → Bool
  lifts? s u F′ F = all (λ (e′ , vs) → let o = applyClo F′ e′ in
    emitRel? u o (map (applyClo F) vs) ∧ (instE u o ≡ᵇ instE s e′)) (emits s)

  scanLifts? : ∀ s u → FnClo Γ′ (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u) → FnClo Γ (u ×ᵗ s) u
             → List (Val Γ′ (plainᵗ u) × Val Γ u) → Val Γ′ (emitᵗ u) → Bool
  scanLifts? s u F′ F as em = all (λ (a′ , a) → all (λ (e′ , vs) →
    let o = applyClo F′ ((a′ , em) , e′) ; r = scanVals F a vs in
    V? u (proj₁ o) (proj₂ r) ∧ emitRel? u (proj₂ o) (proj₁ r) ∧ (instE u (proj₂ o) ≡ᵇ instE s e′)) (emits s)) as

  -- the first sample a cut step fails, named by its plain budget, the
  -- number of values it carried and the conjunct
  cutLifts? : ∀ B s → (Val Γ′ B → ℕ → Bool) → FnClo Γ′ (CutS B s ×ᵗ emitᵗ s) (CutS B s)
            → Maybe (FnClo Γ s boolᵗ) → List (Val Γ′ B × ℕ) → Val Γ′ (emitᵗ s) → Maybe String
  cutLifts? B s bud F′ P bs em = firstJ (concatMap (λ (b′ , b) → concatMap (λ os → map (λ (e′ , vs) →
    let o = applyClo F′ ((b′ , (false , (os , em))) , e′) ; r = takeVals P b vs
        at = "budget " ++ˢ show b ++ˢ ", " ++ˢ show (length vs) ++ˢ " values, " ++ˢ show (length os) ++ˢ " owed: " in
    if not (bud b′ b) then nothing
    else if not (proj₂ (proj₂ r) ∨ bud (proj₁ o) (proj₁ (proj₂ r))) then just (at ++ˢ "budget after")
    else if not (eqB (proj₁ (proj₂ o)) (proj₂ (proj₂ r))) then just (at ++ˢ "cut flag")
    else if not (emitRel? s (proj₂ (proj₂ (proj₂ o))) (proj₁ r)) then just (at ++ˢ "prefix")
    else if not (instE s (proj₂ (proj₂ (proj₂ o))) ≡ᵇ instE s e′) then just (at ++ˢ "instant")
    else nothing) (emits s)) ([] ∷ (4 ∷ []) ∷ [])) bs)
    where
      firstJ : List (Maybe String) → Maybe String
      firstJ []             = nothing
      firstJ (just w ∷ _)   = just w
      firstJ (nothing ∷ ws) = firstJ ws

  -- a one-lane merge at rest: no limit, nothing queued, its outer done
  lane : Maybe (Maybe ℕ × ℕ × ℕ × Bool) → Bool
  lane (just (nothing , _ , q , od)) = (q ≡ᵇ 0) ∧ od
  lane _                             = false

  module Nodes (NP : List (NodeId × NodeState Γ)) (NI : List (NodeId × NodeState Γ′)) where

    P : NodeId → Maybe (NodeState Γ)
    P k = lookupNode k NP

    I : NodeId → Maybe (NodeState Γ′)
    I k = lookupNode k NI

    curR : Maybe NodeId → Maybe NodeId → Res
    curR nothing  nothing   = ok
    curR (just j) (just j′) = pairs j (j′ ∷ [])
    curR _        _         = breaks "flattener: current inners unpaired"

    innerPair : Maybe (NodeId × NodeId) → Res
    innerPair nothing          = ok
    innerPair (just (j , j′)) = pairs j (j′ ∷ [])

    mshow : Maybe ℕ → ℕ → ℕ → Bool → String
    mshow lim a q od = "(limit " ++ˢ maybe′ show "none" lim ++ˢ ", active " ++ˢ show a ++ˢ ", queued " ++ˢ show q
                       ++ˢ ", outer " ++ˢ (if od then "done" else "live") ++ˢ ")"

    -- `Flattener` and `FlatNodes`, and `InnerPair` where an inner is named
    flatNodes : Ty → AllOp → Maybe (NodeState Γ) → Maybe (NodeState Γ′) → Res
    flatNodes u op (just (mergeAll-st {t = s} lim a q od)) (just (mergeAll-st {t = s′} lim′ a′ q′ od′)) =
      when (eqOp op mergeAllᵒ ∧ (s ≈ u) ∧ (s′ ≈ emitᵗ u) ∧ eqMb lim lim′ ∧ (a ≡ᵇ a′) ∧ (length q ≡ᵇ length q′) ∧ eqB od od′)
           ("flattener: merge nodes unrelated: plain " ++ˢ mshow lim a (length q) od ++ˢ ", impl " ++ˢ mshow lim′ a′ (length q′) od′) ok
    flatNodes u op (just (switch-st cur od)) (just (switch-st cur′ od′)) =
      when (eqOp op switchᵒ ∧ eqB od od′) "flattener: switch nodes unrelated" (curR cur cur′)
    flatNodes u op (just (exhaust-st ia od)) (just (exhaust-st ia′ od′)) =
      when (eqOp op exhaustᵒ ∧ eqB ia ia′ ∧ eqB od od′) "flattener: exhaust nodes unrelated" ok
    flatNodes u op _ _ = breaks "flattener: node kinds"

    flat : Ty → AllOp → AllOp → NodeId → NodeId → NodeId → Res → Maybe (NodeId × NodeId) → Res
    flat u op op′ m m′ ks key jj =
      when (eqOp op op′) "flattener: ops differ"
        (key ⊗ flatNodes u op (P m) (I m′) ⊗ innerPair jj ⊗ on (cellOf (FlatSᵗ u) (I ks)) "flattener: restamp cell" (λ _ → ok))

    -- the impl's leading lanes, peeled every way: each with the lanes it took
    mutual
      peel : ∀ {l a b} → Ty → Path Γ′ l a b → List (List NodeId × IP)
      peel u q = ([] , pk q) ∷ more u q

      more : ∀ {l a b} → Ty → Path Γ′ l a b → List (List NodeId × IP)
      more u (from-inner mergeAllᵒ mL jL ↠[ _ ] Q) =
        if lane (mergeOf (emitᵗ u) (I mL)) then map (λ x → (mL ∷ jL ∷ proj₁ x) , proj₂ x) (peel u Q) else []
      more u _ = []

    innerR : Ty → AllOp → NodeId → NodeId → (IP → Res) → IP → Res
    innerR u op m j k q =
      on (vFrom q) "inner: no lane" λ (op′ , m′ , j′ , q₁) →
      on (vScan q₁) "inner: no restamp scan" λ (ks , q₂) →
      on (vMap q₂) "inner: no restamp map" λ q₃ →
        flat u op op′ m m′ ks (pairsFrom m (m′ ∷ ks ∷ [])) (just (j , j′)) ⊗ k q₃

    deferR : Ty → AllOp → NodeId → NodeId → (IP → Res) → IP → Res
    deferR u op nid j k q =
      when (eqOp op mergeAllᵒ) "deferInner: op" (
      on (vFrom q) "deferInner: no marker merge" λ (o₂ , m2 , j2 , q₁) →
      on (vMap q₁) "deferInner: no restamp" λ q₂ →
      on (vFrom q₂) "deferInner: no hop" λ (o′ , nid′ , j′ , q₃) →
      when (eqOp o₂ mergeAllᵒ ∧ eqOp o′ mergeAllᵒ) "deferInner: ops" (
        pairs nid (nid′ ∷ []) ⊗ pairs j (j′ ∷ m2 ∷ j2 ∷ []) ⊗
        on (mergeOf u (P nid)) "deferInner: plain hop node" (λ (l₀ , a , q₀ , d₀) →
        on (mergeOf (emitᵗ u) (I nid′)) "deferInner: impl hop node" λ (l₁ , a₁ , q₁ , d₁) →
        on (mergeOf (emitᵗ u) (I m2)) "deferInner: marker node" λ (l₂ , a₂ , q₂ , d₂) →
        when (is-nothing l₀ ∧ is-nothing l₁ ∧ is-nothing l₂ ∧ (q₀ ≡ᵇ 0) ∧ (q₁ ≡ᵇ 0) ∧ (q₂ ≡ᵇ 0) ∧ d₀ ∧ d₁ ∧ d₂
              ∧ (a ≡ᵇ a₁) ∧ (a ≡ᵇ a₂) ∧ (a ≤ᵇ 1)) "deferInner: hop nodes unrelated" ok)
        ⊗ k q₃))

    outerElem : Ty → AllOp → NodeId → (IP → Res) → IP → Res
    outerElem u op m k q₁ =
      on (vThru q₁) "outerElem: no flattener" λ (op′ , m′ , q₂) →
      on (vScan q₂) "outerElem: no restamp scan" λ (ks , q₃) →
      on (vMap q₃) "outerElem: no restamp map" λ q₄ →
        flat u op op′ m m′ ks (pairs m (m′ ∷ ks ∷ [])) nothing ⊗ k q₄

    outerExplode : Ty → AllOp → NodeId → (IP → Res) → IP → Res
    outerExplode u op m k q₁ =
      on (vMap q₁) "outerExplode: no pair map" λ q₂ →
      on (vThru q₂) "outerExplode: no explode merge" λ (oX , mX , q₃) →
      on (vThru q₃) "outerExplode: no flattener" λ (op′ , m′ , q₄) →
      on (vScan q₄) "outerExplode: no restamp scan" λ (ks , q₅) →
      on (vMap q₅) "outerExplode: no restamp map" λ q₆ →
        when (eqOp oX mergeAllᵒ) "outerExplode: explode op"
          (flat u op op′ m m′ ks (pairs m (m′ ∷ ks ∷ mX ∷ [])) nothing ⊗ k q₆)

    -- `PathRel`, with the impl tail's element type checked at every step
    mutual
      path : ∀ {lo s t} → Path Γ lo s t → IP → Res
      path {s = s} p q = when (srcTy q ≈ emitᵗ s) "path: impl element type" (path′ p q)

      path′ : ∀ {lo s t} → Path Γ lo s t → IP → Res
      path′ root q = when (vRoot q) "root: impl path goes on" ok
      path′ (share-sink i _) q =
        on (vSink q) "sink: impl path is no sink" λ j →
          when (isShared (lookup κ i) ∧ (j ≡ᵇ n + toℕ i)) "sink: slot" ok
      path′ (_↠[_]_ {s = s} {u = u} (map-f F) _ p) q =
        on (vMapF q) "map: no impl map" λ (St , q₁) →
        on (stepAt (emitᵗ s) (emitᵗ u) St) "map: impl step type" λ F′ →
          when (lifts? s u F′ F) "map: Lifts fails" ok ⊗ path p q₁
      path′ (_↠[_]_ {s = s} {u = u} (scan-f F k) _ p) q =
        on (vScanF q) "scan: no impl scan" λ (St , k′ , q₁) →
        on (vMap q₁) "scan: no projection" λ q₂ →
          pairs k (k′ ∷ []) ⊗
          on (cellOf u (P k)) "scan: plain cell" (λ a →
            on (cellOf (ScanAᵗ u) (I k′)) "scan: impl cell" λ c →
            on (stepAt (ScanAᵗ u ×ᵗ emitᵗ s) (ScanAᵗ u) St) "scan: impl step type" λ F′ →
              when (V? u (proj₁ c) a) "scan: cells unrelated"
                (when (scanLifts? s u F′ F ((proj₁ c , a) ∷ samp u) (proj₂ c)) "scan: ScanLifts fails" ok)) ⊗
          path p q₂
      path′ (_↠[_]_ {s = s} (take-f nothing k) _ p) q =
        on (vScanF q) "take: no cut scan" λ (St , k₁ , q₁) →
        on (vTake q₁) "take: no cut test" λ (k₂ , q₂) →
        on (vMap q₂) "take: no cut projection" λ q₃ →
        on (vFrom q₃) "take: no zero merge" λ (o , m , j , q₄) →
          when (eqOp o mergeAllᵒ) "take: zero merge op" ((
            pairs k (k₁ ∷ k₂ ∷ m ∷ j ∷ []) ⊗
            on (takeOf (P k)) "take: plain budget" (λ b →
              on (cellOf (CutS natᵗ s) (I k₁)) "take: cut cell" λ c →
              on (stepAt (CutS natᵗ s ×ᵗ emitᵗ s) (CutS natᵗ s) St) "take: impl step type" λ F₁ →
                when ((proj₁ c ≡ᵇ b) ∧ (1 ≤ᵇ b) ∧ not (proj₁ (proj₂ c))) "take: cut cell unrelated"
                  (fails "take: CutLifts fails at "
                     (cutLifts? natᵗ s (λ b′ b → (b′ ≡ᵇ b) ∧ (1 ≤ᵇ b)) F₁ nothing (map (λ x → x , x) (b ∷ 1 ∷ 2 ∷ 3 ∷ []))
                       (proj₂ (proj₂ (proj₂ c)))))) ⊗
            when (is (takeOf (I k₂)) 1) "take: impl test budget" ok ⊗
            on (mergeOf (emitᵗ s) (I m)) "take: zero merge node" (λ (l , a , ql , od) →
              when (is-nothing l ∧ (a ≤ᵇ 1) ∧ (ql ≡ᵇ 0) ∧ od) "take: zero merge state" ok) ⊗
            path p q₄)
          ⊘ (pairs k (k₁ ∷ k₂ ∷ m ∷ j ∷ []) ⊗
             when (is (takeOf (P k)) 0 ∧ is (takeOf (I k₂)) 0) "take: not spent" ok ⊗
             path p q₄))
      path′ (_↠[_]_ {s = s} (take-f (just Pr) k) _ p) q =
        on (vScanF q) "takeWhile: no cut scan" λ (St , k₁ , q₁) →
        on (vTake q₁) "takeWhile: no cut test" λ (k₂ , q₂) →
        on (vMap q₂) "takeWhile: no cut projection" λ q₃ →
          (pairs k (k₁ ∷ k₂ ∷ []) ⊗
          when (is (takeOf (P k)) 1) "takeWhile: plain budget" ok ⊗
          on (cellOf (CutS unitᵗ s) (I k₁)) "takeWhile: cut cell" (λ c →
            on (stepAt (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s) St) "takeWhile: impl step type" λ F₁ →
              when (not (proj₁ (proj₂ c))) "takeWhile: cut cell unrelated"
                (fails "takeWhile: CutLifts fails at "
                   (cutLifts? unitᵗ s (λ _ b → b ≡ᵇ 1) F₁ (just Pr) ((tt , 1) ∷ []) (proj₂ (proj₂ (proj₂ c)))))) ⊗
          when (is (takeOf (I k₂)) 1) "takeWhile: impl test budget" ok ⊗
          path p q₃)
          ⊘ (pairs k (k₁ ∷ k₂ ∷ []) ⊗
             when (is (takeOf (P k)) 0 ∧ is (takeOf (I k₂)) 0) "takeWhile: not spent" ok ⊗
             path p q₃)
      path′ (batchSync-f _ ↠[ _ ] p) q = breaks "batchSync: no plain clause"
      path′ (_↠[_]_ {u = u} (thru-outer op m) _ p) q =
        on (vMap q) "outer: no element map" λ q₁ →
          outerElem u op m (path p) q₁ ⊘ outerExplode u op m (path p) q₁
      path′ (_↠[_]_ {s = u} (from-inner op m j) _ p) q =
        anyR "inner: no peel fits"
          (map (λ uq → aparts (proj₁ uq) ⊗ (innerR u op m j (path p) (proj₂ uq) ⊘ deferR u op m j (path p) (proj₂ uq)))
               (peel u (proj₂ (proj₂ (proj₂ q)))))

    -- `InputBlock`, then the tail
    blk : Ty → IP → (IP → Res) → Res
    blk a q k =
      on (vMap q) "block: no inr map" λ q₁ →
      on (vFrom q₁) "block: no marked merge" λ (o₁ , m1 , j1 , q₂) →
      on (vBatch q₂) "block: no bracket" λ (b , q₃) →
      on (vMap q₃) "block: no stamp" λ q₄ →
      on (vMap q₄) "block: no pair map" λ q₅ →
      on (vThru q₅) "block: no flattening merge" λ (o₂ , m2 , q₆) →
        when (eqOp o₁ mergeAllᵒ ∧ eqOp o₂ mergeAllᵒ) "block: ops" (
          on (mergeOf (unitᵗ +ᵗ a) (I m1)) "block: marked merge node" (λ (l , a₁ , ql , od) →
            when (is-nothing l ∧ (a₁ ≤ᵇ 1) ∧ (ql ≡ᵇ 0) ∧ od) "block: marked merge state" ok) ⊗
          on (batchOf (unitᵗ +ᵗ a) (I b)) "block: bracket node" (λ (y , bl , d) →
            when (not y ∧ (bl ≡ᵇ 0) ∧ not d) "block: bracket state" ok) ⊗
          on (mergeOf (machineEmitᵗ a) (I m2)) "block: flattening merge node" (λ (l , a₂ , ql , _) →
            when (is-nothing l ∧ (a₂ ≡ᵇ 0) ∧ (ql ≡ᵇ 0)) "block: flattening merge state" ok) ⊗
          apart m1 ⊗ apart j1 ⊗ apart b ⊗ apart m2 ⊗ k q₆)

    -- `SrcPair`: one place in both live lists
    srcPair : List (LiveSource Γ) → List (LiveSource Γ′) → Source → Source → Ty → Ty → Bool
    srcPair (l ∷ LP) (l′ ∷ LI) s s′ x x′ =
      ((LiveSource.source l ≡ᵇ s) ∧ (LiveSource.source l′ ≡ᵇ s′) ∧ (LiveSource.elemTy l ≈ x) ∧ (LiveSource.elemTy l′ ≈ x′))
      ∨ srcPair LP LI s s′ x x′
    srcPair _ _ _ _ _ _ = false

    module Rows (LP : List (LiveSource Γ)) (LI : List (LiveSource Γ′)) where

      deferRow : ∀ {lo s t} → Source → Source → Path Γ lo s t → IP → Res
      deferRow src src′ (_↠[_]_ {u = u} (thru-outer mergeAllᵒ nid) _ p) q =
        when (srcPair LP LI src src′ (echoᵗ u) (echoᵗ (emitᵗ u))) "defer: source pair" (
        on (vThru q) "defer: no impl hop" λ (o′ , nid′ , q₁) →
          when (eqOp o′ mergeAllᵒ) "defer: hop op" (
            pairs nid (nid′ ∷ []) ⊗
            on (mergeOf u (P nid)) "defer: plain hop node" (λ st → when (fresh st) "defer: plain hop state" ok) ⊗
            on (mergeOf (emitᵗ u) (I nid′)) "defer: impl hop node" (λ st → when (fresh st) "defer: impl hop state" ok) ⊗
            path p q₁))
        where
          fresh : Maybe ℕ × ℕ × ℕ × Bool → Bool
          fresh (l , a , ql , od) = is-nothing l ∧ (a ≡ᵇ 0) ∧ (ql ≡ᵇ 0) ∧ not od
      deferRow _ _ _ _ = breaks "defer: plain path is no hop"

      -- `RowRel`
      row : ∀ {t} → RegRow Γ t → RegRow Γ′ (emitᵗ t) → Res
      row (_ , atSlot i , s , p) (_ , atSlot j , s′ , q) =
        when ((isHot (lookup κ i) ∨ isShared (lookup κ i)) ∧ (toℕ j ≡ᵇ n + toℕ i)) "read: slot"
          (when ((s ≈ lookup Γ i) ∧ (s′ ≈ emitᵗ (lookup Γ i))) "read: types"
            (on (vMap (pk q)) "read: no restamp" (path p)))
      row (_ , atDyn src _ , s , p) (_ , atDyn src′ _ , s′ , q) =
        when (srcPair LP LI src src′ s (plainᵗ s) ∧ (s′ ≈ plainᵗ s)) "cold: source pair" (blk (plainᵗ s) (pk q) (path p))
        ⊘ deferRow src src′ p (pk q)
      row _ _ = breaks "row: source shapes differ"

      -- `MachRow`
      mach : ∀ {t} → RegRow Γ′ (emitᵗ t) → Res
      mach (_ , atSlot j , s′ , q) =
        on (finOf (toℕ j)) "mach: not a raw slot's row" λ i →
          when (isHot (lookup κ i) ∧ (s′ ≈ plainᵗ (lookup Γ i))) "mach: kind" (
            blk (plainᵗ (lookup Γ i)) (pk q) λ q′ →
              on (vSink q′) "mach: no share sink" λ j′ → when (j′ ≡ᵇ n + toℕ i) "mach: share slot" ok)
      mach _ = breaks "mach: not a slot row"

      rowSkel : ∀ {t} → ℕ → RegRow Γ t → RegRow Γ′ (emitᵗ t) → String
      rowSkel k (_ , _ , _ , p) (_ , _ , _ , q) =
        "row " ++ˢ show k ++ˢ " [plain: " ++ˢ skel p ++ˢ "] [impl: " ++ˢ skel q ++ˢ "]: "

      -- `RegRel`, the impl's own rows anywhere between
      reg : ∀ {t} → ℕ → List (RegRow Γ t) → List (RegRow Γ′ (emitᵗ t)) → Res
      reg k []       []         = ok
      reg k []       (r′ ∷ rs′) = mach r′ ⊗ reg k [] rs′
      reg k (r ∷ rs) []         = breaks ("row " ++ˢ show k ++ˢ ": no impl row left [plain: " ++ˢ skel (proj₂ (proj₂ (proj₂ r))) ++ˢ "]")
      reg k (r ∷ rs) (r′ ∷ rs′) =
        (tag (rowSkel k r r′) (row r r′) ⊗ reg (suc k) rs rs′) ⊕ (mach r′ ⊗ reg k (r ∷ rs) rs′)

  ----------------------------------------------------------------
  -- The other fields
  ----------------------------------------------------------------

  pend : ∀ t → List (Val Γ′ (plainᵗ t)) → List (Val Γ t) → Bool
  pend t []       []       = true
  pend t (v ∷ vs) (w ∷ ws) = V? t v w ∧ pend t vs ws
  pend t _        _        = false

  -- `Src`'s data arm: the same values at the plain type, a slot's at its slot's
  dataSrc : LiveSource Γ → LiveSource Γ′ → Bool
  dataSrc l l′ with LiveSource.elemTy l′ ≟ᵗ plainᵗ (LiveSource.elemTy l)
  ... | yes eq =
    pend (LiveSource.elemTy l) (map (λ p → subst (Val Γ′) eq (proj₂ p)) (LiveSource.pending l′)) (map proj₂ (LiveSource.pending l))
    ∧ all (λ i → not (LiveSource.source l ≡ᵇ toℕ i) ∨ (LiveSource.elemTy l ≈ lookup Γ i)) (allFin n)
  ... | no _ = false

  -- `Src`'s hop arm: a minted source, every pending value a hop
  hops : ∀ {m} {Δ : Ctx m} u (l : LiveSource Δ) → Bool
  hops {Δ = Δ} u l = all (λ p → hop (castV (LiveSource.elemTy l) (echoᵗ u) (proj₂ p))) (LiveSource.pending l)
    where
      hop : Maybe (Val Δ (echoᵗ u)) → Bool
      hop (just (inj₁ _ , inj₂ _)) = true
      hop _                        = false

  deferSrc : LiveSource Γ → LiveSource Γ′ → Bool
  deferSrc l l′ with echoOf (LiveSource.elemTy l)
  ... | nothing = false
  ... | just u  = (n <ᵇ LiveSource.source l) ∧ (LiveSource.elemTy l′ ≈ echoᵗ (emitᵗ u))
                ∧ (length (LiveSource.pending l) ≡ᵇ length (LiveSource.pending l′)) ∧ hops u l ∧ hops (emitᵗ u) l′

  pointwise : ∀ {A B : Set} → (A → B → Bool) → List A → List B → Bool
  pointwise R []       []       = true
  pointwise R (x ∷ xs) (y ∷ ys) = R x y ∧ pointwise R xs ys
  pointwise R _        _        = false

  kindAt : ℕ → Maybe Kind
  kindAt s = mapᴹ (lookup κ) (finOf s)

  srcNum : LiveSource Γ → LiveSource Γ′ → Bool
  srcNum l l′ =
    ((s <ᵇ n) ∧ hotAt (kindAt s) ∧ (s′ ≡ᵇ s)) ∨ ((n <ᵇ s) ∧ ((n + n) <ᵇ s′))
    where
      s s′ : Source
      s  = LiveSource.source l
      s′ = LiveSource.source l′
      hotAt : Maybe Kind → Bool
      hotAt (just k) = isHot k
      hotAt nothing  = false

  ranked : LiveSource Γ → LiveSource Γ′ → List (LiveSource Γ) → List (LiveSource Γ′) → Bool
  ranked l l′ = pointwise (λ x x′ → eqB (LiveSource.ordinal l <ᵇ LiveSource.ordinal x) (LiveSource.ordinal l′ <ᵇ LiveSource.ordinal x′))

  sync? : List (LiveSource Γ) → List (LiveSource Γ′) → Bool
  sync? []       []         = true
  sync? (l ∷ ls) (l′ ∷ ls′) = eqListℕ (ticks l) (ticks l′) ∧ ranked l l′ ls ls′ ∧ sync? ls ls′
  sync? _        _          = false

  module Fields {t} {ep : Closed Γ t} {ei : Closed Γ′ (emitᵗ t)}
                (sP : Sched Γ) (stP : EvalSt ep) (sI : Sched Γ′) (stI : EvalSt ei) where

    LP : List (LiveSource Γ)
    LP = Sched.live sP
    LI : List (LiveSource Γ′)
    LI = Sched.live sI
    RP : List (RegRow Γ t)
    RP = EvalSt.registry stP
    RI : List (RegRow Γ′ (emitᵗ t))
    RI = EvalSt.registry stI
    CP CI SP SI : List Source
    CP = EvalSt.completedSources stP
    CI = EvalSt.completedSources stI
    SP = EvalSt.connectedShares stP
    SI = EvalSt.connectedShares stI

    -- `LatchRel`, at slot `i`
    latchAt : Kind → ℕ → Bool
    latchAt hotᵏ    i = eqB (memberSource i CP) (memberSource i CI)
                      ∧ eqB (memberSource (n + i) CI) (memberSource i CI ∧ memberSource (n + i) SI)
    latchAt sharedᵏ i = eqB (memberSource i CP) (memberSource (n + i) CI)
                      ∧ eqB (memberSource i SP) (memberSource (n + i) SI)
    latchAt coldᵏ   i = true

    -- `Census`, at slot `i`: the raw row once and connected, or neither row and a spent share's slot done
    censusAt : Kind → ℕ → Bool
    censusAt hotᵏ i =
      ((srcCount i RI ≡ᵇ 1) ∧ memberSource (n + i) SI)
      ∨ ((srcCount i RI ≡ᵇ 0) ∧ (srcCount (n + i) RI ≡ᵇ 0) ∧ (not (memberSource (n + i) SI) ∨ memberSource i CI))
    censusAt _    i = true

    -- a reader's row at a stamped slot is exempt
    stamped : RegRow Γ′ (emitᵗ t) → Bool
    stamped (_ , atSlot k , _) = n ≤ᵇ toℕ k
    stamped _                  = false

    owned : Bool
    owned = all (λ (x , r) → stamped r ∨ all (λ j → all (λ (y , r′) → not (pathHasNode j (proj₂ (proj₂ (proj₂ r′)))) ∨ (proj₁ r′ ≡ᵇ proj₁ r))
                                                         (indexed 0 RI))
                                             (blockNodes (proj₂ (proj₂ (proj₂ r)))))
                (indexed 0 RI)

    -- every field but the rows, first failure named
    plain : List (String × Bool)
    plain =
        ("sources" , pointwise (λ l l′ → dataSrc l l′ ∨ deferSrc l l′) LP LI)
      ∷ ("numbers" , pointwise srcNum LP LI)
      ∷ ("distinct" , unique (map LiveSource.source LP) ∧ unique (map LiveSource.source LI))
      ∷ ("sync" , sync? LP LI)
      ∷ ("latches" , all (λ i → latchAt (lookup κ i) (toℕ i)) (allFin n))
      ∷ ("bounded" , all (λ l → LiveSource.source l <ᵇ counter (Sched.mint sP) sourceᵏ) LP
                   ∧ all (λ l → LiveSource.source l <ᵇ counter (Sched.mint sI) sourceᵏ) LI)
      ∷ ("swept" , pointwise (λ l l′ → eqB (guardOf RP l) (guardOf RI l′)) LP LI)
      ∷ ("uncut" , all (λ r → not (any (_≡ᵇ proj₁ r) (EvalSt.cancelled stP))) RP
                 ∧ all (λ r → not (any (_≡ᵇ proj₁ r) (EvalSt.cancelled stI))) RI)
      ∷ ("rids" , unique (map proj₁ RP) ∧ unique (map proj₁ RI))
      ∷ ("fresh-ids" , all (λ r → proj₁ r <ᵇ counter (Sched.mint sP) regᵏ) RP
                     ∧ all (λ r → proj₁ r <ᵇ counter (Sched.mint sI) regᵏ) RI)
      ∷ ("above" , all (λ r → aboveᵇ (proj₁ (proj₂ r))) RP ∧ all (λ r → aboveᵇ (proj₁ (proj₂ r))) RI)
      ∷ ("census" , all (λ i → censusAt (lookup κ i) (toℕ i)) (allFin n))
      ∷ ("owned" , owned)
      ∷ []

    firstFail : List (String × Bool) → Maybe String
    firstFail []               = nothing
    firstFail ((w , b) ∷ fs) = if b then firstFail fs else just w

    verdict : Maybe String
    verdict with firstFail plain
    ... | just w  = just w
    ... | nothing = settle (Nodes.Rows.reg (EvalSt.nodes stP) (EvalSt.nodes stI) LP LI 0 RP RI)

  store? : ∀ {t} {ep : Closed Γ t} {ei : Closed Γ′ (emitᵗ t)} → Sched Γ → EvalSt ep → Sched Γ′ → EvalSt ei → Maybe String
  store? sP stP sI stI = Fields.verdict sP stP sI stI

------------------------------------------------------------------
-- The trace: each run's state after its subscribe and after each
-- arrival, the drain's own builders kept rather than its streams
------------------------------------------------------------------

mutual
  states! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e) ({-@0-}ru : Rule sched st) → List (Sched Γ × EvalSt e)
  states! zero    sched st ru = []
  states! (suc k) sched st ru = statesOn k sched st ru (sched-next sched) refl

  statesOn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (k : Fuel) (sched : Sched Γ) (st : EvalSt e) ({-@0-}ru : Rule sched st)
           → (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) ({-@0-}eqn : sched-next sched ≡ x) → List (Sched Γ × EvalSt e)
  statesOn k sched st ru (inj₁ _)            eqn = []
  statesOn k sched st ru (inj₂ (a , sched′)) eqn = thenS k (cascade! a sched′ st (pop-rule eqn ru))

  thenS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {D : Stream Γ t × Sched Γ × EvalSt e → Set} (k : Fuel)
          (r : Σ⁰ (Stream Γ t × Sched Γ × EvalSt e) λ r → D r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
        → List (Sched Γ × EvalSt e)
  thenS k ((_ , sched′ , st′) , _ , ru′) = (sched′ , st′) ∷ states! k sched′ st′ ru′

trace : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) → List (Sched Γ × EvalSt e)
trace fuel e ins = thenS fuel (subscribe! e ins)

-- THE TWO TRACES, BOUNDARY BY BOUNDARY: the first boundary whose stores
-- are unrelated, or a run that stopped where the other did not
lockstep : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
         → ℕ → List (Sched Γ × EvalSt ep) → List (Sched (plainᵏ Γ κ) × EvalSt ei) → Bool × String
lockstep κ k [] [] = true , "stores related at all " ++ˢ show k ++ˢ " boundaries"
lockstep κ k ((sP , stP) ∷ ps) ((sI , stI) ∷ is) with Decide.store? κ sP stP sI stI
... | nothing = lockstep κ (suc k) ps is
... | just w  = false , "boundary " ++ˢ show k ++ˢ " (0 is the subscribe): " ++ˢ w
lockstep κ k _ _ = false , "lockstep: one run stopped at boundary " ++ˢ show k ++ˢ " and the other did not"

storeSides : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ → Bool × String
storeSides {κ = κ} f e ins =
  lockstep κ 0 (trace f (plainExp e) (plainSlots ins)) (trace f (elaborateImpl κ e) (embedSlotsImpl ins))
