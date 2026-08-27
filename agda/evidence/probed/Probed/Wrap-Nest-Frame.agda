-- ══════════════════════════════════════════════════════════════════
-- THE `*All` HEADS AWAY FROM THE ROOT, AND FROM A NODE TABLE THAT IS
-- ALREADY CARRYING SOMETHING.
--
-- TARGET: pushVals-merge-nest
-- TARGET: pushVals-switch-nest
-- TARGET: pushVals-exhaust-nest
--
-- WHY THIS AXIS.  `Probed.Subscribe-Nest-Wrap` reads all three heads at
-- `κ = root` from `st-init`, and says so: the store conjuncts are
-- `0 ≤ _` in every program reachable that way, and what the heads' own
-- risk names is a NON-EMPTY node table under a frame.  That is this
-- module.  The grant is the reason the axis is worth a row rather than
-- an argument: `G` is `nestB` at the caps size, the ambient program's
-- unit and the SUBTERM's sync size, and it mentions `κ` nowhere at all.
-- A frame's cost reaches the statement only through `descW`, which
-- bounds `W`, so a path that installs is paid for by a quantity the
-- grant reads at one remove.
--
-- THE `W = 0` READING, AND WHY IT STILL TRANSFERS.  Every row fixes the
-- grant at `W = 0`, which is smaller than the `W` these programs' own
-- `descW` premise forces -- `nestB` is `((2 ^ S) ^ suc W) ^ m * …`, so
-- it rises with `W` and clearing the smaller grant clears the larger.
-- That fact is true by inspection of a sealed body and is not a lemma
-- anywhere; the argument is stated where it is spent, at
-- `Probed.Subscribe-Nest-Wrap`.
--
-- WHAT IS LOAD-BEARING.  The incoming table is not a decoration: it
-- holds a merge node whose QUEUE carries a value three deep, so
-- `nodeNestAt` at that node reads 3 rather than zero going in and the
-- second and third conjuncts are no longer `0 ≤ _`.  The rows CAN
-- fail: a subscribe that installs under the frame something deeper
-- than both the incoming reading and the grant breaks them.
-- ══════════════════════════════════════════════════════════════════
module Probed.Wrap-Nest-Frame where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Exp; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
         nat̂; strmᵗ; deferᵉ; syncSizeᵛ; syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init; EvalSt; Stream; Sched;
         Path; _↠_; thru-outer; from-inner; map-f; mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; nestCapsOK?; nodeNestAt)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

-- the three heads, at the type the frame below consumes
oM : ℕ → Closed Γ₂ (obs natᵗ)
oM k = mergeAllᵉ (just 1) (wrapped k)

oS : ℕ → Closed Γ₂ (obs natᵗ)
oS k = switchAllᵉ (wrapped k)

oX : ℕ → Closed Γ₂ (obs natᵗ)
oX k = exhaustAllᵉ (wrapped k)

-- the ambient program, kept trivial so the unit is as small as it goes
prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

-- THE PATH: the head is subscribed UNDER a merge frame, not at the root
κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

-- THE TABLE IT STARTS FROM: a merge node whose queue holds a value
-- three deep, so the store conjuncts are not `0 ≤ _`.  It sits at an id
-- the FRAME does not claim -- put it at the frame's own node and the
-- subscribe overwrites it, and the rows go back to reading zero.
st₀ : EvalSt prog
st₀ = installNode 7 (mergeAll-st {t = natᵗ} (just 1) 1 (deepV 3 ∷ []) false)
                 (st-init prog)

tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

run : ∀ (o : Closed Γ₂ (obs natᵗ)) → _
run o = subscribeE gasBig o κ 0 0 (sched-init prog slots) st₀

-- the premises the head actually names, pinned rather than assumed
prem : (o : Closed Γ₂ (obs natᵗ)) → Set
prem o =
  (nestValOK? (tight {obs (obs natᵗ)} o) (obs (obs natᵗ)) o ≡ true)
  × (nestCapsOK? (tight {obs (obs natᵗ)} o) (sched-init prog slots) st₀ ≡ true)

premM : prem (oM 1)
premM = refl , refl

premS : prem (oS 1)
premS = refl , refl

premX : prem (oX 1)
premX = refl , refl

-- the grant at `W = 0`, written out because `nestB` is sealed
G : (o : Closed Γ₂ (obs natᵗ)) → ℕ
G o =
  let S = Caps.cSize (tight {obs (obs natᵗ)} o)
      m = syncSizeᵉ o
  in (2 ^ S) ^ m * (nestDᵉ o + suc m * nestUnit prog slots)

-- THE ARMING READING: what the table carries going in
armed : ℕ
armed = nodeNestAt 7 st₀

burstOf : (o : Closed Γ₂ (obs natᵗ)) → ℕ
burstOf o = nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ natᵗ} (proj₁ (run o))))

nodesOf : (o : Closed Γ₂ (obs natᵗ)) → ℕ
nodesOf o = nodesMax (proj₂ (proj₂ (run o)))

atOf : (o : Closed Γ₂ (obs natᵗ)) → ℕ
atOf o = nodeNestAt 7 (proj₂ (proj₂ (run o)))

figures : ℕ
figures = armed + 10 * burstOf (oM 1) + 100 * nodesOf (oM 1)
        + 1000 * atOf (oM 1) + 10000 * nodesOf (oS 1) + 100000 * nodesOf (oX 1)

figures≡ : figures ≡ 333313
figures≡ = refl

-- AND THE ROW WHERE THE SUBSCRIBE ITSELF INSTALLS.  The readings above
-- come out equal to what the table already held, so the incoming
-- summand carries them on its own and the grant is never asked for
-- anything.  A limited merge whose FIRST inner is a `deferᵉ` does not
-- finish inside the frame, so its limit is still spent when the descent
-- returns and the second inner is genuinely parked -- and then the
-- node's own queue is what the conjuncts read.
parkedOuter : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
parkedOuter k =
  ofᵉ (strmᵗ (deferᵉ (ofᵉ (strmᵗ (deepV 0) ∷ [])))
       ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

oP : ℕ → Closed Γ₂ (obs natᵗ)
oP k = mergeAllᵉ (just 1) (parkedOuter k)

premP : prem (oP 6)
premP = refl , refl

parked : ℕ
parked = nodesOf (oP 6) + 100 * atOf (oP 6) + 10000 * burstOf (oP 6)

parked≡ : parked ≡ 306
parked≡ = refl

-- THE CONJUNCTS THEMSELVES, at the head that installs
fitsP : ((burstOf (oP 6) ≤ᵇ G (oP 6)) ≡ true)
      × ((nodesOf (oP 6) ≤ᵇ nodesMax st₀ ⊔ G (oP 6)) ≡ true)
      × ((atOf (oP 6) ≤ᵇ armed ⊔ G (oP 6)) ≡ true)
fitsP = refl , refl , refl

-- ── the frame the head's own risk actually names ───────────────────

-- `from-inner` is the exit of a subscribed inner, so it carries the
-- `*All`'s own node and this inner's instance.  It is the constructor
-- the drain reaches under, and it takes the head at the ROOT type
-- rather than one `obs` up -- which is why it is a second setup and
-- not another row of the first.
parkedFlat : ℕ → Val Γ₂ (obs (obs natᵗ))
parkedFlat k =
  ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ []))) ∷ strmᵗ (deepV k) ∷ [])

oF : ℕ → Closed Γ₂ natᵗ
oF k = mergeAllᵉ (just 1) (parkedFlat k)

κF : Path Γ₂ natᵗ natᵗ
κF = from-inner mergeAllᵒ 7 1 ↠ root

runF : ∀ (o : Closed Γ₂ natᵗ)
     → Stream Γ₂ natᵗ × Sched Γ₂ × EvalSt prog
runF o = subscribeE gasBig o κF 0 0 (sched-init prog slots) st₀

premF : (nestValOK? (tight {obs natᵗ} (oF 6)) (obs natᵗ) (oF 6) ≡ true)
      × (nestCapsOK? (tight {obs natᵗ} (oF 6)) (sched-init prog slots) st₀ ≡ true)
premF = refl , refl

GF : (o : Closed Γ₂ natᵗ) → ℕ
GF o =
  let S = Caps.cSize (tight {obs natᵗ} o)
      m = syncSizeᵉ o
  in (2 ^ S) ^ m * (nestDᵉ o + suc m * nestUnit prog slots)

nodesF : (o : Closed Γ₂ natᵗ) → ℕ
nodesF o = nodesMax (proj₂ (proj₂ (runF o)))

burstF : (o : Closed Γ₂ natᵗ) → ℕ
burstF o = nestDᵛˢ {Γ = Γ₂} {u = natᵗ}
             (proj₁ (splitBurst {Γ = Γ₂} {u = natᵗ} {A = Val Γ₂ natᵗ}
                                (proj₁ (runF o))))

-- AND THE TWO HEADS WHOSE NODE STATE IS ZERO BY DEFINITION, taken
-- under the same installing outer: if these move at all, `nodeNest`
-- being zero on `switch-st` and `exhaust-st` is not the whole story.
oSP : ℕ → Closed Γ₂ (obs natᵗ)
oSP k = switchAllᵉ (parkedOuter k)

oXP : ℕ → Closed Γ₂ (obs natᵗ)
oXP k = exhaustAllᵉ (parkedOuter k)

frameFigs : ℕ
frameFigs = nodesF (oF 6) + 100 * burstF (oF 6)
          + 10000 * nodesOf (oSP 6) + 1000000 * nodesOf (oXP 6)

frameFigs≡ : frameFigs ≡ 3030006
frameFigs≡ = refl

-- nodes 6 against the 3 the table came in with, so the `from-inner`
-- row is carried by the GRANT and not by `⊔ nodesMax st₀`; burst 0,
-- since the drain parks the second inner.  The two zero-by-definition
-- heads read 3 and 3 -- EXACTLY the incoming table under an outer that
-- moved the merge head by six, which is what unreachable looks like
-- from the outside and is why no row here can arm them.
atF : (o : Closed Γ₂ natᵗ) → ℕ
atF o = nodeNestAt 7 (proj₂ (proj₂ (runF o)))

fitsF : ((burstF (oF 6) ≤ᵇ GF (oF 6)) ≡ true)
      × ((nodesF (oF 6) ≤ᵇ nodesMax st₀ ⊔ GF (oF 6)) ≡ true)
      × ((atF (oF 6) ≤ᵇ armed ⊔ GF (oF 6)) ≡ true)
fitsF = refl , refl , refl

-- ── the axis `G` cannot see at all ─────────────────────────────────

-- `G` mentions `κ` NOWHERE, and every frame reached above has a
-- `pathNestF` factor of one.  `map-f` does not: its factor is
-- `2 ^ sizeᵗ` of the function, and its body is SUBSCRIBED when a value
-- passes.  So if a path frame can install depth, a κ-blind grant is
-- refutable -- and this is the row that asks.  The body must be
-- DEFERRED or nothing is minted, which is the trap the delivery face
-- already recorded.
deepE : ∀ {Θ} → ℕ → Exp Γ₂ [] [] Θ natᵗ
deepE zero    = ofᵉ (nat̂ 0 ∷ [])
deepE (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepE k) ∷ []))

κMap : ℕ → Path Γ₂ natᵗ natᵗ
κMap k = map-f (strmᵗ (deferᵉ (deepE k))) ↠ (thru-outer mergeAllᵒ 0 ↠ root)

-- a head that EMITS inside the frame, so the map frame actually fires
oE : Closed Γ₂ natᵗ
oE = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

runM : ℕ → Stream Γ₂ natᵗ × Sched Γ₂ × EvalSt prog
runM k = subscribeE gasBig oE (κMap k) 0 0 (sched-init prog slots) st₀

nodesM : ℕ → ℕ
nodesM k = nodesMax (proj₂ (proj₂ (runM k)))

atM : ℕ → ℕ
atM k = nodeNestAt 7 (proj₂ (proj₂ (runM k)))

-- AND THE FIT IS NOT WHAT THIS ROW PINS.  `GF oE` here is on the order
-- of ten to the fifteen, so no reading could have exceeded it and a
-- `≤ᵇ` row would be unfalsifiable by construction.  What CAN fail is
-- the invariance: a body two deep and a body six deep are asked, and
-- if the frame minted at subscribe the second would read six.
mapFigs : ℕ
mapFigs = nodesM 2 + 100 * atM 2 + 10000 * nodesM 6 + 1000000 * atM 6

mapFigs≡ : mapFigs ≡ 3030303
mapFigs≡ = refl

mapInvariant : (nodesM 2 ≡ nodesM 6) × (atM 2 ≡ atM 6)
mapInvariant = refl , refl

-- ── where the grant is SMALL and the store is deep ─────────────────

-- Every fit above is taken against a grant in the millions or worse,
-- so none of them could have failed on arithmetic.  The region that
-- can is the one where `G` is BLIND: `nestDᵉ` and `syncSizeᵉ` both
-- stop at a `deferᵉ`, so a deep body hidden behind one contributes
-- nothing to the bound -- while an UNLIMITED merge subscribes that
-- same inner inside the frame, which is what installs it.  If the two
-- can be made to diverge, the head is refuted.
hidden : ℕ → Closed Γ₂ natᵗ
hidden k = mergeAllᵉ nothing (ofᵉ (strmᵗ (deferᵉ (deepV k)) ∷ []))

-- and the SAME body with the `deferᵉ` taken off, which is what makes
-- the row above load-bearing rather than a pair of equal numbers
sighted : ℕ → Closed Γ₂ natᵗ
sighted k = mergeAllᵉ nothing (ofᵉ (strmᵗ (deepV k) ∷ []))

hidNodes : ℕ
hidNodes = nodesF (hidden 2) + 100 * nodesF (hidden 8)
         + 10000 * nodesF (sighted 2) + 1000000 * nodesF (sighted 8)

hidNodes≡ : hidNodes ≡ 3030303
hidNodes≡ = refl

-- AND THAT RELOCATES THE ATTACK.  A subscribed inner finishes and
-- leaves nothing behind, so neither reading above moves: the depth
-- these conjuncts read is the QUEUE's, and a queue only holds what
-- the limit refused.  So the row that can refute is a limit spent on
-- a parked `deferᵉ` with a deep body queued BEHIND a second one --
-- `G` is blind to that body, and the question is whether the node is
-- too.
parkedHid : ℕ → Val Γ₂ (obs (obs natᵗ))
parkedHid k =
  ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ []))) ∷ strmᵗ (deferᵉ (deepV k)) ∷ [])

oH : ℕ → Closed Γ₂ natᵗ
oH k = mergeAllᵉ (just 1) (parkedHid k)

hidQueue : ℕ
hidQueue = nodesF (oH 2) + 100 * nodesF (oH 8)

hidQueue≡ : hidQueue ≡ 303
hidQueue≡ = refl

hidAligned : nodesF (oH 2) ≡ nodesF (oH 8)
hidAligned = refl

-- AND THE FIT PUSHED ALONG THE ONE AXIS THAT CAN MOVE IT.  The
-- sighted queue grows with `k` and so does `syncSizeᵉ`, so this is
-- the direction where a bound could be outrun; it is asked well past
-- the depth the rows above fit at.
deepFit : ((nodesF (oF 14) ≤ᵇ nodesMax st₀ ⊔ GF (oF 14)) ≡ true)
        × ((atF (oF 14) ≤ᵇ armed ⊔ GF (oF 14)) ≡ true)
deepFit = refl , refl

deepGrown : nodesF (oF 14) ≡ 14
deepGrown = refl
