-- THE SLOT DISPATCH AND ITS OTHER TWO ARMS — the shared slot's live and
-- fresh branches, the scripted slot, and the `with` that picks between
-- them.  The connect arm is one arrow below, and everything here
-- RECEIVES the walk face as an argument (`wl : WalkLevelAt (peelGas g)`)
-- rather than calling it, so none of it is part of the walk's recursion.
--
-- WHY THAT IS WORTH A MODULE, and it is a measured reason.  Sitting
-- textually among the dispatch's declarations put these INSIDE its
-- mutual block, and a block member in no cycle cannot be stubbed: every
-- focused check of every OTHER member re-proved all of these bodies in
-- full.  That was the whole of the per-member loop's overrun — the
-- statement telescopes and the lemma shelf together were worth a couple
-- of seconds, these were worth the rest.
--
-- Consumers name what they need from here directly.

module Verify-Budget-Sufficient.Walk-Level.Arms where

open import Data.Bool    using (T; true; false; _∨_)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-comm; +-monoʳ-≤; ≤⇒≤ᵇ)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Data.List    using (List; []; _∷_; map)
open import Data.Maybe   using (nothing)
-- `all` is the list action on Bool, not Data.List's `All`-valued one;
-- added in the commit that spends it, per this file's own rule
open import Data.Bool.ListAction using (all)

open import Rx.Prim      using (Tick; Id; value; Gas; ObservableInput; hot; cold; Timed)
open import Rx.Exp       using (Ty; obs; Ctx; Closed; Val; inputsBelowᵉ; isData; sizeᵉ; sizeᵛ; syncSizeᵉ; deferᵉ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵛ)
open import Rx.Slot-Hop  using (slotHop; slotHop-scripted)
open import Rx.Evaluator using (Sched; EvalSt; memberSource; Path; _↠_; subscribeE; mergeAllᵒ; mergeAll-st; hasDry; opIterD;
  thru-outer; LiveSource; installNode; register; mintNode; mintSource; mintOrdinal; resolve)
open import Rx.Slots using (scripted; shared; Slots; slotsSize)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; all-++-intro; hopDᵛ-data;
                                                      boundedLive; burstB?; burstHopD?;
                                                      dBound; fnCapLive; fnCapᵉ; hopR; INV?;
                                                      mapValue-B; oneShot-tail-dry; pathB?;
                                                      pathLen; regsLen?; unconn; valB?;
                                                      valsB?-widen; ∧-true)
open import Verify-Budget-Sufficient.Wet.Part2 using
  (addLive-INV)
open import Verify-Budget-Sufficient.Wet.Part1 using
  (INV?-widen)
open import Verify-Budget-Sufficient.Caps using
  (Caps; frameStep; frameStep-mono-j)
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; burstCount?; capsOK?; pathSz?; slotCaps?; slotsCaps?; slotsCaps?-lookup)
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (capsOK?-dropLive; capsOK?-liveHead; cSize≤frameStep; fnCapᵛ-data;
   resolve-fnCap-data)
-- the chain-charge algebra subscribeE-caps' own *All head spends
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE)
-- the caps twin's defer clause, spent by walk-defer-eight below: it is
-- the whole of that leaf's caps half, witness included
open import Verify-Budget-Sufficient.Subscribe-Face
  using (subscribeE-caps)
open import Verify-Budget-Sufficient.Walk-Level.Connect using
  (shared-live-INV; sharedConnect-walk)
open import Verify-Budget-Sufficient.Walk-Level.Statement using
  (inputᶜ; peelGas; WalkLevelAt; WalkStmt; WalkStmt⁻)
open import Verify-Budget-Sufficient.Walk-Level.Parts using
  (input-wet-scripted-regs; INV?-install; mapValue-dry;
   mapValue-hop; register-regsLen)
open import Decide using (T⇒≡true; ∧-intro)


-- THE SHARED SLOT, ASSEMBLED.  Was one opaque postulate over
-- the whole slot; it is now the real three-way dispatch subscribeSharedSlot
-- performs, against the PROVEN clause-for-clause twin `sharedSlot-caps`
-- (.Subscribe-Face), whose three arms are these three at the same
-- scrutinees and in the same order.
--
-- ARM A (spent share) and ARM B (live share) are CLOSED HERE — neither
-- connects, so neither recurses, and between them they account for four of
-- the wet five by computation:
--   · burstB? / burstHopD?  `eventB?` and `hopDev?` are `true` on init,
--     close, handoff and complete alike (.Measures) and these two arms emit
--     no values at all, so both are refl.
--   · hasDry                `dryEvent` fires on `close _ dried` ALONE
--     (Rx.Evaluator); arm A emits `close _ exhausted`, arm B emits no
--     close.  refl both times.
--   · INV? (arm A)          the state is untouched, so this is INV?-widen
--     across the cap step, and `frameStep-mono-j` supplies the step.
--   · regsLen?              arm A leaves the registry alone (the
--     hypothesis); arm B is PROVEN register-regsLen, spending
--     `pathLen κ ≤ ℓ` out of this statement's own `pathLen κ + G ≤ ℓ`.
-- What is left of arm B is its INV? alone (`shared-live-INV`), and arm C is
-- `sharedConnect-walk`.  Both are stated above with their routes.
input-wet-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
    (g : Gas) → WalkLevelAt (peelGas g) →
    ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    -- b is BOUND, not applied: the measures below take a general
    -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
    -- `[]` — an alias of type `Closed Γ _` does not, so writing
    -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
    b ≡ inputᶜ i →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in capsOK? (frameStep (j + j′) c)
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
       burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
       j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
       (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
-- `with … in slotEq2`, NOT `with … | slotEq`.  Both abstract the scrutinee
-- so that subscribeE's own `with Sched.slots sched i` can fire — that much
-- is forced, since subscribeE is stuck on it and the goal does not mention
-- it syntactically, which is why `rewrite` cannot serve here.  But the
-- `| slotEq` form CONSUMES the equation, and arm C has to hand it on to
-- sharedConnect-walk; re-forming it as `refl` afterwards does not typecheck
-- (Agda re-elaborates `Sched.slots sched i` un-reduced).  The `in` form
-- keeps it, at the cost of a scripted branch that slotEq itself refutes.
input-wet-shared c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st
  d slotEq refl 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
  with Sched.slots sched i in slotEq2
-- the slot cannot be scripted: this face was dispatched on `shared`
... | scripted s with slotEq
...   | ()
input-wet-shared c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st
  d slotEq refl 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
  | shared d′
  with memberSource (toℕ i) (EvalSt.completedSources st)
-- ARM A — the spent share.  sched and st both untouched, so the only
-- moving part is the cap widening on INV?.
...  | true =
    INV?-widen sched st (proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))) invW
  , refl , refl , refl , rgs
...  | false with memberSource (toℕ i) (EvalSt.connectedShares st) in eqM
-- ARM B — the live share joins mid-flight: one `init`, and a registration.
...    | true =
    shared-live-INV c Ψ j j′ (toℕ i) κ sched st 2≤S hCR cOK′ invW pB
  , refl , refl , refl
  , register-regsLen ℓ (toℕ i) κ st (≤-trans (m≤m+n (pathLen κ) G) lℓ) rgs
-- ARM C — the connect, and the only arm that recurses; `wl` goes with it.
...    | false =
  sharedConnect-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl
    -- `dpt` needs NO transport: depthE at an input is `depthSlot … (Sched
    -- .slots sched i)` by refl (.Caps-Depth) and depthSlot takes the slot
    -- as its LAST argument, so the with-abstraction of the scrutinee has
    -- already carried this hypothesis' type to depthConn at d′.  That is
    -- the whole reason the leaf is stated at depthConn.
    -- eqM is ARM C's own scrutinee equation, kept by `with … in eqM`
    -- above.  It IS the freshness premise the leaf now takes, and it is
    -- free here precisely because this arm is the not-yet-connected
    -- branch — the same branch `subscribeSharedSlot` guards on.
    sched st d′ slotEq2 refl eqM 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt
    invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle

-- ═══ THE TWO BOUNDS ON A SCRIPTED SLOT'S SYNC PREFIX, BOTH DISCHARGED ═══
--
-- Both cold shapes need exactly these and nothing else, which is why they
-- are stated here rather than inside either: `burstB?` and `burstHopD?` are
-- `all … ∘ InstEmit.events` over a ONE-emit burst whose events are
-- `init src ∷ map value sync`, `init` satisfies both predicates outright,
-- and `mapValue-B` / `mapValue-hop` then reduce each conjunct to a bound on
-- `sync` itself.  The tail never appears, so the SAME two facts serve the
-- empty and async shapes -- and stating them at the slot rather than at the
-- clause is what makes that sharing visible instead of duplicated.
--
-- The size half's route was located as `slotCaps?`'s first conjunct at this
-- slot, reached through a tabulate-lookup projection of `slotsCaps?` -- and
-- that projection turned out to EXIST, `slotsCaps?-lookup` (.Caps-Face/
-- Part1), so the size leaf is discharged below.  The Ψ half needed no
-- hypothesis at all: `fnCapᵛ-data` sends every data-typed value to 0, and
-- `isData` is exactly the `ok` binder the slot already carries.

-- THE SIZE-AND-Ψ BOUND, DISCHARGED.  `slotsCaps?-lookup` projects the slot's
-- own conjunct out of the tabulate, `slotCaps?` at a cold slot IS that bound on
-- `sync` (its second conjunct is the tail, which neither cold shape's burst
-- carries), and the Ψ half is `fnCapᵛ-data` at every element.  The recursion
-- exists only to zip the two halves under `valB?`, which pairs them.
scripted-sync-valB : ∀ {n} {Γ : Ctx n} (B Ψ W : ℕ) (sl : Slots Γ)
  (i : Fin n) {ok : T (isData (lookup Γ i))}
  (sync : List (Val Γ (lookup Γ i)))
  (tl : List (Timed (Val Γ (lookup Γ i)))) →
  sl i ≡ scripted {ok = ok} (cold sync tl) →
  slotsCaps? B W sl ≡ true →
  all (valB? B Ψ (lookup Γ i)) sync ≡ true
scripted-sync-valB {Γ = Γ} B Ψ W sl i {ok} sync tl slotEq slC =
  go sync (proj₁ (∧-true _ _
    (subst (λ s → slotCaps? B W sl s ≡ true) slotEq
      (slotsCaps?-lookup B W sl i slC))))
  where
  u : Ty
  u = lookup Γ i
  go : (vs : List (Val Γ u)) → all (λ v → sizeᵛ u v ≤ᵇ B) vs ≡ true →
       all (valB? B Ψ u) vs ≡ true
  go []       h = refl
  go (v ∷ vs) h
    with ∧-true (sizeᵛ u v ≤ᵇ B) (all (λ w → sizeᵛ u w ≤ᵇ B) vs) h
  ... | h1 , h2 =
        ∧-intro (∧-intro h1
                  (subst (λ x → (x ≤ᵇ Ψ) ≡ true)
                         (sym (fnCapᵛ-data u ok v)) refl))
                (go vs h2)

-- AND THE HOP AXIS -- which turned out not to be a budget argument at all.
-- The bound is ZERO: `hopDᵉ V η (input i)` IS `η i`, `slotHop` at a scripted
-- slot is `slotHopD` of a `scripted`, and that is 0 outright.  That half was
-- unstated and is now `slotHop-scripted` (.Rx/Slot-Hop, beside the fixpoint
-- facts it belongs with).  The values weigh 0 too, the slot's element type
-- being data (`hopDᵛ-data`, .Walk-Level/Parts, third of that family) -- so the
-- two sides MEET at 0 and the `≤ᵇ` is an equality in disguise.
--
-- The header this replaces guessed the route as "no more than the `input i`
-- that replays them", via slotHop-fix.  That was the right intuition and the
-- wrong lemma: slotHop-fix is the SHARED side of the fixpoint and says nothing
-- about a scripted slot.
scripted-sync-hopD : ∀ {n} {Γ : Ctx n} (F : ℕ) (sl : Slots Γ)
  (i : Fin n) (b : Closed Γ (lookup Γ i)) {ok : T (isData (lookup Γ i))}
  (sync : List (Val Γ (lookup Γ i)))
  (tl : List (Timed (Val Γ (lookup Γ i)))) →
  sl i ≡ scripted {ok = ok} (cold sync tl) →
  b ≡ inputᶜ i →
  all (λ v → hopDᵛ F (slotHop F sl) (lookup Γ i) v
               ≤ᵇ hopDᵉ F (slotHop F sl) b) sync ≡ true
scripted-sync-hopD {Γ = Γ} F sl i b {ok} sync tl slotEq refl =
  go sync
  where
  u : Ty
  u = lookup Γ i
  z : slotHop F sl i ≡ 0
  z = slotHop-scripted F sl i (cold sync tl) slotEq
  go : (vs : List (Val Γ u)) →
       all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ slotHop F sl i) vs ≡ true
  go []       = refl
  go (v ∷ vs) =
    ∧-intro (subst₂ (λ x y → (x ≤ᵇ y) ≡ true)
                    (sym (hopDᵛ-data F (slotHop F sl) u ok v)) (sym z) refl)
            (go vs)

-- SHAPE C, ASSEMBLED -- the empty cold, and it is shape D minus the register
-- plus a close.  Every step is one D already spends, which is the payoff of
-- having stated the two slot bounds at the SLOT rather than inside D: they
-- carry over verbatim, because neither burst carries the tail.
--
-- WHAT DIFFERS FROM D, and it is only these three:
--   * nothing is registered and no live entry is minted, so INV? crosses on
--     `INV?-widen` alone -- the mint is invisible to it, reading the schedule
--     only through `live` and `slots`, so no transport is needed here either.
--   * the burst carries a `close _ exhausted` and a `complete` after the
--     values, so each value conjunct is an `all-++-intro` over the values and
--     a tail that satisfies both predicates outright.
--   * hasDry is therefore NOT refl but `oneShot-tail-dry`, which is exactly
--     the statement "this tail is not dry" for a one-shot burst: `dried` is a
--     reason no machine rule emits, and `exhausted` is not it.
scripted-cold-empty-four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas)
  (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (sync : List (Val Γ (lookup Γ i))) →
  Sched.slots sched i ≡ scripted {ok = ok} (cold sync []) →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  depthE g b κ bid now sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g b κ bid now sched st
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
scripted-cold-empty-four {Γ = Γ} c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st {ok} sync slotEq refl
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle
  with trans (sym (cong (λ x → x i) slEq)) slotEq
     | Sched.slots sched i | slotEq
... | slEq′ | .(scripted (cold sync [])) | refl =
      INV?-widen sched st (proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))) inv
    , ∧-intro (∧-intro refl
        (all-++-intro _ (map value sync) _
          (mapValue-B B Ψ (lookup Γ i) sync
            (valsB?-widen (lookup Γ i) sync (cSize≤frameStep c (j + j′) 2≤S)
              (scripted-sync-valB (Caps.cSize c) Ψ (Caps.cWid c) sl i
                {ok} sync [] slEq′ slC)))
          refl))
        refl
    , ∧-intro (∧-intro refl
        (all-++-intro _ (map value sync) _
          (mapValue-hop F (slotHop F sl) _ sync
            (scripted-sync-hopD F sl i _ {ok} sync [] slEq′ refl))
          refl))
        refl
    , cong (λ x → x ∨ false)
           (oneShot-tail-dry sync (proj₁ (mintSource sched)))
  where
  B = Caps.cSize (frameStep (j + j′) c)

-- SHAPE D, ASSEMBLED — and the composition failure its header recorded is
-- REPAIRED rather than routed around.  The census said "register-INV then
-- addLive-INV"; the two did not meet, because `shared-live-INV` wants its
-- caps receipt at the schedule it registers under while this clause is handed
-- one at the POST-addLive schedule, and `capsOK?` genuinely reads
-- `Sched.live`.  The step nobody had named is `capsOK?-dropLive`
-- (.Caps-Face/Part5), which costs no hypothesis: every conjunct that reads
-- `live` reads it through an `all`, and the mints leave `Sched.slots`
-- definitionally alone.
--
-- WHAT THE BODY SPENDS, and only the last line is still owed:
--   · the caps receipt is DROPPED to the pre-addLive schedule, carried across
--     the register by `shared-live-INV` (.Connect), and put back across the
--     live entry by `addLive-INV` (.Wet/Part2) -- so the INV? conjunct is
--     CLOSED, which is what this row was blocked on.
--   · addLive-INV's two side conditions cost nothing.  `boundedLive` is the
--     HEAD of the very conjunct the drop throws away, so the receipt already
--     says it (`capsOK?-liveHead`); and `fnCapLive` no caps receipt could
--     ever supply, since capsOK? has no Ψ conjunct -- it comes from
--     `resolve-fnCap-data`, free on a data slot.
--   · `inv` is stated at `sched` and spent at the double-minted `sched₂`
--     WITHOUT transport: both mints are record updates on counter fields, and
--     INV? reads the schedule only through `live` and `slots`, so the two
--     types are definitionally equal.  That is the "mint is transparent"
--     claim the census made in prose, here made a typecheck.
--   · hasDry is `refl`: `dryEvent` fires on `close _ dried` alone and this
--     burst carries no close at all.
--   · burstB? and burstHopD? are `mapValue-B` / `mapValue-hop` over the two
--     slot bounds above, which are the only thing left postulated.

scripted-cold-async-four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas)
  (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (sync : List (Val Γ (lookup Γ i)))
  (d : Timed (Val Γ (lookup Γ i)))
  (ds : List (Timed (Val Γ (lookup Γ i)))) →
  Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds)) →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  depthE g b κ bid now sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g b κ bid now sched st
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
scripted-cold-async-four {n = n} {Γ = Γ} c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st {ok} sync d ds slotEq refl
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle
  -- the slot equation is stated at `Sched.slots sched i`, which the `with`
  -- below consumes; the two slot bounds want it at `sl i`.  Carrying the
  -- converted form THROUGH the with costs nothing, because its type names no
  -- occurrence of the scrutinee and so survives the abstraction untouched.
  with trans (sym (cong (λ x → x i) slEq)) slotEq
     | Sched.slots sched i | slotEq
... | slEq′ | .(scripted (cold sync (d ∷ ds))) | refl =
      addLive-INV Ψ B sch₂ (register src κ st) L
        (capsOK?-liveHead (frameStep (j + j′) c) L sch₂ (register src κ st) cOK′)
        (resolve-fnCap-data Ψ (lookup Γ i) ok (resolve now (d ∷ ds)))
        (shared-live-INV c Ψ j j′ src κ sch₂ st 2≤S hCR
           (capsOK?-dropLive (frameStep (j + j′) c) L sch₂
              (register src κ st) cOK′)
           inv pB)
    , ∧-intro (∧-intro refl
        (mapValue-B B Ψ (lookup Γ i) sync
          -- the slot bound is stated at the BASE caps, because that is where
          -- slotsCaps? is; the clause reports at frameStep (j + j′), and
          -- cSize only ever grows with j
          (valsB?-widen (lookup Γ i) sync (cSize≤frameStep c (j + j′) 2≤S)
            (scripted-sync-valB (Caps.cSize c) Ψ (Caps.cWid c) sl i
              {ok} sync (d ∷ ds) slEq′ slC))))
        refl
    -- the hop bound is left to UNIFICATION rather than written out: the
    -- measures take a general `Exp Γ Δᵍ Δ Θ t` and only a BINDER pins those
    -- three contexts, so spelling `hopDᵉ F (slotHop F sl) (inputᶜ i)` here
    -- leaves a meta per measure -- the same trap the statement's own header
    -- records.  The goal already carries the term with its implicits solved.
    , ∧-intro (∧-intro refl
        (mapValue-hop F (slotHop F sl) _ sync
          (scripted-sync-hopD F sl i _ {ok} sync (d ∷ ds) slEq′ refl)))
        refl
    -- dryEvent fires on `close _ dried` ALONE, and this burst is `init` plus
    -- values: the init reduces away and the values are mapValue-dry's whole
    -- statement.  No close at all, so no tail term to account for.
    , cong (λ x → x ∨ false) (mapValue-dry sync)
  where
  B    = Caps.cSize (frameStep (j + j′) c)
  src  = proj₁ (mintSource sched)
  sch₁ = proj₂ (mintSource sched)
  sch₂ = proj₂ (mintOrdinal sch₁)
  L : LiveSource Γ
  L = record { source = src ; ordinal = proj₁ (mintOrdinal sch₁)
             ; elemTy = lookup Γ i ; pending = resolve now (d ∷ ds) }

-- no connect, so no recursion: a scripted slot replays its own values
--
-- ═══ THE CENSUS.  FOUR SHAPES × THE WET FIVE ═══
-- GRINDABLE.  The precedent is `subscribeE-input-caps` (.Subscribe-Face,
-- PROVEN), whose scripted side splits into exactly these four branches
-- and whose clauses correspond one-to-one.  Note this postulate takes NO
-- walk face (contrast input-wet-shared) — the scripted slot never
-- connects, so nothing here recurses and no induction has to be designed.
-- The caps receipts arrive as HYPOTHESES, so only the wet five are owed.

-- What subscribeE produces (Rx.Evaluator), and the ingredient for
-- each conjunct.  Every one named below is PROVEN except where marked:
--
--   A. hot, memberSource ≡ true — burst init/close-exhausted/complete;
--      sched AND st untouched; caps twin returns j′ = 0.
--        INV?       INV?-widen (.Wet/Part1) over +-identityʳ
--        burstB?    no values in the burst — computation
--        burstHopD? no values in the burst — computation
--        hasDry     dryEvent fires on `dried` ALONE (Rx.Evaluator), and
--                   this burst carries `exhausted` — computation
--        regsLen?   registry untouched — the hypothesis, as-is
--
--   B. hot, memberSource ≡ false — burst `init` only; st = register; j′ = 1.
--        INV?       register-INV (.Wet/Part1)
--        burstB?    no values — computation
--        burstHopD? no values — computation
--        hasDry     `init` only — computation
--        regsLen?   ⚠ register-regsLen — THE ONE GAP, stated below
--
--   C. cold sync [] — oneShotBurst; st untouched; j′ = 1.
--        INV?       INV?-widen; the mint is TRANSPARENT (below)
--        burstB?    mapValue-B (.Measures)
--        burstHopD? mapValue-hop (above, this module)
--        hasDry     oneShot-tail-dry (.Measures)
--        regsLen?   registry untouched — the hypothesis, as-is
--
--   D. cold sync (d ∷ ds) — mint + addLive; st = register; j′ = 1.
--        INV?       register-INV then addLive-INV (.Wet/Part2)
--        burstB?    mapValue-B (.Measures)
--        burstHopD? mapValue-hop (above, this module)
--        hasDry     mapValue-dry + any-dry-++ (above, this module)
--        regsLen?   ⚠ register-regsLen — THE ONE GAP, stated below

-- THE MINT IS TRANSPARENT TO INV?, which is why C and D need no lemma for
-- it: INV? reads the schedule ONLY through `Sched.live` and `Sched.slots`
-- (.Measures, via stBounded? and fnCapBounded?), while mintSource and
-- mintOrdinal touch `nextSource` / `nextOrdinal` alone (Rx.Evaluator).
-- The record update reduces, so the mint is invisible to the predicate.
-- Only D's addLive genuinely moves `live`, and that is addLive-INV's job.

-- THE regsLen? CONJUNCT IS DISCHARGED.  `input-wet-scripted`
-- below is a REAL BODY over this leaf: it pairs the four conjuncts owed
-- here with the PROVEN `input-wet-scripted-regs` (above, this module),
-- which closes the fifth for all four shapes off `register-regsLen`.  So
-- the ⚠ rows in A-D are shape B's and shape D's, and they are shut.

-- `pathLen κ ≤ ℓ`, which that lemma wants, comes from this statement's own
-- `pathLen κ + G ≤ ℓ` by m≤m+n — nothing new is spent for it.

-- PLACEMENT, a real constraint and cheap to get wrong: neither the leaf nor
-- the body takes a walk face, so neither may join the heavy mutual block
-- (block 42, 15 members — `make agda-dev ARGS='--list …'` shows them free).
-- The regs lemma sits ABOVE that block with the dry/hop helpers it spends
-- (retagEvents-dry, mapValue-hop, mapValue-dry, any-dry-++).  The regsLen?
-- helpers do NOT: capsOK⇒regsLen and regsLen?-mono sit ~1200 lines BELOW,
-- after the block, so anything of theirs a future clause wants moves up too.
--
-- ═══ TWO CHORES BEFORE THE GRIND, NEITHER STRUCTURAL ═══
-- Both are bookkeeping, and both are recorded because each reads as
-- already-done from the census above.
--
--   · THE PRECEDENT IS NOT IN SCOPE.  `subscribeE-input-caps` is named
--     as the clause-for-clause twin, and it is PROVEN, but it is absent
--     from this module's `using` list for .Subscribe-Face — so the twin
--     cannot be APPLIED here until it is added.  Deliberately not added
--     ahead of the body: an unapplied name in a `using` list earns no
--     reachability credit and is indistinguishable from clutter.  Add it
--     in the commit that spends it.
--   · EIGHT CONJUNCTS ARE ROUTED "BY COMPUTATION" AND NONE OF THE EIGHT
--     IS TYPECHECKED.  The census discharges them by inspection of the
--     evaluator, which is the same disclaimer the walkFace family carries
--     — located, not spent.  Expect the residue to be larger than four
--     lemmas, and treat any of the eight that does NOT fall out as the
--     finding rather than as a slip in the census.
input-wet-scripted-four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas)
  (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (src : ObservableInput (Val Γ (lookup Γ i))) →
  Sched.slots sched i ≡ scripted {ok = ok} src →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  depthE g b κ bid now sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g b κ bid now sched st
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st (hot asy) slotEq refl
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle
  with Sched.slots sched i | slotEq
... | .(scripted (hot asy)) | refl
  with memberSource (toℕ i) (EvalSt.completedSources st)
-- A. the spent script: close/complete at once, nothing registered, and
--    neither the schedule nor the state moves — so INV? is pure widening
--    and the burst carries no value to bound.
...   | true  =
        INV?-widen sched st (proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))) inv
      , refl , refl , refl
-- B. the live script: one `init`, and the registration this face exists
--    for.  shared-live-INV (.Connect) is exactly it, and its caps receipt
--    is this clause's own cOK′ — the schedule does not move here, which
--    is precisely what shape D loses.
...   | false =
        shared-live-INV c Ψ j j′ (toℕ i) κ sched st 2≤S hCR cOK′ inv pB
      , refl , refl , refl
input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st (cold sync []) slotEq bEq
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle =
  scripted-cold-empty-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st sync slotEq bEq
    2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle
input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st (cold sync (d ∷ ds)) slotEq bEq
  2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle =
  scripted-cold-async-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st sync d ds slotEq bEq
    2≤S 1≤R hCR slEq slC slS cOK szb pSz spL nst dpt inv fnc pB 2≤Ŝ FŜ R̂eq Ŝge opL dB gHas pℓ rgs cOK′ bC bCt jle

-- THE SCRIPTED SLOT, ASSEMBLED.  A real body over the four-conjunct leaf and
-- the proven regs lemma — the leaf-only shape, so that when a shape's wet
-- four lands the fit is tested by the typechecker rather than asserted.

input-wet-scripted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas)
  (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (src : ObservableInput (Val Γ (lookup Γ i))) →
  Sched.slots sched i ≡ scripted {ok = ok} src →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  -- TAKEN AND DROPPED.  The scripted slot never connects, so nothing here
  -- needs an ops ledger; this is carried only to keep the telescope aligned
  -- with input-wet-core's, which DOES need it for the connect arm.  It is
  -- not passed on, so the postulate above stays at full strength.
  suc (sizeᵉ b) ≤ ops →
  depthE g b κ bid now sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g b κ bid now sched st
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
input-wet-scripted c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st
  src slotEq bEq 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst _ dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle =
  let (a₁ , a₂ , a₃ , a₄) =
        input-wet-scripted-four c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid
          now sl sched st src slotEq bEq 2≤S 1≤R hCR slEq slC slSz cOK szb pSz
          lC nst dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
  in a₁ , a₂ , a₃ , a₄
   , input-wet-scripted-regs ℓ g i b κ bid now sched st src slotEq bEq
       (≤-trans (m≤m+n (pathLen κ) G) lℓ) rgs

-- the dispatch itself: match the slot, hand each shape its own residue.
input-wet-core : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas) → WalkLevelAt (peelGas g) →
  ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  suc (sizeᵉ b) ≤ ops →
  depthE g b κ bid now sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g b κ bid now sched st
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
input-wet-core c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st
  with Sched.slots sched i in slotEq
... | shared d   = input-wet-shared c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g wl i b κ bid now sl sched st d slotEq
... | scripted s = input-wet-scripted c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i b κ bid now sl sched st s slotEq


------------------------------------------------------------------
-- THE defer CLAUSE'S LEAF, ASSEMBLED.  Install the mergeAll node, mint the
-- source and ordinal, park the body as a one-element pending, register
-- the thru-outer chain; the burst is `init src ∷ []` and nothing else.
--
-- IT NEITHER RECURSES NOR PUSHES, which is what makes it the one row in
-- this family with no induction in it at all: the caps half is
-- `subscribeE-caps`'s own defer clause verbatim — four conjuncts and the
-- witness, delivered rather than re-derived — and the wet half is four
-- transports across three state writes.
--
--   INV?       three writes, one lemma each and in this order: the node
--              install (INV?-install, the mint invisible to it since
--              INV? reads the schedule only through `live` and `slots`),
--              the registration (shared-live-INV, whose caps receipt is
--              the caps half's own first conjunct with the new live head
--              dropped off by capsOK?-dropLive), and the live extension
--              (addLive-INV).  The two side conditions of the last cost
--              a `≤ᵇ` each: `sizeᵛ (obs u) body` IS `sizeᵉ body`, one
--              below the subscribed `sizeᵉ (deferᵉ body)`, and
--              `fnCapᵛ (obs u) body` IS `fnCapᵉ (deferᵉ body)`, equal to
--              the hypothesis rather than below it.
--   burstB?    the burst carries no `value` at all, so `eventB?` is
--   burstHopD? `true` on every event of it by definition, at any B and
--              any r — both `refl`.
--   hasDry     a lone `init` is not a dry close.  `refl`.
--
-- The `pathB?` the registration wants is free the same way:
-- `frameB? B Ψ (thru-outer _ _) = true`, so the extended chain is the
-- hypothesis with one `refl` in front of it.
walk-defer-eight : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (body : Closed Γ u) → WalkStmt⁻ {e = e} (deferᵉ body)
walk-defer-eight {Γ = Γ} {u = u} body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  j′ , a₁ , a₂ , a₃ , a₄
     , addLive-INV Ψ B′ SCHED₃ ST NEW BL FL
         (shared-live-INV c Ψ j j′ SRC PATH SCHED₃ ST₀ 2≤S hCR
            (capsOK?-dropLive (frameStep (j + j′) c) NEW SCHED₃ ST a₁)
            INV₀ pB′)
     , refl , refl , refl
  where
  CAPS = subscribeE-caps c dep bud ops j g (deferᵉ body) κ bid now sl sched st
           2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt
  j′ = proj₁ CAPS
  a₁ = proj₁ (proj₂ CAPS)
  a₂ = proj₁ (proj₂ (proj₂ CAPS))
  a₃ = proj₁ (proj₂ (proj₂ (proj₂ CAPS)))
  a₄ = proj₂ (proj₂ (proj₂ (proj₂ CAPS)))
  B  = Caps.cSize (frameStep j c)
  B′ = Caps.cSize (frameStep (j + j′) c)
  nid  = Sched.nextNode sched
  SRC  = Sched.nextSource sched
  PATH = thru-outer mergeAllᵒ nid ↠ κ
  ST₀  = installNode nid (mergeAll-st {t = u} nothing 0 [] false) st
  ST   = register SRC PATH ST₀
  SCHED₃ = record (record (record sched { nextNode = suc (Sched.nextNode sched) })
                          { nextSource = suc (Sched.nextSource sched) })
                  { nextOrdinal = suc (Sched.nextOrdinal sched) }
  NEW : LiveSource Γ
  NEW = record { source = SRC ; ordinal = Sched.nextOrdinal sched
               ; elemTy = obs u ; pending = (suc now , body) ∷ [] }
  INV₀ : INV? Ψ B SCHED₃ ST₀ ≡ true
  INV₀ = INV?-install Ψ B B nid (mergeAll-st {t = u} nothing 0 [] false) sched SCHED₃ st
           ≤-refl refl refl refl refl invW
  pB′ : pathB? B Ψ PATH ≡ true
  pB′ = ∧-intro refl pB
  BL : boundedLive B′ NEW ≡ true
  BL = ∧-intro (T⇒≡true (sizeᵉ body ≤ᵇ B′)
                 (≤⇒≤ᵇ (≤-trans (≤-trans (n≤1+n (sizeᵉ body)) szb)
                                (proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))))))
               refl
  FL : fnCapLive Ψ NEW ≡ true
  FL = ∧-intro (T⇒≡true (fnCapᵉ body ≤ᵇ Ψ) (≤⇒≤ᵇ fnC)) refl

-- THE defer CLAUSE, ASSEMBLED.  The leaf above owes the eight conjuncts that
-- need the caps twin and the wet predicates; the ninth is register-regsLen at
-- the path the clause actually registers.
--
-- The length arithmetic is the whole content and it is three steps:
-- `syncSizeᵉ (deferᵉ body) = 1` (Rx.Exp) sits in dBound's summand position,
-- so `1 ≤ dBound … ≤ G` by s≤s z≤n; that funds `pathLen κ + 1 ≤ pathLen κ + G
-- ≤ ℓ`; and +-comm turns it into the `suc (pathLen κ) ≤ ℓ` the extended path
-- needs.  installNode touches `nodes` alone, so the registry hypothesis
-- passes through unchanged.
walk-defer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (body : Closed Γ u) → WalkStmt {e = e} (deferᵉ body)
walk-defer {u = u} body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  let (j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , a₇ , a₈) =
        walk-defer-eight body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs
  in j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , a₇ , a₈
   , register-regsLen ℓ _ (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
       (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} nothing 0 [] false) st)
       (subst (_≤ ℓ) (+-comm (pathLen κ) 1)
              (≤-trans (+-monoʳ-≤ (pathLen κ) (≤-trans (s≤s z≤n) dmd)) lℓ))
       rgs
