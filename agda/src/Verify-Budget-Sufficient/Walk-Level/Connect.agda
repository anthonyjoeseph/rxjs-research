-- THE CONNECT ARM — the share slot's third branch, where the walk spends
-- a gas peel on `sharedConnect` and hands the slot's stored definition
-- to the walk face it was given.  Its own leaves come with it, so the
-- whole arm is one module: what it postulates and what consumes those
-- postulates sit together, and the arm's inventory is what this file
-- contains.
--
-- ITS SIBLINGS ARE ONE ARROW ABOVE, and the split is the granularity
-- rule rather than a taxonomy: nothing here has a mutual block, so a
-- module is checked whole and its cost is the sum of its bodies.  The
-- connect arm alone is that sum's larger half, which is what makes it
-- worth its own file — the other arms should not be re-proved to
-- iterate on this one, and this one is where the grinding is.
--
-- Consumers name what they need from here directly.

module Verify-Budget-Sufficient.Walk-Level.Connect where

open import Data.Bool    using (T; true; false)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.List    using ([]; _∷_; _++_; length)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; +-comm; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Prim      using (Tick; Id; Source; init; close; exhausted; subscribe; _at_from_as_; Gas; g0; gs)
open import Rx.Exp       using (Ctx; Closed; inputsBelowᵉ; sizeᵉ; syncSizeᵉ)
open import Rx.Frame-Width using (dWᵉ; pWᵉ)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop  using (slotHop; slotHop-fix)
open import Rx.Evaluator using (Sched; EvalSt; memberSource; Path; share-sink; subscribeE; sharedConnect; hasDry;
  burstCompleted; sharedPlumb; dropSource; opIterD; register)
open import Rx.Slots using (shared; Slots; slotsSize)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; all-++-intro; burstB?;
                                                      burstHopD?; dBound; dropSource-all;
                                                      fnCapᵉ; fᵢ≤sum-tab; hasAtLeast-mono;
                                                      hopR; INV-parts; INV?; pathB?;
                                                      pathB?-widen; pathLen; regsB?;
                                                      regsB?-widen; regsLen?; slotFnCap;
                                                      slotsFnCap; stBounded-widen; unconn;
                                                      ∧-true)
open import Verify-Budget-Sufficient.Wet.Part2 using
  (connectWrap-wet; sharedPlumb-hopD; sharedPlumb-nodry)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; subscribeE-keeps)
open import Verify-Budget-Sufficient.Wet.Part6 using
  (connect-edge)
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; burstCount?; capsOK?; pathSz?; slotCaps?; slotsCaps?; slotsCaps?-lookup)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-parts; register-caps)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (cSize≤frameStep; cWid≤frameStep)
open import Verify-Budget-Sufficient.Psi-Split using
  (burstB?-reindex; INV?-reindex)
-- the chain-charge algebra subscribeE-caps' own *All head spends
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
open import Verify-Budget-Sufficient.Caps
  using (frameStep-reg≤size; Caps; frameStep; frameStep-0; frameStep-mono-j)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthConn)
open import Verify-Budget-Sufficient.Caps-Nest
  using (share-step; nest)
open import Verify-Budget-Sufficient.Walk-Level.Parts using
  (hasAtLeast-peel-gs; register-regsLen)
open import Verify-Budget-Sufficient.Walk-Level.Statement using
  (inputᶜ; mu-lvl-desc; peelGas; WalkLevelAt)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)


-- ARM B's INV?, AND ONLY IT.  The live-share join registers and touches
-- nothing else, so four of the wet five close by computation or by the
-- hypothesis (see the body below); this is the fifth.
--
-- ⚠ THE CAPS RECEIPT IS LOAD-BEARING, AND WITHOUT IT THIS IS FALSE AT
-- j′ = 0.  Stated first as `INV? at j → INV? at (j + j′) after register`
-- with no caps hypothesis; that is refuted by INV?'s own third conjunct,
-- `length (EvalSt.registry st) ≤ᵇ B` (.Measures).  `register` APPENDS one
-- entry, so the length goes L ↦ suc L, while j′ = 0 leaves B alone — and
-- a registry sitting exactly at its cap satisfies the hypothesis and
-- refutes the conclusion.  j′ = 0 is not hypothetical here: this face
-- quantifies j′ universally and the caller supplies it.
--
-- The repair is not `1 ≤ j′` (which the dispatch cannot supply) but the
-- observation that the length conjunct never came from widening in the
-- first place: `capsOK?` (.Caps-Face/Part1) carries
-- `length (registry st) ≤ᵇ Caps.cReg c` at the POST-state, and PROVEN
-- `frameStep-reg≤size` (.Caps) lifts cReg to cSize at any j.  So the
-- caps face already pays for the entry and this lemma spends its receipt.
--
-- WHAT THE BODY SPENDS, conjunct by conjunct.  Three WIDEN across the one
-- inequality `le` that `frameStep-mono-j` delivers — stBounded? and regsB?
-- through their own -widen lemmas, and the slotsSize conjunct through plain
-- `≤ᵇ-widen`.  Two pass VERBATIM, because they are indexed by Ψ and not by
-- the size: fnCapBounded?, and the slotsFnCap conjunct.  The third is the
-- one that cannot widen, and it is the caps receipt being spent: `cOK′`'s
-- own registry bound lifted from cReg to cSize by `frameStep-reg≤size`.
-- The new registry entry is `pathB?-widen κ le pB`, appended by
-- `all-++-intro`.
--
-- CORRECTED: this paragraph used to say "the other five by widening" and
-- "the two slots conjuncts unchanged (slots never move)".  Slots indeed
-- never move, but conjunct 5 compares slotsSize against B, and B is exactly
-- what grows — so it widens like the rest.  Only the two Ψ-indexed
-- conjuncts are untouched.
--
-- PROVEN TWIN: `register-INV` (.Wet/Part1) is this statement on the
-- `capᴱ W E` ladder — same five arms in the same order, and its `regOK`
-- transfers under the ladder substitution.  Only the length arm differs,
-- and that difference is the whole point of the caps hypothesis: there it
-- comes from the ×2 ledger edge, here it is SPENT from the caps receipt,
-- which is why this face survives j′ = 0 where an unconditional
-- restatement would not.
--
-- The scripted census's shape B needs exactly this lemma too, so
-- input-wet-scripted-four spends it rather than restating it.
shared-live-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ j j′ : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  Caps.cReg c ≤ Caps.cSize c →
  capsOK? (frameStep (j + j′) c) sched (register src κ st) ≡ true →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  INV? Ψ (Caps.cSize (frameStep (j + j′) c)) sched (register src κ st) ≡ true
shared-live-INV {u = u} c Ψ j j′ src κ sched st 2≤S hCR cOK′ inv pB
  with INV-parts Ψ (Caps.cSize (frameStep j c)) sched st inv
... | sb , fc , rl , rb , ss , sf =
  ∧-intro (stBounded-widen le sched st sb)
  (∧-intro fc
  (∧-intro lenOK
  (∧-intro regOK
  (∧-intro (≤ᵇ-widen (slotsSize (Sched.slots sched)) le ss) sf))))
  where
  le : Caps.cSize (frameStep j c) ≤ Caps.cSize (frameStep (j + j′) c)
  le = proj₁ (frameStep-mono-j c 2≤S (m≤m+n j j′))
  lenOK : (length (EvalSt.registry st
                   ++ (EvalSt.nextReg st , src , u , κ) ∷ [])
            ≤ᵇ Caps.cSize (frameStep (j + j′) c)) ≡ true
  regCap : (length (EvalSt.registry st
                    ++ (EvalSt.nextReg st , src , u , κ) ∷ [])
             ≤ᵇ Caps.cReg (frameStep (j + j′) c)) ≡ true
  regCap = proj₂ (proj₂ (proj₂ (proj₂
    (capsOK?-parts (frameStep (j + j′) c) sched (register src κ st) cOK′))))
  lenOK = ≤ᵇ-widen (length (EvalSt.registry st
                            ++ (EvalSt.nextReg st , src , u , κ) ∷ []))
            (frameStep-reg≤size c (j + j′) (≤-trans (s≤s z≤n) 2≤S) hCR)
            regCap
  regOK : regsB? (Caps.cSize (frameStep (j + j′) c)) Ψ
            (EvalSt.registry st
             ++ (EvalSt.nextReg st , src , u , κ) ∷ []) ≡ true
  regOK = all-++-intro _ (EvalSt.registry st) _
            (regsB?-widen (EvalSt.registry st) le rb)
            (∧-intro (pathB?-widen κ le pB) refl)

-- ARM C's RECURSIVE WALK, ASSEMBLED.  This is `wl` at the slot's stored
-- def and nothing else: `sharedConnect` makes exactly ONE recursive call,
-- at `peelGas g`, which is `wl`'s own index — so what was owed here was a
-- call-site discharge, never a second induction.
--
-- REPORTING AT ITS OWN LEVEL IS THE POINT, and it is what keeps this
-- statement smaller than its parent rather than a renaming of it.  The
-- parent receives caps receipts at the CALLER's level and reconciles the
-- two by re-indexing, which costs only a size receipt because every
-- Ψ-indexed conjunct is level-free; so no level arithmetic belongs here.
-- The walk's own `j′` is delivered and the parent moves it.
--
-- THE HYPOTHESES `wl` WANTS THAT THIS TELESCOPE DOES NOT HOLD are the
-- whole content of the body, and they share one cause: every size and
-- width bound here is at `b = inputᶜ i` while `wl` runs at `d`, the slot's
-- DEF, and no arithmetic gets from the input's size to the def's.  The
-- proven caps twin (`sharedConnect-caps`, .Subscribe-Face) shows nothing
-- about them, because it TAKES both of the first two as hypotheses and
-- lets its caller supply them.  They come out of the SLOT TELESCOPE
-- instead, and the fourth out of the WET invariant:
--
--   sizeᵉ d ≤ cSize     slotsCaps?-lookup refined by the slot equation
--   dWᵉ n sl d ≤ cWid   the same lookup, whose width conjunct is stated at
--                       `pWᵉ = outWᵉ ⊔ dWᵉ` — there is no `dWᵉ` lemma to
--                       look for, only a ⊔-bound
--   suc (sizeᵉ d) ≤ ops NOT inherited at all: `ops` is CHOSEN at the inner
--                       call, and `mu-lvl-desc` fixes the choice, being
--                       the only descent that pays for the level step
--   fnCapᵉ d ≤ Ψ        INV?'s LAST conjunct, `slotsFnCap sl ≤ Ψ`,
--                       projected at i.  Worth naming separately: it is
--                       the one ingredient off the wet invariant rather
--                       than the caps telescope, and the inventory that
--                       earned this row its class missed it
--
-- ⚠ unconn-insert AND share-step WERE BOTH NEARLY REWRITTEN while taking
-- that inventory; `unconn-insert` sits thirty lines under `unconn-cons-≤`,
-- which is the ≤ half every other consumer wants.  Searching for the ≤
-- form and stopping is how that happens.
--
-- ⚠ THE HOP CONJUNCT IS TIGHT — THERE IS NO SPARE UNIT.  A note here once
-- claimed it is stated at `suc (hopDᵉ F η b)`, "one MORE than the scripted
-- side", with the suc unspent; the declaration below has no `suc` at all.
-- So the widening from the def's own hop depth to the input's has to land
-- at EQUALITY, and the route that does is `hopDᵉ F η (input i) = η i =
-- slotHop F sl i` against PROVEN slotHop-fix — not an arithmetic slack
-- that does not exist.
--
-- SEALED, and this is not optional: the row is consumed transitively by
-- `budget-sufficient`, whose towers OOM the checker on an unfoldable body
-- on this spine.  The untyped `where` bindings rule out a plain `abstract`
-- block, so this takes the mandated private-impl plus abstract-alias shape.
private
  sharedConnect-inner-wet-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ)
    (fuel : Gas) → WalkLevelAt fuel →
    ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    b ≡ inputᶜ i →
    -- FRESHNESS, added 2026-08-20, and it is a PRECONDITION OF THE
    -- OPERATION rather than a convenience of today's caller — which is
    -- what makes this a restatement of a true theorem and not a
    -- weakening.  `subscribeSharedSlot` (Rx/Evaluator:1388-1396) reaches
    -- `sharedConnect` only in the `else` of `if memberSource (toℕ i)
    -- (EvalSt.connectedShares st)`, so the evaluator NEVER runs this
    -- operation on an already-connected share; the unconditioned
    -- statement was about a case that does not occur.
    --
    -- Without it two of this row's own named ingredients do not apply:
    -- `share-step` (.Caps-Nest) and `unconn-insert` (.Measures) each take
    -- this equation as a premise, and no route avoids them, because
    -- `residAt sl cs i` is `if memberSource (toℕ i) cs then 0 else
    -- syncSizeᵉ d` — a connected slot donates ZERO, leaving `nest d sl
    -- (i ∷ cs) ≤ bud-1` unreachable and `dBound-connect`'s `U′ < U`
    -- unavailable, so the single recursive `wl` call cannot be funded.
    memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
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
    -- depthCONN, not depthE, and this is forced rather than cosmetic: in
    -- the dispatch's arm C the slot scrutinee is with-abstracted, so a
    -- `depthE g b κ …` hypothesis there reduces to `depthConn g i d′ κ …`
    -- while the caller's own `dpt` still reads `depthSlot … (Sched.slots
    -- sched i)`, and the two are not convertible.  Stating it at depthConn
    -- also puts this face on exactly the proven twin's telescope
    -- (sharedConnect-caps, .Subscribe-Face), which is where it belongs.
    depthConn (gs fuel) i d κ bid now sched st ≤ dep →
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
    gs fuel hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE fuel d (share-sink i) bid now sched
              (register (toℕ i) κ
                (record st { connectedShares =
                               toℕ i ∷ EvalSt.connectedShares st }))
    in Σ ℕ λ j₂ →
       (INV? Ψ (Caps.cSize (frameStep (suc j + j₂) c))
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (suc j + j₂) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
  sharedConnect-inner-wet-go {n = n} {Γ = Γ} c Ψ F Ŝ R̂ G ℓ L̂ dep (suc bud′) (suc ops′) j fuel wl i _ κ
    bid now sl sched st d {ok = ok} slotEq refl fresh 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC
    (s≤s nstᵖ) (s≤s _) dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
      j′
    , iINV
    , iBB
    , subst (λ h → burstHopD? F (slotHop F sl) h burst ≡ true) (sym HOPEQ) iHOP
    , iDRY
    , iRGS
    where
    cs    = EvalSt.connectedShares st
    st₀   = record st { connectedShares = toℕ i ∷ cs }
    st₁   = register (toℕ i) κ st₀
    res   = subscribeE fuel d (share-sink i) bid now sched st₁
    burst = proj₁ res
    -- the slot equation at `sl`: the caller states it at `Sched.slots
    -- sched`, and every slot lemma below wants it at `sl`
    slEqi : sl i ≡ shared d {ok = ok}
    slEqi = trans (sym (cong (λ y → y i) slEq)) slotEq
    jsuc : j + 1 ≡ suc j
    jsuc = +-comm j 1
    -- THE SLOT TELESCOPE'S OWN SIDE CONDITION, at the def
    sd = subst (λ s → slotCaps? (Caps.cSize c) (Caps.cWid c) sl s ≡ true) slEqi
               (slotsCaps?-lookup (Caps.cSize c) (Caps.cWid c) sl i slC)
    szd : sizeᵉ d ≤ Caps.cSize c
    szd = ≤ᵇ⇒≤ (sizeᵉ d) (Caps.cSize c)
            (T-to (proj₁ (∧-true (sizeᵉ d ≤ᵇ Caps.cSize c) _ sd)))
    wdd : dWᵉ n sl d ≤ Caps.cWid c
    wdd = ≤-trans (m≤n⊔m _ (dWᵉ n sl d))
            (≤ᵇ⇒≤ (pWᵉ n sl d) (Caps.cWid c)
              (T-to (proj₁ (∧-true (pWᵉ n sl d ≤ᵇ Caps.cWid c) _
                             (proj₂ (∧-true (sizeᵉ d ≤ᵇ Caps.cSize c) _ sd))))))
    szdJ : sizeᵉ d ≤ Caps.cSize (frameStep (j + 1) c)
    szdJ = ≤-trans szd (cSize≤frameStep c (j + 1) 2≤S)
    wddJ : dWᵉ n sl d ≤ Caps.cWid (frameStep (j + 1) c)
    wddJ = ≤-trans wdd (cWid≤frameStep c (j + 1) 2≤S)
    -- the reset cap dominates `c` itself, through the free ceiling
    c≤Ŝ : Caps.cSize c ≤ Ŝ
    c≤Ŝ = ≤-trans (cSize≤frameStep c L̂ 2≤S) ceil
    -- the register lands the level at `suc j`; everything below is stated
    -- at `j + 1`, which is where shared-live-INV and mu-lvl-desc deliver
    CAPS₁ : capsOK? (frameStep (j + 1) c) sched st₁ ≡ true
    CAPS₁ = subst (λ x → capsOK? (frameStep x c) sched st₁ ≡ true) (sym jsuc)
              (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R cOK pSz)
    INV₁ : INV? Ψ (Caps.cSize (frameStep (j + 1) c)) sched st₁ ≡ true
    INV₁ = shared-live-INV c Ψ j 1 (toℕ i) κ sched st₀ 2≤S hCR CAPS₁ invW pB
    fnCd : fnCapᵉ d ≤ Ψ
    fnCd = ≤-trans
             (subst (λ s → slotFnCap s ≤ slotsFnCap sl) slEqi
                    (fᵢ≤sum-tab (λ k → slotFnCap (sl k)) i))
             (≤ᵇ⇒≤ (slotsFnCap sl) Ψ
                (T-to (subst (λ y → (slotsFnCap y ≤ᵇ Ψ) ≡ true) slEq
                         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
                           (INV-parts Ψ (Caps.cSize (frameStep j c)) sched st invW)))))))))
    -- the nesting the connect edge spends, and the demand it funds
    NST : nest d sl (toℕ i ∷ cs) ≤ bud′
    NST = share-step sl cs i bud′ slEqi fresh (s≤s nstᵖ)
    G′ = dBound Ŝ R̂ (unconn sl (toℕ i ∷ cs))
                (hopDᵉ F (slotHop F sl) d) (syncSizeᵉ d)
    -- THE EDGE IS ALREADY PROVEN (.Wet/Part6's `connect-edge`), and its
    -- statement is this composition verbatim — the u-drop, the hop cap and the
    -- syncSize link, pinned at the honest `slotHop Ŝ sl` environment.  Nothing
    -- of it is re-derived here; all that remains is the F/R̂-to-Ŝ transport the
    -- telescope's two reset-anchor pins license.
    DESC : suc G′ ≤ G
    DESC = ≤-trans
             (subst₂ (λ f r →
                 suc (dBound Ŝ r (unconn sl (toℕ i ∷ cs))
                             (hopDᵉ f (slotHop f sl) d) (syncSizeᵉ d))
                   ≤ dBound Ŝ r (unconn sl cs)
                             (hopDᵉ f (slotHop f sl) (inputᶜ {Γ = Γ} i))
                             (syncSizeᵉ (inputᶜ {Γ = Γ} i)))
                (sym fS) (sym rS)
                (connect-edge Ŝ (hopDᵉ Ŝ (slotHop Ŝ sl) (inputᶜ {Γ = Γ} i))
                                (syncSizeᵉ (inputᶜ {Γ = Γ} i))
                   s2 sl (≤-trans slSz c≤Ŝ) cs i slEqi fresh
                   (≤-trans szd c≤Ŝ)))
             dmd
    LB : opIterD (Caps.cSize c) (Caps.cWid c) dep bud′
                 (suc (Caps.cSize (frameStep (j + 1) c))) (j + 1) ≤ L̂
    LB = ≤-trans (mu-lvl-desc c dep bud′ ops′ j 1 2≤S
                    (≤-trans (≤-reflexive jsuc)
                             (s≤s (m≤m+n j (suc (Caps.cSize (frameStep j c))
                                              * suc (Caps.cSize (frameStep j c)))))))
                 lb
    IH = wl d c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud′
           (suc (Caps.cSize (frameStep (j + 1) c))) (j + 1)
           (share-sink i) bid now sl sched st₁
           2≤S 1≤R hCR slEq slC slSz CAPS₁ szdJ wddJ refl
           (≤-trans (s≤s z≤n) (≤-trans 2≤S (cSize≤frameStep c (j + 1) 2≤S)))
           NST (s≤s szdJ) dpt INV₁ fnCd refl
           s2 fS rS ceil LB ≤-refl
           (hasAtLeast-mono DESC (hasAtLeast-peel-gs gas))
           (≤-trans (≤-trans (n≤1+n G′) DESC)
                    (≤-trans (m≤n+m G (pathLen κ)) lℓ))
           (register-regsLen ℓ (toℕ i) κ st₀
             (≤-trans (m≤m+n (pathLen κ) G) lℓ) rgs)
    j′ = proj₁ IH
    -- the walk reports at `(j + 1) + j′`; the statement reads `suc j + j′`
    lvl : (j + 1) + j′ ≡ suc j + j′
    lvl = cong (_+ j′) jsuc
    R1 = proj₂ IH
    R2 = proj₂ R1
    R3 = proj₂ R2
    R4 = proj₂ R3
    R5 = proj₂ R4
    R6 = proj₂ R5
    R7 = proj₂ R6
    R8 = proj₂ R7
    iINV = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                          (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
                 lvl (proj₁ R5)
    iBB  = subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ burst ≡ true)
                 lvl (proj₁ R6)
    iHOP = proj₁ R7
    iDRY = proj₁ R8
    iRGS = proj₂ R8
    -- the hop transport, at EQUALITY (see the header)
    HOPEQ : hopDᵉ F (slotHop F sl) (inputᶜ {Γ = Γ} i) ≡ hopDᵉ F (slotHop F sl) d
    HOPEQ = slotHop-fix F sl i slEqi

abstract
  sharedConnect-inner-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ)
    (fuel : Gas) → WalkLevelAt fuel →
    ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    b ≡ inputᶜ i →
    -- FRESHNESS, added 2026-08-20, and it is a PRECONDITION OF THE
    -- OPERATION rather than a convenience of today's caller — which is
    -- what makes this a restatement of a true theorem and not a
    -- weakening.  `subscribeSharedSlot` (Rx/Evaluator:1388-1396) reaches
    -- `sharedConnect` only in the `else` of `if memberSource (toℕ i)
    -- (EvalSt.connectedShares st)`, so the evaluator NEVER runs this
    -- operation on an already-connected share; the unconditioned
    -- statement was about a case that does not occur.
    --
    -- Without it two of this row's own named ingredients do not apply:
    -- `share-step` (.Caps-Nest) and `unconn-insert` (.Measures) each take
    -- this equation as a premise, and no route avoids them, because
    -- `residAt sl cs i` is `if memberSource (toℕ i) cs then 0 else
    -- syncSizeᵉ d` — a connected slot donates ZERO, leaving `nest d sl
    -- (i ∷ cs) ≤ bud-1` unreachable and `dBound-connect`'s `U′ < U`
    -- unavailable, so the single recursive `wl` call cannot be funded.
    memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
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
    -- depthCONN, not depthE, and this is forced rather than cosmetic: in
    -- the dispatch's arm C the slot scrutinee is with-abstracted, so a
    -- `depthE g b κ …` hypothesis there reduces to `depthConn g i d′ κ …`
    -- while the caller's own `dpt` still reads `depthSlot … (Sched.slots
    -- sched i)`, and the two are not convertible.  Stating it at depthConn
    -- also puts this face on exactly the proven twin's telescope
    -- (sharedConnect-caps, .Subscribe-Face), which is where it belongs.
    depthConn (gs fuel) i d κ bid now sched st ≤ dep →
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
    gs fuel hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE fuel d (share-sink i) bid now sched
              (register (toℕ i) κ
                (record st { connectedShares =
                               toℕ i ∷ EvalSt.connectedShares st }))
    in Σ ℕ λ j₂ →
       (INV? Ψ (Caps.cSize (frameStep (suc j + j₂) c))
              (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (suc j + j₂) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
  sharedConnect-inner-wet = sharedConnect-inner-wet-go

-- ARM C, ASSEMBLED — AND THE ARM IS NOW POSTULATE-FREE.  The wrap and the
-- level reconciliation are checked here; the recursive walk is checked in
-- `sharedConnect-inner-wet` above, which is a real body over `wl` and holds
-- no leaf of its own.
--
-- THE SPLIT IS THE WHOLE CONTENT.  Both of the level-sensitive conjuncts
-- factor into a B-indexed half and a Ψ-indexed half, and the Ψ half
-- MENTIONS NO LEVEL — so the walk's facts, which arrive at whatever level
-- the recursion happened to reach, cross to the caller's level without any
-- ordering between the two bounds at all: the Ψ half is carried untouched
-- and the size half is RE-SUPPLIED from the caps receipt this statement
-- already takes as a hypothesis.  That is `INV?-reindex` and
-- `burstB?-reindex` (.Psi-Split), and it is why this face can be stated at
-- a fixed caller-supplied level and still be provable.
--
-- ⚠ A LEVEL RECONCILIATION READ AS UNPROVABLE HERE FOR A WHILE, and the
-- reading nearly bought a restatement of five definitions in this family.
-- What was missing was not a lemma but the observation above; the split and
-- the zips were already proven and already in the tree.  Read
-- `INV?-reindex`'s own header before concluding that two levels have to be
-- ordered.
--
-- THE OTHER THREE CONJUNCTS ARE THE WRAP, and they are computation plus a
-- relabel.  The prepended emit carries `init` and `close _ exhausted`
-- only: `hopDev?` is `true` on both and `dryEvent` fires on `close _
-- dried` ALONE, so the hop and dry conjuncts are `refl` on the prepend and
-- a `sharedPlumb` transport on the tail.  The latch arm's registry shrinks
-- under `dropSource`, and `regsLen?` is an `all`, so `dropSource-all`
-- carries it.
--
-- THE HYPOTHESIS LIST IS THE DISPATCH'S VERBATIM, so arm C's caller passes
-- it straight through and no call-site arithmetic hides here.
--
-- SEALED, and this is not optional: the row is consumed transitively by
-- `budget-sufficient`, whose towers OOM the checker on an unfoldable body
-- on this spine.  The with-abstraction and the untyped `where` bindings
-- rule out a plain `abstract` block, so this takes the mandated
-- private-impl plus abstract-alias shape.
private
  sharedConnect-walk-conn-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
    (fuel : Gas) → WalkLevelAt fuel →
    ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    b ≡ inputᶜ i →
    -- FRESHNESS, added 2026-08-20, and it is a PRECONDITION OF THE
    -- OPERATION rather than a convenience of today's caller — which is
    -- what makes this a restatement of a true theorem and not a
    -- weakening.  `subscribeSharedSlot` (Rx/Evaluator:1388-1396) reaches
    -- `sharedConnect` only in the `else` of `if memberSource (toℕ i)
    -- (EvalSt.connectedShares st)`, so the evaluator NEVER runs this
    -- operation on an already-connected share; the unconditioned
    -- statement was about a case that does not occur.
    --
    -- Without it two of this row's own named ingredients do not apply:
    -- `share-step` (.Caps-Nest) and `unconn-insert` (.Measures) each take
    -- this equation as a premise, and no route avoids them, because
    -- `residAt sl cs i` is `if memberSource (toℕ i) cs then 0 else
    -- syncSizeᵉ d` — a connected slot donates ZERO, leaving `nest d sl
    -- (i ∷ cs) ≤ bud-1` unreachable and `dBound-connect`'s `U′ < U`
    -- unavailable, so the single recursive `wl` call cannot be funded.
    memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
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
    -- depthCONN, not depthE, and this is forced rather than cosmetic: in
    -- the dispatch's arm C the slot scrutinee is with-abstracted, so a
    -- `depthE g b κ …` hypothesis there reduces to `depthConn g i d′ κ …`
    -- while the caller's own `dpt` still reads `depthSlot … (Sched.slots
    -- sched i)`, and the two are not convertible.  Stating it at depthConn
    -- also puts this face on exactly the proven twin's telescope
    -- (sharedConnect-caps, .Subscribe-Face), which is where it belongs.
    depthConn (gs fuel) i d κ bid now sched st ≤ dep →
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
    gs fuel hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = sharedConnect (gs fuel) i d κ bid now sched st
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
  sharedConnect-walk-conn-go {Γ = Γ} c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ fuel wl i b κ bid now sl
    sched st d slotEq bEq fresh 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
    s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
    with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) bid now sched
                                 (register (toℕ i) κ
                                   (record st { connectedShares =
                                                  toℕ i ∷ EvalSt.connectedShares st }))))
  ... | true =
      INV?-reindex Ψ B₂ B′ sched₁ DROP (proj₁ WRAP) (proj₁ CP) RL (proj₁ (proj₂ CP)) SS
    , burstB?-reindex (frameStep (j + j′) c) sl B₂ Ψ
        (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
            at bid from toℕ i as subscribe) ∷ sharedPlumb burst)
        (proj₂ WRAP) bC
    , ∧-intro refl
        (sharedPlumb-hopD F (slotHop F sl) (hopDᵉ F (slotHop F sl) b) burst iHOP)
    , sharedPlumb-nodry burst iDRY
    , dropSource-all (λ en → pathLen (proj₂ (proj₂ (proj₂ en))) ≤ᵇ ℓ)
        (toℕ i) (EvalSt.registry st₂) iRGS
    where
    st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
    st₁ = register (toℕ i) κ st₀
    res = subscribeE fuel d (share-sink i) bid now sched st₁
    burst  = proj₁ res
    sched₁ = proj₁ (proj₂ res)
    st₂    = proj₂ (proj₂ res)
    DROP = record st₂ { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                      ; completedSources = toℕ i ∷ EvalSt.completedSources st₂ }
    IW = sharedConnect-inner-wet c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j fuel wl i b κ bid now sl
           sched st d slotEq bEq fresh 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx
           dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs
    j₂ = proj₁ IW
    B₂ = Caps.cSize (frameStep (suc j + j₂) c)
    B′ = Caps.cSize (frameStep (j + j′) c)
    iINV = proj₁ (proj₂ IW)
    iBB  = proj₁ (proj₂ (proj₂ IW))
    iHOP = proj₁ (proj₂ (proj₂ (proj₂ IW)))
    iDRY = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IW))))
    iRGS = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IW))))
    WRAP = connectWrap-wet Ψ B₂ i bid true burst sched₁ st₂ iINV iBB
    CP = capsOK?-parts (frameStep (j + j′) c) sched₁ DROP cOK′
    RL = ≤ᵇ-widen (length (EvalSt.registry DROP))
           (frameStep-reg≤size c (j + j′) (≤-trans (s≤s z≤n) 2≤S) hCR)
           (proj₂ (proj₂ (proj₂ (proj₂ CP))))
    slEq₁ : Sched.slots sched₁ ≡ sl
    slEq₁ = trans (KeepsC.slotsEq
                     (subscribeE-keeps fuel d (share-sink i) bid now sched st₁)) slEq
    c≤B′ : Caps.cSize c ≤ B′
    c≤B′ = subst (λ x → Caps.cSize x ≤ B′) (frameStep-0 c)
             (proj₁ (frameStep-mono-j c 2≤S {0} {j + j′} z≤n))
    SS = T⇒≡true _ (≤⇒≤ᵇ (subst (λ x → slotsSize x ≤ B′) (sym slEq₁)
                                (≤-trans slSz c≤B′)))
  ... | false =
      INV?-reindex Ψ B₂ B′ sched₁ st₂ (proj₁ WRAP) (proj₁ CP) RL (proj₁ (proj₂ CP)) SS
    , burstB?-reindex (frameStep (j + j′) c) sl B₂ Ψ
        (((init (toℕ i) ∷ []) at bid from toℕ i as subscribe) ∷ sharedPlumb burst)
        (proj₂ WRAP) bC
    , ∧-intro refl
        (sharedPlumb-hopD F (slotHop F sl) (hopDᵉ F (slotHop F sl) b) burst iHOP)
    , sharedPlumb-nodry burst iDRY
    , iRGS
    where
    st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
    st₁ = register (toℕ i) κ st₀
    res = subscribeE fuel d (share-sink i) bid now sched st₁
    burst  = proj₁ res
    sched₁ = proj₁ (proj₂ res)
    st₂    = proj₂ (proj₂ res)
    IW = sharedConnect-inner-wet c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j fuel wl i b κ bid now sl
           sched st d slotEq bEq fresh 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx
           dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs
    j₂ = proj₁ IW
    B₂ = Caps.cSize (frameStep (suc j + j₂) c)
    B′ = Caps.cSize (frameStep (j + j′) c)
    iINV = proj₁ (proj₂ IW)
    iBB  = proj₁ (proj₂ (proj₂ IW))
    iHOP = proj₁ (proj₂ (proj₂ (proj₂ IW)))
    iDRY = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IW))))
    iRGS = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IW))))
    WRAP = connectWrap-wet Ψ B₂ i bid false burst sched₁ st₂ iINV iBB
    CP = capsOK?-parts (frameStep (j + j′) c) sched₁ st₂ cOK′
    RL = ≤ᵇ-widen (length (EvalSt.registry st₂))
           (frameStep-reg≤size c (j + j′) (≤-trans (s≤s z≤n) 2≤S) hCR)
           (proj₂ (proj₂ (proj₂ (proj₂ CP))))
    slEq₁ : Sched.slots sched₁ ≡ sl
    slEq₁ = trans (KeepsC.slotsEq
                     (subscribeE-keeps fuel d (share-sink i) bid now sched st₁)) slEq
    c≤B′ : Caps.cSize c ≤ B′
    c≤B′ = subst (λ x → Caps.cSize x ≤ B′) (frameStep-0 c)
             (proj₁ (frameStep-mono-j c 2≤S {0} {j + j′} z≤n))
    SS = T⇒≡true _ (≤⇒≤ᵇ (subst (λ x → slotsSize x ≤ B′) (sym slEq₁)
                                (≤-trans slSz c≤B′)))

abstract
  sharedConnect-walk-conn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
    (fuel : Gas) → WalkLevelAt fuel →
    ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    b ≡ inputᶜ i →
    -- FRESHNESS, added 2026-08-20, and it is a PRECONDITION OF THE
    -- OPERATION rather than a convenience of today's caller — which is
    -- what makes this a restatement of a true theorem and not a
    -- weakening.  `subscribeSharedSlot` (Rx/Evaluator:1388-1396) reaches
    -- `sharedConnect` only in the `else` of `if memberSource (toℕ i)
    -- (EvalSt.connectedShares st)`, so the evaluator NEVER runs this
    -- operation on an already-connected share; the unconditioned
    -- statement was about a case that does not occur.
    --
    -- Without it two of this row's own named ingredients do not apply:
    -- `share-step` (.Caps-Nest) and `unconn-insert` (.Measures) each take
    -- this equation as a premise, and no route avoids them, because
    -- `residAt sl cs i` is `if memberSource (toℕ i) cs then 0 else
    -- syncSizeᵉ d` — a connected slot donates ZERO, leaving `nest d sl
    -- (i ∷ cs) ≤ bud-1` unreachable and `dBound-connect`'s `U′ < U`
    -- unavailable, so the single recursive `wl` call cannot be funded.
    memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
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
    -- depthCONN, not depthE, and this is forced rather than cosmetic: in
    -- the dispatch's arm C the slot scrutinee is with-abstracted, so a
    -- `depthE g b κ …` hypothesis there reduces to `depthConn g i d′ κ …`
    -- while the caller's own `dpt` still reads `depthSlot … (Sched.slots
    -- sched i)`, and the two are not convertible.  Stating it at depthConn
    -- also puts this face on exactly the proven twin's telescope
    -- (sharedConnect-caps, .Subscribe-Face), which is where it belongs.
    depthConn (gs fuel) i d κ bid now sched st ≤ dep →
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
    gs fuel hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = sharedConnect (gs fuel) i d κ bid now sched st
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
  sharedConnect-walk-conn = sharedConnect-walk-conn-go


-- ARM C, ASSEMBLED — the gas split, and the g0 half is CLOSED HERE.
-- `sharedConnect g0 = dryBurst id` would emit `close _ dried` and so fail
-- this statement's own `hasDry ≡ false` outright; the clause is discharged
-- not by proving anything about `dryBurst` but by observing that the case
-- cannot arise.  `_hasAtLeast_` has two constructors, `hz` at index `zero`
-- and `hs` at gas `gs _`, so `g0 hasAtLeast suc G` is uninhabited and `gas`
-- is an absurd pattern.  This is the same reason walk-mu's g0 clause closes,
-- and it is worth doing as a real clause rather than folding into the leaf:
-- what is left over is a statement whose gas is a KNOWN SUCCESSOR, which is
-- the precondition of every remaining step — `wl` runs at `peelGas g`, and
-- only at `gs fuel` does that reduce to something the recursive call can be
-- funded from.
--
-- ⚠ THE UNDERSCORES ARE POSITIONAL AND THERE ARE TWENTY-FOUR OF THEM.  The
-- hypothesis list was counted mechanically off the declaration, not by eye,
-- and `gas` is the twenty-fifth; the sibling call site in
-- `input-wet-shared` below spells every one of them, which is the check.
sharedConnect-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas) → WalkLevelAt (peelGas g) →
  ∀ (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
  (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
  Sched.slots sched i ≡ shared d {ok = ok} →
  b ≡ inputᶜ i →
  -- FRESHNESS, added 2026-08-20, and it is a PRECONDITION OF THE
  -- OPERATION rather than a convenience of today's caller — which is
  -- what makes this a restatement of a true theorem and not a
  -- weakening.  `subscribeSharedSlot` (Rx/Evaluator:1388-1396) reaches
  -- `sharedConnect` only in the `else` of `if memberSource (toℕ i)
  -- (EvalSt.connectedShares st)`, so the evaluator NEVER runs this
  -- operation on an already-connected share; the unconditioned
  -- statement was about a case that does not occur.
  --
  -- Without it two of this row's own named ingredients do not apply:
  -- `share-step` (.Caps-Nest) and `unconn-insert` (.Measures) each take
  -- this equation as a premise, and no route avoids them, because
  -- `residAt sl cs i` is `if memberSource (toℕ i) cs then 0 else
  -- syncSizeᵉ d` — a connected slot donates ZERO, leaving `nest d sl
  -- (i ∷ cs) ≤ bud-1` unreachable and `dBound-connect`'s `U′ < U`
  -- unavailable, so the single recursive `wl` call cannot be funded.
  memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
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
  -- depthCONN, not depthE, and this is forced rather than cosmetic: in
  -- the dispatch's arm C the slot scrutinee is with-abstracted, so a
  -- `depthE g b κ …` hypothesis there reduces to `depthConn g i d′ κ …`
  -- while the caller's own `dpt` still reads `depthSlot … (Sched.slots
  -- sched i)`, and the two are not convertible.  Stating it at depthConn
  -- also puts this face on exactly the proven twin's telescope
  -- (sharedConnect-caps, .Subscribe-Face), which is where it belongs.
  depthConn g i d κ bid now sched st ≤ dep →
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
  let r = sharedConnect g i d κ bid now sched st
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
sharedConnect-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g0 wl i b κ bid now sl
  sched st d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
sharedConnect-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ (gs fuel) wl i b κ bid now sl
  sched st d slotEq bEq fresh 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle =
  sharedConnect-walk-conn c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ fuel wl i b κ bid now sl
    sched st d slotEq bEq fresh 2≤S 1≤R hCR slEq slC slSz cOK szb pSz lC nst hidx dpt invW fnC pB
    s2 fS rS ceil lb dmd gas lℓ rgs cOK′ bC bCnt jle
