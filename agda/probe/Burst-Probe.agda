-- The BURST PROBE: an empirical measurement of what subscription bursts the
-- evaluator actually mints.  It exists to decide one question that no proof in
-- Verify-Well-Formed can decide by itself — whether TailRel's `acc-le` field is
-- vacuous or load-bearing (see the note above `record TailRel`).
--
-- It is built by scripts/burst-probe.sh, which copies agda/src to a scratch
-- project, runs scripts/burst-probe-instrument.py on the copied Rx/Evaluator.agda
-- (adding a write-only `burstLog` to EvalSt and a logging wrapper around
-- subscribeE), drops this module in beside it and compiles.  The verified tree is
-- never touched.  `oneProgram` replays the probe's own drain against the real
-- `evaluate` on every program, so a probe drain that drifted from `drain` is a
-- loud failure rather than a quiet wrong number.  That check runs entirely
-- inside the instrumented build, so it says nothing about whether the
-- instrumentation itself moved the evaluator — what settles THAT is the grep in
-- burst-probe.sh confirming burstLog is written and never read.
--
-- FOUR COUNTERS, per the question they answer:
--
--   0. valsLast   — valsLast? burst, asserted on EVERY burst: a burst carries
--                   its values in its LAST emit or not at all.  This is the
--                   invariant the take-cut argument wants directly — a cut rides
--                   an emit that admitted values, so under valsLast? that emit is
--                   final and the burst tail is empty.  Counter 3ᵗ below is
--                   DOWNSTREAM of it (no tail ⇒ nothing in the tail); this
--                   measures the invariant itself, which is the stronger claim.
--                   `valBursts`/`multiVal` say how much of the corpus can even
--                   witness it: a burst with two value-carrying emits is an
--                   automatic failure, so multiVal must be 0 too.
--   1. fresh      — frameFresh? [] burst, asserted on EVERY burst.  Any failure
--                   is an immediate finding: the discipline Verify-Well-Formed
--                   hypothesises on `cut-cons-joint` would not hold of the
--                   evaluator, and the postulate would be vacuous.
--   2. reach      — bursts carrying a CROSS-EMIT OPEN: a source inited in emit i
--                   still open when emit j > i starts.  Without nonzero reach,
--                   counter 3 measures nothing.
--   3. accClose   — bursts carrying an ACC-MATCHED CLOSE: a close in emit j for a
--                   source opened in an earlier emit i < j of the same burst.
--                   This is the configuration acc-le is about.  `accCloseCut`
--                   narrows it to closes whose reason is cut/cutPending — an
--                   operator severing a registration minted earlier in the same
--                   burst, which is exactly the take-cut case.  `accCloseTail`
--                   narrows it further, to the sub-configuration the transport
--                   (pushBurst-take-zero-transport) actually runs into: an
--                   acc-matched close in an emit STRICTLY AFTER a cutting one,
--                   i.e. inside the tail the transport re-runs at the swept state.
--
-- Counters 0 and 1 are measured with Rx.Protocol's own `valsLast?` / `frameFresh?`
-- — the very predicates the postulates hypothesise — and `walkMismatch`
-- cross-checks the richer walk below against frameFresh?, so the extra
-- bookkeeping cannot drift from the real thing.
module Burst-Probe where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map; length; concat)
                      renaming (_++_ to _++ᴸ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_) renaming (_==_ to _==ˢ_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Fuel; Id; Source; after_,_;
                           ObservableInput; hot; cold;
                           InstEvent; init; value; close; handoff; complete;
                           CloseReason; cut; cutPending; exhausted; dried;
                           EmitKind; subscribe; delivery; plumbing;
                           InstEmit; _at_from_as_)
open import Rx.Exp using (natᵗ; _×ᵗ_; Ctx; Exp; Fn; Closed;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; add)
open import Rx.Evaluator using (Slot; scripted; shared; Slots; Sched; EvalSt;
                                Stream; evaluate; subscribeE; cascade; sched-next;
                                sched-init; st-init; budgetAt; root)
open import Rx.Protocol using (wellFormed?; frameFresh?; valsLast?; hasValue)
open import QuickCheck using (Gen; _>>=G_; pureG; genB; randList; Γ₂;
                              genExp; genSlots;
                              showExp; showSlots; showStream;
                              toCodes; parseNat; numAt; concatStr)
open import CLI.IO

------------------------------------------------------------------------
-- the accumulator walk: frameFresh?'s bookkeeping, plus a per-source flag
-- recording whether that init rode an EARLIER emit.  `removeOne`'s search is
-- front-to-back and inits cons onto the front, so keeping the tagged list in
-- the same order matches frameFreshEv's matching exactly: a close prefers the
-- most recent init, i.e. a same-emit one when there is one.

Tagged : Set
Tagged = List (Source × Bool)   -- Bool: opened in an earlier emit

-- remove the first entry for s, reporting whether it was an earlier-emit open
takeTagged : Source → Tagged → Maybe (Bool × Tagged)
takeTagged s []              = nothing
takeTagged s ((x , b) ∷ xs) with s ≡ᵇ x
... | true  = just (b , xs)
... | false with takeTagged s xs
...   | just (b′ , xs′) = just (b′ , (x , b) ∷ xs′)
...   | nothing         = nothing

record Walk : Set where       -- the running result of one burst's walk
  constructor mkWalk
  field ok         : Bool     -- still frameFresh
        acc        : Tagged
        crossOpen  : Bool     -- some emit began with a nonempty accumulator
        matched    : Bool     -- some close resolved against an earlier-emit init
        matchedCut : Bool     -- …and its reason was cut / cutPending
        -- the take-cut geometry.  The transport (pushBurst-take-zero-transport)
        -- runs the burst TAIL — the emits strictly after the cutting one — at the
        -- post-cut state, so an acc-matched close only endangers it when it lands
        -- in that tail.  An acc-matched close riding the CUTTING emit is a
        -- different (and harmless-to-the-transport) fact.
        cutHere    : Bool     -- this emit carried a severing close
        cutEarlier : Bool     -- a strictly earlier emit did
        cutNotLast : Bool     -- some emit followed a cutting emit (tail nonempty)
        matchedTail : Bool    -- an acc-matched close landed in such a tail

severing : CloseReason → Bool
severing cut        = true
severing cutPending = true
severing exhausted  = false
severing dried      = false

walkEv : List (InstEvent ⊤) → Walk → Walk
walkEv []                w = w
walkEv (init s    ∷ es) w = walkEv es (record w { acc = (s , false) ∷ Walk.acc w })
walkEv (value _   ∷ es) w = walkEv es w
walkEv (complete  ∷ es) w = walkEv es w
walkEv (handoff _ ∷ es) w = record w { ok = false }   -- foldPath-only: not a burst event
walkEv (close s r ∷ es) w with takeTagged s (Walk.acc w)
... | nothing            = record w { ok = false }
... | just (older , acc′) =
      walkEv es (record w
        { acc         = acc′
        ; matched     = Walk.matched w ∨ older
        ; matchedCut  = Walk.matchedCut w ∨ (older ∧ severing r)
        ; matchedTail = Walk.matchedTail w ∨ (older ∧ Walk.cutEarlier w)
        ; cutHere     = Walk.cutHere w ∨ severing r })

-- age the accumulator: everything still open belongs to an earlier emit now
age : Tagged → Tagged
age = map (λ p → proj₁ p , true)

nonEmpty : {A : Set} → List A → Bool
nonEmpty []      = false
nonEmpty (_ ∷ _) = true

-- an emit STARTS with the (aged) accumulator and with the cut flags rolled
-- forward; crossOpen is charged when it began nonempty — i.e. an earlier emit of
-- this same burst left a source open — and cutNotLast when it began after a cut
walkStep : InstEmit ⊤ → Walk → Walk
walkStep e w₀ =
  let aged   = age (Walk.acc w₀)
      earlier = Walk.cutEarlier w₀ ∨ Walk.cutHere w₀
  in walkEv (InstEmit.events e)
       (record w₀ { acc        = aged
                  ; crossOpen  = Walk.crossOpen w₀ ∨ nonEmpty aged
                  ; cutHere    = false
                  ; cutEarlier = earlier
                  ; cutNotLast = Walk.cutNotLast w₀ ∨ earlier })

walkBurst : List (InstEmit ⊤) → Walk → Walk
walkBurst []         w = w
walkBurst (em ∷ ems) w with InstEmit.kind em
... | delivery  = record w { ok = false }   -- a delivery emit never rides a burst
... | subscribe = walkBurst ems (walkStep em w)
... | plumbing  = walkBurst ems (walkStep em w)

walk0 : Walk
walk0 = mkWalk true [] false false false false false false false

walkOf : List (InstEmit ⊤) → Walk
walkOf b = walkBurst b walk0

anyCut : Walk → Bool
anyCut w = Walk.cutHere w ∨ Walk.cutEarlier w

------------------------------------------------------------------------
-- the counters

record Stats : Set where
  constructor mkStats
  field programs selfFail wfFail bursts multiEmit freshFail walkMismatch : ℕ
  field reach accClose accCloseCut cutBursts cutNotLast accCloseTail : ℕ
  field valsFail valBursts multiVal : ℕ

zeroStats : Stats
zeroStats = mkStats 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

_+ˢ_ : Stats → Stats → Stats
mkStats a b c d e f m g h i j k l p q r
  +ˢ mkStats a′ b′ c′ d′ e′ f′ m′ g′ h′ i′ j′ k′ l′ p′ q′ r′ =
  mkStats (a + a′) (b + b′) (c + c′) (d + d′) (e + e′) (f + f′) (m + m′)
          (g + g′) (h + h′) (i + i′) (j + j′) (k + k′) (l + l′)
          (p + p′) (q + q′) (r + r′)

b→ℕ : Bool → ℕ
b→ℕ true  = 1
b→ℕ false = 0

isMulti : {A : Set} → List A → Bool
isMulti []           = false
isMulti (_ ∷ [])     = false
isMulti (_ ∷ _ ∷ _)  = true

-- how many emits of the burst carry a payload.  0 or 1 is consistent with
-- valsLast?; 2 or more is an automatic violation, so this is the direct
-- measure of "can two payloads ride one subscribe frame at all"
valEmits : List (InstEmit ⊤) → ℕ
valEmits []         = 0
valEmits (em ∷ ems) = b→ℕ (hasValue (InstEmit.events em)) + valEmits ems

-- counters 0 and 1 are Rx.Protocol's own predicates; the walk's `ok` is only
-- cross-checked against frameFresh?, never substituted for it
burstStats : List (InstEmit ⊤) → Stats
burstStats b =
  let w     = walkOf b
      fresh = frameFresh? [] b
      nv    = valEmits b
  in mkStats 0 0 0 1 (b→ℕ (isMulti b)) (b→ℕ (not fresh))
             (b→ℕ (not (fresh xnor Walk.ok w)))
             (b→ℕ (Walk.crossOpen w)) (b→ℕ (Walk.matched w))
             (b→ℕ (Walk.matchedCut w)) (b→ℕ (anyCut w))
             (b→ℕ (Walk.cutNotLast w)) (b→ℕ (Walk.matchedTail w))
             (b→ℕ (not (valsLast? b))) (b→ℕ (1 ≤ᵇ nv)) (b→ℕ (2 ≤ᵇ nv))
  where
  _xnor_ : Bool → Bool → Bool
  true  xnor y = y
  false xnor y = not y

sumStats : List Stats → Stats
sumStats []       = zeroStats
sumStats (s ∷ ss) = s +ˢ sumStats ss

------------------------------------------------------------------------
-- running one program, collecting its bursts.
--
-- probeDrain mirrors Rx.Evaluator.drain, which discards its final state — and
-- the log rides in that state.  oneProgram compares the stream this mirror
-- produces against the real `evaluate`, so a drift shows up as a selfcheck
-- failure rather than as quietly-wrong counters.

FUEL : Fuel
FUEL = 30

probeDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → Fuel → Id → Sched Γ → EvalSt e → Stream Γ t × EvalSt e
probeDrain zero    _      _     st = [] , st
probeDrain (suc k) nextId sched st with sched-next sched
... | inj₁ _            = [] , st
... | inj₂ (a , sched′) =
      let (out , sched″ , st′) = cascade a nextId sched′ st
          (rest , st″)         = probeDrain k (suc nextId) sched″ st′
      in out ++ᴸ rest , st″

-- Γ-generic: corpus C wants a THREE-slot telescope (two shares that both stay
-- live need a scripted slot below them, and Γ₂ has no room for that), while the
-- generated corpora stay at Γ₂.  Nothing here is Γ₂-specific — `Val Γ natᵗ` is ℕ
-- for every Γ, which is also why showStream applies.
runProbe : ∀ {n} {Γ : Ctx n} → (e : Exp Γ [] [] [] natᵗ) → Slots Γ
         → Stream Γ natᵗ × List (List (InstEmit ⊤))
runProbe e ins =
  let (burst , sched₀ , st₀) =
        subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
      (rest , st₁) = probeDrain FUEL 1 sched₀ st₀
  in burst ++ᴸ rest , EvalSt.burstLog st₁

-- stream equality, via the canonical rendering (events, values, instants,
-- sources and order all appear in it)
-- `Val Γ natᵗ` is ℕ for every Γ, so this is Stream Γ natᵗ stated in the one
-- form that does not leave Γ to be guessed at the call site
eqStream : List (InstEmit ℕ) → List (InstEmit ℕ) → Bool
eqStream a b = showStream a ==ˢ showStream b

------------------------------------------------------------------------
-- reporting

showBurst : List (InstEmit ⊤) → String
showBurst b = go b
  where
  showEv : InstEvent ⊤ → String
  showEv (init s)             = "i" ++ show s
  showEv (value _)            = "v"
  showEv (close s cut)        = "c" ++ show s ++ "!"
  showEv (close s cutPending) = "c" ++ show s ++ "?"
  showEv (close s _)          = "c" ++ show s
  showEv (handoff s)          = "h" ++ show s
  showEv complete             = "F"
  showEvs : List (InstEvent ⊤) → String
  showEvs []       = ""
  showEvs (x ∷ xs) = showEv x ++ " " ++ showEvs xs
  showKind : EmitKind → String
  showKind subscribe = "s"
  showKind delivery  = "d"
  showKind plumbing  = "p"
  showEm : InstEmit ⊤ → String
  showEm (es at i from s as k) =
    "@" ++ show i ++ "/" ++ showKind k ++ "{" ++ showEvs es ++ "}"
  go : List (InstEmit ⊤) → String
  go []       = "·"
  go (x ∷ xs) = showEm x ++ " " ++ go xs

-- witnesses are what turn a counter into a finding, so each is printed with the
-- exact burst and enough of the program to rebuild it
Witness : Set
Witness = String

witnessOf : String → String → List (InstEmit ⊤) → Witness
witnessOf tag prog b =
  "    " ++ tag ++ "  " ++ showBurst b ++ "\n      prog = " ++ prog ++ "\n"

------------------------------------------------------------------------
-- one program: counters + witnesses

oneProgram : ∀ {n} {Γ : Ctx n}
           → String → Exp Γ [] [] [] natᵗ → Slots Γ → Stats × List Witness
oneProgram prog e ins =
  let (stream , logs) = runProbe e ins
      real            = evaluate FUEL e ins
      selfOK          = eqStream stream real
      wfOK            = wellFormed? real
      per             = map burstStats logs
      wits            = concat (map witness logs)
  in (mkStats 1 (b→ℕ (not selfOK)) (b→ℕ (not wfOK)) 0 0 0 0 0 0 0 0 0 0 0 0 0
        +ˢ sumStats per)
     , (if selfOK then [] else ("    SELFCHECK-FAIL  prog = " ++ prog ++ "\n") ∷ [])
       -- a protocol rejection is reported with the whole stream, not just a
       -- count: it is the one outcome that would make this an evaluator finding
       -- rather than a measurement, so it must be diagnosable from the report
       ++ᴸ (if wfOK then []
            else ("    WF-FAIL      " ++ showStream real
                    ++ "\n      prog = " ++ prog ++ "\n") ∷ [])
       ++ᴸ wits
  where
  witness : List (InstEmit ⊤) → List Witness
  witness b with walkOf b
  ... | w = (if not (valsLast? b)    then witnessOf "VALS-EARLY " prog b ∷ [] else [])
            ++ᴸ (if not (Walk.ok w)    then witnessOf "FRESH-FAIL " prog b ∷ [] else [])
            ++ᴸ (if Walk.matchedTail w then witnessOf "ACC-IN-TAIL" prog b ∷ [] else [])
            ++ᴸ (if Walk.matched w     then witnessOf "ACC-CLOSE  " prog b ∷ [] else [])

------------------------------------------------------------------------
-- corpus A: the plain QuickCheck generator (scripted slots only — it mints no
-- shares, so its reach is expected to be structurally zero; it is here to
-- assert counter 1 at scale)

caseA : ℕ → Gen (Stats × List Witness)
caseA d = genSlots >>=G λ ins → genExp d >>=G λ e →
  pureG (oneProgram (showExp e ++ "  " ++ showSlots ins) e ins)

-- corpus B: the same generator with SHARED slots enabled, respecting the CONST
-- TELESCOPE — a def may reference only STRICTLY EARLIER slots.  So slot 0's def
-- is generated source-free and slot 1's may reach for `input zero` only.  That
-- restriction is not cosmetic: an unrestricted version of this generator, whose
-- defs could reference their own or a later slot, produced streams the protocol
-- rejects (6 wellFormed failures in 360 programs, seeds 1..6 depth 3).  Those
-- programs are outside the evaluator's contract — the telescope is the
-- generator's/decoder's obligation, not something the types enforce — so they
-- say nothing about the evaluator, and admitting them here would have polluted
-- every counter below with out-of-contract runs.
noSource : QuickCheck.SrcLeaf                 -- slot 0's def: no earlier slot exists
noSource = pureG emptyᵉ

slot0Only : QuickCheck.SrcLeaf                -- slot 1's def: slot 0 and no further
slot0Only = pureG (input zero)

genSharedSlots : ℕ → Gen (Slots Γ₂)
genSharedSlots d =
  genB 2 >>=G λ c0 → genB 2 >>=G λ c1 →
  QuickCheck.genInput >>=G λ i0 → QuickCheck.genInput >>=G λ i1 →
  QuickCheck.genExpAt noSource d >>=G λ d0 →
  QuickCheck.genExpAt slot0Only d >>=G λ d1 →
  pureG λ where
    zero          → if c0 ≡ᵇ 0 then scripted i0 else shared d0
    (suc zero)    → if c1 ≡ᵇ 0 then scripted i1 else shared d1
    (suc (suc ()))

caseB : ℕ → Gen (Stats × List Witness)
caseB d = genSharedSlots d >>=G λ ins → genExp d >>=G λ e →
  pureG (oneProgram (showExp e ++ "  <shared-slots>") e ins)

runN : (ℕ → Gen (Stats × List Witness)) → ℕ → ℕ → Gen (Stats × List Witness)
runN f zero    d = pureG (zeroStats , [])
runN f (suc k) d = f d >>=G λ r → runN f k d >>=G λ acc →
  pureG ((proj₁ r +ˢ proj₁ acc) , proj₂ r ++ᴸ proj₂ acc)

-- one corpus over a whole seed range, aggregated
sweep : (ℕ → Gen (Stats × List Witness)) → ℕ → ℕ → ℕ → ℕ → Stats × List Witness
sweep f first count runs d = go count first
  where
  go : ℕ → ℕ → Stats × List Witness
  go zero    _ = zeroStats , []
  go (suc k) s =
    let r  = proj₁ (runN f runs d (randList s 2000000))
        rs = go k (suc s)
    in (proj₁ r +ˢ proj₁ rs) , proj₂ r ++ᴸ proj₂ rs

------------------------------------------------------------------------
-- corpus C: DIRECTED programs.
--
-- Only one construction gives a burst more than one emit: sharedConnect returns
-- `own-init-emit ∷ sharedPlumb (def burst)`, and every other clause either mints
-- one emit or maps pushBurst over its child's (emit count preserved).  An inner
-- subscription's burst is flattened into a single emit by splitBurst, so the
-- configuration needs a share connecting on a SUBSCRIPTION SPINE with a frame
-- above it — `map/take/scan` over a shared `input i`, either at the root or
-- inside an inner expression.  These are built to hit exactly that, and to keep
-- the share's registration ALIVE past the connect (a def that completes
-- synchronously latches and drops it, taking the configuration away).

hotIn coldSync coldBoth : ObservableInput ℕ
hotIn    = hot ((after 0 , 7) ∷ (after 0 , 8) ∷ [])
coldSync = cold (1 ∷ 2 ∷ 3 ∷ []) []
coldBoth = cold (1 ∷ 2 ∷ 3 ∷ []) ((after 0 , 9) ∷ [])

slots2 : Slot Γ₂ natᵗ → Slot Γ₂ natᵗ → Slots Γ₂
slots2 s0 s1 = λ where
  zero          → s0
  (suc zero)    → s1
  (suc (suc ()))

in0 in1 : Exp Γ₂ [] [] [] natᵗ
in0 = input zero
in1 = input (suc zero)

addFn : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] natᵗ natᵗ
addFn = primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 1))

scanFn : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ
scanFn = primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))

directed : List (String × Slots Γ₂ × Exp Γ₂ [] [] [] natᵗ)
directed =
  -- the canonical shape: the share's own `init` rides emit 0, the def's cold
  -- sync values ride emit 1, and take's budget runs out THERE — so cutThrough
  -- closes the share registration one emit after it opened
    ( "take 2 (share := cold[1,2,3]+async)"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 2) in1 )
  ∷ ( "take 1 (share := cold[1,2,3]+async)"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 1) in1 )
  -- budget exactly spent: take completes on its last admitted value, so this
  -- still cuts (as rxjs's take(3) does on the third emission)
  ∷ ( "take 3 (share := cold[1,2,3]+async)"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 3) in1 )
  -- budget NOT spent: no cut, so no severing close for the share at all
  ∷ ( "take 5 (share := cold[1,2,3]+async)"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 5) in1 )
  -- a def that completes inside its own connect burst: the share latches and
  -- its registration is dropped before the cut can see it
  ∷ ( "take 2 (share := of[1,2])"
    , slots2 (scripted hotIn) (shared (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])))
    , takeᵉ (nat̂ 2) in1 )
  ∷ ( "take 2 (share := cold[1,2,3] sync-only)"
    , slots2 (scripted coldSync) (shared in0) , takeᵉ (nat̂ 2) in1 )
  -- nested takes over the same share: two cutting frames on one spine
  ∷ ( "take 1 (take 2 (share := cold+async))"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 1) (takeᵉ (nat̂ 2) in1) )
  ∷ ( "take 2 (take 1 (share := cold+async))"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 2) (takeᵉ (nat̂ 1) in1) )
  -- a frame between the share and the take
  ∷ ( "take 2 (map (+1) (share := cold+async))"
    , slots2 (scripted coldBoth) (shared in0) , takeᵉ (nat̂ 2) (mapᵉ addFn in1) )
  ∷ ( "take 2 (scan (+) 0 (share := cold+async))"
    , slots2 (scripted coldBoth) (shared in0)
    , takeᵉ (nat̂ 2) (scanᵉ scanFn (nat̂ 0) in1) )
  -- the share's def is itself a merge of two colds: more registrations minted
  -- during the connect, all of them under the take
  ∷ ( "take 2 (share := mergeAll(of[cold,cold]))"
    , slots2 (scripted coldBoth)
             (shared (mergeAllᵉ (ofᵉ (strmᵗ in0 ∷ strmᵗ in0 ∷ []))))
    , takeᵉ (nat̂ 2) in1 )
  ∷ ( "take 2 (share := concatAll(of[cold,cold]))"
    , slots2 (scripted coldBoth)
             (shared (concatAllᵉ (ofᵉ (strmᵗ in0 ∷ strmᵗ in0 ∷ []))))
    , takeᵉ (nat̂ 2) in1 )
  -- a share telescope: slot 1's def is slot 0's share, so the burst is three
  -- emits deep and the outer share's init is two emits away from the cut
  ∷ ( "take 2 (share1 := share0 := of[1,2,3])"
    , slots2 (shared (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))) (shared in0)
    , takeᵉ (nat̂ 2) in1 )
  -- the same shapes in INNER position: the inner's own spine carries the take,
  -- so its burst is the multi-emit one
  ∷ ( "mergeAll(of[take 2 share, take 2 share])"
    , slots2 (scripted coldBoth) (shared in0)
    , mergeAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 2) in1) ∷ strmᵗ (takeᵉ (nat̂ 2) in1) ∷ [])) )
  ∷ ( "switchAll(of[take 2 share, take 1 share])"
    , slots2 (scripted coldBoth) (shared in0)
    , switchAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 2) in1) ∷ strmᵗ (takeᵉ (nat̂ 1) in1) ∷ [])) )
  ∷ ( "exhaustAll(of[take 2 share, take 2 share])"
    , slots2 (scripted coldBoth) (shared in0)
    , exhaustAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 2) in1) ∷ strmᵗ (takeᵉ (nat̂ 2) in1) ∷ [])) )
  -- take over a plain cold-async source: one emit, the control for "no share"
  ∷ ( "take 1 (cold[1,2,3]+async)"
    , slots2 (scripted coldBoth) (scripted hotIn) , takeᵉ (nat̂ 1) in0 )
  -- two shares in one frame, at Γ₂: slot 0's def cannot mention a source (it is
  -- the first slot), so both of these latch inside their connect burst.  The
  -- LIVE version of this shape needs a third slot — see directed₃
  ∷ ( "mergeAll(of[share0 := of[1,2,3], share1 := share0])"
    , slots2 (shared (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))) (shared in0)
    , mergeAllᵉ (ofᵉ (strmᵗ in0 ∷ strmᵗ in1 ∷ [])) )
  ∷ ( "take 2 (mergeAll(of[share0 := of[1,2,3], share1 := share0]))"
    , slots2 (shared (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))) (shared in0)
    , takeᵉ (nat̂ 2) (mergeAllᵉ (ofᵉ (strmᵗ in0 ∷ strmᵗ in1 ∷ []))) )
  ∷ []

------------------------------------------------------------------------
-- corpus C, second half: THREE slots.
--
-- Counter 0 asks whether two payloads can ride one subscribe frame, and the
-- shape that would do it is several connects on one frame with a live def
-- underneath each.  Γ₂ cannot express that: the const telescope makes slot 0's
-- def source-free, so a Γ₂ share over a real source is unique and a second Γ₂
-- share can only be literal-driven (hence sync-latching).  With three slots the
-- bottom slot is a scripted cold and BOTH shares above it stay live past their
-- connect — so `mergeAll(of[share1, share2])` really does connect two live
-- shares inside one frame, and `take k` over it really does cut across them.

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

slots3 : Slot Γ₃ natᵗ → Slot Γ₃ natᵗ → Slot Γ₃ natᵗ → Slots Γ₃
slots3 s0 s1 s2 = λ where
  zero                → s0
  (suc zero)          → s1
  (suc (suc zero))    → s2
  (suc (suc (suc ())))

j0 j1 j2 : Exp Γ₃ [] [] [] natᵗ
j0 = input zero
j1 = input (suc zero)
j2 = input (suc (suc zero))

-- slot 0 scripted; slots 1 and 2 are independent shares of it, both live
twoShares : Slots Γ₃
twoShares = slots3 (scripted coldBoth) (shared j0) (shared j0)

-- a share TELESCOPE over a live source: slot 2's def is slot 1's share, so a
-- single subscription to j2 mints a three-emit connect burst
shareChain : Slots Γ₃
shareChain = slots3 (scripted coldBoth) (shared j0) (shared j1)

directed₃ : List (String × Slots Γ₃ × Exp Γ₃ [] [] [] natᵗ)
directed₃ =
  -- two live connects on one frame, under each *All in turn
    ( "mergeAll(of[share1, share2])   (both live over cold+async)"
    , twoShares , mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  ∷ ( "concatAll(of[share1, share2])"
    , twoShares , concatAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  ∷ ( "switchAll(of[share1, share2])"
    , twoShares , switchAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  ∷ ( "exhaustAll(of[share1, share2])"
    , twoShares , exhaustAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  -- …with a cut above, at every budget around the payload size
  ∷ ( "take 1 (mergeAll(of[share1, share2]))"
    , twoShares , takeᵉ (nat̂ 1) (mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  ∷ ( "take 2 (mergeAll(of[share1, share2]))"
    , twoShares , takeᵉ (nat̂ 2) (mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  ∷ ( "take 4 (mergeAll(of[share1, share2]))"
    , twoShares , takeᵉ (nat̂ 4) (mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  ∷ ( "take 2 (concatAll(of[share1, share2]))"
    , twoShares , takeᵉ (nat̂ 2) (concatAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  ∷ ( "take 2 (switchAll(of[share1, share2]))"
    , twoShares , takeᵉ (nat̂ 2) (switchAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  -- the raw source alongside its own two shares: three connects, one frame
  ∷ ( "mergeAll(of[cold, share1, share2])"
    , twoShares , mergeAllᵉ (ofᵉ (strmᵗ j0 ∷ strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  ∷ ( "take 2 (mergeAll(of[cold, share1, share2]))"
    , twoShares
    , takeᵉ (nat̂ 2) (mergeAllᵉ (ofᵉ (strmᵗ j0 ∷ strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  -- inner takes, so the cut is inside a flattened inner burst rather than above
  ∷ ( "mergeAll(of[take 1 share1, take 2 share2])"
    , twoShares
    , mergeAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 1) j1) ∷ strmᵗ (takeᵉ (nat̂ 2) j2) ∷ [])) )
  ∷ ( "take 2 (mergeAll(of[take 1 share1, take 2 share2]))"
    , twoShares
    , takeᵉ (nat̂ 2)
        (mergeAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 1) j1) ∷ strmᵗ (takeᵉ (nat̂ 2) j2) ∷ []))) )
  -- the share telescope: one subscription, a three-emit connect burst
  ∷ ( "share2 := share1 := cold+async"          , shareChain , j2 )
  ∷ ( "take 1 (share2 := share1 := cold+async)" , shareChain , takeᵉ (nat̂ 1) j2 )
  ∷ ( "take 2 (share2 := share1 := cold+async)" , shareChain , takeᵉ (nat̂ 2) j2 )
  ∷ ( "take 3 (share2 := share1 := cold+async)" , shareChain , takeᵉ (nat̂ 3) j2 )
  ∷ ( "take 2 (map (+1) (share2 := share1 := cold+async))"
    , shareChain , takeᵉ (nat̂ 2) (mapᵉ addFn j2) )
  ∷ ( "take 2 (scan (+) 0 (share2 := share1 := cold+async))"
    , shareChain , takeᵉ (nat̂ 2) (scanᵉ scanFn (nat̂ 0) j2) )
  -- both ends of the chain subscribed in one frame: share1's connect burst is
  -- nested inside share2's, and share1 is ALSO joined directly beside it
  ∷ ( "mergeAll(of[share2, share1])   (chained)"
    , shareChain , mergeAllᵉ (ofᵉ (strmᵗ j2 ∷ strmᵗ j1 ∷ [])) )
  ∷ ( "mergeAll(of[share1, share2])   (chained)"
    , shareChain , mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  ∷ ( "take 2 (mergeAll(of[share2, share1]))   (chained)"
    , shareChain , takeᵉ (nat̂ 2) (mergeAllᵉ (ofᵉ (strmᵗ j2 ∷ strmᵗ j1 ∷ []))) )
  -- a share whose def is itself a merge of a share and the raw source: the
  -- connect burst carries two subscriptions' worth of payload
  ∷ ( "take 2 (share2 := mergeAll(of[share1, cold]))"
    , slots3 (scripted coldBoth) (shared j0)
             (shared (mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j0 ∷ []))))
    , takeᵉ (nat̂ 2) j2 )
  ∷ ( "share2 := mergeAll(of[share1, cold])"
    , slots3 (scripted coldBoth) (shared j0)
             (shared (mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j0 ∷ []))))
    , j2 )
  -- sync-only source under two shares: both latch inside their own connect
  ∷ ( "mergeAll(of[share1, share2])   (over cold sync-only)"
    , slots3 (scripted coldSync) (shared j0) (shared j0)
    , mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ [])) )
  ∷ ( "take 2 (mergeAll(of[share1, share2]))   (over cold sync-only)"
    , slots3 (scripted coldSync) (shared j0) (shared j0)
    , takeᵉ (nat̂ 2) (mergeAllᵉ (ofᵉ (strmᵗ j1 ∷ strmᵗ j2 ∷ []))) )
  ∷ []

runDirected : ∀ {n} {Γ : Ctx n}
            → List (String × Slots Γ × Exp Γ [] [] [] natᵗ) → Stats × List Witness
runDirected []                    = zeroStats , []
runDirected ((nm , ins , e) ∷ ps) =
  let r  = oneProgram nm e ins
      rs = runDirected ps
  in (proj₁ r +ˢ proj₁ rs) , proj₂ r ++ᴸ proj₂ rs

------------------------------------------------------------------------
-- output

pad : Stats → String → String
pad s label =
  label ++ "\n"
  ++ "    programs            " ++ show (Stats.programs s) ++ "\n"
  ++ "    selfcheck failures  " ++ show (Stats.selfFail s) ++ "\n"
  ++ "    wellFormed failures " ++ show (Stats.wfFail s) ++ "\n"
  ++ "    bursts              " ++ show (Stats.bursts s) ++ "\n"
  ++ "    multi-emit bursts   " ++ show (Stats.multiEmit s) ++ "\n"
  ++ "  0 valsLast failures   " ++ show (Stats.valsFail s) ++ "\n"
  ++ "    bursts with values  " ++ show (Stats.valBursts s) ++ "\n"
  ++ "    …with 2+ val emits  " ++ show (Stats.multiVal s) ++ "\n"
  ++ "  1 frameFresh failures " ++ show (Stats.freshFail s) ++ "\n"
  ++ "    walk/frameFresh ≠  " ++ show (Stats.walkMismatch s) ++ "\n"
  ++ "  2 reach (cross-emit)  " ++ show (Stats.reach s) ++ "\n"
  ++ "  3 acc-matched close   " ++ show (Stats.accClose s) ++ "\n"
  ++ "      …reason cut/cutP  " ++ show (Stats.accCloseCut s) ++ "\n"
  ++ "    bursts with a cut   " ++ show (Stats.cutBursts s) ++ "\n"
  ++ "    cut with a tail     " ++ show (Stats.cutNotLast s) ++ "\n"
  ++ "  3ᵗ acc-close IN TAIL  " ++ show (Stats.accCloseTail s) ++ "\n"

firstN : ℕ → List String → List String
firstN zero    _        = []
firstN (suc k) []       = []
firstN (suc k) (x ∷ xs) = x ∷ firstN k xs

witnessBlock : String → List Witness → String
witnessBlock label []             = "  " ++ label ++ ": none\n"
witnessBlock label ws@(_ ∷ _) =
  "  " ++ label ++ " (" ++ show (length ws) ++ " total, first 12):\n"
  ++ concatStr (firstN 12 ws)

-- stdin: "FIRST [LAST] [RUNS] [DEPTH]" — seeds FIRST..LAST, RUNS programs each
main : IO Unit
main = getContents >>= λ s →
  let cs    = toCodes s
      first = parseNat cs
      last  = numAt 1 first cs
      runs  = numAt 2 200 cs
      d     = numAt 3 4 cs
      count = suc (last ∸ first)
      rA    = sweep caseA first count runs d
      rB    = sweep caseB (first + 100000) count runs d
      rC    = runDirected directed
      rC₃   = runDirected directed₃
  in putStr (concatStr
       ( "BURST PROBE — seeds " ∷ show first ∷ ".." ∷ show last ∷ ", " ∷ show runs
       ∷ " programs/seed, depth " ∷ show d ∷ "\n\n"
       ∷ pad (proj₁ rA) "A. QuickCheck generator (scripted slots only)"
       ∷ witnessBlock "A witnesses" (proj₂ rA)
       ∷ "\n"
       ∷ pad (proj₁ rB) "B. generator with SHARED slots enabled"
       ∷ witnessBlock "B witnesses" (proj₂ rB)
       ∷ "\n"
       ∷ pad (proj₁ rC) "C. directed programs (2 slots)"
       ∷ witnessBlock "C witnesses" (proj₂ rC)
       ∷ "\n"
       ∷ pad (proj₁ rC₃) "C₃. directed programs (3 slots: two live shares)"
       ∷ witnessBlock "C₃ witnesses" (proj₂ rC₃)
       ∷ []))
