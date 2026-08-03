-- STRATUM 2a-iii of Verify-Budget-Sufficient: THE COUNT FACE.
--
-- (b) of the two things Sub-Charge-Probe § 5's composition gate is
-- counted in: how many EMITS a subscribe burst has, and how many VALUES
-- sit inside each one.  `op-step`'s pushBurst premise iterates fIterD
-- over `suc (widAt S W A)` frames and pushBurst-caps spends one per emit;
-- `frame-step`'s walk premise iterates sIterD over `suc (widAt S W j)`
-- payloads and pushBurst-caps hands stepFrame-caps one per `value` event
-- inside the emit.  Both are cardinalities of the ONE object subscribeE
-- hands back, so both are `burstCount?` (.Caps-Face).
--
-- WHY IT IS ITS OWN MODULE.  The count siblings will recurse on each
-- other over the same thirteen clause shapes the subscribe clique has,
-- but they consume the -caps results as FINISHED FACTS — the caps
-- invariant at the level a sub-subscribe left, the slot telescope, the
-- path bounds — and nothing in .Subscribe-Face reads a count.  So the
-- two families are separate SCCs, and a clause edit in the count grind
-- re-checks this module rather than the clique's seven minutes.
--
-- AND WHY THE EXIT LEVEL.  The statement was first written at the ENTRY
-- level `frameStep j c`, on the reasoning that widAt is monotone in j so
-- an entry bound implies the exit bound the charge side consumes and
-- costs no existential at all.  THAT IS FALSE (Share-Count-Probe, both
-- rows machine-checked): `sharedConnect` prepends its own `init`
-- envelope onto the def's whole burst, so a ladder of k nested shares
-- hands back k+1 emits, and nothing in the entry hypotheses bounds k —
-- `slotsCaps?` reads each shared def POINTWISE and a ladder of `input`
-- keeps every pointwise measure at 1 however long it gets.  The face
-- therefore reports its own `j′`, exactly as `subscribeE-caps` does.
--
-- THE TWO EXISTENTIALS DO NOT HAVE TO AGREE, which is what keeps the
-- families separable: `burstCount?` widens along ⊑ᶜ (below, ground), and
-- so do `capsOK?` and `burstCaps?`, so a consumer that needs all three at
-- one level takes the larger of the two receipts and widens.  Should the
-- receipt pass turn out to need them level-locked, the count becomes a
-- third conjunct of subscribeE-caps's Σ and this module folds back into
-- .Subscribe-Face; that is a ruling for (a), not for (b).
module Verify-Budget-Sufficient.Subscribe-Count where

open import Data.Bool    using (Bool; true; _∧_)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _≤ᵇ_; s≤s)
open import Data.List    using (List; all; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Gas; Id; Tick; InstEmit)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Evaluator using (Slots; Sched; EvalSt; Path; Stream; subscribeE)

open import Verify-Budget-Sufficient.Subscribe-Face public

------------------------------------------------------------------
-- burstCount? WIDENS.  Both conjuncts are `_ ≤ᵇ suc (cWid c)` and ⊑ᶜ
-- gives `cWid c ≤ cWid c′`, so the whole predicate rides the order —
-- the lemma that lets the count receipt and the caps receipt be
-- reconciled at whichever of the two levels is larger
------------------------------------------------------------------

burstCount?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (str : Stream Γ u) →
  c ⊑ᶜ c′ → burstCount? c str ≡ true → burstCount? c′ str ≡ true
burstCount?-widen {c = c} str (_ , wd≤ , _) h
  with ∧-true (length str ≤ᵇ suc (Caps.cWid c))
              (all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ suc (Caps.cWid c)) str)
              h
... | hlen , hval =
  ∧-intro (≤ᵇ-widen (length str) (s≤s wd≤) hlen)
          (all-impl _ _
             (λ em → ≤ᵇ-widen (valCountᵉ (InstEmit.events em)) (s≤s wd≤)) str hval)

------------------------------------------------------------------
-- THE FACE.  Same hypotheses as subscribeE-caps, its own receipt.
--
-- WHAT ITS DISCHARGE WILL LOOK LIKE, read off the ground bodies:
--
--   · THE EMIT COUNT IS PRESERVED EXCEPT AT A CONNECT.  `pushBurst … (em
--     ∷ ems)` conses exactly one envelope per input emit, so every
--     operator clause inherits its source's count unchanged, and the
--     leaves mint exactly one.  `sharedConnect` is the sole grower, by
--     exactly one, and it pays `suc j₂` for it — one fold per connect —
--     which is why the receipt covers it: `foldStep S w = S ^ suc w`
--     clears a successor after two rungs.
--   · THE PAYLOAD COUNT IS stepFrame's OUTPUT LENGTH.  A pushed emit's
--     values are `map value vals′` for `vals′` the frame's output, so
--     the per-emit half descends to one question per Frame constructor:
--     `map-f` is `map (applyFn fn) vals` (length preserved), `scan-f` is
--     `scanVals` (one out per in, or `[]` at a node-type mismatch),
--     `take-f` is takeDispatch (a prefix), and the two *All frames are
--     the ones that are NOT structural, because both output a
--     CONCATENATION — innerFinish's concat clause is `vals ++
--     concatDrain …` and thruWalk's step is `proj₁ TC ++ proj₁ REST`.
--     Each is a sum over a list of one subscribe's value count, i.e. of
--     this very statement, so the two *All clauses are where the width
--     arithmetic is paid.
--
-- AND WHAT CONSUMES IT BESIDES (a).  Raising stepFrame-caps's payload
-- premise from `all (valCaps? …)` to `valsCaps?` — the length conjunct
-- `FrameFace` carries and the companion does not — needs
-- `splitEvents-valsCaps`, whose second hypothesis is `valCountᵉ es ≤ suc
-- (Caps.cWid c)`.  pushBurst-caps, its only caller, has `burstCaps?` and
-- nothing else, and `burstCaps?` carries no cardinality.  So the premise
-- strengthening waits on this face too
------------------------------------------------------------------

postulate
  subscribeE-count : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    Σ ℕ λ j′ →
      burstCount? (frameStep (j + j′) c)
        (proj₁ (subscribeE g b κ bid now sched st)) ≡ true
