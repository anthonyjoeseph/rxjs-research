------------------------------------------------------------------
-- THE COUNT-LEVEL PROBE: WHAT, IF ANYTHING, DOES THE COUNT FACE SAY?
--
-- Share-Count-Probe refuted the ENTRY-level reading of a subscribe
-- burst's emit count and concluded, in its own words, that "the count
-- face therefore has to SHARE subscribeE-caps's existential — a third
-- conjunct of its Σ, not a sibling lemma."  What landed instead was a
-- SIBLING lemma in its own module, with its OWN existential:
--
--   Σ ℕ λ j′ → burstCount? (frameStep (j + j′) c) (proj₁ (subscribeE …)) ≡ true
--
-- and `j′` occurs NOWHERE ELSE in that statement.  This probe asks what
-- that says about `subscribeE`.  THREE ANSWERS, all machine-checked:
--
--   § 1-4  NOTHING.  `cWid (frameStep k c) = iterFold (cSize c) k (cWid c)`
--     and `foldStep S w = S ^ suc w` clears a successor outright for
--     S ≥ 2 (`suc w ≤ 2 ^ w ≤ S ^ suc w`, which is `n<2^n` with the
--     `<⇒≤` that `foldStep-infl` throws away), so `cWid (frameStep k c)
--     ≥ k` for every k.  A burst is a FINITE list of finite event lists,
--     so its emit count and its per-emit value counts are computable
--     numbers, and taking j′ to be their maximum satisfies the predicate
--     for ANY stream whatever.  `count-vacuous` is that proof: parametric
--     in the stream, never mentions `subscribeE`, and discharges the
--     landed postulate using NONE of its ten hypotheses but `2 ≤ cSize c`.
--
--   § 5  AND THE FOLD-BACK DOES NOT FIX IT.  Making the count a THIRD
--     CONJUNCT of subscribeE-caps's Σ — the repair Share-Count-Probe
--     called for — is ALSO free: all three conjuncts are upward closed
--     in the level (`capsOK?-mono`, `burstCaps?-widen`, `burstCount?-widen`
--     along `frameStep-mono-j`), so given ANY caps receipt one simply
--     enlarges its witness past the stream's own ceiling and all three
--     hold at once.  `shared-free` derives the three-conjunct Σ from the
--     two-conjunct one, mechanically.  A Σ whose every conjunct widens
--     says nothing about the WITNESS, and the witness is the whole
--     content: what the charge side consumes (Sub-Charge-Probe § 5's
--     `op-step`) is `fIterD … (suc (widAt S W A)) A` at exactly the A the
--     SOURCE's caps receipt reports — one frame per emit, at that level
--     and no other.  The count is LEVEL-LOCKED to the caps witness.
--
--   § 6  AND LEVEL-LOCKED, IT IS FALSE — at the INPUT LEAF, which pays
--     no fold at all.  `subscribeE-input-caps` reports j′ = 0 on the
--     `scripted (cold sync [])` branch (.Subscribe-Face, and checked here
--     off the proof term), while that branch's burst is `oneShotBurst
--     sync`: ONE emit carrying `length sync` values.  Nothing in the
--     hypotheses bounds `length sync` by a WIDTH: `slotCaps?` on a
--     scripted slot is `all (λ v → sizeᵛ v ≤ᵇ B)` — pointwise, no
--     cardinality — and `sizeᵛ natᵗ v` is 1, so a cold list of ANY length
--     passes `slotsCaps? 2 1`.  Nor does the entry width repair it:
--     `slotCeil j sl (scripted _) = 0`, so a cold slot contributes ZERO
--     to `entryCeil`, i.e. to the base `cWid`, while `slotsSize` — a
--     SIZE — does read the list.  Two rows below, three values and eight,
--     with every face hypothesis `refl` at the same `caps 2 1 1`: the
--     caps witness is 0 for both and the count needs 1 and 2.
------------------------------------------------------------------
module Count-Level-Probe where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-assoc;
                                       *-mono-≤; *-monoʳ-≤; *-identityʳ;
                                       ^-monoʳ-≤;
                                       ^-monoˡ-≤; n≤1+n; +-monoʳ-≤;
                                       m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m; ≤⇒≤ᵇ)
open import Data.List    using (List; []; _∷_; all; length)
open import Data.Fin     using (Fin; zero; suc)
open import Data.Vec     using (Vec) renaming (_∷_ to _∷ᵛ_; [] to []ᵛ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Rx.Prim      using (Gas; g0; gs; Id; Tick; InstEmit;
                                ObservableInput; cold)
open import Rx.Exp       using (Ctx; Closed; Val; natᵗ; input; sizeᵉ)
open import Rx.Frame-Width using (dWᵉ; entryCeil)
open import Rx.Evaluator using (Slots; scripted; Sched; EvalSt; Path; root; Stream;
                                subscribeE; sched-init; st-init; slotsSize;
                                foldStep; iterFold)

open import Verify-Budget-Sufficient.Subscribe-Face

------------------------------------------------------------------
-- § 1.  ONE FOLD CLEARS A SUCCESSOR.  foldStep-infl proves `w ≤
-- foldStep S w` by `<⇒≤ (n<2^n w)`; drop that coercion and the same
-- chain proves the strict form
------------------------------------------------------------------

foldStep-suc : ∀ (S w : ℕ) → 2 ≤ S → suc w ≤ foldStep S w
foldStep-suc S w hS =
  ≤-trans (n<2^n w)
          (≤-trans (^-monoʳ-≤ 2 (n≤1+n w))
                   (^-monoˡ-≤ (suc w) hS))

-- so k folds clear k
iterFold-lb : ∀ (S : ℕ) → 2 ≤ S → ∀ (k w : ℕ) → k + w ≤ iterFold S k w
iterFold-lb S hS zero    w = ≤-refl
iterFold-lb S hS (suc k) w =
  ≤-trans (≤-reflexive (sym (+-suc k w)))
          (≤-trans (+-monoʳ-≤ k (foldStep-suc S w hS))
                   (iterFold-lb S hS k (foldStep S w)))

-- the width at level k dominates k outright
k≤widAt : ∀ (c : Caps) (k : ℕ) → 2 ≤ Caps.cSize c →
  k ≤ Caps.cWid (frameStep k c)
k≤widAt c k hS =
  ≤-trans (m≤m+n k (Caps.cWid c)) (iterFold-lb (Caps.cSize c) hS k (Caps.cWid c))

------------------------------------------------------------------
-- § 2.  A STREAM'S OWN CEILING, computed from the stream
------------------------------------------------------------------

streamCeil : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → ℕ
streamCeil []         = 0
streamCeil (em ∷ ems) = valCountᵉ (InstEmit.events em) ⊔ streamCeil ems

-- every emit's value count is under it
ceil-vals : ∀ {n} {Γ : Ctx n} {u} (str : Stream Γ u) (M : ℕ) →
  streamCeil str ≤ M →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ suc M) str ≡ true
ceil-vals []         M h = refl
ceil-vals (em ∷ ems) M h =
  ∧-intro (T⇒≡true (valCountᵉ (InstEmit.events em) ≤ᵇ suc M)
             (≤⇒≤ᵇ (≤-trans (≤-trans (m≤m⊔n (valCountᵉ (InstEmit.events em))
                                            (streamCeil ems)) h)
                            (n≤1+n M))))
          (ceil-vals ems M (≤-trans (m≤n⊔m (valCountᵉ (InstEmit.events em))
                                           (streamCeil ems)) h))

-- BOTH conjuncts, at any level past the stream's ceiling
count-holds : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (k : ℕ) (str : Stream Γ u) →
  2 ≤ Caps.cSize c →
  length str ⊔ streamCeil str ≤ k →
  burstCount? (frameStep k c) str ≡ true
count-holds c k str 2≤S hk =
  ∧-intro (T⇒≡true (length str ≤ᵇ suc (Caps.cWid (frameStep k c)))
             (≤⇒≤ᵇ (≤-trans (≤-trans (≤-trans (m≤m⊔n (length str) (streamCeil str)) hk)
                                     (k≤widAt c k 2≤S))
                            (n≤1+n (Caps.cWid (frameStep k c))))))
          (ceil-vals str (Caps.cWid (frameStep k c))
             (≤-trans (≤-trans (m≤n⊔m (length str) (streamCeil str)) hk)
                      (k≤widAt c k 2≤S)))

------------------------------------------------------------------
-- § 3.  THE VACUITY.  Parametric in the stream; `subscribeE` never
-- appears
------------------------------------------------------------------

count-vacuous : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (str : Stream Γ u) →
  2 ≤ Caps.cSize c →
  Σ ℕ λ j′ → burstCount? (frameStep (j + j′) c) str ≡ true
count-vacuous c j str 2≤S =
  M , count-holds c (j + M) str 2≤S (m≤n+m M j)
  where
  M = length str ⊔ streamCeil str

------------------------------------------------------------------
-- § 4.  AND THE LANDED POSTULATE FALLS OUT, ten hypotheses unused
------------------------------------------------------------------

subscribeE-count-cheap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
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
subscribeE-count-cheap c j g b κ bid now sl sched st 2≤S _ _ _ _ _ _ _ _ =
  count-vacuous c j (proj₁ (subscribeE g b κ bid now sched st)) 2≤S

------------------------------------------------------------------
-- § 5.  NOR IS THE FOLD-BACK ANY BETTER.  The three-conjunct Σ — the
-- count sharing subscribeE-caps's existential — is DERIVABLE from the
-- two-conjunct one, because every conjunct rides ⊑ᶜ and `frameStep` is
-- monotone in the level.  Enlarge the caps witness past the stream's own
-- ceiling: the caps halves widen, the count half becomes true, and the
-- statement is proven without looking at a single clause of subscribeE
------------------------------------------------------------------

shared-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
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
  let r = subscribeE g b κ bid now sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
shared-free {n = n} c j g b κ bid now sl sched st 2≤S 1≤R slEq slC inv szB wdB pC lC
  with subscribeE-caps c j g b κ bid now sl sched st 2≤S 1≤R slEq slC inv szB wdB pC lC
... | j₁ , hOK , hBC =
  j₁ + M
  , subst (λ x → capsOK? (frameStep x c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
          (+-assoc j j₁ M)
          (capsOK?-mono (frameStep (j + j₁) c) (frameStep ((j + j₁) + M) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) step hOK)
  , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ r) ≡ true)
          (+-assoc j j₁ M)
          (burstCaps?-widen sl (proj₁ r) step hBC)
  , subst (λ x → burstCount? (frameStep x c) (proj₁ r) ≡ true)
          (+-assoc j j₁ M)
          (count-holds c ((j + j₁) + M) (proj₁ r) 2≤S (m≤n+m M (j + j₁)))
  where
  r    = subscribeE g b κ bid now sched st
  M    = length (proj₁ r) ⊔ streamCeil (proj₁ r)
  step : frameStep (j + j₁) c ⊑ᶜ frameStep ((j + j₁) + M) c
  step = frameStep-mono-j c 2≤S (m≤m+n (j + j₁) M)

------------------------------------------------------------------
-- § 6.  THE LEVEL-LOCKED READING, WHICH IS THE ONLY ONE WITH CONTENT,
-- IS FALSE AT THE INPUT LEAF.
--
-- ONE SLOT, a cold script with no async tail, and the program is the
-- `input` that reads it.  `subscribeE` takes the `scripted (cold sync [])`
-- branch: `oneShotBurst sync`, ONE emit whose events are `init ∷ map
-- value sync ++ close ∷ complete ∷ []` — so `valCountᵉ` is `length sync`
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

script₃ : ObservableInput (Val Γ₁ natᵗ)
script₃ = cold (1 ∷ 2 ∷ 3 ∷ []) []

script₈ : ObservableInput (Val Γ₁ natᵗ)
script₈ = cold (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []) []

sl₃ : Slots Γ₁
sl₃ zero    = scripted script₃
sl₃ (suc ())

sl₈ : Slots Γ₁
sl₈ zero    = scripted script₈
sl₈ (suc ())

prog : Closed Γ₁ natᵗ
prog = input zero

sched₃ : Sched Γ₁
sched₃ = sched-init prog sl₃

st₃ : EvalSt prog
st₃ = st-init prog

sched₈ : Sched Γ₁
sched₈ = sched-init prog sl₈

st₈ : EvalSt prog
st₈ = st-init prog

fuel : Gas
fuel = gs (gs g0)

burst₃ : Stream Γ₁ natᵗ
burst₃ = proj₁ (subscribeE fuel prog root 0 0 sched₃ st₃)

burst₈ : Stream Γ₁ natᵗ
burst₈ = proj₁ (subscribeE fuel prog root 0 0 sched₈ st₈)

-- ONE emit each, carrying three values and eight
_ : length burst₃ ≡ 1
_ = refl

_ : length burst₈ ≡ 1
_ = refl

_ : streamCeil {Γ = Γ₁} {u = natᵗ} burst₃ ≡ 3
_ = refl

_ : streamCeil {Γ = Γ₁} {u = natᵗ} burst₈ ≡ 8
_ = refl

------------------------------------------------------------------
-- THE SAME CAPS AS THE SHARE ROW, and every hypothesis of the face
-- still holds by computation — for BOTH scripts.  `slotCaps?` reads the
-- cold list POINTWISE and `sizeᵛ natᵗ` is 1, so its length is invisible
------------------------------------------------------------------

c₀ : Caps
c₀ = caps 2 1 1

_ : Caps.cWid (frameStep 0 c₀) ≡ 1
_ = refl

h2≤S : 2 ≤ Caps.cSize c₀
h2≤S = s≤s (s≤s z≤n)

h1≤R : 1 ≤ Caps.cReg c₀
h1≤R = s≤s z≤n

_ : slotsCaps? (Caps.cSize c₀) (Caps.cWid c₀) sl₃ ≡ true
_ = refl

_ : slotsCaps? (Caps.cSize c₀) (Caps.cWid c₀) sl₈ ≡ true
_ = refl

_ : capsOK? (frameStep 0 c₀) sched₃ st₃ ≡ true
_ = refl

_ : capsOK? (frameStep 0 c₀) sched₈ st₈ ≡ true
_ = refl

hSize : sizeᵉ prog ≤ Caps.cSize (frameStep 0 c₀)
hSize = s≤s z≤n

hWid₃ : dWᵉ 1 sl₃ prog ≤ Caps.cWid (frameStep 0 c₀)
hWid₃ = z≤n

hWid₈ : dWᵉ 1 sl₈ prog ≤ Caps.cWid (frameStep 0 c₀)
hWid₈ = z≤n

_ : pathSz? (Caps.cSize (frameStep 0 c₀)) (root {Γ = Γ₁} {t = natᵗ}) ≡ true
_ = refl

hLen : suc (pathLen (root {Γ = Γ₁} {t = natᵗ})) ≤ Caps.cSize (frameStep 0 c₀)
hLen = s≤s z≤n

------------------------------------------------------------------
-- AND THE CAPS FACE REPORTS ZERO — read off the ground proof term, not
-- off the source comment.  `subscribeE-input-caps`'s cold-no-tail clause
-- is `0 , subst … (sym (+-identityʳ j)) …`, and it reports the same 0
-- whether the script has three values or eight
------------------------------------------------------------------

capsWit₃ : ℕ
capsWit₃ = proj₁ (subscribeE-input-caps c₀ 0 fuel zero root 0 0 sl₃ sched₃ st₃
                    h2≤S h1≤R refl refl refl refl hLen)

capsWit₈ : ℕ
capsWit₈ = proj₁ (subscribeE-input-caps c₀ 0 fuel zero root 0 0 sl₈ sched₈ st₈
                    h2≤S h1≤R refl refl refl refl hLen)

_ : capsWit₃ ≡ 0
_ = refl

_ : capsWit₈ ≡ 0
_ = refl

------------------------------------------------------------------
-- AT THAT WITNESS THE COUNT IS FALSE.  `suc (cWid (frameStep 0 c₀))` is
-- 2, against three values and eight
------------------------------------------------------------------

_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 0 c₀) burst₃ ≡ false
_ = refl

_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 0 c₀) burst₈ ≡ false
_ = refl

-- and the level the count DOES need moves with the script's length while
-- the caps witness stays 0: one fold carries three values, not eight
_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 1 c₀) burst₃ ≡ true
_ = refl

_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 1 c₀) burst₈ ≡ false
_ = refl

_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 2 c₀) burst₈ ≡ true
_ = refl

------------------------------------------------------------------
-- AND THE ENTRY WIDTH CANNOT BE ASKED TO ABSORB IT EITHER.  `slotCeil j
-- sl (scripted _) = 0`, so both scripts give the SAME `entryCeil` — the
-- number the base caps' `cWid` is built from — while `slotsSize`, a
-- SIZE, tracks the list exactly.  The quantity the count needs is on the
-- size axis and the predicate that must bound it is on the width axis
------------------------------------------------------------------

_ : entryCeil 1 sl₃ prog ≡ entryCeil 1 sl₈ prog
_ = refl

_ : entryCeil 1 sl₃ prog ≡ 1
_ = refl

_ : slotsSize sl₃ ≡ 4
_ = refl

_ : slotsSize sl₈ ≡ 9
_ = refl

------------------------------------------------------------------
-- § 7.  AND THE REPAIR THAT SURVIVES THE ROW.  The breach is an
-- artefact of the face's hypotheses being WEAKER than every call site:
-- `c` is arbitrary subject to `slotsCaps? (cSize c) (cWid c) sl`, but a
-- real invocation always has `c = capsAt e sl id`, whose cSize is built
-- from `2 + sizeᵉ e + slotsSize sl` and so already DOMINATES the slot
-- telescope.  Add that as a hypothesis — `slotsSize sl ≤ cSize c`, true
-- at capsAt by construction — and ONE fold converts it into the width
-- the count needs, because `cWid (frameStep 1 c) = S ^ suc W ≥ S`.
--
-- So the leaf can report j′ = 1 instead of 0 and be right, at every c
-- the tree actually passes it.  The row below is the eight-value script
-- at `caps 9 1 1` — the smallest cSize its own telescope admits — with
-- every face hypothesis still `refl` and the count TRUE one fold up
------------------------------------------------------------------

pow-pos : ∀ (S w : ℕ) → 1 ≤ S → 1 ≤ S ^ w
pow-pos S zero    h = s≤s z≤n
pow-pos S (suc w) h = *-mono-≤ h (pow-pos S w h)

-- ONE fold turns a SIZE bound into a WIDTH bound
size≤widAt1 : ∀ (c : Caps) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cWid (frameStep 1 c)
size≤widAt1 c 1≤S =
  ≤-trans (≤-reflexive (sym (*-identityʳ (Caps.cSize c))))
          (*-monoʳ-≤ (Caps.cSize c) (pow-pos (Caps.cSize c) (Caps.cWid c) 1≤S))

c₈ : Caps
c₈ = caps 9 1 1

_ : slotsSize sl₈ ≡ Caps.cSize c₈
_ = refl

_ : slotsCaps? (Caps.cSize c₈) (Caps.cWid c₈) sl₈ ≡ true
_ = refl

_ : capsOK? (frameStep 0 c₈) sched₈ st₈ ≡ true
_ = refl

_ : pathSz? (Caps.cSize (frameStep 0 c₈)) (root {Γ = Γ₁} {t = natᵗ}) ≡ true
_ = refl

-- still false at the caps face's reported 0 …
_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 0 c₈) burst₈ ≡ false
_ = refl

-- … and true one fold up, which is what the size bound buys
_ : burstCount? {Γ = Γ₁} {u = natᵗ} (frameStep 1 c₈) burst₈ ≡ true
_ = refl
