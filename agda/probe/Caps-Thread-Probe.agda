-- CAPS-THREAD PROBE (2026-08-05).  Rehearsal site for GAP 4's second
-- invariant: the width/pop lemmas that let `capsOK?`/`valCaps?` travel
-- beside `INV?`/`valB?` down the wet chain.
--
-- WHY A PROBE.  These bodies land in .Caps-Bridge, not .Wet — see
-- PROOF-STATE.md § "RULING: Caps-Bridge was built UPSIDE DOWN".  A
-- dirty .Wet costs ~9 min per iteration; an UNCHANGED .Wet is a cached
-- interface and deserializes in seconds, so this probe is a faithful
-- rehearsal of the real landing site (which also sits above .Wet) at a
-- fraction of the cost.  Land only bodies that are green here.
--
-- STAGE 1 (this file): the eight genuinely-new lemmas.  The three slots
-- lemmas the first attempt also wrote are NOT here on purpose —
-- .Caps-Bridge already proves them (`slots-tick`, `chainStep-slots`,
-- `cascadeGo-slots`) and duplicating them was the cost that ruling
-- rejected.
module Caps-Thread-Probe where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat  using (ℕ; zero; suc; _≤ᵇ_)
open import Data.List using (List; []; _∷_; all)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim using (Id; Fuel)
open import Rx.Exp  using (Ty; Ctx; Closed)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                arrTy; arrVal; sched-next; schedGo;
                                schedHeadOf; schedEarlier;
                                cascade; drain; hasDry; subscribeE; budgetAt;
                                root; sched-init; st-init; evaluate)

-- the wet family: INV?, ΨAt, sizeCapAt, capsAt, valB?, INV-parts,
-- pop-bounded, pop-slots, pop-head-bounded, the Bool toolkit
-- (∧-true/∧-intro), and the Caps record — all via .Wet's public chain
-- Wet → Caps → Keeps-Ring → Measures.  UNCHANGED on disk, so this is a
-- deserialize, not a recheck.
open import Verify-Budget-Sufficient.Wet

-- the caps face, named explicitly: .Caps-Face re-exports the same
-- Measures names .Wet does (both chain down to it), so a bare open
-- would make every shared name ambiguous.
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; valCaps?; caps-tick; capsOK?-parts; widLive; widNode)

-- THE PIECE THE WHOLE RULING TURNS ON.  .Caps-Bridge already proves the
-- joint one-cascade step; .Wet cannot consume it (.Caps-Bridge imports
-- .Wet), but a module ABOVE .Wet can — which is what the real landing
-- site will be.  Named explicitly so this probe records exactly what it
-- spends.
open import Verify-Budget-Sufficient.Caps-Bridge
  using (cascade-wet-via-caps; slots-tick)

------------------------------------------------------------------
-- § 1  THE HEAD, WIDTH HALF.  capsOK?'s `widLive` conjunct, extracted
-- at the popped arrival — the width sibling of GAP 3's
-- schedHeadOf-head/schedGo-head.
--
-- NOTE ON `cOK`: the first attempt named this hypothesis `caps` and
-- Agda rejected the LHS with "caps is not a constructor of the
-- datatype _≡_".  CAUSE, confirmed: `caps` IS a constructor in scope —
-- it is the `Caps` record's own constructor (Caps.agda:105,
-- `constructor caps`) — so in a pattern the name resolves to that
-- constructor instead of binding fresh.  Same family as the
-- PatternShadowsConstructor warning `make agda-all` prints for
-- CLI/Encode.agda's `dried`, except fatal here because the argument's
-- type is `_≡_` and `caps` belongs to a different datatype.  Any
-- lowercase record-constructor name is a landmine as a variable:
-- `caps`, `slots`, `sched` are all worth checking before use.
------------------------------------------------------------------

schedHeadOf-widHead : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  widLive W sl l ≡ true →
  (pWᵛ n sl (arrTy a) (arrVal a) ≤ᵇ W) ≡ true
schedHeadOf-widHead W sl l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₁ (∧-true _ _ bnd′)

schedGo-widHead : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (widLive W sl) ls ≡ true →
  (pWᵛ n sl (arrTy a) (arrVal a) ≤ᵇ W) ≡ true
schedGo-widHead W sl (l ∷ ls) eq bs
  with ∧-true (widLive W sl l) (all (widLive W sl) ls) bs
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-widHead W sl (l ∷ ls) refl bs | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  schedGo-widHead W sl ls eqR bls
schedGo-widHead W sl (l ∷ ls) refl bs | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  schedHeadOf-widHead W sl l eqH bl
schedGo-widHead W sl (l ∷ ls) eq bs | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = schedHeadOf-widHead W sl l eqH bl
... | false | refl = schedGo-widHead W sl ls eqR bls

pop-head-widCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  capsOK? c sched st ≡ true →
  (pWᵛ n (Sched.slots sched) (arrTy a) (arrVal a) ≤ᵇ Caps.cWid c) ≡ true
pop-head-widCaps c sched st eq cOK
  with capsOK?-parts c sched st cOK
... | _ , _ , wl , _ , _ with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      schedGo-widHead (Caps.cWid c) (Sched.slots sched) (Sched.live sched) eqL wl

-- the joint reader cascade-dry's caps face wants.  The SIZE half is
-- free: `sizeCapAt e sl id` IS `Caps.cSize (capsAt e sl id)` by
-- definition (Wet.agda:4117), so GAP 3's pop-head-bounded already
-- supplies it; only the width half above is new content.
pop-head-valCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? (ΨAt e (Sched.slots sched)) (sizeCapAt e (Sched.slots sched) id) sched st ≡ true →
  capsOK? (capsAt e (Sched.slots sched) id) sched st ≡ true →
  valCaps? (capsAt e (Sched.slots sched) id) (Sched.slots sched) (arrTy a) (arrVal a) ≡ true
-- `valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)` (Measures:5337)
-- and `valCaps? c sl u v = (sizeᵛ u v ≤ᵇ cSize c) ∧ (pWᵛ n sl u v ≤ᵇ cWid c)`
-- (Caps-Face:667).  At `B = sizeCapAt e sl id = cSize (capsAt e sl id)`
-- the two FIRST conjuncts are literally the same Bool, so the size half
-- is a projection off pop-head-bounded — via ∧-true, since valB? is a
-- Bool conjunction and not a Σ (the first attempt used proj₁ directly
-- and that is what the probe caught).
pop-head-valCaps {e = e} id sched st eq inv cOK =
  ∧-intro
    (proj₁ (∧-true _ _
      (pop-head-bounded (ΨAt e (Sched.slots sched))
                        (sizeCapAt e (Sched.slots sched) id) sched st eq inv)))
    (pop-head-widCaps (capsAt e (Sched.slots sched) id) sched st eq cOK)

------------------------------------------------------------------
-- § 2  THE TAIL.  capsOK? survives a pop — the capsOK? sibling of
-- `pop-INV`.  Four of the five conjuncts are pop-bounded /
-- untouched / pop-slots-transported exactly as pop-INV's are; only
-- widLive needs a new tail-preserving induction, the same shape as
-- `pop-fnCap`'s `schedGo-fnCap`.
------------------------------------------------------------------

schedHeadOf-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  widLive W sl l ≡ true → widLive W sl l′ ≡ true
schedHeadOf-widLive W sl l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (widLive W sl) ls ≡ true → all (widLive W sl) ls′ ≡ true
schedGo-widLive W sl (l ∷ ls) eq bnd
  with ∧-true (widLive W sl l) (all (widLive W sl) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-widLive W sl (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-widLive W sl ls eqR bls)
schedGo-widLive W sl (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-widLive W sl l eqH bl) bls
schedGo-widLive W sl (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-widLive W sl l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-widLive W sl ls eqR bls)

pop-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sched : Sched Γ)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  all (widLive W (Sched.slots sched)) (Sched.live sched) ≡ true →
  all (widLive W (Sched.slots sched′)) (Sched.live sched′) ≡ true
pop-widLive W sched eq h with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl = schedGo-widLive W (Sched.slots sched) (Sched.live sched) eqL h

pop-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  capsOK? c sched st ≡ true → capsOK? c sched′ st ≡ true
pop-caps c sched st eq h with capsOK?-parts c sched st h
... | sb , rg , wl , wn , rl =
  ∧-intro (pop-bounded (Caps.cSize c) sched st eq sb)
  (∧-intro rg
  (∧-intro (pop-widLive (Caps.cWid c) sched eq wl)
  (∧-intro (subst (λ sl → all (λ kv → widNode (Caps.cWid c) sl (proj₂ kv)) (EvalSt.nodes st) ≡ true)
                  (sym (pop-slots sched eq)) wn)
           rl)))

------------------------------------------------------------------
-- § 3  STAGE 2 — THE ASSEMBLY.  The fuel loop and the theorem, with
-- `capsOK?` travelling beside `INV?`.
--
-- NOTE what is NOT restated here: the one-cascade step.  `cascade-dry`
-- threaded with a caps face has EXACTLY `cascade-wet-via-caps`'s
-- conclusion, character for character (Caps-Bridge.agda:527-530), so
-- that step is a relocation and not a proof.  Its dryness half rests on
-- `dry-tick`, which is where the ANCHOR PROBLEM sits — the postulate
-- this route trades P2 (`cascadeGo-wet`) for.
------------------------------------------------------------------

postulate
  -- GAP 4's CAPS-SIDE LANDING FOR P1, typed rather than left in prose:
  -- the root subscribe's own burst lands `capsOK?` at instant 1, exactly
  -- as `burst-wet` already lands `INV?` there.  NOT VACUOUS: a plain
  -- `≡ true` equation, no Σ and no witness to enlarge, and capsOK?'s
  -- conjuncts are real constraints on the post-burst state.
  --
  -- TO CHECK BEFORE LANDING: `sub-charge` (Caps-Bridge.agda:420, PROVEN,
  -- GAP 4(a)) is the subscribe-level charge.  If it discharges this,
  -- this postulate must NOT be landed — an assumption beside its own
  -- proof is the worst outcome available here.
  burst-caps : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in capsOK? (capsAt e ins 1) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

drain-dry-threaded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  INV? (ΨAt e (Sched.slots sched)) (sizeCapAt e (Sched.slots sched) id)
       sched st ≡ true →
  capsOK? (capsAt e (Sched.slots sched) id) sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry-threaded zero    id sched st inv cOK = refl
drain-dry-threaded (suc k) id sched st inv cOK with sched-next sched in eq
... | inj₁ _            = refl
drain-dry-threaded {e = e} (suc k) id sched st inv cOK | inj₂ (a , sched′) =
  let Ψ = ΨAt e (Sched.slots sched)
      B = sizeCapAt e (Sched.slots sched) id
      C = capsAt e (Sched.slots sched) id
      inv′ : INV? (ΨAt e (Sched.slots sched′))
                  (sizeCapAt e (Sched.slots sched′) id) sched′ st ≡ true
      inv′ = subst
               (λ sl → INV? (ΨAt e sl) (sizeCapAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-INV Ψ B sched st eq inv)
      val′ : valB? (sizeCapAt e (Sched.slots sched′) id)
                   (ΨAt e (Sched.slots sched′)) (arrTy a) (arrVal a) ≡ true
      val′ = subst
               (λ sl → valB? (sizeCapAt e sl id) (ΨAt e sl)
                             (arrTy a) (arrVal a) ≡ true)
               (sym (pop-slots sched eq))
               (pop-head-bounded Ψ B sched st eq inv)
      caps′ : capsOK? (capsAt e (Sched.slots sched′) id) sched′ st ≡ true
      caps′ = subst
               (λ sl → capsOK? (capsAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-caps C sched st eq cOK)
      valC′ : valCaps? (capsAt e (Sched.slots sched′) id) (Sched.slots sched′)
                       (arrTy a) (arrVal a) ≡ true
      valC′ = subst
               (λ sl → valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true)
               (sym (pop-slots sched eq))
               (pop-head-valCaps id sched st eq inv cOK)
      (dry₁ , inv″ , caps″) = cascade-wet-via-caps a id sched′ st inv′ val′ caps′ valC′
  in hasDry-append (proj₁ (cascade a id sched′ st)) _
       dry₁
       (drain-dry-threaded k (suc id)
         (proj₁ (proj₂ (cascade a id sched′ st)))
         (proj₂ (proj₂ (cascade a id sched′ st)))
         inv″
         caps″)

-- THE THEOREM.  Same face as .Wet's `budget-sufficient` — it does not
-- move.  Only the interior changes: it now also seeds and carries
-- capsOK?, transported from `ins` to the post-burst sched's own slots by
-- subscribeE-slots.
budget-sufficient-threaded :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
budget-sufficient-threaded fuel e ins =
  hasDry-append
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)))
    _
    (burst-dry e ins)
    (drain-dry-threaded fuel 1 sched₁ st₁ (burst-bounded e ins) caps₁)
  where
  sched₁ = proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                    (sched-init e ins) (st-init e)))
  st₁    = proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                    (sched-init e ins) (st-init e)))
  slEq : Sched.slots sched₁ ≡ ins
  slEq = subscribeE-slots (budgetAt e ins 0) e root 0 0
                          (sched-init e ins) (st-init e)
  caps₁ : capsOK? (capsAt e (Sched.slots sched₁) 1) sched₁ st₁ ≡ true
  caps₁ = subst (λ s → capsOK? (capsAt e s 1) sched₁ st₁ ≡ true)
                (sym slEq)
                (burst-caps e ins)
