------------------------------------------------------------------
-- THE TIMED TRANSLATION: the author's program rewritten so that every
-- value it emits carries a PACKET naming the instant that value
-- belongs to.  It is how the top line says "same instant" without
-- reading the evaluator: two emits are simultaneous when the timed
-- program gives them the same packet, and the impl's instant stamps
-- are held to that (`Timing-Correct`).
--
-- IT IS AN SEXP-TO-SEXP TRANSLATION, SO THE OPERATORS ARE BLIND TO IT.
-- The timed program is an ordinary program over the same formers,
-- run plain; a packet is just a value riding along, and nothing an
-- operator does can depend on it.  What makes the packets name
-- instants is the inputs: each scripted slot is tagged with its own
-- tick (`tickInput`), and the translation threads those tags, together
-- with the flattener positions they pass through, into the packet of
-- everything downstream.  A shared slot holds another program, so it
-- is translated too.
--
-- EVERY STREAM ENDS WITH AN END ITEM carrying the completion's packet.
-- A concat grafts its next inner on a completion, so what that inner
-- emits synchronously belongs to the instant the completion did, and
-- only the END item says which one that was: nothing the completed
-- inner emitted need carry it.  END is last, so `take` over a timed
-- stream counts values exactly as it does over the plain one.
------------------------------------------------------------------
module Timed.Translation where

open import Data.Bool    using (T)
open import Data.Fin     using (toℕ)
open import Data.List    using (List; []; _∷_; map)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (lookup; zipWith)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Rx.Prim  using (ObservableInput; hot; cold; Timed; after_,_)
open import Rx.Exp   using (Ty; Ctx; Val; isData; inputsBelowᵉ;
  unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs)
open import SExp.Syntax  using (SExp; Kind; Kinds; scriptedᵏ; sharedᵏ; plainᵗ)
open import SExp.Plain using (plainExp; mapInput; ∧ˡ; ∧ʳ)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; scriptedˢ; sharedˢ)

------------------------------------------------------------------
-- Types.
------------------------------------------------------------------

-- AN INSTANT'S NAME: the input and tick that started it, then one
-- step per flattener it passed through.  Only equality is ever read.
packetᵗ : Ty
packetᵗ = listᵗ natᵗ

-- A SCRIPTED DELIVERY'S TAG, which is all an input knows about when
-- it happened: synchronous at subscription (the subscriber's own
-- instant), the k-th tick of a hot input, or the k-th async tick of a
-- cold one counted from its subscription.
tickᵗ : Ty
tickᵗ = unitᵗ +ᵗ (natᵗ +ᵗ natᵗ)

mutual
  -- a stream's elements are items, all the way down
  timedᵗ : Ty → Ty
  timedᵗ unitᵗ     = unitᵗ
  timedᵗ boolᵗ     = boolᵗ
  timedᵗ natᵗ      = natᵗ
  timedᵗ uniqᵗ     = uniqᵗ
  timedᵗ (s ×ᵗ t)  = timedᵗ s ×ᵗ timedᵗ t
  timedᵗ (s +ᵗ t)  = timedᵗ s +ᵗ timedᵗ t
  timedᵗ (listᵗ t) = listᵗ (timedᵗ t)
  timedᵗ (obs t)   = obs (itemᵗ t)

  -- a value or the END marker, with its packet
  itemᵗ : Ty → Ty
  itemᵗ t = packetᵗ ×ᵗ (timedᵗ t +ᵗ unitᵗ)

-- a scripted slot carries its tick beside each payload; a shared slot
-- is a translated program, so it emits items
timedTy : Ty → Kind → Ty
timedTy t scriptedᵏ = tickᵗ ×ᵗ t
timedTy t sharedᵏ   = itemᵗ t

timedᶜ : ∀ {n} → Ctx n → Kinds n → Ctx n
timedᶜ Γ κ = zipWith timedTy Γ κ

------------------------------------------------------------------
-- The translation.
------------------------------------------------------------------

-- UNWRITTEN, AND A POSTULATED FUNCTION ASSERTS NOTHING: `λ _ → emptyˢ`
-- inhabits this type.  `timed-faithful` is what rules that out, and
-- `Timing-Correct` is what makes the packets mean instants; neither
-- is content until this has a body.  The TypeScript prototype
-- (`typescript/src/timed.ts`) is the route: its packets partition
-- emits exactly as rxjs call stacks do on every generated program.
--
-- A QUEUED INNER NEEDS AN ORDER ON PACKETS, NOT A MULTICAST.  Under a
-- concurrency-limited `mergeAll` an inner is subscribed at the LATER
-- of its own outer emission and the last lane instant before it, so
-- with packets that compare in the driver's (tick, ordinal) order the
-- translation needs no former it lacks: the `max-key` rule, `max`
-- resolved at the root.  Two places it still falls short, both pinned
-- by `timed-fuzz.ts --selftest`: `switchAll`'s own END, which needs the
-- outer's END and cannot take it as a lane without cancelling one; and
-- a SHARED slot, whose frame is anchored on each subscriber though it
-- connected on one, so a late subscriber's keys are wrong.  Two dynamic
-- sources registered in one arrival and firing at one tick are ordered
-- as the driver does by the `max-sub` rule: their registrations'
-- depth-first positions in that arrival's call stack, ranked at a hot
-- or shared fan-out by each subscriber's own subscription, not by
-- position in the program.  The default rule multicasts the outer with
-- rxjs `connect` and has neither gap.
postulate
  timed : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t}
        → SExp Γ [] [] [] t → SExp (timedᶜ Γ κ) [] [] [] (itemᵗ t)

  -- the translation reads the inputs its source read, and no others
  timed-below : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (k : ℕ) (d : SExp Γ [] [] [] t)
              → T (inputsBelowᵉ k (plainExp d))
              → T (inputsBelowᵉ k (plainExp (timed κ d)))

------------------------------------------------------------------
-- The slot table, translated.
------------------------------------------------------------------

-- a data value is the same value in every context
retypeᵈ : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} t → T (isData t) → Val Γ t → Val Γ′ t
retypeᵈ unitᵗ     ok v        = v
retypeᵈ boolᵗ     ok v        = v
retypeᵈ natᵗ      ok v        = v
retypeᵈ uniqᵗ     ok v        = v
retypeᵈ (s ×ᵗ t)  ok (a , b)  = retypeᵈ s (∧ˡ (isData s) ok) a , retypeᵈ t (∧ʳ (isData s) ok) b
retypeᵈ (s +ᵗ t)  ok (inj₁ a) = inj₁ (retypeᵈ s (∧ˡ (isData s) ok) a)
retypeᵈ (s +ᵗ t)  ok (inj₂ b) = inj₂ (retypeᵈ t (∧ʳ (isData s) ok) b)
retypeᵈ (listᵗ t) ok vs       = map (retypeᵈ t ok) vs
retypeᵈ (obs t)   () _

private
  ticks : ∀ {A : Set} → (ℕ → ⊤ ⊎ (ℕ ⊎ ℕ)) → ℕ → List (Timed A)
        → List (Timed ((⊤ ⊎ (ℕ ⊎ ℕ)) × A))
  ticks tag k []                = []
  ticks tag k ((after w , v) ∷ as) = (after w , (tag k , v)) ∷ ticks tag (suc k) as

-- EACH DELIVERY TAGGED WITH ITS OWN TICK, which is the only timing
-- fact the translation is handed
tickInput : ∀ {A : Set} → ObservableInput A → ObservableInput ((⊤ ⊎ (ℕ ⊎ ℕ)) × A)
tickInput (hot as)     = hot (ticks (λ k → inj₂ (inj₁ k)) zero as)
tickInput (cold ss as) = cold (map (inj₁ tt ,_) ss) (ticks (λ k → inj₂ (inj₂ k)) zero as)

timedSlots : ∀ {n} {Γ : Ctx n} {κ : Kinds n} → SimulSlots Γ κ → SimulSlots (timedᶜ Γ κ) κ
timedSlots {Γ = Γ} {κ = κ} ins i =
  subst (λ τ → SimulSlot (timedᶜ Γ κ) κ (toℕ i) τ (lookup κ i))
        (sym (lookup-zipWith timedTy i Γ κ))
        (go (lookup κ i) (ins i))
  where
    go : ∀ kd → SimulSlot Γ κ (toℕ i) (lookup Γ i) kd
       → SimulSlot (timedᶜ Γ κ) κ (toℕ i) (timedTy (lookup Γ i) kd) kd
    go scriptedᵏ (scriptedˢ {ok = ok} inp) =
      scriptedˢ {ok = ok} (tickInput (mapInput (retypeᵈ (plainᵗ (lookup Γ i)) ok) inp))
    go sharedᵏ   (sharedˢ d {ok = ok})     =
      sharedˢ (timed κ d) {ok = timed-below κ (toℕ i) d ok}

------------------------------------------------------------------
-- Reading a timed run.
------------------------------------------------------------------

-- an item's packet, at the impl's reading of the item type
packetOf : ∀ {n} {Γ : Ctx n} t → Val Γ (plainᵗ (itemᵗ t)) → List ℕ
packetOf t = proj₁

-- the values a timed run carries, END markers dropped
valuesᵀ : ∀ {n} {Γ : Ctx n} {t} → List (Val Γ (itemᵗ t)) → List (Val Γ (timedᵗ t))
valuesᵀ []                  = []
valuesᵀ ((_ , inj₁ v) ∷ xs) = v ∷ valuesᵀ xs
valuesᵀ ((_ , inj₂ _) ∷ xs) = valuesᵀ xs

-- `timedᵗ` is the identity on data
untimedᵈ : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} t → T (isData t) → Val Γ′ (timedᵗ t) → Val Γ t
untimedᵈ unitᵗ     ok v        = v
untimedᵈ boolᵗ     ok v        = v
untimedᵈ natᵗ      ok v        = v
untimedᵈ uniqᵗ     ok v        = v
untimedᵈ (s ×ᵗ t)  ok (a , b)  = untimedᵈ s (∧ˡ (isData s) ok) a , untimedᵈ t (∧ʳ (isData s) ok) b
untimedᵈ (s +ᵗ t)  ok (inj₁ a) = inj₁ (untimedᵈ s (∧ˡ (isData s) ok) a)
untimedᵈ (s +ᵗ t)  ok (inj₂ b) = inj₂ (untimedᵈ t (∧ʳ (isData s) ok) b)
untimedᵈ (listᵗ t) ok vs       = map (untimedᵈ t ok) vs
untimedᵈ (obs t)   () _
