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
-- inner emitted need carry it.
------------------------------------------------------------------
module Timed.Translation where

open import Data.Bool    using (Bool; T; true; false; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.List    using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (nothing; just)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (lookup; zipWith)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import Rx.Prim  using (ObservableInput; hot; cold; Timed; after_,_)
open import Rx.Exp   using (Ty; Ctx; Val; isData; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ; PrimOp;
  add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ; FlatOp; mergeᶠ;
  unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs)
open import SExp.Syntax  using (SExp; STm; Kind; Kinds; hotᵏ; coldᵏ; sharedᵏ; plainᵗ;
  inputˢ; ofˢ; emptyˢ; takeWhileˢ; mapˢ; scanˢ; flattenˢ; μˢ; varˢ; deferˢ;
  varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ;
  caseˢ; foldˢ; ifˢ; primˢ; strmˢ)
open import SExp.Plain using (plainExp; plainTm; plainTms; mapInput; ∧ˡ; ∧ʳ; ∧-intro)
open import Decide using (∧⁺) renaming (∧ˡ to ∧ˡᵇ; ∧ʳ to ∧ʳᵇ)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; sharedˢ)

------------------------------------------------------------------
-- Types.
------------------------------------------------------------------

-- AN INSTANT'S NAME: the input and tick that started it, then one
-- step per frame it passed out of.  Only equality is ever read, so the
-- encoding need only be injective.  A leading tag says which kind of
-- name it is: the empty list is the HOLE, the instant the stream was
-- subscribed in; `1 i k` the k-th tick of hot slot i; `2` a name
-- RELATIVE to the frame it was minted in -- `0 i k`, the k-th async
-- tick of a subscription to cold slot i, or `1 d 0`, the hop of the
-- defer at depth d -- followed by one `d n` per frame it has left,
-- innermost first; and `3 j` a relative name closed by shared slot j,
-- which subscribes its program once.
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
timedTy t hotᵏ    = tickᵗ ×ᵗ timedᵗ t
timedTy t coldᵏ   = tickᵗ ×ᵗ timedᵗ t
timedTy t sharedᵏ = itemᵗ t

timedᶜ : ∀ {n} → Ctx n → Kinds n → Ctx n
timedᶜ Γ κ = zipWith timedTy Γ κ

-- an element of a flattener's outer, translated: its echo and its lane
Elemᵗ : Ty → Ty
Elemᵗ t = (unitᵗ +ᵗ timedᵗ t) ×ᵗ (unitᵗ +ᵗ obs (itemᵗ t))

-- what a translated flattener's own flatten carries: an outer element's
-- echo with its BEAT (the packet it arrived at, present when it opens a
-- lane or ends the outer), a lane's START, a lane's item, and the end
Echoᵗ : Ty → Ty
Echoᵗ t = (unitᵗ +ᵗ itemᵗ t) ×ᵗ (unitᵗ +ᵗ packetᵗ)

Msgᵗ : Ty → Ty
Msgᵗ t = Echoᵗ t +ᵗ (natᵗ +ᵗ ((natᵗ ×ᵗ itemᵗ t) +ᵗ unitᵗ))

-- the last packet seen, each lane's subscribe packet, and what to emit
Seenᵗ : Ty → Ty
Seenᵗ t = packetᵗ ×ᵗ (listᵗ (natᵗ ×ᵗ packetᵗ) ×ᵗ (unitᵗ +ᵗ itemᵗ t))

-- the last packet seen, whether an END was, and what to emit
EndSt : Ty → Ty
EndSt t = packetᵗ ×ᵗ (boolᵗ ×ᵗ (unitᵗ +ᵗ itemᵗ t))

------------------------------------------------------------------
-- Vocabulary: terms and streams every translated former is built of.
-- Each body under a binder reads only its own binders, so none needs
-- a weakening.
------------------------------------------------------------------

module _ {n} {Γ : Ctx n} {Δᵍ Δ : List Ty} where

  v₀ : ∀ {Θ a} → STm Γ Δᵍ Δ (a ∷ Θ) a
  v₀ = varˢᵗ (here refl)

  v₁ : ∀ {Θ a b} → STm Γ Δᵍ Δ (a ∷ b ∷ Θ) b
  v₁ = varˢᵗ (there (here refl))

  v₂ : ∀ {Θ a b c} → STm Γ Δᵍ Δ (a ∷ b ∷ c ∷ Θ) c
  v₂ = varˢᵗ (there (there (here refl)))

  v₃ : ∀ {Θ a b c d} → STm Γ Δᵍ Δ (a ∷ b ∷ c ∷ d ∷ Θ) d
  v₃ = varˢᵗ (there (there (there (here refl))))

  v₄ : ∀ {Θ a b c d e} → STm Γ Δᵍ Δ (a ∷ b ∷ c ∷ d ∷ e ∷ Θ) e
  v₄ = varˢᵗ (there (there (there (there (here refl)))))

  letˢ : ∀ {Θ a u} → STm Γ Δᵍ Δ Θ a → STm Γ Δᵍ Δ (a ∷ Θ) u → STm Γ Δᵍ Δ Θ u
  letˢ m b = caseˢ (inlˢ m) b v₀

  litˢ : ∀ {Θ} → List ℕ → STm Γ Δᵍ Δ Θ packetᵗ
  litˢ []       = nilˢ
  litˢ (k ∷ ks) = consˢ (natˢ k) (litˢ ks)

  eqˢ : ∀ {Θ} → STm Γ Δᵍ Δ Θ natᵗ → STm Γ Δᵍ Δ Θ natᵗ → STm Γ Δᵍ Δ Θ boolᵗ
  eqˢ a b = primˢ eqᵖ (pairˢ a b)

  -- `foldˢ` is a LEFT fold, so consing reverses
  revˢ : ∀ {Θ a} → STm Γ Δᵍ Δ Θ (listᵗ a) → STm Γ Δᵍ Δ Θ (listᵗ a)
  revˢ xs = foldˢ xs nilˢ (consˢ v₀ v₁)

  appendˢ : ∀ {Θ a} → STm Γ Δᵍ Δ Θ (listᵗ a) → STm Γ Δᵍ Δ Θ (listᵗ a) → STm Γ Δᵍ Δ Θ (listᵗ a)
  appendˢ xs ys = foldˢ (revˢ xs) ys (consˢ v₀ v₁)

  nullˢ : ∀ {Θ a} → STm Γ Δᵍ Δ Θ (listᵗ a) → STm Γ Δᵍ Δ Θ boolᵗ
  nullˢ xs = foldˢ xs (boolˢ true) (boolˢ false)

  headIsˢ : ∀ {Θ} → ℕ → STm Γ Δᵍ Δ Θ packetᵗ → STm Γ Δᵍ Δ Θ boolᵗ
  headIsˢ k p = sndˢ (foldˢ p (pairˢ (boolˢ false) (boolˢ false))
    (ifˢ (fstˢ v₁) v₁ (pairˢ (boolˢ true) (eqˢ v₀ (natˢ k)))))

  -- the packet paired with lane k
  lookupˢ : ∀ {Θ} → STm Γ Δᵍ Δ Θ natᵗ → STm Γ Δᵍ Δ Θ (listᵗ (natᵗ ×ᵗ packetᵗ))
          → STm Γ Δᵍ Δ Θ packetᵗ
  lookupˢ k ps = sndˢ (foldˢ ps (pairˢ k nilˢ)
    (pairˢ (fstˢ v₁) (ifˢ (eqˢ (fstˢ v₀) (fstˢ v₁)) (sndˢ v₀) (sndˢ v₁))))

  -- A PACKET LEAVING SUB-FRAME `seg`, which was subscribed in instant
  -- `sp`: the hole is that instant, a relative name gains the frame, an
  -- absolute one is untouched
  substᵖ : ∀ {Θ} → STm Γ Δᵍ Δ Θ packetᵗ → STm Γ Δᵍ Δ Θ packetᵗ → STm Γ Δᵍ Δ Θ packetᵗ
         → STm Γ Δᵍ Δ Θ packetᵗ
  substᵖ seg sp p = ifˢ (nullˢ p) sp (ifˢ (headIsˢ 2 p) (appendˢ p seg) p)

  -- A SHARE CONNECTS ONCE, so its frame is unique and every relative
  -- name inside it closes there.  The hole stays a hole: a connect's
  -- burst belongs to whichever subscriber connected it.
  closeᵖ : ∀ {Θ} → ℕ → STm Γ Δᵍ Δ Θ packetᵗ → STm Γ Δᵍ Δ Θ packetᵗ
  closeᵖ j p = ifˢ (headIsˢ 2 p) (consˢ (natˢ 3) (consˢ (natˢ j) p)) p

  -- a scripted delivery's name, read off its tag for slot i
  tickᵖ : ∀ {Θ} → ℕ → STm Γ Δᵍ Δ Θ tickᵗ → STm Γ Δᵍ Δ Θ packetᵗ
  tickᵖ i k = caseˢ k nilˢ
    (caseˢ v₀ (consˢ (natˢ 1) (consˢ (natˢ i) (consˢ v₀ nilˢ)))
              (consˢ (natˢ 2) (consˢ (natˢ 0) (consˢ (natˢ i) (consˢ v₀ nilˢ)))))

  -- the present ones, in order: an echo-only flatten
  someˢ : ∀ {Θ t} → SExp Γ Δᵍ Δ Θ (unitᵗ +ᵗ t) → SExp Γ Δᵍ Δ Θ t
  someˢ e = flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ v₀ (inlˢ unitˢ)) e)

  -- spelled out rather than `map`ped, so the recursion is structural
  lanesˢ : ∀ {Θ t} → List (SExp Γ Δᵍ Δ Θ t)
         → List (STm Γ Δᵍ Δ Θ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)))
  lanesˢ []       = []
  lanesˢ (e ∷ es) = pairˢ (inlˢ unitˢ) (inrˢ (strmˢ e)) ∷ lanesˢ es

  concatˢ : ∀ {Θ t} → List (SExp Γ Δᵍ Δ Θ t) → SExp Γ Δᵍ Δ Θ t
  concatˢ es = flattenˢ (mergeᶠ (just 1)) (ofˢ (lanesˢ es))

  -- a stream value, subscribed
  runˢ : ∀ {Θ t} → STm Γ Δᵍ Δ Θ (obs t) → SExp Γ Δᵍ Δ Θ t
  runˢ o = flattenˢ (mergeᶠ nothing) (ofˢ (pairˢ (inlˢ unitˢ) (inrˢ o) ∷ []))

  endStepˢ : ∀ {Θ t} → STm Γ Δᵍ Δ ((EndSt t ×ᵗ (itemᵗ t +ᵗ unitᵗ)) ∷ Θ) (EndSt t)
  endStepˢ = caseˢ (sndˢ v₀)
    (pairˢ (fstˢ v₀) (pairˢ (caseˢ (sndˢ v₀) (boolˢ false) (boolˢ true)) (inrˢ v₀)))
    (ifˢ (fstˢ (sndˢ (fstˢ v₁)))
         (pairˢ nilˢ (pairˢ (boolˢ true) (inlˢ unitˢ)))
         (pairˢ nilˢ (pairˢ (boolˢ true) (inrˢ (pairˢ (fstˢ (fstˢ v₁)) (inrˢ unitˢ))))))

  -- THE END ITEM APPENDED, carrying the last packet seen, unless the
  -- stream already ended with one.  A stream that completes having
  -- emitted nothing ends in its own subscription: the hole.
  endAfterˢ : ∀ {Θ t} → SExp Γ Δᵍ Δ Θ (itemᵗ t) → SExp Γ Δᵍ Δ Θ (itemᵗ t)
  endAfterˢ {t = t} e =
    someˢ (mapˢ (sndˢ (sndˢ v₀))
      (scanˢ (endStepˢ {t = t}) (pairˢ nilˢ (pairˢ (boolˢ false) (inlˢ unitˢ)))
        (concatˢ (mapˢ (inlˢ v₀) e ∷ ofˢ (inrˢ unitˢ ∷ []) ∷ []))))

  -- an outer element numbered by the lanes opened so far, its own
  -- included
  numberStepˢ : ∀ {Θ t} → STm Γ Δᵍ Δ
    (((natᵗ ×ᵗ (packetᵗ ×ᵗ (Elemᵗ t +ᵗ unitᵗ))) ×ᵗ (packetᵗ ×ᵗ (Elemᵗ t +ᵗ unitᵗ))) ∷ Θ)
    (natᵗ ×ᵗ (packetᵗ ×ᵗ (Elemᵗ t +ᵗ unitᵗ)))
  numberStepˢ = pairˢ
    (caseˢ (sndˢ (sndˢ v₀))
      (caseˢ (sndˢ v₀) (fstˢ (fstˢ v₂)) (primˢ add (pairˢ (fstˢ (fstˢ v₂)) (natˢ 1))))
      (fstˢ (fstˢ v₁)))
    (sndˢ v₀)

  -- lane k: its START, then the inner's items tagged with k
  laneˢ : ∀ {Θ a b t} → SExp Γ Δᵍ Δ (obs (itemᵗ t) ∷ a ∷ (natᵗ ×ᵗ b) ∷ Θ) (Msgᵗ t)
  laneˢ = concatˢ
    ( ofˢ (inrˢ (inlˢ (fstˢ v₂)) ∷ [])
    ∷ mapˢ (inrˢ (inrˢ (inlˢ (pairˢ (fstˢ v₃) v₀)))) (runˢ v₀)
    ∷ [])

  -- THE ECHO LEAVES BEFORE THE LANE IS HANDLED, as the source's own does:
  -- an element's echo carries the author's echo and the element's beat,
  -- and its lane is the lane it carries.  The outer's END is a beat with
  -- no lane, and no policy sees an element without one.
  elemˢ : ∀ {Θ t} → STm Γ Δᵍ Δ ((natᵗ ×ᵗ (packetᵗ ×ᵗ (Elemᵗ t +ᵗ unitᵗ))) ∷ Θ)
                      ((unitᵗ +ᵗ Msgᵗ t) ×ᵗ (unitᵗ +ᵗ obs (Msgᵗ t)))
  elemˢ {t = t} = caseˢ (sndˢ (sndˢ v₀))
    (pairˢ (inrˢ (inlˢ (pairˢ
              (caseˢ (fstˢ v₀) (inlˢ unitˢ) (inrˢ (pairˢ (fstˢ (sndˢ v₂)) (inlˢ v₀))))
              (caseˢ (sndˢ v₀) (inlˢ unitˢ) (inrˢ (fstˢ (sndˢ v₂)))))))
           (caseˢ (sndˢ v₀) (inlˢ unitˢ) (inrˢ (strmˢ (laneˢ {t = t})))))
    (pairˢ (inrˢ (inlˢ (pairˢ (inlˢ unitˢ) (inrˢ (fstˢ (sndˢ v₁)))))) (inlˢ unitˢ))

  -- A LANE IS SUBSCRIBED IN THE LAST INSTANT SEEN BEFORE ITS START: a
  -- beat's, or a lane item's.  Each lane item leaves its frame, and the
  -- flattener ends in the last instant seen.
  seenStepˢ : ∀ {Θ t} → ℕ → STm Γ Δᵍ Δ ((Seenᵗ t ×ᵗ Msgᵗ t) ∷ Θ) (Seenᵗ t)
  seenStepˢ d = caseˢ (sndˢ v₀)
    (pairˢ (caseˢ (sndˢ v₀) (fstˢ (fstˢ v₂)) v₀)
           (pairˢ (fstˢ (sndˢ (fstˢ v₁))) (fstˢ v₀)))
    (caseˢ v₀
      (pairˢ (fstˢ (fstˢ v₂))
             (pairˢ (consˢ (pairˢ v₀ (fstˢ (fstˢ v₂))) (fstˢ (sndˢ (fstˢ v₂))))
                    (inlˢ unitˢ)))
      (caseˢ v₀
        (letˢ (substᵖ (consˢ (natˢ d) (consˢ (fstˢ v₀) nilˢ))
                      (lookupˢ (fstˢ v₀) (fstˢ (sndˢ (fstˢ v₃))))
                      (fstˢ (sndˢ v₀)))
          (pairˢ v₀ (pairˢ (fstˢ (sndˢ (fstˢ v₄)))
                           (caseˢ (sndˢ (sndˢ v₁)) (inrˢ (pairˢ v₁ (inlˢ v₀))) (inlˢ unitˢ)))))
        (pairˢ (fstˢ (fstˢ v₃))
               (pairˢ (fstˢ (sndˢ (fstˢ v₃)))
                      (inrˢ (pairˢ (fstˢ (fstˢ v₃)) (inrˢ unitˢ)))))))

  -- THE FLATTENER AT DEPTH d, over its translated outer: one flatten
  -- under the source's policy, its echoes and lanes read back in order
  flattenᵀ : ∀ {Θ t} → ℕ → FlatOp → SExp Γ Δᵍ Δ Θ (packetᵗ ×ᵗ (Elemᵗ t +ᵗ unitᵗ))
           → SExp Γ Δᵍ Δ Θ (itemᵗ t)
  flattenᵀ {t = t} d op e =
    someˢ (mapˢ (sndˢ (sndˢ v₀))
      (scanˢ (seenStepˢ {t = t} d) (pairˢ nilˢ (pairˢ nilˢ (inlˢ unitˢ)))
        (concatˢ
          ( flattenˢ op (mapˢ (elemˢ {t = t})
              (scanˢ numberStepˢ (pairˢ (natˢ 0) (pairˢ nilˢ (inrˢ unitˢ))) e))
          ∷ ofˢ (inrˢ (inrˢ (inrˢ unitˢ)) ∷ [])
          ∷ []))))

------------------------------------------------------------------
-- The translation.
------------------------------------------------------------------

-- a term variable, at its timed type
Ren : List Ty → List Ty → Set
Ren Θ Θ′ = ∀ {u} → u ∈ Θ → timedᵗ u ∈ Θ′

extᵀ : ∀ {Θ Θ′ s} → Ren Θ Θ′ → Ren (s ∷ Θ) (timedᵗ s ∷ Θ′)
extᵀ ρ (here p)  = here (cong timedᵗ p)
extᵀ ρ (there x) = there (ρ x)

wkᵀ : ∀ {Θ Θ′ a} → Ren Θ Θ′ → Ren Θ (a ∷ Θ′)
wkᵀ ρ x = there (ρ x)

noneᵀ : ∀ {Θ′} → Ren [] Θ′
noneᵀ ()

-- every primitive is over data, which the translation leaves alone
timedᵒ : ∀ {s t} → PrimOp s t → PrimOp (timedᵗ s) (timedᵗ t)
timedᵒ add  = add
timedᵒ sub  = sub
timedᵒ mul  = mul
timedᵒ eqᵖ  = eqᵖ
timedᵒ ltᵖ  = ltᵖ
timedᵒ eqᵘ  = eqᵘ
timedᵒ notᵖ = notᵖ

-- THE TRANSLATION IS THE `echo` RULE OF `typescript/src/timed.ts`,
-- former for former, its packets names alone.  `d` is a node's depth in
-- its frame, which names a flattener's lanes and a defer's hop; every
-- stream former has at most one stream child, so depth is a position.
-- A stream value's body is a frame of its own, entered through a lane.
--
-- WITHOUT AN ECHO, PACKETS MUST BE ORDERED rather than only named: a
-- queued inner is subscribed at the LATER of its outer emission and the
-- last lane instant, which the `max-` rules there resolve by computed
-- keys, reading `switchAll`'s END off a second copy of the outer.  They
-- fall short where a shared slot's keys are anchored on a late
-- subscriber, and where a scheduling outer reaches a share.
--
-- DEAD ROUTE: a flattener reporting only a Start and a Done per lane and
--   an OuterDone.  A lane whose outer value arrives after the previous
--   lane's Done reads exactly as a queued one, and the OuterDone carries
--   no instant; `timed-fuzz.ts --selftest` pins both under its `markers`
--   rule.
-- DEAD ROUTE: the echo spelled with lane-only flattens.  Every outer
--   element, its END item included, must reach both the beat and the
--   policy, and within one subscription a stream reaches ONE operator;
--   the palette's only fan-out is a shared slot, which the table fixes,
--   and subscribing the outer twice mints a second schedule.  Folding the
--   beat into its lane as a leading `ofˢ` holds under an unbounded merge
--   and nowhere else: an exhaust drops the beat with its lane, a bounded
--   merge queues it, and under a switch the END item's beat, as an inner,
--   cancels the live lane.
module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a slot read as items, ended where its source completes: a scripted
  -- slot's tag named, a shared slot's items as its own translation left
  -- them
  inputᵏ : ∀ {Δᵍ Δ Θ} (i : Fin n) kd → SExp (timedᶜ Γ κ) Δᵍ Δ Θ (timedTy (lookup Γ i) kd)
         → SExp (timedᶜ Γ κ) Δᵍ Δ Θ (itemᵗ (lookup Γ i))
  inputᵏ i hotᵏ    e = endAfterˢ {t = lookup Γ i}
    (mapˢ (pairˢ (tickᵖ (toℕ i) (fstˢ v₀)) (inlˢ (sndˢ v₀))) e)
  inputᵏ i coldᵏ   e = endAfterˢ {t = lookup Γ i}
    (mapˢ (pairˢ (tickᵖ (toℕ i) (fstˢ v₀)) (inlˢ (sndˢ v₀))) e)
  inputᵏ i sharedᵏ e = endAfterˢ {t = lookup Γ i} e

  inputᵀ : ∀ {Δᵍ Δ Θ} (i : Fin n) → SExp (timedᶜ Γ κ) Δᵍ Δ Θ (itemᵗ (lookup Γ i))
  inputᵀ {Δᵍ} {Δ} {Θ} i =
    inputᵏ i (lookup κ i) (subst (SExp (timedᶜ Γ κ) Δᵍ Δ Θ) (lookup-zipWith timedTy i Γ κ) (inputˢ i))

  mutual
    τ : ∀ {Δᵍ Δ Θ Θ′ t} → ℕ → Ren Θ Θ′ → SExp Γ Δᵍ Δ Θ t
      → SExp (timedᶜ Γ κ) (map itemᵗ Δᵍ) (map itemᵗ Δ) Θ′ (itemᵗ t)
    τ d ρ (inputˢ i)                  = inputᵀ i
    τ d ρ (ofˢ ts)                    = ofˢ (τof ρ ts)
    τ d ρ emptyˢ                      = ofˢ (pairˢ nilˢ (inrˢ unitˢ) ∷ [])
    -- a `takeWhile` lets an END through, so one never failing the
    -- predicate passes its source's
    τ d ρ (takeWhileˢ {t = t} f e)    =
      endAfterˢ {t = t} (takeWhileˢ (caseˢ (sndˢ v₀) (τᵗ (extᵀ (wkᵀ ρ)) f) (boolˢ true))
                                    (τ (suc d) ρ e))
    τ d ρ (mapˢ f e)                  =
      mapˢ (pairˢ (fstˢ v₀) (caseˢ (sndˢ v₀) (inlˢ (τᵗ (extᵀ (wkᵀ ρ)) f)) (inrˢ unitˢ)))
           (τ (suc d) ρ e)
    -- an END passes with the state untouched; a value's output takes
    -- that value's packet
    τ d ρ (scanˢ f z e)               =
      mapˢ (sndˢ v₀)
        (scanˢ (caseˢ (sndˢ (sndˢ v₀))
                  (letˢ (pairˢ (fstˢ (fstˢ v₁)) v₀)
                    (letˢ (τᵗ (extᵀ (wkᵀ (wkᵀ ρ))) f)
                      (pairˢ v₀ (pairˢ (fstˢ (sndˢ v₃)) (inlˢ v₀)))))
                  (pairˢ (fstˢ (fstˢ v₁)) (pairˢ (fstˢ (sndˢ v₁)) (inrˢ unitˢ))))
               (pairˢ (τᵗ ρ z) (pairˢ nilˢ (inrˢ unitˢ)))
               (τ (suc d) ρ e))
    τ d ρ (flattenˢ {t = t} op e)     = flattenᵀ {t = t} d op (τ (suc d) ρ e)
    τ d ρ (μˢ e)                      = μˢ (τ (suc d) ρ e)
    τ d ρ (varˢ x)                    = varˢ (∈-map⁺ itemᵗ x)
    -- the hop is an instant minted in this frame, and the body a
    -- sub-frame subscribed in it
    τ {Δᵍ = Δᵍ} {Δ = Δ} {Θ′ = Θ′} d ρ (deferˢ {t = t} e) =
      mapˢ (pairˢ (substᵖ (litˢ (d ∷ 0 ∷ [])) (litˢ (2 ∷ 1 ∷ d ∷ 0 ∷ [])) (fstˢ v₀)) (sndˢ v₀))
        (deferˢ (subst (λ ζ → SExp (timedᶜ Γ κ) [] ζ Θ′ (itemᵗ t))
                       (map-++ itemᵗ Δᵍ Δ) (τ (suc d) ρ e)))

    -- each value in its subscriber's instant, then the END there too
    τof : ∀ {Δᵍ Δ Θ Θ′ t} → Ren Θ Θ′ → List (STm Γ Δᵍ Δ Θ t)
        → List (STm (timedᶜ Γ κ) (map itemᵗ Δᵍ) (map itemᵗ Δ) Θ′ (itemᵗ t))
    τof ρ []       = pairˢ nilˢ (inrˢ unitˢ) ∷ []
    τof ρ (x ∷ xs) = pairˢ nilˢ (inlˢ (τᵗ ρ x)) ∷ τof ρ xs

    τᵗ : ∀ {Δᵍ Δ Θ Θ′ t} → Ren Θ Θ′ → STm Γ Δᵍ Δ Θ t
       → STm (timedᶜ Γ κ) (map itemᵗ Δᵍ) (map itemᵗ Δ) Θ′ (timedᵗ t)
    τᵗ ρ (varˢᵗ x)     = varˢᵗ (ρ x)
    τᵗ ρ unitˢ         = unitˢ
    τᵗ ρ (boolˢ b)     = boolˢ b
    τᵗ ρ (natˢ k)      = natˢ k
    τᵗ ρ (pairˢ a b)   = pairˢ (τᵗ ρ a) (τᵗ ρ b)
    τᵗ ρ (fstˢ p)      = fstˢ (τᵗ ρ p)
    τᵗ ρ (sndˢ p)      = sndˢ (τᵗ ρ p)
    τᵗ ρ nilˢ          = nilˢ
    τᵗ ρ (consˢ h t)   = consˢ (τᵗ ρ h) (τᵗ ρ t)
    τᵗ ρ (inlˢ a)      = inlˢ (τᵗ ρ a)
    τᵗ ρ (inrˢ b)      = inrˢ (τᵗ ρ b)
    τᵗ ρ (caseˢ s l r) = caseˢ (τᵗ ρ s) (τᵗ (extᵀ ρ) l) (τᵗ (extᵀ ρ) r)
    τᵗ ρ (foldˢ l z f) = foldˢ (τᵗ ρ l) (τᵗ ρ z) (τᵗ (extᵀ (extᵀ ρ)) f)
    τᵗ ρ (ifˢ c a b)   = ifˢ (τᵗ ρ c) (τᵗ ρ a) (τᵗ ρ b)
    τᵗ ρ (primˢ op a)  = primˢ (timedᵒ op) (τᵗ ρ a)
    τᵗ ρ (strmˢ e)     = strmˢ (τ 0 ρ e)

timed : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t}
      → SExp Γ [] [] [] t → SExp (timedᶜ Γ κ) [] [] [] (itemᵗ t)
timed κ e = τ κ 0 noneᵀ e

------------------------------------------------------------------
-- THE TRANSLATION READS THE INPUTS ITS SOURCE READ, AND NO OTHERS:
-- every term it adds mentions no input, so each guard reduces to its
-- source's, with a trailing `true` at most.
------------------------------------------------------------------

conj² : ∀ a b a′ b′ → (T a → T a′) → (T b → T b′) → T (a ∧ b) → T (a′ ∧ b′)
conj² a b a′ b′ f g p = ∧⁺ a′ b′ (f (∧ˡᵇ a b p)) (g (∧ʳᵇ a b p))

conj³ : ∀ a b c a′ b′ c′ → (T a → T a′) → (T b → T b′) → (T c → T c′)
      → T (a ∧ b ∧ c) → T (a′ ∧ b′ ∧ c′)
conj³ a b c a′ b′ c′ f g h = conj² a (b ∧ c) a′ (b′ ∧ c′) f (conj² b c b′ c′ g h)

conj-true : ∀ a → T a → T (a ∧ true)
conj-true a p = ∧⁺ a true p tt

module _ {n} {Γ : Ctx n} (k : ℕ) where
  ib : ∀ {Δᵍ Δ Θ t} → SExp Γ Δᵍ Δ Θ t → Bool
  ib e = inputsBelowᵉ k (plainExp e)

  ibᵗ : ∀ {Δᵍ Δ Θ t} → STm Γ Δᵍ Δ Θ t → Bool
  ibᵗ m = inputsBelowᵗ k (plainTm m)

  ibᵗˢ : ∀ {Δᵍ Δ Θ t} → List (STm Γ Δᵍ Δ Θ t) → Bool
  ibᵗˢ ms = inputsBelowᵗˢ k (plainTms ms)

  subst-belowᵗ : ∀ {Δᵍ Δ Θ s t} (eq : s ≡ t) (e : SExp Γ Δᵍ Δ Θ s)
               → T (ib e) → T (ib (subst (SExp Γ Δᵍ Δ Θ) eq e))
  subst-belowᵗ refl e p = p

  subst-belowᴰ : ∀ {Δᵍ Δ Δ′ Θ t} (eq : Δ ≡ Δ′) (e : SExp Γ Δᵍ Δ Θ t)
               → T (ib e) → T (ib (subst (λ ζ → SExp Γ Δᵍ ζ Θ t) eq e))
  subst-belowᴰ refl e p = p

module _ {n} {Γ : Ctx n} (κ : Kinds n) (k : ℕ) where
  inputᵏ-below : ∀ {Δᵍ Δ Θ} (i : Fin n) kd (e : SExp (timedᶜ Γ κ) Δᵍ Δ Θ (timedTy (lookup Γ i) kd))
               → T (ib k e) → T (ib k (inputᵏ κ i kd e))
  inputᵏ-below i hotᵏ    e p = conj-true (ib k e) p
  inputᵏ-below i coldᵏ   e p = conj-true (ib k e) p
  inputᵏ-below i sharedᵏ e p = conj-true (ib k e) p

  mutual
    τ-below : ∀ {Δᵍ Δ Θ Θ′ t} d (ρ : Ren Θ Θ′) (e : SExp Γ Δᵍ Δ Θ t)
            → T (ib k e) → T (ib k (τ κ d ρ e))
    τ-below d ρ (inputˢ i) p =
      inputᵏ-below i (lookup κ i) _
        (subst-belowᵗ k (lookup-zipWith timedTy i Γ κ) (inputˢ i) p)
    τ-below d ρ (ofˢ ts) p = τof-below ρ ts p
    τ-below d ρ emptyˢ p = tt
    τ-below d ρ (takeWhileˢ f e) p =
      conj-true ((ibᵗ k f′ ∧ true) ∧ ib k (τ κ (suc d) ρ e))
        (conj² (ibᵗ k f) (ib k e) (ibᵗ k f′ ∧ true) (ib k (τ κ (suc d) ρ e))
           (λ q → conj-true (ibᵗ k f′) (τᵗ-below (extᵀ (wkᵀ ρ)) f q)) (τ-below (suc d) ρ e) p)
      where f′ = τᵗ κ (extᵀ (wkᵀ ρ)) f
    τ-below d ρ (mapˢ f e) p =
      conj² (ibᵗ k f) (ib k e) (ibᵗ k f′ ∧ true) (ib k (τ κ (suc d) ρ e))
         (λ q → conj-true (ibᵗ k f′) (τᵗ-below (extᵀ (wkᵀ ρ)) f q)) (τ-below (suc d) ρ e) p
      where f′ = τᵗ κ (extᵀ (wkᵀ ρ)) f
    τ-below d ρ (scanˢ f z e) p =
      conj³ (ibᵗ k f) (ibᵗ k z) (ib k e)
         (((ibᵗ k f′ ∧ true) ∧ true) ∧ true) (ibᵗ k (τᵗ κ ρ z) ∧ true) (ib k (τ κ (suc d) ρ e))
         (λ q → conj-true ((ibᵗ k f′ ∧ true) ∧ true) (conj-true (ibᵗ k f′ ∧ true)
                  (conj-true (ibᵗ k f′) (τᵗ-below (extᵀ (wkᵀ (wkᵀ ρ))) f q))))
         (λ q → conj-true (ibᵗ k (τᵗ κ ρ z)) (τᵗ-below ρ z q))
         (τ-below (suc d) ρ e) p
      where f′ = τᵗ κ (extᵀ (wkᵀ (wkᵀ ρ))) f
    τ-below d ρ (flattenˢ op e) p = conj-true (ib k (τ κ (suc d) ρ e)) (τ-below (suc d) ρ e p)
    τ-below d ρ (μˢ e) p = τ-below (suc d) ρ e p
    τ-below d ρ (varˢ x) p = tt
    τ-below {Δᵍ = Δᵍ} {Δ = Δ} d ρ (deferˢ e) p =
      subst-belowᴰ k (map-++ itemᵗ Δᵍ Δ) (τ κ (suc d) ρ e) (τ-below (suc d) ρ e p)

    τof-below : ∀ {Δᵍ Δ Θ Θ′ t} (ρ : Ren Θ Θ′) (ts : List (STm Γ Δᵍ Δ Θ t))
              → T (ibᵗˢ k ts) → T (ibᵗˢ k (τof κ ρ ts))
    τof-below ρ []       p = tt
    τof-below ρ (x ∷ xs) p =
      conj² (ibᵗ k x) (ibᵗˢ k xs) (ibᵗ k (τᵗ κ ρ x)) (ibᵗˢ k (τof κ ρ xs))
         (τᵗ-below ρ x) (τof-below ρ xs) p

    τᵗ-below : ∀ {Δᵍ Δ Θ Θ′ t} (ρ : Ren Θ Θ′) (m : STm Γ Δᵍ Δ Θ t)
             → T (ibᵗ k m) → T (ibᵗ k (τᵗ κ ρ m))
    τᵗ-below ρ (varˢᵗ x)     p = tt
    τᵗ-below ρ unitˢ         p = tt
    τᵗ-below ρ (boolˢ b)     p = tt
    τᵗ-below ρ (natˢ j)      p = tt
    τᵗ-below ρ (pairˢ a b)   p =
      conj² (ibᵗ k a) (ibᵗ k b) (ibᵗ k (τᵗ κ ρ a)) (ibᵗ k (τᵗ κ ρ b))
         (τᵗ-below ρ a) (τᵗ-below ρ b) p
    τᵗ-below ρ (fstˢ a)      p = τᵗ-below ρ a p
    τᵗ-below ρ (sndˢ a)      p = τᵗ-below ρ a p
    τᵗ-below ρ nilˢ          p = tt
    τᵗ-below ρ (consˢ a b)   p =
      conj² (ibᵗ k a) (ibᵗ k b) (ibᵗ k (τᵗ κ ρ a)) (ibᵗ k (τᵗ κ ρ b))
         (τᵗ-below ρ a) (τᵗ-below ρ b) p
    τᵗ-below ρ (inlˢ a)      p = τᵗ-below ρ a p
    τᵗ-below ρ (inrˢ a)      p = τᵗ-below ρ a p
    τᵗ-below ρ (caseˢ s l r) p =
      conj³ (ibᵗ k s) (ibᵗ k l) (ibᵗ k r)
         (ibᵗ k (τᵗ κ ρ s)) (ibᵗ k (τᵗ κ (extᵀ ρ) l)) (ibᵗ k (τᵗ κ (extᵀ ρ) r))
         (τᵗ-below ρ s) (τᵗ-below (extᵀ ρ) l) (τᵗ-below (extᵀ ρ) r) p
    τᵗ-below ρ (foldˢ l z f) p =
      conj³ (ibᵗ k l) (ibᵗ k z) (ibᵗ k f)
         (ibᵗ k (τᵗ κ ρ l)) (ibᵗ k (τᵗ κ ρ z)) (ibᵗ k (τᵗ κ (extᵀ (extᵀ ρ)) f))
         (τᵗ-below ρ l) (τᵗ-below ρ z) (τᵗ-below (extᵀ (extᵀ ρ)) f) p
    τᵗ-below ρ (ifˢ c a b)   p =
      conj³ (ibᵗ k c) (ibᵗ k a) (ibᵗ k b)
         (ibᵗ k (τᵗ κ ρ c)) (ibᵗ k (τᵗ κ ρ a)) (ibᵗ k (τᵗ κ ρ b))
         (τᵗ-below ρ c) (τᵗ-below ρ a) (τᵗ-below ρ b) p
    τᵗ-below ρ (primˢ op a)  p = τᵗ-below ρ a p
    τᵗ-below ρ (strmˢ e)     p = τ-below 0 ρ e p

timed-below : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t} (k : ℕ) (d : SExp Γ [] [] [] t)
            → T (inputsBelowᵉ k (plainExp d))
            → T (inputsBelowᵉ k (plainExp (timed κ d)))
timed-below κ k d = τ-below κ k 0 noneᵀ d

------------------------------------------------------------------
-- The slot table, translated.
------------------------------------------------------------------

-- a data value is its own translation
timedᵈ : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} t → T (isData (plainᵗ t))
       → Val Γ (plainᵗ t) → Val Γ′ (plainᵗ (timedᵗ t))
timedᵈ unitᵗ     ok v        = v
timedᵈ boolᵗ     ok v        = v
timedᵈ natᵗ      ok v        = v
timedᵈ uniqᵗ     ok v        = v
timedᵈ (s ×ᵗ t)  ok (a , b)  =
  timedᵈ s (∧ˡ (isData (plainᵗ s)) ok) a , timedᵈ t (∧ʳ (isData (plainᵗ s)) ok) b
timedᵈ (s +ᵗ t)  ok (inj₁ a) = inj₁ (timedᵈ s (∧ˡ (isData (plainᵗ s)) ok) a)
timedᵈ (s +ᵗ t)  ok (inj₂ b) = inj₂ (timedᵈ t (∧ʳ (isData (plainᵗ s)) ok) b)
timedᵈ (listᵗ t) ok vs       = map (timedᵈ t ok) vs
timedᵈ (obs t)   () _

timedᵈ-ok : ∀ t → T (isData (plainᵗ t)) → T (isData (plainᵗ (timedᵗ t)))
timedᵈ-ok unitᵗ     ok = ok
timedᵈ-ok boolᵗ     ok = ok
timedᵈ-ok natᵗ      ok = ok
timedᵈ-ok uniqᵗ     ok = ok
timedᵈ-ok (s ×ᵗ t)  ok =
  ∧-intro (isData (plainᵗ (timedᵗ s))) (timedᵈ-ok s (∧ˡ (isData (plainᵗ s)) ok))
                                       (timedᵈ-ok t (∧ʳ (isData (plainᵗ s)) ok))
timedᵈ-ok (s +ᵗ t)  ok =
  ∧-intro (isData (plainᵗ (timedᵗ s))) (timedᵈ-ok s (∧ˡ (isData (plainᵗ s)) ok))
                                       (timedᵈ-ok t (∧ʳ (isData (plainᵗ s)) ok))
timedᵈ-ok (listᵗ t) ok = timedᵈ-ok t ok
timedᵈ-ok (obs t)   ()

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

-- a script's two halves, read back off a tagged one
syncOf : ∀ {A : Set} → ObservableInput A → List A
syncOf (hot _)     = []
syncOf (cold ss _) = ss

asyncOf : ∀ {A : Set} → ObservableInput A → List (Timed A)
asyncOf (hot as)    = as
asyncOf (cold _ as) = as

-- shared slot j's program, its relative names closed
closeShareˢ : ∀ {n} {Γ : Ctx n} {t} → ℕ → SExp Γ [] [] [] (itemᵗ t) → SExp Γ [] [] [] (itemᵗ t)
closeShareˢ j e = mapˢ (pairˢ (closeᵖ j (fstˢ v₀)) (sndˢ v₀)) e

timedSlots : ∀ {n} {Γ : Ctx n} {κ : Kinds n} → SimulSlots Γ κ → SimulSlots (timedᶜ Γ κ) κ
timedSlots {Γ = Γ} {κ = κ} ins i =
  subst (λ τ → SimulSlot (timedᶜ Γ κ) κ (toℕ i) τ (lookup κ i))
        (sym (lookup-zipWith timedTy i Γ κ))
        (go (lookup κ i) (ins i))
  where
    go : ∀ kd → SimulSlot Γ κ (toℕ i) (lookup Γ i) kd
       → SimulSlot (timedᶜ Γ κ) κ (toℕ i) (timedTy (lookup Γ i) kd) kd
    go hotᵏ    (hotˢ {ok = ok} as) =
      hotˢ {ok = timedᵈ-ok (lookup Γ i) ok}
           (asyncOf (tickInput (mapInput (timedᵈ (lookup Γ i) ok) (hot as))))
    go coldᵏ   (coldˢ {ok = ok} ss as) =
      coldˢ {ok = timedᵈ-ok (lookup Γ i) ok}
            (syncOf (tickInput (mapInput (timedᵈ (lookup Γ i) ok) (cold ss as))))
            (asyncOf (tickInput (mapInput (timedᵈ (lookup Γ i) ok) (cold ss as))))
    go sharedᵏ   (sharedˢ d {ok = ok})     =
      sharedˢ (closeShareˢ (toℕ i) (timed κ d)) {ok = timed-below κ (toℕ i) d ok}

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
