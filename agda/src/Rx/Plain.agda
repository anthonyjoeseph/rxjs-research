------------------------------------------------------------------
-- THE AUTHOR'S PROGRAM AS PLAIN RXJS: every simul former read as the
-- same-named `Exp` former, over the same contexts and at the same
-- type.  No envelope, no instant, no mint -- this is what the program
-- means before anything is batched, and `plain-agrees` holds the
-- impl's elaboration to it value for value, arrival by arrival.
--
-- IT IS AN IDENTITY MAP BECAUSE THE TWO GRAMMARS ARE ONE GRAMMAR.
-- `Rx.SExp` is `Rx.Exp` minus the two formers only an elaboration
-- writes (`batchSyncᵉ`, `mintᵉ`), so no clause below has a choice to
-- make, and a clause that did would be a second semantics.
--
-- A SHARED SLOT HOLDS AN AUTHOR'S PROGRAM TOO, so the table is read
-- the same way: a script stays a script, a share is its definition
-- read plain.  A script's payloads are typed in the elaboration's
-- context, where the slot stands at `plainᵗ` of the author's type;
-- a script is data, and a data value is the same value in every
-- context, which `unplainᵈ` says without inspecting anything.
------------------------------------------------------------------
module Rx.Plain where

open import Data.Bool    using (T; true; false; if_then_else_)
open import Data.List    using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)

open import Rx.Prim  using (ObservableInput; hot; cold; after_,_; PlainEvent; valueᵖ; completeᵖ)
open import Rx.Exp   using (unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Val; isData; Exp; Tm; input; ofᵉ;
  emptyᵉ; takeᵉ; mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ;
  unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ; foldᵗ; ifᵗ; primᵗ;
  strmᵗ)
open import Rx.SExp  using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ; mergeAllˢ; switchAllˢ; exhaustAllˢ; μˢ;
  varˢ; deferˢ; varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ; caseˢ;
  foldˢ; ifˢ; primˢ; strmˢ; plainᵗ)

mutual
  plainExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → SExp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ t
  plainExp (inputˢ i)      = input i
  plainExp (ofˢ ts)        = ofᵉ (plainTms ts)
  plainExp emptyˢ          = emptyᵉ
  plainExp (takeˢ k e)     = takeᵉ (plainTm k) (plainExp e)
  plainExp (mapˢ f e)      = mapᵉ (plainTm f) (plainExp e)
  plainExp (scanˢ f z e)   = scanᵉ (plainTm f) (plainTm z) (plainExp e)
  plainExp (mergeAllˢ k e) = mergeAllᵉ k (plainExp e)
  plainExp (switchAllˢ e)  = switchAllᵉ (plainExp e)
  plainExp (exhaustAllˢ e) = exhaustAllᵉ (plainExp e)
  plainExp (μˢ e)          = μᵉ (plainExp e)
  plainExp (varˢ x)        = varᵉ x
  plainExp (deferˢ e)      = deferᵉ (plainExp e)

  plainTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → STm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ t
  plainTm (varˢᵗ x)     = varᵗ x
  plainTm unitˢ         = unit̂
  plainTm (boolˢ b)     = bool̂ b
  plainTm (natˢ k)      = nat̂ k
  plainTm (pairˢ a b)   = pairᵗ (plainTm a) (plainTm b)
  plainTm (fstˢ p)      = fstᵗ (plainTm p)
  plainTm (sndˢ p)      = sndᵗ (plainTm p)
  plainTm nilˢ          = nilᵗ
  plainTm (consˢ h t)   = consᵗ (plainTm h) (plainTm t)
  plainTm (inlˢ a)      = inlᵗ (plainTm a)
  plainTm (inrˢ b)      = inrᵗ (plainTm b)
  plainTm (caseˢ s l r) = caseᵗ (plainTm s) (plainTm l) (plainTm r)
  plainTm (foldˢ l z f) = foldᵗ (plainTm l) (plainTm z) (plainTm f)
  plainTm (ifˢ c a b)   = ifᵗ (plainTm c) (plainTm a) (plainTm b)
  plainTm (primˢ p a)   = primᵗ p (plainTm a)
  plainTm (strmˢ e)     = strmᵗ (plainExp e)

  plainTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (STm Γ Δᵍ Δ Θ t) → List (Tm Γ Δᵍ Δ Θ t)
  plainTms []       = []
  plainTms (m ∷ ms) = plainTm m ∷ plainTms ms

------------------------------------------------------------------
-- A data value does not depend on its context, and `plainᵗ` is the
-- identity on data.
------------------------------------------------------------------

∧ˡ : ∀ b {c} → T (if b then c else false) → T b
∧ˡ true _ = tt

∧ʳ : ∀ b {c} → T (if b then c else false) → T c
∧ʳ true p = p

∧-intro : ∀ b {c} → T b → T c → T (if b then c else false)
∧-intro true _ q = q

isData-unplain : ∀ t → T (isData (plainᵗ t)) → T (isData t)
isData-unplain unitᵗ     ok = tt
isData-unplain boolᵗ     ok = tt
isData-unplain natᵗ      ok = tt
isData-unplain uniqᵗ     ok = tt
isData-unplain (s ×ᵗ t)  ok =
  ∧-intro (isData s) (isData-unplain s (∧ˡ (isData (plainᵗ s)) ok))
                     (isData-unplain t (∧ʳ (isData (plainᵗ s)) ok))
isData-unplain (s +ᵗ t)  ok =
  ∧-intro (isData s) (isData-unplain s (∧ˡ (isData (plainᵗ s)) ok))
                     (isData-unplain t (∧ʳ (isData (plainᵗ s)) ok))
isData-unplain (listᵗ t) ok = isData-unplain t ok
isData-unplain (obs t)   ()

unplainᵈ : ∀ {n m} {Γ : Ctx n} {Γ′ : Ctx m} t → T (isData t)
         → Val Γ′ (plainᵗ t) → Val Γ t
unplainᵈ unitᵗ     ok v        = v
unplainᵈ boolᵗ     ok v        = v
unplainᵈ natᵗ      ok v        = v
unplainᵈ uniqᵗ     ok v        = v
unplainᵈ (s ×ᵗ t)  ok (a , b)  =
  unplainᵈ s (∧ˡ (isData s) ok) a , unplainᵈ t (∧ʳ (isData s) ok) b
unplainᵈ (s +ᵗ t)  ok (inj₁ a) = inj₁ (unplainᵈ s (∧ˡ (isData s) ok) a)
unplainᵈ (s +ᵗ t)  ok (inj₂ b) = inj₂ (unplainᵈ t (∧ʳ (isData s) ok) b)
unplainᵈ (listᵗ t) ok vs       = map (unplainᵈ t ok) vs
unplainᵈ (obs t)   () _

mapInput : ∀ {A B : Set} → (A → B) → ObservableInput A → ObservableInput B
mapInput f (hot as)     = hot (map (λ { (after w , v) → after w , f v }) as)
mapInput f (cold ss as) = cold (map f ss) (map (λ { (after w , v) → after w , f v }) as)

-- WHAT A SUBSCRIBER SEES of a plain run: its values.  The stream's end
-- marker is the machine's business and carries none.
plainValues : ∀ {A : Set} → List (PlainEvent A) → List A
plainValues []                = []
plainValues (valueᵖ v ∷ evs)  = v ∷ plainValues evs
plainValues (completeᵖ ∷ evs) = plainValues evs
