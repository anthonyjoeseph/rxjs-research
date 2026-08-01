------------------------------------------------------------------
-- THE CHAIN-HALF LEMMA IS FALSE AT A FIXED C.  Refuted 2026-08-01, by
-- computation on a five-node program.
--
-- The statement was `regsSz?-subscribeE`: from a registry bounded by C,
-- subscribing an expression of size ≤ C under a continuation κ whose
-- own frames are bounded (`pathSz? C κ`) and which has room to grow by
-- one (`suc (pathLen κ) ≤ C`), the registry stays bounded by C.
--
-- IT DOES NOT, AND THE REASON IS THAT C CANNOT PAY FOR THE DESCENT.
-- `subscribeE` pushes ONE FRAME PER SHELL of the expression it walks —
-- `mapᵉ f b` recurses on `b` at `map-f f ↠ κ` — so what is registered
-- at the leaf is κ lengthened by the expression's shell count.  The
-- hypothesis gives κ room for exactly ONE more frame; two shells
-- overrun it.
--
-- Below: C = 5, a κ of four `map-f` frames (`pathSz? 5 κ` and
-- `suc (pathLen κ) = 5 ≤ 5`, both tight), and `mapᵉ f (mapᵉ f (input
-- 0))`, whose sizeᵉ is exactly 5.  Every hypothesis holds.  The
-- registry that comes back holds a chain of length six, and
-- `regsSz? 5` of it is FALSE.
--
-- THE CONTRAST, and it is what makes this a defect of THIS statement
-- rather than of the descent: `subscribeE-caps` carries the very same
-- two hypotheses and is GROUND, because it does not report at a fixed
-- cap — it reports at `frameStep (j + j′) c`, and one j at least
-- doubles cSize (frameStep-size-suc), so each pushed frame is paid for
-- by the j that pushes it.  A statement with no j has nothing to pay
-- with.
--
-- AND THE LEMMA WAS REDUNDANT ANYWAY.  `capsOK?` has `regsSz?` as its
-- second conjunct, so the ground `subscribeE-caps` already hands the
-- chain half back at the reported level.  The postulate had no
-- consumer.  It is gone; this file is why.
--
-- Standalone (one hand-built configuration), so src/Main.agda never
-- reaches it.
------------------------------------------------------------------
module Chain-Half-Probe where

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_)
open import Data.Nat     using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Fin     using (Fin) renaming (zero to fz)
open import Data.Vec     using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
open import Rx.Prim
open import Rx.Evaluator
open import Verify-Budget-Sufficient using (regsSz?; pathSz?; pathLen)

Γ : Ctx 1
Γ = natᵗ ∷ᵛ []ᵛ

-- one HOT scripted slot, so the `input` clause registers rather than
-- connecting or one-shotting.  Its script is empty: nothing here reads
-- an arrival, only the REGISTRATION the subscribe leaves behind
ins : Slots Γ
ins fz = scripted (hot [])

idf : Fn Γ [] [] [] natᵗ natᵗ
idf = varᵗ (here refl)

-- THE PROGRAM.  Any closed expression will do — it only indexes the
-- store — so it is the same shape as `b`
prog : Closed Γ natᵗ
prog = mapᵉ idf (input fz)

-- THE CONTINUATION: four frames, so `pathLen κ` is 4 and the
-- hypothesis `suc (pathLen κ) ≤ 5` is TIGHT
κ : Path Γ natᵗ natᵗ
κ = map-f idf ↠ (map-f idf ↠ (map-f idf ↠ (map-f idf ↠ root)))

_ : pathLen κ ≡ 4
_ = refl

-- THE SUBSCRIBED EXPRESSION: two shells over the slot, sizeᵉ exactly 5
b : Closed Γ natᵗ
b = mapᵉ idf (mapᵉ idf (input fz))

_ : sizeᵉ b ≡ 5
_ = refl

C : ℕ
C = 5

sched₀ : Sched Γ
sched₀ = sched-init prog ins

st₀ : EvalSt prog
st₀ = st-init prog

------------------------------------------------------------------
-- EVERY HYPOTHESIS, CHECKED
------------------------------------------------------------------

hyp-registry : regsSz? C (EvalSt.registry st₀) ≡ true
hyp-registry = refl

hyp-size : sizeᵉ b ≤ C
hyp-size = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

hyp-path : pathSz? C κ ≡ true
hyp-path = refl

hyp-room : suc (pathLen κ) ≤ C
hyp-room = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

------------------------------------------------------------------
-- AND THE CONCLUSION, FALSE
------------------------------------------------------------------

result : Stream Γ natᵗ × Sched Γ × EvalSt prog
result = subscribeE g0 b κ 0 0 sched₀ st₀

-- the chain that was registered: κ with the two walked shells on top
regd : List (RegId × Source × Chain Γ natᵗ)
regd = EvalSt.registry (proj₂ (proj₂ result))

_ : regd ≡ (0 , 0 , (natᵗ , map-f idf ↠ (map-f idf ↠ κ))) ∷ []
_ = refl

-- six frames where the cap allows five
_ : pathLen (map-f idf ↠ (map-f idf ↠ κ)) ≡ 6
_ = refl

chain-half-refuted : regsSz? C regd ≡ false
chain-half-refuted = refl

-- ONE SHELL IS ALREADY THE WHOLE MARGIN, and the margin is what the
-- hypothesis gives: subscribing a single-shell expression under the
-- same κ lands exactly on the cap and stays true.  So the failure is
-- not a slack constant — it is one frame per shell against a fixed
-- allowance of one
b₁ : Closed Γ natᵗ
b₁ = mapᵉ idf (input fz)

_ : regsSz? C (EvalSt.registry (proj₂ (proj₂ (subscribeE g0 b₁ κ 0 0 sched₀ st₀))))
      ≡ true
_ = refl
