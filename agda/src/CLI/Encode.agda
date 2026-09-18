-- Encode an evaluated run's VALUES as JSON: the `value` payloads in
-- stream order, encoded by recursion on the root type t.
--
-- THE ENVELOPE IS PROJECTED AWAY HERE AND THAT IS THE POINT (Anthony:
-- the oracle wants "nothing involving InstEmit at all").  What the
-- comparison is about is whether this tree run as ORDINARY rxjs emits
-- what the Agda evaluator emits, so the ids, the kinds, the
-- registrations and the instants are all this evaluator's own
-- bookkeeping rather than anything a plain pipeline has — and a
-- comparison carrying them tests the protocol layer instead of the
-- tree.  The projection is a stand-in: the evaluator that produces
-- values WITHOUT minting an envelope is a tier-1 leg of its own, and it
-- is what retires this walk.
module CLI.Encode where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ˡ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)

open import Rx.Prim using (InstEvent; value; InstEmit; _at_from_as_)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ; Val; Ctx)

private
  quote′ : String → String
  quote′ s = "\"" ++ s ++ "\""

  field′ : String → String → String
  field′ k v = quote′ k ++ ":" ++ v

  commaJoin : List String → String
  commaJoin []           = ""
  commaJoin (s ∷ [])     = s
  commaJoin (s ∷ t ∷ ss) = s ++ "," ++ commaJoin (t ∷ ss)

  arr : List String → String
  arr ss = "[" ++ commaJoin ss ++ "]"

encodeVal : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → String
encodeVal unitᵗ    _        = "null"
encodeVal boolᵗ    false    = "false"
encodeVal boolᵗ    true     = "true"
encodeVal natᵗ     n        = show n
encodeVal uniqᵗ    n        = show n
encodeVal (s ×ᵗ t) (a , b)  = arr (encodeVal s a ∷ encodeVal t b ∷ [])
encodeVal (s +ᵗ t) (inj₁ a) = "{" ++ field′ "type" (quote′ "inl") ++ "," ++ field′ "val" (encodeVal s a) ++ "}"
encodeVal (s +ᵗ t) (inj₂ b) = "{" ++ field′ "type" (quote′ "inr") ++ "," ++ field′ "val" (encodeVal t b) ++ "}"
encodeVal (listᵗ t) xs     = arr (map (encodeVal t) xs)
encodeVal (obs t)  _        = "null"   -- obs-valued streams don't occur at a first-order root

encodeValues : ∀ {n} {Γ : Ctx n} (t : Ty) → List (InstEmit (Val Γ t)) → String
encodeValues t ems = arr (go ems)
  where
    evs : List (InstEvent (Val _ t)) → List String
    evs []             = []
    evs (value v ∷ es) = encodeVal t v ∷ evs es
    evs (_       ∷ es) = evs es

    go : List (InstEmit (Val _ t)) → List String
    go []                             = []
    go ((es at _ from _ as _) ∷ rest) = evs es ++ˡ go rest
