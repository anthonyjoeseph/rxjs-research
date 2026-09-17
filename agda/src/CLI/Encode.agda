-- Encode an evaluated Stream (List (InstEmit (Val Γ t))) as JSON matching
-- the TS InstEmit shape. Values are encoded by recursion on the root type
-- t; ids (instant/source, both ℕ) print as numbers — the TS side compares
-- streams up to id renaming, so the exact numerals do not matter.
module CLI.Encode where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)

open import Rx.Prim using (InstEvent; init; value; close; handoff; complete; CloseReason; cut; cutPending; exhausted;
  EmitKind; subscribe; delivery; plumbing; InstEmit; _at_from_as_)
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

private
  encKind : EmitKind → String
  encKind subscribe = quote′ "subscribe"
  encKind delivery  = quote′ "delivery"
  encKind plumbing  = quote′ "plumbing"

  encReason : CloseReason → String
  encReason cut        = quote′ "cut"
  encReason cutPending = quote′ "cutPending"
  encReason exhausted  = quote′ "exhausted"

  encEvent : ∀ {n} {Γ : Ctx n} (t : Ty) → InstEvent (Val Γ t) → String
  encEvent t (init s)     = "{" ++ field′ "type" (quote′ "init") ++ "," ++ field′ "source" (show s) ++ "}"
  encEvent t (value v)    = "{" ++ field′ "type" (quote′ "value") ++ "," ++ field′ "value" (encodeVal t v) ++ "}"
  encEvent t (close s r)  = "{" ++ field′ "type" (quote′ "close") ++ "," ++ field′ "source" (show s) ++ "," ++ field′ "reason" (encReason r) ++ "}"
  encEvent t (handoff s)  = "{" ++ field′ "type" (quote′ "handoff") ++ "," ++ field′ "source" (show s) ++ "}"
  encEvent t complete     = "{" ++ field′ "type" (quote′ "complete") ++ "}"

  encEmit : ∀ {n} {Γ : Ctx n} (t : Ty) → InstEmit (Val Γ t) → String
  encEmit t (es at i from s as k) =
    "{" ++ field′ "events" (arr (mapEvents es))
        ++ "," ++ field′ "instant" (show i)
        ++ "," ++ field′ "source" (show s)
        ++ "," ++ field′ "kind" (encKind k) ++ "}"
    where
      mapEvents : List (InstEvent (Val _ t)) → List String
      mapEvents []       = []
      mapEvents (e ∷ es) = encEvent t e ∷ mapEvents es

encodeStream : ∀ {n} {Γ : Ctx n} (t : Ty) → List (InstEmit (Val Γ t)) → String
encodeStream t ems = arr (go ems)
  where
    go : List (InstEmit (Val _ t)) → List String
    go []       = []
    go (e ∷ es) = encEmit t e ∷ go es
