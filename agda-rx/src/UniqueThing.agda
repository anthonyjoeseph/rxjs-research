{-# OPTIONS --safe #-}

-- The trick: instead of a postulate (banned under --safe), each expansion mints a fresh top-level definition via declareDef/defineFun. 
-- This is allowed under --safe because it's a genuine total function, not an axiom — and embeds that function's Name as the token. 
-- The payload (0) is irrelevant; the name identity is what carries uniqueness, and primQNameEquality compares exactly that.

module SafeUnique where
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

record UniqueThing (A : Set) : Set where
  constructor mkUnique
  field
    uniqueSymbol : Name       -- reflected name = the identity token
    value        : A
open UniqueThing

vis : {A : Set} -> A -> Arg A
vis x = arg (arg-info visible (modality relevant quantity-ω)) x

infixl 1 _>>=_ _>>_
_>>=_ : {A B : Set} -> TC A -> (A -> TC B) -> TC B
_>>=_ = bindTC
_>>_  : {A B : Set} -> TC A -> TC B -> TC B
m >> n = bindTC m (\ _ -> n)

macro
  unique : {A : Set} -> A -> Term -> TC ⊤
  unique {A} v hole =
    freshName "sym" >>= \ n ->
    declareDef (vis n) (def (quote Nat) []) >>          -- a REAL def, not a postulate
    defineFun n (clause [] [] (lit (nat 0)) ∷ []) >>    -- (payload is irrelevant; identity is the Name)
    quoteTC v >>= \ v' ->
    unify hole (con (quote mkUnique) (vis (lit (name n)) ∷ vis v' ∷ []))

sameName : {A B : Set} -> UniqueThing A -> UniqueThing B -> Bool
sameName x y = primQNameEquality (uniqueSymbol x) (uniqueSymbol y)