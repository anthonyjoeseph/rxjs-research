{-# OPTIONS --guardedness #-}

-- THE ORACLE'S AGDA HALF: the generated programs, and what the three
-- semantics make of them, as JSON lines for `typescript/` to replay in
-- rxjs.  Same seeds, unfolding budget and step budget as `Quickcheck`.
--
--   Oracle-CLI prog FROM COUNT   one line per seed: the program, the
--                                denotation's trace and the pure
--                                semantics'
--   Oracle-CLI io SEED           the IO engine's trace of one seed
--   Oracle-CLI named FROM COUNT  as `prog`, over the seed's named program
--                                (`quickcheck.Quickcheck.named`)
--   Oracle-CLI named-code SEED   that program
--   Oracle-CLI named-io SEED     the IO engine's trace of it
--   Oracle-CLI denote SEED       the denotation's trace of one seed, its
--                                emission set listed
--   Oracle-CLI pure SEED         the pure semantics' trace of one seed
--   Oracle-CLI table SEED        the enumerator's listing of one seed
--   Oracle-CLI table-trace SEED  its walk node by node, unbuffered, which
--                                a timeout does not swallow
--   Oracle-CLI hand              `quickcheck.Quickcheck.prop` over
--                                `quickcheck.Adversary`
--
-- The IO engine runs one seed per process because a program that never
-- finishes never returns: the caller's timeout is the only way out.
module quickcheck.Oracle-CLI where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; upTo) renaming (map to mapL)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show using (readMaybe) renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
open import IO.Primitive.Core using (pure; _>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import System.Environment.Primitive using (getArgs)

open import quickcheck.Ty using (Ty; natᵗ; nameᵗ; _×ᵗ_)
open import quickcheck.Code using (Prog; showCode)
open import quickcheck.Trace using (showTrace)
open import quickcheck.Oracle using (denoteTrace; pureTrace; oracle; ioOp)
open import quickcheck.Quickcheck using (prop; program; named)
open import quickcheck.Adversary using (cases)
open import quickcheck.Tabled using (tableJSON; tableTrace)

open import IO.Primitive.Handle using (hSetBuffering; stdout; noBuffering)

private
  -- Unbuffered, so what a killed run printed survives it.
  eachLine : List String → IO ⊤
  eachLine xs = hSetBuffering stdout noBuffering >>= λ _ → go xs
    where
    go : List String → IO ⊤
    go []       = pure _
    go (x ∷ xs) = putStrLn x >>= λ _ → go xs

  each : List ℕ → (ℕ → IO ⊤) → IO ⊤
  each []       f = pure _
  each (x ∷ xs) f = f x >>= λ _ → each xs f

  prog : ℕ → IO ⊤
  prog s = putStrLn ("{\"seed\":" ++ showℕ s ++ ",\"prog\":" ++ showCode natᵗ (program s)
                     ++ ",\"denote\":" ++ showTrace natᵗ (denoteTrace 3 (program s))
                     ++ ",\"pure\":" ++ showTrace natᵗ (pureTrace 3 500 (program s))
                     ++ ",\"table\":" ++ tableJSON 3 (program s) ++ "}")

  io : ℕ → IO ⊤
  io s = oracle ioOp 3 500 (program s)

  namedᵗ : Ty
  namedᵗ = natᵗ ×ᵗ nameᵗ

  namedProg : ℕ → IO ⊤
  namedProg s = putStrLn ("{\"seed\":" ++ showℕ s ++ ",\"prog\":" ++ showCode namedᵗ (named s)
                          ++ ",\"denote\":" ++ showTrace namedᵗ (denoteTrace 3 (named s))
                          ++ ",\"pure\":" ++ showTrace namedᵗ (pureTrace 3 500 (named s))
                          ++ ",\"table\":" ++ tableJSON 3 (named s) ++ "}")

  hand : List (String × Prog natᵗ) → IO ⊤
  hand []             = putStrLn "hand: done"
  hand ((l , p) ∷ cs) = putStrLn ((if prop natᵗ p then "hand: ok   " else "hand: FAIL ") ++ l) >>= λ _ → hand cs

  nat : String → Maybe ℕ
  nat = readMaybe 10

  usage : IO ⊤
  usage = putStrLn "usage: Oracle-CLI prog FROM COUNT | Oracle-CLI code SEED | Oracle-CLI named FROM COUNT | Oracle-CLI named-code SEED | Oracle-CLI named-io SEED | Oracle-CLI denote SEED | Oracle-CLI pure SEED | Oracle-CLI table SEED | Oracle-CLI table-trace SEED | Oracle-CLI io SEED | Oracle-CLI hand"

  dispatch : List String → IO ⊤
  dispatch ("prog" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (mapL (f′ +_) (upTo c′)) prog
  ... | _       | _       = usage
  dispatch ("named" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (mapL (f′ +_) (upTo c′)) namedProg
  ... | _       | _       = usage
  dispatch ("named-code" ∷ s ∷ []) with nat s
  ... | just s′ = putStrLn (showCode namedᵗ (named s′))
  ... | nothing = usage
  dispatch ("named-io" ∷ s ∷ []) with nat s
  ... | just s′ = oracle ioOp 3 500 (named s′)
  ... | nothing = usage
  dispatch ("code" ∷ s ∷ []) with nat s
  ... | just s′ = putStrLn (showCode natᵗ (program s′))
  ... | nothing = usage
  dispatch ("denote" ∷ s ∷ []) with nat s
  ... | just s′ = putStrLn (showTrace natᵗ (denoteTrace 3 (program s′)))
  ... | nothing = usage
  dispatch ("pure" ∷ s ∷ []) with nat s
  ... | just s′ = putStrLn (showTrace natᵗ (pureTrace 3 500 (program s′)))
  ... | nothing = usage
  dispatch ("table" ∷ s ∷ []) with nat s
  ... | just s′ = putStrLn (tableJSON 3 (program s′))
  ... | nothing = usage
  dispatch ("table-trace" ∷ s ∷ []) with nat s
  ... | just s′ = eachLine (tableTrace 3 (program s′))
  ... | nothing = usage
  dispatch ("io" ∷ s ∷ []) with nat s
  ... | just s′ = io s′
  ... | nothing = usage
  dispatch ("hand" ∷ []) = hand cases
  dispatch _ = usage

main : IO ⊤
main = getArgs >>= dispatch
