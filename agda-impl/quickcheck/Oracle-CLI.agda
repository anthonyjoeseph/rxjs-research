{-# OPTIONS --guardedness #-}

-- THE ORACLE'S AGDA HALF: the generated programs, and what the three
-- engines make of them, as JSON lines for `typescript/` to replay in
-- rxjs.  Same seeds, unfolding budget and step budget as `Quickcheck`.
--
--   Oracle-CLI prog FROM COUNT   one line per seed: the program, the
--                                denotation's trace and the machine's
--   Oracle-CLI io SEED           the IO engine's trace of one seed
--   Oracle-CLI chain FROM COUNT  the seeds whose denotation's approximants
--                                are no chain (`quickcheck.Chain`)
--   Oracle-CLI leaves FROM COUNT the seeds where an operator reads past
--                                its inputs' agreement (`quickcheck.Leaves`)
--   Oracle-CLI hand              the QuickCheck property over
--                                `quickcheck.Adversary`'s programs
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

open import quickcheck.Ty using (natᵗ)
open import quickcheck.Code using (Prog; showCode)
open import quickcheck.Oracle using (showTrace; denoteTrace; pureTrace; oracle; ioOp)
open import quickcheck.Quickcheck using (program; prop)
open import quickcheck.Chain using (chainFails)
open import quickcheck.Leaves using (leavesFails)
open import quickcheck.Adversary using (cases)

private
  each : List ℕ → (ℕ → IO ⊤) → IO ⊤
  each []       f = pure _
  each (x ∷ xs) f = f x >>= λ _ → each xs f

  prog : ℕ → IO ⊤
  prog s = putStrLn ("{\"seed\":" ++ showℕ s ++ ",\"prog\":" ++ showCode natᵗ (program s)
                     ++ ",\"denote\":" ++ showTrace natᵗ (denoteTrace 3 500 (program s))
                     ++ ",\"pure\":" ++ showTrace natᵗ (pureTrace 3 500 (program s)) ++ "}")

  io : ℕ → IO ⊤
  io s = oracle ioOp 3 500 (program s)

  hand : List (String × Prog natᵗ) → IO ⊤
  hand []             = putStrLn "hand: done"
  hand ((l , p) ∷ cs) = putStrLn ((if prop p then "hand: ok   " else "hand: FAIL ") ++ l) >>= λ _ → hand cs

  nat : String → Maybe ℕ
  nat = readMaybe 10

  usage : IO ⊤
  usage = putStrLn "usage: Oracle-CLI prog FROM COUNT | Oracle-CLI io SEED | Oracle-CLI chain FROM COUNT | Oracle-CLI leaves FROM COUNT | Oracle-CLI hand"

  dispatch : List String → IO ⊤
  dispatch ("prog" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (mapL (f′ +_) (upTo c′)) prog
  ... | _       | _       = usage
  dispatch ("io" ∷ s ∷ []) with nat s
  ... | just s′ = io s′
  ... | nothing = usage
  dispatch ("chain" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (chainFails f′ c′) (λ s → putStrLn ("chain: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("chain: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch ("leaves" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (leavesFails f′ c′) (λ s → putStrLn ("leaves: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("leaves: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch ("hand" ∷ []) = hand cases
  dispatch _ = usage

main : IO ⊤
main = getArgs >>= dispatch
