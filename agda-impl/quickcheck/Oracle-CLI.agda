{-# OPTIONS --guardedness #-}

-- THE ORACLE'S AGDA HALF: the generated programs, and what the three
-- engines make of them, as JSON lines for `typescript/` to replay in
-- rxjs.  Same seeds, unfolding budget and step budget as `Quickcheck`.
--
--   Oracle-CLI prog FROM COUNT   one line per seed: the program, the
--                                denotation's trace and the pure engine's
--   Oracle-CLI io SEED           the IO engine's trace of one seed
--   Oracle-CLI chain FROM COUNT  the seeds whose denotation's approximants
--                                are no chain (`quickcheck.Chain`)
--   Oracle-CLI places FROM COUNT the seeds whose pure run places its
--                                record where the denotation does not
--   Oracle-CLI gets FROM COUNT   the seeds whose pure run, at the budget
--                                `Progress` reads off the meaning, falls
--                                short of an item the meaning shows
--   Oracle-CLI ghosts FROM COUNT the seeds with an observer inside the run
--                                delivered what its subtree's denotation
--                                does not show (`quickcheck.Ghost`)
--
-- The IO engine runs one seed per process because a program that never
-- finishes never returns: the caller's timeout is the only way out.
module quickcheck.Oracle-CLI where

open import Agda.Builtin.IO using (IO)
open import Data.List using (List; []; _∷_; upTo) renaming (map to mapL)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show using (readMaybe) renaming (show to showℕ)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
open import IO.Primitive.Core using (pure; _>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import System.Environment.Primitive using (getArgs)

open import quickcheck.Ty using (natᵗ)
open import quickcheck.Code using (showCode)
open import quickcheck.Oracle using (showTrace; denoteTrace; pureTrace; machineTrace; oracle; ioOp)
open import quickcheck.Quickcheck using (program; machineFails)
open import quickcheck.Chain using (chainFails; placeFails; placed; getsFails)
open import quickcheck.Ghost using (ghostFails; watchedCount)

private
  each : List ℕ → (ℕ → IO ⊤) → IO ⊤
  each []       f = pure _
  each (x ∷ xs) f = f x >>= λ _ → each xs f

  prog : ℕ → IO ⊤
  prog s = putStrLn ("{\"seed\":" ++ showℕ s ++ ",\"prog\":" ++ showCode natᵗ (program s)
                     ++ ",\"denote\":" ++ showTrace natᵗ (denoteTrace 3 500 (program s))
                     ++ ",\"pure\":" ++ showTrace natᵗ (pureTrace 3 500 (program s))
                     ++ ",\"machine\":" ++ showTrace natᵗ (machineTrace 3 500 (program s)) ++ "}")

  io : ℕ → IO ⊤
  io s = oracle ioOp 3 500 (program s)

  nat : String → Maybe ℕ
  nat = readMaybe 10

  usage : IO ⊤
  usage = putStrLn "usage: Oracle-CLI prog FROM COUNT | Oracle-CLI io SEED | Oracle-CLI chain FROM COUNT | Oracle-CLI places FROM COUNT | Oracle-CLI gets FROM COUNT | Oracle-CLI ghosts FROM COUNT | Oracle-CLI machine FROM COUNT"

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
  dispatch ("places" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (placeFails f′ c′) (λ s → putStrLn ("places: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("places: done " ++ showℕ c′ ++ ", " ++ showℕ (placed f′ c′) ++ " positions compared")
  ... | _       | _       = usage
  dispatch ("gets" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (getsFails f′ c′) (λ s → putStrLn ("gets: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("gets: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch ("ghosts" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (ghostFails f′ c′) (λ s → putStrLn ("ghosts: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("ghosts: done " ++ showℕ c′ ++ ", " ++ showℕ (watchedCount f′ c′) ++ " deliveries compared")
  ... | _       | _       = usage
  dispatch ("machine" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (machineFails f′ c′) (λ s → putStrLn ("machine: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("machine: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch _ = usage

main : IO ⊤
main = getArgs >>= dispatch
