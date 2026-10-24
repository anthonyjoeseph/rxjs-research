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
--   Oracle-CLI denote SEED       the denotation's trace of one seed
--   Oracle-CLI pure SEED         the pure semantics' trace of one seed
--   Oracle-CLI chain FROM COUNT  the seeds whose denotation's approximants
--                                are no chain (`quickcheck.Chain`)
--   Oracle-CLI placing SEED CHECK whether that seed's machine trace strays
--                                from the meaning, positions included, and
--                                which checks fail; CHECK names one, or
--                                "all" (`quickcheck.Placing`)
--   Oracle-CLI stepping FROM COUNT the seeds whose stepper parts from the
--                                meaning, skips included (`quickcheck.Stepping`)
--   Oracle-CLI kept-depth FROM COUNT each seed's engine run: whether every
--                                silent step drops its meaning's first skip
--                                or means the same (`quickcheck.KeptDepth`)
--   Oracle-CLI hand              placing over `quickcheck.Adversary`
--   Oracle-CLI why-hand N        its Nth program and the checks it fails
--   Oracle-CLI spin              progress over `quickcheck.Spin`'s programs
--   Oracle-CLI why-spin N K      its Nth program, each side's first K events
--
-- The IO engine runs one seed per process because a program that never
-- finishes never returns: the caller's timeout is the only way out.
module quickcheck.Oracle-CLI where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; upTo; foldr) renaming (map to mapL)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (readMaybe) renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
open import IO.Primitive.Core using (pure; _>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import System.Environment.Primitive using (getArgs)

open import quickcheck.Ty using (Ty; natᵗ; nameᵗ; _×ᵗ_)
open import quickcheck.Code using (Prog; showCode)
open import quickcheck.Oracle using (showTrace; denoteTrace; pureTrace; oracle; ioOp)
open import quickcheck.Quickcheck using (program; named)
open import quickcheck.Chain using (chainFails)
open import quickcheck.Adversary using (cases)
import quickcheck.Spin as Spin
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline)
open import quickcheck.Placing using (placing; placingParts)
open import quickcheck.Stepping using (steppingFails)
open import quickcheck.KeptDepth using (keptLines)

private
  each : List ℕ → (ℕ → IO ⊤) → IO ⊤
  each []       f = pure _
  each (x ∷ xs) f = f x >>= λ _ → each xs f

  each′ : List String → IO ⊤
  each′ []       = pure _
  each′ (x ∷ xs) = putStrLn x >>= λ _ → each′ xs

  prog : ℕ → IO ⊤
  prog s = putStrLn ("{\"seed\":" ++ showℕ s ++ ",\"prog\":" ++ showCode natᵗ (program s)
                     ++ ",\"denote\":" ++ showTrace natᵗ (denoteTrace 3 500 (program s))
                     ++ ",\"pure\":" ++ showTrace natᵗ (pureTrace 3 500 (program s)) ++ "}")

  io : ℕ → IO ⊤
  io s = oracle ioOp 3 500 (program s)

  namedᵗ : Ty
  namedᵗ = natᵗ ×ᵗ nameᵗ

  namedProg : ℕ → IO ⊤
  namedProg s = putStrLn ("{\"seed\":" ++ showℕ s ++ ",\"prog\":" ++ showCode namedᵗ (named s)
                          ++ ",\"denote\":" ++ showTrace namedᵗ (denoteTrace 3 500 (named s))
                          ++ ",\"pure\":" ++ showTrace namedᵗ (pureTrace 3 500 (named s)) ++ "}")

  hand : List (String × Prog natᵗ) → IO ⊤
  hand []             = putStrLn "hand: done"
  hand ((l , p) ∷ cs) = putStrLn ((if placing p then "hand: ok   " else "hand: FAIL ") ++ l) >>= λ _ → hand cs

  spins : List (String × Obs Timeline [] ℕ) → IO ⊤
  spins []             = putStrLn "spin: done"
  spins ((l , o) ∷ cs) = putStrLn ((if Spin.progress 8 o then "spin: ok   " else "spin: FAIL ") ++ l) >>= λ _ → spins cs

  nth : ∀ {ℓ} {X : Set ℓ} → ℕ → List (String × X) → Maybe (String × X)
  nth _       []       = nothing
  nth zero    (c ∷ cs) = just c
  nth (suc n) (c ∷ cs) = nth n cs

  nat : String → Maybe ℕ
  nat = readMaybe 10

  usage : IO ⊤
  usage = putStrLn "usage: Oracle-CLI prog FROM COUNT | Oracle-CLI code SEED | Oracle-CLI named FROM COUNT | Oracle-CLI named-code SEED | Oracle-CLI named-io SEED | Oracle-CLI denote SEED | Oracle-CLI pure SEED | Oracle-CLI io SEED | Oracle-CLI chain FROM COUNT | Oracle-CLI placing SEED CHECK | Oracle-CLI stepping FROM COUNT | Oracle-CLI kept-depth FROM COUNT | Oracle-CLI hand | Oracle-CLI why-hand N | Oracle-CLI spin | Oracle-CLI why-spin N K"

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
  ... | just s′ = putStrLn (showTrace natᵗ (denoteTrace 3 500 (program s′)))
  ... | nothing = usage
  dispatch ("pure" ∷ s ∷ []) with nat s
  ... | just s′ = putStrLn (showTrace natᵗ (pureTrace 3 500 (program s′)))
  ... | nothing = usage
  dispatch ("io" ∷ s ∷ []) with nat s
  ... | just s′ = io s′
  ... | nothing = usage
  dispatch ("chain" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (chainFails f′ c′) (λ s → putStrLn ("chain: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("chain: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch ("placing" ∷ n ∷ c ∷ []) with nat n
  ... | just s  = putStrLn (verdict (placingParts c (program s)))
    where verdict : List String → String
          verdict [] = "placing: ok seed " ++ n
          verdict ps = "placing: FAIL seed " ++ n ++ foldr (λ q r → " " ++ q ++ r) "" ps
  ... | nothing = usage
  dispatch ("stepping" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each (steppingFails f′ c′) (λ s → putStrLn ("stepping: FAIL seed " ++ showℕ s))
                            >>= λ _ → putStrLn ("stepping: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch ("kept-depth" ∷ f ∷ c ∷ []) with nat f | nat c
  ... | just f′ | just c′ = each′ (keptLines f′ c′) >>= λ _ → putStrLn ("kept-depth: done " ++ showℕ c′)
  ... | _       | _       = usage
  dispatch ("hand" ∷ []) = hand cases
  dispatch ("spin" ∷ []) = spins Spin.cases
  dispatch ("why-spin" ∷ n ∷ k ∷ []) with nat n | nat k
  ... | just n′ | just k′ with nth {X = Obs Timeline [] ℕ} n′ Spin.cases
  ...   | just (l , o) = putStrLn l >>= λ _ → each′ (Spin.progressWhy k′ o)
  ...   | nothing      = usage
  dispatch ("why-spin" ∷ n ∷ k ∷ []) | _ | _ = usage
  dispatch ("why-hand" ∷ n ∷ []) with nat n
  ... | just n′ with nth {X = Prog natᵗ} n′ cases
  ...   | just (l , p) = putStrLn l >>= λ _ → putStrLn (showCode natᵗ p) >>= λ _ → each′ (placingParts "all" p)
  ...   | nothing      = usage
  dispatch ("why-hand" ∷ n ∷ []) | nothing = usage
  dispatch _ = usage

main : IO ⊤
main = getArgs >>= dispatch
