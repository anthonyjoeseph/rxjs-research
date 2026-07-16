module Main where

open import Data.Nat     using (ℕ; zero; suc; _≤_; _+_)
open import Data.Bool    using (Bool)
open import Data.List    using (List; []; _∷_; _++_; take; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Vec     using (Vec; lookup)
open import Data.Fin     using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤)
open import Data.Sum     using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Rx         using (Tick; Fuel; Ordinal; Id; freshId; InstEmit)




