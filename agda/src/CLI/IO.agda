-- The CLI's FFI surface: I/O + string handling WITHOUT importing any
-- number-touching builtin (which would clash with the custom Prelude's
-- BUILTIN NATURAL). String is an opaque BUILTIN STRING; characters are read
-- as ℕ codepoints through one fold. Everything else stays in Prelude types.
module CLI.IO where

open import Prelude
open import Agda.Builtin.IO public using (IO)

postulate String : Set
{-# BUILTIN STRING String #-}

data Unit : Set where unit : Unit
{-# COMPILE GHC Unit = data () (()) #-}

postulate
  returnIO     : {A : Set} → A → IO A
  _>>=_        : {A B : Set} → IO A → (A → IO B) → IO B
  getContents  : IO String
  putStr       : String → IO Unit
  foldString   : {A : Set} → (ℕ → A → A) → A → String → A
  natToStr     : ℕ → String
  appendStr    : String → String → String
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# COMPILE GHC returnIO = \_ x -> return x #-}
{-# COMPILE GHC _>>=_ = \_ _ m k -> m >>= k #-}
{-# COMPILE GHC getContents = TIO.getContents #-}
{-# COMPILE GHC putStr = \s -> TIO.putStr s >> return () #-}
{-# COMPILE GHC foldString = \_ f z s -> T.foldr (\c acc -> f (fromIntegral (fromEnum c)) acc) z s #-}
{-# COMPILE GHC natToStr = \n -> T.pack (show (n :: Integer)) #-}
{-# COMPILE GHC appendStr = T.append #-}

infixl 1 _>>=_

toCodes : String → List ℕ
toCodes = foldString _∷_ []

concatStr : List String → String
concatStr []       = ""
concatStr (s ∷ ss) = appendStr s (concatStr ss)
