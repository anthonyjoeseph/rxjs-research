-- The CLI's FFI surface: stdin/stdout over Agda String (mapped to
-- Haskell Text by MAlonzo). Everything else — codepoints, number
-- formatting, string building — is plain stdlib on top of this.
module CLI.IO where

open import Agda.Builtin.IO public using (IO)

open import Data.String using (String)

data Unit : Set where unit : Unit
{-# COMPILE GHC Unit = data () (()) #-}

postulate
  returnIO : {A : Set} → A → IO A
  _>>=_    : {A B : Set} → IO A → (A → IO B) → IO B
  getContents : IO String
  putStr      : String → IO Unit
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# COMPILE GHC returnIO = \_ x -> return x #-}
{-# COMPILE GHC _>>=_ = \_ _ m k -> m >>= k #-}
{-# COMPILE GHC getContents = TIO.getContents #-}
{-# COMPILE GHC putStr = \s -> TIO.putStr s >> System.IO.hFlush System.IO.stdout >> return () #-}

infixl 1 _>>=_
