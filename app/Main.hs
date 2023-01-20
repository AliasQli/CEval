module Main where

import qualified Data.ByteString.Lazy  as B
import           Data.Functor.Identity
import           Evaluator
import qualified Lexer                 as L
import qualified Parser                as P
import           System.Environment    (getArgs)
import           Tychecker

main :: IO ()
main = do
  getArgs >>= \case
    [filename] -> do
      file <- B.readFile filename
      run file
    ["parse", filename] -> do
      file <- B.readFile filename
      case L.runAlex file P.parseC of
        Left e      -> fail e
        Right gDefs -> print gDefs
    ["ast", filename] -> do
      file <- B.readFile filename
      case L.runAlex file P.parseC of
        Left e -> fail e
        Right gDefs -> do
          case formProgram gDefs of
            Identity (Program _ main) -> print main
    _          -> fail "Bad argument"
