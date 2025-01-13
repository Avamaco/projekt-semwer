module Main where

import Jezyk.Par (myLexer, pExpr)
import System.Exit (exitFailure)
import TypeCheck (typifyExpr)

main :: IO ()
main = do
  getContents >>= compute
  putStrLn ""

compute :: String -> IO ()
compute str =
  case pExpr (myLexer str) of
    Left err -> do putStrLn err; exitFailure
    Right expr -> print (typifyExpr expr)
