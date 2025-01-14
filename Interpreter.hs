module Main where

import Jezyk.Par (myLexer, pProg)
import System.Exit (exitFailure)
import TypeCheck (checkProg)

main :: IO ()
main = do
  getContents >>= compute
  putStrLn ""

compute :: String -> IO ()
compute str =
  case pProg (myLexer str) of
    Left err -> do putStrLn err; exitFailure
    Right prog -> print (checkProg prog)
