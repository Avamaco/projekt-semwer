module Main where

import Data.Map (Map)
import Data.Map qualified as Map
import Jezyk.Abs (Decl (..), Expr (..), Ident (..), Prog (..), Stmt (..), Var (..))
import Jezyk.Par (myLexer, pProg)
import System.Exit (exitFailure)
import TypeCheck (checkProg)

type Loc = Integer
data Value = IntValue Integer | BoolValue Bool
data Error = Error

type VEnv = Map Ident Loc
data Store = CStore --{currMap :: Map Loc Value, nextLoc :: Loc}
type Cont = Store -> Store

main :: IO ()
main = do
  getContents >>= compute
  putStrLn ""

compute :: String -> IO ()
compute str =
  case pProg (myLexer str) of
    Left err -> do putStrLn err; exitFailure
    Right prog -> do print (checkProg prog); print (execProg prog)

execProg :: Prog -> Bool
execProg (Prog stmt) = True

-- Expressions

eE :: Expr -> VEnv -> Store -> Either Error Value

eE (ETrue) rhoV sto = Right (BoolValue True)
eE (EFalse) rhoV sto = Right (BoolValue False)
eE (ENum n) rhoV sto = Right (IntValue n)
eE (EVar v) rhoV sto = Right (IntValue 0) --TODO

eE (EPlus exp0 exp1) rhoV sto = (eE exp0 rhoV sto) + (eE exp1 rhoV sto)
eE (EMinus exp0 exp1) rhoV sto = (eE exp0 rhoV sto) - (eE exp1 rhoV sto)
eE (EMul exp0 exp1) rhoV sto = (eE exp0 rhoV sto) * (eE exp1 rhoV sto)
eE (EDiv exp0 exp1) rhoV sto = (eE exp0 rhoV sto) / (eE exp1 rhoV sto)
eE (ENeg exp) rhoV sto = - (eE exp rhoV sto)

eE (EEq exp0 exp1) rhoV sto = (eE exp0 rhoV sto) == (eE exp1 rhoV sto)
eE (ELt exp0 exp1) rhoV sto = (eE exp0 rhoV sto) < (eE exp1 rhoV sto)
eE (EGt exp0 exp1) rhoV sto = (eE exp0 rhoV sto) > (eE exp1 rhoV sto)
eE (ELeq exp0 exp1) rhoV sto = (eE exp0 rhoV sto) <= (eE exp1 rhoV sto)
eE (EGeq exp0 exp1) rhoV sto = (eE exp0 rhoV sto) >= (eE exp1 rhoV sto)
eE (ENeq exp0 exp1) rhoV sto = (eE exp0 rhoV sto) /= (eE exp1 rhoV sto)

eE (EAnd exp0 exp1) rhoV sto = (eE exp0 rhoV sto) && (eE exp1 rhoV sto)
eE (EOr exp0 exp1) rhoV sto = (eE exp0 rhoV sto) || (eE exp1 rhoV sto)
eE (ENot exp) rhoV sto = not (eE exp rhoV sto)

eE (ETern exp0 exp1 exp2) rhoV sto = if (eE exp0 rhoV sto) then (eE exp1 rhoV sto) else (eE exp2 rhoV sto)

eE (ECheck exp i) rhoV sto = Right (IntValue 0) --TODO