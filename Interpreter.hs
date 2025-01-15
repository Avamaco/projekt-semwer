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

opInt :: Expr -> Expr -> VEnv -> Store -> (Integer -> Integer -> Integer) -> Either Error Value
opInt exp0 exp1 rhoV sto op = 
  let v0 = eE exp0 rhoV sto
      v1 = eE exp1 rhoV sto
   in case (v0, v1) of
        (Right (IntValue i0), Right (IntValue i1)) -> Right (IntValue (op i0 i1))
        _ -> Left Error

opBool :: Expr -> Expr -> VEnv -> Store -> (Bool -> Bool -> Bool) -> Either Error Value
opBool exp0 exp1 rhoV sto op = 
  let v0 = eE exp0 rhoV sto
      v1 = eE exp1 rhoV sto
   in case (v0, v1) of
        (Right (BoolValue b0), Right (BoolValue b1)) -> Right (BoolValue (op b0 b1))
        _ -> Left Error

opCompare :: Expr -> Expr -> VEnv -> Store -> (Integer -> Integer -> Bool) -> Either Error Value
opCompare exp0 exp1 rhoV sto op = 
  let v0 = eE exp0 rhoV sto
      v1 = eE exp1 rhoV sto
   in case (v0, v1) of
        (Right (IntValue i0), Right (IntValue i1)) -> Right (BoolValue (op i0 i1))
        _ -> Left Error

eE :: Expr -> VEnv -> Store -> Either Error Value

eE (ETrue) rhoV sto = Right (BoolValue True)
eE (EFalse) rhoV sto = Right (BoolValue False)
eE (ENum n) rhoV sto = Right (IntValue n)
eE (EVar v) rhoV sto = Right (IntValue 0) --TODO

eE (EPlus exp0 exp1) rhoV sto = opInt exp0 exp1 rhoV sto (+)
eE (EMinus exp0 exp1) rhoV sto = opInt exp0 exp1 rhoV sto (-)
eE (EMul exp0 exp1) rhoV sto = opInt exp0 exp1 rhoV sto (*)
eE (EDiv exp0 exp1) rhoV sto = opInt exp0 exp1 rhoV sto (div)
eE (ENeg exp) rhoV sto = 
  let v = eE exp rhoV sto
   in case v of
        Right (IntValue i) -> Right (IntValue (-i))
        _ -> Left Error

eE (EEq exp0 exp1) rhoV sto = opCompare exp0 exp1 rhoV sto (==)
eE (ELt exp0 exp1) rhoV sto = opCompare exp0 exp1 rhoV sto (<)
eE (EGt exp0 exp1) rhoV sto = opCompare exp0 exp1 rhoV sto (>)
eE (ELeq exp0 exp1) rhoV sto = opCompare exp0 exp1 rhoV sto (<=)
eE (EGeq exp0 exp1) rhoV sto = opCompare exp0 exp1 rhoV sto (>=)
eE (ENeq exp0 exp1) rhoV sto = opCompare exp0 exp1 rhoV sto (/=)

eE (EAnd exp0 exp1) rhoV sto = opBool exp0 exp1 rhoV sto (&&)
eE (EOr exp0 exp1) rhoV sto = opBool exp0 exp1 rhoV sto (||)
eE (ENot exp) rhoV sto =
  let v = eE exp rhoV sto
   in case v of
        Right (BoolValue b) -> Right (BoolValue (not b))
        _ -> Left Error

eE (ETern exp0 exp1 exp2) rhoV sto =
  let v0 = eE exp0 rhoV sto
      v1 = eE exp1 rhoV sto
      v2 = eE exp2 rhoV sto
   in case (v0, v1, v2) of
        (Right (BoolValue b), Right (IntValue i1), Right (IntValue i2)) -> Right (IntValue (if b then i1 else i2))
        _ -> Left Error

eE (ECheck exp i) rhoV sto = Right (IntValue 0) --TODO