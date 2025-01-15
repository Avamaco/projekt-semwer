module Main where

import Data.Map (Map)
import Data.Map qualified as Map
import Jezyk.Abs (Decl (..), Expr (..), Ident (..), Prog (..), Stmt (..), Var (..))
import Jezyk.Par (myLexer, pExpr, pProg)
import System.Exit (exitFailure)
import TypeCheck (checkProg)

type Loc = Integer

data SType = Bool | Int

data CType = Array Integer SType | Dict SType

data SValue = VInt Integer | VBool Bool | VError deriving (Show)

data CValue
  = CArray {size :: Integer, typ :: SType, values :: Map Integer SValue}
  | CDict {typ :: SType, values :: Map Integer SValue}

data Value = SValue SValue | CValue CValue | Error

type VEnv = Map Ident Loc

data Store = CStore {currMap :: Map Loc Value, nextLoc :: Loc}

type Cont = Store -> Store

main :: IO ()
main = do
  getContents >>= compute
  putStrLn ""

dict0 :: CValue
dict0 = CDict Bool (Map.fromList [(-1, VBool True), (1, VBool False)])

arr0 :: CValue
arr0 = CArray 3 Int (Map.fromList [(0, VInt 1), (1, VInt 2), (2, VInt 3)])

sto0 :: Store
sto0 = CStore {currMap = Map.fromList [(0, SValue (VInt 3)), (1, SValue (VBool True)), (2, CValue dict0), (3, CValue arr0)], nextLoc = 0}

venv0 :: VEnv
venv0 = Map.fromList [(Ident "i", 0), (Ident "b", 1), (Ident "d", 2), (Ident "a", 3)]

compute :: String -> IO ()
compute str =
  case pExpr (myLexer str) of
    Left err -> do putStrLn err; exitFailure
    Right expr -> do print (eE expr venv0 sto0)

-- case pProg (myLexer str) of
--   Left err -> do putStrLn err; exitFailure
--   Right prog -> do print (checkProg prog); print (execProg prog)

execProg :: Prog -> Bool
execProg (Prog stmt) = True

-- Expressions

defVal :: SType -> SValue
defVal Bool = VBool False
defVal Int = VInt 0

opInt :: Expr -> Expr -> VEnv -> Store -> (Integer -> Integer -> Integer) -> SValue
opInt e1 e2 venv sto op =
  let v1 = eE e1 venv sto
      v2 = eE e2 venv sto
   in case (v1, v2) of
        (VInt i1, VInt i2) -> VInt (op i1 i2)
        _ -> VError

opBool :: Expr -> Expr -> VEnv -> Store -> (Bool -> Bool -> Bool) -> SValue
opBool e1 e2 venv sto op =
  let v1 = eE e1 venv sto
      v2 = eE e2 venv sto
   in case (v1, v2) of
        (VBool b1, VBool b2) -> VBool (op b1 b2)
        _ -> VError

opCompare :: Expr -> Expr -> VEnv -> Store -> (Integer -> Integer -> Bool) -> SValue
opCompare e1 e2 venv sto op =
  let v1 = eE e1 venv sto
      v2 = eE e2 venv sto
   in case (v1, v2) of
        (VInt i1, VInt i2) -> VBool (op i1 i2)
        _ -> VError

eE :: Expr -> VEnv -> Store -> SValue
eE ETrue venv sto = VBool True
eE EFalse venv sto = VBool False
eE (ENum n) venv sto = VInt n
eE (EVar (VId i)) venv sto =
  case Map.lookup i venv of
    Just loc -> case Map.lookup loc (currMap sto) of
      Just (SValue v) -> v
      _ -> VError
    _ -> VError
eE (EVar (VAt i e)) venv sto =
  let v = eE e venv sto
      loc = Map.lookup i venv
   in case (v, loc) of
        (VInt i, Just l) -> case Map.lookup l (currMap sto) of
          Just (CValue (CArray s t vs)) ->
            if i >= 0 && i < s then Map.findWithDefault (defVal t) i vs else VError
          Just (CValue (CDict t vs)) -> Map.findWithDefault VError i vs
          _ -> VError
        _ -> VError
eE (EPlus e1 e2) venv sto = opInt e1 e2 venv sto (+)
eE (EMinus e1 e) venv sto = opInt e1 e venv sto (-)
eE (EMul e1 e2) venv sto = opInt e1 e2 venv sto (*)
eE (EDiv e1 e2) venv sto =
  let v1 = eE e1 venv sto
      v2 = eE e2 venv sto
   in case (v1, v2) of
        (_, VInt 0) -> VError
        (VInt i1, VInt i2) -> VInt (div i1 i2)
        _ -> VError
eE (ENeg e) venv sto =
  let v = eE e venv sto
   in case v of
        VInt i -> VInt (-i)
        _ -> VError
eE (EEq e1 e2) venv sto = opCompare e1 e2 venv sto (==)
eE (ELt e1 e2) venv sto = opCompare e1 e2 venv sto (<)
eE (EGt e1 e2) venv sto = opCompare e1 e2 venv sto (>)
eE (ELeq e1 e2) venv sto = opCompare e1 e2 venv sto (<=)
eE (EGeq e1 e2) venv sto = opCompare e1 e2 venv sto (>=)
eE (ENeq e1 e2) venv sto = opCompare e1 e2 venv sto (/=)
eE (EAnd e1 e2) venv sto = opBool e1 e2 venv sto (&&)
eE (EOr e1 e2) venv sto = opBool e1 e2 venv sto (||)
eE (ENot e) venv sto =
  let v = eE e venv sto
   in case v of
        VBool b -> VBool (not b)
        _ -> VError
eE (ETern e e1 e2) venv sto =
  let v = eE e venv sto
      v1 = eE e1 venv sto
      v2 = eE e2 venv sto
   in case (v, v1, v2) of
        (VBool b, VInt i1, VInt i2) -> VInt (if b then i1 else i2)
        _ -> VError
eE (ECheck e i) venv sto =
  let v = eE e venv sto
      loc = Map.lookup i venv
   in case (v, loc) of
        (VInt i, Just l) -> case Map.lookup l (currMap sto) of
          Just (CValue (CArray s t vs)) ->
            if i >= 0 && i < s then VBool True else VBool False
          Just (CValue (CDict t vs)) -> if Map.member i vs then VBool True else VBool False
          _ -> VError
        _ -> VError
