module Main where

import Data.Map (Map)
import Data.Map qualified as Map
import Jezyk.Abs (Decl (..), Expr (..), Ident (..), Prog (..), Stmt (..), Var (..))
import Jezyk.Abs qualified as Abs (CType (..), Type (..))
import Jezyk.Par (myLexer, pExpr, pProg)
import System.Exit (exitFailure)
import TypeCheck (checkProg)

type Loc = Integer

data SType = Bool | Int

data CType = Array Integer SType | Dict SType

data SValue = VInt Integer | VBool Bool | VError

instance Show SValue where
  show :: SValue -> String
  show (VInt i) = show i
  show (VBool True) = "true"
  show (VBool False) = "false"
  show VError = "Runtime error"

data CValue
  = CArray {size :: Integer, typ :: SType, values :: Map Integer SValue}
  | CDict {typ :: SType, values :: Map Integer SValue}

instance Show CValue where
  show :: CValue -> String
  show (CDict t vs) = unwords (map (\(i, v) -> show i ++ "=" ++ show v) (Map.toList vs))
  show (CArray s t vs) = unwords (map show (Map.elems vs))

data Value = SValue SValue | CValue CValue

instance Show Value where
  show :: Value -> String
  show (SValue v) = show v
  show (CValue v) = show v

type VEnv = Map Ident Loc

data Store = CStore {currMap :: Map Loc Value, nextLoc :: Loc}

type Output = [String]

type Cont = Store -> Output

type DCont = VEnv -> Cont

main :: IO ()
main = do
  getContents >>= compute
  putStrLn ""

sto0 :: Store
sto0 = CStore {currMap = Map.empty, nextLoc = 0}

venv0 :: VEnv
venv0 = Map.empty

compute :: String -> IO ()
compute str =
  case pProg (myLexer str) of
    Left err -> do
      putStrLn err
      exitFailure
    Right prog ->
      if checkProg prog
        then putStr (unlines (execProg prog))
        else putStrLn "Type error"

cont0 :: Cont
cont0 sto = []

contx0 :: Cont
contx0 sto = ["Runtime error"]

execProg :: Prog -> Output
execProg (Prog stmt) = sS stmt venv0 cont0 contx0 sto0

-- Expressions

defVal :: SType -> SValue
defVal Bool = VBool False
defVal Int = VInt 0

defCVal :: CType -> CValue
defCVal (Array s t) = CArray s t (Map.fromList [(i, defVal t) | i <- [0 .. s - 1]])
defCVal (Dict t) = CDict t Map.empty

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

-- Statements

assgnVal :: Var -> SValue -> VEnv -> Store -> Maybe Store
assgnVal (VId i) v venv sto =
  case Map.lookup i venv of
    Just loc -> Just (sto {currMap = Map.insert loc (SValue v) (currMap sto)})
    _ -> Nothing
assgnVal (VAt i e) v venv sto =
  let loc = Map.lookup i venv
      val = eE e venv sto
   in case (loc, val) of
        (Just l, VInt i) -> case Map.lookup l (currMap sto) of
          Just (CValue (CArray s t vs)) ->
            if i >= 0 && i < s
              then
                Just (sto {currMap = Map.insert l (CValue (CArray s t (Map.insert i v vs))) (currMap sto)})
              else Nothing
          Just (CValue (CDict t vs)) ->
            Just (sto {currMap = Map.insert l (CValue (CDict t (Map.insert i v vs))) (currMap sto)})
          _ -> Nothing
        _ -> Nothing

sS :: Stmt -> VEnv -> Cont -> Cont -> Cont
-- sS (SCall i) venv k kx = -- TODO
-- sS (SCallA i a) venv k kx = -- TODO
sS (SAssgn v e) venv k kx = \sto ->
  let val = eE e venv sto
   in case val of
        VError -> kx sto
        _ -> case assgnVal v val venv sto of
          Just sto' -> k sto'
          _ -> kx sto
-- sS (SAssgnF v i') venv k kx = -- TODO
-- sS (SAssgnFA v i' a) venv k kx = -- TODO
sS (SDel e i) venv k kx = \sto ->
  let v = eE e venv sto
      loc = Map.lookup i venv
   in case (v, loc) of
        (VInt i, Just l) -> case Map.lookup l (currMap sto) of
          Just (CValue (CDict t vs)) ->
            k (sto {currMap = Map.insert l (CValue (CDict t (Map.delete i vs))) (currMap sto)})
          _ -> kx sto
        _ -> kx sto
sS (SIfte e s1 s2) venv k kx = \sto ->
  let v = eE e venv sto
   in case v of
        VBool True -> sS s1 venv k kx sto
        VBool False -> sS s2 venv k kx sto
        _ -> kx sto
sS (SIfend e s) venv k kx = \sto ->
  let v = eE e venv sto
   in case v of
        VBool True -> sS s venv k kx sto
        VBool False -> k sto
        _ -> kx sto
sS (SWhile e s) venv k kx = \sto ->
  let b = eE e venv sto
   in case b of
        VBool True -> sS s venv (sS (SWhile e s) venv k kx) kx sto
        VBool False -> k sto
        _ -> kx sto
-- sS (SFor i e1 e2 s) venv k kx = -- TODO
-- sS (SForKeys i i' s) venv k kx = -- TODO
-- sS (SForVals i i' s) venv k kx = -- TODO
-- sS (SForPairs i1 i2 i' s) venv k kx = -- TODO
sS (SPrint i) venv k kx = \sto ->
  case Map.lookup i venv of
    Just loc -> case Map.lookup loc (currMap sto) of
      Just v -> show v : k sto
    _ -> kx sto
sS (SBlock d s) venv k kx = dD d venv (\venv' -> sS s venv' k kx)
sS (STry s1 s2) venv k kx = sS s1 venv k (sS s2 venv k kx)
sS (SSeq s1 s2) venv k kx = sS s1 venv (sS s2 venv k kx) kx

-- Declarations

declare :: Ident -> Value -> VEnv -> Store -> (VEnv, Store)
declare i v venv sto =
  let loc = nextLoc sto
      sto' = sto {currMap = Map.insert loc v (currMap sto), nextLoc = loc + 1}
   in (Map.insert i loc venv, sto')

getType :: Abs.Type -> SType
getType Abs.TInt = Int
getType Abs.TBool = Bool

getCType :: Abs.CType -> CType
getCType (Abs.CTArray n t) = Array n (getType t)
getCType (Abs.CTDict t) = Dict (getType t)

dD :: Decl -> VEnv -> DCont -> Cont
dD (DSimple i t) venv k = \sto ->
  let (venv', sto') = declare i (SValue (defVal (getType t))) venv sto
   in k venv' sto'
dD (DComplex i t) venv k = \sto ->
  let (venv', sto') = declare i (CValue (defCVal (getCType t))) venv sto
   in k venv' sto'
-- dD (DFunction f s) venv k sto = -- TODO
dD (DSeq d1 d2) venv k = dD d1 venv (\venv' -> dD d2 venv' k)
