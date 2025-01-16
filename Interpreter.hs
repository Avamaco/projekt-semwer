module Main where

import Data.Map (Map)
import qualified Data.Map as Map
import Jezyk.Abs (Decl (..), Expr (..), Ident (..), Prog (..), Stmt (..), Var (..))
import qualified Jezyk.Abs as Abs (ADecl (..), Arg (..), CType (..), FDecl (..), Type (..))
import Jezyk.Par (myLexer, pExpr, pProg)
import qualified System.Environment as Env
import System.Exit (exitFailure)
import System.IO (IOMode (ReadMode), hGetContents, openFile)
import TypeCheck (checkProg)

type Loc = Integer

data SType = Bool | Int

data CType = Array Integer SType | Dict SType

data SValue = VInt Integer | VBool Bool | VError

data FValue = Value SValue | Void

instance Show SValue where
  show (VInt i) = show i
  show (VBool True) = "true"
  show (VBool False) = "false"
  show VError = "Runtime error"

data CValue
  = CArray {size :: Integer, typ :: SType, values :: Map Integer SValue}
  | CDict {typ :: SType, values :: Map Integer SValue}

instance Show CValue where
  show (CDict t vs) = unwords (map (\(i, v) -> show i ++ "=" ++ show v) (Map.toList vs))
  show (CArray s t vs) = unwords (map show (Map.elems vs))

data Value = SValue SValue | CValue CValue

instance Show Value where
  show (SValue v) = show v
  show (CValue v) = show v

type VEnv = Map Ident Loc

type FEnv = Map Ident Fun

data Store = CStore {currMap :: Map Loc Value, nextLoc :: Loc}

type Output = [String]

type Cont = Store -> Output

type DCont = VEnv -> FEnv -> Cont

type FCont = FValue -> Cont

data ADecl = ADecl Ident SType

type ADList = [ADecl]

data RType = Return Ident SType | RVoid

data FDecl = FDecl ADList RType

type Arg = SValue

type AList = [Arg]

type Fun = AList -> FCont -> Cont -> Cont

type SStmt = VEnv -> FEnv -> Cont -> Cont -> Cont

main :: IO ()
main = do
  a <- Env.getArgs
  if null a || length a > 1
    then putStrLn "Usage: Interpreter <file>"
    else do
      handle <- openFile (head a) ReadMode
      hGetContents handle >>= compute

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

sto0 :: Store
sto0 = CStore {currMap = Map.empty, nextLoc = 0}

venv0 :: VEnv
venv0 = Map.empty

fenv0 :: FEnv
fenv0 = Map.empty

cont0 :: Cont
cont0 sto = []

contx0 :: Cont
contx0 sto = ["Runtime error"]

execProg :: Prog -> Output
execProg (Prog stmt) = sS stmt venv0 fenv0 cont0 contx0 sto0

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

forNum :: Ident -> Integer -> Integer -> Stmt -> VEnv -> FEnv -> Cont -> Cont -> Cont
forNum i n1 n2 s venv fenv k kx =
  if n1 > n2
    then k
    else
      let k' = sS s venv fenv (forNum i (n1 + 1) n2 s venv fenv k kx) kx
       in \sto ->
            case assgnVal (VId i) (VInt n1) venv sto of
              Just sto' -> k' sto'
              _ -> kx sto

loop :: [SValue] -> Ident -> Stmt -> VEnv -> FEnv -> Cont -> Cont -> Cont
loop [] i s venv fenv k kx = k
loop (v : vs) i s venv fenv k kx =
  let k' = sS s venv fenv (loop vs i s venv fenv k kx) kx
   in \sto ->
        let Just sto' = assgnVal (VId i) v venv sto
         in k' sto'

loop2 :: [(Integer, SValue)] -> Ident -> Ident -> Stmt -> VEnv -> FEnv -> Cont -> Cont -> Cont
loop2 [] i1 i2 s venv fenv k kx = k
loop2 ((v1, v2) : vs) i1 i2 s venv fenv k kx =
  let k' = sS s venv fenv (loop2 vs i1 i2 s venv fenv k kx) kx
   in \sto ->
        let Just sto' = assgnVal (VId i1) (VInt v1) venv sto
            Just sto'' = assgnVal (VId i2) v2 venv sto'
         in k' sto''

getArgs :: Abs.Arg -> VEnv -> Store -> AList
getArgs (Abs.AId i) venv sto =
  let Just loc = Map.lookup i venv
      Just (SValue val) = Map.lookup loc (currMap sto)
   in [val]
getArgs (Abs.ASeq i as) venv sto =
  let Just loc = Map.lookup i venv
      Just (SValue val) = Map.lookup loc (currMap sto)
   in val : getArgs as venv sto

sS :: Stmt -> SStmt
sS (SCall i) venv fenv k kx =
  let Just fun = Map.lookup i fenv
   in fun [] (const k) kx
sS (SCallA i a) venv fenv k kx = \sto ->
  let Just fun = Map.lookup i fenv
      args = getArgs a venv sto
   in fun args (const k) kx sto
sS (SAssgn v e) venv fenv k kx = \sto ->
  let val = eE e venv sto
   in case val of
        VError -> kx sto
        _ -> case assgnVal v val venv sto of
          Just sto' -> k sto'
          _ -> kx sto
sS (SAssgnF v i) venv fenv k kx = \sto ->
  let Just fun = Map.lookup i fenv
   in fun
        []
        ( \ret sto ->
            let Value val = ret
                Just sto' = assgnVal v val venv sto
             in k sto'
        )
        kx
        sto
sS (SAssgnFA v i' a) venv fenv k kx = \sto ->
  let Just fun = Map.lookup i' fenv
      args = getArgs a venv sto
   in fun
        args
        ( \ret sto ->
            let Value val = ret
                Just sto' = assgnVal v val venv sto
             in k sto'
        )
        kx
        sto
sS (SDel e i) venv fenv k kx = \sto ->
  let v = eE e venv sto
      loc = Map.lookup i venv
   in case (v, loc) of
        (VInt i, Just l) -> case Map.lookup l (currMap sto) of
          Just (CValue (CDict t vs)) ->
            k (sto {currMap = Map.insert l (CValue (CDict t (Map.delete i vs))) (currMap sto)})
          _ -> kx sto
        _ -> kx sto
sS (SIfte e s1 s2) venv fenv k kx = \sto ->
  let v = eE e venv sto
   in case v of
        VBool True -> sS s1 venv fenv k kx sto
        VBool False -> sS s2 venv fenv k kx sto
        _ -> kx sto
sS (SIfend e s) venv fenv k kx = \sto ->
  let v = eE e venv sto
   in case v of
        VBool True -> sS s venv fenv k kx sto
        VBool False -> k sto
        _ -> kx sto
sS (SWhile e s) venv fenv k kx = \sto ->
  let b = eE e venv sto
   in case b of
        VBool True -> sS s venv fenv (sS (SWhile e s) venv fenv k kx) kx sto
        VBool False -> k sto
        _ -> kx sto
sS (SFor i e1 e2 s) venv fenv k kx = \sto ->
  let v1 = eE e1 venv sto
      v2 = eE e2 venv sto
      (venv', sto') = declare i (SValue (VInt 0)) venv sto
   in case (v1, v2) of
        (VInt n1, VInt n2) -> forNum i n1 n2 s venv' fenv k kx sto'
        _ -> kx sto
sS (SForKeys i i' s) venv fenv k kx = \sto ->
  let Just loc = Map.lookup i' venv
      Just (CValue val) = Map.lookup loc (currMap sto)
      (venv', sto') = declare i (SValue VError) venv sto
   in case val of
        CArray siz _ vs -> forNum i 0 (siz - 1) s venv' fenv k kx sto'
        CDict _ vs -> loop (map VInt (Map.keys vs)) i s venv' fenv k kx sto'
sS (SForVals i i' s) venv fenv k kx = \sto ->
  let Just loc = Map.lookup i' venv
      Just (CValue val) = Map.lookup loc (currMap sto)
      (venv', sto') = declare i (SValue VError) venv sto
   in case val of
        CArray siz t vs -> loop (Map.elems vs) i s venv' fenv k kx sto'
        CDict t vs -> loop (Map.elems vs) i s venv' fenv k kx sto'
sS (SForPairs i1 i2 i' s) venv fenv k kx = \sto ->
  let Just loc = Map.lookup i' venv
      Just (CValue val) = Map.lookup loc (currMap sto)
      (venv', sto') = declare i1 (SValue VError) venv sto
      (venv'', sto'') = declare i2 (SValue VError) venv' sto'
   in case val of
        CArray siz t vs -> loop2 (Map.toList vs) i1 i2 s venv'' fenv k kx sto''
        CDict t vs -> loop2 (Map.toList vs) i1 i2 s venv'' fenv k kx sto''
sS (SPrint i) venv fenv k kx = \sto ->
  case Map.lookup i venv of
    Just loc -> case Map.lookup loc (currMap sto) of
      Just v -> show v : k sto
    _ -> kx sto
sS (SBlock d s) venv fenv k kx = dD d venv fenv (\venv' fenv' -> sS s venv' fenv' k kx)
sS (STry s1 s2) venv fenv k kx = sS s1 venv fenv k (sS s2 venv fenv k kx)
sS (SSeq s1 s2) venv fenv k kx = sS s1 venv fenv (sS s2 venv fenv k kx) kx

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

getres :: FDecl -> VEnv -> Store -> FValue
getres (FDecl ad RVoid) venv sto = Void
getres (FDecl ad (Return ri rt)) venv sto =
  let Just loc = Map.lookup ri venv
      Just (SValue val) = Map.lookup loc (currMap sto)
   in Value val

declArgs :: VEnv -> Store -> ADList -> AList -> (VEnv, Store)
declArgs venv sto [] [] = (venv, sto)
declArgs venv sto (ADecl i t : ads) (v : as) =
  let (venv', sto') = declare i (SValue v) venv sto
   in declArgs venv' sto' ads as

declRes :: VEnv -> Store -> FDecl -> (VEnv, Store)
declRes venv sto (FDecl ad RVoid) = (venv, sto)
declRes venv sto (FDecl ad (Return ri rt)) = declare ri (SValue (defVal rt)) venv sto

declFun :: VEnv -> FEnv -> Ident -> FDecl -> SStmt -> FEnv
declFun venv fenv i fd s =
  let fun a kf kx sto = s venv'' fenv'' k kx sto''
        where
          k stor = kf (getres fd venv'' stor) stor
          FDecl ad r = fd
          (venv', sto') = declArgs venv sto ad a
          (venv'', sto'') = declRes venv' sto' fd
          fenv'' = Map.insert i fun fenv
   in Map.insert i fun fenv

dA :: Abs.ADecl -> ADList
dA (Abs.ADId i t) = [ADecl i (getType t)]
dA (Abs.ADSeq i t a) = ADecl i (getType t) : dA a

dF :: Abs.FDecl -> FDecl
dF Abs.FDVoid = FDecl [] RVoid
dF (Abs.FDRet i t) = FDecl [] (Return i (getType t))
dF (Abs.FDArg a) = FDecl (dA a) RVoid
dF (Abs.FDFull a i t) = FDecl (dA a) (Return i (getType t))

dD :: Decl -> VEnv -> FEnv -> DCont -> Cont
dD (DSimple i t) venv fenv k = \sto ->
  let (venv', sto') = declare i (SValue (defVal (getType t))) venv sto
   in k venv' fenv sto'
dD (DComplex i t) venv fenv k = \sto ->
  let (venv', sto') = declare i (CValue (defCVal (getCType t))) venv sto
   in k venv' fenv sto'
dD (DFunction i f s) venv fenv k = \sto ->
  let fenv' = declFun venv fenv i (dF f) (sS s)
   in k venv fenv' sto
dD (DSeq d1 d2) venv fenv k = dD d1 venv fenv (\venv' fenv' -> dD d2 venv' fenv' k)
