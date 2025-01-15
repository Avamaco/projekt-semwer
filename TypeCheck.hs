module TypeCheck where

import Data.Map (Map)
import Data.Map qualified as Map
import Jezyk.Abs (Decl (..), Expr (..), Ident (..), Prog (..), Stmt (..), Var (..))
import Jezyk.Abs qualified as Abs (ADecl (..), Arg (..), CType (..), FDecl (..), Type (..))

data SType = Bool | Int deriving (Eq, Show)

data CType = Array SType | Dict SType deriving (Eq, Show)

data Type = SType SType | CType CType | Error deriving (Eq, Show)

data ADecl = ADecl Ident Type

type ADList = [ADecl]

data RType = Return Ident SType | Void

data FDecl = FDecl ADList RType

type AList = [Type]

type VEnv = Map Ident Type

type FEnv = Map Ident FDecl

data DEnv = Env VEnv FEnv | DError

getType :: Abs.Type -> Type
getType Abs.TBool = SType Bool
getType Abs.TInt = SType Int

getCType :: Abs.CType -> Type
getCType (Abs.CTArray _ t) =
  case getType t of
    SType t' -> CType (Array t')
    _ -> Error
getCType (Abs.CTDict t) =
  case getType t of
    SType t' -> CType (Dict t')
    _ -> Error

underType :: Type -> Type
underType (CType (Array t)) = SType t
underType (CType (Dict t)) = SType t
underType _ = Error

assertType :: Expr -> Expr -> VEnv -> Type -> Type -> Type
assertType e1 e2 venv t rt =
  let t1 = exprType e1 venv
      t2 = exprType e2 venv
   in if t1 == t && t2 == t then rt else Error

varType :: Var -> VEnv -> Type
varType (VId i) venv = Map.findWithDefault Error i venv
varType (VAt i e) venv =
  let t = Map.findWithDefault Error i venv
      et = exprType e venv
      ut = underType t
   in if et == SType Int then ut else Error

exprType :: Expr -> VEnv -> Type
exprType ETrue _ = SType Bool
exprType EFalse _ = SType Bool
exprType (ENum _) _ = SType Int
exprType (EVar v) venv = varType v venv
exprType (EPlus e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (EMinus e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (EMul e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (EDiv e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (ENeg e) venv = assertType e e venv (SType Int) (SType Int)
exprType (EEq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (ELt e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (EGt e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (ELeq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (EGeq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (ENeq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (EAnd e1 e2) venv = assertType e1 e2 venv (SType Bool) (SType Bool)
exprType (EOr e1 e2) venv = assertType e1 e2 venv (SType Bool) (SType Bool)
exprType (ENot e) venv = assertType e e venv (SType Bool) (SType Bool)
exprType (ETern e e1 e2) venv =
  let t = exprType e venv
      t1 = exprType e1 venv
      t2 = exprType e2 venv
   in if t == SType Bool && t1 == t2 then t1 else Error
exprType (ECheck e i) venv =
  let et = exprType e venv
      t = varType (VId i) venv
   in case (et, t) of
        (SType Int, CType _) -> SType Bool
        _ -> Error

argDecl :: Abs.ADecl -> ADList
argDecl (Abs.ADId i t) = [ADecl i (getType t)]
argDecl (Abs.ADSeq i t a) = ADecl i (getType t) : argDecl a

funDecl :: Abs.FDecl -> FDecl
funDecl Abs.FDVoid = FDecl [] Void
funDecl (Abs.FDRet i t) = let SType t' = getType t in FDecl [] (Return i t')
funDecl (Abs.FDArg a) = FDecl (argDecl a) Void
funDecl (Abs.FDFull a i t) = let SType t' = getType t in FDecl (argDecl a) (Return i t')

declareArgs :: ADList -> VEnv -> VEnv
declareArgs [] venv = venv
declareArgs (ADecl i t : as) venv = Map.insert i t (declareArgs as venv)

declare :: Decl -> VEnv -> FEnv -> DEnv
declare (DSimple i t) venv fenv = Env (Map.insert i (getType t) venv) fenv
declare (DComplex i ct) venv fenv = Env (Map.insert i (getCType ct) venv) fenv
declare (DFunction i fd s) venv fenv =
  let fd' = funDecl fd
      fenv' = Map.insert i fd' fenv
      FDecl args ret = fd'
      venv' = declareArgs args venv
      venv'' = case ret of
        Return i' t -> Map.insert i' (SType t) venv'
        Void -> venv'
   in if checkStmt s venv'' fenv' then Env venv fenv' else DError
declare (DSeq d1 d2) venv fenv =
  case declare d1 venv fenv of
    Env venv' fenv -> declare d2 venv' fenv
    DError -> DError

getArgs :: Abs.Arg -> VEnv -> AList
getArgs (Abs.AId i) venv = [varType (VId i) venv]
getArgs (Abs.ASeq i a) venv = varType (VId i) venv : getArgs a venv

matchArgs :: AList -> ADList -> Bool
matchArgs [] [] = True
matchArgs (t : ts) (ADecl _ t' : ts') = t == t' && matchArgs ts ts'
matchArgs _ _ = False

checkStmt :: Stmt -> VEnv -> FEnv -> Bool
checkStmt (SCall i) venv fenv =
  case Map.lookup i fenv of
    Just (FDecl args _) -> matchArgs [] args
    _ -> False
checkStmt (SCallA i a) venv fenv =
  case Map.lookup i fenv of
    Just (FDecl args _) -> matchArgs (getArgs a venv) args
    _ -> False
checkStmt (SAssgn v e) venv fenv =
  let t = varType v venv
      et = exprType e venv
   in t == et && t /= Error
checkStmt (SAssgnF v i) venv fenv =
  let t = varType v venv
   in case Map.lookup i fenv of
        Just (FDecl args ret) ->
          matchArgs [] args && case ret of
            Return _ t' -> t == SType t'
            Void -> False
        _ -> False
checkStmt (SAssgnFA v i a) venv fenv =
  let t = varType v venv
   in case Map.lookup i fenv of
        Just (FDecl args ret) ->
          matchArgs (getArgs a venv) args && case ret of
            Return _ t' -> t == SType t'
            Void -> False
        _ -> False
checkStmt (SDel e i) venv fenv =
  let et = exprType e venv
      t = varType (VId i) venv
   in case (et, t) of
        (SType Int, CType (Dict _)) -> True
        _ -> False
checkStmt (SIfte e s1 s2) venv fenv =
  exprType e venv == SType Bool && checkStmt s1 venv fenv && checkStmt s2 venv fenv
checkStmt (SIfend e s) venv fenv =
  exprType e venv == SType Bool && checkStmt s venv fenv
checkStmt (SWhile e s) venv fenv =
  exprType e venv == SType Bool && checkStmt s venv fenv
checkStmt (SFor i e1 e2 s) venv fenv =
  let t1 = exprType e1 venv
      t2 = exprType e2 venv
      venv' = Map.insert i (SType Int) venv
   in t1 == SType Int && t2 == SType Int && checkStmt s venv' fenv
checkStmt (SForKeys i i' s) venv fenv =
  let t = underType (varType (VId i') venv)
      venv' = Map.insert i (SType Int) venv
   in t /= Error && checkStmt s venv' fenv
checkStmt (SForVals i i' s) venv fenv =
  let t = underType (varType (VId i') venv)
      venv' = Map.insert i t venv
   in t /= Error && checkStmt s venv' fenv
checkStmt (SForPairs i1 i2 i' s) venv fenv =
  let t = underType (varType (VId i') venv)
      venv' = Map.insert i1 (SType Int) (Map.insert i2 t venv)
   in t /= Error && checkStmt s venv' fenv
checkStmt (SPrint i) venv fenv = varType (VId i) venv /= Error
checkStmt (SBlock d s) venv fenv =
  case declare d venv fenv of
    Env venv' fenv -> checkStmt s venv' fenv
    DError -> False
checkStmt (STry s1 s2) venv fenv = checkStmt s1 venv fenv && checkStmt s2 venv fenv
checkStmt (SSeq s1 s2) venv fenv = checkStmt s1 venv fenv && checkStmt s2 venv fenv

venv0 :: VEnv
venv0 = Map.fromList [(Ident "i", SType Int), (Ident "b", SType Bool), (Ident "a", CType (Array Int)), (Ident "d", CType (Dict Bool))]

fenv0 :: FEnv
fenv0 = Map.empty

checkProg :: Prog -> Bool
checkProg (Prog stmt) = checkStmt stmt venv0 fenv0
