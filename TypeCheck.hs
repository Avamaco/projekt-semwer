module TypeCheck where

import Data.Map (Map)
import Data.Map qualified as Map
import Jezyk.Abs (Expr (..), Ident (..), Prog (..), Stmt (..), Var (..))
import Jezyk.Abs qualified as Abs (CType (..), Type (..))

data SType = Bool | Int deriving (Eq, Show)

data CType = Array SType | Dict SType deriving (Eq, Show)

data Type = SType SType | CType CType | Error deriving (Eq, Show)

type VEnv = Map Ident Type

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

checkStmt :: Stmt -> VEnv -> Bool
-- checkStmt (SCall {}) venv =
-- checkStmt (SCallA {}) venv =
checkStmt (SAssgn v e) venv =
  let t = varType v venv
      et = exprType e venv
   in t == et && t /= Error
-- checkStmt (SAssgnF {}) venv = False
-- checkStmt (SAssgnFA {}) venv = False
checkStmt (SDel e i) venv =
  let et = exprType e venv
      t = varType (VId i) venv
   in case (et, t) of
        (SType Int, CType (Dict _)) -> True
        _ -> False
checkStmt (SIfte e s1 s2) venv =
  exprType e venv == SType Bool && checkStmt s1 venv && checkStmt s2 venv
checkStmt (SIfend e s) venv =
  exprType e venv == SType Bool && checkStmt s venv
checkStmt (SWhile e s) venv =
  exprType e venv == SType Bool && checkStmt s venv
checkStmt (SFor i e1 e2 s) venv =
  let t1 = exprType e1 venv
      t2 = exprType e2 venv
      venv' = Map.insert i (SType Int) venv
   in t1 == SType Int && t2 == SType Int && checkStmt s venv'
checkStmt (SForKeys i i' s) venv =
  let t = underType (varType (VId i') venv)
      venv' = Map.insert i (SType Int) venv
   in t /= Error && checkStmt s venv'
checkStmt (SForVals i i' s) venv =
  let t = underType (varType (VId i') venv)
      venv' = Map.insert i t venv
   in t /= Error && checkStmt s venv'
checkStmt (SForPairs i1 i2 i' s) venv =
  let t = underType (varType (VId i') venv)
      venv' = Map.insert i1 (SType Int) (Map.insert i2 t venv)
   in t /= Error && checkStmt s venv'
checkStmt (SPrint i) venv = varType (VId i) venv /= Error
-- checkStmt (SBlock {}) venv =
checkStmt (STry s1 s2) venv = checkStmt s1 venv && checkStmt s2 venv
checkStmt (SSeq s1 s2) venv = checkStmt s1 venv && checkStmt s2 venv

venv0 :: VEnv
venv0 = Map.fromList [(Ident "x", SType Int), (Ident "y", CType (Dict Bool))]

checkProg :: Prog -> Bool
checkProg (Prog stmt) = checkStmt stmt venv0
