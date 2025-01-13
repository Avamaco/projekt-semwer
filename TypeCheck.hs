module TypeCheck where

import Data.Map (Map)
import Data.Map qualified as Map
import Jezyk.Abs (Ident (..))
import Jezyk.Abs qualified as Abs (CType (..), Expr (..), Type (..), Var (..))

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

assertType :: Abs.Expr -> Abs.Expr -> VEnv -> Type -> Type -> Type
assertType e1 e2 venv t rt =
  let t1 = exprType e1 venv
      t2 = exprType e2 venv
   in if t1 == t && t2 == t then rt else Error

varType :: Abs.Var -> VEnv -> Type
varType (Abs.VId i) venv = Map.findWithDefault Error i venv
varType (Abs.VAt i e) venv =
  let t = Map.findWithDefault Error i venv
      et = exprType e venv
      ut = underType t
   in if et == SType Int then ut else Error

exprType :: Abs.Expr -> VEnv -> Type
exprType Abs.ETrue _ = SType Bool
exprType Abs.EFalse _ = SType Bool
exprType (Abs.ENum _) _ = SType Int
exprType (Abs.EVar (Abs.VId i)) venv = Map.findWithDefault Error i venv
exprType (Abs.EVar (Abs.VAt i e)) venv =
  let t = Map.findWithDefault Error i venv
      et = exprType e venv
      ut = underType t
   in if et == SType Int then ut else Error
exprType (Abs.EPlus e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (Abs.EMinus e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (Abs.EMul e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (Abs.EDiv e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Int)
exprType (Abs.ENeg e) venv = assertType e e venv (SType Int) (SType Int)
exprType (Abs.EEq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (Abs.ELt e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (Abs.EGt e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (Abs.ELeq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (Abs.EGeq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (Abs.ENeq e1 e2) venv = assertType e1 e2 venv (SType Int) (SType Bool)
exprType (Abs.EAnd e1 e2) venv = assertType e1 e2 venv (SType Bool) (SType Bool)
exprType (Abs.EOr e1 e2) venv = assertType e1 e2 venv (SType Bool) (SType Bool)
exprType (Abs.ENot e) venv = assertType e e venv (SType Bool) (SType Bool)
exprType (Abs.ETern e e1 e2) venv =
  let t = exprType e venv
      t1 = exprType e1 venv
      t2 = exprType e2 venv
   in if t == SType Bool && t1 == t2 then t1 else Error
exprType (Abs.ECheck e (Ident i)) venv =
  let et = exprType e venv
      t = Map.findWithDefault Error (Ident i) venv
   in case (et, t) of
        (SType Int, CType _) -> SType Bool
        _ -> Error

venv0 = Map.fromList [(Ident "x", SType Int), (Ident "y", CType (Array Bool))]

typifyExpr :: Abs.Expr -> Type
typifyExpr expr = exprType expr venv0
