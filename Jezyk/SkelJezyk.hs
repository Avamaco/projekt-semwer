-- File generated by the BNF Converter (bnfc 2.9.5).

-- Templates for pattern matching on abstract syntax

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module SkelJezyk where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified AbsJezyk

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: AbsJezyk.Ident -> Result
transIdent x = case x of
  AbsJezyk.Ident string -> failure x

transVar :: AbsJezyk.Var -> Result
transVar x = case x of
  AbsJezyk.VId ident -> failure x
  AbsJezyk.VAt ident expr -> failure x

transArg :: AbsJezyk.Arg -> Result
transArg x = case x of
  AbsJezyk.AId ident -> failure x
  AbsJezyk.ASeq ident arg -> failure x

transStmt :: AbsJezyk.Stmt -> Result
transStmt x = case x of
  AbsJezyk.SCall ident -> failure x
  AbsJezyk.SCallA ident arg -> failure x
  AbsJezyk.SAssgn var expr -> failure x
  AbsJezyk.SAssgnF var ident -> failure x
  AbsJezyk.SAssgnFA var ident arg -> failure x
  AbsJezyk.SDel expr ident -> failure x
  AbsJezyk.SIfte bexpr stmt1 stmt2 -> failure x
  AbsJezyk.SIfend bexpr stmt -> failure x
  AbsJezyk.SWhile bexpr stmt -> failure x
  AbsJezyk.SFor ident expr1 expr2 stmt -> failure x
  AbsJezyk.SForKeys ident1 ident2 stmt -> failure x
  AbsJezyk.SForVals ident1 ident2 stmt -> failure x
  AbsJezyk.SForPairs ident1 ident2 ident3 stmt -> failure x
  AbsJezyk.SPrint ident -> failure x
  AbsJezyk.SBlock decl stmt -> failure x
  AbsJezyk.STry stmt1 stmt2 -> failure x
  AbsJezyk.SSeq stmt1 stmt2 -> failure x

transBExpr :: AbsJezyk.BExpr -> Result
transBExpr x = case x of
  AbsJezyk.BAnd bexpr1 bexpr2 -> failure x
  AbsJezyk.BOr bexpr1 bexpr2 -> failure x
  AbsJezyk.BNot bexpr -> failure x
  AbsJezyk.BEq expr1 expr2 -> failure x
  AbsJezyk.BLt expr1 expr2 -> failure x
  AbsJezyk.BLeq expr1 expr2 -> failure x
  AbsJezyk.BGt expr1 expr2 -> failure x
  AbsJezyk.BGeq expr1 expr2 -> failure x
  AbsJezyk.BNeq expr1 expr2 -> failure x
  AbsJezyk.BTrue -> failure x
  AbsJezyk.BFalse -> failure x
  AbsJezyk.BCheck expr ident -> failure x

transExpr :: AbsJezyk.Expr -> Result
transExpr x = case x of
  AbsJezyk.EPlus expr1 expr2 -> failure x
  AbsJezyk.EMinus expr1 expr2 -> failure x
  AbsJezyk.EMul expr1 expr2 -> failure x
  AbsJezyk.EDiv expr1 expr2 -> failure x
  AbsJezyk.ENeg expr -> failure x
  AbsJezyk.ENum integer -> failure x
  AbsJezyk.EVar ident -> failure x
  AbsJezyk.Etern expr1 expr2 expr3 -> failure x

transType :: AbsJezyk.Type -> Result
transType x = case x of
  AbsJezyk.TBool -> failure x
  AbsJezyk.TInt -> failure x

transCType :: AbsJezyk.CType -> Result
transCType x = case x of
  AbsJezyk.CTArray integer type_ -> failure x
  AbsJezyk.CTDict type_ -> failure x

transADecl :: AbsJezyk.ADecl -> Result
transADecl x = case x of
  AbsJezyk.ADId ident type_ -> failure x
  AbsJezyk.ADSeq ident type_ adecl -> failure x

transFDecl :: AbsJezyk.FDecl -> Result
transFDecl x = case x of
  AbsJezyk.FDVoid -> failure x
  AbsJezyk.FDRet ident type_ -> failure x
  AbsJezyk.FDArg adecl -> failure x
  AbsJezyk.FDFull adecl ident type_ -> failure x

transDecl :: AbsJezyk.Decl -> Result
transDecl x = case x of
  AbsJezyk.DSimple ident type_ -> failure x
  AbsJezyk.DComplex ident ctype -> failure x
  AbsJezyk.DFunction ident fdecl stmt -> failure x
  AbsJezyk.DSeq decl1 decl2 -> failure x
