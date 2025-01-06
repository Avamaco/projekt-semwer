-- File generated by the BNF Converter (bnfc 2.9.5).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for PrintJezyk.

module PrintJezyk where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsJezyk

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t, null spc, null rest) of
      (True , _   , True ) -> []             -- remove trailing space
      (False, _   , True ) -> t              -- remove trailing space
      (False, True, False) -> t ++ ' ' : s   -- add space if none
      _                    -> t ++ s
    where
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print AbsJezyk.Ident where
  prt _ (AbsJezyk.Ident i) = doc $ showString i
instance Print AbsJezyk.Var where
  prt i = \case
    AbsJezyk.VId id_ -> prPrec i 0 (concatD [prt 0 id_])
    AbsJezyk.VAt id_ expr -> prPrec i 0 (concatD [prt 0 id_, doc (showString "at"), prt 0 expr])

instance Print AbsJezyk.Arg where
  prt i = \case
    AbsJezyk.AId id_ -> prPrec i 0 (concatD [prt 0 id_])
    AbsJezyk.ASeq id_ arg -> prPrec i 0 (concatD [prt 0 id_, doc (showString ","), prt 0 arg])

instance Print AbsJezyk.Stmt where
  prt i = \case
    AbsJezyk.SCall id_ -> prPrec i 0 (concatD [doc (showString "call"), prt 0 id_])
    AbsJezyk.SCallA id_ arg -> prPrec i 0 (concatD [doc (showString "call"), prt 0 id_, doc (showString "with"), prt 0 arg])
    AbsJezyk.SAssgn var expr -> prPrec i 1 (concatD [doc (showString "set"), prt 0 var, doc (showString "to"), prt 0 expr])
    AbsJezyk.SAssgnF var id_ -> prPrec i 1 (concatD [doc (showString "set"), prt 0 var, doc (showString "to"), doc (showString "call"), prt 0 id_])
    AbsJezyk.SAssgnFA var id_ arg -> prPrec i 1 (concatD [doc (showString "set"), prt 0 var, doc (showString "to"), doc (showString "call"), prt 0 id_, doc (showString "with"), prt 0 arg])
    AbsJezyk.SDel expr id_ -> prPrec i 1 (concatD [doc (showString "del"), prt 0 expr, doc (showString "from"), prt 0 id_])
    AbsJezyk.SIfte bexpr stmt1 stmt2 -> prPrec i 2 (concatD [doc (showString "if"), prt 0 bexpr, doc (showString "then"), prt 0 stmt1, doc (showString "else"), prt 0 stmt2, doc (showString "end")])
    AbsJezyk.SIfend bexpr stmt -> prPrec i 2 (concatD [doc (showString "if"), prt 0 bexpr, doc (showString "then"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.SWhile bexpr stmt -> prPrec i 2 (concatD [doc (showString "while"), prt 0 bexpr, doc (showString "do"), prt 1 stmt])
    AbsJezyk.SFor id_ expr1 expr2 stmt -> prPrec i 2 (concatD [doc (showString "for"), prt 0 id_, doc (showString "from"), prt 0 expr1, doc (showString "to"), prt 0 expr2, doc (showString "do"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.SForKeys id_1 id_2 stmt -> prPrec i 2 (concatD [doc (showString "for"), prt 0 id_1, doc (showString "in"), doc (showString "keys"), prt 0 id_2, doc (showString "do"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.SForVals id_1 id_2 stmt -> prPrec i 2 (concatD [doc (showString "for"), prt 0 id_1, doc (showString "in"), doc (showString "values"), prt 0 id_2, doc (showString "do"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.SForPairs id_1 id_2 id_3 stmt -> prPrec i 2 (concatD [doc (showString "for"), prt 0 id_1, doc (showString ","), prt 0 id_2, doc (showString "in"), prt 0 id_3, doc (showString "do"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.SPrint id_ -> prPrec i 0 (concatD [doc (showString "print"), prt 0 id_])
    AbsJezyk.SBlock decl stmt -> prPrec i 0 (concatD [doc (showString "begin"), prt 0 decl, doc (showString ";"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.STry stmt1 stmt2 -> prPrec i 0 (concatD [doc (showString "try"), prt 0 stmt1, doc (showString "catch"), prt 0 stmt2, doc (showString "end")])
    AbsJezyk.SSeq stmt1 stmt2 -> prPrec i 0 (concatD [prt 1 stmt1, doc (showString ";"), prt 0 stmt2])

instance Print AbsJezyk.BExpr where
  prt i = \case
    AbsJezyk.BAnd bexpr1 bexpr2 -> prPrec i 0 (concatD [prt 0 bexpr1, doc (showString "&"), prt 1 bexpr2])
    AbsJezyk.BOr bexpr1 bexpr2 -> prPrec i 0 (concatD [prt 0 bexpr1, doc (showString "|"), prt 1 bexpr2])
    AbsJezyk.BNot bexpr -> prPrec i 1 (concatD [doc (showString "!"), prt 1 bexpr])
    AbsJezyk.BEq expr1 expr2 -> prPrec i 1 (concatD [prt 0 expr1, doc (showString "="), prt 0 expr2])
    AbsJezyk.BLt expr1 expr2 -> prPrec i 1 (concatD [prt 0 expr1, doc (showString "<"), prt 0 expr2])
    AbsJezyk.BLeq expr1 expr2 -> prPrec i 1 (concatD [prt 0 expr1, doc (showString "<="), prt 0 expr2])
    AbsJezyk.BGt expr1 expr2 -> prPrec i 1 (concatD [prt 0 expr1, doc (showString ">"), prt 0 expr2])
    AbsJezyk.BGeq expr1 expr2 -> prPrec i 1 (concatD [prt 0 expr1, doc (showString ">="), prt 0 expr2])
    AbsJezyk.BNeq expr1 expr2 -> prPrec i 1 (concatD [prt 0 expr1, doc (showString "!="), prt 0 expr2])
    AbsJezyk.BTrue -> prPrec i 1 (concatD [doc (showString "true")])
    AbsJezyk.BFalse -> prPrec i 1 (concatD [doc (showString "false")])
    AbsJezyk.BCheck expr id_ -> prPrec i 0 (concatD [doc (showString "check"), prt 0 expr, doc (showString "in"), prt 0 id_])

instance Print AbsJezyk.Expr where
  prt i = \case
    AbsJezyk.EPlus expr1 expr2 -> prPrec i 0 (concatD [prt 0 expr1, doc (showString "+"), prt 1 expr2])
    AbsJezyk.EMinus expr1 expr2 -> prPrec i 0 (concatD [prt 0 expr1, doc (showString "-"), prt 1 expr2])
    AbsJezyk.EMul expr1 expr2 -> prPrec i 1 (concatD [prt 1 expr1, doc (showString "*"), prt 2 expr2])
    AbsJezyk.EDiv expr1 expr2 -> prPrec i 1 (concatD [prt 1 expr1, doc (showString "/"), prt 2 expr2])
    AbsJezyk.ENeg expr -> prPrec i 0 (concatD [doc (showString "-"), prt 0 expr])
    AbsJezyk.ENum n -> prPrec i 2 (concatD [prt 0 n])
    AbsJezyk.EVar id_ -> prPrec i 2 (concatD [prt 0 id_])
    AbsJezyk.Etern expr1 expr2 expr3 -> prPrec i 0 (concatD [prt 0 expr1, doc (showString "?"), prt 0 expr2, doc (showString ":"), prt 0 expr3])

instance Print AbsJezyk.Type where
  prt i = \case
    AbsJezyk.TBool -> prPrec i 0 (concatD [doc (showString "bool")])
    AbsJezyk.TInt -> prPrec i 0 (concatD [doc (showString "int")])

instance Print AbsJezyk.CType where
  prt i = \case
    AbsJezyk.CTArray n type_ -> prPrec i 0 (concatD [doc (showString "array"), doc (showString "of"), prt 0 n, prt 0 type_])
    AbsJezyk.CTDict type_ -> prPrec i 0 (concatD [doc (showString "dict"), doc (showString "of"), prt 0 type_])

instance Print AbsJezyk.ADecl where
  prt i = \case
    AbsJezyk.ADId id_ type_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString "of"), prt 0 type_])
    AbsJezyk.ADSeq id_ type_ adecl -> prPrec i 0 (concatD [prt 0 id_, doc (showString "of"), prt 0 type_, doc (showString ","), prt 0 adecl])

instance Print AbsJezyk.FDecl where
  prt i = \case
    AbsJezyk.FDVoid -> prPrec i 0 (concatD [doc (showString "fun"), doc (showString "to"), doc (showString "void")])
    AbsJezyk.FDRet id_ type_ -> prPrec i 0 (concatD [doc (showString "fun"), doc (showString "to"), prt 0 id_, doc (showString "of"), prt 0 type_])
    AbsJezyk.FDArg adecl -> prPrec i 0 (concatD [doc (showString "fun"), doc (showString "from"), prt 0 adecl, doc (showString "to"), doc (showString "void")])
    AbsJezyk.FDFull adecl id_ type_ -> prPrec i 0 (concatD [doc (showString "fun"), doc (showString "from"), prt 0 adecl, doc (showString "to"), prt 0 id_, doc (showString "of"), prt 0 type_])

instance Print AbsJezyk.Decl where
  prt i = \case
    AbsJezyk.DSimple id_ type_ -> prPrec i 1 (concatD [doc (showString "let"), prt 0 id_, doc (showString "be"), prt 0 type_])
    AbsJezyk.DComplex id_ ctype -> prPrec i 1 (concatD [doc (showString "let"), prt 0 id_, doc (showString "be"), prt 0 ctype])
    AbsJezyk.DFunction id_ fdecl stmt -> prPrec i 1 (concatD [doc (showString "elt"), prt 0 id_, doc (showString "be"), prt 0 fdecl, doc (showString "do"), prt 0 stmt, doc (showString "end")])
    AbsJezyk.DSeq decl1 decl2 -> prPrec i 0 (concatD [prt 1 decl1, doc (showString ";"), prt 0 decl2])