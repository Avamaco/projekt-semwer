module Main where

import Prelude

import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )

import Data.Map
import qualified GHC.Integer (leInteger) 


import Jezyk.Abs ( Expr(..), BExpr(..), Stmt(..), Ident(..) )
import Jezyk.Lex   ( Token, mkPosToken )
import Jezyk.Par   ( pExpr, pBExpr, pStmt, myLexer )
import Jezyk.Print ( Print, printTree )
import Jezyk.Skel  ()

mapGet :: (Ord k) => (Map k v) -> k -> v
mapGet map arg = map ! arg

mapSet :: (Ord k) => (Map k v) -> k -> v -> (Map k v)
mapSet map arg val = insert arg val map


type Loc = Integer
type Var = String

type VEnv = Map Var Loc
data Store = CStore {currMap :: Map Loc Integer, nextLoc :: Loc} deriving Show
type Cont = Store -> Store

{--
===
  data Store = CStore (Map.Map Loc Integer) Loc
  
  CStore :: (Map Loc Integer) -> Loc -> Store
  currMap :: Store -> (Map.Map Loc Integer)
  nextLoc :: Store -> Loc
--}

newloc:: Store -> (Loc, Store)
newloc (CStore map loc) = (loc, CStore map (loc + 1))

getVar:: VEnv -> Store -> Var -> Integer
getVar rhoV sto var =
  let loc = mapGet rhoV var in
    mapGet (currMap sto) loc

setVar:: VEnv -> Store -> Var -> Integer -> Store
setVar rhoV sto var val =
  let loc = mapGet rhoV var in
  let map = mapSet (currMap sto) loc val in
    CStore map (nextLoc sto)

-- Semantics of expressions
eE :: Expr -> VEnv -> Store -> Integer

eE (EPlus exp0 exp1) rhoV sto = (eE exp0 rhoV sto) + (eE exp1 rhoV sto) 
eE (EMinus exp0 exp1) rhoV sto = (eE exp0 rhoV sto) - (eE exp1 rhoV sto)
eE (EMul  exp0 exp1) rhoV sto = (eE exp0 rhoV sto) * (eE exp1 rhoV sto)
eE (ENum n) rhoV sto = n
eE (EVar (Ident x)) rhoV sto = getVar rhoV sto x

-- Semantics of boolean expressions
eB :: BExpr -> VEnv -> Store -> Bool

eB (BAnd bexp0 bexp1) rhoV sto = (eB bexp0 rhoV sto) && (eB bexp1 rhoV sto)

eB (BLeq exp0 exp1) rhoV sto = GHC.Integer.leInteger (eE exp0 rhoV sto) (eE exp1 rhoV sto)
{--
  BNot bexp  -> not $ eB bexp st
  BLeq exp0 exp  -> GHC.Integer.leInteger (eE exp0 st) (eE exp st)
  BTrue  -> True
  BFalse -> False
  --}


-- Semantics of statements
iS :: Stmt -> VEnv -> Cont -> Cont -> Cont -> Cont

iS (SAssgn (Ident var) expr) rhoV k1 k2 k3 = k3

iS (SSkip) rhoV k1 k2 k3 = k3

iS (SIf bex i1 i2) rhoV k1 k2 k3 = k3
                          
iS (SWhile bex i) rhoV k1 k2 k3 = k3
    
iS (SSeq i1 i2) rhoV k1 k2 k3 = k3

iS (SBreak) rhoV k1 k2 k3 = k3

iS (SContinue) rhoV k1 k2 k3 = k3



main :: IO ()
main = do
    getContents >>= compute
    putStrLn ""

rhoV0:: VEnv
rhoV0 = fromList [("x", 0), ("y", 1), ("z", 2)]

sto0 :: Store
sto0 = CStore (fromList [(0, 3), (1, 2), (2, 3)]) 3

cont0 :: Cont
cont0 = \s -> s

compute s =
    case pStmt (myLexer s) of
        Left err -> do
            putStrLn "\nParse              Failed...\n"
            putStrLn err
            exitFailure
        Right e -> do
            putStrLn "\nParse Successful!"
            putStrLn $ show (iS e rhoV0 cont0 cont0 cont0 sto0)
