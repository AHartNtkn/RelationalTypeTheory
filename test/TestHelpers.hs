{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module TestHelpers
  ( PositionInsensitive (..),
    simpleParamInfo,
    simpleTermMacro,
    simpleRelMacro,
  )
where

import Core.Syntax
import Control.Monad (unless)
import Test.Hspec ( expectationFailure, Expectation )
import Text.Megaparsec (initialPos, SourcePos)

-- | Dummy position for position-insensitive comparison
dummyPos :: SourcePos
dummyPos = initialPos ""

-- | Position-stripping utility functions for true position-insensitive comparison

stripTermPos :: Term -> Term
stripTermPos term = case term of
  Var name idx _ -> Var name idx dummyPos
  FVar name _ -> FVar name dummyPos
  Lam name body _ -> Lam name (stripTermPos body) dummyPos
  App f x _ -> App (stripTermPos f) (stripTermPos x) dummyPos
  TMacro name args _ -> TMacro name (map stripMacroArgPos args) dummyPos

stripRTypePos :: RType -> RType
stripRTypePos rtype = case rtype of
  RVar name idx _ -> RVar name idx dummyPos
  FRVar name _ -> FRVar name dummyPos
  RMacro name args _ -> RMacro name (map stripMacroArgPos args) dummyPos
  Arr arg res _ -> Arr (stripRTypePos arg) (stripRTypePos res) dummyPos
  All name body _ -> All name (stripRTypePos body) dummyPos
  Conv r _ -> Conv (stripRTypePos r) dummyPos
  Comp r s _ -> Comp (stripRTypePos r) (stripRTypePos s) dummyPos
  Prom t _ -> Prom (stripTermPos t) dummyPos

stripProofPos :: Proof -> Proof
stripProofPos proof = case proof of
  PVar name idx _ -> PVar name idx dummyPos
  FPVar name _ -> FPVar name dummyPos
  PTheoremApp name args _ -> PTheoremApp name (map stripTheoremArgPos args) dummyPos
  LamP name rtype body _ -> LamP name (stripRTypePos rtype) (stripProofPos body) dummyPos
  AppP f x _ -> AppP (stripProofPos f) (stripProofPos x) dummyPos
  TyApp p r _ -> TyApp (stripProofPos p) (stripRTypePos r) dummyPos
  TyLam name body _ -> TyLam name (stripProofPos body) dummyPos
  ConvProof t1 p t2 _ -> ConvProof (stripTermPos t1) (stripProofPos p) (stripTermPos t2) dummyPos
  ConvIntro p _ -> ConvIntro (stripProofPos p) dummyPos
  ConvElim p _ -> ConvElim (stripProofPos p) dummyPos
  Iota t1 t2 _ -> Iota (stripTermPos t1) (stripTermPos t2) dummyPos
  RhoElim name t1 t2 p1 p2 _ -> RhoElim name (stripTermPos t1) (stripTermPos t2) (stripProofPos p1) (stripProofPos p2) dummyPos
  Pair p1 p2 _ -> Pair (stripProofPos p1) (stripProofPos p2) dummyPos
  Pi p name1 name2 name3 q _ -> Pi (stripProofPos p) name1 name2 name3 (stripProofPos q) dummyPos
  PMacro name args _ -> PMacro name (map stripMacroArgPos args) dummyPos

stripMacroArgPos :: MacroArg -> MacroArg
stripMacroArgPos arg = case arg of
  MTerm t -> MTerm (stripTermPos t)
  MRel r -> MRel (stripRTypePos r)
  MProof p -> MProof (stripProofPos p)

stripTheoremArgPos :: TheoremArg -> TheoremArg
stripTheoremArgPos arg = case arg of
  TermArg t -> TermArg (stripTermPos t)
  RelArg r -> RelArg (stripRTypePos r)
  ProofArg p -> ProofArg (stripProofPos p)

stripJudgmentPos :: RelJudgment -> RelJudgment
stripJudgmentPos (RelJudgment t1 r t2) = 
  RelJudgment (stripTermPos t1) (stripRTypePos r) (stripTermPos t2)

stripDeclarationPos :: Declaration -> Declaration
stripDeclarationPos decl = case decl of
  MacroDef name params body -> MacroDef name params (stripMacroBodyPos body)
  TheoremDef name bindings judgment proof -> 
    TheoremDef name bindings (stripJudgmentPos judgment) (stripProofPos proof)
  ImportDecl imp -> ImportDecl imp
  ExportDecl expDecl -> ExportDecl expDecl  
  FixityDecl fixity name -> FixityDecl fixity name

stripMacroBodyPos :: MacroBody -> MacroBody
stripMacroBodyPos body = case body of
  TermMacro t -> TermMacro (stripTermPos t)
  RelMacro r -> RelMacro (stripRTypePos r)
  ProofMacro p -> ProofMacro (stripProofPos p)

-- Helper type class for position-insensitive comparison
class PositionInsensitive a where
  shouldBeEqual :: a -> a -> Expectation

instance PositionInsensitive Term where
  shouldBeEqual actual expected = 
    unless (stripTermPos actual == stripTermPos expected) $
      expectationFailure $
        "Terms not equal (ignoring positions):\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive RType where
  shouldBeEqual actual expected = 
    unless (stripRTypePos actual == stripRTypePos expected) $
      expectationFailure $
        "RTypes not equal (ignoring positions):\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive Proof where
  shouldBeEqual actual expected = 
    unless (stripProofPos actual == stripProofPos expected) $
      expectationFailure $
        "Proofs not equal (ignoring positions):\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive Declaration where
  shouldBeEqual actual expected = 
    unless (stripDeclarationPos actual == stripDeclarationPos expected) $
      expectationFailure $
        "Declarations not equal (ignoring positions):\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive RelJudgment where
  shouldBeEqual actual expected =
    unless (stripJudgmentPos actual == stripJudgmentPos expected) $
      expectationFailure $
        "RelJudgments not equal (ignoring positions):\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance (PositionInsensitive a) => PositionInsensitive [a] where
  shouldBeEqual [] [] = return ()
  shouldBeEqual (x : xs) (y : ys) = do
    shouldBeEqual x y
    shouldBeEqual xs ys
  shouldBeEqual actual expected =
    expectationFailure $ "Lists have different lengths:\nExpected: " ++ show (length expected) ++ " elements\nActual: " ++ show (length actual) ++ " elements"



-- | Helper functions for creating test macro signatures
simpleParamInfo :: String -> VarKind -> ParamInfo
simpleParamInfo name kind = ParamInfo name kind False []

-- | Create a simple term macro sig for testing
simpleTermMacro :: [String] -> Term -> MacroSig
simpleTermMacro params body = ([simpleParamInfo p TermK | p <- params], TermMacro body)

-- | Create a simple rel macro sig for testing
simpleRelMacro :: [String] -> RType -> MacroSig
simpleRelMacro params body = ([simpleParamInfo p RelK | p <- params], RelMacro body)

