{-# LANGUAGE FlexibleInstances #-}

module TestHelpers
  ( PositionInsensitive (..),
    equalTerm,
    equalRType,
    equalProof,
    equalDeclaration,
    equalMacroBody,
    equalRelJudgment,
    equalBinding,
    shouldBeEqualTerm,
    shouldBeEqualRType,
    shouldBeEqualProof,
    shouldBeEqualDeclaration,
    buildContextFromBindings,
  )
where

import Context
import Control.Monad (unless)
import Lib
import Test.Hspec
import Text.Megaparsec (initialPos)

-- Helper functions for position-insensitive equality
equalTerm :: Term -> Term -> Bool
equalTerm (Var n1 i1 _) (Var n2 i2 _) = n1 == n2 && i1 == i2
equalTerm (Lam n1 t1 _) (Lam n2 t2 _) = n1 == n2 && equalTerm t1 t2
equalTerm (App t1 u1 _) (App t2 u2 _) = equalTerm t1 t2 && equalTerm u1 u2
equalTerm (TMacro n1 ts1 _) (TMacro n2 ts2 _) = n1 == n2 && length ts1 == length ts2 && all (uncurry equalTerm) (zip ts1 ts2)
equalTerm _ _ = False

equalRType :: RType -> RType -> Bool
equalRType (RVar n1 i1 _) (RVar n2 i2 _) = n1 == n2 && i1 == i2
equalRType (RMacro n1 ts1 _) (RMacro n2 ts2 _) = n1 == n2 && length ts1 == length ts2 && all (uncurry equalRType) (zip ts1 ts2)
equalRType (Arr r1 s1 _) (Arr r2 s2 _) = equalRType r1 r2 && equalRType s1 s2
equalRType (All n1 r1 _) (All n2 r2 _) = n1 == n2 && equalRType r1 r2
equalRType (Comp r1 s1 _) (Comp r2 s2 _) = equalRType r1 r2 && equalRType s1 s2
equalRType (Conv r1 _) (Conv r2 _) = equalRType r1 r2
equalRType (Prom t1 _) (Prom t2 _) = equalTerm t1 t2
equalRType _ _ = False

equalProof :: Proof -> Proof -> Bool
equalProof (PVar n1 i1 _) (PVar n2 i2 _) = n1 == n2 && i1 == i2
equalProof (PTheoremApp n1 args1 _) (PTheoremApp n2 args2 _) = n1 == n2 && args1 == args2
equalProof (LamP n1 r1 p1 _) (LamP n2 r2 p2 _) = n1 == n2 && equalRType r1 r2 && equalProof p1 p2
equalProof (AppP p1 q1 _) (AppP p2 q2 _) = equalProof p1 p2 && equalProof q1 q2
equalProof (TyApp p1 r1 _) (TyApp p2 r2 _) = equalProof p1 p2 && equalRType r1 r2
equalProof (TyLam n1 p1 _) (TyLam n2 p2 _) = n1 == n2 && equalProof p1 p2
equalProof (ConvProof t1 p1 u1 _) (ConvProof t2 p2 u2 _) = equalTerm t1 t2 && equalProof p1 p2 && equalTerm u1 u2
equalProof (ConvIntro p1 _) (ConvIntro p2 _) = equalProof p1 p2
equalProof (ConvElim p1 _) (ConvElim p2 _) = equalProof p1 p2
equalProof (RhoElim n1 t1 u1 p1 q1 _) (RhoElim n2 t2 u2 p2 q2 _) =
  n1 == n2 && equalTerm t1 t2 && equalTerm u1 u2 && equalProof p1 p2 && equalProof q1 q2
equalProof (Pi p1 n1 m1 o1 q1 _) (Pi p2 n2 m2 o2 q2 _) =
  equalProof p1 p2 && n1 == n2 && m1 == m2 && o1 == o2 && equalProof q1 q2
equalProof (Iota t1 u1 _) (Iota t2 u2 _) = equalTerm t1 t2 && equalTerm u1 u2
equalProof (Pair p1 q1 _) (Pair p2 q2 _) = equalProof p1 p2 && equalProof q1 q2
equalProof _ _ = False

equalDeclaration :: Declaration -> Declaration -> Bool
equalDeclaration (MacroDef n1 ps1 b1) (MacroDef n2 ps2 b2) =
  n1 == n2 && ps1 == ps2 && equalMacroBody b1 b2
equalDeclaration (TheoremDef n1 bs1 rj1 p1) (TheoremDef n2 bs2 rj2 p2) =
  n1 == n2 && length bs1 == length bs2 && all (uncurry equalBinding) (zip bs1 bs2) && equalRelJudgment rj1 rj2 && equalProof p1 p2
equalDeclaration (ImportDecl i1) (ImportDecl i2) = i1 == i2
equalDeclaration (ExportDecl e1) (ExportDecl e2) = e1 == e2
equalDeclaration (FixityDecl f1 n1) (FixityDecl f2 n2) = f1 == f2 && n1 == n2
equalDeclaration _ _ = False

equalMacroBody :: MacroBody -> MacroBody -> Bool
equalMacroBody (TermMacro t1) (TermMacro t2) = equalTerm t1 t2
equalMacroBody (RelMacro r1) (RelMacro r2) = equalRType r1 r2
equalMacroBody _ _ = False

equalRelJudgment :: RelJudgment -> RelJudgment -> Bool
equalRelJudgment (RelJudgment t1 r1 u1) (RelJudgment t2 r2 u2) =
  equalTerm t1 t2 && equalRType r1 r2 && equalTerm u1 u2

equalBinding :: Binding -> Binding -> Bool
equalBinding (TermBinding n1) (TermBinding n2) = n1 == n2
equalBinding (RelBinding n1) (RelBinding n2) = n1 == n2
equalBinding (ProofBinding n1 rj1) (ProofBinding n2 rj2) = n1 == n2 && equalRelJudgment rj1 rj2
equalBinding _ _ = False

-- Custom shouldBe functions for position-insensitive comparison
shouldBeEqualTerm :: Term -> Term -> Expectation
shouldBeEqualTerm actual expected =
  unless (equalTerm actual expected) $
    expectationFailure $
      "Terms not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

shouldBeEqualRType :: RType -> RType -> Expectation
shouldBeEqualRType actual expected =
  unless (equalRType actual expected) $
    expectationFailure $
      "RTypes not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

shouldBeEqualProof :: Proof -> Proof -> Expectation
shouldBeEqualProof actual expected =
  unless (equalProof actual expected) $
    expectationFailure $
      "Proofs not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

shouldBeEqualDeclaration :: Declaration -> Declaration -> Expectation
shouldBeEqualDeclaration actual expected =
  unless (equalDeclaration actual expected) $
    expectationFailure $
      "Declarations not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

-- Helper type class for position-insensitive comparison
class PositionInsensitive a where
  shouldBeEqual :: a -> a -> Expectation

instance PositionInsensitive Term where
  shouldBeEqual = shouldBeEqualTerm

instance PositionInsensitive RType where
  shouldBeEqual = shouldBeEqualRType

instance PositionInsensitive Proof where
  shouldBeEqual = shouldBeEqualProof

instance PositionInsensitive Declaration where
  shouldBeEqual = shouldBeEqualDeclaration

instance PositionInsensitive RelJudgment where
  shouldBeEqual rj1 rj2 =
    unless (equalRelJudgment rj1 rj2) $
      expectationFailure $
        "RelJudgments not structurally equal:\nExpected: " ++ show rj2 ++ "\nActual: " ++ show rj1

instance (PositionInsensitive a) => PositionInsensitive [a] where
  shouldBeEqual [] [] = return ()
  shouldBeEqual (x : xs) (y : ys) = do
    shouldBeEqual x y
    shouldBeEqual xs ys
  shouldBeEqual actual expected =
    expectationFailure $ "Lists have different lengths:\nExpected: " ++ show (length expected) ++ " elements\nActual: " ++ show (length actual) ++ " elements"

-- | Build typing context from parsed theorem bindings
buildContextFromBindings :: [Binding] -> TypingContext
buildContextFromBindings bindings = buildContext emptyTypingContext bindings
  where
    ip = initialPos "test"
    buildContext ctx [] = ctx
    buildContext ctx (binding : rest) =
      case binding of
        TermBinding name ->
          let newCtx = extendTermContext name (RMacro "A" [] ip) ctx
           in buildContext newCtx rest
        RelBinding name ->
          let newCtx = extendRelContext name ctx
           in buildContext newCtx rest
        ProofBinding name judgment ->
          let newCtx = extendProofContext name judgment ctx
           in buildContext newCtx rest
