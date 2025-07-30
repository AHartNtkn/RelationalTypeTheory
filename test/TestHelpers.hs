{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module TestHelpers
  ( PositionInsensitive (..),
    shouldBeEqualProof,
    shouldBeEqualDeclaration,
    buildContextFromBindings,
    parseFileDeclarations,
    buildContextFromDeclarations,
    simpleParamInfo,
    simpleTermMacro,
    simpleRelMacro,
  )
where

import Core.Context
import Control.Monad (unless)
import Parser.Elaborate
import Core.Syntax
import Operations.Generic.Mixfix (defaultFixity)
import Operations.Generic.Macro (inferParamInfosG)
import qualified Core.Raw as Raw
import Parser.Raw (parseFile)
import Test.Hspec ( expectationFailure, Expectation )
import Text.Megaparsec (runParser, errorBundlePretty)


shouldBeEqualProof :: Proof -> Proof -> Expectation
shouldBeEqualProof actual expected =
  unless (actual == expected) $
    expectationFailure $
      "Proofs not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

shouldBeEqualDeclaration :: Declaration -> Declaration -> Expectation  
shouldBeEqualDeclaration actual expected =
  unless (actual == expected) $
    expectationFailure $
      "Declarations not structurally equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

-- Helper type class for position-insensitive comparison
class PositionInsensitive a where
  shouldBeEqual :: a -> a -> Expectation

instance PositionInsensitive Term where
  shouldBeEqual actual expected = 
    unless (actual == expected) $
      expectationFailure $
        "Terms not equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive RType where
  shouldBeEqual actual expected = 
    unless (actual == expected) $
      expectationFailure $
        "RTypes not equal:\nExpected: " ++ show expected ++ "\nActual: " ++ show actual

instance PositionInsensitive Proof where
  shouldBeEqual = shouldBeEqualProof

instance PositionInsensitive Declaration where
  shouldBeEqual = shouldBeEqualDeclaration

instance PositionInsensitive RelJudgment where
  shouldBeEqual rj1 rj2 =
    unless (rj1 == rj2) $
      expectationFailure $
        "RelJudgments not equal:\nExpected: " ++ show rj2 ++ "\nActual: " ++ show rj1

instance (PositionInsensitive a) => PositionInsensitive [a] where
  shouldBeEqual [] [] = return ()
  shouldBeEqual (x : xs) (y : ys) = do
    shouldBeEqual x y
    shouldBeEqual xs ys
  shouldBeEqual actual expected =
    expectationFailure $ "Lists have different lengths:\nExpected: " ++ show (length expected) ++ " elements\nActual: " ++ show (length actual) ++ " elements"


-- | Parse file content using new parser pipeline
parseFileDeclarations :: String -> Either String [Declaration]
parseFileDeclarations content = 
  case runParser parseFile "test" content of
    Left parseErr -> Left $ "Parse error: " ++ errorBundlePretty parseErr
    Right rawDecls -> elaborateDeclarationsSequentially emptyContext rawDecls []
  where
    elaborateDeclarationsSequentially :: Context -> [Raw.RawDeclaration] -> [Declaration] -> Either String [Declaration]
    elaborateDeclarationsSequentially _ [] acc = Right (reverse acc)
    elaborateDeclarationsSequentially ctx (rawDecl:remaining) acc = do
      case elaborate ctx rawDecl of
        Left err -> Left $ "Elaboration error: " ++ show err
        Right decl -> do
          -- Update context with the newly elaborated declaration
          let newCtx = updateContextWithDeclaration decl ctx
          elaborateDeclarationsSequentially newCtx remaining (decl:acc)
    
    updateContextWithDeclaration :: Declaration -> Context -> Context
    updateContextWithDeclaration (MacroDef name params body) ctx =
      let paramInfos = inferParamInfosG params body
      in extendMacroContext name paramInfos body (defaultFixity "TEST") ctx
    updateContextWithDeclaration (TheoremDef name bindings judgment proof) ctx =
      extendTheoremContext name bindings judgment proof ctx
    updateContextWithDeclaration _ ctx = ctx  -- Other declaration types don't affect elaboration context


-- | Build unified context from parsed declarations
buildContextFromDeclarations :: [Declaration] -> Context
buildContextFromDeclarations decls = foldr addDeclaration emptyContext decls
  where
    addDeclaration (MacroDef name params body) ctx =
      let paramInfos = inferParamInfosG params body
      in extendMacroContext name paramInfos body (defaultFixity "TEST") ctx
    addDeclaration (TheoremDef name bindings judgment proof) ctx =
      extendTheoremContext name bindings judgment proof ctx
    addDeclaration _ ctx = ctx

-- | Helper functions for creating test macro signatures
simpleParamInfo :: String -> VarKind -> ParamInfo
simpleParamInfo name kind = ParamInfo name kind False []

-- | Create a simple term macro sig for testing
simpleTermMacro :: [String] -> Term -> MacroSig
simpleTermMacro params body = ([simpleParamInfo p TermK | p <- params], TermMacro body)

-- | Create a simple rel macro sig for testing
simpleRelMacro :: [String] -> RType -> MacroSig
simpleRelMacro params body = ([simpleParamInfo p RelK | p <- params], RelMacro body)

-- | Create a simple proof macro sig for testing
simpleProofMacro :: [String] -> Proof -> MacroSig
simpleProofMacro params body = ([simpleParamInfo p ProofK | p <- params], ProofMacro body)
