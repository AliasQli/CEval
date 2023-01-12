{-# OPTIONS_GHC -Wno-unused-matches #-}

module Tychecker where

import           AST
import           Control.Applicative
import           Data.Type.Equality
import qualified Lexer               as L
import qualified Parser              as P

data Help ctx b = forall c. Basic c ~ b => Help (DCType c) (Ix ctx c)

formVarIx :: Table ctx -> (forall b. DBType b -> Help ctx b) -> P.Var L.Range -> Either String (Sig (LeftVal ctx))
formVarIx tbl ixf (P.Var (P.Name nn s)) = case lookup s tbl of
  Nothing           -> Left "a"
  Just (Sig ty var) -> let bty = basic ty in
    case ixf bty of
      Help ty' ix -> case ty =?= ty' of
        Nothing   -> Left "b"
        Just Refl -> Right (Sig (basic ty) (LeftVal var ix))
formVarIx tbl ixf (P.Ix ra var exp) = case formExp tbl exp of
  Left s               -> Left s
  Right (Sig DInt exp) -> formVarIx tbl (\bty -> case ixf bty of Help ty ix -> Help (DCArray ty) (Ix ix exp)) var
  Right (Sig _ exp)    -> Left "c"

formExp :: Table ctx -> P.Exp L.Range -> Either String (Sig (Exp ctx))
formExp tbl (P.EInt ra n) = pure $ Sig DInt (EInt n)
formExp tbl (P.EVar n var) = do
  Sig ty l <- formVarIx tbl (\bty -> Help (DBType bty) L) var
  pure $ Sig ty (Var l)
formExp tbl (P.EBinOp ra exp (P.Plus n) exp2) = do
  Sig ty exp <- formExp tbl exp
  Sig ty2 exp2 <- formExp tbl exp2
  case (ty =?= DInt, ty2 =?= DInt) of
    (Just Refl, Just Refl) -> pure $ Sig DInt (EAdd exp exp2)
    (_, _)                 -> Left ""
formExp tbl (P.EBinOpMut ra var (P.Assign n) exp) = do
  Sig ty l <- formVarIx tbl (\bty -> Help (DBType bty) L) var
  Sig ty2 exp <- formExp tbl exp
  case ty =?= ty2 of
    Nothing   -> Left ""
    Just Refl -> pure $ Sig ty (EAssign l exp)
formExp tbl (P.ECall _ (P.Name _ "print") [exp]) = do
  Sig ty exp <- formExp tbl exp
  case ty =?= DInt of
    Nothing   -> Left ""
    Just Refl -> pure $ Sig DInt (EPrintInt exp)
formExp _ _ = error "TODO"

tryCastExp :: DBType b -> Sig (Exp ctx) -> Either String (Exp ctx b)
tryCastExp DInt (Sig DInt exp)       = pure exp
tryCastExp DInt (Sig DFloat exp)     = pure $ EF2I exp
tryCastExp DInt (Sig DChar exp)      = pure $ EC2I exp
tryCastExp DFloat (Sig DInt exp)     = pure $ EI2F exp
tryCastExp DFloat (Sig DFloat exp)   = pure exp
tryCastExp DFloat (Sig DChar exp)    = pure $ EI2F (EC2I exp)
tryCastExp DChar (Sig DInt exp)      = pure $ EI2C exp
tryCastExp DChar (Sig DFloat exp)    = pure $ EI2C (EF2I exp)
tryCastExp DChar (Sig DChar exp)     = pure exp
tryCastExp DString (Sig DString exp) = pure exp
tryCastExp DVoid (Sig DVoid exp)     = pure exp
tryCastExp DVoid (Sig _ exp)         = pure $ E2V exp
tryCastExp b (Sig ty _)              = Left $ "Can't cast expression of type " <> show ty <> " to " <> show b <> "."

formStmtBlock
  :: Table ctx -> DBType b
  -> [P.Stmt L.Range] -> Either String (StmtBlock ctx b)
formStmtBlock tbl b []                              = pure Empty
formStmtBlock tbl b (P.Defs _ _ [] : xs)            = formStmtBlock tbl b xs
formStmtBlock tbl b (P.Defs r ty (P.Def _ les (P.Name _ txt) mExp : defs) : xs) = do
  let go [] = case ty of
          P.Int ra    -> Sig (DBType DInt) D0
          P.Float ra  -> Sig (DBType DFloat) D0
          P.Char ra   -> Sig (DBType DChar) D0
          P.String ra -> Sig (DBType DString) D0
      go (P.Length r i : ls) = case go ls of Sig ty dim -> Sig (DCArray ty) (DS i dim)
  case go les of
    Sig ctype dim -> do
      s <- formStmtBlock ((txt, Sig ctype Z) : weakenTable tbl) b (P.Defs r ty defs : xs)
      s' <- case mExp of
        Nothing -> pure s
        Just exp -> do
          Sig ty exp <- formExp tbl exp
          case (basic ctype =?= ty, DBType ty =?= ctype) of
            (Just Refl, Just Refl) -> pure $ Exp (EAssign (LeftVal Z L) (renExp S exp)) :. s
            _                      -> Left ""
      pure $ Def ctype dim s' :. Empty
formStmtBlock tbl b (P.If ra exp st : xs) = do
  exp <- formExp tbl exp
  exp <- tryCastExp DInt exp
  b1 <- formStmtBlock tbl b [st]
  xs <- formStmtBlock tbl b xs
  pure $ Branch exp b1 Empty :. xs
formStmtBlock tbl b (P.IfElse ra exp st st' : xs) = do
  exp <- formExp tbl exp
  exp <- tryCastExp DInt exp
  b1 <- formStmtBlock tbl b [st]
  b2 <- formStmtBlock tbl b [st']
  xs <- formStmtBlock tbl b xs
  pure $ Branch exp b1 b2 :. xs
formStmtBlock tbl b (P.While ra exp st : xs)        = do
  Sig ty exp <- formExp tbl exp
  case ty =?= DInt of
    Nothing -> Left ""
    Just Refl -> do
      xs <- formStmtBlock tbl b xs
      body <- formStmtBlock tbl b [st]
      pure $ Loop exp body :. xs
formStmtBlock tbl b (P.For ra st exp exp' st' : xs) = error "TODO"
formStmtBlock tbl b (P.Break ra : xs)               = pure Break -- TODO: Check scope
formStmtBlock tbl b (P.Continue ra : xs)            = pure Empty
formStmtBlock tbl b (P.Return ra mexp : _)          = do
  case mexp of
    Nothing -> case b of
      DVoid -> pure $ Return EVoid
      _     -> Left ""
    Just exp -> do
      sexp <- formExp tbl exp
      exp <- tryCastExp b sexp
      pure $ Return exp
formStmtBlock tbl b (P.Exp ra exp : xs)             = do
  Sig ty exp <- formExp tbl exp
  b <- formStmtBlock tbl b xs
  pure $ Exp exp :. b
formStmtBlock tbl b (P.Block (P.StmtBlock n ys) : xs) =
  liftA2 (<>) (formStmtBlock tbl b ys) (formStmtBlock tbl b xs)
formStmtBlock tbl b (P.Empty ra : xs)                 = formStmtBlock tbl b xs
