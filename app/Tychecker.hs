{-# OPTIONS_GHC -Wno-unused-matches #-}

module Tychecker where

import           AST
import           Control.Applicative
import           Control.Monad.Except
import           Data.Type.Equality
import qualified Lexer                as L
import qualified Parser               as P
import qualified Data.Text as T

errorAt :: L.Range -> String
errorAt r = " at " <> show r

errorIn :: Foldable f => f L.Range -> String
errorIn fa = errorAt (P.info fa)

traceErrorIn :: (MonadError String m, Foldable f) => f L.Range -> String -> m a
traceErrorIn fa s = throwError $ s <> errorIn fa

data Help ctx b = forall c. Basic c ~ b => Help (DCType c) (Ix ctx c) L.Range

formVarIx :: Table ctx -> (forall b. DBType b -> Help ctx b) -> P.Var L.Range -> Either String (Sig (LeftVal ctx))
formVarIx tbl ixf (P.Var (P.Name r s)) = case lookup s tbl of
  Nothing           -> throwError $ "Variable " <> T.unpack s <> " not defined or out of scope" <> errorAt r
  Just (Sig ty var) -> case ixf (basic ty) of
    Help ty' ix r -> case ty =?= ty' of
      Nothing   -> throwError $ "Can't use an array as a left value" <> errorAt r
      Just Refl -> Right (Sig (basic ty) (LeftVal var ix))
formVarIx tbl ixf (P.Ix ra var exp) = case formExp tbl exp of
  Left s               -> Left s
  Right index -> do
    index <- tryCastExp DInt index `catchError` traceErrorIn exp
    formVarIx tbl (\bty -> case ixf bty of Help ty ix r -> Help (DCArray ty) (Ix ix index) r) var

formExp :: Table ctx -> P.Exp L.Range -> Either String (Sig (Exp ctx))
formExp tbl (P.EInt ra r) = pure $ Sig DInt (EInt r)
formExp tbl (P.EVar n var) = do
  Sig ty l <- formVarIx tbl (\bty -> Help (DBType bty) L n) var
  pure $ Sig ty (Var l)
formExp tbl (P.EBinOp ra exp (P.Plus n) exp2) = do -- Subject to change
  Sig ty exp <- formExp tbl exp
  Sig ty2 exp2 <- formExp tbl exp2
  case (ty =?= DInt, ty2 =?= DInt) of
    (Just Refl, Just Refl) -> pure $ Sig DInt (EAdd exp exp2)
    (_, _)                 -> Left ""
formExp tbl (P.EBinOpMut r var (P.Assign n) exp) = do
  Sig ty l <- formVarIx tbl (\bty -> Help (DBType bty) L r) var
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
tryCastExp b (Sig ty _)              = throwError $ "Can't cast expression of type " <> show ty <> " to " <> show b

formStmtBlock
  :: Table ctx -> DBType b -> Bool
  -> [P.Stmt L.Range] -> Either String (StmtBlock ctx b)
formStmtBlock tbl b inloop []                              = pure Empty
formStmtBlock tbl b inloop (P.Defs _ _ [] : xs)            = formStmtBlock tbl b inloop xs
formStmtBlock tbl b inloop (P.Defs _ ty (P.Def r les (P.Name _ txt) mExp : defs) : xs) = do
  let go [] = case ty of
          P.Int ra    -> Sig (DBType DInt) D0
          P.Float ra  -> Sig (DBType DFloat) D0
          P.Char ra   -> Sig (DBType DChar) D0
          P.String ra -> Sig (DBType DString) D0
      go (P.Length r i : ls) = case go ls of Sig ty dim -> Sig (DCArray ty) (DS i dim)
  case go les of
    Sig ctype dim -> do
      s <- formStmtBlock ((txt, Sig ctype Z) : weakenTable tbl) b inloop (P.Defs r ty defs : xs)
      s' <- case mExp of
        Nothing -> pure s
        Just exp -> do
          case DBType (basic ctype) =?= ctype of
            Nothing -> throwError $ "Can't assign to an array directly" <> errorAt r
            Just Refl -> do
              defVal <- formExp tbl exp
              defVal <- tryCastExp (basic ctype) defVal `catchError` traceErrorIn exp
              pure $ Exp (EAssign (LeftVal Z L) (renExp S defVal)) :. s
      pure $ Def ctype dim s' :. Empty
formStmtBlock tbl b inloop (P.If ra exp st : xs) = do
  cond <- formExp tbl exp
  cond <- tryCastExp DInt cond `catchError` traceErrorIn exp
  b1 <- formStmtBlock tbl b inloop [st]
  xs <- formStmtBlock tbl b inloop xs
  pure $ Branch cond b1 Empty :. xs
formStmtBlock tbl b inloop (P.IfElse ra exp st st' : xs) = do
  cond <- formExp tbl exp
  cond <- tryCastExp DInt cond `catchError` traceErrorIn exp
  b1 <- formStmtBlock tbl b inloop [st]
  b2 <- formStmtBlock tbl b inloop [st']
  xs <- formStmtBlock tbl b inloop xs
  pure $ Branch cond b1 b2 :. xs
formStmtBlock tbl b inloop (P.While ra exp st : xs)        = do
  cond <- formExp tbl exp
  cond <- tryCastExp DInt cond `catchError` traceErrorIn exp
  xs <- formStmtBlock tbl b inloop xs
  body <- formStmtBlock tbl b True [st]
  pure $ Loop cond body :. xs
formStmtBlock tbl b inloop (P.For ra st exp exp' st' : xs) = error "TODO"
formStmtBlock tbl b inloop (P.Break ra : xs)               =
  if inloop
    then pure Break
    else throwError $ "Statement 'break' not in any loop" <> errorAt ra
formStmtBlock tbl b inloop (P.Continue ra : xs)            =
  if inloop
    then pure Empty
    else throwError $ "Statement 'continue' not in any loop" <> errorAt ra
formStmtBlock tbl b inloop (P.Return ra mexp : _)          = do
  case mexp of
    Nothing -> case b of
      DVoid -> pure $ Return EVoid
      _     -> throwError $ "Trying to return nothing for type " <> show b <> errorAt ra
    Just exp -> case b =?= DVoid of
      Just _ -> throwError $ "Trying to return an expression for type " <> show DVoid <> errorAt ra
      Nothing -> do
        sexp <- formExp tbl exp
        exp <- tryCastExp b sexp
        pure $ Return exp
formStmtBlock tbl b inloop (P.Exp ra exp : xs)             = do
  Sig ty exp <- formExp tbl exp
  b <- formStmtBlock tbl b inloop xs
  pure $ Exp exp :. b
formStmtBlock tbl b inloop (P.Block (P.StmtBlock n ys) : xs) =
  liftA2 (<>) (formStmtBlock tbl b inloop ys) (formStmtBlock tbl b inloop xs)
formStmtBlock tbl b inloop (P.Empty ra : xs)                 = formStmtBlock tbl b inloop xs
