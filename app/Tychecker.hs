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

formStmtBlock
  :: Table ctx -> Either String (StmtBlock ctx) -> Either String (StmtBlock ctx)
  -> [P.Stmt L.Range] -> Either String (StmtBlock ctx, Bool)
formStmtBlock tbl break continue []                                = pure (Empty, False)
formStmtBlock tbl break continue ((P.Defs _ _ []) : xs)            = formStmtBlock tbl break continue xs
formStmtBlock tbl break continue ((P.Defs r ty ((P.Def _ les (P.Name _ txt) mExp) : defs)) : xs) = do
  let btype = case ty of
        P.Int ra    -> Sig DInt DInt
        P.Float ra  -> Sig DFloat DFloat
        P.Char ra   -> Sig DChar DChar
        P.String ra -> Sig DString DString
      go (Sig ty ty') [] = Sig (DBType ty) D0
      go sig ((P.Length r i) : ls) = case go sig ls of Sig ty dim -> Sig (DCArray ty) (DS i dim)
  case go btype les of
    Sig ctype dim -> do
      (s, bool) <- formStmtBlock ((txt, Sig ctype Z) : weakenTable tbl)
        (fmap weakenStmtBlock break) (fmap weakenStmtBlock continue) ((P.Defs r ty defs) : xs)
      s' <- case mExp of
        Nothing -> pure s
        Just exp -> do
          Sig ty exp <- formExp tbl exp
          case (basic ctype =?= ty, DBType ty =?= ctype) of
            (Just Refl, Just Refl) -> pure $ Exp (EAssign (LeftVal Z L) (renExp S exp)) :. s
            _                      -> Left ""
      pure $ (Def ctype dim s' :. Empty, bool)
formStmtBlock tbl break continue ((P.If ra exp st) : xs) = do
  Sig ty exp <- formExp tbl exp
  case ty =?= DInt of
    Nothing -> Left ""
    Just Refl -> do
      (b1, bool1) <- formStmtBlock tbl break continue [st]
      (b, bool2) <- formStmtBlock tbl break continue xs
      pure $ (Branch exp (b1 <> b) b, bool1 <> bool2) -- Wrong
formStmtBlock tbl break continue ((P.IfElse ra exp st st') : xs) = do
  Sig ty exp <- formExp tbl exp
  case ty =?= DInt of
    Nothing -> Left ""
    Just Refl -> do
      (b1, bool1) <- formStmtBlock tbl break continue [st]
      (b2, bool2) <- formStmtBlock tbl break continue [st']
      (b, bool3) <- formStmtBlock tbl break continue xs
      pure $ (Branch exp (b1 <> b) (b2 <> b), bool1 <> bool2 <> bool3)
formStmtBlock tbl break continue ((P.While ra exp st) : xs)        = do
  Sig ty exp <- formExp tbl exp
  case ty =?= DInt of
    Nothing -> Left ""
    Just Refl -> do
      rec (break', bool) <- formStmtBlock tbl break continue xs
          (body, bOrC) <- formStmtBlock tbl (pure break') (pure continue') [st]
          let continue' = Branch exp (if bOrC then body else body <> continue') break'
      pure (continue', bool)
formStmtBlock tbl break continue ((P.For ra st exp exp' st') : xs) = error "TODO"
formStmtBlock tbl break continue ((P.Break ra) : xs)               = fmap (, True) break
formStmtBlock tbl break continue ((P.Continue ra) : xs)            = fmap (, True) continue
formStmtBlock tbl break continue ((P.Exp ra exp) : xs)             = do
  Sig ty exp <- formExp tbl exp
  (b, bool) <- formStmtBlock tbl break continue xs
  pure $ (Exp exp :. b, bool)
formStmtBlock tbl break continue ((P.Block (P.StmtBlock n ys)) : xs) =
  liftA2 (<>) (formStmtBlock tbl break continue ys) (formStmtBlock tbl break continue xs)
formStmtBlock tbl break continue ((P.Empty ra) : xs)                 = formStmtBlock tbl break continue xs
