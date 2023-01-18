{-# OPTIONS_GHC -Wno-unused-matches #-}

module Tychecker where

import           AST
import           Control.Applicative
import           Control.Monad.Except
import           Data.Functor.Identity
import           Data.Kind             (Type)
import           Data.Maybe            (fromJust)
import           Data.Text             (Text)
import qualified Data.Text             as T
import           Data.Type.Equality
import           Data.Vector           (Vector)
import qualified Data.Vector           as V
import qualified Lexer                 as L
import qualified Parser                as P

errorAt :: R -> String
errorAt r = " at " <> show r

errorIn :: Foldable f => f R -> String
errorIn fa = errorAt (P.info fa)

data Help ctx b = forall c. Basic c ~ b => Help (DCType c) (Ix ctx c) R

formVarIx :: Table ctx -> [(Text, Sig2 (Function ctx))] -> (forall b. DBType b -> Help ctx b) -> P.Var R -> Identity (Sig (LeftVal ctx))
formVarIx tbl funs ixf (P.Var (P.Name r s)) = case lookup s tbl of
  Nothing           -> error $ "Variable '" <> T.unpack s <> "' not defined or out of scope" <> errorAt r
  Just (Sig ty var) -> case ixf (basic ty) of
    Help ty' ix r -> case ty =?= ty' of
      Nothing   -> error $ "Can't use an array as a left value" <> errorAt r
      Just Refl -> pure (Sig (basic ty) (LeftVal var ix))
formVarIx tbl funs ixf (P.Ix ra var exp) = do
  index <- formExp tbl funs exp
  index <- tryCastExp DInt index (P.info exp)
  formVarIx tbl funs (\bty -> case ixf bty of Help ty ix r -> Help (DCArray ty) (Ix ix index) r) var

formExp :: Table ctx -> [(Text, Sig2 (Function ctx))] -> P.Exp R -> Identity (Sig (Exp ctx))
formExp tbl funs (P.EInt ra r) = pure $ Sig DInt (EInt r)
formExp tbl funs (P.EVar n var) = do
  Sig ty l <- formVarIx tbl funs (\bty -> Help (DBType bty) L n) var
  pure $ Sig ty (Var l)
formExp tbl funs (P.EBinOp ra exp (P.Plus n) exp2) = do -- Subject to change
  Sig ty exp <- formExp tbl funs exp
  Sig ty2 exp2 <- formExp tbl funs exp2
  case (ty =?= DInt, ty2 =?= DInt) of
    (Just Refl, Just Refl) -> pure $ Sig DInt (EAdd exp exp2)
    (_, _)                 -> error ""
formExp tbl funs (P.EBinOpMut r var (P.Assign n) exp) = do
  Sig ty l <- formVarIx tbl funs (\bty -> Help (DBType bty) L r) var
  Sig ty2 exp <- formExp tbl funs exp
  case ty =?= ty2 of
    Nothing   -> error ""
    Just Refl -> pure $ Sig ty (EAssign l exp)
formExp tbl funs (P.ECall _ (P.Name _ "print") [P.Arg exp]) = do
  Sig ty exp <- formExp tbl funs exp
  case ty =?= DInt of
    Nothing   -> error ""
    Just Refl -> pure $ Sig DInt (EPrintInt exp)
formExp tbl funs (P.ECall r (P.Name ra name) args) = case lookup name funs of
  Nothing -> error $ "Calling an undefined function '" <> show name <> "'" <> errorAt ra
  Just (Sig2 argType (retType :: DBType ret) fun) -> Sig retType . ERun <$> go tbl funs argType fun args
    where
      go :: Table ctx -> [(Text, Sig2 (Function ctx))] -> Dep [CType] as -> Function ctx as ret -> [P.PassArg R] -> Identity (StmtBlock ctx ret)
      go tbl funs DNil (Fun sb) []                              = pure sb
      go tbl funs (DCons dep dl) (Arg func btype) (P.Arg exp : args) = do
        arg <- formExp tbl funs exp
        arg <- tryCastExp btype arg (P.info exp)
        stmts <- go (weakenTable tbl) (weakenFuns funs) dl func args
        pure $ Def (DBType btype) D0 (Exp (EAssign (LeftVal Z L) (renExp S arg)) :. stmts) :. Empty
      go tbl funs (DCons dep dl) (Ref func ctype) (P.Ref ra' (P.Name ra2 name) : args) =
        case lookup name tbl of
          Nothing -> error $ "Variable '" <> T.unpack name <> "' not defined or out of scope" <> errorAt ra2
          Just (Sig ctype' var) -> do
            case ctype =?= ctype' of
              Nothing -> error $ "Reference type mismatch: expecting " <> show ctype <> ", got " <> show ctype' <> errorAt r
              Just Refl -> do
                stmts <- go (weakenTable tbl) (weakenFuns funs) dl func args
                pure $ renStmtBlock (renw id var) stmts
      go tbl funs argType (Arg func btype) (P.Ref ra' _ : args) =
        error $ "Passing a reference, but the function is expecting an expression" <> errorAt ra'
      go tbl funs argType (Ref func ctype) (P.Arg exp : _) =
        error $ "Passing an expression, but the function is expecting a reference" <> errorIn exp
      go tbl funs _ _ _                                         = error $ "Argument number mismatch" <> errorAt r
formExp _ _ _ = error "TODO"

tryCastExp :: DBType b -> Sig (Exp ctx) -> R -> Identity (Exp ctx b)
tryCastExp DInt (Sig DInt exp)       r = pure exp
tryCastExp DInt (Sig DFloat exp)     r = pure $ EF2I exp
tryCastExp DInt (Sig DChar exp)      r = pure $ EC2I exp
tryCastExp DFloat (Sig DInt exp)     r = pure $ EI2F exp
tryCastExp DFloat (Sig DFloat exp)   r = pure exp
tryCastExp DFloat (Sig DChar exp)    r = pure $ EI2F (EC2I exp)
tryCastExp DChar (Sig DInt exp)      r = pure $ EI2C exp
tryCastExp DChar (Sig DFloat exp)    r = pure $ EI2C (EF2I exp)
tryCastExp DChar (Sig DChar exp)     r = pure exp
tryCastExp DString (Sig DString exp) r = pure exp
tryCastExp DVoid (Sig DVoid exp)     r = pure exp
tryCastExp DVoid (Sig _ exp)         r = pure $ E2V exp
tryCastExp b (Sig ty _)              r = error $ "Can't cast expression of type " <> show ty <> " to " <> show b <> errorAt r

formBType :: P.Type R -> Sig DBType
formBType (P.Int ra)    = Sig DInt DInt
formBType (P.Float ra)  = Sig DFloat DFloat
formBType (P.Char ra)   = Sig DChar DChar
formBType (P.String ra) = Sig DString DString

formRetType :: P.RetType R -> Sig DBType
formRetType (P.Type b)  = formBType b
formRetType (P.Void ra) = Sig DVoid DVoid

formDim :: [P.Length R] -> P.Type R -> Identity (Sig Dim)
formDim (P.Length ra n : xs) ty = do
  when (n < 0) $ error $ "Invalid negative array boundary " <> show n <> errorAt ra
  Sig ctype d <- formDim xs ty
  pure $ Sig (DCArray ctype) (DS n d)
formDim [] ty = pure $ case ty of
    P.Int ra    -> Sig (DBType DInt) D0
    P.Float ra  -> Sig (DBType DFloat) D0
    P.Char ra   -> Sig (DBType DChar) D0
    P.String ra -> Sig (DBType DString) D0

formStmtBlock
  :: Table ctx
  -> [(Text, Sig2 (Function ctx))]
  -> DBType b -- ^ Expected return type
  -> Bool     -- ^ Init: False
  -> [P.Stmt R] -> Identity (StmtBlock ctx b)
formStmtBlock tbl funs b inloop []                              = pure Empty
formStmtBlock tbl funs b inloop (P.Defs _ _ [] : xs)            = formStmtBlock tbl funs b inloop xs
formStmtBlock tbl funs b inloop (P.Defs _ ty (P.Def r les (P.Name _ txt) mExp : defs) : xs) = do
  Sig ctype dim <- formDim les ty
  s <- formStmtBlock ((txt, Sig ctype Z) : weakenTable tbl) (weakenFuns funs) b inloop (P.Defs r ty defs : xs)
  s' <- case mExp of
    Nothing -> pure s
    Just exp -> do
      case DBType (basic ctype) =?= ctype of
        Nothing -> error $ "Can't assign to an array directly" <> errorAt r
        Just Refl -> do
          defVal <- formExp tbl funs exp
          defVal <- tryCastExp (basic ctype) defVal (P.info exp)
          pure $ Exp (EAssign (LeftVal Z L) (renExp S defVal)) :. s
  pure $ Def ctype dim s' :. Empty
formStmtBlock tbl funs b inloop (P.If ra exp st : xs) = do
  cond <- formExp tbl funs exp
  cond <- tryCastExp DInt cond (P.info exp)
  b1 <- formStmtBlock tbl funs b inloop [st]
  xs <- formStmtBlock tbl funs b inloop xs
  pure $ Branch cond b1 Empty :. xs
formStmtBlock tbl funs b inloop (P.IfElse ra exp st st' : xs) = do
  cond <- formExp tbl funs exp
  cond <- tryCastExp DInt cond (P.info exp)
  b1 <- formStmtBlock tbl funs b inloop [st]
  b2 <- formStmtBlock tbl funs b inloop [st']
  xs <- formStmtBlock tbl funs b inloop xs
  pure $ Branch cond b1 b2 :. xs
formStmtBlock tbl funs b inloop (P.While ra exp st : xs)        = do
  cond <- formExp tbl funs exp
  cond <- tryCastExp DInt cond (P.info exp)
  xs <- formStmtBlock tbl funs b inloop xs
  body <- formStmtBlock tbl funs b True [st]
  pure $ Loop cond body :. xs
formStmtBlock tbl funs b inloop (P.For ra st exp exp' st' : xs) = error "TODO"
formStmtBlock tbl funs b inloop (P.Break ra : xs)               =
  if inloop
    then do
      s <- formStmtBlock tbl funs b inloop xs
      pure $ Break :. s
    else error $ "Statement 'break' not in any loop" <> errorAt ra
formStmtBlock tbl funs b inloop (P.Continue ra : xs)            =
  if inloop
    then do
      s <- formStmtBlock tbl funs b inloop xs
      pure $ Continue :. s
    else error $ "Statement 'continue' not in any loop" <> errorAt ra
formStmtBlock tbl funs b inloop (P.Return ra mexp : xs)          = do
  case mexp of
    Nothing -> case b of
      DVoid -> do
        s <- formStmtBlock tbl funs b inloop xs
        pure $ Return EVoid :. s
      _     -> error $ "Trying to return nothing for type " <> show b <> errorAt ra
    Just exp -> case b =?= DVoid of
      Just _ -> error $ "Trying to return an expression for type " <> show DVoid <> errorAt ra
      Nothing -> do
        sexp <- formExp tbl funs exp
        exp <- tryCastExp b sexp (P.info exp)
        s <- formStmtBlock tbl funs b inloop xs
        pure $ Return exp :. s
formStmtBlock tbl funs b inloop (P.Exp ra exp : xs)             = do
  Sig ty exp <- formExp tbl funs exp
  b <- formStmtBlock tbl funs b inloop xs
  pure $ Exp exp :. b
formStmtBlock tbl funs b inloop (P.Block (P.StmtBlock n ys) : xs) =
  liftA2 (<>) (formStmtBlock tbl funs b inloop ys) (formStmtBlock tbl funs b inloop xs)
formStmtBlock tbl funs b inloop (P.Empty ra : xs)                 = formStmtBlock tbl funs b inloop xs

checkHaveReturn :: DBType b -> StmtBlock ctx b -> Text -> R -> Identity (StmtBlock ctx b)
checkHaveReturn btype stmts name r = if go stmts
    then pure stmts
    else case btype of
            DVoid -> pure $ stmts <> Return EVoid :. Empty
            _     -> error $ "Possible control flow detected with no return statement in function '" <> T.unpack name <> "'" <> errorAt r
  where
    go :: forall ctx b. StmtBlock ctx b -> Bool
    go Empty                       = False
    go (Branch _ left right :. sb) = (go left && go right) || go sb
    go (Def _ _ sb' :. sb)         = go sb' || go sb
    go (Return _ :. sb)            = True
    go (_ :. sb)                   = go sb

type R = L.Range

type family B (b :: BType) :: Type where
  B 'BInt = Int
  B 'BFloat = Float
  B 'BChar = Char
  B 'BString = Text
  B 'BVoid = ()

type family C (c :: CType) :: Type where
  C ('BType b) = B b
  C ('CArray c) = Vector (C c)

type family Ctx (ctx :: [CType]) :: Type where
  Ctx '[] = ()
  Ctx (c ': cs) = (C c, Ctx cs)

initB :: DBType b -> B b
initB DInt    = 0
initB DFloat  = 0
initB DChar   = '\0'
initB DString = ""
initB DVoid   = ()

initC :: DCType c -> Dim c -> C c
initC (DBType b) D0          = initB b
initC (DCArray c) (DS n dim) = V.replicate n (initC c dim)

data CtxTable ctx = CtxTable (Ctx ctx) (Table ctx)

data Program = forall global. Program (Dep [CType] global) (Ctx global) [(Text, Sig2 (Function global))]

formProgram :: [P.GlobalDef R] -> Identity Program
formProgram defs = do
  let (gDefs, fs) = go defs
  Sig ctype (CtxTable ctx tbl) <- globalVar gDefs
  rec funs <- traverse (formFunction tbl funs) fs
  pure $ Program ctype ctx funs
  where
    go :: [P.GlobalDef R] -> ([(R, P.Name R, P.Type R, [P.Length R], Maybe (P.Exp R))], [P.GlobalDef R])
    go = foldr f ([], [])
      where
        f (P.VarDefs _ra ty defs) (x, y) = (map (\(P.Def r ls name mexp) -> (r, name, ty, ls, mexp)) defs ++ x, y)
        f g (x, y) = (x, g : y)
    globalVar :: [(R, P.Name R, P.Type R, [P.Length R], Maybe (P.Exp R))] -> Identity (Sig CtxTable)
    globalVar [] = pure $ Sig DNil (CtxTable () [])
    globalVar ((r, P.Name _ name, ty, len, _) : xs) = do
      -- TODO: init val ignored!
      Sig ctype dim <- formDim len ty
      Sig dep (CtxTable ctx tbl) <- globalVar xs
      pure $ Sig (DCons ctype dep) (CtxTable (initC ctype dim, ctx) ((name, Sig ctype Z) : weakenTable tbl))
    formFunction :: Table ctx -> [(Text, Sig2 (Function ctx))] -> P.GlobalDef R -> Identity (Text, Sig2 (Function ctx))
    formFunction tbl funs P.VarDefs{} = error "UNREACHABLE"
    formFunction tbl funs f@(P.Function ra rt (P.Name ra2 name) [] (P.StmtBlock ra' sts)) =
      case formRetType rt of
        Sig dep rt -> do
          block' <- formStmtBlock tbl funs rt False sts
          block <- checkHaveReturn rt block' name ra
          pure $ (name, Sig2 DNil rt (Fun block))
    formFunction tbl funs (P.Function ra rt na ((ty, ref, P.Name r argName, (len, mRange)) : args) sb) = do
      case ref of
        Just ra' -> do
          Sig ctype _ <- formDim (replicate len (P.Length undefined 0)) ty
          (name, Sig2 args ret fun) <- formFunction ((argName, Sig ctype Z) : weakenTable tbl) (weakenFuns funs) (P.Function ra rt na args sb)
          let x = (name, Sig2 (DCons ctype args) ret (Ref fun ctype))
          pure x
        Nothing -> do
          when (len /= 0) $ error $ "Expressions passed by value must not have an array type" <> errorAt (fromJust mRange)
          Sig btype _ <- pure $ formBType ty
          (name, Sig2 args ret fun) <- formFunction ((argName, Sig (DBType btype) Z) : weakenTable tbl) (weakenFuns funs) (P.Function ra rt na args sb)
          let x = (name, Sig2 (DCons (DBType btype) args) ret (Arg fun btype))
          pure x
    -- TODO: Multiple definition, main function
