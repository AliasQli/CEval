{-# OPTIONS_GHC -Wno-unused-matches #-}

module Tychecker where

import           AST
import           Control.Applicative
import           Control.Monad.Except
import           Data.Functor.Identity
import           Data.Kind             (Type)
import           Data.List             (groupBy)
import           Data.Maybe            (fromJust)
import           Data.Text             (Text)
import qualified Data.Text             as T
import           Data.Type.Equality
import           Data.Vector           (Vector)
import qualified Data.Vector           as V
import qualified Lexer                 as L
import qualified Parser                as P
import Data.List (find)

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
formExp tbl funs (P.EFloat ra r) = pure $ Sig DFloat (EFloat r)
formExp tbl funs (P.EString ra r) = pure $ Sig DString (EString r)
formExp tbl funs (P.EChar ra r) = pure $ Sig DChar (EChar r)
formExp tbl funs (P.EVar n var) = do
  Sig ty l <- formVarIx tbl funs (\bty -> Help (DBType bty) L n) var
  pure $ Sig ty (Var l)
formExp tbl funs (P.EBinOp ra exp op exp2) = do
  exp <- formExp tbl funs exp
  exp2 <- formExp tbl funs exp2
  Sig ty (exp :*: exp2) <- unifyExp exp exp2 ra
  case op of
    P.Plus ra'   -> pure $ Sig ty (EArith ty Add exp exp2)
    P.Minus ra'  -> pure $ Sig ty (EArith ty Sub exp exp2)
    P.Times ra'  -> pure $ Sig ty (EArith ty Mul exp exp2)
    P.Divide ra' -> pure $ Sig ty (EArith ty Div exp exp2)
    P.Eq ra'     -> pure $ Sig DInt (ECmp ty Eq exp exp2)
    P.Neq ra'    -> pure $ Sig DInt (ECmp ty Ne exp exp2)
    P.Lt ra'     -> pure $ Sig DInt (ECmp ty Lt exp exp2)
    P.Le ra'     -> pure $ Sig DInt (ECmp ty Le exp exp2)
    P.Gt ra'     -> pure $ Sig DInt (ECmp ty Gt exp exp2)
    P.Ge ra'     -> pure $ Sig DInt (ECmp ty Ge exp exp2)
    P.Mod ra'    -> case ty of
      DInt  -> pure $ Sig DInt (EMod exp exp2)
      DChar -> pure $ Sig DInt (EMod (EC2I exp) (EC2I exp2))
      _     -> error $ "Expecting integral expression in modulo" <> errorAt ra
formExp tbl funs (P.EBinOpMut r var op exp) = do
  Sig ty l <- formVarIx tbl funs (\bty -> Help (DBType bty) L r) var
  val <- formExp tbl funs exp
  val <- tryCastExp ty val (P.info exp)
  let canArith :: DBType b -> Bool
      canArith DInt   = True
      canArith DFloat = True
      canArith DChar  = True
      canArith _      = False
  case op of
    P.Assign ra -> pure $ Sig ty (EAssign l val)
    P.PlusAssign ra -> do
      unless (canArith ty) $ error $ "Can't perform arithmetic operation on a left value of type '" <> show ty <> "'" <> errorIn var
      pure $ Sig ty (EAssign l (EArith ty Add (Var l) val))
    P.MinusAssign ra -> do
      unless (canArith ty) $ error $ "Can't perform arithmetic operation on a left value of type '" <> show ty <> "'" <> errorIn var
      pure $ Sig ty (EAssign l (EArith ty Sub (Var l) val))
    P.TimesAssign ra -> do
      unless (canArith ty) $ error $ "Can't perform arithmetic operation on a left value of type '" <> show ty <> "'" <> errorIn var
      pure $ Sig ty (EAssign l (EArith ty Mul (Var l) val))
    P.DivideAssign ra -> do
      unless (canArith ty) $ error $ "Can't perform arithmetic operation on a left value of type '" <> show ty <> "'" <> errorIn var
      pure $ Sig ty (EAssign l (EArith ty Div (Var l) val))
    P.ModAssign ra -> case ty =?= DInt of
      Nothing -> error $ "Expecting integral expression in modulo" <> errorIn exp
      Just Refl -> pure $ Sig ty (EAssign l (EMod (Var l) val))
formExp tbl funs (P.EUOp ra (P.Negate _) exp) = do
  Sig ty val <- formExp tbl funs exp
  case ty of
    DInt    -> pure $ Sig DInt (EArith DInt Sub (EInt 0) val)
    DFloat  -> pure $ Sig DFloat (EArith DFloat Sub (EFloat 0) val)
    DChar   -> pure $ Sig DInt (EArith DInt Sub (EInt 0) (EC2I val))
    _       -> error $ "Can't negate an expression of type '" <> show ty <> "'" <> errorIn exp
formExp tbl funs (P.EUOpMut ra op var) = do
  Sig (ty :: DBType a) l <- formVarIx tbl funs (\bty -> Help (DBType bty) L ra) var
  let one :: Exp _ a = case ty of
        DInt   -> EInt 1
        DFloat -> EFloat 1
        DChar  -> EChar '\1'
        _      -> error $ "Can't perform arithmetic operation on a left value of type '" <> show ty <> "'" <> errorIn var
  case op of
    P.LInc ra' -> pure $ Sig ty (EAssign l (EArith ty Add (Var l) one))
    P.RInc ra' -> pure $ Sig ty (ERetAssign l (EArith ty Add (Var l) one))
    P.LDec ra' -> pure $ Sig ty (EAssign l (EArith ty Sub (Var l) one))
    P.RDec ra' -> pure $ Sig ty (ERetAssign l (EArith ty Sub (Var l) one))
formExp tbl funs (P.ECall r (P.Name _ "print") args) = case args of
  [P.Arg arg] -> do
    Sig ty exp <- formExp tbl funs arg
    case ty =?= DVoid of
      Nothing   -> pure $ Sig ty (EPrint ty exp)
      Just Refl -> error $ "Can't print a value of type void" <> errorAt (P.info arg)
  [P.Ref{}]   -> error $ "Passing a reference, but the function is expecting an expression" <> errorAt r
  _           -> error $ "Argument number mismatch, expecting 1" <> errorAt r
formExp tbl funs (P.ECall r (P.Name _ "readInt") args) = do
  unless (null args) $ error $ "Argument number mismatch, expecting 0" <> errorAt r
  pure $ Sig DInt (ERead DInt)
formExp tbl funs (P.ECall r (P.Name _ "readFloat") args) = do
  unless (null args) $ error $ "Argument number mismatch, expecting 0" <> errorAt r
  pure $ Sig DFloat (ERead DFloat)
formExp tbl funs (P.ECall r (P.Name _ "readChar") args) = do
  unless (null args) $ error $ "Argument number mismatch, expecting 0" <> errorAt r
  pure $ Sig DChar (ERead DChar)
formExp tbl funs (P.ECall r (P.Name _ "readString") args) = do
  unless (null args) $ error $ "Argument number mismatch, expecting 0" <> errorAt r
  pure $ Sig DString (ERead DString)
formExp tbl funs (P.ECall r (P.Name ra name) args) = case lookup name funs of
  Nothing -> error $ "Calling an undefined function '" <> show name <> "'" <> errorAt ra
  Just (Sig2 argType (retType :: DBType ret) fun) -> Sig retType . ERun <$> go tbl funs argType fun args
    where
      go :: Table ctx -> [(Text, Sig2 (Function ctx))] -> Dep [CType] as -> Function ctx as ret -> [P.PassArg R] -> Identity (StmtBlock ctx ret)
      go tbl funs DNil (Fun sb) []                              = pure (Lazy sb)
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

unifyExp :: Sig (Exp ctx) -> Sig (Exp ctx) -> R -> Identity (Sig (Exp ctx :*: Exp ctx))
unifyExp (Sig DInt exp) (Sig DInt exp2)   r = pure $ Sig DInt (exp :*: exp2)
unifyExp (Sig DInt exp) (Sig DFloat exp2) r = pure $ Sig DFloat (EI2F exp :*: exp2)
unifyExp (Sig DInt exp) (Sig DChar exp2)  r = pure $ Sig DInt (exp :*: EC2I exp2)
unifyExp (Sig DFloat exp) (Sig DInt exp2) r = pure $ Sig DFloat (exp :*: EI2F exp2)
unifyExp (Sig DFloat exp) (Sig DFloat exp2) r = pure $ Sig DFloat (exp :*: exp2)
unifyExp (Sig DFloat exp) (Sig DChar exp2) r = pure $ Sig DFloat (exp :*: EI2F (EC2I exp2))
unifyExp (Sig DChar exp) (Sig DInt exp2) r = pure $ Sig DInt (EC2I exp :*: exp2)
unifyExp (Sig DChar exp) (Sig DFloat exp2) r = pure $ Sig DFloat (EI2F (EC2I exp) :*: exp2)
unifyExp (Sig DChar exp) (Sig DChar exp2) r = pure $ Sig DChar (exp :*: exp2)
unifyExp (Sig ty _) (Sig ty2 _)           r =
  error $ "Can't unify '" <> show ty <> "' and '" <> show ty2 <> "' in an arithmetic expression" <> errorAt r

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
formDim (P.Length ra n : xs) ty = if n < 0
  then error $ "Invalid negative array boundary " <> show n <> errorAt ra
  else do
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
  -> [Text]   -- ^ Init: []
  -> DBType b -- ^ Expected return type
  -> Bool     -- ^ Init: False
  -> [P.Stmt R] -> Identity (StmtBlock ctx b)
formStmtBlock tbl funs names b inloop []                              = pure Empty
formStmtBlock tbl funs names b inloop (P.Defs _ _ [] : xs)            = formStmtBlock tbl funs names b inloop xs
formStmtBlock tbl funs names b inloop (P.Defs _ ty (P.Def r les (P.Name rvar txt) mExp : defs) : xs) = if txt `elem` names
  then error $ "Redefinition of variable '" <> T.unpack txt <> "'" <> errorAt rvar
  else do
    Sig ctype dim <- formDim les ty
    s <- formStmtBlock ((txt, Sig ctype Z) : weakenTable tbl) (weakenFuns funs) (txt : names) b inloop (P.Defs r ty defs : xs)
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
formStmtBlock tbl funs names b inloop (P.If ra exp st : xs) = formStmtBlock tbl funs names b inloop (P.IfElse ra exp st (P.Empty undefined) : xs)
formStmtBlock tbl funs names b inloop (P.IfElse ra exp st st' : xs) = do
  cond <- formExp tbl funs exp
  cond <- tryCastExp DInt cond (P.info exp)
  b1 <- formStmtBlock tbl funs names b inloop [st]
  b2 <- formStmtBlock tbl funs names b inloop [st']
  xs <- formStmtBlock tbl funs names b inloop xs
  pure $ Branch cond b1 b2 :. xs
formStmtBlock tbl funs names b inloop (P.While ra exp sts : xs) = do
  cond <- formExp tbl funs exp
  cond <- tryCastExp DInt cond (P.info exp)
  xs <- formStmtBlock tbl funs names b inloop xs
  body <- formStmtBlock tbl funs names b True sts
  pure $ Loop cond body :. xs
formStmtBlock tbl funs names b inloop (P.For ra (P.ForEmpty _) cond step st : xs) =
  formStmtBlock tbl funs names b inloop (P.While ra cond [st, P.Exp (P.info step) step] : xs)
formStmtBlock tbl funs names b inloop (P.For ra (P.ForExp _ first) cond step st : xs) = do
  Sig _ first <- formExp tbl funs first
  b <- formStmtBlock tbl funs names b inloop (P.While ra cond [st, P.Exp (P.info step) step] : xs)
  pure $ Exp first :. b
formStmtBlock tbl funs names b inloop (P.For ra (P.ForDefs r ty defs) cond step st : xs) =
  formStmtBlock tbl funs names b inloop (P.Block (P.StmtBlock undefined [P.Defs r ty defs, P.While ra cond [st, P.Exp (P.info step) step]]) : xs)
formStmtBlock tbl funs names b inloop (P.Break ra : xs)               =
  if inloop
    then do
      s <- formStmtBlock tbl funs names b inloop xs
      pure $ Break :. s
    else error $ "Statement 'break' not in any loop" <> errorAt ra
formStmtBlock tbl funs names b inloop (P.Continue ra : xs)            =
  if inloop
    then do
      s <- formStmtBlock tbl funs names b inloop xs
      pure $ Continue :. s
    else error $ "Statement 'continue' not in any loop" <> errorAt ra
formStmtBlock tbl funs names b inloop (P.Return ra mexp : xs)          = do
  case mexp of
    Nothing -> case b of
      DVoid -> do
        s <- formStmtBlock tbl funs names b inloop xs
        pure $ Return EVoid :. s
      _     -> error $ "Trying to return nothing for type " <> show b <> errorAt ra
    Just exp -> case b =?= DVoid of
      Just _ -> error $ "Trying to return an expression for type " <> show DVoid <> errorAt ra
      Nothing -> do
        sexp <- formExp tbl funs exp
        exp <- tryCastExp b sexp (P.info exp)
        s <- formStmtBlock tbl funs names b inloop xs
        pure $ Return exp :. s
formStmtBlock tbl funs names b inloop (P.Exp ra exp : xs)             = do
  Sig ty exp <- formExp tbl funs exp
  b <- formStmtBlock tbl funs names b inloop xs
  pure $ Exp exp :. b
formStmtBlock tbl funs names b inloop (P.Block (P.StmtBlock n ys) : xs) =
  liftA2 (<>) (formStmtBlock tbl funs names b inloop ys) (formStmtBlock tbl funs names b inloop xs)
formStmtBlock tbl funs names b inloop (P.Empty ra : xs)                 = formStmtBlock tbl funs names b inloop xs

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
    go (Lazy _)                    = False

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

newtype BB b = BB (B b)

evalConstExp :: P.Exp R -> Identity (Sig BB)
evalConstExp (P.EInt ra r) = pure $ Sig DInt (BB r)
evalConstExp (P.EFloat ra r) = pure $ Sig DFloat (BB r)
evalConstExp (P.EString ra r) = pure $ Sig DString (BB r)
evalConstExp (P.EChar ra r) = pure $ Sig DChar (BB r)
evalConstExp (P.EUOp ra (P.Negate _) exp) = do
  Sig ty (BB val) <- evalConstExp exp
  case ty of
    DInt    -> pure $ Sig DInt (BB (0 - val))
    DFloat  -> pure $ Sig DFloat (BB (0 - val))
    DChar   -> pure $ Sig DInt (BB (0 - fromEnum val))
    _       -> error $ "Can't negate an expression of type '" <> show ty <> "'" <> errorIn exp
evalConstExp (P.EBinOp ra exp op exp2) = do
  exp <- evalConstExp exp
  exp2 <- evalConstExp exp2
  Sig ty (BB exp :*: BB exp2) <- pure $ unifyConstExp exp exp2 ra
  case ty of
    DInt -> case op of
      P.Plus ra'   -> pure $ Sig DInt $ BB $ exp + exp2
      P.Minus ra'  -> pure $ Sig DInt $ BB $ exp - exp2
      P.Times ra'  -> pure $ Sig DInt $ BB $ exp * exp2
      P.Divide ra' -> pure $ Sig DInt $ BB $ exp `div` exp2
      P.Eq ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp == exp2
      P.Neq ra'    -> pure $ Sig DInt $ BB $ fromEnum $ exp /= exp2
      P.Lt ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp < exp2
      P.Le ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp <= exp2
      P.Gt ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp > exp2
      P.Ge ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp >= exp2
      P.Mod ra'    -> pure $ Sig DInt $ BB $ exp `mod` exp2
    DFloat -> case op of
      P.Plus ra'   -> pure $ Sig DFloat $ BB $ exp + exp2
      P.Minus ra'  -> pure $ Sig DFloat $ BB $ exp - exp2
      P.Times ra'  -> pure $ Sig DFloat $ BB $ exp * exp2
      P.Divide ra' -> pure $ Sig DFloat $ BB $ exp / exp2
      P.Eq ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp == exp2
      P.Neq ra'    -> pure $ Sig DInt $ BB $ fromEnum $ exp /= exp2
      P.Lt ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp < exp2
      P.Le ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp <= exp2
      P.Gt ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp > exp2
      P.Ge ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp >= exp2
      P.Mod ra'    -> error $ "Expecting integral expression in modulo" <> errorAt ra
    DChar -> case op of
      P.Plus ra'   -> pure $ Sig DInt $ BB $ fromEnum exp + fromEnum exp2
      P.Minus ra'  -> pure $ Sig DInt $ BB $ fromEnum exp - fromEnum exp2
      P.Times ra'  -> pure $ Sig DInt $ BB $ fromEnum exp * fromEnum exp2
      P.Divide ra' -> pure $ Sig DInt $ BB $ fromEnum exp `div` fromEnum exp2
      P.Eq ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp == exp2
      P.Neq ra'    -> pure $ Sig DInt $ BB $ fromEnum $ exp /= exp2
      P.Lt ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp < exp2
      P.Le ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp <= exp2
      P.Gt ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp > exp2
      P.Ge ra'     -> pure $ Sig DInt $ BB $ fromEnum $ exp >= exp2
      P.Mod ra'    -> pure $ Sig DInt $ BB $ fromEnum exp `mod` fromEnum exp2
    _ -> error "IMPOSSIBLE"
evalConstExp e = error $ "Not a constant expression" <> errorIn e

castConstExp :: Sig BB -> DBType b -> R -> B b
castConstExp (Sig DInt (BB i)) DInt r = i
castConstExp (Sig DInt (BB i)) DFloat r = fromIntegral i
castConstExp (Sig DInt (BB i)) DChar r = toEnum i
castConstExp (Sig DFloat (BB i)) DInt r = round i
castConstExp (Sig DFloat (BB i)) DFloat r = i
castConstExp (Sig DFloat (BB i)) DChar r = toEnum (round i)
castConstExp (Sig DChar (BB i)) DInt r = fromEnum i
castConstExp (Sig DChar (BB i)) DFloat r = fromIntegral (fromEnum i)
castConstExp (Sig DChar (BB i)) DChar r = i
castConstExp (Sig DString (BB i)) DString r = i
castConstExp (Sig ty (BB i)) ty2 r = error $ "Can't cast expression of type " <> show ty <> " to " <> show ty2 <> errorAt r

unifyConstExp :: Sig BB -> Sig BB -> R -> Sig (BB :*: BB)
unifyConstExp (Sig DInt (BB i)) (Sig DInt (BB i2)) r = Sig DInt (BB i :*: BB i2)
unifyConstExp (Sig DInt (BB i)) (Sig DFloat (BB i2)) r = Sig DFloat (BB (fromIntegral i) :*: BB i2)
unifyConstExp (Sig DInt (BB i)) (Sig DChar (BB i2)) r = Sig DInt (BB i :*: BB (fromEnum i2))
unifyConstExp (Sig DFloat (BB i)) (Sig DInt (BB i2)) r = Sig DFloat (BB i :*: BB (fromIntegral i2))
unifyConstExp (Sig DFloat (BB i)) (Sig DFloat (BB i2)) r = Sig DFloat (BB i :*: BB i2)
unifyConstExp (Sig DFloat (BB i)) (Sig DChar (BB i2)) r = Sig DFloat (BB i :*: BB (fromIntegral $ fromEnum i2))
unifyConstExp (Sig DChar (BB i)) (Sig DInt (BB i2)) r = Sig DInt (BB (fromEnum i) :*: BB i2)
unifyConstExp (Sig DChar (BB i)) (Sig DFloat (BB i2)) r = Sig DFloat (BB (fromIntegral $ fromEnum i) :*: BB i2)
unifyConstExp (Sig DChar (BB i)) (Sig DChar (BB i2)) r = Sig DChar (BB i :*: BB i2)
unifyConstExp (Sig ty _) (Sig ty2 _) r = error $ "Can't unify '" <> show ty <> "' and '" <> show ty2 <> "' in a const arithmetic expression" <> errorAt r

data CtxTable ctx = CtxTable (Ctx ctx) (Table ctx)

data Program = forall global. Program (Ctx global) (StmtBlock global 'BVoid)

formProgram :: [P.GlobalDef R] -> Identity Program
formProgram defs = do
  let (gDefs, fs) = go defs
  case filter ((> 1) . length) $ groupBy (\(_, P.Name _ n1, _, _, _) (_, P.Name _ n2, _, _, _) -> n1 == n2) gDefs of
    ((_, P.Name r1 n1, _, _, _) : (_, P.Name r2 n2, _, _, _) : _) : _ -> error $
      "Redefinition of global variable '" <> T.unpack n1 <> "'" <> errorAt r1 <> " and" <> errorAt r2
    _ -> case filter ((> 1) . length) $ groupBy (\(P.Function _ _ (P.Name _ n1) _ _) (P.Function _ _ (P.Name _ n2) _ _) -> n1 == n2) fs of
      ((P.Function _ _ (P.Name r1 n1) _ _) : (P.Function _ _ (P.Name r2 _) _ _) : _) : _ -> error $
        "Redefinition of function '" <> T.unpack n1 <> "'" <> errorAt r1 <> " and" <> errorAt r2
      _ -> case find (\(P.Function _ _ (P.Name _ n) _ _) -> n `elem` ["print", "readInt", "readChar", "readFloat", "readString"]) fs of
        Just (P.Function _ _ (P.Name r n) _ _) -> error $
          "Function name clashed with builtin function '" <> T.unpack n <> "'" <> errorAt r
        _ -> do
          globalVar gDefs >>= \case
            Sig ctype (CtxTable ctx tbl) -> do
              rec funs <- traverse (formFunction tbl funs) fs
              let seqAll []                         = id
                  seqAll ((_, Sig2 _ _ fun) : funs) = seqAll funs . seq (forceFun fun)
              seqAll funs $ case lookup "main" funs of
                Nothing -> error $ "No main function"
                Just (Sig2 DNil DVoid (Fun main)) -> pure $ Program ctx main
                Just _ -> error $ "Main function should not have arguments and should return void"
  where
    go :: [P.GlobalDef R] -> ([(R, P.Name R, P.Type R, [P.Length R], Maybe (P.Exp R))], [P.GlobalDef R])
    go = foldr f ([], [])
      where
        f (P.VarDefs _ra ty defs) (x, y) = (map (\(P.Def r ls name mexp) -> (r, name, ty, ls, mexp)) defs ++ x, y)
        f g (x, y) = (x, g : y)
    globalVar :: [(R, P.Name R, P.Type R, [P.Length R], Maybe (P.Exp R))] -> Identity (Sig CtxTable)
    globalVar [] = pure $ Sig DNil (CtxTable () [])
    globalVar ((r, P.Name _ name, ty, len, mexp) : xs) = do
      Sig ctype dim <- formDim len ty
      Sig dep (CtxTable ctx tbl) <- globalVar xs
      init <- case (ctype, mexp) of
        (DBType btype, Just exp) -> fmap (\i -> castConstExp i btype (P.info exp)) $ evalConstExp exp
        (_, Just _) -> error $ "Can't assign to an array directly" <> errorAt r
        _ -> pure $ initC ctype dim
      pure $ Sig (DCons ctype dep) (CtxTable (init, ctx) ((name, Sig ctype Z) : weakenTable tbl))
    formFunction :: Table ctx -> [(Text, Sig2 (Function ctx))] -> P.GlobalDef R -> Identity (Text, Sig2 (Function ctx))
    formFunction tbl funs P.VarDefs{} = error "UNREACHABLE"
    formFunction tbl funs f@(P.Function ra rt (P.Name ra2 name) [] (P.StmtBlock ra' sts)) =
      case formRetType rt of
        Sig dep rt -> do
          block' <- formStmtBlock tbl funs [] rt False sts
          block <- checkHaveReturn rt block' name ra
          pure $ (name, Sig2 DNil rt (Fun block))
    formFunction tbl funs (P.Function ra rt na ((ty, ref, P.Name r argName, (len, mRange)) : args) sb) = do
      case ref of
        Just ra' -> do
          Sig ctype _ <- formDim (replicate len (P.Length undefined 0)) ty
          (name, Sig2 args ret fun) <- formFunction ((argName, Sig ctype Z) : weakenTable tbl) (weakenFuns funs) (P.Function ra rt na args sb)
          let x = (name, Sig2 (DCons ctype args) ret (Ref fun ctype))
          pure x
        Nothing -> if len == 0
            then do
              Sig btype _ <- pure $ formBType ty
              (name, Sig2 args ret fun) <- formFunction ((argName, Sig (DBType btype) Z) : weakenTable tbl) (weakenFuns funs) (P.Function ra rt na args sb)
              let x = (name, Sig2 (DCons (DBType btype) args) ret (Arg fun btype))
              pure x
            else error $ "Expressions passed by value must not have an array type" <> errorAt (fromJust mRange)
