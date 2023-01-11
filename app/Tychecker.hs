{-# OPTIONS_GHC -Wno-unused-matches #-}

module Tychecker where

import           Control.Applicative
import           Data.Kind
import           Data.Text           (Text)
import           Data.Type.Equality
import qualified Lexer               as L
import qualified Parser              as P

type family Dep (d :: Type) :: d -> Type

class DecEq d where
  (=?=) :: Dep d x -> Dep d y -> Maybe (x :~: y)

data Sig (f :: k -> Type) = forall a. Sig (Dep k a) (f a)

data (:*:) f g a = f a :*: g a

data BType
  = BInt
  | BFloat
  | BChar
  | BString
  deriving (Eq, Show)

type instance Dep BType = DBType

data DBType (b :: BType) where
  DInt    :: DBType 'BInt
  DFloat  :: DBType 'BFloat
  DChar   :: DBType 'BChar
  DString :: DBType 'BString

deriving instance Show (Sig DBType)
deriving instance Show (DBType b)

instance DecEq BType where
  (=?=) :: DBType x -> DBType y -> Maybe (x :~: y)
  DInt =?= DInt       = Just Refl
  DFloat =?= DFloat   = Just Refl
  DChar =?= DChar     = Just Refl
  DString =?= DString = Just Refl
  _ =?= _             = Nothing

data CType
  = BType BType
  | CArray CType
  deriving (Eq, Show)

type instance Dep CType = DCType

data DCType (c :: CType) where
  DBType  :: DBType b -> DCType ('BType b)
  DCArray :: DCType c -> DCType ('CArray c)

deriving instance Show (Sig DCType)
deriving instance Show (DCType b)

instance DecEq CType where
  (=?=) :: DCType x -> DCType y -> Maybe (x :~: y)
  DBType x =?= DBType y   = fmap (\Refl -> Refl) $ x =?= y
  DCArray x =?= DCArray y = fmap (\Refl -> Refl) $ x =?= y
  _ =?= _                 = Nothing

data Dim (c :: CType) where
  D0 :: Dim ('BType b)
  DS :: Int -> Dim c -> Dim ('CArray c)

deriving instance Show (Dim c)

type CInt = 'BType 'BInt

type family Basic (c :: CType) :: BType where
  Basic ('BType b) = b
  Basic ('CArray c) = Basic c

basic :: DCType c -> DBType (Basic c)
basic (DBType b)  = b
basic (DCArray c) = basic c

data Var (ctx :: [CType]) (ty :: CType) where
  Z :: Var (x ': xs) x
  S :: Var xs y -> Var (x ': xs) y

deriving instance Show (Sig (Var ctx))
deriving instance Show (Var ctx ty)

data Ix (ctx :: [CType]) (ty :: CType) where
  L :: Ix xs ('BType x)
  Ix :: Ix xs c -> Exp xs 'BInt -> Ix xs ('CArray c)

deriving instance Show (Sig (Ix ctx))
deriving instance Show (Ix ctx ty)

data LeftVal (ctx :: [CType]) (ty :: BType) where
  LeftVal :: Var xs c -> Ix xs c -> LeftVal xs (Basic c)

deriving instance Show (Sig (LeftVal ctx))
deriving instance Show (LeftVal ctx ty)

type Table ctx = [(Text, Sig (Var ctx))]

lookupTable :: Table ctx -> Text -> Either Text (Sig (Var ctx))
lookupTable tbl s = case lookup s tbl of
  Nothing -> Left $ "Name " <> s <> " out of range."
  Just so -> pure so

data Help ctx b = forall c. Basic c ~ b => Help (DCType c) (Ix ctx c)

formVarIx :: Table ctx -> (forall b. DBType b -> Help ctx b) -> (P.Var L.Range) -> Either String (Sig (LeftVal ctx))
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

data Exp (ctx :: [CType]) (ty :: BType) where
  Var :: LeftVal xs b -> Exp xs b
  EInt :: Int -> Exp xs 'BInt
  EAssign :: LeftVal xs b -> Exp xs b -> Exp xs b
  EAdd :: Exp xs 'BInt -> Exp xs 'BInt -> Exp xs 'BInt
  EPrintInt :: Exp xs 'BInt -> Exp xs 'BInt
  -- And more

deriving instance Show (Sig (Exp ctx))
deriving instance Show (Exp ctx ty)

formExp :: Table ctx -> (P.Exp L.Range) -> Either String (Sig (Exp ctx))
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

data Stmt (ctx :: [CType]) where
  Exp :: Exp xs x -> Stmt xs
  Def :: DCType c -> Dim c -> StmtBlock (c ': xs) -> Stmt xs

deriving instance Show (Stmt ctx)

data StmtBlock (ctx :: [CType]) where
  Empty :: StmtBlock xs
  (:.) :: Stmt xs -> StmtBlock xs -> StmtBlock xs
  Branch :: Exp xs 'BInt -> StmtBlock xs -> StmtBlock xs -> StmtBlock xs
infixr 7 :.

deriving instance Show (StmtBlock ctx)

type Renaming ctx ctx2 = forall x. Var ctx x -> Var ctx2 x

renw :: Renaming ctx ctx2 -> Var ctx2 x -> Renaming (x ': ctx) ctx2
renw r lv Z       = lv
renw r lv (S var) = r var

wren :: Renaming ctx ctx2 -> Renaming ctx (x ': ctx2)
wren r = S . r

renIx :: Renaming ctx ctx2 -> Ix ctx x -> Ix ctx2 x
renIx r L           = L
renIx r (Ix ix exp) = Ix (renIx r ix) (renExp r exp)

renLeftVal :: Renaming ctx ctx2 -> LeftVal ctx x -> LeftVal ctx2 x
renLeftVal r (LeftVal var ix) = LeftVal (r var) (renIx r ix)

renExp :: Renaming ctx ctx2 -> Exp ctx x -> Exp ctx2 x
renExp r (Var lv)         = Var (renLeftVal r lv)
renExp r (EInt n)         = EInt n
renExp r (EAssign lv exp) = EAssign (renLeftVal r lv) (renExp r exp)
renExp r (EAdd exp exp')  = EAdd (renExp r exp) (renExp r exp')
renExp r (EPrintInt exp)  = EPrintInt (renExp r exp)

renStmt :: Renaming ctx ctx2 -> Stmt ctx -> Stmt ctx2
renStmt r (Exp exp)       = Exp (renExp r exp)
renStmt r (Def dt dim sb) = Def dt dim (renStmtBlock (renw (wren r) Z) sb)

renStmtBlock :: Renaming ctx ctx2 -> StmtBlock ctx -> StmtBlock ctx2
renStmtBlock _ Empty = Empty
renStmtBlock r (st :. sb) = renStmt r st :. renStmtBlock r sb
renStmtBlock r (Branch exp sb sb') = Branch (renExp r exp) (renStmtBlock r sb) (renStmtBlock r sb')

weakenTable :: Table xs -> Table (x ': xs)
weakenTable = fmap (fmap (\(Sig ty var) -> Sig ty (S var)))

weakenStmtBlock :: StmtBlock ctx -> StmtBlock (x : ctx)
weakenStmtBlock = renStmtBlock S

instance Semigroup Bool where
  (<>) :: Bool -> Bool -> Bool
  (<>) = (||)

instance Semigroup (StmtBlock ctx) where
  (<>) :: StmtBlock ctx -> StmtBlock ctx -> StmtBlock ctx
  Empty <> stmts             = stmts
  sig :. sb <> stmts         = sig :. (sb <> stmts)
  Branch exp sb sb' <> stmts = Branch exp (sb <> stmts) (sb' <> stmts)

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
      pure $ (Branch exp (b1 <> b) b1, bool1 <> bool2)
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
