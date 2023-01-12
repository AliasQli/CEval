module AST where

import           Data.Kind
import           Data.Text          (Text)
import           Data.Type.Equality

-- * DT utils

-- | Maps to corerresponding singleton type.
type family Dep (d :: Type) :: d -> Type

class DecEq d where
  -- | Decidable type equality.
  (=?=) :: Dep d x -> Dep d y -> Maybe (x :~: y)

-- | Sigma type.
data Sig (f :: k -> Type) = forall a. Sig (Dep k a) (f a)

-- | Functor product.
data (:*:) f g a = f a :*: g a

-- * Type definition

-- | Basic type.
data BType
  = BInt
  | BFloat
  | BChar
  | BString
  | BVoid -- ^ C's @void@, Haskell's `()'.
  deriving (Eq, Show)

type instance Dep BType = DBType

data DBType (b :: BType) where
  DInt    :: DBType 'BInt
  DFloat  :: DBType 'BFloat
  DChar   :: DBType 'BChar
  DString :: DBType 'BString
  DVoid   :: DBType 'BVoid

deriving instance Show (Sig DBType)
deriving instance Show (DBType b)

instance DecEq BType where
  (=?=) :: DBType x -> DBType y -> Maybe (x :~: y)
  DInt =?= DInt       = Just Refl
  DFloat =?= DFloat   = Just Refl
  DChar =?= DChar     = Just Refl
  DString =?= DString = Just Refl
  _ =?= _             = Nothing

-- | C type.
data CType
  = BType BType
  | CArray CType
  deriving (Eq, Show)

type CInt = 'BType 'BInt
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

-- | Shape of an array.
data Dim (c :: CType) where
  D0 :: Dim ('BType b)
  DS :: Int -> Dim c -> Dim ('CArray c)

deriving instance Show (Dim c)

-- | Extract the basic type.
type family Basic (c :: CType) :: BType where
  Basic ('BType b) = b
  Basic ('CArray c) = Basic c

basic :: DCType c -> DBType (Basic c)
basic (DBType b)  = b
basic (DCArray c) = basic c

-- * AST definition

-- | Variable, that is, a /de Bruijn/ index of the context.
data Var (ctx :: [CType]) (ty :: CType) where
  Z :: Var (x ': xs) x
  S :: Var xs y -> Var (x ': xs) y

deriving instance Show (Sig (Var ctx))
deriving instance Show (Var ctx ty)

-- | Index of an array.
data Ix (ctx :: [CType]) (ty :: CType) where
  L :: Ix xs ('BType x)
  Ix :: Ix xs c -> Exp xs 'BInt -> Ix xs ('CArray c)

deriving instance Show (Sig (Ix ctx))
deriving instance Show (Ix ctx ty)

-- | A left value, /a.k.a./ fully indexed variable.
data LeftVal (ctx :: [CType]) (ty :: BType) where
  LeftVal :: Var xs c -> Ix xs c -> LeftVal xs (Basic c)

deriving instance Show (Sig (LeftVal ctx))
deriving instance Show (LeftVal ctx ty)

-- | An expression.
data Exp (ctx :: [CType]) (ty :: BType) where
  Var :: LeftVal xs b -> Exp xs b
  EInt :: Int -> Exp xs 'BInt
  EAssign :: LeftVal xs b -> Exp xs b -> Exp xs b
  EAdd :: Exp xs 'BInt -> Exp xs 'BInt -> Exp xs 'BInt
  EPrintInt :: Exp xs 'BInt -> Exp xs 'BInt
  -- And more

deriving instance Show (Sig (Exp ctx))
deriving instance Show (Exp ctx ty)

-- | A statement.
data Stmt (ctx :: [CType]) where
  Exp :: Exp xs x -> Stmt xs
  Def :: DCType c -> Dim c -> StmtBlock (c ': xs) -> Stmt xs

deriving instance Show (Stmt ctx)

-- | A statement block.
data StmtBlock (ctx :: [CType]) where
  Empty :: StmtBlock xs
  (:.) :: Stmt xs -> StmtBlock xs -> StmtBlock xs
  Branch :: Exp xs 'BInt -> StmtBlock xs -> StmtBlock xs -> StmtBlock xs
infixr 7 :.

deriving instance Show (StmtBlock ctx)

instance Semigroup Bool where
  (<>) :: Bool -> Bool -> Bool
  (<>) = (||)

instance Semigroup (StmtBlock ctx) where
  (<>) :: StmtBlock ctx -> StmtBlock ctx -> StmtBlock ctx
  Empty <> stmts             = stmts
  sig :. sb <> stmts         = sig :. (sb <> stmts)
  Branch exp sb sb' <> stmts = Branch exp (sb <> stmts) (sb' <> stmts)

-- | Map from variable name to its /de Bruijn/ index, used during typechecking.
type Table ctx = [(Text, Sig (Var ctx))]

lookupTable :: Table ctx -> Text -> Either Text (Sig (Var ctx))
lookupTable tbl s = case lookup s tbl of
  Nothing -> Left $ "Name " <> s <> " out of range."
  Just so -> pure so

-- * Renaming and weakening

type Renaming ctx ctx2 = forall x. Var ctx x -> Var ctx2 x

renw :: Renaming ctx ctx2 -> Var ctx2 x -> Renaming (x ': ctx) ctx2
renw _r lv Z       = lv
renw r _lv (S var) = r var

wren :: Renaming ctx ctx2 -> Renaming ctx (x ': ctx2)
wren r = S . r

-- Simply, renVar = S.

renIx :: Renaming ctx ctx2 -> Ix ctx x -> Ix ctx2 x
renIx _ L           = L
renIx r (Ix ix exp) = Ix (renIx r ix) (renExp r exp)

renLeftVal :: Renaming ctx ctx2 -> LeftVal ctx x -> LeftVal ctx2 x
renLeftVal r (LeftVal var ix) = LeftVal (r var) (renIx r ix)

renExp :: Renaming ctx ctx2 -> Exp ctx x -> Exp ctx2 x
renExp r (Var lv)         = Var (renLeftVal r lv)
renExp _ (EInt n)         = EInt n
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

weakenStmtBlock :: StmtBlock ctx -> StmtBlock (x : ctx)
weakenStmtBlock = renStmtBlock S

weakenTable :: Table xs -> Table (x ': xs)
weakenTable = fmap (fmap (\(Sig ty var) -> Sig ty (S var)))
