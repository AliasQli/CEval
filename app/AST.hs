{-# LANGUAGE StrictData           #-}
{-# LANGUAGE UndecidableInstances #-}

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

mapSig :: (forall a. f a -> g a) -> Sig f -> Sig g
mapSig fun (Sig dep a) = Sig dep (fun a)

data Sig2 (f :: k -> k2 -> Type) = forall a b. Sig2 (Dep k a) (Dep k2 b) (f a b)

mapSig2 :: (forall a b. f a b -> g a b) -> Sig2 f -> Sig2 g
mapSig2 fun (Sig2 dep dep2 a) = Sig2 dep dep2 (fun a)

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

instance Show (DBType b) where
  show :: DBType b -> String
  show DInt    = "int"
  show DFloat  = "float"
  show DChar   = "char"
  show DString = "string"
  show DVoid   = "void"

deriving instance Show (Sig DBType)

instance DecEq BType where
  (=?=) :: DBType x -> DBType y -> Maybe (x :~: y)
  DInt =?= DInt       = Just Refl
  DFloat =?= DFloat   = Just Refl
  DChar =?= DChar     = Just Refl
  DString =?= DString = Just Refl
  DVoid =?= DVoid     = Just Refl
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

instance Show (DCType b) where
  show :: DCType b -> String
  show (DBType b)  = show b
  show (DCArray c) = show c ++ "[]"

deriving instance Show (Sig DCType)

instance DecEq CType where
  (=?=) :: DCType x -> DCType y -> Maybe (x :~: y)
  DBType x =?= DBType y   = fmap (\Refl -> Refl) $ x =?= y
  DCArray x =?= DCArray y = fmap (\Refl -> Refl) $ x =?= y
  _ =?= _                 = Nothing

data DList a (l :: [a]) where
  DNil :: DList a '[]
  DCons :: Dep a x -> DList a xs -> DList a (x ': xs)

type instance Dep [a] = DList a

instance DecEq a => DecEq [a] where
  (=?=) :: Dep [a] x -> Dep [a] y -> Maybe (x :~: y)
  DNil =?= DNil                   = Just Refl
  DCons dep dl =?= DCons dep' dl' = do
    Refl <- dl =?= dl'
    Refl <- dep =?= dep'
    pure Refl
  _ =?= _                         = Nothing

deriving instance Show (DList CType xs)

-- | Shape of an array.
data Dim (c :: CType) where
  D0 :: Dim ('BType b)
  DS :: Int -> Dim c -> Dim ('CArray c)

instance Show (Dim c) where
  show :: Dim c -> String
  show D0       = ""
  show (DS i d) = "[" <> show i <> "]" <> show d

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

instance Show (Var ctx ty) where
  show :: Var ctx ty -> String
  show v = "<var" ++ show (go v) ++ ">"
    where
      go :: forall ctx x. Var ctx x -> Int
      go Z     = 0
      go (S v) = go v + 1

deriving instance Show (Sig (Var ctx))

-- | Index of an array.
data Ix (ctx :: [CType]) (ty :: CType) where
  L :: Ix xs ('BType x)
  Ix :: Ix xs c -> Exp xs 'BInt -> Ix xs ('CArray c)

deriving instance Show (Sig (Ix ctx))
instance Show (Ix ctx ty) where
  show :: Ix ctx ty -> String
  show L           = ""
  show (Ix ix exp) = "[" ++ show exp ++ "]" ++ show ix

-- | A left value, /a.k.a./ fully indexed variable.
data LeftVal (ctx :: [CType]) (ty :: BType) where
  LeftVal :: Var xs c -> Ix xs c -> LeftVal xs (Basic c)

deriving instance Show (Sig (LeftVal ctx))
instance Show (LeftVal ctx ty) where
  show :: LeftVal ctx ty -> String
  show (LeftVal v ix) = show v ++ show ix

data Arith = Add | Sub | Mul | Div
  deriving (Eq, Show)

data Cmp = Eq | Ne | Gt | Lt | Ge | Le
  deriving (Eq, Show)

-- | An expression.
data Exp (ctx :: [CType]) (ty :: BType) where
  Var :: LeftVal xs b -> Exp xs b
  -- Const
  EInt :: Int -> Exp xs 'BInt
  EFloat :: Float -> Exp xs 'BFloat
  EChar :: Char -> Exp xs 'BChar
  EString :: Text -> Exp xs 'BString
  EVoid :: Exp xs 'BVoid
  -- Arith
  EArith :: DBType b -> Arith -> Exp xs b -> Exp xs b -> Exp xs b
  EMod :: Exp xs 'BInt -> Exp xs 'BInt -> Exp xs 'BInt
  -- Cmp
  ECmp :: DBType b -> Cmp -> Exp xs b -> Exp xs b -> Exp xs 'BInt
  -- Assign
  EAssign :: LeftVal xs b -> Exp xs b -> Exp xs b
  ERetAssign :: LeftVal xs b -> Exp xs b -> Exp xs b
  -- Prim call
  EPrint :: DBType b -> Exp xs b -> Exp xs b
  ERead :: DBType b -> Exp xs b
  -- Call
  ERun :: StmtBlock xs x -> Exp xs x
  -- Cast
  EI2F :: Exp xs 'BInt -> Exp xs 'BFloat
  EF2I :: Exp xs 'BFloat -> Exp xs 'BInt
  EI2C :: Exp xs 'BInt -> Exp xs 'BChar
  EC2I :: Exp xs 'BChar -> Exp xs 'BInt
  E2V :: Exp xs x -> Exp xs 'BVoid
  -- Comma
  (:&) :: Exp xs x -> Exp xs y -> Exp xs y

deriving instance Show (Sig (Exp ctx))
deriving instance Show (Exp ctx ty)

-- | A statement.
data Stmt (ctx :: [CType]) (b :: BType) where
  Exp :: Exp xs y -> Stmt xs x
  Branch :: Exp xs 'BInt -> StmtBlock xs x -> StmtBlock xs x -> Stmt xs x
  Loop :: Exp xs 'BInt -> StmtBlock xs x -> Stmt xs x
  Def :: DCType c -> Dim c -> StmtBlock (c ': xs) x -> Stmt xs x
  Return :: Exp xs x -> Stmt xs x
  Break :: Stmt xs x
  Continue :: Stmt xs x

deriving instance Show (Sig (Stmt ctx))
deriving instance Show (Stmt ctx x)

-- | A statement block.
data StmtBlock (ctx :: [CType]) (b :: BType) where
  Empty :: StmtBlock xs x
  Lazy :: ~(StmtBlock xs x) -> StmtBlock xs x
  (:.) :: Stmt xs x -> ~(StmtBlock xs x) -> StmtBlock xs x
infixr 7 :.

deriving instance Show (Sig (StmtBlock ctx))
instance Show (StmtBlock ctx x) where
  show :: StmtBlock ctx x -> String
  show Empty = ""
  show (Lazy _) = "<fun call>"
  show (s :. ss) = show s <> "; " <> show ss

instance Semigroup (StmtBlock ctx b) where
  (<>) :: StmtBlock ctx b -> StmtBlock ctx b -> StmtBlock ctx b
  Empty <> stmts     = stmts
  Lazy a <> stmts    = Lazy $ a <> stmts
  sig :. sb <> stmts = sig :. (sb <> stmts)

data Function (global :: [CType]) (args :: [CType]) (ret :: BType) where
  Fun :: ~(StmtBlock ctx x) -> Function ctx '[] x
  Arg :: Function ('BType a ': ctx) as x -> DBType a -> Function ctx ('BType a ': as) x
  Ref :: Function (a ': ctx) as x -> DCType a -> Function ctx (a ': as) x

deriving instance Show (Function global ctx x)
deriving instance Show (Sig2 (Function global))

forceFun :: Function global ctx x -> ()
forceFun (Fun sb)  = forceSB sb
forceFun (Arg f b) = b `seq` forceFun f
forceFun (Ref f c) = c `seq` forceFun f

forceC :: DCType c -> ()
forceC (DBType b)  = b `seq` ()
forceC (DCArray c) = forceC c

forceSB :: StmtBlock ctx x -> ()
forceSB (stmt :. sb) = forceS stmt `seq` forceSB sb
forceSB (Lazy _)     = ()
forceSB Empty        = ()

forceS :: Stmt ctx x -> ()
forceS (Branch exp sb sb') = exp `seq` forceSB sb `seq` forceSB sb'
forceS (Loop exp sb)       = exp `seq` forceSB sb
forceS (Def dt dim sb)     = dt `seq` forceDim dim `seq` forceSB sb
forceS (Return e)          = e `seq` ()
forceS (Exp e)             = e `seq` ()
forceS _                   = ()

forceDim :: Dim c -> ()
forceDim D0       = ()
forceDim (DS i d) = i `seq` forceDim d

-- forceExp :: E

-- forceExp
type family AppendRev ctx as where
  AppendRev ctx '[] = ctx
  AppendRev ctx (a ': as) = AppendRev (a ': ctx) as

-- | Map from variable name to its /de Bruijn/ index, used during typechecking.
type Table ctx = [(Text, Sig (Var ctx))]

lookupTable :: Table ctx -> Text -> Either Text (Sig (Var ctx))
lookupTable tbl s = case lookup s tbl of
  Nothing -> Left $ "Name " <> s <> " out of range."
  Just so -> pure so

-- * Renaming and weakening

type Renaming ctx ctx2 = forall x. Var ctx x -> Var ctx2 x

renw :: Renaming ctx ctx2 -> Var ctx2 x -> Renaming (x ': ctx) ctx2
renw _r v Z       = v
renw r _v (S var) = r var

wren :: Renaming ctx ctx2 -> Renaming ctx (x ': ctx2)
wren r = S . r

-- Simply, renVar = id.

renIx :: Renaming ctx ctx2 -> Ix ctx x -> Ix ctx2 x
renIx _ L           = L
renIx r (Ix ix exp) = Ix (renIx r ix) (renExp r exp)

renLeftVal :: Renaming ctx ctx2 -> LeftVal ctx x -> LeftVal ctx2 x
renLeftVal r (LeftVal var ix) = LeftVal (r var) (renIx r ix)

renExp :: Renaming ctx ctx2 -> Exp ctx x -> Exp ctx2 x
renExp r (Var lv)              = Var (renLeftVal r lv)
renExp _ (EInt n)              = EInt n
renExp _ (EFloat n)            = EFloat n
renExp _ (EChar n)             = EChar n
renExp _ (EString n)           = EString n
renExp r (EAssign lv exp)      = EAssign (renLeftVal r lv) (renExp r exp)
renExp r (ERetAssign lv exp)   = ERetAssign (renLeftVal r lv) (renExp r exp)
renExp r (EArith a b exp exp') = EArith a b (renExp r exp) (renExp r exp')
renExp r (EMod exp exp')       = EMod (renExp r exp) (renExp r exp')
renExp r (ECmp a b exp exp')   = ECmp a b (renExp r exp) (renExp r exp')
renExp r (EPrint b exp)        = EPrint b (renExp r exp)
renExp _ (ERead b)             = ERead b
renExp r (ERun stmts)          = ERun (renStmtBlock r stmts)
renExp _ EVoid                 = EVoid
renExp r (EI2F exp)            = EI2F (renExp r exp)
renExp r (EF2I exp)            = EF2I (renExp r exp)
renExp r (EI2C exp)            = EI2C (renExp r exp)
renExp r (EC2I exp)            = EC2I (renExp r exp)
renExp r (E2V exp)             = E2V (renExp r exp)
renExp r (exp :& exp2)         = renExp r exp :& renExp r exp2

renStmt :: Renaming ctx ctx2 -> Stmt ctx x -> Stmt ctx2 x
renStmt r (Exp exp)           = Exp (renExp r exp)
renStmt r (Def dt dim sb)     = Def dt dim (renStmtBlock (renw (wren r) Z) sb)
renStmt r (Branch exp sb sb') = Branch (renExp r exp) (renStmtBlock r sb) (renStmtBlock r sb')
renStmt r (Loop exp sb)       = Loop (renExp r exp) (renStmtBlock r sb)
renStmt r (Return exp)        = Return (renExp r exp)
renStmt _ Break               = Break
renStmt _ Continue            = Continue

renStmtBlock :: Renaming ctx ctx2 -> StmtBlock ctx x -> StmtBlock ctx2 x
renStmtBlock _ Empty        = Empty
renStmtBlock r (Lazy stmts) = Lazy $ renStmtBlock r stmts
renStmtBlock r (st :. sb)   = renStmt r st :. renStmtBlock r sb

renFunction :: Renaming ctx ctx2 -> Function ctx args x -> Function ctx2 args x
renFunction r (Fun sb)      = Fun (renStmtBlock r sb)
renFunction r (Arg func dt) = Arg (renFunction (renw (wren r) Z) func) dt
renFunction r (Ref func dt) = Ref (renFunction (renw (wren r) Z) func) dt

weakenStmtBlock :: StmtBlock ctx x -> StmtBlock (c : ctx) x
weakenStmtBlock = renStmtBlock S

weakenFun :: Function ctx args x -> Function (c : ctx) args x
weakenFun = renFunction S

weakenTable :: Table xs -> Table (x ': xs)
weakenTable = fmap (fmap (\(Sig ty var) -> Sig ty (S var)))

type Funs ctx = [(Text, Sig2 (Function ctx))]

weakenFuns :: Funs ctx -> Funs (c ': ctx)
weakenFuns = fmap (fmap (\(Sig2 arg ty fun) -> Sig2 arg ty (weakenFun fun)))
