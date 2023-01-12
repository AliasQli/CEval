module Evaluator where

import           AST
import           Control.Lens               hiding (Empty)
import           Control.Monad.State
import           Control.Monad.Except
import           Data.ByteString.Lazy.Char8 (ByteString)
import           Data.Functor
import           Data.Kind
import           Data.Text                  (Text)
import           Data.Vector                (Vector)
import qualified Data.Vector                as V
import qualified Data.Vector.Mutable        as MV
import qualified Lexer                      as L
import qualified Parser                     as P
import           Tychecker

newtype Len s a = Len (Lens' s a)

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

vectorIx :: Int -> Lens' (Vector a) a
vectorIx i = lens (V.! i) (\v a -> V.modify (\mv -> MV.write mv i a) v)

initB :: DBType b -> B b
initB DInt    = 0
initB DFloat  = 0
initB DChar   = '\0'
initB DString = ""
initB DVoid   = ()

initC :: DCType c -> Dim c -> C c
initC (DBType b) D0          = initB b
initC (DCArray c) (DS n dim) = V.replicate n (initC c dim)

evalVar :: Var ctx c -> Lens' (Ctx ctx) (C c)
evalVar Z       = _1
evalVar (S var) = _2 . evalVar var

evalIx :: Ix ctx c -> StateT (Ctx ctx) IO (Len (C c) (B (Basic c)))
evalIx L            = pure $ Len id
evalIx (Ix ix exp) = do
  i <- evalExp exp
  Len lens <- evalIx ix
  pure $ Len $ vectorIx i . lens

evalLeftVal :: forall ctx b. LeftVal ctx b -> StateT (Ctx ctx) IO (Len (Ctx ctx) (B b))
evalLeftVal (LeftVal var ix) = do
  Len lens <- evalIx ix
  pure $ Len $ evalVar var . lens

evalExp :: Exp ctx b -> StateT (Ctx ctx) IO (B b)
evalExp (Var lv) = do
  Len lens <- evalLeftVal lv
  use lens
evalExp (EInt n) = pure n
evalExp (EAssign lv exp) = do
  Len lens <- evalLeftVal lv
  val <- evalExp exp
  lens .= val
  pure val
evalExp (EAdd exp exp2) = do
  exp <- evalExp exp
  exp2 <- evalExp exp2
  pure (exp + exp2)
evalExp (EPrintInt exp) = do
  exp <- evalExp exp
  liftIO $ print exp
  pure exp
evalExp EVoid = pure ()
evalExp (EI2F exp) = fmap fromIntegral $ evalExp exp
evalExp (EF2I exp) = fmap round $ evalExp exp
evalExp (EI2C exp) = fmap toEnum $ evalExp exp
evalExp (EC2I exp) = fmap fromEnum $ evalExp exp
evalExp (E2V exp)  = evalExp exp $> ()

evalStmt :: Stmt ctx x -> ExceptT (B x) (StateT (Ctx ctx) IO) Bool
evalStmt (Exp exp) = lift (evalExp exp) $> False
evalStmt (Branch exp sb sb') = do
  cond <- lift $ evalExp exp
  if cond /= 0
    then evalStmts sb
    else evalStmts sb'
evalStmt (Loop exp sb) = do
  cond <- lift $ evalExp exp
  if cond /= 0
    then do
      break <- evalStmts sb
      if break
        then pure False
        else evalStmt (Loop exp sb)
    else pure False
evalStmt (Def dt dim sb) = mapExceptT (\(StateT f) -> StateT $ fmap (fmap snd) . f . (initC dt dim,)) (evalStmts sb)

evalStmts :: StmtBlock ctx x -> ExceptT (B x) (StateT (Ctx ctx) IO) Bool
evalStmts (Return exp) = lift (evalExp exp) >>= throwError
evalStmts Break        = pure True
evalStmts Empty        = pure False
evalStmts (st :. sb)   = evalStmt st >> evalStmts sb

-- * Tests

run :: ByteString -> IO ()
run bs = do
  case L.runAlex bs P.parseC of
    Left e -> fail e
    Right (P.StmtBlock _ stmts) -> do
      case formStmtBlock [] DVoid (stmts ++ [P.Return undefined Nothing]) of
        Left e -> fail e
        Right (s :: StmtBlock '[] 'BVoid) -> do
          runStateT (runExceptT (evalStmts s)) ()
          pure ()
