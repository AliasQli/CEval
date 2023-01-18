module Evaluator where

import           AST
import           Control.Lens               hiding (Empty)
import           Control.Monad.Except
import           Control.Monad.State
import           Data.ByteString.Lazy.Char8 (ByteString)
import           Data.Functor
import           Data.Vector                (Vector)
import qualified Data.Vector                as V
import qualified Data.Vector.Mutable        as MV
import qualified Lexer                      as L
import qualified Parser                     as P
import           Tychecker

newtype Len s a = Len (Lens' s a)

vectorIx :: Int -> Lens' (Vector a) a
vectorIx i = lens (V.! i) (\v a -> V.modify (\mv -> MV.write mv i a) v)

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
evalExp (ERun stmts) = evalStmtsAsFun stmts
evalExp EVoid = pure ()
evalExp (EI2F exp) = fmap fromIntegral $ evalExp exp
evalExp (EF2I exp) = fmap round $ evalExp exp
evalExp (EI2C exp) = fmap toEnum $ evalExp exp
evalExp (EC2I exp) = fmap fromEnum $ evalExp exp
evalExp (E2V exp)  = evalExp exp $> ()

data Next = B | C | N deriving Eq

evalStmt :: Stmt ctx x -> ExceptT (B x) (StateT (Ctx ctx) IO) Next
evalStmt (Exp exp) = lift (evalExp exp) $> N
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
      if break == B
        then pure N
        else evalStmt (Loop exp sb)
    else pure N
evalStmt (Def dt dim sb) = mapExceptT (\(StateT f) -> StateT $ fmap (fmap snd) . f . (initC dt dim,)) (evalStmts sb)
evalStmt (Return exp) = lift (evalExp exp) >>= throwError
evalStmt Break        = pure B
evalStmt Continue     = pure C

evalStmts :: StmtBlock ctx x -> ExceptT (B x) (StateT (Ctx ctx) IO) Next
evalStmts Empty      = pure N
evalStmts (st :. sb) = do
  next <- evalStmt st
  case next of 
    B -> pure B
    C -> pure C
    N -> evalStmts sb

evalStmtsAsFun :: StmtBlock ctx x -> StateT (Ctx ctx) IO (B x)
evalStmtsAsFun stmts = do
  eth <- runExceptT $ evalStmts stmts
  case eth of
    Left b  -> pure b
    Right _ -> error "IMPOSSIBLE"

-- * Tests

disp :: ByteString -> IO ()
disp bs = do
  case L.runAlex bs P.parseC of
    Left e -> fail e
    Right gDefs -> do
      case formProgram gDefs of
        Identity (Program _ _ funs) -> case lookup "main" funs of
          Nothing -> fail "main function not found"
          Just (Sig2 DNil DVoid (Fun sb)) -> do
            print sb
            pure ()
          Just _ -> fail "main function type incorrect"

run :: ByteString -> IO ()
run bs = do
  case L.runAlex bs P.parseC of
    Left e -> fail e
    Right gDefs -> do
      case formProgram gDefs of
        Identity (Program _ ctx funs) -> case lookup "main" funs of
          Nothing -> fail "main function not found"
          Just (Sig2 DNil DVoid (Fun sb)) -> do
            let fsb = forceSB sb
            fsb `seq` putStrLn "-----------"
            runStateT (evalStmtsAsFun sb) ctx
            pure ()
          Just _ -> fail "main function type incorrect"
