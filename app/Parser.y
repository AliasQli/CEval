{
module Parser
  ( parseC
  , parseCExp
  , Name (..)
  , Var (..)
  , UOp (..)
  , UOpMut (..)
  , BinOp (..)
  , BinOpMut (..)
  , PassArg (..)
  , Exp (..)
  , Type (..)
  , Length (..)
  , Def (..)
  , Stmt (..)
  , StmtBlock (..)
  , RetType (..)
  , GlobalDef (..)
  , info
  ) where

import Data.ByteString.Lazy.Char8 (ByteString)
import Data.Maybe (fromJust, fromMaybe)
import Data.Monoid (First (..))
import Data.Text (Text)
import Data.List (intercalate)
import Data.Void

import qualified Lexer as L
}

%name parseC program
%name parseCExp exp
%tokentype { L.RangedToken }
%error { parseError }
%errorhandlertype explist
%monad { L.Alex } { >>= } { pure }
%lexer { lexer } { L.RangedToken L.EOF _ }
%expect 0

%token
  -- Identifiers
  identifier { L.RangedToken (L.Identifier _) _ }
  -- Constants
  string     { L.RangedToken (L.String _) _ }
  int        { L.RangedToken (L.Int _) _ }
  float      { L.RangedToken (L.Float _) _ }
  char       { L.RangedToken (L.Char _) _ }
  -- -- Keywords
  if         { L.RangedToken L.If _ }
  else       { L.RangedToken L.Else _ }
  for        { L.RangedToken L.For _ }
  while      { L.RangedToken L.While _ }
  break      { L.RangedToken L.Break _ }
  continue   { L.RangedToken L.Continue _ }
  return     { L.RangedToken L.Return _ }
  'char'     { L.RangedToken L.TypeChar _ }
  'int'      { L.RangedToken L.TypeInt _ }
  'float'    { L.RangedToken L.TypeFloat _ }
  'string'   { L.RangedToken L.TypeString _ }
  'void'     { L.RangedToken L.TypeVoid _ }
  -- Arithmetic operators
  '++'       { L.RangedToken L.PlusPlus _ }
  '--'       { L.RangedToken L.MinusMinus _ }
  '+'        { L.RangedToken L.Plus _ }
  '-'        { L.RangedToken L.Minus _ }
  '*'        { L.RangedToken L.Times _ }
  '/'        { L.RangedToken L.Divide _ }
  '%'        { L.RangedToken L.Mod _ }
  -- Assignment
  '+='       { L.RangedToken L.PlusAssign _ }
  '-='       { L.RangedToken L.MinusAssign _ }
  '*='       { L.RangedToken L.TimesAssign _ }
  '/='       { L.RangedToken L.DivideAssign _ }
  '%='       { L.RangedToken L.ModAssign _ }
  '='        { L.RangedToken L.Assign _ }
  -- Comparison operators
  '=='       { L.RangedToken L.Eq _ }
  '!='       { L.RangedToken L.Neq _ }
  '<'        { L.RangedToken L.Lt _ }
  '<='       { L.RangedToken L.Le _ }
  '>'        { L.RangedToken L.Gt _ }
  '>='       { L.RangedToken L.Ge _ }
  -- Parentheses
  '('        { L.RangedToken L.LPar _ }
  ')'        { L.RangedToken L.RPar _ }
  '['        { L.RangedToken L.LBrack _ }
  ']'        { L.RangedToken L.RBrack _ }
  '{'        { L.RangedToken L.LBrace _ }
  '}'        { L.RangedToken L.RBrace _ }
  -- Separators
  ','        { L.RangedToken L.Comma _ }
  ';'        { L.RangedToken L.Semi _ }
  '&'        { L.RangedToken L.Ref _ }

-- %right else
%right ','
%right '=' '+=' '-=' '*=' '/=' '%='
%left '==' '!=' '<' '>' '<=' '>='
%left '+' '-'
%left '*' '/' '%'
-- %nonassoc '(' ')'

%%

optional(p)
  :   { Nothing }
  | p { Just $1 }

many_rev(p)
  :               { [] }
  | many_rev(p) p { $2 : $1 }

many(p)
  : many_rev(p) { reverse $1 }

sepBy_rev(p, sep)
  :                         { [] }
  | p                       { [ $1 ] }
  | sepBy_rev(p, sep) sep p { $3 : $1 }

sepBy(p, sep)
  : sepBy_rev(p, sep) { reverse $1 }

sepBy1_rev(p, sep)
  : p                        { [ $1 ] }
  | sepBy1_rev(p, sep) sep p { $3 : $1 }

sepBy1(p, sep)
  : sepBy1_rev(p, sep) { reverse $1 }

name :: { Name L.Range }
  : identifier { unTok $1 (\range (L.Identifier name) -> Name range name) }

var :: { Var L.Range }
  : name            { Var $1 }
  | var '[' exp ']' { Ix (info $1 <-> L.rtRange $4) $1 $3 }

pass_arg :: { PassArg L.Range }
  : exp       { Arg $1 }
  | '&' name  { Ref (L.rtRange $1 <-> info $2) $2 }

exp :: { Exp L.Range }
  : -- Unary operators
    '++' var                 { EUOpMut (L.rtRange $1 <-> info $2) (LInc (L.rtRange $1)) $2 }
  | '--' var                 { EUOpMut (L.rtRange $1 <-> info $2) (LDec (L.rtRange $1)) $2 }
  | var '++'                 { EUOpMut (info $1 <-> L.rtRange $2) (RInc (L.rtRange $2)) $1 }
  | var '--'                 { EUOpMut (info $1 <-> L.rtRange $2) (RDec (L.rtRange $2)) $1 }
  | '-' exp                  { EUOp (L.rtRange $1 <-> info $2) (Negate (L.rtRange $1)) $2 }
  -- Arithmetic operators
  | exp '+'  exp             { EBinOp (info $1 <-> info $3) $1 (Plus (L.rtRange $2)) $3 }
  | exp '-'  exp             { EBinOp (info $1 <-> info $3) $1 (Minus (L.rtRange $2)) $3 }
  | exp '*'  exp             { EBinOp (info $1 <-> info $3) $1 (Times (L.rtRange $2)) $3 }
  | exp '/'  exp             { EBinOp (info $1 <-> info $3) $1 (Divide (L.rtRange $2)) $3 }
  | exp '%'  exp             { EBinOp (info $1 <-> info $3) $1 (Mod (L.rtRange $2)) $3 }
  -- Assignment
  | var '+='  exp            { EBinOpMut (info $1 <-> info $3) $1 (PlusAssign (L.rtRange $2)) $3 }
  | var '-='  exp            { EBinOpMut (info $1 <-> info $3) $1 (MinusAssign (L.rtRange $2)) $3 }
  | var '*='  exp            { EBinOpMut (info $1 <-> info $3) $1 (TimesAssign (L.rtRange $2)) $3 }
  | var '/='  exp            { EBinOpMut (info $1 <-> info $3) $1 (DivideAssign (L.rtRange $2)) $3 }
  | var '%='  exp            { EBinOpMut (info $1 <-> info $3) $1 (ModAssign (L.rtRange $2)) $3 }
  | var '='  exp             { EBinOpMut (info $1 <-> info $3) $1 (Assign (L.rtRange $2)) $3 }
  -- Comparison operators
  | exp '=='  exp            { EBinOp (info $1 <-> info $3) $1 (Eq (L.rtRange $2)) $3 }
  | exp '!=' exp             { EBinOp (info $1 <-> info $3) $1 (Neq (L.rtRange $2)) $3 }
  | exp '<'  exp             { EBinOp (info $1 <-> info $3) $1 (Lt (L.rtRange $2)) $3 }
  | exp '<=' exp             { EBinOp (info $1 <-> info $3) $1 (Le (L.rtRange $2)) $3 }
  | exp '>'  exp             { EBinOp (info $1 <-> info $3) $1 (Gt (L.rtRange $2)) $3 }
  | exp '>=' exp             { EBinOp (info $1 <-> info $3) $1 (Ge (L.rtRange $2)) $3 }
  -- Variable
  | var                      { EVar (info $1) $1 }
  -- Constants
  | string                   { unTok $1 (\range (L.String x) -> EString range x) }
  | int                      { unTok $1 (\range (L.Int x) -> EInt range x) }
  | float                    { unTok $1 (\range (L.Float x) -> EFloat range x) }
  | char                     { unTok $1 (\range (L.Char x) -> EChar range x) }
  -- Function call
  | name '(' sepBy(pass_arg, ',') ')' { ECall (info $1 <-> L.rtRange $4) $1 $3 }

type :: { Type L.Range }
  : 'char'   { Char (L.rtRange $1) } 
  | 'int'    { Int (L.rtRange $1) } 
  | 'float'  { Float (L.rtRange $1) } 
  | 'string' { String (L.rtRange $1) } 

assign_exp :: { Exp L.Range }
  : '=' exp   { $2 }

array_length :: { Length L.Range }
  : '[' int ']'   { unTok $2 (\range (L.Int x) -> Length range x) }

assign_default :: { Def L.Range }
  : name many(array_length) optional(assign_exp)  { Def (info $1 <-> maybe (if null $2 then info $1 else info (last $2)) info $3) $2 $1 $3 }

forfirst :: { ForFirst L.Range }
  : type sepBy1(assign_default, ',') ';'  { ForDefs (info $1 <-> L.rtRange $3) $1 $2 }
  | exp ';'                               { ForExp (info $1 <-> L.rtRange $2) $1 }
  | ';'                                   { ForEmpty (L.rtRange $1) }

stmt :: { Stmt L.Range }
  : type sepBy1(assign_default, ',') ';'  { Defs (info $1 <-> L.rtRange $3) $1 $2 }
  | if '(' exp ')' stmt %shift            { If (L.rtRange $1 <-> info $5) $3 $5 }
  | if '(' exp ')' stmt else stmt         { IfElse (L.rtRange $1 <-> info $7) $3 $5 $7 }
  | while '(' exp ')' stmt                { While (L.rtRange $1 <-> info $5) $3 $5 }
  | for '(' forfirst exp ';' exp ')' stmt { For (L.rtRange $1 <-> info $8) $3 $4 $6 $8 }
  | break ';'                             { Break (L.rtRange $1 <-> L.rtRange $2) }
  | continue ';'                          { Continue (L.rtRange $1 <-> L.rtRange $2) }
  | return ';'                            { Return (L.rtRange $1 <-> L.rtRange $2) Nothing }
  | return exp ';'                        { Return (L.rtRange $1 <-> L.rtRange $3) (Just $2) }
  | exp ';'                               { Exp (info $1 <-> L.rtRange $2) $1 }
  | stmtblock                             { Block $1 }
  | ';'                                   { Empty (L.rtRange $1) }

stmtblock :: { StmtBlock L.Range }
  : '{' many(stmt) '}'                    { StmtBlock (L.rtRange $1 <-> L.rtRange $3) $2 }

dim :: { (Int, Maybe L.Range) }
  :             { (0, Nothing) }
  | dim '[' ']' { (fst $1 + 1, snd $1 <> Just (L.rtRange $3)) }

arg :: { (Type L.Range, Maybe L.Range, Name L.Range, (Int, Maybe L.Range)) }
  : type optional('&') name dim   { ($1, fmap L.rtRange $2, $3, $4) }

-- Introduced solely to avoid S/R conflict
global_help :: { Type L.Range -> GlobalDef L.Range }
  : sepBy1(assign_default, ',') ';'           { \ty -> VarDefs (info ty <-> L.rtRange $2) ty $1 }
  | name '(' sepBy(arg, ',') ')' stmtblock   { \ty -> Function (info ty <-> info $5) (Type ty) $1 $3 $5 }

global :: { GlobalDef L.Range }
  : type global_help                                { $2 $1 }
  | 'void' name '(' sepBy(arg, ',') ')' stmtblock  { Function (L.rtRange $1 <-> info $6) (Void (L.rtRange $1)) $2 $4 $6 }

program :: { [GlobalDef L.Range] }
  : many(global)  { $1 }

{
parseError :: (L.RangedToken, [String]) -> L.Alex a
parseError (token, ss) = do
  (L.AlexPn _ line column, _, _, _) <- L.alexGetInput
  L.alexError $ "Parse error at position " <> show line <> ":" <> show column <> ", expecting " <> intercalate ", " ss

lexer :: (L.RangedToken -> L.Alex a) -> L.Alex a
lexer = (=<< L.alexMonadScan)

-- | Build a simple node by extracting its token type and range.
unTok :: L.RangedToken -> (L.Range -> L.Token -> a) -> a
unTok (L.RangedToken tok range) ctor = ctor range tok

-- | Unsafely extracts the the metainformation field of a node.
info :: Foldable f => f a -> a
info = fromJust . getFirst . foldMap pure

-- | Performs the union of two ranges by creating a new range starting at the
-- start position of the first range, and stopping at the stop position of the
-- second range.
-- Invariant: The LHS range starts before the RHS range.
(<->) :: L.Range -> L.Range -> L.Range
L.Range a1 _ <-> L.Range _ b2 = L.Range a1 b2

instance Semigroup L.Range where
  (<>) = (<->)

-- * AST

-- | A name, /a.k.a./ identifier.
data Name a
  = Name a Text
  deriving (Functor, Foldable, Show)

-- | A variable, /a.k.a./ left value.
data Var a
  = Var (Name a)
  | Ix a (Var a) (Exp a)
  deriving (Functor, Foldable, Show)

-- | An unary operator.
data UOp a
  = Negate a
  deriving (Functor, Foldable, Show)

-- | An unary operator that modifies the operand.
data UOpMut a 
  = LInc a
  | RInc a
  | LDec a
  | RDec a
  deriving (Functor, Foldable, Show)

-- | A binary operator.
data BinOp a
  = Plus a
  | Minus a
  | Times a
  | Divide a
  | Mod a
  | Eq a
  | Neq a
  | Lt a
  | Le a
  | Gt a
  | Ge a
  deriving (Functor, Foldable, Show)

-- | A binary operator that modifies the left operand.
data BinOpMut a
  = PlusAssign a
  | MinusAssign a
  | TimesAssign a
  | DivideAssign a
  | ModAssign a
  | Assign a
  deriving (Functor, Foldable, Show)

data PassArg a
  = Arg (Exp a)
  | Ref a (Name a)
  deriving (Functor, Foldable, Show)

-- | An expression, /a.k.a/ right value.
data Exp a
  = EInt a Int
  | EFloat a Float
  | EString a Text
  | EChar a Char
  | EVar a (Var a)
  | EUOp a (UOp a) (Exp a)
  | EUOpMut a (UOpMut a) (Var a)
  | EBinOp a (Exp a) (BinOp a) (Exp a)
  | EBinOpMut a (Var a) (BinOpMut a) (Exp a)
  | ECall a (Name a) [PassArg a]
  deriving (Functor, Foldable, Show)

data Type a
  = Int a
  | Float a
  | Char a
  | String a
  deriving (Functor, Foldable, Show)

data Length a
  = Length a Int
  deriving (Functor, Foldable, Show)

data Def a
  = Def a [Length a] (Name a) (Maybe (Exp a))
  deriving (Functor, Foldable, Show)

data ForFirst a
  = ForEmpty a
  | ForDefs a (Type a) [Def a]
  | ForExp a (Exp a)
  deriving (Functor, Foldable, Show)

data Stmt a
  = Defs a (Type a) [Def a]
  | If a (Exp a) (Stmt a)
  | IfElse a (Exp a) (Stmt a) (Stmt a)
  | While a (Exp a) (Stmt a)
  | For a (ForFirst a) (Exp a) (Exp a) (Stmt a)
  | Break a
  | Continue a
  | Return a (Maybe (Exp a))
  | Exp a (Exp a)
  | Block (StmtBlock a)
  | Empty a
  deriving (Functor, Foldable, Show)

data StmtBlock a
  = StmtBlock a [Stmt a]
  deriving (Functor, Foldable, Show)

data RetType a
  = Type (Type a)
  | Void a
  deriving (Functor, Foldable, Show)

data GlobalDef a
  = VarDefs a (Type a) [Def a] -- initial value ignored
  | Function a (RetType a) (Name a) [(Type a, Maybe a, Name a, (Int, Maybe a))] (StmtBlock a)
  deriving (Functor, Foldable, Show)

}