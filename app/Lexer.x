{
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Lexer
  ( -- * Invoking Alex
    Alex
  , AlexPosn (..)
  , alexGetInput
  , alexError
  , runAlex
  , alexMonadScan

  , Range (..)
  , RangedToken (..)
  , Token (..)
  , scanMany
  ) where

import Control.Monad (when)
import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Text (Text)
import Data.Text.Encoding
}

%wrapper "monadUserState-bytestring"

$digit = [0-9]
$alpha = [a-zA-Z]

@id = ($alpha | \_) ($alpha | $digit | \_)*

tokens :-

<0> $white+ ;

<0>       "/*" { nestComment `andBegin` comment }
<0>       "*/" { \_ _ -> alexError "Error: unexpected closing comment" }
<comment> "/*" { nestComment }
<comment> "*/" { unnestComment }
<comment> .    ;
<comment> \n   ;

<0>       "//" { begin lcomment }
<lcomment> \n  { begin 0 }
<lcomment> .   ;

-- Keywords
<0> if      { tok If }
<0> else    { tok Else }
<0> while   { tok While }
<0> for     { tok For }
<0> break   { tok Break }
<0> continue{ tok Continue }
<0> return  { tok Return }
<0> string  { tok TypeString }
<0> char    { tok TypeChar }
<0> int     { tok TypeInt }
<0> float   { tok TypeFloat }
<0> void    { tok TypeVoid }

-- Assignment
<0> "+="    { tok PlusAssign }
<0> "-="    { tok MinusAssign }
<0> "*="    { tok TimesAssign }
<0> "/="    { tok DivideAssign }
<0> "%="    { tok ModAssign }
<0> "="     { tok Assign }

-- Arithmetic operators
<0> "++"    { tok PlusPlus }
<0> "--"    { tok MinusMinus }
<0> "+"     { tok Plus }
<0> "-"     { tok Minus }
<0> "*"     { tok Times }
<0> "/"     { tok Divide }
<0> "%"     { tok Mod }

-- Comparison operators
<0> "=="    { tok Eq }
<0> "!="    { tok Neq }
<0> "<="    { tok Le }
<0> "<"     { tok Lt }
<0> ">="    { tok Ge }
<0> ">"     { tok Gt }

-- Parenthesis
<0> "("     { tok LPar }
<0> ")"     { tok RPar }
<0> "["     { tok LBrack }
<0> "]"     { tok RBrack }
<0> "{"     { tok LBrace }
<0> "}"     { tok RBrace }

-- Separators
<0> ","     { tok Comma }
<0> ";"     { tok Semi }
<0> "&"     { tok Ref }

-- Identifiers
<0> @id     { tokId }

-- Constants
<0> $digit*\.$digit+    { tokFloat }
<0> $digit+             { tokInt }
<0> \'\\?[^\']\'        { tokChar }
<0> \"[^\"]*\"          { tokString }

{
data AlexUserState = AlexUserState
  { nestLevel :: Int
  }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState
  { nestLevel = 0
  }

get :: Alex AlexUserState
get = Alex $ \s -> Right (s, alex_ust s)

put :: AlexUserState -> Alex ()
put s' = Alex $ \s -> Right (s{alex_ust = s'}, ())

modify :: (AlexUserState -> AlexUserState) -> Alex ()
modify f = Alex $ \s -> Right (s{alex_ust = f (alex_ust s)}, ())

alexEOF :: Alex RangedToken
alexEOF = do
  (pos, _, _, _) <- alexGetInput
  startCode <- alexGetStartCode
  when (startCode == comment) $
    alexError "Error: unclosed comment"
  pure $ RangedToken EOF (Range pos pos)

data Range = Range
  { start :: AlexPosn
  , stop :: AlexPosn
  } deriving (Eq)

instance Show Range where
  show (Range (AlexPn _ l1 c1) (AlexPn _ l2 c2)) = show l1 <> ":" <> show c1 <> "-" <> show l2 <> ":" <> show c2

data RangedToken = RangedToken
  { rtToken :: Token
  , rtRange :: Range
  } deriving (Eq, Show)

data Token
  -- Identifiers
  = Identifier Text
  -- Constants
  | String Text
  | Int Int
  | Float Float
  | Char Char
  -- Keywords
  | If
  | Else
  | While
  | For
  | Break
  | Continue
  | Return
  | TypeString
  | TypeChar
  | TypeInt
  | TypeFloat
  | TypeVoid
  -- Arithmetic operators
  | Plus
  | Minus
  | Times
  | Divide
  | Mod
  | PlusPlus
  | MinusMinus
  -- Assignment
  | PlusAssign
  | MinusAssign
  | TimesAssign
  | DivideAssign
  | ModAssign
  | Assign
  -- Comparison operators
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge
  -- Logical operators
  | And
  | Or
  -- Parenthesis
  | LPar
  | RPar
  | LBrack
  | RBrack
  | LBrace
  | RBrace
  -- Separators
  | Comma
  | Semi
  | Ref
  | EOF
  deriving (Eq, Show)

mkRange :: AlexInput -> Int64 -> Range
mkRange (start, _, str, _) len = Range{start = start, stop = stop}
  where
    stop = BS.foldl' alexMove start $ BS.take len str

tok :: Token -> AlexAction RangedToken
tok ctor inp len =
  pure RangedToken
    { rtToken = ctor
    , rtRange = mkRange inp len
    }

tokId :: AlexAction RangedToken
tokId inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Identifier $ decodeUtf8 $ BS.toStrict $ BS.take len str
    , rtRange = mkRange inp len
    }

tokFloat :: AlexAction RangedToken
tokFloat inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Float $ read $ (++ "0") $ ("0" ++) $ BS.unpack $ BS.take len str
    , rtRange = mkRange inp len
    }

tokInt :: AlexAction RangedToken
tokInt inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Int $ read $ BS.unpack $ BS.take len str
    , rtRange = mkRange inp len
    }

tokChar :: AlexAction RangedToken
tokChar inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Char $ read $ BS.unpack $ BS.take len str
    , rtRange = mkRange inp len
    }

tokString :: AlexAction RangedToken
tokString inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = String $ read $ BS.unpack $ BS.take len str
    , rtRange = mkRange inp len
    }

nestComment, unnestComment :: AlexAction RangedToken
nestComment input len = do
  modify $ \s -> s{nestLevel = nestLevel s + 1}
  skip input len
unnestComment input len = do
  state <- get
  let level = nestLevel state - 1
  put state{nestLevel = level}
  when (level == 0) $
    alexSetStartCode 0
  skip input len

scanMany :: ByteString -> Either String [RangedToken]
scanMany input = runAlex input go
  where
    go = do
      output <- alexMonadScan
      if rtToken output == EOF
        then pure [output]
        else (output :) <$> go
}