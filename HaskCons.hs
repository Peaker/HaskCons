{-# LANGUAGE GADTs, KindSignatures #-}
module HaskCons
  ( IntSize(..), ParserMaker, Parser
  , doc, bytes, unsigned, ignoreInput, (***), (&&&)
  , pair
  , parse
  , parserOutputCType, CType(..)
  , formatCType, declsCType
  , parserCode, Plan(..)
  , id, (.)
  ) where

import Control.Arrow (second)
import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Binary.Get
import Data.Int
import Prelude hiding (id, (.))
import qualified Data.ByteString.Lazy as LBS

data IntSize = Word8 | Word16 | Word32 | Word64
  deriving (Eq, Ord, Read, Show)

data ParserMaker :: * -> * -> * where
  Id :: ParserMaker i i
  Dot :: ParserMaker i1 i2 -> ParserMaker i0 i1 -> ParserMaker i0 i2
  Split :: ParserMaker a (a, a)
  Vertical :: ParserMaker i0 o0 -> ParserMaker i1 o1 -> ParserMaker (i0, i1) (o0, o1)
  Bytes :: ParserMaker Int64 LBS.ByteString
  Doc :: String -> ParserMaker a b -> ParserMaker a b
  PureIntSize :: IntSize -> Parser IntSize
  Unsigned :: Integral a => ParserMaker IntSize a
  IgnoreInput :: Parser b -> ParserMaker a b

bytes :: ParserMaker Int64 LBS.ByteString
bytes = Bytes

doc :: String -> ParserMaker a b -> ParserMaker a b
doc = Doc

unsigned :: Integral a => IntSize -> Parser a
unsigned intSize = Unsigned . PureIntSize intSize

ignoreInput :: Parser b -> ParserMaker a b
ignoreInput = IgnoreInput

-- Like the Control.Arrow combinators:
(***) :: ParserMaker i0 o0 -> ParserMaker i1 o1 -> ParserMaker (i0, i1) (o0, o1)
(***) = Vertical

(&&&) :: ParserMaker i o0 -> ParserMaker i o1 -> ParserMaker i (o0, o1)
f &&& g = (f *** g) . Split

pair :: ParserMaker i o -> Parser b -> ParserMaker i (o, b)
pair a b = a >>> (id &&& ignoreInput b)

type Parser = ParserMaker ()

instance Category ParserMaker where
  id = Id
  (.) = Dot

parse :: ParserMaker a b -> a -> Get b
parse Id x = pure x
parse (Dot after before) x = parse before x >>= parse after
parse (Vertical one two) (x, y) = (,) <$> parse one x <*> parse two y
parse Bytes len = getLazyByteString len
parse (Doc _ parser) x = parse parser x
parse Split x = pure (x, x)
parse (PureIntSize x) () = pure x
parse Unsigned Word8 = fromIntegral <$> getWord8
parse Unsigned Word16 = fromIntegral <$> getWord16le
parse Unsigned Word32 = fromIntegral <$> getWord32le
parse Unsigned Word64 = fromIntegral <$> getWord64le
parse (IgnoreInput parser) _ = parse parser ()

data CType = Void | Primitive (String -> String) | TypeProduct String CType CType | CDoc String CType

atomicCType :: String -> CType
atomicCType typeName = Primitive mkDecl
  where
    mkDecl name = typeName ++ " " ++ name

-- intSizeCName :: IntSize -> String
-- intSizeCName Word8 = "uint8_t"
-- intSizeCName Word16 = "uint16_t"
-- intSizeCName Word32 = "uint32_t"
-- intSizeCName Word64 = "uint64_t"

intSizeToInt :: IntSize -> Int
intSizeToInt Word8 = 1
intSizeToInt Word16 = 2
intSizeToInt Word32 = 4
intSizeToInt Word64 = 8

-- TODO: CType can be a GADT with tuples for products, to avoid the
-- runtime error here
onTypeProduct :: (CType -> CType -> a) -> CType -> a
onTypeProduct _ Void = error "Expecting a TypeProduct!"
onTypeProduct _ (Primitive _) = error "Expecting a TypeProduct!"
onTypeProduct f (TypeProduct _name x y) = f x y
onTypeProduct f (CDoc _ inner) = onTypeProduct f inner

typeProductFst :: CType -> CType
typeProductFst = onTypeProduct const

typeProductSnd :: CType -> CType
typeProductSnd = onTypeProduct (flip const)

mkTypeProduct :: CType -> CType -> NameGen CType
mkTypeProduct x y = do
  name <- mkName "s_"
  pure $ TypeProduct name x y

parserMakerOutputCType :: ParserMaker i o -> CType -> NameGen CType
parserMakerOutputCType Id i = pure i
parserMakerOutputCType (Dot after before) i =
  parserMakerOutputCType after =<< parserMakerOutputCType before i
parserMakerOutputCType Split i = mkTypeProduct i i
parserMakerOutputCType (Vertical one two) i =
  join $
  mkTypeProduct
  <$> parserMakerOutputCType one (typeProductFst i)
  <*> parserMakerOutputCType two (typeProductSnd i)
parserMakerOutputCType Bytes _ =
  mkTypeProduct (atomicCType "size_t") (atomicCType "char *")
parserMakerOutputCType (PureIntSize _) _ = pure $ atomicCType "uint8_t"
parserMakerOutputCType Unsigned _ = pure $ atomicCType "uint64_t" -- dynamic int size
parserMakerOutputCType (Doc d parser) i = CDoc d <$> parserMakerOutputCType parser i
parserMakerOutputCType (IgnoreInput parser) _ = parserMakerOutputCType parser Void

parserOutputCType :: Parser a -> CType
parserOutputCType = runNameGen . (`parserMakerOutputCType` Void)

type NameGen = State Int

runNameGen :: NameGen a -> a
runNameGen = (`evalState` 0)

mkName :: String -> NameGen String
mkName prefix = modify (+1) >> (prefix ++) . show <$> get

data Plan = Plan
  { planValName :: String
  , planType :: CType
  }

planInProduct :: String -> (CType -> CType) -> Plan -> Plan
planInProduct attr typInProduct (Plan valName typ) =
  Plan
    { planValName = valName ++ "." ++ attr
    , planType = typInProduct typ
    }

planFst :: Plan -> Plan
planFst = planInProduct "fst" typeProductFst

planSnd :: Plan -> Plan
planSnd = planInProduct "snd" typeProductSnd

forwardInputStream :: [Char] -> [[Char]]
forwardInputStream howMuch =
  [ "inputStream += " ++ howMuch ++ ";"
  , "bytesLeft -= " ++ howMuch ++ ";"
  ]

tellMkTypeProduct :: CType -> CType -> WriterT [String] NameGen CType
tellMkTypeProduct x y = do
  tp <- lift $ mkTypeProduct x y
  tell $ declsCType tp
  pure tp

parserMakerPlan :: ParserMaker a b -> Plan -> WriterT [String] NameGen Plan
parserMakerPlan Id i = pure i
parserMakerPlan (Dot after before) i = parserMakerPlan after =<< parserMakerPlan before i
parserMakerPlan Split (Plan valName typ) = do
  resType <- tellMkTypeProduct typ typ
  resValName <- lift $ mkName "val"
  tell [ formatCType resType resValName ++ " = {" ++ valName ++ ", " ++ valName ++ "};" ]
  pure Plan
    { planValName = resValName
    , planType = resType
    }
parserMakerPlan (Vertical a b) i = do
  Plan aValName aType <- parserMakerPlan a $ planFst i
  Plan bValName bType <- parserMakerPlan b $ planSnd i
  resType <- tellMkTypeProduct aType bType
  resValName <- lift $ mkName "val"
  tell [ formatCType resType resValName ++ " = {" ++ aValName ++ ", " ++ bValName ++ "};" ]
  pure Plan
    { planValName = resValName
    , planType = resType
    }
parserMakerPlan Bytes (Plan valName _) = do
  resType <- tellMkTypeProduct (atomicCType "size_t") (atomicCType "char *")
  resName <- lift $ mkName "val"
  tell $
    [ "if (bytesLeft < " ++ valName ++ ") return -1;"
    , formatCType resType resName ++ " = { " ++ valName ++ ", inputStream };"
    ] ++ forwardInputStream valName
  pure Plan
    { planValName = resName
    , planType = resType
    }
parserMakerPlan (Doc s parser) i =
  tell ["/* {{{ " ++ s ++ " */"] *>
  censor (map ("  "++)) (parserMakerPlan parser i) <*
  tell ["/* " ++ s ++ " }}} */"]
parserMakerPlan (PureIntSize intSize) (Plan _ _) = do
  resName <- lift $ mkName "val"
  tell [ "uint8_t " ++ resName ++ " = " ++ show (intSizeToInt intSize) ++ ";" ]
  pure Plan
    { planValName = resName
    , planType = atomicCType "uint8_t"
    }
parserMakerPlan Unsigned (Plan valName _) = do
  resName <- lift $ mkName "val"
  tell $
    [ "if (bytesLeft < " ++ valName ++ ") return -1;"
    , "uint64_t " ++ resName ++ ";"
    , "switch(" ++ valName ++ ") {"
    , "  case 1:  " ++ resName ++ " = *(uint8_t)inputStream; break;"
    , "  case 2:  " ++ resName ++ " = *(uint16_t)inputStream; break;"
    , "  case 4:  " ++ resName ++ " = *(uint32_t)inputStream; break;"
    , "  case 8:  " ++ resName ++ " = *(uint64_t)inputStream; break;"
    , "  default: abort();"
    , "}"
    ] ++ forwardInputStream valName
  pure Plan
    { planValName = resName
    , planType = atomicCType "uint64_t"
    }
parserMakerPlan (IgnoreInput parser) _ =
  parserMakerPlan parser voidPlan

voidPlan :: Plan
voidPlan = Plan "should-never-appear-in-code" Void

parserCode :: Parser a -> (Plan, String)
parserCode parser = second unlines . runNameGen . runWriterT $ parserMakerPlan parser voidPlan

formatCType :: CType -> String -> String
formatCType (CDoc d x) name = (++ (" /* " ++ d ++ " */")) $ formatCType x name
formatCType Void name = "void " ++ name
formatCType (Primitive mkDecl) name = mkDecl name
formatCType (TypeProduct productName _ _) name = "struct " ++ productName ++ " " ++ name

declsCType :: CType -> [String]
declsCType (CDoc d x) = ("/* " ++ d ++ " */") : declsCType x
declsCType Void = []
declsCType (Primitive _) = []
declsCType (TypeProduct productName a b) =
  [ "struct " ++ productName ++ " {"
  , "  " ++ formatCType a "fst" ++ ";"
  , "  " ++ formatCType b "snd" ++ ";"
  , "};"
  ]
