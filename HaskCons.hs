{-# LANGUAGE GADTs, KindSignatures #-}
module HaskCons
  ( IntSize(..), ParserMaker, Parser
  , doc, bytes, unsigned, ignoreInput, (***), (&&&)
  , pair
  , parse
  , parserOutputCType, CType(..)
  , formatCType, declsCType
  -- , parserCode
  , id, (.)
  ) where

import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.Trans.State
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

-- intSizeCType :: IntSize -> String
-- intSizeCType Word8 = "uint8_t"
-- intSizeCType Word16 = "uint16_t"
-- intSizeCType Word32 = "uint32_t"
-- intSizeCType Word64 = "uint64_t"

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
  name <- mkName
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
parserMakerOutputCType Bytes _ = pure $ atomicCType "char *"
parserMakerOutputCType (PureIntSize _) _ = pure $ atomicCType "uint8_t"
parserMakerOutputCType Unsigned _ = pure $ atomicCType "uint64_t" -- dynamic int size
parserMakerOutputCType (Doc d parser) i = CDoc d <$> parserMakerOutputCType parser i
parserMakerOutputCType (IgnoreInput parser) _ = parserMakerOutputCType parser Void

parserOutputCType :: Parser a -> CType
parserOutputCType = runNameGen . (`parserMakerOutputCType` Void)

type NameGen = State Int

runNameGen :: NameGen a -> a
runNameGen = (`evalState` 0)

mkName :: NameGen String
mkName = modify (+1) >> ("var" ++) . show <$> get

-- data Plan a = Plan
--   { planCode :: [String]
--   , planValName :: String
--   , planValType :: CType
--   }

-- parserMakerPlan :: ParserMaker a b -> Plan a -> NameGen (Plan b)
-- parserMakerPlan Id i = pure i
-- parserMakerPlan (Dot after before) i = parserMakerPlan after =<< parserMakerPlan before i
-- parserMakerPlan Split (Plan code valName valType) = do
--   resTypeName <- ("struct split_"++) <$> mkName
--   resValName <- mkName
--   let
--     myCode =
--       [ resTypeName ++ " {"
--       , "  " ++ formatCType valType "fst"
--       , "  " ++ formatCType valType "snd"
--       , "} " ++ resValName ++ " = {" ++ valName ++ ", " ++ valName ++ "};"
--       ]
--   pure Plan
--     { planCode = code ++ myCode
--     , planValName = resValName
--     , planValType = resTypeName
--     }
-- -- parserMakerPlan (Vertical a b) i = do
-- --   parserMakerPlan a $ planFst i
-- --   parserMakerPlan b
-- --   pure Plan
-- --     { planCode
-- -- parserMakerPlan   Bytes :: ParserMaker Int64 LBS.ByteString
-- -- parserMakerPlan   Doc :: String -> ParserMaker a b -> ParserMaker a b
-- -- parserMakerPlan   PureIntSize :: IntSize -> Parser IntSize
-- -- parserMakerPlan   Unsigned :: Integral a => ParserMaker IntSize a
-- -- parserMakerPlan   IgnoreInput :: Parser b -> ParserMaker a b

-- voidPlan :: Plan ()
-- voidPlan = Plan [] "should-never-appear-in-code" "should-never-appear-in-code"

-- parserCode :: Parser a -> String
-- parserCode parser = unlines . planCode . runNameGen $ parserMakerPlan parser voidPlan

formatCType :: CType -> String -> String
formatCType (CDoc d x) name = (++ (" /* " ++ d ++ " */")) $ formatCType x name
formatCType Void name = "void " ++ name
formatCType (Primitive mkDecl) name = (++ ";") $ mkDecl name
formatCType (TypeProduct productName _ _) name = "struct " ++ productName ++ " " ++ name

declsCType :: CType -> [String]
declsCType (CDoc d x) = ("/* " ++ d ++ " */") : declsCType x
declsCType Void = []
declsCType (Primitive _) = []
declsCType (TypeProduct productName a b) =
  [ "struct " ++ productName ++ " {"
  , "  " ++ formatCType a "fst"
  , "  " ++ formatCType b "snd"
  , "};"
  ]
