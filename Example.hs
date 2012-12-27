{-# LANGUAGE OverloadedStrings #-}
import Control.Category
import Data.Binary.Get
import Data.ByteString.Lazy.Char8 () -- For the IsString instance
import Data.Monoid ((<>))
import HaskCons
import Prelude hiding (id, (.))
import qualified Data.ByteString.Lazy as LBS

typeP :: Parser Integer
typeP = doc "type" $ unsigned Word16

lenValP :: Parser LBS.ByteString
lenValP = unsigned Word8 >>> bytes

tlvP :: Parser (Integer, LBS.ByteString)
tlvP = typeP `pair` lenValP

main :: IO ()
main = do
  putStrLn ""
  print . runGet (parse tlvP ()) $ LBS.pack [1, 0, 6] <> "Hello!"
  putStrLn ""
  putStrLn . unlines $ declsCType (parserOutputCType tlvP)
  putStrLn $ formatCType (parserOutputCType tlvP) "tlv_t" ++ ";"
