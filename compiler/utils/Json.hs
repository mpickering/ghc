{-# LANGUAGE GADTs #-}
module Json where

import Data.List

-- | Simply data type to represent JSON documents.
data JsonDoc where
  JSNull :: JsonDoc
  JSBool :: Bool -> JsonDoc
  JSInt  :: Int  -> JsonDoc
  JSString :: String -> JsonDoc
  JSArray :: [JsonDoc] -> JsonDoc
  JSObject :: [(String, JsonDoc)] -> JsonDoc


-- This is simple and slow as it is only used for error reporting
renderJSON :: JsonDoc -> String
renderJSON d =
  case d of
    JSNull -> "null"
    JSBool b -> if b then "true" else "false"
    JSInt    n -> show n
    JSString s -> show s
    JSArray as -> "[" ++ unwords (map renderJSON as) ++ "]"
    JSObject fs -> "{" ++ intercalate ", " (map renderField fs) ++ "}"
  where
    renderField :: (String, JsonDoc) -> String
    renderField (s, j) = s ++ ": " ++ renderJSON j

class ToJson a where
  json :: a -> JsonDoc
