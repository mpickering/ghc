{-# LANGUAGE GADTs #-}
module Json where

import Outputable

-- | Simply data type to represent JSON documents.
data JsonDoc where
  JSNull :: JsonDoc
  JSBool :: Bool -> JsonDoc
  JSInt  :: Int  -> JsonDoc
  JSString :: String -> JsonDoc
  JSArray :: [JsonDoc] -> JsonDoc
  JSObject :: [(String, JsonDoc)] -> JsonDoc


-- This is simple and slow as it is only used for error reporting
renderJSON :: JsonDoc -> SDoc
renderJSON d =
  case d of
    JSNull -> text "null"
    JSBool b -> text $ if b then "true" else "false"
    JSInt    n -> ppr n
    JSString s -> doubleQuotes $ text $ escapeJsonString s
    JSArray as -> brackets $ pprWithCommas renderJSON as
    JSObject fs -> braces $ pprWithCommas renderField fs
  where
    renderField :: (String, JsonDoc) -> SDoc
    renderField (s, j) = doubleQuotes (text s) <>  colon <+> renderJSON j

escapeJsonString :: String -> String
escapeJsonString = concatMap escapeChar
  where
    escapeChar '\b' = "\\b"
    escapeChar '\f' = "\\f"
    escapeChar '\n' = "\\n"
    escapeChar '\r' = "\\r"
    escapeChar '\t' = "\\t"
    escapeChar '"'  = "\""
    escapeChar '\\'  = "\\\\"
    escapeChar c    = [c]

class ToJson a where
  json :: a -> JsonDoc
