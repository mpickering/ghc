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
    JSString s -> text $ show s -- Show the string for escaping. This is probably wrong
    JSArray as -> brackets $ pprWithCommas renderJSON as
    JSObject fs -> braces $ pprWithCommas renderField fs
  where
    renderField :: (String, JsonDoc) -> SDoc
    renderField (s, j) = text s <>  colon <+> renderJSON j

class ToJson a where
  json :: a -> JsonDoc
