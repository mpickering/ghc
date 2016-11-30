{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}

module Type.Reflection
    ( -- * The Typeable class
      I.Typeable
    , I.typeRep
    , I.withTypeable

      -- * Propositional equality
    , (:~:)(Refl)
    , (:~~:)(HRefl)

      -- * Type representations
      -- ** Type-Indexed
    , I.TypeRep
    , I.typeOf
    , pattern I.TRApp, pattern I.TRCon, pattern I.TRCon', pattern I.TRFun
    , I.typeRepFingerprint
    , I.typeRepTyCon
    , I.splitApp
    , I.rnfTypeRep
    , I.eqTypeRep
    , I.typeRepKind

      -- ** Quantified
    , I.SomeTypeRep(..)
    , I.typeRepXTyCon
    , I.rnfSomeTypeRep

      -- * Type constructors
    , I.TyCon           -- abstract, instance of: Eq, Show, Typeable
                        -- For now don't export Module, to avoid name clashes
    , I.tyConPackage
    , I.tyConModule
    , I.tyConName
    , I.rnfTyCon
    ) where

import qualified Data.Typeable.Internal as I
import Data.Type.Equality
