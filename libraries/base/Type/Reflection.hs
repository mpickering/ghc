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
    , pattern I.TRApp, pattern I.TRCon, pattern I.TRFun
    , I.decomposeFun
    , I.typeRepFingerprint
    , I.typeRepTyCon
    , I.typeRepKind
    , I.splitApp
    , I.rnfTypeRep
    , I.eqTypeRep

      -- ** Quantified
    , I.TypeRepX(..)
    , I.typeRepXTyCon
    , I.rnfTypeRepX

      -- * Type constructors
    , I.TyCon           -- abstract, instance of: Eq, Show, Typeable
                        -- For now don't export Module, to avoid name clashes
    , I.tyConPackage
    , I.tyConModule
    , I.tyConName
    , I.rnfTyCon
    , I.debugShow
    ) where

import qualified Data.Typeable.Internal as I
import Data.Type.Equality
