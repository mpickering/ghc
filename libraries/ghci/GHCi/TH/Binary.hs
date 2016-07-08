{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

-- This module is full of orphans, unfortunately
module GHCi.TH.Binary () where

import Data.Binary
import qualified Data.ByteString as B
#if MIN_VERSION_base(4,10,0)
import Type.Reflection
import Type.Reflection.Unsafe
import Data.Kind (Type)
import GHC.Exts (RuntimeRep)
#else
import Data.Typeable
#endif
import GHC.Serialized
import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH

-- Put these in a separate module because they take ages to compile

instance Binary TH.Loc
instance Binary TH.Name
instance Binary TH.ModName
instance Binary TH.NameFlavour
instance Binary TH.PkgName
instance Binary TH.NameSpace
instance Binary TH.Module
instance Binary TH.Info
instance Binary TH.Type
instance Binary TH.TyLit
instance Binary TH.TyVarBndr
instance Binary TH.Role
instance Binary TH.Lit
instance Binary TH.Range
instance Binary TH.Stmt
instance Binary TH.Pat
instance Binary TH.Exp
instance Binary TH.Dec
instance Binary TH.Overlap
instance Binary TH.DerivClause
instance Binary TH.DerivStrategy
instance Binary TH.Guard
instance Binary TH.Body
instance Binary TH.Match
instance Binary TH.Fixity
instance Binary TH.TySynEqn
instance Binary TH.FamFlavour
instance Binary TH.FunDep
instance Binary TH.AnnTarget
instance Binary TH.RuleBndr
instance Binary TH.Phases
instance Binary TH.RuleMatch
instance Binary TH.Inline
instance Binary TH.Pragma
instance Binary TH.Safety
instance Binary TH.Callconv
instance Binary TH.Foreign
instance Binary TH.Bang
instance Binary TH.SourceUnpackedness
instance Binary TH.SourceStrictness
instance Binary TH.DecidedStrictness
instance Binary TH.FixityDirection
instance Binary TH.OccName
instance Binary TH.Con
instance Binary TH.AnnLookup
instance Binary TH.ModuleInfo
instance Binary TH.Clause
instance Binary TH.InjectivityAnn
instance Binary TH.FamilyResultSig
instance Binary TH.TypeFamilyHead
instance Binary TH.PatSynDir
instance Binary TH.PatSynArgs

-- We need Binary TypeRep for serializing annotations

#if MIN_VERSION_base(4,10,0)
instance Binary TyCon where
    put tc = put (tyConPackage tc) >> put (tyConModule tc) >> put (tyConName tc)
    get = mkTyCon <$> get <*> get <*> get

putTypeRep :: TypeRep a -> Put
-- Special handling for Type, (->), and RuntimeRep due to recursive kind
-- relations.
-- See Note [Mutually recursive representations of primitive types]
putTypeRep rep
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep Type)
  = put (0 :: Word8)
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep RuntimeRep)
  = put (1 :: Word8)
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep (->))
  = put (2 :: Word8)
putTypeRep rep@(TRCon con) = do
    put (3 :: Word8)
    put con
    putTypeRep (typeRepKind rep)
putTypeRep (TRApp f x) = do
    put (4 :: Word8)
    putTypeRep f
    putTypeRep x
putTypeRep _ = fail "GHCi.TH.Binary.putTypeRep: Impossible"

getTypeRepX :: Get TypeRepX
getTypeRepX = do
    tag <- get :: Get Word8
    case tag of
        0 -> return $ TypeRepX (typeRep :: TypeRep Type)
        1 -> return $ TypeRepX (typeRep :: TypeRep RuntimeRep)
        2 -> return $ TypeRepX (typeRep :: TypeRep (->))
        3 -> do con <- get :: Get TyCon
                TypeRepX rep_k <- getTypeRepX
                case rep_k `eqTypeRep` (typeRep :: TypeRep Type) of
                    Just HRefl -> pure $ TypeRepX $ mkTrCon con rep_k
                    Nothing    -> failure "Kind mismatch"
                                          [ "Type constructor: " ++ show con
                                          , "Applied to type:  " ++ show rep_k
                                          ]

        4 -> do TypeRepX f <- getTypeRepX
                TypeRepX x <- getTypeRepX
                case typeRepKind f of
                    TRFun arg _ ->
                        case arg `eqTypeRep` typeRepKind x of
                            Just HRefl ->
                                pure $ TypeRepX $ mkTrApp f x
                            _ -> failure "Kind mismatch"
                                         [ "Found argument of kind:      " ++ show (typeRepKind x)
                                         , "Where the constructor:       " ++ show f
                                         , "Expects an argument of kind: " ++ show arg
                                         ]
                    _ -> failure "Applied non-arrow type"
                                 [ "Applied type: " ++ show f
                                 , "To argument:  " ++ show x
                                 ]
        _ -> failure "Invalid TypeRepX" []
  where
    failure description info =
        fail $ unlines $ [ "GHCi.TH.Binary.getTypeRepX: "++description ]
                      ++ map ("    "++) info

instance Typeable a => Binary (TypeRep (a :: k)) where
    put = putTypeRep
    get = do
        TypeRepX rep <- getTypeRepX
        case rep `eqTypeRep` expected of
            Just HRefl -> pure rep
            Nothing    -> fail $ unlines
                               [ "GHCi.TH.Binary: Type mismatch"
                               , "    Deserialized type: " ++ show rep
                               , "    Expected type:     " ++ show expected
                               ]
     where expected = typeRep :: TypeRep a

instance Binary TypeRepX where
    put (TypeRepX rep) = putTypeRep rep
    get = getTypeRepX
#else
instance Binary TyCon where
    put tc = put (tyConPackage tc) >> put (tyConModule tc) >> put (tyConName tc)
    get = mkTyCon3 <$> get <*> get <*> get

instance Binary TypeRep where
    put type_rep = put (splitTyConApp type_rep)
    get = do
        (ty_con, child_type_reps) <- get
        return (mkTyConApp ty_con child_type_reps)
#endif

instance Binary Serialized where
    put (Serialized tyrep wds) = put tyrep >> put (B.pack wds)
    get = Serialized <$> get <*> (B.unpack <$> get)
