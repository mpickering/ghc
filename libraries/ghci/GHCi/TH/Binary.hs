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
#if MIN_VERSION_base(4,9,0)
import Type.Reflection
import Type.Reflection.Unsafe
import Data.Kind (Type)
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

#if MIN_VERSION_base(4,9,0)
instance Binary TyCon where
    put tc = put (tyConPackage tc) >> put (tyConModule tc) >> put (tyConName tc)
    get = mkTyCon <$> get <*> get <*> get

putTypeRep :: TypeRep a -> Put
putTypeRep rep@(TRCon con) = do
    put (0 :: Word8)
    put con
    putTypeRep (typeRepKind rep)
putTypeRep (TRApp f x) = do
    put (1 :: Word8)
    putTypeRep f
    putTypeRep x
putTypeRep _ = fail "putTypeRep: Impossible"

getTypeRepX :: Get TypeRepX
getTypeRepX = do
    tag <- get :: Get Word8
    case tag of
        0 -> do con <- get :: Get TyCon
                TypeRepX rep_k <- getTypeRepX
                case rep_k `eqTypeRep` (typeRep :: TypeRep Type) of
                    Just HRefl -> pure $ TypeRepX $ mkTrCon con rep_k
                    Nothing    -> fail "getTypeRepX: Kind mismatch"

        1 -> do TypeRepX f <- getTypeRepX
                TypeRepX x <- getTypeRepX
                case typeRepKind f of
                    TRFun arg _ ->
                        case arg `eqTypeRep` typeRepKind x of
                            Just HRefl ->
                                pure $ TypeRepX $ mkTrApp f x
                            _ -> fail "getTypeRepX: Kind mismatch"
                    _ -> fail "getTypeRepX: Applied non-arrow type"
        _ -> fail "getTypeRepX: Invalid TypeRepX"

instance Typeable a => Binary (TypeRep (a :: k)) where
    put = putTypeRep
    get = do
        TypeRepX rep <- getTypeRepX
        case rep `eqTypeRep` (typeRep :: TypeRep a) of
            Just HRefl -> pure rep
            Nothing    -> fail "Binary: Type mismatch"

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
