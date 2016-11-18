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
import GHC.Exts (TYPE, RuntimeRep)
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
-- Special handling for TYPE, (->), and RuntimeRep due to recursive kind
-- relations.
-- See Note [Mutually recursive representations of primitive types]
putTypeRep rep
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep Type)
  = put (5 :: Word8)
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep TYPE)
  = put (0 :: Word8)
  | Just HRefl <- rep `eqTypeRep` (typeRep :: TypeRep RuntimeRep)
  = put (1 :: Word8)
putTypeRep (TRFun arg res) = do
    put (2 :: Word8)
    put arg
    put res
putTypeRep rep@(TRCon' con ks) = do
    put (3 :: Word8)
    put con
    put ks
putTypeRep (TRApp f x) = do
    put (4 :: Word8)
    putTypeRep f
    putTypeRep x
putTypeRep _ = fail "GHCi.TH.Binary.putTypeRep: Impossible"

getSomeTypeRep :: Get SomeTypeRep
getSomeTypeRep = do
    tag <- get :: Get Word8
    case tag of
        5 -> return $ SomeTypeRep (typeRep :: TypeRep Type)
        0 -> return $ SomeTypeRep (typeRep :: TypeRep TYPE)
        1 -> return $ SomeTypeRep (typeRep :: TypeRep RuntimeRep)
        2 -> return undefined -- TODO
        3 -> do con <- get :: Get TyCon
                SomeTypeRep rep_k <- getSomeTypeRep
                ks <- get :: Get [SomeTypeRep]
                return $ mkTrCon con ks

        4 -> do SomeTypeRep f <- getSomeTypeRep
                SomeTypeRep x <- getSomeTypeRep
                case typeRepKind f of
                    TRFun arg _ ->
                        case arg `eqTypeRep` typeRepKind x of
                            Just HRefl ->
                                pure $ SomeTypeRep $ mkTrApp f x
                            _ -> failure "Kind mismatch"
                                         [ "Found argument of kind:      " ++ show (typeRepKind x)
                                         , "Where the constructor:       " ++ show f
                                         , "Expects an argument of kind: " ++ show arg
                                         ]
                    _ -> failure "Applied non-arrow type"
                                 [ "Applied type: " ++ show f
                                 , "To argument:  " ++ show x
                                 ]
        _ -> failure "Invalid SomeTypeRep" []
  where
    failure description info =
        fail $ unlines $ [ "GHCi.TH.Binary.getSomeTypeRep: "++description ]
                      ++ map ("    "++) info

instance Typeable a => Binary (TypeRep (a :: k)) where
    put = putTypeRep
    get = do
        SomeTypeRep rep <- getSomeTypeRep
        case rep `eqTypeRep` expected of
            Just HRefl -> pure rep
            Nothing    -> fail $ unlines
                               [ "GHCi.TH.Binary: Type mismatch"
                               , "    Deserialized type: " ++ show rep
                               , "    Expected type:     " ++ show expected
                               ]
     where expected = typeRep :: TypeRep a

instance Binary SomeTypeRep where
    put (SomeTypeRep rep) = putTypeRep rep
    get = getSomeTypeRep
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
