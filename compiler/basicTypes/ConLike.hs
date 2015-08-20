{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1998

\section[ConLike]{@ConLike@: Constructor-like things}
-}

{-# LANGUAGE CPP, DeriveDataTypeable #-}

module ConLike (
          ConLike(..)
        , conLikeArity
        , conLikeFieldLabels
        , conLikeInstOrigArgTys
        , conLikeExTyVars
        , conLikeName
        , conLikeStupidTheta
        , conLikeWrapId
        , conLikeImplBangs
        , conLikeFullSig
        , conLikeResTy
    ) where

#include "HsVersions.h"

import DataCon
import PatSyn
import Outputable
import Unique
import Util
import Name
import TyCon
import BasicTypes
import {-# SOURCE #-} TypeRep (Type, ThetaType)
import Var
import Type (mkTyConApp)

import Data.Function (on)
import qualified Data.Data as Data
import qualified Data.Typeable

{-
************************************************************************
*                                                                      *
\subsection{Constructor-like things}
*                                                                      *
************************************************************************
-}

-- | A constructor-like thing
data ConLike = RealDataCon DataCon
             | PatSynCon PatSyn
  deriving Data.Typeable.Typeable

{-
************************************************************************
*                                                                      *
\subsection{Instances}
*                                                                      *
************************************************************************
-}

instance Eq ConLike where
    (==) = (==) `on` getUnique
    (/=) = (/=) `on` getUnique

instance Ord ConLike where
    (<=) = (<=) `on` getUnique
    (<) = (<) `on` getUnique
    (>=) = (>=) `on` getUnique
    (>) = (>) `on` getUnique
    compare = compare `on` getUnique

instance Uniquable ConLike where
    getUnique (RealDataCon dc) = getUnique dc
    getUnique (PatSynCon ps)   = getUnique ps

instance NamedThing ConLike where
    getName (RealDataCon dc) = getName dc
    getName (PatSynCon ps)   = getName ps

instance Outputable ConLike where
    ppr (RealDataCon dc) = ppr dc
    ppr (PatSynCon ps) = ppr ps

instance OutputableBndr ConLike where
    pprInfixOcc (RealDataCon dc) = pprInfixOcc dc
    pprInfixOcc (PatSynCon ps) = pprInfixOcc ps
    pprPrefixOcc (RealDataCon dc) = pprPrefixOcc dc
    pprPrefixOcc (PatSynCon ps) = pprPrefixOcc ps

instance Data.Data ConLike where
    -- don't traverse?
    toConstr _   = abstractConstr "ConLike"
    gunfold _ _  = error "gunfold"
    dataTypeOf _ = mkNoRepType "ConLike"


conLikeArity :: ConLike -> Arity
conLikeArity (RealDataCon data_con) = dataConSourceArity data_con
conLikeArity (PatSynCon pat_syn)    = patSynArity pat_syn

conLikeFieldLabels :: ConLike -> [FieldLabel]
conLikeFieldLabels (RealDataCon data_con) = dataConFieldLabels data_con
conLikeFieldLabels (PatSynCon pat_syn)    = patSynFieldLabels pat_syn

conLikeInstOrigArgTys :: ConLike -> [Type] -> [Type]
conLikeInstOrigArgTys (RealDataCon data_con) tys =
    dataConInstOrigArgTys data_con tys
conLikeInstOrigArgTys (PatSynCon pat_syn) tys =
    patSynInstArgTys pat_syn tys

conLikeExTyVars :: ConLike -> [TyVar]
conLikeExTyVars (RealDataCon dcon1) = dataConExTyVars dcon1
conLikeExTyVars (PatSynCon psyn1)   = patSynExTyVars psyn1

conLikeName :: ConLike -> Name
conLikeName (RealDataCon data_con) = dataConName data_con
conLikeName (PatSynCon pat_syn)    = patSynName pat_syn

conLikeStupidTheta :: ConLike -> ThetaType
conLikeStupidTheta (RealDataCon data_con) = dataConStupidTheta data_con
conLikeStupidTheta (PatSynCon {})         = []

conLikeWrapId :: ConLike -> Maybe Id
conLikeWrapId (RealDataCon data_con) = Just $ dataConWrapId data_con
conLikeWrapId (PatSynCon pat_syn)    = fst <$> patSynBuilder pat_syn

conLikeImplBangs :: ConLike -> [HsImplBang]
conLikeImplBangs (RealDataCon data_con) = dataConImplBangs data_con
conLikeImplBangs (PatSynCon pat_syn)         =
    replicate (length (patSynFieldLabels pat_syn)) HsLazy


conLikeResTy :: ConLike -> [Type] -> Type
conLikeResTy (RealDataCon con) tys = mkTyConApp (dataConTyCon con) tys
conLikeResTy (PatSynCon ps)    tys = patSynInstResTy ps tys

conLikeFullSig :: ConLike
               -> ([TyVar], [TyVar], [(TyVar,Type)], ThetaType, ThetaType, [Type], Type)
conLikeFullSig (RealDataCon con) =
  let (univ_tvs, ex_tvs, eq_spec, theta, arg_tys, res_ty) = dataConFullSig con
  -- Prov and req thetas are equal
  in (univ_tvs, ex_tvs, eq_spec, theta, theta, arg_tys, res_ty)
conLikeFullSig (PatSynCon pat_syn) =
 let (univ_tvs, ex_tvs, prov, req, arg_tys, res_ty) = patSynSig pat_syn
 -- eqSpec is empty
 in (univ_tvs, ex_tvs, [], prov, req, arg_tys, res_ty)
