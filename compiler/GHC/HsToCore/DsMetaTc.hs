{-# LANGUAGE CPP, TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-----------------------------------------------------------------------------
--
-- (c) The University of Glasgow 2006
--
-- The purpose of this module is to transform an HsExpr into a CoreExpr which
-- when evaluated, returns a (Meta.Q Meta.Exp) computation analogous to the
-- input HsExpr. We do this in the DsM monad, which supplies access to
-- CoreExpr's of the "smart constructors" of the Meta.Exp datatype.
--
-- It also defines a bunch of knownKeyNames, in the same way as is done
-- in prelude/PrelNames.  It's much more convenient to do it here, because
-- otherwise we have to recompile PrelNames whenever we add a Name, which is
-- a Royal Pain (triggers other recompilation).
-----------------------------------------------------------------------------

module GHC.HsToCore.DsMetaTc( dsBracketTc, dsType, repEFP, repVar ) where

#include "HsVersions.h"

import GhcPrelude

import {-# SOURCE #-}  GHC.HsToCore.Expr ( dsExpr )

import GHC.HsToCore.Monad

import GHC.Hs

import GHC.Core.Class
import Id
--import Name hiding( isVarOcc, isTcOcc, varName, tcName )
import THNames
import TcType
import GHC.Core.TyCon
import TysWiredIn
import GHC.Core
import GHC.Core.Make
import GHC.Core.Utils
import GHC.Core.Type
import SrcLoc
import Unique
import Outputable
import GHC.Driver.Session
import MonadUtils
import GHC.HsToCore.Quote (Core(..))

import GHC.CoreToIface
import GHC.Iface.Binary
import Binary
import System.IO
import VarSet
import GHC.Core.FVs

initBinMemSize :: Int
initBinMemSize = 1024*1024

dsType :: Type -> DsM CoreExpr
dsType t = do
  MkC r <- repType t
  return r


-----------------------------------------------------------------------------
dsBracketTc :: HsBracket GhcTc -> [PendingTcTypedSplice]
                               -> [PendingZonkSplice]
                               -> [PendingZonkSplice]
                               -> DsM CoreExpr
-- Returns a CoreExpr of type String which can be deserialised to get an
-- IfaceExpr.

dsBracketTc brack splices ev_zs zs
  = do
      b <- do_brack brack
      sps <- mapMaybeM do_one splices
      zss <- mapM do_one_z zs
      ev_zss <- mapMaybeM do_one_ev ev_zs

      -- thname <- lookupType nameTyConName
--      ty <- return stringTy --lookupType tExpUTyConName
      (_,ty) <- splitFunTy . snd . splitForAllTy . snd . splitForAllTy . idType <$> dsLookupGlobalId unTypeQName
      let tu_ty = mkBoxedTupleTy [intTy, ty]
      ty' <- funResultTy . funResultTy . idType <$> dsLookupGlobalId mkTTExpName
      let tt_ty = mkBoxedTupleTy [intTy, ty']

      pprTrace "dsBracket" (ppr splices $$ ppr sps $$ ppr zss)
        $ return $ mkCoreTup [mkListExpr tt_ty zss, mkListExpr tu_ty (sps ++ ev_zss), b]
  where
    do_one_z (PendingZonkSplice n e) = do
      let k = getKey (idUnique n)
      dflags <- getDynFlags
      let k_expr = mkIntExprInt dflags k
      Just liftTClass <- tyConClass_maybe <$> dsLookupTyCon liftTClassName
      let [lift_id] = classMethods liftTClass
      --untype <- dsLookupGlobalId unTypeQName
      --e' <- dsExpr (unLoc e)
      -- The type of the expression has to be Q (TExp r)
      pprTraceM "do_one_z" (ppr (exprType e))
      {-
      case splitTyConApp (exprType e) of
          (ty, [r]) -> let (ty', [r']) = splitTyConApp r
                       in return $ Just $ mkCoreTup [k_expr, mkCoreApps (Var untype) [Type r', e']]
          _ -> return Nothing
      -}
      let (_, [k, a]) = splitTyConApp (exprType e)
      pprTraceM "do_one_z" (ppr a $$  ppr k)
      return $ mkCoreTup [k_expr, mkCoreApps (Var lift_id) [Type k, Type a, e]]
    do_one_ev (PendingZonkSplice n e) = do
      let k = getKey (idUnique n)
      dflags <- getDynFlags
      let k_expr = mkIntExprInt dflags k
      e' <- return e
      -- The type of the expression has to be Q (TExp r)
      pprTraceM "ty" (ppr $ exprType e')
      pprTraceM "e" (ppr $ e')
      ccev <- dsLookupGlobalId codeCevidenceName
      case splitTyConApp (exprType e') of
          (ty, [r]) ->
            return $ Just $ mkCoreTup [k_expr, mkCoreApps (Var ccev) [Type r, e']]
          _ -> pprPanic "split failed" (ppr e')
    do_one (PendingTcSplice n e) = do
      let k = getKey (idUnique n)
      dflags <- getDynFlags
      let k_expr = mkIntExprInt dflags k
      untype <- dsLookupGlobalId unTypeQName
      e' <- dsExpr (unLoc e)
      -- The type of the expression has to be Q (TExp r)
      pprTraceM "ty" (ppr $ exprType e')
      pprTraceM "e" (ppr $ e')
      case splitTyConApp (exprType e') of
          (ty, [r]) | ty `hasKey` qTyConKey ->
            let (_ty', [rep, r']) = splitTyConApp r
            in return $ Just $ mkCoreTup [k_expr, mkCoreApps (Var untype) [Type rep, Type r', e']]
          _ -> return Nothing

    do_brack (TExpBr _ e)  = do { MkC s <- repLE' e; return s }
    do_brack _ = panic "dsBracket: unexpected XBracket"

{- -------------- Examples --------------------

  [| \x -> x |]
====>
  gensym (unpackString "x"#) `bindQ` \ x1::String ->
  lam (pvar x1) (var x1)


  [| \x -> $(f [| x |]) |]
====>
  gensym (unpackString "x"#) `bindQ` \ x1::String ->
  lam (pvar x1) (f (var x1))
-}


-----------------------------------------------------------------------------
--              Expressions
-----------------------------------------------------------------------------

repLE' :: LHsExpr GhcTc -> DsM (Core String)
repLE' (L loc e) = putSrcSpanDs loc (repECore e)

coreStringLit :: String -> DsM (Core String)
coreStringLit s = do { z <- mkStringExpr s; return(MkC z) }

repType :: Type -> DsM (Core String)
repType ty = do
  let it = toIfaceType ty
  pprTraceM "Writing type" (ppr ty)
  liftIO (writeBracket it) >>= coreStringLit

repECore :: HsExpr GhcTc -> DsM (Core String)
repECore e = do
  {-c_e <- mkCoreLams vs <$> dsExpr e
  dflags <- getDynFlags
  env <- env_top <$> getEnv
  c_e' <- liftIO $ corePrepExpr dflags env c_e
  let c_e'' = tidyExpr emptyTidyEnv c_e'
  pprTraceM "desugaring" (ppr ())
  pprTraceM "desugared" (ppr ())
  -}
  repEFP e >>= coreStringLit

repVar :: Id -> DsM CoreExpr
repVar ev_id =  do
  texpco <- dsLookupGlobalId unsafeTExpCoerceName
  let ie = toIfaceExpr (unitVarSet ev_id) (Var ev_id)
  fp <- liftIO (writeBracket ie)
  MkC s <- coreStringLit fp
  (_,ty) <- splitFunTy . snd . splitForAllTy . snd . splitForAllTy . idType <$> dsLookupGlobalId unTypeQName
  let tu_ty = mkBoxedTupleTy [intTy, ty]
  ty' <- funResultTy . funResultTy . idType <$> dsLookupGlobalId mkTTExpName
  let tt_ty = mkBoxedTupleTy [intTy, ty']
  untype <- dsLookupGlobalId unTypeQName
  return $ mkCoreApps (Var untype) [Type liftedRepTy, Type unitTy, mkCoreApps (Var texpco) [Type liftedRepTy, Type unitTy, (mkCoreTup [mkNilExpr tt_ty, mkNilExpr tu_ty, s])]]

repEFP :: HsExpr GhcTc -> DsM FilePath
repEFP e = do
  c_e <- dsExpr e
  let ie = toIfaceExpr (exprFreeVars c_e) c_e
  pprTraceM "toIfaceExpr" (ppr ie)
  liftIO (writeBracket ie)


writeBracket :: (Binary b, Outputable b) => b -> IO FilePath
writeBracket e = do
  bh <- openBinMem initBinMemSize
  putWithUserData (\_ -> return ()) bh e
  (fp, h) <- openBinaryTempFile "/tmp" "bracket"
  pprTraceM "Writing" (ppr (fp, e))
  hClose h
  writeBinMem bh fp
  return fp

{-
lookupType :: Name      -- Name of type constructor (e.g. TH.ExpQ)
           -> DsM Type  -- The type
lookupType tc_name = do { tc <- dsLookupTyCon tc_name ;
                          return (mkTyConApp tc []) }
                          -}

