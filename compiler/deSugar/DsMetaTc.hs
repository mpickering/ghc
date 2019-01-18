{-# LANGUAGE CPP, TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

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

module DsMetaTc( dsBracketTc ) where

#include "HsVersions.h"

import GhcPrelude

import {-# SOURCE #-}   DsExpr ( dsExpr )

import MatchLit
import DsMonad

import qualified Language.Haskell.TH as TH

import HsSyn
import PrelNames
-- To avoid clashes with DsMeta.varName we must make a local alias for
-- OccName.varName we do this by removing varName from the import of
-- OccName above, making a qualified instance of OccName and using
-- OccNameAlias.varName where varName ws previously used in this file.
import qualified OccName( isDataOcc, isVarOcc, isTcOcc )

import Module
import Id
import Name hiding( isVarOcc, isTcOcc, varName, tcName )
import THNames
import NameEnv
import NameSet
import TcType
import TyCon
import TysWiredIn
import CoreSyn
import MkCore
import CoreUtils
import SrcLoc
import Unique
import BasicTypes
import Outputable
import Bag
import DynFlags
import FastString
import ForeignCall
import Util
import Maybes
import MonadUtils

import Data.ByteString ( unpack )
import Control.Monad
import Data.List
import ToIface
import BinIface
import Binary

initBinMemSize = 1024*1024

-----------------------------------------------------------------------------
dsBracketTc :: HsBracket GhcTc -> [PendingTcSplice] -> DsM CoreExpr
-- Returns a CoreExpr of type String which can be deserialised to get an
-- IfaceExpr.

dsBracketTc brack splices
  = dsExtendMetaEnv new_bit (do_brack brack)
  where
    new_bit = mkNameEnv [(n, DsSplice (unLoc e))
                        | PendingTcSplice n e <- splices]

    do_brack (TExpBr _ e)  = do { MkC e1  <- repLE' e     ; return e1 }
    do_brack (XBracket {}) = panic "dsBracket: unexpected XBracket"

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


-- See Note [How brackets and nested splices are handled] in TcSplice
-- We return a CoreExpr of any old type; the context should know
repSplice (HsTypedSplice   _ _ n _) = rep_splice n
repSplice (HsUntypedSplice _ _ n _) = rep_splice n
repSplice (HsQuasiQuote _ n _ _ _)  = rep_splice n
repSplice e@(HsSpliced {})          = pprPanic "repSplice" (ppr e)
repSplice e@(HsSplicedT {})         = pprPanic "repSpliceT" (ppr e)
repSplice e@(XSplice {})            = pprPanic "repSplice" (ppr e)

rep_splice :: Name -> DsM (Core a)
rep_splice splice_name
 = do { mb_val <- dsLookupMetaEnv splice_name
       ; case mb_val of
           Just (DsSplice e) -> do { e' <- dsExpr e
                                   ; return (MkC e') }
           _ -> pprPanic "HsSplice" (ppr splice_name) }
                        -- Should not happen; statically checked

-----------------------------------------------------------------------------
--              Expressions
-----------------------------------------------------------------------------

repLEs es = undefined
repLE = undefined

-- FIXME: some of these panics should be converted into proper error messages
--        unless we can make sure that constructs, which are plainly not
--        supported in TH already lead to error messages at an earlier stage
repLE' :: LHsExpr GhcTc -> DsM (Core String)
repLE' (dL->L loc e) = putSrcSpanDs loc (repECore e)

data Core a = MkC CoreExpr

coreStringLit :: String -> DsM (Core String)
coreStringLit s = do { z <- mkStringExpr s; return(MkC z) }

repECore :: HsExpr GhcTc -> DsM (Core String)
repECore e = do
  c_e <- dsExpr e
  let ie = toIfaceExpr c_e
  liftIO $ writeBracket ie
  coreStringLit "/tmp/splice.bin"


writeBracket e = do
  bh <- openBinMem initBinMemSize
  putWithUserData (\_ -> return ()) bh e
  writeBinMem bh "/tmp/splice.bin"

