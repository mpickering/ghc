{-# LANGUAGE CPP #-}

-- ----------------------------------------------------------------------------
-- | Pretty print helpers for the LLVM Code generator.
--
module LlvmCodeGen.Ppr (
        pprLlvmCmmDecl, pprLlvmData, infoSection
    ) where

#include "HsVersions.h"

import GhcPrelude

import Llvm
import LlvmCodeGen.Base
import LlvmCodeGen.Data

import CLabel
import Cmm

import FastString
import Outputable
import Unique

import SrcLoc
import CoreSyn ( Tickish(SourceNote) )
import Debug
import Hoopl.Label ( LabelMap )
import Hoopl.Collections ( IsMap(..) )


import Data.Maybe ( maybeToList )


-- ----------------------------------------------------------------------------
-- * Top level
--

-- | Pretty print LLVM data code
pprLlvmData :: LlvmData -> SDoc
pprLlvmData (globals, types) =
    let ppLlvmTys (LMAlias    a) = ppLlvmAlias a
        ppLlvmTys (LMFunction f) = ppLlvmFunctionDecl f
        ppLlvmTys _other         = empty

        types'   = vcat $ map ppLlvmTys types
        globals' = ppLlvmGlobals globals
    in types' $+$ globals'


-- | Pretty print LLVM code
pprLlvmCmmDecl :: MetaId -> LabelMap DebugBlock -> LlvmCmmDecl -> LlvmM (SDoc, [LlvmVar])
pprLlvmCmmDecl _ _ (CmmData _ lmdata)
  = return (vcat $ map pprLlvmData lmdata, [])

pprLlvmCmmDecl cuId debug_map (CmmProc (label, mb_info) entry_lbl live (ListGraph blks))
  = do let lbl = case mb_info of
                     Nothing                   -> entry_lbl
                     Just (Statics info_lbl _) -> info_lbl
           link = if externallyVisibleCLabel lbl
                      then ExternallyVisible
                      else Internal

       funDec <- llvmFunSig live lbl link
       dflags <- getDynFlags
       let buildArg = fsLit . showSDoc dflags . ppPlainName
           funArgs = map buildArg (llvmFunArgs dflags live)
           funSect = llvmFunSection dflags (decName funDec)
           defName = decName funDec `appendFS` fsLit "$def"

       -- generate the info table
       prefix <- case mb_info of
                     Nothing -> return Nothing
                     Just (Statics _ statics) -> do
                       infoStatics <- mapM genData statics
                       let infoTy = LMStruct $ map getStatType infoStatics
                       return $ Just $ LMStaticStruc infoStatics infoTy

       -- generate debug information metadata
       subprogMeta <-
           case mapLookup label debug_map >>= dblSourceTick of
             Just (SourceNote span name) -> do
               subprogMeta <- getMetaUniqueId
               fileMeta <- getMetaUniqueId
               typeMeta <- getMetaUniqueId
               let fileDef = MetaUnnamed fileMeta NotDistinct
                             $ MetaDIFile { difFilename = srcSpanFile span
                                          , difDirectory = fsLit "TODO"
                                          }
                   typeMetaDef =
                       MetaUnnamed typeMeta NotDistinct
                       $ MetaDISubroutineType [MetaVar $ LMLitVar $ LMNullLit i1]
                   subprog =
                       MetaDISubprogram { disName         = fsLit name
                                        , disLinkageName  = fsLit name
                                        , disScope        = fileMeta
                                        , disFile         = fileMeta
                                        , disLine         = srcSpanStartLine span
                                        , disType         = typeMeta
                                        , disIsDefinition = True
                                        , disCompileUnit  = cuId
                                        }
                   location = MetaDILocation { dilLine = srcSpanStartLine span
                                              , dilColumn = srcSpanStartCol span
                                              , dilScope  = subprogMeta }
               locationMeta <- getMetaUniqueId
               --addMetaDecl (MetaUnnamed locationMeta NotDistinct location)
               addMetaDecl fileDef
               addMetaDecl typeMetaDef
               addMetaDecl (MetaUnnamed subprogMeta Distinct subprog)
               return $ Just subprogMeta
             _   -> return Nothing

       let
          addDebugLocation :: MetaId -> LlvmStatement -> LlvmStatement
          addDebugLocation mid llvm =
            case llvm of
              MetaStmt ms s -> MetaStmt (dbg_meta : ms) s
              s -> MetaStmt [dbg_meta] s
            where
              dbg_meta = MetaAnnot (fsLit "dbg") (MetaNode mid)

          mkLlvmBlock (BasicBlock id stmts) = do
            llvm_stmts <-
                  case (,) <$> (mapLookup id debug_map >>= dblSourceTick)
                           <*> subprogMeta  of
                    Just ((SourceNote span _name), subprogMeta) -> do
                      locationMeta <- getMetaUniqueId
                      let location = MetaDILocation { dilLine = srcSpanStartLine span
                                                    , dilColumn = srcSpanStartCol span
                          -- This causes errors at -O2 if you set it to subprogMeta
                                                    , dilScope  = subprogMeta }
                      addMetaDecl (MetaUnnamed locationMeta NotDistinct location)
                      return (map (addDebugLocation locationMeta) stmts)
                    _ -> return stmts
            return $ LlvmBlock (getUnique id) llvm_stmts
       lmblocks <- mapM mkLlvmBlock blks

       let subprogAnnot = MetaAnnot (fsLit "dbg") . MetaNode <$> subprogMeta
           funcMetas = maybeToList subprogAnnot


       let attrs = XRayInstrument : llvmStdFunAttrs
           fun = LlvmFunction funDec funArgs attrs funSect
                              prefix funcMetas lmblocks
           name = decName $ funcDecl fun
           funcDecl' = (funcDecl fun) { decName = defName }
           fun' = fun { funcDecl = funcDecl' }
           funTy = LMFunction funcDecl'
           funVar = LMGlobalVar name
                                (LMPointer funTy)
                                link
                                Nothing
                                Nothing
                                Alias
           defVar = LMGlobalVar defName
                                (LMPointer funTy)
                                (funcLinkage funcDecl')
                                (funcSect fun)
                                (funcAlign funcDecl')
                                Alias
           alias = LMGlobal funVar
                            (Just $ LMBitc (LMStaticPointer defVar)
                                           i8Ptr)

       return (ppLlvmGlobal alias $+$ ppLlvmFunction fun', [])


-- | The section we are putting info tables and their entry code into, should
-- be unique since we process the assembly pattern matching this.
infoSection :: String
infoSection = "X98A__STRIP,__me"
