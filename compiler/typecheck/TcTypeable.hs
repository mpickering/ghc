{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1999
-}

{-# LANGUAGE RecordWildCards #-}

module TcTypeable(mkTypeableBinds) where


import BasicTypes ( SourceText(..) )
import TcBinds( addTypecheckedBinds )
import IfaceEnv( newGlobalBinder )
import TyCoRep( Type(..) )
import TcEnv
import TcRnMonad
import HscTypes ( lookupId )
import PrelNames
import TysPrim ( primTyCons, primTypeableTyCons )
import TysWiredIn ( tupleTyCon )
import Id
import Type
import Kind ( isStarKind)
import TyCon
import DataCon
import Name ( getOccName, nameOccName )
import OccName
import Module
import NameEnv
import HsSyn
import DynFlags
import Bag
import Var ( TyVarBndr(..) )
import VarEnv
import SrcLoc ( noLoc )
import BasicTypes ( Boxity(..) )
import Constants  ( mAX_TUPLE_SIZE )
import Fingerprint(Fingerprint(..), fingerprintString)
import Outputable
import FastString ( FastString, mkFastString )

import Data.Word( Word64 )

{- Note [Grand plan for Typeable]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The overall plan is this:

1. Generate a binding for each module p:M
   (done in TcTypeable by mkModIdBindings)
       M.$trModule :: GHC.Types.Module
       M.$trModule = Module "p" "M"
   ("tr" is short for "type representation"; see GHC.Types)

   We might want to add the filename too.
   This can be used for the lightweight stack-tracing stuff too

   Record the Name M.$trModule in the tcg_tr_module field of TcGblEnv

2. Generate a binding for every data type declaration T in module M,
       M.$tcT :: GHC.Types.TyCon
       M.$tcT = TyCon ...fingerprint info...
                      $trModule
                      "T"
   We define (in TyCon)
      type TyConRepName = Name
   to use for these M.$tcT "tycon rep names".

3. Record the TyConRepName in T's TyCon, including for promoted
   data and type constructors, and kinds like * and #.

   The TyConRepName is not an "implicit Id".  It's more like a record
   selector: the TyCon knows its name but you have to go to the
   interface file to find its type, value, etc

4. Solve Typeable constraints.  This is done by a custom Typeable solver,
   currently in TcInteract, that use M.$tcT so solve (Typeable T).

There are many wrinkles:

* The timing of when we produce this bindings is rather important: they must be
  defined after the rest of the module has been typechecked since we need to be
  able to lookup Module and TyCon in the type environment and we may be
  currently compiling GHC.Types (where they are defined).

* GHC.Prim doesn't have any associated object code, so we need to put the
  representations for types defined in this module elsewhere. We chose this
  place to be GHC.Types. TcTypeable.mkPrimTypeableBinds is responsible for
  injecting the bindings for the GHC.Prim representions when compiling
  GHC.Types.

* TyCon.tyConRepModOcc is responsible for determining where to find
  the representation binding for a given type. This is where we handle
  the special case for GHC.Prim.

* To save space and reduce dependencies, we need use quite low-level
  representations for TyCon and Module.  See GHC.Types
  Note [Runtime representation of modules and tycons]

-}

-- | Generate the Typeable bindings for a module. This is the only
-- entry-point of this module and is invoked by the typechecker driver in
-- 'tcRnSrcDecls'.
--
-- See Note [Grand plan for Typeable] in TcTypeable.
mkTypeableBinds :: TcM TcGblEnv
mkTypeableBinds
  = do { -- Create a binding for $trModule.
         -- Do this before processing any data type declarations,
         -- which need tcg_tr_module to be initialised
       ; tcg_env <- mkModIdBindings
         -- Now we can generate the TyCon representations...
         -- First we handle the primitive TyCons if we are compiling GHC.Types
       ; tcg_env <- setGblEnv tcg_env mkPrimTypeableBinds
         -- Then we produce bindings for the user-defined types in this module.
       ; setGblEnv tcg_env $

    do { let tycons = filter needs_typeable_binds (tcg_tcs tcg_env)
       ; traceTc "mkTypeableBinds" (ppr tycons)
       ; mkTypeableTyConBinds tycons
       } }
  where
    needs_typeable_binds tc =
          (not (isFamInstTyCon tc) && isAlgTyCon tc)
       || isDataFamilyTyCon tc
       || isClassTyCon tc


{- *********************************************************************
*                                                                      *
            Building top-level binding for $trModule
*                                                                      *
********************************************************************* -}

mkModIdBindings :: TcM TcGblEnv
mkModIdBindings
  = do { mod <- getModule
       ; loc <- getSrcSpanM
       ; mod_nm        <- newGlobalBinder mod (mkVarOcc "$trModule") loc
       ; trModuleTyCon <- tcLookupTyCon trModuleTyConName
       ; let mod_id = mkExportedVanillaId mod_nm (mkTyConApp trModuleTyCon [])
       ; mod_bind      <- mkVarBind mod_id <$> mkModIdRHS mod

       ; tcg_env <- tcExtendGlobalValEnv [mod_id] getGblEnv
       ; return (tcg_env { tcg_tr_module = Just mod_id }
                 `addTypecheckedBinds` [unitBag mod_bind]) }

mkModIdRHS :: Module -> TcM (LHsExpr Id)
mkModIdRHS mod
  = do { trModuleDataCon <- tcLookupDataCon trModuleDataConName
       ; trNameLit <- mkTrNameLit
       ; return $ nlHsDataCon trModuleDataCon
                  `nlHsApp` trNameLit (unitIdFS (moduleUnitId mod))
                  `nlHsApp` trNameLit (moduleNameFS (moduleName mod))
       }

{- *********************************************************************
*                                                                      *
                Building type-representation bindings
*                                                                      *
********************************************************************* -}

-- | Generate TyCon bindings for a set of type constructors
mkTypeableTyConBinds :: [TyCon] -> TcM TcGblEnv
mkTypeableTyConBinds tycons
  = do { gbl_env <- getGblEnv
       ; mod <- getModule
       ; let mod_expr = case tcg_tr_module gbl_env of  -- Should be set by now
                           Just mod_id -> nlHsVar mod_id
                           Nothing     -> pprPanic "tcMkTypeableBinds" (ppr tycons)
       ; stuff <- collect_stuff mod mod_expr
       ; let all_tycons = [ tc' | tc <- tycons, tc' <- tc : tyConATs tc ]
                             -- We need type representations for any associated types
       ; tc_binds <- mapM (mk_typeable_binds stuff) all_tycons
       ; let tycon_rep_ids = foldr ((++) . collectHsBindsBinders) [] tc_binds

       ; gbl_env <- tcExtendGlobalValEnv tycon_rep_ids getGblEnv
       ; return (gbl_env `addTypecheckedBinds` tc_binds) }

-- | Generate bindings for the type representation of a wired-in 'TyCon's defined
-- by the virtual "GHC.Prim" module. This is where we inject the representation
-- bindings for these primitive types into "GHC.Types"
--
-- See Note [Grand plan for Typeable] in this module.
mkPrimTypeableBinds :: TcM TcGblEnv
mkPrimTypeableBinds
  = do { mod <- getModule
       ; if mod == gHC_TYPES
           then do { trModuleTyCon <- tcLookupTyCon trModuleTyConName
                   ; let ghc_prim_module_id =
                             mkExportedVanillaId trGhcPrimModuleName
                                                 (mkTyConTy trModuleTyCon)

                   ; ghc_prim_module_bind <- mkVarBind ghc_prim_module_id
                                             <$> mkModIdRHS gHC_PRIM

                   ; stuff <- collect_stuff gHC_PRIM (nlHsVar ghc_prim_module_id)
                   ; binds <- ghcPrimTypeableBinds stuff
                   ; let prim_binds :: LHsBinds Id
                         prim_binds = ghc_prim_module_bind `consBag` binds

                         prim_rep_ids = collectHsBindsBinders prim_binds
                   ; gbl_env <- tcExtendGlobalValEnv prim_rep_ids getGblEnv
                   ; return (gbl_env `addTypecheckedBinds` [prim_binds])
                   }
           else getGblEnv
       }
  where

-- | This is the list of primitive 'TyCon's for which we must generate bindings
-- in "GHC.Types". This should include all types defined in "GHC.Prim".
--
-- The majority of the types we need here are contained in 'primTyCons'.
-- However, not all of them: in particular unboxed tuples are absent since we
-- don't want to include them in the original name cache. See
-- Note [Built-in syntax and the OrigNameCache] in IfaceEnv for more.
ghcPrimTypeableTyCons :: [TyCon]
ghcPrimTypeableTyCons = filter (not . definedManually) $ concat
    [ [funTyCon, tupleTyCon Unboxed 0]
    , map (tupleTyCon Unboxed) [2..mAX_TUPLE_SIZE]
    , primTyCons
    ]
  where
    -- Some things, like TYPE, have mutually recursion kind relationships and
    -- therefore have manually-defined representations. See Note [Mutually
    -- recursive representations of primitive types] in Data.Typeable.Internal
    -- and Note [Grand plan for Typeable] for details.
    definedManually tc = tyConName tc `elemNameEnv` primTypeableTyCons

-- | Generate bindings for the type representation of the wired-in TyCons defined
-- by the virtual "GHC.Prim" module. This differs from the usual
-- @mkTypeableBinds@ path in that here we need to lie to 'mk_typeable_binds'
-- about the module we are compiling (since we are currently compiling
-- "GHC.Types" yet are producing representations for types in "GHC.Prim").
--
-- See Note [Grand plan for Typeable] in this module.
ghcPrimTypeableBinds :: TypeableStuff -> TcM (LHsBinds Id)
ghcPrimTypeableBinds stuff
  = unionManyBags <$> mapM (mk_typeable_binds stuff) all_prim_tys
  where
    all_prim_tys :: [TyCon]
    all_prim_tys = [ tc' | tc <- ghcPrimTypeableTyCons
                         , tc' <- tc : tyConATs tc ]

data TypeableStuff
    = Stuff { dflags         :: DynFlags
            , mod_rep        :: LHsExpr Id  -- ^ Of type GHC.Types.Module
            , pkg_str        :: String      -- ^ Package name
            , mod_str        :: String      -- ^ Module name
            , trTyConTyCon   :: TyCon       -- ^ of @TyCon@
            , trTyConDataCon :: DataCon     -- ^ of @TyCon@
            , trNameLit      :: FastString -> LHsExpr Id
                                            -- ^ To construct @TrName@s
            , kindRepTyCon   :: TyCon       -- ^ of @KindRep@
            , kindRepTyConAppDataCon :: DataCon -- ^ of @KindRepTyConApp@
            , kindRepVarDataCon :: DataCon -- ^ of @KindRepVar@
            , kindRepAppDataCon :: DataCon -- ^ of @KindRepApp@
            , kindRepFunDataCon :: DataCon -- ^ of @KindRepFun@
            , kindRepTYPEDataCon :: DataCon -- ^ of @KindRepType@
            }

-- | Collect various tidbits which we'll need to generate TyCon representations.
collect_stuff :: Module -> LHsExpr Id -> TcM TypeableStuff
collect_stuff mod mod_rep = do
    dflags <- getDynFlags
    let pkg_str  = unitIdString (moduleUnitId mod)
        mod_str  = moduleNameString (moduleName mod)

    trTyConTyCon   <- tcLookupTyCon trTyConTyConName
    trTyConDataCon <- tcLookupDataCon trTyConDataConName
    kindRepTyCon           <- tcLookupTyCon   kindRepTyConName
    kindRepTyConAppDataCon <- tcLookupDataCon kindRepTyConAppDataConName
    kindRepVarDataCon      <- tcLookupDataCon kindRepVarDataConName
    kindRepAppDataCon      <- tcLookupDataCon kindRepAppDataConName
    kindRepFunDataCon      <- tcLookupDataCon kindRepFunDataConName
    kindRepTYPEDataCon     <- tcLookupDataCon kindRepTYPEDataConName
    trNameLit      <- mkTrNameLit
    return Stuff {..}

-- | Lookup the necessary pieces to construct the @trNameLit@. We do this so we
-- can save the work of repeating lookups when constructing many TyCon
-- representations.
mkTrNameLit :: TcM (FastString -> LHsExpr Id)
mkTrNameLit = do
    trNameSDataCon <- tcLookupDataCon trNameSDataConName
    let trNameLit :: FastString -> LHsExpr Id
        trNameLit fs = nlHsDataCon trNameSDataCon
                       `nlHsApp` nlHsLit (mkHsStringPrimLit fs)
    return trNameLit

-- | Make bindings for the type representations of a 'TyCon' and its
-- promoted constructors.
mk_typeable_binds :: TypeableStuff -> TyCon -> TcM (LHsBinds Id)
mk_typeable_binds stuff tycon
  = do reps <- mkTyConRepBinds stuff tycon
       promoted_reps <- mapM (mkTyConRepBinds stuff . promoteDataCon)
                             (tyConDataCons tycon)
       return $ reps `unionBags` unionManyBags promoted_reps

-- | Make typeable bindings for the given 'TyCon'.
mkTyConRepBinds :: TypeableStuff -> TyCon -> TcRn (LHsBinds Id)
mkTyConRepBinds stuff@(Stuff {..}) tycon
  = pprTrace "mkTyConRepBinds" (ppr tycon) $
    case tyConRepName_maybe tycon of
      Just rep_name -> do
          kind_rep <- mkTyConKindRepBinds stuff tycon
                                          (tyConResKind tycon)
          return $ listToBag [ tycon_rep, kind_rep ]
        where
           tycon_rep_id  = mkExportedVanillaId rep_name (mkTyConTy trTyConTyCon)
           tycon_rep_rhs = mkTyConRepTyConRHS stuff tycon
           tycon_rep     = mkVarBind tycon_rep_id tycon_rep_rhs
      _ -> return emptyBag

-- | Produce the right-hand-side of a @TyCon@ representation.
mkTyConRepTyConRHS :: TypeableStuff -> TyCon -> LHsExpr Id
mkTyConRepTyConRHS (Stuff {..}) tycon = rep_rhs
  where
    rep_rhs = nlHsDataCon trTyConDataCon
              `nlHsApp` nlHsLit (word64 high)
              `nlHsApp` nlHsLit (word64 low)
              `nlHsApp` mod_rep
              `nlHsApp` trNameLit (mkFastString tycon_str)

    tycon_str = add_tick (occNameString (getOccName tycon))
    add_tick s | isPromotedDataCon tycon = '\'' : s
               | otherwise               = s

    hashThis :: String
    hashThis = unwords [pkg_str, mod_str, tycon_str]

    Fingerprint high low = fingerprintString hashThis

    word64 :: Word64 -> HsLit
    word64
      | wORD_SIZE dflags == 4 = \n -> HsWord64Prim NoSourceText (toInteger n)
      | otherwise             = \n -> HsWordPrim   NoSourceText (toInteger n)
