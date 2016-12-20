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
import TcEvidence ( mkWpTyApps )
import TcRnMonad
import HscTypes ( lookupId )
import PrelNames
import TysPrim ( primTyCons, primTypeableTyCons )
import TysWiredIn ( tupleTyCon, runtimeRepTyCon, vecCountTyCon, vecElemTyCon
                  , nilDataCon, consDataCon )
import Id
import Type
import Kind ( isTYPEApp )
import TyCon
import DataCon
import Name ( getOccName )
import OccName
import Module
import NameEnv
import HsSyn
import DynFlags
import Bag
import Var ( TyVarBndr(..) )
import VarEnv
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
             mod_id = case tcg_tr_module tcg_env of  -- Should be set by now
                        Just mod_id -> mod_id
                        Nothing     -> pprPanic "tcMkTypeableBinds" (ppr tycons)
       ; traceTc "mkTypeableBinds" (ppr tycons)
       ; mkTypeableTyConBinds mod_id tycons
       } }
  where
    needs_typeable_binds tc
      | tc `elem` [runtimeRepTyCon, vecCountTyCon, vecElemTyCon]
      = False
      | otherwise =
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
       ; return $ nlHsApps (dataConWrapId trModuleDataCon)
                           [ trNameLit (unitIdFS (moduleUnitId mod))
                           , trNameLit (moduleNameFS (moduleName mod)) ]
       }

{- *********************************************************************
*                                                                      *
                Building type-representation bindings
*                                                                      *
********************************************************************* -}

-- | Generate TyCon bindings for a set of type constructors
mkTypeableTyConBinds :: Id -> [TyCon] -> TcM TcGblEnv
mkTypeableTyConBinds mod_id tycons
  = do { mod <- getModule
       ; let mod_expr = nlHsVar mod_id
       ; stuff <- collect_stuff mod mod_expr
       ; let all_tycons = [ tc' | tc <- tycons
                                , tc' <- tc : tyConATs tc ]
                             -- We need type representations for any associated types

         -- First extend the type environment with all of the bindings which we
         -- are going to produce since we may need to refer to them while
         -- generating the RHSs
       ; let tycon_rep_bndrs :: [Id]
             tycon_rep_bndrs = [ rep_id
                               | tc <- all_tycons
                               , let promoted = map promoteDataCon (tyConDataCons tc)
                               , tc' <- tc : promoted
                               , Just rep_id <- pure $ tyConRepId stuff tc'
                               ]
       ; gbl_env <- pprTrace "typeable tycons" (ppr $ map (\x -> (x, tyConRepId stuff x)) all_tycons)
                    $ pprTrace "typeable tycons'" (ppr [ (tc', promoted, tyConRepId stuff tc')
                                                       | tc <- all_tycons
                                                       , let promoted = map promoteDataCon (tyConDataCons tc)
                                                       , tc' <- tc:promoted ])
                    $ pprTrace "typeable binders" (ppr tycon_rep_bndrs) $
                    tcExtendGlobalValEnv tycon_rep_bndrs getGblEnv

       ; setGblEnv gbl_env $ foldlM (mk_typeable_binds stuff) gbl_env all_tycons }

-- | Generate bindings for the type representation of a wired-in 'TyCon's defined
-- by the virtual "GHC.Prim" module. This is where we inject the representation
-- bindings for these primitive types into "GHC.Types"
--
-- See Note [Grand plan for Typeable] in this module.
mkPrimTypeableBinds :: TcM TcGblEnv
mkPrimTypeableBinds
  = do { mod <- getModule
       ; if mod == gHC_TYPES
           then do { trModuleTyCon <- pprTrace "mkPrimTypeableBinds" (ppr $ map tyConName ghcPrimTypeableTyCons) $ tcLookupTyCon trModuleTyConName
                   ; let ghc_prim_module_id =
                             mkExportedVanillaId trGhcPrimModuleName
                                                 (mkTyConTy trModuleTyCon)

                   ; ghc_prim_module_bind <- mkVarBind ghc_prim_module_id
                                             <$> mkModIdRHS gHC_PRIM

                   ; gbl_env <- tcExtendGlobalValEnv [ghc_prim_module_id] getGblEnv
                   ; setGblEnv (gbl_env `addTypecheckedBinds` [unitBag ghc_prim_module_bind])
                     $ mkTypeableTyConBinds ghc_prim_module_id ghcPrimTypeableTyCons }
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
    [ [ runtimeRepTyCon, vecCountTyCon, vecElemTyCon
      , funTyCon, tupleTyCon Unboxed 0]
    , map (tupleTyCon Unboxed) [2..mAX_TUPLE_SIZE]
    , primTyCons
    ]
  where
    -- Some things, like TYPE, have mutually recursion kind relationships and
    -- therefore have manually-defined representations. See Note [Mutually
    -- recursive representations of primitive types] in Data.Typeable.Internal
    -- and Note [Grand plan for Typeable] for details.
    definedManually tc = tyConName tc `elemNameEnv` primTypeableTyCons

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
mk_typeable_binds :: TypeableStuff -> TcGblEnv -> TyCon -> TcM TcGblEnv
mk_typeable_binds stuff gbl_env tycon
  = do binds <- mkTyConRepBinds stuff tycon
       let gbl_env' = pprTrace "mk_typeable_binds" (ppr binds) $ gbl_env `addTypecheckedBinds` [binds]
       setGblEnv gbl_env' $ do
            promoted_reps <- mapM (mkTyConRepBinds stuff . promoteDataCon)
                                  (tyConDataCons tycon)
            return $ gbl_env' `addTypecheckedBinds` promoted_reps

-- | The 'Id' of the @TyCon@ binding for a type constructor.
tyConRepId :: TypeableStuff -> TyCon -> Maybe Id
tyConRepId (Stuff {..}) tycon
  = mkRepId <$> tyConRepName_maybe tycon
  where
    mkRepId rep_name = mkExportedVanillaId rep_name (mkTyConTy trTyConTyCon)

-- | Make typeable bindings for the given 'TyCon'.
mkTyConRepBinds :: TypeableStuff -> TyCon -> TcRn (LHsBinds Id)
mkTyConRepBinds stuff@(Stuff {..}) tycon
  = pprTrace "mkTyConRepBinds" (ppr tycon) $
    case tyConRepId stuff tycon of
      Just tycon_rep_id -> do
          tycon_rep_rhs <- mkTyConRepTyConRHS stuff tycon
          let tycon_rep = mkVarBind tycon_rep_id tycon_rep_rhs
          return $ unitBag tycon_rep
      _ -> return emptyBag

-- | Produce the right-hand-side of a @TyCon@ representation.
mkTyConRepTyConRHS :: TypeableStuff -> TyCon -> TcRn (LHsExpr Id)
mkTyConRepTyConRHS stuff@(Stuff {..}) tycon
  = do kind_rep <- mkTyConKindRep stuff tycon
       let rep_rhs = nlHsApps (dataConWrapId trTyConDataCon)
                              [ nlHsLit (word64 high), nlHsLit (word64 low)
                              , mod_rep
                              , trNameLit (mkFastString tycon_str)
                              , nlHsLit (int 0) -- TODO
                              , kind_rep
                              ]
       return rep_rhs
  where

    tycon_str = add_tick (occNameString (getOccName tycon))
    add_tick s | isPromotedDataCon tycon = '\'' : s
               | otherwise               = s

    hashThis :: String
    hashThis = unwords [pkg_str, mod_str, tycon_str]

    Fingerprint high low = fingerprintString hashThis

    int :: Int -> HsLit
    int n = HsIntPrim (SourceText $ show n) (toInteger n)

    word64 :: Word64 -> HsLit
    word64
      | wORD_SIZE dflags == 4 = \n -> HsWord64Prim NoSourceText (toInteger n)
      | otherwise             = \n -> HsWordPrim   NoSourceText (toInteger n)

pprType' :: Type -> SDoc
pprType' (TyVarTy v) = text "tyvar" <+> ppr v
pprType' (AppTy a b) = text "app" <+> parens (ppr a) <+> parens (ppr b)
pprType' (TyConApp tycon tys) = text "conapp" <+> ppr tycon <+> hsep (map pprType' tys)
pprType' (ForAllTy bndr ty) = text "forall" <+> ppr bndr <> char '.' <+> pprType' ty
pprType' (FunTy a b) = text "fun" <+> parens (ppr a) <+> parens (ppr b)
pprType' (LitTy lit) = text "lit" <+> ppr lit
pprType' (CastTy ty _) = text "cast" <+> pprType' ty
pprType' (CoercionTy _) = text "coercion"

{-
Note [Representing TyCon kinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One of the operations supported by Typeable is typeRepKind,

    typeRepKind :: TypeRep (a :: k) -> TypeRep k

Implementing this is a bit tricky. To see why let's consider the TypeRep
encoding of `Proxy Int` where

    data Proxy (a :: k) :: Type

which looks like,

    $tcProxy :: TyCon
    $trInt   :: TypeRep Int
    $trType  :: TypeRep Type

    $trProxyType :: TypeRep (Proxy :: Type -> Type)
    $trProxyType = TrTyCon $tcProxy
                           [$trType]  -- kind variable instantiation

    $trProxy :: TypeRep (Proxy Int)
    $trProxy = TrApp $trProxyType $trInt

Note how $trProxyType encodes only the kind variables of the TyCon
instantiation. To compute the kind (Proxy Int) we need to have a recipe to
compute the kind of a concrete instantiation of Proxy. We call"inplace/bin/ghc-stage1" -hisuf hi -osuf  o -hcsuf hc -static  -O -H64m -Wall      -this-unit-id ghc-prim-0.5.0.0 -hide-all-packages -i -ilibraries/ghc-prim/. -ilibraries/ghc-prim/dist-install/build -Ilibraries/ghc-prim/dist-install/build -ilibraries/ghc-prim/dist-install/build/./autogen -Ilibraries/ghc-prim/dist-install/build/./autogen -Ilibraries/ghc-prim/.    -optP-include -optPlibraries/ghc-prim/dist-install/build/./autogen/cabal_macros.h -package-id rts -this-unit-id ghc-prim -XHaskell2010 -O -dcore-lint  -no-user-package-db -rtsopts -Wno-trustworthy-safe -Wno-deprecated-flags     -Wnoncanonical-monad-instances  -odir libraries/ghc-prim/dist-install/build -hidir libraries/ghc-prim/dist-install/build -stubdir libraries/ghc-prim/dist-install/build  -split-sections -dynamic-too -c libraries/ghc-prim/./GHC/Types.hs -o libraries/ghc-prim/dist-install/build/GHC/Types.o -dyno libraries/ghc-prim/dist-install/build/GHC/Types.dyn_o
 this recipe a
KindRep and store it in the TyCon produced for Proxy,

    type KindBndr = Int   -- de Bruijn index

    data KindRep = KindRepTyConApp TyCon [KindRep]
                 | KindRepVar !KindBndr
                 | KindRepApp KindRep KindRep
                 | KindRepFun KindRep KindRep

The KindRep for Proxy would look like,

    $tkProxy :: KindRep
    $tkProxy = KindRepFun (KindRepVar 0) (KindRepTyConApp $trType [])


data Maybe a = Nothing | Just a

'Just :: a -> Maybe a

F :: forall k. k -> forall k'. k' -> Type
-}

-- | Produce a @KindRep@ expression for the given 'Kind'.
mkTyConKindRep :: TypeableStuff -> TyCon -> TcRn (LHsExpr Id)
mkTyConKindRep (Stuff {..}) tycon = do
    let bndrs = mkVarEnv $ (`zip` [0..]) $ map binderVar
                $ reverse $ filter isNamedTyConBinder (tyConBinders tycon)
    pprTrace "mkTyConKeyRepBinds" (ppr tycon <+> pprType' (tyConKind tycon)) $ go bndrs (tyConResKind tycon)
  where
    -- Compute RHS
    go :: VarEnv Int -> Kind -> TcRn (LHsExpr Id)
    go bndrs (TyVarTy v)
      | Just idx <- lookupVarEnv bndrs v
      = return $ nlHsApps (dataConWrapId kindRepVarDataCon)
                          [nlHsIntLit (fromIntegral idx)]
      | otherwise
      = pprPanic "mkTyConKindRepBinds.go(tyvar)" (ppr v $$ ppr bndrs)
    go bndrs (AppTy t1 t2)
      = do t1' <- go bndrs t1
           t2' <- go bndrs t2
           return $ nlHsApps (dataConWrapId kindRepAppDataCon) [t1', t2']
    go _ ty | Just rr <- isTYPEApp ty
      = pprTrace "mkTyConKeyRepBinds(type)" (ppr rr) $
        return $ nlHsApps (dataConWrapId kindRepTYPEDataCon) [nlHsVar $ dataConWrapId rr]
    go bndrs (TyConApp tycon tys)
      | Just rep_name <- tyConRepName_maybe tycon
      = do rep_id <- lookupId rep_name
           tys' <- mapM (go bndrs) tys
           return $ nlHsApps (dataConWrapId kindRepTyConAppDataCon)
                             [ nlHsVar rep_id
                             , mkList (mkTyConTy kindRepTyCon) tys'
                             ]
      | otherwise
      = pprPanic "UnrepresentableThingy" empty
    go _bndrs (ForAllTy (TvBndr var _) ty)
      = pprPanic "mkTyConKeyRepBinds(forall)" (ppr var $$ ppr ty)
    --  = let bndrs' = extendVarEnv (mapVarEnv (+1) bndrs) var 0
    --    in go bndrs' ty
    go bndrs (FunTy t1 t2)
      = do t1' <- go bndrs t1
           t2' <- go bndrs t2
           return $ nlHsApps (dataConWrapId kindRepFunDataCon) [ t1', t2' ]
    go _ (LitTy lit)
      = pprPanic "mkTyConKindRepBinds.go(lit)" (ppr lit) -- TODO
    go bndrs (CastTy ty _)
      = go bndrs ty
    go _ (CoercionTy co)
      = pprPanic "mkTyConKindRepBinds.go(coercion)" (ppr co)

    mkList :: Type -> [LHsExpr Id] -> LHsExpr Id
    mkList ty = foldr consApp (nilExpr ty)
      where
        cons = consExpr ty
        consApp :: LHsExpr Id -> LHsExpr Id -> LHsExpr Id
        consApp x xs = cons `nlHsApp` x `nlHsApp` xs

    nilExpr :: Type -> LHsExpr Id
    nilExpr ty = mkLHsWrap (mkWpTyApps [ty]) (nlHsVar $ dataConWrapId nilDataCon)

    consExpr :: Type -> LHsExpr Id
    consExpr ty = mkLHsWrap (mkWpTyApps [ty]) (nlHsVar $ dataConWrapId consDataCon)

