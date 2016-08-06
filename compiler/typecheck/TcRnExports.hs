module TcRnExports (rnExports, tcExports) where

import DynFlags
import StaticFlags
import HsSyn
import PrelNames
import RdrName
import TcHsSyn
import TcExpr
import TcRnMonad
import TcEvidence
import PprTyThing( pprTyThing )
import MkIface( tyThingToIfaceDecl )
import Coercion( pprCoAxiom )
import CoreFVs( orphNamesOfFamInst )
import FamInst
import InstEnv
import FamInstEnv
import TcAnnotations
import TcBinds
import HeaderInfo       ( mkPrelImports )
import TcDefaults
import TcEnv
import TcRules
import TcForeign
import TcInstDcls
import TcIface
import TcMType
import TcType
import TcSimplify
import TcTyClsDecls
import TcTypeable ( mkTypeableBinds )
import LoadIface
import TidyPgm    ( mkBootModDetailsTc )
import RnNames
import RnEnv
import RnSource
import ErrUtils
import Id
import IdInfo
import VarEnv
import Module
import UniqDFM
import Name
import NameEnv
import NameSet
import Avail
import TyCon
import SrcLoc
import HscTypes
import ListSetOps
import Outputable
import ConLike
import DataCon
import PatSyn
import Type
import Class
import BasicTypes hiding( SuccessFlag(..) )
import CoAxiom
import Annotations
import Data.List ( sortBy )
import Data.Ord
import Data.Char
import FastString
import Maybes
import Util
import Bag
import Inst (tcGetInsts)
import qualified GHC.LanguageExtensions as LangExt

import Control.Monad
import GHC.Exts (groupWith, sortWith)
import DynFlags
import HsSyn
import TcEnv
import RnEnv
import RnHsDoc          ( rnHsDoc )
import LoadIface        ( loadSrcInterface )
import TcRnMonad
import PrelNames
import Module
import Name
import NameEnv
import NameSet
import Avail
import FieldLabel
import HscTypes
import RdrName
import RdrHsSyn        ( setRdrNameSpace )
import Outputable
import Maybes
import SrcLoc
import BasicTypes      ( TopLevelFlag(..), StringLiteral(..) )
import ErrUtils
import Util
import FastString
import FastStringEnv
import ListSetOps
import Id
import Type
import PatSyn
import qualified GHC.LanguageExtensions as LangExt

import Control.Monad
import Data.Foldable (asum)
import Data.Either      ( partitionEithers, isRight, rights )
-- import qualified Data.Foldable as Foldable
import Data.Map         ( Map )
import qualified Data.Map as Map
import Data.Ord         ( comparing )
import Data.List        ( partition, (\\), find, sortBy )
-- import qualified Data.Set as Set
import System.FilePath  ((</>))
import System.IO

{-
************************************************************************
*                                                                      *
\subsection{Export list processing}
*                                                                      *
************************************************************************

Processing the export list.

You might think that we should record things that appear in the export
list as ``occurrences'' (using @addOccurrenceName@), but you'd be
wrong.  We do check (here) that they are in scope, but there is no
need to slurp in their actual declaration (which is what
@addOccurrenceName@ forces).

Indeed, doing so would big trouble when compiling @PrelBase@, because
it re-exports @GHC@, which includes @takeMVar#@, whose type includes
@ConcBase.StateAndSynchVar#@, and so on...

Note [Exports of data families]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose you see (Trac #5306)
        module M where
          import X( F )
          data instance F Int = FInt
What does M export?  AvailTC F [FInt]
                  or AvailTC F [F,FInt]?
The former is strictly right because F isn't defined in this module.
But then you can never do an explicit import of M, thus
    import M( F( FInt ) )
because F isn't exported by M.  Nor can you import FInt alone from here
    import M( FInt )
because we don't have syntax to support that.  (It looks like an import of
the type FInt.)

At one point I implemented a compromise:
  * When constructing exports with no export list, or with module M(
    module M ), we add the parent to the exports as well.
  * But not when you see module M( f ), even if f is a
    class method with a parent.
  * Nor when you see module M( module N ), with N /= M.

But the compromise seemed too much of a hack, so we backed it out.
You just have to use an explicit export list:
    module M( F(..) ) where ...
-}

type ExportAccum        -- The type of the accumulating parameter of
                        -- the main worker function in rnExports
     = ([LIE Name],             -- Export items with Names
        ExportOccMap,           -- Tracks exported occurrence names
        [AvailInfo])            -- The accumulated exported stuff
                                --   Not nub'd!

emptyExportAccum :: ExportAccum
emptyExportAccum = ([], emptyOccEnv, [])

type ExportOccMap = OccEnv (Name, IE RdrName)
        -- Tracks what a particular exported OccName
        --   in an export list refers to, and which item
        --   it came from.  It's illegal to export two distinct things
        --   that have the same occurrence name

rnExports :: Bool       -- False => no 'module M(..) where' header at all
          -> Maybe (Located [LIE RdrName]) -- Nothing => no explicit export list
          -> TcGblEnv
          -> RnM (Maybe [LIE Name], TcGblEnv)

        -- Complains if two distinct exports have same OccName
        -- Warns about identical exports.
        -- Complains about exports items not in scope

rnExports explicit_mod exports
          tcg_env@(TcGblEnv { tcg_mod     = this_mod,
                              tcg_rdr_env = rdr_env,
                              tcg_imports = imports })
 = unsetWOptM Opt_WarnWarningsDeprecations $
       -- Do not report deprecations arising from the export
       -- list, to avoid bleating about re-exporting a deprecated
       -- thing (especially via 'module Foo' export item)
   do   {
        -- If the module header is omitted altogether, then behave
        -- as if the user had written "module Main(main) where..."
        -- EXCEPT in interactive mode, when we behave as if he had
        -- written "module Main where ..."
        -- Reason: don't want to complain about 'main' not in scope
        --         in interactive mode
        ; dflags <- getDynFlags
        ; let real_exports
                 | explicit_mod = exports
                 | ghcLink dflags == LinkInMemory = Nothing
                 | otherwise
                          = Just (noLoc [noLoc (IEVar (noLoc main_RDR_Unqual))])
                        -- ToDo: the 'noLoc' here is unhelpful if 'main'
                        --       turns out to be out of scope

        ; (rn_exports, avails) <- exports_from_avail real_exports rdr_env imports this_mod
        ; traceRn (ppr avails)
        ; let final_avails = nubAvails avails    -- Combine families
              final_ns     = availsToNameSetWithSelectors final_avails

        ; traceRn (text "rnExports: Exports:" <+> ppr final_avails)

        ; let new_tcg_env =
                  (tcg_env { tcg_exports    = final_avails,
                             tcg_rn_exports = case tcg_rn_exports tcg_env of
                                                Nothing -> Nothing
                                                Just _  -> rn_exports,
                            tcg_dus = tcg_dus tcg_env `plusDU`
                                      usesOnly final_ns })
        ; failIfErrsM
        ; return (rn_exports, new_tcg_env) }

exports_from_avail :: Maybe (Located [LIE RdrName])
                         -- Nothing => no explicit export list
                   -> GlobalRdrEnv
                   -> ImportAvails
                   -> Module
                   -> RnM (Maybe [LIE Name], [AvailInfo])

exports_from_avail Nothing rdr_env _imports _this_mod
   -- The same as (module M) where M is the current module name,
   -- so that's how we handle it, except we also export the data family
   -- when a data instance is exported.
  = let avails = [ fix_faminst $ availFromGRE gre
                 | gre <- globalRdrEnvElts rdr_env
                 , isLocalGRE gre ]
    in return (Nothing, avails)
  where
    -- #11164: when we define a data instance
    -- but not data family, re-export the family
    -- Even though we don't check whether this is actually a data family
    -- only data families can locally define subordinate things (`ns` here)
    -- without locally defining (and instead importing) the parent (`n`)
    fix_faminst (AvailTC n ns flds)
      | not (n `elem` ns)
      = AvailTC n (n:ns) flds

    fix_faminst avail = avail


exports_from_avail (Just (L _ rdr_items)) rdr_env imports this_mod
  = do (ie_names, _, exports) <- foldlM do_litem emptyExportAccum rdr_items
       return (Just ie_names, exports)
  where
    do_litem :: ExportAccum -> LIE RdrName -> RnM ExportAccum
    do_litem acc lie = setSrcSpan (getLoc lie) (exports_from_item acc lie)

    -- Maps a parent to its in-scope children
    kids_env :: NameEnv [GlobalRdrElt]
    kids_env = mkChildEnv (globalRdrEnvElts rdr_env)


    imported_modules = [ imv_name imv
                       | xs <- moduleEnvElts $ imp_mods imports, imv <- xs ]

    exports_from_item :: ExportAccum -> LIE RdrName -> RnM ExportAccum
    exports_from_item acc@(ie_names, occs, exports)
                      (L loc (IEModuleContents (L lm mod)))
        | let earlier_mods = [ mod
                             | (L _ (IEModuleContents (L _ mod))) <- ie_names ]
        , mod `elem` earlier_mods    -- Duplicate export of M
        = do { warnIf (Reason Opt_WarnDuplicateExports) True
                      (dupModuleExport mod) ;
               return acc }

        | otherwise
        = do { let { exportValid = (mod `elem` imported_modules)
                                || (moduleName this_mod == mod)
                   ; gre_prs     = pickGREsModExp mod (globalRdrEnvElts rdr_env)
                   ; new_exports = map (availFromGRE . fst) gre_prs
                   ; names       = map (gre_name     . fst) gre_prs
                   ; all_gres    = foldr (\(gre1,gre2) gres -> gre1 : gre2 : gres) [] gre_prs
               }

             ; checkErr exportValid (moduleNotImported mod)
             ; warnIf (Reason Opt_WarnDodgyExports)
                      (exportValid && null gre_prs)
                      (nullModuleExport mod)

             ; traceRn (text "efa" <+> (ppr mod $$ ppr all_gres))
             ; addUsedGREs all_gres

             ; occs' <- check_occs (IEModuleContents (noLoc mod)) occs names
                      -- This check_occs not only finds conflicts
                      -- between this item and others, but also
                      -- internally within this item.  That is, if
                      -- 'M.x' is in scope in several ways, we'll have
                      -- several members of mod_avails with the same
                      -- OccName.
             ; traceRn (vcat [ text "export mod" <+> ppr mod
                             , ppr new_exports ])
             ; return (L loc (IEModuleContents (L lm mod)) : ie_names,
                       occs', new_exports ++ exports) }

    exports_from_item acc@(lie_names, occs, exports) (L loc ie)
        | isDoc ie
        = do new_ie <- lookup_doc_ie ie
             return (L loc new_ie : lie_names, occs, exports)

        | otherwise
        = do (new_ie, avail) <- lookup_ie ie
             if isUnboundName (ieName new_ie)
                  then return acc    -- Avoid error cascade
                  else do

                    occs' <- check_occs ie occs (availNames avail)

                    return (L loc new_ie : lie_names, occs', avail : exports)

    -------------
    lookup_ie :: IE RdrName -> RnM (IE Name, AvailInfo)
    lookup_ie (IEVar (L l rdr))
        = do (name, avail) <- lookupGreAvailRn rdr
             return (IEVar (L l name), avail)

    lookup_ie (IEThingAbs (L l rdr))
        = do (name, avail) <- lookupGreAvailRn rdr
             return (IEThingAbs (L l name), avail)

    lookup_ie ie@(IEThingAll n)
        = do
            (n, avail, flds) <- lookup_ie_all ie n
            let name = unLoc n
            return (IEThingAll n, AvailTC name (name:avail) flds)


    lookup_ie ie@(IEThingWith l wc sub_rdrs _)
        = do
            (lname, subs, avails, flds) <- lookup_ie_with l sub_rdrs
            (_, all_avail, all_flds) <-
              case wc of
                NoIEWildcard -> return (lname, [], [])
                IEWildcard _ -> lookup_ie_all ie l
            let name = unLoc lname
            return (IEThingWith lname wc subs (map noLoc (flds ++ all_flds)),
                    AvailTC name (name : avails ++ all_avail)
                                 (flds ++ all_flds))




    lookup_ie _ = panic "lookup_ie"    -- Other cases covered earlier

    lookup_ie_with :: Located RdrName -> [Located RdrName]
                   -> RnM (Located Name, [Located Name], [Name], [FieldLabel])
    lookup_ie_with (L l rdr) sub_rdrs
        = do name <- lookupGlobalOccRn rdr
             (non_flds, flds) <- lookupChildrenExport name sub_rdrs
             if isUnboundName name
                then return (L l name, [], [name], [])
                else return (L l name, non_flds
                            , map unLoc non_flds
                            , map unLoc flds)
    lookup_ie_all :: IE RdrName -> Located RdrName
                  -> RnM (Located Name, [Name], [FieldLabel])
    lookup_ie_all ie (L l rdr) =
          do name <- lookupGlobalOccRn rdr
             let gres = findChildren kids_env name
                 (non_flds, flds) = classifyGREs gres
             addUsedKids rdr gres
             warnDodgyExports <- woptM Opt_WarnDodgyExports
             when (null gres) $
                  if isTyConName name
                  then when warnDodgyExports $
                           addWarn (Reason Opt_WarnDodgyExports)
                                   (dodgyExportWarn name)
                  else -- This occurs when you export T(..), but
                       -- only import T abstractly, or T is a synonym.
                       addErr (exportItemErr ie)
             return (L l name, non_flds, flds)

    -------------
    lookup_doc_ie :: IE RdrName -> RnM (IE Name)
    lookup_doc_ie (IEGroup lev doc) = do rn_doc <- rnHsDoc doc
                                         return (IEGroup lev rn_doc)
    lookup_doc_ie (IEDoc doc)       = do rn_doc <- rnHsDoc doc
                                         return (IEDoc rn_doc)
    lookup_doc_ie (IEDocNamed str)  = return (IEDocNamed str)
    lookup_doc_ie _ = panic "lookup_doc_ie"    -- Other cases covered earlier

    -- In an export item M.T(A,B,C), we want to treat the uses of
    -- A,B,C as if they were M.A, M.B, M.C
    -- Happily pickGREs does just the right thing
    addUsedKids :: RdrName -> [GlobalRdrElt] -> RnM ()
    addUsedKids parent_rdr kid_gres = addUsedGREs (pickGREs parent_rdr kid_gres)

isDoc :: IE RdrName -> Bool
isDoc (IEDoc _)      = True
isDoc (IEDocNamed _) = True
isDoc (IEGroup _ _)  = True
isDoc _ = False

-- Renaming and typechecking of exports happens after everything else has
-- been typechecked.

{-
******************************************************************************
** Typechecking module exports
When it comes to pattern synonyms, in the renamer we have no way to check that
whether a pattern synonym should be allowed to be bundled or not so we allow
them to be bundled with any type or class. Here we then check that

1) Pattern synonyms are only bundled with types which are able to
   have data constructors. Datatypes, newtypes and data families.
2) Are the correct type, for example if P is a synonym
   then if we export Foo(P) then P should be an instance of Foo.

We also check for normal parent-child relationships here as well.

******************************************************************************
-}

tcExports :: Maybe [LIE Name]
          -> TcM ()
tcExports Nothing = return ()
tcExports (Just ies) = checkNoErrs $ mapM_ tc_export ies

tc_export :: LIE Name -> TcM ()
tc_export ie@(L _ (IEThingWith name _ names sels)) =
  addExportErrCtxt ie
    $ tc_export_with (unLoc name) (map unLoc names)
                                  (map unLoc sels)
tc_export _ = return ()

addExportErrCtxt :: LIE Name -> TcM a -> TcM a
addExportErrCtxt (L l ie) = setSrcSpan l . addErrCtxt exportCtxt
  where
    exportCtxt = text "In the export:" <+> ppr ie


-- Note: [Types of TyCon]
--
-- This check appears to be overlly complicated, Richard asked why it
-- is not simply just `isAlgTyCon`. The answer for this is that
-- a classTyCon is also an `AlgTyCon` which we explicitly want to disallow.
-- (It is either a newtype or data depending on the number of methods)
--
--
-- Note: [Typing Pattern Synonym Exports]
-- It proved quite a challenge to precisely specify which pattern synonyms
-- should be allowed to be bundled with which type constructors.
-- In the end it was decided to be quite liberal in what we allow. Below is
-- how Simon described the implementation.
--
-- "Personally I think we should Keep It Simple.  All this talk of
--  satisfiability makes me shiver.  I suggest this: allow T( P ) in all
--   situations except where `P`'s type is ''visibly incompatible'' with
--   `T`.
--
--    What does "visibly incompatible" mean?  `P` is visibly incompatible
--    with
--     `T` if
--       * `P`'s type is of form `... -> S t1 t2`
--       * `S` is a data/newtype constructor distinct from `T`
--
--  Nothing harmful happens if we allow `P` to be exported with
--  a type it can't possibly be useful for, but specifying a tighter
--  relationship is very awkward as you have discovered."
--
-- Note that this allows *any* pattern synonym to be bundled with any
-- datatype type constructor. For example, the following pattern `P` can be
-- bundled with any type.
--
-- ```
-- pattern P :: (A ~ f) => f
-- ```
--
-- So we provide basic type checking in order to help the user out, most
-- pattern synonyms are defined with definite type constructors, but don't
-- actually prevent a library author completely confusing their users if
-- they want to.

exportErrCtxt :: Outputable o => String -> o -> SDoc
exportErrCtxt herald exp =
  text "In the" <+> text (herald ++ ":") <+> ppr exp

tc_export_with :: Name  -- ^ Type constructor
               -> [Name] -- ^ A mixture of data constructors, pattern syonyms
                         -- , class methods and record selectors.
               -> [FieldLbl Name]
               -> TcM ()
tc_export_with n ns fls = do
  ty_con <- tcLookupTyCon n
  things <- mapM tcLookupGlobal ns
  let data_cons = [(c,  dataConTyCon c)
                        | AConLike (RealDataCon c) <- things ]
      ps        = [(psErr p,p) | AConLike (PatSynCon p) <- things]
      ps_sels   = [(selErr i,p)
                    | AnId i <- things
                    , isId i
                    , RecSelId {sel_tycon = RecSelPatSyn p} <- [idDetails i]]

  let actual_res_ty =
          mkTyConApp ty_con (mkTyVarTys (tyConTyVars ty_con))

  mapM_ (tc_one_dc_export_with ty_con) data_cons
  mapM_ (tc_flds ty_con)  (partitionFieldLabels fls)

  let pat_syns = ps ++ ps_sels

  -- See note [Types of TyCon]
  checkTc ( null pat_syns || isTyConWithSrcDataCons ty_con) assocClassErr
  mapM_ (tc_one_ps_export_with actual_res_ty ty_con ) pat_syns

  where
    psErr = exportErrCtxt "pattern synonym"
    selErr = exportErrCtxt "pattern synonym record selector"
    -- Partition based on source-level name
    partitionFieldLabels :: [FieldLbl Name] -> [(FastString, [Name])]
    partitionFieldLabels = map assemble
                         . groupWith flLabel
                         . sortWith flLabel
      where
        assemble :: [FieldLbl Name] -> (FastString, [Name])
        assemble [] = panic "partitionFieldLabels"
        assemble fls@(fl:_) = (flLabel fl, map flSelector fls)

    dcErrMsg :: Outputable a => TyCon -> String -> a -> [SDoc] -> SDoc
    dcErrMsg ty_con what_is thing parents =
            let capitalise [] = []
                capitalise (c:cs) = toUpper c : cs
            in
              text "The type constructor" <+> quotes (ppr ty_con)
                    <+> text "is not the parent of the" <+> text what_is
                    <+> quotes (ppr thing) <> char '.'
                    $$ text (capitalise what_is) <> text "s can only be exported with their parent type constructor."
                    $$ (case parents of
                          [] -> empty
                          [_] -> text "Parent:"
                          _  -> text "Parents:") <+> fsep (punctuate comma parents)

    -- This is only used for normal record field labels
    tc_flds :: TyCon -> (FastString, [Name]) -> TcM ()
    tc_flds ty_con (fs, flds) = do
      fldIds <- mapM tcLookupId flds
      traceTc "tc_flds" (ppr fldIds)
      let parents = [tc | i <- fldIds, RecSelId { sel_tycon = RecSelData tc }
                                        <- [idDetails i]]
      unless (any (ty_con ==) parents) $
        addErrTc (dcErrMsg ty_con "record selector" fs (map ppr parents))



    assocClassErr :: SDoc
    assocClassErr =
      text "Pattern synonyms can be bundled only with datatypes."

    -- Check whether a data constructor is exported with its parent.
    tc_one_dc_export_with :: Outputable a =>
                              TyCon -> (a, TyCon) -> TcM ()
    tc_one_dc_export_with ty_con (thing, tc) =
      unless (ty_con == tc)
        (addErrTc (dcErrMsg ty_con "data constructor" thing [ppr tc]))



    tc_one_ps_export_with :: TcTauType -- ^ TyCon type
                       -> TyCon       -- ^ Parent TyCon
                       -> (SDoc, PatSyn)   -- ^ Corresponding bundled PatSyn
                                           -- and pretty printed origin
                       -> TcM ()
    tc_one_ps_export_with actual_res_ty ty_con (errCtxt, pat_syn)
      = addErrCtxt errCtxt $
      let (_, _, _, _, _, res_ty) = patSynSig pat_syn
          mtycon = tcSplitTyConApp_maybe res_ty
          typeMismatchError :: SDoc
          typeMismatchError =
            text "Pattern synonyms can only be bundled with matching type constructors"
                $$ text "Couldn't match expected type of"
                <+> quotes (ppr actual_res_ty)
                <+> text "with actual type of"
                <+> quotes (ppr res_ty)
      in case mtycon of
            Nothing -> return ()
            Just (p_ty_con, _) ->
              -- See note [Typing Pattern Synonym Exports]
              unless (p_ty_con == ty_con)
                (addErrTc typeMismatchError)

check_occs :: IE RdrName -> ExportOccMap -> [Name] -> RnM ExportOccMap
check_occs ie occs names  -- 'names' are the entities specifed by 'ie'
  = foldlM check occs names
  where
    check occs name
      = case lookupOccEnv occs name_occ of
          Nothing -> return (extendOccEnv occs name_occ (name, ie))

          Just (name', ie')
            | name == name'   -- Duplicate export
            -- But we don't want to warn if the same thing is exported
            -- by two different module exports. See ticket #4478.
            -> do { warnIf (Reason Opt_WarnDuplicateExports)
                           (not (dupExport_ok name ie ie'))
                           (dupExportWarn name_occ ie ie')
                  ; return occs }

            | otherwise    -- Same occ name but different names: an error
            ->  do { global_env <- getGlobalRdrEnv ;
                     addErr (exportClashErr global_env name' name ie' ie) ;
                     return occs }
      where
        name_occ = nameOccName name


dupExport_ok :: Name -> IE RdrName -> IE RdrName -> Bool
-- The Name is exported by both IEs. Is that ok?
-- "No"  iff the name is mentioned explicitly in both IEs
--        or one of the IEs mentions the name *alone*
-- "Yes" otherwise
--
-- Examples of "no":  module M( f, f )
--                    module M( fmap, Functor(..) )
--                    module M( module Data.List, head )
--
-- Example of "yes"
--    module M( module A, module B ) where
--        import A( f )
--        import B( f )
--
-- Example of "yes" (Trac #2436)
--    module M( C(..), T(..) ) where
--         class C a where { data T a }
--         instance C Int where { data T Int = TInt }
--
-- Example of "yes" (Trac #2436)
--    module Foo ( T ) where
--      data family T a
--    module Bar ( T(..), module Foo ) where
--        import Foo
--        data instance T Int = TInt

dupExport_ok n ie1 ie2
  = not (  single ie1 || single ie2
        || (explicit_in ie1 && explicit_in ie2) )
  where
    explicit_in (IEModuleContents _) = False                -- module M
    explicit_in (IEThingAll r) = nameOccName n == rdrNameOcc (unLoc r)  -- T(..)
    explicit_in _              = True

    single (IEVar {})      = True
    single (IEThingAbs {}) = True
    single _               = False


dupModuleExport :: ModuleName -> SDoc
dupModuleExport mod
  = hsep [text "Duplicate",
          quotes (text "Module" <+> ppr mod),
          text "in export list"]

moduleNotImported :: ModuleName -> SDoc
moduleNotImported mod
  = text "The export item `module" <+> ppr mod <>
    text "' is not imported"

nullModuleExport :: ModuleName -> SDoc
nullModuleExport mod
  = text "The export item `module" <+> ppr mod <> ptext (sLit "' exports nothing")


dodgyExportWarn :: Name -> SDoc
dodgyExportWarn item = dodgyMsg (text "export") item


exportItemErr :: IE RdrName -> SDoc
exportItemErr export_item
  = sep [ text "The export item" <+> quotes (ppr export_item),
          text "attempts to export constructors or class methods that are not visible here" ]


dupExportWarn :: OccName -> IE RdrName -> IE RdrName -> SDoc
dupExportWarn occ_name ie1 ie2
  = hsep [quotes (ppr occ_name),
          text "is exported by", quotes (ppr ie1),
          text "and",            quotes (ppr ie2)]

exportClashErr :: GlobalRdrEnv -> Name -> Name -> IE RdrName -> IE RdrName
               -> MsgDoc
exportClashErr global_env name1 name2 ie1 ie2
  = vcat [ text "Conflicting exports for" <+> quotes (ppr occ) <> colon
         , ppr_export ie1' name1'
         , ppr_export ie2' name2' ]
  where
    occ = nameOccName name1
    ppr_export ie name = nest 3 (hang (quotes (ppr ie) <+> text "exports" <+>
                                       quotes (ppr name))
                                    2 (pprNameProvenance (get_gre name)))

    -- get_gre finds a GRE for the Name, so that we can show its provenance
    get_gre name
        = case lookupGRE_Name global_env name of
             Just gre -> gre
             Nothing  -> pprPanic "exportClashErr" (ppr name)
    get_loc name = greSrcSpan (get_gre name)
    (name1', ie1', name2', ie2') = if get_loc name1 < get_loc name2
                                   then (name1, ie1, name2, ie2)
                                   else (name2, ie2, name1, ie1)

-- This is a minefield. Three different things can appear in exports list.
-- 1. Record selectors
-- 2. Type constructors
-- 3. Data constructors
--
-- However, things get put into weird name spaces.
-- 1. Some type constructors are parsed as variables (-.->) for example.
-- 2. All data constructors are parsed as type constructors
-- 3. When there is ambiguity, we default type constructors to data
-- constructors and require the explicit `type` keyword for type
-- constructors.
--
--
-- Further to this madness, duplicate record fields complicate
-- things as we must find the FieldLabel rather than just the Name.
--
lookupChildrenExport :: Name -> [Located RdrName]
                     -> RnM ([Located Name], [Located FieldLabel])
lookupChildrenExport parent rdr_items =
  do
    let

        doOne :: Located RdrName
              -> RnM (Either (Located Name) [Located FieldLabel])
        doOne n = do

          let bareName = unLoc n
              lkup = lookupExportChild parent

          mname <- runMaybeT . asum . map (MaybeT . lkup) $
            [ (setRdrNameSpace bareName varName)  -- Record selector
            , (setRdrNameSpace bareName dataName) -- data constructor
            , (setRdrNameSpace bareName tcName)   -- type constructor
            ]

          -- Default to data constructors for slightly better error
          -- messages
          let unboundName :: RdrName
              unboundName = if rdrNameSpace bareName == varName
                                then bareName
                                else setRdrNameSpace bareName dataName


          name <- maybe (Left <$> reportUnboundName unboundName) return mname

          case name of
            Right fls -> return $ Right (map (L (getLoc n)) fls)
            Left name -> return $ Left (L (getLoc n) name)

    xs <- mapM doOne rdr_items
    return $ (fmap concat . partitionEithers) xs


classifyGREs :: [GlobalRdrElt] -> ([Name], [FieldLabel])
classifyGREs = partitionEithers . map classifyGRE

classifyGRE :: GlobalRdrElt -> Either Name FieldLabel
classifyGRE gre = case gre_par gre of
  FldParent _ Nothing -> Right (FieldLabel (occNameFS (nameOccName n)) False n)
  FldParent _ (Just lbl) -> Right (FieldLabel lbl True n)
  _                      -> Left  n
  where
    n = gre_name gre
