{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


Error-checking and other utilities for @deriving@ clauses or declarations.
-}

{-# LANGUAGE ImplicitParams #-}

module TcDerivUtils (
        DerivSpec(..), pprDerivSpec,
        DerivInstArgs(..), DerivInstArgsNoRep, DerivInstArgsWithRep,
        DataTypeInstArgs(..), DataTypeInstArgsNoRep,
        DataTypeInstArgsWithRep, derivInstArgsToTypes,
        DerivSpecMechanism(..), isDerivSpecStock,
        isDerivSpecNewtype, isDerivSpecAnyClass,
        DerivContext, DerivStatus(..),
        PredOrigin(..), ThetaOrigin(..), mkPredOrigin,
        mkThetaOrigin, mkThetaOriginFromPreds, substPredOrigin,
        checkSideConditions, hasStockDeriving, nonStdErr,
        canDeriveAnyClass,
        std_class_via_coercible, non_coercible_class,
        newDerivClsInst, extendLocalInstEnv
    ) where

import Bag
import BasicTypes
import Class
import DataCon
import DynFlags
import ErrUtils
import HscTypes (lookupFixity, mi_fix)
import HsSyn
import Inst
import InstEnv
import LoadIface (loadInterfaceForName)
import Module (getModule)
import Name
import Outputable
import PrelNames
import RdrName
import SrcLoc
import TcGenDeriv
import TcGenFunctor
import TcGenGenerics
import TcRnMonad
import TcType
import THNames (liftClassKey)
import TyCon
import Type
import Util
import VarSet

import qualified GHC.LanguageExtensions as LangExt
import ListSetOps (assocMaybe)

data DerivSpec theta = DS { ds_loc       :: SrcSpan
                          , ds_name      :: Name         -- DFun name
                          , ds_tvs       :: [TyVar]
                          , ds_theta     :: theta
                          , ds_cls       :: Class
                          , ds_tys       :: [Type]
                          , ds_overlap   :: Maybe OverlapMode
                          , ds_mechanism :: DerivSpecMechanism }
        -- This spec implies a dfun declaration of the form
        --       df :: forall tvs. theta => C tys
        -- The Name is the name for the DFun we'll build
        -- The tyvars bind all the variables in the theta

        -- ds_tys contains all of the type arguments to the class. For stock-
        -- and newtype-derived instances, the last type in ds_tys will always
        -- be a datatype application. For example,
        --
        --   newtype Foo a = Foo a
        --     deriving (C Int)
        --   ===>
        --   DS { ds_cls = C, ds_tys = [Int, Foo a] }
        --
        -- If the stock- or newtype-derived instance is for a data family, the
        -- head tycon in the last type in ds_tys is the *family* tycon, not the
        -- *representation* tycon. The representation tycon is stored in the
        -- dsm_head_tycon field of DerivSpecMechanism instead (the
        -- DerivSpecStock/DerivSpecNewtype constructors only). We do not store
        -- the representation tycon in DerivSpec as DeriveAnyClass is not
        -- guaranteed to have one.
        -- See Note [Unconventional anyclass-derived instances]

        -- the theta is either the given and final theta, in standalone deriving,
        -- or the not-yet-simplified list of constraints together with their origin

        -- ds_mechanism specifies the means by which GHC derives the instance.
        -- See Note [Deriving strategies] in TcDeriv

{-
Example:

     newtype instance T [a] = MkT (Tree a) deriving( C s )
==>
     axiom T [a] = :RTList a
     axiom :RTList a = Tree a

     DS { ds_tvs = [a,s], ds_cls = C, ds_tys = [s, T [a]]
        , ds_mechanism = DerivSpecNewtype (Tree a) }
-}

pprDerivSpec :: Outputable theta => DerivSpec theta -> SDoc
pprDerivSpec (DS { ds_loc = l, ds_name = n, ds_tvs = tvs, ds_cls = c,
                   ds_tys = tys, ds_theta = rhs, ds_mechanism = mech })
  = hang (text "DerivSpec")
       2 (vcat [ text "ds_loc       =" <+> ppr l
               , text "ds_name      =" <+> ppr n
               , text "ds_tvs       =" <+> ppr tvs
               , text "ds_cls       =" <+> ppr c
               , text "ds_tys       =" <+> ppr tys
               , text "ds_theta     =" <+> ppr rhs
               , text "ds_mechanism =" <+> ppr mech ])

instance Outputable theta => Outputable (DerivSpec theta) where
  ppr = pprDerivSpec

-- | A representation of a class's argument types in a derived instance.
--
-- This is quite similar in structure to 'DerivSpecMechanism', but this data
-- type is used before we know with certainty which deriving strategy we are
-- going to commit to.

-- See Note [Unconventional anyclass-derived instances]
data DerivInstArgs a b
  = ConventionalInstArgs (DataTypeInstArgs a b)
    -- ^ A derived instance where the last argument type is a data type
    -- applied to some number of other types.
    --
    -- All stock- and newtype-derived instances must be of this form, and
    -- 95% of anyclass-derived instances are also of this form (but see also
    -- 'UnconventionalInstArgs' for the 5% that aren't).

  | UnconventionalInstArgs [Type]
    -- ^ A derived instance that does not decompose into a data type
    -- application (as in 'DerivInstArgs'). This can sometimes happen with
    -- @DeriveAnyClass@. Some examples:
    --
    -- @
    -- class C
    -- deriving anyclass instance C -- No type arguments to C
    --
    -- class Anything a
    -- deriving anyclass instance Anything a -- a is not a data type
    -- @
    --
    -- The only argument to 'UnconventionalInstArgs' are the list of type
    -- arguments to the derived class.

instance (Outputable a, Outputable b) => Outputable (DerivInstArgs a b) where
  ppr (ConventionalInstArgs args) = hang (text "ConventionalInstArgs")
                                       2 (parens $ ppr args)
  ppr (UnconventionalInstArgs tys) = text "UnconventionalInstArgs" <+> ppr tys

-- | A 'DerivInstArgs' value that is used before we know what the
-- representation 'TyCon' is.
type DerivInstArgsNoRep = DerivInstArgs () ()
-- | A 'DerivInstArgs' value where we know what the representation 'TyCon' is,
-- and what types it is being applied to.
type DerivInstArgsWithRep = DerivInstArgs TyCon [Type]

-- | Extract the class argument types from a 'DerivInstArgs' value.
derivInstArgsToTypes :: DerivInstArgs a b -> [Type]
derivInstArgsToTypes (ConventionalInstArgs inst_args)
  | DataTypeInstArgs { dtia_class_tys = cls_tys, dtia_head_tycon = tc
                     , dtia_head_tycon_args = tc_args } <- inst_args
  = cls_tys ++ [mkTyConApp tc tc_args]
derivInstArgsToTypes (UnconventionalInstArgs tys) = tys

-- | A representation of a class's argument types in a derived instance,
-- where the last argument type is a data type applied to some number of other
-- types, e.g.,
--
-- @
-- deriving instance C Int String (Foo Char Bool)
-- @
data DataTypeInstArgs a b = DataTypeInstArgs
    { dtia_class_tys :: [Type]
      -- ^ All type arguments to the derived class except the last one. In the
      -- above example, @dtia_class_tys = [Int, String]@.
    , dtia_head_tycon :: TyCon
      -- ^ The 'TyCon' at the head of the last type argument to the derived
      -- class. In the above example, @dtia_head_tycon = Foo@.
      --
      -- In the case of data families, this is the family 'TyCon', not the
      -- representation 'TyCon'. The representation 'TyCon' is located in
      -- 'dtia_head_rep_tycon' (if it is known).
    , dtia_head_tycon_args :: [Type]
      -- ^ The types to which @dtia_head_tycon@ is applied in the last type
      -- argument to the derived class. In the above example,
      -- @dtia_head_tycon_args = [Char, Bool]@.
      --
      -- In the case of data families, these are the arguments to the family
      -- 'TyCon', not the representation 'TyCon'. The arguments to the
      -- representation 'TyCon' are located in 'dtia_head_rep_tycon_args'
      -- (if they are known).
    , dtia_head_rep_tycon :: a
      -- ^ The representation 'TyCon' of 'dtia_head_tycon' (if it is known).
      -- This will only ever be different from 'dtia_head_tycon' in the case
      -- of data families.
    , dtia_head_rep_tycon_args :: b
      -- ^ The type arguments to 'dtia_head_rep_tycon' (if they are known).
      -- These will only ever be different from 'dtia_head_tycon_args' in the
      -- case of data families.
    }

instance (Outputable a, Outputable b)
    => Outputable (DataTypeInstArgs a b) where
  ppr (DataTypeInstArgs { dtia_class_tys = cls_tys, dtia_head_tycon = tc
                        , dtia_head_tycon_args = tc_args
                        , dtia_head_rep_tycon = rep_tc
                        , dtia_head_rep_tycon_args = rep_tc_args })
    = hang (text "DataTypeInstArgs")
         2 (vcat [ text "dtia_class_tys          " <+> ppr cls_tys
                 , text "dtia_head_tycon         " <+> ppr tc
                 , text "dtia_head_tycon_args    " <+> ppr tc_args
                 , text "dtia_head_rep_tycon     " <+> ppr rep_tc
                 , text "dtia_head_rep_tycon_args" <+> ppr rep_tc_args ])

-- | A 'DataTypeInstArgs' value that is used before we know what the
-- representation 'TyCon' is.
type DataTypeInstArgsNoRep   = DataTypeInstArgs () ()
-- | A 'DataTypeInstArgs' value where we know what the representation 'TyCon'
-- is, and what types it is being applied to.
type DataTypeInstArgsWithRep = DataTypeInstArgs TyCon [Type]

-- | What action to take in order to derive a class instance.

-- See Note [Deriving strategies] in TcDeriv
data DerivSpecMechanism
  = -- | "Standard" classes
    DerivSpecStock
    { dsm_inst_args :: DataTypeInstArgsWithRep
      -- ^ The arguments to the derived class in the instance head.
    , dsm_gen_fn :: SrcSpan -> TyCon -> [Type]
                 -> TcM (LHsBinds RdrName, BagDerivStuff)
      -- ^ The function which generates stock-derived method bindings and other
      -- auxiliary definitions for a given data type 'TyCon' and the arguments
      -- to which it is applied.

      -- NB: The TyCon argument to dsm_gen_fn will always be contained in
      -- dsm_inst_args, We keep this TyCon separate because it is
      -- useful to inspect its value in various places
      -- (e.g., validity checking).
    }

  | -- | @-XGeneralizedNewtypeDeriving@
    DerivSpecNewtype
    { dsm_inst_args :: DataTypeInstArgsWithRep
      -- ^ The arguments to the derived class in the instance head.
    , dsm_rep_ty :: Type
      -- ^ The newtype rep type
    }

  | DerivSpecAnyClass -- | @-XDeriveAnyClass@

isDerivSpecStock, isDerivSpecNewtype, isDerivSpecAnyClass
  :: DerivSpecMechanism -> Bool
isDerivSpecStock (DerivSpecStock{}) = True
isDerivSpecStock _                  = False

isDerivSpecNewtype (DerivSpecNewtype{}) = True
isDerivSpecNewtype _                    = False

isDerivSpecAnyClass (DerivSpecAnyClass{}) = True
isDerivSpecAnyClass _                     = False

-- A DerivSpecMechanism can be losslessly converted to a DerivStrategy.
mechanismToStrategy :: DerivSpecMechanism -> DerivStrategy
mechanismToStrategy (DerivSpecStock{})    = StockStrategy
mechanismToStrategy (DerivSpecNewtype{})  = NewtypeStrategy
mechanismToStrategy (DerivSpecAnyClass{}) = AnyclassStrategy

instance Outputable DerivSpecMechanism where
  ppr = ppr . mechanismToStrategy

type DerivContext = Maybe ThetaType
   -- Nothing    <=> Vanilla deriving; infer the context of the instance decl
   -- Just theta <=> Standalone deriving: context supplied by programmer

data DerivStatus = CanDerive DataTypeInstArgsWithRep -- Stock class, can derive
                 | DerivableClassError SDoc  -- Stock class, but can't do it
                 | DerivableViaInstance      -- See Note [Deriving any class]
                 | NonDerivableClass SDoc    -- Non-stock class

-- A stock class is one either defined in the Haskell report or for which GHC
-- otherwise knows how to generate code for (possibly requiring the use of a
-- language extension), such as Eq, Ord, Ix, Data, Generic, etc.

-- | A 'PredType' annotated with the origin of the constraint 'CtOrigin',
-- and whether or the constraint deals in types or kinds.
data PredOrigin = PredOrigin PredType CtOrigin TypeOrKind

-- | A list of wanted 'PredOrigin' constraints ('to_wanted_origins') alongside
-- any corresponding given constraints ('to_givens') and locally quantified
-- type variables ('to_tvs').
--
-- In most cases, 'to_givens' will be empty, as most deriving mechanisms (e.g.,
-- stock and newtype deriving) do not require given constraints. The exception
-- is @DeriveAnyClass@, which can involve given constraints. For example,
-- if you tried to derive an instance for the following class using
-- @DeriveAnyClass@:
--
-- @
-- class Foo a where
--   bar :: a -> b -> String
--   default bar :: (Show a, Ix b) => a -> b -> String
--   bar = show
--
--   baz :: Eq a => a -> a -> Bool
--   default baz :: Ord a => a -> a -> Bool
--   baz x y = compare x y == EQ
-- @
--
-- Then it would generate two 'ThetaOrigin's, one for each method:
--
-- @
-- [ ThetaOrigin { to_tvs            = [b]
--               , to_givens         = []
--               , to_wanted_origins = [Show a, Ix b] }
-- , ThetaOrigin { to_tvs            = []
--               , to_givens         = [Eq a]
--               , to_wanted_origins = [Ord a] }
-- ]
-- @
data ThetaOrigin
  = ThetaOrigin { to_tvs            :: [TyVar]
                , to_givens         :: ThetaType
                , to_wanted_origins :: [PredOrigin] }

instance Outputable PredOrigin where
  ppr (PredOrigin ty _ _) = ppr ty -- The origin is not so interesting when debugging

instance Outputable ThetaOrigin where
  ppr (ThetaOrigin { to_tvs = tvs
                   , to_givens = givens
                   , to_wanted_origins = wanted_origins })
    = hang (text "ThetaOrigin")
         2 (vcat [ text "to_tvs            =" <+> ppr tvs
                 , text "to_givens         =" <+> ppr givens
                 , text "to_wanted_origins =" <+> ppr wanted_origins ])

mkPredOrigin :: CtOrigin -> TypeOrKind -> PredType -> PredOrigin
mkPredOrigin origin t_or_k pred = PredOrigin pred origin t_or_k

mkThetaOrigin :: CtOrigin -> TypeOrKind -> [TyVar] -> ThetaType -> ThetaType
              -> ThetaOrigin
mkThetaOrigin origin t_or_k tvs givens
  = ThetaOrigin tvs givens . map (mkPredOrigin origin t_or_k)

-- A common case where the ThetaOrigin only contains wanted constraints, with
-- no givens or locally scoped type variables.
mkThetaOriginFromPreds :: [PredOrigin] -> ThetaOrigin
mkThetaOriginFromPreds = ThetaOrigin [] []

substPredOrigin :: HasCallStack => TCvSubst -> PredOrigin -> PredOrigin
substPredOrigin subst (PredOrigin pred origin t_or_k)
  = PredOrigin (substTy subst pred) origin t_or_k

{-
************************************************************************
*                                                                      *
                Class deriving diagnostics
*                                                                      *
************************************************************************

Only certain blessed classes can be used in a deriving clause (without the
assistance of GeneralizedNewtypeDeriving or DeriveAnyClass). These classes
are listed below in the definition of hasStockDeriving. The sideConditions
function determines the criteria that needs to be met in order for a particular
class to be able to be derived successfully.

A class might be able to be used in a deriving clause if -XDeriveAnyClass
is willing to support it. The canDeriveAnyClass function checks if this is the
case.
-}

hasStockDeriving :: Class
                   -> Maybe (SrcSpan
                             -> TyCon
                             -> [Type]
                             -> TcM (LHsBinds RdrName, BagDerivStuff))
hasStockDeriving clas
  = assocMaybe gen_list (getUnique clas)
  where
    gen_list :: [(Unique, SrcSpan
                          -> TyCon
                          -> [Type]
                          -> TcM (LHsBinds RdrName, BagDerivStuff))]
    gen_list = [ (eqClassKey,          simpleM gen_Eq_binds)
               , (ordClassKey,         simpleM gen_Ord_binds)
               , (enumClassKey,        simpleM gen_Enum_binds)
               , (boundedClassKey,     simple gen_Bounded_binds)
               , (ixClassKey,          simpleM gen_Ix_binds)
               , (showClassKey,        with_fix_env gen_Show_binds)
               , (readClassKey,        with_fix_env gen_Read_binds)
               , (dataClassKey,        simpleM gen_Data_binds)
               , (functorClassKey,     simple gen_Functor_binds)
               , (foldableClassKey,    simple gen_Foldable_binds)
               , (traversableClassKey, simple gen_Traversable_binds)
               , (liftClassKey,        simple gen_Lift_binds)
               , (genClassKey,         generic (gen_Generic_binds Gen0))
               , (gen1ClassKey,        generic (gen_Generic_binds Gen1)) ]

    simple gen_fn loc tc _
      = return (gen_fn loc tc)

    simpleM gen_fn loc tc _
      = gen_fn loc tc

    with_fix_env gen_fn loc tc _
      = do { fix_env <- getDataConFixityFun tc
           ; return (gen_fn fix_env loc tc) }

    generic gen_fn _ tc inst_tys
      = do { (binds, faminst) <- gen_fn tc inst_tys
           ; return (binds, unitBag (DerivFamInst faminst)) }

getDataConFixityFun :: TyCon -> TcM (Name -> Fixity)
-- If the TyCon is locally defined, we want the local fixity env;
-- but if it is imported (which happens for standalone deriving)
-- we need to get the fixity env from the interface file
-- c.f. RnEnv.lookupFixity, and Trac #9830
getDataConFixityFun tc
  = do { this_mod <- getModule
       ; if nameIsLocalOrFrom this_mod name
         then do { fix_env <- getFixityEnv
                 ; return (lookupFixity fix_env) }
         else do { iface <- loadInterfaceForName doc name
                            -- Should already be loaded!
                 ; return (mi_fix iface . nameOccName) } }
  where
    name = tyConName tc
    doc = text "Data con fixities for" <+> ppr name

------------------------------------------------------------------
-- Check side conditions that dis-allow derivability for particular classes
-- This is *apart* from the newtype-deriving mechanism
--
-- Here we get the representation tycon in case of family instances as it has
-- the data constructors - but we need to be careful to fall back to the
-- family tycon (with indexes) in error messages.

checkSideConditions :: DynFlags -> DerivContext -> Class
                    -> DerivInstArgsWithRep
                    -> DerivStatus
checkSideConditions dflags mtheta cls deriv_inst_rep_args
  | Just cond <- sideConditions mtheta cls
  , ConventionalInstArgs
      inst_args@(DataTypeInstArgs { dtia_class_tys      = cls_tys
                                  , dtia_head_tycon     = tc
                                  , dtia_head_rep_tycon = rep_tc })
      <- deriv_inst_rep_args
    -- NB: pass the *representation* tycon
  = case (cond dflags tc rep_tc) of
        NotValid err -> DerivableClassError err  -- Class-specific error
        IsValid  | null (filterOutInvisibleTypes (classTyCon cls) cls_tys)
                   -> CanDerive inst_args
                   -- All stock derivable classes are unary in the sense that
                   -- there should be not types in cls_tys (i.e., no type args
                   -- other than last). Note that cls_types can contain
                   -- invisible types as well (e.g., for Generic1, which is
                   -- poly-kinded), so make sure those are not counted.
                 | otherwise -> DerivableClassError (classArgsErr cls cls_tys)
                   -- e.g. deriving( Eq s )

    -- DeriveAnyClass does not work, and furthermore, we are trying to derive
    -- an instance for a class itself, which warrants a special error message.
    -- See Note [Deriving instances for classes themselves]
  | NotValid{} <- can_dac
  , ConventionalInstArgs
      (DataTypeInstArgs { dtia_head_tycon     = tc
                        , dtia_head_rep_tycon = rep_tc }) <- deriv_inst_rep_args
  , isClassTyCon rep_tc
  = NonDerivableClass $
    quotes (ppr tc) <+> text "is a type class,"
                    <+> text "and can only have a derived instance"
                    $+$ text "if DeriveAnyClass is enabled"

    -- DeriveAnyClass does not work
  | NotValid err <- can_dac
  = NonDerivableClass (nonStdErr cls $$ err)

  | otherwise
  = DerivableViaInstance   -- DeriveAnyClass should work
 where
  can_dac = canDeriveAnyClass dflags

classArgsErr :: Class -> [Type] -> SDoc
classArgsErr cls cls_tys = quotes (ppr (mkClassPred cls cls_tys)) <+> text "is not a class"

nonStdErr :: Class -> SDoc
nonStdErr cls =
      quotes (ppr cls)
  <+> text "is not a stock derivable class (Eq, Show, etc.)"

-- Side conditions (whether the datatype must have at least one constructor,
-- required language extensions, etc.) for using GHC's stock deriving
-- mechanism on certain classes (as opposed to classes that require
-- GeneralizedNewtypeDeriving or DeriveAnyClass). Returns Nothing for a
-- class for which stock deriving isn't possible.
sideConditions :: DerivContext -> Class -> Maybe Condition
sideConditions mtheta cls
  | cls_key == eqClassKey          = Just (cond_std `andCond` cond_args cls)
  | cls_key == ordClassKey         = Just (cond_std `andCond` cond_args cls)
  | cls_key == showClassKey        = Just (cond_std `andCond` cond_args cls)
  | cls_key == readClassKey        = Just (cond_std `andCond` cond_args cls)
  | cls_key == enumClassKey        = Just (cond_std `andCond` cond_isEnumeration)
  | cls_key == ixClassKey          = Just (cond_std `andCond` cond_enumOrProduct cls)
  | cls_key == boundedClassKey     = Just (cond_std `andCond` cond_enumOrProduct cls)
  | cls_key == dataClassKey        = Just (checkFlag LangExt.DeriveDataTypeable `andCond`
                                           cond_std `andCond`
                                           cond_args cls)
  | cls_key == functorClassKey     = Just (checkFlag LangExt.DeriveFunctor `andCond`
                                           cond_vanilla `andCond`
                                           cond_functorOK True False)
  | cls_key == foldableClassKey    = Just (checkFlag LangExt.DeriveFoldable `andCond`
                                           cond_vanilla `andCond`
                                           cond_functorOK False True)
                                           -- Functor/Fold/Trav works ok
                                           -- for rank-n types
  | cls_key == traversableClassKey = Just (checkFlag LangExt.DeriveTraversable `andCond`
                                           cond_vanilla `andCond`
                                           cond_functorOK False False)
  | cls_key == genClassKey         = Just (checkFlag LangExt.DeriveGeneric `andCond`
                                           cond_vanilla `andCond`
                                           cond_RepresentableOk)
  | cls_key == gen1ClassKey        = Just (checkFlag LangExt.DeriveGeneric `andCond`
                                           cond_vanilla `andCond`
                                           cond_Representable1Ok)
  | cls_key == liftClassKey        = Just (checkFlag LangExt.DeriveLift `andCond`
                                           cond_vanilla `andCond`
                                           cond_args cls)
  | otherwise                      = Nothing
  where
    cls_key = getUnique cls
    cond_std     = cond_stdOK mtheta False  -- Vanilla data constructors, at least one,
                                            --    and monotype arguments
    cond_vanilla = cond_stdOK mtheta True   -- Vanilla data constructors but
                                            --   allow no data cons or polytype arguments

canDeriveAnyClass :: DynFlags -> Validity
-- IsValid: we can (try to) derive it via an empty instance declaration
-- NotValid s:  we can't, reason s
canDeriveAnyClass dflags
  | not (xopt LangExt.DeriveAnyClass dflags)
  = NotValid (text "Try enabling DeriveAnyClass")
  | otherwise
  = IsValid   -- OK!

type Condition  = DynFlags

               -> TyCon    -- ^ The data type's 'TyCon'. For data families,
                           -- this is the family 'TyCon'.

               -> TyCon    -- ^ For data families, this is the representation
                           -- 'TyCon'. Otherwise, this is the same as the other
                           -- 'TyCon' argument.

               -> Validity -- ^ 'IsValid' if deriving an instance for this
                           -- 'TyCon' is possible. Otherwise, it's
                           -- @'NotValid' err@, where @err@ explains what went
                           -- wrong.

orCond :: Condition -> Condition -> Condition
orCond c1 c2 dflags tc rep_tc
  = case (c1 dflags tc rep_tc, c2 dflags tc rep_tc) of
     (IsValid,    _)          -> IsValid    -- c1 succeeds
     (_,          IsValid)    -> IsValid    -- c21 succeeds
     (NotValid x, NotValid y) -> NotValid (x $$ text "  or" $$ y)
                                            -- Both fail

andCond :: Condition -> Condition -> Condition
andCond c1 c2 dflags tc rep_tc
  = c1 dflags tc rep_tc `andValid` c2 dflags tc rep_tc

cond_stdOK :: DerivContext -- Says whether this is standalone deriving or not;
                           --     if standalone, we just say "yes, go for it"
           -> Bool         -- True <=> permissive: allow higher rank
                           --          args and no data constructors
           -> Condition
cond_stdOK _ _ _ tc _
  | not (isAlgTyCon tc) && not (isDataFamilyTyCon tc)
    -- Complain about functions, primitive types, etc.
  = NotValid $ text "The last argument of the instance must be a"
           <+> text "data or newtype application"
cond_stdOK (Just _) _ _ _ _
  = IsValid     -- Don't check these conservative conditions for
                -- standalone deriving; just generate the code
                -- and let the typechecker handle the result
cond_stdOK Nothing permissive _ _ rep_tc
  | null data_cons
  , not permissive      = NotValid (no_cons_why rep_tc $$ suggestion)
  | not (null con_whys) = NotValid (vcat con_whys $$ suggestion)
  | otherwise           = IsValid
  where
    suggestion = text "Possible fix: use a standalone deriving declaration instead"
    data_cons  = tyConDataCons rep_tc
    con_whys   = getInvalids (map check_con data_cons)

    check_con :: DataCon -> Validity
    check_con con
      | not (null eq_spec)
      = bad "is a GADT"
      | not (null ex_tvs)
      = bad "has existential type variables in its type"
      | not (null theta)
      = bad "has constraints in its type"
      | not (permissive || all isTauTy (dataConOrigArgTys con))
      = bad "has a higher-rank type"
      | otherwise
      = IsValid
      where
        (_, ex_tvs, eq_spec, theta, _, _) = dataConFullSig con
        bad msg = NotValid (badCon con (text msg))

no_cons_why :: TyCon -> SDoc
no_cons_why rep_tc = quotes (pprSourceTyCon rep_tc) <+>
                     text "must have at least one data constructor"

cond_RepresentableOk :: Condition
cond_RepresentableOk _ _ rep_tc = canDoGenerics rep_tc

cond_Representable1Ok :: Condition
cond_Representable1Ok _ _ rep_tc = canDoGenerics1 rep_tc

cond_enumOrProduct :: Class -> Condition
cond_enumOrProduct cls = cond_isEnumeration `orCond`
                         (cond_isProduct `andCond` cond_args cls)

cond_args :: Class -> Condition
-- For some classes (eg Eq, Ord) we allow unlifted arg types
-- by generating specialised code.  For others (eg Data) we don't.
cond_args cls _ _ rep_tc
  = case bad_args of
      []     -> IsValid
      (ty:_) -> NotValid (hang (text "Don't know how to derive" <+> quotes (ppr cls))
                             2 (text "for type" <+> quotes (ppr ty)))
  where
    bad_args = [ arg_ty | con <- tyConDataCons rep_tc
                        , arg_ty <- dataConOrigArgTys con
                        , isUnliftedType arg_ty
                        , not (ok_ty arg_ty) ]

    cls_key = classKey cls
    ok_ty arg_ty
     | cls_key == eqClassKey   = check_in arg_ty ordOpTbl
     | cls_key == ordClassKey  = check_in arg_ty ordOpTbl
     | cls_key == showClassKey = check_in arg_ty boxConTbl
     | cls_key == liftClassKey = check_in arg_ty litConTbl
     | otherwise               = False    -- Read, Ix etc

    check_in :: Type -> [(Type,a)] -> Bool
    check_in arg_ty tbl = any (eqType arg_ty . fst) tbl


cond_isEnumeration :: Condition
cond_isEnumeration _ _ rep_tc
  | isEnumerationTyCon rep_tc = IsValid
  | otherwise                 = NotValid why
  where
    why = sep [ quotes (pprSourceTyCon rep_tc) <+>
                  text "must be an enumeration type"
              , text "(an enumeration consists of one or more nullary, non-GADT constructors)" ]
                  -- See Note [Enumeration types] in TyCon

cond_isProduct :: Condition
cond_isProduct _ _ rep_tc
  | isProductTyCon rep_tc = IsValid
  | otherwise             = NotValid why
  where
    why = quotes (pprSourceTyCon rep_tc) <+>
          text "must have precisely one constructor"

cond_functorOK :: Bool -> Bool -> Condition
-- OK for Functor/Foldable/Traversable class
-- Currently: (a) at least one argument
--            (b) don't use argument contravariantly
--            (c) don't use argument in the wrong place, e.g. data T a = T (X a a)
--            (d) optionally: don't use function types
--            (e) no "stupid context" on data type
cond_functorOK allowFunctions allowExQuantifiedLastTyVar _ _ rep_tc
  | null tc_tvs
  = NotValid (text "Data type" <+> quotes (ppr rep_tc)
              <+> text "must have some type parameters")

  | not (null bad_stupid_theta)
  = NotValid (text "Data type" <+> quotes (ppr rep_tc)
              <+> text "must not have a class context:" <+> pprTheta bad_stupid_theta)

  | otherwise
  = allValid (map check_con data_cons)
  where
    tc_tvs            = tyConTyVars rep_tc
    Just (_, last_tv) = snocView tc_tvs
    bad_stupid_theta  = filter is_bad (tyConStupidTheta rep_tc)
    is_bad pred       = last_tv `elemVarSet` tyCoVarsOfType pred

    data_cons = tyConDataCons rep_tc
    check_con con = allValid (check_universal con : foldDataConArgs (ft_check con) con)

    check_universal :: DataCon -> Validity
    check_universal con
      | allowExQuantifiedLastTyVar
      = IsValid -- See Note [DeriveFoldable with ExistentialQuantification]
                -- in TcGenFunctor
      | Just tv <- getTyVar_maybe (last (tyConAppArgs (dataConOrigResTy con)))
      , tv `elem` dataConUnivTyVars con
      , not (tv `elemVarSet` tyCoVarsOfTypes (dataConTheta con))
      = IsValid   -- See Note [Check that the type variable is truly universal]
      | otherwise
      = NotValid (badCon con existential)

    ft_check :: DataCon -> FFoldType Validity
    ft_check con = FT { ft_triv = IsValid, ft_var = IsValid
                      , ft_co_var = NotValid (badCon con covariant)
                      , ft_fun = \x y -> if allowFunctions then x `andValid` y
                                                           else NotValid (badCon con functions)
                      , ft_tup = \_ xs  -> allValid xs
                      , ft_ty_app = \_ x   -> x
                      , ft_bad_app = NotValid (badCon con wrong_arg)
                      , ft_forall = \_ x   -> x }

    existential = text "must be truly polymorphic in the last argument of the data type"
    covariant   = text "must not use the type variable in a function argument"
    functions   = text "must not contain function types"
    wrong_arg   = text "must use the type variable only as the last argument of a data type"

checkFlag :: LangExt.Extension -> Condition
checkFlag flag dflags _ _
  | xopt flag dflags = IsValid
  | otherwise        = NotValid why
  where
    why = text "You need " <> text flag_str
          <+> text "to derive an instance for this class"
    flag_str = case [ flagSpecName f | f <- xFlags , flagSpecFlag f == flag ] of
                 [s]   -> s
                 other -> pprPanic "checkFlag" (ppr other)

std_class_via_coercible :: Class -> Bool
-- These standard classes can be derived for a newtype
-- using the coercible trick *even if no -XGeneralizedNewtypeDeriving
-- because giving so gives the same results as generating the boilerplate
std_class_via_coercible clas
  = classKey clas `elem` [eqClassKey, ordClassKey, ixClassKey, boundedClassKey]
        -- Not Read/Show because they respect the type
        -- Not Enum, because newtypes are never in Enum


non_coercible_class :: Class -> Bool
-- *Never* derive Read, Show, Typeable, Data, Generic, Generic1, Lift
-- by Coercible, even with -XGeneralizedNewtypeDeriving
-- Also, avoid Traversable, as the Coercible-derived instance and the "normal"-derived
-- instance behave differently if there's a non-lawful Applicative out there.
-- Besides, with roles, Coercible-deriving Traversable is ill-roled.
non_coercible_class cls
  = classKey cls `elem` ([ readClassKey, showClassKey, dataClassKey
                         , genClassKey, gen1ClassKey, typeableClassKey
                         , traversableClassKey, liftClassKey ])

badCon :: DataCon -> SDoc -> SDoc
badCon con msg = text "Constructor" <+> quotes (ppr con) <+> msg

------------------------------------------------------------------

newDerivClsInst :: ThetaType -> DerivSpec theta -> TcM ClsInst
newDerivClsInst theta (DS { ds_name = dfun_name, ds_overlap = overlap_mode
                          , ds_tvs = tvs, ds_cls = clas, ds_tys = tys })
  = newClsInst overlap_mode dfun_name tvs theta clas tys

extendLocalInstEnv :: [ClsInst] -> TcM a -> TcM a
-- Add new locally-defined instances; don't bother to check
-- for functional dependency errors -- that'll happen in TcInstDcls
extendLocalInstEnv dfuns thing_inside
 = do { env <- getGblEnv
      ; let  inst_env' = extendInstEnvList (tcg_inst_env env) dfuns
             env'      = env { tcg_inst_env = inst_env' }
      ; setGblEnv env' thing_inside }

{-
Note [Deriving any class]
~~~~~~~~~~~~~~~~~~~~~~~~~
Classic uses of a deriving clause, or a standalone-deriving declaration, are
for:
  * a stock class like Eq or Show, for which GHC knows how to generate
    the instance code
  * a newtype, via the mechanism enabled by GeneralizedNewtypeDeriving

The DeriveAnyClass extension adds a third way to derive instances, based on
empty instance declarations.

The canonical use case is in combination with GHC.Generics and default method
signatures. These allow us to have instance declarations being empty, but still
useful, e.g.

  data T a = ...blah..blah... deriving( Generic )
  instance C a => C (T a)  -- No 'where' clause

where C is some "random" user-defined class.

This boilerplate code can be replaced by the more compact

  data T a = ...blah..blah... deriving( Generic, C )

if DeriveAnyClass is enabled.

This is not restricted to Generics; any class can be derived, simply giving
rise to an empty instance.

Unfortunately, it is not clear how to determine the context (when using a
deriving clause; in standalone deriving, the user provides the context).
GHC uses the same heuristic for figuring out the class context that it uses for
Eq in the case of *-kinded classes, and for Functor in the case of
* -> *-kinded classes. That may not be optimal or even wrong. But in such
cases, standalone deriving can still be used.

Note [Check that the type variable is truly universal]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For Functor and Traversable instances, we must check that the *last argument*
of the type constructor is used truly universally quantified.  Example

   data T a b where
     T1 :: a -> b -> T a b      -- Fine! Vanilla H-98
     T2 :: b -> c -> T a b      -- Fine! Existential c, but we can still map over 'b'
     T3 :: b -> T Int b         -- Fine! Constraint 'a', but 'b' is still polymorphic
     T4 :: Ord b => b -> T a b  -- No!  'b' is constrained
     T5 :: b -> T b b           -- No!  'b' is constrained
     T6 :: T a (b,b)            -- No!  'b' is constrained

Notice that only the first of these constructors is vanilla H-98. We only
need to take care about the last argument (b in this case).  See Trac #8678.
Eg. for T1-T3 we can write

     fmap f (T1 a b) = T1 a (f b)
     fmap f (T2 b c) = T2 (f b) c
     fmap f (T3 x)   = T3 (f x)

We need not perform these checks for Foldable instances, however, since
functions in Foldable can only consume existentially quantified type variables,
rather than produce them (as is the case in Functor and Traversable functions.)
As a result, T can have a derived Foldable instance:

    foldr f z (T1 a b) = f b z
    foldr f z (T2 b c) = f b z
    foldr f z (T3 x)   = f x z
    foldr f z (T4 x)   = f x z
    foldr f z (T5 x)   = f x z
    foldr _ z T6       = z

See Note [DeriveFoldable with ExistentialQuantification] in TcGenFunctor.

Note [Unconventional anyclass-derived instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
95% of derived instances are what I will label "conventional". That is, they
generate an instance of the form:

  instance C c1 ... cm (T t1 ... tn) where ...

where T is a data type constructor. In particular, it is guaranteed that all
stock- and newtype-derived instances will be of this form, as they simply
wouldn't make sense otherwise.

With DeriveAnyClass, however, the other 5% of the instances emerge (the
"unconventional" ones), as there's no requirement that the last type be headed
with a data type constructor. For instance, this is a perfectly legitimate
anyclass-derived instance:

  class C a
  deriving instance C a

In this way, DeriveAnyClass is quite different, and we need to be careful not
to ingrain the assumption that all instances are of the "conventional" form.
We accomplish this by careful use of datatypes.

First, there's the DerivInstTys data type. This represents whether you are
dealing with an "unconventional" derived instance or a "conventional" one. In
the former case, you only have a list of types. In the latter case, however,
you have a list of types followed by a data type constructor and the arguments
to which it is applied. We encapsulate the latter case's types (and tycon)
with the DataTypeInstArgs data type.

Note that DataTypeInstArgs has *two* copies of the data type constructor and
its argument. This second copy is for the case of data families, in which case
the data family instance has a different representation tycon than the parent
data family's tycon (similarly, the arguments to the tycon might be different
if you use the representation tycon instead). We don't always know what this
representation tycon is (it's only at TcDeriv.mkEqnHelp that we obtain it),
which is we have both DataTypeInstArgsNoRep and DataTypeInstArgsWithRep
(and similarly, DerivInstArgsNoRep and DerivInstArgsWithRep).

It's important to note that DerivInstArgs is only used _before_ we know for
sure what the deriving strategy will be. Once we know this, DerivInstArgs'
functionality is superseded by DerivSpecMechanism. Two constructors of
DerivSpecMechanism also contain DataTypeInstArgs, as it's convenient to refer
to them later when generating bindings.

All of this data type engineering leads to a much cleaner validity-checking
story, as it is now very easy to check in various places whether an instance
is "conventional" or not, and if so, we can perform special "conventional"-only
validity checks.
-}
